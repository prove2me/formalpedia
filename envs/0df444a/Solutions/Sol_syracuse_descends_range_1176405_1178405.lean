-- Prove2me | solution 1 for syracuse_descends_range_1176405_1178405
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:30.507007+00:00
-- url     : https://prove2.me/submissions/322d94fa-13cc-4a07-99e5-8413c21b101f

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


theorem B2981893 : Blo 1176405 2981893 := bbase (se 4 (by rfl) ⟨279552, by rfl⟩ : syracuseStep 2981893 = 559105) (by norm_num)
theorem B5955605 : Blo 1176405 5955605 := bbase (se 6 (by rfl) ⟨139584, by rfl⟩ : syracuseStep 5955605 = 279169) (by norm_num)
theorem B1490977 : Blo 1176405 1490977 := bbase (se 2 (by rfl) ⟨559116, by rfl⟩ : syracuseStep 1490977 = 1118233) (by norm_num)
theorem B3973157 : Blo 1176405 3973157 := bbase (se 4 (by rfl) ⟨372483, by rfl⟩ : syracuseStep 3973157 = 744967) (by norm_num)
theorem B1531973 : Blo 1176405 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B11313269 : Blo 1176405 11313269 := bbase (se 5 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 11313269 = 1060619) (by norm_num)
theorem B2982005 : Blo 1176405 2982005 := bbase (se 5 (by rfl) ⟨139781, by rfl⟩ : syracuseStep 2982005 = 279563) (by norm_num)
theorem B2236565 : Blo 1176405 2236565 := bbase (se 6 (by rfl) ⟨52419, by rfl⟩ : syracuseStep 2236565 = 104839) (by norm_num)
theorem B1491149 : Blo 1176405 1491149 := bbase (se 3 (by rfl) ⟨279590, by rfl⟩ : syracuseStep 1491149 = 559181) (by norm_num)
theorem B2515205 : Blo 1176405 2515205 := bbase (se 4 (by rfl) ⟨235800, by rfl⟩ : syracuseStep 2515205 = 471601) (by norm_num)
theorem B1491205 : Blo 1176405 1491205 := bbase (se 4 (by rfl) ⟨139800, by rfl⟩ : syracuseStep 1491205 = 279601) (by norm_num)
theorem B2236709 : Blo 1176405 2236709 := bbase (se 4 (by rfl) ⟨209691, by rfl⟩ : syracuseStep 2236709 = 419383) (by norm_num)
theorem B2982197 : Blo 1176405 2982197 := bbase (se 5 (by rfl) ⟨139790, by rfl⟩ : syracuseStep 2982197 = 279581) (by norm_num)
theorem B6037829 : Blo 1176405 6037829 := bbase (se 4 (by rfl) ⟨566046, by rfl⟩ : syracuseStep 6037829 = 1132093) (by norm_num)
theorem B2720101 : Blo 1176405 2720101 := bbase (se 4 (by rfl) ⟨255009, by rfl⟩ : syracuseStep 2720101 = 510019) (by norm_num)
theorem B1491301 : Blo 1176405 1491301 := bbase (se 4 (by rfl) ⟨139809, by rfl⟩ : syracuseStep 1491301 = 279619) (by norm_num)
theorem B2687357 : Blo 1176405 2687357 := bbase (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) (by norm_num)
theorem B2548117 : Blo 1176405 2548117 := bbase (se 6 (by rfl) ⟨59721, by rfl⟩ : syracuseStep 2548117 = 119443) (by norm_num)
theorem B3973589 : Blo 1176405 3973589 := bbase (se 7 (by rfl) ⟨46565, by rfl⟩ : syracuseStep 3973589 = 93131) (by norm_num)
theorem B5374421 : Blo 1176405 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B5366245 : Blo 1176405 5366245 := bbase (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) (by norm_num)
theorem B3351077 : Blo 1176405 3351077 := bbase (se 4 (by rfl) ⟨314163, by rfl⟩ : syracuseStep 3351077 = 628327) (by norm_num)
theorem B1884725 : Blo 1176405 1884725 := bbase (se 5 (by rfl) ⟨88346, by rfl⟩ : syracuseStep 1884725 = 176693) (by norm_num)
theorem B6365749 : Blo 1176405 6365749 := bbase (se 5 (by rfl) ⟨298394, by rfl⟩ : syracuseStep 6365749 = 596789) (by norm_num)
theorem B2236997 : Blo 1176405 2236997 := bbase (se 4 (by rfl) ⟨209718, by rfl⟩ : syracuseStep 2236997 = 419437) (by norm_num)
theorem B5374549 : Blo 1176405 5374549 := bbase (se 8 (by rfl) ⟨31491, by rfl⟩ : syracuseStep 5374549 = 62983) (by norm_num)
theorem B2040437 : Blo 1176405 2040437 := bbase (se 5 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 2040437 = 191291) (by norm_num)
theorem B6709877 : Blo 1176405 6709877 := bbase (se 5 (by rfl) ⟨314525, by rfl⟩ : syracuseStep 6709877 = 629051) (by norm_num)
theorem B2982541 : Blo 1176405 2982541 := bbase (se 3 (by rfl) ⟨559226, by rfl⟩ : syracuseStep 2982541 = 1118453) (by norm_num)
theorem B1884917 : Blo 1176405 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B2982653 : Blo 1176405 2982653 := bbase (se 3 (by rfl) ⟨559247, by rfl⟩ : syracuseStep 2982653 = 1118495) (by norm_num)
theorem B1590085 : Blo 1176405 1590085 := bbase (se 4 (by rfl) ⟨149070, by rfl⟩ : syracuseStep 1590085 = 298141) (by norm_num)
theorem B2646917 : Blo 1176405 2646917 := bbase (se 4 (by rfl) ⟨248148, by rfl⟩ : syracuseStep 2646917 = 496297) (by norm_num)
theorem B3974021 : Blo 1176405 3974021 := bbase (se 4 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 3974021 = 745129) (by norm_num)
theorem B5964677 : Blo 1176405 5964677 := bbase (se 4 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 5964677 = 1118377) (by norm_num)
theorem B2646989 : Blo 1176405 2646989 := bbase (se 3 (by rfl) ⟨496310, by rfl⟩ : syracuseStep 2646989 = 992621) (by norm_num)
theorem B14320597 : Blo 1176405 14320597 := bbase (se 7 (by rfl) ⟨167819, by rfl⟩ : syracuseStep 14320597 = 335639) (by norm_num)
theorem B2647061 : Blo 1176405 2647061 := bbase (se 6 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 2647061 = 124081) (by norm_num)
theorem B8946773 : Blo 1176405 8946773 := bbase (se 8 (by rfl) ⟨52422, by rfl⟩ : syracuseStep 8946773 = 104845) (by norm_num)
theorem B2647133 : Blo 1176405 2647133 := bbase (se 3 (by rfl) ⟨496337, by rfl⟩ : syracuseStep 2647133 = 992675) (by norm_num)
theorem B2516093 : Blo 1176405 2516093 := bbase (se 3 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 2516093 = 943535) (by norm_num)
theorem B2647205 : Blo 1176405 2647205 := bbase (se 4 (by rfl) ⟨248175, by rfl⟩ : syracuseStep 2647205 = 496351) (by norm_num)
theorem B2647277 : Blo 1176405 2647277 := bbase (se 3 (by rfl) ⟨496364, by rfl⟩ : syracuseStep 2647277 = 992729) (by norm_num)
theorem B5956901 : Blo 1176405 5956901 := bbase (se 4 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 5956901 = 1116919) (by norm_num)
theorem B1361197 : Blo 1176405 1361197 := bbase (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) (by norm_num)
theorem B2647349 : Blo 1176405 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B3974453 : Blo 1176405 3974453 := bbase (se 5 (by rfl) ⟨186302, by rfl⟩ : syracuseStep 3974453 = 372605) (by norm_num)
theorem B7546229 : Blo 1176405 7546229 := bbase (se 5 (by rfl) ⟨353729, by rfl⟩ : syracuseStep 7546229 = 707459) (by norm_num)
theorem B2516341 : Blo 1176405 2516341 := bbase (se 5 (by rfl) ⟨117953, by rfl⟩ : syracuseStep 2516341 = 235907) (by norm_num)
theorem B2647421 : Blo 1176405 2647421 := bbase (se 3 (by rfl) ⟨496391, by rfl⟩ : syracuseStep 2647421 = 992783) (by norm_num)
theorem B1361305 : Blo 1176405 1361305 := bbase (se 2 (by rfl) ⟨510489, by rfl⟩ : syracuseStep 1361305 = 1020979) (by norm_num)
theorem B5662133 : Blo 1176405 5662133 := bbase (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) (by norm_num)
theorem B2647493 : Blo 1176405 2647493 := bbase (se 4 (by rfl) ⟨248202, by rfl⟩ : syracuseStep 2647493 = 496405) (by norm_num)
theorem B8938997 : Blo 1176405 8938997 := bbase (se 5 (by rfl) ⟨419015, by rfl⟩ : syracuseStep 8938997 = 838031) (by norm_num)
theorem B2647565 : Blo 1176405 2647565 := bbase (se 3 (by rfl) ⟨496418, by rfl⟩ : syracuseStep 2647565 = 992837) (by norm_num)
theorem B2385445 : Blo 1176405 2385445 := bbase (se 4 (by rfl) ⟨223635, by rfl⟩ : syracuseStep 2385445 = 447271) (by norm_num)
theorem B2647637 : Blo 1176405 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B2385517 : Blo 1176405 2385517 := bbase (se 3 (by rfl) ⟨447284, by rfl⟩ : syracuseStep 2385517 = 894569) (by norm_num)
theorem B5662325 : Blo 1176405 5662325 := bbase (se 5 (by rfl) ⟨265421, by rfl⟩ : syracuseStep 5662325 = 530843) (by norm_num)
theorem B2647709 : Blo 1176405 2647709 := bbase (se 3 (by rfl) ⟨496445, by rfl⟩ : syracuseStep 2647709 = 992891) (by norm_num)
theorem B2123429 : Blo 1176405 2123429 := bbase (se 4 (by rfl) ⟨199071, by rfl⟩ : syracuseStep 2123429 = 398143) (by norm_num)
theorem B4245173 : Blo 1176405 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B3352261 : Blo 1176405 3352261 := bbase (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) (by norm_num)
theorem B2647781 : Blo 1176405 2647781 := bbase (se 4 (by rfl) ⟨248229, by rfl⟩ : syracuseStep 2647781 = 496459) (by norm_num)
theorem B3974885 : Blo 1176405 3974885 := bbase (se 4 (by rfl) ⟨372645, by rfl⟩ : syracuseStep 3974885 = 745291) (by norm_num)
theorem B2647853 : Blo 1176405 2647853 := bbase (se 3 (by rfl) ⟨496472, by rfl⟩ : syracuseStep 2647853 = 992945) (by norm_num)
theorem B4245301 : Blo 1176405 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B1910621 : Blo 1176405 1910621 := bbase (se 3 (by rfl) ⟨358241, by rfl⟩ : syracuseStep 1910621 = 716483) (by norm_num)
theorem B2828125 : Blo 1176405 2828125 := bbase (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) (by norm_num)
theorem B3352421 : Blo 1176405 3352421 := bbase (se 4 (by rfl) ⟨314289, by rfl⟩ : syracuseStep 3352421 = 628579) (by norm_num)
theorem B2647925 : Blo 1176405 2647925 := bbase (se 5 (by rfl) ⟨124121, by rfl⟩ : syracuseStep 2647925 = 248243) (by norm_num)
theorem B2647997 : Blo 1176405 2647997 := bbase (se 3 (by rfl) ⟨496499, by rfl⟩ : syracuseStep 2647997 = 992999) (by norm_num)
theorem B5031877 : Blo 1176405 5031877 := bbase (se 4 (by rfl) ⟨471738, by rfl⟩ : syracuseStep 5031877 = 943477) (by norm_num)
theorem B5662709 : Blo 1176405 5662709 := bbase (se 5 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 5662709 = 530879) (by norm_num)
theorem B2582525 : Blo 1176405 2582525 := bbase (se 3 (by rfl) ⟨484223, by rfl⟩ : syracuseStep 2582525 = 968447) (by norm_num)
theorem B2648069 : Blo 1176405 2648069 := bbase (se 4 (by rfl) ⟨248256, by rfl⟩ : syracuseStep 2648069 = 496513) (by norm_num)
theorem B1886237 : Blo 1176405 1886237 := bbase (se 3 (by rfl) ⟨353669, by rfl⟩ : syracuseStep 1886237 = 707339) (by norm_num)
theorem B1509421 : Blo 1176405 1509421 := bbase (se 3 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 1509421 = 566033) (by norm_num)
theorem B2648141 : Blo 1176405 2648141 := bbase (se 3 (by rfl) ⟨496526, by rfl⟩ : syracuseStep 2648141 = 993053) (by norm_num)
theorem B3352661 : Blo 1176405 3352661 := bbase (se 8 (by rfl) ⟨19644, by rfl⟩ : syracuseStep 3352661 = 39289) (by norm_num)
theorem B2386037 : Blo 1176405 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B6367349 : Blo 1176405 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B1886333 : Blo 1176405 1886333 := bbase (se 3 (by rfl) ⟨353687, by rfl⟩ : syracuseStep 1886333 = 707375) (by norm_num)
theorem B2648213 : Blo 1176405 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B3975317 : Blo 1176405 3975317 := bbase (se 6 (by rfl) ⟨93171, by rfl⟩ : syracuseStep 3975317 = 186343) (by norm_num)
theorem B1886365 : Blo 1176405 1886365 := bbase (se 3 (by rfl) ⟨353693, by rfl⟩ : syracuseStep 1886365 = 707387) (by norm_num)
theorem B2418853 : Blo 1176405 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B2648285 : Blo 1176405 2648285 := bbase (se 3 (by rfl) ⟨496553, by rfl⟩ : syracuseStep 2648285 = 993107) (by norm_num)
theorem B4466933 : Blo 1176405 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B3352853 : Blo 1176405 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B2648357 : Blo 1176405 2648357 := bbase (se 4 (by rfl) ⟨248283, by rfl⟩ : syracuseStep 2648357 = 496567) (by norm_num)
theorem B2648429 : Blo 1176405 2648429 := bbase (se 3 (by rfl) ⟨496580, by rfl⟩ : syracuseStep 2648429 = 993161) (by norm_num)
theorem B2648501 : Blo 1176405 2648501 := bbase (se 5 (by rfl) ⟨124148, by rfl⟩ : syracuseStep 2648501 = 248297) (by norm_num)
theorem B2648573 : Blo 1176405 2648573 := bbase (se 3 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 2648573 = 993215) (by norm_num)
theorem B4467221 : Blo 1176405 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B5958197 : Blo 1176405 5958197 := bbase (se 5 (by rfl) ⟨279290, by rfl⟩ : syracuseStep 5958197 = 558581) (by norm_num)
theorem B2648645 : Blo 1176405 2648645 := bbase (se 4 (by rfl) ⟨248310, by rfl⟩ : syracuseStep 2648645 = 496621) (by norm_num)
theorem B3975749 : Blo 1176405 3975749 := bbase (se 4 (by rfl) ⟨372726, by rfl⟩ : syracuseStep 3975749 = 745453) (by norm_num)
theorem B2648717 : Blo 1176405 2648717 := bbase (se 3 (by rfl) ⟨496634, by rfl⟩ : syracuseStep 2648717 = 993269) (by norm_num)
theorem B2648789 : Blo 1176405 2648789 := bbase (se 7 (by rfl) ⟨31040, by rfl⟩ : syracuseStep 2648789 = 62081) (by norm_num)
theorem B1985269 : Blo 1176405 1985269 := bbase (se 5 (by rfl) ⟨93059, by rfl⟩ : syracuseStep 1985269 = 186119) (by norm_num)
theorem B2386685 : Blo 1176405 2386685 := bbase (se 3 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 2386685 = 895007) (by norm_num)
theorem B1723141 : Blo 1176405 1723141 := bbase (se 4 (by rfl) ⟨161544, by rfl⟩ : syracuseStep 1723141 = 323089) (by norm_num)
theorem B2648861 : Blo 1176405 2648861 := bbase (se 3 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 2648861 = 993323) (by norm_num)
theorem B1256257 : Blo 1176405 1256257 := bbase (se 2 (by rfl) ⟨471096, by rfl⟩ : syracuseStep 1256257 = 942193) (by norm_num)
theorem B1985357 : Blo 1176405 1985357 := bbase (se 3 (by rfl) ⟨372254, by rfl⟩ : syracuseStep 1985357 = 744509) (by norm_num)
theorem B2648933 : Blo 1176405 2648933 := bbase (se 4 (by rfl) ⟨248337, by rfl⟩ : syracuseStep 2648933 = 496675) (by norm_num)
theorem B3771269 : Blo 1176405 3771269 := bbase (se 4 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 3771269 = 707113) (by norm_num)
theorem B1256329 : Blo 1176405 1256329 := bbase (se 2 (by rfl) ⟨471123, by rfl⟩ : syracuseStep 1256329 = 942247) (by norm_num)
theorem B2649005 : Blo 1176405 2649005 := bbase (se 3 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 2649005 = 993377) (by norm_num)
theorem B1985485 : Blo 1176405 1985485 := bbase (se 3 (by rfl) ⟨372278, by rfl⟩ : syracuseStep 1985485 = 744557) (by norm_num)
theorem B2649077 : Blo 1176405 2649077 := bbase (se 5 (by rfl) ⟨124175, by rfl⟩ : syracuseStep 2649077 = 248351) (by norm_num)
theorem B3976181 : Blo 1176405 3976181 := bbase (se 5 (by rfl) ⟨186383, by rfl⟩ : syracuseStep 3976181 = 372767) (by norm_num)
theorem B1985573 : Blo 1176405 1985573 := bbase (se 4 (by rfl) ⟨186147, by rfl⟩ : syracuseStep 1985573 = 372295) (by norm_num)
theorem B5237797 : Blo 1176405 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B1256509 : Blo 1176405 1256509 := bbase (se 3 (by rfl) ⟨235595, by rfl⟩ : syracuseStep 1256509 = 471191) (by norm_num)
theorem B2649149 : Blo 1176405 2649149 := bbase (se 3 (by rfl) ⟨496715, by rfl⟩ : syracuseStep 2649149 = 993431) (by norm_num)
theorem B1592389 : Blo 1176405 1592389 := bbase (se 4 (by rfl) ⟨149286, by rfl⟩ : syracuseStep 1592389 = 298573) (by norm_num)
theorem B2649221 : Blo 1176405 2649221 := bbase (se 4 (by rfl) ⟨248364, by rfl⟩ : syracuseStep 2649221 = 496729) (by norm_num)
theorem B19106965 : Blo 1176405 19106965 := bbase (se 6 (by rfl) ⟨447819, by rfl⟩ : syracuseStep 19106965 = 895639) (by norm_num)
theorem B1985701 : Blo 1176405 1985701 := bbase (se 4 (by rfl) ⟨186159, by rfl⟩ : syracuseStep 1985701 = 372319) (by norm_num)
theorem B2829509 : Blo 1176405 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B2649293 : Blo 1176405 2649293 := bbase (se 3 (by rfl) ⟨496742, by rfl⟩ : syracuseStep 2649293 = 993485) (by norm_num)
theorem B3353845 : Blo 1176405 3353845 := bbase (se 5 (by rfl) ⟨157211, by rfl⟩ : syracuseStep 3353845 = 314423) (by norm_num)
theorem B1985789 : Blo 1176405 1985789 := bbase (se 3 (by rfl) ⟨372335, by rfl⟩ : syracuseStep 1985789 = 744671) (by norm_num)
theorem B1764629 : Blo 1176405 1764629 := bbase (se 6 (by rfl) ⟨41358, by rfl⟩ : syracuseStep 1764629 = 82717) (by norm_num)
theorem B2649365 : Blo 1176405 2649365 := bbase (se 6 (by rfl) ⟨62094, by rfl⟩ : syracuseStep 2649365 = 124189) (by norm_num)
theorem B1764653 : Blo 1176405 1764653 := bbase (se 3 (by rfl) ⟨330872, by rfl⟩ : syracuseStep 1764653 = 661745) (by norm_num)
theorem B1764677 : Blo 1176405 1764677 := bbase (se 4 (by rfl) ⟨165438, by rfl⟩ : syracuseStep 1764677 = 330877) (by norm_num)
theorem B1764701 : Blo 1176405 1764701 := bbase (se 3 (by rfl) ⟨330881, by rfl⟩ : syracuseStep 1764701 = 661763) (by norm_num)
theorem B2649437 : Blo 1176405 2649437 := bbase (se 3 (by rfl) ⟨496769, by rfl⟩ : syracuseStep 2649437 = 993539) (by norm_num)
theorem B1789285 : Blo 1176405 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B1764725 : Blo 1176405 1764725 := bbase (se 5 (by rfl) ⟨82721, by rfl⟩ : syracuseStep 1764725 = 165443) (by norm_num)
theorem B1985917 : Blo 1176405 1985917 := bbase (se 3 (by rfl) ⟨372359, by rfl⟩ : syracuseStep 1985917 = 744719) (by norm_num)
theorem B2829701 : Blo 1176405 2829701 := bbase (se 4 (by rfl) ⟨265284, by rfl⟩ : syracuseStep 2829701 = 530569) (by norm_num)
theorem B1764749 : Blo 1176405 1764749 := bbase (se 3 (by rfl) ⟨330890, by rfl⟩ : syracuseStep 1764749 = 661781) (by norm_num)
theorem B1764773 : Blo 1176405 1764773 := bbase (se 4 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 1764773 = 330895) (by norm_num)
theorem B2649509 : Blo 1176405 2649509 := bbase (se 4 (by rfl) ⟨248391, by rfl⟩ : syracuseStep 2649509 = 496783) (by norm_num)
theorem B3976613 : Blo 1176405 3976613 := bbase (se 4 (by rfl) ⟨372807, by rfl⟩ : syracuseStep 3976613 = 745615) (by norm_num)
theorem B1764797 : Blo 1176405 1764797 := bbase (se 3 (by rfl) ⟨330899, by rfl⟩ : syracuseStep 1764797 = 661799) (by norm_num)
theorem B1764821 : Blo 1176405 1764821 := bbase (se 7 (by rfl) ⟨20681, by rfl⟩ : syracuseStep 1764821 = 41363) (by norm_num)
theorem B1986005 : Blo 1176405 1986005 := bbase (se 7 (by rfl) ⟨23273, by rfl⟩ : syracuseStep 1986005 = 46547) (by norm_num)
theorem B1764845 : Blo 1176405 1764845 := bbase (se 3 (by rfl) ⟨330908, by rfl⟩ : syracuseStep 1764845 = 661817) (by norm_num)
theorem B2649581 : Blo 1176405 2649581 := bbase (se 3 (by rfl) ⟨496796, by rfl⟩ : syracuseStep 2649581 = 993593) (by norm_num)
theorem B1256953 : Blo 1176405 1256953 := bbase (se 2 (by rfl) ⟨471357, by rfl⟩ : syracuseStep 1256953 = 942715) (by norm_num)
theorem B1764869 : Blo 1176405 1764869 := bbase (se 4 (by rfl) ⟨165456, by rfl⟩ : syracuseStep 1764869 = 330913) (by norm_num)
theorem B1764893 : Blo 1176405 1764893 := bbase (se 3 (by rfl) ⟨330917, by rfl⟩ : syracuseStep 1764893 = 661835) (by norm_num)
theorem B1764917 : Blo 1176405 1764917 := bbase (se 5 (by rfl) ⟨82730, by rfl⟩ : syracuseStep 1764917 = 165461) (by norm_num)
theorem B2649653 : Blo 1176405 2649653 := bbase (se 5 (by rfl) ⟨124202, by rfl⟩ : syracuseStep 2649653 = 248405) (by norm_num)
theorem B1764941 : Blo 1176405 1764941 := bbase (se 3 (by rfl) ⟨330926, by rfl⟩ : syracuseStep 1764941 = 661853) (by norm_num)
theorem B1986133 : Blo 1176405 1986133 := bbase (se 8 (by rfl) ⟨11637, by rfl⟩ : syracuseStep 1986133 = 23275) (by norm_num)
theorem B1764965 : Blo 1176405 1764965 := bbase (se 4 (by rfl) ⟨165465, by rfl⟩ : syracuseStep 1764965 = 330931) (by norm_num)
theorem B1257077 : Blo 1176405 1257077 := bbase (se 5 (by rfl) ⟨58925, by rfl⟩ : syracuseStep 1257077 = 117851) (by norm_num)
theorem B1764989 : Blo 1176405 1764989 := bbase (se 3 (by rfl) ⟨330935, by rfl⟩ : syracuseStep 1764989 = 661871) (by norm_num)
theorem B2649725 : Blo 1176405 2649725 := bbase (se 3 (by rfl) ⟨496823, by rfl⟩ : syracuseStep 2649725 = 993647) (by norm_num)
theorem B1765013 : Blo 1176405 1765013 := bbase (se 6 (by rfl) ⟨41367, by rfl⟩ : syracuseStep 1765013 = 82735) (by norm_num)
theorem B1765037 : Blo 1176405 1765037 := bbase (se 3 (by rfl) ⟨330944, by rfl⟩ : syracuseStep 1765037 = 661889) (by norm_num)
theorem B1986221 : Blo 1176405 1986221 := bbase (se 3 (by rfl) ⟨372416, by rfl⟩ : syracuseStep 1986221 = 744833) (by norm_num)
theorem B4468405 : Blo 1176405 4468405 := bbase (se 5 (by rfl) ⟨209456, by rfl⟩ : syracuseStep 4468405 = 418913) (by norm_num)
theorem B1765061 : Blo 1176405 1765061 := bbase (se 4 (by rfl) ⟨165474, by rfl⟩ : syracuseStep 1765061 = 330949) (by norm_num)
theorem B2649797 : Blo 1176405 2649797 := bbase (se 4 (by rfl) ⟨248418, by rfl⟩ : syracuseStep 2649797 = 496837) (by norm_num)
theorem B1765085 : Blo 1176405 1765085 := bbase (se 3 (by rfl) ⟨330953, by rfl⟩ : syracuseStep 1765085 = 661907) (by norm_num)
theorem B1765109 : Blo 1176405 1765109 := bbase (se 5 (by rfl) ⟨82739, by rfl⟩ : syracuseStep 1765109 = 165479) (by norm_num)
theorem B3772165 : Blo 1176405 3772165 := bbase (se 4 (by rfl) ⟨353640, by rfl⟩ : syracuseStep 3772165 = 707281) (by norm_num)
theorem B1765133 : Blo 1176405 1765133 := bbase (se 3 (by rfl) ⟨330962, by rfl⟩ : syracuseStep 1765133 = 661925) (by norm_num)
theorem B2649869 : Blo 1176405 2649869 := bbase (se 3 (by rfl) ⟨496850, by rfl⟩ : syracuseStep 2649869 = 993701) (by norm_num)
theorem B1675037 : Blo 1176405 1675037 := bbase (se 3 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 1675037 = 628139) (by norm_num)
theorem B1765157 : Blo 1176405 1765157 := bbase (se 4 (by rfl) ⟨165483, by rfl⟩ : syracuseStep 1765157 = 330967) (by norm_num)
theorem B1986349 : Blo 1176405 1986349 := bbase (se 3 (by rfl) ⟨372440, by rfl⟩ : syracuseStep 1986349 = 744881) (by norm_num)
theorem B1765181 : Blo 1176405 1765181 := bbase (se 3 (by rfl) ⟨330971, by rfl⟩ : syracuseStep 1765181 = 661943) (by norm_num)
theorem B5959493 : Blo 1176405 5959493 := bbase (se 4 (by rfl) ⟨558702, by rfl⟩ : syracuseStep 5959493 = 1117405) (by norm_num)
theorem B2387789 : Blo 1176405 2387789 := bbase (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) (by norm_num)
theorem B1765205 : Blo 1176405 1765205 := bbase (se 9 (by rfl) ⟨5171, by rfl⟩ : syracuseStep 1765205 = 10343) (by norm_num)
theorem B2649941 : Blo 1176405 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B3977045 : Blo 1176405 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B1675117 : Blo 1176405 1675117 := bbase (se 3 (by rfl) ⟨314084, by rfl⟩ : syracuseStep 1675117 = 628169) (by norm_num)
theorem B1765229 : Blo 1176405 1765229 := bbase (se 3 (by rfl) ⟨330980, by rfl⟩ : syracuseStep 1765229 = 661961) (by norm_num)
theorem B1257329 : Blo 1176405 1257329 := bbase (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) (by norm_num)
theorem B1765253 : Blo 1176405 1765253 := bbase (se 4 (by rfl) ⟨165492, by rfl⟩ : syracuseStep 1765253 = 330985) (by norm_num)
theorem B1986437 : Blo 1176405 1986437 := bbase (se 4 (by rfl) ⟨186228, by rfl⟩ : syracuseStep 1986437 = 372457) (by norm_num)
theorem B1511309 : Blo 1176405 1511309 := bbase (se 3 (by rfl) ⟨283370, by rfl⟩ : syracuseStep 1511309 = 566741) (by norm_num)
theorem B1765277 : Blo 1176405 1765277 := bbase (se 3 (by rfl) ⟨330989, by rfl⟩ : syracuseStep 1765277 = 661979) (by norm_num)
theorem B2650013 : Blo 1176405 2650013 := bbase (se 3 (by rfl) ⟨496877, by rfl⟩ : syracuseStep 2650013 = 993755) (by norm_num)
theorem B1765301 : Blo 1176405 1765301 := bbase (se 5 (by rfl) ⟨82748, by rfl⟩ : syracuseStep 1765301 = 165497) (by norm_num)
theorem B1765325 : Blo 1176405 1765325 := bbase (se 3 (by rfl) ⟨330998, by rfl⟩ : syracuseStep 1765325 = 661997) (by norm_num)
theorem B1675237 : Blo 1176405 1675237 := bbase (se 4 (by rfl) ⟨157053, by rfl⟩ : syracuseStep 1675237 = 314107) (by norm_num)
theorem B1765349 : Blo 1176405 1765349 := bbase (se 4 (by rfl) ⟨165501, by rfl⟩ : syracuseStep 1765349 = 331003) (by norm_num)
theorem B4468709 : Blo 1176405 4468709 := bbase (se 4 (by rfl) ⟨418941, by rfl⟩ : syracuseStep 4468709 = 837883) (by norm_num)
theorem B2650085 : Blo 1176405 2650085 := bbase (se 4 (by rfl) ⟨248445, by rfl⟩ : syracuseStep 2650085 = 496891) (by norm_num)
theorem B1765373 : Blo 1176405 1765373 := bbase (se 3 (by rfl) ⟨331007, by rfl⟩ : syracuseStep 1765373 = 662015) (by norm_num)
theorem B1986565 : Blo 1176405 1986565 := bbase (se 4 (by rfl) ⟨186240, by rfl⟩ : syracuseStep 1986565 = 372481) (by norm_num)
theorem B1765397 : Blo 1176405 1765397 := bbase (se 6 (by rfl) ⟨41376, by rfl⟩ : syracuseStep 1765397 = 82753) (by norm_num)
theorem B1765421 : Blo 1176405 1765421 := bbase (se 3 (by rfl) ⟨331016, by rfl⟩ : syracuseStep 1765421 = 662033) (by norm_num)
theorem B2650157 : Blo 1176405 2650157 := bbase (se 3 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 2650157 = 993809) (by norm_num)
theorem B1675333 : Blo 1176405 1675333 := bbase (se 4 (by rfl) ⟨157062, by rfl⟩ : syracuseStep 1675333 = 314125) (by norm_num)
theorem B1765445 : Blo 1176405 1765445 := bbase (se 4 (by rfl) ⟨165510, by rfl⟩ : syracuseStep 1765445 = 331021) (by norm_num)
theorem B1765469 : Blo 1176405 1765469 := bbase (se 3 (by rfl) ⟨331025, by rfl⟩ : syracuseStep 1765469 = 662051) (by norm_num)
theorem B1986653 : Blo 1176405 1986653 := bbase (se 3 (by rfl) ⟨372497, by rfl⟩ : syracuseStep 1986653 = 744995) (by norm_num)
theorem B1765493 : Blo 1176405 1765493 := bbase (se 5 (by rfl) ⟨82757, by rfl⟩ : syracuseStep 1765493 = 165515) (by norm_num)
theorem B2650229 : Blo 1176405 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B1765517 : Blo 1176405 1765517 := bbase (se 3 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 1765517 = 662069) (by norm_num)
theorem B3772565 : Blo 1176405 3772565 := bbase (se 6 (by rfl) ⟨88419, by rfl⟩ : syracuseStep 3772565 = 176839) (by norm_num)
theorem B1765541 : Blo 1176405 1765541 := bbase (se 4 (by rfl) ⟨165519, by rfl⟩ : syracuseStep 1765541 = 331039) (by norm_num)
theorem B1765565 : Blo 1176405 1765565 := bbase (se 3 (by rfl) ⟨331043, by rfl⟩ : syracuseStep 1765565 = 662087) (by norm_num)
theorem B2650301 : Blo 1176405 2650301 := bbase (se 3 (by rfl) ⟨496931, by rfl⟩ : syracuseStep 2650301 = 993863) (by norm_num)
theorem B9539797 : Blo 1176405 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B2978005 : Blo 1176405 2978005 := bbase (se 7 (by rfl) ⟨34898, by rfl⟩ : syracuseStep 2978005 = 69797) (by norm_num)
theorem B1765589 : Blo 1176405 1765589 := bbase (se 7 (by rfl) ⟨20690, by rfl⟩ : syracuseStep 1765589 = 41381) (by norm_num)
theorem B1274077 : Blo 1176405 1274077 := bbase (se 3 (by rfl) ⟨238889, by rfl⟩ : syracuseStep 1274077 = 477779) (by norm_num)
theorem B1986781 : Blo 1176405 1986781 := bbase (se 3 (by rfl) ⟨372521, by rfl⟩ : syracuseStep 1986781 = 745043) (by norm_num)
theorem B1765613 : Blo 1176405 1765613 := bbase (se 3 (by rfl) ⟨331052, by rfl⟩ : syracuseStep 1765613 = 662105) (by norm_num)
theorem B1765637 : Blo 1176405 1765637 := bbase (se 4 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 1765637 = 331057) (by norm_num)
theorem B2650373 : Blo 1176405 2650373 := bbase (se 4 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 2650373 = 496945) (by norm_num)
theorem B1765661 : Blo 1176405 1765661 := bbase (se 3 (by rfl) ⟨331061, by rfl⟩ : syracuseStep 1765661 = 662123) (by norm_num)
theorem B1257773 : Blo 1176405 1257773 := bbase (se 3 (by rfl) ⟨235832, by rfl⟩ : syracuseStep 1257773 = 471665) (by norm_num)
theorem B1765685 : Blo 1176405 1765685 := bbase (se 5 (by rfl) ⟨82766, by rfl⟩ : syracuseStep 1765685 = 165533) (by norm_num)
theorem B1986869 : Blo 1176405 1986869 := bbase (se 5 (by rfl) ⟨93134, by rfl⟩ : syracuseStep 1986869 = 186269) (by norm_num)
theorem B2978117 : Blo 1176405 2978117 := bbase (se 4 (by rfl) ⟨279198, by rfl⟩ : syracuseStep 2978117 = 558397) (by norm_num)
theorem B3354949 : Blo 1176405 3354949 := bbase (se 4 (by rfl) ⟨314526, by rfl⟩ : syracuseStep 3354949 = 629053) (by norm_num)
theorem B1765709 : Blo 1176405 1765709 := bbase (se 3 (by rfl) ⟨331070, by rfl⟩ : syracuseStep 1765709 = 662141) (by norm_num)
theorem B2650445 : Blo 1176405 2650445 := bbase (se 3 (by rfl) ⟨496958, by rfl⟩ : syracuseStep 2650445 = 993917) (by norm_num)
theorem B48329045 : Blo 1176405 48329045 := bbase (se 10 (by rfl) ⟨70794, by rfl⟩ : syracuseStep 48329045 = 141589) (by norm_num)
theorem B1765733 : Blo 1176405 1765733 := bbase (se 4 (by rfl) ⟨165537, by rfl⟩ : syracuseStep 1765733 = 331075) (by norm_num)
theorem B1765757 : Blo 1176405 1765757 := bbase (se 3 (by rfl) ⟨331079, by rfl⟩ : syracuseStep 1765757 = 662159) (by norm_num)
theorem B1765781 : Blo 1176405 1765781 := bbase (se 6 (by rfl) ⟨41385, by rfl⟩ : syracuseStep 1765781 = 82771) (by norm_num)
theorem B2650517 : Blo 1176405 2650517 := bbase (se 6 (by rfl) ⟨62121, by rfl⟩ : syracuseStep 2650517 = 124243) (by norm_num)
theorem B1765805 : Blo 1176405 1765805 := bbase (se 3 (by rfl) ⟨331088, by rfl⟩ : syracuseStep 1765805 = 662177) (by norm_num)
theorem B1986997 : Blo 1176405 1986997 := bbase (se 5 (by rfl) ⟨93140, by rfl⟩ : syracuseStep 1986997 = 186281) (by norm_num)
theorem B1765829 : Blo 1176405 1765829 := bbase (se 4 (by rfl) ⟨165546, by rfl⟩ : syracuseStep 1765829 = 331093) (by norm_num)
theorem B1700293 : Blo 1176405 1700293 := bbase (se 4 (by rfl) ⟨159402, by rfl⟩ : syracuseStep 1700293 = 318805) (by norm_num)
theorem B1323481 : Blo 1176405 1323481 := bbase (se 2 (by rfl) ⟨496305, by rfl⟩ : syracuseStep 1323481 = 992611) (by norm_num)
theorem B1765853 : Blo 1176405 1765853 := bbase (se 3 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 1765853 = 662195) (by norm_num)
theorem B2650589 : Blo 1176405 2650589 := bbase (se 3 (by rfl) ⟨496985, by rfl⟩ : syracuseStep 2650589 = 993971) (by norm_num)
theorem B1765877 : Blo 1176405 1765877 := bbase (se 5 (by rfl) ⟨82775, by rfl⟩ : syracuseStep 1765877 = 165551) (by norm_num)
theorem B11473397 : Blo 1176405 11473397 := bbase (se 5 (by rfl) ⟨537815, by rfl⟩ : syracuseStep 11473397 = 1075631) (by norm_num)
theorem B1323517 : Blo 1176405 1323517 := bbase (se 3 (by rfl) ⟨248159, by rfl⟩ : syracuseStep 1323517 = 496319) (by norm_num)
theorem B2978309 : Blo 1176405 2978309 := bbase (se 4 (by rfl) ⟨279216, by rfl⟩ : syracuseStep 2978309 = 558433) (by norm_num)
theorem B1765901 : Blo 1176405 1765901 := bbase (se 3 (by rfl) ⟨331106, by rfl⟩ : syracuseStep 1765901 = 662213) (by norm_num)
theorem B1987085 : Blo 1176405 1987085 := bbase (se 3 (by rfl) ⟨372578, by rfl⟩ : syracuseStep 1987085 = 745157) (by norm_num)
theorem B12079637 : Blo 1176405 12079637 := bbase (se 6 (by rfl) ⟨283116, by rfl⟩ : syracuseStep 12079637 = 566233) (by norm_num)
theorem B1323553 : Blo 1176405 1323553 := bbase (se 2 (by rfl) ⟨496332, by rfl⟩ : syracuseStep 1323553 = 992665) (by norm_num)
theorem B1765925 : Blo 1176405 1765925 := bbase (se 4 (by rfl) ⟨165555, by rfl⟩ : syracuseStep 1765925 = 331111) (by norm_num)
theorem B1274405 : Blo 1176405 1274405 := bbase (se 4 (by rfl) ⟨119475, by rfl⟩ : syracuseStep 1274405 = 238951) (by norm_num)
theorem B1258021 : Blo 1176405 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B2650661 : Blo 1176405 2650661 := bbase (se 4 (by rfl) ⟨248499, by rfl⟩ : syracuseStep 2650661 = 496999) (by norm_num)
theorem B1675829 : Blo 1176405 1675829 := bbase (se 5 (by rfl) ⟨78554, by rfl⟩ : syracuseStep 1675829 = 157109) (by norm_num)
theorem B1765949 : Blo 1176405 1765949 := bbase (se 3 (by rfl) ⟨331115, by rfl⟩ : syracuseStep 1765949 = 662231) (by norm_num)
theorem B1323589 : Blo 1176405 1323589 := bbase (se 4 (by rfl) ⟨124086, by rfl⟩ : syracuseStep 1323589 = 248173) (by norm_num)
theorem B1765973 : Blo 1176405 1765973 := bbase (se 8 (by rfl) ⟨10347, by rfl⟩ : syracuseStep 1765973 = 20695) (by norm_num)
theorem B1323625 : Blo 1176405 1323625 := bbase (se 2 (by rfl) ⟨496359, by rfl⟩ : syracuseStep 1323625 = 992719) (by norm_num)
theorem B1765997 : Blo 1176405 1765997 := bbase (se 3 (by rfl) ⟨331124, by rfl⟩ : syracuseStep 1765997 = 662249) (by norm_num)
theorem B2650733 : Blo 1176405 2650733 := bbase (se 3 (by rfl) ⟨497012, by rfl⟩ : syracuseStep 2650733 = 994025) (by norm_num)
theorem B1766021 : Blo 1176405 1766021 := bbase (se 4 (by rfl) ⟨165564, by rfl⟩ : syracuseStep 1766021 = 331129) (by norm_num)
theorem B1323661 : Blo 1176405 1323661 := bbase (se 3 (by rfl) ⟨248186, by rfl⟩ : syracuseStep 1323661 = 496373) (by norm_num)
theorem B1987213 : Blo 1176405 1987213 := bbase (se 3 (by rfl) ⟨372602, by rfl⟩ : syracuseStep 1987213 = 745205) (by norm_num)
theorem B1766045 : Blo 1176405 1766045 := bbase (se 3 (by rfl) ⟨331133, by rfl⟩ : syracuseStep 1766045 = 662267) (by norm_num)
theorem B1413793 : Blo 1176405 1413793 := bbase (se 2 (by rfl) ⟨530172, by rfl⟩ : syracuseStep 1413793 = 1060345) (by norm_num)
theorem B1323697 : Blo 1176405 1323697 := bbase (se 2 (by rfl) ⟨496386, by rfl⟩ : syracuseStep 1323697 = 992773) (by norm_num)
theorem B1766069 : Blo 1176405 1766069 := bbase (se 5 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 1766069 = 165569) (by norm_num)
theorem B2650805 : Blo 1176405 2650805 := bbase (se 5 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 2650805 = 248513) (by norm_num)
theorem B1766093 : Blo 1176405 1766093 := bbase (se 3 (by rfl) ⟨331142, by rfl⟩ : syracuseStep 1766093 = 662285) (by norm_num)
theorem B1323733 : Blo 1176405 1323733 := bbase (se 7 (by rfl) ⟨15512, by rfl⟩ : syracuseStep 1323733 = 31025) (by norm_num)
theorem B1766117 : Blo 1176405 1766117 := bbase (se 4 (by rfl) ⟨165573, by rfl⟩ : syracuseStep 1766117 = 331147) (by norm_num)
theorem B1987301 : Blo 1176405 1987301 := bbase (se 4 (by rfl) ⟨186309, by rfl⟩ : syracuseStep 1987301 = 372619) (by norm_num)
theorem B1323769 : Blo 1176405 1323769 := bbase (se 2 (by rfl) ⟨496413, by rfl⟩ : syracuseStep 1323769 = 992827) (by norm_num)
theorem B1766141 : Blo 1176405 1766141 := bbase (se 3 (by rfl) ⟨331151, by rfl⟩ : syracuseStep 1766141 = 662303) (by norm_num)
theorem B2650877 : Blo 1176405 2650877 := bbase (se 3 (by rfl) ⟨497039, by rfl⟩ : syracuseStep 2650877 = 994079) (by norm_num)
theorem B1766165 : Blo 1176405 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B1323805 : Blo 1176405 1323805 := bbase (se 3 (by rfl) ⟨248213, by rfl⟩ : syracuseStep 1323805 = 496427) (by norm_num)
theorem B1766189 : Blo 1176405 1766189 := bbase (se 3 (by rfl) ⟨331160, by rfl⟩ : syracuseStep 1766189 = 662321) (by norm_num)
theorem B8172341 : Blo 1176405 8172341 := bbase (se 5 (by rfl) ⟨383078, by rfl⟩ : syracuseStep 8172341 = 766157) (by norm_num)
theorem B1323841 : Blo 1176405 1323841 := bbase (se 2 (by rfl) ⟨496440, by rfl⟩ : syracuseStep 1323841 = 992881) (by norm_num)
theorem B1766213 : Blo 1176405 1766213 := bbase (se 4 (by rfl) ⟨165582, by rfl⟩ : syracuseStep 1766213 = 331165) (by norm_num)
theorem B2650949 : Blo 1176405 2650949 := bbase (se 4 (by rfl) ⟨248526, by rfl⟩ : syracuseStep 2650949 = 497053) (by norm_num)
theorem B2978653 : Blo 1176405 2978653 := bbase (se 3 (by rfl) ⟨558497, by rfl⟩ : syracuseStep 2978653 = 1116995) (by norm_num)
theorem B1766237 : Blo 1176405 1766237 := bbase (se 3 (by rfl) ⟨331169, by rfl⟩ : syracuseStep 1766237 = 662339) (by norm_num)
theorem B1323877 : Blo 1176405 1323877 := bbase (se 4 (by rfl) ⟨124113, by rfl⟩ : syracuseStep 1323877 = 248227) (by norm_num)
theorem B1987429 : Blo 1176405 1987429 := bbase (se 4 (by rfl) ⟨186321, by rfl⟩ : syracuseStep 1987429 = 372643) (by norm_num)
theorem B1766261 : Blo 1176405 1766261 := bbase (se 5 (by rfl) ⟨82793, by rfl⟩ : syracuseStep 1766261 = 165587) (by norm_num)
theorem B1323913 : Blo 1176405 1323913 := bbase (se 2 (by rfl) ⟨496467, by rfl⟩ : syracuseStep 1323913 = 992935) (by norm_num)
theorem B1766285 : Blo 1176405 1766285 := bbase (se 3 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 1766285 = 662357) (by norm_num)
theorem B2651021 : Blo 1176405 2651021 := bbase (se 3 (by rfl) ⟨497066, by rfl⟩ : syracuseStep 2651021 = 994133) (by norm_num)
theorem B3019685 : Blo 1176405 3019685 := bbase (se 4 (by rfl) ⟨283095, by rfl⟩ : syracuseStep 3019685 = 566191) (by norm_num)
theorem B1766309 : Blo 1176405 1766309 := bbase (se 4 (by rfl) ⟨165591, by rfl⟩ : syracuseStep 1766309 = 331183) (by norm_num)
theorem B1790885 : Blo 1176405 1790885 := bbase (se 4 (by rfl) ⟨167895, by rfl⟩ : syracuseStep 1790885 = 335791) (by norm_num)
theorem B2831269 : Blo 1176405 2831269 := bbase (se 4 (by rfl) ⟨265431, by rfl⟩ : syracuseStep 2831269 = 530863) (by norm_num)
theorem B1323949 : Blo 1176405 1323949 := bbase (se 3 (by rfl) ⟨248240, by rfl⟩ : syracuseStep 1323949 = 496481) (by norm_num)
theorem B1766333 : Blo 1176405 1766333 := bbase (se 3 (by rfl) ⟨331187, by rfl⟩ : syracuseStep 1766333 = 662375) (by norm_num)
theorem B1987517 : Blo 1176405 1987517 := bbase (se 3 (by rfl) ⟨372659, by rfl⟩ : syracuseStep 1987517 = 745319) (by norm_num)
theorem B2978765 : Blo 1176405 2978765 := bbase (se 3 (by rfl) ⟨558518, by rfl⟩ : syracuseStep 2978765 = 1117037) (by norm_num)
theorem B1323985 : Blo 1176405 1323985 := bbase (se 2 (by rfl) ⟨496494, by rfl⟩ : syracuseStep 1323985 = 992989) (by norm_num)
theorem B1766357 : Blo 1176405 1766357 := bbase (se 7 (by rfl) ⟨20699, by rfl⟩ : syracuseStep 1766357 = 41399) (by norm_num)
theorem B2651093 : Blo 1176405 2651093 := bbase (se 7 (by rfl) ⟨31067, by rfl⟩ : syracuseStep 2651093 = 62135) (by norm_num)
theorem B1766381 : Blo 1176405 1766381 := bbase (se 3 (by rfl) ⟨331196, by rfl⟩ : syracuseStep 1766381 = 662393) (by norm_num)
theorem B5026805 : Blo 1176405 5026805 := bbase (se 5 (by rfl) ⟨235631, by rfl⟩ : syracuseStep 5026805 = 471263) (by norm_num)
theorem B1324021 : Blo 1176405 1324021 := bbase (se 5 (by rfl) ⟨62063, by rfl⟩ : syracuseStep 1324021 = 124127) (by norm_num)
theorem B6042613 : Blo 1176405 6042613 := bbase (se 5 (by rfl) ⟨283247, by rfl⟩ : syracuseStep 6042613 = 566495) (by norm_num)
theorem B1766405 : Blo 1176405 1766405 := bbase (se 4 (by rfl) ⟨165600, by rfl⟩ : syracuseStep 1766405 = 331201) (by norm_num)
theorem B1324057 : Blo 1176405 1324057 := bbase (se 2 (by rfl) ⟨496521, by rfl⟩ : syracuseStep 1324057 = 993043) (by norm_num)
theorem B1766429 : Blo 1176405 1766429 := bbase (se 3 (by rfl) ⟨331205, by rfl⟩ : syracuseStep 1766429 = 662411) (by norm_num)
theorem B2651165 : Blo 1176405 2651165 := bbase (se 3 (by rfl) ⟨497093, by rfl⟩ : syracuseStep 2651165 = 994187) (by norm_num)
theorem B1766453 : Blo 1176405 1766453 := bbase (se 5 (by rfl) ⟨82802, by rfl⟩ : syracuseStep 1766453 = 165605) (by norm_num)
theorem B1324093 : Blo 1176405 1324093 := bbase (se 3 (by rfl) ⟨248267, by rfl⟩ : syracuseStep 1324093 = 496535) (by norm_num)
theorem B1987645 : Blo 1176405 1987645 := bbase (se 3 (by rfl) ⟨372683, by rfl⟩ : syracuseStep 1987645 = 745367) (by norm_num)
theorem B1766477 : Blo 1176405 1766477 := bbase (se 3 (by rfl) ⟨331214, by rfl⟩ : syracuseStep 1766477 = 662429) (by norm_num)
theorem B5960789 : Blo 1176405 5960789 := bbase (se 8 (by rfl) ⟨34926, by rfl⟩ : syracuseStep 5960789 = 69853) (by norm_num)
theorem B1676381 : Blo 1176405 1676381 := bbase (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) (by norm_num)
theorem B1324129 : Blo 1176405 1324129 := bbase (se 2 (by rfl) ⟨496548, by rfl⟩ : syracuseStep 1324129 = 993097) (by norm_num)
theorem B1766501 : Blo 1176405 1766501 := bbase (se 4 (by rfl) ⟨165609, by rfl⟩ : syracuseStep 1766501 = 331219) (by norm_num)
theorem B2651237 : Blo 1176405 2651237 := bbase (se 4 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 2651237 = 497107) (by norm_num)
theorem B1791085 : Blo 1176405 1791085 := bbase (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) (by norm_num)
theorem B1766525 : Blo 1176405 1766525 := bbase (se 3 (by rfl) ⟨331223, by rfl⟩ : syracuseStep 1766525 = 662447) (by norm_num)
theorem B1324165 : Blo 1176405 1324165 := bbase (se 4 (by rfl) ⟨124140, by rfl⟩ : syracuseStep 1324165 = 248281) (by norm_num)
theorem B2978957 : Blo 1176405 2978957 := bbase (se 3 (by rfl) ⟨558554, by rfl⟩ : syracuseStep 2978957 = 1117109) (by norm_num)
theorem B1766549 : Blo 1176405 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B1987733 : Blo 1176405 1987733 := bbase (se 6 (by rfl) ⟨46587, by rfl⟩ : syracuseStep 1987733 = 93175) (by norm_num)
theorem B1324201 : Blo 1176405 1324201 := bbase (se 2 (by rfl) ⟨496575, by rfl⟩ : syracuseStep 1324201 = 993151) (by norm_num)
theorem B1766573 : Blo 1176405 1766573 := bbase (se 3 (by rfl) ⟨331232, by rfl⟩ : syracuseStep 1766573 = 662465) (by norm_num)
theorem B2651309 : Blo 1176405 2651309 := bbase (se 3 (by rfl) ⟨497120, by rfl⟩ : syracuseStep 2651309 = 994241) (by norm_num)
theorem B4027589 : Blo 1176405 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B1766597 : Blo 1176405 1766597 := bbase (se 4 (by rfl) ⟨165618, by rfl⟩ : syracuseStep 1766597 = 331237) (by norm_num)
theorem B1324237 : Blo 1176405 1324237 := bbase (se 3 (by rfl) ⟨248294, by rfl⟩ : syracuseStep 1324237 = 496589) (by norm_num)
theorem B1193177 : Blo 1176405 1193177 := bbase (se 2 (by rfl) ⟨447441, by rfl⟩ : syracuseStep 1193177 = 894883) (by norm_num)
theorem B2233565 : Blo 1176405 2233565 := bbase (se 3 (by rfl) ⟨418793, by rfl⟩ : syracuseStep 2233565 = 837587) (by norm_num)
theorem B1766621 : Blo 1176405 1766621 := bbase (se 3 (by rfl) ⟨331241, by rfl⟩ : syracuseStep 1766621 = 662483) (by norm_num)
theorem B1324273 : Blo 1176405 1324273 := bbase (se 2 (by rfl) ⟨496602, by rfl⟩ : syracuseStep 1324273 = 993205) (by norm_num)
theorem B4773109 : Blo 1176405 4773109 := bbase (se 5 (by rfl) ⟨223739, by rfl⟩ : syracuseStep 4773109 = 447479) (by norm_num)
theorem B1766645 : Blo 1176405 1766645 := bbase (se 5 (by rfl) ⟨82811, by rfl⟩ : syracuseStep 1766645 = 165623) (by norm_num)
theorem B2651381 : Blo 1176405 2651381 := bbase (se 5 (by rfl) ⟨124283, by rfl⟩ : syracuseStep 2651381 = 248567) (by norm_num)
theorem B1766669 : Blo 1176405 1766669 := bbase (se 3 (by rfl) ⟨331250, by rfl⟩ : syracuseStep 1766669 = 662501) (by norm_num)
theorem B5027093 : Blo 1176405 5027093 := bbase (se 6 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 5027093 = 235645) (by norm_num)
theorem B1324309 : Blo 1176405 1324309 := bbase (se 6 (by rfl) ⟨31038, by rfl⟩ : syracuseStep 1324309 = 62077) (by norm_num)
theorem B1987861 : Blo 1176405 1987861 := bbase (se 6 (by rfl) ⟨46590, by rfl⟩ : syracuseStep 1987861 = 93181) (by norm_num)
theorem B1766693 : Blo 1176405 1766693 := bbase (se 4 (by rfl) ⟨165627, by rfl⟩ : syracuseStep 1766693 = 331255) (by norm_num)
theorem B1324345 : Blo 1176405 1324345 := bbase (se 2 (by rfl) ⟨496629, by rfl⟩ : syracuseStep 1324345 = 993259) (by norm_num)
theorem B1766717 : Blo 1176405 1766717 := bbase (se 3 (by rfl) ⟨331259, by rfl⟩ : syracuseStep 1766717 = 662519) (by norm_num)
theorem B1766741 : Blo 1176405 1766741 := bbase (se 13 (by rfl) ⟨323, by rfl⟩ : syracuseStep 1766741 = 647) (by norm_num)
theorem B1324381 : Blo 1176405 1324381 := bbase (se 3 (by rfl) ⟨248321, by rfl⟩ : syracuseStep 1324381 = 496643) (by norm_num)
theorem B1766765 : Blo 1176405 1766765 := bbase (se 3 (by rfl) ⟨331268, by rfl⟩ : syracuseStep 1766765 = 662537) (by norm_num)
theorem B1987949 : Blo 1176405 1987949 := bbase (se 3 (by rfl) ⟨372740, by rfl⟩ : syracuseStep 1987949 = 745481) (by norm_num)
theorem B7853429 : Blo 1176405 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B3102077 : Blo 1176405 3102077 := bbase (se 3 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 3102077 = 1163279) (by norm_num)
theorem B1324417 : Blo 1176405 1324417 := bbase (se 2 (by rfl) ⟨496656, by rfl⟩ : syracuseStep 1324417 = 993313) (by norm_num)
theorem B1766789 : Blo 1176405 1766789 := bbase (se 4 (by rfl) ⟨165636, by rfl⟩ : syracuseStep 1766789 = 331273) (by norm_num)
theorem B1766813 : Blo 1176405 1766813 := bbase (se 3 (by rfl) ⟨331277, by rfl⟩ : syracuseStep 1766813 = 662555) (by norm_num)
theorem B2487709 : Blo 1176405 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B1324453 : Blo 1176405 1324453 := bbase (se 4 (by rfl) ⟨124167, by rfl⟩ : syracuseStep 1324453 = 248335) (by norm_num)
theorem B1766837 : Blo 1176405 1766837 := bbase (se 5 (by rfl) ⟨82820, by rfl⟩ : syracuseStep 1766837 = 165641) (by norm_num)
theorem B1324489 : Blo 1176405 1324489 := bbase (se 2 (by rfl) ⟨496683, by rfl⟩ : syracuseStep 1324489 = 993367) (by norm_num)
theorem B1766861 : Blo 1176405 1766861 := bbase (se 3 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 1766861 = 662573) (by norm_num)
theorem B3184085 : Blo 1176405 3184085 := bbase (se 7 (by rfl) ⟨37313, by rfl⟩ : syracuseStep 3184085 = 74627) (by norm_num)
theorem B2979301 : Blo 1176405 2979301 := bbase (se 4 (by rfl) ⟨279309, by rfl⟩ : syracuseStep 2979301 = 558619) (by norm_num)
theorem B1766885 : Blo 1176405 1766885 := bbase (se 4 (by rfl) ⟨165645, by rfl⟩ : syracuseStep 1766885 = 331291) (by norm_num)
theorem B1324525 : Blo 1176405 1324525 := bbase (se 3 (by rfl) ⟨248348, by rfl⟩ : syracuseStep 1324525 = 496697) (by norm_num)
theorem B1988077 : Blo 1176405 1988077 := bbase (se 3 (by rfl) ⟨372764, by rfl⟩ : syracuseStep 1988077 = 745529) (by norm_num)
theorem B1766909 : Blo 1176405 1766909 := bbase (se 3 (by rfl) ⟨331295, by rfl⟩ : syracuseStep 1766909 = 662591) (by norm_num)
theorem B3970565 : Blo 1176405 3970565 := bbase (se 4 (by rfl) ⟨372240, by rfl⟩ : syracuseStep 3970565 = 744481) (by norm_num)
theorem B1324561 : Blo 1176405 1324561 := bbase (se 2 (by rfl) ⟨496710, by rfl⟩ : syracuseStep 1324561 = 993421) (by norm_num)
theorem B6706709 : Blo 1176405 6706709 := bbase (se 6 (by rfl) ⟨157188, by rfl⟩ : syracuseStep 6706709 = 314377) (by norm_num)
theorem B1766933 : Blo 1176405 1766933 := bbase (se 6 (by rfl) ⟨41412, by rfl⟩ : syracuseStep 1766933 = 82825) (by norm_num)
theorem B1766957 : Blo 1176405 1766957 := bbase (se 3 (by rfl) ⟨331304, by rfl⟩ : syracuseStep 1766957 = 662609) (by norm_num)
theorem B1324597 : Blo 1176405 1324597 := bbase (se 5 (by rfl) ⟨62090, by rfl⟩ : syracuseStep 1324597 = 124181) (by norm_num)
theorem B1766981 : Blo 1176405 1766981 := bbase (se 4 (by rfl) ⟨165654, by rfl⟩ : syracuseStep 1766981 = 331309) (by norm_num)
theorem B1988165 : Blo 1176405 1988165 := bbase (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) (by norm_num)
theorem B2979413 : Blo 1176405 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B1324633 : Blo 1176405 1324633 := bbase (se 2 (by rfl) ⟨496737, by rfl⟩ : syracuseStep 1324633 = 993475) (by norm_num)
theorem B1767005 : Blo 1176405 1767005 := bbase (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) (by norm_num)
theorem B1816157 : Blo 1176405 1816157 := bbase (se 3 (by rfl) ⟨340529, by rfl⟩ : syracuseStep 1816157 = 681059) (by norm_num)
theorem B1767029 : Blo 1176405 1767029 := bbase (se 5 (by rfl) ⟨82829, by rfl⟩ : syracuseStep 1767029 = 165659) (by norm_num)
theorem B1324669 : Blo 1176405 1324669 := bbase (se 3 (by rfl) ⟨248375, by rfl⟩ : syracuseStep 1324669 = 496751) (by norm_num)
theorem B1414793 : Blo 1176405 1414793 := bbase (se 2 (by rfl) ⟨530547, by rfl⟩ : syracuseStep 1414793 = 1061095) (by norm_num)
theorem B1767053 : Blo 1176405 1767053 := bbase (se 3 (by rfl) ⟨331322, by rfl⟩ : syracuseStep 1767053 = 662645) (by norm_num)
theorem B1324705 : Blo 1176405 1324705 := bbase (se 2 (by rfl) ⟨496764, by rfl⟩ : syracuseStep 1324705 = 993529) (by norm_num)
theorem B1767077 : Blo 1176405 1767077 := bbase (se 4 (by rfl) ⟨165663, by rfl⟩ : syracuseStep 1767077 = 331327) (by norm_num)
theorem B5732021 : Blo 1176405 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B1414841 : Blo 1176405 1414841 := bbase (se 2 (by rfl) ⟨530565, by rfl⟩ : syracuseStep 1414841 = 1061131) (by norm_num)
theorem B1767101 : Blo 1176405 1767101 := bbase (se 3 (by rfl) ⟨331331, by rfl⟩ : syracuseStep 1767101 = 662663) (by norm_num)
theorem B1324741 : Blo 1176405 1324741 := bbase (se 4 (by rfl) ⟨124194, by rfl⟩ : syracuseStep 1324741 = 248389) (by norm_num)
theorem B1988293 : Blo 1176405 1988293 := bbase (se 4 (by rfl) ⟨186402, by rfl⟩ : syracuseStep 1988293 = 372805) (by norm_num)
theorem B1767125 : Blo 1176405 1767125 := bbase (se 7 (by rfl) ⟨20708, by rfl⟩ : syracuseStep 1767125 = 41417) (by norm_num)
theorem B1324777 : Blo 1176405 1324777 := bbase (se 2 (by rfl) ⟨496791, by rfl⟩ : syracuseStep 1324777 = 993583) (by norm_num)
theorem B1767149 : Blo 1176405 1767149 := bbase (se 3 (by rfl) ⟨331340, by rfl⟩ : syracuseStep 1767149 = 662681) (by norm_num)
theorem B1767173 : Blo 1176405 1767173 := bbase (se 4 (by rfl) ⟨165672, by rfl⟩ : syracuseStep 1767173 = 331345) (by norm_num)
theorem B1324813 : Blo 1176405 1324813 := bbase (se 3 (by rfl) ⟨248402, by rfl⟩ : syracuseStep 1324813 = 496805) (by norm_num)
theorem B2979605 : Blo 1176405 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B1767197 : Blo 1176405 1767197 := bbase (se 3 (by rfl) ⟨331349, by rfl⟩ : syracuseStep 1767197 = 662699) (by norm_num)
theorem B1988381 : Blo 1176405 1988381 := bbase (se 3 (by rfl) ⟨372821, by rfl⟩ : syracuseStep 1988381 = 745643) (by norm_num)
theorem B1324849 : Blo 1176405 1324849 := bbase (se 2 (by rfl) ⟨496818, by rfl⟩ : syracuseStep 1324849 = 993637) (by norm_num)
theorem B1767221 : Blo 1176405 1767221 := bbase (se 5 (by rfl) ⟨82838, by rfl⟩ : syracuseStep 1767221 = 165677) (by norm_num)
theorem B1677133 : Blo 1176405 1677133 := bbase (se 3 (by rfl) ⟨314462, by rfl⟩ : syracuseStep 1677133 = 628925) (by norm_num)
theorem B1767245 : Blo 1176405 1767245 := bbase (se 3 (by rfl) ⟨331358, by rfl⟩ : syracuseStep 1767245 = 662717) (by norm_num)
theorem B1324885 : Blo 1176405 1324885 := bbase (se 9 (by rfl) ⟨3881, by rfl⟩ : syracuseStep 1324885 = 7763) (by norm_num)
theorem B1767269 : Blo 1176405 1767269 := bbase (se 4 (by rfl) ⟨165681, by rfl⟩ : syracuseStep 1767269 = 331363) (by norm_num)
theorem B1324921 : Blo 1176405 1324921 := bbase (se 2 (by rfl) ⟨496845, by rfl⟩ : syracuseStep 1324921 = 993691) (by norm_num)
theorem B1767293 : Blo 1176405 1767293 := bbase (se 3 (by rfl) ⟨331367, by rfl⟩ : syracuseStep 1767293 = 662735) (by norm_num)
theorem B1767317 : Blo 1176405 1767317 := bbase (se 6 (by rfl) ⟨41421, by rfl⟩ : syracuseStep 1767317 = 82843) (by norm_num)
theorem B1324957 : Blo 1176405 1324957 := bbase (se 3 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 1324957 = 496859) (by norm_num)
theorem B1988509 : Blo 1176405 1988509 := bbase (se 3 (by rfl) ⟨372845, by rfl⟩ : syracuseStep 1988509 = 745691) (by norm_num)
theorem B1767341 : Blo 1176405 1767341 := bbase (se 3 (by rfl) ⟨331376, by rfl⟩ : syracuseStep 1767341 = 662753) (by norm_num)
theorem B3970997 : Blo 1176405 3970997 := bbase (se 5 (by rfl) ⟨186140, by rfl⟩ : syracuseStep 3970997 = 372281) (by norm_num)
theorem B2512829 : Blo 1176405 2512829 := bbase (se 3 (by rfl) ⟨471155, by rfl⟩ : syracuseStep 2512829 = 942311) (by norm_num)
theorem B1324993 : Blo 1176405 1324993 := bbase (se 2 (by rfl) ⟨496872, by rfl⟩ : syracuseStep 1324993 = 993745) (by norm_num)
theorem B1767365 : Blo 1176405 1767365 := bbase (se 4 (by rfl) ⟨165690, by rfl⟩ : syracuseStep 1767365 = 331381) (by norm_num)
theorem B2234317 : Blo 1176405 2234317 := bbase (se 3 (by rfl) ⟨418934, by rfl⟩ : syracuseStep 2234317 = 837869) (by norm_num)
theorem B1767389 : Blo 1176405 1767389 := bbase (se 3 (by rfl) ⟨331385, by rfl⟩ : syracuseStep 1767389 = 662771) (by norm_num)
theorem B1325029 : Blo 1176405 1325029 := bbase (se 4 (by rfl) ⟨124221, by rfl⟩ : syracuseStep 1325029 = 248443) (by norm_num)
theorem B1767413 : Blo 1176405 1767413 := bbase (se 5 (by rfl) ⟨82847, by rfl⟩ : syracuseStep 1767413 = 165695) (by norm_num)
theorem B5027845 : Blo 1176405 5027845 := bbase (se 4 (by rfl) ⟨471360, by rfl⟩ : syracuseStep 5027845 = 942721) (by norm_num)
theorem B1325065 : Blo 1176405 1325065 := bbase (se 2 (by rfl) ⟨496899, by rfl⟩ : syracuseStep 1325065 = 993799) (by norm_num)
theorem B1767437 : Blo 1176405 1767437 := bbase (se 3 (by rfl) ⟨331394, by rfl⟩ : syracuseStep 1767437 = 662789) (by norm_num)
theorem B10065941 : Blo 1176405 10065941 := bbase (se 6 (by rfl) ⟨235920, by rfl⟩ : syracuseStep 10065941 = 471841) (by norm_num)
theorem B4470821 : Blo 1176405 4470821 := bbase (se 4 (by rfl) ⟨419139, by rfl⟩ : syracuseStep 4470821 = 838279) (by norm_num)
theorem B1767461 : Blo 1176405 1767461 := bbase (se 4 (by rfl) ⟨165699, by rfl⟩ : syracuseStep 1767461 = 331399) (by norm_num)
theorem B1488937 : Blo 1176405 1488937 := bbase (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) (by norm_num)
theorem B1325101 : Blo 1176405 1325101 := bbase (se 3 (by rfl) ⟨248456, by rfl⟩ : syracuseStep 1325101 = 496913) (by norm_num)
theorem B1767485 : Blo 1176405 1767485 := bbase (se 3 (by rfl) ⟨331403, by rfl⟩ : syracuseStep 1767485 = 662807) (by norm_num)
theorem B1325137 : Blo 1176405 1325137 := bbase (se 2 (by rfl) ⟨496926, by rfl⟩ : syracuseStep 1325137 = 993853) (by norm_num)
theorem B22632533 : Blo 1176405 22632533 := bbase (se 8 (by rfl) ⟨132612, by rfl⟩ : syracuseStep 22632533 = 265225) (by norm_num)
theorem B1767509 : Blo 1176405 1767509 := bbase (se 8 (by rfl) ⟨10356, by rfl⟩ : syracuseStep 1767509 = 20713) (by norm_num)
theorem B2234461 : Blo 1176405 2234461 := bbase (se 3 (by rfl) ⟨418961, by rfl⟩ : syracuseStep 2234461 = 837923) (by norm_num)
theorem B1194085 : Blo 1176405 1194085 := bbase (se 4 (by rfl) ⟨111945, by rfl⟩ : syracuseStep 1194085 = 223891) (by norm_num)
theorem B2979949 : Blo 1176405 2979949 := bbase (se 3 (by rfl) ⟨558740, by rfl⟩ : syracuseStep 2979949 = 1117481) (by norm_num)
theorem B1767533 : Blo 1176405 1767533 := bbase (se 3 (by rfl) ⟨331412, by rfl⟩ : syracuseStep 1767533 = 662825) (by norm_num)
theorem B1325173 : Blo 1176405 1325173 := bbase (se 5 (by rfl) ⟨62117, by rfl⟩ : syracuseStep 1325173 = 124235) (by norm_num)
theorem B1767557 : Blo 1176405 1767557 := bbase (se 4 (by rfl) ⟨165708, by rfl⟩ : syracuseStep 1767557 = 331417) (by norm_num)
theorem B1489033 : Blo 1176405 1489033 := bbase (se 2 (by rfl) ⟨558387, by rfl⟩ : syracuseStep 1489033 = 1116775) (by norm_num)
theorem B10057877 : Blo 1176405 10057877 := bbase (se 6 (by rfl) ⟨235731, by rfl⟩ : syracuseStep 10057877 = 471463) (by norm_num)
theorem B1325209 : Blo 1176405 1325209 := bbase (se 2 (by rfl) ⟨496953, by rfl⟩ : syracuseStep 1325209 = 993907) (by norm_num)
theorem B1767581 : Blo 1176405 1767581 := bbase (se 3 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 1767581 = 662843) (by norm_num)
theorem B1767605 : Blo 1176405 1767605 := bbase (se 5 (by rfl) ⟨82856, by rfl⟩ : syracuseStep 1767605 = 165713) (by norm_num)
theorem B1325245 : Blo 1176405 1325245 := bbase (se 3 (by rfl) ⟨248483, by rfl⟩ : syracuseStep 1325245 = 496967) (by norm_num)
theorem B4774085 : Blo 1176405 4774085 := bbase (se 4 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 4774085 = 895141) (by norm_num)
theorem B2980061 : Blo 1176405 2980061 := bbase (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) (by norm_num)
theorem B1415389 : Blo 1176405 1415389 := bbase (se 3 (by rfl) ⟨265385, by rfl⟩ : syracuseStep 1415389 = 530771) (by norm_num)
theorem B1325281 : Blo 1176405 1325281 := bbase (se 2 (by rfl) ⟨496980, by rfl⟩ : syracuseStep 1325281 = 993961) (by norm_num)
theorem B2234621 : Blo 1176405 2234621 := bbase (se 3 (by rfl) ⟨418991, by rfl⟩ : syracuseStep 2234621 = 837983) (by norm_num)
theorem B1325317 : Blo 1176405 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B1325353 : Blo 1176405 1325353 := bbase (se 2 (by rfl) ⟨497007, by rfl⟩ : syracuseStep 1325353 = 994015) (by norm_num)
theorem B2513197 : Blo 1176405 2513197 := bbase (se 3 (by rfl) ⟨471224, by rfl⟩ : syracuseStep 2513197 = 942449) (by norm_num)
theorem B1489205 : Blo 1176405 1489205 := bbase (se 5 (by rfl) ⟨69806, by rfl⟩ : syracuseStep 1489205 = 139613) (by norm_num)
theorem B2013493 : Blo 1176405 2013493 := bbase (se 5 (by rfl) ⟨94382, by rfl⟩ : syracuseStep 2013493 = 188765) (by norm_num)
theorem B4471109 : Blo 1176405 4471109 := bbase (se 4 (by rfl) ⟨419166, by rfl⟩ : syracuseStep 4471109 = 838333) (by norm_num)
theorem B1325389 : Blo 1176405 1325389 := bbase (se 3 (by rfl) ⟨248510, by rfl⟩ : syracuseStep 1325389 = 497021) (by norm_num)
theorem B3971429 : Blo 1176405 3971429 := bbase (se 4 (by rfl) ⟨372321, by rfl⟩ : syracuseStep 3971429 = 744643) (by norm_num)
theorem B5962085 : Blo 1176405 5962085 := bbase (se 4 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 5962085 = 1117891) (by norm_num)
theorem B1489261 : Blo 1176405 1489261 := bbase (se 3 (by rfl) ⟨279236, by rfl⟩ : syracuseStep 1489261 = 558473) (by norm_num)
theorem B1325425 : Blo 1176405 1325425 := bbase (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) (by norm_num)
theorem B7649653 : Blo 1176405 7649653 := bbase (se 5 (by rfl) ⟨358577, by rfl⟩ : syracuseStep 7649653 = 717155) (by norm_num)
theorem B2234765 : Blo 1176405 2234765 := bbase (se 3 (by rfl) ⟨419018, by rfl⟩ : syracuseStep 2234765 = 838037) (by norm_num)
theorem B1325461 : Blo 1176405 1325461 := bbase (se 6 (by rfl) ⟨31065, by rfl⟩ : syracuseStep 1325461 = 62131) (by norm_num)
theorem B2980253 : Blo 1176405 2980253 := bbase (se 3 (by rfl) ⟨558797, by rfl⟩ : syracuseStep 2980253 = 1117595) (by norm_num)
theorem B1325497 : Blo 1176405 1325497 := bbase (se 2 (by rfl) ⟨497061, by rfl⟩ : syracuseStep 1325497 = 994123) (by norm_num)
theorem B1489357 : Blo 1176405 1489357 := bbase (se 3 (by rfl) ⟨279254, by rfl⟩ : syracuseStep 1489357 = 558509) (by norm_num)
theorem B1194445 : Blo 1176405 1194445 := bbase (se 3 (by rfl) ⟨223958, by rfl⟩ : syracuseStep 1194445 = 447917) (by norm_num)
theorem B1325533 : Blo 1176405 1325533 := bbase (se 3 (by rfl) ⟨248537, by rfl⟩ : syracuseStep 1325533 = 497075) (by norm_num)
theorem B1325569 : Blo 1176405 1325569 := bbase (se 2 (by rfl) ⟨497088, by rfl⟩ : syracuseStep 1325569 = 994177) (by norm_num)
theorem B1325605 : Blo 1176405 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B1325641 : Blo 1176405 1325641 := bbase (se 2 (by rfl) ⟨497115, by rfl⟩ : syracuseStep 1325641 = 994231) (by norm_num)
theorem B1325677 : Blo 1176405 1325677 := bbase (se 3 (by rfl) ⟨248564, by rfl⟩ : syracuseStep 1325677 = 497129) (by norm_num)
theorem B1489529 : Blo 1176405 1489529 := bbase (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) (by norm_num)
theorem B2865797 : Blo 1176405 2865797 := bbase (se 4 (by rfl) ⟨268668, by rfl⟩ : syracuseStep 2865797 = 537337) (by norm_num)
theorem B2235053 : Blo 1176405 2235053 := bbase (se 3 (by rfl) ⟨419072, by rfl⟩ : syracuseStep 2235053 = 838145) (by norm_num)
theorem B1489585 : Blo 1176405 1489585 := bbase (se 2 (by rfl) ⟨558594, by rfl⟩ : syracuseStep 1489585 = 1117189) (by norm_num)
theorem B6707893 : Blo 1176405 6707893 := bbase (se 5 (by rfl) ⟨314432, by rfl⟩ : syracuseStep 6707893 = 628865) (by norm_num)
theorem B5028581 : Blo 1176405 5028581 := bbase (se 4 (by rfl) ⟨471429, by rfl⟩ : syracuseStep 5028581 = 942859) (by norm_num)
theorem B2980597 : Blo 1176405 2980597 := bbase (se 5 (by rfl) ⟨139715, by rfl⟩ : syracuseStep 2980597 = 279431) (by norm_num)
theorem B1489681 : Blo 1176405 1489681 := bbase (se 2 (by rfl) ⟨558630, by rfl⟩ : syracuseStep 1489681 = 1117261) (by norm_num)
theorem B3971861 : Blo 1176405 3971861 := bbase (se 6 (by rfl) ⟨93090, by rfl⟩ : syracuseStep 3971861 = 186181) (by norm_num)
theorem B2235205 : Blo 1176405 2235205 := bbase (se 4 (by rfl) ⟨209550, by rfl⟩ : syracuseStep 2235205 = 419101) (by norm_num)
theorem B61193045 : Blo 1176405 61193045 := bbase (se 9 (by rfl) ⟨179276, by rfl⟩ : syracuseStep 61193045 = 358553) (by norm_num)
theorem B2980709 : Blo 1176405 2980709 := bbase (se 4 (by rfl) ⟨279441, by rfl⟩ : syracuseStep 2980709 = 558883) (by norm_num)
theorem B7650229 : Blo 1176405 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B2866109 : Blo 1176405 2866109 := bbase (se 3 (by rfl) ⟨537395, by rfl⟩ : syracuseStep 2866109 = 1074791) (by norm_num)
theorem B1489853 : Blo 1176405 1489853 := bbase (se 3 (by rfl) ⟨279347, by rfl⟩ : syracuseStep 1489853 = 558695) (by norm_num)
theorem B1489909 : Blo 1176405 1489909 := bbase (se 5 (by rfl) ⟨69839, by rfl⟩ : syracuseStep 1489909 = 139679) (by norm_num)
theorem B2980901 : Blo 1176405 2980901 := bbase (se 4 (by rfl) ⟨279459, by rfl⟩ : syracuseStep 2980901 = 558919) (by norm_num)
theorem B1490005 : Blo 1176405 1490005 := bbase (se 8 (by rfl) ⟨8730, by rfl⟩ : syracuseStep 1490005 = 17461) (by norm_num)
theorem B2235509 : Blo 1176405 2235509 := bbase (se 5 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 2235509 = 209579) (by norm_num)
theorem B1432733 : Blo 1176405 1432733 := bbase (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) (by norm_num)
theorem B3972293 : Blo 1176405 3972293 := bbase (se 4 (by rfl) ⟨372402, by rfl⟩ : syracuseStep 3972293 = 744805) (by norm_num)
theorem B2866421 : Blo 1176405 2866421 := bbase (se 5 (by rfl) ⟨134363, by rfl⟩ : syracuseStep 2866421 = 268727) (by norm_num)
theorem B1490177 : Blo 1176405 1490177 := bbase (se 2 (by rfl) ⟨558816, by rfl⟩ : syracuseStep 1490177 = 1117633) (by norm_num)
theorem B1490233 : Blo 1176405 1490233 := bbase (se 2 (by rfl) ⟨558837, by rfl⟩ : syracuseStep 1490233 = 1117675) (by norm_num)
theorem B2981245 : Blo 1176405 2981245 := bbase (se 3 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 2981245 = 1117967) (by norm_num)
theorem B1490329 : Blo 1176405 1490329 := bbase (se 2 (by rfl) ⟨558873, by rfl⟩ : syracuseStep 1490329 = 1117747) (by norm_num)
theorem B4472293 : Blo 1176405 4472293 := bbase (se 4 (by rfl) ⟨419277, by rfl⟩ : syracuseStep 4472293 = 838555) (by norm_num)
theorem B2981357 : Blo 1176405 2981357 := bbase (se 3 (by rfl) ⟨559004, by rfl⟩ : syracuseStep 2981357 = 1118009) (by norm_num)
theorem B1490501 : Blo 1176405 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B3972725 : Blo 1176405 3972725 := bbase (se 5 (by rfl) ⟨186221, by rfl⟩ : syracuseStep 3972725 = 372443) (by norm_num)
theorem B5963381 : Blo 1176405 5963381 := bbase (se 5 (by rfl) ⟨279533, by rfl⟩ : syracuseStep 5963381 = 559067) (by norm_num)
theorem B1490557 : Blo 1176405 1490557 := bbase (se 3 (by rfl) ⟨279479, by rfl⟩ : syracuseStep 1490557 = 558959) (by norm_num)
theorem B2981549 : Blo 1176405 2981549 := bbase (se 3 (by rfl) ⟨559040, by rfl⟩ : syracuseStep 2981549 = 1118081) (by norm_num)
theorem B1490653 : Blo 1176405 1490653 := bbase (se 3 (by rfl) ⟨279497, by rfl⟩ : syracuseStep 1490653 = 558995) (by norm_num)
theorem B2514701 : Blo 1176405 2514701 := bbase (se 3 (by rfl) ⟨471506, by rfl⟩ : syracuseStep 2514701 = 943013) (by norm_num)
theorem B4472597 : Blo 1176405 4472597 := bbase (se 6 (by rfl) ⟨104826, by rfl⟩ : syracuseStep 4472597 = 209653) (by norm_num)
theorem B2236261 : Blo 1176405 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B1490825 : Blo 1176405 1490825 := bbase (se 2 (by rfl) ⟨559059, by rfl⟩ : syracuseStep 1490825 = 1118119) (by norm_num)
theorem B2514845 : Blo 1176405 2514845 := bbase (se 3 (by rfl) ⟨471533, by rfl⟩ : syracuseStep 2514845 = 943067) (by norm_num)
theorem B1490881 : Blo 1176405 1490881 := bbase (se 2 (by rfl) ⟨559080, by rfl⟩ : syracuseStep 1490881 = 1118161) (by norm_num)
theorem B2236405 : Blo 1176405 2236405 := bbase (se 5 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 2236405 = 209663) (by norm_num)
theorem B2515043 : Blo 1176405 2515043 := bstep (se 1 (by rfl) ⟨1886282, by rfl⟩ : syracuseStep 2515043 = 3772565) B3772565
theorem B1491043 : Blo 1176405 1491043 := bstep (se 1 (by rfl) ⟨1118282, by rfl⟩ : syracuseStep 1491043 = 2236565) B2236565
theorem B3973265 : Blo 1176405 3973265 := bstep (se 2 (by rfl) ⟨1489974, by rfl⟩ : syracuseStep 3973265 = 2979949) B2979949
theorem B1491139 : Blo 1176405 1491139 := bstep (se 1 (by rfl) ⟨1118354, by rfl⟩ : syracuseStep 1491139 = 2236709) B2236709
theorem B2515153 : Blo 1176405 2515153 := bstep (se 2 (by rfl) ⟨943182, by rfl⟩ : syracuseStep 2515153 = 1886365) B1886365
theorem B32219363 : Blo 1176405 32219363 := bstep (se 1 (by rfl) ⟨24164522, by rfl⟩ : syracuseStep 32219363 = 48329045) B48329045
theorem B5030221 : Blo 1176405 5030221 := bstep (se 3 (by rfl) ⟨943166, by rfl⟩ : syracuseStep 5030221 = 1886333) B1886333
theorem B8053091 : Blo 1176405 8053091 := bstep (se 1 (by rfl) ⟨6039818, by rfl⟩ : syracuseStep 8053091 = 12079637) B12079637
theorem B3350929 : Blo 1176405 3350929 := bstep (se 2 (by rfl) ⟨1256598, by rfl⟩ : syracuseStep 3350929 = 2513197) B2513197
theorem B4473251 : Blo 1176405 4473251 := bstep (se 1 (by rfl) ⟨3354938, by rfl⟩ : syracuseStep 4473251 = 6709877) B6709877
theorem B4473265 : Blo 1176405 4473265 := bstep (se 2 (by rfl) ⟨1677474, by rfl⟩ : syracuseStep 4473265 = 3354949) B3354949
theorem B10199537 : Blo 1176405 10199537 := bstep (se 2 (by rfl) ⟨3824826, by rfl⟩ : syracuseStep 10199537 = 7649653) B7649653
theorem B5448227 : Blo 1176405 5448227 := bstep (se 1 (by rfl) ⟨4086170, by rfl⟩ : syracuseStep 5448227 = 8172341) B8172341
theorem B3351203 : Blo 1176405 3351203 := bstep (se 1 (by rfl) ⟨2513402, by rfl⟩ : syracuseStep 3351203 = 5026805) B5026805
theorem B3973805 : Blo 1176405 3973805 := bstep (se 3 (by rfl) ⟨745088, by rfl⟩ : syracuseStep 3973805 = 1490177) B1490177
theorem B3973859 : Blo 1176405 3973859 := bstep (se 1 (by rfl) ⟨2980394, by rfl⟩ : syracuseStep 3973859 = 5960789) B5960789
theorem B5964515 : Blo 1176405 5964515 := bstep (se 1 (by rfl) ⟨4473386, by rfl⟩ : syracuseStep 5964515 = 8946773) B8946773
theorem B8487665 : Blo 1176405 8487665 := bstep (se 2 (by rfl) ⟨3182874, by rfl⟩ : syracuseStep 8487665 = 6365749) B6365749
theorem B51602197 : Blo 1176405 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B3351395 : Blo 1176405 3351395 := bstep (se 1 (by rfl) ⟨2513546, by rfl⟩ : syracuseStep 3351395 = 5027093) B5027093
theorem B5235619 : Blo 1176405 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B5030819 : Blo 1176405 5030819 := bstep (se 1 (by rfl) ⟨3773114, by rfl⟩ : syracuseStep 5030819 = 7546229) B7546229
theorem B2122723 : Blo 1176405 2122723 := bstep (se 1 (by rfl) ⟨1592042, by rfl⟩ : syracuseStep 2122723 = 3184085) B3184085
theorem B2647025 : Blo 1176405 2647025 := bstep (se 2 (by rfl) ⟨992634, by rfl⟩ : syracuseStep 2647025 = 1985269) B1985269
theorem B3974129 : Blo 1176405 3974129 := bstep (se 2 (by rfl) ⟨1490298, by rfl⟩ : syracuseStep 3974129 = 2980597) B2980597
theorem B2647043 : Blo 1176405 2647043 := bstep (se 1 (by rfl) ⟨1985282, by rfl⟩ : syracuseStep 2647043 = 3970565) B3970565
theorem B7545869 : Blo 1176405 7545869 := bstep (se 3 (by rfl) ⟨1414850, by rfl⟩ : syracuseStep 7545869 = 2829701) B2829701
theorem B10200305 : Blo 1176405 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B2647313 : Blo 1176405 2647313 := bstep (se 2 (by rfl) ⟨992742, by rfl⟩ : syracuseStep 2647313 = 1985485) B1985485
theorem B2647331 : Blo 1176405 2647331 := bstep (se 1 (by rfl) ⟨1985498, by rfl⟩ : syracuseStep 2647331 = 3970997) B3970997
theorem B1721683 : Blo 1176405 1721683 := bstep (se 1 (by rfl) ⟨1291262, by rfl⟩ : syracuseStep 1721683 = 2582525) B2582525
theorem B6710627 : Blo 1176405 6710627 := bstep (se 1 (by rfl) ⟨5032970, by rfl⟩ : syracuseStep 6710627 = 10065941) B10065941
theorem B1590691 : Blo 1176405 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B4244899 : Blo 1176405 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B2123185 : Blo 1176405 2123185 := bstep (se 2 (by rfl) ⟨796194, by rfl⟩ : syracuseStep 2123185 = 1592389) B1592389
theorem B3974669 : Blo 1176405 3974669 := bstep (se 3 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 3974669 = 1490501) B1490501
theorem B5965325 : Blo 1176405 5965325 := bstep (se 3 (by rfl) ⟨1118498, by rfl⟩ : syracuseStep 5965325 = 2236997) B2236997
theorem B2647601 : Blo 1176405 2647601 := bstep (se 2 (by rfl) ⟨992850, by rfl⟩ : syracuseStep 2647601 = 1985701) B1985701
theorem B2647619 : Blo 1176405 2647619 := bstep (se 1 (by rfl) ⟨1985714, by rfl⟩ : syracuseStep 2647619 = 3971429) B3971429
theorem B3974723 : Blo 1176405 3974723 := bstep (se 1 (by rfl) ⟨2981042, by rfl⟩ : syracuseStep 3974723 = 5962085) B5962085
theorem B5441165 : Blo 1176405 5441165 := bstep (se 3 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 5441165 = 2040437) B2040437
theorem B3352205 : Blo 1176405 3352205 := bstep (se 3 (by rfl) ⟨628538, by rfl⟩ : syracuseStep 3352205 = 1257077) B1257077
theorem B1910531 : Blo 1176405 1910531 := bstep (se 1 (by rfl) ⟨1432898, by rfl⟩ : syracuseStep 1910531 = 2865797) B2865797
theorem B5662477 : Blo 1176405 5662477 := bstep (se 3 (by rfl) ⟨1061714, by rfl⟩ : syracuseStep 5662477 = 2123429) B2123429
theorem B2385713 : Blo 1176405 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B3352387 : Blo 1176405 3352387 := bstep (se 1 (by rfl) ⟨2514290, by rfl⟩ : syracuseStep 3352387 = 5028581) B5028581
theorem B2647889 : Blo 1176405 2647889 := bstep (se 2 (by rfl) ⟨992958, by rfl⟩ : syracuseStep 2647889 = 1985917) B1985917
theorem B3974993 : Blo 1176405 3974993 := bstep (se 2 (by rfl) ⟨1490622, by rfl⟩ : syracuseStep 3974993 = 2981245) B2981245
theorem B2647907 : Blo 1176405 2647907 := bstep (se 1 (by rfl) ⟨1985930, by rfl⟩ : syracuseStep 2647907 = 3971861) B3971861
theorem B3180593 : Blo 1176405 3180593 := bstep (se 2 (by rfl) ⟨1192722, by rfl⟩ : syracuseStep 3180593 = 2385445) B2385445
theorem B4466765 : Blo 1176405 4466765 := bstep (se 3 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 4466765 = 1675037) B1675037
theorem B2648177 : Blo 1176405 2648177 := bstep (se 2 (by rfl) ⟨993066, by rfl⟩ : syracuseStep 2648177 = 1986133) B1986133
theorem B2648195 : Blo 1176405 2648195 := bstep (se 1 (by rfl) ⟨1986146, by rfl⟩ : syracuseStep 2648195 = 3972293) B3972293
theorem B1886339 : Blo 1176405 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B7260293 : Blo 1176405 7260293 := bstep (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) B1361305
theorem B3180689 : Blo 1176405 3180689 := bstep (se 2 (by rfl) ⟨1192758, by rfl⟩ : syracuseStep 3180689 = 2385517) B2385517
theorem B1910947 : Blo 1176405 1910947 := bstep (se 1 (by rfl) ⟨1433210, by rfl⟩ : syracuseStep 1910947 = 2866421) B2866421
theorem B5957873 : Blo 1176405 5957873 := bstep (se 2 (by rfl) ⟨2234202, by rfl⟩ : syracuseStep 5957873 = 4468405) B4468405
theorem B3352877 : Blo 1176405 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B3975533 : Blo 1176405 3975533 := bstep (se 3 (by rfl) ⟨745412, by rfl⟩ : syracuseStep 3975533 = 1490825) B1490825
theorem B2648465 : Blo 1176405 2648465 := bstep (se 2 (by rfl) ⟨993174, by rfl⟩ : syracuseStep 2648465 = 1986349) B1986349
theorem B2648483 : Blo 1176405 2648483 := bstep (se 1 (by rfl) ⟨1986362, by rfl⟩ : syracuseStep 2648483 = 3972725) B3972725
theorem B3975587 : Blo 1176405 3975587 := bstep (se 1 (by rfl) ⟨2981690, by rfl⟩ : syracuseStep 3975587 = 5963381) B5963381
theorem B3770833 : Blo 1176405 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B1591859 : Blo 1176405 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B6703793 : Blo 1176405 6703793 := bstep (se 2 (by rfl) ⟨2513922, by rfl⟩ : syracuseStep 6703793 = 5027845) B5027845
theorem B2648753 : Blo 1176405 2648753 := bstep (se 2 (by rfl) ⟨993282, by rfl⟩ : syracuseStep 2648753 = 1986565) B1986565
theorem B3975857 : Blo 1176405 3975857 := bstep (se 2 (by rfl) ⟨1490946, by rfl⟩ : syracuseStep 3975857 = 2981893) B2981893
theorem B2648771 : Blo 1176405 2648771 := bstep (se 1 (by rfl) ⟨1986578, by rfl⟩ : syracuseStep 2648771 = 3973157) B3973157
theorem B1985249 : Blo 1176405 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B1985377 : Blo 1176405 1985377 := bstep (se 2 (by rfl) ⟨744516, by rfl⟩ : syracuseStep 1985377 = 1489033) B1489033
theorem B1985411 : Blo 1176405 1985411 := bstep (se 1 (by rfl) ⟨1489058, by rfl⟩ : syracuseStep 1985411 = 2978117) B2978117
theorem B4025219 : Blo 1176405 4025219 := bstep (se 1 (by rfl) ⟨3018914, by rfl⟩ : syracuseStep 4025219 = 6037829) B6037829
theorem B1698769 : Blo 1176405 1698769 := bstep (se 2 (by rfl) ⟨637038, by rfl⟩ : syracuseStep 1698769 = 1274077) B1274077
theorem B2649041 : Blo 1176405 2649041 := bstep (se 2 (by rfl) ⟨993390, by rfl⟩ : syracuseStep 2649041 = 1986781) B1986781
theorem B1887185 : Blo 1176405 1887185 := bstep (se 2 (by rfl) ⟨707694, by rfl⟩ : syracuseStep 1887185 = 1415389) B1415389
theorem B2649059 : Blo 1176405 2649059 := bstep (se 1 (by rfl) ⟨1986794, by rfl⟩ : syracuseStep 2649059 = 3973589) B3973589
theorem B3582947 : Blo 1176405 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B1985539 : Blo 1176405 1985539 := bstep (se 1 (by rfl) ⟨1489154, by rfl⟩ : syracuseStep 1985539 = 2978309) B2978309
theorem B1256483 : Blo 1176405 1256483 := bstep (se 1 (by rfl) ⟨942362, by rfl⟩ : syracuseStep 1256483 = 1884725) B1884725
theorem B13593653 : Blo 1176405 13593653 := bstep (se 5 (by rfl) ⟨637202, by rfl⟩ : syracuseStep 13593653 = 1274405) B1274405
theorem B3820621 : Blo 1176405 3820621 := bstep (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) B1432733
theorem B1985681 : Blo 1176405 1985681 := bstep (se 2 (by rfl) ⟨744630, by rfl⟩ : syracuseStep 1985681 = 1489261) B1489261
theorem B6368453 : Blo 1176405 6368453 := bstep (se 4 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 6368453 = 1194085) B1194085
theorem B3976397 : Blo 1176405 3976397 := bstep (se 3 (by rfl) ⟨745574, by rfl⟩ : syracuseStep 3976397 = 1491149) B1491149
theorem B3181805 : Blo 1176405 3181805 := bstep (se 3 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 3181805 = 1193177) B1193177
theorem B2649329 : Blo 1176405 2649329 := bstep (se 2 (by rfl) ⟨993498, by rfl⟩ : syracuseStep 2649329 = 1986997) B1986997
theorem B1764611 : Blo 1176405 1764611 := bstep (se 1 (by rfl) ⟨1323458, by rfl⟩ : syracuseStep 1764611 = 2646917) B2646917
theorem B2649347 : Blo 1176405 2649347 := bstep (se 1 (by rfl) ⟨1987010, by rfl⟩ : syracuseStep 2649347 = 3974021) B3974021
theorem B3976451 : Blo 1176405 3976451 := bstep (se 1 (by rfl) ⟨2982338, by rfl⟩ : syracuseStep 3976451 = 5964677) B5964677
theorem B1985809 : Blo 1176405 1985809 := bstep (se 2 (by rfl) ⟨744678, by rfl⟩ : syracuseStep 1985809 = 1489357) B1489357
theorem B1764641 : Blo 1176405 1764641 := bstep (se 2 (by rfl) ⟨661740, by rfl⟩ : syracuseStep 1764641 = 1323481) B1323481
theorem B7154993 : Blo 1176405 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B1764659 : Blo 1176405 1764659 := bstep (se 1 (by rfl) ⟨1323494, by rfl⟩ : syracuseStep 1764659 = 2646989) B2646989
theorem B1985843 : Blo 1176405 1985843 := bstep (se 1 (by rfl) ⟨1489382, by rfl⟩ : syracuseStep 1985843 = 2978765) B2978765
theorem B1764689 : Blo 1176405 1764689 := bstep (se 2 (by rfl) ⟨661758, by rfl⟩ : syracuseStep 1764689 = 1323517) B1323517
theorem B1764707 : Blo 1176405 1764707 := bstep (se 1 (by rfl) ⟨1323530, by rfl⟩ : syracuseStep 1764707 = 2647061) B2647061
theorem B1764737 : Blo 1176405 1764737 := bstep (se 2 (by rfl) ⟨661776, by rfl⟩ : syracuseStep 1764737 = 1323553) B1323553
theorem B8940941 : Blo 1176405 8940941 := bstep (se 3 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 8940941 = 3352853) B3352853
theorem B1764755 : Blo 1176405 1764755 := bstep (se 1 (by rfl) ⟨1323566, by rfl⟩ : syracuseStep 1764755 = 2647133) B2647133
theorem B1764785 : Blo 1176405 1764785 := bstep (se 2 (by rfl) ⟨661794, by rfl⟩ : syracuseStep 1764785 = 1323589) B1323589
theorem B1985971 : Blo 1176405 1985971 := bstep (se 1 (by rfl) ⟨1489478, by rfl⟩ : syracuseStep 1985971 = 2978957) B2978957
theorem B1764803 : Blo 1176405 1764803 := bstep (se 1 (by rfl) ⟨1323602, by rfl⟩ : syracuseStep 1764803 = 2647205) B2647205
theorem B3354061 : Blo 1176405 3354061 := bstep (se 3 (by rfl) ⟨628886, by rfl⟩ : syracuseStep 3354061 = 1257773) B1257773
theorem B1764833 : Blo 1176405 1764833 := bstep (se 2 (by rfl) ⟨661812, by rfl⟩ : syracuseStep 1764833 = 1323625) B1323625
theorem B1764851 : Blo 1176405 1764851 := bstep (se 1 (by rfl) ⟨1323638, by rfl⟩ : syracuseStep 1764851 = 2647277) B2647277
theorem B7540229 : Blo 1176405 7540229 := bstep (se 4 (by rfl) ⟨706896, by rfl⟩ : syracuseStep 7540229 = 1413793) B1413793
theorem B1764881 : Blo 1176405 1764881 := bstep (se 2 (by rfl) ⟨661830, by rfl⟩ : syracuseStep 1764881 = 1323661) B1323661
theorem B2649617 : Blo 1176405 2649617 := bstep (se 2 (by rfl) ⟨993606, by rfl⟩ : syracuseStep 2649617 = 1987213) B1987213
theorem B3976721 : Blo 1176405 3976721 := bstep (se 2 (by rfl) ⟨1491270, by rfl⟩ : syracuseStep 3976721 = 2982541) B2982541
theorem B1764899 : Blo 1176405 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B2649635 : Blo 1176405 2649635 := bstep (se 1 (by rfl) ⟨1987226, by rfl⟩ : syracuseStep 2649635 = 3974453) B3974453
theorem B1764929 : Blo 1176405 1764929 := bstep (se 2 (by rfl) ⟨661848, by rfl⟩ : syracuseStep 1764929 = 1323697) B1323697
theorem B1986113 : Blo 1176405 1986113 := bstep (se 2 (by rfl) ⟨744792, by rfl⟩ : syracuseStep 1986113 = 1489585) B1489585
theorem B1764947 : Blo 1176405 1764947 := bstep (se 1 (by rfl) ⟨1323710, by rfl⟩ : syracuseStep 1764947 = 2647421) B2647421
theorem B1764977 : Blo 1176405 1764977 := bstep (se 2 (by rfl) ⟨661866, by rfl⟩ : syracuseStep 1764977 = 1323733) B1323733
theorem B1764995 : Blo 1176405 1764995 := bstep (se 1 (by rfl) ⟨1323746, by rfl⟩ : syracuseStep 1764995 = 2647493) B2647493
theorem B1765025 : Blo 1176405 1765025 := bstep (se 2 (by rfl) ⟨661884, by rfl⟩ : syracuseStep 1765025 = 1323769) B1323769
theorem B5959331 : Blo 1176405 5959331 := bstep (se 1 (by rfl) ⟨4469498, by rfl⟩ : syracuseStep 5959331 = 8938997) B8938997
theorem B2297521 : Blo 1176405 2297521 := bstep (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) B1723141
theorem B1765043 : Blo 1176405 1765043 := bstep (se 1 (by rfl) ⟨1323782, by rfl⟩ : syracuseStep 1765043 = 2647565) B2647565
theorem B1986241 : Blo 1176405 1986241 := bstep (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) B1489681
theorem B1765073 : Blo 1176405 1765073 := bstep (se 2 (by rfl) ⟨661902, by rfl⟩ : syracuseStep 1765073 = 1323805) B1323805
theorem B1765091 : Blo 1176405 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B1986275 : Blo 1176405 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B1675009 : Blo 1176405 1675009 := bstep (se 2 (by rfl) ⟨628128, by rfl⟩ : syracuseStep 1675009 = 1256257) B1256257
theorem B1765121 : Blo 1176405 1765121 := bstep (se 2 (by rfl) ⟨661920, by rfl⟩ : syracuseStep 1765121 = 1323841) B1323841
theorem B1765139 : Blo 1176405 1765139 := bstep (se 1 (by rfl) ⟨1323854, by rfl⟩ : syracuseStep 1765139 = 2647709) B2647709
theorem B3821347 : Blo 1176405 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B2830115 : Blo 1176405 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B1765169 : Blo 1176405 1765169 := bstep (se 2 (by rfl) ⟨661938, by rfl⟩ : syracuseStep 1765169 = 1323877) B1323877
theorem B2649905 : Blo 1176405 2649905 := bstep (se 2 (by rfl) ⟨993714, by rfl⟩ : syracuseStep 2649905 = 1987429) B1987429
theorem B1765187 : Blo 1176405 1765187 := bstep (se 1 (by rfl) ⟨1323890, by rfl⟩ : syracuseStep 1765187 = 2647781) B2647781
theorem B2649923 : Blo 1176405 2649923 := bstep (se 1 (by rfl) ⟨1987442, by rfl⟩ : syracuseStep 2649923 = 3974885) B3974885
theorem B1765217 : Blo 1176405 1765217 := bstep (se 2 (by rfl) ⟨661956, by rfl⟩ : syracuseStep 1765217 = 1323913) B1323913
theorem B1986403 : Blo 1176405 1986403 := bstep (se 1 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 1986403 = 2979605) B2979605
theorem B1765235 : Blo 1176405 1765235 := bstep (se 1 (by rfl) ⟨1323926, by rfl⟩ : syracuseStep 1765235 = 2647853) B2647853
theorem B1765265 : Blo 1176405 1765265 := bstep (se 2 (by rfl) ⟨661974, by rfl⟩ : syracuseStep 1765265 = 1323949) B1323949
theorem B1765283 : Blo 1176405 1765283 := bstep (se 1 (by rfl) ⟨1323962, by rfl⟩ : syracuseStep 1765283 = 2647925) B2647925
theorem B1765313 : Blo 1176405 1765313 := bstep (se 2 (by rfl) ⟨661992, by rfl⟩ : syracuseStep 1765313 = 1323985) B1323985
theorem B1765331 : Blo 1176405 1765331 := bstep (se 1 (by rfl) ⟨1323998, by rfl⟩ : syracuseStep 1765331 = 2647997) B2647997
theorem B1765361 : Blo 1176405 1765361 := bstep (se 2 (by rfl) ⟨662010, by rfl⟩ : syracuseStep 1765361 = 1324021) B1324021
theorem B1986545 : Blo 1176405 1986545 := bstep (se 2 (by rfl) ⟨744954, by rfl⟩ : syracuseStep 1986545 = 1489909) B1489909
theorem B8056817 : Blo 1176405 8056817 := bstep (se 2 (by rfl) ⟨3021306, by rfl⟩ : syracuseStep 8056817 = 6042613) B6042613
theorem B1765379 : Blo 1176405 1765379 := bstep (se 1 (by rfl) ⟨1324034, by rfl⟩ : syracuseStep 1765379 = 2648069) B2648069
theorem B1257491 : Blo 1176405 1257491 := bstep (se 1 (by rfl) ⟨943118, by rfl⟩ : syracuseStep 1257491 = 1886237) B1886237
theorem B1765409 : Blo 1176405 1765409 := bstep (se 2 (by rfl) ⟨662028, by rfl⟩ : syracuseStep 1765409 = 1324057) B1324057
theorem B6983729 : Blo 1176405 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B1765427 : Blo 1176405 1765427 := bstep (se 1 (by rfl) ⟨1324070, by rfl⟩ : syracuseStep 1765427 = 2648141) B2648141
theorem B1675345 : Blo 1176405 1675345 := bstep (se 2 (by rfl) ⟨628254, by rfl⟩ : syracuseStep 1675345 = 1256509) B1256509
theorem B1765457 : Blo 1176405 1765457 := bstep (se 2 (by rfl) ⟨662046, by rfl⟩ : syracuseStep 1765457 = 1324093) B1324093
theorem B2650193 : Blo 1176405 2650193 := bstep (se 2 (by rfl) ⟨993822, by rfl⟩ : syracuseStep 2650193 = 1987645) B1987645
theorem B1765475 : Blo 1176405 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B6705251 : Blo 1176405 6705251 := bstep (se 1 (by rfl) ⟨5028938, by rfl⟩ : syracuseStep 6705251 = 10057877) B10057877
theorem B2650211 : Blo 1176405 2650211 := bstep (se 1 (by rfl) ⟨1987658, by rfl⟩ : syracuseStep 2650211 = 3975317) B3975317
theorem B1986673 : Blo 1176405 1986673 := bstep (se 2 (by rfl) ⟨745002, by rfl⟩ : syracuseStep 1986673 = 1490005) B1490005
theorem B1765505 : Blo 1176405 1765505 := bstep (se 2 (by rfl) ⟨662064, by rfl⟩ : syracuseStep 1765505 = 1324129) B1324129
theorem B3182723 : Blo 1176405 3182723 := bstep (se 1 (by rfl) ⟨2387042, by rfl⟩ : syracuseStep 3182723 = 4774085) B4774085
theorem B4468877 : Blo 1176405 4468877 := bstep (se 3 (by rfl) ⟨837914, by rfl⟩ : syracuseStep 4468877 = 1675829) B1675829
theorem B2388113 : Blo 1176405 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B1765523 : Blo 1176405 1765523 := bstep (se 1 (by rfl) ⟨1324142, by rfl⟩ : syracuseStep 1765523 = 2648285) B2648285
theorem B1986707 : Blo 1176405 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B2977955 : Blo 1176405 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B1765553 : Blo 1176405 1765553 := bstep (se 2 (by rfl) ⟨662082, by rfl⟩ : syracuseStep 1765553 = 1324165) B1324165
theorem B1765571 : Blo 1176405 1765571 := bstep (se 1 (by rfl) ⟨1324178, by rfl⟩ : syracuseStep 1765571 = 2648357) B2648357
theorem B1765601 : Blo 1176405 1765601 := bstep (se 2 (by rfl) ⟨662100, by rfl⟩ : syracuseStep 1765601 = 1324201) B1324201
theorem B1765619 : Blo 1176405 1765619 := bstep (se 1 (by rfl) ⟨1324214, by rfl⟩ : syracuseStep 1765619 = 2648429) B2648429
theorem B1765649 : Blo 1176405 1765649 := bstep (se 2 (by rfl) ⟨662118, by rfl⟩ : syracuseStep 1765649 = 1324237) B1324237
theorem B1986835 : Blo 1176405 1986835 := bstep (se 1 (by rfl) ⟨1490126, by rfl⟩ : syracuseStep 1986835 = 2980253) B2980253
theorem B1765667 : Blo 1176405 1765667 := bstep (se 1 (by rfl) ⟨1324250, by rfl⟩ : syracuseStep 1765667 = 2648501) B2648501
theorem B1765697 : Blo 1176405 1765697 := bstep (se 2 (by rfl) ⟨662136, by rfl⟩ : syracuseStep 1765697 = 1324273) B1324273
theorem B1765715 : Blo 1176405 1765715 := bstep (se 1 (by rfl) ⟨1324286, by rfl⟩ : syracuseStep 1765715 = 2648573) B2648573
theorem B2978147 : Blo 1176405 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B3772781 : Blo 1176405 3772781 := bstep (se 3 (by rfl) ⟨707396, by rfl⟩ : syracuseStep 3772781 = 1414793) B1414793
theorem B1765745 : Blo 1176405 1765745 := bstep (se 2 (by rfl) ⟨662154, by rfl⟩ : syracuseStep 1765745 = 1324309) B1324309
theorem B2650481 : Blo 1176405 2650481 := bstep (se 2 (by rfl) ⟨993930, by rfl⟩ : syracuseStep 2650481 = 1987861) B1987861
theorem B1765763 : Blo 1176405 1765763 := bstep (se 1 (by rfl) ⟨1324322, by rfl⟩ : syracuseStep 1765763 = 2648645) B2648645
theorem B2650499 : Blo 1176405 2650499 := bstep (se 1 (by rfl) ⟨1987874, by rfl⟩ : syracuseStep 2650499 = 3975749) B3975749
theorem B1814929 : Blo 1176405 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B1765793 : Blo 1176405 1765793 := bstep (se 2 (by rfl) ⟨662172, by rfl⟩ : syracuseStep 1765793 = 1324345) B1324345
theorem B1986977 : Blo 1176405 1986977 := bstep (se 2 (by rfl) ⟨745116, by rfl⟩ : syracuseStep 1986977 = 1490233) B1490233
theorem B1765811 : Blo 1176405 1765811 := bstep (se 1 (by rfl) ⟨1324358, by rfl⟩ : syracuseStep 1765811 = 2648717) B2648717
theorem B5960141 : Blo 1176405 5960141 := bstep (se 3 (by rfl) ⟨1117526, by rfl⟩ : syracuseStep 5960141 = 2235053) B2235053
theorem B1765841 : Blo 1176405 1765841 := bstep (se 2 (by rfl) ⟨662190, by rfl⟩ : syracuseStep 1765841 = 1324381) B1324381
theorem B1765859 : Blo 1176405 1765859 := bstep (se 1 (by rfl) ⟨1324394, by rfl⟩ : syracuseStep 1765859 = 2648789) B2648789
theorem B3772909 : Blo 1176405 3772909 := bstep (se 3 (by rfl) ⟨707420, by rfl⟩ : syracuseStep 3772909 = 1414841) B1414841
theorem B3355121 : Blo 1176405 3355121 := bstep (se 2 (by rfl) ⟨1258170, by rfl⟩ : syracuseStep 3355121 = 2516341) B2516341
theorem B1765889 : Blo 1176405 1765889 := bstep (se 2 (by rfl) ⟨662208, by rfl⟩ : syracuseStep 1765889 = 1324417) B1324417
theorem B1765907 : Blo 1176405 1765907 := bstep (se 1 (by rfl) ⟨1324430, by rfl⟩ : syracuseStep 1765907 = 2648861) B2648861
theorem B1987105 : Blo 1176405 1987105 := bstep (se 2 (by rfl) ⟨745164, by rfl⟩ : syracuseStep 1987105 = 1490329) B1490329
theorem B1765937 : Blo 1176405 1765937 := bstep (se 2 (by rfl) ⟨662226, by rfl⟩ : syracuseStep 1765937 = 1324453) B1324453
theorem B1323571 : Blo 1176405 1323571 := bstep (se 1 (by rfl) ⟨992678, by rfl⟩ : syracuseStep 1323571 = 1985357) B1985357
theorem B1765955 : Blo 1176405 1765955 := bstep (se 1 (by rfl) ⟨1324466, by rfl⟩ : syracuseStep 1765955 = 2648933) B2648933
theorem B1987139 : Blo 1176405 1987139 := bstep (se 1 (by rfl) ⟨1490354, by rfl⟩ : syracuseStep 1987139 = 2980709) B2980709
theorem B1765985 : Blo 1176405 1765985 := bstep (se 2 (by rfl) ⟨662244, by rfl⟩ : syracuseStep 1765985 = 1324489) B1324489
theorem B1766003 : Blo 1176405 1766003 := bstep (se 1 (by rfl) ⟨1324502, by rfl⟩ : syracuseStep 1766003 = 2649005) B2649005
theorem B5026445 : Blo 1176405 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B1766033 : Blo 1176405 1766033 := bstep (se 2 (by rfl) ⟨662262, by rfl⟩ : syracuseStep 1766033 = 1324525) B1324525
theorem B2650769 : Blo 1176405 2650769 := bstep (se 2 (by rfl) ⟨994038, by rfl⟩ : syracuseStep 2650769 = 1988077) B1988077
theorem B1675937 : Blo 1176405 1675937 := bstep (se 2 (by rfl) ⟨628476, by rfl⟩ : syracuseStep 1675937 = 1256953) B1256953
theorem B1766051 : Blo 1176405 1766051 := bstep (se 1 (by rfl) ⟨1324538, by rfl⟩ : syracuseStep 1766051 = 2649077) B2649077
theorem B2650787 : Blo 1176405 2650787 := bstep (se 1 (by rfl) ⟨1988090, by rfl⟩ : syracuseStep 2650787 = 3976181) B3976181
theorem B1766081 : Blo 1176405 1766081 := bstep (se 2 (by rfl) ⟨662280, by rfl⟩ : syracuseStep 1766081 = 1324561) B1324561
theorem B1323715 : Blo 1176405 1323715 := bstep (se 1 (by rfl) ⟨992786, by rfl⟩ : syracuseStep 1323715 = 1985573) B1985573
theorem B1987267 : Blo 1176405 1987267 := bstep (se 1 (by rfl) ⟨1490450, by rfl⟩ : syracuseStep 1987267 = 2980901) B2980901
theorem B1766099 : Blo 1176405 1766099 := bstep (se 1 (by rfl) ⟨1324574, by rfl⟩ : syracuseStep 1766099 = 2649149) B2649149
theorem B1766129 : Blo 1176405 1766129 := bstep (se 2 (by rfl) ⟨662298, by rfl⟩ : syracuseStep 1766129 = 1324597) B1324597
theorem B1766147 : Blo 1176405 1766147 := bstep (se 1 (by rfl) ⟨1324610, by rfl⟩ : syracuseStep 1766147 = 2649221) B2649221
theorem B1766177 : Blo 1176405 1766177 := bstep (se 2 (by rfl) ⟨662316, by rfl⟩ : syracuseStep 1766177 = 1324633) B1324633
theorem B1766195 : Blo 1176405 1766195 := bstep (se 1 (by rfl) ⟨1324646, by rfl⟩ : syracuseStep 1766195 = 2649293) B2649293
theorem B1766225 : Blo 1176405 1766225 := bstep (se 2 (by rfl) ⟨662334, by rfl⟩ : syracuseStep 1766225 = 1324669) B1324669
theorem B1987409 : Blo 1176405 1987409 := bstep (se 2 (by rfl) ⟨745278, by rfl⟩ : syracuseStep 1987409 = 1490557) B1490557
theorem B1323859 : Blo 1176405 1323859 := bstep (se 1 (by rfl) ⟨992894, by rfl⟩ : syracuseStep 1323859 = 1985789) B1985789
theorem B1176419 : Blo 1176405 1176419 := bstep (se 1 (by rfl) ⟨882314, by rfl⟩ : syracuseStep 1176419 = 1764629) B1764629
theorem B1766243 : Blo 1176405 1766243 := bstep (se 1 (by rfl) ⟨1324682, by rfl⟩ : syracuseStep 1766243 = 2649365) B2649365
theorem B1176435 : Blo 1176405 1176435 := bstep (se 1 (by rfl) ⟨882326, by rfl⟩ : syracuseStep 1176435 = 1764653) B1764653
theorem B1766273 : Blo 1176405 1766273 := bstep (se 2 (by rfl) ⟨662352, by rfl⟩ : syracuseStep 1766273 = 1324705) B1324705
theorem B1176451 : Blo 1176405 1176451 := bstep (se 1 (by rfl) ⟨882338, by rfl⟩ : syracuseStep 1176451 = 1764677) B1764677
theorem B1176467 : Blo 1176405 1176467 := bstep (se 1 (by rfl) ⟨882350, by rfl⟩ : syracuseStep 1176467 = 1764701) B1764701
theorem B1766291 : Blo 1176405 1766291 := bstep (se 1 (by rfl) ⟨1324718, by rfl⟩ : syracuseStep 1766291 = 2649437) B2649437
theorem B1176483 : Blo 1176405 1176483 := bstep (se 1 (by rfl) ⟨882362, by rfl⟩ : syracuseStep 1176483 = 1764725) B1764725
theorem B4469681 : Blo 1176405 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B1766321 : Blo 1176405 1766321 := bstep (se 2 (by rfl) ⟨662370, by rfl⟩ : syracuseStep 1766321 = 1324741) B1324741
theorem B1176499 : Blo 1176405 1176499 := bstep (se 1 (by rfl) ⟨882374, by rfl⟩ : syracuseStep 1176499 = 1764749) B1764749
theorem B2651057 : Blo 1176405 2651057 := bstep (se 2 (by rfl) ⟨994146, by rfl⟩ : syracuseStep 2651057 = 1988293) B1988293
theorem B1176515 : Blo 1176405 1176515 := bstep (se 1 (by rfl) ⟨882386, by rfl⟩ : syracuseStep 1176515 = 1764773) B1764773
theorem B1766339 : Blo 1176405 1766339 := bstep (se 1 (by rfl) ⟨1324754, by rfl⟩ : syracuseStep 1766339 = 2649509) B2649509
theorem B2651075 : Blo 1176405 2651075 := bstep (se 1 (by rfl) ⟨1988306, by rfl⟩ : syracuseStep 2651075 = 3976613) B3976613
theorem B1987537 : Blo 1176405 1987537 := bstep (se 2 (by rfl) ⟨745326, by rfl⟩ : syracuseStep 1987537 = 1490653) B1490653
theorem B1176531 : Blo 1176405 1176531 := bstep (se 1 (by rfl) ⟨882398, by rfl⟩ : syracuseStep 1176531 = 1764797) B1764797
theorem B1766369 : Blo 1176405 1766369 := bstep (se 2 (by rfl) ⟨662388, by rfl⟩ : syracuseStep 1766369 = 1324777) B1324777
theorem B1176547 : Blo 1176405 1176547 := bstep (se 1 (by rfl) ⟨882410, by rfl⟩ : syracuseStep 1176547 = 1764821) B1764821
theorem B1324003 : Blo 1176405 1324003 := bstep (se 1 (by rfl) ⟨993002, by rfl⟩ : syracuseStep 1324003 = 1986005) B1986005
theorem B1176563 : Blo 1176405 1176563 := bstep (se 1 (by rfl) ⟨882422, by rfl⟩ : syracuseStep 1176563 = 1764845) B1764845
theorem B1766387 : Blo 1176405 1766387 := bstep (se 1 (by rfl) ⟨1324790, by rfl⟩ : syracuseStep 1766387 = 2649581) B2649581
theorem B1987571 : Blo 1176405 1987571 := bstep (se 1 (by rfl) ⟨1490678, by rfl⟩ : syracuseStep 1987571 = 2981357) B2981357
theorem B1176579 : Blo 1176405 1176579 := bstep (se 1 (by rfl) ⟨882434, by rfl⟩ : syracuseStep 1176579 = 1764869) B1764869
theorem B1766417 : Blo 1176405 1766417 := bstep (se 2 (by rfl) ⟨662406, by rfl⟩ : syracuseStep 1766417 = 1324813) B1324813
theorem B1176595 : Blo 1176405 1176595 := bstep (se 1 (by rfl) ⟨882446, by rfl⟩ : syracuseStep 1176595 = 1764893) B1764893
theorem B1176611 : Blo 1176405 1176611 := bstep (se 1 (by rfl) ⟨882458, by rfl⟩ : syracuseStep 1176611 = 1764917) B1764917
theorem B1766435 : Blo 1176405 1766435 := bstep (se 1 (by rfl) ⟨1324826, by rfl⟩ : syracuseStep 1766435 = 2649653) B2649653
theorem B1176627 : Blo 1176405 1176627 := bstep (se 1 (by rfl) ⟨882470, by rfl⟩ : syracuseStep 1176627 = 1764941) B1764941
theorem B1766465 : Blo 1176405 1766465 := bstep (se 2 (by rfl) ⟨662424, by rfl⟩ : syracuseStep 1766465 = 1324849) B1324849
theorem B1176643 : Blo 1176405 1176643 := bstep (se 1 (by rfl) ⟨882482, by rfl⟩ : syracuseStep 1176643 = 1764965) B1764965
theorem B6370373 : Blo 1176405 6370373 := bstep (se 4 (by rfl) ⟨597222, by rfl⟩ : syracuseStep 6370373 = 1194445) B1194445
theorem B6706253 : Blo 1176405 6706253 := bstep (se 3 (by rfl) ⟨1257422, by rfl⟩ : syracuseStep 6706253 = 2514845) B2514845
theorem B1176659 : Blo 1176405 1176659 := bstep (se 1 (by rfl) ⟨882494, by rfl⟩ : syracuseStep 1176659 = 1764989) B1764989
theorem B1766483 : Blo 1176405 1766483 := bstep (se 1 (by rfl) ⟨1324862, by rfl⟩ : syracuseStep 1766483 = 2649725) B2649725
theorem B1176675 : Blo 1176405 1176675 := bstep (se 1 (by rfl) ⟨882506, by rfl⟩ : syracuseStep 1176675 = 1765013) B1765013
theorem B1766513 : Blo 1176405 1766513 := bstep (se 2 (by rfl) ⟨662442, by rfl⟩ : syracuseStep 1766513 = 1324885) B1324885
theorem B1176691 : Blo 1176405 1176691 := bstep (se 1 (by rfl) ⟨882518, by rfl⟩ : syracuseStep 1176691 = 1765037) B1765037
theorem B1324147 : Blo 1176405 1324147 := bstep (se 1 (by rfl) ⟨993110, by rfl⟩ : syracuseStep 1324147 = 1986221) B1986221
theorem B1987699 : Blo 1176405 1987699 := bstep (se 1 (by rfl) ⟨1490774, by rfl⟩ : syracuseStep 1987699 = 2981549) B2981549
theorem B1176707 : Blo 1176405 1176707 := bstep (se 1 (by rfl) ⟨882530, by rfl⟩ : syracuseStep 1176707 = 1765061) B1765061
theorem B1766531 : Blo 1176405 1766531 := bstep (se 1 (by rfl) ⟨1324898, by rfl⟩ : syracuseStep 1766531 = 2649797) B2649797
theorem B2233489 : Blo 1176405 2233489 := bstep (se 2 (by rfl) ⟨837558, by rfl⟩ : syracuseStep 2233489 = 1675117) B1675117
theorem B1176723 : Blo 1176405 1176723 := bstep (se 1 (by rfl) ⟨882542, by rfl⟩ : syracuseStep 1176723 = 1765085) B1765085
theorem B1766561 : Blo 1176405 1766561 := bstep (se 2 (by rfl) ⟨662460, by rfl⟩ : syracuseStep 1766561 = 1324921) B1324921
theorem B1176739 : Blo 1176405 1176739 := bstep (se 1 (by rfl) ⟨882554, by rfl⟩ : syracuseStep 1176739 = 1765109) B1765109
theorem B1176755 : Blo 1176405 1176755 := bstep (se 1 (by rfl) ⟨882566, by rfl⟩ : syracuseStep 1176755 = 1765133) B1765133
theorem B1676467 : Blo 1176405 1676467 := bstep (se 1 (by rfl) ⟨1257350, by rfl⟩ : syracuseStep 1676467 = 2514701) B2514701
theorem B1766579 : Blo 1176405 1766579 := bstep (se 1 (by rfl) ⟨1324934, by rfl⟩ : syracuseStep 1766579 = 2649869) B2649869
theorem B1176771 : Blo 1176405 1176771 := bstep (se 1 (by rfl) ⟨882578, by rfl⟩ : syracuseStep 1176771 = 1765157) B1765157
theorem B1176787 : Blo 1176405 1176787 := bstep (se 1 (by rfl) ⟨882590, by rfl⟩ : syracuseStep 1176787 = 1765181) B1765181
theorem B1766609 : Blo 1176405 1766609 := bstep (se 2 (by rfl) ⟨662478, by rfl⟩ : syracuseStep 1766609 = 1324957) B1324957
theorem B2651345 : Blo 1176405 2651345 := bstep (se 2 (by rfl) ⟨994254, by rfl⟩ : syracuseStep 2651345 = 1988509) B1988509
theorem B1176803 : Blo 1176405 1176803 := bstep (se 1 (by rfl) ⟨882602, by rfl⟩ : syracuseStep 1176803 = 1765205) B1765205
theorem B1766627 : Blo 1176405 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B2651363 : Blo 1176405 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B1176819 : Blo 1176405 1176819 := bstep (se 1 (by rfl) ⟨882614, by rfl⟩ : syracuseStep 1176819 = 1765229) B1765229
theorem B1766657 : Blo 1176405 1766657 := bstep (se 2 (by rfl) ⟨662496, by rfl⟩ : syracuseStep 1766657 = 1324993) B1324993
theorem B1987841 : Blo 1176405 1987841 := bstep (se 2 (by rfl) ⟨745440, by rfl⟩ : syracuseStep 1987841 = 1490881) B1490881
theorem B1176835 : Blo 1176405 1176835 := bstep (se 1 (by rfl) ⟨882626, by rfl⟩ : syracuseStep 1176835 = 1765253) B1765253
theorem B1324291 : Blo 1176405 1324291 := bstep (se 1 (by rfl) ⟨993218, by rfl⟩ : syracuseStep 1324291 = 1986437) B1986437
theorem B2979089 : Blo 1176405 2979089 := bstep (se 2 (by rfl) ⟨1117158, by rfl⟩ : syracuseStep 2979089 = 2234317) B2234317
theorem B1176851 : Blo 1176405 1176851 := bstep (se 1 (by rfl) ⟨882638, by rfl⟩ : syracuseStep 1176851 = 1765277) B1765277
theorem B1766675 : Blo 1176405 1766675 := bstep (se 1 (by rfl) ⟨1325006, by rfl⟩ : syracuseStep 1766675 = 2650013) B2650013
theorem B1176867 : Blo 1176405 1176867 := bstep (se 1 (by rfl) ⟨882650, by rfl⟩ : syracuseStep 1176867 = 1765301) B1765301
theorem B2233649 : Blo 1176405 2233649 := bstep (se 2 (by rfl) ⟨837618, by rfl⟩ : syracuseStep 2233649 = 1675237) B1675237
theorem B1176883 : Blo 1176405 1176883 := bstep (se 1 (by rfl) ⟨882662, by rfl⟩ : syracuseStep 1176883 = 1765325) B1765325
theorem B1766705 : Blo 1176405 1766705 := bstep (se 2 (by rfl) ⟨662514, by rfl⟩ : syracuseStep 1766705 = 1325029) B1325029
theorem B1176899 : Blo 1176405 1176899 := bstep (se 1 (by rfl) ⟨882674, by rfl⟩ : syracuseStep 1176899 = 1765349) B1765349
theorem B2979139 : Blo 1176405 2979139 := bstep (se 1 (by rfl) ⟨2234354, by rfl⟩ : syracuseStep 2979139 = 4468709) B4468709
theorem B1766723 : Blo 1176405 1766723 := bstep (se 1 (by rfl) ⟨1325042, by rfl⟩ : syracuseStep 1766723 = 2650085) B2650085
theorem B1176915 : Blo 1176405 1176915 := bstep (se 1 (by rfl) ⟨882686, by rfl⟩ : syracuseStep 1176915 = 1765373) B1765373
theorem B1766753 : Blo 1176405 1766753 := bstep (se 2 (by rfl) ⟨662532, by rfl⟩ : syracuseStep 1766753 = 1325065) B1325065
theorem B3970403 : Blo 1176405 3970403 := bstep (se 1 (by rfl) ⟨2977802, by rfl⟩ : syracuseStep 3970403 = 5955605) B5955605
theorem B1176931 : Blo 1176405 1176931 := bstep (se 1 (by rfl) ⟨882698, by rfl⟩ : syracuseStep 1176931 = 1765397) B1765397
theorem B1176947 : Blo 1176405 1176947 := bstep (se 1 (by rfl) ⟨882710, by rfl⟩ : syracuseStep 1176947 = 1765421) B1765421
theorem B1766771 : Blo 1176405 1766771 := bstep (se 1 (by rfl) ⟨1325078, by rfl⟩ : syracuseStep 1766771 = 2650157) B2650157
theorem B1987969 : Blo 1176405 1987969 := bstep (se 2 (by rfl) ⟨745488, by rfl⟩ : syracuseStep 1987969 = 1490977) B1490977
theorem B1176963 : Blo 1176405 1176963 := bstep (se 1 (by rfl) ⟨882722, by rfl⟩ : syracuseStep 1176963 = 1765445) B1765445
theorem B2012561 : Blo 1176405 2012561 := bstep (se 2 (by rfl) ⟨754710, by rfl⟩ : syracuseStep 2012561 = 1509421) B1509421
theorem B1766801 : Blo 1176405 1766801 := bstep (se 2 (by rfl) ⟨662550, by rfl⟩ : syracuseStep 1766801 = 1325101) B1325101
theorem B1176979 : Blo 1176405 1176979 := bstep (se 1 (by rfl) ⟨882734, by rfl⟩ : syracuseStep 1176979 = 1765469) B1765469
theorem B1324435 : Blo 1176405 1324435 := bstep (se 1 (by rfl) ⟨993326, by rfl⟩ : syracuseStep 1324435 = 1986653) B1986653
theorem B1176995 : Blo 1176405 1176995 := bstep (se 1 (by rfl) ⟨882746, by rfl⟩ : syracuseStep 1176995 = 1765493) B1765493
theorem B7542179 : Blo 1176405 7542179 := bstep (se 1 (by rfl) ⟨5656634, by rfl⟩ : syracuseStep 7542179 = 11313269) B11313269
theorem B1766819 : Blo 1176405 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B1177011 : Blo 1176405 1177011 := bstep (se 1 (by rfl) ⟨882758, by rfl⟩ : syracuseStep 1177011 = 1765517) B1765517
theorem B1766849 : Blo 1176405 1766849 := bstep (se 2 (by rfl) ⟨662568, by rfl⟩ : syracuseStep 1766849 = 1325137) B1325137
theorem B1177027 : Blo 1176405 1177027 := bstep (se 1 (by rfl) ⟨882770, by rfl⟩ : syracuseStep 1177027 = 1765541) B1765541
theorem B2979281 : Blo 1176405 2979281 := bstep (se 2 (by rfl) ⟨1117230, by rfl⟩ : syracuseStep 2979281 = 2234461) B2234461
theorem B1177043 : Blo 1176405 1177043 := bstep (se 1 (by rfl) ⟨882782, by rfl⟩ : syracuseStep 1177043 = 1765565) B1765565
theorem B1766867 : Blo 1176405 1766867 := bstep (se 1 (by rfl) ⟨1325150, by rfl⟩ : syracuseStep 1766867 = 2650301) B2650301
theorem B1177059 : Blo 1176405 1177059 := bstep (se 1 (by rfl) ⟨882794, by rfl⟩ : syracuseStep 1177059 = 1765589) B1765589
theorem B1766897 : Blo 1176405 1766897 := bstep (se 2 (by rfl) ⟨662586, by rfl⟩ : syracuseStep 1766897 = 1325173) B1325173
theorem B1177075 : Blo 1176405 1177075 := bstep (se 1 (by rfl) ⟨882806, by rfl⟩ : syracuseStep 1177075 = 1765613) B1765613
theorem B1177091 : Blo 1176405 1177091 := bstep (se 1 (by rfl) ⟨882818, by rfl⟩ : syracuseStep 1177091 = 1765637) B1765637
theorem B1676803 : Blo 1176405 1676803 := bstep (se 1 (by rfl) ⟨1257602, by rfl⟩ : syracuseStep 1676803 = 2515205) B2515205
theorem B1766915 : Blo 1176405 1766915 := bstep (se 1 (by rfl) ⟨1325186, by rfl⟩ : syracuseStep 1766915 = 2650373) B2650373
theorem B4085261 : Blo 1176405 4085261 := bstep (se 3 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 4085261 = 1531973) B1531973
theorem B1177107 : Blo 1176405 1177107 := bstep (se 1 (by rfl) ⟨882830, by rfl⟩ : syracuseStep 1177107 = 1765661) B1765661
theorem B1766945 : Blo 1176405 1766945 := bstep (se 2 (by rfl) ⟨662604, by rfl⟩ : syracuseStep 1766945 = 1325209) B1325209
theorem B1177123 : Blo 1176405 1177123 := bstep (se 1 (by rfl) ⟨882842, by rfl⟩ : syracuseStep 1177123 = 1765685) B1765685
theorem B1324579 : Blo 1176405 1324579 := bstep (se 1 (by rfl) ⟨993434, by rfl⟩ : syracuseStep 1324579 = 1986869) B1986869
theorem B1988131 : Blo 1176405 1988131 := bstep (se 1 (by rfl) ⟨1491098, by rfl⟩ : syracuseStep 1988131 = 2982197) B2982197
theorem B1177139 : Blo 1176405 1177139 := bstep (se 1 (by rfl) ⟨882854, by rfl⟩ : syracuseStep 1177139 = 1765709) B1765709
theorem B1766963 : Blo 1176405 1766963 := bstep (se 1 (by rfl) ⟨1325222, by rfl⟩ : syracuseStep 1766963 = 2650445) B2650445
theorem B1177155 : Blo 1176405 1177155 := bstep (se 1 (by rfl) ⟨882866, by rfl⟩ : syracuseStep 1177155 = 1765733) B1765733
theorem B4470349 : Blo 1176405 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B1766993 : Blo 1176405 1766993 := bstep (se 2 (by rfl) ⟨662622, by rfl⟩ : syracuseStep 1766993 = 1325245) B1325245
theorem B1177171 : Blo 1176405 1177171 := bstep (se 1 (by rfl) ⟨882878, by rfl⟩ : syracuseStep 1177171 = 1765757) B1765757
theorem B1791571 : Blo 1176405 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B1177187 : Blo 1176405 1177187 := bstep (se 1 (by rfl) ⟨882890, by rfl⟩ : syracuseStep 1177187 = 1765781) B1765781
theorem B1767011 : Blo 1176405 1767011 := bstep (se 1 (by rfl) ⟨1325258, by rfl⟩ : syracuseStep 1767011 = 2650517) B2650517
theorem B12719729 : Blo 1176405 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B3970673 : Blo 1176405 3970673 := bstep (se 2 (by rfl) ⟨1489002, by rfl⟩ : syracuseStep 3970673 = 2978005) B2978005
theorem B1177203 : Blo 1176405 1177203 := bstep (se 1 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 1177203 = 1765805) B1765805
theorem B1767041 : Blo 1176405 1767041 := bstep (se 2 (by rfl) ⟨662640, by rfl⟩ : syracuseStep 1767041 = 1325281) B1325281
theorem B1177219 : Blo 1176405 1177219 := bstep (se 1 (by rfl) ⟨882914, by rfl⟩ : syracuseStep 1177219 = 1765829) B1765829
theorem B1177235 : Blo 1176405 1177235 := bstep (se 1 (by rfl) ⟨882926, by rfl⟩ : syracuseStep 1177235 = 1765853) B1765853
theorem B1767059 : Blo 1176405 1767059 := bstep (se 1 (by rfl) ⟨1325294, by rfl⟩ : syracuseStep 1767059 = 2650589) B2650589
theorem B1177251 : Blo 1176405 1177251 := bstep (se 1 (by rfl) ⟨882938, by rfl⟩ : syracuseStep 1177251 = 1765877) B1765877
theorem B7648931 : Blo 1176405 7648931 := bstep (se 1 (by rfl) ⟨5736698, by rfl⟩ : syracuseStep 7648931 = 11473397) B11473397
theorem B1767089 : Blo 1176405 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B1988273 : Blo 1176405 1988273 := bstep (se 2 (by rfl) ⟨745602, by rfl⟩ : syracuseStep 1988273 = 1491205) B1491205
theorem B1177267 : Blo 1176405 1177267 := bstep (se 1 (by rfl) ⟨882950, by rfl⟩ : syracuseStep 1177267 = 1765901) B1765901
theorem B1324723 : Blo 1176405 1324723 := bstep (se 1 (by rfl) ⟨993542, by rfl⟩ : syracuseStep 1324723 = 1987085) B1987085
theorem B2234051 : Blo 1176405 2234051 := bstep (se 1 (by rfl) ⟨1675538, by rfl⟩ : syracuseStep 2234051 = 3351077) B3351077
theorem B1177283 : Blo 1176405 1177283 := bstep (se 1 (by rfl) ⟨882962, by rfl⟩ : syracuseStep 1177283 = 1765925) B1765925
theorem B8935109 : Blo 1176405 8935109 := bstep (se 4 (by rfl) ⟨837666, by rfl⟩ : syracuseStep 8935109 = 1675333) B1675333
theorem B1767107 : Blo 1176405 1767107 := bstep (se 1 (by rfl) ⟨1325330, by rfl⟩ : syracuseStep 1767107 = 2650661) B2650661
theorem B1177299 : Blo 1176405 1177299 := bstep (se 1 (by rfl) ⟨882974, by rfl⟩ : syracuseStep 1177299 = 1765949) B1765949
theorem B1767137 : Blo 1176405 1767137 := bstep (se 2 (by rfl) ⟨662676, by rfl⟩ : syracuseStep 1767137 = 1325353) B1325353
theorem B1177315 : Blo 1176405 1177315 := bstep (se 1 (by rfl) ⟨882986, by rfl⟩ : syracuseStep 1177315 = 1765973) B1765973
theorem B2684657 : Blo 1176405 2684657 := bstep (se 2 (by rfl) ⟨1006746, by rfl⟩ : syracuseStep 2684657 = 2013493) B2013493
theorem B1177331 : Blo 1176405 1177331 := bstep (se 1 (by rfl) ⟨882998, by rfl⟩ : syracuseStep 1177331 = 1765997) B1765997
theorem B1767155 : Blo 1176405 1767155 := bstep (se 1 (by rfl) ⟨1325366, by rfl⟩ : syracuseStep 1767155 = 2650733) B2650733
theorem B1177347 : Blo 1176405 1177347 := bstep (se 1 (by rfl) ⟨883010, by rfl⟩ : syracuseStep 1177347 = 1766021) B1766021
theorem B1767185 : Blo 1176405 1767185 := bstep (se 2 (by rfl) ⟨662694, by rfl⟩ : syracuseStep 1767185 = 1325389) B1325389
theorem B1177363 : Blo 1176405 1177363 := bstep (se 1 (by rfl) ⟨883022, by rfl⟩ : syracuseStep 1177363 = 1766045) B1766045
theorem B1177379 : Blo 1176405 1177379 := bstep (se 1 (by rfl) ⟨883034, by rfl⟩ : syracuseStep 1177379 = 1766069) B1766069
theorem B1767203 : Blo 1176405 1767203 := bstep (se 1 (by rfl) ⟨1325402, by rfl⟩ : syracuseStep 1767203 = 2650805) B2650805
theorem B3626801 : Blo 1176405 3626801 := bstep (se 2 (by rfl) ⟨1360050, by rfl⟩ : syracuseStep 3626801 = 2720101) B2720101
theorem B1177395 : Blo 1176405 1177395 := bstep (se 1 (by rfl) ⟨883046, by rfl⟩ : syracuseStep 1177395 = 1766093) B1766093
theorem B1988401 : Blo 1176405 1988401 := bstep (se 2 (by rfl) ⟨745650, by rfl⟩ : syracuseStep 1988401 = 1491301) B1491301
theorem B1767233 : Blo 1176405 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B1177411 : Blo 1176405 1177411 := bstep (se 1 (by rfl) ⟨883058, by rfl⟩ : syracuseStep 1177411 = 1766117) B1766117
theorem B1324867 : Blo 1176405 1324867 := bstep (se 1 (by rfl) ⟨993650, by rfl⟩ : syracuseStep 1324867 = 1987301) B1987301
theorem B1177427 : Blo 1176405 1177427 := bstep (se 1 (by rfl) ⟨883070, by rfl⟩ : syracuseStep 1177427 = 1766141) B1766141
theorem B1767251 : Blo 1176405 1767251 := bstep (se 1 (by rfl) ⟨1325438, by rfl⟩ : syracuseStep 1767251 = 2650877) B2650877
theorem B1988435 : Blo 1176405 1988435 := bstep (se 1 (by rfl) ⟨1491326, by rfl⟩ : syracuseStep 1988435 = 2982653) B2982653
theorem B1177443 : Blo 1176405 1177443 := bstep (se 1 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 1177443 = 1766165) B1766165
theorem B1767281 : Blo 1176405 1767281 := bstep (se 2 (by rfl) ⟨662730, by rfl⟩ : syracuseStep 1767281 = 1325461) B1325461
theorem B1177459 : Blo 1176405 1177459 := bstep (se 1 (by rfl) ⟨883094, by rfl⟩ : syracuseStep 1177459 = 1766189) B1766189
theorem B1177475 : Blo 1176405 1177475 := bstep (se 1 (by rfl) ⟨883106, by rfl⟩ : syracuseStep 1177475 = 1766213) B1766213
theorem B1767299 : Blo 1176405 1767299 := bstep (se 1 (by rfl) ⟨1325474, by rfl⟩ : syracuseStep 1767299 = 2650949) B2650949
theorem B1177491 : Blo 1176405 1177491 := bstep (se 1 (by rfl) ⟨883118, by rfl⟩ : syracuseStep 1177491 = 1766237) B1766237
theorem B1767329 : Blo 1176405 1767329 := bstep (se 2 (by rfl) ⟨662748, by rfl⟩ : syracuseStep 1767329 = 1325497) B1325497
theorem B1177507 : Blo 1176405 1177507 := bstep (se 1 (by rfl) ⟨883130, by rfl⟩ : syracuseStep 1177507 = 1766261) B1766261
theorem B2267057 : Blo 1176405 2267057 := bstep (se 2 (by rfl) ⟨850146, by rfl⟩ : syracuseStep 2267057 = 1700293) B1700293
theorem B1177523 : Blo 1176405 1177523 := bstep (se 1 (by rfl) ⟨883142, by rfl⟩ : syracuseStep 1177523 = 1766285) B1766285
theorem B1767347 : Blo 1176405 1767347 := bstep (se 1 (by rfl) ⟨1325510, by rfl⟩ : syracuseStep 1767347 = 2651021) B2651021
theorem B1177539 : Blo 1176405 1177539 := bstep (se 1 (by rfl) ⟨883154, by rfl⟩ : syracuseStep 1177539 = 1766309) B1766309
theorem B1193923 : Blo 1176405 1193923 := bstep (se 1 (by rfl) ⟨895442, by rfl⟩ : syracuseStep 1193923 = 1790885) B1790885
theorem B1767377 : Blo 1176405 1767377 := bstep (se 2 (by rfl) ⟨662766, by rfl⟩ : syracuseStep 1767377 = 1325533) B1325533
theorem B1177555 : Blo 1176405 1177555 := bstep (se 1 (by rfl) ⟨883166, by rfl⟩ : syracuseStep 1177555 = 1766333) B1766333
theorem B1325011 : Blo 1176405 1325011 := bstep (se 1 (by rfl) ⟨993758, by rfl⟩ : syracuseStep 1325011 = 1987517) B1987517
theorem B1177571 : Blo 1176405 1177571 := bstep (se 1 (by rfl) ⟨883178, by rfl⟩ : syracuseStep 1177571 = 1766357) B1766357
theorem B1767395 : Blo 1176405 1767395 := bstep (se 1 (by rfl) ⟨1325546, by rfl⟩ : syracuseStep 1767395 = 2651093) B2651093
theorem B1177587 : Blo 1176405 1177587 := bstep (se 1 (by rfl) ⟨883190, by rfl⟩ : syracuseStep 1177587 = 1766381) B1766381
theorem B1767425 : Blo 1176405 1767425 := bstep (se 2 (by rfl) ⟨662784, by rfl⟩ : syracuseStep 1767425 = 1325569) B1325569
theorem B1177603 : Blo 1176405 1177603 := bstep (se 1 (by rfl) ⟨883202, by rfl⟩ : syracuseStep 1177603 = 1766405) B1766405
theorem B1177619 : Blo 1176405 1177619 := bstep (se 1 (by rfl) ⟨883214, by rfl⟩ : syracuseStep 1177619 = 1766429) B1766429
theorem B1767443 : Blo 1176405 1767443 := bstep (se 1 (by rfl) ⟨1325582, by rfl⟩ : syracuseStep 1767443 = 2651165) B2651165
theorem B1177635 : Blo 1176405 1177635 := bstep (se 1 (by rfl) ⟨883226, by rfl⟩ : syracuseStep 1177635 = 1766453) B1766453
theorem B1677361 : Blo 1176405 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B1767473 : Blo 1176405 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B1177651 : Blo 1176405 1177651 := bstep (se 1 (by rfl) ⟨883238, by rfl⟩ : syracuseStep 1177651 = 1766477) B1766477
theorem B1177667 : Blo 1176405 1177667 := bstep (se 1 (by rfl) ⟨883250, by rfl⟩ : syracuseStep 1177667 = 1766501) B1766501
theorem B1767491 : Blo 1176405 1767491 := bstep (se 1 (by rfl) ⟨1325618, by rfl⟩ : syracuseStep 1767491 = 2651237) B2651237
theorem B1177683 : Blo 1176405 1177683 := bstep (se 1 (by rfl) ⟨883262, by rfl⟩ : syracuseStep 1177683 = 1766525) B1766525
theorem B1677395 : Blo 1176405 1677395 := bstep (se 1 (by rfl) ⟨1258046, by rfl⟩ : syracuseStep 1677395 = 2516093) B2516093
theorem B1767521 : Blo 1176405 1767521 := bstep (se 2 (by rfl) ⟨662820, by rfl⟩ : syracuseStep 1767521 = 1325641) B1325641
theorem B1177699 : Blo 1176405 1177699 := bstep (se 1 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 1177699 = 1766549) B1766549
theorem B1325155 : Blo 1176405 1325155 := bstep (se 1 (by rfl) ⟨993866, by rfl⟩ : syracuseStep 1325155 = 1987733) B1987733
theorem B7166065 : Blo 1176405 7166065 := bstep (se 2 (by rfl) ⟨2687274, by rfl⟩ : syracuseStep 7166065 = 5374549) B5374549
theorem B1177715 : Blo 1176405 1177715 := bstep (se 1 (by rfl) ⟨883286, by rfl⟩ : syracuseStep 1177715 = 1766573) B1766573
theorem B1767539 : Blo 1176405 1767539 := bstep (se 1 (by rfl) ⟨1325654, by rfl⟩ : syracuseStep 1767539 = 2651309) B2651309
theorem B2685059 : Blo 1176405 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1177731 : Blo 1176405 1177731 := bstep (se 1 (by rfl) ⟨883298, by rfl⟩ : syracuseStep 1177731 = 1766597) B1766597
theorem B3971213 : Blo 1176405 3971213 := bstep (se 3 (by rfl) ⟨744602, by rfl⟩ : syracuseStep 3971213 = 1489205) B1489205
theorem B1767569 : Blo 1176405 1767569 := bstep (se 2 (by rfl) ⟨662838, by rfl⟩ : syracuseStep 1767569 = 1325677) B1325677
theorem B1489043 : Blo 1176405 1489043 := bstep (se 1 (by rfl) ⟨1116782, by rfl⟩ : syracuseStep 1489043 = 2233565) B2233565
theorem B1177747 : Blo 1176405 1177747 := bstep (se 1 (by rfl) ⟨883310, by rfl⟩ : syracuseStep 1177747 = 1766621) B1766621
theorem B1177763 : Blo 1176405 1177763 := bstep (se 1 (by rfl) ⟨883322, by rfl⟩ : syracuseStep 1177763 = 1766645) B1766645
theorem B1767587 : Blo 1176405 1767587 := bstep (se 1 (by rfl) ⟨1325690, by rfl⟩ : syracuseStep 1767587 = 2651381) B2651381
theorem B1177779 : Blo 1176405 1177779 := bstep (se 1 (by rfl) ⟨883334, by rfl⟩ : syracuseStep 1177779 = 1766669) B1766669
theorem B3971267 : Blo 1176405 3971267 := bstep (se 1 (by rfl) ⟨2978450, by rfl⟩ : syracuseStep 3971267 = 5956901) B5956901
theorem B1177795 : Blo 1176405 1177795 := bstep (se 1 (by rfl) ⟨883346, by rfl⟩ : syracuseStep 1177795 = 1766693) B1766693
theorem B1177811 : Blo 1176405 1177811 := bstep (se 1 (by rfl) ⟨883358, by rfl⟩ : syracuseStep 1177811 = 1766717) B1766717
theorem B1177827 : Blo 1176405 1177827 := bstep (se 1 (by rfl) ⟨883370, by rfl⟩ : syracuseStep 1177827 = 1766741) B1766741
theorem B8943857 : Blo 1176405 8943857 := bstep (se 2 (by rfl) ⟨3353946, by rfl⟩ : syracuseStep 8943857 = 6707893) B6707893
theorem B1177843 : Blo 1176405 1177843 := bstep (se 1 (by rfl) ⟨883382, by rfl⟩ : syracuseStep 1177843 = 1766765) B1766765
theorem B1325299 : Blo 1176405 1325299 := bstep (se 1 (by rfl) ⟨993974, by rfl⟩ : syracuseStep 1325299 = 1987949) B1987949
theorem B1177859 : Blo 1176405 1177859 := bstep (se 1 (by rfl) ⟨883394, by rfl⟩ : syracuseStep 1177859 = 1766789) B1766789
theorem B1177875 : Blo 1176405 1177875 := bstep (se 1 (by rfl) ⟨883406, by rfl⟩ : syracuseStep 1177875 = 1766813) B1766813
theorem B1177891 : Blo 1176405 1177891 := bstep (se 1 (by rfl) ⟨883418, by rfl⟩ : syracuseStep 1177891 = 1766837) B1766837
theorem B3774755 : Blo 1176405 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B1177907 : Blo 1176405 1177907 := bstep (se 1 (by rfl) ⟨883430, by rfl⟩ : syracuseStep 1177907 = 1766861) B1766861
theorem B1177923 : Blo 1176405 1177923 := bstep (se 1 (by rfl) ⟨883442, by rfl⟩ : syracuseStep 1177923 = 1766885) B1766885
theorem B8272205 : Blo 1176405 8272205 := bstep (se 3 (by rfl) ⟨1551038, by rfl⟩ : syracuseStep 8272205 = 3102077) B3102077
theorem B1177939 : Blo 1176405 1177939 := bstep (se 1 (by rfl) ⟨883454, by rfl⟩ : syracuseStep 1177939 = 1766909) B1766909
theorem B4471139 : Blo 1176405 4471139 := bstep (se 1 (by rfl) ⟨3353354, by rfl⟩ : syracuseStep 4471139 = 6706709) B6706709
theorem B1177955 : Blo 1176405 1177955 := bstep (se 1 (by rfl) ⟨883466, by rfl⟩ : syracuseStep 1177955 = 1766933) B1766933
theorem B1177971 : Blo 1176405 1177971 := bstep (se 1 (by rfl) ⟨883478, by rfl⟩ : syracuseStep 1177971 = 1766957) B1766957
theorem B1177987 : Blo 1176405 1177987 := bstep (se 1 (by rfl) ⟨883490, by rfl⟩ : syracuseStep 1177987 = 1766981) B1766981
theorem B1325443 : Blo 1176405 1325443 := bstep (se 1 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 1325443 = 1988165) B1988165
theorem B1178003 : Blo 1176405 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B1210771 : Blo 1176405 1210771 := bstep (se 1 (by rfl) ⟨908078, by rfl⟩ : syracuseStep 1210771 = 1816157) B1816157
theorem B1178019 : Blo 1176405 1178019 := bstep (se 1 (by rfl) ⟨883514, by rfl⟩ : syracuseStep 1178019 = 1767029) B1767029
theorem B3774883 : Blo 1176405 3774883 := bstep (se 1 (by rfl) ⟨2831162, by rfl⟩ : syracuseStep 3774883 = 5662325) B5662325
theorem B2120113 : Blo 1176405 2120113 := bstep (se 2 (by rfl) ⟨795042, by rfl⟩ : syracuseStep 2120113 = 1590085) B1590085
theorem B2980273 : Blo 1176405 2980273 := bstep (se 2 (by rfl) ⟨1117602, by rfl⟩ : syracuseStep 2980273 = 2235205) B2235205
theorem B1178035 : Blo 1176405 1178035 := bstep (se 1 (by rfl) ⟨883526, by rfl⟩ : syracuseStep 1178035 = 1767053) B1767053
theorem B1178051 : Blo 1176405 1178051 := bstep (se 1 (by rfl) ⟨883538, by rfl⟩ : syracuseStep 1178051 = 1767077) B1767077
theorem B3971537 : Blo 1176405 3971537 := bstep (se 2 (by rfl) ⟨1489326, by rfl⟩ : syracuseStep 3971537 = 2978653) B2978653
theorem B1178067 : Blo 1176405 1178067 := bstep (se 1 (by rfl) ⟨883550, by rfl⟩ : syracuseStep 1178067 = 1767101) B1767101
theorem B1178083 : Blo 1176405 1178083 := bstep (se 1 (by rfl) ⟨883562, by rfl⟩ : syracuseStep 1178083 = 1767125) B1767125
theorem B1178099 : Blo 1176405 1178099 := bstep (se 1 (by rfl) ⟨883574, by rfl⟩ : syracuseStep 1178099 = 1767149) B1767149
theorem B1178115 : Blo 1176405 1178115 := bstep (se 1 (by rfl) ⟨883586, by rfl⟩ : syracuseStep 1178115 = 1767173) B1767173
theorem B1178131 : Blo 1176405 1178131 := bstep (se 1 (by rfl) ⟨883598, by rfl⟩ : syracuseStep 1178131 = 1767197) B1767197
theorem B1325587 : Blo 1176405 1325587 := bstep (se 1 (by rfl) ⟨994190, by rfl⟩ : syracuseStep 1325587 = 1988381) B1988381
theorem B1178147 : Blo 1176405 1178147 := bstep (se 1 (by rfl) ⟨883610, by rfl⟩ : syracuseStep 1178147 = 1767221) B1767221
theorem B3775025 : Blo 1176405 3775025 := bstep (se 2 (by rfl) ⟨1415634, by rfl⟩ : syracuseStep 3775025 = 2831269) B2831269
theorem B1178163 : Blo 1176405 1178163 := bstep (se 1 (by rfl) ⟨883622, by rfl⟩ : syracuseStep 1178163 = 1767245) B1767245
theorem B2234947 : Blo 1176405 2234947 := bstep (se 1 (by rfl) ⟨1676210, by rfl⟩ : syracuseStep 2234947 = 3352421) B3352421
theorem B1178179 : Blo 1176405 1178179 := bstep (se 1 (by rfl) ⟨883634, by rfl⟩ : syracuseStep 1178179 = 1767269) B1767269
theorem B1178195 : Blo 1176405 1178195 := bstep (se 1 (by rfl) ⟨883646, by rfl⟩ : syracuseStep 1178195 = 1767293) B1767293
theorem B1178211 : Blo 1176405 1178211 := bstep (se 1 (by rfl) ⟨883658, by rfl⟩ : syracuseStep 1178211 = 1767317) B1767317
theorem B19094129 : Blo 1176405 19094129 := bstep (se 2 (by rfl) ⟨7160298, by rfl⟩ : syracuseStep 19094129 = 14320597) B14320597
theorem B1178227 : Blo 1176405 1178227 := bstep (se 1 (by rfl) ⟨883670, by rfl⟩ : syracuseStep 1178227 = 1767341) B1767341
theorem B1178243 : Blo 1176405 1178243 := bstep (se 1 (by rfl) ⟨883682, by rfl⟩ : syracuseStep 1178243 = 1767365) B1767365
theorem B1178259 : Blo 1176405 1178259 := bstep (se 1 (by rfl) ⟨883694, by rfl⟩ : syracuseStep 1178259 = 1767389) B1767389
theorem B1178275 : Blo 1176405 1178275 := bstep (se 1 (by rfl) ⟨883706, by rfl⟩ : syracuseStep 1178275 = 1767413) B1767413
theorem B3775139 : Blo 1176405 3775139 := bstep (se 1 (by rfl) ⟨2831354, by rfl⟩ : syracuseStep 3775139 = 5662709) B5662709
theorem B1178291 : Blo 1176405 1178291 := bstep (se 1 (by rfl) ⟨883718, by rfl⟩ : syracuseStep 1178291 = 1767437) B1767437
theorem B2980547 : Blo 1176405 2980547 := bstep (se 1 (by rfl) ⟨2235410, by rfl⟩ : syracuseStep 2980547 = 4470821) B4470821
theorem B1178307 : Blo 1176405 1178307 := bstep (se 1 (by rfl) ⟨883730, by rfl⟩ : syracuseStep 1178307 = 1767461) B1767461
theorem B1178323 : Blo 1176405 1178323 := bstep (se 1 (by rfl) ⟨883742, by rfl⟩ : syracuseStep 1178323 = 1767485) B1767485
theorem B2235107 : Blo 1176405 2235107 := bstep (se 1 (by rfl) ⟨1676330, by rfl⟩ : syracuseStep 2235107 = 3352661) B3352661
theorem B15088355 : Blo 1176405 15088355 := bstep (se 1 (by rfl) ⟨11316266, by rfl⟩ : syracuseStep 15088355 = 22632533) B22632533
theorem B1178339 : Blo 1176405 1178339 := bstep (se 1 (by rfl) ⟨883754, by rfl⟩ : syracuseStep 1178339 = 1767509) B1767509
theorem B1178355 : Blo 1176405 1178355 := bstep (se 1 (by rfl) ⟨883766, by rfl⟩ : syracuseStep 1178355 = 1767533) B1767533
theorem B1178371 : Blo 1176405 1178371 := bstep (se 1 (by rfl) ⟨883778, by rfl⟩ : syracuseStep 1178371 = 1767557) B1767557
theorem B1178387 : Blo 1176405 1178387 := bstep (se 1 (by rfl) ⟨883790, by rfl⟩ : syracuseStep 1178387 = 1767581) B1767581
theorem B1178403 : Blo 1176405 1178403 := bstep (se 1 (by rfl) ⟨883802, by rfl⟩ : syracuseStep 1178403 = 1767605) B1767605
theorem B1489747 : Blo 1176405 1489747 := bstep (se 1 (by rfl) ⟨1117310, by rfl⟩ : syracuseStep 1489747 = 2234621) B2234621
theorem B25475953 : Blo 1176405 25475953 := bstep (se 2 (by rfl) ⟨9553482, by rfl⟩ : syracuseStep 25475953 = 19106965) B19106965
theorem B2980739 : Blo 1176405 2980739 := bstep (se 1 (by rfl) ⟨2235554, by rfl⟩ : syracuseStep 2980739 = 4471109) B4471109
theorem B1489843 : Blo 1176405 1489843 := bstep (se 1 (by rfl) ⟨1117382, by rfl⟩ : syracuseStep 1489843 = 2234765) B2234765
theorem B3972077 : Blo 1176405 3972077 := bstep (se 3 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 3972077 = 1489529) B1489529
theorem B6364145 : Blo 1176405 6364145 := bstep (se 2 (by rfl) ⟨2386554, by rfl⟩ : syracuseStep 6364145 = 4773109) B4773109
theorem B4471793 : Blo 1176405 4471793 := bstep (se 2 (by rfl) ⟨1676922, by rfl⟩ : syracuseStep 4471793 = 3353845) B3353845
theorem B3972131 : Blo 1176405 3972131 := bstep (se 1 (by rfl) ⟨2979098, by rfl⟩ : syracuseStep 3972131 = 5958197) B5958197
theorem B3316945 : Blo 1176405 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B40795363 : Blo 1176405 40795363 := bstep (se 1 (by rfl) ⟨30596522, by rfl⟩ : syracuseStep 40795363 = 61193045) B61193045
theorem B2514179 : Blo 1176405 2514179 := bstep (se 1 (by rfl) ⟨1885634, by rfl⟩ : syracuseStep 2514179 = 3771269) B3771269
theorem B3972401 : Blo 1176405 3972401 := bstep (se 2 (by rfl) ⟨1489650, by rfl⟩ : syracuseStep 3972401 = 2979301) B2979301
theorem B5963057 : Blo 1176405 5963057 := bstep (se 2 (by rfl) ⟨2236146, by rfl⟩ : syracuseStep 5963057 = 4472293) B4472293
theorem B6364493 : Blo 1176405 6364493 := bstep (se 3 (by rfl) ⟨1193342, by rfl⟩ : syracuseStep 6364493 = 2386685) B2386685
theorem B6700421 : Blo 1176405 6700421 := bstep (se 4 (by rfl) ⟨628164, by rfl⟩ : syracuseStep 6700421 = 1256329) B1256329
theorem B1490339 : Blo 1176405 1490339 := bstep (se 1 (by rfl) ⟨1117754, by rfl⟩ : syracuseStep 1490339 = 2235509) B2235509
theorem B13589957 : Blo 1176405 13589957 := bstep (se 4 (by rfl) ⟨1274058, by rfl⟩ : syracuseStep 13589957 = 2548117) B2548117
theorem B5094989 : Blo 1176405 5094989 := bstep (se 3 (by rfl) ⟨955310, by rfl⟩ : syracuseStep 5094989 = 1910621) B1910621
theorem B5029553 : Blo 1176405 5029553 := bstep (se 2 (by rfl) ⟨1886082, by rfl⟩ : syracuseStep 5029553 = 3772165) B3772165
theorem B4030157 : Blo 1176405 4030157 := bstep (se 3 (by rfl) ⟨755654, by rfl⟩ : syracuseStep 4030157 = 1511309) B1511309
theorem B1988003 : Blo 1176405 1988003 := bstep (se 1 (by rfl) ⟨1491002, by rfl⟩ : syracuseStep 1988003 = 2982005) B2982005
theorem B5660401 : Blo 1176405 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B8052493 : Blo 1176405 8052493 := bstep (se 3 (by rfl) ⟨1509842, by rfl⟩ : syracuseStep 8052493 = 3019685) B3019685
theorem B2236177 : Blo 1176405 2236177 := bstep (se 2 (by rfl) ⟨838566, by rfl⟩ : syracuseStep 2236177 = 1677133) B1677133
theorem B2981681 : Blo 1176405 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B3972941 : Blo 1176405 3972941 := bstep (se 3 (by rfl) ⟨744926, by rfl⟩ : syracuseStep 3972941 = 1489853) B1489853
theorem B6700877 : Blo 1176405 6700877 := bstep (se 3 (by rfl) ⟨1256414, by rfl⟩ : syracuseStep 6700877 = 2512829) B2512829
theorem B7642957 : Blo 1176405 7642957 := bstep (se 3 (by rfl) ⟨1433054, by rfl⟩ : syracuseStep 7642957 = 2866109) B2866109
theorem B2981731 : Blo 1176405 2981731 := bstep (se 1 (by rfl) ⟨2236298, by rfl⟩ : syracuseStep 2981731 = 4472597) B4472597
theorem B3972995 : Blo 1176405 3972995 := bstep (se 1 (by rfl) ⟨2979746, by rfl⟩ : syracuseStep 3972995 = 5959493) B5959493
theorem B6709169 : Blo 1176405 6709169 := bstep (se 2 (by rfl) ⟨2515938, by rfl⟩ : syracuseStep 6709169 = 5031877) B5031877
theorem B2981873 : Blo 1176405 2981873 := bstep (se 2 (by rfl) ⟨1118202, by rfl⟩ : syracuseStep 2981873 = 2236405) B2236405
theorem B2236481 : Blo 1176405 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B2121815 : Blo 1176405 2121815 := bstep (se 1 (by rfl) ⟨1591361, by rfl⟩ : syracuseStep 2121815 = 3182723) B3182723
theorem B3350621 : Blo 1176405 3350621 := bstep (se 3 (by rfl) ⟨628241, by rfl⟩ : syracuseStep 3350621 = 1256483) B1256483
theorem B21479575 : Blo 1176405 21479575 := bstep (se 1 (by rfl) ⟨16109681, by rfl⟩ : syracuseStep 21479575 = 32219363) B32219363
theorem B2547929 : Blo 1176405 2547929 := bstep (se 2 (by rfl) ⟨955473, by rfl⟩ : syracuseStep 2547929 = 1910947) B1910947
theorem B4473053 : Blo 1176405 4473053 := bstep (se 3 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 4473053 = 1677395) B1677395
theorem B2515187 : Blo 1176405 2515187 := bstep (se 1 (by rfl) ⟨1886390, by rfl⟩ : syracuseStep 2515187 = 3772781) B3772781
theorem B2982167 : Blo 1176405 2982167 := bstep (se 1 (by rfl) ⟨2236625, by rfl⟩ : syracuseStep 2982167 = 4473251) B4473251
theorem B3973427 : Blo 1176405 3973427 := bstep (se 1 (by rfl) ⟨2980070, by rfl⟩ : syracuseStep 3973427 = 5960141) B5960141
theorem B6799691 : Blo 1176405 6799691 := bstep (se 1 (by rfl) ⟨5099768, by rfl⟩ : syracuseStep 6799691 = 10199537) B10199537
theorem B2236747 : Blo 1176405 2236747 := bstep (se 1 (by rfl) ⟨1677560, by rfl⟩ : syracuseStep 2236747 = 3355121) B3355121
theorem B5030237 : Blo 1176405 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B58114421 : Blo 1176405 58114421 := bstep (se 5 (by rfl) ⟨2724113, by rfl⟩ : syracuseStep 58114421 = 5448227) B5448227
theorem B3350963 : Blo 1176405 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B3973697 : Blo 1176405 3973697 := bstep (se 2 (by rfl) ⟨1490136, by rfl⟩ : syracuseStep 3973697 = 2980273) B2980273
theorem B5964353 : Blo 1176405 5964353 := bstep (se 2 (by rfl) ⟨2236632, by rfl⟩ : syracuseStep 5964353 = 4473265) B4473265
theorem B5030545 : Blo 1176405 5030545 := bstep (se 2 (by rfl) ⟨1886454, by rfl⟩ : syracuseStep 5030545 = 3772909) B3772909
theorem B5030579 : Blo 1176405 5030579 := bstep (se 1 (by rfl) ⟨3772934, by rfl⟩ : syracuseStep 5030579 = 7545869) B7545869
theorem B19079981 : Blo 1176405 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B6800203 : Blo 1176405 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B2646935 : Blo 1176405 2646935 := bstep (se 1 (by rfl) ⟨1985201, by rfl⟩ : syracuseStep 2646935 = 3970403) B3970403
theorem B4473751 : Blo 1176405 4473751 := bstep (se 1 (by rfl) ⟨3355313, by rfl⟩ : syracuseStep 4473751 = 6710627) B6710627
theorem B8479819 : Blo 1176405 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B2647115 : Blo 1176405 2647115 := bstep (se 1 (by rfl) ⟨1985336, by rfl⟩ : syracuseStep 2647115 = 3970673) B3970673
theorem B3974237 : Blo 1176405 3974237 := bstep (se 3 (by rfl) ⟨745169, by rfl⟩ : syracuseStep 3974237 = 1490339) B1490339
theorem B2647169 : Blo 1176405 2647169 := bstep (se 2 (by rfl) ⟨992688, by rfl⟩ : syracuseStep 2647169 = 1985377) B1985377
theorem B5956739 : Blo 1176405 5956739 := bstep (se 1 (by rfl) ⟨4467554, by rfl⟩ : syracuseStep 5956739 = 8935109) B8935109
theorem B2417867 : Blo 1176405 2417867 := bstep (se 1 (by rfl) ⟨1813400, by rfl⟩ : syracuseStep 2417867 = 3626801) B3626801
theorem B6980825 : Blo 1176405 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B2647385 : Blo 1176405 2647385 := bstep (se 2 (by rfl) ⟨992769, by rfl⟩ : syracuseStep 2647385 = 1985539) B1985539
theorem B2647475 : Blo 1176405 2647475 := bstep (se 1 (by rfl) ⟨1985606, by rfl⟩ : syracuseStep 2647475 = 3971213) B3971213
theorem B2647511 : Blo 1176405 2647511 := bstep (se 1 (by rfl) ⟨1985633, by rfl⟩ : syracuseStep 2647511 = 3971267) B3971267
theorem B4244957 : Blo 1176405 4244957 := bstep (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) B1591859
theorem B2516503 : Blo 1176405 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B5514803 : Blo 1176405 5514803 := bstep (se 1 (by rfl) ⟨4136102, by rfl⟩ : syracuseStep 5514803 = 8272205) B8272205
theorem B2647691 : Blo 1176405 2647691 := bstep (se 1 (by rfl) ⟨1985768, by rfl⟩ : syracuseStep 2647691 = 3971537) B3971537
theorem B2647745 : Blo 1176405 2647745 := bstep (se 2 (by rfl) ⟨992904, by rfl⟩ : syracuseStep 2647745 = 1985809) B1985809
theorem B2516683 : Blo 1176405 2516683 := bstep (se 1 (by rfl) ⟨1887512, by rfl⟩ : syracuseStep 2516683 = 3775025) B3775025
theorem B2516759 : Blo 1176405 2516759 := bstep (se 1 (by rfl) ⟨1887569, by rfl⟩ : syracuseStep 2516759 = 3775139) B3775139
theorem B2295577 : Blo 1176405 2295577 := bstep (se 2 (by rfl) ⟨860841, by rfl⟩ : syracuseStep 2295577 = 1721683) B1721683
theorem B13412141 : Blo 1176405 13412141 := bstep (se 3 (by rfl) ⟨2514776, by rfl⟩ : syracuseStep 13412141 = 5029553) B5029553
theorem B2647961 : Blo 1176405 2647961 := bstep (se 2 (by rfl) ⟨992985, by rfl⟩ : syracuseStep 2647961 = 1985971) B1985971
theorem B2648051 : Blo 1176405 2648051 := bstep (se 1 (by rfl) ⟨1986038, by rfl⟩ : syracuseStep 2648051 = 3972077) B3972077
theorem B2648087 : Blo 1176405 2648087 := bstep (se 1 (by rfl) ⟨1986065, by rfl⟩ : syracuseStep 2648087 = 3972131) B3972131
theorem B9062435 : Blo 1176405 9062435 := bstep (se 1 (by rfl) ⟨6796826, by rfl⟩ : syracuseStep 9062435 = 13593653) B13593653
theorem B6457445 : Blo 1176405 6457445 := bstep (se 4 (by rfl) ⟨605385, by rfl⟩ : syracuseStep 6457445 = 1210771) B1210771
theorem B4245635 : Blo 1176405 4245635 := bstep (se 1 (by rfl) ⟨3184226, by rfl⟩ : syracuseStep 4245635 = 6368453) B6368453
theorem B2648267 : Blo 1176405 2648267 := bstep (se 1 (by rfl) ⟨1986200, by rfl⟩ : syracuseStep 2648267 = 3972401) B3972401
theorem B3975371 : Blo 1176405 3975371 := bstep (se 1 (by rfl) ⟨2981528, by rfl⟩ : syracuseStep 3975371 = 5963057) B5963057
theorem B2648321 : Blo 1176405 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B4466947 : Blo 1176405 4466947 := bstep (se 1 (by rfl) ⟨3350210, by rfl⟩ : syracuseStep 4466947 = 6700421) B6700421
theorem B11307269 : Blo 1176405 11307269 := bstep (se 4 (by rfl) ⟨1060056, by rfl⟩ : syracuseStep 11307269 = 2120113) B2120113
theorem B7547201 : Blo 1176405 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B10733917 : Blo 1176405 10733917 := bstep (se 3 (by rfl) ⟨2012609, by rfl⟩ : syracuseStep 10733917 = 4025219) B4025219
theorem B2648537 : Blo 1176405 2648537 := bstep (se 2 (by rfl) ⟨993201, by rfl⟩ : syracuseStep 2648537 = 1986403) B1986403
theorem B3975641 : Blo 1176405 3975641 := bstep (se 2 (by rfl) ⟨1490865, by rfl⟩ : syracuseStep 3975641 = 2981731) B2981731
theorem B1886743 : Blo 1176405 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B5032493 : Blo 1176405 5032493 := bstep (se 3 (by rfl) ⟨943592, by rfl⟩ : syracuseStep 5032493 = 1887185) B1887185
theorem B4467251 : Blo 1176405 4467251 := bstep (se 1 (by rfl) ⟨3350438, by rfl⟩ : syracuseStep 4467251 = 6700877) B6700877
theorem B2648627 : Blo 1176405 2648627 := bstep (se 1 (by rfl) ⟨1986470, by rfl⟩ : syracuseStep 2648627 = 3972941) B3972941
theorem B2648663 : Blo 1176405 2648663 := bstep (se 1 (by rfl) ⟨1986497, by rfl⟩ : syracuseStep 2648663 = 3972995) B3972995
theorem B1591897 : Blo 1176405 1591897 := bstep (se 2 (by rfl) ⟨596961, by rfl⟩ : syracuseStep 1591897 = 1193923) B1193923
theorem B4655819 : Blo 1176405 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B3353309 : Blo 1176405 3353309 := bstep (se 3 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 3353309 = 1257491) B1257491
theorem B2648843 : Blo 1176405 2648843 := bstep (se 1 (by rfl) ⟨1986632, by rfl⟩ : syracuseStep 2648843 = 3973265) B3973265
theorem B1592075 : Blo 1176405 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B1985303 : Blo 1176405 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B8481581 : Blo 1176405 8481581 := bstep (se 3 (by rfl) ⟨1590296, by rfl⟩ : syracuseStep 8481581 = 3180593) B3180593
theorem B2648897 : Blo 1176405 2648897 := bstep (se 2 (by rfl) ⟨993336, by rfl⟩ : syracuseStep 2648897 = 1986673) B1986673
theorem B9554753 : Blo 1176405 9554753 := bstep (se 2 (by rfl) ⟨3583032, by rfl⟩ : syracuseStep 9554753 = 7166065) B7166065
theorem B1985431 : Blo 1176405 1985431 := bstep (se 1 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 1985431 = 2978147) B2978147
theorem B5368727 : Blo 1176405 5368727 := bstep (se 1 (by rfl) ⟨4026545, by rfl⟩ : syracuseStep 5368727 = 8053091) B8053091
theorem B3353537 : Blo 1176405 3353537 := bstep (se 2 (by rfl) ⟨1257576, by rfl⟩ : syracuseStep 3353537 = 2515153) B2515153
theorem B2649113 : Blo 1176405 2649113 := bstep (se 2 (by rfl) ⟨993417, by rfl⟩ : syracuseStep 2649113 = 1986835) B1986835
theorem B2649203 : Blo 1176405 2649203 := bstep (se 1 (by rfl) ⟨1986902, by rfl⟩ : syracuseStep 2649203 = 3973805) B3973805
theorem B2649239 : Blo 1176405 2649239 := bstep (se 1 (by rfl) ⟨1986929, by rfl⟩ : syracuseStep 2649239 = 3973859) B3973859
theorem B3976343 : Blo 1176405 3976343 := bstep (se 1 (by rfl) ⟨2982257, by rfl⟩ : syracuseStep 3976343 = 5964515) B5964515
theorem B4467905 : Blo 1176405 4467905 := bstep (se 2 (by rfl) ⟨1675464, by rfl⟩ : syracuseStep 4467905 = 3350929) B3350929
theorem B5033177 : Blo 1176405 5033177 := bstep (se 2 (by rfl) ⟨1887441, by rfl⟩ : syracuseStep 5033177 = 3774883) B3774883
theorem B3353879 : Blo 1176405 3353879 := bstep (se 1 (by rfl) ⟨2515409, by rfl⟩ : syracuseStep 3353879 = 5030819) B5030819
theorem B1764683 : Blo 1176405 1764683 := bstep (se 1 (by rfl) ⟨1323512, by rfl⟩ : syracuseStep 1764683 = 2647025) B2647025
theorem B2649419 : Blo 1176405 2649419 := bstep (se 1 (by rfl) ⟨1987064, by rfl⟩ : syracuseStep 2649419 = 3974129) B3974129
theorem B1764695 : Blo 1176405 1764695 := bstep (se 1 (by rfl) ⟨1323521, by rfl⟩ : syracuseStep 1764695 = 2647043) B2647043
theorem B6704477 : Blo 1176405 6704477 := bstep (se 3 (by rfl) ⟨1257089, by rfl⟩ : syracuseStep 6704477 = 2514179) B2514179
theorem B2649473 : Blo 1176405 2649473 := bstep (se 2 (by rfl) ⟨993552, by rfl⟩ : syracuseStep 2649473 = 1987105) B1987105
theorem B4246915 : Blo 1176405 4246915 := bstep (se 1 (by rfl) ⟨3185186, by rfl⟩ : syracuseStep 4246915 = 6370373) B6370373
theorem B1764761 : Blo 1176405 1764761 := bstep (se 2 (by rfl) ⟨661785, by rfl⟩ : syracuseStep 1764761 = 1323571) B1323571
theorem B1764875 : Blo 1176405 1764875 := bstep (se 1 (by rfl) ⟨1323656, by rfl⟩ : syracuseStep 1764875 = 2647313) B2647313
theorem B1986059 : Blo 1176405 1986059 := bstep (se 1 (by rfl) ⟨1489544, by rfl⟩ : syracuseStep 1986059 = 2979089) B2979089
theorem B1764887 : Blo 1176405 1764887 := bstep (se 1 (by rfl) ⟨1323665, by rfl⟩ : syracuseStep 1764887 = 2647331) B2647331
theorem B1764953 : Blo 1176405 1764953 := bstep (se 2 (by rfl) ⟨661857, by rfl⟩ : syracuseStep 1764953 = 1323715) B1323715
theorem B2649689 : Blo 1176405 2649689 := bstep (se 2 (by rfl) ⟨993633, by rfl⟩ : syracuseStep 2649689 = 1987267) B1987267
theorem B1986187 : Blo 1176405 1986187 := bstep (se 1 (by rfl) ⟨1489640, by rfl⟩ : syracuseStep 1986187 = 2979281) B2979281
theorem B2649779 : Blo 1176405 2649779 := bstep (se 1 (by rfl) ⟨1987334, by rfl⟩ : syracuseStep 2649779 = 3974669) B3974669
theorem B2723507 : Blo 1176405 2723507 := bstep (se 1 (by rfl) ⟨2042630, by rfl⟩ : syracuseStep 2723507 = 4085261) B4085261
theorem B3976883 : Blo 1176405 3976883 := bstep (se 1 (by rfl) ⟨2982662, by rfl⟩ : syracuseStep 3976883 = 5965325) B5965325
theorem B1765067 : Blo 1176405 1765067 := bstep (se 1 (by rfl) ⟨1323800, by rfl⟩ : syracuseStep 1765067 = 2647601) B2647601
theorem B1765079 : Blo 1176405 1765079 := bstep (se 1 (by rfl) ⟨1323809, by rfl⟩ : syracuseStep 1765079 = 2647619) B2647619
theorem B2649815 : Blo 1176405 2649815 := bstep (se 1 (by rfl) ⟨1987361, by rfl⟩ : syracuseStep 2649815 = 3974723) B3974723
theorem B5099287 : Blo 1176405 5099287 := bstep (se 1 (by rfl) ⟨3824465, by rfl⟩ : syracuseStep 5099287 = 7648931) B7648931
theorem B1765145 : Blo 1176405 1765145 := bstep (se 2 (by rfl) ⟨661929, by rfl⟩ : syracuseStep 1765145 = 1323859) B1323859
theorem B1986329 : Blo 1176405 1986329 := bstep (se 2 (by rfl) ⟨744873, by rfl⟩ : syracuseStep 1986329 = 1489747) B1489747
theorem B33967937 : Blo 1176405 33967937 := bstep (se 2 (by rfl) ⟨12737976, by rfl⟩ : syracuseStep 33967937 = 25475953) B25475953
theorem B1789771 : Blo 1176405 1789771 := bstep (se 1 (by rfl) ⟨1342328, by rfl⟩ : syracuseStep 1789771 = 2684657) B2684657
theorem B1273687 : Blo 1176405 1273687 := bstep (se 1 (by rfl) ⟨955265, by rfl⟩ : syracuseStep 1273687 = 1910531) B1910531
theorem B1765259 : Blo 1176405 1765259 := bstep (se 1 (by rfl) ⟨1323944, by rfl⟩ : syracuseStep 1765259 = 2647889) B2647889
theorem B2649995 : Blo 1176405 2649995 := bstep (se 1 (by rfl) ⟨1987496, by rfl⟩ : syracuseStep 2649995 = 3974993) B3974993
theorem B1765271 : Blo 1176405 1765271 := bstep (se 1 (by rfl) ⟨1323953, by rfl⟩ : syracuseStep 1765271 = 2647907) B2647907
theorem B1986457 : Blo 1176405 1986457 := bstep (se 2 (by rfl) ⟨744921, by rfl⟩ : syracuseStep 1986457 = 1489843) B1489843
theorem B2650049 : Blo 1176405 2650049 := bstep (se 2 (by rfl) ⟨993768, by rfl⟩ : syracuseStep 2650049 = 1987537) B1987537
theorem B1511371 : Blo 1176405 1511371 := bstep (se 1 (by rfl) ⟨1133528, by rfl⟩ : syracuseStep 1511371 = 2267057) B2267057
theorem B1765337 : Blo 1176405 1765337 := bstep (se 2 (by rfl) ⟨662001, by rfl⟩ : syracuseStep 1765337 = 1324003) B1324003
theorem B2830297 : Blo 1176405 2830297 := bstep (se 2 (by rfl) ⟨1061361, by rfl⟩ : syracuseStep 2830297 = 2122723) B2122723
theorem B20107277 : Blo 1176405 20107277 := bstep (se 3 (by rfl) ⟨3770114, by rfl⟩ : syracuseStep 20107277 = 7540229) B7540229
theorem B2977843 : Blo 1176405 2977843 := bstep (se 1 (by rfl) ⟨2233382, by rfl⟩ : syracuseStep 2977843 = 4466765) B4466765
theorem B1765451 : Blo 1176405 1765451 := bstep (se 1 (by rfl) ⟨1324088, by rfl⟩ : syracuseStep 1765451 = 2648177) B2648177
theorem B1765463 : Blo 1176405 1765463 := bstep (se 1 (by rfl) ⟨1324097, by rfl⟩ : syracuseStep 1765463 = 2648195) B2648195
theorem B1790039 : Blo 1176405 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1765529 : Blo 1176405 1765529 := bstep (se 2 (by rfl) ⟨662073, by rfl⟩ : syracuseStep 1765529 = 1324147) B1324147
theorem B2650265 : Blo 1176405 2650265 := bstep (se 2 (by rfl) ⟨993849, by rfl⟩ : syracuseStep 2650265 = 1987699) B1987699
theorem B2977985 : Blo 1176405 2977985 := bstep (se 2 (by rfl) ⟨1116744, by rfl⟩ : syracuseStep 2977985 = 2233489) B2233489
theorem B2650355 : Blo 1176405 2650355 := bstep (se 1 (by rfl) ⟨1987766, by rfl⟩ : syracuseStep 2650355 = 3975533) B3975533
theorem B1765643 : Blo 1176405 1765643 := bstep (se 1 (by rfl) ⟨1324232, by rfl⟩ : syracuseStep 1765643 = 2648465) B2648465
theorem B1765655 : Blo 1176405 1765655 := bstep (se 1 (by rfl) ⟨1324241, by rfl⟩ : syracuseStep 1765655 = 2648483) B2648483
theorem B2650391 : Blo 1176405 2650391 := bstep (se 1 (by rfl) ⟨1987793, by rfl⟩ : syracuseStep 2650391 = 3975587) B3975587
theorem B1765721 : Blo 1176405 1765721 := bstep (se 2 (by rfl) ⟨662145, by rfl⟩ : syracuseStep 1765721 = 1324291) B1324291
theorem B4469165 : Blo 1176405 4469165 := bstep (se 3 (by rfl) ⟨837968, by rfl⟩ : syracuseStep 4469165 = 1675937) B1675937
theorem B4469195 : Blo 1176405 4469195 := bstep (se 1 (by rfl) ⟨3351896, by rfl⟩ : syracuseStep 4469195 = 6703793) B6703793
theorem B1765835 : Blo 1176405 1765835 := bstep (se 1 (by rfl) ⟨1324376, by rfl⟩ : syracuseStep 1765835 = 2648753) B2648753
theorem B2650571 : Blo 1176405 2650571 := bstep (se 1 (by rfl) ⟨1987928, by rfl⟩ : syracuseStep 2650571 = 3975857) B3975857
theorem B1765847 : Blo 1176405 1765847 := bstep (se 1 (by rfl) ⟨1324385, by rfl⟩ : syracuseStep 1765847 = 2648771) B2648771
theorem B1987031 : Blo 1176405 1987031 := bstep (se 1 (by rfl) ⟨1490273, by rfl⟩ : syracuseStep 1987031 = 2980547) B2980547
theorem B1323499 : Blo 1176405 1323499 := bstep (se 1 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 1323499 = 1985249) B1985249
theorem B2650625 : Blo 1176405 2650625 := bstep (se 2 (by rfl) ⟨993984, by rfl⟩ : syracuseStep 2650625 = 1987969) B1987969
theorem B1765913 : Blo 1176405 1765913 := bstep (se 2 (by rfl) ⟨662217, by rfl⟩ : syracuseStep 1765913 = 1324435) B1324435
theorem B2830913 : Blo 1176405 2830913 := bstep (se 2 (by rfl) ⟨1061592, by rfl⟩ : syracuseStep 2830913 = 2123185) B2123185
theorem B1323607 : Blo 1176405 1323607 := bstep (se 1 (by rfl) ⟨992705, by rfl⟩ : syracuseStep 1323607 = 1985411) B1985411
theorem B1987159 : Blo 1176405 1987159 := bstep (se 1 (by rfl) ⟨1490369, by rfl⟩ : syracuseStep 1987159 = 2980739) B2980739
theorem B1766027 : Blo 1176405 1766027 := bstep (se 1 (by rfl) ⟨1324520, by rfl⟩ : syracuseStep 1766027 = 2649041) B2649041
theorem B1766039 : Blo 1176405 1766039 := bstep (se 1 (by rfl) ⟨1324529, by rfl⟩ : syracuseStep 1766039 = 2649059) B2649059
theorem B2388631 : Blo 1176405 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B1766105 : Blo 1176405 1766105 := bstep (se 2 (by rfl) ⟨662289, by rfl⟩ : syracuseStep 1766105 = 1324579) B1324579
theorem B2650841 : Blo 1176405 2650841 := bstep (se 2 (by rfl) ⟨994065, by rfl⟩ : syracuseStep 2650841 = 1988131) B1988131
theorem B9679621 : Blo 1176405 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B1323787 : Blo 1176405 1323787 := bstep (se 1 (by rfl) ⟨992840, by rfl⟩ : syracuseStep 1323787 = 1985681) B1985681
theorem B5960465 : Blo 1176405 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B2388761 : Blo 1176405 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B6361901 : Blo 1176405 6361901 := bstep (se 3 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 6361901 = 2385713) B2385713
theorem B2650931 : Blo 1176405 2650931 := bstep (se 1 (by rfl) ⟨1988198, by rfl⟩ : syracuseStep 2650931 = 3976397) B3976397
theorem B1766219 : Blo 1176405 1766219 := bstep (se 1 (by rfl) ⟨1324664, by rfl⟩ : syracuseStep 1766219 = 2649329) B2649329
theorem B1176407 : Blo 1176405 1176407 := bstep (se 1 (by rfl) ⟨882305, by rfl⟩ : syracuseStep 1176407 = 1764611) B1764611
theorem B1766231 : Blo 1176405 1766231 := bstep (se 1 (by rfl) ⟨1324673, by rfl⟩ : syracuseStep 1766231 = 2649347) B2649347
theorem B2650967 : Blo 1176405 2650967 := bstep (se 1 (by rfl) ⟨1988225, by rfl⟩ : syracuseStep 2650967 = 3976451) B3976451
theorem B1176427 : Blo 1176405 1176427 := bstep (se 1 (by rfl) ⟨882320, by rfl⟩ : syracuseStep 1176427 = 1764641) B1764641
theorem B1176439 : Blo 1176405 1176439 := bstep (se 1 (by rfl) ⟨882329, by rfl⟩ : syracuseStep 1176439 = 1764659) B1764659
theorem B1323895 : Blo 1176405 1323895 := bstep (se 1 (by rfl) ⟨992921, by rfl⟩ : syracuseStep 1323895 = 1985843) B1985843
theorem B1176459 : Blo 1176405 1176459 := bstep (se 1 (by rfl) ⟨882344, by rfl⟩ : syracuseStep 1176459 = 1764689) B1764689
theorem B1176471 : Blo 1176405 1176471 := bstep (se 1 (by rfl) ⟨882353, by rfl⟩ : syracuseStep 1176471 = 1764707) B1764707
theorem B1766297 : Blo 1176405 1766297 := bstep (se 2 (by rfl) ⟨662361, by rfl⟩ : syracuseStep 1766297 = 1324723) B1324723
theorem B1176491 : Blo 1176405 1176491 := bstep (se 1 (by rfl) ⟨882368, by rfl⟩ : syracuseStep 1176491 = 1764737) B1764737
theorem B5960627 : Blo 1176405 5960627 := bstep (se 1 (by rfl) ⟨4470470, by rfl⟩ : syracuseStep 5960627 = 8940941) B8940941
theorem B1176503 : Blo 1176405 1176503 := bstep (se 1 (by rfl) ⟨882377, by rfl⟩ : syracuseStep 1176503 = 1764755) B1764755
theorem B1176523 : Blo 1176405 1176523 := bstep (se 1 (by rfl) ⟨882392, by rfl⟩ : syracuseStep 1176523 = 1764785) B1764785
theorem B1176535 : Blo 1176405 1176535 := bstep (se 1 (by rfl) ⟨882401, by rfl⟩ : syracuseStep 1176535 = 1764803) B1764803
theorem B1176555 : Blo 1176405 1176555 := bstep (se 1 (by rfl) ⟨882416, by rfl⟩ : syracuseStep 1176555 = 1764833) B1764833
theorem B1176567 : Blo 1176405 1176567 := bstep (se 1 (by rfl) ⟨882425, by rfl⟩ : syracuseStep 1176567 = 1764851) B1764851
theorem B2233345 : Blo 1176405 2233345 := bstep (se 2 (by rfl) ⟨837504, by rfl⟩ : syracuseStep 2233345 = 1675009) B1675009
theorem B1176587 : Blo 1176405 1176587 := bstep (se 1 (by rfl) ⟨882440, by rfl⟩ : syracuseStep 1176587 = 1764881) B1764881
theorem B1766411 : Blo 1176405 1766411 := bstep (se 1 (by rfl) ⟨1324808, by rfl⟩ : syracuseStep 1766411 = 2649617) B2649617
theorem B2651147 : Blo 1176405 2651147 := bstep (se 1 (by rfl) ⟨1988360, by rfl⟩ : syracuseStep 2651147 = 3976721) B3976721
theorem B10736657 : Blo 1176405 10736657 := bstep (se 2 (by rfl) ⟨4026246, by rfl⟩ : syracuseStep 10736657 = 8052493) B8052493
theorem B7549969 : Blo 1176405 7549969 := bstep (se 2 (by rfl) ⟨2831238, by rfl⟩ : syracuseStep 7549969 = 5662477) B5662477
theorem B1176599 : Blo 1176405 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B1766423 : Blo 1176405 1766423 := bstep (se 1 (by rfl) ⟨1324817, by rfl⟩ : syracuseStep 1766423 = 2649635) B2649635
theorem B1176619 : Blo 1176405 1176619 := bstep (se 1 (by rfl) ⟨882464, by rfl⟩ : syracuseStep 1176619 = 1764929) B1764929
theorem B1324075 : Blo 1176405 1324075 := bstep (se 1 (by rfl) ⟨993056, by rfl⟩ : syracuseStep 1324075 = 1986113) B1986113
theorem B3396659 : Blo 1176405 3396659 := bstep (se 1 (by rfl) ⟨2547494, by rfl⟩ : syracuseStep 3396659 = 5094989) B5094989
theorem B1176631 : Blo 1176405 1176631 := bstep (se 1 (by rfl) ⟨882473, by rfl⟩ : syracuseStep 1176631 = 1764947) B1764947
theorem B2651201 : Blo 1176405 2651201 := bstep (se 2 (by rfl) ⟨994200, by rfl⟩ : syracuseStep 2651201 = 1988401) B1988401
theorem B1176651 : Blo 1176405 1176651 := bstep (se 1 (by rfl) ⟨882488, by rfl⟩ : syracuseStep 1176651 = 1764977) B1764977
theorem B1176663 : Blo 1176405 1176663 := bstep (se 1 (by rfl) ⟨882497, by rfl⟩ : syracuseStep 1176663 = 1764995) B1764995
theorem B4469849 : Blo 1176405 4469849 := bstep (se 2 (by rfl) ⟨1676193, by rfl⟩ : syracuseStep 4469849 = 3352387) B3352387
theorem B1766489 : Blo 1176405 1766489 := bstep (se 2 (by rfl) ⟨662433, by rfl⟩ : syracuseStep 1766489 = 1324867) B1324867
theorem B1176683 : Blo 1176405 1176683 := bstep (se 1 (by rfl) ⟨882512, by rfl⟩ : syracuseStep 1176683 = 1765025) B1765025
theorem B1176695 : Blo 1176405 1176695 := bstep (se 1 (by rfl) ⟨882521, by rfl⟩ : syracuseStep 1176695 = 1765043) B1765043
theorem B1176715 : Blo 1176405 1176715 := bstep (se 1 (by rfl) ⟨882536, by rfl⟩ : syracuseStep 1176715 = 1765073) B1765073
theorem B1176727 : Blo 1176405 1176727 := bstep (se 1 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 1176727 = 1765091) B1765091
theorem B1324183 : Blo 1176405 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B1176747 : Blo 1176405 1176747 := bstep (se 1 (by rfl) ⟨882560, by rfl⟩ : syracuseStep 1176747 = 1765121) B1765121
theorem B1176759 : Blo 1176405 1176759 := bstep (se 1 (by rfl) ⟨882569, by rfl⟩ : syracuseStep 1176759 = 1765139) B1765139
theorem B1176779 : Blo 1176405 1176779 := bstep (se 1 (by rfl) ⟨882584, by rfl⟩ : syracuseStep 1176779 = 1765169) B1765169
theorem B1766603 : Blo 1176405 1766603 := bstep (se 1 (by rfl) ⟨1324952, by rfl⟩ : syracuseStep 1766603 = 2649905) B2649905
theorem B1987787 : Blo 1176405 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B1176791 : Blo 1176405 1176791 := bstep (se 1 (by rfl) ⟨882593, by rfl⟩ : syracuseStep 1176791 = 1765187) B1765187
theorem B1766615 : Blo 1176405 1766615 := bstep (se 1 (by rfl) ⟨1324961, by rfl⟩ : syracuseStep 1766615 = 2649923) B2649923
theorem B1176811 : Blo 1176405 1176811 := bstep (se 1 (by rfl) ⟨882608, by rfl⟩ : syracuseStep 1176811 = 1765217) B1765217
theorem B1176823 : Blo 1176405 1176823 := bstep (se 1 (by rfl) ⟨882617, by rfl⟩ : syracuseStep 1176823 = 1765235) B1765235
theorem B1176843 : Blo 1176405 1176843 := bstep (se 1 (by rfl) ⟨882632, by rfl⟩ : syracuseStep 1176843 = 1765265) B1765265
theorem B1176855 : Blo 1176405 1176855 := bstep (se 1 (by rfl) ⟨882641, by rfl⟩ : syracuseStep 1176855 = 1765283) B1765283
theorem B1766681 : Blo 1176405 1766681 := bstep (se 2 (by rfl) ⟨662505, by rfl⟩ : syracuseStep 1766681 = 1325011) B1325011
theorem B1176875 : Blo 1176405 1176875 := bstep (se 1 (by rfl) ⟨882656, by rfl⟩ : syracuseStep 1176875 = 1765313) B1765313
theorem B1176887 : Blo 1176405 1176887 := bstep (se 1 (by rfl) ⟨882665, by rfl⟩ : syracuseStep 1176887 = 1765331) B1765331
theorem B1176907 : Blo 1176405 1176907 := bstep (se 1 (by rfl) ⟨882680, by rfl⟩ : syracuseStep 1176907 = 1765361) B1765361
theorem B1324363 : Blo 1176405 1324363 := bstep (se 1 (by rfl) ⟨993272, by rfl⟩ : syracuseStep 1324363 = 1986545) B1986545
theorem B5371211 : Blo 1176405 5371211 := bstep (se 1 (by rfl) ⟨4028408, by rfl⟩ : syracuseStep 5371211 = 8056817) B8056817
theorem B1987915 : Blo 1176405 1987915 := bstep (se 1 (by rfl) ⟨1490936, by rfl⟩ : syracuseStep 1987915 = 2981873) B2981873
theorem B1176919 : Blo 1176405 1176919 := bstep (se 1 (by rfl) ⟨882689, by rfl⟩ : syracuseStep 1176919 = 1765379) B1765379
theorem B1176939 : Blo 1176405 1176939 := bstep (se 1 (by rfl) ⟨882704, by rfl⟩ : syracuseStep 1176939 = 1765409) B1765409
theorem B1176951 : Blo 1176405 1176951 := bstep (se 1 (by rfl) ⟨882713, by rfl⟩ : syracuseStep 1176951 = 1765427) B1765427
theorem B1176971 : Blo 1176405 1176971 := bstep (se 1 (by rfl) ⟨882728, by rfl⟩ : syracuseStep 1176971 = 1765457) B1765457
theorem B1766795 : Blo 1176405 1766795 := bstep (se 1 (by rfl) ⟨1325096, by rfl⟩ : syracuseStep 1766795 = 2650193) B2650193
theorem B1176983 : Blo 1176405 1176983 := bstep (se 1 (by rfl) ⟨882737, by rfl⟩ : syracuseStep 1176983 = 1765475) B1765475
theorem B4470167 : Blo 1176405 4470167 := bstep (se 1 (by rfl) ⟨3352625, by rfl⟩ : syracuseStep 4470167 = 6705251) B6705251
theorem B1676695 : Blo 1176405 1676695 := bstep (se 1 (by rfl) ⟨1257521, by rfl⟩ : syracuseStep 1676695 = 2515043) B2515043
theorem B1766807 : Blo 1176405 1766807 := bstep (se 1 (by rfl) ⟨1325105, by rfl⟩ : syracuseStep 1766807 = 2650211) B2650211
theorem B1177003 : Blo 1176405 1177003 := bstep (se 1 (by rfl) ⟨882752, by rfl⟩ : syracuseStep 1177003 = 1765505) B1765505
theorem B2979251 : Blo 1176405 2979251 := bstep (se 1 (by rfl) ⟨2234438, by rfl⟩ : syracuseStep 2979251 = 4468877) B4468877
theorem B1177015 : Blo 1176405 1177015 := bstep (se 1 (by rfl) ⟨882761, by rfl⟩ : syracuseStep 1177015 = 1765523) B1765523
theorem B1324471 : Blo 1176405 1324471 := bstep (se 1 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 1324471 = 1986707) B1986707
theorem B2233793 : Blo 1176405 2233793 := bstep (se 2 (by rfl) ⟨837672, by rfl⟩ : syracuseStep 2233793 = 1675345) B1675345
theorem B1177035 : Blo 1176405 1177035 := bstep (se 1 (by rfl) ⟨882776, by rfl⟩ : syracuseStep 1177035 = 1765553) B1765553
theorem B1177047 : Blo 1176405 1177047 := bstep (se 1 (by rfl) ⟨882785, by rfl⟩ : syracuseStep 1177047 = 1765571) B1765571
theorem B1766873 : Blo 1176405 1766873 := bstep (se 2 (by rfl) ⟨662577, by rfl⟩ : syracuseStep 1766873 = 1325155) B1325155
theorem B1988057 : Blo 1176405 1988057 := bstep (se 2 (by rfl) ⟨745521, by rfl⟩ : syracuseStep 1988057 = 1491043) B1491043
theorem B1177067 : Blo 1176405 1177067 := bstep (se 1 (by rfl) ⟨882800, by rfl⟩ : syracuseStep 1177067 = 1765601) B1765601
theorem B1177079 : Blo 1176405 1177079 := bstep (se 1 (by rfl) ⟨882809, by rfl⟩ : syracuseStep 1177079 = 1765619) B1765619
theorem B1177099 : Blo 1176405 1177099 := bstep (se 1 (by rfl) ⟨882824, by rfl⟩ : syracuseStep 1177099 = 1765649) B1765649
theorem B1177111 : Blo 1176405 1177111 := bstep (se 1 (by rfl) ⟨882833, by rfl⟩ : syracuseStep 1177111 = 1765667) B1765667
theorem B1177131 : Blo 1176405 1177131 := bstep (se 1 (by rfl) ⟨882848, by rfl⟩ : syracuseStep 1177131 = 1765697) B1765697
theorem B1177143 : Blo 1176405 1177143 := bstep (se 1 (by rfl) ⟨882857, by rfl⟩ : syracuseStep 1177143 = 1765715) B1765715
theorem B1177163 : Blo 1176405 1177163 := bstep (se 1 (by rfl) ⟨882872, by rfl⟩ : syracuseStep 1177163 = 1765745) B1765745
theorem B1766987 : Blo 1176405 1766987 := bstep (se 1 (by rfl) ⟨1325240, by rfl⟩ : syracuseStep 1766987 = 2650481) B2650481
theorem B1177175 : Blo 1176405 1177175 := bstep (se 1 (by rfl) ⟨882881, by rfl⟩ : syracuseStep 1177175 = 1765763) B1765763
theorem B1766999 : Blo 1176405 1766999 := bstep (se 1 (by rfl) ⟨1325249, by rfl⟩ : syracuseStep 1766999 = 2650499) B2650499
theorem B1988185 : Blo 1176405 1988185 := bstep (se 2 (by rfl) ⟨745569, by rfl⟩ : syracuseStep 1988185 = 1491139) B1491139
theorem B1177195 : Blo 1176405 1177195 := bstep (se 1 (by rfl) ⟨882896, by rfl⟩ : syracuseStep 1177195 = 1765793) B1765793
theorem B1324651 : Blo 1176405 1324651 := bstep (se 1 (by rfl) ⟨993488, by rfl⟩ : syracuseStep 1324651 = 1986977) B1986977
theorem B1177207 : Blo 1176405 1177207 := bstep (se 1 (by rfl) ⟨882905, by rfl⟩ : syracuseStep 1177207 = 1765811) B1765811
theorem B1177227 : Blo 1176405 1177227 := bstep (se 1 (by rfl) ⟨882920, by rfl⟩ : syracuseStep 1177227 = 1765841) B1765841
theorem B1177239 : Blo 1176405 1177239 := bstep (se 1 (by rfl) ⟨882929, by rfl⟩ : syracuseStep 1177239 = 1765859) B1765859
theorem B1767065 : Blo 1176405 1767065 := bstep (se 2 (by rfl) ⟨662649, by rfl⟩ : syracuseStep 1767065 = 1325299) B1325299
theorem B1177259 : Blo 1176405 1177259 := bstep (se 1 (by rfl) ⟨882944, by rfl⟩ : syracuseStep 1177259 = 1765889) B1765889
theorem B1177271 : Blo 1176405 1177271 := bstep (se 1 (by rfl) ⟨882953, by rfl⟩ : syracuseStep 1177271 = 1765907) B1765907
theorem B1177291 : Blo 1176405 1177291 := bstep (se 1 (by rfl) ⟨882968, by rfl⟩ : syracuseStep 1177291 = 1765937) B1765937
theorem B1177303 : Blo 1176405 1177303 := bstep (se 1 (by rfl) ⟨882977, by rfl⟩ : syracuseStep 1177303 = 1765955) B1765955
theorem B1324759 : Blo 1176405 1324759 := bstep (se 1 (by rfl) ⟨993569, by rfl⟩ : syracuseStep 1324759 = 1987139) B1987139
theorem B3970781 : Blo 1176405 3970781 := bstep (se 3 (by rfl) ⟨744521, by rfl⟩ : syracuseStep 3970781 = 1489043) B1489043
theorem B1177323 : Blo 1176405 1177323 := bstep (se 1 (by rfl) ⟨882992, by rfl⟩ : syracuseStep 1177323 = 1765985) B1765985
theorem B1177335 : Blo 1176405 1177335 := bstep (se 1 (by rfl) ⟨883001, by rfl⟩ : syracuseStep 1177335 = 1766003) B1766003
theorem B1177355 : Blo 1176405 1177355 := bstep (se 1 (by rfl) ⟨883016, by rfl⟩ : syracuseStep 1177355 = 1766033) B1766033
theorem B1767179 : Blo 1176405 1767179 := bstep (se 1 (by rfl) ⟨1325384, by rfl⟩ : syracuseStep 1767179 = 2650769) B2650769
theorem B6706961 : Blo 1176405 6706961 := bstep (se 2 (by rfl) ⟨2515110, by rfl⟩ : syracuseStep 6706961 = 5030221) B5030221
theorem B2234135 : Blo 1176405 2234135 := bstep (se 1 (by rfl) ⟨1675601, by rfl⟩ : syracuseStep 2234135 = 3351203) B3351203
theorem B1177367 : Blo 1176405 1177367 := bstep (se 1 (by rfl) ⟨883025, by rfl⟩ : syracuseStep 1177367 = 1766051) B1766051
theorem B1767191 : Blo 1176405 1767191 := bstep (se 1 (by rfl) ⟨1325393, by rfl⟩ : syracuseStep 1767191 = 2650787) B2650787
theorem B1177387 : Blo 1176405 1177387 := bstep (se 1 (by rfl) ⟨883040, by rfl⟩ : syracuseStep 1177387 = 1766081) B1766081
theorem B1177399 : Blo 1176405 1177399 := bstep (se 1 (by rfl) ⟨883049, by rfl⟩ : syracuseStep 1177399 = 1766099) B1766099
theorem B1177419 : Blo 1176405 1177419 := bstep (se 1 (by rfl) ⟨883064, by rfl⟩ : syracuseStep 1177419 = 1766129) B1766129
theorem B5658443 : Blo 1176405 5658443 := bstep (se 1 (by rfl) ⟨4243832, by rfl⟩ : syracuseStep 5658443 = 8487665) B8487665
theorem B1177431 : Blo 1176405 1177431 := bstep (se 1 (by rfl) ⟨883073, by rfl⟩ : syracuseStep 1177431 = 1766147) B1766147
theorem B1767257 : Blo 1176405 1767257 := bstep (se 2 (by rfl) ⟨662721, by rfl⟩ : syracuseStep 1767257 = 1325443) B1325443
theorem B1177451 : Blo 1176405 1177451 := bstep (se 1 (by rfl) ⟨883088, by rfl⟩ : syracuseStep 1177451 = 1766177) B1766177
theorem B1177463 : Blo 1176405 1177463 := bstep (se 1 (by rfl) ⟨883097, by rfl⟩ : syracuseStep 1177463 = 1766195) B1766195
theorem B1177483 : Blo 1176405 1177483 := bstep (se 1 (by rfl) ⟨883112, by rfl⟩ : syracuseStep 1177483 = 1766225) B1766225
theorem B1324939 : Blo 1176405 1324939 := bstep (se 1 (by rfl) ⟨993704, by rfl⟩ : syracuseStep 1324939 = 1987409) B1987409
theorem B1177495 : Blo 1176405 1177495 := bstep (se 1 (by rfl) ⟨883121, by rfl⟩ : syracuseStep 1177495 = 1766243) B1766243
theorem B1177515 : Blo 1176405 1177515 := bstep (se 1 (by rfl) ⟨883136, by rfl⟩ : syracuseStep 1177515 = 1766273) B1766273
theorem B1177527 : Blo 1176405 1177527 := bstep (se 1 (by rfl) ⟨883145, by rfl⟩ : syracuseStep 1177527 = 1766291) B1766291
theorem B5027777 : Blo 1176405 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B2979787 : Blo 1176405 2979787 := bstep (se 1 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 2979787 = 4469681) B4469681
theorem B1177547 : Blo 1176405 1177547 := bstep (se 1 (by rfl) ⟨883160, by rfl⟩ : syracuseStep 1177547 = 1766321) B1766321
theorem B1767371 : Blo 1176405 1767371 := bstep (se 1 (by rfl) ⟨1325528, by rfl⟩ : syracuseStep 1767371 = 2651057) B2651057
theorem B1177559 : Blo 1176405 1177559 := bstep (se 1 (by rfl) ⟨883169, by rfl⟩ : syracuseStep 1177559 = 1766339) B1766339
theorem B1767383 : Blo 1176405 1767383 := bstep (se 1 (by rfl) ⟨1325537, by rfl⟩ : syracuseStep 1767383 = 2651075) B2651075
theorem B1177579 : Blo 1176405 1177579 := bstep (se 1 (by rfl) ⟨883184, by rfl⟩ : syracuseStep 1177579 = 1766369) B1766369
theorem B1177591 : Blo 1176405 1177591 := bstep (se 1 (by rfl) ⟨883193, by rfl⟩ : syracuseStep 1177591 = 1766387) B1766387
theorem B1325047 : Blo 1176405 1325047 := bstep (se 1 (by rfl) ⟨993785, by rfl⟩ : syracuseStep 1325047 = 1987571) B1987571
theorem B1177611 : Blo 1176405 1177611 := bstep (se 1 (by rfl) ⟨883208, by rfl⟩ : syracuseStep 1177611 = 1766417) B1766417
theorem B1177623 : Blo 1176405 1177623 := bstep (se 1 (by rfl) ⟨883217, by rfl⟩ : syracuseStep 1177623 = 1766435) B1766435
theorem B1767449 : Blo 1176405 1767449 := bstep (se 2 (by rfl) ⟨662793, by rfl⟩ : syracuseStep 1767449 = 1325587) B1325587
theorem B1177643 : Blo 1176405 1177643 := bstep (se 1 (by rfl) ⟨883232, by rfl⟩ : syracuseStep 1177643 = 1766465) B1766465
theorem B4470835 : Blo 1176405 4470835 := bstep (se 1 (by rfl) ⟨3353126, by rfl⟩ : syracuseStep 4470835 = 6706253) B6706253
theorem B1177655 : Blo 1176405 1177655 := bstep (se 1 (by rfl) ⟨883241, by rfl⟩ : syracuseStep 1177655 = 1766483) B1766483
theorem B1177675 : Blo 1176405 1177675 := bstep (se 1 (by rfl) ⟨883256, by rfl⟩ : syracuseStep 1177675 = 1766513) B1766513
theorem B1177687 : Blo 1176405 1177687 := bstep (se 1 (by rfl) ⟨883265, by rfl⟩ : syracuseStep 1177687 = 1766531) B1766531
theorem B2979929 : Blo 1176405 2979929 := bstep (se 2 (by rfl) ⟨1117473, by rfl⟩ : syracuseStep 2979929 = 2234947) B2234947
theorem B1177707 : Blo 1176405 1177707 := bstep (se 1 (by rfl) ⟨883280, by rfl⟩ : syracuseStep 1177707 = 1766561) B1766561
theorem B1177719 : Blo 1176405 1177719 := bstep (se 1 (by rfl) ⟨883289, by rfl⟩ : syracuseStep 1177719 = 1766579) B1766579
theorem B1177739 : Blo 1176405 1177739 := bstep (se 1 (by rfl) ⟨883304, by rfl⟩ : syracuseStep 1177739 = 1766609) B1766609
theorem B1767563 : Blo 1176405 1767563 := bstep (se 1 (by rfl) ⟨1325672, by rfl⟩ : syracuseStep 1767563 = 2651345) B2651345
theorem B1177751 : Blo 1176405 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B1767575 : Blo 1176405 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B1177771 : Blo 1176405 1177771 := bstep (se 1 (by rfl) ⟨883328, by rfl⟩ : syracuseStep 1177771 = 1766657) B1766657
theorem B1325227 : Blo 1176405 1325227 := bstep (se 1 (by rfl) ⟨993920, by rfl⟩ : syracuseStep 1325227 = 1987841) B1987841
theorem B1177783 : Blo 1176405 1177783 := bstep (se 1 (by rfl) ⟨883337, by rfl⟩ : syracuseStep 1177783 = 1766675) B1766675
theorem B1489099 : Blo 1176405 1489099 := bstep (se 1 (by rfl) ⟨1116824, by rfl⟩ : syracuseStep 1489099 = 2233649) B2233649
theorem B1177803 : Blo 1176405 1177803 := bstep (se 1 (by rfl) ⟨883352, by rfl⟩ : syracuseStep 1177803 = 1766705) B1766705
theorem B1177815 : Blo 1176405 1177815 := bstep (se 1 (by rfl) ⟨883361, by rfl⟩ : syracuseStep 1177815 = 1766723) B1766723
theorem B1177835 : Blo 1176405 1177835 := bstep (se 1 (by rfl) ⟨883376, by rfl⟩ : syracuseStep 1177835 = 1766753) B1766753
theorem B1177847 : Blo 1176405 1177847 := bstep (se 1 (by rfl) ⟨883385, by rfl⟩ : syracuseStep 1177847 = 1766771) B1766771
theorem B1341707 : Blo 1176405 1341707 := bstep (se 1 (by rfl) ⟨1006280, by rfl⟩ : syracuseStep 1341707 = 2012561) B2012561
theorem B1177867 : Blo 1176405 1177867 := bstep (se 1 (by rfl) ⟨883400, by rfl⟩ : syracuseStep 1177867 = 1766801) B1766801
theorem B5028119 : Blo 1176405 5028119 := bstep (se 1 (by rfl) ⟨3771089, by rfl⟩ : syracuseStep 5028119 = 7542179) B7542179
theorem B1177879 : Blo 1176405 1177879 := bstep (se 1 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 1177879 = 1766819) B1766819
theorem B1325335 : Blo 1176405 1325335 := bstep (se 1 (by rfl) ⟨994001, by rfl⟩ : syracuseStep 1325335 = 1988003) B1988003
theorem B1177899 : Blo 1176405 1177899 := bstep (se 1 (by rfl) ⟨883424, by rfl⟩ : syracuseStep 1177899 = 1766849) B1766849
theorem B1177911 : Blo 1176405 1177911 := bstep (se 1 (by rfl) ⟨883433, by rfl⟩ : syracuseStep 1177911 = 1766867) B1766867
theorem B1177931 : Blo 1176405 1177931 := bstep (se 1 (by rfl) ⟨883448, by rfl⟩ : syracuseStep 1177931 = 1766897) B1766897
theorem B1177943 : Blo 1176405 1177943 := bstep (se 1 (by rfl) ⟨883457, by rfl⟩ : syracuseStep 1177943 = 1766915) B1766915
theorem B1177963 : Blo 1176405 1177963 := bstep (se 1 (by rfl) ⟨883472, by rfl⟩ : syracuseStep 1177963 = 1766945) B1766945
theorem B68802929 : Blo 1176405 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B1177975 : Blo 1176405 1177975 := bstep (se 1 (by rfl) ⟨883481, by rfl⟩ : syracuseStep 1177975 = 1766963) B1766963
theorem B1177995 : Blo 1176405 1177995 := bstep (se 1 (by rfl) ⟨883496, by rfl⟩ : syracuseStep 1177995 = 1766993) B1766993
theorem B1178007 : Blo 1176405 1178007 := bstep (se 1 (by rfl) ⟨883505, by rfl⟩ : syracuseStep 1178007 = 1767011) B1767011
theorem B1178027 : Blo 1176405 1178027 := bstep (se 1 (by rfl) ⟨883520, by rfl⟩ : syracuseStep 1178027 = 1767041) B1767041
theorem B3627443 : Blo 1176405 3627443 := bstep (se 1 (by rfl) ⟨2720582, by rfl⟩ : syracuseStep 3627443 = 5441165) B5441165
theorem B2234803 : Blo 1176405 2234803 := bstep (se 1 (by rfl) ⟨1676102, by rfl⟩ : syracuseStep 2234803 = 3352205) B3352205
theorem B1178039 : Blo 1176405 1178039 := bstep (se 1 (by rfl) ⟨883529, by rfl⟩ : syracuseStep 1178039 = 1767059) B1767059
theorem B1178059 : Blo 1176405 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B1325515 : Blo 1176405 1325515 := bstep (se 1 (by rfl) ⟨994136, by rfl⟩ : syracuseStep 1325515 = 1988273) B1988273
theorem B1489367 : Blo 1176405 1489367 := bstep (se 1 (by rfl) ⟨1117025, by rfl⟩ : syracuseStep 1489367 = 2234051) B2234051
theorem B1178071 : Blo 1176405 1178071 := bstep (se 1 (by rfl) ⟨883553, by rfl⟩ : syracuseStep 1178071 = 1767107) B1767107
theorem B1178091 : Blo 1176405 1178091 := bstep (se 1 (by rfl) ⟨883568, by rfl⟩ : syracuseStep 1178091 = 1767137) B1767137
theorem B1178103 : Blo 1176405 1178103 := bstep (se 1 (by rfl) ⟨883577, by rfl⟩ : syracuseStep 1178103 = 1767155) B1767155
theorem B1178123 : Blo 1176405 1178123 := bstep (se 1 (by rfl) ⟨883592, by rfl⟩ : syracuseStep 1178123 = 1767185) B1767185
theorem B36239885 : Blo 1176405 36239885 := bstep (se 3 (by rfl) ⟨6794978, by rfl⟩ : syracuseStep 36239885 = 13589957) B13589957
theorem B1178135 : Blo 1176405 1178135 := bstep (se 1 (by rfl) ⟨883601, by rfl⟩ : syracuseStep 1178135 = 1767203) B1767203
theorem B1178155 : Blo 1176405 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B1178167 : Blo 1176405 1178167 := bstep (se 1 (by rfl) ⟨883625, by rfl⟩ : syracuseStep 1178167 = 1767251) B1767251
theorem B1325623 : Blo 1176405 1325623 := bstep (se 1 (by rfl) ⟨994217, by rfl⟩ : syracuseStep 1325623 = 1988435) B1988435
theorem B1178187 : Blo 1176405 1178187 := bstep (se 1 (by rfl) ⟨883640, by rfl⟩ : syracuseStep 1178187 = 1767281) B1767281
theorem B1178199 : Blo 1176405 1178199 := bstep (se 1 (by rfl) ⟨883649, by rfl⟩ : syracuseStep 1178199 = 1767299) B1767299
theorem B1178219 : Blo 1176405 1178219 := bstep (se 1 (by rfl) ⟨883664, by rfl⟩ : syracuseStep 1178219 = 1767329) B1767329
theorem B1178231 : Blo 1176405 1178231 := bstep (se 1 (by rfl) ⟨883673, by rfl⟩ : syracuseStep 1178231 = 1767347) B1767347
theorem B1178251 : Blo 1176405 1178251 := bstep (se 1 (by rfl) ⟨883688, by rfl⟩ : syracuseStep 1178251 = 1767377) B1767377
theorem B1178263 : Blo 1176405 1178263 := bstep (se 1 (by rfl) ⟨883697, by rfl⟩ : syracuseStep 1178263 = 1767395) B1767395
theorem B1178283 : Blo 1176405 1178283 := bstep (se 1 (by rfl) ⟨883712, by rfl⟩ : syracuseStep 1178283 = 1767425) B1767425
theorem B1178295 : Blo 1176405 1178295 := bstep (se 1 (by rfl) ⟨883721, by rfl⟩ : syracuseStep 1178295 = 1767443) B1767443
theorem B1178315 : Blo 1176405 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B1178327 : Blo 1176405 1178327 := bstep (se 1 (by rfl) ⟨883745, by rfl⟩ : syracuseStep 1178327 = 1767491) B1767491
theorem B1178347 : Blo 1176405 1178347 := bstep (se 1 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 1178347 = 1767521) B1767521
theorem B1178359 : Blo 1176405 1178359 := bstep (se 1 (by rfl) ⟨883769, by rfl⟩ : syracuseStep 1178359 = 1767539) B1767539
theorem B4840195 : Blo 1176405 4840195 := bstep (se 1 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 4840195 = 7260293) B7260293
theorem B2120459 : Blo 1176405 2120459 := bstep (se 1 (by rfl) ⟨1590344, by rfl⟩ : syracuseStep 2120459 = 3180689) B3180689
theorem B1178379 : Blo 1176405 1178379 := bstep (se 1 (by rfl) ⟨883784, by rfl⟩ : syracuseStep 1178379 = 1767569) B1767569
theorem B5094161 : Blo 1176405 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B1178391 : Blo 1176405 1178391 := bstep (se 1 (by rfl) ⟨883793, by rfl⟩ : syracuseStep 1178391 = 1767587) B1767587
theorem B3971915 : Blo 1176405 3971915 := bstep (se 1 (by rfl) ⟨2978936, by rfl⟩ : syracuseStep 3971915 = 5957873) B5957873
theorem B5962571 : Blo 1176405 5962571 := bstep (se 1 (by rfl) ⟨4471928, by rfl⟩ : syracuseStep 5962571 = 8943857) B8943857
theorem B20380517 : Blo 1176405 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B2235251 : Blo 1176405 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B2980759 : Blo 1176405 2980759 := bstep (se 1 (by rfl) ⟨2235569, by rfl⟩ : syracuseStep 2980759 = 4471139) B4471139
theorem B2235289 : Blo 1176405 2235289 := bstep (se 2 (by rfl) ⟨838233, by rfl⟩ : syracuseStep 2235289 = 1676467) B1676467
theorem B4422593 : Blo 1176405 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B54393817 : Blo 1176405 54393817 := bstep (se 2 (by rfl) ⟨20397681, by rfl⟩ : syracuseStep 54393817 = 40795363) B40795363
theorem B12729419 : Blo 1176405 12729419 := bstep (se 1 (by rfl) ⟨9547064, by rfl⟩ : syracuseStep 12729419 = 19094129) B19094129
theorem B3972185 : Blo 1176405 3972185 := bstep (se 2 (by rfl) ⟨1489569, by rfl⟩ : syracuseStep 3972185 = 2979139) B2979139
theorem B1490071 : Blo 1176405 1490071 := bstep (se 1 (by rfl) ⟨1117553, by rfl⟩ : syracuseStep 1490071 = 2235107) B2235107
theorem B10058903 : Blo 1176405 10058903 := bstep (se 1 (by rfl) ⟨7544177, by rfl⟩ : syracuseStep 10058903 = 15088355) B15088355
theorem B10747085 : Blo 1176405 10747085 := bstep (se 3 (by rfl) ⟨2015078, by rfl⟩ : syracuseStep 10747085 = 4030157) B4030157
theorem B2120921 : Blo 1176405 2120921 := bstep (se 2 (by rfl) ⟨795345, by rfl⟩ : syracuseStep 2120921 = 1590691) B1590691
theorem B5659865 : Blo 1176405 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B4472081 : Blo 1176405 4472081 := bstep (se 2 (by rfl) ⟨1677030, by rfl⟩ : syracuseStep 4472081 = 3354061) B3354061
theorem B4242763 : Blo 1176405 4242763 := bstep (se 1 (by rfl) ⟨3182072, by rfl⟩ : syracuseStep 4242763 = 6364145) B6364145
theorem B2981195 : Blo 1176405 2981195 := bstep (se 1 (by rfl) ⟨2235896, by rfl⟩ : syracuseStep 2981195 = 4471793) B4471793
theorem B2235737 : Blo 1176405 2235737 := bstep (se 2 (by rfl) ⟨838401, by rfl⟩ : syracuseStep 2235737 = 1676803) B1676803
theorem B2121203 : Blo 1176405 2121203 := bstep (se 1 (by rfl) ⟨1590902, by rfl⟩ : syracuseStep 2121203 = 3181805) B3181805
theorem B4242995 : Blo 1176405 4242995 := bstep (se 1 (by rfl) ⟨3182246, by rfl⟩ : syracuseStep 4242995 = 6364493) B6364493
theorem B3063361 : Blo 1176405 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B8937053 : Blo 1176405 8937053 := bstep (se 3 (by rfl) ⟨1675697, by rfl⟩ : syracuseStep 8937053 = 3351395) B3351395
theorem B2981569 : Blo 1176405 2981569 := bstep (se 2 (by rfl) ⟨1118088, by rfl⟩ : syracuseStep 2981569 = 2236177) B2236177
theorem B9060101 : Blo 1176405 9060101 := bstep (se 4 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 9060101 = 1698769) B1698769
theorem B10190609 : Blo 1176405 10190609 := bstep (se 2 (by rfl) ⟨3821478, by rfl⟩ : syracuseStep 10190609 = 7642957) B7642957
theorem B3972887 : Blo 1176405 3972887 := bstep (se 1 (by rfl) ⟨2979665, by rfl⟩ : syracuseStep 3972887 = 5959331) B5959331
theorem B4472779 : Blo 1176405 4472779 := bstep (se 1 (by rfl) ⟨3354584, by rfl⟩ : syracuseStep 4472779 = 6709169) B6709169
theorem B1490987 : Blo 1176405 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B14311541 : Blo 1176405 14311541 := bstep (se 5 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 14311541 = 1341707) B1341707
theorem B2982035 : Blo 1176405 2982035 := bstep (se 1 (by rfl) ⟨2236526, by rfl⟩ : syracuseStep 2982035 = 4473053) B4473053
theorem B28639433 : Blo 1176405 28639433 := bstep (se 2 (by rfl) ⟨10739787, by rfl⟩ : syracuseStep 28639433 = 21479575) B21479575
theorem B5955929 : Blo 1176405 5955929 := bstep (se 2 (by rfl) ⟨2233473, by rfl⟩ : syracuseStep 5955929 = 4466947) B4466947
theorem B2982329 : Blo 1176405 2982329 := bstep (se 2 (by rfl) ⟨1118373, by rfl⟩ : syracuseStep 2982329 = 2236747) B2236747
theorem B14311889 : Blo 1176405 14311889 := bstep (se 2 (by rfl) ⟨5366958, by rfl⟩ : syracuseStep 14311889 = 10733917) B10733917
theorem B3973643 : Blo 1176405 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B3973751 : Blo 1176405 3973751 := bstep (se 1 (by rfl) ⟨2980313, by rfl⟩ : syracuseStep 3973751 = 5960627) B5960627
theorem B2122529 : Blo 1176405 2122529 := bstep (se 2 (by rfl) ⟨795948, by rfl⟩ : syracuseStep 2122529 = 1591897) B1591897
theorem B4653883 : Blo 1176405 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B3580807 : Blo 1176405 3580807 := bstep (se 1 (by rfl) ⟨2685605, by rfl⟩ : syracuseStep 3580807 = 5371211) B5371211
theorem B2647187 : Blo 1176405 2647187 := bstep (se 1 (by rfl) ⟨1985390, by rfl⟩ : syracuseStep 2647187 = 3970781) B3970781
theorem B2647241 : Blo 1176405 2647241 := bstep (se 2 (by rfl) ⟨992715, by rfl⟩ : syracuseStep 2647241 = 1985431) B1985431
theorem B3974345 : Blo 1176405 3974345 := bstep (se 2 (by rfl) ⟨1490379, by rfl⟩ : syracuseStep 3974345 = 2980759) B2980759
theorem B5965001 : Blo 1176405 5965001 := bstep (se 2 (by rfl) ⟨2236875, by rfl⟩ : syracuseStep 5965001 = 4473751) B4473751
theorem B72525089 : Blo 1176405 72525089 := bstep (se 2 (by rfl) ⟨27196908, by rfl⟩ : syracuseStep 72525089 = 54393817) B54393817
theorem B3351851 : Blo 1176405 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B11306425 : Blo 1176405 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B7538179 : Blo 1176405 7538179 := bstep (se 1 (by rfl) ⟨5653634, by rfl⟩ : syracuseStep 7538179 = 11307269) B11307269
theorem B3352079 : Blo 1176405 3352079 := bstep (se 1 (by rfl) ⟨2514059, by rfl⟩ : syracuseStep 3352079 = 5028119) B5028119
theorem B5031467 : Blo 1176405 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B45868619 : Blo 1176405 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B2418295 : Blo 1176405 2418295 := bstep (se 1 (by rfl) ⟨1813721, by rfl⟩ : syracuseStep 2418295 = 3627443) B3627443
theorem B24159923 : Blo 1176405 24159923 := bstep (se 1 (by rfl) ⟨18119942, by rfl⟩ : syracuseStep 24159923 = 36239885) B36239885
theorem B22628069 : Blo 1176405 22628069 := bstep (se 4 (by rfl) ⟨2121381, by rfl⟩ : syracuseStep 22628069 = 4242763) B4242763
theorem B6792997 : Blo 1176405 6792997 := bstep (se 4 (by rfl) ⟨636843, by rfl⟩ : syracuseStep 6792997 = 1273687) B1273687
theorem B5662553 : Blo 1176405 5662553 := bstep (se 2 (by rfl) ⟨2123457, by rfl⟩ : syracuseStep 5662553 = 4246915) B4246915
theorem B5654387 : Blo 1176405 5654387 := bstep (se 1 (by rfl) ⟨4240790, by rfl⟩ : syracuseStep 5654387 = 8481581) B8481581
theorem B2647943 : Blo 1176405 2647943 := bstep (se 1 (by rfl) ⟨1985957, by rfl⟩ : syracuseStep 2647943 = 3971915) B3971915
theorem B3975047 : Blo 1176405 3975047 := bstep (se 1 (by rfl) ⟨2981285, by rfl⟩ : syracuseStep 3975047 = 5962571) B5962571
theorem B5654557 : Blo 1176405 5654557 := bstep (se 3 (by rfl) ⟨1060229, by rfl⟩ : syracuseStep 5654557 = 2120459) B2120459
theorem B4245533 : Blo 1176405 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B2648123 : Blo 1176405 2648123 := bstep (se 1 (by rfl) ⟨1986092, by rfl⟩ : syracuseStep 2648123 = 3972185) B3972185
theorem B2648249 : Blo 1176405 2648249 := bstep (se 2 (by rfl) ⟨993093, by rfl⟩ : syracuseStep 2648249 = 1986187) B1986187
theorem B3975425 : Blo 1176405 3975425 := bstep (se 2 (by rfl) ⟨1490784, by rfl⟩ : syracuseStep 3975425 = 2981569) B2981569
theorem B2828663 : Blo 1176405 2828663 := bstep (se 1 (by rfl) ⟨2121497, by rfl⟩ : syracuseStep 2828663 = 4242995) B4242995
theorem B5958035 : Blo 1176405 5958035 := bstep (se 1 (by rfl) ⟨4468526, by rfl⟩ : syracuseStep 5958035 = 8937053) B8937053
theorem B2386361 : Blo 1176405 2386361 := bstep (se 2 (by rfl) ⟨894885, by rfl⟩ : syracuseStep 2386361 = 1789771) B1789771
theorem B6040067 : Blo 1176405 6040067 := bstep (se 1 (by rfl) ⟨4530050, by rfl⟩ : syracuseStep 6040067 = 9060101) B9060101
theorem B6793739 : Blo 1176405 6793739 := bstep (se 1 (by rfl) ⟨5095304, by rfl⟩ : syracuseStep 6793739 = 10190609) B10190609
theorem B2648591 : Blo 1176405 2648591 := bstep (se 1 (by rfl) ⟨1986443, by rfl⟩ : syracuseStep 2648591 = 3972887) B3972887
theorem B2648609 : Blo 1176405 2648609 := bstep (se 2 (by rfl) ⟨993228, by rfl⟩ : syracuseStep 2648609 = 1986457) B1986457
theorem B22645291 : Blo 1176405 22645291 := bstep (se 1 (by rfl) ⟨16983968, by rfl⟩ : syracuseStep 22645291 = 33967937) B33967937
theorem B13404851 : Blo 1176405 13404851 := bstep (se 1 (by rfl) ⟨10053638, by rfl⟩ : syracuseStep 13404851 = 20107277) B20107277
theorem B10062629 : Blo 1176405 10062629 := bstep (se 4 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 10062629 = 1886743) B1886743
theorem B1985323 : Blo 1176405 1985323 := bstep (se 1 (by rfl) ⟨1488992, by rfl⟩ : syracuseStep 1985323 = 2977985) B2977985
theorem B1698619 : Blo 1176405 1698619 := bstep (se 1 (by rfl) ⟨1273964, by rfl⟩ : syracuseStep 1698619 = 2547929) B2547929
theorem B2648951 : Blo 1176405 2648951 := bstep (se 1 (by rfl) ⟨1986713, by rfl⟩ : syracuseStep 2648951 = 3973427) B3973427
theorem B4533127 : Blo 1176405 4533127 := bstep (se 1 (by rfl) ⟨3399845, by rfl⟩ : syracuseStep 4533127 = 6799691) B6799691
theorem B3353491 : Blo 1176405 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B38742947 : Blo 1176405 38742947 := bstep (se 1 (by rfl) ⟨29057210, by rfl⟩ : syracuseStep 38742947 = 58114421) B58114421
theorem B1985465 : Blo 1176405 1985465 := bstep (se 2 (by rfl) ⟨744549, by rfl⟩ : syracuseStep 1985465 = 1489099) B1489099
theorem B2649131 : Blo 1176405 2649131 := bstep (se 1 (by rfl) ⟨1986848, by rfl⟩ : syracuseStep 2649131 = 3973697) B3973697
theorem B3976235 : Blo 1176405 3976235 := bstep (se 1 (by rfl) ⟨2982176, by rfl⟩ : syracuseStep 3976235 = 5964353) B5964353
theorem B1887275 : Blo 1176405 1887275 := bstep (se 1 (by rfl) ⟨1415456, by rfl⟩ : syracuseStep 1887275 = 2830913) B2830913
theorem B3353719 : Blo 1176405 3353719 := bstep (se 1 (by rfl) ⟨2515289, by rfl⟩ : syracuseStep 3353719 = 5030579) B5030579
theorem B1592507 : Blo 1176405 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B28658893 : Blo 1176405 28658893 := bstep (se 3 (by rfl) ⟨5373542, by rfl⟩ : syracuseStep 28658893 = 10747085) B10747085
theorem B1764623 : Blo 1176405 1764623 := bstep (se 1 (by rfl) ⟨1323467, by rfl⟩ : syracuseStep 1764623 = 2646935) B2646935
theorem B1764665 : Blo 1176405 1764665 := bstep (se 2 (by rfl) ⟨661749, by rfl⟩ : syracuseStep 1764665 = 1323499) B1323499
theorem B1764743 : Blo 1176405 1764743 := bstep (se 1 (by rfl) ⟨1323557, by rfl⟩ : syracuseStep 1764743 = 2647115) B2647115
theorem B2649491 : Blo 1176405 2649491 := bstep (se 1 (by rfl) ⟨1987118, by rfl⟩ : syracuseStep 2649491 = 3974237) B3974237
theorem B1764779 : Blo 1176405 1764779 := bstep (se 1 (by rfl) ⟨1323584, by rfl⟩ : syracuseStep 1764779 = 2647169) B2647169
theorem B1764809 : Blo 1176405 1764809 := bstep (se 2 (by rfl) ⟨661803, by rfl⟩ : syracuseStep 1764809 = 1323607) B1323607
theorem B2649545 : Blo 1176405 2649545 := bstep (se 2 (by rfl) ⟨993579, by rfl⟩ : syracuseStep 2649545 = 1987159) B1987159
theorem B1764923 : Blo 1176405 1764923 := bstep (se 1 (by rfl) ⟨1323692, by rfl⟩ : syracuseStep 1764923 = 2647385) B2647385
theorem B1764983 : Blo 1176405 1764983 := bstep (se 1 (by rfl) ⟨1323737, by rfl⟩ : syracuseStep 1764983 = 2647475) B2647475
theorem B1986167 : Blo 1176405 1986167 := bstep (se 1 (by rfl) ⟨1489625, by rfl⟩ : syracuseStep 1986167 = 2979251) B2979251
theorem B1765007 : Blo 1176405 1765007 := bstep (se 1 (by rfl) ⟨1323755, by rfl⟩ : syracuseStep 1765007 = 2647511) B2647511
theorem B2829971 : Blo 1176405 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B12906161 : Blo 1176405 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B1765049 : Blo 1176405 1765049 := bstep (se 2 (by rfl) ⟨661893, by rfl⟩ : syracuseStep 1765049 = 1323787) B1323787
theorem B1765127 : Blo 1176405 1765127 := bstep (se 1 (by rfl) ⟨1323845, by rfl⟩ : syracuseStep 1765127 = 2647691) B2647691
theorem B1765163 : Blo 1176405 1765163 := bstep (se 1 (by rfl) ⟨1323872, by rfl⟩ : syracuseStep 1765163 = 2647745) B2647745
theorem B1765193 : Blo 1176405 1765193 := bstep (se 2 (by rfl) ⟨661947, by rfl⟩ : syracuseStep 1765193 = 1323895) B1323895
theorem B8941427 : Blo 1176405 8941427 := bstep (se 1 (by rfl) ⟨6706070, by rfl⟩ : syracuseStep 8941427 = 13412141) B13412141
theorem B3772295 : Blo 1176405 3772295 := bstep (se 1 (by rfl) ⟨2829221, by rfl⟩ : syracuseStep 3772295 = 5658443) B5658443
theorem B1765307 : Blo 1176405 1765307 := bstep (se 1 (by rfl) ⟨1323980, by rfl⟩ : syracuseStep 1765307 = 2647961) B2647961
theorem B1765367 : Blo 1176405 1765367 := bstep (se 1 (by rfl) ⟨1324025, by rfl⟩ : syracuseStep 1765367 = 2648051) B2648051
theorem B2977793 : Blo 1176405 2977793 := bstep (se 2 (by rfl) ⟨1116672, by rfl⟩ : syracuseStep 2977793 = 2233345) B2233345
theorem B1765391 : Blo 1176405 1765391 := bstep (se 1 (by rfl) ⟨1324043, by rfl⟩ : syracuseStep 1765391 = 2648087) B2648087
theorem B6041623 : Blo 1176405 6041623 := bstep (se 1 (by rfl) ⟨4531217, by rfl⟩ : syracuseStep 6041623 = 9062435) B9062435
theorem B1765433 : Blo 1176405 1765433 := bstep (se 2 (by rfl) ⟨662037, by rfl⟩ : syracuseStep 1765433 = 1324075) B1324075
theorem B1986619 : Blo 1176405 1986619 := bstep (se 1 (by rfl) ⟨1489964, by rfl⟩ : syracuseStep 1986619 = 2979929) B2979929
theorem B4304963 : Blo 1176405 4304963 := bstep (se 1 (by rfl) ⟨3228722, by rfl⟩ : syracuseStep 4304963 = 6457445) B6457445
theorem B2830423 : Blo 1176405 2830423 := bstep (se 1 (by rfl) ⟨2122817, by rfl⟩ : syracuseStep 2830423 = 4245635) B4245635
theorem B12243077 : Blo 1176405 12243077 := bstep (se 4 (by rfl) ⟨1147788, by rfl⟩ : syracuseStep 12243077 = 2295577) B2295577
theorem B1765511 : Blo 1176405 1765511 := bstep (se 1 (by rfl) ⟨1324133, by rfl⟩ : syracuseStep 1765511 = 2648267) B2648267
theorem B2650247 : Blo 1176405 2650247 := bstep (se 1 (by rfl) ⟨1987685, by rfl⟩ : syracuseStep 2650247 = 3975371) B3975371
theorem B1765547 : Blo 1176405 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B1765577 : Blo 1176405 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B1986761 : Blo 1176405 1986761 := bstep (se 2 (by rfl) ⟨745035, by rfl⟩ : syracuseStep 1986761 = 1490071) B1490071
theorem B1765691 : Blo 1176405 1765691 := bstep (se 1 (by rfl) ⟨1324268, by rfl⟩ : syracuseStep 1765691 = 2648537) B2648537
theorem B2650427 : Blo 1176405 2650427 := bstep (se 1 (by rfl) ⟨1987820, by rfl⟩ : syracuseStep 2650427 = 3975641) B3975641
theorem B3354995 : Blo 1176405 3354995 := bstep (se 1 (by rfl) ⟨2516246, by rfl⟩ : syracuseStep 3354995 = 5032493) B5032493
theorem B2978167 : Blo 1176405 2978167 := bstep (se 1 (by rfl) ⟨2233625, by rfl⟩ : syracuseStep 2978167 = 4467251) B4467251
theorem B1765751 : Blo 1176405 1765751 := bstep (se 1 (by rfl) ⟨1324313, by rfl⟩ : syracuseStep 1765751 = 2648627) B2648627
theorem B1765775 : Blo 1176405 1765775 := bstep (se 1 (by rfl) ⟨1324331, by rfl⟩ : syracuseStep 1765775 = 2648663) B2648663
theorem B1765817 : Blo 1176405 1765817 := bstep (se 2 (by rfl) ⟨662181, by rfl⟩ : syracuseStep 1765817 = 1324363) B1324363
theorem B2650553 : Blo 1176405 2650553 := bstep (se 2 (by rfl) ⟨993957, by rfl⟩ : syracuseStep 2650553 = 1987915) B1987915
theorem B1765895 : Blo 1176405 1765895 := bstep (se 1 (by rfl) ⟨1324421, by rfl⟩ : syracuseStep 1765895 = 2648843) B2648843
theorem B3396107 : Blo 1176405 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B1323535 : Blo 1176405 1323535 := bstep (se 1 (by rfl) ⟨992651, by rfl⟩ : syracuseStep 1323535 = 1985303) B1985303
theorem B1765931 : Blo 1176405 1765931 := bstep (se 1 (by rfl) ⟨1324448, by rfl⟩ : syracuseStep 1765931 = 2648897) B2648897
theorem B6369835 : Blo 1176405 6369835 := bstep (se 1 (by rfl) ⟨4777376, by rfl⟩ : syracuseStep 6369835 = 9554753) B9554753
theorem B13587011 : Blo 1176405 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B1765961 : Blo 1176405 1765961 := bstep (se 2 (by rfl) ⟨662235, by rfl⟩ : syracuseStep 1765961 = 1324471) B1324471
theorem B1766075 : Blo 1176405 1766075 := bstep (se 1 (by rfl) ⟨1324556, by rfl⟩ : syracuseStep 1766075 = 2649113) B2649113
theorem B3355337 : Blo 1176405 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B1766135 : Blo 1176405 1766135 := bstep (se 1 (by rfl) ⟨1324601, by rfl⟩ : syracuseStep 1766135 = 2649203) B2649203
theorem B4084481 : Blo 1176405 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B1766159 : Blo 1176405 1766159 := bstep (se 1 (by rfl) ⟨1324619, by rfl⟩ : syracuseStep 1766159 = 2649239) B2649239
theorem B6705935 : Blo 1176405 6705935 := bstep (se 1 (by rfl) ⟨5029451, by rfl⟩ : syracuseStep 6705935 = 10058903) B10058903
theorem B2650895 : Blo 1176405 2650895 := bstep (se 1 (by rfl) ⟨1988171, by rfl⟩ : syracuseStep 2650895 = 3976343) B3976343
theorem B2650913 : Blo 1176405 2650913 := bstep (se 2 (by rfl) ⟨994092, by rfl⟩ : syracuseStep 2650913 = 1988185) B1988185
theorem B2978603 : Blo 1176405 2978603 := bstep (se 1 (by rfl) ⟨2233952, by rfl⟩ : syracuseStep 2978603 = 4467905) B4467905
theorem B1766201 : Blo 1176405 1766201 := bstep (se 2 (by rfl) ⟨662325, by rfl⟩ : syracuseStep 1766201 = 1324651) B1324651
theorem B1413947 : Blo 1176405 1413947 := bstep (se 1 (by rfl) ⟨1060460, by rfl⟩ : syracuseStep 1413947 = 2120921) B2120921
theorem B3773243 : Blo 1176405 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B3355451 : Blo 1176405 3355451 := bstep (se 1 (by rfl) ⟨2516588, by rfl⟩ : syracuseStep 3355451 = 5033177) B5033177
theorem B1176455 : Blo 1176405 1176455 := bstep (se 1 (by rfl) ⟨882341, by rfl⟩ : syracuseStep 1176455 = 1764683) B1764683
theorem B1766279 : Blo 1176405 1766279 := bstep (se 1 (by rfl) ⟨1324709, by rfl⟩ : syracuseStep 1766279 = 2649419) B2649419
theorem B1987463 : Blo 1176405 1987463 := bstep (se 1 (by rfl) ⟨1490597, by rfl⟩ : syracuseStep 1987463 = 2981195) B2981195
theorem B1176463 : Blo 1176405 1176463 := bstep (se 1 (by rfl) ⟨882347, by rfl⟩ : syracuseStep 1176463 = 1764695) B1764695
theorem B4469651 : Blo 1176405 4469651 := bstep (se 1 (by rfl) ⟨3352238, by rfl⟩ : syracuseStep 4469651 = 6704477) B6704477
theorem B1766315 : Blo 1176405 1766315 := bstep (se 1 (by rfl) ⟨1324736, by rfl⟩ : syracuseStep 1766315 = 2649473) B2649473
theorem B3355577 : Blo 1176405 3355577 := bstep (se 2 (by rfl) ⟨1258341, by rfl⟩ : syracuseStep 3355577 = 2516683) B2516683
theorem B1176507 : Blo 1176405 1176507 := bstep (se 1 (by rfl) ⟨882380, by rfl⟩ : syracuseStep 1176507 = 1764761) B1764761
theorem B1766345 : Blo 1176405 1766345 := bstep (se 2 (by rfl) ⟨662379, by rfl⟩ : syracuseStep 1766345 = 1324759) B1324759
theorem B1414135 : Blo 1176405 1414135 := bstep (se 1 (by rfl) ⟨1060601, by rfl⟩ : syracuseStep 1414135 = 2121203) B2121203
theorem B1176583 : Blo 1176405 1176583 := bstep (se 1 (by rfl) ⟨882437, by rfl⟩ : syracuseStep 1176583 = 1764875) B1764875
theorem B1324039 : Blo 1176405 1324039 := bstep (se 1 (by rfl) ⟨993029, by rfl⟩ : syracuseStep 1324039 = 1986059) B1986059
theorem B1176591 : Blo 1176405 1176591 := bstep (se 1 (by rfl) ⟨882443, by rfl⟩ : syracuseStep 1176591 = 1764887) B1764887
theorem B1176635 : Blo 1176405 1176635 := bstep (se 1 (by rfl) ⟨882476, by rfl⟩ : syracuseStep 1176635 = 1764953) B1764953
theorem B1766459 : Blo 1176405 1766459 := bstep (se 1 (by rfl) ⟨1324844, by rfl⟩ : syracuseStep 1766459 = 2649689) B2649689
theorem B1766519 : Blo 1176405 1766519 := bstep (se 1 (by rfl) ⟨1324889, by rfl⟩ : syracuseStep 1766519 = 2649779) B2649779
theorem B1815671 : Blo 1176405 1815671 := bstep (se 1 (by rfl) ⟨1361753, by rfl⟩ : syracuseStep 1815671 = 2723507) B2723507
theorem B2651255 : Blo 1176405 2651255 := bstep (se 1 (by rfl) ⟨1988441, by rfl⟩ : syracuseStep 2651255 = 3976883) B3976883
theorem B1176711 : Blo 1176405 1176711 := bstep (se 1 (by rfl) ⟨882533, by rfl⟩ : syracuseStep 1176711 = 1765067) B1765067
theorem B1176719 : Blo 1176405 1176719 := bstep (se 1 (by rfl) ⟨882539, by rfl⟩ : syracuseStep 1176719 = 1765079) B1765079
theorem B1766543 : Blo 1176405 1766543 := bstep (se 1 (by rfl) ⟨1324907, by rfl⟩ : syracuseStep 1766543 = 2649815) B2649815
theorem B1766585 : Blo 1176405 1766585 := bstep (se 2 (by rfl) ⟨662469, by rfl⟩ : syracuseStep 1766585 = 1324939) B1324939
theorem B1176763 : Blo 1176405 1176763 := bstep (se 1 (by rfl) ⟨882572, by rfl⟩ : syracuseStep 1176763 = 1765145) B1765145
theorem B1324219 : Blo 1176405 1324219 := bstep (se 1 (by rfl) ⟨993164, by rfl⟩ : syracuseStep 1324219 = 1986329) B1986329
theorem B1176839 : Blo 1176405 1176839 := bstep (se 1 (by rfl) ⟨882629, by rfl⟩ : syracuseStep 1176839 = 1765259) B1765259
theorem B1766663 : Blo 1176405 1766663 := bstep (se 1 (by rfl) ⟨1324997, by rfl⟩ : syracuseStep 1766663 = 2649995) B2649995
theorem B1176847 : Blo 1176405 1176847 := bstep (se 1 (by rfl) ⟨882635, by rfl⟩ : syracuseStep 1176847 = 1765271) B1765271
theorem B3773729 : Blo 1176405 3773729 := bstep (se 2 (by rfl) ⟨1415148, by rfl⟩ : syracuseStep 3773729 = 2830297) B2830297
theorem B1766699 : Blo 1176405 1766699 := bstep (se 1 (by rfl) ⟨1325024, by rfl⟩ : syracuseStep 1766699 = 2650049) B2650049
theorem B1176891 : Blo 1176405 1176891 := bstep (se 1 (by rfl) ⟨882668, by rfl⟩ : syracuseStep 1176891 = 1765337) B1765337
theorem B1766729 : Blo 1176405 1766729 := bstep (se 2 (by rfl) ⟨662523, by rfl⟩ : syracuseStep 1766729 = 1325047) B1325047
theorem B1176967 : Blo 1176405 1176967 := bstep (se 1 (by rfl) ⟨882725, by rfl⟩ : syracuseStep 1176967 = 1765451) B1765451
theorem B1176975 : Blo 1176405 1176975 := bstep (se 1 (by rfl) ⟨882731, by rfl⟩ : syracuseStep 1176975 = 1765463) B1765463
theorem B2233747 : Blo 1176405 2233747 := bstep (se 1 (by rfl) ⟨1675310, by rfl⟩ : syracuseStep 2233747 = 3350621) B3350621
theorem B3970457 : Blo 1176405 3970457 := bstep (se 2 (by rfl) ⟨1488921, by rfl⟩ : syracuseStep 3970457 = 2977843) B2977843
theorem B5961113 : Blo 1176405 5961113 := bstep (se 2 (by rfl) ⟨2235417, by rfl⟩ : syracuseStep 5961113 = 4470835) B4470835
theorem B1177019 : Blo 1176405 1177019 := bstep (se 1 (by rfl) ⟨882764, by rfl⟩ : syracuseStep 1177019 = 1765529) B1765529
theorem B1766843 : Blo 1176405 1766843 := bstep (se 1 (by rfl) ⟨1325132, by rfl⟩ : syracuseStep 1766843 = 2650265) B2650265
theorem B9057757 : Blo 1176405 9057757 := bstep (se 3 (by rfl) ⟨1698329, by rfl⟩ : syracuseStep 9057757 = 3396659) B3396659
theorem B1676791 : Blo 1176405 1676791 := bstep (se 1 (by rfl) ⟨1257593, by rfl⟩ : syracuseStep 1676791 = 2515187) B2515187
theorem B1766903 : Blo 1176405 1766903 := bstep (se 1 (by rfl) ⟨1325177, by rfl⟩ : syracuseStep 1766903 = 2650355) B2650355
theorem B1177095 : Blo 1176405 1177095 := bstep (se 1 (by rfl) ⟨882821, by rfl⟩ : syracuseStep 1177095 = 1765643) B1765643
theorem B1177103 : Blo 1176405 1177103 := bstep (se 1 (by rfl) ⟨882827, by rfl⟩ : syracuseStep 1177103 = 1765655) B1765655
theorem B1766927 : Blo 1176405 1766927 := bstep (se 1 (by rfl) ⟨1325195, by rfl⟩ : syracuseStep 1766927 = 2650391) B2650391
theorem B1988111 : Blo 1176405 1988111 := bstep (se 1 (by rfl) ⟨1491083, by rfl⟩ : syracuseStep 1988111 = 2982167) B2982167
theorem B1766969 : Blo 1176405 1766969 := bstep (se 2 (by rfl) ⟨662613, by rfl⟩ : syracuseStep 1766969 = 1325227) B1325227
theorem B1177147 : Blo 1176405 1177147 := bstep (se 1 (by rfl) ⟨882860, by rfl⟩ : syracuseStep 1177147 = 1765721) B1765721
theorem B4773437 : Blo 1176405 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B5658173 : Blo 1176405 5658173 := bstep (se 3 (by rfl) ⟨1060907, by rfl⟩ : syracuseStep 5658173 = 2121815) B2121815
theorem B2979443 : Blo 1176405 2979443 := bstep (se 1 (by rfl) ⟨2234582, by rfl⟩ : syracuseStep 2979443 = 4469165) B4469165
theorem B2233975 : Blo 1176405 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B2979463 : Blo 1176405 2979463 := bstep (se 1 (by rfl) ⟨2234597, by rfl⟩ : syracuseStep 2979463 = 4469195) B4469195
theorem B1177223 : Blo 1176405 1177223 := bstep (se 1 (by rfl) ⟨882917, by rfl⟩ : syracuseStep 1177223 = 1765835) B1765835
theorem B1767047 : Blo 1176405 1767047 := bstep (se 1 (by rfl) ⟨1325285, by rfl⟩ : syracuseStep 1767047 = 2650571) B2650571
theorem B1177231 : Blo 1176405 1177231 := bstep (se 1 (by rfl) ⟨882923, by rfl⟩ : syracuseStep 1177231 = 1765847) B1765847
theorem B1324687 : Blo 1176405 1324687 := bstep (se 1 (by rfl) ⟨993515, by rfl⟩ : syracuseStep 1324687 = 1987031) B1987031
theorem B1767083 : Blo 1176405 1767083 := bstep (se 1 (by rfl) ⟨1325312, by rfl⟩ : syracuseStep 1767083 = 2650625) B2650625
theorem B1177275 : Blo 1176405 1177275 := bstep (se 1 (by rfl) ⟨882956, by rfl⟩ : syracuseStep 1177275 = 1765913) B1765913
theorem B1767113 : Blo 1176405 1767113 := bstep (se 2 (by rfl) ⟨662667, by rfl⟩ : syracuseStep 1767113 = 1325335) B1325335
theorem B1177351 : Blo 1176405 1177351 := bstep (se 1 (by rfl) ⟨883013, by rfl⟩ : syracuseStep 1177351 = 1766027) B1766027
theorem B1177359 : Blo 1176405 1177359 := bstep (se 1 (by rfl) ⟨883019, by rfl⟩ : syracuseStep 1177359 = 1766039) B1766039
theorem B1177403 : Blo 1176405 1177403 := bstep (se 1 (by rfl) ⟨883052, by rfl⟩ : syracuseStep 1177403 = 1766105) B1766105
theorem B1767227 : Blo 1176405 1767227 := bstep (se 1 (by rfl) ⟨1325420, by rfl⟩ : syracuseStep 1767227 = 2650841) B2650841
theorem B12719987 : Blo 1176405 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B4241267 : Blo 1176405 4241267 := bstep (se 1 (by rfl) ⟨3180950, by rfl⟩ : syracuseStep 4241267 = 6361901) B6361901
theorem B1767287 : Blo 1176405 1767287 := bstep (se 1 (by rfl) ⟨1325465, by rfl⟩ : syracuseStep 1767287 = 2650931) B2650931
theorem B1177479 : Blo 1176405 1177479 := bstep (se 1 (by rfl) ⟨883109, by rfl⟩ : syracuseStep 1177479 = 1766219) B1766219
theorem B1177487 : Blo 1176405 1177487 := bstep (se 1 (by rfl) ⟨883115, by rfl⟩ : syracuseStep 1177487 = 1766231) B1766231
theorem B1767311 : Blo 1176405 1767311 := bstep (se 1 (by rfl) ⟨1325483, by rfl⟩ : syracuseStep 1767311 = 2650967) B2650967
theorem B2979737 : Blo 1176405 2979737 := bstep (se 2 (by rfl) ⟨1117401, by rfl⟩ : syracuseStep 2979737 = 2234803) B2234803
theorem B1767353 : Blo 1176405 1767353 := bstep (se 2 (by rfl) ⟨662757, by rfl⟩ : syracuseStep 1767353 = 1325515) B1325515
theorem B1177531 : Blo 1176405 1177531 := bstep (se 1 (by rfl) ⟨883148, by rfl⟩ : syracuseStep 1177531 = 1766297) B1766297
theorem B1177607 : Blo 1176405 1177607 := bstep (se 1 (by rfl) ⟨883205, by rfl⟩ : syracuseStep 1177607 = 1766411) B1766411
theorem B1767431 : Blo 1176405 1767431 := bstep (se 1 (by rfl) ⟨1325573, by rfl⟩ : syracuseStep 1767431 = 2651147) B2651147
theorem B7157771 : Blo 1176405 7157771 := bstep (se 1 (by rfl) ⟨5368328, by rfl⟩ : syracuseStep 7157771 = 10736657) B10736657
theorem B1177615 : Blo 1176405 1177615 := bstep (se 1 (by rfl) ⟨883211, by rfl⟩ : syracuseStep 1177615 = 1766423) B1766423
theorem B1767467 : Blo 1176405 1767467 := bstep (se 1 (by rfl) ⟨1325600, by rfl⟩ : syracuseStep 1767467 = 2651201) B2651201
theorem B2979899 : Blo 1176405 2979899 := bstep (se 1 (by rfl) ⟨2234924, by rfl⟩ : syracuseStep 2979899 = 4469849) B4469849
theorem B1177659 : Blo 1176405 1177659 := bstep (se 1 (by rfl) ⟨883244, by rfl⟩ : syracuseStep 1177659 = 1766489) B1766489
theorem B1767497 : Blo 1176405 1767497 := bstep (se 2 (by rfl) ⟨662811, by rfl⟩ : syracuseStep 1767497 = 1325623) B1325623
theorem B3971159 : Blo 1176405 3971159 := bstep (se 1 (by rfl) ⟨2978369, by rfl⟩ : syracuseStep 3971159 = 5956739) B5956739
theorem B1611911 : Blo 1176405 1611911 := bstep (se 1 (by rfl) ⟨1208933, by rfl⟩ : syracuseStep 1611911 = 2417867) B2417867
theorem B1177735 : Blo 1176405 1177735 := bstep (se 1 (by rfl) ⟨883301, by rfl⟩ : syracuseStep 1177735 = 1766603) B1766603
theorem B1325191 : Blo 1176405 1325191 := bstep (se 1 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 1325191 = 1987787) B1987787
theorem B1177743 : Blo 1176405 1177743 := bstep (se 1 (by rfl) ⟨883307, by rfl⟩ : syracuseStep 1177743 = 1766615) B1766615
theorem B1177787 : Blo 1176405 1177787 := bstep (se 1 (by rfl) ⟨883340, by rfl⟩ : syracuseStep 1177787 = 1766681) B1766681
theorem B6707393 : Blo 1176405 6707393 := bstep (se 2 (by rfl) ⟨2515272, by rfl⟩ : syracuseStep 6707393 = 5030545) B5030545
theorem B3184841 : Blo 1176405 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B1177863 : Blo 1176405 1177863 := bstep (se 1 (by rfl) ⟨883397, by rfl⟩ : syracuseStep 1177863 = 1766795) B1766795
theorem B2980111 : Blo 1176405 2980111 := bstep (se 1 (by rfl) ⟨2235083, by rfl⟩ : syracuseStep 2980111 = 4470167) B4470167
theorem B1177871 : Blo 1176405 1177871 := bstep (se 1 (by rfl) ⟨883403, by rfl⟩ : syracuseStep 1177871 = 1766807) B1766807
theorem B1489195 : Blo 1176405 1489195 := bstep (se 1 (by rfl) ⟨1116896, by rfl⟩ : syracuseStep 1489195 = 2233793) B2233793
theorem B1177915 : Blo 1176405 1177915 := bstep (se 1 (by rfl) ⟨883436, by rfl⟩ : syracuseStep 1177915 = 1766873) B1766873
theorem B1325371 : Blo 1176405 1325371 := bstep (se 1 (by rfl) ⟨994028, by rfl⟩ : syracuseStep 1325371 = 1988057) B1988057
theorem B6453593 : Blo 1176405 6453593 := bstep (se 2 (by rfl) ⟨2420097, by rfl⟩ : syracuseStep 6453593 = 4840195) B4840195
theorem B3676535 : Blo 1176405 3676535 := bstep (se 1 (by rfl) ⟨2757401, by rfl⟩ : syracuseStep 3676535 = 5514803) B5514803
theorem B1177991 : Blo 1176405 1177991 := bstep (se 1 (by rfl) ⟨883493, by rfl⟩ : syracuseStep 1177991 = 1766987) B1766987
theorem B1177999 : Blo 1176405 1177999 := bstep (se 1 (by rfl) ⟨883499, by rfl⟩ : syracuseStep 1177999 = 1766999) B1766999
theorem B9066937 : Blo 1176405 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B1178043 : Blo 1176405 1178043 := bstep (se 1 (by rfl) ⟨883532, by rfl⟩ : syracuseStep 1178043 = 1767065) B1767065
theorem B1178119 : Blo 1176405 1178119 := bstep (se 1 (by rfl) ⟨883589, by rfl⟩ : syracuseStep 1178119 = 1767179) B1767179
theorem B4471307 : Blo 1176405 4471307 := bstep (se 1 (by rfl) ⟨3353480, by rfl⟩ : syracuseStep 4471307 = 6706961) B6706961
theorem B1489423 : Blo 1176405 1489423 := bstep (se 1 (by rfl) ⟨1117067, by rfl⟩ : syracuseStep 1489423 = 2234135) B2234135
theorem B1178127 : Blo 1176405 1178127 := bstep (se 1 (by rfl) ⟨883595, by rfl⟩ : syracuseStep 1178127 = 1767191) B1767191
theorem B1677839 : Blo 1176405 1677839 := bstep (se 1 (by rfl) ⟨1258379, by rfl⟩ : syracuseStep 1677839 = 2516759) B2516759
theorem B2980385 : Blo 1176405 2980385 := bstep (se 2 (by rfl) ⟨1117644, by rfl⟩ : syracuseStep 2980385 = 2235289) B2235289
theorem B1178171 : Blo 1176405 1178171 := bstep (se 1 (by rfl) ⟨883628, by rfl⟩ : syracuseStep 1178171 = 1767257) B1767257
theorem B3971645 : Blo 1176405 3971645 := bstep (se 3 (by rfl) ⟨744683, by rfl⟩ : syracuseStep 3971645 = 1489367) B1489367
theorem B1178247 : Blo 1176405 1178247 := bstep (se 1 (by rfl) ⟨883685, by rfl⟩ : syracuseStep 1178247 = 1767371) B1767371
theorem B1178255 : Blo 1176405 1178255 := bstep (se 1 (by rfl) ⟨883691, by rfl⟩ : syracuseStep 1178255 = 1767383) B1767383
theorem B1178299 : Blo 1176405 1178299 := bstep (se 1 (by rfl) ⟨883724, by rfl⟩ : syracuseStep 1178299 = 1767449) B1767449
theorem B10066625 : Blo 1176405 10066625 := bstep (se 2 (by rfl) ⟨3774984, by rfl⟩ : syracuseStep 10066625 = 7549969) B7549969
theorem B1178375 : Blo 1176405 1178375 := bstep (se 1 (by rfl) ⟨883781, by rfl⟩ : syracuseStep 1178375 = 1767563) B1767563
theorem B1178383 : Blo 1176405 1178383 := bstep (se 1 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 1178383 = 1767575) B1767575
theorem B3103879 : Blo 1176405 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B2235539 : Blo 1176405 2235539 := bstep (se 1 (by rfl) ⟨1676654, by rfl⟩ : syracuseStep 2235539 = 3353309) B3353309
theorem B2235593 : Blo 1176405 2235593 := bstep (se 2 (by rfl) ⟨838347, by rfl⟩ : syracuseStep 2235593 = 1676695) B1676695
theorem B1490167 : Blo 1176405 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B3579151 : Blo 1176405 3579151 := bstep (se 1 (by rfl) ⟨2684363, by rfl⟩ : syracuseStep 3579151 = 5368727) B5368727
theorem B2235691 : Blo 1176405 2235691 := bstep (se 1 (by rfl) ⟨1676768, by rfl⟩ : syracuseStep 2235691 = 3353537) B3353537
theorem B2948395 : Blo 1176405 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B8486279 : Blo 1176405 8486279 := bstep (se 1 (by rfl) ⟨6364709, by rfl⟩ : syracuseStep 8486279 = 12729419) B12729419
theorem B2981387 : Blo 1176405 2981387 := bstep (se 1 (by rfl) ⟨2236040, by rfl⟩ : syracuseStep 2981387 = 4472081) B4472081
theorem B2235919 : Blo 1176405 2235919 := bstep (se 1 (by rfl) ⟨1676939, by rfl⟩ : syracuseStep 2235919 = 3353879) B3353879
theorem B1490491 : Blo 1176405 1490491 := bstep (se 1 (by rfl) ⟨1117868, by rfl⟩ : syracuseStep 1490491 = 2235737) B2235737
theorem B6799049 : Blo 1176405 6799049 := bstep (se 2 (by rfl) ⟨2549643, by rfl⟩ : syracuseStep 6799049 = 5099287) B5099287
theorem B3973049 : Blo 1176405 3973049 := bstep (se 2 (by rfl) ⟨1489893, by rfl⟩ : syracuseStep 3973049 = 2979787) B2979787
theorem B5963705 : Blo 1176405 5963705 := bstep (se 2 (by rfl) ⟨2236389, by rfl⟩ : syracuseStep 5963705 = 4472779) B4472779
theorem B2015161 : Blo 1176405 2015161 := bstep (se 2 (by rfl) ⟨755685, by rfl⟩ : syracuseStep 2015161 = 1511371) B1511371
theorem B2236663 : Blo 1176405 2236663 := bstep (se 1 (by rfl) ⟨1677497, by rfl⟩ : syracuseStep 2236663 = 3354995) B3354995
theorem B3973481 : Blo 1176405 3973481 := bstep (se 2 (by rfl) ⟨1490055, by rfl⟩ : syracuseStep 3973481 = 2980111) B2980111
theorem B2236891 : Blo 1176405 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B2515495 : Blo 1176405 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B2236967 : Blo 1176405 2236967 := bstep (se 1 (by rfl) ⟨1677725, by rfl⟩ : syracuseStep 2236967 = 3355451) B3355451
theorem B2237051 : Blo 1176405 2237051 := bstep (se 1 (by rfl) ⟨1677788, by rfl⟩ : syracuseStep 2237051 = 3355577) B3355577
theorem B2646971 : Blo 1176405 2646971 := bstep (se 1 (by rfl) ⟨1985228, by rfl⟩ : syracuseStep 2646971 = 3970457) B3970457
theorem B3974075 : Blo 1176405 3974075 := bstep (se 1 (by rfl) ⟨2980556, by rfl⟩ : syracuseStep 3974075 = 5961113) B5961113
theorem B2647097 : Blo 1176405 2647097 := bstep (se 2 (by rfl) ⟨992661, by rfl⟩ : syracuseStep 2647097 = 1985323) B1985323
theorem B16106615 : Blo 1176405 16106615 := bstep (se 1 (by rfl) ⟨12079961, by rfl⟩ : syracuseStep 16106615 = 24159923) B24159923
theorem B8479991 : Blo 1176405 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B3769591 : Blo 1176405 3769591 := bstep (se 1 (by rfl) ⟨2827193, by rfl⟩ : syracuseStep 3769591 = 5654387) B5654387
theorem B2827511 : Blo 1176405 2827511 := bstep (se 1 (by rfl) ⟨2120633, by rfl⟩ : syracuseStep 2827511 = 4241267) B4241267
theorem B1885513 : Blo 1176405 1885513 := bstep (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) B1414135
theorem B16106845 : Blo 1176405 16106845 := bstep (se 3 (by rfl) ⟨3020033, by rfl⟩ : syracuseStep 16106845 = 6040067) B6040067
theorem B4474237 : Blo 1176405 4474237 := bstep (se 3 (by rfl) ⟨838919, by rfl⟩ : syracuseStep 4474237 = 1677839) B1677839
theorem B2647439 : Blo 1176405 2647439 := bstep (se 1 (by rfl) ⟨1985579, by rfl⟩ : syracuseStep 2647439 = 3971159) B3971159
theorem B2123227 : Blo 1176405 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B4138505 : Blo 1176405 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B4302395 : Blo 1176405 4302395 := bstep (se 1 (by rfl) ⟨3226796, by rfl⟩ : syracuseStep 4302395 = 6453593) B6453593
theorem B2451023 : Blo 1176405 2451023 := bstep (se 1 (by rfl) ⟨1838267, by rfl⟩ : syracuseStep 2451023 = 3676535) B3676535
theorem B1885775 : Blo 1176405 1885775 := bstep (se 1 (by rfl) ⟨1414331, by rfl⟩ : syracuseStep 1885775 = 2828663) B2828663
theorem B2647763 : Blo 1176405 2647763 := bstep (se 1 (by rfl) ⟨1985822, by rfl⟩ : syracuseStep 2647763 = 3971645) B3971645
theorem B6711083 : Blo 1176405 6711083 := bstep (se 1 (by rfl) ⟨5033312, by rfl⟩ : syracuseStep 6711083 = 10066625) B10066625
theorem B15075233 : Blo 1176405 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B12077009 : Blo 1176405 12077009 := bstep (se 2 (by rfl) ⟨4528878, by rfl⟩ : syracuseStep 12077009 = 9057757) B9057757
theorem B24176677 : Blo 1176405 24176677 := bstep (se 4 (by rfl) ⟨2266563, by rfl⟩ : syracuseStep 24176677 = 4533127) B4533127
theorem B3770525 : Blo 1176405 3770525 := bstep (se 3 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 3770525 = 1413947) B1413947
theorem B15100141 : Blo 1176405 15100141 := bstep (se 3 (by rfl) ⟨2831276, by rfl⟩ : syracuseStep 15100141 = 5662553) B5662553
theorem B1886647 : Blo 1176405 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B8604107 : Blo 1176405 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B4532699 : Blo 1176405 4532699 := bstep (se 1 (by rfl) ⟨3399524, by rfl⟩ : syracuseStep 4532699 = 6799049) B6799049
theorem B2648699 : Blo 1176405 2648699 := bstep (se 1 (by rfl) ⟨1986524, by rfl⟩ : syracuseStep 2648699 = 3973049) B3973049
theorem B3975803 : Blo 1176405 3975803 := bstep (se 1 (by rfl) ⟨2981852, by rfl⟩ : syracuseStep 3975803 = 5963705) B5963705
theorem B1985195 : Blo 1176405 1985195 := bstep (se 1 (by rfl) ⟨1488896, by rfl⟩ : syracuseStep 1985195 = 2977793) B2977793
theorem B8055497 : Blo 1176405 8055497 := bstep (se 2 (by rfl) ⟨3020811, by rfl⟩ : syracuseStep 8055497 = 6041623) B6041623
theorem B7539409 : Blo 1176405 7539409 := bstep (se 2 (by rfl) ⟨2827278, by rfl⟩ : syracuseStep 7539409 = 5654557) B5654557
theorem B2869975 : Blo 1176405 2869975 := bstep (se 1 (by rfl) ⟨2152481, by rfl⟩ : syracuseStep 2869975 = 4304963) B4304963
theorem B2648825 : Blo 1176405 2648825 := bstep (se 2 (by rfl) ⟨993309, by rfl⟩ : syracuseStep 2648825 = 1986619) B1986619
theorem B8162051 : Blo 1176405 8162051 := bstep (se 1 (by rfl) ⟨6121538, by rfl⟩ : syracuseStep 8162051 = 12243077) B12243077
theorem B3975965 : Blo 1176405 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B2649095 : Blo 1176405 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B1985593 : Blo 1176405 1985593 := bstep (se 2 (by rfl) ⟨744597, by rfl⟩ : syracuseStep 1985593 = 1489195) B1489195
theorem B2649167 : Blo 1176405 2649167 := bstep (se 1 (by rfl) ⟨1986875, by rfl⟩ : syracuseStep 2649167 = 3973751) B3973751
theorem B4246685 : Blo 1176405 4246685 := bstep (se 3 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 4246685 = 1592507) B1592507
theorem B2722987 : Blo 1176405 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B1985735 : Blo 1176405 1985735 := bstep (se 1 (by rfl) ⟨1489301, by rfl⟩ : syracuseStep 1985735 = 2978603) B2978603
theorem B1764713 : Blo 1176405 1764713 := bstep (se 2 (by rfl) ⟨661767, by rfl⟩ : syracuseStep 1764713 = 1323535) B1323535
theorem B1985897 : Blo 1176405 1985897 := bstep (se 2 (by rfl) ⟨744711, by rfl⟩ : syracuseStep 1985897 = 1489423) B1489423
theorem B193400237 : Blo 1176405 193400237 := bstep (se 3 (by rfl) ⟨36262544, by rfl⟩ : syracuseStep 193400237 = 72525089) B72525089
theorem B10063277 : Blo 1176405 10063277 := bstep (se 3 (by rfl) ⟨1886864, by rfl⟩ : syracuseStep 10063277 = 3773729) B3773729
theorem B1764791 : Blo 1176405 1764791 := bstep (se 1 (by rfl) ⟨1323593, by rfl⟩ : syracuseStep 1764791 = 2647187) B2647187
theorem B1764827 : Blo 1176405 1764827 := bstep (se 1 (by rfl) ⟨1323620, by rfl⟩ : syracuseStep 1764827 = 2647241) B2647241
theorem B2649563 : Blo 1176405 2649563 := bstep (se 1 (by rfl) ⟨1987172, by rfl⟩ : syracuseStep 2649563 = 3974345) B3974345
theorem B3976667 : Blo 1176405 3976667 := bstep (se 1 (by rfl) ⟨2982500, by rfl⟩ : syracuseStep 3976667 = 5965001) B5965001
theorem B3354311 : Blo 1176405 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B3182291 : Blo 1176405 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B3772115 : Blo 1176405 3772115 := bstep (se 1 (by rfl) ⟨2829086, by rfl⟩ : syracuseStep 3772115 = 5658173) B5658173
theorem B1986295 : Blo 1176405 1986295 := bstep (se 1 (by rfl) ⟨1489721, by rfl⟩ : syracuseStep 1986295 = 2979443) B2979443
theorem B6205177 : Blo 1176405 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B2264825 : Blo 1176405 2264825 := bstep (se 2 (by rfl) ⟨849309, by rfl⟩ : syracuseStep 2264825 = 1698619) B1698619
theorem B15085379 : Blo 1176405 15085379 := bstep (se 1 (by rfl) ⟨11314034, by rfl⟩ : syracuseStep 15085379 = 22628069) B22628069
theorem B1765295 : Blo 1176405 1765295 := bstep (se 1 (by rfl) ⟨1323971, by rfl⟩ : syracuseStep 1765295 = 2647943) B2647943
theorem B2650031 : Blo 1176405 2650031 := bstep (se 1 (by rfl) ⟨1987523, by rfl⟩ : syracuseStep 2650031 = 3975047) B3975047
theorem B1986491 : Blo 1176405 1986491 := bstep (se 1 (by rfl) ⟨1489868, by rfl⟩ : syracuseStep 1986491 = 2979737) B2979737
theorem B4771847 : Blo 1176405 4771847 := bstep (se 1 (by rfl) ⟨3578885, by rfl⟩ : syracuseStep 4771847 = 7157771) B7157771
theorem B1765385 : Blo 1176405 1765385 := bstep (se 2 (by rfl) ⟨662019, by rfl⟩ : syracuseStep 1765385 = 1324039) B1324039
theorem B2830355 : Blo 1176405 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B9056285 : Blo 1176405 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B1765415 : Blo 1176405 1765415 := bstep (se 1 (by rfl) ⟨1324061, by rfl⟩ : syracuseStep 1765415 = 2648123) B2648123
theorem B1986599 : Blo 1176405 1986599 := bstep (se 1 (by rfl) ⟨1489949, by rfl⟩ : syracuseStep 1986599 = 2979899) B2979899
theorem B1765499 : Blo 1176405 1765499 := bstep (se 1 (by rfl) ⟨1324124, by rfl⟩ : syracuseStep 1765499 = 2648249) B2648249
theorem B2650283 : Blo 1176405 2650283 := bstep (se 1 (by rfl) ⟨1987712, by rfl⟩ : syracuseStep 2650283 = 3975425) B3975425
theorem B1765625 : Blo 1176405 1765625 := bstep (se 2 (by rfl) ⟨662109, by rfl⟩ : syracuseStep 1765625 = 1324219) B1324219
theorem B38211857 : Blo 1176405 38211857 := bstep (se 2 (by rfl) ⟨14329446, by rfl⟩ : syracuseStep 38211857 = 28658893) B28658893
theorem B1986889 : Blo 1176405 1986889 := bstep (se 2 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 1986889 = 1490167) B1490167
theorem B1765727 : Blo 1176405 1765727 := bstep (se 1 (by rfl) ⟨1324295, by rfl⟩ : syracuseStep 1765727 = 2648591) B2648591
theorem B4772201 : Blo 1176405 4772201 := bstep (se 2 (by rfl) ⟨1789575, by rfl⟩ : syracuseStep 4772201 = 3579151) B3579151
theorem B1765739 : Blo 1176405 1765739 := bstep (se 1 (by rfl) ⟨1324304, by rfl⟩ : syracuseStep 1765739 = 2648609) B2648609
theorem B1986923 : Blo 1176405 1986923 := bstep (se 1 (by rfl) ⟨1490192, by rfl⟩ : syracuseStep 1986923 = 2980385) B2980385
theorem B2978329 : Blo 1176405 2978329 := bstep (se 2 (by rfl) ⟨1116873, by rfl⟩ : syracuseStep 2978329 = 2233747) B2233747
theorem B1765967 : Blo 1176405 1765967 := bstep (se 1 (by rfl) ⟨1324475, by rfl⟩ : syracuseStep 1765967 = 2648951) B2648951
theorem B1323643 : Blo 1176405 1323643 := bstep (se 1 (by rfl) ⟨992732, by rfl⟩ : syracuseStep 1323643 = 1985465) B1985465
theorem B1766087 : Blo 1176405 1766087 := bstep (se 1 (by rfl) ⟨1324565, by rfl⟩ : syracuseStep 1766087 = 2649131) B2649131
theorem B2650823 : Blo 1176405 2650823 := bstep (se 1 (by rfl) ⟨1988117, by rfl⟩ : syracuseStep 2650823 = 3976235) B3976235
theorem B1258183 : Blo 1176405 1258183 := bstep (se 1 (by rfl) ⟨943637, by rfl⟩ : syracuseStep 1258183 = 1887275) B1887275
theorem B1987321 : Blo 1176405 1987321 := bstep (se 2 (by rfl) ⟨745245, by rfl⟩ : syracuseStep 1987321 = 1490491) B1490491
theorem B2978633 : Blo 1176405 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B3224393 : Blo 1176405 3224393 := bstep (se 2 (by rfl) ⟨1209147, by rfl⟩ : syracuseStep 3224393 = 2418295) B2418295
theorem B1176415 : Blo 1176405 1176415 := bstep (se 1 (by rfl) ⟨882311, by rfl⟩ : syracuseStep 1176415 = 1764623) B1764623
theorem B1766249 : Blo 1176405 1766249 := bstep (se 2 (by rfl) ⟨662343, by rfl⟩ : syracuseStep 1766249 = 1324687) B1324687
theorem B1176443 : Blo 1176405 1176443 := bstep (se 1 (by rfl) ⟨882332, by rfl⟩ : syracuseStep 1176443 = 1764665) B1764665
theorem B1176495 : Blo 1176405 1176495 := bstep (se 1 (by rfl) ⟨882371, by rfl⟩ : syracuseStep 1176495 = 1764743) B1764743
theorem B5657519 : Blo 1176405 5657519 := bstep (se 1 (by rfl) ⟨4243139, by rfl⟩ : syracuseStep 5657519 = 8486279) B8486279
theorem B1766327 : Blo 1176405 1766327 := bstep (se 1 (by rfl) ⟨1324745, by rfl⟩ : syracuseStep 1766327 = 2649491) B2649491
theorem B1176519 : Blo 1176405 1176519 := bstep (se 1 (by rfl) ⟨882389, by rfl⟩ : syracuseStep 1176519 = 1764779) B1764779
theorem B1176539 : Blo 1176405 1176539 := bstep (se 1 (by rfl) ⟨882404, by rfl⟩ : syracuseStep 1176539 = 1764809) B1764809
theorem B1766363 : Blo 1176405 1766363 := bstep (se 1 (by rfl) ⟨1324772, by rfl⟩ : syracuseStep 1766363 = 2649545) B2649545
theorem B1987591 : Blo 1176405 1987591 := bstep (se 1 (by rfl) ⟨1490693, by rfl⟩ : syracuseStep 1987591 = 2981387) B2981387
theorem B1176615 : Blo 1176405 1176615 := bstep (se 1 (by rfl) ⟨882461, by rfl⟩ : syracuseStep 1176615 = 1764923) B1764923
theorem B9057329 : Blo 1176405 9057329 := bstep (se 2 (by rfl) ⟨3396498, by rfl⟩ : syracuseStep 9057329 = 6792997) B6792997
theorem B1176655 : Blo 1176405 1176655 := bstep (se 1 (by rfl) ⟨882491, by rfl⟩ : syracuseStep 1176655 = 1764983) B1764983
theorem B1324111 : Blo 1176405 1324111 := bstep (se 1 (by rfl) ⟨993083, by rfl⟩ : syracuseStep 1324111 = 1986167) B1986167
theorem B1176671 : Blo 1176405 1176671 := bstep (se 1 (by rfl) ⟨882503, by rfl⟩ : syracuseStep 1176671 = 1765007) B1765007
theorem B1176699 : Blo 1176405 1176699 := bstep (se 1 (by rfl) ⟨882524, by rfl⟩ : syracuseStep 1176699 = 1765049) B1765049
theorem B1176751 : Blo 1176405 1176751 := bstep (se 1 (by rfl) ⟨882563, by rfl⟩ : syracuseStep 1176751 = 1765127) B1765127
theorem B1176775 : Blo 1176405 1176775 := bstep (se 1 (by rfl) ⟨882581, by rfl⟩ : syracuseStep 1176775 = 1765163) B1765163
theorem B1176795 : Blo 1176405 1176795 := bstep (se 1 (by rfl) ⟨882596, by rfl⟩ : syracuseStep 1176795 = 1765193) B1765193
theorem B5960951 : Blo 1176405 5960951 := bstep (se 1 (by rfl) ⟨4470713, by rfl⟩ : syracuseStep 5960951 = 8941427) B8941427
theorem B8942885 : Blo 1176405 8942885 := bstep (se 4 (by rfl) ⟨838395, by rfl⟩ : syracuseStep 8942885 = 1676791) B1676791
theorem B1176871 : Blo 1176405 1176871 := bstep (se 1 (by rfl) ⟨882653, by rfl⟩ : syracuseStep 1176871 = 1765307) B1765307
theorem B1176911 : Blo 1176405 1176911 := bstep (se 1 (by rfl) ⟨882683, by rfl⟩ : syracuseStep 1176911 = 1765367) B1765367
theorem B1176927 : Blo 1176405 1176927 := bstep (se 1 (by rfl) ⟨882695, by rfl⟩ : syracuseStep 1176927 = 1765391) B1765391
theorem B1176955 : Blo 1176405 1176955 := bstep (se 1 (by rfl) ⟨882716, by rfl⟩ : syracuseStep 1176955 = 1765433) B1765433
theorem B9541027 : Blo 1176405 9541027 := bstep (se 1 (by rfl) ⟨7155770, by rfl⟩ : syracuseStep 9541027 = 14311541) B14311541
theorem B1177007 : Blo 1176405 1177007 := bstep (se 1 (by rfl) ⟨882755, by rfl⟩ : syracuseStep 1177007 = 1765511) B1765511
theorem B1766831 : Blo 1176405 1766831 := bstep (se 1 (by rfl) ⟨1325123, by rfl⟩ : syracuseStep 1766831 = 2650247) B2650247
theorem B1988023 : Blo 1176405 1988023 := bstep (se 1 (by rfl) ⟨1491017, by rfl⟩ : syracuseStep 1988023 = 2982035) B2982035
theorem B1177031 : Blo 1176405 1177031 := bstep (se 1 (by rfl) ⟨882773, by rfl⟩ : syracuseStep 1177031 = 1765547) B1765547
theorem B3773897 : Blo 1176405 3773897 := bstep (se 2 (by rfl) ⟨1415211, by rfl⟩ : syracuseStep 3773897 = 2830423) B2830423
theorem B1177051 : Blo 1176405 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B19092955 : Blo 1176405 19092955 := bstep (se 1 (by rfl) ⟨14319716, by rfl⟩ : syracuseStep 19092955 = 28639433) B28639433
theorem B1324507 : Blo 1176405 1324507 := bstep (se 1 (by rfl) ⟨993380, by rfl⟩ : syracuseStep 1324507 = 1986761) B1986761
theorem B1766921 : Blo 1176405 1766921 := bstep (se 2 (by rfl) ⟨662595, by rfl⟩ : syracuseStep 1766921 = 1325191) B1325191
theorem B1177127 : Blo 1176405 1177127 := bstep (se 1 (by rfl) ⟨882845, by rfl⟩ : syracuseStep 1177127 = 1765691) B1765691
theorem B1766951 : Blo 1176405 1766951 := bstep (se 1 (by rfl) ⟨1325213, by rfl⟩ : syracuseStep 1766951 = 2650427) B2650427
theorem B3970619 : Blo 1176405 3970619 := bstep (se 1 (by rfl) ⟨2977964, by rfl⟩ : syracuseStep 3970619 = 5955929) B5955929
theorem B1177167 : Blo 1176405 1177167 := bstep (se 1 (by rfl) ⟨882875, by rfl⟩ : syracuseStep 1177167 = 1765751) B1765751
theorem B1177183 : Blo 1176405 1177183 := bstep (se 1 (by rfl) ⟨882887, by rfl⟩ : syracuseStep 1177183 = 1765775) B1765775
theorem B1177211 : Blo 1176405 1177211 := bstep (se 1 (by rfl) ⟨882908, by rfl⟩ : syracuseStep 1177211 = 1765817) B1765817
theorem B1767035 : Blo 1176405 1767035 := bstep (se 1 (by rfl) ⟨1325276, by rfl⟩ : syracuseStep 1767035 = 2650553) B2650553
theorem B1988219 : Blo 1176405 1988219 := bstep (se 1 (by rfl) ⟨1491164, by rfl⟩ : syracuseStep 1988219 = 2982329) B2982329
theorem B9541259 : Blo 1176405 9541259 := bstep (se 1 (by rfl) ⟨7155944, by rfl⟩ : syracuseStep 9541259 = 14311889) B14311889
theorem B1177263 : Blo 1176405 1177263 := bstep (se 1 (by rfl) ⟨882947, by rfl⟩ : syracuseStep 1177263 = 1765895) B1765895
theorem B4298429 : Blo 1176405 4298429 := bstep (se 3 (by rfl) ⟨805955, by rfl⟩ : syracuseStep 4298429 = 1611911) B1611911
theorem B1177287 : Blo 1176405 1177287 := bstep (se 1 (by rfl) ⟨882965, by rfl⟩ : syracuseStep 1177287 = 1765931) B1765931
theorem B9058007 : Blo 1176405 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B1177307 : Blo 1176405 1177307 := bstep (se 1 (by rfl) ⟨882980, by rfl⟩ : syracuseStep 1177307 = 1765961) B1765961
theorem B5961437 : Blo 1176405 5961437 := bstep (se 3 (by rfl) ⟨1117769, by rfl⟩ : syracuseStep 5961437 = 2235539) B2235539
theorem B1767161 : Blo 1176405 1767161 := bstep (se 2 (by rfl) ⟨662685, by rfl⟩ : syracuseStep 1767161 = 1325371) B1325371
theorem B1177383 : Blo 1176405 1177383 := bstep (se 1 (by rfl) ⟨883037, by rfl⟩ : syracuseStep 1177383 = 1766075) B1766075
theorem B3970889 : Blo 1176405 3970889 := bstep (se 2 (by rfl) ⟨1489083, by rfl⟩ : syracuseStep 3970889 = 2978167) B2978167
theorem B1177423 : Blo 1176405 1177423 := bstep (se 1 (by rfl) ⟨883067, by rfl⟩ : syracuseStep 1177423 = 1766135) B1766135
theorem B1177439 : Blo 1176405 1177439 := bstep (se 1 (by rfl) ⟨883079, by rfl⟩ : syracuseStep 1177439 = 1766159) B1766159
theorem B4470623 : Blo 1176405 4470623 := bstep (se 1 (by rfl) ⟨3352967, by rfl⟩ : syracuseStep 4470623 = 6705935) B6705935
theorem B1767263 : Blo 1176405 1767263 := bstep (se 1 (by rfl) ⟨1325447, by rfl⟩ : syracuseStep 1767263 = 2650895) B2650895
theorem B1767275 : Blo 1176405 1767275 := bstep (se 1 (by rfl) ⟨1325456, by rfl⟩ : syracuseStep 1767275 = 2650913) B2650913
theorem B1177467 : Blo 1176405 1177467 := bstep (se 1 (by rfl) ⟨883100, by rfl⟩ : syracuseStep 1177467 = 1766201) B1766201
theorem B12089249 : Blo 1176405 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B1177519 : Blo 1176405 1177519 := bstep (se 1 (by rfl) ⟨883139, by rfl⟩ : syracuseStep 1177519 = 1766279) B1766279
theorem B1324975 : Blo 1176405 1324975 := bstep (se 1 (by rfl) ⟨993731, by rfl⟩ : syracuseStep 1324975 = 1987463) B1987463
theorem B2979767 : Blo 1176405 2979767 := bstep (se 1 (by rfl) ⟨2234825, by rfl⟩ : syracuseStep 2979767 = 4469651) B4469651
theorem B1177543 : Blo 1176405 1177543 := bstep (se 1 (by rfl) ⟨883157, by rfl⟩ : syracuseStep 1177543 = 1766315) B1766315
theorem B1177563 : Blo 1176405 1177563 := bstep (se 1 (by rfl) ⟨883172, by rfl⟩ : syracuseStep 1177563 = 1766345) B1766345
theorem B1177639 : Blo 1176405 1177639 := bstep (se 1 (by rfl) ⟨883229, by rfl⟩ : syracuseStep 1177639 = 1766459) B1766459
theorem B30193721 : Blo 1176405 30193721 := bstep (se 2 (by rfl) ⟨11322645, by rfl⟩ : syracuseStep 30193721 = 22645291) B22645291
theorem B8493113 : Blo 1176405 8493113 := bstep (se 2 (by rfl) ⟨3184917, by rfl⟩ : syracuseStep 8493113 = 6369835) B6369835
theorem B1177679 : Blo 1176405 1177679 := bstep (se 1 (by rfl) ⟨883259, by rfl⟩ : syracuseStep 1177679 = 1766519) B1766519
theorem B1210447 : Blo 1176405 1210447 := bstep (se 1 (by rfl) ⟨907835, by rfl⟩ : syracuseStep 1210447 = 1815671) B1815671
theorem B1767503 : Blo 1176405 1767503 := bstep (se 1 (by rfl) ⟨1325627, by rfl⟩ : syracuseStep 1767503 = 2651255) B2651255
theorem B1177695 : Blo 1176405 1177695 := bstep (se 1 (by rfl) ⟨883271, by rfl⟩ : syracuseStep 1177695 = 1766543) B1766543
theorem B1177723 : Blo 1176405 1177723 := bstep (se 1 (by rfl) ⟨883292, by rfl⟩ : syracuseStep 1177723 = 1766585) B1766585
theorem B1177775 : Blo 1176405 1177775 := bstep (se 1 (by rfl) ⟨883331, by rfl⟩ : syracuseStep 1177775 = 1766663) B1766663
theorem B2234567 : Blo 1176405 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B1177799 : Blo 1176405 1177799 := bstep (se 1 (by rfl) ⟨883349, by rfl⟩ : syracuseStep 1177799 = 1766699) B1766699
theorem B1177819 : Blo 1176405 1177819 := bstep (se 1 (by rfl) ⟨883364, by rfl⟩ : syracuseStep 1177819 = 1766729) B1766729
theorem B1177895 : Blo 1176405 1177895 := bstep (se 1 (by rfl) ⟨883421, by rfl⟩ : syracuseStep 1177895 = 1766843) B1766843
theorem B1177935 : Blo 1176405 1177935 := bstep (se 1 (by rfl) ⟨883451, by rfl⟩ : syracuseStep 1177935 = 1766903) B1766903
theorem B2234719 : Blo 1176405 2234719 := bstep (se 1 (by rfl) ⟨1676039, by rfl⟩ : syracuseStep 2234719 = 3352079) B3352079
theorem B1177951 : Blo 1176405 1177951 := bstep (se 1 (by rfl) ⟨883463, by rfl⟩ : syracuseStep 1177951 = 1766927) B1766927
theorem B1325407 : Blo 1176405 1325407 := bstep (se 1 (by rfl) ⟨994055, by rfl⟩ : syracuseStep 1325407 = 1988111) B1988111
theorem B1177979 : Blo 1176405 1177979 := bstep (se 1 (by rfl) ⟨883484, by rfl⟩ : syracuseStep 1177979 = 1766969) B1766969
theorem B30579079 : Blo 1176405 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B1178031 : Blo 1176405 1178031 := bstep (se 1 (by rfl) ⟨883523, by rfl⟩ : syracuseStep 1178031 = 1767047) B1767047
theorem B1178055 : Blo 1176405 1178055 := bstep (se 1 (by rfl) ⟨883541, by rfl⟩ : syracuseStep 1178055 = 1767083) B1767083
theorem B1178075 : Blo 1176405 1178075 := bstep (se 1 (by rfl) ⟨883556, by rfl⟩ : syracuseStep 1178075 = 1767113) B1767113
theorem B6363629 : Blo 1176405 6363629 := bstep (se 3 (by rfl) ⟨1193180, by rfl⟩ : syracuseStep 6363629 = 2386361) B2386361
theorem B4774409 : Blo 1176405 4774409 := bstep (se 2 (by rfl) ⟨1790403, by rfl⟩ : syracuseStep 4774409 = 3580807) B3580807
theorem B42990101 : Blo 1176405 42990101 := bstep (se 6 (by rfl) ⟨1007580, by rfl⟩ : syracuseStep 42990101 = 2015161) B2015161
theorem B4471321 : Blo 1176405 4471321 := bstep (se 2 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 4471321 = 3353491) B3353491
theorem B1178151 : Blo 1176405 1178151 := bstep (se 1 (by rfl) ⟨883613, by rfl⟩ : syracuseStep 1178151 = 1767227) B1767227
theorem B1178191 : Blo 1176405 1178191 := bstep (se 1 (by rfl) ⟨883643, by rfl⟩ : syracuseStep 1178191 = 1767287) B1767287
theorem B1178207 : Blo 1176405 1178207 := bstep (se 1 (by rfl) ⟨883655, by rfl⟩ : syracuseStep 1178207 = 1767311) B1767311
theorem B1178235 : Blo 1176405 1178235 := bstep (se 1 (by rfl) ⟨883676, by rfl⟩ : syracuseStep 1178235 = 1767353) B1767353
theorem B1178287 : Blo 1176405 1178287 := bstep (se 1 (by rfl) ⟨883715, by rfl⟩ : syracuseStep 1178287 = 1767431) B1767431
theorem B1178311 : Blo 1176405 1178311 := bstep (se 1 (by rfl) ⟨883733, by rfl⟩ : syracuseStep 1178311 = 1767467) B1767467
theorem B1178331 : Blo 1176405 1178331 := bstep (se 1 (by rfl) ⟨883748, by rfl⟩ : syracuseStep 1178331 = 1767497) B1767497
theorem B4471595 : Blo 1176405 4471595 := bstep (se 1 (by rfl) ⟨3353696, by rfl⟩ : syracuseStep 4471595 = 6707393) B6707393
theorem B4471625 : Blo 1176405 4471625 := bstep (se 2 (by rfl) ⟨1676859, by rfl⟩ : syracuseStep 4471625 = 3353719) B3353719
theorem B3972023 : Blo 1176405 3972023 := bstep (se 1 (by rfl) ⟨2979017, by rfl⟩ : syracuseStep 3972023 = 5958035) B5958035
theorem B4529159 : Blo 1176405 4529159 := bstep (se 1 (by rfl) ⟨3396869, by rfl⟩ : syracuseStep 4529159 = 6793739) B6793739
theorem B2980871 : Blo 1176405 2980871 := bstep (se 1 (by rfl) ⟨2235653, by rfl⟩ : syracuseStep 2980871 = 4471307) B4471307
theorem B2980921 : Blo 1176405 2980921 := bstep (se 2 (by rfl) ⟨1117845, by rfl⟩ : syracuseStep 2980921 = 2235691) B2235691
theorem B3931193 : Blo 1176405 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B8936567 : Blo 1176405 8936567 := bstep (se 1 (by rfl) ⟨6702425, by rfl⟩ : syracuseStep 8936567 = 13404851) B13404851
theorem B6708419 : Blo 1176405 6708419 := bstep (se 1 (by rfl) ⟨5031314, by rfl⟩ : syracuseStep 6708419 = 10062629) B10062629
theorem B25828631 : Blo 1176405 25828631 := bstep (se 1 (by rfl) ⟨19371473, by rfl⟩ : syracuseStep 25828631 = 38742947) B38742947
theorem B10050905 : Blo 1176405 10050905 := bstep (se 2 (by rfl) ⟨3769089, by rfl⟩ : syracuseStep 10050905 = 7538179) B7538179
theorem B2981225 : Blo 1176405 2981225 := bstep (se 2 (by rfl) ⟨1117959, by rfl⟩ : syracuseStep 2981225 = 2235919) B2235919
theorem B5660077 : Blo 1176405 5660077 := bstep (se 3 (by rfl) ⟨1061264, by rfl⟩ : syracuseStep 5660077 = 2122529) B2122529
theorem B1490395 : Blo 1176405 1490395 := bstep (se 1 (by rfl) ⟨1117796, by rfl⟩ : syracuseStep 1490395 = 2235593) B2235593
theorem B3972617 : Blo 1176405 3972617 := bstep (se 2 (by rfl) ⟨1489731, by rfl⟩ : syracuseStep 3972617 = 2979463) B2979463
theorem B2514863 : Blo 1176405 2514863 := bstep (se 1 (by rfl) ⟨1886147, by rfl⟩ : syracuseStep 2514863 = 3772295) B3772295
theorem B6037523 : Blo 1176405 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B32235569 : Blo 1176405 32235569 := bstep (se 2 (by rfl) ⟨12088338, by rfl⟩ : syracuseStep 32235569 = 24176677) B24176677
theorem B2982217 : Blo 1176405 2982217 := bstep (se 2 (by rfl) ⟨1118331, by rfl⟩ : syracuseStep 2982217 = 2236663) B2236663
theorem B1491311 : Blo 1176405 1491311 := bstep (se 1 (by rfl) ⟨1118483, by rfl⟩ : syracuseStep 1491311 = 2236967) B2236967
theorem B6455717 : Blo 1176405 6455717 := bstep (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) B1210447
theorem B1491367 : Blo 1176405 1491367 := bstep (se 1 (by rfl) ⟨1118525, by rfl⟩ : syracuseStep 1491367 = 2237051) B2237051
theorem B40772105 : Blo 1176405 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B2515529 : Blo 1176405 2515529 := bstep (se 2 (by rfl) ⟨943323, by rfl⟩ : syracuseStep 2515529 = 1886647) B1886647
theorem B2982521 : Blo 1176405 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B6038219 : Blo 1176405 6038219 := bstep (se 1 (by rfl) ⟨4528664, by rfl⟩ : syracuseStep 6038219 = 9057329) B9057329
theorem B5653327 : Blo 1176405 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B1885007 : Blo 1176405 1885007 := bstep (se 1 (by rfl) ⟨1413755, by rfl⟩ : syracuseStep 1885007 = 2827511) B2827511
theorem B3973967 : Blo 1176405 3973967 := bstep (se 1 (by rfl) ⟨2980475, by rfl⟩ : syracuseStep 3973967 = 5960951) B5960951
theorem B10052545 : Blo 1176405 10052545 := bstep (se 2 (by rfl) ⟨3769704, by rfl⟩ : syracuseStep 10052545 = 7539409) B7539409
theorem B2515931 : Blo 1176405 2515931 := bstep (se 1 (by rfl) ⟨1886948, by rfl⟩ : syracuseStep 2515931 = 3773897) B3773897
theorem B6710309 : Blo 1176405 6710309 := bstep (se 4 (by rfl) ⟨629091, by rfl⟩ : syracuseStep 6710309 = 1258183) B1258183
theorem B2647079 : Blo 1176405 2647079 := bstep (se 1 (by rfl) ⟨1985309, by rfl⟩ : syracuseStep 2647079 = 3970619) B3970619
theorem B2868263 : Blo 1176405 2868263 := bstep (se 1 (by rfl) ⟨2151197, by rfl⟩ : syracuseStep 2868263 = 4302395) B4302395
theorem B3974291 : Blo 1176405 3974291 := bstep (se 1 (by rfl) ⟨2980718, by rfl⟩ : syracuseStep 3974291 = 5961437) B5961437
theorem B4474055 : Blo 1176405 4474055 := bstep (se 1 (by rfl) ⟨3355541, by rfl⟩ : syracuseStep 4474055 = 6711083) B6711083
theorem B2647259 : Blo 1176405 2647259 := bstep (se 1 (by rfl) ⟨1985444, by rfl⟩ : syracuseStep 2647259 = 3970889) B3970889
theorem B20129147 : Blo 1176405 20129147 := bstep (se 1 (by rfl) ⟨15096860, by rfl⟩ : syracuseStep 20129147 = 30193721) B30193721
theorem B5662075 : Blo 1176405 5662075 := bstep (se 1 (by rfl) ⟨4246556, by rfl⟩ : syracuseStep 5662075 = 8493113) B8493113
theorem B2647457 : Blo 1176405 2647457 := bstep (se 2 (by rfl) ⟨992796, by rfl⟩ : syracuseStep 2647457 = 1985593) B1985593
theorem B3974561 : Blo 1176405 3974561 := bstep (se 2 (by rfl) ⟨1490460, by rfl⟩ : syracuseStep 3974561 = 2980921) B2980921
theorem B5736071 : Blo 1176405 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B11462477 : Blo 1176405 11462477 := bstep (se 3 (by rfl) ⟨2149214, by rfl⟩ : syracuseStep 11462477 = 4298429) B4298429
theorem B5965649 : Blo 1176405 5965649 := bstep (se 2 (by rfl) ⟨2237118, by rfl⟩ : syracuseStep 5965649 = 4474237) B4474237
theorem B21481325 : Blo 1176405 21481325 := bstep (se 3 (by rfl) ⟨4027748, by rfl⟩ : syracuseStep 21481325 = 8055497) B8055497
theorem B7546769 : Blo 1176405 7546769 := bstep (se 2 (by rfl) ⟨2830038, by rfl⟩ : syracuseStep 7546769 = 5660077) B5660077
theorem B2648015 : Blo 1176405 2648015 := bstep (se 1 (by rfl) ⟨1986011, by rfl⟩ : syracuseStep 2648015 = 3972023) B3972023
theorem B5957711 : Blo 1176405 5957711 := bstep (se 1 (by rfl) ⟨4468283, by rfl⟩ : syracuseStep 5957711 = 8936567) B8936567
theorem B2648393 : Blo 1176405 2648393 := bstep (se 2 (by rfl) ⟨993147, by rfl⟩ : syracuseStep 2648393 = 1986295) B1986295
theorem B2648411 : Blo 1176405 2648411 := bstep (se 1 (by rfl) ⟨1986308, by rfl⟩ : syracuseStep 2648411 = 3972617) B3972617
theorem B1509883 : Blo 1176405 1509883 := bstep (se 1 (by rfl) ⟨1132412, by rfl⟩ : syracuseStep 1509883 = 2264825) B2264825
theorem B3181231 : Blo 1176405 3181231 := bstep (se 1 (by rfl) ⟨2385923, by rfl⟩ : syracuseStep 3181231 = 4771847) B4771847
theorem B1886903 : Blo 1176405 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B2648987 : Blo 1176405 2648987 := bstep (se 1 (by rfl) ⟨1986740, by rfl⟩ : syracuseStep 2648987 = 3973481) B3973481
theorem B2649185 : Blo 1176405 2649185 := bstep (se 2 (by rfl) ⟨993444, by rfl⟩ : syracuseStep 2649185 = 1986889) B1986889
theorem B5958845 : Blo 1176405 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B1985755 : Blo 1176405 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B2149595 : Blo 1176405 2149595 := bstep (se 1 (by rfl) ⟨1612196, by rfl⟩ : syracuseStep 2149595 = 3224393) B3224393
theorem B3771679 : Blo 1176405 3771679 := bstep (se 1 (by rfl) ⟨2828759, by rfl⟩ : syracuseStep 3771679 = 5657519) B5657519
theorem B1764647 : Blo 1176405 1764647 := bstep (se 1 (by rfl) ⟨1323485, by rfl⟩ : syracuseStep 1764647 = 2646971) B2646971
theorem B2649383 : Blo 1176405 2649383 := bstep (se 1 (by rfl) ⟨1987037, by rfl⟩ : syracuseStep 2649383 = 3974075) B3974075
theorem B1764731 : Blo 1176405 1764731 := bstep (se 1 (by rfl) ⟨1323548, by rfl⟩ : syracuseStep 1764731 = 2647097) B2647097
theorem B3353993 : Blo 1176405 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B1764857 : Blo 1176405 1764857 := bstep (se 2 (by rfl) ⟨661821, by rfl⟩ : syracuseStep 1764857 = 1323643) B1323643
theorem B1764959 : Blo 1176405 1764959 := bstep (se 1 (by rfl) ⟨1323719, by rfl⟩ : syracuseStep 1764959 = 2647439) B2647439
theorem B12725869 : Blo 1176405 12725869 := bstep (se 3 (by rfl) ⟨2386100, by rfl⟩ : syracuseStep 12725869 = 4772201) B4772201
theorem B2649761 : Blo 1176405 2649761 := bstep (se 2 (by rfl) ⟨993660, by rfl⟩ : syracuseStep 2649761 = 1987321) B1987321
theorem B1634015 : Blo 1176405 1634015 := bstep (se 1 (by rfl) ⟨1225511, by rfl⟩ : syracuseStep 1634015 = 2451023) B2451023
theorem B6360839 : Blo 1176405 6360839 := bstep (se 1 (by rfl) ⟨4770629, by rfl⟩ : syracuseStep 6360839 = 9541259) B9541259
theorem B15306533 : Blo 1176405 15306533 := bstep (se 4 (by rfl) ⟨1434987, by rfl⟩ : syracuseStep 15306533 = 2869975) B2869975
theorem B1765175 : Blo 1176405 1765175 := bstep (se 1 (by rfl) ⟨1323881, by rfl⟩ : syracuseStep 1765175 = 2647763) B2647763
theorem B1986511 : Blo 1176405 1986511 := bstep (se 1 (by rfl) ⟨1489883, by rfl⟩ : syracuseStep 1986511 = 2979767) B2979767
theorem B2650121 : Blo 1176405 2650121 := bstep (se 2 (by rfl) ⟨993795, by rfl⟩ : syracuseStep 2650121 = 1987591) B1987591
theorem B1765481 : Blo 1176405 1765481 := bstep (se 2 (by rfl) ⟨662055, by rfl⟩ : syracuseStep 1765481 = 1324111) B1324111
theorem B5026121 : Blo 1176405 5026121 := bstep (se 2 (by rfl) ⟨1884795, by rfl⟩ : syracuseStep 5026121 = 3769591) B3769591
theorem B3182939 : Blo 1176405 3182939 := bstep (se 1 (by rfl) ⟨2387204, by rfl⟩ : syracuseStep 3182939 = 4774409) B4774409
theorem B28660067 : Blo 1176405 28660067 := bstep (se 1 (by rfl) ⟨21495050, by rfl⟩ : syracuseStep 28660067 = 42990101) B42990101
theorem B1765799 : Blo 1176405 1765799 := bstep (se 1 (by rfl) ⟨1324349, by rfl⟩ : syracuseStep 1765799 = 2648699) B2648699
theorem B2650535 : Blo 1176405 2650535 := bstep (se 1 (by rfl) ⟨1987901, by rfl⟩ : syracuseStep 2650535 = 3975803) B3975803
theorem B1323463 : Blo 1176405 1323463 := bstep (se 1 (by rfl) ⟨992597, by rfl⟩ : syracuseStep 1323463 = 1985195) B1985195
theorem B21475793 : Blo 1176405 21475793 := bstep (se 2 (by rfl) ⟨8053422, by rfl⟩ : syracuseStep 21475793 = 16106845) B16106845
theorem B1765883 : Blo 1176405 1765883 := bstep (se 1 (by rfl) ⟨1324412, by rfl⟩ : syracuseStep 1765883 = 2648825) B2648825
theorem B2650643 : Blo 1176405 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B24154685 : Blo 1176405 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B2650697 : Blo 1176405 2650697 := bstep (se 2 (by rfl) ⟨994011, by rfl⟩ : syracuseStep 2650697 = 1988023) B1988023
theorem B25457273 : Blo 1176405 25457273 := bstep (se 2 (by rfl) ⟨9546477, by rfl⟩ : syracuseStep 25457273 = 19092955) B19092955
theorem B1766009 : Blo 1176405 1766009 := bstep (se 2 (by rfl) ⟨662253, by rfl⟩ : syracuseStep 1766009 = 1324507) B1324507
theorem B1987193 : Blo 1176405 1987193 := bstep (se 2 (by rfl) ⟨745197, by rfl⟩ : syracuseStep 1987193 = 1490395) B1490395
theorem B2830969 : Blo 1176405 2830969 := bstep (se 2 (by rfl) ⟨1061613, by rfl⟩ : syracuseStep 2830969 = 2123227) B2123227
theorem B3019439 : Blo 1176405 3019439 := bstep (se 1 (by rfl) ⟨2264579, by rfl⟩ : syracuseStep 3019439 = 4529159) B4529159
theorem B1766063 : Blo 1176405 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B1987247 : Blo 1176405 1987247 := bstep (se 1 (by rfl) ⟨1490435, by rfl⟩ : syracuseStep 1987247 = 2980871) B2980871
theorem B1766111 : Blo 1176405 1766111 := bstep (se 1 (by rfl) ⟨1324583, by rfl⟩ : syracuseStep 1766111 = 2649167) B2649167
theorem B2831123 : Blo 1176405 2831123 := bstep (se 1 (by rfl) ⟨2123342, by rfl⟩ : syracuseStep 2831123 = 4246685) B4246685
theorem B1323823 : Blo 1176405 1323823 := bstep (se 1 (by rfl) ⟨992867, by rfl⟩ : syracuseStep 1323823 = 1985735) B1985735
theorem B1176475 : Blo 1176405 1176475 := bstep (se 1 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 1176475 = 1764713) B1764713
theorem B1323931 : Blo 1176405 1323931 := bstep (se 1 (by rfl) ⟨992948, by rfl⟩ : syracuseStep 1323931 = 1985897) B1985897
theorem B1987483 : Blo 1176405 1987483 := bstep (se 1 (by rfl) ⟨1490612, by rfl⟩ : syracuseStep 1987483 = 2981225) B2981225
theorem B1176527 : Blo 1176405 1176527 := bstep (se 1 (by rfl) ⟨882395, by rfl⟩ : syracuseStep 1176527 = 1764791) B1764791
theorem B1176551 : Blo 1176405 1176551 := bstep (se 1 (by rfl) ⟨882413, by rfl⟩ : syracuseStep 1176551 = 1764827) B1764827
theorem B1766375 : Blo 1176405 1766375 := bstep (se 1 (by rfl) ⟨1324781, by rfl⟩ : syracuseStep 1766375 = 2649563) B2649563
theorem B2651111 : Blo 1176405 2651111 := bstep (se 1 (by rfl) ⟨1988333, by rfl⟩ : syracuseStep 2651111 = 3976667) B3976667
theorem B10056919 : Blo 1176405 10056919 := bstep (se 1 (by rfl) ⟨7542689, by rfl⟩ : syracuseStep 10056919 = 15085379) B15085379
theorem B1766633 : Blo 1176405 1766633 := bstep (se 2 (by rfl) ⟨662487, by rfl⟩ : syracuseStep 1766633 = 1324975) B1324975
theorem B1176863 : Blo 1176405 1176863 := bstep (se 1 (by rfl) ⟨882647, by rfl⟩ : syracuseStep 1176863 = 1765295) B1765295
theorem B1676575 : Blo 1176405 1676575 := bstep (se 1 (by rfl) ⟨1257431, by rfl⟩ : syracuseStep 1676575 = 2514863) B2514863
theorem B1766687 : Blo 1176405 1766687 := bstep (se 1 (by rfl) ⟨1325015, by rfl⟩ : syracuseStep 1766687 = 2650031) B2650031
theorem B1324327 : Blo 1176405 1324327 := bstep (se 1 (by rfl) ⟨993245, by rfl⟩ : syracuseStep 1324327 = 1986491) B1986491
theorem B1176923 : Blo 1176405 1176923 := bstep (se 1 (by rfl) ⟨882692, by rfl⟩ : syracuseStep 1176923 = 1765385) B1765385
theorem B1176943 : Blo 1176405 1176943 := bstep (se 1 (by rfl) ⟨882707, by rfl⟩ : syracuseStep 1176943 = 1765415) B1765415
theorem B1324399 : Blo 1176405 1324399 := bstep (se 1 (by rfl) ⟨993299, by rfl⟩ : syracuseStep 1324399 = 1986599) B1986599
theorem B1176999 : Blo 1176405 1176999 := bstep (se 1 (by rfl) ⟨882749, by rfl⟩ : syracuseStep 1176999 = 1765499) B1765499
theorem B1766855 : Blo 1176405 1766855 := bstep (se 1 (by rfl) ⟨1325141, by rfl⟩ : syracuseStep 1766855 = 2650283) B2650283
theorem B10483181 : Blo 1176405 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B1177083 : Blo 1176405 1177083 := bstep (se 1 (by rfl) ⟨882812, by rfl⟩ : syracuseStep 1177083 = 1765625) B1765625
theorem B25474571 : Blo 1176405 25474571 := bstep (se 1 (by rfl) ⟨19105928, by rfl⟩ : syracuseStep 25474571 = 38211857) B38211857
theorem B1177151 : Blo 1176405 1177151 := bstep (se 1 (by rfl) ⟨882863, by rfl⟩ : syracuseStep 1177151 = 1765727) B1765727
theorem B1177159 : Blo 1176405 1177159 := bstep (se 1 (by rfl) ⟨882869, by rfl⟩ : syracuseStep 1177159 = 1765739) B1765739
theorem B1324615 : Blo 1176405 1324615 := bstep (se 1 (by rfl) ⟨993461, by rfl⟩ : syracuseStep 1324615 = 1986923) B1986923
theorem B20133521 : Blo 1176405 20133521 := bstep (se 2 (by rfl) ⟨7550070, by rfl⟩ : syracuseStep 20133521 = 15100141) B15100141
theorem B1177311 : Blo 1176405 1177311 := bstep (se 1 (by rfl) ⟨882983, by rfl⟩ : syracuseStep 1177311 = 1765967) B1765967
theorem B2979625 : Blo 1176405 2979625 := bstep (se 2 (by rfl) ⟨1117359, by rfl⟩ : syracuseStep 2979625 = 2234719) B2234719
theorem B1767209 : Blo 1176405 1767209 := bstep (se 2 (by rfl) ⟨662703, by rfl⟩ : syracuseStep 1767209 = 1325407) B1325407
theorem B1177391 : Blo 1176405 1177391 := bstep (se 1 (by rfl) ⟨883043, by rfl⟩ : syracuseStep 1177391 = 1766087) B1766087
theorem B1767215 : Blo 1176405 1767215 := bstep (se 1 (by rfl) ⟨1325411, by rfl⟩ : syracuseStep 1767215 = 2650823) B2650823
theorem B1177499 : Blo 1176405 1177499 := bstep (se 1 (by rfl) ⟨883124, by rfl⟩ : syracuseStep 1177499 = 1766249) B1766249
theorem B1177551 : Blo 1176405 1177551 := bstep (se 1 (by rfl) ⟨883163, by rfl⟩ : syracuseStep 1177551 = 1766327) B1766327
theorem B1177575 : Blo 1176405 1177575 := bstep (se 1 (by rfl) ⟨883181, by rfl⟩ : syracuseStep 1177575 = 1766363) B1766363
theorem B3971105 : Blo 1176405 3971105 := bstep (se 2 (by rfl) ⟨1489164, by rfl⟩ : syracuseStep 3971105 = 2978329) B2978329
theorem B5961761 : Blo 1176405 5961761 := bstep (se 2 (by rfl) ⟨2235660, by rfl⟩ : syracuseStep 5961761 = 4471321) B4471321
theorem B10737743 : Blo 1176405 10737743 := bstep (se 1 (by rfl) ⟨8053307, by rfl⟩ : syracuseStep 10737743 = 16106615) B16106615
theorem B5961923 : Blo 1176405 5961923 := bstep (se 1 (by rfl) ⟨4471442, by rfl⟩ : syracuseStep 5961923 = 8942885) B8942885
theorem B14522597 : Blo 1176405 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B1177887 : Blo 1176405 1177887 := bstep (se 1 (by rfl) ⟨883415, by rfl⟩ : syracuseStep 1177887 = 1766831) B1766831
theorem B2759003 : Blo 1176405 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B1177947 : Blo 1176405 1177947 := bstep (se 1 (by rfl) ⟨883460, by rfl⟩ : syracuseStep 1177947 = 1766921) B1766921
theorem B1177967 : Blo 1176405 1177967 := bstep (se 1 (by rfl) ⟨883475, by rfl⟩ : syracuseStep 1177967 = 1766951) B1766951
theorem B1178023 : Blo 1176405 1178023 := bstep (se 1 (by rfl) ⟨883517, by rfl⟩ : syracuseStep 1178023 = 1767035) B1767035
theorem B1325479 : Blo 1176405 1325479 := bstep (se 1 (by rfl) ⟨994109, by rfl⟩ : syracuseStep 1325479 = 1988219) B1988219
theorem B1178107 : Blo 1176405 1178107 := bstep (se 1 (by rfl) ⟨883580, by rfl⟩ : syracuseStep 1178107 = 1767161) B1767161
theorem B2980415 : Blo 1176405 2980415 := bstep (se 1 (by rfl) ⟨2235311, by rfl⟩ : syracuseStep 2980415 = 4470623) B4470623
theorem B1178175 : Blo 1176405 1178175 := bstep (se 1 (by rfl) ⟨883631, by rfl⟩ : syracuseStep 1178175 = 1767263) B1767263
theorem B1178183 : Blo 1176405 1178183 := bstep (se 1 (by rfl) ⟨883637, by rfl⟩ : syracuseStep 1178183 = 1767275) B1767275
theorem B10050155 : Blo 1176405 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B8059499 : Blo 1176405 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B33094277 : Blo 1176405 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B8051339 : Blo 1176405 8051339 := bstep (se 1 (by rfl) ⟨6038504, by rfl⟩ : syracuseStep 8051339 = 12077009) B12077009
theorem B1178335 : Blo 1176405 1178335 := bstep (se 1 (by rfl) ⟨883751, by rfl⟩ : syracuseStep 1178335 = 1767503) B1767503
theorem B2513683 : Blo 1176405 2513683 := bstep (se 1 (by rfl) ⟨1885262, by rfl⟩ : syracuseStep 2513683 = 3770525) B3770525
theorem B5028733 : Blo 1176405 5028733 := bstep (se 3 (by rfl) ⟨942887, by rfl⟩ : syracuseStep 5028733 = 1885775) B1885775
theorem B3021799 : Blo 1176405 3021799 := bstep (se 1 (by rfl) ⟨2266349, by rfl⟩ : syracuseStep 3021799 = 4532699) B4532699
theorem B4242419 : Blo 1176405 4242419 := bstep (se 1 (by rfl) ⟨3181814, by rfl⟩ : syracuseStep 4242419 = 6363629) B6363629
theorem B2514017 : Blo 1176405 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B8944829 : Blo 1176405 8944829 := bstep (se 3 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 8944829 = 3354311) B3354311
theorem B2981063 : Blo 1176405 2981063 := bstep (se 1 (by rfl) ⟨2235797, by rfl⟩ : syracuseStep 2981063 = 4471595) B4471595
theorem B12721369 : Blo 1176405 12721369 := bstep (se 2 (by rfl) ⟨4770513, by rfl⟩ : syracuseStep 12721369 = 9541027) B9541027
theorem B2981083 : Blo 1176405 2981083 := bstep (se 1 (by rfl) ⟨2235812, by rfl⟩ : syracuseStep 2981083 = 4471625) B4471625
theorem B21765469 : Blo 1176405 21765469 := bstep (se 3 (by rfl) ⟨4081025, by rfl⟩ : syracuseStep 21765469 = 8162051) B8162051
theorem B4472279 : Blo 1176405 4472279 := bstep (se 1 (by rfl) ⟨3354209, by rfl⟩ : syracuseStep 4472279 = 6708419) B6708419
theorem B17219087 : Blo 1176405 17219087 := bstep (se 1 (by rfl) ⟨12914315, by rfl⟩ : syracuseStep 17219087 = 25828631) B25828631
theorem B6700603 : Blo 1176405 6700603 := bstep (se 1 (by rfl) ⟨5025452, by rfl⟩ : syracuseStep 6700603 = 10050905) B10050905
theorem B128933491 : Blo 1176405 128933491 := bstep (se 1 (by rfl) ⟨96700118, by rfl⟩ : syracuseStep 128933491 = 193400237) B193400237
theorem B6708851 : Blo 1176405 6708851 := bstep (se 1 (by rfl) ⟨5031638, by rfl⟩ : syracuseStep 6708851 = 10063277) B10063277
theorem B2121527 : Blo 1176405 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B2514743 : Blo 1176405 2514743 := bstep (se 1 (by rfl) ⟨1886057, by rfl⟩ : syracuseStep 2514743 = 3772115) B3772115
theorem B3350747 : Blo 1176405 3350747 := bstep (se 1 (by rfl) ⟨2513060, by rfl⟩ : syracuseStep 3350747 = 5026121) B5026121
theorem B2121959 : Blo 1176405 2121959 := bstep (se 1 (by rfl) ⟨1591469, by rfl⟩ : syracuseStep 2121959 = 3182939) B3182939
theorem B27181403 : Blo 1176405 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B15098501 : Blo 1176405 15098501 := bstep (se 4 (by rfl) ⟨1415484, by rfl⟩ : syracuseStep 15098501 = 2830969) B2830969
theorem B4473539 : Blo 1176405 4473539 := bstep (se 1 (by rfl) ⟨3355154, by rfl⟩ : syracuseStep 4473539 = 6710309) B6710309
theorem B2982703 : Blo 1176405 2982703 := bstep (se 1 (by rfl) ⟨2237027, by rfl⟩ : syracuseStep 2982703 = 4474055) B4474055
theorem B122266421 : Blo 1176405 122266421 := bstep (se 5 (by rfl) ⟨5731238, by rfl⟩ : syracuseStep 122266421 = 11462477) B11462477
theorem B13419431 : Blo 1176405 13419431 := bstep (se 1 (by rfl) ⟨10064573, by rfl⟩ : syracuseStep 13419431 = 20129147) B20129147
theorem B6988787 : Blo 1176405 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B16983047 : Blo 1176405 16983047 := bstep (se 1 (by rfl) ⟨12737285, by rfl⟩ : syracuseStep 16983047 = 25474571) B25474571
theorem B7537769 : Blo 1176405 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B14320883 : Blo 1176405 14320883 := bstep (se 1 (by rfl) ⟨10740662, by rfl⟩ : syracuseStep 14320883 = 21481325) B21481325
theorem B13403393 : Blo 1176405 13403393 := bstep (se 2 (by rfl) ⟨5026272, by rfl⟩ : syracuseStep 13403393 = 10052545) B10052545
theorem B5031179 : Blo 1176405 5031179 := bstep (se 1 (by rfl) ⟨3773384, by rfl⟩ : syracuseStep 5031179 = 7546769) B7546769
theorem B2647403 : Blo 1176405 2647403 := bstep (se 1 (by rfl) ⟨1985552, by rfl⟩ : syracuseStep 2647403 = 3971105) B3971105
theorem B3974507 : Blo 1176405 3974507 := bstep (se 1 (by rfl) ⟨2980880, by rfl⟩ : syracuseStep 3974507 = 5961761) B5961761
theorem B3974615 : Blo 1176405 3974615 := bstep (se 1 (by rfl) ⟨2980961, by rfl⟩ : syracuseStep 3974615 = 5961923) B5961923
theorem B2647673 : Blo 1176405 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B3974777 : Blo 1176405 3974777 := bstep (se 2 (by rfl) ⟨1490541, by rfl⟩ : syracuseStep 3974777 = 2981083) B2981083
theorem B22062851 : Blo 1176405 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B5367559 : Blo 1176405 5367559 := bstep (se 1 (by rfl) ⟨4025669, by rfl⟩ : syracuseStep 5367559 = 8051339) B8051339
theorem B2828279 : Blo 1176405 2828279 := bstep (se 1 (by rfl) ⟨2121209, by rfl⟩ : syracuseStep 2828279 = 4242419) B4242419
theorem B16967825 : Blo 1176405 16967825 := bstep (se 2 (by rfl) ⟨6362934, by rfl⟩ : syracuseStep 16967825 = 12725869) B12725869
theorem B171911321 : Blo 1176405 171911321 := bstep (se 2 (by rfl) ⟨64466745, by rfl⟩ : syracuseStep 171911321 = 128933491) B128933491
theorem B11479391 : Blo 1176405 11479391 := bstep (se 1 (by rfl) ⟨8609543, by rfl⟩ : syracuseStep 11479391 = 17219087) B17219087
theorem B2648681 : Blo 1176405 2648681 := bstep (se 2 (by rfl) ⟨993255, by rfl⟩ : syracuseStep 2648681 = 1986511) B1986511
theorem B4025015 : Blo 1176405 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B21490379 : Blo 1176405 21490379 := bstep (se 1 (by rfl) ⟨16117784, by rfl⟩ : syracuseStep 21490379 = 32235569) B32235569
theorem B28633981 : Blo 1176405 28633981 := bstep (se 3 (by rfl) ⟨5368871, by rfl⟩ : syracuseStep 28633981 = 10737743) B10737743
theorem B19106711 : Blo 1176405 19106711 := bstep (se 1 (by rfl) ⟨14330033, by rfl⟩ : syracuseStep 19106711 = 28660067) B28660067
theorem B6704045 : Blo 1176405 6704045 := bstep (se 3 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 6704045 = 2514017) B2514017
theorem B4303811 : Blo 1176405 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B3976289 : Blo 1176405 3976289 := bstep (se 2 (by rfl) ⟨1491108, by rfl⟩ : syracuseStep 3976289 = 2982217) B2982217
theorem B4025479 : Blo 1176405 4025479 := bstep (se 1 (by rfl) ⟨3019109, by rfl⟩ : syracuseStep 4025479 = 6038219) B6038219
theorem B1256671 : Blo 1176405 1256671 := bstep (se 1 (by rfl) ⟨942503, by rfl⟩ : syracuseStep 1256671 = 1885007) B1885007
theorem B2649311 : Blo 1176405 2649311 := bstep (se 1 (by rfl) ⟨1986983, by rfl⟩ : syracuseStep 2649311 = 3973967) B3973967
theorem B1764617 : Blo 1176405 1764617 := bstep (se 2 (by rfl) ⟨661731, by rfl⟩ : syracuseStep 1764617 = 1323463) B1323463
theorem B1764719 : Blo 1176405 1764719 := bstep (se 1 (by rfl) ⟨1323539, by rfl⟩ : syracuseStep 1764719 = 2647079) B2647079
theorem B1912175 : Blo 1176405 1912175 := bstep (se 1 (by rfl) ⟨1434131, by rfl⟩ : syracuseStep 1912175 = 2868263) B2868263
theorem B2649527 : Blo 1176405 2649527 := bstep (se 1 (by rfl) ⟨1987145, by rfl⟩ : syracuseStep 2649527 = 3974291) B3974291
theorem B1764839 : Blo 1176405 1764839 := bstep (se 1 (by rfl) ⟨1323629, by rfl⟩ : syracuseStep 1764839 = 2647259) B2647259
theorem B1764971 : Blo 1176405 1764971 := bstep (se 1 (by rfl) ⟨1323728, by rfl⟩ : syracuseStep 1764971 = 2647457) B2647457
theorem B2649707 : Blo 1176405 2649707 := bstep (se 1 (by rfl) ⟨1987280, by rfl⟩ : syracuseStep 2649707 = 3974561) B3974561
theorem B29429365 : Blo 1176405 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B3976829 : Blo 1176405 3976829 := bstep (se 3 (by rfl) ⟨745655, by rfl⟩ : syracuseStep 3976829 = 1491311) B1491311
theorem B1765097 : Blo 1176405 1765097 := bstep (se 2 (by rfl) ⟨661911, by rfl⟩ : syracuseStep 1765097 = 1323823) B1323823
theorem B13422347 : Blo 1176405 13422347 := bstep (se 1 (by rfl) ⟨10066760, by rfl⟩ : syracuseStep 13422347 = 20133521) B20133521
theorem B6704977 : Blo 1176405 6704977 := bstep (se 2 (by rfl) ⟨2514366, by rfl⟩ : syracuseStep 6704977 = 5028733) B5028733
theorem B1765241 : Blo 1176405 1765241 := bstep (se 2 (by rfl) ⟨661965, by rfl⟩ : syracuseStep 1765241 = 1323931) B1323931
theorem B2649977 : Blo 1176405 2649977 := bstep (se 2 (by rfl) ⟨993741, by rfl⟩ : syracuseStep 2649977 = 1987483) B1987483
theorem B3977099 : Blo 1176405 3977099 := bstep (se 1 (by rfl) ⟨2982824, by rfl⟩ : syracuseStep 3977099 = 5965649) B5965649
theorem B1765343 : Blo 1176405 1765343 := bstep (se 1 (by rfl) ⟨1324007, by rfl⟩ : syracuseStep 1765343 = 2648015) B2648015
theorem B13406309 : Blo 1176405 13406309 := bstep (se 4 (by rfl) ⟨1256841, by rfl⟩ : syracuseStep 13406309 = 2513683) B2513683
theorem B1765595 : Blo 1176405 1765595 := bstep (se 1 (by rfl) ⟨1324196, by rfl⟩ : syracuseStep 1765595 = 2648393) B2648393
theorem B1765607 : Blo 1176405 1765607 := bstep (se 1 (by rfl) ⟨1324205, by rfl⟩ : syracuseStep 1765607 = 2648411) B2648411
theorem B16961825 : Blo 1176405 16961825 := bstep (se 2 (by rfl) ⟨6360684, by rfl⟩ : syracuseStep 16961825 = 12721369) B12721369
theorem B1986943 : Blo 1176405 1986943 := bstep (se 1 (by rfl) ⟨1490207, by rfl⟩ : syracuseStep 1986943 = 2980415) B2980415
theorem B1765769 : Blo 1176405 1765769 := bstep (se 2 (by rfl) ⟨662163, by rfl⟩ : syracuseStep 1765769 = 1324327) B1324327
theorem B1257935 : Blo 1176405 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B29020625 : Blo 1176405 29020625 := bstep (se 2 (by rfl) ⟨10882734, by rfl⟩ : syracuseStep 29020625 = 21765469) B21765469
theorem B1765865 : Blo 1176405 1765865 := bstep (se 2 (by rfl) ⟨662199, by rfl⟩ : syracuseStep 1765865 = 1324399) B1324399
theorem B7549433 : Blo 1176405 7549433 := bstep (se 2 (by rfl) ⟨2831037, by rfl⟩ : syracuseStep 7549433 = 5662075) B5662075
theorem B1765991 : Blo 1176405 1765991 := bstep (se 1 (by rfl) ⟨1324493, by rfl⟩ : syracuseStep 1765991 = 2648987) B2648987
theorem B7549661 : Blo 1176405 7549661 := bstep (se 3 (by rfl) ⟨1415561, by rfl⟩ : syracuseStep 7549661 = 2831123) B2831123
theorem B1766123 : Blo 1176405 1766123 := bstep (se 1 (by rfl) ⟨1324592, by rfl⟩ : syracuseStep 1766123 = 2649185) B2649185
theorem B8934137 : Blo 1176405 8934137 := bstep (se 2 (by rfl) ⟨3350301, by rfl⟩ : syracuseStep 8934137 = 6700603) B6700603
theorem B1766153 : Blo 1176405 1766153 := bstep (se 2 (by rfl) ⟨662307, by rfl⟩ : syracuseStep 1766153 = 1324615) B1324615
theorem B1987375 : Blo 1176405 1987375 := bstep (se 1 (by rfl) ⟨1490531, by rfl⟩ : syracuseStep 1987375 = 2981063) B2981063
theorem B1176431 : Blo 1176405 1176431 := bstep (se 1 (by rfl) ⟨882323, by rfl⟩ : syracuseStep 1176431 = 1764647) B1764647
theorem B1766255 : Blo 1176405 1766255 := bstep (se 1 (by rfl) ⟨1324691, by rfl⟩ : syracuseStep 1766255 = 2649383) B2649383
theorem B1176487 : Blo 1176405 1176487 := bstep (se 1 (by rfl) ⟨882365, by rfl⟩ : syracuseStep 1176487 = 1764731) B1764731
theorem B1176571 : Blo 1176405 1176571 := bstep (se 1 (by rfl) ⟨882428, by rfl⟩ : syracuseStep 1176571 = 1764857) B1764857
theorem B1176639 : Blo 1176405 1176639 := bstep (se 1 (by rfl) ⟨882479, by rfl⟩ : syracuseStep 1176639 = 1764959) B1764959
theorem B1766507 : Blo 1176405 1766507 := bstep (se 1 (by rfl) ⟨1324880, by rfl⟩ : syracuseStep 1766507 = 2649761) B2649761
theorem B4240559 : Blo 1176405 4240559 := bstep (se 1 (by rfl) ⟨3180419, by rfl⟩ : syracuseStep 4240559 = 6360839) B6360839
theorem B10204355 : Blo 1176405 10204355 := bstep (se 1 (by rfl) ⟨7653266, by rfl⟩ : syracuseStep 10204355 = 15306533) B15306533
theorem B1176783 : Blo 1176405 1176783 := bstep (se 1 (by rfl) ⟨882587, by rfl⟩ : syracuseStep 1176783 = 1765175) B1765175
theorem B1414351 : Blo 1176405 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B1676495 : Blo 1176405 1676495 := bstep (se 1 (by rfl) ⟨1257371, by rfl⟩ : syracuseStep 1676495 = 2514743) B2514743
theorem B1766747 : Blo 1176405 1766747 := bstep (se 1 (by rfl) ⟨1325060, by rfl⟩ : syracuseStep 1766747 = 2650121) B2650121
theorem B1176987 : Blo 1176405 1176987 := bstep (se 1 (by rfl) ⟨882740, by rfl⟩ : syracuseStep 1176987 = 1765481) B1765481
theorem B1177199 : Blo 1176405 1177199 := bstep (se 1 (by rfl) ⟨882899, by rfl⟩ : syracuseStep 1177199 = 1765799) B1765799
theorem B1767023 : Blo 1176405 1767023 := bstep (se 1 (by rfl) ⟨1325267, by rfl⟩ : syracuseStep 1767023 = 2650535) B2650535
theorem B14317195 : Blo 1176405 14317195 := bstep (se 1 (by rfl) ⟨10737896, by rfl⟩ : syracuseStep 14317195 = 21475793) B21475793
theorem B1177255 : Blo 1176405 1177255 := bstep (se 1 (by rfl) ⟨882941, by rfl⟩ : syracuseStep 1177255 = 1765883) B1765883
theorem B1767095 : Blo 1176405 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B16103123 : Blo 1176405 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B1677019 : Blo 1176405 1677019 := bstep (se 1 (by rfl) ⟨1257764, by rfl⟩ : syracuseStep 1677019 = 2515529) B2515529
theorem B1767131 : Blo 1176405 1767131 := bstep (se 1 (by rfl) ⟨1325348, by rfl⟩ : syracuseStep 1767131 = 2650697) B2650697
theorem B16971515 : Blo 1176405 16971515 := bstep (se 1 (by rfl) ⟨12728636, by rfl⟩ : syracuseStep 16971515 = 25457273) B25457273
theorem B1177339 : Blo 1176405 1177339 := bstep (se 1 (by rfl) ⟨883004, by rfl⟩ : syracuseStep 1177339 = 1766009) B1766009
theorem B1324795 : Blo 1176405 1324795 := bstep (se 1 (by rfl) ⟨993596, by rfl⟩ : syracuseStep 1324795 = 1987193) B1987193
theorem B1988347 : Blo 1176405 1988347 := bstep (se 1 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 1988347 = 2982521) B2982521
theorem B2012959 : Blo 1176405 2012959 := bstep (se 1 (by rfl) ⟨1509719, by rfl⟩ : syracuseStep 2012959 = 3019439) B3019439
theorem B1177375 : Blo 1176405 1177375 := bstep (se 1 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 1177375 = 1766063) B1766063
theorem B1324831 : Blo 1176405 1324831 := bstep (se 1 (by rfl) ⟨993623, by rfl⟩ : syracuseStep 1324831 = 1987247) B1987247
theorem B1177407 : Blo 1176405 1177407 := bstep (se 1 (by rfl) ⟨883055, by rfl⟩ : syracuseStep 1177407 = 1766111) B1766111
theorem B1767305 : Blo 1176405 1767305 := bstep (se 2 (by rfl) ⟨662739, by rfl⟩ : syracuseStep 1767305 = 1325479) B1325479
theorem B1988489 : Blo 1176405 1988489 := bstep (se 2 (by rfl) ⟨745683, by rfl⟩ : syracuseStep 1988489 = 1491367) B1491367
theorem B1677287 : Blo 1176405 1677287 := bstep (se 1 (by rfl) ⟨1257965, by rfl⟩ : syracuseStep 1677287 = 2515931) B2515931
theorem B1177583 : Blo 1176405 1177583 := bstep (se 1 (by rfl) ⟨883187, by rfl⟩ : syracuseStep 1177583 = 1766375) B1766375
theorem B1767407 : Blo 1176405 1767407 := bstep (se 1 (by rfl) ⟨1325555, by rfl⟩ : syracuseStep 1767407 = 2651111) B2651111
theorem B1177755 : Blo 1176405 1177755 := bstep (se 1 (by rfl) ⟨883316, by rfl⟩ : syracuseStep 1177755 = 1766633) B1766633
theorem B1177791 : Blo 1176405 1177791 := bstep (se 1 (by rfl) ⟨883343, by rfl⟩ : syracuseStep 1177791 = 1766687) B1766687
theorem B4241641 : Blo 1176405 4241641 := bstep (se 2 (by rfl) ⟨1590615, by rfl⟩ : syracuseStep 4241641 = 3181231) B3181231
theorem B1177903 : Blo 1176405 1177903 := bstep (se 1 (by rfl) ⟨883427, by rfl⟩ : syracuseStep 1177903 = 1766855) B1766855
theorem B3824047 : Blo 1176405 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B1178139 : Blo 1176405 1178139 := bstep (se 1 (by rfl) ⟨883604, by rfl⟩ : syracuseStep 1178139 = 1767209) B1767209
theorem B1178143 : Blo 1176405 1178143 := bstep (se 1 (by rfl) ⟨883607, by rfl⟩ : syracuseStep 1178143 = 1767215) B1767215
theorem B4029065 : Blo 1176405 4029065 := bstep (se 2 (by rfl) ⟨1510899, by rfl⟩ : syracuseStep 4029065 = 3021799) B3021799
theorem B3971807 : Blo 1176405 3971807 := bstep (se 1 (by rfl) ⟨2978855, by rfl⟩ : syracuseStep 3971807 = 5957711) B5957711
theorem B9681731 : Blo 1176405 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B13409225 : Blo 1176405 13409225 := bstep (se 2 (by rfl) ⟨5028459, by rfl⟩ : syracuseStep 13409225 = 10056919) B10056919
theorem B5028905 : Blo 1176405 5028905 := bstep (se 2 (by rfl) ⟨1885839, by rfl⟩ : syracuseStep 5028905 = 3771679) B3771679
theorem B2235433 : Blo 1176405 2235433 := bstep (se 2 (by rfl) ⟨838287, by rfl⟩ : syracuseStep 2235433 = 1676575) B1676575
theorem B6700103 : Blo 1176405 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B5372999 : Blo 1176405 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B4357373 : Blo 1176405 4357373 := bstep (se 3 (by rfl) ⟨817007, by rfl⟩ : syracuseStep 4357373 = 1634015) B1634015
theorem B3972563 : Blo 1176405 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B5963219 : Blo 1176405 5963219 := bstep (se 1 (by rfl) ⟨4472414, by rfl⟩ : syracuseStep 5963219 = 8944829) B8944829
theorem B1433063 : Blo 1176405 1433063 := bstep (se 1 (by rfl) ⟨1074797, by rfl⟩ : syracuseStep 1433063 = 2149595) B2149595
theorem B2235995 : Blo 1176405 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B2981519 : Blo 1176405 2981519 := bstep (se 1 (by rfl) ⟨2236139, by rfl⟩ : syracuseStep 2981519 = 4472279) B4472279
theorem B3972833 : Blo 1176405 3972833 := bstep (se 2 (by rfl) ⟨1489812, by rfl⟩ : syracuseStep 3972833 = 2979625) B2979625
theorem B4472567 : Blo 1176405 4472567 := bstep (se 1 (by rfl) ⟨3354425, by rfl⟩ : syracuseStep 4472567 = 6708851) B6708851
theorem B8052709 : Blo 1176405 8052709 := bstep (se 4 (by rfl) ⟨754941, by rfl⟩ : syracuseStep 8052709 = 1509883) B1509883
theorem B8937539 : Blo 1176405 8937539 := bstep (se 1 (by rfl) ⟨6703154, by rfl⟩ : syracuseStep 8937539 = 13406309) B13406309
theorem B18120935 : Blo 1176405 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B2982359 : Blo 1176405 2982359 := bstep (se 1 (by rfl) ⟨2236769, by rfl⟩ : syracuseStep 2982359 = 4473539) B4473539
theorem B5956091 : Blo 1176405 5956091 := bstep (se 1 (by rfl) ⟨4467068, by rfl⟩ : syracuseStep 5956091 = 8934137) B8934137
theorem B81510947 : Blo 1176405 81510947 := bstep (se 1 (by rfl) ⟨61133210, by rfl⟩ : syracuseStep 81510947 = 122266421) B122266421
theorem B8946287 : Blo 1176405 8946287 := bstep (se 1 (by rfl) ⟨6709715, by rfl⟩ : syracuseStep 8946287 = 13419431) B13419431
theorem B11322031 : Blo 1176405 11322031 := bstep (se 1 (by rfl) ⟨8491523, by rfl⟩ : syracuseStep 11322031 = 16983047) B16983047
theorem B11314343 : Blo 1176405 11314343 := bstep (se 1 (by rfl) ⟨8485757, by rfl⟩ : syracuseStep 11314343 = 16971515) B16971515
theorem B1885519 : Blo 1176405 1885519 := bstep (se 1 (by rfl) ⟨1414139, by rfl⟩ : syracuseStep 1885519 = 2828279) B2828279
theorem B114607547 : Blo 1176405 114607547 := bstep (se 1 (by rfl) ⟨85955660, by rfl⟩ : syracuseStep 114607547 = 171911321) B171911321
theorem B5367305 : Blo 1176405 5367305 := bstep (se 2 (by rfl) ⟨2012739, by rfl⟩ : syracuseStep 5367305 = 4025479) B4025479
theorem B7652927 : Blo 1176405 7652927 := bstep (se 1 (by rfl) ⟨5739695, by rfl⟩ : syracuseStep 7652927 = 11479391) B11479391
theorem B2647871 : Blo 1176405 2647871 := bstep (se 1 (by rfl) ⟨1985903, by rfl⟩ : syracuseStep 2647871 = 3971807) B3971807
theorem B8939483 : Blo 1176405 8939483 := bstep (se 1 (by rfl) ⟨6704612, by rfl⟩ : syracuseStep 8939483 = 13409225) B13409225
theorem B3352603 : Blo 1176405 3352603 := bstep (se 1 (by rfl) ⟨2514452, by rfl⟩ : syracuseStep 3352603 = 5028905) B5028905
theorem B4466735 : Blo 1176405 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B3581999 : Blo 1176405 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B19089593 : Blo 1176405 19089593 := bstep (se 2 (by rfl) ⟨7158597, by rfl⟩ : syracuseStep 19089593 = 14317195) B14317195
theorem B2648375 : Blo 1176405 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B3975479 : Blo 1176405 3975479 := bstep (se 1 (by rfl) ⟨2981609, by rfl⟩ : syracuseStep 3975479 = 5963219) B5963219
theorem B8939969 : Blo 1176405 8939969 := bstep (se 2 (by rfl) ⟨3352488, by rfl⟩ : syracuseStep 8939969 = 6704977) B6704977
theorem B2648555 : Blo 1176405 2648555 := bstep (se 1 (by rfl) ⟨1986416, by rfl⟩ : syracuseStep 2648555 = 3972833) B3972833
theorem B8948231 : Blo 1176405 8948231 := bstep (se 1 (by rfl) ⟨6711173, by rfl⟩ : syracuseStep 8948231 = 13422347) B13422347
theorem B5655521 : Blo 1176405 5655521 := bstep (se 2 (by rfl) ⟨2120820, by rfl⟩ : syracuseStep 5655521 = 4241641) B4241641
theorem B5032955 : Blo 1176405 5032955 := bstep (se 1 (by rfl) ⟨3774716, by rfl⟩ : syracuseStep 5032955 = 7549433) B7549433
theorem B11308157 : Blo 1176405 11308157 := bstep (se 3 (by rfl) ⟨2120279, by rfl⟩ : syracuseStep 11308157 = 4240559) B4240559
theorem B5033107 : Blo 1176405 5033107 := bstep (se 1 (by rfl) ⟨3774830, by rfl⟩ : syracuseStep 5033107 = 7549661) B7549661
theorem B2649257 : Blo 1176405 2649257 := bstep (se 2 (by rfl) ⟨993471, by rfl⟩ : syracuseStep 2649257 = 1986943) B1986943
theorem B5098729 : Blo 1176405 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B11619661 : Blo 1176405 11619661 := bstep (se 3 (by rfl) ⟨2178686, by rfl⟩ : syracuseStep 11619661 = 4357373) B4357373
theorem B5025179 : Blo 1176405 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B45231533 : Blo 1176405 45231533 := bstep (se 3 (by rfl) ⟨8480912, by rfl⟩ : syracuseStep 45231533 = 16961825) B16961825
theorem B6802903 : Blo 1176405 6802903 := bstep (se 1 (by rfl) ⟨5102177, by rfl⟩ : syracuseStep 6802903 = 10204355) B10204355
theorem B9547255 : Blo 1176405 9547255 := bstep (se 1 (by rfl) ⟨7160441, by rfl⟩ : syracuseStep 9547255 = 14320883) B14320883
theorem B3354119 : Blo 1176405 3354119 := bstep (se 1 (by rfl) ⟨2515589, by rfl⟩ : syracuseStep 3354119 = 5031179) B5031179
theorem B1764935 : Blo 1176405 1764935 := bstep (se 1 (by rfl) ⟨1323701, by rfl⟩ : syracuseStep 1764935 = 2647403) B2647403
theorem B2649671 : Blo 1176405 2649671 := bstep (se 1 (by rfl) ⟨1987253, by rfl⟩ : syracuseStep 2649671 = 3974507) B3974507
theorem B2649743 : Blo 1176405 2649743 := bstep (se 1 (by rfl) ⟨1987307, by rfl⟩ : syracuseStep 2649743 = 3974615) B3974615
theorem B2649833 : Blo 1176405 2649833 := bstep (se 2 (by rfl) ⟨993687, by rfl⟩ : syracuseStep 2649833 = 1987375) B1987375
theorem B3976937 : Blo 1176405 3976937 := bstep (se 2 (by rfl) ⟨1491351, by rfl⟩ : syracuseStep 3976937 = 2982703) B2982703
theorem B1765115 : Blo 1176405 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B2649851 : Blo 1176405 2649851 := bstep (se 1 (by rfl) ⟨1987388, by rfl⟩ : syracuseStep 2649851 = 3974777) B3974777
theorem B10735415 : Blo 1176405 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B38178641 : Blo 1176405 38178641 := bstep (se 2 (by rfl) ⟨14316990, by rfl⟩ : syracuseStep 38178641 = 28633981) B28633981
theorem B14708567 : Blo 1176405 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B3821501 : Blo 1176405 3821501 := bstep (se 3 (by rfl) ⟨716531, by rfl⟩ : syracuseStep 3821501 = 1433063) B1433063
theorem B1675561 : Blo 1176405 1675561 := bstep (se 2 (by rfl) ⟨628335, by rfl⟩ : syracuseStep 1675561 = 1256671) B1256671
theorem B1765787 : Blo 1176405 1765787 := bstep (se 1 (by rfl) ⟨1324340, by rfl⟩ : syracuseStep 1765787 = 2648681) B2648681
theorem B2683343 : Blo 1176405 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B4469363 : Blo 1176405 4469363 := bstep (se 1 (by rfl) ⟨3352022, by rfl⟩ : syracuseStep 4469363 = 6704045) B6704045
theorem B2650859 : Blo 1176405 2650859 := bstep (se 1 (by rfl) ⟨1988144, by rfl⟩ : syracuseStep 2650859 = 3976289) B3976289
theorem B1766207 : Blo 1176405 1766207 := bstep (se 1 (by rfl) ⟨1324655, by rfl⟩ : syracuseStep 1766207 = 2649311) B2649311
theorem B1176411 : Blo 1176405 1176411 := bstep (se 1 (by rfl) ⟨882308, by rfl⟩ : syracuseStep 1176411 = 1764617) B1764617
theorem B1176479 : Blo 1176405 1176479 := bstep (se 1 (by rfl) ⟨882359, by rfl⟩ : syracuseStep 1176479 = 1764719) B1764719
theorem B1274783 : Blo 1176405 1274783 := bstep (se 1 (by rfl) ⟨956087, by rfl⟩ : syracuseStep 1274783 = 1912175) B1912175
theorem B1766351 : Blo 1176405 1766351 := bstep (se 1 (by rfl) ⟨1324763, by rfl⟩ : syracuseStep 1766351 = 2649527) B2649527
theorem B1176559 : Blo 1176405 1176559 := bstep (se 1 (by rfl) ⟨882419, by rfl⟩ : syracuseStep 1176559 = 1764839) B1764839
theorem B1766393 : Blo 1176405 1766393 := bstep (se 2 (by rfl) ⟨662397, by rfl⟩ : syracuseStep 1766393 = 1324795) B1324795
theorem B2651129 : Blo 1176405 2651129 := bstep (se 2 (by rfl) ⟨994173, by rfl⟩ : syracuseStep 2651129 = 1988347) B1988347
theorem B7156745 : Blo 1176405 7156745 := bstep (se 2 (by rfl) ⟨2683779, by rfl⟩ : syracuseStep 7156745 = 5367559) B5367559
theorem B2683945 : Blo 1176405 2683945 := bstep (se 2 (by rfl) ⟨1006479, by rfl⟩ : syracuseStep 2683945 = 2012959) B2012959
theorem B1766441 : Blo 1176405 1766441 := bstep (se 2 (by rfl) ⟨662415, by rfl⟩ : syracuseStep 1766441 = 1324831) B1324831
theorem B1176647 : Blo 1176405 1176647 := bstep (se 1 (by rfl) ⟨882485, by rfl⟩ : syracuseStep 1176647 = 1764971) B1764971
theorem B1766471 : Blo 1176405 1766471 := bstep (se 1 (by rfl) ⟨1324853, by rfl⟩ : syracuseStep 1766471 = 2649707) B2649707
theorem B2651219 : Blo 1176405 2651219 := bstep (se 1 (by rfl) ⟨1988414, by rfl⟩ : syracuseStep 2651219 = 3976829) B3976829
theorem B1987679 : Blo 1176405 1987679 := bstep (se 1 (by rfl) ⟨1490759, by rfl⟩ : syracuseStep 1987679 = 2981519) B2981519
theorem B1176731 : Blo 1176405 1176731 := bstep (se 1 (by rfl) ⟨882548, by rfl⟩ : syracuseStep 1176731 = 1765097) B1765097
theorem B1176827 : Blo 1176405 1176827 := bstep (se 1 (by rfl) ⟨882620, by rfl⟩ : syracuseStep 1176827 = 1765241) B1765241
theorem B1766651 : Blo 1176405 1766651 := bstep (se 1 (by rfl) ⟨1324988, by rfl⟩ : syracuseStep 1766651 = 2649977) B2649977
theorem B2651399 : Blo 1176405 2651399 := bstep (se 1 (by rfl) ⟨1988549, by rfl⟩ : syracuseStep 2651399 = 3977099) B3977099
theorem B10736945 : Blo 1176405 10736945 := bstep (se 2 (by rfl) ⟨4026354, by rfl⟩ : syracuseStep 10736945 = 8052709) B8052709
theorem B1176895 : Blo 1176405 1176895 := bstep (se 1 (by rfl) ⟨882671, by rfl⟩ : syracuseStep 1176895 = 1765343) B1765343
theorem B2233831 : Blo 1176405 2233831 := bstep (se 1 (by rfl) ⟨1675373, by rfl⟩ : syracuseStep 2233831 = 3350747) B3350747
theorem B1177063 : Blo 1176405 1177063 := bstep (se 1 (by rfl) ⟨882797, by rfl⟩ : syracuseStep 1177063 = 1765595) B1765595
theorem B1177071 : Blo 1176405 1177071 := bstep (se 1 (by rfl) ⟨882803, by rfl⟩ : syracuseStep 1177071 = 1765607) B1765607
theorem B1414639 : Blo 1176405 1414639 := bstep (se 1 (by rfl) ⟨1060979, by rfl⟩ : syracuseStep 1414639 = 2121959) B2121959
theorem B1177179 : Blo 1176405 1177179 := bstep (se 1 (by rfl) ⟨882884, by rfl⟩ : syracuseStep 1177179 = 1765769) B1765769
theorem B19347083 : Blo 1176405 19347083 := bstep (se 1 (by rfl) ⟨14510312, by rfl⟩ : syracuseStep 19347083 = 29020625) B29020625
theorem B1177243 : Blo 1176405 1177243 := bstep (se 1 (by rfl) ⟨882932, by rfl⟩ : syracuseStep 1177243 = 1765865) B1765865
theorem B1177327 : Blo 1176405 1177327 := bstep (se 1 (by rfl) ⟨882995, by rfl⟩ : syracuseStep 1177327 = 1765991) B1765991
theorem B10065667 : Blo 1176405 10065667 := bstep (se 1 (by rfl) ⟨7549250, by rfl⟩ : syracuseStep 10065667 = 15098501) B15098501
theorem B1177415 : Blo 1176405 1177415 := bstep (se 1 (by rfl) ⟨883061, by rfl⟩ : syracuseStep 1177415 = 1766123) B1766123
theorem B1177435 : Blo 1176405 1177435 := bstep (se 1 (by rfl) ⟨883076, by rfl⟩ : syracuseStep 1177435 = 1766153) B1766153
theorem B4470653 : Blo 1176405 4470653 := bstep (se 3 (by rfl) ⟨838247, by rfl⟩ : syracuseStep 4470653 = 1676495) B1676495
theorem B1177503 : Blo 1176405 1177503 := bstep (se 1 (by rfl) ⟨883127, by rfl⟩ : syracuseStep 1177503 = 1766255) B1766255
theorem B4659191 : Blo 1176405 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B1177671 : Blo 1176405 1177671 := bstep (se 1 (by rfl) ⟨883253, by rfl⟩ : syracuseStep 1177671 = 1766507) B1766507
theorem B8935595 : Blo 1176405 8935595 := bstep (se 1 (by rfl) ⟨6701696, by rfl⟩ : syracuseStep 8935595 = 13403393) B13403393
theorem B1177831 : Blo 1176405 1177831 := bstep (se 1 (by rfl) ⟨883373, by rfl⟩ : syracuseStep 1177831 = 1766747) B1766747
theorem B1178015 : Blo 1176405 1178015 := bstep (se 1 (by rfl) ⟨883511, by rfl⟩ : syracuseStep 1178015 = 1767023) B1767023
theorem B7543205 : Blo 1176405 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B1178063 : Blo 1176405 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B1178087 : Blo 1176405 1178087 := bstep (se 1 (by rfl) ⟨883565, by rfl⟩ : syracuseStep 1178087 = 1767131) B1767131
theorem B1178203 : Blo 1176405 1178203 := bstep (se 1 (by rfl) ⟨883652, by rfl⟩ : syracuseStep 1178203 = 1767305) B1767305
theorem B1325659 : Blo 1176405 1325659 := bstep (se 1 (by rfl) ⟨994244, by rfl⟩ : syracuseStep 1325659 = 1988489) B1988489
theorem B1178271 : Blo 1176405 1178271 := bstep (se 1 (by rfl) ⟨883703, by rfl⟩ : syracuseStep 1178271 = 1767407) B1767407
theorem B2980577 : Blo 1176405 2980577 := bstep (se 2 (by rfl) ⟨1117716, by rfl⟩ : syracuseStep 2980577 = 2235433) B2235433
theorem B11311883 : Blo 1176405 11311883 := bstep (se 1 (by rfl) ⟨8483912, by rfl⟩ : syracuseStep 11311883 = 16967825) B16967825
theorem B2686043 : Blo 1176405 2686043 := bstep (se 1 (by rfl) ⟨2014532, by rfl⟩ : syracuseStep 2686043 = 4029065) B4029065
theorem B14326919 : Blo 1176405 14326919 := bstep (se 1 (by rfl) ⟨10745189, by rfl⟩ : syracuseStep 14326919 = 21490379) B21490379
theorem B6454487 : Blo 1176405 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B12737807 : Blo 1176405 12737807 := bstep (se 1 (by rfl) ⟨9553355, by rfl⟩ : syracuseStep 12737807 = 19106711) B19106711
theorem B39239153 : Blo 1176405 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B13417973 : Blo 1176405 13417973 := bstep (se 5 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 13417973 = 1257935) B1257935
theorem B2236025 : Blo 1176405 2236025 := bstep (se 2 (by rfl) ⟨838509, by rfl⟩ : syracuseStep 2236025 = 1677019) B1677019
theorem B1490663 : Blo 1176405 1490663 := bstep (se 1 (by rfl) ⟨1117997, by rfl⟩ : syracuseStep 1490663 = 2235995) B2235995
theorem B2981711 : Blo 1176405 2981711 := bstep (se 1 (by rfl) ⟨2236283, by rfl⟩ : syracuseStep 2981711 = 4472567) B4472567
theorem B11476829 : Blo 1176405 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B4472765 : Blo 1176405 4472765 := bstep (se 3 (by rfl) ⟨838643, by rfl⟩ : syracuseStep 4472765 = 1677287) B1677287
theorem B5964191 : Blo 1176405 5964191 := bstep (se 1 (by rfl) ⟨4473143, by rfl⟩ : syracuseStep 5964191 = 8946287) B8946287
theorem B3106127 : Blo 1176405 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B5957063 : Blo 1176405 5957063 := bstep (se 1 (by rfl) ⟨4467797, by rfl⟩ : syracuseStep 5957063 = 8935595) B8935595
theorem B6710809 : Blo 1176405 6710809 := bstep (se 2 (by rfl) ⟨2516553, by rfl⟩ : syracuseStep 6710809 = 5033107) B5033107
theorem B5965487 : Blo 1176405 5965487 := bstep (se 1 (by rfl) ⟨4474115, by rfl⟩ : syracuseStep 5965487 = 8948231) B8948231
theorem B15492881 : Blo 1176405 15492881 := bstep (se 2 (by rfl) ⟨5809830, by rfl⟩ : syracuseStep 15492881 = 11619661) B11619661
theorem B3975101 : Blo 1176405 3975101 := bstep (se 3 (by rfl) ⟨745331, by rfl⟩ : syracuseStep 3975101 = 1490663) B1490663
theorem B9070537 : Blo 1176405 9070537 := bstep (se 2 (by rfl) ⟨3401451, by rfl⟩ : syracuseStep 9070537 = 6802903) B6802903
theorem B1886185 : Blo 1176405 1886185 := bstep (se 2 (by rfl) ⟨707319, by rfl⟩ : syracuseStep 1886185 = 1414639) B1414639
theorem B3770347 : Blo 1176405 3770347 := bstep (se 1 (by rfl) ⟨2827760, by rfl⟩ : syracuseStep 3770347 = 5655521) B5655521
theorem B7538771 : Blo 1176405 7538771 := bstep (se 1 (by rfl) ⟨5654078, by rfl⟩ : syracuseStep 7538771 = 11308157) B11308157
theorem B4302991 : Blo 1176405 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B26159435 : Blo 1176405 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B13420889 : Blo 1176405 13420889 := bstep (se 2 (by rfl) ⟨5032833, by rfl⟩ : syracuseStep 13420889 = 10065667) B10065667
theorem B5958359 : Blo 1176405 5958359 := bstep (se 1 (by rfl) ⟨4468769, by rfl⟩ : syracuseStep 5958359 = 8937539) B8937539
theorem B1788895 : Blo 1176405 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B54340631 : Blo 1176405 54340631 := bstep (se 1 (by rfl) ⟨40755473, by rfl⟩ : syracuseStep 54340631 = 81510947) B81510947
theorem B4771163 : Blo 1176405 4771163 := bstep (se 1 (by rfl) ⟨3578372, by rfl⟩ : syracuseStep 4771163 = 7156745) B7156745
theorem B12898055 : Blo 1176405 12898055 := bstep (se 1 (by rfl) ⟨9673541, by rfl⟩ : syracuseStep 12898055 = 19347083) B19347083
theorem B1765247 : Blo 1176405 1765247 := bstep (se 1 (by rfl) ⟨1323935, by rfl⟩ : syracuseStep 1765247 = 2647871) B2647871
theorem B5959655 : Blo 1176405 5959655 := bstep (se 1 (by rfl) ⟨4469741, by rfl⟩ : syracuseStep 5959655 = 8939483) B8939483
theorem B2977823 : Blo 1176405 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B2387999 : Blo 1176405 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B12726395 : Blo 1176405 12726395 := bstep (se 1 (by rfl) ⟨9544796, by rfl⟩ : syracuseStep 12726395 = 19089593) B19089593
theorem B1765583 : Blo 1176405 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B2650319 : Blo 1176405 2650319 := bstep (se 1 (by rfl) ⟨1987739, by rfl⟩ : syracuseStep 2650319 = 3975479) B3975479
theorem B5959979 : Blo 1176405 5959979 := bstep (se 1 (by rfl) ⟨4469984, by rfl⟩ : syracuseStep 5959979 = 8939969) B8939969
theorem B1765703 : Blo 1176405 1765703 := bstep (se 1 (by rfl) ⟨1324277, by rfl⟩ : syracuseStep 1765703 = 2648555) B2648555
theorem B1987051 : Blo 1176405 1987051 := bstep (se 1 (by rfl) ⟨1490288, by rfl⟩ : syracuseStep 1987051 = 2980577) B2980577
theorem B7541255 : Blo 1176405 7541255 := bstep (se 1 (by rfl) ⟨5655941, by rfl⟩ : syracuseStep 7541255 = 11311883) B11311883
theorem B2978441 : Blo 1176405 2978441 := bstep (se 2 (by rfl) ⟨1116915, by rfl⟩ : syracuseStep 2978441 = 2233831) B2233831
theorem B3355303 : Blo 1176405 3355303 := bstep (se 1 (by rfl) ⟨2516477, by rfl⟩ : syracuseStep 3355303 = 5032955) B5032955
theorem B1790695 : Blo 1176405 1790695 := bstep (se 1 (by rfl) ⟨1343021, by rfl⟩ : syracuseStep 1790695 = 2686043) B2686043
theorem B1766171 : Blo 1176405 1766171 := bstep (se 1 (by rfl) ⟨1324628, by rfl⟩ : syracuseStep 1766171 = 2649257) B2649257
theorem B8491871 : Blo 1176405 8491871 := bstep (se 1 (by rfl) ⟨6368903, by rfl⟩ : syracuseStep 8491871 = 12737807) B12737807
theorem B1176623 : Blo 1176405 1176623 := bstep (se 1 (by rfl) ⟨882467, by rfl⟩ : syracuseStep 1176623 = 1764935) B1764935
theorem B1766447 : Blo 1176405 1766447 := bstep (se 1 (by rfl) ⟨1324835, by rfl⟩ : syracuseStep 1766447 = 2649671) B2649671
theorem B1766495 : Blo 1176405 1766495 := bstep (se 1 (by rfl) ⟨1324871, by rfl⟩ : syracuseStep 1766495 = 2649743) B2649743
theorem B1766555 : Blo 1176405 1766555 := bstep (se 1 (by rfl) ⟨1324916, by rfl⟩ : syracuseStep 1766555 = 2649833) B2649833
theorem B2651291 : Blo 1176405 2651291 := bstep (se 1 (by rfl) ⟨1988468, by rfl⟩ : syracuseStep 2651291 = 3976937) B3976937
theorem B1176743 : Blo 1176405 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B1766567 : Blo 1176405 1766567 := bstep (se 1 (by rfl) ⟨1324925, by rfl⟩ : syracuseStep 1766567 = 2649851) B2649851
theorem B7156943 : Blo 1176405 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B1987807 : Blo 1176405 1987807 := bstep (se 1 (by rfl) ⟨1490855, by rfl⟩ : syracuseStep 1987807 = 2981711) B2981711
theorem B4470137 : Blo 1176405 4470137 := bstep (se 2 (by rfl) ⟨1676301, by rfl⟩ : syracuseStep 4470137 = 3352603) B3352603
theorem B12080623 : Blo 1176405 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B1177191 : Blo 1176405 1177191 := bstep (se 1 (by rfl) ⟨882893, by rfl⟩ : syracuseStep 1177191 = 1765787) B1765787
theorem B1988239 : Blo 1176405 1988239 := bstep (se 1 (by rfl) ⟨1491179, by rfl⟩ : syracuseStep 1988239 = 2982359) B2982359
theorem B3970727 : Blo 1176405 3970727 := bstep (se 1 (by rfl) ⟨2978045, by rfl⟩ : syracuseStep 3970727 = 5956091) B5956091
theorem B2234081 : Blo 1176405 2234081 := bstep (se 2 (by rfl) ⟨837780, by rfl⟩ : syracuseStep 2234081 = 1675561) B1675561
theorem B2979575 : Blo 1176405 2979575 := bstep (se 1 (by rfl) ⟨2234681, by rfl⟩ : syracuseStep 2979575 = 4469363) B4469363
theorem B1767239 : Blo 1176405 1767239 := bstep (se 1 (by rfl) ⟨1325429, by rfl⟩ : syracuseStep 1767239 = 2650859) B2650859
theorem B1177471 : Blo 1176405 1177471 := bstep (se 1 (by rfl) ⟨883103, by rfl⟩ : syracuseStep 1177471 = 1766207) B1766207
theorem B1177567 : Blo 1176405 1177567 := bstep (se 1 (by rfl) ⟨883175, by rfl⟩ : syracuseStep 1177567 = 1766351) B1766351
theorem B1177595 : Blo 1176405 1177595 := bstep (se 1 (by rfl) ⟨883196, by rfl⟩ : syracuseStep 1177595 = 1766393) B1766393
theorem B1767419 : Blo 1176405 1767419 := bstep (se 1 (by rfl) ⟨1325564, by rfl⟩ : syracuseStep 1767419 = 2651129) B2651129
theorem B1177627 : Blo 1176405 1177627 := bstep (se 1 (by rfl) ⟨883220, by rfl⟩ : syracuseStep 1177627 = 1766441) B1766441
theorem B1177647 : Blo 1176405 1177647 := bstep (se 1 (by rfl) ⟨883235, by rfl⟩ : syracuseStep 1177647 = 1766471) B1766471
theorem B1767479 : Blo 1176405 1767479 := bstep (se 1 (by rfl) ⟨1325609, by rfl⟩ : syracuseStep 1767479 = 2651219) B2651219
theorem B1325119 : Blo 1176405 1325119 := bstep (se 1 (by rfl) ⟨993839, by rfl⟩ : syracuseStep 1325119 = 1987679) B1987679
theorem B7542895 : Blo 1176405 7542895 := bstep (se 1 (by rfl) ⟨5657171, by rfl⟩ : syracuseStep 7542895 = 11314343) B11314343
theorem B1767545 : Blo 1176405 1767545 := bstep (se 2 (by rfl) ⟨662829, by rfl⟩ : syracuseStep 1767545 = 1325659) B1325659
theorem B1177767 : Blo 1176405 1177767 := bstep (se 1 (by rfl) ⟨883325, by rfl⟩ : syracuseStep 1177767 = 1766651) B1766651
theorem B1767599 : Blo 1176405 1767599 := bstep (se 1 (by rfl) ⟨1325699, by rfl⟩ : syracuseStep 1767599 = 2651399) B2651399
theorem B7157963 : Blo 1176405 7157963 := bstep (se 1 (by rfl) ⟨5368472, by rfl⟩ : syracuseStep 7157963 = 10736945) B10736945
theorem B15096041 : Blo 1176405 15096041 := bstep (se 2 (by rfl) ⟨5661015, by rfl⟩ : syracuseStep 15096041 = 11322031) B11322031
theorem B76405031 : Blo 1176405 76405031 := bstep (se 1 (by rfl) ⟨57303773, by rfl⟩ : syracuseStep 76405031 = 114607547) B114607547
theorem B3578203 : Blo 1176405 3578203 := bstep (se 1 (by rfl) ⟨2683652, by rfl⟩ : syracuseStep 3578203 = 5367305) B5367305
theorem B5101951 : Blo 1176405 5101951 := bstep (se 1 (by rfl) ⟨3826463, by rfl⟩ : syracuseStep 5101951 = 7652927) B7652927
theorem B13400477 : Blo 1176405 13400477 := bstep (se 3 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 13400477 = 5025179) B5025179
theorem B2980435 : Blo 1176405 2980435 := bstep (se 1 (by rfl) ⟨2235326, by rfl⟩ : syracuseStep 2980435 = 4470653) B4470653
theorem B3578593 : Blo 1176405 3578593 := bstep (se 2 (by rfl) ⟨1341972, by rfl⟩ : syracuseStep 3578593 = 2683945) B2683945
theorem B5028803 : Blo 1176405 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B6798305 : Blo 1176405 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B5962733 : Blo 1176405 5962733 := bstep (se 3 (by rfl) ⟨1118012, by rfl⟩ : syracuseStep 5962733 = 2236025) B2236025
theorem B2514025 : Blo 1176405 2514025 := bstep (se 2 (by rfl) ⟨942759, by rfl⟩ : syracuseStep 2514025 = 1885519) B1885519
theorem B12729673 : Blo 1176405 12729673 := bstep (se 2 (by rfl) ⟨4773627, by rfl⟩ : syracuseStep 12729673 = 9547255) B9547255
theorem B9551279 : Blo 1176405 9551279 := bstep (se 1 (by rfl) ⟨7163459, by rfl⟩ : syracuseStep 9551279 = 14326919) B14326919
theorem B30154355 : Blo 1176405 30154355 := bstep (se 1 (by rfl) ⟨22615766, by rfl⟩ : syracuseStep 30154355 = 45231533) B45231533
theorem B8945315 : Blo 1176405 8945315 := bstep (se 1 (by rfl) ⟨6708986, by rfl⟩ : syracuseStep 8945315 = 13417973) B13417973
theorem B2236079 : Blo 1176405 2236079 := bstep (se 1 (by rfl) ⟨1677059, by rfl⟩ : syracuseStep 2236079 = 3354119) B3354119
theorem B3399421 : Blo 1176405 3399421 := bstep (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) B1274783
theorem B25452427 : Blo 1176405 25452427 := bstep (se 1 (by rfl) ⟨19089320, by rfl⟩ : syracuseStep 25452427 = 38178641) B38178641
theorem B9805711 : Blo 1176405 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B7651219 : Blo 1176405 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B2547667 : Blo 1176405 2547667 := bstep (se 1 (by rfl) ⟨1910750, by rfl⟩ : syracuseStep 2547667 = 3821501) B3821501
theorem B2981843 : Blo 1176405 2981843 := bstep (se 1 (by rfl) ⟨2236382, by rfl⟩ : syracuseStep 2981843 = 4472765) B4472765
theorem B3973319 : Blo 1176405 3973319 := bstep (se 1 (by rfl) ⟨2979989, by rfl⟩ : syracuseStep 3973319 = 5959979) B5959979
theorem B5661247 : Blo 1176405 5661247 := bstep (se 1 (by rfl) ⟨4245935, by rfl⟩ : syracuseStep 5661247 = 8491871) B8491871
theorem B3973913 : Blo 1176405 3973913 := bstep (se 2 (by rfl) ⟨1490217, by rfl⟩ : syracuseStep 3973913 = 2980435) B2980435
theorem B8283005 : Blo 1176405 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B4473737 : Blo 1176405 4473737 := bstep (se 2 (by rfl) ⟨1677651, by rfl⟩ : syracuseStep 4473737 = 3355303) B3355303
theorem B12723101 : Blo 1176405 12723101 := bstep (se 3 (by rfl) ⟨2385581, by rfl⟩ : syracuseStep 12723101 = 4771163) B4771163
theorem B2647151 : Blo 1176405 2647151 := bstep (se 1 (by rfl) ⟨1985363, by rfl⟩ : syracuseStep 2647151 = 3970727) B3970727
theorem B3352033 : Blo 1176405 3352033 := bstep (se 2 (by rfl) ⟨1257012, by rfl⟩ : syracuseStep 3352033 = 2514025) B2514025
theorem B8947259 : Blo 1176405 8947259 := bstep (se 1 (by rfl) ⟨6710444, by rfl⟩ : syracuseStep 8947259 = 13420889) B13420889
theorem B5957549 : Blo 1176405 5957549 := bstep (se 3 (by rfl) ⟨1117040, by rfl⟩ : syracuseStep 5957549 = 2234081) B2234081
theorem B3352535 : Blo 1176405 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B16107497 : Blo 1176405 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B4532203 : Blo 1176405 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B3975155 : Blo 1176405 3975155 := bstep (se 1 (by rfl) ⟨2981366, by rfl⟩ : syracuseStep 3975155 = 5962733) B5962733
theorem B36227087 : Blo 1176405 36227087 := bstep (se 1 (by rfl) ⟨27170315, by rfl⟩ : syracuseStep 36227087 = 54340631) B54340631
theorem B8947745 : Blo 1176405 8947745 := bstep (se 2 (by rfl) ⟨3355404, by rfl⟩ : syracuseStep 8947745 = 6710809) B6710809
theorem B41314349 : Blo 1176405 41314349 := bstep (se 3 (by rfl) ⟨7746440, by rfl⟩ : syracuseStep 41314349 = 15492881) B15492881
theorem B6367519 : Blo 1176405 6367519 := bstep (se 1 (by rfl) ⟨4775639, by rfl⟩ : syracuseStep 6367519 = 9551279) B9551279
theorem B4532561 : Blo 1176405 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B10201625 : Blo 1176405 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B12094049 : Blo 1176405 12094049 := bstep (se 2 (by rfl) ⟨4535268, by rfl⟩ : syracuseStep 12094049 = 9070537) B9070537
theorem B1985215 : Blo 1176405 1985215 := bstep (se 1 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 1985215 = 2977823) B2977823
theorem B6367997 : Blo 1176405 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B5737321 : Blo 1176405 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B3976127 : Blo 1176405 3976127 := bstep (se 1 (by rfl) ⟨2982095, by rfl⟩ : syracuseStep 3976127 = 5964191) B5964191
theorem B1985627 : Blo 1176405 1985627 := bstep (se 1 (by rfl) ⟨1489220, by rfl⟩ : syracuseStep 1985627 = 2978441) B2978441
theorem B4770937 : Blo 1176405 4770937 := bstep (se 2 (by rfl) ⟨1789101, by rfl⟩ : syracuseStep 4770937 = 3578203) B3578203
theorem B6802601 : Blo 1176405 6802601 := bstep (se 2 (by rfl) ⟨2550975, by rfl⟩ : syracuseStep 6802601 = 5101951) B5101951
theorem B2649401 : Blo 1176405 2649401 := bstep (se 2 (by rfl) ⟨993525, by rfl⟩ : syracuseStep 2649401 = 1987051) B1987051
theorem B4771295 : Blo 1176405 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B4771457 : Blo 1176405 4771457 := bstep (se 2 (by rfl) ⟨1789296, by rfl⟩ : syracuseStep 4771457 = 3578593) B3578593
theorem B2387593 : Blo 1176405 2387593 := bstep (se 2 (by rfl) ⟨895347, by rfl⟩ : syracuseStep 2387593 = 1790695) B1790695
theorem B3976991 : Blo 1176405 3976991 := bstep (se 1 (by rfl) ⟨2982743, by rfl⟩ : syracuseStep 3976991 = 5965487) B5965487
theorem B1986383 : Blo 1176405 1986383 := bstep (se 1 (by rfl) ⟨1489787, by rfl⟩ : syracuseStep 1986383 = 2979575) B2979575
theorem B2650067 : Blo 1176405 2650067 := bstep (se 1 (by rfl) ⟨1987550, by rfl⟩ : syracuseStep 2650067 = 3975101) B3975101
theorem B5025847 : Blo 1176405 5025847 := bstep (se 1 (by rfl) ⟨3769385, by rfl⟩ : syracuseStep 5025847 = 7538771) B7538771
theorem B4771975 : Blo 1176405 4771975 := bstep (se 1 (by rfl) ⟨3578981, by rfl⟩ : syracuseStep 4771975 = 7157963) B7157963
theorem B10064027 : Blo 1176405 10064027 := bstep (se 1 (by rfl) ⟨7548020, by rfl⟩ : syracuseStep 10064027 = 15096041) B15096041
theorem B8933651 : Blo 1176405 8933651 := bstep (se 1 (by rfl) ⟨6700238, by rfl⟩ : syracuseStep 8933651 = 13400477) B13400477
theorem B2650409 : Blo 1176405 2650409 := bstep (se 2 (by rfl) ⟨993903, by rfl⟩ : syracuseStep 2650409 = 1987807) B1987807
theorem B34394813 : Blo 1176405 34394813 := bstep (se 3 (by rfl) ⟨6449027, by rfl⟩ : syracuseStep 34394813 = 12898055) B12898055
theorem B2650985 : Blo 1176405 2650985 := bstep (se 2 (by rfl) ⟨994119, by rfl⟩ : syracuseStep 2650985 = 1988239) B1988239
theorem B9540773 : Blo 1176405 9540773 := bstep (se 4 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 9540773 = 1788895) B1788895
theorem B33936569 : Blo 1176405 33936569 := bstep (se 2 (by rfl) ⟨12726213, by rfl⟩ : syracuseStep 33936569 = 25452427) B25452427
theorem B1176831 : Blo 1176405 1176831 := bstep (se 1 (by rfl) ⟨882623, by rfl⟩ : syracuseStep 1176831 = 1765247) B1765247
theorem B3396889 : Blo 1176405 3396889 := bstep (se 2 (by rfl) ⟨1273833, by rfl⟩ : syracuseStep 3396889 = 2547667) B2547667
theorem B5027129 : Blo 1176405 5027129 := bstep (se 2 (by rfl) ⟨1885173, by rfl⟩ : syracuseStep 5027129 = 3770347) B3770347
theorem B1987895 : Blo 1176405 1987895 := bstep (se 1 (by rfl) ⟨1490921, by rfl⟩ : syracuseStep 1987895 = 2981843) B2981843
theorem B8484263 : Blo 1176405 8484263 := bstep (se 1 (by rfl) ⟨6363197, by rfl⟩ : syracuseStep 8484263 = 12726395) B12726395
theorem B1766825 : Blo 1176405 1766825 := bstep (se 2 (by rfl) ⟨662559, by rfl⟩ : syracuseStep 1766825 = 1325119) B1325119
theorem B1177055 : Blo 1176405 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B1766879 : Blo 1176405 1766879 := bstep (se 1 (by rfl) ⟨1325159, by rfl⟩ : syracuseStep 1766879 = 2650319) B2650319
theorem B10057193 : Blo 1176405 10057193 := bstep (se 2 (by rfl) ⟨3771447, by rfl⟩ : syracuseStep 10057193 = 7542895) B7542895
theorem B1177135 : Blo 1176405 1177135 := bstep (se 1 (by rfl) ⟨882851, by rfl⟩ : syracuseStep 1177135 = 1765703) B1765703
theorem B5027503 : Blo 1176405 5027503 := bstep (se 1 (by rfl) ⟨3770627, by rfl⟩ : syracuseStep 5027503 = 7541255) B7541255
theorem B1177447 : Blo 1176405 1177447 := bstep (se 1 (by rfl) ⟨883085, by rfl⟩ : syracuseStep 1177447 = 1766171) B1766171
theorem B1177631 : Blo 1176405 1177631 := bstep (se 1 (by rfl) ⟨883223, by rfl⟩ : syracuseStep 1177631 = 1766447) B1766447
theorem B1177663 : Blo 1176405 1177663 := bstep (se 1 (by rfl) ⟨883247, by rfl⟩ : syracuseStep 1177663 = 1766495) B1766495
theorem B1177703 : Blo 1176405 1177703 := bstep (se 1 (by rfl) ⟨883277, by rfl⟩ : syracuseStep 1177703 = 1766555) B1766555
theorem B1767527 : Blo 1176405 1767527 := bstep (se 1 (by rfl) ⟨1325645, by rfl⟩ : syracuseStep 1767527 = 2651291) B2651291
theorem B1177711 : Blo 1176405 1177711 := bstep (se 1 (by rfl) ⟨883283, by rfl⟩ : syracuseStep 1177711 = 1766567) B1766567
theorem B2980091 : Blo 1176405 2980091 := bstep (se 1 (by rfl) ⟨2235068, by rfl⟩ : syracuseStep 2980091 = 4470137) B4470137
theorem B3971375 : Blo 1176405 3971375 := bstep (se 1 (by rfl) ⟨2978531, by rfl⟩ : syracuseStep 3971375 = 5957063) B5957063
theorem B1178159 : Blo 1176405 1178159 := bstep (se 1 (by rfl) ⟨883619, by rfl⟩ : syracuseStep 1178159 = 1767239) B1767239
theorem B1178279 : Blo 1176405 1178279 := bstep (se 1 (by rfl) ⟨883709, by rfl⟩ : syracuseStep 1178279 = 1767419) B1767419
theorem B1178319 : Blo 1176405 1178319 := bstep (se 1 (by rfl) ⟨883739, by rfl⟩ : syracuseStep 1178319 = 1767479) B1767479
theorem B1178363 : Blo 1176405 1178363 := bstep (se 1 (by rfl) ⟨883772, by rfl⟩ : syracuseStep 1178363 = 1767545) B1767545
theorem B1178399 : Blo 1176405 1178399 := bstep (se 1 (by rfl) ⟨883799, by rfl⟩ : syracuseStep 1178399 = 1767599) B1767599
theorem B50936687 : Blo 1176405 50936687 := bstep (se 1 (by rfl) ⟨38202515, by rfl⟩ : syracuseStep 50936687 = 76405031) B76405031
theorem B17439623 : Blo 1176405 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B16972897 : Blo 1176405 16972897 := bstep (se 2 (by rfl) ⟨6364836, by rfl⟩ : syracuseStep 16972897 = 12729673) B12729673
theorem B3972239 : Blo 1176405 3972239 := bstep (se 1 (by rfl) ⟨2979179, by rfl⟩ : syracuseStep 3972239 = 5958359) B5958359
theorem B20102903 : Blo 1176405 20102903 := bstep (se 1 (by rfl) ⟨15077177, by rfl⟩ : syracuseStep 20102903 = 30154355) B30154355
theorem B5963543 : Blo 1176405 5963543 := bstep (se 1 (by rfl) ⟨4472657, by rfl⟩ : syracuseStep 5963543 = 8945315) B8945315
theorem B1490719 : Blo 1176405 1490719 := bstep (se 1 (by rfl) ⟨1118039, by rfl⟩ : syracuseStep 1490719 = 2236079) B2236079
theorem B13074281 : Blo 1176405 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B10059653 : Blo 1176405 10059653 := bstep (se 4 (by rfl) ⟨943092, by rfl⟩ : syracuseStep 10059653 = 1886185) B1886185
theorem B3973103 : Blo 1176405 3973103 := bstep (se 1 (by rfl) ⟨2979827, by rfl⟩ : syracuseStep 3973103 = 5959655) B5959655
theorem B6701129 : Blo 1176405 6701129 := bstep (se 2 (by rfl) ⟨2512923, by rfl⟩ : syracuseStep 6701129 = 5025847) B5025847
theorem B6709351 : Blo 1176405 6709351 := bstep (se 1 (by rfl) ⟨5032013, by rfl⟩ : syracuseStep 6709351 = 10064027) B10064027
theorem B5955767 : Blo 1176405 5955767 := bstep (se 1 (by rfl) ⟨4466825, by rfl⟩ : syracuseStep 5955767 = 8933651) B8933651
theorem B22929875 : Blo 1176405 22929875 := bstep (se 1 (by rfl) ⟨17197406, by rfl⟩ : syracuseStep 22929875 = 34394813) B34394813
theorem B5522003 : Blo 1176405 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B2982491 : Blo 1176405 2982491 := bstep (se 1 (by rfl) ⟨2236868, by rfl⟩ : syracuseStep 2982491 = 4473737) B4473737
theorem B3351419 : Blo 1176405 3351419 := bstep (se 1 (by rfl) ⟨2513564, by rfl⟩ : syracuseStep 3351419 = 5027129) B5027129
theorem B2646953 : Blo 1176405 2646953 := bstep (se 2 (by rfl) ⟨992607, by rfl⟩ : syracuseStep 2646953 = 1985215) B1985215
theorem B5964839 : Blo 1176405 5964839 := bstep (se 1 (by rfl) ⟨4473629, by rfl⟩ : syracuseStep 5964839 = 8947259) B8947259
theorem B24151391 : Blo 1176405 24151391 := bstep (se 1 (by rfl) ⟨18113543, by rfl⟩ : syracuseStep 24151391 = 36227087) B36227087
theorem B5965163 : Blo 1176405 5965163 := bstep (se 1 (by rfl) ⟨4473872, by rfl⟩ : syracuseStep 5965163 = 8947745) B8947745
theorem B27542899 : Blo 1176405 27542899 := bstep (se 1 (by rfl) ⟨20657174, by rfl⟩ : syracuseStep 27542899 = 41314349) B41314349
theorem B2647583 : Blo 1176405 2647583 := bstep (se 1 (by rfl) ⟨1985687, by rfl⟩ : syracuseStep 2647583 = 3971375) B3971375
theorem B6801083 : Blo 1176405 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B8062699 : Blo 1176405 8062699 := bstep (se 1 (by rfl) ⟨6047024, by rfl⟩ : syracuseStep 8062699 = 12094049) B12094049
theorem B33957791 : Blo 1176405 33957791 := bstep (se 1 (by rfl) ⟨25468343, by rfl⟩ : syracuseStep 33957791 = 50936687) B50936687
theorem B11626415 : Blo 1176405 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B2648159 : Blo 1176405 2648159 := bstep (se 1 (by rfl) ⟨1986119, by rfl⟩ : syracuseStep 2648159 = 3972239) B3972239
theorem B6703337 : Blo 1176405 6703337 := bstep (se 2 (by rfl) ⟨2513751, by rfl⟩ : syracuseStep 6703337 = 5027503) B5027503
theorem B3180863 : Blo 1176405 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B3180971 : Blo 1176405 3180971 := bstep (se 1 (by rfl) ⟨2385728, by rfl⟩ : syracuseStep 3180971 = 4771457) B4771457
theorem B3975695 : Blo 1176405 3975695 := bstep (se 1 (by rfl) ⟨2981771, by rfl⟩ : syracuseStep 3975695 = 5963543) B5963543
theorem B2648735 : Blo 1176405 2648735 := bstep (se 1 (by rfl) ⟨1986551, by rfl⟩ : syracuseStep 2648735 = 3973103) B3973103
theorem B2648879 : Blo 1176405 2648879 := bstep (se 1 (by rfl) ⟨1986659, by rfl⟩ : syracuseStep 2648879 = 3973319) B3973319
theorem B8490025 : Blo 1176405 8490025 := bstep (se 2 (by rfl) ⟨3183759, by rfl⟩ : syracuseStep 8490025 = 6367519) B6367519
theorem B18140269 : Blo 1176405 18140269 := bstep (se 3 (by rfl) ⟨3401300, by rfl⟩ : syracuseStep 18140269 = 6802601) B6802601
theorem B2649275 : Blo 1176405 2649275 := bstep (se 1 (by rfl) ⟨1986956, by rfl⟩ : syracuseStep 2649275 = 3973913) B3973913
theorem B8482067 : Blo 1176405 8482067 := bstep (se 1 (by rfl) ⟨6361550, by rfl⟩ : syracuseStep 8482067 = 12723101) B12723101
theorem B1764767 : Blo 1176405 1764767 := bstep (se 1 (by rfl) ⟨1323575, by rfl⟩ : syracuseStep 1764767 = 2647151) B2647151
theorem B7548329 : Blo 1176405 7548329 := bstep (se 2 (by rfl) ⟨2830623, by rfl⟩ : syracuseStep 7548329 = 5661247) B5661247
theorem B6360515 : Blo 1176405 6360515 := bstep (se 1 (by rfl) ⟨4770386, by rfl⟩ : syracuseStep 6360515 = 9540773) B9540773
theorem B5656175 : Blo 1176405 5656175 := bstep (se 1 (by rfl) ⟨4242131, by rfl⟩ : syracuseStep 5656175 = 8484263) B8484263
theorem B6704795 : Blo 1176405 6704795 := bstep (se 1 (by rfl) ⟨5028596, by rfl⟩ : syracuseStep 6704795 = 10057193) B10057193
theorem B2650103 : Blo 1176405 2650103 := bstep (se 1 (by rfl) ⟨1987577, by rfl⟩ : syracuseStep 2650103 = 3975155) B3975155
theorem B22630529 : Blo 1176405 22630529 := bstep (se 2 (by rfl) ⟨8486448, by rfl⟩ : syracuseStep 22630529 = 16972897) B16972897
theorem B18116741 : Blo 1176405 18116741 := bstep (se 4 (by rfl) ⟨1698444, by rfl⟩ : syracuseStep 18116741 = 3396889) B3396889
theorem B6361249 : Blo 1176405 6361249 := bstep (se 2 (by rfl) ⟨2385468, by rfl⟩ : syracuseStep 6361249 = 4770937) B4770937
theorem B1986727 : Blo 1176405 1986727 := bstep (se 1 (by rfl) ⟨1490045, by rfl⟩ : syracuseStep 1986727 = 2980091) B2980091
theorem B4469377 : Blo 1176405 4469377 := bstep (se 2 (by rfl) ⟨1676016, by rfl⟩ : syracuseStep 4469377 = 3352033) B3352033
theorem B2650751 : Blo 1176405 2650751 := bstep (se 1 (by rfl) ⟨1988063, by rfl⟩ : syracuseStep 2650751 = 3976127) B3976127
theorem B1323751 : Blo 1176405 1323751 := bstep (se 1 (by rfl) ⟨992813, by rfl⟩ : syracuseStep 1323751 = 1985627) B1985627
theorem B3183457 : Blo 1176405 3183457 := bstep (se 2 (by rfl) ⟨1193796, by rfl⟩ : syracuseStep 3183457 = 2387593) B2387593
theorem B1766267 : Blo 1176405 1766267 := bstep (se 1 (by rfl) ⟨1324700, by rfl⟩ : syracuseStep 1766267 = 2649401) B2649401
theorem B1987625 : Blo 1176405 1987625 := bstep (se 2 (by rfl) ⟨745359, by rfl⟩ : syracuseStep 1987625 = 1490719) B1490719
theorem B2651327 : Blo 1176405 2651327 := bstep (se 1 (by rfl) ⟨1988495, by rfl⟩ : syracuseStep 2651327 = 3976991) B3976991
theorem B1324255 : Blo 1176405 1324255 := bstep (se 1 (by rfl) ⟨993191, by rfl⟩ : syracuseStep 1324255 = 1986383) B1986383
theorem B6706435 : Blo 1176405 6706435 := bstep (se 1 (by rfl) ⟨5029826, by rfl⟩ : syracuseStep 6706435 = 10059653) B10059653
theorem B1766711 : Blo 1176405 1766711 := bstep (se 1 (by rfl) ⟨1325033, by rfl⟩ : syracuseStep 1766711 = 2650067) B2650067
theorem B6042937 : Blo 1176405 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B6362633 : Blo 1176405 6362633 := bstep (se 2 (by rfl) ⟨2385987, by rfl⟩ : syracuseStep 6362633 = 4771975) B4771975
theorem B1766939 : Blo 1176405 1766939 := bstep (se 1 (by rfl) ⟨1325204, by rfl⟩ : syracuseStep 1766939 = 2650409) B2650409
theorem B1767323 : Blo 1176405 1767323 := bstep (se 1 (by rfl) ⟨1325492, by rfl⟩ : syracuseStep 1767323 = 2650985) B2650985
theorem B22624379 : Blo 1176405 22624379 := bstep (se 1 (by rfl) ⟨16968284, by rfl⟩ : syracuseStep 22624379 = 33936569) B33936569
theorem B1325263 : Blo 1176405 1325263 := bstep (se 1 (by rfl) ⟨993947, by rfl⟩ : syracuseStep 1325263 = 1987895) B1987895
theorem B1177883 : Blo 1176405 1177883 := bstep (se 1 (by rfl) ⟨883412, by rfl⟩ : syracuseStep 1177883 = 1766825) B1766825
theorem B1177919 : Blo 1176405 1177919 := bstep (se 1 (by rfl) ⟨883439, by rfl⟩ : syracuseStep 1177919 = 1766879) B1766879
theorem B7649761 : Blo 1176405 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B3971699 : Blo 1176405 3971699 := bstep (se 1 (by rfl) ⟨2978774, by rfl⟩ : syracuseStep 3971699 = 5957549) B5957549
theorem B2235023 : Blo 1176405 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B10738331 : Blo 1176405 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B1178351 : Blo 1176405 1178351 := bstep (se 1 (by rfl) ⟨883763, by rfl⟩ : syracuseStep 1178351 = 1767527) B1767527
theorem B3021707 : Blo 1176405 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B16981325 : Blo 1176405 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B13401935 : Blo 1176405 13401935 := bstep (se 1 (by rfl) ⟨10051451, by rfl⟩ : syracuseStep 13401935 = 20102903) B20102903
theorem B8716187 : Blo 1176405 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B8945801 : Blo 1176405 8945801 := bstep (se 2 (by rfl) ⟨3354675, by rfl⟩ : syracuseStep 8945801 = 6709351) B6709351
theorem B15286583 : Blo 1176405 15286583 := bstep (se 1 (by rfl) ⟨11464937, by rfl⟩ : syracuseStep 15286583 = 22929875) B22929875
theorem B10199681 : Blo 1176405 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B4244609 : Blo 1176405 4244609 := bstep (se 2 (by rfl) ⟨1591728, by rfl⟩ : syracuseStep 4244609 = 3183457) B3183457
theorem B7750943 : Blo 1176405 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B15082919 : Blo 1176405 15082919 := bstep (se 1 (by rfl) ⟨11312189, by rfl⟩ : syracuseStep 15082919 = 22624379) B22624379
theorem B2647799 : Blo 1176405 2647799 := bstep (se 1 (by rfl) ⟨1985849, by rfl⟩ : syracuseStep 2647799 = 3971699) B3971699
theorem B5654711 : Blo 1176405 5654711 := bstep (se 1 (by rfl) ⟨4241033, by rfl⟩ : syracuseStep 5654711 = 8482067) B8482067
theorem B5032219 : Blo 1176405 5032219 := bstep (se 1 (by rfl) ⟨3774164, by rfl⟩ : syracuseStep 5032219 = 7548329) B7548329
theorem B10750265 : Blo 1176405 10750265 := bstep (se 2 (by rfl) ⟨4031349, by rfl⟩ : syracuseStep 10750265 = 8062699) B8062699
theorem B3770783 : Blo 1176405 3770783 := bstep (se 1 (by rfl) ⟨2828087, by rfl⟩ : syracuseStep 3770783 = 5656175) B5656175
theorem B5810791 : Blo 1176405 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B4467419 : Blo 1176405 4467419 := bstep (se 1 (by rfl) ⟨3350564, by rfl⟩ : syracuseStep 4467419 = 6701129) B6701129
theorem B8481665 : Blo 1176405 8481665 := bstep (se 2 (by rfl) ⟨3180624, by rfl⟩ : syracuseStep 8481665 = 6361249) B6361249
theorem B2648969 : Blo 1176405 2648969 := bstep (se 2 (by rfl) ⟨993363, by rfl⟩ : syracuseStep 2648969 = 1986727) B1986727
theorem B48311309 : Blo 1176405 48311309 := bstep (se 3 (by rfl) ⟨9058370, by rfl⟩ : syracuseStep 48311309 = 18116741) B18116741
theorem B3681335 : Blo 1176405 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B1764635 : Blo 1176405 1764635 := bstep (se 1 (by rfl) ⟨1323476, by rfl⟩ : syracuseStep 1764635 = 2646953) B2646953
theorem B3976559 : Blo 1176405 3976559 := bstep (se 1 (by rfl) ⟨2982419, by rfl⟩ : syracuseStep 3976559 = 5964839) B5964839
theorem B5959169 : Blo 1176405 5959169 := bstep (se 2 (by rfl) ⟨2234688, by rfl⟩ : syracuseStep 5959169 = 4469377) B4469377
theorem B16100927 : Blo 1176405 16100927 := bstep (se 1 (by rfl) ⟨12075695, by rfl⟩ : syracuseStep 16100927 = 24151391) B24151391
theorem B3976775 : Blo 1176405 3976775 := bstep (se 1 (by rfl) ⟨2982581, by rfl⟩ : syracuseStep 3976775 = 5965163) B5965163
theorem B1765001 : Blo 1176405 1765001 := bstep (se 2 (by rfl) ⟨661875, by rfl⟩ : syracuseStep 1765001 = 1323751) B1323751
theorem B1765055 : Blo 1176405 1765055 := bstep (se 1 (by rfl) ⟨1323791, by rfl⟩ : syracuseStep 1765055 = 2647583) B2647583
theorem B8482589 : Blo 1176405 8482589 := bstep (se 3 (by rfl) ⟨1590485, by rfl⟩ : syracuseStep 8482589 = 3180971) B3180971
theorem B4534055 : Blo 1176405 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B22638527 : Blo 1176405 22638527 := bstep (se 1 (by rfl) ⟨16978895, by rfl⟩ : syracuseStep 22638527 = 33957791) B33957791
theorem B1765439 : Blo 1176405 1765439 := bstep (se 1 (by rfl) ⟨1324079, by rfl⟩ : syracuseStep 1765439 = 2648159) B2648159
theorem B24187025 : Blo 1176405 24187025 := bstep (se 2 (by rfl) ⟨9070134, by rfl⟩ : syracuseStep 24187025 = 18140269) B18140269
theorem B4468891 : Blo 1176405 4468891 := bstep (se 1 (by rfl) ⟨3351668, by rfl⟩ : syracuseStep 4468891 = 6703337) B6703337
theorem B1765673 : Blo 1176405 1765673 := bstep (se 2 (by rfl) ⟨662127, by rfl⟩ : syracuseStep 1765673 = 1324255) B1324255
theorem B8941913 : Blo 1176405 8941913 := bstep (se 2 (by rfl) ⟨3353217, by rfl⟩ : syracuseStep 8941913 = 6706435) B6706435
theorem B2650463 : Blo 1176405 2650463 := bstep (se 1 (by rfl) ⟨1987847, by rfl⟩ : syracuseStep 2650463 = 3975695) B3975695
theorem B8057249 : Blo 1176405 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B1765823 : Blo 1176405 1765823 := bstep (se 1 (by rfl) ⟨1324367, by rfl⟩ : syracuseStep 1765823 = 2648735) B2648735
theorem B1765919 : Blo 1176405 1765919 := bstep (se 1 (by rfl) ⟨1324439, by rfl⟩ : syracuseStep 1765919 = 2648879) B2648879
theorem B1766183 : Blo 1176405 1766183 := bstep (se 1 (by rfl) ⟨1324637, by rfl⟩ : syracuseStep 1766183 = 2649275) B2649275
theorem B1176511 : Blo 1176405 1176511 := bstep (se 1 (by rfl) ⟨882383, by rfl⟩ : syracuseStep 1176511 = 1764767) B1764767
theorem B4240343 : Blo 1176405 4240343 := bstep (se 1 (by rfl) ⟨3180257, by rfl⟩ : syracuseStep 4240343 = 6360515) B6360515
theorem B4469863 : Blo 1176405 4469863 := bstep (se 1 (by rfl) ⟨3352397, by rfl⟩ : syracuseStep 4469863 = 6704795) B6704795
theorem B8934623 : Blo 1176405 8934623 := bstep (se 1 (by rfl) ⟨6700967, by rfl⟩ : syracuseStep 8934623 = 13401935) B13401935
theorem B1766735 : Blo 1176405 1766735 := bstep (se 1 (by rfl) ⟨1325051, by rfl⟩ : syracuseStep 1766735 = 2650103) B2650103
theorem B15087019 : Blo 1176405 15087019 := bstep (se 1 (by rfl) ⟨11315264, by rfl⟩ : syracuseStep 15087019 = 22630529) B22630529
theorem B3970511 : Blo 1176405 3970511 := bstep (se 1 (by rfl) ⟨2977883, by rfl⟩ : syracuseStep 3970511 = 5955767) B5955767
theorem B1767017 : Blo 1176405 1767017 := bstep (se 2 (by rfl) ⟨662631, by rfl⟩ : syracuseStep 1767017 = 1325263) B1325263
theorem B1988327 : Blo 1176405 1988327 := bstep (se 1 (by rfl) ⟨1491245, by rfl⟩ : syracuseStep 1988327 = 2982491) B2982491
theorem B1767167 : Blo 1176405 1767167 := bstep (se 1 (by rfl) ⟨1325375, by rfl⟩ : syracuseStep 1767167 = 2650751) B2650751
theorem B2234279 : Blo 1176405 2234279 := bstep (se 1 (by rfl) ⟨1675709, by rfl⟩ : syracuseStep 2234279 = 3351419) B3351419
theorem B1177511 : Blo 1176405 1177511 := bstep (se 1 (by rfl) ⟨883133, by rfl⟩ : syracuseStep 1177511 = 1766267) B1766267
theorem B1325083 : Blo 1176405 1325083 := bstep (se 1 (by rfl) ⟨993812, by rfl⟩ : syracuseStep 1325083 = 1987625) B1987625
theorem B1767551 : Blo 1176405 1767551 := bstep (se 1 (by rfl) ⟨1325663, by rfl⟩ : syracuseStep 1767551 = 2651327) B2651327
theorem B1177807 : Blo 1176405 1177807 := bstep (se 1 (by rfl) ⟨883355, by rfl⟩ : syracuseStep 1177807 = 1766711) B1766711
theorem B4241755 : Blo 1176405 4241755 := bstep (se 1 (by rfl) ⟨3181316, by rfl⟩ : syracuseStep 4241755 = 6362633) B6362633
theorem B1177959 : Blo 1176405 1177959 := bstep (se 1 (by rfl) ⟨883469, by rfl⟩ : syracuseStep 1177959 = 1766939) B1766939
theorem B1178215 : Blo 1176405 1178215 := bstep (se 1 (by rfl) ⟨883661, by rfl⟩ : syracuseStep 1178215 = 1767323) B1767323
theorem B11320033 : Blo 1176405 11320033 := bstep (se 2 (by rfl) ⟨4245012, by rfl⟩ : syracuseStep 11320033 = 8490025) B8490025
theorem B2120575 : Blo 1176405 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B1490015 : Blo 1176405 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B7158887 : Blo 1176405 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B36723865 : Blo 1176405 36723865 := bstep (se 2 (by rfl) ⟨13771449, by rfl⟩ : syracuseStep 36723865 = 27542899) B27542899
theorem B2014471 : Blo 1176405 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B11320883 : Blo 1176405 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B5963867 : Blo 1176405 5963867 := bstep (se 1 (by rfl) ⟨4472900, by rfl⟩ : syracuseStep 5963867 = 8945801) B8945801
theorem B10191055 : Blo 1176405 10191055 := bstep (se 1 (by rfl) ⟨7643291, by rfl⟩ : syracuseStep 10191055 = 15286583) B15286583
theorem B3973373 : Blo 1176405 3973373 := bstep (se 3 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 3973373 = 1490015) B1490015
theorem B6709625 : Blo 1176405 6709625 := bstep (se 2 (by rfl) ⟨2516109, by rfl⟩ : syracuseStep 6709625 = 5032219) B5032219
theorem B6799787 : Blo 1176405 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B2826895 : Blo 1176405 2826895 := bstep (se 1 (by rfl) ⟨2120171, by rfl⟩ : syracuseStep 2826895 = 4240343) B4240343
theorem B5956415 : Blo 1176405 5956415 := bstep (se 1 (by rfl) ⟨4467311, by rfl⟩ : syracuseStep 5956415 = 8934623) B8934623
theorem B2647007 : Blo 1176405 2647007 := bstep (se 1 (by rfl) ⟨1985255, by rfl⟩ : syracuseStep 2647007 = 3970511) B3970511
theorem B2827433 : Blo 1176405 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B48965153 : Blo 1176405 48965153 := bstep (se 2 (by rfl) ⟨18361932, by rfl⟩ : syracuseStep 48965153 = 36723865) B36723865
theorem B5654443 : Blo 1176405 5654443 := bstep (se 1 (by rfl) ⟨4240832, by rfl⟩ : syracuseStep 5654443 = 8481665) B8481665
theorem B7547255 : Blo 1176405 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B10733951 : Blo 1176405 10733951 := bstep (se 1 (by rfl) ⟨8050463, by rfl⟩ : syracuseStep 10733951 = 16100927) B16100927
theorem B5655059 : Blo 1176405 5655059 := bstep (se 1 (by rfl) ⟨4241294, by rfl⟩ : syracuseStep 5655059 = 8482589) B8482589
theorem B15092351 : Blo 1176405 15092351 := bstep (se 1 (by rfl) ⟨11319263, by rfl⟩ : syracuseStep 15092351 = 22638527) B22638527
theorem B16124683 : Blo 1176405 16124683 := bstep (se 1 (by rfl) ⟨12093512, by rfl⟩ : syracuseStep 16124683 = 24187025) B24187025
theorem B5958521 : Blo 1176405 5958521 := bstep (se 2 (by rfl) ⟨2234445, by rfl⟩ : syracuseStep 5958521 = 4468891) B4468891
theorem B5655673 : Blo 1176405 5655673 := bstep (se 2 (by rfl) ⟨2120877, by rfl⟩ : syracuseStep 5655673 = 4241755) B4241755
theorem B2829739 : Blo 1176405 2829739 := bstep (se 1 (by rfl) ⟨2122304, by rfl⟩ : syracuseStep 2829739 = 4244609) B4244609
theorem B10055279 : Blo 1176405 10055279 := bstep (se 1 (by rfl) ⟨7541459, by rfl⟩ : syracuseStep 10055279 = 15082919) B15082919
theorem B15093377 : Blo 1176405 15093377 := bstep (se 2 (by rfl) ⟨5660016, by rfl⟩ : syracuseStep 15093377 = 11320033) B11320033
theorem B1765199 : Blo 1176405 1765199 := bstep (se 1 (by rfl) ⟨1323899, by rfl⟩ : syracuseStep 1765199 = 2647799) B2647799
theorem B5959817 : Blo 1176405 5959817 := bstep (se 2 (by rfl) ⟨2234931, by rfl⟩ : syracuseStep 5959817 = 4469863) B4469863
theorem B2978279 : Blo 1176405 2978279 := bstep (se 1 (by rfl) ⟨2233709, by rfl⟩ : syracuseStep 2978279 = 4467419) B4467419
theorem B20116025 : Blo 1176405 20116025 := bstep (se 2 (by rfl) ⟨7543509, by rfl⟩ : syracuseStep 20116025 = 15087019) B15087019
theorem B1765979 : Blo 1176405 1765979 := bstep (se 1 (by rfl) ⟨1324484, by rfl⟩ : syracuseStep 1765979 = 2648969) B2648969
theorem B32207539 : Blo 1176405 32207539 := bstep (se 1 (by rfl) ⟨24155654, by rfl⟩ : syracuseStep 32207539 = 48311309) B48311309
theorem B2454223 : Blo 1176405 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B4772591 : Blo 1176405 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B1176423 : Blo 1176405 1176423 := bstep (se 1 (by rfl) ⟨882317, by rfl⟩ : syracuseStep 1176423 = 1764635) B1764635
theorem B2651039 : Blo 1176405 2651039 := bstep (se 1 (by rfl) ⟨1988279, by rfl⟩ : syracuseStep 2651039 = 3976559) B3976559
theorem B2651183 : Blo 1176405 2651183 := bstep (se 1 (by rfl) ⟨1988387, by rfl⟩ : syracuseStep 2651183 = 3976775) B3976775
theorem B1176667 : Blo 1176405 1176667 := bstep (se 1 (by rfl) ⟨882500, by rfl⟩ : syracuseStep 1176667 = 1765001) B1765001
theorem B1176703 : Blo 1176405 1176703 := bstep (se 1 (by rfl) ⟨882527, by rfl⟩ : syracuseStep 1176703 = 1765055) B1765055
theorem B1766777 : Blo 1176405 1766777 := bstep (se 2 (by rfl) ⟨662541, by rfl⟩ : syracuseStep 1766777 = 1325083) B1325083
theorem B1176959 : Blo 1176405 1176959 := bstep (se 1 (by rfl) ⟨882719, by rfl⟩ : syracuseStep 1176959 = 1765439) B1765439
theorem B1177115 : Blo 1176405 1177115 := bstep (se 1 (by rfl) ⟨882836, by rfl⟩ : syracuseStep 1177115 = 1765673) B1765673
theorem B5961275 : Blo 1176405 5961275 := bstep (se 1 (by rfl) ⟨4470956, by rfl⟩ : syracuseStep 5961275 = 8941913) B8941913
theorem B1766975 : Blo 1176405 1766975 := bstep (se 1 (by rfl) ⟨1325231, by rfl⟩ : syracuseStep 1766975 = 2650463) B2650463
theorem B5371499 : Blo 1176405 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B1177215 : Blo 1176405 1177215 := bstep (se 1 (by rfl) ⟨882911, by rfl⟩ : syracuseStep 1177215 = 1765823) B1765823
theorem B1177279 : Blo 1176405 1177279 := bstep (se 1 (by rfl) ⟨882959, by rfl⟩ : syracuseStep 1177279 = 1765919) B1765919
theorem B15079229 : Blo 1176405 15079229 := bstep (se 3 (by rfl) ⟨2827355, by rfl⟩ : syracuseStep 15079229 = 5654711) B5654711
theorem B1177455 : Blo 1176405 1177455 := bstep (se 1 (by rfl) ⟨883091, by rfl⟩ : syracuseStep 1177455 = 1766183) B1766183
theorem B7747721 : Blo 1176405 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B5167295 : Blo 1176405 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B1177823 : Blo 1176405 1177823 := bstep (se 1 (by rfl) ⟨883367, by rfl⟩ : syracuseStep 1177823 = 1766735) B1766735
theorem B1178011 : Blo 1176405 1178011 := bstep (se 1 (by rfl) ⟨883508, by rfl⟩ : syracuseStep 1178011 = 1767017) B1767017
theorem B1325551 : Blo 1176405 1325551 := bstep (se 1 (by rfl) ⟨994163, by rfl⟩ : syracuseStep 1325551 = 1988327) B1988327
theorem B1178111 : Blo 1176405 1178111 := bstep (se 1 (by rfl) ⟨883583, by rfl⟩ : syracuseStep 1178111 = 1767167) B1767167
theorem B1489519 : Blo 1176405 1489519 := bstep (se 1 (by rfl) ⟨1117139, by rfl⟩ : syracuseStep 1489519 = 2234279) B2234279
theorem B1178367 : Blo 1176405 1178367 := bstep (se 1 (by rfl) ⟨883775, by rfl⟩ : syracuseStep 1178367 = 1767551) B1767551
theorem B7166843 : Blo 1176405 7166843 := bstep (se 1 (by rfl) ⟨5375132, by rfl⟩ : syracuseStep 7166843 = 10750265) B10750265
theorem B2513855 : Blo 1176405 2513855 := bstep (se 1 (by rfl) ⟨1885391, by rfl⟩ : syracuseStep 2513855 = 3770783) B3770783
theorem B2685961 : Blo 1176405 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B3972779 : Blo 1176405 3972779 := bstep (se 1 (by rfl) ⟨2979584, by rfl⟩ : syracuseStep 3972779 = 5959169) B5959169
theorem B3022703 : Blo 1176405 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B3973211 : Blo 1176405 3973211 := bstep (se 1 (by rfl) ⟨2979908, by rfl⟩ : syracuseStep 3973211 = 5959817) B5959817
theorem B4473083 : Blo 1176405 4473083 := bstep (se 1 (by rfl) ⟨3354812, by rfl⟩ : syracuseStep 4473083 = 6709625) B6709625
theorem B13410683 : Blo 1176405 13410683 := bstep (se 1 (by rfl) ⟨10058012, by rfl⟩ : syracuseStep 13410683 = 20116025) B20116025
theorem B1884955 : Blo 1176405 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B3769193 : Blo 1176405 3769193 := bstep (se 2 (by rfl) ⟨1413447, by rfl⟩ : syracuseStep 3769193 = 2826895) B2826895
theorem B42943385 : Blo 1176405 42943385 := bstep (se 2 (by rfl) ⟨16103769, by rfl⟩ : syracuseStep 42943385 = 32207539) B32207539
theorem B3974183 : Blo 1176405 3974183 := bstep (se 1 (by rfl) ⟨2980637, by rfl⟩ : syracuseStep 3974183 = 5961275) B5961275
theorem B3580999 : Blo 1176405 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B10052819 : Blo 1176405 10052819 := bstep (se 1 (by rfl) ⟨7539614, by rfl⟩ : syracuseStep 10052819 = 15079229) B15079229
theorem B3581281 : Blo 1176405 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B130573741 : Blo 1176405 130573741 := bstep (se 3 (by rfl) ⟨24482576, by rfl⟩ : syracuseStep 130573741 = 48965153) B48965153
theorem B5031503 : Blo 1176405 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B3770039 : Blo 1176405 3770039 := bstep (se 1 (by rfl) ⟨2827529, by rfl⟩ : syracuseStep 3770039 = 5655059) B5655059
theorem B10061567 : Blo 1176405 10061567 := bstep (se 1 (by rfl) ⟨7546175, by rfl⟩ : syracuseStep 10061567 = 15092351) B15092351
theorem B4777895 : Blo 1176405 4777895 := bstep (se 1 (by rfl) ⟨3583421, by rfl⟩ : syracuseStep 4777895 = 7166843) B7166843
theorem B6703519 : Blo 1176405 6703519 := bstep (se 1 (by rfl) ⟨5027639, by rfl⟩ : syracuseStep 6703519 = 10055279) B10055279
theorem B10062251 : Blo 1176405 10062251 := bstep (se 1 (by rfl) ⟨7546688, by rfl⟩ : syracuseStep 10062251 = 15093377) B15093377
theorem B2648519 : Blo 1176405 2648519 := bstep (se 1 (by rfl) ⟨1986389, by rfl⟩ : syracuseStep 2648519 = 3972779) B3972779
theorem B7539257 : Blo 1176405 7539257 := bstep (se 2 (by rfl) ⟨2827221, by rfl⟩ : syracuseStep 7539257 = 5654443) B5654443
theorem B3975911 : Blo 1176405 3975911 := bstep (se 1 (by rfl) ⟨2981933, by rfl⟩ : syracuseStep 3975911 = 5963867) B5963867
theorem B2648915 : Blo 1176405 2648915 := bstep (se 1 (by rfl) ⟨1986686, by rfl⟩ : syracuseStep 2648915 = 3973373) B3973373
theorem B4533191 : Blo 1176405 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B1985519 : Blo 1176405 1985519 := bstep (se 1 (by rfl) ⟨1489139, by rfl⟩ : syracuseStep 1985519 = 2978279) B2978279
theorem B3181727 : Blo 1176405 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B1764671 : Blo 1176405 1764671 := bstep (se 1 (by rfl) ⟨1323503, by rfl⟩ : syracuseStep 1764671 = 2647007) B2647007
theorem B1986025 : Blo 1176405 1986025 := bstep (se 2 (by rfl) ⟨744759, by rfl⟩ : syracuseStep 1986025 = 1489519) B1489519
theorem B3272297 : Blo 1176405 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B21499577 : Blo 1176405 21499577 := bstep (se 2 (by rfl) ⟨8062341, by rfl⟩ : syracuseStep 21499577 = 16124683) B16124683
theorem B5165147 : Blo 1176405 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B3444863 : Blo 1176405 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B7540897 : Blo 1176405 7540897 := bstep (se 2 (by rfl) ⟨2827836, by rfl⟩ : syracuseStep 7540897 = 5655673) B5655673
theorem B7155967 : Blo 1176405 7155967 := bstep (se 1 (by rfl) ⟨5366975, by rfl⟩ : syracuseStep 7155967 = 10733951) B10733951
theorem B3772985 : Blo 1176405 3772985 := bstep (se 2 (by rfl) ⟨1414869, by rfl⟩ : syracuseStep 3772985 = 2829739) B2829739
theorem B1675903 : Blo 1176405 1675903 := bstep (se 1 (by rfl) ⟨1256927, by rfl⟩ : syracuseStep 1675903 = 2513855) B2513855
theorem B1176799 : Blo 1176405 1176799 := bstep (se 1 (by rfl) ⟨882599, by rfl⟩ : syracuseStep 1176799 = 1765199) B1765199
theorem B13588073 : Blo 1176405 13588073 := bstep (se 2 (by rfl) ⟨5095527, by rfl⟩ : syracuseStep 13588073 = 10191055) B10191055
theorem B1177319 : Blo 1176405 1177319 := bstep (se 1 (by rfl) ⟨882989, by rfl⟩ : syracuseStep 1177319 = 1765979) B1765979
theorem B3970943 : Blo 1176405 3970943 := bstep (se 1 (by rfl) ⟨2978207, by rfl⟩ : syracuseStep 3970943 = 5956415) B5956415
theorem B1767359 : Blo 1176405 1767359 := bstep (se 1 (by rfl) ⟨1325519, by rfl⟩ : syracuseStep 1767359 = 2651039) B2651039
theorem B1767401 : Blo 1176405 1767401 := bstep (se 2 (by rfl) ⟨662775, by rfl⟩ : syracuseStep 1767401 = 1325551) B1325551
theorem B1767455 : Blo 1176405 1767455 := bstep (se 1 (by rfl) ⟨1325591, by rfl⟩ : syracuseStep 1767455 = 2651183) B2651183
theorem B1177851 : Blo 1176405 1177851 := bstep (se 1 (by rfl) ⟨883388, by rfl⟩ : syracuseStep 1177851 = 1766777) B1766777
theorem B1177983 : Blo 1176405 1177983 := bstep (se 1 (by rfl) ⟨883487, by rfl⟩ : syracuseStep 1177983 = 1766975) B1766975
theorem B3972347 : Blo 1176405 3972347 := bstep (se 1 (by rfl) ⟨2979260, by rfl⟩ : syracuseStep 3972347 = 5958521) B5958521
theorem B2015135 : Blo 1176405 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B2982055 : Blo 1176405 2982055 := bstep (se 1 (by rfl) ⟨2236541, by rfl⟩ : syracuseStep 2982055 = 4473083) B4473083
theorem B8938025 : Blo 1176405 8938025 := bstep (se 2 (by rfl) ⟨3351759, by rfl⟩ : syracuseStep 8938025 = 6703519) B6703519
theorem B6701879 : Blo 1176405 6701879 := bstep (se 1 (by rfl) ⟨5026409, by rfl⟩ : syracuseStep 6701879 = 10052819) B10052819
theorem B2647295 : Blo 1176405 2647295 := bstep (se 1 (by rfl) ⟨1985471, by rfl⟩ : syracuseStep 2647295 = 3970943) B3970943
theorem B10061293 : Blo 1176405 10061293 := bstep (se 3 (by rfl) ⟨1886492, by rfl⟩ : syracuseStep 10061293 = 3772985) B3772985
theorem B8726125 : Blo 1176405 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B174098321 : Blo 1176405 174098321 := bstep (se 2 (by rfl) ⟨65286870, by rfl⟩ : syracuseStep 174098321 = 130573741) B130573741
theorem B2648033 : Blo 1176405 2648033 := bstep (se 2 (by rfl) ⟨993012, by rfl⟩ : syracuseStep 2648033 = 1986025) B1986025
theorem B2648231 : Blo 1176405 2648231 := bstep (se 1 (by rfl) ⟨1986173, by rfl⟩ : syracuseStep 2648231 = 3972347) B3972347
theorem B2648807 : Blo 1176405 2648807 := bstep (se 1 (by rfl) ⟨1986605, by rfl⟩ : syracuseStep 2648807 = 3973211) B3973211
theorem B10054529 : Blo 1176405 10054529 := bstep (se 2 (by rfl) ⟨3770448, by rfl⟩ : syracuseStep 10054529 = 7540897) B7540897
theorem B13773725 : Blo 1176405 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B8940455 : Blo 1176405 8940455 := bstep (se 1 (by rfl) ⟨6705341, by rfl⟩ : syracuseStep 8940455 = 13410683) B13410683
theorem B9186301 : Blo 1176405 9186301 := bstep (se 3 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 9186301 = 3444863) B3444863
theorem B19098661 : Blo 1176405 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B2649455 : Blo 1176405 2649455 := bstep (se 1 (by rfl) ⟨1987091, by rfl⟩ : syracuseStep 2649455 = 3974183) B3974183
theorem B3354335 : Blo 1176405 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B1765679 : Blo 1176405 1765679 := bstep (se 1 (by rfl) ⟨1324259, by rfl⟩ : syracuseStep 1765679 = 2648519) B2648519
theorem B5026171 : Blo 1176405 5026171 := bstep (se 1 (by rfl) ⟨3769628, by rfl⟩ : syracuseStep 5026171 = 7539257) B7539257
theorem B2650607 : Blo 1176405 2650607 := bstep (se 1 (by rfl) ⟨1987955, by rfl⟩ : syracuseStep 2650607 = 3975911) B3975911
theorem B1765943 : Blo 1176405 1765943 := bstep (se 1 (by rfl) ⟨1324457, by rfl⟩ : syracuseStep 1765943 = 2648915) B2648915
theorem B1323679 : Blo 1176405 1323679 := bstep (se 1 (by rfl) ⟨992759, by rfl⟩ : syracuseStep 1323679 = 1985519) B1985519
theorem B1176447 : Blo 1176405 1176447 := bstep (se 1 (by rfl) ⟨882335, by rfl⟩ : syracuseStep 1176447 = 1764671) B1764671
theorem B14333051 : Blo 1176405 14333051 := bstep (se 1 (by rfl) ⟨10749788, by rfl⟩ : syracuseStep 14333051 = 21499577) B21499577
theorem B9541289 : Blo 1176405 9541289 := bstep (se 2 (by rfl) ⟨3577983, by rfl⟩ : syracuseStep 9541289 = 7155967) B7155967
theorem B2512795 : Blo 1176405 2512795 := bstep (se 1 (by rfl) ⟨1884596, by rfl⟩ : syracuseStep 2512795 = 3769193) B3769193
theorem B2234537 : Blo 1176405 2234537 := bstep (se 2 (by rfl) ⟨837951, by rfl⟩ : syracuseStep 2234537 = 1675903) B1675903
theorem B2513273 : Blo 1176405 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B9058715 : Blo 1176405 9058715 := bstep (se 1 (by rfl) ⟨6794036, by rfl⟩ : syracuseStep 9058715 = 13588073) B13588073
theorem B2513359 : Blo 1176405 2513359 := bstep (se 1 (by rfl) ⟨1885019, by rfl⟩ : syracuseStep 2513359 = 3770039) B3770039
theorem B6707711 : Blo 1176405 6707711 := bstep (se 1 (by rfl) ⟨5030783, by rfl⟩ : syracuseStep 6707711 = 10061567) B10061567
theorem B3185263 : Blo 1176405 3185263 := bstep (se 1 (by rfl) ⟨2388947, by rfl⟩ : syracuseStep 3185263 = 4777895) B4777895
theorem B1178239 : Blo 1176405 1178239 := bstep (se 1 (by rfl) ⟨883679, by rfl⟩ : syracuseStep 1178239 = 1767359) B1767359
theorem B1178267 : Blo 1176405 1178267 := bstep (se 1 (by rfl) ⟨883700, by rfl⟩ : syracuseStep 1178267 = 1767401) B1767401
theorem B1178303 : Blo 1176405 1178303 := bstep (se 1 (by rfl) ⟨883727, by rfl⟩ : syracuseStep 1178303 = 1767455) B1767455
theorem B6708167 : Blo 1176405 6708167 := bstep (se 1 (by rfl) ⟨5031125, by rfl⟩ : syracuseStep 6708167 = 10062251) B10062251
theorem B4775041 : Blo 1176405 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B3022127 : Blo 1176405 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B2121151 : Blo 1176405 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B114515693 : Blo 1176405 114515693 := bstep (se 3 (by rfl) ⟨21471692, by rfl⟩ : syracuseStep 114515693 = 42943385) B42943385
theorem B1343423 : Blo 1176405 1343423 := bstep (se 1 (by rfl) ⟨1007567, by rfl⟩ : syracuseStep 1343423 = 2015135) B2015135
theorem B6701561 : Blo 1176405 6701561 := bstep (se 2 (by rfl) ⟨2513085, by rfl⟩ : syracuseStep 6701561 = 5026171) B5026171
theorem B3351145 : Blo 1176405 3351145 := bstep (se 2 (by rfl) ⟨1256679, by rfl⟩ : syracuseStep 3351145 = 2513359) B2513359
theorem B6702061 : Blo 1176405 6702061 := bstep (se 3 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 6702061 = 2513273) B2513273
theorem B116065547 : Blo 1176405 116065547 := bstep (se 1 (by rfl) ⟨87049160, by rfl⟩ : syracuseStep 116065547 = 174098321) B174098321
theorem B12248401 : Blo 1176405 12248401 := bstep (se 2 (by rfl) ⟨4593150, by rfl⟩ : syracuseStep 12248401 = 9186301) B9186301
theorem B6039143 : Blo 1176405 6039143 := bstep (se 1 (by rfl) ⟨4529357, by rfl⟩ : syracuseStep 6039143 = 9058715) B9058715
theorem B2828201 : Blo 1176405 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B6703019 : Blo 1176405 6703019 := bstep (se 1 (by rfl) ⟨5027264, by rfl⟩ : syracuseStep 6703019 = 10054529) B10054529
theorem B11634833 : Blo 1176405 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B76343795 : Blo 1176405 76343795 := bstep (se 1 (by rfl) ⟨57257846, by rfl⟩ : syracuseStep 76343795 = 114515693) B114515693
theorem B3582461 : Blo 1176405 3582461 := bstep (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) B1343423
theorem B3976073 : Blo 1176405 3976073 := bstep (se 2 (by rfl) ⟨1491027, by rfl⟩ : syracuseStep 3976073 = 2982055) B2982055
theorem B5958683 : Blo 1176405 5958683 := bstep (se 1 (by rfl) ⟨4469012, by rfl⟩ : syracuseStep 5958683 = 8938025) B8938025
theorem B4467919 : Blo 1176405 4467919 := bstep (se 1 (by rfl) ⟨3350939, by rfl⟩ : syracuseStep 4467919 = 6701879) B6701879
theorem B1764863 : Blo 1176405 1764863 := bstep (se 1 (by rfl) ⟨1323647, by rfl⟩ : syracuseStep 1764863 = 2647295) B2647295
theorem B1764905 : Blo 1176405 1764905 := bstep (se 2 (by rfl) ⟨661839, by rfl⟩ : syracuseStep 1764905 = 1323679) B1323679
theorem B6360859 : Blo 1176405 6360859 := bstep (se 1 (by rfl) ⟨4770644, by rfl⟩ : syracuseStep 6360859 = 9541289) B9541289
theorem B1765355 : Blo 1176405 1765355 := bstep (se 1 (by rfl) ⟨1324016, by rfl⟩ : syracuseStep 1765355 = 2648033) B2648033
theorem B25464881 : Blo 1176405 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B1765487 : Blo 1176405 1765487 := bstep (se 1 (by rfl) ⟨1324115, by rfl⟩ : syracuseStep 1765487 = 2648231) B2648231
theorem B1765871 : Blo 1176405 1765871 := bstep (se 1 (by rfl) ⟨1324403, by rfl⟩ : syracuseStep 1765871 = 2648807) B2648807
theorem B5960303 : Blo 1176405 5960303 := bstep (se 1 (by rfl) ⟨4470227, by rfl⟩ : syracuseStep 5960303 = 8940455) B8940455
theorem B13415057 : Blo 1176405 13415057 := bstep (se 2 (by rfl) ⟨5030646, by rfl⟩ : syracuseStep 13415057 = 10061293) B10061293
theorem B1766303 : Blo 1176405 1766303 := bstep (se 1 (by rfl) ⟨1324727, by rfl⟩ : syracuseStep 1766303 = 2649455) B2649455
theorem B1177119 : Blo 1176405 1177119 := bstep (se 1 (by rfl) ⟨882839, by rfl⟩ : syracuseStep 1177119 = 1765679) B1765679
theorem B38221469 : Blo 1176405 38221469 := bstep (se 3 (by rfl) ⟨7166525, by rfl⟩ : syracuseStep 38221469 = 14333051) B14333051
theorem B1767071 : Blo 1176405 1767071 := bstep (se 1 (by rfl) ⟨1325303, by rfl⟩ : syracuseStep 1767071 = 2650607) B2650607
theorem B1177295 : Blo 1176405 1177295 := bstep (se 1 (by rfl) ⟨882971, by rfl⟩ : syracuseStep 1177295 = 1765943) B1765943
theorem B16988069 : Blo 1176405 16988069 := bstep (se 4 (by rfl) ⟨1592631, by rfl⟩ : syracuseStep 16988069 = 3185263) B3185263
theorem B25466885 : Blo 1176405 25466885 := bstep (se 4 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 25466885 = 4775041) B4775041
theorem B1489691 : Blo 1176405 1489691 := bstep (se 1 (by rfl) ⟨1117268, by rfl⟩ : syracuseStep 1489691 = 2234537) B2234537
theorem B4471807 : Blo 1176405 4471807 := bstep (se 1 (by rfl) ⟨3353855, by rfl⟩ : syracuseStep 4471807 = 6707711) B6707711
theorem B9182483 : Blo 1176405 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B4472111 : Blo 1176405 4472111 := bstep (se 1 (by rfl) ⟨3354083, by rfl⟩ : syracuseStep 4472111 = 6708167) B6708167
theorem B2014751 : Blo 1176405 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B2236223 : Blo 1176405 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B3350393 : Blo 1176405 3350393 := bstep (se 2 (by rfl) ⟨1256397, by rfl⟩ : syracuseStep 3350393 = 2512795) B2512795
theorem B3973535 : Blo 1176405 3973535 := bstep (se 1 (by rfl) ⟨2980151, by rfl⟩ : syracuseStep 3973535 = 5960303) B5960303
theorem B5957225 : Blo 1176405 5957225 := bstep (se 2 (by rfl) ⟨2233959, by rfl⟩ : syracuseStep 5957225 = 4467919) B4467919
theorem B6121655 : Blo 1176405 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B8481145 : Blo 1176405 8481145 := bstep (se 2 (by rfl) ⟨3180429, by rfl⟩ : syracuseStep 8481145 = 6360859) B6360859
theorem B67906349 : Blo 1176405 67906349 := bstep (se 3 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 67906349 = 25464881) B25464881
theorem B4467707 : Blo 1176405 4467707 := bstep (se 1 (by rfl) ⟨3350780, by rfl⟩ : syracuseStep 4467707 = 6701561) B6701561
theorem B4468193 : Blo 1176405 4468193 := bstep (se 2 (by rfl) ⟨1675572, by rfl⟩ : syracuseStep 4468193 = 3351145) B3351145
theorem B77377031 : Blo 1176405 77377031 := bstep (se 1 (by rfl) ⟨58032773, by rfl⟩ : syracuseStep 77377031 = 116065547) B116065547
theorem B4026095 : Blo 1176405 4026095 := bstep (se 1 (by rfl) ⟨3019571, by rfl⟩ : syracuseStep 4026095 = 6039143) B6039143
theorem B25480979 : Blo 1176405 25480979 := bstep (se 1 (by rfl) ⟨19110734, by rfl⟩ : syracuseStep 25480979 = 38221469) B38221469
theorem B11325379 : Blo 1176405 11325379 := bstep (se 1 (by rfl) ⟨8494034, by rfl⟩ : syracuseStep 11325379 = 16988069) B16988069
theorem B4468679 : Blo 1176405 4468679 := bstep (se 1 (by rfl) ⟨3351509, by rfl⟩ : syracuseStep 4468679 = 6703019) B6703019
theorem B16977923 : Blo 1176405 16977923 := bstep (se 1 (by rfl) ⟨12733442, by rfl⟩ : syracuseStep 16977923 = 25466885) B25466885
theorem B2388307 : Blo 1176405 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B30167477 : Blo 1176405 30167477 := bstep (se 5 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 30167477 = 2828201) B2828201
theorem B16331201 : Blo 1176405 16331201 := bstep (se 2 (by rfl) ⟨6124200, by rfl⟩ : syracuseStep 16331201 = 12248401) B12248401
theorem B2650715 : Blo 1176405 2650715 := bstep (se 1 (by rfl) ⟨1988036, by rfl⟩ : syracuseStep 2650715 = 3976073) B3976073
theorem B1176575 : Blo 1176405 1176575 := bstep (se 1 (by rfl) ⟨882431, by rfl⟩ : syracuseStep 1176575 = 1764863) B1764863
theorem B1176603 : Blo 1176405 1176603 := bstep (se 1 (by rfl) ⟨882452, by rfl⟩ : syracuseStep 1176603 = 1764905) B1764905
theorem B2233595 : Blo 1176405 2233595 := bstep (se 1 (by rfl) ⟨1675196, by rfl⟩ : syracuseStep 2233595 = 3350393) B3350393
theorem B1176903 : Blo 1176405 1176903 := bstep (se 1 (by rfl) ⟨882677, by rfl⟩ : syracuseStep 1176903 = 1765355) B1765355
theorem B1176991 : Blo 1176405 1176991 := bstep (se 1 (by rfl) ⟨882743, by rfl⟩ : syracuseStep 1176991 = 1765487) B1765487
theorem B1177247 : Blo 1176405 1177247 := bstep (se 1 (by rfl) ⟨882935, by rfl⟩ : syracuseStep 1177247 = 1765871) B1765871
theorem B8943371 : Blo 1176405 8943371 := bstep (se 1 (by rfl) ⟨6707528, by rfl⟩ : syracuseStep 8943371 = 13415057) B13415057
theorem B1177535 : Blo 1176405 1177535 := bstep (se 1 (by rfl) ⟨883151, by rfl⟩ : syracuseStep 1177535 = 1766303) B1766303
theorem B1178047 : Blo 1176405 1178047 := bstep (se 1 (by rfl) ⟨883535, by rfl⟩ : syracuseStep 1178047 = 1767071) B1767071
theorem B8936081 : Blo 1176405 8936081 := bstep (se 2 (by rfl) ⟨3351030, by rfl⟩ : syracuseStep 8936081 = 6702061) B6702061
theorem B5962409 : Blo 1176405 5962409 := bstep (se 2 (by rfl) ⟨2235903, by rfl⟩ : syracuseStep 5962409 = 4471807) B4471807
theorem B5372669 : Blo 1176405 5372669 := bstep (se 3 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 5372669 = 2014751) B2014751
theorem B7756555 : Blo 1176405 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B50895863 : Blo 1176405 50895863 := bstep (se 1 (by rfl) ⟨38171897, by rfl⟩ : syracuseStep 50895863 = 76343795) B76343795
theorem B3972455 : Blo 1176405 3972455 := bstep (se 1 (by rfl) ⟨2979341, by rfl⟩ : syracuseStep 3972455 = 5958683) B5958683
theorem B3972509 : Blo 1176405 3972509 := bstep (se 3 (by rfl) ⟨744845, by rfl⟩ : syracuseStep 3972509 = 1489691) B1489691
theorem B2981407 : Blo 1176405 2981407 := bstep (se 1 (by rfl) ⟨2236055, by rfl⟩ : syracuseStep 2981407 = 4472111) B4472111
theorem B1490815 : Blo 1176405 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B20111651 : Blo 1176405 20111651 := bstep (se 1 (by rfl) ⟨15083738, by rfl⟩ : syracuseStep 20111651 = 30167477) B30167477
theorem B10887467 : Blo 1176405 10887467 := bstep (se 1 (by rfl) ⟨8165600, by rfl⟩ : syracuseStep 10887467 = 16331201) B16331201
theorem B5956253 : Blo 1176405 5956253 := bstep (se 3 (by rfl) ⟨1116797, by rfl⟩ : syracuseStep 5956253 = 2233595) B2233595
theorem B4081103 : Blo 1176405 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B5957387 : Blo 1176405 5957387 := bstep (se 1 (by rfl) ⟨4468040, by rfl⟩ : syracuseStep 5957387 = 8936081) B8936081
theorem B3974939 : Blo 1176405 3974939 := bstep (se 1 (by rfl) ⟨2981204, by rfl⟩ : syracuseStep 3974939 = 5962409) B5962409
theorem B3581779 : Blo 1176405 3581779 := bstep (se 1 (by rfl) ⟨2686334, by rfl⟩ : syracuseStep 3581779 = 5372669) B5372669
theorem B45270899 : Blo 1176405 45270899 := bstep (se 1 (by rfl) ⟨33953174, by rfl⟩ : syracuseStep 45270899 = 67906349) B67906349
theorem B3975209 : Blo 1176405 3975209 := bstep (se 2 (by rfl) ⟨1490703, by rfl⟩ : syracuseStep 3975209 = 2981407) B2981407
theorem B2648303 : Blo 1176405 2648303 := bstep (se 1 (by rfl) ⟨1986227, by rfl⟩ : syracuseStep 2648303 = 3972455) B3972455
theorem B2648339 : Blo 1176405 2648339 := bstep (se 1 (by rfl) ⟨1986254, by rfl⟩ : syracuseStep 2648339 = 3972509) B3972509
theorem B15100505 : Blo 1176405 15100505 := bstep (se 2 (by rfl) ⟨5662689, by rfl⟩ : syracuseStep 15100505 = 11325379) B11325379
theorem B2649023 : Blo 1176405 2649023 := bstep (se 1 (by rfl) ⟨1986767, by rfl⟩ : syracuseStep 2649023 = 3973535) B3973535
theorem B11308193 : Blo 1176405 11308193 := bstep (se 2 (by rfl) ⟨4240572, by rfl⟩ : syracuseStep 11308193 = 8481145) B8481145
theorem B10342073 : Blo 1176405 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B2978471 : Blo 1176405 2978471 := bstep (se 1 (by rfl) ⟨2233853, by rfl⟩ : syracuseStep 2978471 = 4467707) B4467707
theorem B2978795 : Blo 1176405 2978795 := bstep (se 1 (by rfl) ⟨2234096, by rfl⟩ : syracuseStep 2978795 = 4468193) B4468193
theorem B2684063 : Blo 1176405 2684063 := bstep (se 1 (by rfl) ⟨2013047, by rfl⟩ : syracuseStep 2684063 = 4026095) B4026095
theorem B1987753 : Blo 1176405 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B16987319 : Blo 1176405 16987319 := bstep (se 1 (by rfl) ⟨12740489, by rfl⟩ : syracuseStep 16987319 = 25480979) B25480979
theorem B2979119 : Blo 1176405 2979119 := bstep (se 1 (by rfl) ⟨2234339, by rfl⟩ : syracuseStep 2979119 = 4468679) B4468679
theorem B11318615 : Blo 1176405 11318615 := bstep (se 1 (by rfl) ⟨8488961, by rfl⟩ : syracuseStep 11318615 = 16977923) B16977923
theorem B1767143 : Blo 1176405 1767143 := bstep (se 1 (by rfl) ⟨1325357, by rfl⟩ : syracuseStep 1767143 = 2650715) B2650715
theorem B3184409 : Blo 1176405 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B3971483 : Blo 1176405 3971483 := bstep (se 1 (by rfl) ⟨2978612, by rfl⟩ : syracuseStep 3971483 = 5957225) B5957225
theorem B5962247 : Blo 1176405 5962247 := bstep (se 1 (by rfl) ⟨4471685, by rfl⟩ : syracuseStep 5962247 = 8943371) B8943371
theorem B33930575 : Blo 1176405 33930575 := bstep (se 1 (by rfl) ⟨25447931, by rfl⟩ : syracuseStep 33930575 = 50895863) B50895863
theorem B51584687 : Blo 1176405 51584687 := bstep (se 1 (by rfl) ⟨38688515, by rfl⟩ : syracuseStep 51584687 = 77377031) B77377031
theorem B29033245 : Blo 1176405 29033245 := bstep (se 3 (by rfl) ⟨5443733, by rfl⟩ : syracuseStep 29033245 = 10887467) B10887467
theorem B7545743 : Blo 1176405 7545743 := bstep (se 1 (by rfl) ⟨5659307, by rfl⟩ : syracuseStep 7545743 = 11318615) B11318615
theorem B2720735 : Blo 1176405 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B2122939 : Blo 1176405 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B30180599 : Blo 1176405 30180599 := bstep (se 1 (by rfl) ⟨22635449, by rfl⟩ : syracuseStep 30180599 = 45270899) B45270899
theorem B2647655 : Blo 1176405 2647655 := bstep (se 1 (by rfl) ⟨1985741, by rfl⟩ : syracuseStep 2647655 = 3971483) B3971483
theorem B3974831 : Blo 1176405 3974831 := bstep (se 1 (by rfl) ⟨2981123, by rfl⟩ : syracuseStep 3974831 = 5962247) B5962247
theorem B7538795 : Blo 1176405 7538795 := bstep (se 1 (by rfl) ⟨5654096, by rfl⟩ : syracuseStep 7538795 = 11308193) B11308193
theorem B22620383 : Blo 1176405 22620383 := bstep (se 1 (by rfl) ⟨16965287, by rfl⟩ : syracuseStep 22620383 = 33930575) B33930575
theorem B1985647 : Blo 1176405 1985647 := bstep (se 1 (by rfl) ⟨1489235, by rfl⟩ : syracuseStep 1985647 = 2978471) B2978471
theorem B1985863 : Blo 1176405 1985863 := bstep (se 1 (by rfl) ⟨1489397, by rfl⟩ : syracuseStep 1985863 = 2978795) B2978795
theorem B11324879 : Blo 1176405 11324879 := bstep (se 1 (by rfl) ⟨8493659, by rfl⟩ : syracuseStep 11324879 = 16987319) B16987319
theorem B1986079 : Blo 1176405 1986079 := bstep (se 1 (by rfl) ⟨1489559, by rfl⟩ : syracuseStep 1986079 = 2979119) B2979119
theorem B2649959 : Blo 1176405 2649959 := bstep (se 1 (by rfl) ⟨1987469, by rfl⟩ : syracuseStep 2649959 = 3974939) B3974939
theorem B2650139 : Blo 1176405 2650139 := bstep (se 1 (by rfl) ⟨1987604, by rfl⟩ : syracuseStep 2650139 = 3975209) B3975209
theorem B1765535 : Blo 1176405 1765535 := bstep (se 1 (by rfl) ⟨1324151, by rfl⟩ : syracuseStep 1765535 = 2648303) B2648303
theorem B1765559 : Blo 1176405 1765559 := bstep (se 1 (by rfl) ⟨1324169, by rfl⟩ : syracuseStep 1765559 = 2648339) B2648339
theorem B2650337 : Blo 1176405 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B1766015 : Blo 1176405 1766015 := bstep (se 1 (by rfl) ⟨1324511, by rfl⟩ : syracuseStep 1766015 = 2649023) B2649023
theorem B6894715 : Blo 1176405 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B13407767 : Blo 1176405 13407767 := bstep (se 1 (by rfl) ⟨10055825, by rfl⟩ : syracuseStep 13407767 = 20111651) B20111651
theorem B7157501 : Blo 1176405 7157501 := bstep (se 3 (by rfl) ⟨1342031, by rfl⟩ : syracuseStep 7157501 = 2684063) B2684063
theorem B3970835 : Blo 1176405 3970835 := bstep (se 1 (by rfl) ⟨2978126, by rfl⟩ : syracuseStep 3970835 = 5956253) B5956253
theorem B1178095 : Blo 1176405 1178095 := bstep (se 1 (by rfl) ⟨883571, by rfl⟩ : syracuseStep 1178095 = 1767143) B1767143
theorem B3971591 : Blo 1176405 3971591 := bstep (se 1 (by rfl) ⟨2978693, by rfl⟩ : syracuseStep 3971591 = 5957387) B5957387
theorem B10067003 : Blo 1176405 10067003 := bstep (se 1 (by rfl) ⟨7550252, by rfl⟩ : syracuseStep 10067003 = 15100505) B15100505
theorem B4775705 : Blo 1176405 4775705 := bstep (se 2 (by rfl) ⟨1790889, by rfl⟩ : syracuseStep 4775705 = 3581779) B3581779
theorem B34389791 : Blo 1176405 34389791 := bstep (se 1 (by rfl) ⟨25792343, by rfl⟩ : syracuseStep 34389791 = 51584687) B51584687
theorem B5030495 : Blo 1176405 5030495 := bstep (se 1 (by rfl) ⟨3772871, by rfl⟩ : syracuseStep 5030495 = 7545743) B7545743
theorem B20120399 : Blo 1176405 20120399 := bstep (se 1 (by rfl) ⟨15090299, by rfl⟩ : syracuseStep 20120399 = 30180599) B30180599
theorem B11322341 : Blo 1176405 11322341 := bstep (se 4 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 11322341 = 2122939) B2122939
theorem B8938511 : Blo 1176405 8938511 := bstep (se 1 (by rfl) ⟨6703883, by rfl⟩ : syracuseStep 8938511 = 13407767) B13407767
theorem B2647223 : Blo 1176405 2647223 := bstep (se 1 (by rfl) ⟨1985417, by rfl⟩ : syracuseStep 2647223 = 3970835) B3970835
theorem B2647529 : Blo 1176405 2647529 := bstep (se 2 (by rfl) ⟨992823, by rfl⟩ : syracuseStep 2647529 = 1985647) B1985647
theorem B9192953 : Blo 1176405 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B2647727 : Blo 1176405 2647727 := bstep (se 1 (by rfl) ⟨1985795, by rfl⟩ : syracuseStep 2647727 = 3971591) B3971591
theorem B2647817 : Blo 1176405 2647817 := bstep (se 2 (by rfl) ⟨992931, by rfl⟩ : syracuseStep 2647817 = 1985863) B1985863
theorem B6711335 : Blo 1176405 6711335 := bstep (se 1 (by rfl) ⟨5033501, by rfl⟩ : syracuseStep 6711335 = 10067003) B10067003
theorem B2648105 : Blo 1176405 2648105 := bstep (se 2 (by rfl) ⟨993039, by rfl⟩ : syracuseStep 2648105 = 1986079) B1986079
theorem B1813823 : Blo 1176405 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B38710993 : Blo 1176405 38710993 := bstep (se 2 (by rfl) ⟨14516622, by rfl⟩ : syracuseStep 38710993 = 29033245) B29033245
theorem B1765103 : Blo 1176405 1765103 := bstep (se 1 (by rfl) ⟨1323827, by rfl⟩ : syracuseStep 1765103 = 2647655) B2647655
theorem B2649887 : Blo 1176405 2649887 := bstep (se 1 (by rfl) ⟨1987415, by rfl⟩ : syracuseStep 2649887 = 3974831) B3974831
theorem B4771667 : Blo 1176405 4771667 := bstep (se 1 (by rfl) ⟨3578750, by rfl⟩ : syracuseStep 4771667 = 7157501) B7157501
theorem B5025863 : Blo 1176405 5025863 := bstep (se 1 (by rfl) ⟨3769397, by rfl⟩ : syracuseStep 5025863 = 7538795) B7538795
theorem B7549919 : Blo 1176405 7549919 := bstep (se 1 (by rfl) ⟨5662439, by rfl⟩ : syracuseStep 7549919 = 11324879) B11324879
theorem B3183803 : Blo 1176405 3183803 := bstep (se 1 (by rfl) ⟨2387852, by rfl⟩ : syracuseStep 3183803 = 4775705) B4775705
theorem B22926527 : Blo 1176405 22926527 := bstep (se 1 (by rfl) ⟨17194895, by rfl⟩ : syracuseStep 22926527 = 34389791) B34389791
theorem B1766639 : Blo 1176405 1766639 := bstep (se 1 (by rfl) ⟨1324979, by rfl⟩ : syracuseStep 1766639 = 2649959) B2649959
theorem B1766759 : Blo 1176405 1766759 := bstep (se 1 (by rfl) ⟨1325069, by rfl⟩ : syracuseStep 1766759 = 2650139) B2650139
theorem B1177023 : Blo 1176405 1177023 := bstep (se 1 (by rfl) ⟨882767, by rfl⟩ : syracuseStep 1177023 = 1765535) B1765535
theorem B1177039 : Blo 1176405 1177039 := bstep (se 1 (by rfl) ⟨882779, by rfl⟩ : syracuseStep 1177039 = 1765559) B1765559
theorem B1766891 : Blo 1176405 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B1177343 : Blo 1176405 1177343 := bstep (se 1 (by rfl) ⟨883007, by rfl⟩ : syracuseStep 1177343 = 1766015) B1766015
theorem B15080255 : Blo 1176405 15080255 := bstep (se 1 (by rfl) ⟨11310191, by rfl⟩ : syracuseStep 15080255 = 22620383) B22620383
theorem B3350575 : Blo 1176405 3350575 := bstep (se 1 (by rfl) ⟨2512931, by rfl⟩ : syracuseStep 3350575 = 5025863) B5025863
theorem B2122535 : Blo 1176405 2122535 := bstep (se 1 (by rfl) ⟨1591901, by rfl⟩ : syracuseStep 2122535 = 3183803) B3183803
theorem B6128635 : Blo 1176405 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B4474223 : Blo 1176405 4474223 := bstep (se 1 (by rfl) ⟨3355667, by rfl⟩ : syracuseStep 4474223 = 6711335) B6711335
theorem B10053503 : Blo 1176405 10053503 := bstep (se 1 (by rfl) ⟨7540127, by rfl⟩ : syracuseStep 10053503 = 15080255) B15080255
theorem B12724445 : Blo 1176405 12724445 := bstep (se 3 (by rfl) ⟨2385833, by rfl⟩ : syracuseStep 12724445 = 4771667) B4771667
theorem B3353663 : Blo 1176405 3353663 := bstep (se 1 (by rfl) ⟨2515247, by rfl⟩ : syracuseStep 3353663 = 5030495) B5030495
theorem B13413599 : Blo 1176405 13413599 := bstep (se 1 (by rfl) ⟨10060199, by rfl⟩ : syracuseStep 13413599 = 20120399) B20120399
theorem B5033279 : Blo 1176405 5033279 := bstep (se 1 (by rfl) ⟨3774959, by rfl⟩ : syracuseStep 5033279 = 7549919) B7549919
theorem B7548227 : Blo 1176405 7548227 := bstep (se 1 (by rfl) ⟨5661170, by rfl⟩ : syracuseStep 7548227 = 11322341) B11322341
theorem B5959007 : Blo 1176405 5959007 := bstep (se 1 (by rfl) ⟨4469255, by rfl⟩ : syracuseStep 5959007 = 8938511) B8938511
theorem B1764815 : Blo 1176405 1764815 := bstep (se 1 (by rfl) ⟨1323611, by rfl⟩ : syracuseStep 1764815 = 2647223) B2647223
theorem B1765019 : Blo 1176405 1765019 := bstep (se 1 (by rfl) ⟨1323764, by rfl⟩ : syracuseStep 1765019 = 2647529) B2647529
theorem B1765151 : Blo 1176405 1765151 := bstep (se 1 (by rfl) ⟨1323863, by rfl⟩ : syracuseStep 1765151 = 2647727) B2647727
theorem B1765211 : Blo 1176405 1765211 := bstep (se 1 (by rfl) ⟨1323908, by rfl⟩ : syracuseStep 1765211 = 2647817) B2647817
theorem B1765403 : Blo 1176405 1765403 := bstep (se 1 (by rfl) ⟨1324052, by rfl⟩ : syracuseStep 1765403 = 2648105) B2648105
theorem B1209215 : Blo 1176405 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B51614657 : Blo 1176405 51614657 := bstep (se 2 (by rfl) ⟨19355496, by rfl⟩ : syracuseStep 51614657 = 38710993) B38710993
theorem B1176735 : Blo 1176405 1176735 := bstep (se 1 (by rfl) ⟨882551, by rfl⟩ : syracuseStep 1176735 = 1765103) B1765103
theorem B1766591 : Blo 1176405 1766591 := bstep (se 1 (by rfl) ⟨1324943, by rfl⟩ : syracuseStep 1766591 = 2649887) B2649887
theorem B15284351 : Blo 1176405 15284351 := bstep (se 1 (by rfl) ⟨11463263, by rfl⟩ : syracuseStep 15284351 = 22926527) B22926527
theorem B1177759 : Blo 1176405 1177759 := bstep (se 1 (by rfl) ⟨883319, by rfl⟩ : syracuseStep 1177759 = 1766639) B1766639
theorem B1177839 : Blo 1176405 1177839 := bstep (se 1 (by rfl) ⟨883379, by rfl⟩ : syracuseStep 1177839 = 1766759) B1766759
theorem B1177927 : Blo 1176405 1177927 := bstep (se 1 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 1177927 = 1766891) B1766891
theorem B2982815 : Blo 1176405 2982815 := bstep (se 1 (by rfl) ⟨2237111, by rfl⟩ : syracuseStep 2982815 = 4474223) B4474223
theorem B6702335 : Blo 1176405 6702335 := bstep (se 1 (by rfl) ⟨5026751, by rfl⟩ : syracuseStep 6702335 = 10053503) B10053503
theorem B5032151 : Blo 1176405 5032151 := bstep (se 1 (by rfl) ⟨3774113, by rfl⟩ : syracuseStep 5032151 = 7548227) B7548227
theorem B4467433 : Blo 1176405 4467433 := bstep (se 2 (by rfl) ⟨1675287, by rfl⟩ : syracuseStep 4467433 = 3350575) B3350575
theorem B34409771 : Blo 1176405 34409771 := bstep (se 1 (by rfl) ⟨25807328, by rfl⟩ : syracuseStep 34409771 = 51614657) B51614657
theorem B8171513 : Blo 1176405 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B8482963 : Blo 1176405 8482963 := bstep (se 1 (by rfl) ⟨6362222, by rfl⟩ : syracuseStep 8482963 = 12724445) B12724445
theorem B8942399 : Blo 1176405 8942399 := bstep (se 1 (by rfl) ⟨6706799, by rfl⟩ : syracuseStep 8942399 = 13413599) B13413599
theorem B3355519 : Blo 1176405 3355519 := bstep (se 1 (by rfl) ⟨2516639, by rfl⟩ : syracuseStep 3355519 = 5033279) B5033279
theorem B1176543 : Blo 1176405 1176543 := bstep (se 1 (by rfl) ⟨882407, by rfl⟩ : syracuseStep 1176543 = 1764815) B1764815
theorem B3224573 : Blo 1176405 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B1176679 : Blo 1176405 1176679 := bstep (se 1 (by rfl) ⟨882509, by rfl⟩ : syracuseStep 1176679 = 1765019) B1765019
theorem B1176767 : Blo 1176405 1176767 := bstep (se 1 (by rfl) ⟨882575, by rfl⟩ : syracuseStep 1176767 = 1765151) B1765151
theorem B1176807 : Blo 1176405 1176807 := bstep (se 1 (by rfl) ⟨882605, by rfl⟩ : syracuseStep 1176807 = 1765211) B1765211
theorem B1176935 : Blo 1176405 1176935 := bstep (se 1 (by rfl) ⟨882701, by rfl⟩ : syracuseStep 1176935 = 1765403) B1765403
theorem B1177727 : Blo 1176405 1177727 := bstep (se 1 (by rfl) ⟨883295, by rfl⟩ : syracuseStep 1177727 = 1766591) B1766591
theorem B10189567 : Blo 1176405 10189567 := bstep (se 1 (by rfl) ⟨7642175, by rfl⟩ : syracuseStep 10189567 = 15284351) B15284351
theorem B2235775 : Blo 1176405 2235775 := bstep (se 1 (by rfl) ⟨1676831, by rfl⟩ : syracuseStep 2235775 = 3353663) B3353663
theorem B5660093 : Blo 1176405 5660093 := bstep (se 3 (by rfl) ⟨1061267, by rfl⟩ : syracuseStep 5660093 = 2122535) B2122535
theorem B3972671 : Blo 1176405 3972671 := bstep (se 1 (by rfl) ⟨2979503, by rfl⟩ : syracuseStep 3972671 = 5959007) B5959007
theorem B5956577 : Blo 1176405 5956577 := bstep (se 2 (by rfl) ⟨2233716, by rfl⟩ : syracuseStep 5956577 = 4467433) B4467433
theorem B4474025 : Blo 1176405 4474025 := bstep (se 2 (by rfl) ⟨1677759, by rfl⟩ : syracuseStep 4474025 = 3355519) B3355519
theorem B22939847 : Blo 1176405 22939847 := bstep (se 1 (by rfl) ⟨17204885, by rfl⟩ : syracuseStep 22939847 = 34409771) B34409771
theorem B2648447 : Blo 1176405 2648447 := bstep (se 1 (by rfl) ⟨1986335, by rfl⟩ : syracuseStep 2648447 = 3972671) B3972671
theorem B2149715 : Blo 1176405 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B4468223 : Blo 1176405 4468223 := bstep (se 1 (by rfl) ⟨3351167, by rfl⟩ : syracuseStep 4468223 = 6702335) B6702335
theorem B13586089 : Blo 1176405 13586089 := bstep (se 2 (by rfl) ⟨5094783, by rfl⟩ : syracuseStep 13586089 = 10189567) B10189567
theorem B3354767 : Blo 1176405 3354767 := bstep (se 1 (by rfl) ⟨2516075, by rfl⟩ : syracuseStep 3354767 = 5032151) B5032151
theorem B3773395 : Blo 1176405 3773395 := bstep (se 1 (by rfl) ⟨2830046, by rfl⟩ : syracuseStep 3773395 = 5660093) B5660093
theorem B11310617 : Blo 1176405 11310617 := bstep (se 2 (by rfl) ⟨4241481, by rfl⟩ : syracuseStep 11310617 = 8482963) B8482963
theorem B5961599 : Blo 1176405 5961599 := bstep (se 1 (by rfl) ⟨4471199, by rfl⟩ : syracuseStep 5961599 = 8942399) B8942399
theorem B1988543 : Blo 1176405 1988543 := bstep (se 1 (by rfl) ⟨1491407, by rfl⟩ : syracuseStep 1988543 = 2982815) B2982815
theorem B2981033 : Blo 1176405 2981033 := bstep (se 2 (by rfl) ⟨1117887, by rfl⟩ : syracuseStep 2981033 = 2235775) B2235775
theorem B5447675 : Blo 1176405 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B2236511 : Blo 1176405 2236511 := bstep (se 1 (by rfl) ⟨1677383, by rfl⟩ : syracuseStep 2236511 = 3354767) B3354767
theorem B2982683 : Blo 1176405 2982683 := bstep (se 1 (by rfl) ⟨2237012, by rfl⟩ : syracuseStep 2982683 = 4474025) B4474025
theorem B3974399 : Blo 1176405 3974399 := bstep (se 1 (by rfl) ⟨2980799, by rfl⟩ : syracuseStep 3974399 = 5961599) B5961599
theorem B18114785 : Blo 1176405 18114785 := bstep (se 2 (by rfl) ⟨6793044, by rfl⟩ : syracuseStep 18114785 = 13586089) B13586089
theorem B14527133 : Blo 1176405 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B7540411 : Blo 1176405 7540411 := bstep (se 1 (by rfl) ⟨5655308, by rfl⟩ : syracuseStep 7540411 = 11310617) B11310617
theorem B1765631 : Blo 1176405 1765631 := bstep (se 1 (by rfl) ⟨1324223, by rfl⟩ : syracuseStep 1765631 = 2648447) B2648447
theorem B1987355 : Blo 1176405 1987355 := bstep (se 1 (by rfl) ⟨1490516, by rfl⟩ : syracuseStep 1987355 = 2981033) B2981033
theorem B2978815 : Blo 1176405 2978815 := bstep (se 1 (by rfl) ⟨2234111, by rfl⟩ : syracuseStep 2978815 = 4468223) B4468223
theorem B20124773 : Blo 1176405 20124773 := bstep (se 4 (by rfl) ⟨1886697, by rfl⟩ : syracuseStep 20124773 = 3773395) B3773395
theorem B3971051 : Blo 1176405 3971051 := bstep (se 1 (by rfl) ⟨2978288, by rfl⟩ : syracuseStep 3971051 = 5956577) B5956577
theorem B1325695 : Blo 1176405 1325695 := bstep (se 1 (by rfl) ⟨994271, by rfl⟩ : syracuseStep 1325695 = 1988543) B1988543
theorem B15293231 : Blo 1176405 15293231 := bstep (se 1 (by rfl) ⟨11469923, by rfl⟩ : syracuseStep 15293231 = 22939847) B22939847
theorem B1433143 : Blo 1176405 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B5964029 : Blo 1176405 5964029 := bstep (se 3 (by rfl) ⟨1118255, by rfl⟩ : syracuseStep 5964029 = 2236511) B2236511
theorem B7643429 : Blo 1176405 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B2647367 : Blo 1176405 2647367 := bstep (se 1 (by rfl) ⟨1985525, by rfl⟩ : syracuseStep 2647367 = 3971051) B3971051
theorem B12076523 : Blo 1176405 12076523 := bstep (se 1 (by rfl) ⟨9057392, by rfl⟩ : syracuseStep 12076523 = 18114785) B18114785
theorem B9684755 : Blo 1176405 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B10053881 : Blo 1176405 10053881 := bstep (se 2 (by rfl) ⟨3770205, by rfl⟩ : syracuseStep 10053881 = 7540411) B7540411
theorem B2649599 : Blo 1176405 2649599 := bstep (se 1 (by rfl) ⟨1987199, by rfl⟩ : syracuseStep 2649599 = 3974399) B3974399
theorem B10195487 : Blo 1176405 10195487 := bstep (se 1 (by rfl) ⟨7646615, by rfl⟩ : syracuseStep 10195487 = 15293231) B15293231
theorem B1177087 : Blo 1176405 1177087 := bstep (se 1 (by rfl) ⟨882815, by rfl⟩ : syracuseStep 1177087 = 1765631) B1765631
theorem B1324903 : Blo 1176405 1324903 := bstep (se 1 (by rfl) ⟨993677, by rfl⟩ : syracuseStep 1324903 = 1987355) B1987355
theorem B1988455 : Blo 1176405 1988455 := bstep (se 1 (by rfl) ⟨1491341, by rfl⟩ : syracuseStep 1988455 = 2982683) B2982683
theorem B13416515 : Blo 1176405 13416515 := bstep (se 1 (by rfl) ⟨10062386, by rfl⟩ : syracuseStep 13416515 = 20124773) B20124773
theorem B1767593 : Blo 1176405 1767593 := bstep (se 2 (by rfl) ⟨662847, by rfl⟩ : syracuseStep 1767593 = 1325695) B1325695
theorem B3971753 : Blo 1176405 3971753 := bstep (se 2 (by rfl) ⟨1489407, by rfl⟩ : syracuseStep 3971753 = 2978815) B2978815
theorem B5095619 : Blo 1176405 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B6456503 : Blo 1176405 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B6702587 : Blo 1176405 6702587 := bstep (se 1 (by rfl) ⟨5026940, by rfl⟩ : syracuseStep 6702587 = 10053881) B10053881
theorem B2647835 : Blo 1176405 2647835 := bstep (se 1 (by rfl) ⟨1985876, by rfl⟩ : syracuseStep 2647835 = 3971753) B3971753
theorem B3976019 : Blo 1176405 3976019 := bstep (se 1 (by rfl) ⟨2982014, by rfl⟩ : syracuseStep 3976019 = 5964029) B5964029
theorem B1764911 : Blo 1176405 1764911 := bstep (se 1 (by rfl) ⟨1323683, by rfl⟩ : syracuseStep 1764911 = 2647367) B2647367
theorem B1766399 : Blo 1176405 1766399 := bstep (se 1 (by rfl) ⟨1324799, by rfl⟩ : syracuseStep 1766399 = 2649599) B2649599
theorem B1766537 : Blo 1176405 1766537 := bstep (se 2 (by rfl) ⟨662451, by rfl⟩ : syracuseStep 1766537 = 1324903) B1324903
theorem B2651273 : Blo 1176405 2651273 := bstep (se 2 (by rfl) ⟨994227, by rfl⟩ : syracuseStep 2651273 = 1988455) B1988455
theorem B6796991 : Blo 1176405 6796991 := bstep (se 1 (by rfl) ⟨5097743, by rfl⟩ : syracuseStep 6796991 = 10195487) B10195487
theorem B8051015 : Blo 1176405 8051015 := bstep (se 1 (by rfl) ⟨6038261, by rfl⟩ : syracuseStep 8051015 = 12076523) B12076523
theorem B8944343 : Blo 1176405 8944343 := bstep (se 1 (by rfl) ⟨6708257, by rfl⟩ : syracuseStep 8944343 = 13416515) B13416515
theorem B1178395 : Blo 1176405 1178395 := bstep (se 1 (by rfl) ⟨883796, by rfl⟩ : syracuseStep 1178395 = 1767593) B1767593
theorem B5367343 : Blo 1176405 5367343 := bstep (se 1 (by rfl) ⟨4025507, by rfl⟩ : syracuseStep 5367343 = 8051015) B8051015
theorem B4304335 : Blo 1176405 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B4468391 : Blo 1176405 4468391 := bstep (se 1 (by rfl) ⟨3351293, by rfl⟩ : syracuseStep 4468391 = 6702587) B6702587
theorem B1765223 : Blo 1176405 1765223 := bstep (se 1 (by rfl) ⟨1323917, by rfl⟩ : syracuseStep 1765223 = 2647835) B2647835
theorem B18125309 : Blo 1176405 18125309 := bstep (se 3 (by rfl) ⟨3398495, by rfl⟩ : syracuseStep 18125309 = 6796991) B6796991
theorem B2650679 : Blo 1176405 2650679 := bstep (se 1 (by rfl) ⟨1988009, by rfl⟩ : syracuseStep 2650679 = 3976019) B3976019
theorem B1176607 : Blo 1176405 1176607 := bstep (se 1 (by rfl) ⟨882455, by rfl⟩ : syracuseStep 1176607 = 1764911) B1764911
theorem B3397079 : Blo 1176405 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B1177599 : Blo 1176405 1177599 := bstep (se 1 (by rfl) ⟨883199, by rfl⟩ : syracuseStep 1177599 = 1766399) B1766399
theorem B1177691 : Blo 1176405 1177691 := bstep (se 1 (by rfl) ⟨883268, by rfl⟩ : syracuseStep 1177691 = 1766537) B1766537
theorem B1767515 : Blo 1176405 1767515 := bstep (se 1 (by rfl) ⟨1325636, by rfl⟩ : syracuseStep 1767515 = 2651273) B2651273
theorem B5962895 : Blo 1176405 5962895 := bstep (se 1 (by rfl) ⟨4472171, by rfl⟩ : syracuseStep 5962895 = 8944343) B8944343
theorem B12083539 : Blo 1176405 12083539 := bstep (se 1 (by rfl) ⟨9062654, by rfl⟩ : syracuseStep 12083539 = 18125309) B18125309
theorem B3975263 : Blo 1176405 3975263 := bstep (se 1 (by rfl) ⟨2981447, by rfl⟩ : syracuseStep 3975263 = 5962895) B5962895
theorem B2264719 : Blo 1176405 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B5739113 : Blo 1176405 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B7156457 : Blo 1176405 7156457 := bstep (se 2 (by rfl) ⟨2683671, by rfl⟩ : syracuseStep 7156457 = 5367343) B5367343
theorem B2978927 : Blo 1176405 2978927 := bstep (se 1 (by rfl) ⟨2234195, by rfl⟩ : syracuseStep 2978927 = 4468391) B4468391
theorem B1176815 : Blo 1176405 1176815 := bstep (se 1 (by rfl) ⟨882611, by rfl⟩ : syracuseStep 1176815 = 1765223) B1765223
theorem B1767119 : Blo 1176405 1767119 := bstep (se 1 (by rfl) ⟨1325339, by rfl⟩ : syracuseStep 1767119 = 2650679) B2650679
theorem B1178343 : Blo 1176405 1178343 := bstep (se 1 (by rfl) ⟨883757, by rfl⟩ : syracuseStep 1178343 = 1767515) B1767515
theorem B3826075 : Blo 1176405 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B4770971 : Blo 1176405 4770971 := bstep (se 1 (by rfl) ⟨3578228, by rfl⟩ : syracuseStep 4770971 = 7156457) B7156457
theorem B1985951 : Blo 1176405 1985951 := bstep (se 1 (by rfl) ⟨1489463, by rfl⟩ : syracuseStep 1985951 = 2978927) B2978927
theorem B2650175 : Blo 1176405 2650175 := bstep (se 1 (by rfl) ⟨1987631, by rfl⟩ : syracuseStep 2650175 = 3975263) B3975263
theorem B3019625 : Blo 1176405 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B16111385 : Blo 1176405 16111385 := bstep (se 2 (by rfl) ⟨6041769, by rfl⟩ : syracuseStep 16111385 = 12083539) B12083539
theorem B1178079 : Blo 1176405 1178079 := bstep (se 1 (by rfl) ⟨883559, by rfl⟩ : syracuseStep 1178079 = 1767119) B1767119
theorem B10740923 : Blo 1176405 10740923 := bstep (se 1 (by rfl) ⟨8055692, by rfl⟩ : syracuseStep 10740923 = 16111385) B16111385
theorem B3180647 : Blo 1176405 3180647 := bstep (se 1 (by rfl) ⟨2385485, by rfl⟩ : syracuseStep 3180647 = 4770971) B4770971
theorem B1323967 : Blo 1176405 1323967 := bstep (se 1 (by rfl) ⟨992975, by rfl⟩ : syracuseStep 1323967 = 1985951) B1985951
theorem B1766783 : Blo 1176405 1766783 := bstep (se 1 (by rfl) ⟨1325087, by rfl⟩ : syracuseStep 1766783 = 2650175) B2650175
theorem B5101433 : Blo 1176405 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B2013083 : Blo 1176405 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B7160615 : Blo 1176405 7160615 := bstep (se 1 (by rfl) ⟨5370461, by rfl⟩ : syracuseStep 7160615 = 10740923) B10740923
theorem B3400955 : Blo 1176405 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B1765289 : Blo 1176405 1765289 := bstep (se 2 (by rfl) ⟨661983, by rfl⟩ : syracuseStep 1765289 = 1323967) B1323967
theorem B1177855 : Blo 1176405 1177855 := bstep (se 1 (by rfl) ⟨883391, by rfl⟩ : syracuseStep 1177855 = 1766783) B1766783
theorem B1342055 : Blo 1176405 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B2120431 : Blo 1176405 2120431 := bstep (se 1 (by rfl) ⟨1590323, by rfl⟩ : syracuseStep 2120431 = 3180647) B3180647
theorem B2827241 : Blo 1176405 2827241 := bstep (se 2 (by rfl) ⟨1060215, by rfl⟩ : syracuseStep 2827241 = 2120431) B2120431
theorem B1176859 : Blo 1176405 1176859 := bstep (se 1 (by rfl) ⟨882644, by rfl⟩ : syracuseStep 1176859 = 1765289) B1765289
theorem B4773743 : Blo 1176405 4773743 := bstep (se 1 (by rfl) ⟨3580307, by rfl⟩ : syracuseStep 4773743 = 7160615) B7160615
theorem B2267303 : Blo 1176405 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B3578813 : Blo 1176405 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B1884827 : Blo 1176405 1884827 := bstep (se 1 (by rfl) ⟨1413620, by rfl⟩ : syracuseStep 1884827 = 2827241) B2827241
theorem B24184565 : Blo 1176405 24184565 := bstep (se 5 (by rfl) ⟨1133651, by rfl⟩ : syracuseStep 24184565 = 2267303) B2267303
theorem B2385875 : Blo 1176405 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B3182495 : Blo 1176405 3182495 := bstep (se 1 (by rfl) ⟨2386871, by rfl⟩ : syracuseStep 3182495 = 4773743) B4773743
theorem B16123043 : Blo 1176405 16123043 := bstep (se 1 (by rfl) ⟨12092282, by rfl⟩ : syracuseStep 16123043 = 24184565) B24184565
theorem B5026205 : Blo 1176405 5026205 := bstep (se 3 (by rfl) ⟨942413, by rfl⟩ : syracuseStep 5026205 = 1884827) B1884827
theorem B6362333 : Blo 1176405 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B33946613 : Blo 1176405 33946613 := bstep (se 5 (by rfl) ⟨1591247, by rfl⟩ : syracuseStep 33946613 = 3182495) B3182495
theorem B3350803 : Blo 1176405 3350803 := bstep (se 1 (by rfl) ⟨2513102, by rfl⟩ : syracuseStep 3350803 = 5026205) B5026205
theorem B10748695 : Blo 1176405 10748695 := bstep (se 1 (by rfl) ⟨8061521, by rfl⟩ : syracuseStep 10748695 = 16123043) B16123043
theorem B22631075 : Blo 1176405 22631075 := bstep (se 1 (by rfl) ⟨16973306, by rfl⟩ : syracuseStep 22631075 = 33946613) B33946613
theorem B4241555 : Blo 1176405 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B2827703 : Blo 1176405 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B4467737 : Blo 1176405 4467737 := bstep (se 2 (by rfl) ⟨1675401, by rfl⟩ : syracuseStep 4467737 = 3350803) B3350803
theorem B14331593 : Blo 1176405 14331593 := bstep (se 2 (by rfl) ⟨5374347, by rfl⟩ : syracuseStep 14331593 = 10748695) B10748695
theorem B15087383 : Blo 1176405 15087383 := bstep (se 1 (by rfl) ⟨11315537, by rfl⟩ : syracuseStep 15087383 = 22631075) B22631075
theorem B1885135 : Blo 1176405 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B9554395 : Blo 1176405 9554395 := bstep (se 1 (by rfl) ⟨7165796, by rfl⟩ : syracuseStep 9554395 = 14331593) B14331593
theorem B2978491 : Blo 1176405 2978491 := bstep (se 1 (by rfl) ⟨2233868, by rfl⟩ : syracuseStep 2978491 = 4467737) B4467737
theorem B10058255 : Blo 1176405 10058255 := bstep (se 1 (by rfl) ⟨7543691, by rfl⟩ : syracuseStep 10058255 = 15087383) B15087383
theorem B12739193 : Blo 1176405 12739193 := bstep (se 2 (by rfl) ⟨4777197, by rfl⟩ : syracuseStep 12739193 = 9554395) B9554395
theorem B6705503 : Blo 1176405 6705503 := bstep (se 1 (by rfl) ⟨5029127, by rfl⟩ : syracuseStep 6705503 = 10058255) B10058255
theorem B3971321 : Blo 1176405 3971321 := bstep (se 2 (by rfl) ⟨1489245, by rfl⟩ : syracuseStep 3971321 = 2978491) B2978491
theorem B2513513 : Blo 1176405 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B2647547 : Blo 1176405 2647547 := bstep (se 1 (by rfl) ⟨1985660, by rfl⟩ : syracuseStep 2647547 = 3971321) B3971321
theorem B1675675 : Blo 1176405 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B4470335 : Blo 1176405 4470335 := bstep (se 1 (by rfl) ⟨3352751, by rfl⟩ : syracuseStep 4470335 = 6705503) B6705503
theorem B8492795 : Blo 1176405 8492795 := bstep (se 1 (by rfl) ⟨6369596, by rfl⟩ : syracuseStep 8492795 = 12739193) B12739193
theorem B5661863 : Blo 1176405 5661863 := bstep (se 1 (by rfl) ⟨4246397, by rfl⟩ : syracuseStep 5661863 = 8492795) B8492795
theorem B1765031 : Blo 1176405 1765031 := bstep (se 1 (by rfl) ⟨1323773, by rfl⟩ : syracuseStep 1765031 = 2647547) B2647547
theorem B2234233 : Blo 1176405 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B2980223 : Blo 1176405 2980223 := bstep (se 1 (by rfl) ⟨2235167, by rfl⟩ : syracuseStep 2980223 = 4470335) B4470335
theorem B1986815 : Blo 1176405 1986815 := bstep (se 1 (by rfl) ⟨1490111, by rfl⟩ : syracuseStep 1986815 = 2980223) B2980223
theorem B1176687 : Blo 1176405 1176687 := bstep (se 1 (by rfl) ⟨882515, by rfl⟩ : syracuseStep 1176687 = 1765031) B1765031
theorem B2978977 : Blo 1176405 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B3774575 : Blo 1176405 3774575 := bstep (se 1 (by rfl) ⟨2830931, by rfl⟩ : syracuseStep 3774575 = 5661863) B5661863
theorem B2516383 : Blo 1176405 2516383 := bstep (se 1 (by rfl) ⟨1887287, by rfl⟩ : syracuseStep 2516383 = 3774575) B3774575
theorem B1324543 : Blo 1176405 1324543 := bstep (se 1 (by rfl) ⟨993407, by rfl⟩ : syracuseStep 1324543 = 1986815) B1986815
theorem B3971969 : Blo 1176405 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B2647979 : Blo 1176405 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B3355177 : Blo 1176405 3355177 := bstep (se 2 (by rfl) ⟨1258191, by rfl⟩ : syracuseStep 3355177 = 2516383) B2516383
theorem B1766057 : Blo 1176405 1766057 := bstep (se 2 (by rfl) ⟨662271, by rfl⟩ : syracuseStep 1766057 = 1324543) B1324543
theorem B4473569 : Blo 1176405 4473569 := bstep (se 2 (by rfl) ⟨1677588, by rfl⟩ : syracuseStep 4473569 = 3355177) B3355177
theorem B1765319 : Blo 1176405 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B1177371 : Blo 1176405 1177371 := bstep (se 1 (by rfl) ⟨883028, by rfl⟩ : syracuseStep 1177371 = 1766057) B1766057
theorem B2982379 : Blo 1176405 2982379 := bstep (se 1 (by rfl) ⟨2236784, by rfl⟩ : syracuseStep 2982379 = 4473569) B4473569
theorem B1176879 : Blo 1176405 1176879 := bstep (se 1 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 1176879 = 1765319) B1765319
theorem B3976505 : Blo 1176405 3976505 := bstep (se 2 (by rfl) ⟨1491189, by rfl⟩ : syracuseStep 3976505 = 2982379) B2982379
theorem B2651003 : Blo 1176405 2651003 := bstep (se 1 (by rfl) ⟨1988252, by rfl⟩ : syracuseStep 2651003 = 3976505) B3976505
theorem B1767335 : Blo 1176405 1767335 := bstep (se 1 (by rfl) ⟨1325501, by rfl⟩ : syracuseStep 1767335 = 2651003) B2651003
theorem B1178223 : Blo 1176405 1178223 := bstep (se 1 (by rfl) ⟨883667, by rfl⟩ : syracuseStep 1178223 = 1767335) B1767335

theorem C0 (j : ℕ) (h1 : 294101 ≤ j) (h2 : j ≤ 294600) : Blo 1176405 (4 * j + 3) := by
  interval_cases j
  · exact B1176407
  · exact B1176411
  · exact B1176415
  · exact B1176419
  · exact B1176423
  · exact B1176427
  · exact B1176431
  · exact B1176435
  · exact B1176439
  · exact B1176443
  · exact B1176447
  · exact B1176451
  · exact B1176455
  · exact B1176459
  · exact B1176463
  · exact B1176467
  · exact B1176471
  · exact B1176475
  · exact B1176479
  · exact B1176483
  · exact B1176487
  · exact B1176491
  · exact B1176495
  · exact B1176499
  · exact B1176503
  · exact B1176507
  · exact B1176511
  · exact B1176515
  · exact B1176519
  · exact B1176523
  · exact B1176527
  · exact B1176531
  · exact B1176535
  · exact B1176539
  · exact B1176543
  · exact B1176547
  · exact B1176551
  · exact B1176555
  · exact B1176559
  · exact B1176563
  · exact B1176567
  · exact B1176571
  · exact B1176575
  · exact B1176579
  · exact B1176583
  · exact B1176587
  · exact B1176591
  · exact B1176595
  · exact B1176599
  · exact B1176603
  · exact B1176607
  · exact B1176611
  · exact B1176615
  · exact B1176619
  · exact B1176623
  · exact B1176627
  · exact B1176631
  · exact B1176635
  · exact B1176639
  · exact B1176643
  · exact B1176647
  · exact B1176651
  · exact B1176655
  · exact B1176659
  · exact B1176663
  · exact B1176667
  · exact B1176671
  · exact B1176675
  · exact B1176679
  · exact B1176683
  · exact B1176687
  · exact B1176691
  · exact B1176695
  · exact B1176699
  · exact B1176703
  · exact B1176707
  · exact B1176711
  · exact B1176715
  · exact B1176719
  · exact B1176723
  · exact B1176727
  · exact B1176731
  · exact B1176735
  · exact B1176739
  · exact B1176743
  · exact B1176747
  · exact B1176751
  · exact B1176755
  · exact B1176759
  · exact B1176763
  · exact B1176767
  · exact B1176771
  · exact B1176775
  · exact B1176779
  · exact B1176783
  · exact B1176787
  · exact B1176791
  · exact B1176795
  · exact B1176799
  · exact B1176803
  · exact B1176807
  · exact B1176811
  · exact B1176815
  · exact B1176819
  · exact B1176823
  · exact B1176827
  · exact B1176831
  · exact B1176835
  · exact B1176839
  · exact B1176843
  · exact B1176847
  · exact B1176851
  · exact B1176855
  · exact B1176859
  · exact B1176863
  · exact B1176867
  · exact B1176871
  · exact B1176875
  · exact B1176879
  · exact B1176883
  · exact B1176887
  · exact B1176891
  · exact B1176895
  · exact B1176899
  · exact B1176903
  · exact B1176907
  · exact B1176911
  · exact B1176915
  · exact B1176919
  · exact B1176923
  · exact B1176927
  · exact B1176931
  · exact B1176935
  · exact B1176939
  · exact B1176943
  · exact B1176947
  · exact B1176951
  · exact B1176955
  · exact B1176959
  · exact B1176963
  · exact B1176967
  · exact B1176971
  · exact B1176975
  · exact B1176979
  · exact B1176983
  · exact B1176987
  · exact B1176991
  · exact B1176995
  · exact B1176999
  · exact B1177003
  · exact B1177007
  · exact B1177011
  · exact B1177015
  · exact B1177019
  · exact B1177023
  · exact B1177027
  · exact B1177031
  · exact B1177035
  · exact B1177039
  · exact B1177043
  · exact B1177047
  · exact B1177051
  · exact B1177055
  · exact B1177059
  · exact B1177063
  · exact B1177067
  · exact B1177071
  · exact B1177075
  · exact B1177079
  · exact B1177083
  · exact B1177087
  · exact B1177091
  · exact B1177095
  · exact B1177099
  · exact B1177103
  · exact B1177107
  · exact B1177111
  · exact B1177115
  · exact B1177119
  · exact B1177123
  · exact B1177127
  · exact B1177131
  · exact B1177135
  · exact B1177139
  · exact B1177143
  · exact B1177147
  · exact B1177151
  · exact B1177155
  · exact B1177159
  · exact B1177163
  · exact B1177167
  · exact B1177171
  · exact B1177175
  · exact B1177179
  · exact B1177183
  · exact B1177187
  · exact B1177191
  · exact B1177195
  · exact B1177199
  · exact B1177203
  · exact B1177207
  · exact B1177211
  · exact B1177215
  · exact B1177219
  · exact B1177223
  · exact B1177227
  · exact B1177231
  · exact B1177235
  · exact B1177239
  · exact B1177243
  · exact B1177247
  · exact B1177251
  · exact B1177255
  · exact B1177259
  · exact B1177263
  · exact B1177267
  · exact B1177271
  · exact B1177275
  · exact B1177279
  · exact B1177283
  · exact B1177287
  · exact B1177291
  · exact B1177295
  · exact B1177299
  · exact B1177303
  · exact B1177307
  · exact B1177311
  · exact B1177315
  · exact B1177319
  · exact B1177323
  · exact B1177327
  · exact B1177331
  · exact B1177335
  · exact B1177339
  · exact B1177343
  · exact B1177347
  · exact B1177351
  · exact B1177355
  · exact B1177359
  · exact B1177363
  · exact B1177367
  · exact B1177371
  · exact B1177375
  · exact B1177379
  · exact B1177383
  · exact B1177387
  · exact B1177391
  · exact B1177395
  · exact B1177399
  · exact B1177403
  · exact B1177407
  · exact B1177411
  · exact B1177415
  · exact B1177419
  · exact B1177423
  · exact B1177427
  · exact B1177431
  · exact B1177435
  · exact B1177439
  · exact B1177443
  · exact B1177447
  · exact B1177451
  · exact B1177455
  · exact B1177459
  · exact B1177463
  · exact B1177467
  · exact B1177471
  · exact B1177475
  · exact B1177479
  · exact B1177483
  · exact B1177487
  · exact B1177491
  · exact B1177495
  · exact B1177499
  · exact B1177503
  · exact B1177507
  · exact B1177511
  · exact B1177515
  · exact B1177519
  · exact B1177523
  · exact B1177527
  · exact B1177531
  · exact B1177535
  · exact B1177539
  · exact B1177543
  · exact B1177547
  · exact B1177551
  · exact B1177555
  · exact B1177559
  · exact B1177563
  · exact B1177567
  · exact B1177571
  · exact B1177575
  · exact B1177579
  · exact B1177583
  · exact B1177587
  · exact B1177591
  · exact B1177595
  · exact B1177599
  · exact B1177603
  · exact B1177607
  · exact B1177611
  · exact B1177615
  · exact B1177619
  · exact B1177623
  · exact B1177627
  · exact B1177631
  · exact B1177635
  · exact B1177639
  · exact B1177643
  · exact B1177647
  · exact B1177651
  · exact B1177655
  · exact B1177659
  · exact B1177663
  · exact B1177667
  · exact B1177671
  · exact B1177675
  · exact B1177679
  · exact B1177683
  · exact B1177687
  · exact B1177691
  · exact B1177695
  · exact B1177699
  · exact B1177703
  · exact B1177707
  · exact B1177711
  · exact B1177715
  · exact B1177719
  · exact B1177723
  · exact B1177727
  · exact B1177731
  · exact B1177735
  · exact B1177739
  · exact B1177743
  · exact B1177747
  · exact B1177751
  · exact B1177755
  · exact B1177759
  · exact B1177763
  · exact B1177767
  · exact B1177771
  · exact B1177775
  · exact B1177779
  · exact B1177783
  · exact B1177787
  · exact B1177791
  · exact B1177795
  · exact B1177799
  · exact B1177803
  · exact B1177807
  · exact B1177811
  · exact B1177815
  · exact B1177819
  · exact B1177823
  · exact B1177827
  · exact B1177831
  · exact B1177835
  · exact B1177839
  · exact B1177843
  · exact B1177847
  · exact B1177851
  · exact B1177855
  · exact B1177859
  · exact B1177863
  · exact B1177867
  · exact B1177871
  · exact B1177875
  · exact B1177879
  · exact B1177883
  · exact B1177887
  · exact B1177891
  · exact B1177895
  · exact B1177899
  · exact B1177903
  · exact B1177907
  · exact B1177911
  · exact B1177915
  · exact B1177919
  · exact B1177923
  · exact B1177927
  · exact B1177931
  · exact B1177935
  · exact B1177939
  · exact B1177943
  · exact B1177947
  · exact B1177951
  · exact B1177955
  · exact B1177959
  · exact B1177963
  · exact B1177967
  · exact B1177971
  · exact B1177975
  · exact B1177979
  · exact B1177983
  · exact B1177987
  · exact B1177991
  · exact B1177995
  · exact B1177999
  · exact B1178003
  · exact B1178007
  · exact B1178011
  · exact B1178015
  · exact B1178019
  · exact B1178023
  · exact B1178027
  · exact B1178031
  · exact B1178035
  · exact B1178039
  · exact B1178043
  · exact B1178047
  · exact B1178051
  · exact B1178055
  · exact B1178059
  · exact B1178063
  · exact B1178067
  · exact B1178071
  · exact B1178075
  · exact B1178079
  · exact B1178083
  · exact B1178087
  · exact B1178091
  · exact B1178095
  · exact B1178099
  · exact B1178103
  · exact B1178107
  · exact B1178111
  · exact B1178115
  · exact B1178119
  · exact B1178123
  · exact B1178127
  · exact B1178131
  · exact B1178135
  · exact B1178139
  · exact B1178143
  · exact B1178147
  · exact B1178151
  · exact B1178155
  · exact B1178159
  · exact B1178163
  · exact B1178167
  · exact B1178171
  · exact B1178175
  · exact B1178179
  · exact B1178183
  · exact B1178187
  · exact B1178191
  · exact B1178195
  · exact B1178199
  · exact B1178203
  · exact B1178207
  · exact B1178211
  · exact B1178215
  · exact B1178219
  · exact B1178223
  · exact B1178227
  · exact B1178231
  · exact B1178235
  · exact B1178239
  · exact B1178243
  · exact B1178247
  · exact B1178251
  · exact B1178255
  · exact B1178259
  · exact B1178263
  · exact B1178267
  · exact B1178271
  · exact B1178275
  · exact B1178279
  · exact B1178283
  · exact B1178287
  · exact B1178291
  · exact B1178295
  · exact B1178299
  · exact B1178303
  · exact B1178307
  · exact B1178311
  · exact B1178315
  · exact B1178319
  · exact B1178323
  · exact B1178327
  · exact B1178331
  · exact B1178335
  · exact B1178339
  · exact B1178343
  · exact B1178347
  · exact B1178351
  · exact B1178355
  · exact B1178359
  · exact B1178363
  · exact B1178367
  · exact B1178371
  · exact B1178375
  · exact B1178379
  · exact B1178383
  · exact B1178387
  · exact B1178391
  · exact B1178395
  · exact B1178399
  · exact B1178403

theorem solution (m : ℕ) (hlo : 1176405 ≤ m) (hhi : m ≤ 1178405) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 294101 ≤ j := by omega
    have hj2 : j ≤ 294600 := by omega
    have hb : Blo 1176405 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
