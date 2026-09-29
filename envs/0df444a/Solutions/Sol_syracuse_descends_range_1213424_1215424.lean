-- Prove2me | solution 1 for syracuse_descends_range_1213424_1215424
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:52.266303+00:00
-- url     : https://prove2.me/submissions/fb753b01-44c1-4fe3-8f14-b2e737407649

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


theorem B1458205 : Blo 1213424 1458205 := bbase (se 3 (by rfl) ⟨273413, by rfl⟩ : syracuseStep 1458205 = 546827) (by norm_num)
theorem B3285029 : Blo 1213424 3285029 := bbase (se 4 (by rfl) ⟨307971, by rfl⟩ : syracuseStep 3285029 = 615943) (by norm_num)
theorem B3072077 : Blo 1213424 3072077 := bbase (se 3 (by rfl) ⟨576014, by rfl⟩ : syracuseStep 3072077 = 1152029) (by norm_num)
theorem B2048125 : Blo 1213424 2048125 := bbase (se 3 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 2048125 = 768047) (by norm_num)
theorem B4612261 : Blo 1213424 4612261 := bbase (se 4 (by rfl) ⟨432399, by rfl⟩ : syracuseStep 4612261 = 864799) (by norm_num)
theorem B2048213 : Blo 1213424 2048213 := bbase (se 7 (by rfl) ⟨24002, by rfl⟩ : syracuseStep 2048213 = 48005) (by norm_num)
theorem B3457237 : Blo 1213424 3457237 := bbase (se 7 (by rfl) ⟨40514, by rfl⟩ : syracuseStep 3457237 = 81029) (by norm_num)
theorem B3072269 : Blo 1213424 3072269 := bbase (se 3 (by rfl) ⟨576050, by rfl⟩ : syracuseStep 3072269 = 1152101) (by norm_num)
theorem B4096277 : Blo 1213424 4096277 := bbase (se 6 (by rfl) ⟨96006, by rfl⟩ : syracuseStep 4096277 = 192013) (by norm_num)
theorem B3891493 : Blo 1213424 3891493 := bbase (se 4 (by rfl) ⟨364827, by rfl⟩ : syracuseStep 3891493 = 729655) (by norm_num)
theorem B2916661 : Blo 1213424 2916661 := bbase (se 5 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 2916661 = 273437) (by norm_num)
theorem B2187581 : Blo 1213424 2187581 := bbase (se 3 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 2187581 = 820343) (by norm_num)
theorem B2048341 : Blo 1213424 2048341 := bbase (se 10 (by rfl) ⟨3000, by rfl⟩ : syracuseStep 2048341 = 6001) (by norm_num)
theorem B18702677 : Blo 1213424 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B1556833 : Blo 1213424 1556833 := bbase (se 2 (by rfl) ⟨583812, by rfl⟩ : syracuseStep 1556833 = 1167625) (by norm_num)
theorem B1728869 : Blo 1213424 1728869 := bbase (se 4 (by rfl) ⟨162081, by rfl⟩ : syracuseStep 1728869 = 324163) (by norm_num)
theorem B3457397 : Blo 1213424 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B6152597 : Blo 1213424 6152597 := bbase (se 6 (by rfl) ⟨144201, by rfl⟩ : syracuseStep 6152597 = 288403) (by norm_num)
theorem B2048429 : Blo 1213424 2048429 := bbase (se 3 (by rfl) ⟨384080, by rfl⟩ : syracuseStep 2048429 = 768161) (by norm_num)
theorem B4612565 : Blo 1213424 4612565 := bbase (se 7 (by rfl) ⟨54053, by rfl⟩ : syracuseStep 4612565 = 108107) (by norm_num)
theorem B2187749 : Blo 1213424 2187749 := bbase (se 4 (by rfl) ⟨205101, by rfl⟩ : syracuseStep 2187749 = 410203) (by norm_num)
theorem B2433557 : Blo 1213424 2433557 := bbase (se 6 (by rfl) ⟨57036, by rfl⟩ : syracuseStep 2433557 = 114073) (by norm_num)
theorem B2048557 : Blo 1213424 2048557 := bbase (se 3 (by rfl) ⟨384104, by rfl⟩ : syracuseStep 2048557 = 768209) (by norm_num)
theorem B7782965 : Blo 1213424 7782965 := bbase (se 5 (by rfl) ⟨364826, by rfl⟩ : syracuseStep 7782965 = 729653) (by norm_num)
theorem B3072613 : Blo 1213424 3072613 := bbase (se 4 (by rfl) ⟨288057, by rfl⟩ : syracuseStep 3072613 = 576115) (by norm_num)
theorem B3457637 : Blo 1213424 3457637 := bbase (se 4 (by rfl) ⟨324153, by rfl⟩ : syracuseStep 3457637 = 648307) (by norm_num)
theorem B3326581 : Blo 1213424 3326581 := bbase (se 5 (by rfl) ⟨155933, by rfl⟩ : syracuseStep 3326581 = 311867) (by norm_num)
theorem B2048645 : Blo 1213424 2048645 := bbase (se 4 (by rfl) ⟨192060, by rfl⟩ : syracuseStep 2048645 = 384121) (by norm_num)
theorem B1385105 : Blo 1213424 1385105 := bbase (se 2 (by rfl) ⟨519414, by rfl⟩ : syracuseStep 1385105 = 1038829) (by norm_num)
theorem B5186197 : Blo 1213424 5186197 := bbase (se 6 (by rfl) ⟨121551, by rfl⟩ : syracuseStep 5186197 = 243103) (by norm_num)
theorem B5833397 : Blo 1213424 5833397 := bbase (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) (by norm_num)
theorem B4096709 : Blo 1213424 4096709 := bbase (se 4 (by rfl) ⟨384066, by rfl⟩ : syracuseStep 4096709 = 768133) (by norm_num)
theorem B3072725 : Blo 1213424 3072725 := bbase (se 7 (by rfl) ⟨36008, by rfl⟩ : syracuseStep 3072725 = 72017) (by norm_num)
theorem B4924133 : Blo 1213424 4924133 := bbase (se 4 (by rfl) ⟨461637, by rfl⟩ : syracuseStep 4924133 = 923275) (by norm_num)
theorem B2048773 : Blo 1213424 2048773 := bbase (se 4 (by rfl) ⟨192072, by rfl⟩ : syracuseStep 2048773 = 384145) (by norm_num)
theorem B3457829 : Blo 1213424 3457829 := bbase (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) (by norm_num)
theorem B6144821 : Blo 1213424 6144821 := bbase (se 5 (by rfl) ⟨288038, by rfl⟩ : syracuseStep 6144821 = 576077) (by norm_num)
theorem B2048861 : Blo 1213424 2048861 := bbase (se 3 (by rfl) ⟨384161, by rfl⟩ : syracuseStep 2048861 = 768323) (by norm_num)
theorem B3072917 : Blo 1213424 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B11076533 : Blo 1213424 11076533 := bbase (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) (by norm_num)
theorem B2917333 : Blo 1213424 2917333 := bbase (se 7 (by rfl) ⟨34187, by rfl⟩ : syracuseStep 2917333 = 68375) (by norm_num)
theorem B2048989 : Blo 1213424 2048989 := bbase (se 3 (by rfl) ⟨384185, by rfl⟩ : syracuseStep 2048989 = 768371) (by norm_num)
theorem B1557505 : Blo 1213424 1557505 := bbase (se 2 (by rfl) ⟨584064, by rfl⟩ : syracuseStep 1557505 = 1168129) (by norm_num)
theorem B2049077 : Blo 1213424 2049077 := bbase (se 5 (by rfl) ⟨96050, by rfl⟩ : syracuseStep 2049077 = 192101) (by norm_num)
theorem B1459253 : Blo 1213424 1459253 := bbase (se 5 (by rfl) ⟨68402, by rfl⟩ : syracuseStep 1459253 = 136805) (by norm_num)
theorem B1729621 : Blo 1213424 1729621 := bbase (se 8 (by rfl) ⟨10134, by rfl⟩ : syracuseStep 1729621 = 20269) (by norm_num)
theorem B4097141 : Blo 1213424 4097141 := bbase (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) (by norm_num)
theorem B2049205 : Blo 1213424 2049205 := bbase (se 5 (by rfl) ⟨96056, by rfl⟩ : syracuseStep 2049205 = 192113) (by norm_num)
theorem B2917565 : Blo 1213424 2917565 := bbase (se 3 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 2917565 = 1094087) (by norm_num)
theorem B3073261 : Blo 1213424 3073261 := bbase (se 3 (by rfl) ⟨576236, by rfl⟩ : syracuseStep 3073261 = 1152473) (by norm_num)
theorem B2917613 : Blo 1213424 2917613 := bbase (se 3 (by rfl) ⟨547052, by rfl⟩ : syracuseStep 2917613 = 1094105) (by norm_num)
theorem B2049293 : Blo 1213424 2049293 := bbase (se 3 (by rfl) ⟨384242, by rfl⟩ : syracuseStep 2049293 = 768485) (by norm_num)
theorem B3073373 : Blo 1213424 3073373 := bbase (se 3 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 3073373 = 1152515) (by norm_num)
theorem B1385821 : Blo 1213424 1385821 := bbase (se 3 (by rfl) ⟨259841, by rfl⟩ : syracuseStep 1385821 = 519683) (by norm_num)
theorem B1459561 : Blo 1213424 1459561 := bbase (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) (by norm_num)
theorem B7775605 : Blo 1213424 7775605 := bbase (se 5 (by rfl) ⟨364481, by rfl⟩ : syracuseStep 7775605 = 728963) (by norm_num)
theorem B2049421 : Blo 1213424 2049421 := bbase (se 3 (by rfl) ⟨384266, by rfl⟩ : syracuseStep 2049421 = 768533) (by norm_num)
theorem B6235541 : Blo 1213424 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B2770373 : Blo 1213424 2770373 := bbase (se 4 (by rfl) ⟨259722, by rfl⟩ : syracuseStep 2770373 = 519445) (by norm_num)
theorem B2049509 : Blo 1213424 2049509 := bbase (se 4 (by rfl) ⟨192141, by rfl⟩ : syracuseStep 2049509 = 384283) (by norm_num)
theorem B1295849 : Blo 1213424 1295849 := bbase (se 2 (by rfl) ⟨485943, by rfl⟩ : syracuseStep 1295849 = 971887) (by norm_num)
theorem B1820141 : Blo 1213424 1820141 := bbase (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) (by norm_num)
theorem B1230329 : Blo 1213424 1230329 := bbase (se 2 (by rfl) ⟨461373, by rfl⟩ : syracuseStep 1230329 = 922747) (by norm_num)
theorem B1820165 : Blo 1213424 1820165 := bbase (se 4 (by rfl) ⟨170640, by rfl⟩ : syracuseStep 1820165 = 341281) (by norm_num)
theorem B1459729 : Blo 1213424 1459729 := bbase (se 2 (by rfl) ⟨547398, by rfl⟩ : syracuseStep 1459729 = 1094797) (by norm_num)
theorem B1820189 : Blo 1213424 1820189 := bbase (se 3 (by rfl) ⟨341285, by rfl⟩ : syracuseStep 1820189 = 682571) (by norm_num)
theorem B3073565 : Blo 1213424 3073565 := bbase (se 3 (by rfl) ⟨576293, by rfl⟩ : syracuseStep 3073565 = 1152587) (by norm_num)
theorem B4097573 : Blo 1213424 4097573 := bbase (se 4 (by rfl) ⟨384147, by rfl⟩ : syracuseStep 4097573 = 768295) (by norm_num)
theorem B1820213 : Blo 1213424 1820213 := bbase (se 5 (by rfl) ⟨85322, by rfl⟩ : syracuseStep 1820213 = 170645) (by norm_num)
theorem B1820237 : Blo 1213424 1820237 := bbase (se 3 (by rfl) ⟨341294, by rfl⟩ : syracuseStep 1820237 = 682589) (by norm_num)
theorem B26240597 : Blo 1213424 26240597 := bbase (se 8 (by rfl) ⟨153753, by rfl⟩ : syracuseStep 26240597 = 307507) (by norm_num)
theorem B1820261 : Blo 1213424 1820261 := bbase (se 4 (by rfl) ⟨170649, by rfl⟩ : syracuseStep 1820261 = 341299) (by norm_num)
theorem B2336357 : Blo 1213424 2336357 := bbase (se 4 (by rfl) ⟨219033, by rfl⟩ : syracuseStep 2336357 = 438067) (by norm_num)
theorem B2049637 : Blo 1213424 2049637 := bbase (se 4 (by rfl) ⟨192153, by rfl⟩ : syracuseStep 2049637 = 384307) (by norm_num)
theorem B3892853 : Blo 1213424 3892853 := bbase (se 5 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 3892853 = 364955) (by norm_num)
theorem B1820285 : Blo 1213424 1820285 := bbase (se 3 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 1820285 = 682607) (by norm_num)
theorem B1820309 : Blo 1213424 1820309 := bbase (se 6 (by rfl) ⟨42663, by rfl⟩ : syracuseStep 1820309 = 85327) (by norm_num)
theorem B1296037 : Blo 1213424 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B1820333 : Blo 1213424 1820333 := bbase (se 3 (by rfl) ⟨341312, by rfl⟩ : syracuseStep 1820333 = 682625) (by norm_num)
theorem B2049725 : Blo 1213424 2049725 := bbase (se 3 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 2049725 = 768647) (by norm_num)
theorem B1820357 : Blo 1213424 1820357 := bbase (se 4 (by rfl) ⟨170658, by rfl⟩ : syracuseStep 1820357 = 341317) (by norm_num)
theorem B1459925 : Blo 1213424 1459925 := bbase (se 7 (by rfl) ⟨17108, by rfl⟩ : syracuseStep 1459925 = 34217) (by norm_num)
theorem B1820381 : Blo 1213424 1820381 := bbase (se 3 (by rfl) ⟨341321, by rfl⟩ : syracuseStep 1820381 = 682643) (by norm_num)
theorem B1820405 : Blo 1213424 1820405 := bbase (se 5 (by rfl) ⟨85331, by rfl⟩ : syracuseStep 1820405 = 170663) (by norm_num)
theorem B3892981 : Blo 1213424 3892981 := bbase (se 5 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 3892981 = 364967) (by norm_num)
theorem B3458821 : Blo 1213424 3458821 := bbase (se 4 (by rfl) ⟨324264, by rfl⟩ : syracuseStep 3458821 = 648529) (by norm_num)
theorem B1820429 : Blo 1213424 1820429 := bbase (se 3 (by rfl) ⟨341330, by rfl⟩ : syracuseStep 1820429 = 682661) (by norm_num)
theorem B1820453 : Blo 1213424 1820453 := bbase (se 4 (by rfl) ⟨170667, by rfl⟩ : syracuseStep 1820453 = 341335) (by norm_num)
theorem B5539637 : Blo 1213424 5539637 := bbase (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) (by norm_num)
theorem B1820477 : Blo 1213424 1820477 := bbase (se 3 (by rfl) ⟨341339, by rfl⟩ : syracuseStep 1820477 = 682679) (by norm_num)
theorem B2049853 : Blo 1213424 2049853 := bbase (se 3 (by rfl) ⟨384347, by rfl⟩ : syracuseStep 2049853 = 768695) (by norm_num)
theorem B1820501 : Blo 1213424 1820501 := bbase (se 9 (by rfl) ⟨5333, by rfl⟩ : syracuseStep 1820501 = 10667) (by norm_num)
theorem B1820525 : Blo 1213424 1820525 := bbase (se 3 (by rfl) ⟨341348, by rfl⟩ : syracuseStep 1820525 = 682697) (by norm_num)
theorem B1730413 : Blo 1213424 1730413 := bbase (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) (by norm_num)
theorem B3073909 : Blo 1213424 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B1820549 : Blo 1213424 1820549 := bbase (se 4 (by rfl) ⟨170676, by rfl⟩ : syracuseStep 1820549 = 341353) (by norm_num)
theorem B2049941 : Blo 1213424 2049941 := bbase (se 6 (by rfl) ⟨48045, by rfl⟩ : syracuseStep 2049941 = 96091) (by norm_num)
theorem B1820573 : Blo 1213424 1820573 := bbase (se 3 (by rfl) ⟨341357, by rfl⟩ : syracuseStep 1820573 = 682715) (by norm_num)
theorem B1820597 : Blo 1213424 1820597 := bbase (se 5 (by rfl) ⟨85340, by rfl⟩ : syracuseStep 1820597 = 170681) (by norm_num)
theorem B1820621 : Blo 1213424 1820621 := bbase (se 3 (by rfl) ⟨341366, by rfl⟩ : syracuseStep 1820621 = 682733) (by norm_num)
theorem B4098005 : Blo 1213424 4098005 := bbase (se 7 (by rfl) ⟨48023, by rfl⟩ : syracuseStep 4098005 = 96047) (by norm_num)
theorem B1820645 : Blo 1213424 1820645 := bbase (se 4 (by rfl) ⟨170685, by rfl⟩ : syracuseStep 1820645 = 341371) (by norm_num)
theorem B3074021 : Blo 1213424 3074021 := bbase (se 4 (by rfl) ⟨288189, by rfl⟩ : syracuseStep 3074021 = 576379) (by norm_num)
theorem B3893237 : Blo 1213424 3893237 := bbase (se 5 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 3893237 = 364991) (by norm_num)
theorem B1820669 : Blo 1213424 1820669 := bbase (se 3 (by rfl) ⟨341375, by rfl⟩ : syracuseStep 1820669 = 682751) (by norm_num)
theorem B1820693 : Blo 1213424 1820693 := bbase (se 6 (by rfl) ⟨42672, by rfl⟩ : syracuseStep 1820693 = 85345) (by norm_num)
theorem B2050069 : Blo 1213424 2050069 := bbase (se 6 (by rfl) ⟨48048, by rfl⟩ : syracuseStep 2050069 = 96097) (by norm_num)
theorem B1820717 : Blo 1213424 1820717 := bbase (se 3 (by rfl) ⟨341384, by rfl⟩ : syracuseStep 1820717 = 682769) (by norm_num)
theorem B1820741 : Blo 1213424 1820741 := bbase (se 4 (by rfl) ⟨170694, by rfl⟩ : syracuseStep 1820741 = 341389) (by norm_num)
theorem B6146117 : Blo 1213424 6146117 := bbase (se 4 (by rfl) ⟨576198, by rfl⟩ : syracuseStep 6146117 = 1152397) (by norm_num)
theorem B1820765 : Blo 1213424 1820765 := bbase (se 3 (by rfl) ⟨341393, by rfl⟩ : syracuseStep 1820765 = 682787) (by norm_num)
theorem B5187685 : Blo 1213424 5187685 := bbase (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) (by norm_num)
theorem B2050157 : Blo 1213424 2050157 := bbase (se 3 (by rfl) ⟨384404, by rfl⟩ : syracuseStep 2050157 = 768809) (by norm_num)
theorem B6228085 : Blo 1213424 6228085 := bbase (se 5 (by rfl) ⟨291941, by rfl⟩ : syracuseStep 6228085 = 583883) (by norm_num)
theorem B1820789 : Blo 1213424 1820789 := bbase (se 5 (by rfl) ⟨85349, by rfl⟩ : syracuseStep 1820789 = 170699) (by norm_num)
theorem B4376693 : Blo 1213424 4376693 := bbase (se 5 (by rfl) ⟨205157, by rfl⟩ : syracuseStep 4376693 = 410315) (by norm_num)
theorem B5187701 : Blo 1213424 5187701 := bbase (se 5 (by rfl) ⟨243173, by rfl⟩ : syracuseStep 5187701 = 486347) (by norm_num)
theorem B1820813 : Blo 1213424 1820813 := bbase (se 3 (by rfl) ⟨341402, by rfl⟩ : syracuseStep 1820813 = 682805) (by norm_num)
theorem B1820837 : Blo 1213424 1820837 := bbase (se 4 (by rfl) ⟨170703, by rfl⟩ : syracuseStep 1820837 = 341407) (by norm_num)
theorem B3074213 : Blo 1213424 3074213 := bbase (se 4 (by rfl) ⟨288207, by rfl⟩ : syracuseStep 3074213 = 576415) (by norm_num)
theorem B1820861 : Blo 1213424 1820861 := bbase (se 3 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 1820861 = 682823) (by norm_num)
theorem B1820885 : Blo 1213424 1820885 := bbase (se 7 (by rfl) ⟨21338, by rfl⟩ : syracuseStep 1820885 = 42677) (by norm_num)
theorem B2730221 : Blo 1213424 2730221 := bbase (se 3 (by rfl) ⟨511916, by rfl⟩ : syracuseStep 2730221 = 1023833) (by norm_num)
theorem B1820909 : Blo 1213424 1820909 := bbase (se 3 (by rfl) ⟨341420, by rfl⟩ : syracuseStep 1820909 = 682841) (by norm_num)
theorem B2050285 : Blo 1213424 2050285 := bbase (se 3 (by rfl) ⟨384428, by rfl⟩ : syracuseStep 2050285 = 768857) (by norm_num)
theorem B1943813 : Blo 1213424 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B1820933 : Blo 1213424 1820933 := bbase (se 4 (by rfl) ⟨170712, by rfl⟩ : syracuseStep 1820933 = 341425) (by norm_num)
theorem B1820957 : Blo 1213424 1820957 := bbase (se 3 (by rfl) ⟨341429, by rfl⟩ : syracuseStep 1820957 = 682859) (by norm_num)
theorem B2304301 : Blo 1213424 2304301 := bbase (se 3 (by rfl) ⟨432056, by rfl⟩ : syracuseStep 2304301 = 864113) (by norm_num)
theorem B2730293 : Blo 1213424 2730293 := bbase (se 5 (by rfl) ⟨127982, by rfl⟩ : syracuseStep 2730293 = 255965) (by norm_num)
theorem B1820981 : Blo 1213424 1820981 := bbase (se 5 (by rfl) ⟨85358, by rfl⟩ : syracuseStep 1820981 = 170717) (by norm_num)
theorem B2189629 : Blo 1213424 2189629 := bbase (se 3 (by rfl) ⟨410555, by rfl⟩ : syracuseStep 2189629 = 821111) (by norm_num)
theorem B2050373 : Blo 1213424 2050373 := bbase (se 4 (by rfl) ⟨192222, by rfl⟩ : syracuseStep 2050373 = 384445) (by norm_num)
theorem B1821005 : Blo 1213424 1821005 := bbase (se 3 (by rfl) ⟨341438, by rfl⟩ : syracuseStep 1821005 = 682877) (by norm_num)
theorem B1821029 : Blo 1213424 1821029 := bbase (se 4 (by rfl) ⟨170721, by rfl⟩ : syracuseStep 1821029 = 341443) (by norm_num)
theorem B2730365 : Blo 1213424 2730365 := bbase (se 3 (by rfl) ⟨511943, by rfl⟩ : syracuseStep 2730365 = 1023887) (by norm_num)
theorem B1821053 : Blo 1213424 1821053 := bbase (se 3 (by rfl) ⟨341447, by rfl⟩ : syracuseStep 1821053 = 682895) (by norm_num)
theorem B4098437 : Blo 1213424 4098437 := bbase (se 4 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 4098437 = 768457) (by norm_num)
theorem B1821077 : Blo 1213424 1821077 := bbase (se 6 (by rfl) ⟨42681, by rfl⟩ : syracuseStep 1821077 = 85363) (by norm_num)
theorem B1821101 : Blo 1213424 1821101 := bbase (se 3 (by rfl) ⟨341456, by rfl⟩ : syracuseStep 1821101 = 682913) (by norm_num)
theorem B2304445 : Blo 1213424 2304445 := bbase (se 3 (by rfl) ⟨432083, by rfl⟩ : syracuseStep 2304445 = 864167) (by norm_num)
theorem B2730437 : Blo 1213424 2730437 := bbase (se 4 (by rfl) ⟨255978, by rfl⟩ : syracuseStep 2730437 = 511957) (by norm_num)
theorem B1821125 : Blo 1213424 1821125 := bbase (se 4 (by rfl) ⟨170730, by rfl⟩ : syracuseStep 1821125 = 341461) (by norm_num)
theorem B2050501 : Blo 1213424 2050501 := bbase (se 4 (by rfl) ⟨192234, by rfl⟩ : syracuseStep 2050501 = 384469) (by norm_num)
theorem B9226709 : Blo 1213424 9226709 := bbase (se 7 (by rfl) ⟨108125, by rfl⟩ : syracuseStep 9226709 = 216251) (by norm_num)
theorem B1296857 : Blo 1213424 1296857 := bbase (se 2 (by rfl) ⟨486321, by rfl⟩ : syracuseStep 1296857 = 972643) (by norm_num)
theorem B1821149 : Blo 1213424 1821149 := bbase (se 3 (by rfl) ⟨341465, by rfl⟩ : syracuseStep 1821149 = 682931) (by norm_num)
theorem B1845749 : Blo 1213424 1845749 := bbase (se 5 (by rfl) ⟨86519, by rfl⟩ : syracuseStep 1845749 = 173039) (by norm_num)
theorem B1821173 : Blo 1213424 1821173 := bbase (se 5 (by rfl) ⟨85367, by rfl⟩ : syracuseStep 1821173 = 170735) (by norm_num)
theorem B3074557 : Blo 1213424 3074557 := bbase (se 3 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 3074557 = 1152959) (by norm_num)
theorem B2730509 : Blo 1213424 2730509 := bbase (se 3 (by rfl) ⟨511970, by rfl⟩ : syracuseStep 2730509 = 1023941) (by norm_num)
theorem B1821197 : Blo 1213424 1821197 := bbase (se 3 (by rfl) ⟨341474, by rfl⟩ : syracuseStep 1821197 = 682949) (by norm_num)
theorem B2189845 : Blo 1213424 2189845 := bbase (se 6 (by rfl) ⟨51324, by rfl⟩ : syracuseStep 2189845 = 102649) (by norm_num)
theorem B4614677 : Blo 1213424 4614677 := bbase (se 6 (by rfl) ⟨108156, by rfl⟩ : syracuseStep 4614677 = 216313) (by norm_num)
theorem B2050589 : Blo 1213424 2050589 := bbase (se 3 (by rfl) ⟨384485, by rfl⟩ : syracuseStep 2050589 = 768971) (by norm_num)
theorem B1944101 : Blo 1213424 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B1821221 : Blo 1213424 1821221 := bbase (se 4 (by rfl) ⟨170739, by rfl⟩ : syracuseStep 1821221 = 341479) (by norm_num)
theorem B6916661 : Blo 1213424 6916661 := bbase (se 5 (by rfl) ⟨324218, by rfl⟩ : syracuseStep 6916661 = 648437) (by norm_num)
theorem B1821245 : Blo 1213424 1821245 := bbase (se 3 (by rfl) ⟨341483, by rfl⟩ : syracuseStep 1821245 = 682967) (by norm_num)
theorem B2730581 : Blo 1213424 2730581 := bbase (se 8 (by rfl) ⟨15999, by rfl⟩ : syracuseStep 2730581 = 31999) (by norm_num)
theorem B1821269 : Blo 1213424 1821269 := bbase (se 8 (by rfl) ⟨10671, by rfl⟩ : syracuseStep 1821269 = 21343) (by norm_num)
theorem B2304605 : Blo 1213424 2304605 := bbase (se 3 (by rfl) ⟨432113, by rfl⟩ : syracuseStep 2304605 = 864227) (by norm_num)
theorem B2919005 : Blo 1213424 2919005 := bbase (se 3 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 2919005 = 1094627) (by norm_num)
theorem B1821293 : Blo 1213424 1821293 := bbase (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) (by norm_num)
theorem B3074669 : Blo 1213424 3074669 := bbase (se 3 (by rfl) ⟨576500, by rfl⟩ : syracuseStep 3074669 = 1153001) (by norm_num)
theorem B1821317 : Blo 1213424 1821317 := bbase (se 4 (by rfl) ⟨170748, by rfl⟩ : syracuseStep 1821317 = 341497) (by norm_num)
theorem B2730653 : Blo 1213424 2730653 := bbase (se 3 (by rfl) ⟨511997, by rfl⟩ : syracuseStep 2730653 = 1023995) (by norm_num)
theorem B1821341 : Blo 1213424 1821341 := bbase (se 3 (by rfl) ⟨341501, by rfl⟩ : syracuseStep 1821341 = 683003) (by norm_num)
theorem B2050717 : Blo 1213424 2050717 := bbase (se 3 (by rfl) ⟨384509, by rfl⟩ : syracuseStep 2050717 = 769019) (by norm_num)
theorem B1231529 : Blo 1213424 1231529 := bbase (se 2 (by rfl) ⟨461823, by rfl⟩ : syracuseStep 1231529 = 923647) (by norm_num)
theorem B1821365 : Blo 1213424 1821365 := bbase (se 5 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 1821365 = 170753) (by norm_num)
theorem B1821389 : Blo 1213424 1821389 := bbase (se 3 (by rfl) ⟨341510, by rfl⟩ : syracuseStep 1821389 = 683021) (by norm_num)
theorem B2730725 : Blo 1213424 2730725 := bbase (se 4 (by rfl) ⟨256005, by rfl⟩ : syracuseStep 2730725 = 512011) (by norm_num)
theorem B1821413 : Blo 1213424 1821413 := bbase (se 4 (by rfl) ⟨170757, by rfl⟩ : syracuseStep 1821413 = 341515) (by norm_num)
theorem B2304749 : Blo 1213424 2304749 := bbase (se 3 (by rfl) ⟨432140, by rfl⟩ : syracuseStep 2304749 = 864281) (by norm_num)
theorem B1641205 : Blo 1213424 1641205 := bbase (se 5 (by rfl) ⟨76931, by rfl⟩ : syracuseStep 1641205 = 153863) (by norm_num)
theorem B2050805 : Blo 1213424 2050805 := bbase (se 5 (by rfl) ⟨96131, by rfl⟩ : syracuseStep 2050805 = 192263) (by norm_num)
theorem B1821437 : Blo 1213424 1821437 := bbase (se 3 (by rfl) ⟨341519, by rfl⟩ : syracuseStep 1821437 = 683039) (by norm_num)
theorem B1821461 : Blo 1213424 1821461 := bbase (se 6 (by rfl) ⟨42690, by rfl⟩ : syracuseStep 1821461 = 85381) (by norm_num)
theorem B2919197 : Blo 1213424 2919197 := bbase (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) (by norm_num)
theorem B2730797 : Blo 1213424 2730797 := bbase (se 3 (by rfl) ⟨512024, by rfl⟩ : syracuseStep 2730797 = 1024049) (by norm_num)
theorem B1821485 : Blo 1213424 1821485 := bbase (se 3 (by rfl) ⟨341528, by rfl⟩ : syracuseStep 1821485 = 683057) (by norm_num)
theorem B3074861 : Blo 1213424 3074861 := bbase (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) (by norm_num)
theorem B4098869 : Blo 1213424 4098869 := bbase (se 5 (by rfl) ⟨192134, by rfl⟩ : syracuseStep 4098869 = 384269) (by norm_num)
theorem B1821509 : Blo 1213424 1821509 := bbase (se 4 (by rfl) ⟨170766, by rfl⟩ : syracuseStep 1821509 = 341533) (by norm_num)
theorem B3459925 : Blo 1213424 3459925 := bbase (se 9 (by rfl) ⟨10136, by rfl⟩ : syracuseStep 3459925 = 20273) (by norm_num)
theorem B1821533 : Blo 1213424 1821533 := bbase (se 3 (by rfl) ⟨341537, by rfl⟩ : syracuseStep 1821533 = 683075) (by norm_num)
theorem B2730869 : Blo 1213424 2730869 := bbase (se 5 (by rfl) ⟨128009, by rfl⟩ : syracuseStep 2730869 = 256019) (by norm_num)
theorem B9218933 : Blo 1213424 9218933 := bbase (se 5 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 9218933 = 864275) (by norm_num)
theorem B1821557 : Blo 1213424 1821557 := bbase (se 5 (by rfl) ⟨85385, by rfl⟩ : syracuseStep 1821557 = 170771) (by norm_num)
theorem B2050933 : Blo 1213424 2050933 := bbase (se 5 (by rfl) ⟨96137, by rfl⟩ : syracuseStep 2050933 = 192275) (by norm_num)
theorem B1821581 : Blo 1213424 1821581 := bbase (se 3 (by rfl) ⟨341546, by rfl⟩ : syracuseStep 1821581 = 683093) (by norm_num)
theorem B1297301 : Blo 1213424 1297301 := bbase (se 6 (by rfl) ⟨30405, by rfl⟩ : syracuseStep 1297301 = 60811) (by norm_num)
theorem B2771869 : Blo 1213424 2771869 := bbase (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) (by norm_num)
theorem B1821605 : Blo 1213424 1821605 := bbase (se 4 (by rfl) ⟨170775, by rfl⟩ : syracuseStep 1821605 = 341551) (by norm_num)
theorem B2730941 : Blo 1213424 2730941 := bbase (se 3 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 2730941 = 1024103) (by norm_num)
theorem B1821629 : Blo 1213424 1821629 := bbase (se 3 (by rfl) ⟨341555, by rfl⟩ : syracuseStep 1821629 = 683111) (by norm_num)
theorem B2051021 : Blo 1213424 2051021 := bbase (se 3 (by rfl) ⟨384566, by rfl⟩ : syracuseStep 2051021 = 769133) (by norm_num)
theorem B1821653 : Blo 1213424 1821653 := bbase (se 7 (by rfl) ⟨21347, by rfl⟩ : syracuseStep 1821653 = 42695) (by norm_num)
theorem B1821677 : Blo 1213424 1821677 := bbase (se 3 (by rfl) ⟨341564, by rfl⟩ : syracuseStep 1821677 = 683129) (by norm_num)
theorem B2731013 : Blo 1213424 2731013 := bbase (se 4 (by rfl) ⟨256032, by rfl⟩ : syracuseStep 2731013 = 512065) (by norm_num)
theorem B1821701 : Blo 1213424 1821701 := bbase (se 4 (by rfl) ⟨170784, by rfl⟩ : syracuseStep 1821701 = 341569) (by norm_num)
theorem B2305037 : Blo 1213424 2305037 := bbase (se 3 (by rfl) ⟨432194, by rfl⟩ : syracuseStep 2305037 = 864389) (by norm_num)
theorem B1821725 : Blo 1213424 1821725 := bbase (se 3 (by rfl) ⟨341573, by rfl⟩ : syracuseStep 1821725 = 683147) (by norm_num)
theorem B1821749 : Blo 1213424 1821749 := bbase (se 5 (by rfl) ⟨85394, by rfl⟩ : syracuseStep 1821749 = 170789) (by norm_num)
theorem B2370629 : Blo 1213424 2370629 := bbase (se 4 (by rfl) ⟨222246, by rfl⟩ : syracuseStep 2370629 = 444493) (by norm_num)
theorem B2731085 : Blo 1213424 2731085 := bbase (se 3 (by rfl) ⟨512078, by rfl⟩ : syracuseStep 2731085 = 1024157) (by norm_num)
theorem B1821773 : Blo 1213424 1821773 := bbase (se 3 (by rfl) ⟨341582, by rfl⟩ : syracuseStep 1821773 = 683165) (by norm_num)
theorem B1821797 : Blo 1213424 1821797 := bbase (se 4 (by rfl) ⟨170793, by rfl⟩ : syracuseStep 1821797 = 341587) (by norm_num)
theorem B1821821 : Blo 1213424 1821821 := bbase (se 3 (by rfl) ⟨341591, by rfl⟩ : syracuseStep 1821821 = 683183) (by norm_num)
theorem B1846405 : Blo 1213424 1846405 := bbase (se 4 (by rfl) ⟨173100, by rfl⟩ : syracuseStep 1846405 = 346201) (by norm_num)
theorem B3075205 : Blo 1213424 3075205 := bbase (se 4 (by rfl) ⟨288300, by rfl⟩ : syracuseStep 3075205 = 576601) (by norm_num)
theorem B1297549 : Blo 1213424 1297549 := bbase (se 3 (by rfl) ⟨243290, by rfl⟩ : syracuseStep 1297549 = 486581) (by norm_num)
theorem B2075797 : Blo 1213424 2075797 := bbase (se 6 (by rfl) ⟨48651, by rfl⟩ : syracuseStep 2075797 = 97303) (by norm_num)
theorem B2731157 : Blo 1213424 2731157 := bbase (se 6 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 2731157 = 128023) (by norm_num)
theorem B1821845 : Blo 1213424 1821845 := bbase (se 6 (by rfl) ⟨42699, by rfl⟩ : syracuseStep 1821845 = 85399) (by norm_num)
theorem B2305189 : Blo 1213424 2305189 := bbase (se 4 (by rfl) ⟨216111, by rfl⟩ : syracuseStep 2305189 = 432223) (by norm_num)
theorem B1821869 : Blo 1213424 1821869 := bbase (se 3 (by rfl) ⟨341600, by rfl⟩ : syracuseStep 1821869 = 683201) (by norm_num)
theorem B2337965 : Blo 1213424 2337965 := bbase (se 3 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 2337965 = 876737) (by norm_num)
theorem B1821893 : Blo 1213424 1821893 := bbase (se 4 (by rfl) ⟨170802, by rfl⟩ : syracuseStep 1821893 = 341605) (by norm_num)
theorem B2731229 : Blo 1213424 2731229 := bbase (se 3 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 2731229 = 1024211) (by norm_num)
theorem B1821917 : Blo 1213424 1821917 := bbase (se 3 (by rfl) ⟨341609, by rfl⟩ : syracuseStep 1821917 = 683219) (by norm_num)
theorem B4099301 : Blo 1213424 4099301 := bbase (se 4 (by rfl) ⟨384309, by rfl⟩ : syracuseStep 4099301 = 768619) (by norm_num)
theorem B1821941 : Blo 1213424 1821941 := bbase (se 5 (by rfl) ⟨85403, by rfl⟩ : syracuseStep 1821941 = 170807) (by norm_num)
theorem B3075317 : Blo 1213424 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B2592005 : Blo 1213424 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B1821965 : Blo 1213424 1821965 := bbase (se 3 (by rfl) ⟨341618, by rfl⟩ : syracuseStep 1821965 = 683237) (by norm_num)
theorem B2731301 : Blo 1213424 2731301 := bbase (se 4 (by rfl) ⟨256059, by rfl⟩ : syracuseStep 2731301 = 512119) (by norm_num)
theorem B1821989 : Blo 1213424 1821989 := bbase (se 4 (by rfl) ⟨170811, by rfl⟩ : syracuseStep 1821989 = 341623) (by norm_num)
theorem B1822013 : Blo 1213424 1822013 := bbase (se 3 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 1822013 = 683255) (by norm_num)
theorem B1944901 : Blo 1213424 1944901 := bbase (se 4 (by rfl) ⟨182334, by rfl⟩ : syracuseStep 1944901 = 364669) (by norm_num)
theorem B6147413 : Blo 1213424 6147413 := bbase (se 11 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 6147413 = 9005) (by norm_num)
theorem B1822037 : Blo 1213424 1822037 := bbase (se 11 (by rfl) ⟨1334, by rfl⟩ : syracuseStep 1822037 = 2669) (by norm_num)
theorem B2731373 : Blo 1213424 2731373 := bbase (se 3 (by rfl) ⟨512132, by rfl⟩ : syracuseStep 2731373 = 1024265) (by norm_num)
theorem B1822061 : Blo 1213424 1822061 := bbase (se 3 (by rfl) ⟨341636, by rfl⟩ : syracuseStep 1822061 = 683273) (by norm_num)
theorem B1822085 : Blo 1213424 1822085 := bbase (se 4 (by rfl) ⟨170820, by rfl⟩ : syracuseStep 1822085 = 341641) (by norm_num)
theorem B1822109 : Blo 1213424 1822109 := bbase (se 3 (by rfl) ⟨341645, by rfl⟩ : syracuseStep 1822109 = 683291) (by norm_num)
theorem B2731445 : Blo 1213424 2731445 := bbase (se 5 (by rfl) ⟨128036, by rfl⟩ : syracuseStep 2731445 = 256073) (by norm_num)
theorem B10374581 : Blo 1213424 10374581 := bbase (se 5 (by rfl) ⟨486308, by rfl⟩ : syracuseStep 10374581 = 972617) (by norm_num)
theorem B1822133 : Blo 1213424 1822133 := bbase (se 5 (by rfl) ⟨85412, by rfl⟩ : syracuseStep 1822133 = 170825) (by norm_num)
theorem B3075509 : Blo 1213424 3075509 := bbase (se 5 (by rfl) ⟨144164, by rfl⟩ : syracuseStep 3075509 = 288329) (by norm_num)
theorem B1822157 : Blo 1213424 1822157 := bbase (se 3 (by rfl) ⟨341654, by rfl⟩ : syracuseStep 1822157 = 683309) (by norm_num)
theorem B2305493 : Blo 1213424 2305493 := bbase (se 7 (by rfl) ⟨27017, by rfl⟩ : syracuseStep 2305493 = 54035) (by norm_num)
theorem B2248157 : Blo 1213424 2248157 := bbase (se 3 (by rfl) ⟨421529, by rfl⟩ : syracuseStep 2248157 = 843059) (by norm_num)
theorem B1822181 : Blo 1213424 1822181 := bbase (se 4 (by rfl) ⟨170829, by rfl⟩ : syracuseStep 1822181 = 341659) (by norm_num)
theorem B2592245 : Blo 1213424 2592245 := bbase (se 5 (by rfl) ⟨121511, by rfl⟩ : syracuseStep 2592245 = 243023) (by norm_num)
theorem B2731517 : Blo 1213424 2731517 := bbase (se 3 (by rfl) ⟨512159, by rfl⟩ : syracuseStep 2731517 = 1024319) (by norm_num)
theorem B1822205 : Blo 1213424 1822205 := bbase (se 3 (by rfl) ⟨341663, by rfl⟩ : syracuseStep 1822205 = 683327) (by norm_num)
theorem B1822229 : Blo 1213424 1822229 := bbase (se 6 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 1822229 = 85417) (by norm_num)
theorem B3280421 : Blo 1213424 3280421 := bbase (se 4 (by rfl) ⟨307539, by rfl⟩ : syracuseStep 3280421 = 615079) (by norm_num)
theorem B1822253 : Blo 1213424 1822253 := bbase (se 3 (by rfl) ⟨341672, by rfl⟩ : syracuseStep 1822253 = 683345) (by norm_num)
theorem B1502777 : Blo 1213424 1502777 := bbase (se 2 (by rfl) ⟨563541, by rfl⟩ : syracuseStep 1502777 = 1127083) (by norm_num)
theorem B2731589 : Blo 1213424 2731589 := bbase (se 4 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 2731589 = 512173) (by norm_num)
theorem B1822277 : Blo 1213424 1822277 := bbase (se 4 (by rfl) ⟨170838, by rfl⟩ : syracuseStep 1822277 = 341677) (by norm_num)
theorem B1822301 : Blo 1213424 1822301 := bbase (se 3 (by rfl) ⟨341681, by rfl⟩ : syracuseStep 1822301 = 683363) (by norm_num)
theorem B1822325 : Blo 1213424 1822325 := bbase (se 5 (by rfl) ⟨85421, by rfl⟩ : syracuseStep 1822325 = 170843) (by norm_num)
theorem B2731661 : Blo 1213424 2731661 := bbase (se 3 (by rfl) ⟨512186, by rfl⟩ : syracuseStep 2731661 = 1024373) (by norm_num)
theorem B1822349 : Blo 1213424 1822349 := bbase (se 3 (by rfl) ⟨341690, by rfl⟩ : syracuseStep 1822349 = 683381) (by norm_num)
theorem B4099733 : Blo 1213424 4099733 := bbase (se 6 (by rfl) ⟨96087, by rfl⟩ : syracuseStep 4099733 = 192175) (by norm_num)
theorem B1822373 : Blo 1213424 1822373 := bbase (se 4 (by rfl) ⟨170847, by rfl⟩ : syracuseStep 1822373 = 341695) (by norm_num)
theorem B7786165 : Blo 1213424 7786165 := bbase (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) (by norm_num)
theorem B1822397 : Blo 1213424 1822397 := bbase (se 3 (by rfl) ⟨341699, by rfl⟩ : syracuseStep 1822397 = 683399) (by norm_num)
theorem B2731733 : Blo 1213424 2731733 := bbase (se 7 (by rfl) ⟨32012, by rfl⟩ : syracuseStep 2731733 = 64025) (by norm_num)
theorem B6917845 : Blo 1213424 6917845 := bbase (se 7 (by rfl) ⟨81068, by rfl⟩ : syracuseStep 6917845 = 162137) (by norm_num)
theorem B1822421 : Blo 1213424 1822421 := bbase (se 7 (by rfl) ⟨21356, by rfl⟩ : syracuseStep 1822421 = 42713) (by norm_num)
theorem B1822445 : Blo 1213424 1822445 := bbase (se 3 (by rfl) ⟨341708, by rfl⟩ : syracuseStep 1822445 = 683417) (by norm_num)
theorem B5836549 : Blo 1213424 5836549 := bbase (se 4 (by rfl) ⟨547176, by rfl⟩ : syracuseStep 5836549 = 1094353) (by norm_num)
theorem B1822469 : Blo 1213424 1822469 := bbase (se 4 (by rfl) ⟨170856, by rfl⟩ : syracuseStep 1822469 = 341713) (by norm_num)
theorem B3075853 : Blo 1213424 3075853 := bbase (se 3 (by rfl) ⟨576722, by rfl⟩ : syracuseStep 3075853 = 1153445) (by norm_num)
theorem B2731805 : Blo 1213424 2731805 := bbase (se 3 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 2731805 = 1024427) (by norm_num)
theorem B1822493 : Blo 1213424 1822493 := bbase (se 3 (by rfl) ⟨341717, by rfl⟩ : syracuseStep 1822493 = 683435) (by norm_num)
theorem B1822517 : Blo 1213424 1822517 := bbase (se 5 (by rfl) ⟨85430, by rfl⟩ : syracuseStep 1822517 = 170861) (by norm_num)
theorem B1822541 : Blo 1213424 1822541 := bbase (se 3 (by rfl) ⟨341726, by rfl⟩ : syracuseStep 1822541 = 683453) (by norm_num)
theorem B2731877 : Blo 1213424 2731877 := bbase (se 4 (by rfl) ⟨256113, by rfl⟩ : syracuseStep 2731877 = 512227) (by norm_num)
theorem B1822565 : Blo 1213424 1822565 := bbase (se 4 (by rfl) ⟨170865, by rfl⟩ : syracuseStep 1822565 = 341731) (by norm_num)
theorem B1945453 : Blo 1213424 1945453 := bbase (se 3 (by rfl) ⟨364772, by rfl⟩ : syracuseStep 1945453 = 729545) (by norm_num)
theorem B1535861 : Blo 1213424 1535861 := bbase (se 5 (by rfl) ⟨71993, by rfl⟩ : syracuseStep 1535861 = 143987) (by norm_num)
theorem B1822589 : Blo 1213424 1822589 := bbase (se 3 (by rfl) ⟨341735, by rfl⟩ : syracuseStep 1822589 = 683471) (by norm_num)
theorem B3075965 : Blo 1213424 3075965 := bbase (se 3 (by rfl) ⟨576743, by rfl⟩ : syracuseStep 3075965 = 1153487) (by norm_num)
theorem B1822613 : Blo 1213424 1822613 := bbase (se 6 (by rfl) ⟨42717, by rfl⟩ : syracuseStep 1822613 = 85435) (by norm_num)
theorem B1535917 : Blo 1213424 1535917 := bbase (se 3 (by rfl) ⟨287984, by rfl⟩ : syracuseStep 1535917 = 575969) (by norm_num)
theorem B2731949 : Blo 1213424 2731949 := bbase (se 3 (by rfl) ⟨512240, by rfl⟩ : syracuseStep 2731949 = 1024481) (by norm_num)
theorem B1822637 : Blo 1213424 1822637 := bbase (se 3 (by rfl) ⟨341744, by rfl⟩ : syracuseStep 1822637 = 683489) (by norm_num)
theorem B3116981 : Blo 1213424 3116981 := bbase (se 5 (by rfl) ⟨146108, by rfl⟩ : syracuseStep 3116981 = 292217) (by norm_num)
theorem B6074309 : Blo 1213424 6074309 := bbase (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) (by norm_num)
theorem B1822661 : Blo 1213424 1822661 := bbase (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) (by norm_num)
theorem B1822685 : Blo 1213424 1822685 := bbase (se 3 (by rfl) ⟨341753, by rfl⟩ : syracuseStep 1822685 = 683507) (by norm_num)
theorem B2592749 : Blo 1213424 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B2592757 : Blo 1213424 2592757 := bbase (se 5 (by rfl) ⟨121535, by rfl⟩ : syracuseStep 2592757 = 243071) (by norm_num)
theorem B2732021 : Blo 1213424 2732021 := bbase (se 5 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 2732021 = 256127) (by norm_num)
theorem B1822709 : Blo 1213424 1822709 := bbase (se 5 (by rfl) ⟨85439, by rfl⟩ : syracuseStep 1822709 = 170879) (by norm_num)
theorem B1536013 : Blo 1213424 1536013 := bbase (se 3 (by rfl) ⟨288002, by rfl⟩ : syracuseStep 1536013 = 576005) (by norm_num)
theorem B1822733 : Blo 1213424 1822733 := bbase (se 3 (by rfl) ⟨341762, by rfl⟩ : syracuseStep 1822733 = 683525) (by norm_num)
theorem B1822757 : Blo 1213424 1822757 := bbase (se 4 (by rfl) ⟨170883, by rfl⟩ : syracuseStep 1822757 = 341767) (by norm_num)
theorem B2732093 : Blo 1213424 2732093 := bbase (se 3 (by rfl) ⟨512267, by rfl⟩ : syracuseStep 2732093 = 1024535) (by norm_num)
theorem B1822781 : Blo 1213424 1822781 := bbase (se 3 (by rfl) ⟨341771, by rfl⟩ : syracuseStep 1822781 = 683543) (by norm_num)
theorem B3076157 : Blo 1213424 3076157 := bbase (se 3 (by rfl) ⟨576779, by rfl⟩ : syracuseStep 3076157 = 1153559) (by norm_num)
theorem B4100165 : Blo 1213424 4100165 := bbase (se 4 (by rfl) ⟨384390, by rfl⟩ : syracuseStep 4100165 = 768781) (by norm_num)
theorem B1822805 : Blo 1213424 1822805 := bbase (se 8 (by rfl) ⟨10680, by rfl⟩ : syracuseStep 1822805 = 21361) (by norm_num)
theorem B1945709 : Blo 1213424 1945709 := bbase (se 3 (by rfl) ⟨364820, by rfl⟩ : syracuseStep 1945709 = 729641) (by norm_num)
theorem B1822829 : Blo 1213424 1822829 := bbase (se 3 (by rfl) ⟨341780, by rfl⟩ : syracuseStep 1822829 = 683561) (by norm_num)
theorem B2732165 : Blo 1213424 2732165 := bbase (se 4 (by rfl) ⟨256140, by rfl⟩ : syracuseStep 2732165 = 512281) (by norm_num)
theorem B1822853 : Blo 1213424 1822853 := bbase (se 4 (by rfl) ⟨170892, by rfl⟩ : syracuseStep 1822853 = 341785) (by norm_num)
theorem B1822877 : Blo 1213424 1822877 := bbase (se 3 (by rfl) ⟨341789, by rfl⟩ : syracuseStep 1822877 = 683579) (by norm_num)
theorem B1822901 : Blo 1213424 1822901 := bbase (se 5 (by rfl) ⟨85448, by rfl⟩ : syracuseStep 1822901 = 170897) (by norm_num)
theorem B1536185 : Blo 1213424 1536185 := bbase (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) (by norm_num)
theorem B2306245 : Blo 1213424 2306245 := bbase (se 4 (by rfl) ⟨216210, by rfl⟩ : syracuseStep 2306245 = 432421) (by norm_num)
theorem B2732237 : Blo 1213424 2732237 := bbase (se 3 (by rfl) ⟨512294, by rfl⟩ : syracuseStep 2732237 = 1024589) (by norm_num)
theorem B1822925 : Blo 1213424 1822925 := bbase (se 3 (by rfl) ⟨341798, by rfl⟩ : syracuseStep 1822925 = 683597) (by norm_num)
theorem B1822949 : Blo 1213424 1822949 := bbase (se 4 (by rfl) ⟨170901, by rfl⟩ : syracuseStep 1822949 = 341803) (by norm_num)
theorem B1536241 : Blo 1213424 1536241 := bbase (se 2 (by rfl) ⟨576090, by rfl⟩ : syracuseStep 1536241 = 1152181) (by norm_num)
theorem B1822973 : Blo 1213424 1822973 := bbase (se 3 (by rfl) ⟨341807, by rfl⟩ : syracuseStep 1822973 = 683615) (by norm_num)
theorem B2732309 : Blo 1213424 2732309 := bbase (se 6 (by rfl) ⟨64038, by rfl⟩ : syracuseStep 2732309 = 128077) (by norm_num)
theorem B1822997 : Blo 1213424 1822997 := bbase (se 6 (by rfl) ⟨42726, by rfl⟩ : syracuseStep 1822997 = 85453) (by norm_num)
theorem B1823021 : Blo 1213424 1823021 := bbase (se 3 (by rfl) ⟨341816, by rfl⟩ : syracuseStep 1823021 = 683633) (by norm_num)
theorem B5189957 : Blo 1213424 5189957 := bbase (se 4 (by rfl) ⟨486558, by rfl⟩ : syracuseStep 5189957 = 973117) (by norm_num)
theorem B1847621 : Blo 1213424 1847621 := bbase (se 4 (by rfl) ⟨173214, by rfl⟩ : syracuseStep 1847621 = 346429) (by norm_num)
theorem B1823045 : Blo 1213424 1823045 := bbase (se 4 (by rfl) ⟨170910, by rfl⟩ : syracuseStep 1823045 = 341821) (by norm_num)
theorem B1536337 : Blo 1213424 1536337 := bbase (se 2 (by rfl) ⟨576126, by rfl⟩ : syracuseStep 1536337 = 1152253) (by norm_num)
theorem B2306389 : Blo 1213424 2306389 := bbase (se 10 (by rfl) ⟨3378, by rfl⟩ : syracuseStep 2306389 = 6757) (by norm_num)
theorem B2732381 : Blo 1213424 2732381 := bbase (se 3 (by rfl) ⟨512321, by rfl⟩ : syracuseStep 2732381 = 1024643) (by norm_num)
theorem B1823069 : Blo 1213424 1823069 := bbase (se 3 (by rfl) ⟨341825, by rfl⟩ : syracuseStep 1823069 = 683651) (by norm_num)
theorem B4608373 : Blo 1213424 4608373 := bbase (se 5 (by rfl) ⟨216017, by rfl⟩ : syracuseStep 4608373 = 432035) (by norm_num)
theorem B1823093 : Blo 1213424 1823093 := bbase (se 5 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 1823093 = 170915) (by norm_num)
theorem B1823117 : Blo 1213424 1823117 := bbase (se 3 (by rfl) ⟨341834, by rfl⟩ : syracuseStep 1823117 = 683669) (by norm_num)
theorem B3076501 : Blo 1213424 3076501 := bbase (se 6 (by rfl) ⟨72105, by rfl⟩ : syracuseStep 3076501 = 144211) (by norm_num)
theorem B2732453 : Blo 1213424 2732453 := bbase (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) (by norm_num)
theorem B2732525 : Blo 1213424 2732525 := bbase (se 3 (by rfl) ⟨512348, by rfl⟩ : syracuseStep 2732525 = 1024697) (by norm_num)
theorem B2306549 : Blo 1213424 2306549 := bbase (se 5 (by rfl) ⟨108119, by rfl⟩ : syracuseStep 2306549 = 216239) (by norm_num)
theorem B4100597 : Blo 1213424 4100597 := bbase (se 5 (by rfl) ⟨192215, by rfl⟩ : syracuseStep 4100597 = 384431) (by norm_num)
theorem B1536509 : Blo 1213424 1536509 := bbase (se 3 (by rfl) ⟨288095, by rfl⟩ : syracuseStep 1536509 = 576191) (by norm_num)
theorem B1536565 : Blo 1213424 1536565 := bbase (se 5 (by rfl) ⟨72026, by rfl⟩ : syracuseStep 1536565 = 144053) (by norm_num)
theorem B2732597 : Blo 1213424 2732597 := bbase (se 5 (by rfl) ⟨128090, by rfl⟩ : syracuseStep 2732597 = 256181) (by norm_num)
theorem B6148709 : Blo 1213424 6148709 := bbase (se 4 (by rfl) ⟨576441, by rfl⟩ : syracuseStep 6148709 = 1152883) (by norm_num)
theorem B2732669 : Blo 1213424 2732669 := bbase (se 3 (by rfl) ⟨512375, by rfl⟩ : syracuseStep 2732669 = 1024751) (by norm_num)
theorem B2306693 : Blo 1213424 2306693 := bbase (se 4 (by rfl) ⟨216252, by rfl⟩ : syracuseStep 2306693 = 432505) (by norm_num)
theorem B2667149 : Blo 1213424 2667149 := bbase (se 3 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 2667149 = 1000181) (by norm_num)
theorem B1536661 : Blo 1213424 1536661 := bbase (se 6 (by rfl) ⟨36015, by rfl⟩ : syracuseStep 1536661 = 72031) (by norm_num)
theorem B4608677 : Blo 1213424 4608677 := bbase (se 4 (by rfl) ⟨432063, by rfl⟩ : syracuseStep 4608677 = 864127) (by norm_num)
theorem B2732741 : Blo 1213424 2732741 := bbase (se 4 (by rfl) ⟨256194, by rfl⟩ : syracuseStep 2732741 = 512389) (by norm_num)
theorem B2732813 : Blo 1213424 2732813 := bbase (se 3 (by rfl) ⟨512402, by rfl⟩ : syracuseStep 2732813 = 1024805) (by norm_num)
theorem B1946413 : Blo 1213424 1946413 := bbase (se 3 (by rfl) ⟨364952, by rfl⟩ : syracuseStep 1946413 = 729905) (by norm_num)
theorem B1536833 : Blo 1213424 1536833 := bbase (se 2 (by rfl) ⟨576312, by rfl⟩ : syracuseStep 1536833 = 1152625) (by norm_num)
theorem B2732885 : Blo 1213424 2732885 := bbase (se 9 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 2732885 = 16013) (by norm_num)
theorem B1536889 : Blo 1213424 1536889 := bbase (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) (by norm_num)
theorem B16610197 : Blo 1213424 16610197 := bbase (se 6 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 16610197 = 778603) (by norm_num)
theorem B2077589 : Blo 1213424 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B2732957 : Blo 1213424 2732957 := bbase (se 3 (by rfl) ⟨512429, by rfl⟩ : syracuseStep 2732957 = 1024859) (by norm_num)
theorem B4101029 : Blo 1213424 4101029 := bbase (se 4 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 4101029 = 768943) (by norm_num)
theorem B2306981 : Blo 1213424 2306981 := bbase (se 4 (by rfl) ⟨216279, by rfl⟩ : syracuseStep 2306981 = 432559) (by norm_num)
theorem B1536985 : Blo 1213424 1536985 := bbase (se 2 (by rfl) ⟨576369, by rfl⟩ : syracuseStep 1536985 = 1152739) (by norm_num)
theorem B2733029 : Blo 1213424 2733029 := bbase (se 4 (by rfl) ⟨256221, by rfl⟩ : syracuseStep 2733029 = 512443) (by norm_num)
theorem B2462717 : Blo 1213424 2462717 := bbase (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) (by norm_num)
theorem B2733101 : Blo 1213424 2733101 := bbase (se 3 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 2733101 = 1024913) (by norm_num)
theorem B2307133 : Blo 1213424 2307133 := bbase (se 3 (by rfl) ⟨432587, by rfl⟩ : syracuseStep 2307133 = 865175) (by norm_num)
theorem B2593885 : Blo 1213424 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B2733173 : Blo 1213424 2733173 := bbase (se 5 (by rfl) ⟨128117, by rfl⟩ : syracuseStep 2733173 = 256235) (by norm_num)
theorem B1537157 : Blo 1213424 1537157 := bbase (se 4 (by rfl) ⟨144108, by rfl⟩ : syracuseStep 1537157 = 288217) (by norm_num)
theorem B1365133 : Blo 1213424 1365133 := bbase (se 3 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 1365133 = 511925) (by norm_num)
theorem B1365169 : Blo 1213424 1365169 := bbase (se 2 (by rfl) ⟨511938, by rfl⟩ : syracuseStep 1365169 = 1023877) (by norm_num)
theorem B1537213 : Blo 1213424 1537213 := bbase (se 3 (by rfl) ⟨288227, by rfl⟩ : syracuseStep 1537213 = 576455) (by norm_num)
theorem B2733245 : Blo 1213424 2733245 := bbase (se 3 (by rfl) ⟨512483, by rfl⟩ : syracuseStep 2733245 = 1024967) (by norm_num)
theorem B1365205 : Blo 1213424 1365205 := bbase (se 7 (by rfl) ⟨15998, by rfl⟩ : syracuseStep 1365205 = 31997) (by norm_num)
theorem B1946837 : Blo 1213424 1946837 := bbase (se 7 (by rfl) ⟨22814, by rfl⟩ : syracuseStep 1946837 = 45629) (by norm_num)
theorem B1365241 : Blo 1213424 1365241 := bbase (se 2 (by rfl) ⟨511965, by rfl⟩ : syracuseStep 1365241 = 1023931) (by norm_num)
theorem B2733317 : Blo 1213424 2733317 := bbase (se 4 (by rfl) ⟨256248, by rfl⟩ : syracuseStep 2733317 = 512497) (by norm_num)
theorem B1365277 : Blo 1213424 1365277 := bbase (se 3 (by rfl) ⟨255989, by rfl⟩ : syracuseStep 1365277 = 511979) (by norm_num)
theorem B1537309 : Blo 1213424 1537309 := bbase (se 3 (by rfl) ⟨288245, by rfl⟩ : syracuseStep 1537309 = 576491) (by norm_num)
theorem B1365313 : Blo 1213424 1365313 := bbase (se 2 (by rfl) ⟨511992, by rfl⟩ : syracuseStep 1365313 = 1023985) (by norm_num)
theorem B2733389 : Blo 1213424 2733389 := bbase (se 3 (by rfl) ⟨512510, by rfl⟩ : syracuseStep 2733389 = 1025021) (by norm_num)
theorem B4101461 : Blo 1213424 4101461 := bbase (se 14 (by rfl) ⟨375, by rfl⟩ : syracuseStep 4101461 = 751) (by norm_num)
theorem B1365349 : Blo 1213424 1365349 := bbase (se 4 (by rfl) ⟨128001, by rfl⟩ : syracuseStep 1365349 = 256003) (by norm_num)
theorem B1365385 : Blo 1213424 1365385 := bbase (se 2 (by rfl) ⟨512019, by rfl⟩ : syracuseStep 1365385 = 1024039) (by norm_num)
theorem B2733461 : Blo 1213424 2733461 := bbase (se 6 (by rfl) ⟨64065, by rfl⟩ : syracuseStep 2733461 = 128131) (by norm_num)
theorem B1365421 : Blo 1213424 1365421 := bbase (se 3 (by rfl) ⟨256016, by rfl⟩ : syracuseStep 1365421 = 512033) (by norm_num)
theorem B1537481 : Blo 1213424 1537481 := bbase (se 2 (by rfl) ⟨576555, by rfl⟩ : syracuseStep 1537481 = 1153111) (by norm_num)
theorem B1365457 : Blo 1213424 1365457 := bbase (se 2 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 1365457 = 1024093) (by norm_num)
theorem B2594261 : Blo 1213424 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B2733533 : Blo 1213424 2733533 := bbase (se 3 (by rfl) ⟨512537, by rfl⟩ : syracuseStep 2733533 = 1025075) (by norm_num)
theorem B1365493 : Blo 1213424 1365493 := bbase (se 5 (by rfl) ⟨64007, by rfl⟩ : syracuseStep 1365493 = 128015) (by norm_num)
theorem B1537537 : Blo 1213424 1537537 := bbase (se 2 (by rfl) ⟨576576, by rfl⟩ : syracuseStep 1537537 = 1153153) (by norm_num)
theorem B1365529 : Blo 1213424 1365529 := bbase (se 2 (by rfl) ⟨512073, by rfl⟩ : syracuseStep 1365529 = 1024147) (by norm_num)
theorem B2733605 : Blo 1213424 2733605 := bbase (se 4 (by rfl) ⟨256275, by rfl⟩ : syracuseStep 2733605 = 512551) (by norm_num)
theorem B2078245 : Blo 1213424 2078245 := bbase (se 4 (by rfl) ⟨194835, by rfl⟩ : syracuseStep 2078245 = 389671) (by norm_num)
theorem B1365565 : Blo 1213424 1365565 := bbase (se 3 (by rfl) ⟨256043, by rfl⟩ : syracuseStep 1365565 = 512087) (by norm_num)
theorem B5994053 : Blo 1213424 5994053 := bbase (se 4 (by rfl) ⟨561942, by rfl⟩ : syracuseStep 5994053 = 1123885) (by norm_num)
theorem B1365601 : Blo 1213424 1365601 := bbase (se 2 (by rfl) ⟨512100, by rfl⟩ : syracuseStep 1365601 = 1024201) (by norm_num)
theorem B1537633 : Blo 1213424 1537633 := bbase (se 2 (by rfl) ⟨576612, by rfl⟩ : syracuseStep 1537633 = 1153225) (by norm_num)
theorem B2733677 : Blo 1213424 2733677 := bbase (se 3 (by rfl) ⟨512564, by rfl⟩ : syracuseStep 2733677 = 1025129) (by norm_num)
theorem B1365637 : Blo 1213424 1365637 := bbase (se 4 (by rfl) ⟨128028, by rfl⟩ : syracuseStep 1365637 = 256057) (by norm_num)
theorem B2463365 : Blo 1213424 2463365 := bbase (se 4 (by rfl) ⟨230940, by rfl⟩ : syracuseStep 2463365 = 461881) (by norm_num)
theorem B6919829 : Blo 1213424 6919829 := bbase (se 6 (by rfl) ⟨162183, by rfl⟩ : syracuseStep 6919829 = 324367) (by norm_num)
theorem B1365673 : Blo 1213424 1365673 := bbase (se 2 (by rfl) ⟨512127, by rfl⟩ : syracuseStep 1365673 = 1024255) (by norm_num)
theorem B2733749 : Blo 1213424 2733749 := bbase (se 5 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 2733749 = 256289) (by norm_num)
theorem B1365709 : Blo 1213424 1365709 := bbase (se 3 (by rfl) ⟨256070, by rfl⟩ : syracuseStep 1365709 = 512141) (by norm_num)
theorem B1365745 : Blo 1213424 1365745 := bbase (se 2 (by rfl) ⟨512154, by rfl⟩ : syracuseStep 1365745 = 1024309) (by norm_num)
theorem B2733821 : Blo 1213424 2733821 := bbase (se 3 (by rfl) ⟨512591, by rfl⟩ : syracuseStep 2733821 = 1025183) (by norm_num)
theorem B4101893 : Blo 1213424 4101893 := bbase (se 4 (by rfl) ⟨384552, by rfl⟩ : syracuseStep 4101893 = 769105) (by norm_num)
theorem B1537805 : Blo 1213424 1537805 := bbase (se 3 (by rfl) ⟨288338, by rfl⟩ : syracuseStep 1537805 = 576677) (by norm_num)
theorem B1365781 : Blo 1213424 1365781 := bbase (se 6 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 1365781 = 64021) (by norm_num)
theorem B1578785 : Blo 1213424 1578785 := bbase (se 2 (by rfl) ⟨592044, by rfl⟩ : syracuseStep 1578785 = 1184089) (by norm_num)
theorem B1365817 : Blo 1213424 1365817 := bbase (se 2 (by rfl) ⟨512181, by rfl⟩ : syracuseStep 1365817 = 1024363) (by norm_num)
theorem B2733893 : Blo 1213424 2733893 := bbase (se 4 (by rfl) ⟨256302, by rfl⟩ : syracuseStep 2733893 = 512605) (by norm_num)
theorem B1537861 : Blo 1213424 1537861 := bbase (se 4 (by rfl) ⟨144174, by rfl⟩ : syracuseStep 1537861 = 288349) (by norm_num)
theorem B1365853 : Blo 1213424 1365853 := bbase (se 3 (by rfl) ⟨256097, by rfl⟩ : syracuseStep 1365853 = 512195) (by norm_num)
theorem B6150005 : Blo 1213424 6150005 := bbase (se 5 (by rfl) ⟨288281, by rfl⟩ : syracuseStep 6150005 = 576563) (by norm_num)
theorem B1365889 : Blo 1213424 1365889 := bbase (se 2 (by rfl) ⟨512208, by rfl⟩ : syracuseStep 1365889 = 1024417) (by norm_num)
theorem B2733965 : Blo 1213424 2733965 := bbase (se 3 (by rfl) ⟨512618, by rfl⟩ : syracuseStep 2733965 = 1025237) (by norm_num)
theorem B1365925 : Blo 1213424 1365925 := bbase (se 4 (by rfl) ⟨128055, by rfl⟩ : syracuseStep 1365925 = 256111) (by norm_num)
theorem B4437925 : Blo 1213424 4437925 := bbase (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) (by norm_num)
theorem B1537957 : Blo 1213424 1537957 := bbase (se 4 (by rfl) ⟨144183, by rfl⟩ : syracuseStep 1537957 = 288367) (by norm_num)
theorem B1365961 : Blo 1213424 1365961 := bbase (se 2 (by rfl) ⟨512235, by rfl⟩ : syracuseStep 1365961 = 1024471) (by norm_num)
theorem B2807765 : Blo 1213424 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B2734037 : Blo 1213424 2734037 := bbase (se 7 (by rfl) ⟨32039, by rfl⟩ : syracuseStep 2734037 = 64079) (by norm_num)
theorem B1365997 : Blo 1213424 1365997 := bbase (se 3 (by rfl) ⟨256124, by rfl⟩ : syracuseStep 1365997 = 512249) (by norm_num)
theorem B1366033 : Blo 1213424 1366033 := bbase (se 2 (by rfl) ⟨512262, by rfl⟩ : syracuseStep 1366033 = 1024525) (by norm_num)
theorem B2734109 : Blo 1213424 2734109 := bbase (se 3 (by rfl) ⟨512645, by rfl⟩ : syracuseStep 2734109 = 1025291) (by norm_num)
theorem B4151333 : Blo 1213424 4151333 := bbase (se 4 (by rfl) ⟨389187, by rfl⟩ : syracuseStep 4151333 = 778375) (by norm_num)
theorem B1366069 : Blo 1213424 1366069 := bbase (se 5 (by rfl) ⟨64034, by rfl⟩ : syracuseStep 1366069 = 128069) (by norm_num)
theorem B1538129 : Blo 1213424 1538129 := bbase (se 2 (by rfl) ⟨576798, by rfl⟩ : syracuseStep 1538129 = 1153597) (by norm_num)
theorem B1366105 : Blo 1213424 1366105 := bbase (se 2 (by rfl) ⟨512289, by rfl⟩ : syracuseStep 1366105 = 1024579) (by norm_num)
theorem B2734181 : Blo 1213424 2734181 := bbase (se 4 (by rfl) ⟨256329, by rfl⟩ : syracuseStep 2734181 = 512659) (by norm_num)
theorem B2463853 : Blo 1213424 2463853 := bbase (se 3 (by rfl) ⟨461972, by rfl⟩ : syracuseStep 2463853 = 923945) (by norm_num)
theorem B1366141 : Blo 1213424 1366141 := bbase (se 3 (by rfl) ⟨256151, by rfl⟩ : syracuseStep 1366141 = 512303) (by norm_num)
theorem B1538185 : Blo 1213424 1538185 := bbase (se 2 (by rfl) ⟨576819, by rfl⟩ : syracuseStep 1538185 = 1153639) (by norm_num)
theorem B1366177 : Blo 1213424 1366177 := bbase (se 2 (by rfl) ⟨512316, by rfl⟩ : syracuseStep 1366177 = 1024633) (by norm_num)
theorem B2734253 : Blo 1213424 2734253 := bbase (se 3 (by rfl) ⟨512672, by rfl⟩ : syracuseStep 2734253 = 1025345) (by norm_num)
theorem B5183669 : Blo 1213424 5183669 := bbase (se 5 (by rfl) ⟨242984, by rfl⟩ : syracuseStep 5183669 = 485969) (by norm_num)
theorem B1366213 : Blo 1213424 1366213 := bbase (se 4 (by rfl) ⟨128082, by rfl⟩ : syracuseStep 1366213 = 256165) (by norm_num)
theorem B4987109 : Blo 1213424 4987109 := bbase (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) (by norm_num)
theorem B1366249 : Blo 1213424 1366249 := bbase (se 2 (by rfl) ⟨512343, by rfl⟩ : syracuseStep 1366249 = 1024687) (by norm_num)
theorem B2734325 : Blo 1213424 2734325 := bbase (se 5 (by rfl) ⟨128171, by rfl⟩ : syracuseStep 2734325 = 256343) (by norm_num)
theorem B1366285 : Blo 1213424 1366285 := bbase (se 3 (by rfl) ⟨256178, by rfl⟩ : syracuseStep 1366285 = 512357) (by norm_num)
theorem B1366321 : Blo 1213424 1366321 := bbase (se 2 (by rfl) ⟨512370, by rfl⟩ : syracuseStep 1366321 = 1024741) (by norm_num)
theorem B2734397 : Blo 1213424 2734397 := bbase (se 3 (by rfl) ⟨512699, by rfl⟩ : syracuseStep 2734397 = 1025399) (by norm_num)
theorem B4921669 : Blo 1213424 4921669 := bbase (se 4 (by rfl) ⟨461406, by rfl⟩ : syracuseStep 4921669 = 922813) (by norm_num)
theorem B1366357 : Blo 1213424 1366357 := bbase (se 10 (by rfl) ⟨2001, by rfl⟩ : syracuseStep 1366357 = 4003) (by norm_num)
theorem B10377557 : Blo 1213424 10377557 := bbase (se 10 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 10377557 = 30403) (by norm_num)
theorem B1366393 : Blo 1213424 1366393 := bbase (se 2 (by rfl) ⟨512397, by rfl⟩ : syracuseStep 1366393 = 1024795) (by norm_num)
theorem B2734469 : Blo 1213424 2734469 := bbase (se 4 (by rfl) ⟨256356, by rfl⟩ : syracuseStep 2734469 = 512713) (by norm_num)
theorem B1366429 : Blo 1213424 1366429 := bbase (se 3 (by rfl) ⟨256205, by rfl⟩ : syracuseStep 1366429 = 512411) (by norm_num)
theorem B5183909 : Blo 1213424 5183909 := bbase (se 4 (by rfl) ⟨485991, by rfl⟩ : syracuseStep 5183909 = 971983) (by norm_num)
theorem B1366465 : Blo 1213424 1366465 := bbase (se 2 (by rfl) ⟨512424, by rfl⟩ : syracuseStep 1366465 = 1024849) (by norm_num)
theorem B3037637 : Blo 1213424 3037637 := bbase (se 4 (by rfl) ⟨284778, by rfl⟩ : syracuseStep 3037637 = 569557) (by norm_num)
theorem B2734541 : Blo 1213424 2734541 := bbase (se 3 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 2734541 = 1025453) (by norm_num)
theorem B5257685 : Blo 1213424 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B1366501 : Blo 1213424 1366501 := bbase (se 4 (by rfl) ⟨128109, by rfl⟩ : syracuseStep 1366501 = 256219) (by norm_num)
theorem B1366537 : Blo 1213424 1366537 := bbase (se 2 (by rfl) ⟨512451, by rfl⟩ : syracuseStep 1366537 = 1024903) (by norm_num)
theorem B5536277 : Blo 1213424 5536277 := bbase (se 6 (by rfl) ⟨129756, by rfl⟩ : syracuseStep 5536277 = 259513) (by norm_num)
theorem B2734613 : Blo 1213424 2734613 := bbase (se 6 (by rfl) ⟨64092, by rfl⟩ : syracuseStep 2734613 = 128185) (by norm_num)
theorem B1366573 : Blo 1213424 1366573 := bbase (se 3 (by rfl) ⟨256232, by rfl⟩ : syracuseStep 1366573 = 512465) (by norm_num)
theorem B1366609 : Blo 1213424 1366609 := bbase (se 2 (by rfl) ⟨512478, by rfl⟩ : syracuseStep 1366609 = 1024957) (by norm_num)
theorem B2734685 : Blo 1213424 2734685 := bbase (se 3 (by rfl) ⟨512753, by rfl⟩ : syracuseStep 2734685 = 1025507) (by norm_num)
theorem B1366645 : Blo 1213424 1366645 := bbase (se 5 (by rfl) ⟨64061, by rfl⟩ : syracuseStep 1366645 = 128123) (by norm_num)
theorem B1366681 : Blo 1213424 1366681 := bbase (se 2 (by rfl) ⟨512505, by rfl⟩ : syracuseStep 1366681 = 1025011) (by norm_num)
theorem B1366717 : Blo 1213424 1366717 := bbase (se 3 (by rfl) ⟨256259, by rfl⟩ : syracuseStep 1366717 = 512519) (by norm_num)
theorem B1366753 : Blo 1213424 1366753 := bbase (se 2 (by rfl) ⟨512532, by rfl⟩ : syracuseStep 1366753 = 1025065) (by norm_num)
theorem B4610789 : Blo 1213424 4610789 := bbase (se 4 (by rfl) ⟨432261, by rfl⟩ : syracuseStep 4610789 = 864523) (by norm_num)
theorem B1366789 : Blo 1213424 1366789 := bbase (se 4 (by rfl) ⟨128136, by rfl⟩ : syracuseStep 1366789 = 256273) (by norm_num)
theorem B1366825 : Blo 1213424 1366825 := bbase (se 2 (by rfl) ⟨512559, by rfl⟩ : syracuseStep 1366825 = 1025119) (by norm_num)
theorem B5839685 : Blo 1213424 5839685 := bbase (se 4 (by rfl) ⟨547470, by rfl⟩ : syracuseStep 5839685 = 1094941) (by norm_num)
theorem B1366861 : Blo 1213424 1366861 := bbase (se 3 (by rfl) ⟨256286, by rfl⟩ : syracuseStep 1366861 = 512573) (by norm_num)
theorem B1366897 : Blo 1213424 1366897 := bbase (se 2 (by rfl) ⟨512586, by rfl⟩ : syracuseStep 1366897 = 1025173) (by norm_num)
theorem B11074421 : Blo 1213424 11074421 := bbase (se 5 (by rfl) ⟨519113, by rfl⟩ : syracuseStep 11074421 = 1038227) (by norm_num)
theorem B1366933 : Blo 1213424 1366933 := bbase (se 6 (by rfl) ⟨32037, by rfl⟩ : syracuseStep 1366933 = 64075) (by norm_num)
theorem B1366969 : Blo 1213424 1366969 := bbase (se 2 (by rfl) ⟨512613, by rfl⟩ : syracuseStep 1366969 = 1025227) (by norm_num)
theorem B1367005 : Blo 1213424 1367005 := bbase (se 3 (by rfl) ⟨256313, by rfl⟩ : syracuseStep 1367005 = 512627) (by norm_num)
theorem B1367041 : Blo 1213424 1367041 := bbase (se 2 (by rfl) ⟨512640, by rfl⟩ : syracuseStep 1367041 = 1025281) (by norm_num)
theorem B4611077 : Blo 1213424 4611077 := bbase (se 4 (by rfl) ⟨432288, by rfl⟩ : syracuseStep 4611077 = 864577) (by norm_num)
theorem B3890213 : Blo 1213424 3890213 := bbase (se 4 (by rfl) ⟨364707, by rfl⟩ : syracuseStep 3890213 = 729415) (by norm_num)
theorem B1367077 : Blo 1213424 1367077 := bbase (se 4 (by rfl) ⟨128163, by rfl⟩ : syracuseStep 1367077 = 256327) (by norm_num)
theorem B3456053 : Blo 1213424 3456053 := bbase (se 5 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 3456053 = 324005) (by norm_num)
theorem B1367113 : Blo 1213424 1367113 := bbase (se 2 (by rfl) ⟨512667, by rfl⟩ : syracuseStep 1367113 = 1025335) (by norm_num)
theorem B1367149 : Blo 1213424 1367149 := bbase (se 3 (by rfl) ⟨256340, by rfl⟩ : syracuseStep 1367149 = 512681) (by norm_num)
theorem B6151301 : Blo 1213424 6151301 := bbase (se 4 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 6151301 = 1153369) (by norm_num)
theorem B1367185 : Blo 1213424 1367185 := bbase (se 2 (by rfl) ⟨512694, by rfl⟩ : syracuseStep 1367185 = 1025389) (by norm_num)
theorem B2768021 : Blo 1213424 2768021 := bbase (se 6 (by rfl) ⟨64875, by rfl⟩ : syracuseStep 2768021 = 129751) (by norm_num)
theorem B1367221 : Blo 1213424 1367221 := bbase (se 5 (by rfl) ⟨64088, by rfl⟩ : syracuseStep 1367221 = 128177) (by norm_num)
theorem B1367257 : Blo 1213424 1367257 := bbase (se 2 (by rfl) ⟨512721, by rfl⟩ : syracuseStep 1367257 = 1025443) (by norm_num)
theorem B1727725 : Blo 1213424 1727725 := bbase (se 3 (by rfl) ⟨323948, by rfl⟩ : syracuseStep 1727725 = 647897) (by norm_num)
theorem B7888117 : Blo 1213424 7888117 := bbase (se 5 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 7888117 = 739511) (by norm_num)
theorem B1367293 : Blo 1213424 1367293 := bbase (se 3 (by rfl) ⟨256367, by rfl⟩ : syracuseStep 1367293 = 512735) (by norm_num)
theorem B1367329 : Blo 1213424 1367329 := bbase (se 2 (by rfl) ⟨512748, by rfl⟩ : syracuseStep 1367329 = 1025497) (by norm_num)
theorem B1727821 : Blo 1213424 1727821 := bbase (se 3 (by rfl) ⟨323966, by rfl⟩ : syracuseStep 1727821 = 647933) (by norm_num)
theorem B4095413 : Blo 1213424 4095413 := bbase (se 5 (by rfl) ⟨191972, by rfl⟩ : syracuseStep 4095413 = 383945) (by norm_num)
theorem B6143525 : Blo 1213424 6143525 := bbase (se 4 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 6143525 = 1151911) (by norm_num)
theorem B16621141 : Blo 1213424 16621141 := bbase (se 8 (by rfl) ⟨97389, by rfl⟩ : syracuseStep 16621141 = 194779) (by norm_num)
theorem B3071621 : Blo 1213424 3071621 := bbase (se 4 (by rfl) ⟨287964, by rfl⟩ : syracuseStep 3071621 = 575929) (by norm_num)
theorem B2186941 : Blo 1213424 2186941 := bbase (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) (by norm_num)
theorem B2047693 : Blo 1213424 2047693 := bbase (se 3 (by rfl) ⟨383942, by rfl⟩ : syracuseStep 2047693 = 767885) (by norm_num)
theorem B31571669 : Blo 1213424 31571669 := bbase (se 7 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 31571669 = 739961) (by norm_num)
theorem B2629397 : Blo 1213424 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B2047781 : Blo 1213424 2047781 := bbase (se 4 (by rfl) ⟨191979, by rfl⟩ : syracuseStep 2047781 = 383959) (by norm_num)
theorem B6922037 : Blo 1213424 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B1728317 : Blo 1213424 1728317 := bbase (se 3 (by rfl) ⟨324059, by rfl⟩ : syracuseStep 1728317 = 648119) (by norm_num)
theorem B4095845 : Blo 1213424 4095845 := bbase (se 4 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 4095845 = 767971) (by norm_num)
theorem B2047909 : Blo 1213424 2047909 := bbase (se 4 (by rfl) ⟨191991, by rfl⟩ : syracuseStep 2047909 = 383983) (by norm_num)
theorem B3071965 : Blo 1213424 3071965 := bbase (se 3 (by rfl) ⟨575993, by rfl⟩ : syracuseStep 3071965 = 1151987) (by norm_num)
theorem B1458157 : Blo 1213424 1458157 := bbase (se 3 (by rfl) ⟨273404, by rfl⟩ : syracuseStep 1458157 = 546809) (by norm_num)
theorem B2047997 : Blo 1213424 2047997 := bbase (se 3 (by rfl) ⟨383999, by rfl⟩ : syracuseStep 2047997 = 767999) (by norm_num)
theorem B2048017 : Blo 1213424 2048017 := bstep (se 2 (by rfl) ⟨768006, by rfl⟩ : syracuseStep 2048017 = 1536013) B1536013
theorem B2048051 : Blo 1213424 2048051 := bstep (se 1 (by rfl) ⟨1536038, by rfl⟩ : syracuseStep 2048051 = 3072077) B3072077
theorem B3891341 : Blo 1213424 3891341 := bstep (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) B1459253
theorem B3285137 : Blo 1213424 3285137 := bstep (se 2 (by rfl) ⟨1231926, by rfl⟩ : syracuseStep 3285137 = 2463853) B2463853
theorem B2048179 : Blo 1213424 2048179 := bstep (se 1 (by rfl) ⟨1536134, by rfl⟩ : syracuseStep 2048179 = 3072269) B3072269
theorem B2048321 : Blo 1213424 2048321 := bstep (se 2 (by rfl) ⟨768120, by rfl⟩ : syracuseStep 2048321 = 1536241) B1536241
theorem B1458499 : Blo 1213424 1458499 := bstep (se 1 (by rfl) ⟨1093874, by rfl⟩ : syracuseStep 1458499 = 2187749) B2187749
theorem B1622371 : Blo 1213424 1622371 := bstep (se 1 (by rfl) ⟨1216778, by rfl⟩ : syracuseStep 1622371 = 2433557) B2433557
theorem B3072401 : Blo 1213424 3072401 := bstep (se 2 (by rfl) ⟨1152150, by rfl⟩ : syracuseStep 3072401 = 2304301) B2304301
theorem B6562225 : Blo 1213424 6562225 := bstep (se 2 (by rfl) ⟨2460834, by rfl⟩ : syracuseStep 6562225 = 4921669) B4921669
theorem B2048449 : Blo 1213424 2048449 := bstep (se 2 (by rfl) ⟨768168, by rfl⟩ : syracuseStep 2048449 = 1536337) B1536337
theorem B3072451 : Blo 1213424 3072451 := bstep (se 1 (by rfl) ⟨2304338, by rfl⟩ : syracuseStep 3072451 = 4608677) B4608677
theorem B2048483 : Blo 1213424 2048483 := bstep (se 1 (by rfl) ⟨1536362, by rfl⟩ : syracuseStep 2048483 = 3072725) B3072725
theorem B4096493 : Blo 1213424 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B6144497 : Blo 1213424 6144497 := bstep (se 2 (by rfl) ⟨2304186, by rfl⟩ : syracuseStep 6144497 = 4608373) B4608373
theorem B4096547 : Blo 1213424 4096547 := bstep (se 1 (by rfl) ⟨3072410, by rfl⟩ : syracuseStep 4096547 = 6144821) B6144821
theorem B3072593 : Blo 1213424 3072593 := bstep (se 2 (by rfl) ⟨1152222, by rfl⟩ : syracuseStep 3072593 = 2304445) B2304445
theorem B2048611 : Blo 1213424 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B9847493 : Blo 1213424 9847493 := bstep (se 4 (by rfl) ⟨923202, by rfl⟩ : syracuseStep 9847493 = 1846405) B1846405
theorem B2048753 : Blo 1213424 2048753 := bstep (se 2 (by rfl) ⟨768282, by rfl⟩ : syracuseStep 2048753 = 1536565) B1536565
theorem B4096817 : Blo 1213424 4096817 := bstep (se 2 (by rfl) ⟨1536306, by rfl⟩ : syracuseStep 4096817 = 3072613) B3072613
theorem B5833549 : Blo 1213424 5833549 := bstep (se 3 (by rfl) ⟨1093790, by rfl⟩ : syracuseStep 5833549 = 2187581) B2187581
theorem B6914929 : Blo 1213424 6914929 := bstep (se 2 (by rfl) ⟨2593098, by rfl⟩ : syracuseStep 6914929 = 5186197) B5186197
theorem B2048881 : Blo 1213424 2048881 := bstep (se 2 (by rfl) ⟨768330, by rfl⟩ : syracuseStep 2048881 = 1536661) B1536661
theorem B49873805 : Blo 1213424 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B2048915 : Blo 1213424 2048915 := bstep (se 1 (by rfl) ⟨1536686, by rfl⟩ : syracuseStep 2048915 = 3073373) B3073373
theorem B1729507 : Blo 1213424 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B1213427 : Blo 1213424 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B1213443 : Blo 1213424 1213443 := bstep (se 1 (by rfl) ⟨910082, by rfl⟩ : syracuseStep 1213443 = 1820165) B1820165
theorem B1213459 : Blo 1213424 1213459 := bstep (se 1 (by rfl) ⟨910094, by rfl⟩ : syracuseStep 1213459 = 1820189) B1820189
theorem B2049043 : Blo 1213424 2049043 := bstep (se 1 (by rfl) ⟨1536782, by rfl⟩ : syracuseStep 2049043 = 3073565) B3073565
theorem B1213475 : Blo 1213424 1213475 := bstep (se 1 (by rfl) ⟨910106, by rfl⟩ : syracuseStep 1213475 = 1820213) B1820213
theorem B1213491 : Blo 1213424 1213491 := bstep (se 1 (by rfl) ⟨910118, by rfl⟩ : syracuseStep 1213491 = 1820237) B1820237
theorem B1213507 : Blo 1213424 1213507 := bstep (se 1 (by rfl) ⟨910130, by rfl⟩ : syracuseStep 1213507 = 1820261) B1820261
theorem B1213523 : Blo 1213424 1213523 := bstep (se 1 (by rfl) ⟨910142, by rfl⟩ : syracuseStep 1213523 = 1820285) B1820285
theorem B1213539 : Blo 1213424 1213539 := bstep (se 1 (by rfl) ⟨910154, by rfl⟩ : syracuseStep 1213539 = 1820309) B1820309
theorem B4613219 : Blo 1213424 4613219 := bstep (se 1 (by rfl) ⟨3459914, by rfl⟩ : syracuseStep 4613219 = 6919829) B6919829
theorem B4613233 : Blo 1213424 4613233 := bstep (se 2 (by rfl) ⟨1729962, by rfl⟩ : syracuseStep 4613233 = 3459925) B3459925
theorem B1213555 : Blo 1213424 1213555 := bstep (se 1 (by rfl) ⟨910166, by rfl⟩ : syracuseStep 1213555 = 1820333) B1820333
theorem B1213571 : Blo 1213424 1213571 := bstep (se 1 (by rfl) ⟨910178, by rfl⟩ : syracuseStep 1213571 = 1820357) B1820357
theorem B1213587 : Blo 1213424 1213587 := bstep (se 1 (by rfl) ⟨910190, by rfl⟩ : syracuseStep 1213587 = 1820381) B1820381
theorem B2049185 : Blo 1213424 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B1213603 : Blo 1213424 1213603 := bstep (se 1 (by rfl) ⟨910202, by rfl⟩ : syracuseStep 1213603 = 1820405) B1820405
theorem B1213619 : Blo 1213424 1213619 := bstep (se 1 (by rfl) ⟨910214, by rfl⟩ : syracuseStep 1213619 = 1820429) B1820429
theorem B1213635 : Blo 1213424 1213635 := bstep (se 1 (by rfl) ⟨910226, by rfl⟩ : syracuseStep 1213635 = 1820453) B1820453
theorem B3695825 : Blo 1213424 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B1213651 : Blo 1213424 1213651 := bstep (se 1 (by rfl) ⟨910238, by rfl⟩ : syracuseStep 1213651 = 1820477) B1820477
theorem B1213667 : Blo 1213424 1213667 := bstep (se 1 (by rfl) ⟨910250, by rfl⟩ : syracuseStep 1213667 = 1820501) B1820501
theorem B3458285 : Blo 1213424 3458285 := bstep (se 3 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 3458285 = 1296857) B1296857
theorem B1213683 : Blo 1213424 1213683 := bstep (se 1 (by rfl) ⟨910262, by rfl⟩ : syracuseStep 1213683 = 1820525) B1820525
theorem B1213699 : Blo 1213424 1213699 := bstep (se 1 (by rfl) ⟨910274, by rfl⟩ : syracuseStep 1213699 = 1820549) B1820549
theorem B1213715 : Blo 1213424 1213715 := bstep (se 1 (by rfl) ⟨910286, by rfl⟩ : syracuseStep 1213715 = 1820573) B1820573
theorem B2049313 : Blo 1213424 2049313 := bstep (se 2 (by rfl) ⟨768492, by rfl⟩ : syracuseStep 2049313 = 1536985) B1536985
theorem B1213731 : Blo 1213424 1213731 := bstep (se 1 (by rfl) ⟨910298, by rfl⟩ : syracuseStep 1213731 = 1820597) B1820597
theorem B1213747 : Blo 1213424 1213747 := bstep (se 1 (by rfl) ⟨910310, by rfl⟩ : syracuseStep 1213747 = 1820621) B1820621
theorem B1213763 : Blo 1213424 1213763 := bstep (se 1 (by rfl) ⟨910322, by rfl⟩ : syracuseStep 1213763 = 1820645) B1820645
theorem B2049347 : Blo 1213424 2049347 := bstep (se 1 (by rfl) ⟨1537010, by rfl⟩ : syracuseStep 2049347 = 3074021) B3074021
theorem B4097357 : Blo 1213424 4097357 := bstep (se 3 (by rfl) ⟨768254, by rfl⟩ : syracuseStep 4097357 = 1536509) B1536509
theorem B1213779 : Blo 1213424 1213779 := bstep (se 1 (by rfl) ⟨910334, by rfl⟩ : syracuseStep 1213779 = 1820669) B1820669
theorem B1213795 : Blo 1213424 1213795 := bstep (se 1 (by rfl) ⟨910346, by rfl⟩ : syracuseStep 1213795 = 1820693) B1820693
theorem B1213811 : Blo 1213424 1213811 := bstep (se 1 (by rfl) ⟨910358, by rfl⟩ : syracuseStep 1213811 = 1820717) B1820717
theorem B1213827 : Blo 1213424 1213827 := bstep (se 1 (by rfl) ⟨910370, by rfl⟩ : syracuseStep 1213827 = 1820741) B1820741
theorem B4097411 : Blo 1213424 4097411 := bstep (se 1 (by rfl) ⟨3073058, by rfl⟩ : syracuseStep 4097411 = 6146117) B6146117
theorem B1213843 : Blo 1213424 1213843 := bstep (se 1 (by rfl) ⟨910382, by rfl⟩ : syracuseStep 1213843 = 1820765) B1820765
theorem B1213859 : Blo 1213424 1213859 := bstep (se 1 (by rfl) ⟨910394, by rfl⟩ : syracuseStep 1213859 = 1820789) B1820789
theorem B2917795 : Blo 1213424 2917795 := bstep (se 1 (by rfl) ⟨2188346, by rfl⟩ : syracuseStep 2917795 = 4376693) B4376693
theorem B3458467 : Blo 1213424 3458467 := bstep (se 1 (by rfl) ⟨2593850, by rfl⟩ : syracuseStep 3458467 = 5187701) B5187701
theorem B1213875 : Blo 1213424 1213875 := bstep (se 1 (by rfl) ⟨910406, by rfl⟩ : syracuseStep 1213875 = 1820813) B1820813
theorem B1213891 : Blo 1213424 1213891 := bstep (se 1 (by rfl) ⟨910418, by rfl⟩ : syracuseStep 1213891 = 1820837) B1820837
theorem B2049475 : Blo 1213424 2049475 := bstep (se 1 (by rfl) ⟨1537106, by rfl⟩ : syracuseStep 2049475 = 3074213) B3074213
theorem B3458513 : Blo 1213424 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B1213907 : Blo 1213424 1213907 := bstep (se 1 (by rfl) ⟨910430, by rfl⟩ : syracuseStep 1213907 = 1820861) B1820861
theorem B1213923 : Blo 1213424 1213923 := bstep (se 1 (by rfl) ⟨910442, by rfl⟩ : syracuseStep 1213923 = 1820885) B1820885
theorem B4007405 : Blo 1213424 4007405 := bstep (se 3 (by rfl) ⟨751388, by rfl⟩ : syracuseStep 4007405 = 1502777) B1502777
theorem B1820147 : Blo 1213424 1820147 := bstep (se 1 (by rfl) ⟨1365110, by rfl⟩ : syracuseStep 1820147 = 2730221) B2730221
theorem B1213939 : Blo 1213424 1213939 := bstep (se 1 (by rfl) ⟨910454, by rfl⟩ : syracuseStep 1213939 = 1820909) B1820909
theorem B1295875 : Blo 1213424 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B1213955 : Blo 1213424 1213955 := bstep (se 1 (by rfl) ⟨910466, by rfl⟩ : syracuseStep 1213955 = 1820933) B1820933
theorem B1820177 : Blo 1213424 1820177 := bstep (se 2 (by rfl) ⟨682566, by rfl⟩ : syracuseStep 1820177 = 1365133) B1365133
theorem B1213971 : Blo 1213424 1213971 := bstep (se 1 (by rfl) ⟨910478, by rfl⟩ : syracuseStep 1213971 = 1820957) B1820957
theorem B1820195 : Blo 1213424 1820195 := bstep (se 1 (by rfl) ⟨1365146, by rfl⟩ : syracuseStep 1820195 = 2730293) B2730293
theorem B1213987 : Blo 1213424 1213987 := bstep (se 1 (by rfl) ⟨910490, by rfl⟩ : syracuseStep 1213987 = 1820981) B1820981
theorem B3073585 : Blo 1213424 3073585 := bstep (se 2 (by rfl) ⟨1152594, by rfl⟩ : syracuseStep 3073585 = 2305189) B2305189
theorem B1214003 : Blo 1213424 1214003 := bstep (se 1 (by rfl) ⟨910502, by rfl⟩ : syracuseStep 1214003 = 1821005) B1821005
theorem B13837877 : Blo 1213424 13837877 := bstep (se 5 (by rfl) ⟨648650, by rfl⟩ : syracuseStep 13837877 = 1297301) B1297301
theorem B1820225 : Blo 1213424 1820225 := bstep (se 2 (by rfl) ⟨682584, by rfl⟩ : syracuseStep 1820225 = 1365169) B1365169
theorem B1214019 : Blo 1213424 1214019 := bstep (se 1 (by rfl) ⟨910514, by rfl⟩ : syracuseStep 1214019 = 1821029) B1821029
theorem B10380869 : Blo 1213424 10380869 := bstep (se 4 (by rfl) ⟨973206, by rfl⟩ : syracuseStep 10380869 = 1946413) B1946413
theorem B2049617 : Blo 1213424 2049617 := bstep (se 2 (by rfl) ⟨768606, by rfl⟩ : syracuseStep 2049617 = 1537213) B1537213
theorem B1820243 : Blo 1213424 1820243 := bstep (se 1 (by rfl) ⟨1365182, by rfl⟩ : syracuseStep 1820243 = 2730365) B2730365
theorem B1214035 : Blo 1213424 1214035 := bstep (se 1 (by rfl) ⟨910526, by rfl⟩ : syracuseStep 1214035 = 1821053) B1821053
theorem B1214051 : Blo 1213424 1214051 := bstep (se 1 (by rfl) ⟨910538, by rfl⟩ : syracuseStep 1214051 = 1821077) B1821077
theorem B1820273 : Blo 1213424 1820273 := bstep (se 2 (by rfl) ⟨682602, by rfl⟩ : syracuseStep 1820273 = 1365205) B1365205
theorem B1214067 : Blo 1213424 1214067 := bstep (se 1 (by rfl) ⟨910550, by rfl⟩ : syracuseStep 1214067 = 1821101) B1821101
theorem B1820291 : Blo 1213424 1820291 := bstep (se 1 (by rfl) ⟨1365218, by rfl⟩ : syracuseStep 1820291 = 2730437) B2730437
theorem B2025091 : Blo 1213424 2025091 := bstep (se 1 (by rfl) ⟨1518818, by rfl⟩ : syracuseStep 2025091 = 3037637) B3037637
theorem B1214083 : Blo 1213424 1214083 := bstep (se 1 (by rfl) ⟨910562, by rfl⟩ : syracuseStep 1214083 = 1821125) B1821125
theorem B2303633 : Blo 1213424 2303633 := bstep (se 2 (by rfl) ⟨863862, by rfl⟩ : syracuseStep 2303633 = 1727725) B1727725
theorem B4097681 : Blo 1213424 4097681 := bstep (se 2 (by rfl) ⟨1536630, by rfl⟩ : syracuseStep 4097681 = 3073261) B3073261
theorem B1214099 : Blo 1213424 1214099 := bstep (se 1 (by rfl) ⟨910574, by rfl⟩ : syracuseStep 1214099 = 1821149) B1821149
theorem B1820321 : Blo 1213424 1820321 := bstep (se 2 (by rfl) ⟨682620, by rfl⟩ : syracuseStep 1820321 = 1365241) B1365241
theorem B1230499 : Blo 1213424 1230499 := bstep (se 1 (by rfl) ⟨922874, by rfl⟩ : syracuseStep 1230499 = 1845749) B1845749
theorem B1214115 : Blo 1213424 1214115 := bstep (se 1 (by rfl) ⟨910586, by rfl⟩ : syracuseStep 1214115 = 1821173) B1821173
theorem B1820339 : Blo 1213424 1820339 := bstep (se 1 (by rfl) ⟨1365254, by rfl⟩ : syracuseStep 1820339 = 2730509) B2730509
theorem B1214131 : Blo 1213424 1214131 := bstep (se 1 (by rfl) ⟨910598, by rfl⟩ : syracuseStep 1214131 = 1821197) B1821197
theorem B1214147 : Blo 1213424 1214147 := bstep (se 1 (by rfl) ⟨910610, by rfl⟩ : syracuseStep 1214147 = 1821221) B1821221
theorem B10372805 : Blo 1213424 10372805 := bstep (se 4 (by rfl) ⟨972450, by rfl⟩ : syracuseStep 10372805 = 1944901) B1944901
theorem B1820369 : Blo 1213424 1820369 := bstep (se 2 (by rfl) ⟨682638, by rfl⟩ : syracuseStep 1820369 = 1365277) B1365277
theorem B2049745 : Blo 1213424 2049745 := bstep (se 2 (by rfl) ⟨768654, by rfl⟩ : syracuseStep 2049745 = 1537309) B1537309
theorem B1214163 : Blo 1213424 1214163 := bstep (se 1 (by rfl) ⟨910622, by rfl⟩ : syracuseStep 1214163 = 1821245) B1821245
theorem B1820387 : Blo 1213424 1820387 := bstep (se 1 (by rfl) ⟨1365290, by rfl⟩ : syracuseStep 1820387 = 2730581) B2730581
theorem B1214179 : Blo 1213424 1214179 := bstep (se 1 (by rfl) ⟨910634, by rfl⟩ : syracuseStep 1214179 = 1821269) B1821269
theorem B1214195 : Blo 1213424 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B2049779 : Blo 1213424 2049779 := bstep (se 1 (by rfl) ⟨1537334, by rfl⟩ : syracuseStep 2049779 = 3074669) B3074669
theorem B1820417 : Blo 1213424 1820417 := bstep (se 2 (by rfl) ⟨682656, by rfl⟩ : syracuseStep 1820417 = 1365313) B1365313
theorem B1214211 : Blo 1213424 1214211 := bstep (se 1 (by rfl) ⟨910658, by rfl⟩ : syracuseStep 1214211 = 1821317) B1821317
theorem B1820435 : Blo 1213424 1820435 := bstep (se 1 (by rfl) ⟨1365326, by rfl⟩ : syracuseStep 1820435 = 2730653) B2730653
theorem B1214227 : Blo 1213424 1214227 := bstep (se 1 (by rfl) ⟨910670, by rfl⟩ : syracuseStep 1214227 = 1821341) B1821341
theorem B1214243 : Blo 1213424 1214243 := bstep (se 1 (by rfl) ⟨910682, by rfl⟩ : syracuseStep 1214243 = 1821365) B1821365
theorem B1820465 : Blo 1213424 1820465 := bstep (se 2 (by rfl) ⟨682674, by rfl⟩ : syracuseStep 1820465 = 1365349) B1365349
theorem B1214259 : Blo 1213424 1214259 := bstep (se 1 (by rfl) ⟨910694, by rfl⟩ : syracuseStep 1214259 = 1821389) B1821389
theorem B1820483 : Blo 1213424 1820483 := bstep (se 1 (by rfl) ⟨1365362, by rfl⟩ : syracuseStep 1820483 = 2730725) B2730725
theorem B1214275 : Blo 1213424 1214275 := bstep (se 1 (by rfl) ⟨910706, by rfl⟩ : syracuseStep 1214275 = 1821413) B1821413
theorem B3073859 : Blo 1213424 3073859 := bstep (se 1 (by rfl) ⟨2305394, by rfl⟩ : syracuseStep 3073859 = 4610789) B4610789
theorem B1214291 : Blo 1213424 1214291 := bstep (se 1 (by rfl) ⟨910718, by rfl⟩ : syracuseStep 1214291 = 1821437) B1821437
theorem B1820513 : Blo 1213424 1820513 := bstep (se 2 (by rfl) ⟨682692, by rfl⟩ : syracuseStep 1820513 = 1365385) B1365385
theorem B1214307 : Blo 1213424 1214307 := bstep (se 1 (by rfl) ⟨910730, by rfl⟩ : syracuseStep 1214307 = 1821461) B1821461
theorem B1820531 : Blo 1213424 1820531 := bstep (se 1 (by rfl) ⟨1365398, by rfl⟩ : syracuseStep 1820531 = 2730797) B2730797
theorem B1214323 : Blo 1213424 1214323 := bstep (se 1 (by rfl) ⟨910742, by rfl⟩ : syracuseStep 1214323 = 1821485) B1821485
theorem B2049907 : Blo 1213424 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B1214339 : Blo 1213424 1214339 := bstep (se 1 (by rfl) ⟨910754, by rfl⟩ : syracuseStep 1214339 = 1821509) B1821509
theorem B3893123 : Blo 1213424 3893123 := bstep (se 1 (by rfl) ⟨2919842, by rfl⟩ : syracuseStep 3893123 = 5839685) B5839685
theorem B1820561 : Blo 1213424 1820561 := bstep (se 2 (by rfl) ⟨682710, by rfl⟩ : syracuseStep 1820561 = 1365421) B1365421
theorem B1214355 : Blo 1213424 1214355 := bstep (se 1 (by rfl) ⟨910766, by rfl⟩ : syracuseStep 1214355 = 1821533) B1821533
theorem B1820579 : Blo 1213424 1820579 := bstep (se 1 (by rfl) ⟨1365434, by rfl⟩ : syracuseStep 1820579 = 2730869) B2730869
theorem B7382947 : Blo 1213424 7382947 := bstep (se 1 (by rfl) ⟨5537210, by rfl⟩ : syracuseStep 7382947 = 11074421) B11074421
theorem B6145955 : Blo 1213424 6145955 := bstep (se 1 (by rfl) ⟨4609466, by rfl⟩ : syracuseStep 6145955 = 9218933) B9218933
theorem B1214371 : Blo 1213424 1214371 := bstep (se 1 (by rfl) ⟨910778, by rfl⟩ : syracuseStep 1214371 = 1821557) B1821557
theorem B1214387 : Blo 1213424 1214387 := bstep (se 1 (by rfl) ⟨910790, by rfl⟩ : syracuseStep 1214387 = 1821581) B1821581
theorem B1820609 : Blo 1213424 1820609 := bstep (se 2 (by rfl) ⟨682728, by rfl⟩ : syracuseStep 1820609 = 1365457) B1365457
theorem B1214403 : Blo 1213424 1214403 := bstep (se 1 (by rfl) ⟨910802, by rfl⟩ : syracuseStep 1214403 = 1821605) B1821605
theorem B1820627 : Blo 1213424 1820627 := bstep (se 1 (by rfl) ⟨1365470, by rfl⟩ : syracuseStep 1820627 = 2730941) B2730941
theorem B1214419 : Blo 1213424 1214419 := bstep (se 1 (by rfl) ⟨910814, by rfl⟩ : syracuseStep 1214419 = 1821629) B1821629
theorem B1214435 : Blo 1213424 1214435 := bstep (se 1 (by rfl) ⟨910826, by rfl⟩ : syracuseStep 1214435 = 1821653) B1821653
theorem B1820657 : Blo 1213424 1820657 := bstep (se 2 (by rfl) ⟨682746, by rfl⟩ : syracuseStep 1820657 = 1365493) B1365493
theorem B1214451 : Blo 1213424 1214451 := bstep (se 1 (by rfl) ⟨910838, by rfl⟩ : syracuseStep 1214451 = 1821677) B1821677
theorem B2050049 : Blo 1213424 2050049 := bstep (se 2 (by rfl) ⟨768768, by rfl⟩ : syracuseStep 2050049 = 1537537) B1537537
theorem B1820675 : Blo 1213424 1820675 := bstep (se 1 (by rfl) ⟨1365506, by rfl⟩ : syracuseStep 1820675 = 2731013) B2731013
theorem B3074051 : Blo 1213424 3074051 := bstep (se 1 (by rfl) ⟨2305538, by rfl⟩ : syracuseStep 3074051 = 4611077) B4611077
theorem B1214467 : Blo 1213424 1214467 := bstep (se 1 (by rfl) ⟨910850, by rfl⟩ : syracuseStep 1214467 = 1821701) B1821701
theorem B1214483 : Blo 1213424 1214483 := bstep (se 1 (by rfl) ⟨910862, by rfl⟩ : syracuseStep 1214483 = 1821725) B1821725
theorem B1820705 : Blo 1213424 1820705 := bstep (se 2 (by rfl) ⟨682764, by rfl⟩ : syracuseStep 1820705 = 1365529) B1365529
theorem B2304035 : Blo 1213424 2304035 := bstep (se 1 (by rfl) ⟨1728026, by rfl⟩ : syracuseStep 2304035 = 3456053) B3456053
theorem B1214499 : Blo 1213424 1214499 := bstep (se 1 (by rfl) ⟨910874, by rfl⟩ : syracuseStep 1214499 = 1821749) B1821749
theorem B2770993 : Blo 1213424 2770993 := bstep (se 2 (by rfl) ⟨1039122, by rfl⟩ : syracuseStep 2770993 = 2078245) B2078245
theorem B1820723 : Blo 1213424 1820723 := bstep (se 1 (by rfl) ⟨1365542, by rfl⟩ : syracuseStep 1820723 = 2731085) B2731085
theorem B1214515 : Blo 1213424 1214515 := bstep (se 1 (by rfl) ⟨910886, by rfl⟩ : syracuseStep 1214515 = 1821773) B1821773
theorem B1214531 : Blo 1213424 1214531 := bstep (se 1 (by rfl) ⟨910898, by rfl⟩ : syracuseStep 1214531 = 1821797) B1821797
theorem B7784525 : Blo 1213424 7784525 := bstep (se 3 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 7784525 = 2919197) B2919197
theorem B1820753 : Blo 1213424 1820753 := bstep (se 2 (by rfl) ⟨682782, by rfl⟩ : syracuseStep 1820753 = 1365565) B1365565
theorem B1214547 : Blo 1213424 1214547 := bstep (se 1 (by rfl) ⟨910910, by rfl⟩ : syracuseStep 1214547 = 1821821) B1821821
theorem B1845347 : Blo 1213424 1845347 := bstep (se 1 (by rfl) ⟨1384010, by rfl⟩ : syracuseStep 1845347 = 2768021) B2768021
theorem B1820771 : Blo 1213424 1820771 := bstep (se 1 (by rfl) ⟨1365578, by rfl⟩ : syracuseStep 1820771 = 2731157) B2731157
theorem B1214563 : Blo 1213424 1214563 := bstep (se 1 (by rfl) ⟨910922, by rfl⟩ : syracuseStep 1214563 = 1821845) B1821845
theorem B22161521 : Blo 1213424 22161521 := bstep (se 2 (by rfl) ⟨8310570, by rfl⟩ : syracuseStep 22161521 = 16621141) B16621141
theorem B1214579 : Blo 1213424 1214579 := bstep (se 1 (by rfl) ⟨910934, by rfl⟩ : syracuseStep 1214579 = 1821869) B1821869
theorem B1820801 : Blo 1213424 1820801 := bstep (se 2 (by rfl) ⟨682800, by rfl⟩ : syracuseStep 1820801 = 1365601) B1365601
theorem B2050177 : Blo 1213424 2050177 := bstep (se 2 (by rfl) ⟨768816, by rfl⟩ : syracuseStep 2050177 = 1537633) B1537633
theorem B1214595 : Blo 1213424 1214595 := bstep (se 1 (by rfl) ⟨910946, by rfl⟩ : syracuseStep 1214595 = 1821893) B1821893
theorem B1558643 : Blo 1213424 1558643 := bstep (se 1 (by rfl) ⟨1168982, by rfl⟩ : syracuseStep 1558643 = 2337965) B2337965
theorem B14772365 : Blo 1213424 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B1820819 : Blo 1213424 1820819 := bstep (se 1 (by rfl) ⟨1365614, by rfl⟩ : syracuseStep 1820819 = 2731229) B2731229
theorem B1214611 : Blo 1213424 1214611 := bstep (se 1 (by rfl) ⟨910958, by rfl⟩ : syracuseStep 1214611 = 1821917) B1821917
theorem B1214627 : Blo 1213424 1214627 := bstep (se 1 (by rfl) ⟨910970, by rfl⟩ : syracuseStep 1214627 = 1821941) B1821941
theorem B2050211 : Blo 1213424 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B4098221 : Blo 1213424 4098221 := bstep (se 3 (by rfl) ⟨768416, by rfl⟩ : syracuseStep 4098221 = 1536833) B1536833
theorem B1820849 : Blo 1213424 1820849 := bstep (se 2 (by rfl) ⟨682818, by rfl⟩ : syracuseStep 1820849 = 1365637) B1365637
theorem B1214643 : Blo 1213424 1214643 := bstep (se 1 (by rfl) ⟨910982, by rfl⟩ : syracuseStep 1214643 = 1821965) B1821965
theorem B1820867 : Blo 1213424 1820867 := bstep (se 1 (by rfl) ⟨1365650, by rfl⟩ : syracuseStep 1820867 = 2731301) B2731301
theorem B1214659 : Blo 1213424 1214659 := bstep (se 1 (by rfl) ⟨910994, by rfl⟩ : syracuseStep 1214659 = 1821989) B1821989
theorem B23668933 : Blo 1213424 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B1214675 : Blo 1213424 1214675 := bstep (se 1 (by rfl) ⟨911006, by rfl⟩ : syracuseStep 1214675 = 1822013) B1822013
theorem B1820897 : Blo 1213424 1820897 := bstep (se 2 (by rfl) ⟨682836, by rfl⟩ : syracuseStep 1820897 = 1365673) B1365673
theorem B4098275 : Blo 1213424 4098275 := bstep (se 1 (by rfl) ⟨3073706, by rfl⟩ : syracuseStep 4098275 = 6147413) B6147413
theorem B1214691 : Blo 1213424 1214691 := bstep (se 1 (by rfl) ⟨911018, by rfl⟩ : syracuseStep 1214691 = 1822037) B1822037
theorem B10381553 : Blo 1213424 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B1820915 : Blo 1213424 1820915 := bstep (se 1 (by rfl) ⟨1365686, by rfl⟩ : syracuseStep 1820915 = 2731373) B2731373
theorem B1214707 : Blo 1213424 1214707 := bstep (se 1 (by rfl) ⟨911030, by rfl⟩ : syracuseStep 1214707 = 1822061) B1822061
theorem B1214723 : Blo 1213424 1214723 := bstep (se 1 (by rfl) ⟨911042, by rfl⟩ : syracuseStep 1214723 = 1822085) B1822085
theorem B2730257 : Blo 1213424 2730257 := bstep (se 2 (by rfl) ⟨1023846, by rfl⟩ : syracuseStep 2730257 = 2047693) B2047693
theorem B1820945 : Blo 1213424 1820945 := bstep (se 2 (by rfl) ⟨682854, by rfl⟩ : syracuseStep 1820945 = 1365709) B1365709
theorem B1214739 : Blo 1213424 1214739 := bstep (se 1 (by rfl) ⟨911054, by rfl⟩ : syracuseStep 1214739 = 1822109) B1822109
theorem B2730275 : Blo 1213424 2730275 := bstep (se 1 (by rfl) ⟨2047706, by rfl⟩ : syracuseStep 2730275 = 4095413) B4095413
theorem B1820963 : Blo 1213424 1820963 := bstep (se 1 (by rfl) ⟨1365722, by rfl⟩ : syracuseStep 1820963 = 2731445) B2731445
theorem B6916387 : Blo 1213424 6916387 := bstep (se 1 (by rfl) ⟨5187290, by rfl⟩ : syracuseStep 6916387 = 10374581) B10374581
theorem B1214755 : Blo 1213424 1214755 := bstep (se 1 (by rfl) ⟨911066, by rfl⟩ : syracuseStep 1214755 = 1822133) B1822133
theorem B2050339 : Blo 1213424 2050339 := bstep (se 1 (by rfl) ⟨1537754, by rfl⟩ : syracuseStep 2050339 = 3075509) B3075509
theorem B1214771 : Blo 1213424 1214771 := bstep (se 1 (by rfl) ⟨911078, by rfl⟩ : syracuseStep 1214771 = 1822157) B1822157
theorem B1820993 : Blo 1213424 1820993 := bstep (se 2 (by rfl) ⟨682872, by rfl⟩ : syracuseStep 1820993 = 1365745) B1365745
theorem B1214787 : Blo 1213424 1214787 := bstep (se 1 (by rfl) ⟨911090, by rfl⟩ : syracuseStep 1214787 = 1822181) B1822181
theorem B1821011 : Blo 1213424 1821011 := bstep (se 1 (by rfl) ⟨1365758, by rfl⟩ : syracuseStep 1821011 = 2731517) B2731517
theorem B1214803 : Blo 1213424 1214803 := bstep (se 1 (by rfl) ⟨911102, by rfl⟩ : syracuseStep 1214803 = 1822205) B1822205
theorem B1214819 : Blo 1213424 1214819 := bstep (se 1 (by rfl) ⟨911114, by rfl⟩ : syracuseStep 1214819 = 1822229) B1822229
theorem B1821041 : Blo 1213424 1821041 := bstep (se 2 (by rfl) ⟨682890, by rfl⟩ : syracuseStep 1821041 = 1365781) B1365781
theorem B1214835 : Blo 1213424 1214835 := bstep (se 1 (by rfl) ⟨911126, by rfl⟩ : syracuseStep 1214835 = 1822253) B1822253
theorem B1821059 : Blo 1213424 1821059 := bstep (se 1 (by rfl) ⟨1365794, by rfl⟩ : syracuseStep 1821059 = 2731589) B2731589
theorem B1214851 : Blo 1213424 1214851 := bstep (se 1 (by rfl) ⟨911138, by rfl⟩ : syracuseStep 1214851 = 1822277) B1822277
theorem B5540237 : Blo 1213424 5540237 := bstep (se 3 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 5540237 = 2077589) B2077589
theorem B1214867 : Blo 1213424 1214867 := bstep (se 1 (by rfl) ⟨911150, by rfl⟩ : syracuseStep 1214867 = 1822301) B1822301
theorem B1821089 : Blo 1213424 1821089 := bstep (se 2 (by rfl) ⟨682908, by rfl⟩ : syracuseStep 1821089 = 1365817) B1365817
theorem B1214883 : Blo 1213424 1214883 := bstep (se 1 (by rfl) ⟨911162, by rfl⟩ : syracuseStep 1214883 = 1822325) B1822325
theorem B2050481 : Blo 1213424 2050481 := bstep (se 2 (by rfl) ⟨768930, by rfl⟩ : syracuseStep 2050481 = 1537861) B1537861
theorem B1821107 : Blo 1213424 1821107 := bstep (se 1 (by rfl) ⟨1365830, by rfl⟩ : syracuseStep 1821107 = 2731661) B2731661
theorem B1214899 : Blo 1213424 1214899 := bstep (se 1 (by rfl) ⟨911174, by rfl⟩ : syracuseStep 1214899 = 1822349) B1822349
theorem B1214915 : Blo 1213424 1214915 := bstep (se 1 (by rfl) ⟨911186, by rfl⟩ : syracuseStep 1214915 = 1822373) B1822373
theorem B1821137 : Blo 1213424 1821137 := bstep (se 2 (by rfl) ⟨682926, by rfl⟩ : syracuseStep 1821137 = 1365853) B1365853
theorem B1214931 : Blo 1213424 1214931 := bstep (se 1 (by rfl) ⟨911198, by rfl⟩ : syracuseStep 1214931 = 1822397) B1822397
theorem B1821155 : Blo 1213424 1821155 := bstep (se 1 (by rfl) ⟨1365866, by rfl⟩ : syracuseStep 1821155 = 2731733) B2731733
theorem B1214947 : Blo 1213424 1214947 := bstep (se 1 (by rfl) ⟨911210, by rfl⟩ : syracuseStep 1214947 = 1822421) B1822421
theorem B21047779 : Blo 1213424 21047779 := bstep (se 1 (by rfl) ⟨15785834, by rfl⟩ : syracuseStep 21047779 = 31571669) B31571669
theorem B4098545 : Blo 1213424 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B1214963 : Blo 1213424 1214963 := bstep (se 1 (by rfl) ⟨911222, by rfl⟩ : syracuseStep 1214963 = 1822445) B1822445
theorem B1821185 : Blo 1213424 1821185 := bstep (se 2 (by rfl) ⟨682944, by rfl⟩ : syracuseStep 1821185 = 1365889) B1365889
theorem B1214979 : Blo 1213424 1214979 := bstep (se 1 (by rfl) ⟨911234, by rfl⟩ : syracuseStep 1214979 = 1822469) B1822469
theorem B16198157 : Blo 1213424 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B1821203 : Blo 1213424 1821203 := bstep (se 1 (by rfl) ⟨1365902, by rfl⟩ : syracuseStep 1821203 = 2731805) B2731805
theorem B1214995 : Blo 1213424 1214995 := bstep (se 1 (by rfl) ⟨911246, by rfl⟩ : syracuseStep 1214995 = 1822493) B1822493
theorem B1215011 : Blo 1213424 1215011 := bstep (se 1 (by rfl) ⟨911258, by rfl⟩ : syracuseStep 1215011 = 1822517) B1822517
theorem B4614691 : Blo 1213424 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B2730545 : Blo 1213424 2730545 := bstep (se 2 (by rfl) ⟨1023954, by rfl⟩ : syracuseStep 2730545 = 2047909) B2047909
theorem B1821233 : Blo 1213424 1821233 := bstep (se 2 (by rfl) ⟨682962, by rfl⟩ : syracuseStep 1821233 = 1365925) B1365925
theorem B1215027 : Blo 1213424 1215027 := bstep (se 1 (by rfl) ⟨911270, by rfl⟩ : syracuseStep 1215027 = 1822541) B1822541
theorem B2050609 : Blo 1213424 2050609 := bstep (se 2 (by rfl) ⟨768978, by rfl⟩ : syracuseStep 2050609 = 1537957) B1537957
theorem B2730563 : Blo 1213424 2730563 := bstep (se 1 (by rfl) ⟨2047922, by rfl⟩ : syracuseStep 2730563 = 4095845) B4095845
theorem B1821251 : Blo 1213424 1821251 := bstep (se 1 (by rfl) ⟨1365938, by rfl⟩ : syracuseStep 1821251 = 2731877) B2731877
theorem B1215043 : Blo 1213424 1215043 := bstep (se 1 (by rfl) ⟨911282, by rfl⟩ : syracuseStep 1215043 = 1822565) B1822565
theorem B1215059 : Blo 1213424 1215059 := bstep (se 1 (by rfl) ⟨911294, by rfl⟩ : syracuseStep 1215059 = 1822589) B1822589
theorem B2050643 : Blo 1213424 2050643 := bstep (se 1 (by rfl) ⟨1537982, by rfl⟩ : syracuseStep 2050643 = 3075965) B3075965
theorem B1821281 : Blo 1213424 1821281 := bstep (se 2 (by rfl) ⟨682980, by rfl⟩ : syracuseStep 1821281 = 1365961) B1365961
theorem B1215075 : Blo 1213424 1215075 := bstep (se 1 (by rfl) ⟨911306, by rfl⟩ : syracuseStep 1215075 = 1822613) B1822613
theorem B1821299 : Blo 1213424 1821299 := bstep (se 1 (by rfl) ⟨1365974, by rfl⟩ : syracuseStep 1821299 = 2731949) B2731949
theorem B1215091 : Blo 1213424 1215091 := bstep (se 1 (by rfl) ⟨911318, by rfl⟩ : syracuseStep 1215091 = 1822637) B1822637
theorem B1215107 : Blo 1213424 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B1944209 : Blo 1213424 1944209 := bstep (se 2 (by rfl) ⟨729078, by rfl⟩ : syracuseStep 1944209 = 1458157) B1458157
theorem B1821329 : Blo 1213424 1821329 := bstep (se 2 (by rfl) ⟨682998, by rfl⟩ : syracuseStep 1821329 = 1365997) B1365997
theorem B1215123 : Blo 1213424 1215123 := bstep (se 1 (by rfl) ⟨911342, by rfl⟩ : syracuseStep 1215123 = 1822685) B1822685
theorem B1821347 : Blo 1213424 1821347 := bstep (se 1 (by rfl) ⟨1366010, by rfl⟩ : syracuseStep 1821347 = 2732021) B2732021
theorem B1215139 : Blo 1213424 1215139 := bstep (se 1 (by rfl) ⟨911354, by rfl⟩ : syracuseStep 1215139 = 1822709) B1822709
theorem B1215155 : Blo 1213424 1215155 := bstep (se 1 (by rfl) ⟨911366, by rfl⟩ : syracuseStep 1215155 = 1822733) B1822733
theorem B1821377 : Blo 1213424 1821377 := bstep (se 2 (by rfl) ⟨683016, by rfl⟩ : syracuseStep 1821377 = 1366033) B1366033
theorem B1215171 : Blo 1213424 1215171 := bstep (se 1 (by rfl) ⟨911378, by rfl⟩ : syracuseStep 1215171 = 1822757) B1822757
theorem B2190019 : Blo 1213424 2190019 := bstep (se 1 (by rfl) ⟨1642514, by rfl⟩ : syracuseStep 2190019 = 3285029) B3285029
theorem B6146765 : Blo 1213424 6146765 := bstep (se 3 (by rfl) ⟨1152518, by rfl⟩ : syracuseStep 6146765 = 2305037) B2305037
theorem B1821395 : Blo 1213424 1821395 := bstep (se 1 (by rfl) ⟨1366046, by rfl⟩ : syracuseStep 1821395 = 2732093) B2732093
theorem B1215187 : Blo 1213424 1215187 := bstep (se 1 (by rfl) ⟨911390, by rfl⟩ : syracuseStep 1215187 = 1822781) B1822781
theorem B2050771 : Blo 1213424 2050771 := bstep (se 1 (by rfl) ⟨1538078, by rfl⟩ : syracuseStep 2050771 = 3076157) B3076157
theorem B1215203 : Blo 1213424 1215203 := bstep (se 1 (by rfl) ⟨911402, by rfl⟩ : syracuseStep 1215203 = 1822805) B1822805
theorem B1821425 : Blo 1213424 1821425 := bstep (se 2 (by rfl) ⟨683034, by rfl⟩ : syracuseStep 1821425 = 1366069) B1366069
theorem B1297139 : Blo 1213424 1297139 := bstep (se 1 (by rfl) ⟨972854, by rfl⟩ : syracuseStep 1297139 = 1945709) B1945709
theorem B1215219 : Blo 1213424 1215219 := bstep (se 1 (by rfl) ⟨911414, by rfl⟩ : syracuseStep 1215219 = 1822829) B1822829
theorem B1821443 : Blo 1213424 1821443 := bstep (se 1 (by rfl) ⟨1366082, by rfl⟩ : syracuseStep 1821443 = 2732165) B2732165
theorem B1215235 : Blo 1213424 1215235 := bstep (se 1 (by rfl) ⟨911426, by rfl⟩ : syracuseStep 1215235 = 1822853) B1822853
theorem B1215251 : Blo 1213424 1215251 := bstep (se 1 (by rfl) ⟨911438, by rfl⟩ : syracuseStep 1215251 = 1822877) B1822877
theorem B1821473 : Blo 1213424 1821473 := bstep (se 2 (by rfl) ⟨683052, by rfl⟩ : syracuseStep 1821473 = 1366105) B1366105
theorem B1215267 : Blo 1213424 1215267 := bstep (se 1 (by rfl) ⟨911450, by rfl⟩ : syracuseStep 1215267 = 1822901) B1822901
theorem B6916913 : Blo 1213424 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B1821491 : Blo 1213424 1821491 := bstep (se 1 (by rfl) ⟨1366118, by rfl⟩ : syracuseStep 1821491 = 2732237) B2732237
theorem B1215283 : Blo 1213424 1215283 := bstep (se 1 (by rfl) ⟨911462, by rfl⟩ : syracuseStep 1215283 = 1822925) B1822925
theorem B1215299 : Blo 1213424 1215299 := bstep (se 1 (by rfl) ⟨911474, by rfl⟩ : syracuseStep 1215299 = 1822949) B1822949
theorem B7777093 : Blo 1213424 7777093 := bstep (se 4 (by rfl) ⟨729102, by rfl⟩ : syracuseStep 7777093 = 1458205) B1458205
theorem B2730833 : Blo 1213424 2730833 := bstep (se 2 (by rfl) ⟨1024062, by rfl⟩ : syracuseStep 2730833 = 2048125) B2048125
theorem B1821521 : Blo 1213424 1821521 := bstep (se 2 (by rfl) ⟨683070, by rfl⟩ : syracuseStep 1821521 = 1366141) B1366141
theorem B1215315 : Blo 1213424 1215315 := bstep (se 1 (by rfl) ⟨911486, by rfl⟩ : syracuseStep 1215315 = 1822973) B1822973
theorem B2050913 : Blo 1213424 2050913 := bstep (se 2 (by rfl) ⟨769092, by rfl⟩ : syracuseStep 2050913 = 1538185) B1538185
theorem B2730851 : Blo 1213424 2730851 := bstep (se 1 (by rfl) ⟨2048138, by rfl⟩ : syracuseStep 2730851 = 4096277) B4096277
theorem B1821539 : Blo 1213424 1821539 := bstep (se 1 (by rfl) ⟨1366154, by rfl⟩ : syracuseStep 1821539 = 2732309) B2732309
theorem B1215331 : Blo 1213424 1215331 := bstep (se 1 (by rfl) ⟨911498, by rfl⟩ : syracuseStep 1215331 = 1822997) B1822997
theorem B1215347 : Blo 1213424 1215347 := bstep (se 1 (by rfl) ⟨911510, by rfl⟩ : syracuseStep 1215347 = 1823021) B1823021
theorem B1821569 : Blo 1213424 1821569 := bstep (se 2 (by rfl) ⟨683088, by rfl⟩ : syracuseStep 1821569 = 1366177) B1366177
theorem B3459971 : Blo 1213424 3459971 := bstep (se 1 (by rfl) ⟨2594978, by rfl⟩ : syracuseStep 3459971 = 5189957) B5189957
theorem B1215363 : Blo 1213424 1215363 := bstep (se 1 (by rfl) ⟨911522, by rfl⟩ : syracuseStep 1215363 = 1823045) B1823045
theorem B1821587 : Blo 1213424 1821587 := bstep (se 1 (by rfl) ⟨1366190, by rfl⟩ : syracuseStep 1821587 = 2732381) B2732381
theorem B1215379 : Blo 1213424 1215379 := bstep (se 1 (by rfl) ⟨911534, by rfl⟩ : syracuseStep 1215379 = 1823069) B1823069
theorem B2304931 : Blo 1213424 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B1215395 : Blo 1213424 1215395 := bstep (se 1 (by rfl) ⟨911546, by rfl⟩ : syracuseStep 1215395 = 1823093) B1823093
theorem B1821617 : Blo 1213424 1821617 := bstep (se 2 (by rfl) ⟨683106, by rfl⟩ : syracuseStep 1821617 = 1366213) B1366213
theorem B3074993 : Blo 1213424 3074993 := bstep (se 2 (by rfl) ⟨1153122, by rfl⟩ : syracuseStep 3074993 = 2306245) B2306245
theorem B1215411 : Blo 1213424 1215411 := bstep (se 1 (by rfl) ⟨911558, by rfl⟩ : syracuseStep 1215411 = 1823117) B1823117
theorem B1821635 : Blo 1213424 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B1821665 : Blo 1213424 1821665 := bstep (se 2 (by rfl) ⟨683124, by rfl⟩ : syracuseStep 1821665 = 1366249) B1366249
theorem B3075043 : Blo 1213424 3075043 := bstep (se 1 (by rfl) ⟨2306282, by rfl⟩ : syracuseStep 3075043 = 4612565) B4612565
theorem B1821683 : Blo 1213424 1821683 := bstep (se 1 (by rfl) ⟨1366262, by rfl⟩ : syracuseStep 1821683 = 2732525) B2732525
theorem B4099085 : Blo 1213424 4099085 := bstep (se 3 (by rfl) ⟨768578, by rfl⟩ : syracuseStep 4099085 = 1537157) B1537157
theorem B1821713 : Blo 1213424 1821713 := bstep (se 2 (by rfl) ⟨683142, by rfl⟩ : syracuseStep 1821713 = 1366285) B1366285
theorem B1821731 : Blo 1213424 1821731 := bstep (se 1 (by rfl) ⟨1366298, by rfl⟩ : syracuseStep 1821731 = 2732597) B2732597
theorem B5188643 : Blo 1213424 5188643 := bstep (se 1 (by rfl) ⟨3891482, by rfl⟩ : syracuseStep 5188643 = 7782965) B7782965
theorem B1821761 : Blo 1213424 1821761 := bstep (se 2 (by rfl) ⟨683160, by rfl⟩ : syracuseStep 1821761 = 1366321) B1366321
theorem B2305091 : Blo 1213424 2305091 := bstep (se 1 (by rfl) ⟨1728818, by rfl⟩ : syracuseStep 2305091 = 3457637) B3457637
theorem B4099139 : Blo 1213424 4099139 := bstep (se 1 (by rfl) ⟨3074354, by rfl⟩ : syracuseStep 4099139 = 6148709) B6148709
theorem B2919505 : Blo 1213424 2919505 := bstep (se 2 (by rfl) ⟨1094814, by rfl⟩ : syracuseStep 2919505 = 2189629) B2189629
theorem B1821779 : Blo 1213424 1821779 := bstep (se 1 (by rfl) ⟨1366334, by rfl⟩ : syracuseStep 1821779 = 2732669) B2732669
theorem B2731121 : Blo 1213424 2731121 := bstep (se 2 (by rfl) ⟨1024170, by rfl⟩ : syracuseStep 2731121 = 2048341) B2048341
theorem B1821809 : Blo 1213424 1821809 := bstep (se 2 (by rfl) ⟨683178, by rfl⟩ : syracuseStep 1821809 = 1366357) B1366357
theorem B3075185 : Blo 1213424 3075185 := bstep (se 2 (by rfl) ⟨1153194, by rfl⟩ : syracuseStep 3075185 = 2306389) B2306389
theorem B2075777 : Blo 1213424 2075777 := bstep (se 2 (by rfl) ⟨778416, by rfl⟩ : syracuseStep 2075777 = 1556833) B1556833
theorem B2731139 : Blo 1213424 2731139 := bstep (se 1 (by rfl) ⟨2048354, by rfl⟩ : syracuseStep 2731139 = 4096709) B4096709
theorem B1821827 : Blo 1213424 1821827 := bstep (se 1 (by rfl) ⟨1366370, by rfl⟩ : syracuseStep 1821827 = 2732741) B2732741
theorem B1821857 : Blo 1213424 1821857 := bstep (se 2 (by rfl) ⟨683196, by rfl⟩ : syracuseStep 1821857 = 1366393) B1366393
theorem B1821875 : Blo 1213424 1821875 := bstep (se 1 (by rfl) ⟨1366406, by rfl⟩ : syracuseStep 1821875 = 2732813) B2732813
theorem B1821905 : Blo 1213424 1821905 := bstep (se 2 (by rfl) ⟨683214, by rfl⟩ : syracuseStep 1821905 = 1366429) B1366429
theorem B1821923 : Blo 1213424 1821923 := bstep (se 1 (by rfl) ⟨1366442, by rfl⟩ : syracuseStep 1821923 = 2732885) B2732885
theorem B1821953 : Blo 1213424 1821953 := bstep (se 2 (by rfl) ⟨683232, by rfl⟩ : syracuseStep 1821953 = 1366465) B1366465
theorem B1821971 : Blo 1213424 1821971 := bstep (se 1 (by rfl) ⟨1366478, by rfl⟩ : syracuseStep 1821971 = 2732957) B2732957
theorem B7384355 : Blo 1213424 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B1822001 : Blo 1213424 1822001 := bstep (se 2 (by rfl) ⟨683250, by rfl⟩ : syracuseStep 1822001 = 1366501) B1366501
theorem B1822019 : Blo 1213424 1822019 := bstep (se 1 (by rfl) ⟨1366514, by rfl⟩ : syracuseStep 1822019 = 2733029) B2733029
theorem B4099409 : Blo 1213424 4099409 := bstep (se 2 (by rfl) ⟨1537278, by rfl⟩ : syracuseStep 4099409 = 3074557) B3074557
theorem B1641811 : Blo 1213424 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B1822049 : Blo 1213424 1822049 := bstep (se 2 (by rfl) ⟨683268, by rfl⟩ : syracuseStep 1822049 = 1366537) B1366537
theorem B1822067 : Blo 1213424 1822067 := bstep (se 1 (by rfl) ⟨1366550, by rfl⟩ : syracuseStep 1822067 = 2733101) B2733101
theorem B2731409 : Blo 1213424 2731409 := bstep (se 2 (by rfl) ⟨1024278, by rfl⟩ : syracuseStep 2731409 = 2048557) B2048557
theorem B1822097 : Blo 1213424 1822097 := bstep (se 2 (by rfl) ⟨683286, by rfl⟩ : syracuseStep 1822097 = 1366573) B1366573
theorem B2731427 : Blo 1213424 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B1822115 : Blo 1213424 1822115 := bstep (se 1 (by rfl) ⟨1366586, by rfl⟩ : syracuseStep 1822115 = 2733173) B2733173
theorem B1822145 : Blo 1213424 1822145 := bstep (se 2 (by rfl) ⟨683304, by rfl⟩ : syracuseStep 1822145 = 1366609) B1366609
theorem B1945043 : Blo 1213424 1945043 := bstep (se 1 (by rfl) ⟨1458782, by rfl⟩ : syracuseStep 1945043 = 2917565) B2917565
theorem B1822163 : Blo 1213424 1822163 := bstep (se 1 (by rfl) ⟨1366622, by rfl⟩ : syracuseStep 1822163 = 2733245) B2733245
theorem B1297891 : Blo 1213424 1297891 := bstep (se 1 (by rfl) ⟨973418, by rfl⟩ : syracuseStep 1297891 = 1946837) B1946837
theorem B4435441 : Blo 1213424 4435441 := bstep (se 2 (by rfl) ⟨1663290, by rfl⟩ : syracuseStep 4435441 = 3326581) B3326581
theorem B1822193 : Blo 1213424 1822193 := bstep (se 2 (by rfl) ⟨683322, by rfl⟩ : syracuseStep 1822193 = 1366645) B1366645
theorem B1945075 : Blo 1213424 1945075 := bstep (se 1 (by rfl) ⟨1458806, by rfl⟩ : syracuseStep 1945075 = 2917613) B2917613
theorem B1822211 : Blo 1213424 1822211 := bstep (se 1 (by rfl) ⟨1366658, by rfl⟩ : syracuseStep 1822211 = 2733317) B2733317
theorem B4926989 : Blo 1213424 4926989 := bstep (se 3 (by rfl) ⟨923810, by rfl⟩ : syracuseStep 4926989 = 1847621) B1847621
theorem B1822241 : Blo 1213424 1822241 := bstep (se 2 (by rfl) ⟨683340, by rfl⟩ : syracuseStep 1822241 = 1366681) B1366681
theorem B1822259 : Blo 1213424 1822259 := bstep (se 1 (by rfl) ⟨1366694, by rfl⟩ : syracuseStep 1822259 = 2733389) B2733389
theorem B1822289 : Blo 1213424 1822289 := bstep (se 2 (by rfl) ⟨683358, by rfl⟩ : syracuseStep 1822289 = 1366717) B1366717
theorem B1822307 : Blo 1213424 1822307 := bstep (se 1 (by rfl) ⟨1366730, by rfl⟩ : syracuseStep 1822307 = 2733461) B2733461
theorem B4157027 : Blo 1213424 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B1822337 : Blo 1213424 1822337 := bstep (se 2 (by rfl) ⟨683376, by rfl⟩ : syracuseStep 1822337 = 1366753) B1366753
theorem B1822355 : Blo 1213424 1822355 := bstep (se 1 (by rfl) ⟨1366766, by rfl⟩ : syracuseStep 1822355 = 2733533) B2733533
theorem B2731697 : Blo 1213424 2731697 := bstep (se 2 (by rfl) ⟨1024386, by rfl⟩ : syracuseStep 2731697 = 2048773) B2048773
theorem B1822385 : Blo 1213424 1822385 := bstep (se 2 (by rfl) ⟨683394, by rfl⟩ : syracuseStep 1822385 = 1366789) B1366789
theorem B2731715 : Blo 1213424 2731715 := bstep (se 1 (by rfl) ⟨2048786, by rfl⟩ : syracuseStep 2731715 = 4097573) B4097573
theorem B1822403 : Blo 1213424 1822403 := bstep (se 1 (by rfl) ⟨1366802, by rfl⟩ : syracuseStep 1822403 = 2733605) B2733605
theorem B1822433 : Blo 1213424 1822433 := bstep (se 2 (by rfl) ⟨683412, by rfl⟩ : syracuseStep 1822433 = 1366825) B1366825
theorem B17493731 : Blo 1213424 17493731 := bstep (se 1 (by rfl) ⟨13120298, by rfl⟩ : syracuseStep 17493731 = 26240597) B26240597
theorem B1822451 : Blo 1213424 1822451 := bstep (se 1 (by rfl) ⟨1366838, by rfl⟩ : syracuseStep 1822451 = 2733677) B2733677
theorem B1642243 : Blo 1213424 1642243 := bstep (se 1 (by rfl) ⟨1231682, by rfl⟩ : syracuseStep 1642243 = 2463365) B2463365
theorem B1822481 : Blo 1213424 1822481 := bstep (se 2 (by rfl) ⟨683430, by rfl⟩ : syracuseStep 1822481 = 1366861) B1366861
theorem B1822499 : Blo 1213424 1822499 := bstep (se 1 (by rfl) ⟨1366874, by rfl⟩ : syracuseStep 1822499 = 2733749) B2733749
theorem B1822529 : Blo 1213424 1822529 := bstep (se 2 (by rfl) ⟨683448, by rfl⟩ : syracuseStep 1822529 = 1366897) B1366897
theorem B1822547 : Blo 1213424 1822547 := bstep (se 1 (by rfl) ⟨1366910, by rfl⟩ : syracuseStep 1822547 = 2733821) B2733821
theorem B4099949 : Blo 1213424 4099949 := bstep (se 3 (by rfl) ⟨768740, by rfl⟩ : syracuseStep 4099949 = 1537481) B1537481
theorem B22146929 : Blo 1213424 22146929 := bstep (se 2 (by rfl) ⟨8305098, by rfl⟩ : syracuseStep 22146929 = 16610197) B16610197
theorem B1822577 : Blo 1213424 1822577 := bstep (se 2 (by rfl) ⟨683466, by rfl⟩ : syracuseStep 1822577 = 1366933) B1366933
theorem B1822595 : Blo 1213424 1822595 := bstep (se 1 (by rfl) ⟨1366946, by rfl⟩ : syracuseStep 1822595 = 2733893) B2733893
theorem B1822625 : Blo 1213424 1822625 := bstep (se 2 (by rfl) ⟨683484, by rfl⟩ : syracuseStep 1822625 = 1366969) B1366969
theorem B4100003 : Blo 1213424 4100003 := bstep (se 1 (by rfl) ⟨3075002, by rfl⟩ : syracuseStep 4100003 = 6150005) B6150005
theorem B1822643 : Blo 1213424 1822643 := bstep (se 1 (by rfl) ⟨1366982, by rfl⟩ : syracuseStep 1822643 = 2733965) B2733965
theorem B8753093 : Blo 1213424 8753093 := bstep (se 4 (by rfl) ⟨820602, by rfl⟩ : syracuseStep 8753093 = 1641205) B1641205
theorem B2731985 : Blo 1213424 2731985 := bstep (se 2 (by rfl) ⟨1024494, by rfl⟩ : syracuseStep 2731985 = 2048989) B2048989
theorem B1822673 : Blo 1213424 1822673 := bstep (se 2 (by rfl) ⟨683502, by rfl⟩ : syracuseStep 1822673 = 1367005) B1367005
theorem B2732003 : Blo 1213424 2732003 := bstep (se 1 (by rfl) ⟨2049002, by rfl⟩ : syracuseStep 2732003 = 4098005) B4098005
theorem B1871843 : Blo 1213424 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B1822691 : Blo 1213424 1822691 := bstep (se 1 (by rfl) ⟨1367018, by rfl⟩ : syracuseStep 1822691 = 2734037) B2734037
theorem B3280877 : Blo 1213424 3280877 := bstep (se 3 (by rfl) ⟨615164, by rfl⟩ : syracuseStep 3280877 = 1230329) B1230329
theorem B2076673 : Blo 1213424 2076673 := bstep (se 2 (by rfl) ⟨778752, by rfl⟩ : syracuseStep 2076673 = 1557505) B1557505
theorem B1822721 : Blo 1213424 1822721 := bstep (se 2 (by rfl) ⟨683520, by rfl⟩ : syracuseStep 1822721 = 1367041) B1367041
theorem B1822739 : Blo 1213424 1822739 := bstep (se 1 (by rfl) ⟨1367054, by rfl⟩ : syracuseStep 1822739 = 2734109) B2734109
theorem B1822769 : Blo 1213424 1822769 := bstep (se 2 (by rfl) ⟨683538, by rfl⟩ : syracuseStep 1822769 = 1367077) B1367077
theorem B1822787 : Blo 1213424 1822787 := bstep (se 1 (by rfl) ⟨1367090, by rfl⟩ : syracuseStep 1822787 = 2734181) B2734181
theorem B3076177 : Blo 1213424 3076177 := bstep (se 2 (by rfl) ⟨1153566, by rfl⟩ : syracuseStep 3076177 = 2307133) B2307133
theorem B1822817 : Blo 1213424 1822817 := bstep (se 2 (by rfl) ⟨683556, by rfl⟩ : syracuseStep 1822817 = 1367113) B1367113
theorem B2306161 : Blo 1213424 2306161 := bstep (se 2 (by rfl) ⟨864810, by rfl⟩ : syracuseStep 2306161 = 1729621) B1729621
theorem B1822835 : Blo 1213424 1822835 := bstep (se 1 (by rfl) ⟨1367126, by rfl⟩ : syracuseStep 1822835 = 2734253) B2734253
theorem B1822865 : Blo 1213424 1822865 := bstep (se 2 (by rfl) ⟨683574, by rfl⟩ : syracuseStep 1822865 = 1367149) B1367149
theorem B1822883 : Blo 1213424 1822883 := bstep (se 1 (by rfl) ⟨1367162, by rfl⟩ : syracuseStep 1822883 = 2734325) B2734325
theorem B4100273 : Blo 1213424 4100273 := bstep (se 2 (by rfl) ⟨1537602, by rfl⟩ : syracuseStep 4100273 = 3075205) B3075205
theorem B1822913 : Blo 1213424 1822913 := bstep (se 2 (by rfl) ⟨683592, by rfl⟩ : syracuseStep 1822913 = 1367185) B1367185
theorem B20754629 : Blo 1213424 20754629 := bstep (se 4 (by rfl) ⟨1945746, by rfl⟩ : syracuseStep 20754629 = 3891493) B3891493
theorem B1822931 : Blo 1213424 1822931 := bstep (se 1 (by rfl) ⟨1367198, by rfl⟩ : syracuseStep 1822931 = 2734397) B2734397
theorem B6918371 : Blo 1213424 6918371 := bstep (se 1 (by rfl) ⟨5188778, by rfl⟩ : syracuseStep 6918371 = 10377557) B10377557
theorem B2732273 : Blo 1213424 2732273 := bstep (se 2 (by rfl) ⟨1024602, by rfl⟩ : syracuseStep 2732273 = 2049205) B2049205
theorem B1822961 : Blo 1213424 1822961 := bstep (se 2 (by rfl) ⟨683610, by rfl⟩ : syracuseStep 1822961 = 1367221) B1367221
theorem B2732291 : Blo 1213424 2732291 := bstep (se 1 (by rfl) ⟨2049218, by rfl⟩ : syracuseStep 2732291 = 4098437) B4098437
theorem B1822979 : Blo 1213424 1822979 := bstep (se 1 (by rfl) ⟨1367234, by rfl⟩ : syracuseStep 1822979 = 2734469) B2734469
theorem B6230285 : Blo 1213424 6230285 := bstep (se 3 (by rfl) ⟨1168178, by rfl⟩ : syracuseStep 6230285 = 2336357) B2336357
theorem B1823009 : Blo 1213424 1823009 := bstep (se 2 (by rfl) ⟨683628, by rfl⟩ : syracuseStep 1823009 = 1367257) B1367257
theorem B1823027 : Blo 1213424 1823027 := bstep (se 1 (by rfl) ⟨1367270, by rfl⟩ : syracuseStep 1823027 = 2734541) B2734541
theorem B1823057 : Blo 1213424 1823057 := bstep (se 2 (by rfl) ⟨683646, by rfl⟩ : syracuseStep 1823057 = 1367293) B1367293
theorem B3690851 : Blo 1213424 3690851 := bstep (se 1 (by rfl) ⟨2768138, by rfl⟩ : syracuseStep 3690851 = 5536277) B5536277
theorem B1823075 : Blo 1213424 1823075 := bstep (se 1 (by rfl) ⟨1367306, by rfl⟩ : syracuseStep 1823075 = 2734613) B2734613
theorem B3076451 : Blo 1213424 3076451 := bstep (se 1 (by rfl) ⟨2307338, by rfl⟩ : syracuseStep 3076451 = 4614677) B4614677
theorem B1823105 : Blo 1213424 1823105 := bstep (se 2 (by rfl) ⟨683664, by rfl⟩ : syracuseStep 1823105 = 1367329) B1367329
theorem B1536403 : Blo 1213424 1536403 := bstep (se 1 (by rfl) ⟨1152302, by rfl⟩ : syracuseStep 1536403 = 2304605) B2304605
theorem B1946003 : Blo 1213424 1946003 := bstep (se 1 (by rfl) ⟨1459502, by rfl⟩ : syracuseStep 1946003 = 2919005) B2919005
theorem B1823123 : Blo 1213424 1823123 := bstep (se 1 (by rfl) ⟨1367342, by rfl⟩ : syracuseStep 1823123 = 2734685) B2734685
theorem B1847761 : Blo 1213424 1847761 := bstep (se 2 (by rfl) ⟨692910, by rfl⟩ : syracuseStep 1847761 = 1385821) B1385821
theorem B1946081 : Blo 1213424 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B10367473 : Blo 1213424 10367473 := bstep (se 2 (by rfl) ⟨3887802, by rfl⟩ : syracuseStep 10367473 = 7775605) B7775605
theorem B1536499 : Blo 1213424 1536499 := bstep (se 1 (by rfl) ⟨1152374, by rfl⟩ : syracuseStep 1536499 = 2304749) B2304749
theorem B2732561 : Blo 1213424 2732561 := bstep (se 2 (by rfl) ⟨1024710, by rfl⟩ : syracuseStep 2732561 = 2049421) B2049421
theorem B2732579 : Blo 1213424 2732579 := bstep (se 1 (by rfl) ⟨2049434, by rfl⟩ : syracuseStep 2732579 = 4098869) B4098869
theorem B1946305 : Blo 1213424 1946305 := bstep (se 2 (by rfl) ⟨729864, by rfl⟩ : syracuseStep 1946305 = 1459729) B1459729
theorem B2593475 : Blo 1213424 2593475 := bstep (se 1 (by rfl) ⟨1945106, by rfl⟩ : syracuseStep 2593475 = 3890213) B3890213
theorem B4100813 : Blo 1213424 4100813 := bstep (se 3 (by rfl) ⟨768902, by rfl⟩ : syracuseStep 4100813 = 1537805) B1537805
theorem B4100867 : Blo 1213424 4100867 := bstep (se 1 (by rfl) ⟨3075650, by rfl⟩ : syracuseStep 4100867 = 6151301) B6151301
theorem B9220877 : Blo 1213424 9220877 := bstep (se 3 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 9220877 = 3457829) B3457829
theorem B2732849 : Blo 1213424 2732849 := bstep (se 2 (by rfl) ⟨1024818, by rfl⟩ : syracuseStep 2732849 = 2049637) B2049637
theorem B2732867 : Blo 1213424 2732867 := bstep (se 1 (by rfl) ⟨2049650, by rfl⟩ : syracuseStep 2732867 = 4099301) B4099301
theorem B4608845 : Blo 1213424 4608845 := bstep (se 3 (by rfl) ⟨864158, by rfl⟩ : syracuseStep 4608845 = 1728317) B1728317
theorem B1536995 : Blo 1213424 1536995 := bstep (se 1 (by rfl) ⟨1152746, by rfl⟩ : syracuseStep 1536995 = 2305493) B2305493
theorem B5190641 : Blo 1213424 5190641 := bstep (se 2 (by rfl) ⟨1946490, by rfl⟩ : syracuseStep 5190641 = 3892981) B3892981
theorem B4101137 : Blo 1213424 4101137 := bstep (se 2 (by rfl) ⟨1537926, by rfl⟩ : syracuseStep 4101137 = 3075853) B3075853
theorem B52524085 : Blo 1213424 52524085 := bstep (se 5 (by rfl) ⟨2462066, by rfl⟩ : syracuseStep 52524085 = 4924133) B4924133
theorem B2733137 : Blo 1213424 2733137 := bstep (se 2 (by rfl) ⟨1024926, by rfl⟩ : syracuseStep 2733137 = 2049853) B2049853
theorem B2733155 : Blo 1213424 2733155 := bstep (se 1 (by rfl) ⟨2049866, by rfl⟩ : syracuseStep 2733155 = 4099733) B4099733
theorem B2593937 : Blo 1213424 2593937 := bstep (se 2 (by rfl) ⟨972726, by rfl⟩ : syracuseStep 2593937 = 1945453) B1945453
theorem B2307217 : Blo 1213424 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B1365187 : Blo 1213424 1365187 := bstep (se 1 (by rfl) ⟨1023890, by rfl⟩ : syracuseStep 1365187 = 2047781) B2047781
theorem B2077987 : Blo 1213424 2077987 := bstep (se 1 (by rfl) ⟨1558490, by rfl⟩ : syracuseStep 2077987 = 3116981) B3116981
theorem B1365331 : Blo 1213424 1365331 := bstep (se 1 (by rfl) ⟨1023998, by rfl⟩ : syracuseStep 1365331 = 2047997) B2047997
theorem B2733425 : Blo 1213424 2733425 := bstep (se 2 (by rfl) ⟨1025034, by rfl⟩ : syracuseStep 2733425 = 2050069) B2050069
theorem B2733443 : Blo 1213424 2733443 := bstep (se 1 (by rfl) ⟨2050082, by rfl⟩ : syracuseStep 2733443 = 4100165) B4100165
theorem B11679173 : Blo 1213424 11679173 := bstep (se 4 (by rfl) ⟨1094922, by rfl⟩ : syracuseStep 11679173 = 2189845) B2189845
theorem B1365475 : Blo 1213424 1365475 := bstep (se 1 (by rfl) ⟨1024106, by rfl⟩ : syracuseStep 1365475 = 2048213) B2048213
theorem B8304113 : Blo 1213424 8304113 := bstep (se 2 (by rfl) ⟨3114042, by rfl⟩ : syracuseStep 8304113 = 6228085) B6228085
theorem B4101677 : Blo 1213424 4101677 := bstep (se 3 (by rfl) ⟨769064, by rfl⟩ : syracuseStep 4101677 = 1538129) B1538129
theorem B6149681 : Blo 1213424 6149681 := bstep (se 2 (by rfl) ⟨2306130, by rfl⟩ : syracuseStep 6149681 = 4612261) B4612261
theorem B4101731 : Blo 1213424 4101731 := bstep (se 1 (by rfl) ⟨3076298, by rfl⟩ : syracuseStep 4101731 = 6152597) B6152597
theorem B4609649 : Blo 1213424 4609649 := bstep (se 2 (by rfl) ⟨1728618, by rfl⟩ : syracuseStep 4609649 = 3457237) B3457237
theorem B1365619 : Blo 1213424 1365619 := bstep (se 1 (by rfl) ⟨1024214, by rfl⟩ : syracuseStep 1365619 = 2048429) B2048429
theorem B2733713 : Blo 1213424 2733713 := bstep (se 2 (by rfl) ⟨1025142, by rfl⟩ : syracuseStep 2733713 = 2050285) B2050285
theorem B1537699 : Blo 1213424 1537699 := bstep (se 1 (by rfl) ⟨1153274, by rfl⟩ : syracuseStep 1537699 = 2306549) B2306549
theorem B2733731 : Blo 1213424 2733731 := bstep (se 1 (by rfl) ⟨2050298, by rfl⟩ : syracuseStep 2733731 = 4100597) B4100597
theorem B3888881 : Blo 1213424 3888881 := bstep (se 2 (by rfl) ⟨1458330, by rfl⟩ : syracuseStep 3888881 = 2916661) B2916661
theorem B1365763 : Blo 1213424 1365763 := bstep (se 1 (by rfl) ⟨1024322, by rfl⟩ : syracuseStep 1365763 = 2048645) B2048645
theorem B1537795 : Blo 1213424 1537795 := bstep (se 1 (by rfl) ⟨1153346, by rfl⟩ : syracuseStep 1537795 = 2306693) B2306693
theorem B3888931 : Blo 1213424 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B4102001 : Blo 1213424 4102001 := bstep (se 2 (by rfl) ⟨1538250, by rfl⟩ : syracuseStep 4102001 = 3076501) B3076501
theorem B1365907 : Blo 1213424 1365907 := bstep (se 1 (by rfl) ⟨1024430, by rfl⟩ : syracuseStep 1365907 = 2048861) B2048861
theorem B2734001 : Blo 1213424 2734001 := bstep (se 2 (by rfl) ⟨1025250, by rfl⟩ : syracuseStep 2734001 = 2050501) B2050501
theorem B2734019 : Blo 1213424 2734019 := bstep (se 1 (by rfl) ⟨2050514, by rfl⟩ : syracuseStep 2734019 = 4101029) B4101029
theorem B6912013 : Blo 1213424 6912013 := bstep (se 3 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 6912013 = 2592005) B2592005
theorem B1366051 : Blo 1213424 1366051 := bstep (se 1 (by rfl) ⟨1024538, by rfl⟩ : syracuseStep 1366051 = 2049077) B2049077
theorem B6920261 : Blo 1213424 6920261 := bstep (se 4 (by rfl) ⟨648774, by rfl⟩ : syracuseStep 6920261 = 1297549) B1297549
theorem B1366195 : Blo 1213424 1366195 := bstep (se 1 (by rfl) ⟨1024646, by rfl⟩ : syracuseStep 1366195 = 2049293) B2049293
theorem B2734289 : Blo 1213424 2734289 := bstep (se 2 (by rfl) ⟨1025358, by rfl⟩ : syracuseStep 2734289 = 2050717) B2050717
theorem B2734307 : Blo 1213424 2734307 := bstep (se 1 (by rfl) ⟨2050730, by rfl⟩ : syracuseStep 2734307 = 4101461) B4101461
theorem B4610317 : Blo 1213424 4610317 := bstep (se 3 (by rfl) ⟨864434, by rfl⟩ : syracuseStep 4610317 = 1728869) B1728869
theorem B1366339 : Blo 1213424 1366339 := bstep (se 1 (by rfl) ⟨1024754, by rfl⟩ : syracuseStep 1366339 = 2049509) B2049509
theorem B3996035 : Blo 1213424 3996035 := bstep (se 1 (by rfl) ⟨2997026, by rfl⟩ : syracuseStep 3996035 = 5994053) B5994053
theorem B2595235 : Blo 1213424 2595235 := bstep (se 1 (by rfl) ⟨1946426, by rfl⟩ : syracuseStep 2595235 = 3892853) B3892853
theorem B1366483 : Blo 1213424 1366483 := bstep (se 1 (by rfl) ⟨1024862, by rfl⟩ : syracuseStep 1366483 = 2049725) B2049725
theorem B2734577 : Blo 1213424 2734577 := bstep (se 2 (by rfl) ⟨1025466, by rfl⟩ : syracuseStep 2734577 = 2050933) B2050933
theorem B2734595 : Blo 1213424 2734595 := bstep (se 1 (by rfl) ⟨2050946, by rfl⟩ : syracuseStep 2734595 = 4101893) B4101893
theorem B7387661 : Blo 1213424 7387661 := bstep (se 3 (by rfl) ⟨1385186, by rfl⟩ : syracuseStep 7387661 = 2770373) B2770373
theorem B1366627 : Blo 1213424 1366627 := bstep (se 1 (by rfl) ⟨1024970, by rfl⟩ : syracuseStep 1366627 = 2049941) B2049941
theorem B3455597 : Blo 1213424 3455597 := bstep (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) B1295849
theorem B3889777 : Blo 1213424 3889777 := bstep (se 2 (by rfl) ⟨1458666, by rfl⟩ : syracuseStep 3889777 = 2917333) B2917333
theorem B2595491 : Blo 1213424 2595491 := bstep (se 1 (by rfl) ⟨1946618, by rfl⟩ : syracuseStep 2595491 = 3893237) B3893237
theorem B2767555 : Blo 1213424 2767555 := bstep (se 1 (by rfl) ⟨2075666, by rfl⟩ : syracuseStep 2767555 = 4151333) B4151333
theorem B1366771 : Blo 1213424 1366771 := bstep (se 1 (by rfl) ⟨1025078, by rfl⟩ : syracuseStep 1366771 = 2050157) B2050157
theorem B5184269 : Blo 1213424 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B3455779 : Blo 1213424 3455779 := bstep (se 1 (by rfl) ⟨2591834, by rfl⟩ : syracuseStep 3455779 = 5183669) B5183669
theorem B28449589 : Blo 1213424 28449589 := bstep (se 5 (by rfl) ⟨1333574, by rfl⟩ : syracuseStep 28449589 = 2667149) B2667149
theorem B3324739 : Blo 1213424 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B2767729 : Blo 1213424 2767729 := bstep (se 2 (by rfl) ⟨1037898, by rfl⟩ : syracuseStep 2767729 = 2075797) B2075797
theorem B1366915 : Blo 1213424 1366915 := bstep (se 1 (by rfl) ⟨1025186, by rfl⟩ : syracuseStep 1366915 = 2050373) B2050373
theorem B3455939 : Blo 1213424 3455939 := bstep (se 1 (by rfl) ⟨2591954, by rfl⟩ : syracuseStep 3455939 = 5183909) B5183909
theorem B3505123 : Blo 1213424 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B6151139 : Blo 1213424 6151139 := bstep (se 1 (by rfl) ⟨4613354, by rfl⟩ : syracuseStep 6151139 = 9226709) B9226709
theorem B10517489 : Blo 1213424 10517489 := bstep (se 2 (by rfl) ⟨3944058, by rfl⟩ : syracuseStep 10517489 = 7888117) B7888117
theorem B1367059 : Blo 1213424 1367059 := bstep (se 1 (by rfl) ⟨1025294, by rfl⟩ : syracuseStep 1367059 = 2050589) B2050589
theorem B4611107 : Blo 1213424 4611107 := bstep (se 1 (by rfl) ⟨3458330, by rfl⟩ : syracuseStep 4611107 = 6916661) B6916661
theorem B3693613 : Blo 1213424 3693613 := bstep (se 3 (by rfl) ⟨692552, by rfl⟩ : syracuseStep 3693613 = 1385105) B1385105
theorem B9215045 : Blo 1213424 9215045 := bstep (se 4 (by rfl) ⟨863910, by rfl⟩ : syracuseStep 9215045 = 1727821) B1727821
theorem B3284077 : Blo 1213424 3284077 := bstep (se 3 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 3284077 = 1231529) B1231529
theorem B1367203 : Blo 1213424 1367203 := bstep (se 1 (by rfl) ⟨1025402, by rfl⟩ : syracuseStep 1367203 = 2050805) B2050805
theorem B1367347 : Blo 1213424 1367347 := bstep (se 1 (by rfl) ⟨1025510, by rfl⟩ : syracuseStep 1367347 = 2051021) B2051021
theorem B1580419 : Blo 1213424 1580419 := bstep (se 1 (by rfl) ⟨1185314, by rfl⟩ : syracuseStep 1580419 = 2370629) B2370629
theorem B4210093 : Blo 1213424 4210093 := bstep (se 3 (by rfl) ⟨789392, by rfl⟩ : syracuseStep 4210093 = 1578785) B1578785
theorem B1728049 : Blo 1213424 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B15572533 : Blo 1213424 15572533 := bstep (se 5 (by rfl) ⟨729962, by rfl⟩ : syracuseStep 15572533 = 1459925) B1459925
theorem B2915921 : Blo 1213424 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B9223793 : Blo 1213424 9223793 := bstep (se 2 (by rfl) ⟨3458922, by rfl⟩ : syracuseStep 9223793 = 6917845) B6917845
theorem B4095629 : Blo 1213424 4095629 := bstep (se 3 (by rfl) ⟨767930, by rfl⟩ : syracuseStep 4095629 = 1535861) B1535861
theorem B1498771 : Blo 1213424 1498771 := bstep (se 1 (by rfl) ⟨1124078, by rfl⟩ : syracuseStep 1498771 = 2248157) B2248157
theorem B1728163 : Blo 1213424 1728163 := bstep (se 1 (by rfl) ⟨1296122, by rfl⟩ : syracuseStep 1728163 = 2592245) B2592245
theorem B7782065 : Blo 1213424 7782065 := bstep (se 2 (by rfl) ⟨2918274, by rfl⟩ : syracuseStep 7782065 = 5836549) B5836549
theorem B4611761 : Blo 1213424 4611761 := bstep (se 2 (by rfl) ⟨1729410, by rfl⟩ : syracuseStep 4611761 = 3458821) B3458821
theorem B4095683 : Blo 1213424 4095683 := bstep (se 1 (by rfl) ⟨3071762, by rfl⟩ : syracuseStep 4095683 = 6143525) B6143525
theorem B2186947 : Blo 1213424 2186947 := bstep (se 1 (by rfl) ⟨1640210, by rfl⟩ : syracuseStep 2186947 = 3280421) B3280421
theorem B2047747 : Blo 1213424 2047747 := bstep (se 1 (by rfl) ⟨1535810, by rfl⟩ : syracuseStep 2047747 = 3071621) B3071621
theorem B6151949 : Blo 1213424 6151949 := bstep (se 3 (by rfl) ⟨1153490, by rfl⟩ : syracuseStep 6151949 = 2306981) B2306981
theorem B1752931 : Blo 1213424 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B2047889 : Blo 1213424 2047889 := bstep (se 2 (by rfl) ⟨767958, by rfl⟩ : syracuseStep 2047889 = 1535917) B1535917
theorem B6913997 : Blo 1213424 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B4095953 : Blo 1213424 4095953 := bstep (se 2 (by rfl) ⟨1535982, by rfl⟩ : syracuseStep 4095953 = 3071965) B3071965
theorem B3457009 : Blo 1213424 3457009 := bstep (se 2 (by rfl) ⟨1296378, by rfl⟩ : syracuseStep 3457009 = 2592757) B2592757
theorem B2768897 : Blo 1213424 2768897 := bstep (se 2 (by rfl) ⟨1038336, by rfl⟩ : syracuseStep 2768897 = 2076673) B2076673
theorem B9216017 : Blo 1213424 9216017 := bstep (se 2 (by rfl) ⟨3456006, by rfl⟩ : syracuseStep 9216017 = 6912013) B6912013
theorem B3694657 : Blo 1213424 3694657 := bstep (se 2 (by rfl) ⟨1385496, by rfl⟩ : syracuseStep 3694657 = 2770993) B2770993
theorem B13836419 : Blo 1213424 13836419 := bstep (se 1 (by rfl) ⟨10377314, by rfl⟩ : syracuseStep 13836419 = 20754629) B20754629
theorem B4612247 : Blo 1213424 4612247 := bstep (se 1 (by rfl) ⟨3459185, by rfl⟩ : syracuseStep 4612247 = 6918371) B6918371
theorem B4153523 : Blo 1213424 4153523 := bstep (se 1 (by rfl) ⟨3115142, by rfl⟩ : syracuseStep 4153523 = 6230285) B6230285
theorem B2048267 : Blo 1213424 2048267 := bstep (se 1 (by rfl) ⟨1536200, by rfl⟩ : syracuseStep 2048267 = 3072401) B3072401
theorem B4096331 : Blo 1213424 4096331 := bstep (se 1 (by rfl) ⟨3072248, by rfl⟩ : syracuseStep 4096331 = 6144497) B6144497
theorem B2048395 : Blo 1213424 2048395 := bstep (se 1 (by rfl) ⟨1536296, by rfl⟩ : syracuseStep 2048395 = 3072593) B3072593
theorem B1728983 : Blo 1213424 1728983 := bstep (se 1 (by rfl) ⟨1296737, by rfl⟩ : syracuseStep 1728983 = 2593475) B2593475
theorem B2163161 : Blo 1213424 2163161 := bstep (se 2 (by rfl) ⟨811185, by rfl⟩ : syracuseStep 2163161 = 1622371) B1622371
theorem B2048537 : Blo 1213424 2048537 := bstep (se 2 (by rfl) ⟨768201, by rfl⟩ : syracuseStep 2048537 = 1536403) B1536403
theorem B9855533 : Blo 1213424 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B3072563 : Blo 1213424 3072563 := bstep (se 1 (by rfl) ⟨2304422, by rfl⟩ : syracuseStep 3072563 = 4608845) B4608845
theorem B8749633 : Blo 1213424 8749633 := bstep (se 2 (by rfl) ⟨3281112, by rfl⟩ : syracuseStep 8749633 = 6562225) B6562225
theorem B4096601 : Blo 1213424 4096601 := bstep (se 2 (by rfl) ⟨1536225, by rfl⟩ : syracuseStep 4096601 = 3072451) B3072451
theorem B2048665 : Blo 1213424 2048665 := bstep (se 2 (by rfl) ⟨768249, by rfl⟩ : syracuseStep 2048665 = 1536499) B1536499
theorem B6152921 : Blo 1213424 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B1729291 : Blo 1213424 1729291 := bstep (se 1 (by rfl) ⟨1296968, by rfl⟩ : syracuseStep 1729291 = 2593937) B2593937
theorem B5186369 : Blo 1213424 5186369 := bstep (se 2 (by rfl) ⟨1944888, by rfl⟩ : syracuseStep 5186369 = 3889777) B3889777
theorem B2671603 : Blo 1213424 2671603 := bstep (se 1 (by rfl) ⟨2003702, by rfl⟩ : syracuseStep 2671603 = 4007405) B4007405
theorem B1213431 : Blo 1213424 1213431 := bstep (se 1 (by rfl) ⟨910073, by rfl⟩ : syracuseStep 1213431 = 1820147) B1820147
theorem B1213451 : Blo 1213424 1213451 := bstep (se 1 (by rfl) ⟨910088, by rfl⟩ : syracuseStep 1213451 = 1820177) B1820177
theorem B1213463 : Blo 1213424 1213463 := bstep (se 1 (by rfl) ⟨910097, by rfl⟩ : syracuseStep 1213463 = 1820195) B1820195
theorem B9225251 : Blo 1213424 9225251 := bstep (se 1 (by rfl) ⟨6918938, by rfl⟩ : syracuseStep 9225251 = 13837877) B13837877
theorem B1213483 : Blo 1213424 1213483 := bstep (se 1 (by rfl) ⟨910112, by rfl⟩ : syracuseStep 1213483 = 1820225) B1820225
theorem B1213495 : Blo 1213424 1213495 := bstep (se 1 (by rfl) ⟨910121, by rfl⟩ : syracuseStep 1213495 = 1820243) B1820243
theorem B1213515 : Blo 1213424 1213515 := bstep (se 1 (by rfl) ⟨910136, by rfl⟩ : syracuseStep 1213515 = 1820273) B1820273
theorem B3073099 : Blo 1213424 3073099 := bstep (se 1 (by rfl) ⟨2304824, by rfl⟩ : syracuseStep 3073099 = 4609649) B4609649
theorem B1213527 : Blo 1213424 1213527 := bstep (se 1 (by rfl) ⟨910145, by rfl⟩ : syracuseStep 1213527 = 1820291) B1820291
theorem B4432985 : Blo 1213424 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B1213547 : Blo 1213424 1213547 := bstep (se 1 (by rfl) ⟨910160, by rfl⟩ : syracuseStep 1213547 = 1820321) B1820321
theorem B1213559 : Blo 1213424 1213559 := bstep (se 1 (by rfl) ⟨910169, by rfl⟩ : syracuseStep 1213559 = 1820339) B1820339
theorem B6915203 : Blo 1213424 6915203 := bstep (se 1 (by rfl) ⟨5186402, by rfl⟩ : syracuseStep 6915203 = 10372805) B10372805
theorem B1213579 : Blo 1213424 1213579 := bstep (se 1 (by rfl) ⟨910184, by rfl⟩ : syracuseStep 1213579 = 1820369) B1820369
theorem B1213591 : Blo 1213424 1213591 := bstep (se 1 (by rfl) ⟨910193, by rfl⟩ : syracuseStep 1213591 = 1820387) B1820387
theorem B1213611 : Blo 1213424 1213611 := bstep (se 1 (by rfl) ⟨910208, by rfl⟩ : syracuseStep 1213611 = 1820417) B1820417
theorem B1213623 : Blo 1213424 1213623 := bstep (se 1 (by rfl) ⟨910217, by rfl⟩ : syracuseStep 1213623 = 1820435) B1820435
theorem B1213643 : Blo 1213424 1213643 := bstep (se 1 (by rfl) ⟨910232, by rfl⟩ : syracuseStep 1213643 = 1820465) B1820465
theorem B1213655 : Blo 1213424 1213655 := bstep (se 1 (by rfl) ⟨910241, by rfl⟩ : syracuseStep 1213655 = 1820483) B1820483
theorem B2049239 : Blo 1213424 2049239 := bstep (se 1 (by rfl) ⟨1536929, by rfl⟩ : syracuseStep 2049239 = 3073859) B3073859
theorem B3073241 : Blo 1213424 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B1213675 : Blo 1213424 1213675 := bstep (se 1 (by rfl) ⟨910256, by rfl⟩ : syracuseStep 1213675 = 1820513) B1820513
theorem B1213687 : Blo 1213424 1213687 := bstep (se 1 (by rfl) ⟨910265, by rfl⟩ : syracuseStep 1213687 = 1820531) B1820531
theorem B1213707 : Blo 1213424 1213707 := bstep (se 1 (by rfl) ⟨910280, by rfl⟩ : syracuseStep 1213707 = 1820561) B1820561
theorem B1213719 : Blo 1213424 1213719 := bstep (se 1 (by rfl) ⟨910289, by rfl⟩ : syracuseStep 1213719 = 1820579) B1820579
theorem B4097303 : Blo 1213424 4097303 := bstep (se 1 (by rfl) ⟨3072977, by rfl⟩ : syracuseStep 4097303 = 6145955) B6145955
theorem B1213739 : Blo 1213424 1213739 := bstep (se 1 (by rfl) ⟨910304, by rfl⟩ : syracuseStep 1213739 = 1820609) B1820609
theorem B1213751 : Blo 1213424 1213751 := bstep (se 1 (by rfl) ⟨910313, by rfl⟩ : syracuseStep 1213751 = 1820627) B1820627
theorem B1213771 : Blo 1213424 1213771 := bstep (se 1 (by rfl) ⟨910328, by rfl⟩ : syracuseStep 1213771 = 1820657) B1820657
theorem B1213783 : Blo 1213424 1213783 := bstep (se 1 (by rfl) ⟨910337, by rfl⟩ : syracuseStep 1213783 = 1820675) B1820675
theorem B2049367 : Blo 1213424 2049367 := bstep (se 1 (by rfl) ⟨1537025, by rfl⟩ : syracuseStep 2049367 = 3074051) B3074051
theorem B1213803 : Blo 1213424 1213803 := bstep (se 1 (by rfl) ⟨910352, by rfl⟩ : syracuseStep 1213803 = 1820705) B1820705
theorem B1213815 : Blo 1213424 1213815 := bstep (se 1 (by rfl) ⟨910361, by rfl⟩ : syracuseStep 1213815 = 1820723) B1820723
theorem B4613507 : Blo 1213424 4613507 := bstep (se 1 (by rfl) ⟨3460130, by rfl⟩ : syracuseStep 4613507 = 6920261) B6920261
theorem B1213835 : Blo 1213424 1213835 := bstep (se 1 (by rfl) ⟨910376, by rfl⟩ : syracuseStep 1213835 = 1820753) B1820753
theorem B4924817 : Blo 1213424 4924817 := bstep (se 2 (by rfl) ⟨1846806, by rfl⟩ : syracuseStep 4924817 = 3693613) B3693613
theorem B1213847 : Blo 1213424 1213847 := bstep (se 1 (by rfl) ⟨910385, by rfl⟩ : syracuseStep 1213847 = 1820771) B1820771
theorem B1213867 : Blo 1213424 1213867 := bstep (se 1 (by rfl) ⟨910400, by rfl⟩ : syracuseStep 1213867 = 1820801) B1820801
theorem B9848243 : Blo 1213424 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B1213879 : Blo 1213424 1213879 := bstep (se 1 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 1213879 = 1820819) B1820819
theorem B3892673 : Blo 1213424 3892673 := bstep (se 2 (by rfl) ⟨1459752, by rfl⟩ : syracuseStep 3892673 = 2919505) B2919505
theorem B1213899 : Blo 1213424 1213899 := bstep (se 1 (by rfl) ⟨910424, by rfl⟩ : syracuseStep 1213899 = 1820849) B1820849
theorem B1213911 : Blo 1213424 1213911 := bstep (se 1 (by rfl) ⟨910433, by rfl⟩ : syracuseStep 1213911 = 1820867) B1820867
theorem B1213931 : Blo 1213424 1213931 := bstep (se 1 (by rfl) ⟨910448, by rfl⟩ : syracuseStep 1213931 = 1820897) B1820897
theorem B1213943 : Blo 1213424 1213943 := bstep (se 1 (by rfl) ⟨910457, by rfl⟩ : syracuseStep 1213943 = 1820915) B1820915
theorem B1820171 : Blo 1213424 1820171 := bstep (se 1 (by rfl) ⟨1365128, by rfl⟩ : syracuseStep 1820171 = 2730257) B2730257
theorem B1213963 : Blo 1213424 1213963 := bstep (se 1 (by rfl) ⟨910472, by rfl⟩ : syracuseStep 1213963 = 1820945) B1820945
theorem B1820183 : Blo 1213424 1820183 := bstep (se 1 (by rfl) ⟨1365137, by rfl⟩ : syracuseStep 1820183 = 2730275) B2730275
theorem B1213975 : Blo 1213424 1213975 := bstep (se 1 (by rfl) ⟨910481, by rfl⟩ : syracuseStep 1213975 = 1820963) B1820963
theorem B1213995 : Blo 1213424 1213995 := bstep (se 1 (by rfl) ⟨910496, by rfl⟩ : syracuseStep 1213995 = 1820993) B1820993
theorem B1214007 : Blo 1213424 1214007 := bstep (se 1 (by rfl) ⟨910505, by rfl⟩ : syracuseStep 1214007 = 1821011) B1821011
theorem B1214027 : Blo 1213424 1214027 := bstep (se 1 (by rfl) ⟨910520, by rfl⟩ : syracuseStep 1214027 = 1821041) B1821041
theorem B1214039 : Blo 1213424 1214039 := bstep (se 1 (by rfl) ⟨910529, by rfl⟩ : syracuseStep 1214039 = 1821059) B1821059
theorem B1820249 : Blo 1213424 1820249 := bstep (se 2 (by rfl) ⟨682593, by rfl⟩ : syracuseStep 1820249 = 1365187) B1365187
theorem B1214059 : Blo 1213424 1214059 := bstep (se 1 (by rfl) ⟨910544, by rfl⟩ : syracuseStep 1214059 = 1821089) B1821089
theorem B1214071 : Blo 1213424 1214071 := bstep (se 1 (by rfl) ⟨910553, by rfl⟩ : syracuseStep 1214071 = 1821107) B1821107
theorem B1214091 : Blo 1213424 1214091 := bstep (se 1 (by rfl) ⟨910568, by rfl⟩ : syracuseStep 1214091 = 1821137) B1821137
theorem B1214103 : Blo 1213424 1214103 := bstep (se 1 (by rfl) ⟨910577, by rfl⟩ : syracuseStep 1214103 = 1821155) B1821155
theorem B1214123 : Blo 1213424 1214123 := bstep (se 1 (by rfl) ⟨910592, by rfl⟩ : syracuseStep 1214123 = 1821185) B1821185
theorem B10798771 : Blo 1213424 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B4925107 : Blo 1213424 4925107 := bstep (se 1 (by rfl) ⟨3693830, by rfl⟩ : syracuseStep 4925107 = 7387661) B7387661
theorem B1214135 : Blo 1213424 1214135 := bstep (se 1 (by rfl) ⟨910601, by rfl⟩ : syracuseStep 1214135 = 1821203) B1821203
theorem B1820363 : Blo 1213424 1820363 := bstep (se 1 (by rfl) ⟨1365272, by rfl⟩ : syracuseStep 1820363 = 2730545) B2730545
theorem B1214155 : Blo 1213424 1214155 := bstep (se 1 (by rfl) ⟨910616, by rfl⟩ : syracuseStep 1214155 = 1821233) B1821233
theorem B1820375 : Blo 1213424 1820375 := bstep (se 1 (by rfl) ⟨1365281, by rfl⟩ : syracuseStep 1820375 = 2730563) B2730563
theorem B1214167 : Blo 1213424 1214167 := bstep (se 1 (by rfl) ⟨910625, by rfl⟩ : syracuseStep 1214167 = 1821251) B1821251
theorem B2770649 : Blo 1213424 2770649 := bstep (se 2 (by rfl) ⟨1038993, by rfl⟩ : syracuseStep 2770649 = 2077987) B2077987
theorem B1214187 : Blo 1213424 1214187 := bstep (se 1 (by rfl) ⟨910640, by rfl⟩ : syracuseStep 1214187 = 1821281) B1821281
theorem B2303731 : Blo 1213424 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B1214199 : Blo 1213424 1214199 := bstep (se 1 (by rfl) ⟨910649, by rfl⟩ : syracuseStep 1214199 = 1821299) B1821299
theorem B1214219 : Blo 1213424 1214219 := bstep (se 1 (by rfl) ⟨910664, by rfl⟩ : syracuseStep 1214219 = 1821329) B1821329
theorem B1214231 : Blo 1213424 1214231 := bstep (se 1 (by rfl) ⟨910673, by rfl⟩ : syracuseStep 1214231 = 1821347) B1821347
theorem B1730327 : Blo 1213424 1730327 := bstep (se 1 (by rfl) ⟨1297745, by rfl⟩ : syracuseStep 1730327 = 2595491) B2595491
theorem B1820441 : Blo 1213424 1820441 := bstep (se 2 (by rfl) ⟨682665, by rfl⟩ : syracuseStep 1820441 = 1365331) B1365331
theorem B2189081 : Blo 1213424 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B1214251 : Blo 1213424 1214251 := bstep (se 1 (by rfl) ⟨910688, by rfl⟩ : syracuseStep 1214251 = 1821377) B1821377
theorem B4097843 : Blo 1213424 4097843 := bstep (se 1 (by rfl) ⟨3073382, by rfl⟩ : syracuseStep 4097843 = 6146765) B6146765
theorem B1214263 : Blo 1213424 1214263 := bstep (se 1 (by rfl) ⟨910697, by rfl⟩ : syracuseStep 1214263 = 1821395) B1821395
theorem B1214283 : Blo 1213424 1214283 := bstep (se 1 (by rfl) ⟨910712, by rfl⟩ : syracuseStep 1214283 = 1821425) B1821425
theorem B1214295 : Blo 1213424 1214295 := bstep (se 1 (by rfl) ⟨910721, by rfl⟩ : syracuseStep 1214295 = 1821443) B1821443
theorem B2107225 : Blo 1213424 2107225 := bstep (se 2 (by rfl) ⟨790209, by rfl⟩ : syracuseStep 2107225 = 1580419) B1580419
theorem B9348965 : Blo 1213424 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B1214315 : Blo 1213424 1214315 := bstep (se 1 (by rfl) ⟨910736, by rfl⟩ : syracuseStep 1214315 = 1821473) B1821473
theorem B1214327 : Blo 1213424 1214327 := bstep (se 1 (by rfl) ⟨910745, by rfl⟩ : syracuseStep 1214327 = 1821491) B1821491
theorem B1820555 : Blo 1213424 1820555 := bstep (se 1 (by rfl) ⟨1365416, by rfl⟩ : syracuseStep 1820555 = 2730833) B2730833
theorem B1214347 : Blo 1213424 1214347 := bstep (se 1 (by rfl) ⟨910760, by rfl⟩ : syracuseStep 1214347 = 1821521) B1821521
theorem B5613457 : Blo 1213424 5613457 := bstep (se 2 (by rfl) ⟨2105046, by rfl⟩ : syracuseStep 5613457 = 4210093) B4210093
theorem B1820567 : Blo 1213424 1820567 := bstep (se 1 (by rfl) ⟨1365425, by rfl⟩ : syracuseStep 1820567 = 2730851) B2730851
theorem B1214359 : Blo 1213424 1214359 := bstep (se 1 (by rfl) ⟨910769, by rfl⟩ : syracuseStep 1214359 = 1821539) B1821539
theorem B1214379 : Blo 1213424 1214379 := bstep (se 1 (by rfl) ⟨910784, by rfl⟩ : syracuseStep 1214379 = 1821569) B1821569
theorem B1214391 : Blo 1213424 1214391 := bstep (se 1 (by rfl) ⟨910793, by rfl⟩ : syracuseStep 1214391 = 1821587) B1821587
theorem B1214411 : Blo 1213424 1214411 := bstep (se 1 (by rfl) ⟨910808, by rfl⟩ : syracuseStep 1214411 = 1821617) B1821617
theorem B2049995 : Blo 1213424 2049995 := bstep (se 1 (by rfl) ⟨1537496, by rfl⟩ : syracuseStep 2049995 = 3074993) B3074993
theorem B2303959 : Blo 1213424 2303959 := bstep (se 1 (by rfl) ⟨1727969, by rfl⟩ : syracuseStep 2303959 = 3455939) B3455939
theorem B1214423 : Blo 1213424 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B1820633 : Blo 1213424 1820633 := bstep (se 2 (by rfl) ⟨682737, by rfl⟩ : syracuseStep 1820633 = 1365475) B1365475
theorem B1730521 : Blo 1213424 1730521 := bstep (se 2 (by rfl) ⟨648945, by rfl⟩ : syracuseStep 1730521 = 1297891) B1297891
theorem B3459037 : Blo 1213424 3459037 := bstep (se 3 (by rfl) ⟨648569, by rfl⟩ : syracuseStep 3459037 = 1297139) B1297139
theorem B1214443 : Blo 1213424 1214443 := bstep (se 1 (by rfl) ⟨910832, by rfl⟩ : syracuseStep 1214443 = 1821665) B1821665
theorem B1214455 : Blo 1213424 1214455 := bstep (se 1 (by rfl) ⟨910841, by rfl⟩ : syracuseStep 1214455 = 1821683) B1821683
theorem B1214475 : Blo 1213424 1214475 := bstep (se 1 (by rfl) ⟨910856, by rfl⟩ : syracuseStep 1214475 = 1821713) B1821713
theorem B3074071 : Blo 1213424 3074071 := bstep (se 1 (by rfl) ⟨2305553, by rfl⟩ : syracuseStep 3074071 = 4611107) B4611107
theorem B1214487 : Blo 1213424 1214487 := bstep (se 1 (by rfl) ⟨910865, by rfl⟩ : syracuseStep 1214487 = 1821731) B1821731
theorem B3459095 : Blo 1213424 3459095 := bstep (se 1 (by rfl) ⟨2594321, by rfl⟩ : syracuseStep 3459095 = 5188643) B5188643
theorem B1214507 : Blo 1213424 1214507 := bstep (se 1 (by rfl) ⟨910880, by rfl⟩ : syracuseStep 1214507 = 1821761) B1821761
theorem B1214519 : Blo 1213424 1214519 := bstep (se 1 (by rfl) ⟨910889, by rfl⟩ : syracuseStep 1214519 = 1821779) B1821779
theorem B2304065 : Blo 1213424 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B4098113 : Blo 1213424 4098113 := bstep (se 2 (by rfl) ⟨1536792, by rfl⟩ : syracuseStep 4098113 = 3073585) B3073585
theorem B1820747 : Blo 1213424 1820747 := bstep (se 1 (by rfl) ⟨1365560, by rfl⟩ : syracuseStep 1820747 = 2731121) B2731121
theorem B1214539 : Blo 1213424 1214539 := bstep (se 1 (by rfl) ⟨910904, by rfl⟩ : syracuseStep 1214539 = 1821809) B1821809
theorem B2050123 : Blo 1213424 2050123 := bstep (se 1 (by rfl) ⟨1537592, by rfl⟩ : syracuseStep 2050123 = 3075185) B3075185
theorem B1820759 : Blo 1213424 1820759 := bstep (se 1 (by rfl) ⟨1365569, by rfl⟩ : syracuseStep 1820759 = 2731139) B2731139
theorem B1214551 : Blo 1213424 1214551 := bstep (se 1 (by rfl) ⟨910913, by rfl⟩ : syracuseStep 1214551 = 1821827) B1821827
theorem B1214571 : Blo 1213424 1214571 := bstep (se 1 (by rfl) ⟨910928, by rfl⟩ : syracuseStep 1214571 = 1821857) B1821857
theorem B1214583 : Blo 1213424 1214583 := bstep (se 1 (by rfl) ⟨910937, by rfl⟩ : syracuseStep 1214583 = 1821875) B1821875
theorem B1214603 : Blo 1213424 1214603 := bstep (se 1 (by rfl) ⟨910952, by rfl⟩ : syracuseStep 1214603 = 1821905) B1821905
theorem B1214615 : Blo 1213424 1214615 := bstep (se 1 (by rfl) ⟨910961, by rfl⟩ : syracuseStep 1214615 = 1821923) B1821923
theorem B1820825 : Blo 1213424 1820825 := bstep (se 2 (by rfl) ⟨682809, by rfl⟩ : syracuseStep 1820825 = 1365619) B1365619
theorem B1214635 : Blo 1213424 1214635 := bstep (se 1 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 1214635 = 1821953) B1821953
theorem B1214647 : Blo 1213424 1214647 := bstep (se 1 (by rfl) ⟨910985, by rfl⟩ : syracuseStep 1214647 = 1821971) B1821971
theorem B1214667 : Blo 1213424 1214667 := bstep (se 1 (by rfl) ⟨911000, by rfl⟩ : syracuseStep 1214667 = 1822001) B1822001
theorem B1214679 : Blo 1213424 1214679 := bstep (se 1 (by rfl) ⟨911009, by rfl⟩ : syracuseStep 1214679 = 1822019) B1822019
theorem B2304217 : Blo 1213424 2304217 := bstep (se 2 (by rfl) ⟨864081, by rfl⟩ : syracuseStep 2304217 = 1728163) B1728163
theorem B1640665 : Blo 1213424 1640665 := bstep (se 2 (by rfl) ⟨615249, by rfl⟩ : syracuseStep 1640665 = 1230499) B1230499
theorem B2050265 : Blo 1213424 2050265 := bstep (se 2 (by rfl) ⟨768849, by rfl⟩ : syracuseStep 2050265 = 1537699) B1537699
theorem B1214699 : Blo 1213424 1214699 := bstep (se 1 (by rfl) ⟨911024, by rfl⟩ : syracuseStep 1214699 = 1822049) B1822049
theorem B1214711 : Blo 1213424 1214711 := bstep (se 1 (by rfl) ⟨911033, by rfl⟩ : syracuseStep 1214711 = 1822067) B1822067
theorem B1820939 : Blo 1213424 1820939 := bstep (se 1 (by rfl) ⟨1365704, by rfl⟩ : syracuseStep 1820939 = 2731409) B2731409
theorem B1214731 : Blo 1213424 1214731 := bstep (se 1 (by rfl) ⟨911048, by rfl⟩ : syracuseStep 1214731 = 1822097) B1822097
theorem B1820951 : Blo 1213424 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B1214743 : Blo 1213424 1214743 := bstep (se 1 (by rfl) ⟨911057, by rfl⟩ : syracuseStep 1214743 = 1822115) B1822115
theorem B1214763 : Blo 1213424 1214763 := bstep (se 1 (by rfl) ⟨911072, by rfl⟩ : syracuseStep 1214763 = 1822145) B1822145
theorem B1296695 : Blo 1213424 1296695 := bstep (se 1 (by rfl) ⟨972521, by rfl⟩ : syracuseStep 1296695 = 1945043) B1945043
theorem B1214775 : Blo 1213424 1214775 := bstep (se 1 (by rfl) ⟨911081, by rfl⟩ : syracuseStep 1214775 = 1822163) B1822163
theorem B1214795 : Blo 1213424 1214795 := bstep (se 1 (by rfl) ⟨911096, by rfl⟩ : syracuseStep 1214795 = 1822193) B1822193
theorem B1214807 : Blo 1213424 1214807 := bstep (se 1 (by rfl) ⟨911105, by rfl⟩ : syracuseStep 1214807 = 1822211) B1822211
theorem B2730329 : Blo 1213424 2730329 := bstep (se 2 (by rfl) ⟨1023873, by rfl⟩ : syracuseStep 2730329 = 2047747) B2047747
theorem B1821017 : Blo 1213424 1821017 := bstep (se 2 (by rfl) ⟨682881, by rfl⟩ : syracuseStep 1821017 = 1365763) B1365763
theorem B2050393 : Blo 1213424 2050393 := bstep (se 2 (by rfl) ⟨768897, by rfl⟩ : syracuseStep 2050393 = 1537795) B1537795
theorem B2189657 : Blo 1213424 2189657 := bstep (se 2 (by rfl) ⟨821121, by rfl⟩ : syracuseStep 2189657 = 1642243) B1642243
theorem B1214827 : Blo 1213424 1214827 := bstep (se 1 (by rfl) ⟨911120, by rfl⟩ : syracuseStep 1214827 = 1822241) B1822241
theorem B1214839 : Blo 1213424 1214839 := bstep (se 1 (by rfl) ⟨911129, by rfl⟩ : syracuseStep 1214839 = 1822259) B1822259
theorem B1943947 : Blo 1213424 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B1214859 : Blo 1213424 1214859 := bstep (se 1 (by rfl) ⟨911144, by rfl⟩ : syracuseStep 1214859 = 1822289) B1822289
theorem B1214871 : Blo 1213424 1214871 := bstep (se 1 (by rfl) ⟨911153, by rfl⟩ : syracuseStep 1214871 = 1822307) B1822307
theorem B2771351 : Blo 1213424 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B1214891 : Blo 1213424 1214891 := bstep (se 1 (by rfl) ⟨911168, by rfl⟩ : syracuseStep 1214891 = 1822337) B1822337
theorem B2730419 : Blo 1213424 2730419 := bstep (se 1 (by rfl) ⟨2047814, by rfl⟩ : syracuseStep 2730419 = 4095629) B4095629
theorem B1214903 : Blo 1213424 1214903 := bstep (se 1 (by rfl) ⟨911177, by rfl⟩ : syracuseStep 1214903 = 1822355) B1822355
theorem B1821131 : Blo 1213424 1821131 := bstep (se 1 (by rfl) ⟨1365848, by rfl⟩ : syracuseStep 1821131 = 2731697) B2731697
theorem B5188043 : Blo 1213424 5188043 := bstep (se 1 (by rfl) ⟨3891032, by rfl⟩ : syracuseStep 5188043 = 7782065) B7782065
theorem B3074507 : Blo 1213424 3074507 := bstep (se 1 (by rfl) ⟨2305880, by rfl⟩ : syracuseStep 3074507 = 4611761) B4611761
theorem B1214923 : Blo 1213424 1214923 := bstep (se 1 (by rfl) ⟨911192, by rfl⟩ : syracuseStep 1214923 = 1822385) B1822385
theorem B2730455 : Blo 1213424 2730455 := bstep (se 1 (by rfl) ⟨2047841, by rfl⟩ : syracuseStep 2730455 = 4095683) B4095683
theorem B1821143 : Blo 1213424 1821143 := bstep (se 1 (by rfl) ⟨1365857, by rfl⟩ : syracuseStep 1821143 = 2731715) B2731715
theorem B1214935 : Blo 1213424 1214935 := bstep (se 1 (by rfl) ⟨911201, by rfl⟩ : syracuseStep 1214935 = 1822403) B1822403
theorem B1214955 : Blo 1213424 1214955 := bstep (se 1 (by rfl) ⟨911216, by rfl⟩ : syracuseStep 1214955 = 1822433) B1822433
theorem B1214967 : Blo 1213424 1214967 := bstep (se 1 (by rfl) ⟨911225, by rfl⟩ : syracuseStep 1214967 = 1822451) B1822451
theorem B1214987 : Blo 1213424 1214987 := bstep (se 1 (by rfl) ⟨911240, by rfl⟩ : syracuseStep 1214987 = 1822481) B1822481
theorem B1214999 : Blo 1213424 1214999 := bstep (se 1 (by rfl) ⟨911249, by rfl⟩ : syracuseStep 1214999 = 1822499) B1822499
theorem B1821209 : Blo 1213424 1821209 := bstep (se 2 (by rfl) ⟨682953, by rfl⟩ : syracuseStep 1821209 = 1365907) B1365907
theorem B1215019 : Blo 1213424 1215019 := bstep (se 1 (by rfl) ⟨911264, by rfl⟩ : syracuseStep 1215019 = 1822529) B1822529
theorem B1215031 : Blo 1213424 1215031 := bstep (se 1 (by rfl) ⟨911273, by rfl⟩ : syracuseStep 1215031 = 1822547) B1822547
theorem B14764619 : Blo 1213424 14764619 := bstep (se 1 (by rfl) ⟨11073464, by rfl⟩ : syracuseStep 14764619 = 22146929) B22146929
theorem B1215051 : Blo 1213424 1215051 := bstep (se 1 (by rfl) ⟨911288, by rfl⟩ : syracuseStep 1215051 = 1822577) B1822577
theorem B1215063 : Blo 1213424 1215063 := bstep (se 1 (by rfl) ⟨911297, by rfl⟩ : syracuseStep 1215063 = 1822595) B1822595
theorem B4098653 : Blo 1213424 4098653 := bstep (se 3 (by rfl) ⟨768497, by rfl⟩ : syracuseStep 4098653 = 1536995) B1536995
theorem B4991581 : Blo 1213424 4991581 := bstep (se 3 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 4991581 = 1871843) B1871843
theorem B1215083 : Blo 1213424 1215083 := bstep (se 1 (by rfl) ⟨911312, by rfl⟩ : syracuseStep 1215083 = 1822625) B1822625
theorem B1215095 : Blo 1213424 1215095 := bstep (se 1 (by rfl) ⟨911321, by rfl⟩ : syracuseStep 1215095 = 1822643) B1822643
theorem B5835395 : Blo 1213424 5835395 := bstep (se 1 (by rfl) ⟨4376546, by rfl⟩ : syracuseStep 5835395 = 8753093) B8753093
theorem B2730635 : Blo 1213424 2730635 := bstep (se 1 (by rfl) ⟨2047976, by rfl⟩ : syracuseStep 2730635 = 4095953) B4095953
theorem B1821323 : Blo 1213424 1821323 := bstep (se 1 (by rfl) ⟨1365992, by rfl⟩ : syracuseStep 1821323 = 2731985) B2731985
theorem B1215115 : Blo 1213424 1215115 := bstep (se 1 (by rfl) ⟨911336, by rfl⟩ : syracuseStep 1215115 = 1822673) B1822673
theorem B1821335 : Blo 1213424 1821335 := bstep (se 1 (by rfl) ⟨1366001, by rfl⟩ : syracuseStep 1821335 = 2732003) B2732003
theorem B1215127 : Blo 1213424 1215127 := bstep (se 1 (by rfl) ⟨911345, by rfl⟩ : syracuseStep 1215127 = 1822691) B1822691
theorem B1215147 : Blo 1213424 1215147 := bstep (se 1 (by rfl) ⟨911360, by rfl⟩ : syracuseStep 1215147 = 1822721) B1822721
theorem B1215159 : Blo 1213424 1215159 := bstep (se 1 (by rfl) ⟨911369, by rfl⟩ : syracuseStep 1215159 = 1822739) B1822739
theorem B2730689 : Blo 1213424 2730689 := bstep (se 2 (by rfl) ⟨1024008, by rfl⟩ : syracuseStep 2730689 = 2048017) B2048017
theorem B1215179 : Blo 1213424 1215179 := bstep (se 1 (by rfl) ⟨911384, by rfl⟩ : syracuseStep 1215179 = 1822769) B1822769
theorem B1215191 : Blo 1213424 1215191 := bstep (se 1 (by rfl) ⟨911393, by rfl⟩ : syracuseStep 1215191 = 1822787) B1822787
theorem B1821401 : Blo 1213424 1821401 := bstep (se 2 (by rfl) ⟨683025, by rfl⟩ : syracuseStep 1821401 = 1366051) B1366051
theorem B1215211 : Blo 1213424 1215211 := bstep (se 1 (by rfl) ⟨911408, by rfl⟩ : syracuseStep 1215211 = 1822817) B1822817
theorem B1215223 : Blo 1213424 1215223 := bstep (se 1 (by rfl) ⟨911417, by rfl⟩ : syracuseStep 1215223 = 1822835) B1822835
theorem B1215243 : Blo 1213424 1215243 := bstep (se 1 (by rfl) ⟨911432, by rfl⟩ : syracuseStep 1215243 = 1822865) B1822865
theorem B2190091 : Blo 1213424 2190091 := bstep (se 1 (by rfl) ⟨1642568, by rfl⟩ : syracuseStep 2190091 = 3285137) B3285137
theorem B1215255 : Blo 1213424 1215255 := bstep (se 1 (by rfl) ⟨911441, by rfl⟩ : syracuseStep 1215255 = 1822883) B1822883
theorem B1215275 : Blo 1213424 1215275 := bstep (se 1 (by rfl) ⟨911456, by rfl⟩ : syracuseStep 1215275 = 1822913) B1822913
theorem B1215287 : Blo 1213424 1215287 := bstep (se 1 (by rfl) ⟨911465, by rfl⟩ : syracuseStep 1215287 = 1822931) B1822931
theorem B3074881 : Blo 1213424 3074881 := bstep (se 2 (by rfl) ⟨1153080, by rfl⟩ : syracuseStep 3074881 = 2306161) B2306161
theorem B1821515 : Blo 1213424 1821515 := bstep (se 1 (by rfl) ⟨1366136, by rfl⟩ : syracuseStep 1821515 = 2732273) B2732273
theorem B1215307 : Blo 1213424 1215307 := bstep (se 1 (by rfl) ⟨911480, by rfl⟩ : syracuseStep 1215307 = 1822961) B1822961
theorem B1821527 : Blo 1213424 1821527 := bstep (se 1 (by rfl) ⟨1366145, by rfl⟩ : syracuseStep 1821527 = 2732291) B2732291
theorem B1215319 : Blo 1213424 1215319 := bstep (se 1 (by rfl) ⟨911489, by rfl⟩ : syracuseStep 1215319 = 1822979) B1822979
theorem B1215339 : Blo 1213424 1215339 := bstep (se 1 (by rfl) ⟨911504, by rfl⟩ : syracuseStep 1215339 = 1823009) B1823009
theorem B1215351 : Blo 1213424 1215351 := bstep (se 1 (by rfl) ⟨911513, by rfl⟩ : syracuseStep 1215351 = 1823027) B1823027
theorem B1215371 : Blo 1213424 1215371 := bstep (se 1 (by rfl) ⟨911528, by rfl⟩ : syracuseStep 1215371 = 1823057) B1823057
theorem B1215383 : Blo 1213424 1215383 := bstep (se 1 (by rfl) ⟨911537, by rfl⟩ : syracuseStep 1215383 = 1823075) B1823075
theorem B2050967 : Blo 1213424 2050967 := bstep (se 1 (by rfl) ⟨1538225, by rfl⟩ : syracuseStep 2050967 = 3076451) B3076451
theorem B2730905 : Blo 1213424 2730905 := bstep (se 2 (by rfl) ⟨1024089, by rfl⟩ : syracuseStep 2730905 = 2048179) B2048179
theorem B1821593 : Blo 1213424 1821593 := bstep (se 2 (by rfl) ⟨683097, by rfl⟩ : syracuseStep 1821593 = 1366195) B1366195
theorem B1215403 : Blo 1213424 1215403 := bstep (se 1 (by rfl) ⟨911552, by rfl⟩ : syracuseStep 1215403 = 1823105) B1823105
theorem B31558577 : Blo 1213424 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B1215415 : Blo 1213424 1215415 := bstep (se 1 (by rfl) ⟨911561, by rfl⟩ : syracuseStep 1215415 = 1823123) B1823123
theorem B4156381 : Blo 1213424 4156381 := bstep (se 3 (by rfl) ⟨779321, by rfl⟩ : syracuseStep 4156381 = 1558643) B1558643
theorem B1297387 : Blo 1213424 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B2730995 : Blo 1213424 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B1821707 : Blo 1213424 1821707 := bstep (se 1 (by rfl) ⟨1366280, by rfl⟩ : syracuseStep 1821707 = 2732561) B2732561
theorem B6147089 : Blo 1213424 6147089 := bstep (se 2 (by rfl) ⟨2305158, by rfl⟩ : syracuseStep 6147089 = 4610317) B4610317
theorem B2731031 : Blo 1213424 2731031 := bstep (se 1 (by rfl) ⟨2048273, by rfl⟩ : syracuseStep 2731031 = 4096547) B4096547
theorem B1821719 : Blo 1213424 1821719 := bstep (se 1 (by rfl) ⟨1366289, by rfl⟩ : syracuseStep 1821719 = 2732579) B2732579
theorem B1944665 : Blo 1213424 1944665 := bstep (se 2 (by rfl) ⟨729249, by rfl⟩ : syracuseStep 1944665 = 1458499) B1458499
theorem B1821785 : Blo 1213424 1821785 := bstep (se 2 (by rfl) ⟨683169, by rfl⟩ : syracuseStep 1821785 = 1366339) B1366339
theorem B6564995 : Blo 1213424 6564995 := bstep (se 1 (by rfl) ⟨4923746, by rfl⟩ : syracuseStep 6564995 = 9847493) B9847493
theorem B6147251 : Blo 1213424 6147251 := bstep (se 1 (by rfl) ⟨4610438, by rfl⟩ : syracuseStep 6147251 = 9220877) B9220877
theorem B2731211 : Blo 1213424 2731211 := bstep (se 1 (by rfl) ⟨2048408, by rfl⟩ : syracuseStep 2731211 = 4096817) B4096817
theorem B1821899 : Blo 1213424 1821899 := bstep (se 1 (by rfl) ⟨1366424, by rfl⟩ : syracuseStep 1821899 = 2732849) B2732849
theorem B1821911 : Blo 1213424 1821911 := bstep (se 1 (by rfl) ⟨1366433, by rfl⟩ : syracuseStep 1821911 = 2732867) B2732867
theorem B3460313 : Blo 1213424 3460313 := bstep (se 2 (by rfl) ⟨1297617, by rfl⟩ : syracuseStep 3460313 = 2595235) B2595235
theorem B2731265 : Blo 1213424 2731265 := bstep (se 2 (by rfl) ⟨1024224, by rfl⟩ : syracuseStep 2731265 = 2048449) B2048449
theorem B1821977 : Blo 1213424 1821977 := bstep (se 2 (by rfl) ⟨683241, by rfl⟩ : syracuseStep 1821977 = 1366483) B1366483
theorem B13823297 : Blo 1213424 13823297 := bstep (se 2 (by rfl) ⟨5183736, by rfl⟩ : syracuseStep 13823297 = 10367473) B10367473
theorem B3460427 : Blo 1213424 3460427 := bstep (se 1 (by rfl) ⟨2595320, by rfl⟩ : syracuseStep 3460427 = 5190641) B5190641
theorem B10800485 : Blo 1213424 10800485 := bstep (se 4 (by rfl) ⟨1012545, by rfl⟩ : syracuseStep 10800485 = 2025091) B2025091
theorem B1822091 : Blo 1213424 1822091 := bstep (se 1 (by rfl) ⟨1366568, by rfl⟩ : syracuseStep 1822091 = 2733137) B2733137
theorem B1822103 : Blo 1213424 1822103 := bstep (se 1 (by rfl) ⟨1366577, by rfl⟩ : syracuseStep 1822103 = 2733155) B2733155
theorem B3075479 : Blo 1213424 3075479 := bstep (se 1 (by rfl) ⟨2306609, by rfl⟩ : syracuseStep 3075479 = 4613219) B4613219
theorem B2731481 : Blo 1213424 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B1822169 : Blo 1213424 1822169 := bstep (se 2 (by rfl) ⟨683313, by rfl⟩ : syracuseStep 1822169 = 1366627) B1366627
theorem B2305523 : Blo 1213424 2305523 := bstep (se 1 (by rfl) ⟨1729142, by rfl⟩ : syracuseStep 2305523 = 3458285) B3458285
theorem B2731571 : Blo 1213424 2731571 := bstep (se 1 (by rfl) ⟨2048678, by rfl⟩ : syracuseStep 2731571 = 4097357) B4097357
theorem B1822283 : Blo 1213424 1822283 := bstep (se 1 (by rfl) ⟨1366712, by rfl⟩ : syracuseStep 1822283 = 2733425) B2733425
theorem B2731607 : Blo 1213424 2731607 := bstep (se 1 (by rfl) ⟨2048705, by rfl⟩ : syracuseStep 2731607 = 4097411) B4097411
theorem B1822295 : Blo 1213424 1822295 := bstep (se 1 (by rfl) ⟨1366721, by rfl⟩ : syracuseStep 1822295 = 2733443) B2733443
theorem B3690073 : Blo 1213424 3690073 := bstep (se 2 (by rfl) ⟨1383777, by rfl⟩ : syracuseStep 3690073 = 2767555) B2767555
theorem B2920025 : Blo 1213424 2920025 := bstep (se 2 (by rfl) ⟨1095009, by rfl⟩ : syracuseStep 2920025 = 2190019) B2190019
theorem B7786115 : Blo 1213424 7786115 := bstep (se 1 (by rfl) ⟨5839586, by rfl⟩ : syracuseStep 7786115 = 11679173) B11679173
theorem B2305675 : Blo 1213424 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B1822361 : Blo 1213424 1822361 := bstep (se 2 (by rfl) ⟨683385, by rfl⟩ : syracuseStep 1822361 = 1366771) B1366771
theorem B4099787 : Blo 1213424 4099787 := bstep (se 1 (by rfl) ⟨3074840, by rfl⟩ : syracuseStep 4099787 = 6149681) B6149681
theorem B4607705 : Blo 1213424 4607705 := bstep (se 2 (by rfl) ⟨1727889, by rfl⟩ : syracuseStep 4607705 = 3455779) B3455779
theorem B5189341 : Blo 1213424 5189341 := bstep (se 3 (by rfl) ⟨973001, by rfl⟩ : syracuseStep 5189341 = 1946003) B1946003
theorem B37932785 : Blo 1213424 37932785 := bstep (se 2 (by rfl) ⟨14224794, by rfl⟩ : syracuseStep 37932785 = 28449589) B28449589
theorem B1535755 : Blo 1213424 1535755 := bstep (se 1 (by rfl) ⟨1151816, by rfl⟩ : syracuseStep 1535755 = 2303633) B2303633
theorem B2731787 : Blo 1213424 2731787 := bstep (se 1 (by rfl) ⟨2048840, by rfl⟩ : syracuseStep 2731787 = 4097681) B4097681
theorem B1822475 : Blo 1213424 1822475 := bstep (se 1 (by rfl) ⟨1366856, by rfl⟩ : syracuseStep 1822475 = 2733713) B2733713
theorem B1822487 : Blo 1213424 1822487 := bstep (se 1 (by rfl) ⟨1366865, by rfl⟩ : syracuseStep 1822487 = 2733731) B2733731
theorem B3690305 : Blo 1213424 3690305 := bstep (se 2 (by rfl) ⟨1383864, by rfl⟩ : syracuseStep 3690305 = 2767729) B2767729
theorem B9219905 : Blo 1213424 9219905 := bstep (se 2 (by rfl) ⟨3457464, by rfl⟩ : syracuseStep 9219905 = 6914929) B6914929
theorem B2731841 : Blo 1213424 2731841 := bstep (se 2 (by rfl) ⟨1024440, by rfl⟩ : syracuseStep 2731841 = 2048881) B2048881
theorem B2592587 : Blo 1213424 2592587 := bstep (se 1 (by rfl) ⟨1944440, by rfl⟩ : syracuseStep 2592587 = 3888881) B3888881
theorem B1822553 : Blo 1213424 1822553 := bstep (se 2 (by rfl) ⟨683457, by rfl⟩ : syracuseStep 1822553 = 1366915) B1366915
theorem B1822667 : Blo 1213424 1822667 := bstep (se 1 (by rfl) ⟨1367000, by rfl⟩ : syracuseStep 1822667 = 2734001) B2734001
theorem B1822679 : Blo 1213424 1822679 := bstep (se 1 (by rfl) ⟨1367009, by rfl⟩ : syracuseStep 1822679 = 2734019) B2734019
theorem B2306009 : Blo 1213424 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B4100057 : Blo 1213424 4100057 := bstep (se 2 (by rfl) ⟨1537521, by rfl⟩ : syracuseStep 4100057 = 3075043) B3075043
theorem B1536023 : Blo 1213424 1536023 := bstep (se 1 (by rfl) ⟨1152017, by rfl⟩ : syracuseStep 1536023 = 2304035) B2304035
theorem B2732057 : Blo 1213424 2732057 := bstep (se 2 (by rfl) ⟨1024521, by rfl⟩ : syracuseStep 2732057 = 2049043) B2049043
theorem B1822745 : Blo 1213424 1822745 := bstep (se 2 (by rfl) ⟨683529, by rfl⟩ : syracuseStep 1822745 = 1367059) B1367059
theorem B5189683 : Blo 1213424 5189683 := bstep (se 1 (by rfl) ⟨3892262, by rfl⟩ : syracuseStep 5189683 = 7784525) B7784525
theorem B14774347 : Blo 1213424 14774347 := bstep (se 1 (by rfl) ⟨11080760, by rfl⟩ : syracuseStep 14774347 = 22161521) B22161521
theorem B2732147 : Blo 1213424 2732147 := bstep (se 1 (by rfl) ⟨2049110, by rfl⟩ : syracuseStep 2732147 = 4098221) B4098221
theorem B1822859 : Blo 1213424 1822859 := bstep (se 1 (by rfl) ⟨1367144, by rfl⟩ : syracuseStep 1822859 = 2734289) B2734289
theorem B4378769 : Blo 1213424 4378769 := bstep (se 2 (by rfl) ⟨1642038, by rfl⟩ : syracuseStep 4378769 = 3284077) B3284077
theorem B2732183 : Blo 1213424 2732183 := bstep (se 1 (by rfl) ⟨2049137, by rfl⟩ : syracuseStep 2732183 = 4098275) B4098275
theorem B1822871 : Blo 1213424 1822871 := bstep (se 1 (by rfl) ⟨1367153, by rfl⟩ : syracuseStep 1822871 = 2734307) B2734307
theorem B3076289 : Blo 1213424 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B1822937 : Blo 1213424 1822937 := bstep (se 2 (by rfl) ⟨683601, by rfl⟩ : syracuseStep 1822937 = 1367203) B1367203
theorem B2732363 : Blo 1213424 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B1823051 : Blo 1213424 1823051 := bstep (se 1 (by rfl) ⟨1367288, by rfl⟩ : syracuseStep 1823051 = 2734577) B2734577
theorem B1823063 : Blo 1213424 1823063 := bstep (se 1 (by rfl) ⟨1367297, by rfl⟩ : syracuseStep 1823063 = 2734595) B2734595
theorem B2732417 : Blo 1213424 2732417 := bstep (se 2 (by rfl) ⟨1024656, by rfl⟩ : syracuseStep 2732417 = 2049313) B2049313
theorem B1823129 : Blo 1213424 1823129 := bstep (se 2 (by rfl) ⟨683673, by rfl⟩ : syracuseStep 1823129 = 1367347) B1367347
theorem B2306647 : Blo 1213424 2306647 := bstep (se 1 (by rfl) ⟨1729985, by rfl⟩ : syracuseStep 2306647 = 3459971) B3459971
theorem B2732633 : Blo 1213424 2732633 := bstep (se 2 (by rfl) ⟨1024737, by rfl⟩ : syracuseStep 2732633 = 2049475) B2049475
theorem B4100759 : Blo 1213424 4100759 := bstep (se 1 (by rfl) ⟨3075569, by rfl⟩ : syracuseStep 4100759 = 6151139) B6151139
theorem B2593433 : Blo 1213424 2593433 := bstep (se 2 (by rfl) ⟨972537, by rfl⟩ : syracuseStep 2593433 = 1945075) B1945075
theorem B2732723 : Blo 1213424 2732723 := bstep (se 1 (by rfl) ⟨2049542, by rfl⟩ : syracuseStep 2732723 = 4099085) B4099085
theorem B1536727 : Blo 1213424 1536727 := bstep (se 1 (by rfl) ⟨1152545, by rfl⟩ : syracuseStep 1536727 = 2305091) B2305091
theorem B2732759 : Blo 1213424 2732759 := bstep (se 1 (by rfl) ⟨2049569, by rfl⟩ : syracuseStep 2732759 = 4099139) B4099139
theorem B20763377 : Blo 1213424 20763377 := bstep (se 2 (by rfl) ⟨7786266, by rfl⟩ : syracuseStep 20763377 = 15572533) B15572533
theorem B2732939 : Blo 1213424 2732939 := bstep (se 1 (by rfl) ⟨2049704, by rfl⟩ : syracuseStep 2732939 = 4099409) B4099409
theorem B2732993 : Blo 1213424 2732993 := bstep (se 2 (by rfl) ⟨1024872, by rfl⟩ : syracuseStep 2732993 = 2049745) B2049745
theorem B6149195 : Blo 1213424 6149195 := bstep (se 1 (by rfl) ⟨4611896, by rfl⟩ : syracuseStep 6149195 = 9223793) B9223793
theorem B11662487 : Blo 1213424 11662487 := bstep (se 1 (by rfl) ⟨8746865, by rfl⟩ : syracuseStep 11662487 = 17493731) B17493731
theorem B2733209 : Blo 1213424 2733209 := bstep (se 2 (by rfl) ⟨1024953, by rfl⟩ : syracuseStep 2733209 = 2049907) B2049907
theorem B4101299 : Blo 1213424 4101299 := bstep (se 1 (by rfl) ⟨3075974, by rfl⟩ : syracuseStep 4101299 = 6151949) B6151949
theorem B9843929 : Blo 1213424 9843929 := bstep (se 2 (by rfl) ⟨3691473, by rfl⟩ : syracuseStep 9843929 = 7382947) B7382947
theorem B2733299 : Blo 1213424 2733299 := bstep (se 1 (by rfl) ⟨2049974, by rfl⟩ : syracuseStep 2733299 = 4099949) B4099949
theorem B23655685 : Blo 1213424 23655685 := bstep (se 4 (by rfl) ⟨2217720, by rfl⟩ : syracuseStep 23655685 = 4435441) B4435441
theorem B1365259 : Blo 1213424 1365259 := bstep (se 1 (by rfl) ⟨1023944, by rfl⟩ : syracuseStep 1365259 = 2047889) B2047889
theorem B2733335 : Blo 1213424 2733335 := bstep (se 1 (by rfl) ⟨2050001, by rfl⟩ : syracuseStep 2733335 = 4100003) B4100003
theorem B4609331 : Blo 1213424 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B4609345 : Blo 1213424 4609345 := bstep (se 2 (by rfl) ⟨1728504, by rfl⟩ : syracuseStep 4609345 = 3457009) B3457009
theorem B1365367 : Blo 1213424 1365367 := bstep (se 1 (by rfl) ⟨1024025, by rfl⟩ : syracuseStep 1365367 = 2048051) B2048051
theorem B2594227 : Blo 1213424 2594227 := bstep (se 1 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 2594227 = 3891341) B3891341
theorem B4101569 : Blo 1213424 4101569 := bstep (se 2 (by rfl) ⟨1538088, by rfl⟩ : syracuseStep 4101569 = 3076177) B3076177
theorem B2733515 : Blo 1213424 2733515 := bstep (se 1 (by rfl) ⟨2050136, by rfl⟩ : syracuseStep 2733515 = 4100273) B4100273
theorem B170497493 : Blo 1213424 170497493 := bstep (se 7 (by rfl) ⟨1998017, by rfl⟩ : syracuseStep 170497493 = 3996035) B3996035
theorem B2733569 : Blo 1213424 2733569 := bstep (se 2 (by rfl) ⟨1025088, by rfl⟩ : syracuseStep 2733569 = 2050177) B2050177
theorem B1365547 : Blo 1213424 1365547 := bstep (se 1 (by rfl) ⟨1024160, by rfl⟩ : syracuseStep 1365547 = 2048321) B2048321
theorem B4920925 : Blo 1213424 4920925 := bstep (se 3 (by rfl) ⟨922673, by rfl⟩ : syracuseStep 4920925 = 1845347) B1845347
theorem B1365655 : Blo 1213424 1365655 := bstep (se 1 (by rfl) ⟨1024241, by rfl⟩ : syracuseStep 1365655 = 2048483) B2048483
theorem B9221849 : Blo 1213424 9221849 := bstep (se 2 (by rfl) ⟨3458193, by rfl⟩ : syracuseStep 9221849 = 6916387) B6916387
theorem B2733785 : Blo 1213424 2733785 := bstep (se 2 (by rfl) ⟨1025169, by rfl⟩ : syracuseStep 2733785 = 2050339) B2050339
theorem B2733875 : Blo 1213424 2733875 := bstep (se 1 (by rfl) ⟨2050406, by rfl⟩ : syracuseStep 2733875 = 4100813) B4100813
theorem B1365835 : Blo 1213424 1365835 := bstep (se 1 (by rfl) ⟨1024376, by rfl⟩ : syracuseStep 1365835 = 2048753) B2048753
theorem B2733911 : Blo 1213424 2733911 := bstep (se 1 (by rfl) ⟨2050433, by rfl⟩ : syracuseStep 2733911 = 4100867) B4100867
theorem B33249203 : Blo 1213424 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B1365943 : Blo 1213424 1365943 := bstep (se 1 (by rfl) ⟨1024457, by rfl⟩ : syracuseStep 1365943 = 2048915) B2048915
theorem B28063705 : Blo 1213424 28063705 := bstep (se 2 (by rfl) ⟨10523889, by rfl⟩ : syracuseStep 28063705 = 21047779) B21047779
theorem B2734091 : Blo 1213424 2734091 := bstep (se 1 (by rfl) ⟨2050568, by rfl⟩ : syracuseStep 2734091 = 4101137) B4101137
theorem B2734145 : Blo 1213424 2734145 := bstep (se 2 (by rfl) ⟨1025304, by rfl⟩ : syracuseStep 2734145 = 2050609) B2050609
theorem B1366123 : Blo 1213424 1366123 := bstep (se 1 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 1366123 = 2049185) B2049185
theorem B1366231 : Blo 1213424 1366231 := bstep (se 1 (by rfl) ⟨1024673, by rfl⟩ : syracuseStep 1366231 = 2049347) B2049347
theorem B2595073 : Blo 1213424 2595073 := bstep (se 2 (by rfl) ⟨973152, by rfl⟩ : syracuseStep 2595073 = 1946305) B1946305
theorem B2734361 : Blo 1213424 2734361 := bstep (se 2 (by rfl) ⟨1025385, by rfl⟩ : syracuseStep 2734361 = 2050771) B2050771
theorem B5536075 : Blo 1213424 5536075 := bstep (se 1 (by rfl) ⟨4152056, by rfl⟩ : syracuseStep 5536075 = 8304113) B8304113
theorem B2734451 : Blo 1213424 2734451 := bstep (se 1 (by rfl) ⟨2050838, by rfl⟩ : syracuseStep 2734451 = 4101677) B4101677
theorem B39369077 : Blo 1213424 39369077 := bstep (se 5 (by rfl) ⟨1845425, by rfl⟩ : syracuseStep 39369077 = 3690851) B3690851
theorem B6920579 : Blo 1213424 6920579 := bstep (se 1 (by rfl) ⟨5190434, by rfl⟩ : syracuseStep 6920579 = 10380869) B10380869
theorem B1366411 : Blo 1213424 1366411 := bstep (se 1 (by rfl) ⟨1024808, by rfl⟩ : syracuseStep 1366411 = 2049617) B2049617
theorem B2734487 : Blo 1213424 2734487 := bstep (se 1 (by rfl) ⟨2050865, by rfl⟩ : syracuseStep 2734487 = 4101731) B4101731
theorem B10369457 : Blo 1213424 10369457 := bstep (se 2 (by rfl) ⟨3888546, by rfl⟩ : syracuseStep 10369457 = 7777093) B7777093
theorem B1366519 : Blo 1213424 1366519 := bstep (se 1 (by rfl) ⟨1024889, by rfl⟩ : syracuseStep 1366519 = 2049779) B2049779
theorem B2734667 : Blo 1213424 2734667 := bstep (se 1 (by rfl) ⟨2051000, by rfl⟩ : syracuseStep 2734667 = 4102001) B4102001
theorem B2595415 : Blo 1213424 2595415 := bstep (se 1 (by rfl) ⟨1946561, by rfl⟩ : syracuseStep 2595415 = 3893123) B3893123
theorem B1366699 : Blo 1213424 1366699 := bstep (se 1 (by rfl) ⟨1025024, by rfl⟩ : syracuseStep 1366699 = 2050049) B2050049
theorem B70032113 : Blo 1213424 70032113 := bstep (se 2 (by rfl) ⟨26262042, by rfl⟩ : syracuseStep 70032113 = 52524085) B52524085
theorem B1366807 : Blo 1213424 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B6150977 : Blo 1213424 6150977 := bstep (se 2 (by rfl) ⟨2306616, by rfl⟩ : syracuseStep 6150977 = 4613233) B4613233
theorem B6921035 : Blo 1213424 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B3693491 : Blo 1213424 3693491 := bstep (se 1 (by rfl) ⟨2770118, by rfl⟩ : syracuseStep 3693491 = 5540237) B5540237
theorem B1366987 : Blo 1213424 1366987 := bstep (se 1 (by rfl) ⟨1025240, by rfl⟩ : syracuseStep 1366987 = 2050481) B2050481
theorem B5184557 : Blo 1213424 5184557 := bstep (se 3 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 5184557 = 1944209) B1944209
theorem B1367095 : Blo 1213424 1367095 := bstep (se 1 (by rfl) ⟨1025321, by rfl⟩ : syracuseStep 1367095 = 2050643) B2050643
theorem B31112261 : Blo 1213424 31112261 := bstep (se 4 (by rfl) ⟨2916774, by rfl⟩ : syracuseStep 31112261 = 5833549) B5833549
theorem B3456179 : Blo 1213424 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B4611275 : Blo 1213424 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B3890393 : Blo 1213424 3890393 := bstep (se 2 (by rfl) ⟨1458897, by rfl⟩ : syracuseStep 3890393 = 2917795) B2917795
theorem B4611289 : Blo 1213424 4611289 := bstep (se 2 (by rfl) ⟨1729233, by rfl⟩ : syracuseStep 4611289 = 3458467) B3458467
theorem B1367275 : Blo 1213424 1367275 := bstep (se 1 (by rfl) ⟨1025456, by rfl⟩ : syracuseStep 1367275 = 2050913) B2050913
theorem B7011659 : Blo 1213424 7011659 := bstep (se 1 (by rfl) ⟨5258744, by rfl⟩ : syracuseStep 7011659 = 10517489) B10517489
theorem B1727833 : Blo 1213424 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B6143363 : Blo 1213424 6143363 := bstep (se 1 (by rfl) ⟨4607522, by rfl⟩ : syracuseStep 6143363 = 9215045) B9215045
theorem B1383851 : Blo 1213424 1383851 := bstep (se 1 (by rfl) ⟨1037888, by rfl⟩ : syracuseStep 1383851 = 2075777) B2075777
theorem B4922903 : Blo 1213424 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B1998361 : Blo 1213424 1998361 := bstep (se 2 (by rfl) ⟨749385, by rfl⟩ : syracuseStep 1998361 = 1498771) B1498771
theorem B2915929 : Blo 1213424 2915929 := bstep (se 2 (by rfl) ⟨1093473, by rfl⟩ : syracuseStep 2915929 = 2186947) B2186947
theorem B3284659 : Blo 1213424 3284659 := bstep (se 1 (by rfl) ⟨2463494, by rfl⟩ : syracuseStep 3284659 = 4926989) B4926989
theorem B5185241 : Blo 1213424 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B9854725 : Blo 1213424 9854725 := bstep (se 4 (by rfl) ⟨923880, by rfl⟩ : syracuseStep 9854725 = 1847761) B1847761
theorem B18693989 : Blo 1213424 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B2187251 : Blo 1213424 2187251 := bstep (se 1 (by rfl) ⟨1640438, by rfl⟩ : syracuseStep 2187251 = 3280877) B3280877
theorem B6144011 : Blo 1213424 6144011 := bstep (se 1 (by rfl) ⟨4608008, by rfl⟩ : syracuseStep 6144011 = 9216017) B9216017
theorem B4096061 : Blo 1213424 4096061 := bstep (se 3 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 4096061 = 1536023) B1536023
theorem B9224279 : Blo 1213424 9224279 := bstep (se 1 (by rfl) ⟨6918209, by rfl⟩ : syracuseStep 9224279 = 13836419) B13836419
theorem B10657925 : Blo 1213424 10657925 := bstep (se 4 (by rfl) ⟨999180, by rfl⟩ : syracuseStep 10657925 = 1998361) B1998361
theorem B6144173 : Blo 1213424 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B3072289 : Blo 1213424 3072289 := bstep (se 2 (by rfl) ⟨1152108, by rfl⟩ : syracuseStep 3072289 = 2304217) B2304217
theorem B2187553 : Blo 1213424 2187553 := bstep (se 2 (by rfl) ⟨820332, by rfl⟩ : syracuseStep 2187553 = 1640665) B1640665
theorem B1442107 : Blo 1213424 1442107 := bstep (se 1 (by rfl) ⟨1081580, by rfl⟩ : syracuseStep 1442107 = 2163161) B2163161
theorem B2048375 : Blo 1213424 2048375 := bstep (se 1 (by rfl) ⟨1536281, by rfl⟩ : syracuseStep 2048375 = 3072563) B3072563
theorem B7381433 : Blo 1213424 7381433 := bstep (se 2 (by rfl) ⟨2768037, by rfl⟩ : syracuseStep 7381433 = 5536075) B5536075
theorem B1728955 : Blo 1213424 1728955 := bstep (se 1 (by rfl) ⟨1296716, by rfl⟩ : syracuseStep 1728955 = 2593433) B2593433
theorem B11076061 : Blo 1213424 11076061 := bstep (se 3 (by rfl) ⟨2076761, by rfl⟩ : syracuseStep 11076061 = 4153523) B4153523
theorem B3457579 : Blo 1213424 3457579 := bstep (se 1 (by rfl) ⟨2593184, by rfl⟩ : syracuseStep 3457579 = 5186369) B5186369
theorem B11666177 : Blo 1213424 11666177 := bstep (se 2 (by rfl) ⟨4374816, by rfl⟩ : syracuseStep 11666177 = 8749633) B8749633
theorem B7774991 : Blo 1213424 7774991 := bstep (se 1 (by rfl) ⟨5831243, by rfl⟩ : syracuseStep 7774991 = 11662487) B11662487
theorem B6562619 : Blo 1213424 6562619 := bstep (se 1 (by rfl) ⟨4921964, by rfl⟩ : syracuseStep 6562619 = 9843929) B9843929
theorem B2048827 : Blo 1213424 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B3457853 : Blo 1213424 3457853 := bstep (se 3 (by rfl) ⟨648347, by rfl⟩ : syracuseStep 3457853 = 1296695) B1296695
theorem B3072887 : Blo 1213424 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B2048969 : Blo 1213424 2048969 := bstep (se 2 (by rfl) ⟨768363, by rfl⟩ : syracuseStep 2048969 = 1536727) B1536727
theorem B113664995 : Blo 1213424 113664995 := bstep (se 1 (by rfl) ⟨85248746, by rfl⟩ : syracuseStep 113664995 = 170497493) B170497493
theorem B1213447 : Blo 1213424 1213447 := bstep (se 1 (by rfl) ⟨910085, by rfl⟩ : syracuseStep 1213447 = 1820171) B1820171
theorem B1213455 : Blo 1213424 1213455 := bstep (se 1 (by rfl) ⟨910091, by rfl⟩ : syracuseStep 1213455 = 1820183) B1820183
theorem B1213499 : Blo 1213424 1213499 := bstep (se 1 (by rfl) ⟨910124, by rfl⟩ : syracuseStep 1213499 = 1820249) B1820249
theorem B1213575 : Blo 1213424 1213575 := bstep (se 1 (by rfl) ⟨910181, by rfl⟩ : syracuseStep 1213575 = 1820363) B1820363
theorem B1213583 : Blo 1213424 1213583 := bstep (se 1 (by rfl) ⟨910187, by rfl⟩ : syracuseStep 1213583 = 1820375) B1820375
theorem B1213627 : Blo 1213424 1213627 := bstep (se 1 (by rfl) ⟨910220, by rfl⟩ : syracuseStep 1213627 = 1820441) B1820441
theorem B1459387 : Blo 1213424 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B1213703 : Blo 1213424 1213703 := bstep (se 1 (by rfl) ⟨910277, by rfl⟩ : syracuseStep 1213703 = 1820555) B1820555
theorem B1213711 : Blo 1213424 1213711 := bstep (se 1 (by rfl) ⟨910283, by rfl⟩ : syracuseStep 1213711 = 1820567) B1820567
theorem B1729849 : Blo 1213424 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B1213755 : Blo 1213424 1213755 := bstep (se 1 (by rfl) ⟨910316, by rfl⟩ : syracuseStep 1213755 = 1820633) B1820633
theorem B1213831 : Blo 1213424 1213831 := bstep (se 1 (by rfl) ⟨910373, by rfl⟩ : syracuseStep 1213831 = 1820747) B1820747
theorem B1213839 : Blo 1213424 1213839 := bstep (se 1 (by rfl) ⟨910379, by rfl⟩ : syracuseStep 1213839 = 1820759) B1820759
theorem B4097465 : Blo 1213424 4097465 := bstep (se 2 (by rfl) ⟨1536549, by rfl⟩ : syracuseStep 4097465 = 3073099) B3073099
theorem B1213883 : Blo 1213424 1213883 := bstep (se 1 (by rfl) ⟨910412, by rfl⟩ : syracuseStep 1213883 = 1820825) B1820825
theorem B26281421 : Blo 1213424 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B1213959 : Blo 1213424 1213959 := bstep (se 1 (by rfl) ⟨910469, by rfl⟩ : syracuseStep 1213959 = 1820939) B1820939
theorem B1213967 : Blo 1213424 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B1820219 : Blo 1213424 1820219 := bstep (se 1 (by rfl) ⟨1365164, by rfl⟩ : syracuseStep 1820219 = 2730329) B2730329
theorem B1214011 : Blo 1213424 1214011 := bstep (se 1 (by rfl) ⟨910508, by rfl⟩ : syracuseStep 1214011 = 1821017) B1821017
theorem B4613719 : Blo 1213424 4613719 := bstep (se 1 (by rfl) ⟨3460289, by rfl⟩ : syracuseStep 4613719 = 6920579) B6920579
theorem B1820279 : Blo 1213424 1820279 := bstep (se 1 (by rfl) ⟨1365209, by rfl⟩ : syracuseStep 1820279 = 2730419) B2730419
theorem B1214087 : Blo 1213424 1214087 := bstep (se 1 (by rfl) ⟨910565, by rfl⟩ : syracuseStep 1214087 = 1821131) B1821131
theorem B3458695 : Blo 1213424 3458695 := bstep (se 1 (by rfl) ⟨2594021, by rfl⟩ : syracuseStep 3458695 = 5188043) B5188043
theorem B2049671 : Blo 1213424 2049671 := bstep (se 1 (by rfl) ⟨1537253, by rfl⟩ : syracuseStep 2049671 = 3074507) B3074507
theorem B1820303 : Blo 1213424 1820303 := bstep (se 1 (by rfl) ⟨1365227, by rfl⟩ : syracuseStep 1820303 = 2730455) B2730455
theorem B1214095 : Blo 1213424 1214095 := bstep (se 1 (by rfl) ⟨910571, by rfl⟩ : syracuseStep 1214095 = 1821143) B1821143
theorem B31540913 : Blo 1213424 31540913 := bstep (se 2 (by rfl) ⟨11827842, by rfl⟩ : syracuseStep 31540913 = 23655685) B23655685
theorem B1820345 : Blo 1213424 1820345 := bstep (se 2 (by rfl) ⟨682629, by rfl⟩ : syracuseStep 1820345 = 1365259) B1365259
theorem B1214139 : Blo 1213424 1214139 := bstep (se 1 (by rfl) ⟨910604, by rfl⟩ : syracuseStep 1214139 = 1821209) B1821209
theorem B6145793 : Blo 1213424 6145793 := bstep (se 2 (by rfl) ⟨2304672, by rfl⟩ : syracuseStep 6145793 = 4609345) B4609345
theorem B1820423 : Blo 1213424 1820423 := bstep (se 1 (by rfl) ⟨1365317, by rfl⟩ : syracuseStep 1820423 = 2730635) B2730635
theorem B1214215 : Blo 1213424 1214215 := bstep (se 1 (by rfl) ⟨910661, by rfl⟩ : syracuseStep 1214215 = 1821323) B1821323
theorem B1214223 : Blo 1213424 1214223 := bstep (se 1 (by rfl) ⟨910667, by rfl⟩ : syracuseStep 1214223 = 1821335) B1821335
theorem B2303777 : Blo 1213424 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B1820459 : Blo 1213424 1820459 := bstep (se 1 (by rfl) ⟨1365344, by rfl⟩ : syracuseStep 1820459 = 2730689) B2730689
theorem B1214267 : Blo 1213424 1214267 := bstep (se 1 (by rfl) ⟨910700, by rfl⟩ : syracuseStep 1214267 = 1821401) B1821401
theorem B1820489 : Blo 1213424 1820489 := bstep (se 2 (by rfl) ⟨682683, by rfl⟩ : syracuseStep 1820489 = 1365367) B1365367
theorem B46688075 : Blo 1213424 46688075 := bstep (se 1 (by rfl) ⟨35016056, by rfl⟩ : syracuseStep 46688075 = 70032113) B70032113
theorem B1214343 : Blo 1213424 1214343 := bstep (se 1 (by rfl) ⟨910757, by rfl⟩ : syracuseStep 1214343 = 1821515) B1821515
theorem B4614023 : Blo 1213424 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B1214351 : Blo 1213424 1214351 := bstep (se 1 (by rfl) ⟨910763, by rfl⟩ : syracuseStep 1214351 = 1821527) B1821527
theorem B3458969 : Blo 1213424 3458969 := bstep (se 2 (by rfl) ⟨1297113, by rfl⟩ : syracuseStep 3458969 = 2594227) B2594227
theorem B1820603 : Blo 1213424 1820603 := bstep (se 1 (by rfl) ⟨1365452, by rfl⟩ : syracuseStep 1820603 = 2730905) B2730905
theorem B1214395 : Blo 1213424 1214395 := bstep (se 1 (by rfl) ⟨910796, by rfl⟩ : syracuseStep 1214395 = 1821593) B1821593
theorem B1820663 : Blo 1213424 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B1214471 : Blo 1213424 1214471 := bstep (se 1 (by rfl) ⟨910853, by rfl⟩ : syracuseStep 1214471 = 1821707) B1821707
theorem B4098059 : Blo 1213424 4098059 := bstep (se 1 (by rfl) ⟨3073544, by rfl⟩ : syracuseStep 4098059 = 6147089) B6147089
theorem B1820687 : Blo 1213424 1820687 := bstep (se 1 (by rfl) ⟨1365515, by rfl⟩ : syracuseStep 1820687 = 2731031) B2731031
theorem B1214479 : Blo 1213424 1214479 := bstep (se 1 (by rfl) ⟨910859, by rfl⟩ : syracuseStep 1214479 = 1821719) B1821719
theorem B1820729 : Blo 1213424 1820729 := bstep (se 2 (by rfl) ⟨682773, by rfl⟩ : syracuseStep 1820729 = 1365547) B1365547
theorem B1296443 : Blo 1213424 1296443 := bstep (se 1 (by rfl) ⟨972332, by rfl⟩ : syracuseStep 1296443 = 1944665) B1944665
theorem B1214523 : Blo 1213424 1214523 := bstep (se 1 (by rfl) ⟨910892, by rfl⟩ : syracuseStep 1214523 = 1821785) B1821785
theorem B4614205 : Blo 1213424 4614205 := bstep (se 3 (by rfl) ⟨865163, by rfl⟩ : syracuseStep 4614205 = 1730327) B1730327
theorem B4376663 : Blo 1213424 4376663 := bstep (se 1 (by rfl) ⟨3282497, by rfl⟩ : syracuseStep 4376663 = 6564995) B6564995
theorem B2304119 : Blo 1213424 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B4098167 : Blo 1213424 4098167 := bstep (se 1 (by rfl) ⟨3073625, by rfl⟩ : syracuseStep 4098167 = 6147251) B6147251
theorem B1820807 : Blo 1213424 1820807 := bstep (se 1 (by rfl) ⟨1365605, by rfl⟩ : syracuseStep 1820807 = 2731211) B2731211
theorem B3074183 : Blo 1213424 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B1214599 : Blo 1213424 1214599 := bstep (se 1 (by rfl) ⟨910949, by rfl⟩ : syracuseStep 1214599 = 1821899) B1821899
theorem B1214607 : Blo 1213424 1214607 := bstep (se 1 (by rfl) ⟨910955, by rfl⟩ : syracuseStep 1214607 = 1821911) B1821911
theorem B1820843 : Blo 1213424 1820843 := bstep (se 1 (by rfl) ⟨1365632, by rfl⟩ : syracuseStep 1820843 = 2731265) B2731265
theorem B3074233 : Blo 1213424 3074233 := bstep (se 2 (by rfl) ⟨1152837, by rfl⟩ : syracuseStep 3074233 = 2305675) B2305675
theorem B1214651 : Blo 1213424 1214651 := bstep (se 1 (by rfl) ⟨910988, by rfl⟩ : syracuseStep 1214651 = 1821977) B1821977
theorem B1820873 : Blo 1213424 1820873 := bstep (se 2 (by rfl) ⟨682827, by rfl⟩ : syracuseStep 1820873 = 1365655) B1365655
theorem B1214727 : Blo 1213424 1214727 := bstep (se 1 (by rfl) ⟨911045, by rfl⟩ : syracuseStep 1214727 = 1822091) B1822091
theorem B1214735 : Blo 1213424 1214735 := bstep (se 1 (by rfl) ⟨911051, by rfl⟩ : syracuseStep 1214735 = 1822103) B1822103
theorem B2050319 : Blo 1213424 2050319 := bstep (se 1 (by rfl) ⟨1537739, by rfl⟩ : syracuseStep 2050319 = 3075479) B3075479
theorem B1820987 : Blo 1213424 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B1214779 : Blo 1213424 1214779 := bstep (se 1 (by rfl) ⟨911084, by rfl⟩ : syracuseStep 1214779 = 1822169) B1822169
theorem B1821047 : Blo 1213424 1821047 := bstep (se 1 (by rfl) ⟨1365785, by rfl⟩ : syracuseStep 1821047 = 2731571) B2731571
theorem B1214855 : Blo 1213424 1214855 := bstep (se 1 (by rfl) ⟨911141, by rfl⟩ : syracuseStep 1214855 = 1822283) B1822283
theorem B1821071 : Blo 1213424 1821071 := bstep (se 1 (by rfl) ⟨1365803, by rfl⟩ : syracuseStep 1821071 = 2731607) B2731607
theorem B1214863 : Blo 1213424 1214863 := bstep (se 1 (by rfl) ⟨911147, by rfl⟩ : syracuseStep 1214863 = 1822295) B1822295
theorem B1821113 : Blo 1213424 1821113 := bstep (se 2 (by rfl) ⟨682917, by rfl⟩ : syracuseStep 1821113 = 1365835) B1365835
theorem B1214907 : Blo 1213424 1214907 := bstep (se 1 (by rfl) ⟨911180, by rfl⟩ : syracuseStep 1214907 = 1822361) B1822361
theorem B1821191 : Blo 1213424 1821191 := bstep (se 1 (by rfl) ⟨1365893, by rfl⟩ : syracuseStep 1821191 = 2731787) B2731787
theorem B1214983 : Blo 1213424 1214983 := bstep (se 1 (by rfl) ⟨911237, by rfl⟩ : syracuseStep 1214983 = 1822475) B1822475
theorem B1214991 : Blo 1213424 1214991 := bstep (se 1 (by rfl) ⟨911243, by rfl⟩ : syracuseStep 1214991 = 1822487) B1822487
theorem B2460203 : Blo 1213424 2460203 := bstep (se 1 (by rfl) ⟨1845152, by rfl⟩ : syracuseStep 2460203 = 3690305) B3690305
theorem B6146603 : Blo 1213424 6146603 := bstep (se 1 (by rfl) ⟨4609952, by rfl⟩ : syracuseStep 6146603 = 9219905) B9219905
theorem B1821227 : Blo 1213424 1821227 := bstep (se 1 (by rfl) ⟨1365920, by rfl⟩ : syracuseStep 1821227 = 2731841) B2731841
theorem B1215035 : Blo 1213424 1215035 := bstep (se 1 (by rfl) ⟨911276, by rfl⟩ : syracuseStep 1215035 = 1822553) B1822553
theorem B12462659 : Blo 1213424 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B1821257 : Blo 1213424 1821257 := bstep (se 2 (by rfl) ⟨682971, by rfl⟩ : syracuseStep 1821257 = 1365943) B1365943
theorem B14248549 : Blo 1213424 14248549 := bstep (se 4 (by rfl) ⟨1335801, by rfl⟩ : syracuseStep 14248549 = 2671603) B2671603
theorem B1215111 : Blo 1213424 1215111 := bstep (se 1 (by rfl) ⟨911333, by rfl⟩ : syracuseStep 1215111 = 1822667) B1822667
theorem B1215119 : Blo 1213424 1215119 := bstep (se 1 (by rfl) ⟨911339, by rfl⟩ : syracuseStep 1215119 = 1822679) B1822679
theorem B1845931 : Blo 1213424 1845931 := bstep (se 1 (by rfl) ⟨1384448, by rfl⟩ : syracuseStep 1845931 = 2768897) B2768897
theorem B1821371 : Blo 1213424 1821371 := bstep (se 1 (by rfl) ⟨1366028, by rfl⟩ : syracuseStep 1821371 = 2732057) B2732057
theorem B1215163 : Blo 1213424 1215163 := bstep (se 1 (by rfl) ⟨911372, by rfl⟩ : syracuseStep 1215163 = 1822745) B1822745
theorem B4098761 : Blo 1213424 4098761 := bstep (se 2 (by rfl) ⟨1537035, by rfl⟩ : syracuseStep 4098761 = 3074071) B3074071
theorem B1821431 : Blo 1213424 1821431 := bstep (se 1 (by rfl) ⟨1366073, by rfl⟩ : syracuseStep 1821431 = 2732147) B2732147
theorem B4926209 : Blo 1213424 4926209 := bstep (se 2 (by rfl) ⟨1847328, by rfl⟩ : syracuseStep 4926209 = 3694657) B3694657
theorem B1215239 : Blo 1213424 1215239 := bstep (se 1 (by rfl) ⟨911429, by rfl⟩ : syracuseStep 1215239 = 1822859) B1822859
theorem B2919179 : Blo 1213424 2919179 := bstep (se 1 (by rfl) ⟨2189384, by rfl⟩ : syracuseStep 2919179 = 4378769) B4378769
theorem B1821455 : Blo 1213424 1821455 := bstep (se 1 (by rfl) ⟨1366091, by rfl⟩ : syracuseStep 1821455 = 2732183) B2732183
theorem B3074831 : Blo 1213424 3074831 := bstep (se 1 (by rfl) ⟨2306123, by rfl⟩ : syracuseStep 3074831 = 4612247) B4612247
theorem B1215247 : Blo 1213424 1215247 := bstep (se 1 (by rfl) ⟨911435, by rfl⟩ : syracuseStep 1215247 = 1822871) B1822871
theorem B2050859 : Blo 1213424 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B1821497 : Blo 1213424 1821497 := bstep (se 2 (by rfl) ⟨683061, by rfl⟩ : syracuseStep 1821497 = 1366123) B1366123
theorem B1215291 : Blo 1213424 1215291 := bstep (se 1 (by rfl) ⟨911468, by rfl⟩ : syracuseStep 1215291 = 1822937) B1822937
theorem B2730887 : Blo 1213424 2730887 := bstep (se 1 (by rfl) ⟨2048165, by rfl⟩ : syracuseStep 2730887 = 4096331) B4096331
theorem B1821575 : Blo 1213424 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B1215367 : Blo 1213424 1215367 := bstep (se 1 (by rfl) ⟨911525, by rfl⟩ : syracuseStep 1215367 = 1823051) B1823051
theorem B1215375 : Blo 1213424 1215375 := bstep (se 1 (by rfl) ⟨911531, by rfl⟩ : syracuseStep 1215375 = 1823063) B1823063
theorem B1821611 : Blo 1213424 1821611 := bstep (se 1 (by rfl) ⟨1366208, by rfl⟩ : syracuseStep 1821611 = 2732417) B2732417
theorem B1215419 : Blo 1213424 1215419 := bstep (se 1 (by rfl) ⟨911564, by rfl⟩ : syracuseStep 1215419 = 1823129) B1823129
theorem B1821641 : Blo 1213424 1821641 := bstep (se 2 (by rfl) ⟨683115, by rfl⟩ : syracuseStep 1821641 = 1366231) B1366231
theorem B3460097 : Blo 1213424 3460097 := bstep (se 2 (by rfl) ⟨1297536, by rfl⟩ : syracuseStep 3460097 = 2595073) B2595073
theorem B2731067 : Blo 1213424 2731067 := bstep (se 1 (by rfl) ⟨2048300, by rfl⟩ : syracuseStep 2731067 = 4096601) B4096601
theorem B1821755 : Blo 1213424 1821755 := bstep (se 1 (by rfl) ⟨1366316, by rfl⟩ : syracuseStep 1821755 = 2732633) B2732633
theorem B1821815 : Blo 1213424 1821815 := bstep (se 1 (by rfl) ⟨1366361, by rfl⟩ : syracuseStep 1821815 = 2732723) B2732723
theorem B15551621 : Blo 1213424 15551621 := bstep (se 4 (by rfl) ⟨1457964, by rfl⟩ : syracuseStep 15551621 = 2915929) B2915929
theorem B1821839 : Blo 1213424 1821839 := bstep (se 1 (by rfl) ⟨1366379, by rfl⟩ : syracuseStep 1821839 = 2732759) B2732759
theorem B2591929 : Blo 1213424 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B2731193 : Blo 1213424 2731193 := bstep (se 2 (by rfl) ⟨1024197, by rfl⟩ : syracuseStep 2731193 = 2048395) B2048395
theorem B1821881 : Blo 1213424 1821881 := bstep (se 2 (by rfl) ⟨683205, by rfl⟩ : syracuseStep 1821881 = 1366411) B1366411
theorem B1821959 : Blo 1213424 1821959 := bstep (se 1 (by rfl) ⟨1366469, by rfl⟩ : syracuseStep 1821959 = 2732939) B2732939
theorem B1821995 : Blo 1213424 1821995 := bstep (se 1 (by rfl) ⟨1366496, by rfl⟩ : syracuseStep 1821995 = 2732993) B2732993
theorem B1822025 : Blo 1213424 1822025 := bstep (se 2 (by rfl) ⟨683259, by rfl⟩ : syracuseStep 1822025 = 1366519) B1366519
theorem B4099463 : Blo 1213424 4099463 := bstep (se 1 (by rfl) ⟨3074597, by rfl⟩ : syracuseStep 4099463 = 6149195) B6149195
theorem B1822139 : Blo 1213424 1822139 := bstep (se 1 (by rfl) ⟨1366604, by rfl⟩ : syracuseStep 1822139 = 2733209) B2733209
theorem B3075529 : Blo 1213424 3075529 := bstep (se 2 (by rfl) ⟨1153323, by rfl⟩ : syracuseStep 3075529 = 2306647) B2306647
theorem B3460553 : Blo 1213424 3460553 := bstep (se 2 (by rfl) ⟨1297707, by rfl⟩ : syracuseStep 3460553 = 2595415) B2595415
theorem B6655441 : Blo 1213424 6655441 := bstep (se 2 (by rfl) ⟨2495790, by rfl⟩ : syracuseStep 6655441 = 4991581) B4991581
theorem B1822199 : Blo 1213424 1822199 := bstep (se 1 (by rfl) ⟨1366649, by rfl⟩ : syracuseStep 1822199 = 2733299) B2733299
theorem B2731535 : Blo 1213424 2731535 := bstep (se 1 (by rfl) ⟨2048651, by rfl⟩ : syracuseStep 2731535 = 4097303) B4097303
theorem B1822223 : Blo 1213424 1822223 := bstep (se 1 (by rfl) ⟨1366667, by rfl⟩ : syracuseStep 1822223 = 2733335) B2733335
theorem B2731553 : Blo 1213424 2731553 := bstep (se 2 (by rfl) ⟨1024332, by rfl⟩ : syracuseStep 2731553 = 2048665) B2048665
theorem B1822265 : Blo 1213424 1822265 := bstep (se 2 (by rfl) ⟨683349, by rfl⟩ : syracuseStep 1822265 = 1366699) B1366699
theorem B3075671 : Blo 1213424 3075671 := bstep (se 1 (by rfl) ⟨2306753, by rfl⟩ : syracuseStep 3075671 = 4613507) B4613507
theorem B26267237 : Blo 1213424 26267237 := bstep (se 4 (by rfl) ⟨2462553, by rfl⟩ : syracuseStep 26267237 = 4925107) B4925107
theorem B6565495 : Blo 1213424 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B1822343 : Blo 1213424 1822343 := bstep (se 1 (by rfl) ⟨1366757, by rfl⟩ : syracuseStep 1822343 = 2733515) B2733515
theorem B1822379 : Blo 1213424 1822379 := bstep (se 1 (by rfl) ⟨1366784, by rfl⟩ : syracuseStep 1822379 = 2733569) B2733569
theorem B2305721 : Blo 1213424 2305721 := bstep (se 2 (by rfl) ⟨864645, by rfl⟩ : syracuseStep 2305721 = 1729291) B1729291
theorem B2920121 : Blo 1213424 2920121 := bstep (se 2 (by rfl) ⟨1095045, by rfl⟩ : syracuseStep 2920121 = 2190091) B2190091
theorem B1822409 : Blo 1213424 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B4099841 : Blo 1213424 4099841 := bstep (se 2 (by rfl) ⟨1537440, by rfl⟩ : syracuseStep 4099841 = 3074881) B3074881
theorem B3690269 : Blo 1213424 3690269 := bstep (se 3 (by rfl) ⟨691925, by rfl⟩ : syracuseStep 3690269 = 1383851) B1383851
theorem B6147899 : Blo 1213424 6147899 := bstep (se 1 (by rfl) ⟨4610924, by rfl⟩ : syracuseStep 6147899 = 9221849) B9221849
theorem B1847099 : Blo 1213424 1847099 := bstep (se 1 (by rfl) ⟨1385324, by rfl⟩ : syracuseStep 1847099 = 2770649) B2770649
theorem B1822523 : Blo 1213424 1822523 := bstep (se 1 (by rfl) ⟨1366892, by rfl⟩ : syracuseStep 1822523 = 2733785) B2733785
theorem B2731895 : Blo 1213424 2731895 := bstep (se 1 (by rfl) ⟨2048921, by rfl⟩ : syracuseStep 2731895 = 4097843) B4097843
theorem B1822583 : Blo 1213424 1822583 := bstep (se 1 (by rfl) ⟨1366937, by rfl⟩ : syracuseStep 1822583 = 2733875) B2733875
theorem B1822607 : Blo 1213424 1822607 := bstep (se 1 (by rfl) ⟨1366955, by rfl⟩ : syracuseStep 1822607 = 2733911) B2733911
theorem B1822649 : Blo 1213424 1822649 := bstep (se 2 (by rfl) ⟨683493, by rfl⟩ : syracuseStep 1822649 = 1366987) B1366987
theorem B5541841 : Blo 1213424 5541841 := bstep (se 2 (by rfl) ⟨2078190, by rfl⟩ : syracuseStep 5541841 = 4156381) B4156381
theorem B6148061 : Blo 1213424 6148061 := bstep (se 3 (by rfl) ⟨1152761, by rfl⟩ : syracuseStep 6148061 = 2305523) B2305523
theorem B1822727 : Blo 1213424 1822727 := bstep (se 1 (by rfl) ⟨1367045, by rfl⟩ : syracuseStep 1822727 = 2734091) B2734091
theorem B2306063 : Blo 1213424 2306063 := bstep (se 1 (by rfl) ⟨1729547, by rfl⟩ : syracuseStep 2306063 = 3459095) B3459095
theorem B2732075 : Blo 1213424 2732075 := bstep (se 1 (by rfl) ⟨2049056, by rfl⟩ : syracuseStep 2732075 = 4098113) B4098113
theorem B1822763 : Blo 1213424 1822763 := bstep (se 1 (by rfl) ⟨1367072, by rfl⟩ : syracuseStep 1822763 = 2734145) B2734145
theorem B13127741 : Blo 1213424 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B1822793 : Blo 1213424 1822793 := bstep (se 2 (by rfl) ⟨683547, by rfl⟩ : syracuseStep 1822793 = 1367095) B1367095
theorem B1822907 : Blo 1213424 1822907 := bstep (se 1 (by rfl) ⟨1367180, by rfl⟩ : syracuseStep 1822907 = 2734361) B2734361
theorem B1822967 : Blo 1213424 1822967 := bstep (se 1 (by rfl) ⟨1367225, by rfl⟩ : syracuseStep 1822967 = 2734451) B2734451
theorem B1847567 : Blo 1213424 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B1822991 : Blo 1213424 1822991 := bstep (se 1 (by rfl) ⟨1367243, by rfl⟩ : syracuseStep 1822991 = 2734487) B2734487
theorem B6148385 : Blo 1213424 6148385 := bstep (se 2 (by rfl) ⟨2305644, by rfl⟩ : syracuseStep 6148385 = 4611289) B4611289
theorem B1823033 : Blo 1213424 1823033 := bstep (se 2 (by rfl) ⟨683637, by rfl⟩ : syracuseStep 1823033 = 1367275) B1367275
theorem B9843079 : Blo 1213424 9843079 := bstep (se 1 (by rfl) ⟨7382309, by rfl⟩ : syracuseStep 9843079 = 14764619) B14764619
theorem B1823111 : Blo 1213424 1823111 := bstep (se 1 (by rfl) ⟨1367333, by rfl⟩ : syracuseStep 1823111 = 2734667) B2734667
theorem B2732435 : Blo 1213424 2732435 := bstep (se 1 (by rfl) ⟨2049326, by rfl⟩ : syracuseStep 2732435 = 4098653) B4098653
theorem B2732489 : Blo 1213424 2732489 := bstep (se 2 (by rfl) ⟨1024683, by rfl⟩ : syracuseStep 2732489 = 2049367) B2049367
theorem B4100651 : Blo 1213424 4100651 := bstep (se 1 (by rfl) ⟨3075488, by rfl⟩ : syracuseStep 4100651 = 6150977) B6150977
theorem B2462327 : Blo 1213424 2462327 := bstep (se 1 (by rfl) ⟨1846745, by rfl⟩ : syracuseStep 2462327 = 3693491) B3693491
theorem B4920097 : Blo 1213424 4920097 := bstep (se 2 (by rfl) ⟨1845036, by rfl⟩ : syracuseStep 4920097 = 3690073) B3690073
theorem B2593595 : Blo 1213424 2593595 := bstep (se 1 (by rfl) ⟨1945196, by rfl⟩ : syracuseStep 2593595 = 3890393) B3890393
theorem B2306875 : Blo 1213424 2306875 := bstep (se 1 (by rfl) ⟨1730156, by rfl⟩ : syracuseStep 2306875 = 3460313) B3460313
theorem B4674439 : Blo 1213424 4674439 := bstep (se 1 (by rfl) ⟨3505829, by rfl⟩ : syracuseStep 4674439 = 7011659) B7011659
theorem B2306951 : Blo 1213424 2306951 := bstep (se 1 (by rfl) ⟨1730213, by rfl⟩ : syracuseStep 2306951 = 3460427) B3460427
theorem B14398361 : Blo 1213424 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B4379545 : Blo 1213424 4379545 := bstep (se 2 (by rfl) ⟨1642329, by rfl⟩ : syracuseStep 4379545 = 3284659) B3284659
theorem B6919121 : Blo 1213424 6919121 := bstep (se 2 (by rfl) ⟨2594670, by rfl⟩ : syracuseStep 6919121 = 5189341) B5189341
theorem B1946683 : Blo 1213424 1946683 := bstep (se 1 (by rfl) ⟨1460012, by rfl⟩ : syracuseStep 1946683 = 2920025) B2920025
theorem B5190743 : Blo 1213424 5190743 := bstep (se 1 (by rfl) ⟨3893057, by rfl⟩ : syracuseStep 5190743 = 7786115) B7786115
theorem B2733191 : Blo 1213424 2733191 := bstep (se 1 (by rfl) ⟨2049893, by rfl⟩ : syracuseStep 2733191 = 4099787) B4099787
theorem B7484609 : Blo 1213424 7484609 := bstep (se 2 (by rfl) ⟨2806728, by rfl⟩ : syracuseStep 7484609 = 5613457) B5613457
theorem B6149357 : Blo 1213424 6149357 := bstep (se 3 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 6149357 = 2306009) B2306009
theorem B37418273 : Blo 1213424 37418273 := bstep (se 2 (by rfl) ⟨14031852, by rfl⟩ : syracuseStep 37418273 = 28063705) B28063705
theorem B2307361 : Blo 1213424 2307361 := bstep (se 2 (by rfl) ⟨865260, by rfl⟩ : syracuseStep 2307361 = 1730521) B1730521
theorem B2733371 : Blo 1213424 2733371 := bstep (se 1 (by rfl) ⟨2050028, by rfl⟩ : syracuseStep 2733371 = 4100057) B4100057
theorem B6919577 : Blo 1213424 6919577 := bstep (se 2 (by rfl) ⟨2594841, by rfl⟩ : syracuseStep 6919577 = 5189683) B5189683
theorem B19699129 : Blo 1213424 19699129 := bstep (se 2 (by rfl) ⟨7387173, by rfl⟩ : syracuseStep 19699129 = 14774347) B14774347
theorem B2733497 : Blo 1213424 2733497 := bstep (se 2 (by rfl) ⟨1025061, by rfl⟩ : syracuseStep 2733497 = 2050123) B2050123
theorem B1365511 : Blo 1213424 1365511 := bstep (se 1 (by rfl) ⟨1024133, by rfl⟩ : syracuseStep 1365511 = 2048267) B2048267
theorem B1365691 : Blo 1213424 1365691 := bstep (se 1 (by rfl) ⟨1024268, by rfl⟩ : syracuseStep 1365691 = 2048537) B2048537
theorem B2733839 : Blo 1213424 2733839 := bstep (se 1 (by rfl) ⟨2050379, by rfl⟩ : syracuseStep 2733839 = 4100759) B4100759
theorem B2733857 : Blo 1213424 2733857 := bstep (se 2 (by rfl) ⟨1025196, by rfl⟩ : syracuseStep 2733857 = 2050393) B2050393
theorem B4101947 : Blo 1213424 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B13842251 : Blo 1213424 13842251 := bstep (se 1 (by rfl) ⟨10381688, by rfl⟩ : syracuseStep 13842251 = 20763377) B20763377
theorem B6150167 : Blo 1213424 6150167 := bstep (se 1 (by rfl) ⟨4612625, by rfl⟩ : syracuseStep 6150167 = 9225251) B9225251
theorem B2955323 : Blo 1213424 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B4610135 : Blo 1213424 4610135 := bstep (se 1 (by rfl) ⟨3457601, by rfl⟩ : syracuseStep 4610135 = 6915203) B6915203
theorem B2734199 : Blo 1213424 2734199 := bstep (se 1 (by rfl) ⟨2050649, by rfl⟩ : syracuseStep 2734199 = 4101299) B4101299
theorem B1366159 : Blo 1213424 1366159 := bstep (se 1 (by rfl) ⟨1024619, by rfl⟩ : syracuseStep 1366159 = 2049239) B2049239
theorem B5839085 : Blo 1213424 5839085 := bstep (se 3 (by rfl) ⟨1094828, by rfl⟩ : syracuseStep 5839085 = 2189657) B2189657
theorem B3283211 : Blo 1213424 3283211 := bstep (se 1 (by rfl) ⟨2462408, by rfl⟩ : syracuseStep 3283211 = 4924817) B4924817
theorem B2595115 : Blo 1213424 2595115 := bstep (se 1 (by rfl) ⟨1946336, by rfl⟩ : syracuseStep 2595115 = 3892673) B3892673
theorem B2734379 : Blo 1213424 2734379 := bstep (se 1 (by rfl) ⟨2050784, by rfl⟩ : syracuseStep 2734379 = 4101569) B4101569
theorem B4610621 : Blo 1213424 4610621 := bstep (se 3 (by rfl) ⟨864491, by rfl⟩ : syracuseStep 4610621 = 1728983) B1728983
theorem B6232643 : Blo 1213424 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B22166135 : Blo 1213424 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B1366663 : Blo 1213424 1366663 := bstep (se 1 (by rfl) ⟨1024997, by rfl⟩ : syracuseStep 1366663 = 2049995) B2049995
theorem B1366843 : Blo 1213424 1366843 := bstep (se 1 (by rfl) ⟨1025132, by rfl⟩ : syracuseStep 1366843 = 2050265) B2050265
theorem B26246051 : Blo 1213424 26246051 := bstep (se 1 (by rfl) ⟨19684538, by rfl⟩ : syracuseStep 26246051 = 39369077) B39369077
theorem B6912971 : Blo 1213424 6912971 := bstep (se 1 (by rfl) ⟨5184728, by rfl⟩ : syracuseStep 6912971 = 10369457) B10369457
theorem B3890263 : Blo 1213424 3890263 := bstep (se 1 (by rfl) ⟨2917697, by rfl⟩ : syracuseStep 3890263 = 5835395) B5835395
theorem B11238533 : Blo 1213424 11238533 := bstep (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) B2107225
theorem B1367311 : Blo 1213424 1367311 := bstep (se 1 (by rfl) ⟨1025483, by rfl⟩ : syracuseStep 1367311 = 2050967) B2050967
theorem B3456371 : Blo 1213424 3456371 := bstep (se 1 (by rfl) ⟨2592278, by rfl⟩ : syracuseStep 3456371 = 5184557) B5184557
theorem B20741507 : Blo 1213424 20741507 := bstep (se 1 (by rfl) ⟨15556130, by rfl⟩ : syracuseStep 20741507 = 31112261) B31112261
theorem B6561233 : Blo 1213424 6561233 := bstep (se 2 (by rfl) ⟨2460462, by rfl⟩ : syracuseStep 6561233 = 4920925) B4920925
theorem B9215531 : Blo 1213424 9215531 := bstep (se 1 (by rfl) ⟨6911648, by rfl⟩ : syracuseStep 9215531 = 13823297) B13823297
theorem B7200323 : Blo 1213424 7200323 := bstep (se 1 (by rfl) ⟨5400242, by rfl⟩ : syracuseStep 7200323 = 10800485) B10800485
theorem B4095575 : Blo 1213424 4095575 := bstep (se 1 (by rfl) ⟨3071681, by rfl⟩ : syracuseStep 4095575 = 6143363) B6143363
theorem B3071641 : Blo 1213424 3071641 := bstep (se 2 (by rfl) ⟨1151865, by rfl⟩ : syracuseStep 3071641 = 2303731) B2303731
theorem B13139633 : Blo 1213424 13139633 := bstep (se 2 (by rfl) ⟨4927362, by rfl⟩ : syracuseStep 13139633 = 9854725) B9854725
theorem B2047673 : Blo 1213424 2047673 := bstep (se 2 (by rfl) ⟨767877, by rfl⟩ : syracuseStep 2047673 = 1535755) B1535755
theorem B84156205 : Blo 1213424 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B3071803 : Blo 1213424 3071803 := bstep (se 1 (by rfl) ⟨2303852, by rfl⟩ : syracuseStep 3071803 = 4607705) B4607705
theorem B3456827 : Blo 1213424 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B25288523 : Blo 1213424 25288523 := bstep (se 1 (by rfl) ⟨18966392, by rfl⟩ : syracuseStep 25288523 = 37932785) B37932785
theorem B1728391 : Blo 1213424 1728391 := bstep (se 1 (by rfl) ⟨1296293, by rfl⟩ : syracuseStep 1728391 = 2592587) B2592587
theorem B3071945 : Blo 1213424 3071945 := bstep (se 2 (by rfl) ⟨1151979, by rfl⟩ : syracuseStep 3071945 = 2303959) B2303959
theorem B4612049 : Blo 1213424 4612049 := bstep (se 2 (by rfl) ⟨1729518, by rfl⟩ : syracuseStep 4612049 = 3459037) B3459037
theorem B1458167 : Blo 1213424 1458167 := bstep (se 1 (by rfl) ⟨1093625, by rfl⟩ : syracuseStep 1458167 = 2187251) B2187251
theorem B4096007 : Blo 1213424 4096007 := bstep (se 1 (by rfl) ⟨3072005, by rfl⟩ : syracuseStep 4096007 = 6144011) B6144011
theorem B6152273 : Blo 1213424 6152273 := bstep (se 2 (by rfl) ⟨2307102, by rfl⟩ : syracuseStep 6152273 = 4614205) B4614205
theorem B4096115 : Blo 1213424 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B7880861 : Blo 1213424 7880861 := bstep (se 3 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 7880861 = 2955323) B2955323
theorem B3457181 : Blo 1213424 3457181 := bstep (se 3 (by rfl) ⟨648221, by rfl⟩ : syracuseStep 3457181 = 1296443) B1296443
theorem B4096385 : Blo 1213424 4096385 := bstep (se 2 (by rfl) ⟨1536144, by rfl⟩ : syracuseStep 4096385 = 3072289) B3072289
theorem B2916737 : Blo 1213424 2916737 := bstep (se 2 (by rfl) ⟨1093776, by rfl⟩ : syracuseStep 2916737 = 2187553) B2187553
theorem B13124105 : Blo 1213424 13124105 := bstep (se 2 (by rfl) ⟨4921539, by rfl⟩ : syracuseStep 13124105 = 9843079) B9843079
theorem B4375079 : Blo 1213424 4375079 := bstep (se 1 (by rfl) ⟨3281309, by rfl⟩ : syracuseStep 4375079 = 6562619) B6562619
theorem B1729063 : Blo 1213424 1729063 := bstep (se 1 (by rfl) ⟨1296797, by rfl⟩ : syracuseStep 1729063 = 2593595) B2593595
theorem B2048591 : Blo 1213424 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B4612747 : Blo 1213424 4612747 := bstep (se 1 (by rfl) ⟨3459560, by rfl⟩ : syracuseStep 4612747 = 6919121) B6919121
theorem B75776663 : Blo 1213424 75776663 := bstep (se 1 (by rfl) ⟨56832497, by rfl⟩ : syracuseStep 75776663 = 113664995) B113664995
theorem B18998065 : Blo 1213424 18998065 := bstep (se 2 (by rfl) ⟨7124274, by rfl⟩ : syracuseStep 18998065 = 14248549) B14248549
theorem B24945515 : Blo 1213424 24945515 := bstep (se 1 (by rfl) ⟨18709136, by rfl⟩ : syracuseStep 24945515 = 37418273) B37418273
theorem B4613051 : Blo 1213424 4613051 := bstep (se 1 (by rfl) ⟨3459788, by rfl⟩ : syracuseStep 4613051 = 6919577) B6919577
theorem B9216989 : Blo 1213424 9216989 := bstep (se 3 (by rfl) ⟨1728185, by rfl⟩ : syracuseStep 9216989 = 3456371) B3456371
theorem B7783397 : Blo 1213424 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B1213479 : Blo 1213424 1213479 := bstep (se 1 (by rfl) ⟨910109, by rfl⟩ : syracuseStep 1213479 = 1820219) B1820219
theorem B1213519 : Blo 1213424 1213519 := bstep (se 1 (by rfl) ⟨910139, by rfl⟩ : syracuseStep 1213519 = 1820279) B1820279
theorem B1213535 : Blo 1213424 1213535 := bstep (se 1 (by rfl) ⟨910151, by rfl⟩ : syracuseStep 1213535 = 1820303) B1820303
theorem B1213563 : Blo 1213424 1213563 := bstep (se 1 (by rfl) ⟨910172, by rfl⟩ : syracuseStep 1213563 = 1820345) B1820345
theorem B4097195 : Blo 1213424 4097195 := bstep (se 1 (by rfl) ⟨3072896, by rfl⟩ : syracuseStep 4097195 = 6145793) B6145793
theorem B1213615 : Blo 1213424 1213615 := bstep (se 1 (by rfl) ⟨910211, by rfl⟩ : syracuseStep 1213615 = 1820423) B1820423
theorem B1213639 : Blo 1213424 1213639 := bstep (se 1 (by rfl) ⟨910229, by rfl⟩ : syracuseStep 1213639 = 1820459) B1820459
theorem B1213659 : Blo 1213424 1213659 := bstep (se 1 (by rfl) ⟨910244, by rfl⟩ : syracuseStep 1213659 = 1820489) B1820489
theorem B1213735 : Blo 1213424 1213735 := bstep (se 1 (by rfl) ⟨910301, by rfl⟩ : syracuseStep 1213735 = 1820603) B1820603
theorem B1213775 : Blo 1213424 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B1213791 : Blo 1213424 1213791 := bstep (se 1 (by rfl) ⟨910343, by rfl⟩ : syracuseStep 1213791 = 1820687) B1820687
theorem B1213819 : Blo 1213424 1213819 := bstep (se 1 (by rfl) ⟨910364, by rfl⟩ : syracuseStep 1213819 = 1820729) B1820729
theorem B3073423 : Blo 1213424 3073423 := bstep (se 1 (by rfl) ⟨2305067, by rfl⟩ : syracuseStep 3073423 = 4610135) B4610135
theorem B2917775 : Blo 1213424 2917775 := bstep (se 1 (by rfl) ⟨2188331, by rfl⟩ : syracuseStep 2917775 = 4376663) B4376663
theorem B1213871 : Blo 1213424 1213871 := bstep (se 1 (by rfl) ⟨910403, by rfl⟩ : syracuseStep 1213871 = 1820807) B1820807
theorem B2049455 : Blo 1213424 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B1213895 : Blo 1213424 1213895 := bstep (se 1 (by rfl) ⟨910421, by rfl⟩ : syracuseStep 1213895 = 1820843) B1820843
theorem B5187017 : Blo 1213424 5187017 := bstep (se 2 (by rfl) ⟨1945131, by rfl⟩ : syracuseStep 5187017 = 3890263) B3890263
theorem B1213915 : Blo 1213424 1213915 := bstep (se 1 (by rfl) ⟨910436, by rfl⟩ : syracuseStep 1213915 = 1820873) B1820873
theorem B1213991 : Blo 1213424 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B1214031 : Blo 1213424 1214031 := bstep (se 1 (by rfl) ⟨910523, by rfl⟩ : syracuseStep 1214031 = 1821047) B1821047
theorem B1214047 : Blo 1213424 1214047 := bstep (se 1 (by rfl) ⟨910535, by rfl⟩ : syracuseStep 1214047 = 1821071) B1821071
theorem B1214075 : Blo 1213424 1214075 := bstep (se 1 (by rfl) ⟨910556, by rfl⟩ : syracuseStep 1214075 = 1821113) B1821113
theorem B1214127 : Blo 1213424 1214127 := bstep (se 1 (by rfl) ⟨910595, by rfl⟩ : syracuseStep 1214127 = 1821191) B1821191
theorem B1640135 : Blo 1213424 1640135 := bstep (se 1 (by rfl) ⟨1230101, by rfl⟩ : syracuseStep 1640135 = 2460203) B2460203
theorem B4097735 : Blo 1213424 4097735 := bstep (se 1 (by rfl) ⟨3073301, by rfl⟩ : syracuseStep 4097735 = 6146603) B6146603
theorem B1214151 : Blo 1213424 1214151 := bstep (se 1 (by rfl) ⟨910613, by rfl⟩ : syracuseStep 1214151 = 1821227) B1821227
theorem B3073747 : Blo 1213424 3073747 := bstep (se 1 (by rfl) ⟨2305310, by rfl⟩ : syracuseStep 3073747 = 4610621) B4610621
theorem B8308439 : Blo 1213424 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B4155095 : Blo 1213424 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B1214171 : Blo 1213424 1214171 := bstep (se 1 (by rfl) ⟨910628, by rfl⟩ : syracuseStep 1214171 = 1821257) B1821257
theorem B1214247 : Blo 1213424 1214247 := bstep (se 1 (by rfl) ⟨910685, by rfl⟩ : syracuseStep 1214247 = 1821371) B1821371
theorem B1214287 : Blo 1213424 1214287 := bstep (se 1 (by rfl) ⟨910715, by rfl⟩ : syracuseStep 1214287 = 1821431) B1821431
theorem B1214303 : Blo 1213424 1214303 := bstep (se 1 (by rfl) ⟨910727, by rfl⟩ : syracuseStep 1214303 = 1821455) B1821455
theorem B2049887 : Blo 1213424 2049887 := bstep (se 1 (by rfl) ⟨1537415, by rfl⟩ : syracuseStep 2049887 = 3074831) B3074831
theorem B1214331 : Blo 1213424 1214331 := bstep (se 1 (by rfl) ⟨910748, by rfl⟩ : syracuseStep 1214331 = 1821497) B1821497
theorem B26265505 : Blo 1213424 26265505 := bstep (se 2 (by rfl) ⟨9849564, by rfl⟩ : syracuseStep 26265505 = 19699129) B19699129
theorem B1820591 : Blo 1213424 1820591 := bstep (se 1 (by rfl) ⟨1365443, by rfl⟩ : syracuseStep 1820591 = 2730887) B2730887
theorem B1214383 : Blo 1213424 1214383 := bstep (se 1 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 1214383 = 1821575) B1821575
theorem B8873921 : Blo 1213424 8873921 := bstep (se 2 (by rfl) ⟨3327720, by rfl⟩ : syracuseStep 8873921 = 6655441) B6655441
theorem B1214407 : Blo 1213424 1214407 := bstep (se 1 (by rfl) ⟨910805, by rfl⟩ : syracuseStep 1214407 = 1821611) B1821611
theorem B1214427 : Blo 1213424 1214427 := bstep (se 1 (by rfl) ⟨910820, by rfl⟩ : syracuseStep 1214427 = 1821641) B1821641
theorem B1820681 : Blo 1213424 1820681 := bstep (se 2 (by rfl) ⟨682755, by rfl⟩ : syracuseStep 1820681 = 1365511) B1365511
theorem B1820711 : Blo 1213424 1820711 := bstep (se 1 (by rfl) ⟨1365533, by rfl⟩ : syracuseStep 1820711 = 2731067) B2731067
theorem B1214503 : Blo 1213424 1214503 := bstep (se 1 (by rfl) ⟨910877, by rfl⟩ : syracuseStep 1214503 = 1821755) B1821755
theorem B1214543 : Blo 1213424 1214543 := bstep (se 1 (by rfl) ⟨910907, by rfl⟩ : syracuseStep 1214543 = 1821815) B1821815
theorem B1214559 : Blo 1213424 1214559 := bstep (se 1 (by rfl) ⟨910919, by rfl⟩ : syracuseStep 1214559 = 1821839) B1821839
theorem B1820795 : Blo 1213424 1820795 := bstep (se 1 (by rfl) ⟨1365596, by rfl⟩ : syracuseStep 1820795 = 2731193) B2731193
theorem B1214587 : Blo 1213424 1214587 := bstep (se 1 (by rfl) ⟨910940, by rfl⟩ : syracuseStep 1214587 = 1821881) B1821881
theorem B1214639 : Blo 1213424 1214639 := bstep (se 1 (by rfl) ⟨910979, by rfl⟩ : syracuseStep 1214639 = 1821959) B1821959
theorem B1214663 : Blo 1213424 1214663 := bstep (se 1 (by rfl) ⟨910997, by rfl⟩ : syracuseStep 1214663 = 1821995) B1821995
theorem B1214683 : Blo 1213424 1214683 := bstep (se 1 (by rfl) ⟨911012, by rfl⟩ : syracuseStep 1214683 = 1822025) B1822025
theorem B1820921 : Blo 1213424 1820921 := bstep (se 2 (by rfl) ⟨682845, by rfl⟩ : syracuseStep 1820921 = 1365691) B1365691
theorem B1214759 : Blo 1213424 1214759 := bstep (se 1 (by rfl) ⟨911069, by rfl⟩ : syracuseStep 1214759 = 1822139) B1822139
theorem B1214799 : Blo 1213424 1214799 := bstep (se 1 (by rfl) ⟨911099, by rfl⟩ : syracuseStep 1214799 = 1822199) B1822199
theorem B1821023 : Blo 1213424 1821023 := bstep (se 1 (by rfl) ⟨1365767, by rfl⟩ : syracuseStep 1821023 = 2731535) B2731535
theorem B1214815 : Blo 1213424 1214815 := bstep (se 1 (by rfl) ⟨911111, by rfl⟩ : syracuseStep 1214815 = 1822223) B1822223
theorem B1821035 : Blo 1213424 1821035 := bstep (se 1 (by rfl) ⟨1365776, by rfl⟩ : syracuseStep 1821035 = 2731553) B2731553
theorem B1214843 : Blo 1213424 1214843 := bstep (se 1 (by rfl) ⟨911132, by rfl⟩ : syracuseStep 1214843 = 1822265) B1822265
theorem B2730383 : Blo 1213424 2730383 := bstep (se 1 (by rfl) ⟨2047787, by rfl⟩ : syracuseStep 2730383 = 4095575) B4095575
theorem B112208273 : Blo 1213424 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B2050447 : Blo 1213424 2050447 := bstep (se 1 (by rfl) ⟨1537835, by rfl⟩ : syracuseStep 2050447 = 3075671) B3075671
theorem B1214895 : Blo 1213424 1214895 := bstep (se 1 (by rfl) ⟨911171, by rfl⟩ : syracuseStep 1214895 = 1822343) B1822343
theorem B1214919 : Blo 1213424 1214919 := bstep (se 1 (by rfl) ⟨911189, by rfl⟩ : syracuseStep 1214919 = 1822379) B1822379
theorem B8759755 : Blo 1213424 8759755 := bstep (se 1 (by rfl) ⟨6569816, by rfl⟩ : syracuseStep 8759755 = 13139633) B13139633
theorem B1214939 : Blo 1213424 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B2304521 : Blo 1213424 2304521 := bstep (se 2 (by rfl) ⟨864195, by rfl⟩ : syracuseStep 2304521 = 1728391) B1728391
theorem B2460179 : Blo 1213424 2460179 := bstep (se 1 (by rfl) ⟨1845134, by rfl⟩ : syracuseStep 2460179 = 3690269) B3690269
theorem B2304551 : Blo 1213424 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B4098599 : Blo 1213424 4098599 := bstep (se 1 (by rfl) ⟨3073949, by rfl⟩ : syracuseStep 4098599 = 6147899) B6147899
theorem B1231399 : Blo 1213424 1231399 := bstep (se 1 (by rfl) ⟨923549, by rfl⟩ : syracuseStep 1231399 = 1847099) B1847099
theorem B1215015 : Blo 1213424 1215015 := bstep (se 1 (by rfl) ⟨911261, by rfl⟩ : syracuseStep 1215015 = 1822523) B1822523
theorem B1821263 : Blo 1213424 1821263 := bstep (se 1 (by rfl) ⟨1365947, by rfl⟩ : syracuseStep 1821263 = 2731895) B2731895
theorem B1215055 : Blo 1213424 1215055 := bstep (se 1 (by rfl) ⟨911291, by rfl⟩ : syracuseStep 1215055 = 1822583) B1822583
theorem B1215071 : Blo 1213424 1215071 := bstep (se 1 (by rfl) ⟨911303, by rfl⟩ : syracuseStep 1215071 = 1822607) B1822607
theorem B1215099 : Blo 1213424 1215099 := bstep (se 1 (by rfl) ⟨911324, by rfl⟩ : syracuseStep 1215099 = 1822649) B1822649
theorem B3074699 : Blo 1213424 3074699 := bstep (se 1 (by rfl) ⟨2306024, by rfl⟩ : syracuseStep 3074699 = 4612049) B4612049
theorem B4098707 : Blo 1213424 4098707 := bstep (se 1 (by rfl) ⟨3074030, by rfl⟩ : syracuseStep 4098707 = 6148061) B6148061
theorem B1215151 : Blo 1213424 1215151 := bstep (se 1 (by rfl) ⟨911363, by rfl⟩ : syracuseStep 1215151 = 1822727) B1822727
theorem B52546229 : Blo 1213424 52546229 := bstep (se 5 (by rfl) ⟨2463104, by rfl⟩ : syracuseStep 52546229 = 4926209) B4926209
theorem B1821383 : Blo 1213424 1821383 := bstep (se 1 (by rfl) ⟨1366037, by rfl⟩ : syracuseStep 1821383 = 2732075) B2732075
theorem B1215175 : Blo 1213424 1215175 := bstep (se 1 (by rfl) ⟨911381, by rfl⟩ : syracuseStep 1215175 = 1822763) B1822763
theorem B2730707 : Blo 1213424 2730707 := bstep (se 1 (by rfl) ⟨2048030, by rfl⟩ : syracuseStep 2730707 = 4096061) B4096061
theorem B8751827 : Blo 1213424 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B1215195 : Blo 1213424 1215195 := bstep (se 1 (by rfl) ⟨911396, by rfl⟩ : syracuseStep 1215195 = 1822793) B1822793
theorem B7105283 : Blo 1213424 7105283 := bstep (se 1 (by rfl) ⟨5328962, by rfl⟩ : syracuseStep 7105283 = 10657925) B10657925
theorem B1215271 : Blo 1213424 1215271 := bstep (se 1 (by rfl) ⟨911453, by rfl⟩ : syracuseStep 1215271 = 1822907) B1822907
theorem B1215311 : Blo 1213424 1215311 := bstep (se 1 (by rfl) ⟨911483, by rfl⟩ : syracuseStep 1215311 = 1822967) B1822967
theorem B1215327 : Blo 1213424 1215327 := bstep (se 1 (by rfl) ⟨911495, by rfl⟩ : syracuseStep 1215327 = 1822991) B1822991
theorem B1821545 : Blo 1213424 1821545 := bstep (se 2 (by rfl) ⟨683079, by rfl⟩ : syracuseStep 1821545 = 1366159) B1366159
theorem B4098923 : Blo 1213424 4098923 := bstep (se 1 (by rfl) ⟨3074192, by rfl⟩ : syracuseStep 4098923 = 6148385) B6148385
theorem B1215355 : Blo 1213424 1215355 := bstep (se 1 (by rfl) ⟨911516, by rfl⟩ : syracuseStep 1215355 = 1823033) B1823033
theorem B4098977 : Blo 1213424 4098977 := bstep (se 2 (by rfl) ⟨1537116, by rfl⟩ : syracuseStep 4098977 = 3074233) B3074233
theorem B1215407 : Blo 1213424 1215407 := bstep (se 1 (by rfl) ⟨911555, by rfl⟩ : syracuseStep 1215407 = 1823111) B1823111
theorem B1821623 : Blo 1213424 1821623 := bstep (se 1 (by rfl) ⟨1366217, by rfl⟩ : syracuseStep 1821623 = 2732435) B2732435
theorem B1821659 : Blo 1213424 1821659 := bstep (se 1 (by rfl) ⟨1366244, by rfl⟩ : syracuseStep 1821659 = 2732489) B2732489
theorem B3460153 : Blo 1213424 3460153 := bstep (se 2 (by rfl) ⟨1297557, by rfl⟩ : syracuseStep 3460153 = 2595115) B2595115
theorem B1641551 : Blo 1213424 1641551 := bstep (se 1 (by rfl) ⟨1231163, by rfl⟩ : syracuseStep 1641551 = 2462327) B2462327
theorem B7777451 : Blo 1213424 7777451 := bstep (se 1 (by rfl) ⟨5833088, by rfl⟩ : syracuseStep 7777451 = 11666177) B11666177
theorem B19958957 : Blo 1213424 19958957 := bstep (se 3 (by rfl) ⟨3742304, by rfl⟩ : syracuseStep 19958957 = 7484609) B7484609
theorem B2305235 : Blo 1213424 2305235 := bstep (se 1 (by rfl) ⟨1728926, by rfl⟩ : syracuseStep 2305235 = 3457853) B3457853
theorem B2305273 : Blo 1213424 2305273 := bstep (se 2 (by rfl) ⟨864477, by rfl⟩ : syracuseStep 2305273 = 1728955) B1728955
theorem B4926845 : Blo 1213424 4926845 := bstep (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) B1847567
theorem B3460495 : Blo 1213424 3460495 := bstep (se 1 (by rfl) ⟨2595371, by rfl⟩ : syracuseStep 3460495 = 5190743) B5190743
theorem B1822127 : Blo 1213424 1822127 := bstep (se 1 (by rfl) ⟨1366595, by rfl⟩ : syracuseStep 1822127 = 2733191) B2733191
theorem B4099571 : Blo 1213424 4099571 := bstep (se 1 (by rfl) ⟨3074678, by rfl⟩ : syracuseStep 4099571 = 6149357) B6149357
theorem B1822217 : Blo 1213424 1822217 := bstep (se 2 (by rfl) ⟨683331, by rfl⟩ : syracuseStep 1822217 = 1366663) B1366663
theorem B1822247 : Blo 1213424 1822247 := bstep (se 1 (by rfl) ⟨1366685, by rfl⟩ : syracuseStep 1822247 = 2733371) B2733371
theorem B2461241 : Blo 1213424 2461241 := bstep (se 2 (by rfl) ⟨922965, by rfl⟩ : syracuseStep 2461241 = 1845931) B1845931
theorem B2731643 : Blo 1213424 2731643 := bstep (se 1 (by rfl) ⟨2048732, by rfl⟩ : syracuseStep 2731643 = 4097465) B4097465
theorem B1822331 : Blo 1213424 1822331 := bstep (se 1 (by rfl) ⟨1366748, by rfl⟩ : syracuseStep 1822331 = 2733497) B2733497
theorem B2731769 : Blo 1213424 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B1822457 : Blo 1213424 1822457 := bstep (se 2 (by rfl) ⟨683421, by rfl⟩ : syracuseStep 1822457 = 1366843) B1366843
theorem B3075833 : Blo 1213424 3075833 := bstep (se 2 (by rfl) ⟨1153437, by rfl⟩ : syracuseStep 3075833 = 2306875) B2306875
theorem B1822559 : Blo 1213424 1822559 := bstep (se 1 (by rfl) ⟨1366919, by rfl⟩ : syracuseStep 1822559 = 2733839) B2733839
theorem B1535851 : Blo 1213424 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B1822571 : Blo 1213424 1822571 := bstep (se 1 (by rfl) ⟨1366928, by rfl⟩ : syracuseStep 1822571 = 2733857) B2733857
theorem B31125383 : Blo 1213424 31125383 := bstep (se 1 (by rfl) ⟨23344037, by rfl⟩ : syracuseStep 31125383 = 46688075) B46688075
theorem B9228167 : Blo 1213424 9228167 := bstep (se 1 (by rfl) ⟨6921125, by rfl⟩ : syracuseStep 9228167 = 13842251) B13842251
theorem B3076015 : Blo 1213424 3076015 := bstep (se 1 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 3076015 = 4614023) B4614023
theorem B2305979 : Blo 1213424 2305979 := bstep (se 1 (by rfl) ⟨1729484, by rfl⟩ : syracuseStep 2305979 = 3458969) B3458969
theorem B2732039 : Blo 1213424 2732039 := bstep (se 1 (by rfl) ⟨2049029, by rfl⟩ : syracuseStep 2732039 = 4098059) B4098059
theorem B4100111 : Blo 1213424 4100111 := bstep (se 1 (by rfl) ⟨3075083, by rfl⟩ : syracuseStep 4100111 = 6150167) B6150167
theorem B1536079 : Blo 1213424 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B2732111 : Blo 1213424 2732111 := bstep (se 1 (by rfl) ⟨2049083, by rfl⟩ : syracuseStep 2732111 = 4098167) B4098167
theorem B1822799 : Blo 1213424 1822799 := bstep (se 1 (by rfl) ⟨1367099, by rfl⟩ : syracuseStep 1822799 = 2734199) B2734199
theorem B1822919 : Blo 1213424 1822919 := bstep (se 1 (by rfl) ⟨1367189, by rfl⟩ : syracuseStep 1822919 = 2734379) B2734379
theorem B1823081 : Blo 1213424 1823081 := bstep (se 2 (by rfl) ⟨683655, by rfl⟩ : syracuseStep 1823081 = 1367311) B1367311
theorem B3076481 : Blo 1213424 3076481 := bstep (se 2 (by rfl) ⟨1153680, by rfl⟩ : syracuseStep 3076481 = 2307361) B2307361
theorem B2306465 : Blo 1213424 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B2732507 : Blo 1213424 2732507 := bstep (se 1 (by rfl) ⟨2049380, by rfl⟩ : syracuseStep 2732507 = 4098761) B4098761
theorem B1946119 : Blo 1213424 1946119 := bstep (se 1 (by rfl) ⟨1459589, by rfl⟩ : syracuseStep 1946119 = 2919179) B2919179
theorem B4100705 : Blo 1213424 4100705 := bstep (se 2 (by rfl) ⟨1537764, by rfl⟩ : syracuseStep 4100705 = 3075529) B3075529
theorem B4608647 : Blo 1213424 4608647 := bstep (se 1 (by rfl) ⟨3456485, by rfl⟩ : syracuseStep 4608647 = 6912971) B6912971
theorem B2306731 : Blo 1213424 2306731 := bstep (se 1 (by rfl) ⟨1730048, by rfl⟩ : syracuseStep 2306731 = 3460097) B3460097
theorem B10367747 : Blo 1213424 10367747 := bstep (se 1 (by rfl) ⟨7775810, by rfl⟩ : syracuseStep 10367747 = 15551621) B15551621
theorem B7492355 : Blo 1213424 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B8753993 : Blo 1213424 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B2732975 : Blo 1213424 2732975 := bstep (se 1 (by rfl) ⟨2049731, by rfl⟩ : syracuseStep 2732975 = 4099463) B4099463
theorem B2307035 : Blo 1213424 2307035 := bstep (se 1 (by rfl) ⟨1730276, by rfl⟩ : syracuseStep 2307035 = 3460553) B3460553
theorem B17511491 : Blo 1213424 17511491 := bstep (se 1 (by rfl) ⟨13133618, by rfl⟩ : syracuseStep 17511491 = 26267237) B26267237
theorem B1365115 : Blo 1213424 1365115 := bstep (se 1 (by rfl) ⟨1023836, by rfl⟩ : syracuseStep 1365115 = 2047673) B2047673
theorem B1537147 : Blo 1213424 1537147 := bstep (se 1 (by rfl) ⟨1152860, by rfl⟩ : syracuseStep 1537147 = 2305721) B2305721
theorem B1946747 : Blo 1213424 1946747 := bstep (se 1 (by rfl) ⟨1460060, by rfl⟩ : syracuseStep 1946747 = 2920121) B2920121
theorem B2733227 : Blo 1213424 2733227 := bstep (se 1 (by rfl) ⟨2049920, by rfl⟩ : syracuseStep 2733227 = 4099841) B4099841
theorem B3888445 : Blo 1213424 3888445 := bstep (se 3 (by rfl) ⟨729083, by rfl⟩ : syracuseStep 3888445 = 1458167) B1458167
theorem B1537375 : Blo 1213424 1537375 := bstep (se 1 (by rfl) ⟨1153031, by rfl⟩ : syracuseStep 1537375 = 2306063) B2306063
theorem B6149519 : Blo 1213424 6149519 := bstep (se 1 (by rfl) ⟨4612139, by rfl⟩ : syracuseStep 6149519 = 9224279) B9224279
theorem B1365583 : Blo 1213424 1365583 := bstep (se 1 (by rfl) ⟨1024187, by rfl⟩ : syracuseStep 1365583 = 2048375) B2048375
theorem B4920955 : Blo 1213424 4920955 := bstep (se 1 (by rfl) ⟨3690716, by rfl⟩ : syracuseStep 4920955 = 7381433) B7381433
theorem B2733767 : Blo 1213424 2733767 := bstep (se 1 (by rfl) ⟨2050325, by rfl⟩ : syracuseStep 2733767 = 4100651) B4100651
theorem B1922809 : Blo 1213424 1922809 := bstep (se 2 (by rfl) ⟨721053, by rfl⟩ : syracuseStep 1922809 = 1442107) B1442107
theorem B5183327 : Blo 1213424 5183327 := bstep (se 1 (by rfl) ⟨3887495, by rfl⟩ : syracuseStep 5183327 = 7774991) B7774991
theorem B1537967 : Blo 1213424 1537967 := bstep (se 1 (by rfl) ⟨1153475, by rfl⟩ : syracuseStep 1537967 = 2306951) B2306951
theorem B9598907 : Blo 1213424 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B15570893 : Blo 1213424 15570893 := bstep (se 3 (by rfl) ⟨2919542, by rfl⟩ : syracuseStep 15570893 = 5839085) B5839085
theorem B14768081 : Blo 1213424 14768081 := bstep (se 2 (by rfl) ⟨5538030, by rfl⟩ : syracuseStep 14768081 = 11076061) B11076061
theorem B1365979 : Blo 1213424 1365979 := bstep (se 1 (by rfl) ⟨1024484, by rfl⟩ : syracuseStep 1365979 = 2048969) B2048969
theorem B8755229 : Blo 1213424 8755229 := bstep (se 3 (by rfl) ⟨1641605, by rfl⟩ : syracuseStep 8755229 = 3283211) B3283211
theorem B4610105 : Blo 1213424 4610105 := bstep (se 2 (by rfl) ⟨1728789, by rfl⟩ : syracuseStep 4610105 = 3457579) B3457579
theorem B17520947 : Blo 1213424 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B6560129 : Blo 1213424 6560129 := bstep (se 2 (by rfl) ⟨2460048, by rfl⟩ : syracuseStep 6560129 = 4920097) B4920097
theorem B1366447 : Blo 1213424 1366447 := bstep (se 1 (by rfl) ⟨1024835, by rfl⟩ : syracuseStep 1366447 = 2049671) B2049671
theorem B21027275 : Blo 1213424 21027275 := bstep (se 1 (by rfl) ⟨15770456, by rfl⟩ : syracuseStep 21027275 = 31540913) B31540913
theorem B6232585 : Blo 1213424 6232585 := bstep (se 2 (by rfl) ⟨2337219, by rfl⟩ : syracuseStep 6232585 = 4674439) B4674439
theorem B5839393 : Blo 1213424 5839393 := bstep (se 2 (by rfl) ⟨2189772, by rfl⟩ : syracuseStep 5839393 = 4379545) B4379545
theorem B2734631 : Blo 1213424 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B2595577 : Blo 1213424 2595577 := bstep (se 2 (by rfl) ⟨973341, by rfl⟩ : syracuseStep 2595577 = 1946683) B1946683
theorem B1366879 : Blo 1213424 1366879 := bstep (se 1 (by rfl) ⟨1025159, by rfl⟩ : syracuseStep 1366879 = 2050319) B2050319
theorem B3455905 : Blo 1213424 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B14777423 : Blo 1213424 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B1367239 : Blo 1213424 1367239 := bstep (se 1 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 1367239 = 2050859) B2050859
theorem B17497367 : Blo 1213424 17497367 := bstep (se 1 (by rfl) ⟨13123025, by rfl⟩ : syracuseStep 17497367 = 26246051) B26246051
theorem B6151625 : Blo 1213424 6151625 := bstep (se 2 (by rfl) ⟨2306859, by rfl⟩ : syracuseStep 6151625 = 4613719) B4613719
theorem B4611593 : Blo 1213424 4611593 := bstep (se 2 (by rfl) ⟨1729347, by rfl⟩ : syracuseStep 4611593 = 3458695) B3458695
theorem B4095521 : Blo 1213424 4095521 := bstep (se 2 (by rfl) ⟨1535820, by rfl⟩ : syracuseStep 4095521 = 3071641) B3071641
theorem B13827671 : Blo 1213424 13827671 := bstep (se 1 (by rfl) ⟨10370753, by rfl⟩ : syracuseStep 13827671 = 20741507) B20741507
theorem B4374155 : Blo 1213424 4374155 := bstep (se 1 (by rfl) ⟨3280616, by rfl⟩ : syracuseStep 4374155 = 6561233) B6561233
theorem B6143687 : Blo 1213424 6143687 := bstep (se 1 (by rfl) ⟨4607765, by rfl⟩ : syracuseStep 6143687 = 9215531) B9215531
theorem B4800215 : Blo 1213424 4800215 := bstep (se 1 (by rfl) ⟨3600161, by rfl⟩ : syracuseStep 4800215 = 7200323) B7200323
theorem B4095737 : Blo 1213424 4095737 := bstep (se 2 (by rfl) ⟨1535901, by rfl⟩ : syracuseStep 4095737 = 3071803) B3071803
theorem B29556485 : Blo 1213424 29556485 := bstep (se 4 (by rfl) ⟨2770920, by rfl⟩ : syracuseStep 29556485 = 5541841) B5541841
theorem B16859015 : Blo 1213424 16859015 := bstep (se 1 (by rfl) ⟨12644261, by rfl⟩ : syracuseStep 16859015 = 25288523) B25288523
theorem B2047963 : Blo 1213424 2047963 := bstep (se 1 (by rfl) ⟨1535972, by rfl⟩ : syracuseStep 2047963 = 3071945) B3071945
theorem B2048105 : Blo 1213424 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B8749403 : Blo 1213424 8749403 := bstep (se 1 (by rfl) ⟨6562052, by rfl⟩ : syracuseStep 8749403 = 13124105) B13124105
theorem B2916719 : Blo 1213424 2916719 := bstep (se 1 (by rfl) ⟨2187539, by rfl⟩ : syracuseStep 2916719 = 4375079) B4375079
theorem B3072431 : Blo 1213424 3072431 := bstep (se 1 (by rfl) ⟨2304323, by rfl⟩ : syracuseStep 3072431 = 4608647) B4608647
theorem B16630343 : Blo 1213424 16630343 := bstep (se 1 (by rfl) ⟨12472757, by rfl⟩ : syracuseStep 16630343 = 24945515) B24945515
theorem B6144659 : Blo 1213424 6144659 := bstep (se 1 (by rfl) ⟨4608494, by rfl⟩ : syracuseStep 6144659 = 9216989) B9216989
theorem B11674327 : Blo 1213424 11674327 := bstep (se 1 (by rfl) ⟨8755745, by rfl⟩ : syracuseStep 11674327 = 17511491) B17511491
theorem B25330753 : Blo 1213424 25330753 := bstep (se 2 (by rfl) ⟨9499032, by rfl⟩ : syracuseStep 25330753 = 18998065) B18998065
theorem B5538959 : Blo 1213424 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B1213727 : Blo 1213424 1213727 := bstep (se 1 (by rfl) ⟨910295, by rfl⟩ : syracuseStep 1213727 = 1820591) B1820591
theorem B6399271 : Blo 1213424 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B10380595 : Blo 1213424 10380595 := bstep (se 1 (by rfl) ⟨7785446, by rfl⟩ : syracuseStep 10380595 = 15570893) B15570893
theorem B1213787 : Blo 1213424 1213787 := bstep (se 1 (by rfl) ⟨910340, by rfl⟩ : syracuseStep 1213787 = 1820681) B1820681
theorem B1213807 : Blo 1213424 1213807 := bstep (se 1 (by rfl) ⟨910355, by rfl⟩ : syracuseStep 1213807 = 1820711) B1820711
theorem B3073403 : Blo 1213424 3073403 := bstep (se 1 (by rfl) ⟨2305052, by rfl⟩ : syracuseStep 3073403 = 4610105) B4610105
theorem B4613537 : Blo 1213424 4613537 := bstep (se 2 (by rfl) ⟨1730076, by rfl⟩ : syracuseStep 4613537 = 3460153) B3460153
theorem B1213863 : Blo 1213424 1213863 := bstep (se 1 (by rfl) ⟨910397, by rfl⟩ : syracuseStep 1213863 = 1820795) B1820795
theorem B6145469 : Blo 1213424 6145469 := bstep (se 3 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 6145469 = 2304551) B2304551
theorem B1820153 : Blo 1213424 1820153 := bstep (se 2 (by rfl) ⟨682557, by rfl⟩ : syracuseStep 1820153 = 1365115) B1365115
theorem B1213947 : Blo 1213424 1213947 := bstep (se 1 (by rfl) ⟨910460, by rfl⟩ : syracuseStep 1213947 = 1820921) B1820921
theorem B2049529 : Blo 1213424 2049529 := bstep (se 2 (by rfl) ⟨768573, by rfl⟩ : syracuseStep 2049529 = 1537147) B1537147
theorem B1214015 : Blo 1213424 1214015 := bstep (se 1 (by rfl) ⟨910511, by rfl⟩ : syracuseStep 1214015 = 1821023) B1821023
theorem B1214023 : Blo 1213424 1214023 := bstep (se 1 (by rfl) ⟨910517, by rfl⟩ : syracuseStep 1214023 = 1821035) B1821035
theorem B1820255 : Blo 1213424 1820255 := bstep (se 1 (by rfl) ⟨1365191, by rfl⟩ : syracuseStep 1820255 = 2730383) B2730383
theorem B14018183 : Blo 1213424 14018183 := bstep (se 1 (by rfl) ⟨10513637, by rfl⟩ : syracuseStep 14018183 = 21027275) B21027275
theorem B3073697 : Blo 1213424 3073697 := bstep (se 2 (by rfl) ⟨1152636, by rfl⟩ : syracuseStep 3073697 = 2305273) B2305273
theorem B1214175 : Blo 1213424 1214175 := bstep (se 1 (by rfl) ⟨910631, by rfl⟩ : syracuseStep 1214175 = 1821263) B1821263
theorem B2049799 : Blo 1213424 2049799 := bstep (se 1 (by rfl) ⟨1537349, by rfl⟩ : syracuseStep 2049799 = 3074699) B3074699
theorem B35030819 : Blo 1213424 35030819 := bstep (se 1 (by rfl) ⟨26273114, by rfl⟩ : syracuseStep 35030819 = 52546229) B52546229
theorem B2049833 : Blo 1213424 2049833 := bstep (se 2 (by rfl) ⟨768687, by rfl⟩ : syracuseStep 2049833 = 1537375) B1537375
theorem B1214255 : Blo 1213424 1214255 := bstep (se 1 (by rfl) ⟨910691, by rfl⟩ : syracuseStep 1214255 = 1821383) B1821383
theorem B1820471 : Blo 1213424 1820471 := bstep (se 1 (by rfl) ⟨1365353, by rfl⟩ : syracuseStep 1820471 = 2730707) B2730707
theorem B5834551 : Blo 1213424 5834551 := bstep (se 1 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 5834551 = 8751827) B8751827
theorem B4736855 : Blo 1213424 4736855 := bstep (se 1 (by rfl) ⟨3552641, by rfl⟩ : syracuseStep 4736855 = 7105283) B7105283
theorem B4097897 : Blo 1213424 4097897 := bstep (se 2 (by rfl) ⟨1536711, by rfl⟩ : syracuseStep 4097897 = 3073423) B3073423
theorem B4613993 : Blo 1213424 4613993 := bstep (se 2 (by rfl) ⟨1730247, by rfl⟩ : syracuseStep 4613993 = 3460495) B3460495
theorem B1214363 : Blo 1213424 1214363 := bstep (se 1 (by rfl) ⟨910772, by rfl⟩ : syracuseStep 1214363 = 1821545) B1821545
theorem B1214415 : Blo 1213424 1214415 := bstep (se 1 (by rfl) ⟨910811, by rfl⟩ : syracuseStep 1214415 = 1821623) B1821623
theorem B1214439 : Blo 1213424 1214439 := bstep (se 1 (by rfl) ⟨910829, by rfl⟩ : syracuseStep 1214439 = 1821659) B1821659
theorem B1820777 : Blo 1213424 1820777 := bstep (se 2 (by rfl) ⟨682791, by rfl⟩ : syracuseStep 1820777 = 1365583) B1365583
theorem B13305971 : Blo 1213424 13305971 := bstep (se 1 (by rfl) ⟨9979478, by rfl⟩ : syracuseStep 13305971 = 19958957) B19958957
theorem B4098329 : Blo 1213424 4098329 := bstep (se 2 (by rfl) ⟨1536873, by rfl⟩ : syracuseStep 4098329 = 3073747) B3073747
theorem B1214751 : Blo 1213424 1214751 := bstep (se 1 (by rfl) ⟨911063, by rfl⟩ : syracuseStep 1214751 = 1822127) B1822127
theorem B3074395 : Blo 1213424 3074395 := bstep (se 1 (by rfl) ⟨2305796, by rfl⟩ : syracuseStep 3074395 = 4611593) B4611593
theorem B1214811 : Blo 1213424 1214811 := bstep (se 1 (by rfl) ⟨911108, by rfl⟩ : syracuseStep 1214811 = 1822217) B1822217
theorem B2730347 : Blo 1213424 2730347 := bstep (se 1 (by rfl) ⟨2047760, by rfl⟩ : syracuseStep 2730347 = 4095521) B4095521
theorem B1214831 : Blo 1213424 1214831 := bstep (se 1 (by rfl) ⟨911123, by rfl⟩ : syracuseStep 1214831 = 1822247) B1822247
theorem B1640827 : Blo 1213424 1640827 := bstep (se 1 (by rfl) ⟨1230620, by rfl⟩ : syracuseStep 1640827 = 2461241) B2461241
theorem B9218447 : Blo 1213424 9218447 := bstep (se 1 (by rfl) ⟨6913835, by rfl⟩ : syracuseStep 9218447 = 13827671) B13827671
theorem B1821095 : Blo 1213424 1821095 := bstep (se 1 (by rfl) ⟨1365821, by rfl⟩ : syracuseStep 1821095 = 2731643) B2731643
theorem B1214887 : Blo 1213424 1214887 := bstep (se 1 (by rfl) ⟨911165, by rfl⟩ : syracuseStep 1214887 = 1822331) B1822331
theorem B2730491 : Blo 1213424 2730491 := bstep (se 1 (by rfl) ⟨2047868, by rfl⟩ : syracuseStep 2730491 = 4095737) B4095737
theorem B1821179 : Blo 1213424 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B1214971 : Blo 1213424 1214971 := bstep (se 1 (by rfl) ⟨911228, by rfl⟩ : syracuseStep 1214971 = 1822457) B1822457
theorem B2050555 : Blo 1213424 2050555 := bstep (se 1 (by rfl) ⟨1537916, by rfl⟩ : syracuseStep 2050555 = 3075833) B3075833
theorem B19704323 : Blo 1213424 19704323 := bstep (se 1 (by rfl) ⟨14778242, by rfl⟩ : syracuseStep 19704323 = 29556485) B29556485
theorem B1215039 : Blo 1213424 1215039 := bstep (se 1 (by rfl) ⟨911279, by rfl⟩ : syracuseStep 1215039 = 1822559) B1822559
theorem B1215047 : Blo 1213424 1215047 := bstep (se 1 (by rfl) ⟨911285, by rfl⟩ : syracuseStep 1215047 = 1822571) B1822571
theorem B2730617 : Blo 1213424 2730617 := bstep (se 2 (by rfl) ⟨1023981, by rfl⟩ : syracuseStep 2730617 = 2047963) B2047963
theorem B1821305 : Blo 1213424 1821305 := bstep (se 2 (by rfl) ⟨682989, by rfl⟩ : syracuseStep 1821305 = 1365979) B1365979
theorem B2730671 : Blo 1213424 2730671 := bstep (se 1 (by rfl) ⟨2048003, by rfl⟩ : syracuseStep 2730671 = 4096007) B4096007
theorem B1821359 : Blo 1213424 1821359 := bstep (se 1 (by rfl) ⟨1366019, by rfl⟩ : syracuseStep 1821359 = 2732039) B2732039
theorem B1821407 : Blo 1213424 1821407 := bstep (se 1 (by rfl) ⟨1366055, by rfl⟩ : syracuseStep 1821407 = 2732111) B2732111
theorem B1215199 : Blo 1213424 1215199 := bstep (se 1 (by rfl) ⟨911399, by rfl⟩ : syracuseStep 1215199 = 1822799) B1822799
theorem B2730743 : Blo 1213424 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B5253907 : Blo 1213424 5253907 := bstep (se 1 (by rfl) ⟨3940430, by rfl⟩ : syracuseStep 5253907 = 7880861) B7880861
theorem B2304787 : Blo 1213424 2304787 := bstep (se 1 (by rfl) ⟨1728590, by rfl⟩ : syracuseStep 2304787 = 3457181) B3457181
theorem B1215279 : Blo 1213424 1215279 := bstep (se 1 (by rfl) ⟨911459, by rfl⟩ : syracuseStep 1215279 = 1822919) B1822919
theorem B4377469 : Blo 1213424 4377469 := bstep (se 3 (by rfl) ⟨820775, by rfl⟩ : syracuseStep 4377469 = 1641551) B1641551
theorem B1215387 : Blo 1213424 1215387 := bstep (se 1 (by rfl) ⟨911540, by rfl⟩ : syracuseStep 1215387 = 1823081) B1823081
theorem B2730923 : Blo 1213424 2730923 := bstep (se 1 (by rfl) ⟨2048192, by rfl⟩ : syracuseStep 2730923 = 4096385) B4096385
theorem B1944491 : Blo 1213424 1944491 := bstep (se 1 (by rfl) ⟨1458368, by rfl⟩ : syracuseStep 1944491 = 2916737) B2916737
theorem B2050987 : Blo 1213424 2050987 := bstep (se 1 (by rfl) ⟨1538240, by rfl⟩ : syracuseStep 2050987 = 3076481) B3076481
theorem B1821671 : Blo 1213424 1821671 := bstep (se 1 (by rfl) ⟨1366253, by rfl⟩ : syracuseStep 1821671 = 2732507) B2732507
theorem B5835995 : Blo 1213424 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B1821929 : Blo 1213424 1821929 := bstep (se 2 (by rfl) ⟨683223, by rfl⟩ : syracuseStep 1821929 = 1366447) B1366447
theorem B1821983 : Blo 1213424 1821983 := bstep (se 1 (by rfl) ⟨1366487, by rfl⟩ : syracuseStep 1821983 = 2732975) B2732975
theorem B3075367 : Blo 1213424 3075367 := bstep (se 1 (by rfl) ⟨2306525, by rfl⟩ : syracuseStep 3075367 = 4613051) B4613051
theorem B5188931 : Blo 1213424 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B8310113 : Blo 1213424 8310113 := bstep (se 2 (by rfl) ⟨3116292, by rfl⟩ : syracuseStep 8310113 = 6232585) B6232585
theorem B7785857 : Blo 1213424 7785857 := bstep (se 2 (by rfl) ⟨2919696, by rfl⟩ : syracuseStep 7785857 = 5839393) B5839393
theorem B2305417 : Blo 1213424 2305417 := bstep (se 2 (by rfl) ⟨864531, by rfl⟩ : syracuseStep 2305417 = 1729063) B1729063
theorem B1641865 : Blo 1213424 1641865 := bstep (se 2 (by rfl) ⟨615699, by rfl⟩ : syracuseStep 1641865 = 1231399) B1231399
theorem B1297831 : Blo 1213424 1297831 := bstep (se 1 (by rfl) ⟨973373, by rfl⟩ : syracuseStep 1297831 = 1946747) B1946747
theorem B2731463 : Blo 1213424 2731463 := bstep (se 1 (by rfl) ⟨2048597, by rfl⟩ : syracuseStep 2731463 = 4097195) B4097195
theorem B1822151 : Blo 1213424 1822151 := bstep (se 1 (by rfl) ⟨1366613, by rfl⟩ : syracuseStep 1822151 = 2733227) B2733227
theorem B3075641 : Blo 1213424 3075641 := bstep (se 2 (by rfl) ⟨1153365, by rfl⟩ : syracuseStep 3075641 = 2306731) B2306731
theorem B1945183 : Blo 1213424 1945183 := bstep (se 1 (by rfl) ⟨1458887, by rfl⟩ : syracuseStep 1945183 = 2917775) B2917775
theorem B4099679 : Blo 1213424 4099679 := bstep (se 1 (by rfl) ⟨3074759, by rfl⟩ : syracuseStep 4099679 = 6149519) B6149519
theorem B3460769 : Blo 1213424 3460769 := bstep (se 2 (by rfl) ⟨1297788, by rfl⟩ : syracuseStep 3460769 = 2595577) B2595577
theorem B17493677 : Blo 1213424 17493677 := bstep (se 3 (by rfl) ⟨3280064, by rfl⟩ : syracuseStep 17493677 = 6560129) B6560129
theorem B1822505 : Blo 1213424 1822505 := bstep (se 2 (by rfl) ⟨683439, by rfl⟩ : syracuseStep 1822505 = 1366879) B1366879
theorem B2731823 : Blo 1213424 2731823 := bstep (se 1 (by rfl) ⟨2048867, by rfl⟩ : syracuseStep 2731823 = 4097735) B4097735
theorem B1822511 : Blo 1213424 1822511 := bstep (se 1 (by rfl) ⟨1366883, by rfl⟩ : syracuseStep 1822511 = 2733767) B2733767
theorem B13832045 : Blo 1213424 13832045 := bstep (se 3 (by rfl) ⟨2593508, by rfl⟩ : syracuseStep 13832045 = 5187017) B5187017
theorem B4607873 : Blo 1213424 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B5836819 : Blo 1213424 5836819 := bstep (se 1 (by rfl) ⟨4377614, by rfl⟩ : syracuseStep 5836819 = 8755229) B8755229
theorem B1822985 : Blo 1213424 1822985 := bstep (se 2 (by rfl) ⟨683619, by rfl⟩ : syracuseStep 1822985 = 1367239) B1367239
theorem B74805515 : Blo 1213424 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B1536347 : Blo 1213424 1536347 := bstep (se 1 (by rfl) ⟨1152260, by rfl⟩ : syracuseStep 1536347 = 2304521) B2304521
theorem B2732399 : Blo 1213424 2732399 := bstep (se 1 (by rfl) ⟨2049299, by rfl⟩ : syracuseStep 2732399 = 4098599) B4098599
theorem B1823087 : Blo 1213424 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B2732471 : Blo 1213424 2732471 := bstep (se 1 (by rfl) ⟨2049353, by rfl⟩ : syracuseStep 2732471 = 4098707) B4098707
theorem B11080253 : Blo 1213424 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B2732615 : Blo 1213424 2732615 := bstep (se 1 (by rfl) ⟨2049461, by rfl⟩ : syracuseStep 2732615 = 4098923) B4098923
theorem B2732651 : Blo 1213424 2732651 := bstep (se 1 (by rfl) ⟨2049488, by rfl⟩ : syracuseStep 2732651 = 4098977) B4098977
theorem B9851615 : Blo 1213424 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B1536823 : Blo 1213424 1536823 := bstep (se 1 (by rfl) ⟨1152617, by rfl⟩ : syracuseStep 1536823 = 2305235) B2305235
theorem B4101083 : Blo 1213424 4101083 := bstep (se 1 (by rfl) ⟨3075812, by rfl⟩ : syracuseStep 4101083 = 6151625) B6151625
theorem B2733047 : Blo 1213424 2733047 := bstep (se 1 (by rfl) ⟨2049785, by rfl⟩ : syracuseStep 2733047 = 4099571) B4099571
theorem B4101245 : Blo 1213424 4101245 := bstep (se 3 (by rfl) ⟨768983, by rfl⟩ : syracuseStep 4101245 = 1537967) B1537967
theorem B3200143 : Blo 1213424 3200143 := bstep (se 1 (by rfl) ⟨2400107, by rfl⟩ : syracuseStep 3200143 = 4800215) B4800215
theorem B23663789 : Blo 1213424 23663789 := bstep (se 3 (by rfl) ⟨4436960, by rfl⟩ : syracuseStep 23663789 = 8873921) B8873921
theorem B4101353 : Blo 1213424 4101353 := bstep (se 2 (by rfl) ⟨1538007, by rfl⟩ : syracuseStep 4101353 = 3076015) B3076015
theorem B1537319 : Blo 1213424 1537319 := bstep (se 1 (by rfl) ⟨1152989, by rfl⟩ : syracuseStep 1537319 = 2305979) B2305979
theorem B2733407 : Blo 1213424 2733407 := bstep (se 1 (by rfl) ⟨2050055, by rfl⟩ : syracuseStep 2733407 = 4100111) B4100111
theorem B4101515 : Blo 1213424 4101515 := bstep (se 1 (by rfl) ⟨3076136, by rfl⟩ : syracuseStep 4101515 = 6152273) B6152273
theorem B1537643 : Blo 1213424 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B1365727 : Blo 1213424 1365727 := bstep (se 1 (by rfl) ⟨1024295, by rfl⟩ : syracuseStep 1365727 = 2048591) B2048591
theorem B2733803 : Blo 1213424 2733803 := bstep (se 1 (by rfl) ⟨2050352, by rfl⟩ : syracuseStep 2733803 = 4100705) B4100705
theorem B50517775 : Blo 1213424 50517775 := bstep (se 1 (by rfl) ⟨37888331, by rfl⟩ : syracuseStep 50517775 = 75776663) B75776663
theorem B6911831 : Blo 1213424 6911831 := bstep (se 1 (by rfl) ⟨5183873, by rfl⟩ : syracuseStep 6911831 = 10367747) B10367747
theorem B4994903 : Blo 1213424 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B2733929 : Blo 1213424 2733929 := bstep (se 2 (by rfl) ⟨1025223, by rfl⟩ : syracuseStep 2733929 = 2050447) B2050447
theorem B11679673 : Blo 1213424 11679673 := bstep (se 2 (by rfl) ⟨4379877, by rfl⟩ : syracuseStep 11679673 = 8759755) B8759755
theorem B26245093 : Blo 1213424 26245093 := bstep (se 4 (by rfl) ⟨2460477, by rfl⟩ : syracuseStep 26245093 = 4920955) B4920955
theorem B1538023 : Blo 1213424 1538023 := bstep (se 1 (by rfl) ⟨1153517, by rfl⟩ : syracuseStep 1538023 = 2307035) B2307035
theorem B2594825 : Blo 1213424 2594825 := bstep (se 2 (by rfl) ⟨973059, by rfl⟩ : syracuseStep 2594825 = 1946119) B1946119
theorem B6150329 : Blo 1213424 6150329 := bstep (se 2 (by rfl) ⟨2306373, by rfl⟩ : syracuseStep 6150329 = 4612747) B4612747
theorem B1366303 : Blo 1213424 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B3455551 : Blo 1213424 3455551 := bstep (se 1 (by rfl) ⟨2591663, by rfl⟩ : syracuseStep 3455551 = 5183327) B5183327
theorem B1366591 : Blo 1213424 1366591 := bstep (se 1 (by rfl) ⟨1024943, by rfl⟩ : syracuseStep 1366591 = 2049887) B2049887
theorem B9845387 : Blo 1213424 9845387 := bstep (se 1 (by rfl) ⟨7384040, by rfl⟩ : syracuseStep 9845387 = 14768081) B14768081
theorem B6560477 : Blo 1213424 6560477 := bstep (se 3 (by rfl) ⟨1230089, by rfl⟩ : syracuseStep 6560477 = 2460179) B2460179
theorem B11680631 : Blo 1213424 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B5184593 : Blo 1213424 5184593 := bstep (se 2 (by rfl) ⟨1944222, by rfl⟩ : syracuseStep 5184593 = 3888445) B3888445
theorem B4373693 : Blo 1213424 4373693 := bstep (se 3 (by rfl) ⟨820067, by rfl⟩ : syracuseStep 4373693 = 1640135) B1640135
theorem B5184967 : Blo 1213424 5184967 := bstep (se 1 (by rfl) ⟨3888725, by rfl⟩ : syracuseStep 5184967 = 7777451) B7777451
theorem B11664911 : Blo 1213424 11664911 := bstep (se 1 (by rfl) ⟨8748683, by rfl⟩ : syracuseStep 11664911 = 17497367) B17497367
theorem B3284563 : Blo 1213424 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B2563745 : Blo 1213424 2563745 := bstep (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) B1922809
theorem B2916103 : Blo 1213424 2916103 := bstep (se 1 (by rfl) ⟨2187077, by rfl⟩ : syracuseStep 2916103 = 4374155) B4374155
theorem B4095791 : Blo 1213424 4095791 := bstep (se 1 (by rfl) ⟨3071843, by rfl⟩ : syracuseStep 4095791 = 6143687) B6143687
theorem B2047801 : Blo 1213424 2047801 := bstep (se 2 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 2047801 = 1535851) B1535851
theorem B35020673 : Blo 1213424 35020673 := bstep (se 2 (by rfl) ⟨13132752, by rfl⟩ : syracuseStep 35020673 = 26265505) B26265505
theorem B20750255 : Blo 1213424 20750255 := bstep (se 1 (by rfl) ⟨15562691, by rfl⟩ : syracuseStep 20750255 = 31125383) B31125383
theorem B6152111 : Blo 1213424 6152111 := bstep (se 1 (by rfl) ⟨4614083, by rfl⟩ : syracuseStep 6152111 = 9228167) B9228167
theorem B11239343 : Blo 1213424 11239343 := bstep (se 1 (by rfl) ⟨8429507, by rfl⟩ : syracuseStep 11239343 = 16859015) B16859015
theorem B7782425 : Blo 1213424 7782425 := bstep (se 2 (by rfl) ⟨2918409, by rfl⟩ : syracuseStep 7782425 = 5836819) B5836819
theorem B5832935 : Blo 1213424 5832935 := bstep (se 1 (by rfl) ⟨4374701, by rfl⟩ : syracuseStep 5832935 = 8749403) B8749403
theorem B2048287 : Blo 1213424 2048287 := bstep (se 1 (by rfl) ⟨1536215, by rfl⟩ : syracuseStep 2048287 = 3072431) B3072431
theorem B4096439 : Blo 1213424 4096439 := bstep (se 1 (by rfl) ⟨3072329, by rfl⟩ : syracuseStep 4096439 = 6144659) B6144659
theorem B4096925 : Blo 1213424 4096925 := bstep (se 3 (by rfl) ⟨768173, by rfl⟩ : syracuseStep 4096925 = 1536347) B1536347
theorem B2048935 : Blo 1213424 2048935 := bstep (se 1 (by rfl) ⟨1536701, by rfl⟩ : syracuseStep 2048935 = 3073403) B3073403
theorem B15565769 : Blo 1213424 15565769 := bstep (se 2 (by rfl) ⟨5837163, by rfl⟩ : syracuseStep 15565769 = 11674327) B11674327
theorem B4096979 : Blo 1213424 4096979 := bstep (se 1 (by rfl) ⟨3072734, by rfl⟩ : syracuseStep 4096979 = 6145469) B6145469
theorem B1213435 : Blo 1213424 1213435 := bstep (se 1 (by rfl) ⟨910076, by rfl⟩ : syracuseStep 1213435 = 1820153) B1820153
theorem B7005209 : Blo 1213424 7005209 := bstep (se 2 (by rfl) ⟨2626953, by rfl⟩ : syracuseStep 7005209 = 5253907) B5253907
theorem B3073049 : Blo 1213424 3073049 := bstep (se 2 (by rfl) ⟨1152393, by rfl⟩ : syracuseStep 3073049 = 2304787) B2304787
theorem B1213503 : Blo 1213424 1213503 := bstep (se 1 (by rfl) ⟨910127, by rfl⟩ : syracuseStep 1213503 = 1820255) B1820255
theorem B2049097 : Blo 1213424 2049097 := bstep (se 2 (by rfl) ⟨768411, by rfl⟩ : syracuseStep 2049097 = 1536823) B1536823
theorem B2049131 : Blo 1213424 2049131 := bstep (se 1 (by rfl) ⟨1536848, by rfl⟩ : syracuseStep 2049131 = 3073697) B3073697
theorem B1213647 : Blo 1213424 1213647 := bstep (se 1 (by rfl) ⟨910235, by rfl⟩ : syracuseStep 1213647 = 1820471) B1820471
theorem B1729883 : Blo 1213424 1729883 := bstep (se 1 (by rfl) ⟨1297412, by rfl⟩ : syracuseStep 1729883 = 2594825) B2594825
theorem B1213851 : Blo 1213424 1213851 := bstep (se 1 (by rfl) ⟨910388, by rfl⟩ : syracuseStep 1213851 = 1820777) B1820777
theorem B269428133 : Blo 1213424 269428133 := bstep (se 4 (by rfl) ⟨25258887, by rfl⟩ : syracuseStep 269428133 = 50517775) B50517775
theorem B1820231 : Blo 1213424 1820231 := bstep (se 1 (by rfl) ⟨1365173, by rfl⟩ : syracuseStep 1820231 = 2730347) B2730347
theorem B6145631 : Blo 1213424 6145631 := bstep (se 1 (by rfl) ⟨4609223, by rfl⟩ : syracuseStep 6145631 = 9218447) B9218447
theorem B1214063 : Blo 1213424 1214063 := bstep (se 1 (by rfl) ⟨910547, by rfl⟩ : syracuseStep 1214063 = 1821095) B1821095
theorem B1820327 : Blo 1213424 1820327 := bstep (se 1 (by rfl) ⟨1365245, by rfl⟩ : syracuseStep 1820327 = 2730491) B2730491
theorem B1214119 : Blo 1213424 1214119 := bstep (se 1 (by rfl) ⟨910589, by rfl⟩ : syracuseStep 1214119 = 1821179) B1821179
theorem B1820411 : Blo 1213424 1820411 := bstep (se 1 (by rfl) ⟨1365308, by rfl⟩ : syracuseStep 1820411 = 2730617) B2730617
theorem B1214203 : Blo 1213424 1214203 := bstep (se 1 (by rfl) ⟨910652, by rfl⟩ : syracuseStep 1214203 = 1821305) B1821305
theorem B6563591 : Blo 1213424 6563591 := bstep (se 1 (by rfl) ⟨4922693, by rfl⟩ : syracuseStep 6563591 = 9845387) B9845387
theorem B1820447 : Blo 1213424 1820447 := bstep (se 1 (by rfl) ⟨1365335, by rfl⟩ : syracuseStep 1820447 = 2730671) B2730671
theorem B1214239 : Blo 1213424 1214239 := bstep (se 1 (by rfl) ⟨910679, by rfl⟩ : syracuseStep 1214239 = 1821359) B1821359
theorem B1214271 : Blo 1213424 1214271 := bstep (se 1 (by rfl) ⟨910703, by rfl⟩ : syracuseStep 1214271 = 1821407) B1821407
theorem B1820495 : Blo 1213424 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B3073889 : Blo 1213424 3073889 := bstep (se 2 (by rfl) ⟨1152708, by rfl⟩ : syracuseStep 3073889 = 2305417) B2305417
theorem B2189153 : Blo 1213424 2189153 := bstep (se 2 (by rfl) ⟨820932, by rfl⟩ : syracuseStep 2189153 = 1641865) B1641865
theorem B1730441 : Blo 1213424 1730441 := bstep (se 2 (by rfl) ⟨648915, by rfl⟩ : syracuseStep 1730441 = 1297831) B1297831
theorem B1820615 : Blo 1213424 1820615 := bstep (se 1 (by rfl) ⟨1365461, by rfl⟩ : syracuseStep 1820615 = 2730923) B2730923
theorem B8751077 : Blo 1213424 8751077 := bstep (se 4 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 8751077 = 1640827) B1640827
theorem B1214447 : Blo 1213424 1214447 := bstep (se 1 (by rfl) ⟨910835, by rfl⟩ : syracuseStep 1214447 = 1821671) B1821671
theorem B1214619 : Blo 1213424 1214619 := bstep (se 1 (by rfl) ⟨910964, by rfl⟩ : syracuseStep 1214619 = 1821929) B1821929
theorem B1214655 : Blo 1213424 1214655 := bstep (se 1 (by rfl) ⟨910991, by rfl⟩ : syracuseStep 1214655 = 1821983) B1821983
theorem B3459287 : Blo 1213424 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B5540075 : Blo 1213424 5540075 := bstep (se 1 (by rfl) ⟨4155056, by rfl⟩ : syracuseStep 5540075 = 8310113) B8310113
theorem B1820969 : Blo 1213424 1820969 := bstep (se 2 (by rfl) ⟨682863, by rfl⟩ : syracuseStep 1820969 = 1365727) B1365727
theorem B1820975 : Blo 1213424 1820975 := bstep (se 1 (by rfl) ⟨1365731, by rfl⟩ : syracuseStep 1820975 = 2731463) B2731463
theorem B1214767 : Blo 1213424 1214767 := bstep (se 1 (by rfl) ⟨911075, by rfl⟩ : syracuseStep 1214767 = 1822151) B1822151
theorem B7776607 : Blo 1213424 7776607 := bstep (se 1 (by rfl) ⟨5832455, by rfl⟩ : syracuseStep 7776607 = 11664911) B11664911
theorem B2050427 : Blo 1213424 2050427 := bstep (se 1 (by rfl) ⟨1537820, by rfl⟩ : syracuseStep 2050427 = 3075641) B3075641
theorem B2730401 : Blo 1213424 2730401 := bstep (se 2 (by rfl) ⟨1023900, by rfl⟩ : syracuseStep 2730401 = 2047801) B2047801
theorem B1215003 : Blo 1213424 1215003 := bstep (se 1 (by rfl) ⟨911252, by rfl⟩ : syracuseStep 1215003 = 1822505) B1822505
theorem B2730527 : Blo 1213424 2730527 := bstep (se 1 (by rfl) ⟨2047895, by rfl⟩ : syracuseStep 2730527 = 4095791) B4095791
theorem B1821215 : Blo 1213424 1821215 := bstep (se 1 (by rfl) ⟨1365911, by rfl⟩ : syracuseStep 1821215 = 2731823) B2731823
theorem B1215007 : Blo 1213424 1215007 := bstep (se 1 (by rfl) ⟨911255, by rfl⟩ : syracuseStep 1215007 = 1822511) B1822511
theorem B2050697 : Blo 1213424 2050697 := bstep (se 2 (by rfl) ⟨769011, by rfl⟩ : syracuseStep 2050697 = 1538023) B1538023
theorem B1215323 : Blo 1213424 1215323 := bstep (se 1 (by rfl) ⟨911492, by rfl⟩ : syracuseStep 1215323 = 1822985) B1822985
theorem B1944479 : Blo 1213424 1944479 := bstep (se 1 (by rfl) ⟨1458359, by rfl⟩ : syracuseStep 1944479 = 2916719) B2916719
theorem B1821599 : Blo 1213424 1821599 := bstep (se 1 (by rfl) ⟨1366199, by rfl⟩ : syracuseStep 1821599 = 2732399) B2732399
theorem B1215391 : Blo 1213424 1215391 := bstep (se 1 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 1215391 = 1823087) B1823087
theorem B1821647 : Blo 1213424 1821647 := bstep (se 1 (by rfl) ⟨1366235, by rfl⟩ : syracuseStep 1821647 = 2732471) B2732471
theorem B1821737 : Blo 1213424 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B1821743 : Blo 1213424 1821743 := bstep (se 1 (by rfl) ⟨1366307, by rfl⟩ : syracuseStep 1821743 = 2732615) B2732615
theorem B11086895 : Blo 1213424 11086895 := bstep (se 1 (by rfl) ⟨8315171, by rfl⟩ : syracuseStep 11086895 = 16630343) B16630343
theorem B1821767 : Blo 1213424 1821767 := bstep (se 1 (by rfl) ⟨1366325, by rfl⟩ : syracuseStep 1821767 = 2732651) B2732651
theorem B4099193 : Blo 1213424 4099193 := bstep (se 2 (by rfl) ⟨1537197, by rfl⟩ : syracuseStep 4099193 = 3074395) B3074395
theorem B1822031 : Blo 1213424 1822031 := bstep (se 1 (by rfl) ⟨1366523, by rfl⟩ : syracuseStep 1822031 = 2733047) B2733047
theorem B4607401 : Blo 1213424 4607401 := bstep (se 2 (by rfl) ⟨1727775, by rfl⟩ : syracuseStep 4607401 = 3455551) B3455551
theorem B1822121 : Blo 1213424 1822121 := bstep (se 2 (by rfl) ⟨683295, by rfl⟩ : syracuseStep 1822121 = 1366591) B1366591
theorem B4099517 : Blo 1213424 4099517 := bstep (se 3 (by rfl) ⟨768659, by rfl⟩ : syracuseStep 4099517 = 1537319) B1537319
theorem B1822271 : Blo 1213424 1822271 := bstep (se 1 (by rfl) ⟨1366703, by rfl⟩ : syracuseStep 1822271 = 2733407) B2733407
theorem B3075691 : Blo 1213424 3075691 := bstep (se 1 (by rfl) ⟨2306768, by rfl⟩ : syracuseStep 3075691 = 4613537) B4613537
theorem B1822535 : Blo 1213424 1822535 := bstep (se 1 (by rfl) ⟨1366901, by rfl⟩ : syracuseStep 1822535 = 2733803) B2733803
theorem B5836625 : Blo 1213424 5836625 := bstep (se 2 (by rfl) ⟨2188734, by rfl⟩ : syracuseStep 5836625 = 4377469) B4377469
theorem B4607887 : Blo 1213424 4607887 := bstep (se 1 (by rfl) ⟨3455915, by rfl⟩ : syracuseStep 4607887 = 6911831) B6911831
theorem B3157903 : Blo 1213424 3157903 := bstep (se 1 (by rfl) ⟨2368427, by rfl⟩ : syracuseStep 3157903 = 4736855) B4736855
theorem B2731931 : Blo 1213424 2731931 := bstep (se 1 (by rfl) ⟨2048948, by rfl⟩ : syracuseStep 2731931 = 4097897) B4097897
theorem B1822619 : Blo 1213424 1822619 := bstep (se 1 (by rfl) ⟨1366964, by rfl⟩ : syracuseStep 1822619 = 2733929) B2733929
theorem B3075995 : Blo 1213424 3075995 := bstep (se 1 (by rfl) ⟨2306996, by rfl⟩ : syracuseStep 3075995 = 4613993) B4613993
theorem B4100219 : Blo 1213424 4100219 := bstep (se 1 (by rfl) ⟨3075164, by rfl⟩ : syracuseStep 4100219 = 6150329) B6150329
theorem B2732219 : Blo 1213424 2732219 := bstep (se 1 (by rfl) ⟨2049164, by rfl⟩ : syracuseStep 2732219 = 4098329) B4098329
theorem B4100381 : Blo 1213424 4100381 := bstep (se 3 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 4100381 = 1537643) B1537643
theorem B13136215 : Blo 1213424 13136215 := bstep (se 1 (by rfl) ⟨9852161, by rfl⟩ : syracuseStep 13136215 = 19704323) B19704323
theorem B8532361 : Blo 1213424 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B4100489 : Blo 1213424 4100489 := bstep (se 2 (by rfl) ⟨1537683, by rfl⟩ : syracuseStep 4100489 = 3075367) B3075367
theorem B13840793 : Blo 1213424 13840793 := bstep (se 2 (by rfl) ⟨5190297, by rfl⟩ : syracuseStep 13840793 = 10380595) B10380595
theorem B6836653 : Blo 1213424 6836653 := bstep (se 3 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 6836653 = 2563745) B2563745
theorem B7787087 : Blo 1213424 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B2732705 : Blo 1213424 2732705 := bstep (se 2 (by rfl) ⟨1024764, by rfl⟩ : syracuseStep 2732705 = 2049529) B2049529
theorem B4379417 : Blo 1213424 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B2593577 : Blo 1213424 2593577 := bstep (se 2 (by rfl) ⟨972591, by rfl⟩ : syracuseStep 2593577 = 1945183) B1945183
theorem B5190571 : Blo 1213424 5190571 := bstep (se 1 (by rfl) ⟨3892928, by rfl⟩ : syracuseStep 5190571 = 7785857) B7785857
theorem B3888137 : Blo 1213424 3888137 := bstep (se 2 (by rfl) ⟨1458051, by rfl⟩ : syracuseStep 3888137 = 2916103) B2916103
theorem B2733065 : Blo 1213424 2733065 := bstep (se 2 (by rfl) ⟨1024899, by rfl⟩ : syracuseStep 2733065 = 2049799) B2049799
theorem B2733119 : Blo 1213424 2733119 := bstep (se 1 (by rfl) ⟨2049839, by rfl⟩ : syracuseStep 2733119 = 4099679) B4099679
theorem B7779401 : Blo 1213424 7779401 := bstep (se 2 (by rfl) ⟨2917275, by rfl⟩ : syracuseStep 7779401 = 5834551) B5834551
theorem B2307179 : Blo 1213424 2307179 := bstep (se 1 (by rfl) ⟨1730384, by rfl⟩ : syracuseStep 2307179 = 3460769) B3460769
theorem B11662451 : Blo 1213424 11662451 := bstep (se 1 (by rfl) ⟨8746838, by rfl⟩ : syracuseStep 11662451 = 17493677) B17493677
theorem B9221363 : Blo 1213424 9221363 := bstep (se 1 (by rfl) ⟨6916022, by rfl⟩ : syracuseStep 9221363 = 13832045) B13832045
theorem B13833503 : Blo 1213424 13833503 := bstep (se 1 (by rfl) ⟨10375127, by rfl⟩ : syracuseStep 13833503 = 20750255) B20750255
theorem B4101407 : Blo 1213424 4101407 := bstep (se 1 (by rfl) ⟨3076055, by rfl⟩ : syracuseStep 4101407 = 6152111) B6152111
theorem B7492895 : Blo 1213424 7492895 := bstep (se 1 (by rfl) ⟨5619671, by rfl⟩ : syracuseStep 7492895 = 11239343) B11239343
theorem B34993457 : Blo 1213424 34993457 := bstep (se 2 (by rfl) ⟨13122546, by rfl⟩ : syracuseStep 34993457 = 26245093) B26245093
theorem B1365403 : Blo 1213424 1365403 := bstep (se 1 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 1365403 = 2048105) B2048105
theorem B49870343 : Blo 1213424 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B6567743 : Blo 1213424 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B2734055 : Blo 1213424 2734055 := bstep (se 1 (by rfl) ⟨2050541, by rfl⟩ : syracuseStep 2734055 = 4101083) B4101083
theorem B2734073 : Blo 1213424 2734073 := bstep (se 2 (by rfl) ⟨1025277, by rfl⟩ : syracuseStep 2734073 = 2050555) B2050555
theorem B2734163 : Blo 1213424 2734163 := bstep (se 1 (by rfl) ⟨2050622, by rfl⟩ : syracuseStep 2734163 = 4101245) B4101245
theorem B3692639 : Blo 1213424 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B15775859 : Blo 1213424 15775859 := bstep (se 1 (by rfl) ⟨11831894, by rfl⟩ : syracuseStep 15775859 = 23663789) B23663789
theorem B2734235 : Blo 1213424 2734235 := bstep (se 1 (by rfl) ⟨2050676, by rfl⟩ : syracuseStep 2734235 = 4101353) B4101353
theorem B2734343 : Blo 1213424 2734343 := bstep (se 1 (by rfl) ⟨2050757, by rfl⟩ : syracuseStep 2734343 = 4101515) B4101515
theorem B9345455 : Blo 1213424 9345455 := bstep (se 1 (by rfl) ⟨7009091, by rfl⟩ : syracuseStep 9345455 = 14018183) B14018183
theorem B23353879 : Blo 1213424 23353879 := bstep (se 1 (by rfl) ⟨17515409, by rfl⟩ : syracuseStep 23353879 = 35030819) B35030819
theorem B1366555 : Blo 1213424 1366555 := bstep (se 1 (by rfl) ⟨1024916, by rfl⟩ : syracuseStep 1366555 = 2049833) B2049833
theorem B2734649 : Blo 1213424 2734649 := bstep (se 2 (by rfl) ⟨1025493, by rfl⟩ : syracuseStep 2734649 = 2050987) B2050987
theorem B8870647 : Blo 1213424 8870647 := bstep (se 1 (by rfl) ⟨6652985, by rfl⟩ : syracuseStep 8870647 = 13305971) B13305971
theorem B33774337 : Blo 1213424 33774337 := bstep (se 2 (by rfl) ⟨12665376, by rfl⟩ : syracuseStep 33774337 = 25330753) B25330753
theorem B29547341 : Blo 1213424 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B4266857 : Blo 1213424 4266857 := bstep (se 2 (by rfl) ⟨1600071, by rfl⟩ : syracuseStep 4266857 = 3200143) B3200143
theorem B4373651 : Blo 1213424 4373651 := bstep (se 1 (by rfl) ⟨3280238, by rfl⟩ : syracuseStep 4373651 = 6560477) B6560477
theorem B6913289 : Blo 1213424 6913289 := bstep (se 2 (by rfl) ⟨2592483, by rfl⟩ : syracuseStep 6913289 = 5184967) B5184967
theorem B3456395 : Blo 1213424 3456395 := bstep (se 1 (by rfl) ⟨2592296, by rfl⟩ : syracuseStep 3456395 = 5184593) B5184593
theorem B2915795 : Blo 1213424 2915795 := bstep (se 1 (by rfl) ⟨2186846, by rfl⟩ : syracuseStep 2915795 = 4373693) B4373693
theorem B3890663 : Blo 1213424 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B13319741 : Blo 1213424 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B5185309 : Blo 1213424 5185309 := bstep (se 3 (by rfl) ⟨972245, by rfl⟩ : syracuseStep 5185309 = 1944491) B1944491
theorem B15572897 : Blo 1213424 15572897 := bstep (se 2 (by rfl) ⟨5839836, by rfl⟩ : syracuseStep 15572897 = 11679673) B11679673
theorem B3071915 : Blo 1213424 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B23347115 : Blo 1213424 23347115 := bstep (se 1 (by rfl) ⟨17510336, by rfl⟩ : syracuseStep 23347115 = 35020673) B35020673
theorem B17514953 : Blo 1213424 17514953 := bstep (se 2 (by rfl) ⟨6568107, by rfl⟩ : syracuseStep 17514953 = 13136215) B13136215
theorem B9224765 : Blo 1213424 9224765 := bstep (se 3 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 9224765 = 3459287) B3459287
theorem B2048699 : Blo 1213424 2048699 := bstep (se 1 (by rfl) ⟨1536524, by rfl⟩ : syracuseStep 2048699 = 3073049) B3073049
theorem B31138505 : Blo 1213424 31138505 := bstep (se 2 (by rfl) ⟨11676939, by rfl⟩ : syracuseStep 31138505 = 23353879) B23353879
theorem B5186267 : Blo 1213424 5186267 := bstep (se 1 (by rfl) ⟨3889700, by rfl⟩ : syracuseStep 5186267 = 7779401) B7779401
theorem B7774967 : Blo 1213424 7774967 := bstep (se 1 (by rfl) ⟨5831225, by rfl⟩ : syracuseStep 7774967 = 11662451) B11662451
theorem B4613021 : Blo 1213424 4613021 := bstep (se 3 (by rfl) ⟨864941, by rfl⟩ : syracuseStep 4613021 = 1729883) B1729883
theorem B179618755 : Blo 1213424 179618755 := bstep (se 1 (by rfl) ⟨134714066, by rfl⟩ : syracuseStep 179618755 = 269428133) B269428133
theorem B45032449 : Blo 1213424 45032449 := bstep (se 2 (by rfl) ⟨16887168, by rfl⟩ : syracuseStep 45032449 = 33774337) B33774337
theorem B1213487 : Blo 1213424 1213487 := bstep (se 1 (by rfl) ⟨910115, by rfl⟩ : syracuseStep 1213487 = 1820231) B1820231
theorem B4097087 : Blo 1213424 4097087 := bstep (se 1 (by rfl) ⟨3072815, by rfl⟩ : syracuseStep 4097087 = 6145631) B6145631
theorem B1213551 : Blo 1213424 1213551 := bstep (se 1 (by rfl) ⟨910163, by rfl⟩ : syracuseStep 1213551 = 1820327) B1820327
theorem B1213607 : Blo 1213424 1213607 := bstep (se 1 (by rfl) ⟨910205, by rfl⟩ : syracuseStep 1213607 = 1820411) B1820411
theorem B4375727 : Blo 1213424 4375727 := bstep (se 1 (by rfl) ⟨3281795, by rfl⟩ : syracuseStep 4375727 = 6563591) B6563591
theorem B1213631 : Blo 1213424 1213631 := bstep (se 1 (by rfl) ⟨910223, by rfl⟩ : syracuseStep 1213631 = 1820447) B1820447
theorem B7775453 : Blo 1213424 7775453 := bstep (se 3 (by rfl) ⟨1457897, by rfl⟩ : syracuseStep 7775453 = 2915795) B2915795
theorem B1213663 : Blo 1213424 1213663 := bstep (se 1 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 1213663 = 1820495) B1820495
theorem B2049259 : Blo 1213424 2049259 := bstep (se 1 (by rfl) ⟨1536944, by rfl⟩ : syracuseStep 2049259 = 3073889) B3073889
theorem B1213743 : Blo 1213424 1213743 := bstep (se 1 (by rfl) ⟨910307, by rfl⟩ : syracuseStep 1213743 = 1820615) B1820615
theorem B5834051 : Blo 1213424 5834051 := bstep (se 1 (by rfl) ⟨4375538, by rfl⟩ : syracuseStep 5834051 = 8751077) B8751077
theorem B1213979 : Blo 1213424 1213979 := bstep (se 1 (by rfl) ⟨910484, by rfl⟩ : syracuseStep 1213979 = 1820969) B1820969
theorem B1213983 : Blo 1213424 1213983 := bstep (se 1 (by rfl) ⟨910487, by rfl⟩ : syracuseStep 1213983 = 1820975) B1820975
theorem B1820267 : Blo 1213424 1820267 := bstep (se 1 (by rfl) ⟨1365200, by rfl⟩ : syracuseStep 1820267 = 2730401) B2730401
theorem B1820351 : Blo 1213424 1820351 := bstep (se 1 (by rfl) ⟨1365263, by rfl⟩ : syracuseStep 1820351 = 2730527) B2730527
theorem B1214143 : Blo 1213424 1214143 := bstep (se 1 (by rfl) ⟨910607, by rfl⟩ : syracuseStep 1214143 = 1821215) B1821215
theorem B1820537 : Blo 1213424 1820537 := bstep (se 2 (by rfl) ⟨682701, by rfl⟩ : syracuseStep 1820537 = 1365403) B1365403
theorem B2844571 : Blo 1213424 2844571 := bstep (se 1 (by rfl) ⟨2133428, by rfl⟩ : syracuseStep 2844571 = 4266857) B4266857
theorem B1296319 : Blo 1213424 1296319 := bstep (se 1 (by rfl) ⟨972239, by rfl⟩ : syracuseStep 1296319 = 1944479) B1944479
theorem B1214399 : Blo 1213424 1214399 := bstep (se 1 (by rfl) ⟨910799, by rfl⟩ : syracuseStep 1214399 = 1821599) B1821599
theorem B1214431 : Blo 1213424 1214431 := bstep (se 1 (by rfl) ⟨910823, by rfl⟩ : syracuseStep 1214431 = 1821647) B1821647
theorem B1214491 : Blo 1213424 1214491 := bstep (se 1 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 1214491 = 1821737) B1821737
theorem B1214495 : Blo 1213424 1214495 := bstep (se 1 (by rfl) ⟨910871, by rfl⟩ : syracuseStep 1214495 = 1821743) B1821743
theorem B7391263 : Blo 1213424 7391263 := bstep (se 1 (by rfl) ⟨5543447, by rfl⟩ : syracuseStep 7391263 = 11086895) B11086895
theorem B1214511 : Blo 1213424 1214511 := bstep (se 1 (by rfl) ⟨910883, by rfl⟩ : syracuseStep 1214511 = 1821767) B1821767
theorem B6916205 : Blo 1213424 6916205 := bstep (se 3 (by rfl) ⟨1296788, by rfl⟩ : syracuseStep 6916205 = 2593577) B2593577
theorem B1214687 : Blo 1213424 1214687 := bstep (se 1 (by rfl) ⟨911015, by rfl⟩ : syracuseStep 1214687 = 1822031) B1822031
theorem B2304263 : Blo 1213424 2304263 := bstep (se 1 (by rfl) ⟨1728197, by rfl⟩ : syracuseStep 2304263 = 3456395) B3456395
theorem B1214747 : Blo 1213424 1214747 := bstep (se 1 (by rfl) ⟨911060, by rfl⟩ : syracuseStep 1214747 = 1822121) B1822121
theorem B4614509 : Blo 1213424 4614509 := bstep (se 3 (by rfl) ⟨865220, by rfl⟩ : syracuseStep 4614509 = 1730441) B1730441
theorem B1214847 : Blo 1213424 1214847 := bstep (se 1 (by rfl) ⟨911135, by rfl⟩ : syracuseStep 1214847 = 1822271) B1822271
theorem B1215023 : Blo 1213424 1215023 := bstep (se 1 (by rfl) ⟨911267, by rfl⟩ : syracuseStep 1215023 = 1822535) B1822535
theorem B1821287 : Blo 1213424 1821287 := bstep (se 1 (by rfl) ⟨1365965, by rfl⟩ : syracuseStep 1821287 = 2731931) B2731931
theorem B1215079 : Blo 1213424 1215079 := bstep (se 1 (by rfl) ⟨911309, by rfl⟩ : syracuseStep 1215079 = 1822619) B1822619
theorem B2050663 : Blo 1213424 2050663 := bstep (se 1 (by rfl) ⟨1537997, by rfl⟩ : syracuseStep 2050663 = 3075995) B3075995
theorem B10381931 : Blo 1213424 10381931 := bstep (se 1 (by rfl) ⟨7786448, by rfl⟩ : syracuseStep 10381931 = 15572897) B15572897
theorem B5188283 : Blo 1213424 5188283 := bstep (se 1 (by rfl) ⟨3891212, by rfl⟩ : syracuseStep 5188283 = 7782425) B7782425
theorem B18680557 : Blo 1213424 18680557 := bstep (se 3 (by rfl) ⟨3502604, by rfl⟩ : syracuseStep 18680557 = 7005209) B7005209
theorem B1821479 : Blo 1213424 1821479 := bstep (se 1 (by rfl) ⟨1366109, by rfl⟩ : syracuseStep 1821479 = 2732219) B2732219
theorem B9227195 : Blo 1213424 9227195 := bstep (se 1 (by rfl) ⟨6920396, by rfl⟩ : syracuseStep 9227195 = 13840793) B13840793
theorem B2730959 : Blo 1213424 2730959 := bstep (se 1 (by rfl) ⟨2048219, by rfl⟩ : syracuseStep 2730959 = 4096439) B4096439
theorem B2731049 : Blo 1213424 2731049 := bstep (se 2 (by rfl) ⟨1024143, by rfl⟩ : syracuseStep 2731049 = 2048287) B2048287
theorem B1821803 : Blo 1213424 1821803 := bstep (se 1 (by rfl) ⟨1366352, by rfl⟩ : syracuseStep 1821803 = 2732705) B2732705
theorem B2919611 : Blo 1213424 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B2731283 : Blo 1213424 2731283 := bstep (se 1 (by rfl) ⟨2048462, by rfl⟩ : syracuseStep 2731283 = 4096925) B4096925
theorem B2731319 : Blo 1213424 2731319 := bstep (se 1 (by rfl) ⟨2048489, by rfl⟩ : syracuseStep 2731319 = 4096979) B4096979
theorem B2592091 : Blo 1213424 2592091 := bstep (se 1 (by rfl) ⟨1944068, by rfl⟩ : syracuseStep 2592091 = 3888137) B3888137
theorem B1822043 : Blo 1213424 1822043 := bstep (se 1 (by rfl) ⟨1366532, by rfl⟩ : syracuseStep 1822043 = 2733065) B2733065
theorem B1822073 : Blo 1213424 1822073 := bstep (se 2 (by rfl) ⟨683277, by rfl⟩ : syracuseStep 1822073 = 1366555) B1366555
theorem B1822079 : Blo 1213424 1822079 := bstep (se 1 (by rfl) ⟨1366559, by rfl⟩ : syracuseStep 1822079 = 2733119) B2733119
theorem B6147575 : Blo 1213424 6147575 := bstep (se 1 (by rfl) ⟨4610681, by rfl⟩ : syracuseStep 6147575 = 9221363) B9221363
theorem B33246895 : Blo 1213424 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B4378495 : Blo 1213424 4378495 := bstep (se 1 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 4378495 = 6567743) B6567743
theorem B2731913 : Blo 1213424 2731913 := bstep (se 2 (by rfl) ⟨1024467, by rfl⟩ : syracuseStep 2731913 = 2048935) B2048935
theorem B1822703 : Blo 1213424 1822703 := bstep (se 1 (by rfl) ⟨1367027, by rfl⟩ : syracuseStep 1822703 = 2734055) B2734055
theorem B1822715 : Blo 1213424 1822715 := bstep (se 1 (by rfl) ⟨1367036, by rfl⟩ : syracuseStep 1822715 = 2734073) B2734073
theorem B1822775 : Blo 1213424 1822775 := bstep (se 1 (by rfl) ⟨1367081, by rfl⟩ : syracuseStep 1822775 = 2734163) B2734163
theorem B2461759 : Blo 1213424 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B2732129 : Blo 1213424 2732129 := bstep (se 2 (by rfl) ⟨1024548, by rfl⟩ : syracuseStep 2732129 = 2049097) B2049097
theorem B1822823 : Blo 1213424 1822823 := bstep (se 1 (by rfl) ⟨1367117, by rfl⟩ : syracuseStep 1822823 = 2734235) B2734235
theorem B1822895 : Blo 1213424 1822895 := bstep (se 1 (by rfl) ⟨1367171, by rfl⟩ : syracuseStep 1822895 = 2734343) B2734343
theorem B6230303 : Blo 1213424 6230303 := bstep (se 1 (by rfl) ⟨4672727, by rfl⟩ : syracuseStep 6230303 = 9345455) B9345455
theorem B1823099 : Blo 1213424 1823099 := bstep (se 1 (by rfl) ⟨1367324, by rfl⟩ : syracuseStep 1823099 = 2734649) B2734649
theorem B19698227 : Blo 1213424 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B2732795 : Blo 1213424 2732795 := bstep (se 1 (by rfl) ⟨2049596, by rfl⟩ : syracuseStep 2732795 = 4099193) B4099193
theorem B4100921 : Blo 1213424 4100921 := bstep (se 2 (by rfl) ⟨1537845, by rfl⟩ : syracuseStep 4100921 = 3075691) B3075691
theorem B4608859 : Blo 1213424 4608859 := bstep (se 1 (by rfl) ⟨3456644, by rfl⟩ : syracuseStep 4608859 = 6913289) B6913289
theorem B5837741 : Blo 1213424 5837741 := bstep (se 3 (by rfl) ⟨1094576, by rfl⟩ : syracuseStep 5837741 = 2189153) B2189153
theorem B2733011 : Blo 1213424 2733011 := bstep (se 1 (by rfl) ⟨2049758, by rfl⟩ : syracuseStep 2733011 = 4099517) B4099517
theorem B2593775 : Blo 1213424 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B2733479 : Blo 1213424 2733479 := bstep (se 1 (by rfl) ⟨2050109, by rfl⟩ : syracuseStep 2733479 = 4100219) B4100219
theorem B3888623 : Blo 1213424 3888623 := bstep (se 1 (by rfl) ⟨2916467, by rfl⟩ : syracuseStep 3888623 = 5832935) B5832935
theorem B2733587 : Blo 1213424 2733587 := bstep (se 1 (by rfl) ⟨2050190, by rfl⟩ : syracuseStep 2733587 = 4100381) B4100381
theorem B2733659 : Blo 1213424 2733659 := bstep (se 1 (by rfl) ⟨2050244, by rfl⟩ : syracuseStep 2733659 = 4100489) B4100489
theorem B5191391 : Blo 1213424 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B10368809 : Blo 1213424 10368809 := bstep (se 2 (by rfl) ⟨3888303, by rfl⟩ : syracuseStep 10368809 = 7776607) B7776607
theorem B9115537 : Blo 1213424 9115537 := bstep (se 2 (by rfl) ⟨3418326, by rfl⟩ : syracuseStep 9115537 = 6836653) B6836653
theorem B10377179 : Blo 1213424 10377179 := bstep (se 1 (by rfl) ⟨7782884, by rfl⟩ : syracuseStep 10377179 = 15565769) B15565769
theorem B1366087 : Blo 1213424 1366087 := bstep (se 1 (by rfl) ⟨1024565, by rfl⟩ : syracuseStep 1366087 = 2049131) B2049131
theorem B1538119 : Blo 1213424 1538119 := bstep (se 1 (by rfl) ⟨1153589, by rfl⟩ : syracuseStep 1538119 = 2307179) B2307179
theorem B9222335 : Blo 1213424 9222335 := bstep (se 1 (by rfl) ⟨6916751, by rfl⟩ : syracuseStep 9222335 = 13833503) B13833503
theorem B2734271 : Blo 1213424 2734271 := bstep (se 1 (by rfl) ⟨2050703, by rfl⟩ : syracuseStep 2734271 = 4101407) B4101407
theorem B4995263 : Blo 1213424 4995263 := bstep (se 1 (by rfl) ⟨3746447, by rfl⟩ : syracuseStep 4995263 = 7492895) B7492895
theorem B23328971 : Blo 1213424 23328971 := bstep (se 1 (by rfl) ⟨17496728, by rfl⟩ : syracuseStep 23328971 = 34993457) B34993457
theorem B11827529 : Blo 1213424 11827529 := bstep (se 2 (by rfl) ⟨4435323, by rfl⟩ : syracuseStep 11827529 = 8870647) B8870647
theorem B6920761 : Blo 1213424 6920761 := bstep (se 2 (by rfl) ⟨2595285, by rfl⟩ : syracuseStep 6920761 = 5190571) B5190571
theorem B10517239 : Blo 1213424 10517239 := bstep (se 1 (by rfl) ⟨7887929, by rfl⟩ : syracuseStep 10517239 = 15775859) B15775859
theorem B3693383 : Blo 1213424 3693383 := bstep (se 1 (by rfl) ⟨2770037, by rfl⟩ : syracuseStep 3693383 = 5540075) B5540075
theorem B35519309 : Blo 1213424 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B1366951 : Blo 1213424 1366951 := bstep (se 1 (by rfl) ⟨1025213, by rfl⟩ : syracuseStep 1366951 = 2050427) B2050427
theorem B1367131 : Blo 1213424 1367131 := bstep (se 1 (by rfl) ⟨1025348, by rfl⟩ : syracuseStep 1367131 = 2050697) B2050697
theorem B6143201 : Blo 1213424 6143201 := bstep (se 2 (by rfl) ⟨2303700, by rfl⟩ : syracuseStep 6143201 = 4607401) B4607401
theorem B45505925 : Blo 1213424 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B2915767 : Blo 1213424 2915767 := bstep (se 1 (by rfl) ⟨2186825, by rfl⟩ : syracuseStep 2915767 = 4373651) B4373651
theorem B6913745 : Blo 1213424 6913745 := bstep (se 2 (by rfl) ⟨2592654, by rfl⟩ : syracuseStep 6913745 = 5185309) B5185309
theorem B6143849 : Blo 1213424 6143849 := bstep (se 2 (by rfl) ⟨2303943, by rfl⟩ : syracuseStep 6143849 = 4607887) B4607887
theorem B4210537 : Blo 1213424 4210537 := bstep (se 2 (by rfl) ⟨1578951, by rfl⟩ : syracuseStep 4210537 = 3157903) B3157903
theorem B3891083 : Blo 1213424 3891083 := bstep (se 1 (by rfl) ⟨2918312, by rfl⟩ : syracuseStep 3891083 = 5836625) B5836625
theorem B2047943 : Blo 1213424 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B15564743 : Blo 1213424 15564743 := bstep (se 1 (by rfl) ⟨11673557, by rfl⟩ : syracuseStep 15564743 = 23347115) B23347115
theorem B9855017 : Blo 1213424 9855017 := bstep (se 2 (by rfl) ⟨3695631, by rfl⟩ : syracuseStep 9855017 = 7391263) B7391263
theorem B4153535 : Blo 1213424 4153535 := bstep (se 1 (by rfl) ⟨3115151, by rfl⟩ : syracuseStep 4153535 = 6230303) B6230303
theorem B13132151 : Blo 1213424 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B20759003 : Blo 1213424 20759003 := bstep (se 1 (by rfl) ⟨15569252, by rfl⟩ : syracuseStep 20759003 = 31138505) B31138505
theorem B3457511 : Blo 1213424 3457511 := bstep (se 1 (by rfl) ⟨2593133, by rfl⟩ : syracuseStep 3457511 = 5186267) B5186267
theorem B3891827 : Blo 1213424 3891827 := bstep (se 1 (by rfl) ⟨2918870, by rfl⟩ : syracuseStep 3891827 = 5837741) B5837741
theorem B1729183 : Blo 1213424 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B2917151 : Blo 1213424 2917151 := bstep (se 1 (by rfl) ⟨2187863, by rfl⟩ : syracuseStep 2917151 = 4375727) B4375727
theorem B1213511 : Blo 1213424 1213511 := bstep (se 1 (by rfl) ⟨910133, by rfl⟩ : syracuseStep 1213511 = 1820267) B1820267
theorem B6145145 : Blo 1213424 6145145 := bstep (se 2 (by rfl) ⟨2304429, by rfl⟩ : syracuseStep 6145145 = 4608859) B4608859
theorem B1213567 : Blo 1213424 1213567 := bstep (se 1 (by rfl) ⟨910175, by rfl⟩ : syracuseStep 1213567 = 1820351) B1820351
theorem B1213691 : Blo 1213424 1213691 := bstep (se 1 (by rfl) ⟨910268, by rfl⟩ : syracuseStep 1213691 = 1820537) B1820537
theorem B1214191 : Blo 1213424 1214191 := bstep (se 1 (by rfl) ⟨910643, by rfl⟩ : syracuseStep 1214191 = 1821287) B1821287
theorem B3458855 : Blo 1213424 3458855 := bstep (se 1 (by rfl) ⟨2594141, by rfl⟩ : syracuseStep 3458855 = 5188283) B5188283
theorem B1214319 : Blo 1213424 1214319 := bstep (se 1 (by rfl) ⟨910739, by rfl⟩ : syracuseStep 1214319 = 1821479) B1821479
theorem B1820639 : Blo 1213424 1820639 := bstep (se 1 (by rfl) ⟨1365479, by rfl⟩ : syracuseStep 1820639 = 2730959) B2730959
theorem B1820699 : Blo 1213424 1820699 := bstep (se 1 (by rfl) ⟨1365524, by rfl⟩ : syracuseStep 1820699 = 2731049) B2731049
theorem B1214535 : Blo 1213424 1214535 := bstep (se 1 (by rfl) ⟨910901, by rfl⟩ : syracuseStep 1214535 = 1821803) B1821803
theorem B1820855 : Blo 1213424 1820855 := bstep (se 1 (by rfl) ⟨1365641, by rfl⟩ : syracuseStep 1820855 = 2731283) B2731283
theorem B1820879 : Blo 1213424 1820879 := bstep (se 1 (by rfl) ⟨1365659, by rfl⟩ : syracuseStep 1820879 = 2731319) B2731319
theorem B1214695 : Blo 1213424 1214695 := bstep (se 1 (by rfl) ⟨911021, by rfl⟩ : syracuseStep 1214695 = 1822043) B1822043
theorem B44329193 : Blo 1213424 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B1214715 : Blo 1213424 1214715 := bstep (se 1 (by rfl) ⟨911036, by rfl⟩ : syracuseStep 1214715 = 1822073) B1822073
theorem B1214719 : Blo 1213424 1214719 := bstep (se 1 (by rfl) ⟨911039, by rfl⟩ : syracuseStep 1214719 = 1822079) B1822079
theorem B30337283 : Blo 1213424 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B4098383 : Blo 1213424 4098383 := bstep (se 1 (by rfl) ⟨3073787, by rfl⟩ : syracuseStep 4098383 = 6147575) B6147575
theorem B5614049 : Blo 1213424 5614049 := bstep (se 2 (by rfl) ⟨2105268, by rfl⟩ : syracuseStep 5614049 = 4210537) B4210537
theorem B1821275 : Blo 1213424 1821275 := bstep (se 1 (by rfl) ⟨1365956, by rfl⟩ : syracuseStep 1821275 = 2731913) B2731913
theorem B1215135 : Blo 1213424 1215135 := bstep (se 1 (by rfl) ⟨911351, by rfl⟩ : syracuseStep 1215135 = 1822703) B1822703
theorem B1215143 : Blo 1213424 1215143 := bstep (se 1 (by rfl) ⟨911357, by rfl⟩ : syracuseStep 1215143 = 1822715) B1822715
theorem B1215183 : Blo 1213424 1215183 := bstep (se 1 (by rfl) ⟨911387, by rfl⟩ : syracuseStep 1215183 = 1822775) B1822775
theorem B1821419 : Blo 1213424 1821419 := bstep (se 1 (by rfl) ⟨1366064, by rfl⟩ : syracuseStep 1821419 = 2732129) B2732129
theorem B1215215 : Blo 1213424 1215215 := bstep (se 1 (by rfl) ⟨911411, by rfl⟩ : syracuseStep 1215215 = 1822823) B1822823
theorem B1821449 : Blo 1213424 1821449 := bstep (se 2 (by rfl) ⟨683043, by rfl⟩ : syracuseStep 1821449 = 1366087) B1366087
theorem B2050825 : Blo 1213424 2050825 := bstep (se 2 (by rfl) ⟨769059, by rfl⟩ : syracuseStep 2050825 = 1538119) B1538119
theorem B1215263 : Blo 1213424 1215263 := bstep (se 1 (by rfl) ⟨911447, by rfl⟩ : syracuseStep 1215263 = 1822895) B1822895
theorem B1215399 : Blo 1213424 1215399 := bstep (se 1 (by rfl) ⟨911549, by rfl⟩ : syracuseStep 1215399 = 1823099) B1823099
theorem B11676635 : Blo 1213424 11676635 := bstep (se 1 (by rfl) ⟨8757476, by rfl⟩ : syracuseStep 11676635 = 17514953) B17514953
theorem B7785629 : Blo 1213424 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B1821863 : Blo 1213424 1821863 := bstep (se 1 (by rfl) ⟨1366397, by rfl⟩ : syracuseStep 1821863 = 2732795) B2732795
theorem B3075347 : Blo 1213424 3075347 := bstep (se 1 (by rfl) ⟨2306510, by rfl⟩ : syracuseStep 3075347 = 4613021) B4613021
theorem B1822007 : Blo 1213424 1822007 := bstep (se 1 (by rfl) ⟨1366505, by rfl⟩ : syracuseStep 1822007 = 2733011) B2733011
theorem B2731391 : Blo 1213424 2731391 := bstep (se 1 (by rfl) ⟨2048543, by rfl⟩ : syracuseStep 2731391 = 4097087) B4097087
theorem B9227681 : Blo 1213424 9227681 := bstep (se 2 (by rfl) ⟨3460380, by rfl⟩ : syracuseStep 9227681 = 6920761) B6920761
theorem B1822319 : Blo 1213424 1822319 := bstep (se 1 (by rfl) ⟨1366739, by rfl⟩ : syracuseStep 1822319 = 2733479) B2733479
theorem B24907409 : Blo 1213424 24907409 := bstep (se 2 (by rfl) ⟨9340278, by rfl⟩ : syracuseStep 24907409 = 18680557) B18680557
theorem B2592415 : Blo 1213424 2592415 := bstep (se 1 (by rfl) ⟨1944311, by rfl⟩ : syracuseStep 2592415 = 3888623) B3888623
theorem B1822391 : Blo 1213424 1822391 := bstep (se 1 (by rfl) ⟨1366793, by rfl⟩ : syracuseStep 1822391 = 2733587) B2733587
theorem B1822439 : Blo 1213424 1822439 := bstep (se 1 (by rfl) ⟨1366829, by rfl⟩ : syracuseStep 1822439 = 2733659) B2733659
theorem B1822601 : Blo 1213424 1822601 := bstep (se 2 (by rfl) ⟨683475, by rfl⟩ : syracuseStep 1822601 = 1366951) B1366951
theorem B6918119 : Blo 1213424 6918119 := bstep (se 1 (by rfl) ⟨5188589, by rfl⟩ : syracuseStep 6918119 = 10377179) B10377179
theorem B60043265 : Blo 1213424 60043265 := bstep (se 2 (by rfl) ⟨22516224, by rfl⟩ : syracuseStep 60043265 = 45032449) B45032449
theorem B1822841 : Blo 1213424 1822841 := bstep (se 2 (by rfl) ⟨683565, by rfl⟩ : syracuseStep 1822841 = 1367131) B1367131
theorem B6148223 : Blo 1213424 6148223 := bstep (se 1 (by rfl) ⟨4611167, by rfl⟩ : syracuseStep 6148223 = 9222335) B9222335
theorem B1822847 : Blo 1213424 1822847 := bstep (se 1 (by rfl) ⟨1367135, by rfl⟩ : syracuseStep 1822847 = 2734271) B2734271
theorem B3330175 : Blo 1213424 3330175 := bstep (se 1 (by rfl) ⟨2497631, by rfl⟩ : syracuseStep 3330175 = 4995263) B4995263
theorem B15552647 : Blo 1213424 15552647 := bstep (se 1 (by rfl) ⟨11664485, by rfl⟩ : syracuseStep 15552647 = 23328971) B23328971
theorem B1536175 : Blo 1213424 1536175 := bstep (se 1 (by rfl) ⟨1152131, by rfl⟩ : syracuseStep 1536175 = 2304263) B2304263
theorem B7885019 : Blo 1213424 7885019 := bstep (se 1 (by rfl) ⟨5913764, by rfl⟩ : syracuseStep 7885019 = 11827529) B11827529
theorem B3076339 : Blo 1213424 3076339 := bstep (se 1 (by rfl) ⟨2307254, by rfl⟩ : syracuseStep 3076339 = 4614509) B4614509
theorem B2732345 : Blo 1213424 2732345 := bstep (se 2 (by rfl) ⟨1024629, by rfl⟩ : syracuseStep 2732345 = 2049259) B2049259
theorem B2462255 : Blo 1213424 2462255 := bstep (se 1 (by rfl) ⟨1846691, by rfl⟩ : syracuseStep 2462255 = 3693383) B3693383
theorem B23679539 : Blo 1213424 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B3887689 : Blo 1213424 3887689 := bstep (se 2 (by rfl) ⟨1457883, by rfl⟩ : syracuseStep 3887689 = 2915767) B2915767
theorem B10376221 : Blo 1213424 10376221 := bstep (se 3 (by rfl) ⟨1945541, by rfl⟩ : syracuseStep 10376221 = 3891083) B3891083
theorem B4609163 : Blo 1213424 4609163 := bstep (se 1 (by rfl) ⟨3456872, by rfl⟩ : syracuseStep 4609163 = 6913745) B6913745
theorem B5837993 : Blo 1213424 5837993 := bstep (se 2 (by rfl) ⟨2189247, by rfl⟩ : syracuseStep 5837993 = 4378495) B4378495
theorem B12154049 : Blo 1213424 12154049 := bstep (se 2 (by rfl) ⟨4557768, by rfl⟩ : syracuseStep 12154049 = 9115537) B9115537
theorem B1365295 : Blo 1213424 1365295 := bstep (se 1 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 1365295 = 2047943) B2047943
theorem B10376495 : Blo 1213424 10376495 := bstep (se 1 (by rfl) ⟨7782371, by rfl⟩ : syracuseStep 10376495 = 15564743) B15564743
theorem B13129381 : Blo 1213424 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B6149843 : Blo 1213424 6149843 := bstep (se 1 (by rfl) ⟨4612382, by rfl⟩ : syracuseStep 6149843 = 9224765) B9224765
theorem B1365799 : Blo 1213424 1365799 := bstep (se 1 (by rfl) ⟨1024349, by rfl⟩ : syracuseStep 1365799 = 2048699) B2048699
theorem B5183311 : Blo 1213424 5183311 := bstep (se 1 (by rfl) ⟨3887483, by rfl⟩ : syracuseStep 5183311 = 7774967) B7774967
theorem B2733947 : Blo 1213424 2733947 := bstep (se 1 (by rfl) ⟨2050460, by rfl⟩ : syracuseStep 2733947 = 4100921) B4100921
theorem B2734217 : Blo 1213424 2734217 := bstep (se 2 (by rfl) ⟨1025331, by rfl⟩ : syracuseStep 2734217 = 2050663) B2050663
theorem B5183635 : Blo 1213424 5183635 := bstep (se 1 (by rfl) ⟨3887726, by rfl⟩ : syracuseStep 5183635 = 7775453) B7775453
theorem B3889367 : Blo 1213424 3889367 := bstep (se 1 (by rfl) ⟨2917025, by rfl⟩ : syracuseStep 3889367 = 5834051) B5834051
theorem B14022985 : Blo 1213424 14022985 := bstep (se 2 (by rfl) ⟨5258619, by rfl⟩ : syracuseStep 14022985 = 10517239) B10517239
theorem B6912539 : Blo 1213424 6912539 := bstep (se 1 (by rfl) ⟨5184404, by rfl⟩ : syracuseStep 6912539 = 10368809) B10368809
theorem B239491673 : Blo 1213424 239491673 := bstep (se 2 (by rfl) ⟨89809377, by rfl⟩ : syracuseStep 239491673 = 179618755) B179618755
theorem B4610803 : Blo 1213424 4610803 := bstep (se 1 (by rfl) ⟨3458102, by rfl⟩ : syracuseStep 4610803 = 6916205) B6916205
theorem B6921287 : Blo 1213424 6921287 := bstep (se 1 (by rfl) ⟨5190965, by rfl⟩ : syracuseStep 6921287 = 10381931) B10381931
theorem B3456121 : Blo 1213424 3456121 := bstep (se 2 (by rfl) ⟨1296045, by rfl⟩ : syracuseStep 3456121 = 2592091) B2592091
theorem B13843709 : Blo 1213424 13843709 := bstep (se 3 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 13843709 = 5191391) B5191391
theorem B6151463 : Blo 1213424 6151463 := bstep (se 1 (by rfl) ⟨4613597, by rfl⟩ : syracuseStep 6151463 = 9227195) B9227195
theorem B4095467 : Blo 1213424 4095467 := bstep (se 1 (by rfl) ⟨3071600, by rfl⟩ : syracuseStep 4095467 = 6143201) B6143201
theorem B3792761 : Blo 1213424 3792761 := bstep (se 2 (by rfl) ⟨1422285, by rfl⟩ : syracuseStep 3792761 = 2844571) B2844571
theorem B4095899 : Blo 1213424 4095899 := bstep (se 1 (by rfl) ⟨3071924, by rfl⟩ : syracuseStep 4095899 = 6143849) B6143849
theorem B1728425 : Blo 1213424 1728425 := bstep (se 2 (by rfl) ⟨648159, by rfl⟩ : syracuseStep 1728425 = 1296319) B1296319
theorem B6570011 : Blo 1213424 6570011 := bstep (se 1 (by rfl) ⟨4927508, by rfl⟩ : syracuseStep 6570011 = 9855017) B9855017
theorem B2769023 : Blo 1213424 2769023 := bstep (se 1 (by rfl) ⟨2076767, by rfl⟩ : syracuseStep 2769023 = 4153535) B4153535
theorem B4440233 : Blo 1213424 4440233 := bstep (se 2 (by rfl) ⟨1665087, by rfl⟩ : syracuseStep 4440233 = 3330175) B3330175
theorem B2048233 : Blo 1213424 2048233 := bstep (se 2 (by rfl) ⟨768087, by rfl⟩ : syracuseStep 2048233 = 1536175) B1536175
theorem B15786359 : Blo 1213424 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B4096763 : Blo 1213424 4096763 := bstep (se 1 (by rfl) ⟨3072572, by rfl⟩ : syracuseStep 4096763 = 6145145) B6145145
theorem B3072775 : Blo 1213424 3072775 := bstep (se 1 (by rfl) ⟨2304581, by rfl⟩ : syracuseStep 3072775 = 4609163) B4609163
theorem B3891995 : Blo 1213424 3891995 := bstep (se 1 (by rfl) ⟨2918996, by rfl⟩ : syracuseStep 3891995 = 5837993) B5837993
theorem B8102699 : Blo 1213424 8102699 := bstep (se 1 (by rfl) ⟨6077024, by rfl⟩ : syracuseStep 8102699 = 12154049) B12154049
theorem B1213759 : Blo 1213424 1213759 := bstep (se 1 (by rfl) ⟨910319, by rfl⟩ : syracuseStep 1213759 = 1820639) B1820639
theorem B1213799 : Blo 1213424 1213799 := bstep (se 1 (by rfl) ⟨910349, by rfl⟩ : syracuseStep 1213799 = 1820699) B1820699
theorem B1213903 : Blo 1213424 1213903 := bstep (se 1 (by rfl) ⟨910427, by rfl⟩ : syracuseStep 1213903 = 1820855) B1820855
theorem B1213919 : Blo 1213424 1213919 := bstep (se 1 (by rfl) ⟨910439, by rfl⟩ : syracuseStep 1213919 = 1820879) B1820879
theorem B1214183 : Blo 1213424 1214183 := bstep (se 1 (by rfl) ⟨910637, by rfl⟩ : syracuseStep 1214183 = 1821275) B1821275
theorem B1820393 : Blo 1213424 1820393 := bstep (se 2 (by rfl) ⟨682647, by rfl⟩ : syracuseStep 1820393 = 1365295) B1365295
theorem B1214279 : Blo 1213424 1214279 := bstep (se 1 (by rfl) ⟨910709, by rfl⟩ : syracuseStep 1214279 = 1821419) B1821419
theorem B1214299 : Blo 1213424 1214299 := bstep (se 1 (by rfl) ⟨910724, by rfl⟩ : syracuseStep 1214299 = 1821449) B1821449
theorem B7784423 : Blo 1213424 7784423 := bstep (se 1 (by rfl) ⟨5838317, by rfl⟩ : syracuseStep 7784423 = 11676635) B11676635
theorem B4614191 : Blo 1213424 4614191 := bstep (se 1 (by rfl) ⟨3460643, by rfl⟩ : syracuseStep 4614191 = 6921287) B6921287
theorem B1214575 : Blo 1213424 1214575 := bstep (se 1 (by rfl) ⟨910931, by rfl⟩ : syracuseStep 1214575 = 1821863) B1821863
theorem B2050231 : Blo 1213424 2050231 := bstep (se 1 (by rfl) ⟨1537673, by rfl⟩ : syracuseStep 2050231 = 3075347) B3075347
theorem B1214671 : Blo 1213424 1214671 := bstep (se 1 (by rfl) ⟨911003, by rfl⟩ : syracuseStep 1214671 = 1822007) B1822007
theorem B1820927 : Blo 1213424 1820927 := bstep (se 1 (by rfl) ⟨1365695, by rfl⟩ : syracuseStep 1820927 = 2731391) B2731391
theorem B2730311 : Blo 1213424 2730311 := bstep (se 1 (by rfl) ⟨2047733, by rfl⟩ : syracuseStep 2730311 = 4095467) B4095467
theorem B1821065 : Blo 1213424 1821065 := bstep (se 2 (by rfl) ⟨682899, by rfl⟩ : syracuseStep 1821065 = 1365799) B1365799
theorem B1214879 : Blo 1213424 1214879 := bstep (se 1 (by rfl) ⟨911159, by rfl⟩ : syracuseStep 1214879 = 1822319) B1822319
theorem B1214927 : Blo 1213424 1214927 := bstep (se 1 (by rfl) ⟨911195, by rfl⟩ : syracuseStep 1214927 = 1822391) B1822391
theorem B1214959 : Blo 1213424 1214959 := bstep (se 1 (by rfl) ⟨911219, by rfl⟩ : syracuseStep 1214959 = 1822439) B1822439
theorem B1215067 : Blo 1213424 1215067 := bstep (se 1 (by rfl) ⟨911300, by rfl⟩ : syracuseStep 1215067 = 1822601) B1822601
theorem B2730599 : Blo 1213424 2730599 := bstep (se 1 (by rfl) ⟨2047949, by rfl⟩ : syracuseStep 2730599 = 4095899) B4095899
theorem B40028843 : Blo 1213424 40028843 := bstep (se 1 (by rfl) ⟨30021632, by rfl⟩ : syracuseStep 40028843 = 60043265) B60043265
theorem B1215227 : Blo 1213424 1215227 := bstep (se 1 (by rfl) ⟨911420, by rfl⟩ : syracuseStep 1215227 = 1822841) B1822841
theorem B4098815 : Blo 1213424 4098815 := bstep (se 1 (by rfl) ⟨3074111, by rfl⟩ : syracuseStep 4098815 = 6148223) B6148223
theorem B1215231 : Blo 1213424 1215231 := bstep (se 1 (by rfl) ⟨911423, by rfl⟩ : syracuseStep 1215231 = 1822847) B1822847
theorem B1821563 : Blo 1213424 1821563 := bstep (se 1 (by rfl) ⟨1366172, by rfl⟩ : syracuseStep 1821563 = 2732345) B2732345
theorem B13839335 : Blo 1213424 13839335 := bstep (se 1 (by rfl) ⟨10379501, by rfl⟩ : syracuseStep 13839335 = 20759003) B20759003
theorem B2305007 : Blo 1213424 2305007 := bstep (se 1 (by rfl) ⟨1728755, by rfl⟩ : syracuseStep 2305007 = 3457511) B3457511
theorem B1641503 : Blo 1213424 1641503 := bstep (se 1 (by rfl) ⟨1231127, by rfl⟩ : syracuseStep 1641503 = 2462255) B2462255
theorem B18697313 : Blo 1213424 18697313 := bstep (se 2 (by rfl) ⟨7011492, by rfl⟩ : syracuseStep 18697313 = 14022985) B14022985
theorem B1944767 : Blo 1213424 1944767 := bstep (se 1 (by rfl) ⟨1458575, by rfl⟩ : syracuseStep 1944767 = 2917151) B2917151
theorem B6917663 : Blo 1213424 6917663 := bstep (se 1 (by rfl) ⟨5188247, by rfl⟩ : syracuseStep 6917663 = 10376495) B10376495
theorem B2305577 : Blo 1213424 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B6147737 : Blo 1213424 6147737 := bstep (se 2 (by rfl) ⟨2305401, by rfl⟩ : syracuseStep 6147737 = 4610803) B4610803
theorem B4099895 : Blo 1213424 4099895 := bstep (se 1 (by rfl) ⟨3074921, by rfl⟩ : syracuseStep 4099895 = 6149843) B6149843
theorem B2305903 : Blo 1213424 2305903 := bstep (se 1 (by rfl) ⟨1729427, by rfl⟩ : syracuseStep 2305903 = 3458855) B3458855
theorem B1822631 : Blo 1213424 1822631 := bstep (se 1 (by rfl) ⟨1366973, by rfl⟩ : syracuseStep 1822631 = 2733947) B2733947
theorem B1822811 : Blo 1213424 1822811 := bstep (se 1 (by rfl) ⟨1367108, by rfl⟩ : syracuseStep 1822811 = 2734217) B2734217
theorem B2592911 : Blo 1213424 2592911 := bstep (se 1 (by rfl) ⟨1944683, by rfl⟩ : syracuseStep 2592911 = 3889367) B3889367
theorem B29552795 : Blo 1213424 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B4608161 : Blo 1213424 4608161 := bstep (se 2 (by rfl) ⟨1728060, by rfl⟩ : syracuseStep 4608161 = 3456121) B3456121
theorem B2732255 : Blo 1213424 2732255 := bstep (se 1 (by rfl) ⟨2049191, by rfl⟩ : syracuseStep 2732255 = 4098383) B4098383
theorem B4608359 : Blo 1213424 4608359 := bstep (se 1 (by rfl) ⟨3456269, by rfl⟩ : syracuseStep 4608359 = 6912539) B6912539
theorem B5190419 : Blo 1213424 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B9229139 : Blo 1213424 9229139 := bstep (se 1 (by rfl) ⟨6921854, by rfl⟩ : syracuseStep 9229139 = 13843709) B13843709
theorem B4100975 : Blo 1213424 4100975 := bstep (se 1 (by rfl) ⟨3075731, by rfl⟩ : syracuseStep 4100975 = 6151463) B6151463
theorem B6911081 : Blo 1213424 6911081 := bstep (se 2 (by rfl) ⟨2591655, by rfl⟩ : syracuseStep 6911081 = 5183311) B5183311
theorem B4609133 : Blo 1213424 4609133 := bstep (se 3 (by rfl) ⟨864212, by rfl⟩ : syracuseStep 4609133 = 1728425) B1728425
theorem B2528507 : Blo 1213424 2528507 := bstep (se 1 (by rfl) ⟨1896380, by rfl⟩ : syracuseStep 2528507 = 3792761) B3792761
theorem B10368431 : Blo 1213424 10368431 := bstep (se 1 (by rfl) ⟨7776323, by rfl⟩ : syracuseStep 10368431 = 15552647) B15552647
theorem B5256679 : Blo 1213424 5256679 := bstep (se 1 (by rfl) ⟨3942509, by rfl⟩ : syracuseStep 5256679 = 7885019) B7885019
theorem B6911513 : Blo 1213424 6911513 := bstep (se 2 (by rfl) ⟨2591817, by rfl⟩ : syracuseStep 6911513 = 5183635) B5183635
theorem B8754767 : Blo 1213424 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B4101785 : Blo 1213424 4101785 := bstep (se 2 (by rfl) ⟨1538169, by rfl⟩ : syracuseStep 4101785 = 3076339) B3076339
theorem B5183585 : Blo 1213424 5183585 := bstep (se 2 (by rfl) ⟨1943844, by rfl⟩ : syracuseStep 5183585 = 3887689) B3887689
theorem B13826213 : Blo 1213424 13826213 := bstep (se 4 (by rfl) ⟨1296207, by rfl⟩ : syracuseStep 13826213 = 2592415) B2592415
theorem B2734433 : Blo 1213424 2734433 := bstep (se 2 (by rfl) ⟨1025412, by rfl⟩ : syracuseStep 2734433 = 2050825) B2050825
theorem B13834961 : Blo 1213424 13834961 := bstep (se 2 (by rfl) ⟨5188110, by rfl⟩ : syracuseStep 13834961 = 10376221) B10376221
theorem B20224855 : Blo 1213424 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B10378205 : Blo 1213424 10378205 := bstep (se 3 (by rfl) ⟨1945913, by rfl⟩ : syracuseStep 10378205 = 3891827) B3891827
theorem B3742699 : Blo 1213424 3742699 := bstep (se 1 (by rfl) ⟨2807024, by rfl⟩ : syracuseStep 3742699 = 5614049) B5614049
theorem B159661115 : Blo 1213424 159661115 := bstep (se 1 (by rfl) ⟨119745836, by rfl⟩ : syracuseStep 159661115 = 239491673) B239491673
theorem B17505841 : Blo 1213424 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B6151787 : Blo 1213424 6151787 := bstep (se 1 (by rfl) ⟨4613840, by rfl⟩ : syracuseStep 6151787 = 9227681) B9227681
theorem B16604939 : Blo 1213424 16604939 := bstep (se 1 (by rfl) ⟨12453704, by rfl⟩ : syracuseStep 16604939 = 24907409) B24907409
theorem B4612079 : Blo 1213424 4612079 := bstep (se 1 (by rfl) ⟨3459059, by rfl⟩ : syracuseStep 4612079 = 6918119) B6918119
theorem B19701863 : Blo 1213424 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B3072107 : Blo 1213424 3072107 := bstep (se 1 (by rfl) ⟨2304080, by rfl⟩ : syracuseStep 3072107 = 4608161) B4608161
theorem B3072239 : Blo 1213424 3072239 := bstep (se 1 (by rfl) ⟨2304179, by rfl⟩ : syracuseStep 3072239 = 4608359) B4608359
theorem B6914429 : Blo 1213424 6914429 := bstep (se 3 (by rfl) ⟨1296455, by rfl⟩ : syracuseStep 6914429 = 2592911) B2592911
theorem B5186045 : Blo 1213424 5186045 := bstep (se 3 (by rfl) ⟨972383, by rfl⟩ : syracuseStep 5186045 = 1944767) B1944767
theorem B6152759 : Blo 1213424 6152759 := bstep (se 1 (by rfl) ⟨4614569, by rfl⟩ : syracuseStep 6152759 = 9229139) B9229139
theorem B6742685 : Blo 1213424 6742685 := bstep (se 3 (by rfl) ⟨1264253, by rfl⟩ : syracuseStep 6742685 = 2528507) B2528507
theorem B3072755 : Blo 1213424 3072755 := bstep (se 1 (by rfl) ⟨2304566, by rfl⟩ : syracuseStep 3072755 = 4609133) B4609133
theorem B4097033 : Blo 1213424 4097033 := bstep (se 2 (by rfl) ⟨1536387, by rfl⟩ : syracuseStep 4097033 = 3072775) B3072775
theorem B1213595 : Blo 1213424 1213595 := bstep (se 1 (by rfl) ⟨910196, by rfl⟩ : syracuseStep 1213595 = 1820393) B1820393
theorem B4990265 : Blo 1213424 4990265 := bstep (se 2 (by rfl) ⟨1871349, by rfl⟩ : syracuseStep 4990265 = 3742699) B3742699
theorem B9217475 : Blo 1213424 9217475 := bstep (se 1 (by rfl) ⟨6913106, by rfl⟩ : syracuseStep 9217475 = 13826213) B13826213
theorem B1213951 : Blo 1213424 1213951 := bstep (se 1 (by rfl) ⟨910463, by rfl⟩ : syracuseStep 1213951 = 1820927) B1820927
theorem B1820207 : Blo 1213424 1820207 := bstep (se 1 (by rfl) ⟨1365155, by rfl⟩ : syracuseStep 1820207 = 2730311) B2730311
theorem B1214043 : Blo 1213424 1214043 := bstep (se 1 (by rfl) ⟨910532, by rfl⟩ : syracuseStep 1214043 = 1821065) B1821065
theorem B1820399 : Blo 1213424 1820399 := bstep (se 1 (by rfl) ⟨1365299, by rfl⟩ : syracuseStep 1820399 = 2730599) B2730599
theorem B107865893 : Blo 1213424 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B1214375 : Blo 1213424 1214375 := bstep (se 1 (by rfl) ⟨910781, by rfl⟩ : syracuseStep 1214375 = 1821563) B1821563
theorem B9226223 : Blo 1213424 9226223 := bstep (se 1 (by rfl) ⟨6919667, by rfl⟩ : syracuseStep 9226223 = 13839335) B13839335
theorem B106440743 : Blo 1213424 106440743 := bstep (se 1 (by rfl) ⟨79830557, by rfl⟩ : syracuseStep 106440743 = 159661115) B159661115
theorem B23341121 : Blo 1213424 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B4098491 : Blo 1213424 4098491 := bstep (se 1 (by rfl) ⟨3073868, by rfl⟩ : syracuseStep 4098491 = 6147737) B6147737
theorem B3074537 : Blo 1213424 3074537 := bstep (se 2 (by rfl) ⟨1152951, by rfl⟩ : syracuseStep 3074537 = 2305903) B2305903
theorem B11069959 : Blo 1213424 11069959 := bstep (se 1 (by rfl) ⟨8302469, by rfl⟩ : syracuseStep 11069959 = 16604939) B16604939
theorem B1215087 : Blo 1213424 1215087 := bstep (se 1 (by rfl) ⟨911315, by rfl⟩ : syracuseStep 1215087 = 1822631) B1822631
theorem B3074719 : Blo 1213424 3074719 := bstep (se 1 (by rfl) ⟨2306039, by rfl⟩ : syracuseStep 3074719 = 4612079) B4612079
theorem B1215207 : Blo 1213424 1215207 := bstep (se 1 (by rfl) ⟨911405, by rfl⟩ : syracuseStep 1215207 = 1822811) B1822811
theorem B4377341 : Blo 1213424 4377341 := bstep (se 3 (by rfl) ⟨820751, by rfl⟩ : syracuseStep 4377341 = 1641503) B1641503
theorem B2960155 : Blo 1213424 2960155 := bstep (se 1 (by rfl) ⟨2220116, by rfl⟩ : syracuseStep 2960155 = 4440233) B4440233
theorem B1821503 : Blo 1213424 1821503 := bstep (se 1 (by rfl) ⟨1366127, by rfl⟩ : syracuseStep 1821503 = 2732255) B2732255
theorem B2730977 : Blo 1213424 2730977 := bstep (se 2 (by rfl) ⟨1024116, by rfl⟩ : syracuseStep 2730977 = 2048233) B2048233
theorem B7384061 : Blo 1213424 7384061 := bstep (se 3 (by rfl) ⟨1384511, by rfl⟩ : syracuseStep 7384061 = 2769023) B2769023
theorem B2731175 : Blo 1213424 2731175 := bstep (se 1 (by rfl) ⟨2048381, by rfl⟩ : syracuseStep 2731175 = 4096763) B4096763
theorem B3460279 : Blo 1213424 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B5401799 : Blo 1213424 5401799 := bstep (se 1 (by rfl) ⟨4051349, by rfl⟩ : syracuseStep 5401799 = 8102699) B8102699
theorem B4607387 : Blo 1213424 4607387 := bstep (se 1 (by rfl) ⟨3455540, by rfl⟩ : syracuseStep 4607387 = 6911081) B6911081
theorem B4607675 : Blo 1213424 4607675 := bstep (se 1 (by rfl) ⟨3455756, by rfl⟩ : syracuseStep 4607675 = 6911513) B6911513
theorem B5836511 : Blo 1213424 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B5189615 : Blo 1213424 5189615 := bstep (se 1 (by rfl) ⟨3892211, by rfl⟩ : syracuseStep 5189615 = 7784423) B7784423
theorem B3076127 : Blo 1213424 3076127 := bstep (se 1 (by rfl) ⟨2307095, by rfl⟩ : syracuseStep 3076127 = 4614191) B4614191
theorem B1822955 : Blo 1213424 1822955 := bstep (se 1 (by rfl) ⟨1367216, by rfl⟩ : syracuseStep 1822955 = 2734433) B2734433
theorem B26685895 : Blo 1213424 26685895 := bstep (se 1 (by rfl) ⟨20014421, by rfl⟩ : syracuseStep 26685895 = 40028843) B40028843
theorem B2732543 : Blo 1213424 2732543 := bstep (se 1 (by rfl) ⟨2049407, by rfl⟩ : syracuseStep 2732543 = 4098815) B4098815
theorem B7008905 : Blo 1213424 7008905 := bstep (se 2 (by rfl) ⟨2628339, by rfl⟩ : syracuseStep 7008905 = 5256679) B5256679
theorem B6918803 : Blo 1213424 6918803 := bstep (se 1 (by rfl) ⟨5189102, by rfl⟩ : syracuseStep 6918803 = 10378205) B10378205
theorem B1536671 : Blo 1213424 1536671 := bstep (se 1 (by rfl) ⟨1152503, by rfl⟩ : syracuseStep 1536671 = 2305007) B2305007
theorem B12464875 : Blo 1213424 12464875 := bstep (se 1 (by rfl) ⟨9348656, by rfl⟩ : syracuseStep 12464875 = 18697313) B18697313
theorem B1537051 : Blo 1213424 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B4101191 : Blo 1213424 4101191 := bstep (se 1 (by rfl) ⟨3075893, by rfl⟩ : syracuseStep 4101191 = 6151787) B6151787
theorem B2733263 : Blo 1213424 2733263 := bstep (se 1 (by rfl) ⟨2049947, by rfl⟩ : syracuseStep 2733263 = 4099895) B4099895
theorem B4380007 : Blo 1213424 4380007 := bstep (se 1 (by rfl) ⟨3285005, by rfl⟩ : syracuseStep 4380007 = 6570011) B6570011
theorem B2733641 : Blo 1213424 2733641 := bstep (se 2 (by rfl) ⟨1025115, by rfl⟩ : syracuseStep 2733641 = 2050231) B2050231
theorem B10524239 : Blo 1213424 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B2594663 : Blo 1213424 2594663 := bstep (se 1 (by rfl) ⟨1945997, by rfl⟩ : syracuseStep 2594663 = 3891995) B3891995
theorem B2733983 : Blo 1213424 2733983 := bstep (se 1 (by rfl) ⟨2050487, by rfl⟩ : syracuseStep 2733983 = 4100975) B4100975
theorem B6912287 : Blo 1213424 6912287 := bstep (se 1 (by rfl) ⟨5184215, by rfl⟩ : syracuseStep 6912287 = 10368431) B10368431
theorem B2734523 : Blo 1213424 2734523 := bstep (se 1 (by rfl) ⟨2050892, by rfl⟩ : syracuseStep 2734523 = 4101785) B4101785
theorem B3455723 : Blo 1213424 3455723 := bstep (se 1 (by rfl) ⟨2591792, by rfl⟩ : syracuseStep 3455723 = 5183585) B5183585
theorem B9223307 : Blo 1213424 9223307 := bstep (se 1 (by rfl) ⟨6917480, by rfl⟩ : syracuseStep 9223307 = 13834961) B13834961
theorem B4611775 : Blo 1213424 4611775 := bstep (se 1 (by rfl) ⟨3458831, by rfl⟩ : syracuseStep 4611775 = 6917663) B6917663
theorem B2048071 : Blo 1213424 2048071 := bstep (se 1 (by rfl) ⟨1536053, by rfl⟩ : syracuseStep 2048071 = 3072107) B3072107
theorem B2048159 : Blo 1213424 2048159 := bstep (se 1 (by rfl) ⟨1536119, by rfl⟩ : syracuseStep 2048159 = 3072239) B3072239
theorem B3457363 : Blo 1213424 3457363 := bstep (se 1 (by rfl) ⟨2593022, by rfl⟩ : syracuseStep 3457363 = 5186045) B5186045
theorem B4612535 : Blo 1213424 4612535 := bstep (se 1 (by rfl) ⟨3459401, by rfl⟩ : syracuseStep 4612535 = 6918803) B6918803
theorem B2048503 : Blo 1213424 2048503 := bstep (se 1 (by rfl) ⟨1536377, by rfl⟩ : syracuseStep 2048503 = 3072755) B3072755
theorem B3326843 : Blo 1213424 3326843 := bstep (se 1 (by rfl) ⟨2495132, by rfl⟩ : syracuseStep 3326843 = 4990265) B4990265
theorem B6144983 : Blo 1213424 6144983 := bstep (se 1 (by rfl) ⟨4608737, by rfl⟩ : syracuseStep 6144983 = 9217475) B9217475
theorem B1213471 : Blo 1213424 1213471 := bstep (se 1 (by rfl) ⟨910103, by rfl⟩ : syracuseStep 1213471 = 1820207) B1820207
theorem B1213599 : Blo 1213424 1213599 := bstep (se 1 (by rfl) ⟨910199, by rfl⟩ : syracuseStep 1213599 = 1820399) B1820399
theorem B71910595 : Blo 1213424 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B1729775 : Blo 1213424 1729775 := bstep (se 1 (by rfl) ⟨1297331, by rfl⟩ : syracuseStep 1729775 = 2594663) B2594663
theorem B2049401 : Blo 1213424 2049401 := bstep (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) B1537051
theorem B15787493 : Blo 1213424 15787493 := bstep (se 4 (by rfl) ⟨1480077, by rfl⟩ : syracuseStep 15787493 = 2960155) B2960155
theorem B4613705 : Blo 1213424 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B2049691 : Blo 1213424 2049691 := bstep (se 1 (by rfl) ⟨1537268, by rfl⟩ : syracuseStep 2049691 = 3074537) B3074537
theorem B4097789 : Blo 1213424 4097789 := bstep (se 3 (by rfl) ⟨768335, by rfl⟩ : syracuseStep 4097789 = 1536671) B1536671
theorem B2303815 : Blo 1213424 2303815 := bstep (se 1 (by rfl) ⟨1727861, by rfl⟩ : syracuseStep 2303815 = 3455723) B3455723
theorem B1214335 : Blo 1213424 1214335 := bstep (se 1 (by rfl) ⟨910751, by rfl⟩ : syracuseStep 1214335 = 1821503) B1821503
theorem B1820651 : Blo 1213424 1820651 := bstep (se 1 (by rfl) ⟨1365488, by rfl⟩ : syracuseStep 1820651 = 2730977) B2730977
theorem B1820783 : Blo 1213424 1820783 := bstep (se 1 (by rfl) ⟨1365587, by rfl⟩ : syracuseStep 1820783 = 2731175) B2731175
theorem B3459743 : Blo 1213424 3459743 := bstep (se 1 (by rfl) ⟨2594807, by rfl⟩ : syracuseStep 3459743 = 5189615) B5189615
theorem B2050751 : Blo 1213424 2050751 := bstep (se 1 (by rfl) ⟨1538063, by rfl⟩ : syracuseStep 2050751 = 3076127) B3076127
theorem B13134575 : Blo 1213424 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B1215303 : Blo 1213424 1215303 := bstep (se 1 (by rfl) ⟨911477, by rfl⟩ : syracuseStep 1215303 = 1822955) B1822955
theorem B1821695 : Blo 1213424 1821695 := bstep (se 1 (by rfl) ⟨1366271, by rfl⟩ : syracuseStep 1821695 = 2732543) B2732543
theorem B4672603 : Blo 1213424 4672603 := bstep (se 1 (by rfl) ⟨3504452, by rfl⟩ : syracuseStep 4672603 = 7008905) B7008905
theorem B35581193 : Blo 1213424 35581193 := bstep (se 2 (by rfl) ⟨13342947, by rfl⟩ : syracuseStep 35581193 = 26685895) B26685895
theorem B2731355 : Blo 1213424 2731355 := bstep (se 1 (by rfl) ⟨2048516, by rfl⟩ : syracuseStep 2731355 = 4097033) B4097033
theorem B1822175 : Blo 1213424 1822175 := bstep (se 1 (by rfl) ⟨1366631, by rfl⟩ : syracuseStep 1822175 = 2733263) B2733263
theorem B4099625 : Blo 1213424 4099625 := bstep (se 2 (by rfl) ⟨1537359, by rfl⟩ : syracuseStep 4099625 = 3074719) B3074719
theorem B1822427 : Blo 1213424 1822427 := bstep (se 1 (by rfl) ⟨1366820, by rfl⟩ : syracuseStep 1822427 = 2733641) B2733641
theorem B7016159 : Blo 1213424 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B1822655 : Blo 1213424 1822655 := bstep (se 1 (by rfl) ⟨1366991, by rfl⟩ : syracuseStep 1822655 = 2733983) B2733983
theorem B15560747 : Blo 1213424 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B4608191 : Blo 1213424 4608191 := bstep (se 1 (by rfl) ⟨3456143, by rfl⟩ : syracuseStep 4608191 = 6912287) B6912287
theorem B2732327 : Blo 1213424 2732327 := bstep (se 1 (by rfl) ⟨2049245, by rfl⟩ : syracuseStep 2732327 = 4098491) B4098491
theorem B1823015 : Blo 1213424 1823015 := bstep (se 1 (by rfl) ⟨1367261, by rfl⟩ : syracuseStep 1823015 = 2734523) B2734523
theorem B6148871 : Blo 1213424 6148871 := bstep (se 1 (by rfl) ⟨4611653, by rfl⟩ : syracuseStep 6148871 = 9223307) B9223307
theorem B3601199 : Blo 1213424 3601199 := bstep (se 1 (by rfl) ⟨2700899, by rfl⟩ : syracuseStep 3601199 = 5401799) B5401799
theorem B6149033 : Blo 1213424 6149033 := bstep (se 2 (by rfl) ⟨2305887, by rfl⟩ : syracuseStep 6149033 = 4611775) B4611775
theorem B283841981 : Blo 1213424 283841981 := bstep (se 3 (by rfl) ⟨53220371, by rfl⟩ : syracuseStep 283841981 = 106440743) B106440743
theorem B4609619 : Blo 1213424 4609619 := bstep (se 1 (by rfl) ⟨3457214, by rfl⟩ : syracuseStep 4609619 = 6914429) B6914429
theorem B4101839 : Blo 1213424 4101839 := bstep (se 1 (by rfl) ⟨3076379, by rfl⟩ : syracuseStep 4101839 = 6152759) B6152759
theorem B4495123 : Blo 1213424 4495123 := bstep (se 1 (by rfl) ⟨3371342, by rfl⟩ : syracuseStep 4495123 = 6742685) B6742685
theorem B14759945 : Blo 1213424 14759945 := bstep (se 2 (by rfl) ⟨5534979, by rfl⟩ : syracuseStep 14759945 = 11069959) B11069959
theorem B2734127 : Blo 1213424 2734127 := bstep (se 1 (by rfl) ⟨2050595, by rfl⟩ : syracuseStep 2734127 = 4101191) B4101191
theorem B16619833 : Blo 1213424 16619833 := bstep (se 2 (by rfl) ⟨6232437, by rfl⟩ : syracuseStep 16619833 = 12464875) B12464875
theorem B6150815 : Blo 1213424 6150815 := bstep (se 1 (by rfl) ⟨4613111, by rfl⟩ : syracuseStep 6150815 = 9226223) B9226223
theorem B5840009 : Blo 1213424 5840009 := bstep (se 2 (by rfl) ⟨2190003, by rfl⟩ : syracuseStep 5840009 = 4380007) B4380007
theorem B11672909 : Blo 1213424 11672909 := bstep (se 3 (by rfl) ⟨2188670, by rfl⟩ : syracuseStep 11672909 = 4377341) B4377341
theorem B4922707 : Blo 1213424 4922707 := bstep (se 1 (by rfl) ⟨3692030, by rfl⟩ : syracuseStep 4922707 = 7384061) B7384061
theorem B3071591 : Blo 1213424 3071591 := bstep (se 1 (by rfl) ⟨2303693, by rfl⟩ : syracuseStep 3071591 = 4607387) B4607387
theorem B3071783 : Blo 1213424 3071783 := bstep (se 1 (by rfl) ⟨2303837, by rfl⟩ : syracuseStep 3071783 = 4607675) B4607675
theorem B3891007 : Blo 1213424 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B3072127 : Blo 1213424 3072127 := bstep (se 1 (by rfl) ⟨2304095, by rfl⟩ : syracuseStep 3072127 = 4608191) B4608191
theorem B22159777 : Blo 1213424 22159777 := bstep (se 2 (by rfl) ⟨8309916, by rfl⟩ : syracuseStep 22159777 = 16619833) B16619833
theorem B2400799 : Blo 1213424 2400799 := bstep (se 1 (by rfl) ⟨1800599, by rfl⟩ : syracuseStep 2400799 = 3601199) B3601199
theorem B4612733 : Blo 1213424 4612733 := bstep (se 3 (by rfl) ⟨864887, by rfl⟩ : syracuseStep 4612733 = 1729775) B1729775
theorem B4096655 : Blo 1213424 4096655 := bstep (se 1 (by rfl) ⟨3072491, by rfl⟩ : syracuseStep 4096655 = 6144983) B6144983
theorem B189227987 : Blo 1213424 189227987 := bstep (se 1 (by rfl) ⟨141920990, by rfl⟩ : syracuseStep 189227987 = 283841981) B283841981
theorem B3073079 : Blo 1213424 3073079 := bstep (se 1 (by rfl) ⟨2304809, by rfl⟩ : syracuseStep 3073079 = 4609619) B4609619
theorem B1213767 : Blo 1213424 1213767 := bstep (se 1 (by rfl) ⟨910325, by rfl⟩ : syracuseStep 1213767 = 1820651) B1820651
theorem B9839963 : Blo 1213424 9839963 := bstep (se 1 (by rfl) ⟨7379972, by rfl⟩ : syracuseStep 9839963 = 14759945) B14759945
theorem B1213855 : Blo 1213424 1213855 := bstep (se 1 (by rfl) ⟨910391, by rfl⟩ : syracuseStep 1213855 = 1820783) B1820783
theorem B6563609 : Blo 1213424 6563609 := bstep (se 2 (by rfl) ⟨2461353, by rfl⟩ : syracuseStep 6563609 = 4922707) B4922707
theorem B1214463 : Blo 1213424 1214463 := bstep (se 1 (by rfl) ⟨910847, by rfl⟩ : syracuseStep 1214463 = 1821695) B1821695
theorem B3893339 : Blo 1213424 3893339 := bstep (se 1 (by rfl) ⟨2920004, by rfl⟩ : syracuseStep 3893339 = 5840009) B5840009
theorem B1820903 : Blo 1213424 1820903 := bstep (se 1 (by rfl) ⟨1365677, by rfl⟩ : syracuseStep 1820903 = 2731355) B2731355
theorem B1214783 : Blo 1213424 1214783 := bstep (se 1 (by rfl) ⟨911087, by rfl⟩ : syracuseStep 1214783 = 1822175) B1822175
theorem B5188009 : Blo 1213424 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B1214951 : Blo 1213424 1214951 := bstep (se 1 (by rfl) ⟨911213, by rfl⟩ : syracuseStep 1214951 = 1822427) B1822427
theorem B1215103 : Blo 1213424 1215103 := bstep (se 1 (by rfl) ⟨911327, by rfl⟩ : syracuseStep 1215103 = 1822655) B1822655
theorem B10373831 : Blo 1213424 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B2730761 : Blo 1213424 2730761 := bstep (se 2 (by rfl) ⟨1024035, by rfl⟩ : syracuseStep 2730761 = 2048071) B2048071
theorem B1821551 : Blo 1213424 1821551 := bstep (se 1 (by rfl) ⟨1366163, by rfl⟩ : syracuseStep 1821551 = 2732327) B2732327
theorem B1215343 : Blo 1213424 1215343 := bstep (se 1 (by rfl) ⟨911507, by rfl⟩ : syracuseStep 1215343 = 1823015) B1823015
theorem B3075023 : Blo 1213424 3075023 := bstep (se 1 (by rfl) ⟨2306267, by rfl⟩ : syracuseStep 3075023 = 4612535) B4612535
theorem B4099247 : Blo 1213424 4099247 := bstep (se 1 (by rfl) ⟨3074435, by rfl⟩ : syracuseStep 4099247 = 6148871) B6148871
theorem B4099355 : Blo 1213424 4099355 := bstep (se 1 (by rfl) ⟨3074516, by rfl⟩ : syracuseStep 4099355 = 6149033) B6149033
theorem B2731337 : Blo 1213424 2731337 := bstep (se 2 (by rfl) ⟨1024251, by rfl⟩ : syracuseStep 2731337 = 2048503) B2048503
theorem B3075803 : Blo 1213424 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B2731859 : Blo 1213424 2731859 := bstep (se 1 (by rfl) ⟨2048894, by rfl⟩ : syracuseStep 2731859 = 4097789) B4097789
theorem B1822751 : Blo 1213424 1822751 := bstep (se 1 (by rfl) ⟨1367063, by rfl⟩ : syracuseStep 1822751 = 2734127) B2734127
theorem B6230137 : Blo 1213424 6230137 := bstep (se 2 (by rfl) ⟨2336301, by rfl⟩ : syracuseStep 6230137 = 4672603) B4672603
theorem B2306495 : Blo 1213424 2306495 := bstep (se 1 (by rfl) ⟨1729871, by rfl⟩ : syracuseStep 2306495 = 3459743) B3459743
theorem B4100543 : Blo 1213424 4100543 := bstep (se 1 (by rfl) ⟨3075407, by rfl⟩ : syracuseStep 4100543 = 6150815) B6150815
theorem B23720795 : Blo 1213424 23720795 := bstep (se 1 (by rfl) ⟨17790596, by rfl⟩ : syracuseStep 23720795 = 35581193) B35581193
theorem B2732921 : Blo 1213424 2732921 := bstep (se 2 (by rfl) ⟨1024845, by rfl⟩ : syracuseStep 2732921 = 2049691) B2049691
theorem B5993497 : Blo 1213424 5993497 := bstep (se 2 (by rfl) ⟨2247561, by rfl⟩ : syracuseStep 5993497 = 4495123) B4495123
theorem B2733083 : Blo 1213424 2733083 := bstep (se 1 (by rfl) ⟨2049812, by rfl⟩ : syracuseStep 2733083 = 4099625) B4099625
theorem B1365439 : Blo 1213424 1365439 := bstep (se 1 (by rfl) ⟨1024079, by rfl⟩ : syracuseStep 1365439 = 2048159) B2048159
theorem B4609817 : Blo 1213424 4609817 := bstep (se 2 (by rfl) ⟨1728681, by rfl⟩ : syracuseStep 4609817 = 3457363) B3457363
theorem B1366267 : Blo 1213424 1366267 := bstep (se 1 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 1366267 = 2049401) B2049401
theorem B10524995 : Blo 1213424 10524995 := bstep (se 1 (by rfl) ⟨7893746, by rfl⟩ : syracuseStep 10524995 = 15787493) B15787493
theorem B383523173 : Blo 1213424 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B2734559 : Blo 1213424 2734559 := bstep (se 1 (by rfl) ⟨2050919, by rfl⟩ : syracuseStep 2734559 = 4101839) B4101839
theorem B1367167 : Blo 1213424 1367167 := bstep (se 1 (by rfl) ⟨1025375, by rfl⟩ : syracuseStep 1367167 = 2050751) B2050751
theorem B8756383 : Blo 1213424 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B7781939 : Blo 1213424 7781939 := bstep (se 1 (by rfl) ⟨5836454, by rfl⟩ : syracuseStep 7781939 = 11672909) B11672909
theorem B8871581 : Blo 1213424 8871581 := bstep (se 3 (by rfl) ⟨1663421, by rfl⟩ : syracuseStep 8871581 = 3326843) B3326843
theorem B2047727 : Blo 1213424 2047727 := bstep (se 1 (by rfl) ⟨1535795, by rfl⟩ : syracuseStep 2047727 = 3071591) B3071591
theorem B3071753 : Blo 1213424 3071753 := bstep (se 2 (by rfl) ⟨1151907, by rfl⟩ : syracuseStep 3071753 = 2303815) B2303815
theorem B4677439 : Blo 1213424 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B2047855 : Blo 1213424 2047855 := bstep (se 1 (by rfl) ⟨1535891, by rfl⟩ : syracuseStep 2047855 = 3071783) B3071783
theorem B31965317 : Blo 1213424 31965317 := bstep (se 4 (by rfl) ⟨2996748, by rfl⟩ : syracuseStep 31965317 = 5993497) B5993497
theorem B8306849 : Blo 1213424 8306849 := bstep (se 2 (by rfl) ⟨3115068, by rfl⟩ : syracuseStep 8306849 = 6230137) B6230137
theorem B4096169 : Blo 1213424 4096169 := bstep (se 2 (by rfl) ⟨1536063, by rfl⟩ : syracuseStep 4096169 = 3072127) B3072127
theorem B2048719 : Blo 1213424 2048719 := bstep (se 1 (by rfl) ⟨1536539, by rfl⟩ : syracuseStep 2048719 = 3073079) B3073079
theorem B3073211 : Blo 1213424 3073211 := bstep (se 1 (by rfl) ⟨2304908, by rfl⟩ : syracuseStep 3073211 = 4609817) B4609817
theorem B4375739 : Blo 1213424 4375739 := bstep (se 1 (by rfl) ⟨3281804, by rfl⟩ : syracuseStep 4375739 = 6563609) B6563609
theorem B1213935 : Blo 1213424 1213935 := bstep (se 1 (by rfl) ⟨910451, by rfl⟩ : syracuseStep 1213935 = 1820903) B1820903
theorem B11675177 : Blo 1213424 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B255682115 : Blo 1213424 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B6915887 : Blo 1213424 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B1820507 : Blo 1213424 1820507 := bstep (se 1 (by rfl) ⟨1365380, by rfl⟩ : syracuseStep 1820507 = 2730761) B2730761
theorem B1214367 : Blo 1213424 1214367 := bstep (se 1 (by rfl) ⟨910775, by rfl⟩ : syracuseStep 1214367 = 1821551) B1821551
theorem B1820585 : Blo 1213424 1820585 := bstep (se 2 (by rfl) ⟨682719, by rfl⟩ : syracuseStep 1820585 = 1365439) B1365439
theorem B2050015 : Blo 1213424 2050015 := bstep (se 1 (by rfl) ⟨1537511, by rfl⟩ : syracuseStep 2050015 = 3075023) B3075023
theorem B1820891 : Blo 1213424 1820891 := bstep (se 1 (by rfl) ⟨1365668, by rfl⟩ : syracuseStep 1820891 = 2731337) B2731337
theorem B5187959 : Blo 1213424 5187959 := bstep (se 1 (by rfl) ⟨3890969, by rfl⟩ : syracuseStep 5187959 = 7781939) B7781939
theorem B6236585 : Blo 1213424 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B2050535 : Blo 1213424 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B2730473 : Blo 1213424 2730473 := bstep (se 2 (by rfl) ⟨1023927, by rfl⟩ : syracuseStep 2730473 = 2047855) B2047855
theorem B1821239 : Blo 1213424 1821239 := bstep (se 1 (by rfl) ⟨1365929, by rfl⟩ : syracuseStep 1821239 = 2731859) B2731859
theorem B1215167 : Blo 1213424 1215167 := bstep (se 1 (by rfl) ⟨911375, by rfl⟩ : syracuseStep 1215167 = 1822751) B1822751
theorem B1821689 : Blo 1213424 1821689 := bstep (se 2 (by rfl) ⟨683133, by rfl⟩ : syracuseStep 1821689 = 1366267) B1366267
theorem B3075155 : Blo 1213424 3075155 := bstep (se 1 (by rfl) ⟨2306366, by rfl⟩ : syracuseStep 3075155 = 4612733) B4612733
theorem B2731103 : Blo 1213424 2731103 := bstep (se 1 (by rfl) ⟨2048327, by rfl⟩ : syracuseStep 2731103 = 4096655) B4096655
theorem B6917345 : Blo 1213424 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B15813863 : Blo 1213424 15813863 := bstep (se 1 (by rfl) ⟨11860397, by rfl⟩ : syracuseStep 15813863 = 23720795) B23720795
theorem B1821947 : Blo 1213424 1821947 := bstep (se 1 (by rfl) ⟨1366460, by rfl⟩ : syracuseStep 1821947 = 2732921) B2732921
theorem B126151991 : Blo 1213424 126151991 := bstep (se 1 (by rfl) ⟨94613993, by rfl⟩ : syracuseStep 126151991 = 189227987) B189227987
theorem B1822055 : Blo 1213424 1822055 := bstep (se 1 (by rfl) ⟨1366541, by rfl⟩ : syracuseStep 1822055 = 2733083) B2733083
theorem B1822889 : Blo 1213424 1822889 := bstep (se 2 (by rfl) ⟨683583, by rfl⟩ : syracuseStep 1822889 = 1367167) B1367167
theorem B7016663 : Blo 1213424 7016663 := bstep (se 1 (by rfl) ⟨5262497, by rfl⟩ : syracuseStep 7016663 = 10524995) B10524995
theorem B1823039 : Blo 1213424 1823039 := bstep (se 1 (by rfl) ⟨1367279, by rfl⟩ : syracuseStep 1823039 = 2734559) B2734559
theorem B2732831 : Blo 1213424 2732831 := bstep (se 1 (by rfl) ⟨2049623, by rfl⟩ : syracuseStep 2732831 = 4099247) B4099247
theorem B2732903 : Blo 1213424 2732903 := bstep (se 1 (by rfl) ⟨2049677, by rfl⟩ : syracuseStep 2732903 = 4099355) B4099355
theorem B1365151 : Blo 1213424 1365151 := bstep (se 1 (by rfl) ⟨1023863, by rfl⟩ : syracuseStep 1365151 = 2047727) B2047727
theorem B2733695 : Blo 1213424 2733695 := bstep (se 1 (by rfl) ⟨2050271, by rfl⟩ : syracuseStep 2733695 = 4100543) B4100543
theorem B29546369 : Blo 1213424 29546369 := bstep (se 2 (by rfl) ⟨11079888, by rfl⟩ : syracuseStep 29546369 = 22159777) B22159777
theorem B3201065 : Blo 1213424 3201065 := bstep (se 2 (by rfl) ⟨1200399, by rfl⟩ : syracuseStep 3201065 = 2400799) B2400799
theorem B6559975 : Blo 1213424 6559975 := bstep (se 1 (by rfl) ⟨4919981, by rfl⟩ : syracuseStep 6559975 = 9839963) B9839963
theorem B6150653 : Blo 1213424 6150653 := bstep (se 3 (by rfl) ⟨1153247, by rfl⟩ : syracuseStep 6150653 = 2306495) B2306495
theorem B2595559 : Blo 1213424 2595559 := bstep (se 1 (by rfl) ⟨1946669, by rfl⟩ : syracuseStep 2595559 = 3893339) B3893339
theorem B5914387 : Blo 1213424 5914387 := bstep (se 1 (by rfl) ⟨4435790, by rfl⟩ : syracuseStep 5914387 = 8871581) B8871581
theorem B2047835 : Blo 1213424 2047835 := bstep (se 1 (by rfl) ⟨1535876, by rfl⟩ : syracuseStep 2047835 = 3071753) B3071753
theorem B5537899 : Blo 1213424 5537899 := bstep (se 1 (by rfl) ⟨4153424, by rfl⟩ : syracuseStep 5537899 = 8306849) B8306849
theorem B18711101 : Blo 1213424 18711101 := bstep (se 3 (by rfl) ⟨3508331, by rfl⟩ : syracuseStep 18711101 = 7016663) B7016663
theorem B2048807 : Blo 1213424 2048807 := bstep (se 1 (by rfl) ⟨1536605, by rfl⟩ : syracuseStep 2048807 = 3073211) B3073211
theorem B7783451 : Blo 1213424 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B1213671 : Blo 1213424 1213671 := bstep (se 1 (by rfl) ⟨910253, by rfl⟩ : syracuseStep 1213671 = 1820507) B1820507
theorem B1213723 : Blo 1213424 1213723 := bstep (se 1 (by rfl) ⟨910292, by rfl⟩ : syracuseStep 1213723 = 1820585) B1820585
theorem B1213927 : Blo 1213424 1213927 := bstep (se 1 (by rfl) ⟨910445, by rfl⟩ : syracuseStep 1213927 = 1820891) B1820891
theorem B1820201 : Blo 1213424 1820201 := bstep (se 2 (by rfl) ⟨682575, by rfl⟩ : syracuseStep 1820201 = 1365151) B1365151
theorem B3458639 : Blo 1213424 3458639 := bstep (se 1 (by rfl) ⟨2593979, by rfl⟩ : syracuseStep 3458639 = 5187959) B5187959
theorem B1820315 : Blo 1213424 1820315 := bstep (se 1 (by rfl) ⟨1365236, by rfl⟩ : syracuseStep 1820315 = 2730473) B2730473
theorem B1214159 : Blo 1213424 1214159 := bstep (se 1 (by rfl) ⟨910619, by rfl⟩ : syracuseStep 1214159 = 1821239) B1821239
theorem B1214459 : Blo 1213424 1214459 := bstep (se 1 (by rfl) ⟨910844, by rfl⟩ : syracuseStep 1214459 = 1821689) B1821689
theorem B2050103 : Blo 1213424 2050103 := bstep (se 1 (by rfl) ⟨1537577, by rfl⟩ : syracuseStep 2050103 = 3075155) B3075155
theorem B1820735 : Blo 1213424 1820735 := bstep (se 1 (by rfl) ⟨1365551, by rfl⟩ : syracuseStep 1820735 = 2731103) B2731103
theorem B1214631 : Blo 1213424 1214631 := bstep (se 1 (by rfl) ⟨910973, by rfl⟩ : syracuseStep 1214631 = 1821947) B1821947
theorem B84101327 : Blo 1213424 84101327 := bstep (se 1 (by rfl) ⟨63075995, by rfl⟩ : syracuseStep 84101327 = 126151991) B126151991
theorem B1214703 : Blo 1213424 1214703 := bstep (se 1 (by rfl) ⟨911027, by rfl⟩ : syracuseStep 1214703 = 1822055) B1822055
theorem B2730779 : Blo 1213424 2730779 := bstep (se 1 (by rfl) ⟨2048084, by rfl⟩ : syracuseStep 2730779 = 4096169) B4096169
theorem B1215259 : Blo 1213424 1215259 := bstep (se 1 (by rfl) ⟨911444, by rfl⟩ : syracuseStep 1215259 = 1822889) B1822889
theorem B1215359 : Blo 1213424 1215359 := bstep (se 1 (by rfl) ⟨911519, by rfl⟩ : syracuseStep 1215359 = 1823039) B1823039
theorem B11668637 : Blo 1213424 11668637 := bstep (se 3 (by rfl) ⟨2187869, by rfl⟩ : syracuseStep 11668637 = 4375739) B4375739
theorem B1821887 : Blo 1213424 1821887 := bstep (se 1 (by rfl) ⟨1366415, by rfl⟩ : syracuseStep 1821887 = 2732831) B2732831
theorem B1821935 : Blo 1213424 1821935 := bstep (se 1 (by rfl) ⟨1366451, by rfl⟩ : syracuseStep 1821935 = 2732903) B2732903
theorem B2731625 : Blo 1213424 2731625 := bstep (se 2 (by rfl) ⟨1024359, by rfl⟩ : syracuseStep 2731625 = 2048719) B2048719
theorem B3460745 : Blo 1213424 3460745 := bstep (se 2 (by rfl) ⟨1297779, by rfl⟩ : syracuseStep 3460745 = 2595559) B2595559
theorem B170454743 : Blo 1213424 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B1822463 : Blo 1213424 1822463 := bstep (se 1 (by rfl) ⟨1366847, by rfl⟩ : syracuseStep 1822463 = 2733695) B2733695
theorem B19697579 : Blo 1213424 19697579 := bstep (se 1 (by rfl) ⟨14773184, by rfl⟩ : syracuseStep 19697579 = 29546369) B29546369
theorem B2134043 : Blo 1213424 2134043 := bstep (se 1 (by rfl) ⟨1600532, by rfl⟩ : syracuseStep 2134043 = 3201065) B3201065
theorem B340963381 : Blo 1213424 340963381 := bstep (se 5 (by rfl) ⟨15982658, by rfl⟩ : syracuseStep 340963381 = 31965317) B31965317
theorem B4157723 : Blo 1213424 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B4100435 : Blo 1213424 4100435 := bstep (se 1 (by rfl) ⟨3075326, by rfl⟩ : syracuseStep 4100435 = 6150653) B6150653
theorem B7885849 : Blo 1213424 7885849 := bstep (se 2 (by rfl) ⟨2957193, by rfl⟩ : syracuseStep 7885849 = 5914387) B5914387
theorem B1365223 : Blo 1213424 1365223 := bstep (se 1 (by rfl) ⟨1023917, by rfl⟩ : syracuseStep 1365223 = 2047835) B2047835
theorem B2733353 : Blo 1213424 2733353 := bstep (se 2 (by rfl) ⟨1025007, by rfl⟩ : syracuseStep 2733353 = 2050015) B2050015
theorem B8746633 : Blo 1213424 8746633 := bstep (se 2 (by rfl) ⟨3279987, by rfl⟩ : syracuseStep 8746633 = 6559975) B6559975
theorem B4610591 : Blo 1213424 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B1367023 : Blo 1213424 1367023 := bstep (se 1 (by rfl) ⟨1025267, by rfl⟩ : syracuseStep 1367023 = 2050535) B2050535
theorem B4611563 : Blo 1213424 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B10542575 : Blo 1213424 10542575 := bstep (se 1 (by rfl) ⟨7906931, by rfl⟩ : syracuseStep 10542575 = 15813863) B15813863
theorem B1213467 : Blo 1213424 1213467 := bstep (se 1 (by rfl) ⟨910100, by rfl⟩ : syracuseStep 1213467 = 1820201) B1820201
theorem B1213543 : Blo 1213424 1213543 := bstep (se 1 (by rfl) ⟨910157, by rfl⟩ : syracuseStep 1213543 = 1820315) B1820315
theorem B1213823 : Blo 1213424 1213823 := bstep (se 1 (by rfl) ⟨910367, by rfl⟩ : syracuseStep 1213823 = 1820735) B1820735
theorem B56067551 : Blo 1213424 56067551 := bstep (se 1 (by rfl) ⟨42050663, by rfl⟩ : syracuseStep 56067551 = 84101327) B84101327
theorem B1820297 : Blo 1213424 1820297 := bstep (se 2 (by rfl) ⟨682611, by rfl⟩ : syracuseStep 1820297 = 1365223) B1365223
theorem B3073727 : Blo 1213424 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B1820519 : Blo 1213424 1820519 := bstep (se 1 (by rfl) ⟨1365389, by rfl⟩ : syracuseStep 1820519 = 2730779) B2730779
theorem B1214591 : Blo 1213424 1214591 := bstep (se 1 (by rfl) ⟨910943, by rfl⟩ : syracuseStep 1214591 = 1821887) B1821887
theorem B1214623 : Blo 1213424 1214623 := bstep (se 1 (by rfl) ⟨910967, by rfl⟩ : syracuseStep 1214623 = 1821935) B1821935
theorem B3074375 : Blo 1213424 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B1821083 : Blo 1213424 1821083 := bstep (se 1 (by rfl) ⟨1365812, by rfl⟩ : syracuseStep 1821083 = 2731625) B2731625
theorem B1214975 : Blo 1213424 1214975 := bstep (se 1 (by rfl) ⟨911231, by rfl⟩ : syracuseStep 1214975 = 1822463) B1822463
theorem B454617841 : Blo 1213424 454617841 := bstep (se 2 (by rfl) ⟨170481690, by rfl⟩ : syracuseStep 454617841 = 340963381) B340963381
theorem B7383865 : Blo 1213424 7383865 := bstep (se 2 (by rfl) ⟨2768949, by rfl⟩ : syracuseStep 7383865 = 5537899) B5537899
theorem B2771815 : Blo 1213424 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B5188967 : Blo 1213424 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B46648709 : Blo 1213424 46648709 := bstep (se 4 (by rfl) ⟨4373316, by rfl⟩ : syracuseStep 46648709 = 8746633) B8746633
theorem B1822235 : Blo 1213424 1822235 := bstep (se 1 (by rfl) ⟨1366676, by rfl⟩ : syracuseStep 1822235 = 2733353) B2733353
theorem B2305759 : Blo 1213424 2305759 := bstep (se 1 (by rfl) ⟨1729319, by rfl⟩ : syracuseStep 2305759 = 3458639) B3458639
theorem B1822697 : Blo 1213424 1822697 := bstep (se 2 (by rfl) ⟨683511, by rfl⟩ : syracuseStep 1822697 = 1367023) B1367023
theorem B10514465 : Blo 1213424 10514465 := bstep (se 2 (by rfl) ⟨3942924, by rfl⟩ : syracuseStep 10514465 = 7885849) B7885849
theorem B9228653 : Blo 1213424 9228653 := bstep (se 3 (by rfl) ⟨1730372, by rfl⟩ : syracuseStep 9228653 = 3460745) B3460745
theorem B7779091 : Blo 1213424 7779091 := bstep (se 1 (by rfl) ⟨5834318, by rfl⟩ : syracuseStep 7779091 = 11668637) B11668637
theorem B113636495 : Blo 1213424 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B1422695 : Blo 1213424 1422695 := bstep (se 1 (by rfl) ⟨1067021, by rfl⟩ : syracuseStep 1422695 = 2134043) B2134043
theorem B2733623 : Blo 1213424 2733623 := bstep (se 1 (by rfl) ⟨2050217, by rfl⟩ : syracuseStep 2733623 = 4100435) B4100435
theorem B1365871 : Blo 1213424 1365871 := bstep (se 1 (by rfl) ⟨1024403, by rfl⟩ : syracuseStep 1365871 = 2048807) B2048807
theorem B1366735 : Blo 1213424 1366735 := bstep (se 1 (by rfl) ⟨1025051, by rfl⟩ : syracuseStep 1366735 = 2050103) B2050103
theorem B49896269 : Blo 1213424 49896269 := bstep (se 3 (by rfl) ⟨9355550, by rfl⟩ : syracuseStep 49896269 = 18711101) B18711101
theorem B7028383 : Blo 1213424 7028383 := bstep (se 1 (by rfl) ⟨5271287, by rfl⟩ : syracuseStep 7028383 = 10542575) B10542575
theorem B13131719 : Blo 1213424 13131719 := bstep (se 1 (by rfl) ⟨9848789, by rfl⟩ : syracuseStep 13131719 = 19697579) B19697579
theorem B6152435 : Blo 1213424 6152435 := bstep (se 1 (by rfl) ⟨4614326, by rfl⟩ : syracuseStep 6152435 = 9228653) B9228653
theorem B3793853 : Blo 1213424 3793853 := bstep (se 3 (by rfl) ⟨711347, by rfl⟩ : syracuseStep 3793853 = 1422695) B1422695
theorem B10372121 : Blo 1213424 10372121 := bstep (se 2 (by rfl) ⟨3889545, by rfl⟩ : syracuseStep 10372121 = 7779091) B7779091
theorem B1213531 : Blo 1213424 1213531 := bstep (se 1 (by rfl) ⟨910148, by rfl⟩ : syracuseStep 1213531 = 1820297) B1820297
theorem B2049151 : Blo 1213424 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B3695753 : Blo 1213424 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B1213679 : Blo 1213424 1213679 := bstep (se 1 (by rfl) ⟨910259, by rfl⟩ : syracuseStep 1213679 = 1820519) B1820519
theorem B2049583 : Blo 1213424 2049583 := bstep (se 1 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 2049583 = 3074375) B3074375
theorem B1214055 : Blo 1213424 1214055 := bstep (se 1 (by rfl) ⟨910541, by rfl⟩ : syracuseStep 1214055 = 1821083) B1821083
theorem B3459311 : Blo 1213424 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B31099139 : Blo 1213424 31099139 := bstep (se 1 (by rfl) ⟨23324354, by rfl⟩ : syracuseStep 31099139 = 46648709) B46648709
theorem B3074345 : Blo 1213424 3074345 := bstep (se 2 (by rfl) ⟨1152879, by rfl⟩ : syracuseStep 3074345 = 2305759) B2305759
theorem B1214823 : Blo 1213424 1214823 := bstep (se 1 (by rfl) ⟨911117, by rfl⟩ : syracuseStep 1214823 = 1822235) B1822235
theorem B1821161 : Blo 1213424 1821161 := bstep (se 2 (by rfl) ⟨682935, by rfl⟩ : syracuseStep 1821161 = 1365871) B1365871
theorem B1215131 : Blo 1213424 1215131 := bstep (se 1 (by rfl) ⟨911348, by rfl⟩ : syracuseStep 1215131 = 1822697) B1822697
theorem B1822313 : Blo 1213424 1822313 := bstep (se 2 (by rfl) ⟨683367, by rfl⟩ : syracuseStep 1822313 = 1366735) B1366735
theorem B1822415 : Blo 1213424 1822415 := bstep (se 1 (by rfl) ⟨1366811, by rfl⟩ : syracuseStep 1822415 = 2733623) B2733623
theorem B33264179 : Blo 1213424 33264179 := bstep (se 1 (by rfl) ⟨24948134, by rfl⟩ : syracuseStep 33264179 = 49896269) B49896269
theorem B8754479 : Blo 1213424 8754479 := bstep (se 1 (by rfl) ⟨6565859, by rfl⟩ : syracuseStep 8754479 = 13131719) B13131719
theorem B7009643 : Blo 1213424 7009643 := bstep (se 1 (by rfl) ⟨5257232, by rfl⟩ : syracuseStep 7009643 = 10514465) B10514465
theorem B75757663 : Blo 1213424 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B37378367 : Blo 1213424 37378367 := bstep (se 1 (by rfl) ⟨28033775, by rfl⟩ : syracuseStep 37378367 = 56067551) B56067551
theorem B606157121 : Blo 1213424 606157121 := bstep (se 2 (by rfl) ⟨227308920, by rfl⟩ : syracuseStep 606157121 = 454617841) B454617841
theorem B9845153 : Blo 1213424 9845153 := bstep (se 2 (by rfl) ⟨3691932, by rfl⟩ : syracuseStep 9845153 = 7383865) B7383865
theorem B9371177 : Blo 1213424 9371177 := bstep (se 2 (by rfl) ⟨3514191, by rfl⟩ : syracuseStep 9371177 = 7028383) B7028383
theorem B9855341 : Blo 1213424 9855341 := bstep (se 3 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 9855341 = 3695753) B3695753
theorem B22176119 : Blo 1213424 22176119 := bstep (se 1 (by rfl) ⟨16632089, by rfl⟩ : syracuseStep 22176119 = 33264179) B33264179
theorem B6914747 : Blo 1213424 6914747 := bstep (se 1 (by rfl) ⟨5186060, by rfl⟩ : syracuseStep 6914747 = 10372121) B10372121
theorem B2049563 : Blo 1213424 2049563 := bstep (se 1 (by rfl) ⟨1537172, by rfl⟩ : syracuseStep 2049563 = 3074345) B3074345
theorem B404104747 : Blo 1213424 404104747 := bstep (se 1 (by rfl) ⟨303078560, by rfl⟩ : syracuseStep 404104747 = 606157121) B606157121
theorem B6563435 : Blo 1213424 6563435 := bstep (se 1 (by rfl) ⟨4922576, by rfl⟩ : syracuseStep 6563435 = 9845153) B9845153
theorem B1214107 : Blo 1213424 1214107 := bstep (se 1 (by rfl) ⟨910580, by rfl⟩ : syracuseStep 1214107 = 1821161) B1821161
theorem B1214875 : Blo 1213424 1214875 := bstep (se 1 (by rfl) ⟨911156, by rfl⟩ : syracuseStep 1214875 = 1822313) B1822313
theorem B1214943 : Blo 1213424 1214943 := bstep (se 1 (by rfl) ⟨911207, by rfl⟩ : syracuseStep 1214943 = 1822415) B1822415
theorem B404040869 : Blo 1213424 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B5836319 : Blo 1213424 5836319 := bstep (se 1 (by rfl) ⟨4377239, by rfl⟩ : syracuseStep 5836319 = 8754479) B8754479
theorem B4673095 : Blo 1213424 4673095 := bstep (se 1 (by rfl) ⟨3504821, by rfl⟩ : syracuseStep 4673095 = 7009643) B7009643
theorem B2306207 : Blo 1213424 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B2732201 : Blo 1213424 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B2732777 : Blo 1213424 2732777 := bstep (se 2 (by rfl) ⟨1024791, by rfl⟩ : syracuseStep 2732777 = 2049583) B2049583
theorem B6247451 : Blo 1213424 6247451 := bstep (se 1 (by rfl) ⟨4685588, by rfl⟩ : syracuseStep 6247451 = 9371177) B9371177
theorem B4101623 : Blo 1213424 4101623 := bstep (se 1 (by rfl) ⟨3076217, by rfl⟩ : syracuseStep 4101623 = 6152435) B6152435
theorem B2529235 : Blo 1213424 2529235 := bstep (se 1 (by rfl) ⟨1896926, by rfl⟩ : syracuseStep 2529235 = 3793853) B3793853
theorem B20732759 : Blo 1213424 20732759 := bstep (se 1 (by rfl) ⟨15549569, by rfl⟩ : syracuseStep 20732759 = 31099139) B31099139
theorem B24918911 : Blo 1213424 24918911 := bstep (se 1 (by rfl) ⟨18689183, by rfl⟩ : syracuseStep 24918911 = 37378367) B37378367
theorem B6570227 : Blo 1213424 6570227 := bstep (se 1 (by rfl) ⟨4927670, by rfl⟩ : syracuseStep 6570227 = 9855341) B9855341
theorem B13821839 : Blo 1213424 13821839 := bstep (se 1 (by rfl) ⟨10366379, by rfl⟩ : syracuseStep 13821839 = 20732759) B20732759
theorem B538806329 : Blo 1213424 538806329 := bstep (se 2 (by rfl) ⟨202052373, by rfl⟩ : syracuseStep 538806329 = 404104747) B404104747
theorem B1821467 : Blo 1213424 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B24923173 : Blo 1213424 24923173 := bstep (se 4 (by rfl) ⟨2336547, by rfl⟩ : syracuseStep 24923173 = 4673095) B4673095
theorem B1821851 : Blo 1213424 1821851 := bstep (se 1 (by rfl) ⟨1366388, by rfl⟩ : syracuseStep 1821851 = 2732777) B2732777
theorem B4164967 : Blo 1213424 4164967 := bstep (se 1 (by rfl) ⟨3123725, by rfl⟩ : syracuseStep 4164967 = 6247451) B6247451
theorem B17502493 : Blo 1213424 17502493 := bstep (se 3 (by rfl) ⟨3281717, by rfl⟩ : syracuseStep 17502493 = 6563435) B6563435
theorem B3372313 : Blo 1213424 3372313 := bstep (se 2 (by rfl) ⟨1264617, by rfl⟩ : syracuseStep 3372313 = 2529235) B2529235
theorem B1537471 : Blo 1213424 1537471 := bstep (se 1 (by rfl) ⟨1153103, by rfl⟩ : syracuseStep 1537471 = 2306207) B2306207
theorem B14784079 : Blo 1213424 14784079 := bstep (se 1 (by rfl) ⟨11088059, by rfl⟩ : syracuseStep 14784079 = 22176119) B22176119
theorem B4609831 : Blo 1213424 4609831 := bstep (se 1 (by rfl) ⟨3457373, by rfl⟩ : syracuseStep 4609831 = 6914747) B6914747
theorem B2734415 : Blo 1213424 2734415 := bstep (se 1 (by rfl) ⟨2050811, by rfl⟩ : syracuseStep 2734415 = 4101623) B4101623
theorem B1366375 : Blo 1213424 1366375 := bstep (se 1 (by rfl) ⟨1024781, by rfl⟩ : syracuseStep 1366375 = 2049563) B2049563
theorem B16612607 : Blo 1213424 16612607 := bstep (se 1 (by rfl) ⟨12459455, by rfl⟩ : syracuseStep 16612607 = 24918911) B24918911
theorem B269360579 : Blo 1213424 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B3890879 : Blo 1213424 3890879 := bstep (se 1 (by rfl) ⟨2918159, by rfl⟩ : syracuseStep 3890879 = 5836319) B5836319
theorem B359204219 : Blo 1213424 359204219 := bstep (se 1 (by rfl) ⟨269403164, by rfl⟩ : syracuseStep 359204219 = 538806329) B538806329
theorem B1214311 : Blo 1213424 1214311 := bstep (se 1 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 1214311 = 1821467) B1821467
theorem B2049961 : Blo 1213424 2049961 := bstep (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) B1537471
theorem B1214567 : Blo 1213424 1214567 := bstep (se 1 (by rfl) ⟨910925, by rfl⟩ : syracuseStep 1214567 = 1821851) B1821851
theorem B19712105 : Blo 1213424 19712105 := bstep (se 2 (by rfl) ⟨7392039, by rfl⟩ : syracuseStep 19712105 = 14784079) B14784079
theorem B6146441 : Blo 1213424 6146441 := bstep (se 2 (by rfl) ⟨2304915, by rfl⟩ : syracuseStep 6146441 = 4609831) B4609831
theorem B1821833 : Blo 1213424 1821833 := bstep (se 2 (by rfl) ⟨683187, by rfl⟩ : syracuseStep 1821833 = 1366375) B1366375
theorem B718294877 : Blo 1213424 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B33230897 : Blo 1213424 33230897 := bstep (se 2 (by rfl) ⟨12461586, by rfl⟩ : syracuseStep 33230897 = 24923173) B24923173
theorem B1822943 : Blo 1213424 1822943 := bstep (se 1 (by rfl) ⟨1367207, by rfl⟩ : syracuseStep 1822943 = 2734415) B2734415
theorem B2593919 : Blo 1213424 2593919 := bstep (se 1 (by rfl) ⟨1945439, by rfl⟩ : syracuseStep 2593919 = 3890879) B3890879
theorem B4380151 : Blo 1213424 4380151 := bstep (se 1 (by rfl) ⟨3285113, by rfl⟩ : syracuseStep 4380151 = 6570227) B6570227
theorem B23336657 : Blo 1213424 23336657 := bstep (se 2 (by rfl) ⟨8751246, by rfl⟩ : syracuseStep 23336657 = 17502493) B17502493
theorem B9214559 : Blo 1213424 9214559 := bstep (se 1 (by rfl) ⟨6910919, by rfl⟩ : syracuseStep 9214559 = 13821839) B13821839
theorem B4496417 : Blo 1213424 4496417 := bstep (se 2 (by rfl) ⟨1686156, by rfl⟩ : syracuseStep 4496417 = 3372313) B3372313
theorem B5553289 : Blo 1213424 5553289 := bstep (se 2 (by rfl) ⟨2082483, by rfl⟩ : syracuseStep 5553289 = 4164967) B4164967
theorem B11075071 : Blo 1213424 11075071 := bstep (se 1 (by rfl) ⟨8306303, by rfl⟩ : syracuseStep 11075071 = 16612607) B16612607
theorem B1729279 : Blo 1213424 1729279 := bstep (se 1 (by rfl) ⟨1296959, by rfl⟩ : syracuseStep 1729279 = 2593919) B2593919
theorem B239469479 : Blo 1213424 239469479 := bstep (se 1 (by rfl) ⟨179602109, by rfl⟩ : syracuseStep 239469479 = 359204219) B359204219
theorem B15557771 : Blo 1213424 15557771 := bstep (se 1 (by rfl) ⟨11668328, by rfl⟩ : syracuseStep 15557771 = 23336657) B23336657
theorem B13141403 : Blo 1213424 13141403 := bstep (se 1 (by rfl) ⟨9856052, by rfl⟩ : syracuseStep 13141403 = 19712105) B19712105
theorem B4097627 : Blo 1213424 4097627 := bstep (se 1 (by rfl) ⟨3073220, by rfl⟩ : syracuseStep 4097627 = 6146441) B6146441
theorem B1214555 : Blo 1213424 1214555 := bstep (se 1 (by rfl) ⟨910916, by rfl⟩ : syracuseStep 1214555 = 1821833) B1821833
theorem B22153931 : Blo 1213424 22153931 := bstep (se 1 (by rfl) ⟨16615448, by rfl⟩ : syracuseStep 22153931 = 33230897) B33230897
theorem B1215295 : Blo 1213424 1215295 := bstep (se 1 (by rfl) ⟨911471, by rfl⟩ : syracuseStep 1215295 = 1822943) B1822943
theorem B14766761 : Blo 1213424 14766761 := bstep (se 2 (by rfl) ⟨5537535, by rfl⟩ : syracuseStep 14766761 = 11075071) B11075071
theorem B2733281 : Blo 1213424 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B7404385 : Blo 1213424 7404385 := bstep (se 2 (by rfl) ⟨2776644, by rfl⟩ : syracuseStep 7404385 = 5553289) B5553289
theorem B6143039 : Blo 1213424 6143039 := bstep (se 1 (by rfl) ⟨4607279, by rfl⟩ : syracuseStep 6143039 = 9214559) B9214559
theorem B5840201 : Blo 1213424 5840201 := bstep (se 2 (by rfl) ⟨2190075, by rfl⟩ : syracuseStep 5840201 = 4380151) B4380151
theorem B2997611 : Blo 1213424 2997611 := bstep (se 1 (by rfl) ⟨2248208, by rfl⟩ : syracuseStep 2997611 = 4496417) B4496417
theorem B478863251 : Blo 1213424 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B159646319 : Blo 1213424 159646319 := bstep (se 1 (by rfl) ⟨119734739, by rfl⟩ : syracuseStep 159646319 = 239469479) B239469479
theorem B10371847 : Blo 1213424 10371847 := bstep (se 1 (by rfl) ⟨7778885, by rfl⟩ : syracuseStep 10371847 = 15557771) B15557771
theorem B15573869 : Blo 1213424 15573869 := bstep (se 3 (by rfl) ⟨2920100, by rfl⟩ : syracuseStep 15573869 = 5840201) B5840201
theorem B9872513 : Blo 1213424 9872513 := bstep (se 2 (by rfl) ⟨3702192, by rfl⟩ : syracuseStep 9872513 = 7404385) B7404385
theorem B1822187 : Blo 1213424 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B8760935 : Blo 1213424 8760935 := bstep (se 1 (by rfl) ⟨6570701, by rfl⟩ : syracuseStep 8760935 = 13141403) B13141403
theorem B2731751 : Blo 1213424 2731751 := bstep (se 1 (by rfl) ⟨2048813, by rfl⟩ : syracuseStep 2731751 = 4097627) B4097627
theorem B9844507 : Blo 1213424 9844507 := bstep (se 1 (by rfl) ⟨7383380, by rfl⟩ : syracuseStep 9844507 = 14766761) B14766761
theorem B9222821 : Blo 1213424 9222821 := bstep (se 4 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 9222821 = 1729279) B1729279
theorem B14769287 : Blo 1213424 14769287 := bstep (se 1 (by rfl) ⟨11076965, by rfl⟩ : syracuseStep 14769287 = 22153931) B22153931
theorem B4095359 : Blo 1213424 4095359 := bstep (se 1 (by rfl) ⟨3071519, by rfl⟩ : syracuseStep 4095359 = 6143039) B6143039
theorem B1998407 : Blo 1213424 1998407 := bstep (se 1 (by rfl) ⟨1498805, by rfl⟩ : syracuseStep 1998407 = 2997611) B2997611
theorem B319242167 : Blo 1213424 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B106430879 : Blo 1213424 106430879 := bstep (se 1 (by rfl) ⟨79823159, by rfl⟩ : syracuseStep 106430879 = 159646319) B159646319
theorem B13829129 : Blo 1213424 13829129 := bstep (se 2 (by rfl) ⟨5185923, by rfl⟩ : syracuseStep 13829129 = 10371847) B10371847
theorem B2730239 : Blo 1213424 2730239 := bstep (se 1 (by rfl) ⟨2047679, by rfl⟩ : syracuseStep 2730239 = 4095359) B4095359
theorem B1214791 : Blo 1213424 1214791 := bstep (se 1 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 1214791 = 1822187) B1822187
theorem B13126009 : Blo 1213424 13126009 := bstep (se 2 (by rfl) ⟨4922253, by rfl⟩ : syracuseStep 13126009 = 9844507) B9844507
theorem B1821167 : Blo 1213424 1821167 := bstep (se 1 (by rfl) ⟨1365875, by rfl⟩ : syracuseStep 1821167 = 2731751) B2731751
theorem B10382579 : Blo 1213424 10382579 := bstep (se 1 (by rfl) ⟨7786934, by rfl⟩ : syracuseStep 10382579 = 15573869) B15573869
theorem B6581675 : Blo 1213424 6581675 := bstep (se 1 (by rfl) ⟨4936256, by rfl⟩ : syracuseStep 6581675 = 9872513) B9872513
theorem B6148547 : Blo 1213424 6148547 := bstep (se 1 (by rfl) ⟨4611410, by rfl⟩ : syracuseStep 6148547 = 9222821) B9222821
theorem B1332271 : Blo 1213424 1332271 := bstep (se 1 (by rfl) ⟨999203, by rfl⟩ : syracuseStep 1332271 = 1998407) B1998407
theorem B9846191 : Blo 1213424 9846191 := bstep (se 1 (by rfl) ⟨7384643, by rfl⟩ : syracuseStep 9846191 = 14769287) B14769287
theorem B5840623 : Blo 1213424 5840623 := bstep (se 1 (by rfl) ⟨4380467, by rfl⟩ : syracuseStep 5840623 = 8760935) B8760935
theorem B212828111 : Blo 1213424 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B1820159 : Blo 1213424 1820159 := bstep (se 1 (by rfl) ⟨1365119, by rfl⟩ : syracuseStep 1820159 = 2730239) B2730239
theorem B1214111 : Blo 1213424 1214111 := bstep (se 1 (by rfl) ⟨910583, by rfl⟩ : syracuseStep 1214111 = 1821167) B1821167
theorem B6564127 : Blo 1213424 6564127 := bstep (se 1 (by rfl) ⟨4923095, by rfl⟩ : syracuseStep 6564127 = 9846191) B9846191
theorem B4099031 : Blo 1213424 4099031 := bstep (se 1 (by rfl) ⟨3074273, by rfl⟩ : syracuseStep 4099031 = 6148547) B6148547
theorem B17501345 : Blo 1213424 17501345 := bstep (se 2 (by rfl) ⟨6563004, by rfl⟩ : syracuseStep 17501345 = 13126009) B13126009
theorem B9219419 : Blo 1213424 9219419 := bstep (se 1 (by rfl) ⟨6914564, by rfl⟩ : syracuseStep 9219419 = 13829129) B13829129
theorem B283815677 : Blo 1213424 283815677 := bstep (se 3 (by rfl) ⟨53215439, by rfl⟩ : syracuseStep 283815677 = 106430879) B106430879
theorem B4387783 : Blo 1213424 4387783 := bstep (se 1 (by rfl) ⟨3290837, by rfl⟩ : syracuseStep 4387783 = 6581675) B6581675
theorem B7787497 : Blo 1213424 7787497 := bstep (se 2 (by rfl) ⟨2920311, by rfl⟩ : syracuseStep 7787497 = 5840623) B5840623
theorem B1776361 : Blo 1213424 1776361 := bstep (se 2 (by rfl) ⟨666135, by rfl⟩ : syracuseStep 1776361 = 1332271) B1332271
theorem B6921719 : Blo 1213424 6921719 := bstep (se 1 (by rfl) ⟨5191289, by rfl⟩ : syracuseStep 6921719 = 10382579) B10382579
theorem B141885407 : Blo 1213424 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B2368481 : Blo 1213424 2368481 := bstep (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) B1776361
theorem B1213439 : Blo 1213424 1213439 := bstep (se 1 (by rfl) ⟨910079, by rfl⟩ : syracuseStep 1213439 = 1820159) B1820159
theorem B5850377 : Blo 1213424 5850377 := bstep (se 2 (by rfl) ⟨2193891, by rfl⟩ : syracuseStep 5850377 = 4387783) B4387783
theorem B11667563 : Blo 1213424 11667563 := bstep (se 1 (by rfl) ⟨8750672, by rfl⟩ : syracuseStep 11667563 = 17501345) B17501345
theorem B6146279 : Blo 1213424 6146279 := bstep (se 1 (by rfl) ⟨4609709, by rfl⟩ : syracuseStep 6146279 = 9219419) B9219419
theorem B4614479 : Blo 1213424 4614479 := bstep (se 1 (by rfl) ⟨3460859, by rfl⟩ : syracuseStep 4614479 = 6921719) B6921719
theorem B8752169 : Blo 1213424 8752169 := bstep (se 2 (by rfl) ⟨3282063, by rfl⟩ : syracuseStep 8752169 = 6564127) B6564127
theorem B10383329 : Blo 1213424 10383329 := bstep (se 2 (by rfl) ⟨3893748, by rfl⟩ : syracuseStep 10383329 = 7787497) B7787497
theorem B2732687 : Blo 1213424 2732687 := bstep (se 1 (by rfl) ⟨2049515, by rfl⟩ : syracuseStep 2732687 = 4099031) B4099031
theorem B94590271 : Blo 1213424 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B189210451 : Blo 1213424 189210451 := bstep (se 1 (by rfl) ⟨141907838, by rfl⟩ : syracuseStep 189210451 = 283815677) B283815677
theorem B23339117 : Blo 1213424 23339117 := bstep (se 3 (by rfl) ⟨4376084, by rfl⟩ : syracuseStep 23339117 = 8752169) B8752169
theorem B3900251 : Blo 1213424 3900251 := bstep (se 1 (by rfl) ⟨2925188, by rfl⟩ : syracuseStep 3900251 = 5850377) B5850377
theorem B4097519 : Blo 1213424 4097519 := bstep (se 1 (by rfl) ⟨3073139, by rfl⟩ : syracuseStep 4097519 = 6146279) B6146279
theorem B1821791 : Blo 1213424 1821791 := bstep (se 1 (by rfl) ⟨1366343, by rfl⟩ : syracuseStep 1821791 = 2732687) B2732687
theorem B7778375 : Blo 1213424 7778375 := bstep (se 1 (by rfl) ⟨5833781, by rfl⟩ : syracuseStep 7778375 = 11667563) B11667563
theorem B3076319 : Blo 1213424 3076319 := bstep (se 1 (by rfl) ⟨2307239, by rfl⟩ : syracuseStep 3076319 = 4614479) B4614479
theorem B126120361 : Blo 1213424 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B25263797 : Blo 1213424 25263797 := bstep (se 5 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 25263797 = 2368481) B2368481
theorem B252280601 : Blo 1213424 252280601 := bstep (se 2 (by rfl) ⟨94605225, by rfl⟩ : syracuseStep 252280601 = 189210451) B189210451
theorem B6922219 : Blo 1213424 6922219 := bstep (se 1 (by rfl) ⟨5191664, by rfl⟩ : syracuseStep 6922219 = 10383329) B10383329
theorem B5185583 : Blo 1213424 5185583 := bstep (se 1 (by rfl) ⟨3889187, by rfl⟩ : syracuseStep 5185583 = 7778375) B7778375
theorem B1214527 : Blo 1213424 1214527 := bstep (se 1 (by rfl) ⟨910895, by rfl⟩ : syracuseStep 1214527 = 1821791) B1821791
theorem B15559411 : Blo 1213424 15559411 := bstep (se 1 (by rfl) ⟨11669558, by rfl⟩ : syracuseStep 15559411 = 23339117) B23339117
theorem B2050879 : Blo 1213424 2050879 := bstep (se 1 (by rfl) ⟨1538159, by rfl⟩ : syracuseStep 2050879 = 3076319) B3076319
theorem B168160481 : Blo 1213424 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B2600167 : Blo 1213424 2600167 := bstep (se 1 (by rfl) ⟨1950125, by rfl⟩ : syracuseStep 2600167 = 3900251) B3900251
theorem B2731679 : Blo 1213424 2731679 := bstep (se 1 (by rfl) ⟨2048759, by rfl⟩ : syracuseStep 2731679 = 4097519) B4097519
theorem B168187067 : Blo 1213424 168187067 := bstep (se 1 (by rfl) ⟨126140300, by rfl⟩ : syracuseStep 168187067 = 252280601) B252280601
theorem B9229625 : Blo 1213424 9229625 := bstep (se 2 (by rfl) ⟨3461109, by rfl⟩ : syracuseStep 9229625 = 6922219) B6922219
theorem B67370125 : Blo 1213424 67370125 := bstep (se 3 (by rfl) ⟨12631898, by rfl⟩ : syracuseStep 67370125 = 25263797) B25263797
theorem B3457055 : Blo 1213424 3457055 := bstep (se 1 (by rfl) ⟨2592791, by rfl⟩ : syracuseStep 3457055 = 5185583) B5185583
theorem B112124711 : Blo 1213424 112124711 := bstep (se 1 (by rfl) ⟨84093533, by rfl⟩ : syracuseStep 112124711 = 168187067) B168187067
theorem B6153083 : Blo 1213424 6153083 := bstep (se 1 (by rfl) ⟨4614812, by rfl⟩ : syracuseStep 6153083 = 9229625) B9229625
theorem B89826833 : Blo 1213424 89826833 := bstep (se 2 (by rfl) ⟨33685062, by rfl⟩ : syracuseStep 89826833 = 67370125) B67370125
theorem B3466889 : Blo 1213424 3466889 := bstep (se 2 (by rfl) ⟨1300083, by rfl⟩ : syracuseStep 3466889 = 2600167) B2600167
theorem B1821119 : Blo 1213424 1821119 := bstep (se 1 (by rfl) ⟨1365839, by rfl⟩ : syracuseStep 1821119 = 2731679) B2731679
theorem B20745881 : Blo 1213424 20745881 := bstep (se 2 (by rfl) ⟨7779705, by rfl⟩ : syracuseStep 20745881 = 15559411) B15559411
theorem B2734505 : Blo 1213424 2734505 := bstep (se 2 (by rfl) ⟨1025439, by rfl⟩ : syracuseStep 2734505 = 2050879) B2050879
theorem B112106987 : Blo 1213424 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B59884555 : Blo 1213424 59884555 := bstep (se 1 (by rfl) ⟨44913416, by rfl⟩ : syracuseStep 59884555 = 89826833) B89826833
theorem B2311259 : Blo 1213424 2311259 := bstep (se 1 (by rfl) ⟨1733444, by rfl⟩ : syracuseStep 2311259 = 3466889) B3466889
theorem B1214079 : Blo 1213424 1214079 := bstep (se 1 (by rfl) ⟨910559, by rfl⟩ : syracuseStep 1214079 = 1821119) B1821119
theorem B74737991 : Blo 1213424 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B13830587 : Blo 1213424 13830587 := bstep (se 1 (by rfl) ⟨10372940, by rfl⟩ : syracuseStep 13830587 = 20745881) B20745881
theorem B2304703 : Blo 1213424 2304703 := bstep (se 1 (by rfl) ⟨1728527, by rfl⟩ : syracuseStep 2304703 = 3457055) B3457055
theorem B1823003 : Blo 1213424 1823003 := bstep (se 1 (by rfl) ⟨1367252, by rfl⟩ : syracuseStep 1823003 = 2734505) B2734505
theorem B74749807 : Blo 1213424 74749807 := bstep (se 1 (by rfl) ⟨56062355, by rfl⟩ : syracuseStep 74749807 = 112124711) B112124711
theorem B4102055 : Blo 1213424 4102055 := bstep (se 1 (by rfl) ⟨3076541, by rfl⟩ : syracuseStep 4102055 = 6153083) B6153083
theorem B3072937 : Blo 1213424 3072937 := bstep (se 2 (by rfl) ⟨1152351, by rfl⟩ : syracuseStep 3072937 = 2304703) B2304703
theorem B49825327 : Blo 1213424 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B99666409 : Blo 1213424 99666409 := bstep (se 2 (by rfl) ⟨37374903, by rfl⟩ : syracuseStep 99666409 = 74749807) B74749807
theorem B1215335 : Blo 1213424 1215335 := bstep (se 1 (by rfl) ⟨911501, by rfl⟩ : syracuseStep 1215335 = 1823003) B1823003
theorem B24653429 : Blo 1213424 24653429 := bstep (se 5 (by rfl) ⟨1155629, by rfl⟩ : syracuseStep 24653429 = 2311259) B2311259
theorem B9220391 : Blo 1213424 9220391 := bstep (se 1 (by rfl) ⟨6915293, by rfl⟩ : syracuseStep 9220391 = 13830587) B13830587
theorem B2734703 : Blo 1213424 2734703 := bstep (se 1 (by rfl) ⟨2051027, by rfl⟩ : syracuseStep 2734703 = 4102055) B4102055
theorem B79846073 : Blo 1213424 79846073 := bstep (se 2 (by rfl) ⟨29942277, by rfl⟩ : syracuseStep 79846073 = 59884555) B59884555
theorem B4097249 : Blo 1213424 4097249 := bstep (se 2 (by rfl) ⟨1536468, by rfl⟩ : syracuseStep 4097249 = 3072937) B3072937
theorem B16435619 : Blo 1213424 16435619 := bstep (se 1 (by rfl) ⟨12326714, by rfl⟩ : syracuseStep 16435619 = 24653429) B24653429
theorem B6146927 : Blo 1213424 6146927 := bstep (se 1 (by rfl) ⟨4610195, by rfl⟩ : syracuseStep 6146927 = 9220391) B9220391
theorem B1823135 : Blo 1213424 1823135 := bstep (se 1 (by rfl) ⟨1367351, by rfl⟩ : syracuseStep 1823135 = 2734703) B2734703
theorem B66433769 : Blo 1213424 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B132888545 : Blo 1213424 132888545 := bstep (se 2 (by rfl) ⟨49833204, by rfl⟩ : syracuseStep 132888545 = 99666409) B99666409
theorem B53230715 : Blo 1213424 53230715 := bstep (se 1 (by rfl) ⟨39923036, by rfl⟩ : syracuseStep 53230715 = 79846073) B79846073
theorem B4097951 : Blo 1213424 4097951 := bstep (se 1 (by rfl) ⟨3073463, by rfl⟩ : syracuseStep 4097951 = 6146927) B6146927
theorem B1215423 : Blo 1213424 1215423 := bstep (se 1 (by rfl) ⟨911567, by rfl⟩ : syracuseStep 1215423 = 1823135) B1823135
theorem B44289179 : Blo 1213424 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B2731499 : Blo 1213424 2731499 := bstep (se 1 (by rfl) ⟨2048624, by rfl⟩ : syracuseStep 2731499 = 4097249) B4097249
theorem B88592363 : Blo 1213424 88592363 := bstep (se 1 (by rfl) ⟨66444272, by rfl⟩ : syracuseStep 88592363 = 132888545) B132888545
theorem B10957079 : Blo 1213424 10957079 := bstep (se 1 (by rfl) ⟨8217809, by rfl⟩ : syracuseStep 10957079 = 16435619) B16435619
theorem B35487143 : Blo 1213424 35487143 := bstep (se 1 (by rfl) ⟨26615357, by rfl⟩ : syracuseStep 35487143 = 53230715) B53230715
theorem B29526119 : Blo 1213424 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B1820999 : Blo 1213424 1820999 := bstep (se 1 (by rfl) ⟨1365749, by rfl⟩ : syracuseStep 1820999 = 2731499) B2731499
theorem B2731967 : Blo 1213424 2731967 := bstep (se 1 (by rfl) ⟨2048975, by rfl⟩ : syracuseStep 2731967 = 4097951) B4097951
theorem B59061575 : Blo 1213424 59061575 := bstep (se 1 (by rfl) ⟨44296181, by rfl⟩ : syracuseStep 59061575 = 88592363) B88592363
theorem B29218877 : Blo 1213424 29218877 := bstep (se 3 (by rfl) ⟨5478539, by rfl⟩ : syracuseStep 29218877 = 10957079) B10957079
theorem B23658095 : Blo 1213424 23658095 := bstep (se 1 (by rfl) ⟨17743571, by rfl⟩ : syracuseStep 23658095 = 35487143) B35487143
theorem B1213999 : Blo 1213424 1213999 := bstep (se 1 (by rfl) ⟨910499, by rfl⟩ : syracuseStep 1213999 = 1820999) B1820999
theorem B63088253 : Blo 1213424 63088253 := bstep (se 3 (by rfl) ⟨11829047, by rfl⟩ : syracuseStep 63088253 = 23658095) B23658095
theorem B1821311 : Blo 1213424 1821311 := bstep (se 1 (by rfl) ⟨1365983, by rfl⟩ : syracuseStep 1821311 = 2731967) B2731967
theorem B39374383 : Blo 1213424 39374383 := bstep (se 1 (by rfl) ⟨29530787, by rfl⟩ : syracuseStep 39374383 = 59061575) B59061575
theorem B19479251 : Blo 1213424 19479251 := bstep (se 1 (by rfl) ⟨14609438, by rfl⟩ : syracuseStep 19479251 = 29218877) B29218877
theorem B19684079 : Blo 1213424 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B42058835 : Blo 1213424 42058835 := bstep (se 1 (by rfl) ⟨31544126, by rfl⟩ : syracuseStep 42058835 = 63088253) B63088253
theorem B1214207 : Blo 1213424 1214207 := bstep (se 1 (by rfl) ⟨910655, by rfl⟩ : syracuseStep 1214207 = 1821311) B1821311
theorem B12986167 : Blo 1213424 12986167 := bstep (se 1 (by rfl) ⟨9739625, by rfl⟩ : syracuseStep 12986167 = 19479251) B19479251
theorem B52499177 : Blo 1213424 52499177 := bstep (se 2 (by rfl) ⟨19687191, by rfl⟩ : syracuseStep 52499177 = 39374383) B39374383
theorem B13122719 : Blo 1213424 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B34999451 : Blo 1213424 34999451 := bstep (se 1 (by rfl) ⟨26249588, by rfl⟩ : syracuseStep 34999451 = 52499177) B52499177
theorem B17314889 : Blo 1213424 17314889 := bstep (se 2 (by rfl) ⟨6493083, by rfl⟩ : syracuseStep 17314889 = 12986167) B12986167
theorem B28039223 : Blo 1213424 28039223 := bstep (se 1 (by rfl) ⟨21029417, by rfl⟩ : syracuseStep 28039223 = 42058835) B42058835
theorem B8748479 : Blo 1213424 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B23332967 : Blo 1213424 23332967 := bstep (se 1 (by rfl) ⟨17499725, by rfl⟩ : syracuseStep 23332967 = 34999451) B34999451
theorem B74771261 : Blo 1213424 74771261 := bstep (se 3 (by rfl) ⟨14019611, by rfl⟩ : syracuseStep 74771261 = 28039223) B28039223
theorem B46173037 : Blo 1213424 46173037 := bstep (se 3 (by rfl) ⟨8657444, by rfl⟩ : syracuseStep 46173037 = 17314889) B17314889
theorem B5832319 : Blo 1213424 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B61564049 : Blo 1213424 61564049 := bstep (se 2 (by rfl) ⟨23086518, by rfl⟩ : syracuseStep 61564049 = 46173037) B46173037
theorem B7776425 : Blo 1213424 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B15555311 : Blo 1213424 15555311 := bstep (se 1 (by rfl) ⟨11666483, by rfl⟩ : syracuseStep 15555311 = 23332967) B23332967
theorem B49847507 : Blo 1213424 49847507 := bstep (se 1 (by rfl) ⟨37385630, by rfl⟩ : syracuseStep 49847507 = 74771261) B74771261
theorem B41042699 : Blo 1213424 41042699 := bstep (se 1 (by rfl) ⟨30782024, by rfl⟩ : syracuseStep 41042699 = 61564049) B61564049
theorem B20737133 : Blo 1213424 20737133 := bstep (se 3 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 20737133 = 7776425) B7776425
theorem B33231671 : Blo 1213424 33231671 := bstep (se 1 (by rfl) ⟨24923753, by rfl⟩ : syracuseStep 33231671 = 49847507) B49847507
theorem B10370207 : Blo 1213424 10370207 := bstep (se 1 (by rfl) ⟨7777655, by rfl⟩ : syracuseStep 10370207 = 15555311) B15555311
theorem B27361799 : Blo 1213424 27361799 := bstep (se 1 (by rfl) ⟨20521349, by rfl⟩ : syracuseStep 27361799 = 41042699) B41042699
theorem B22154447 : Blo 1213424 22154447 := bstep (se 1 (by rfl) ⟨16615835, by rfl⟩ : syracuseStep 22154447 = 33231671) B33231671
theorem B13824755 : Blo 1213424 13824755 := bstep (se 1 (by rfl) ⟨10368566, by rfl⟩ : syracuseStep 13824755 = 20737133) B20737133
theorem B6913471 : Blo 1213424 6913471 := bstep (se 1 (by rfl) ⟨5185103, by rfl⟩ : syracuseStep 6913471 = 10370207) B10370207
theorem B9216503 : Blo 1213424 9216503 := bstep (se 1 (by rfl) ⟨6912377, by rfl⟩ : syracuseStep 9216503 = 13824755) B13824755
theorem B9217961 : Blo 1213424 9217961 := bstep (se 2 (by rfl) ⟨3456735, by rfl⟩ : syracuseStep 9217961 = 6913471) B6913471
theorem B18241199 : Blo 1213424 18241199 := bstep (se 1 (by rfl) ⟨13680899, by rfl⟩ : syracuseStep 18241199 = 27361799) B27361799
theorem B14769631 : Blo 1213424 14769631 := bstep (se 1 (by rfl) ⟨11077223, by rfl⟩ : syracuseStep 14769631 = 22154447) B22154447
theorem B6144335 : Blo 1213424 6144335 := bstep (se 1 (by rfl) ⟨4608251, by rfl⟩ : syracuseStep 6144335 = 9216503) B9216503
theorem B6145307 : Blo 1213424 6145307 := bstep (se 1 (by rfl) ⟨4608980, by rfl⟩ : syracuseStep 6145307 = 9217961) B9217961
theorem B12160799 : Blo 1213424 12160799 := bstep (se 1 (by rfl) ⟨9120599, by rfl⟩ : syracuseStep 12160799 = 18241199) B18241199
theorem B78771365 : Blo 1213424 78771365 := bstep (se 4 (by rfl) ⟨7384815, by rfl⟩ : syracuseStep 78771365 = 14769631) B14769631
theorem B4096223 : Blo 1213424 4096223 := bstep (se 1 (by rfl) ⟨3072167, by rfl⟩ : syracuseStep 4096223 = 6144335) B6144335
theorem B4096871 : Blo 1213424 4096871 := bstep (se 1 (by rfl) ⟨3072653, by rfl⟩ : syracuseStep 4096871 = 6145307) B6145307
theorem B52514243 : Blo 1213424 52514243 := bstep (se 1 (by rfl) ⟨39385682, by rfl⟩ : syracuseStep 52514243 = 78771365) B78771365
theorem B8107199 : Blo 1213424 8107199 := bstep (se 1 (by rfl) ⟨6080399, by rfl⟩ : syracuseStep 8107199 = 12160799) B12160799
theorem B2730815 : Blo 1213424 2730815 := bstep (se 1 (by rfl) ⟨2048111, by rfl⟩ : syracuseStep 2730815 = 4096223) B4096223
theorem B2731247 : Blo 1213424 2731247 := bstep (se 1 (by rfl) ⟨2048435, by rfl⟩ : syracuseStep 2731247 = 4096871) B4096871
theorem B35009495 : Blo 1213424 35009495 := bstep (se 1 (by rfl) ⟨26257121, by rfl⟩ : syracuseStep 35009495 = 52514243) B52514243
theorem B5404799 : Blo 1213424 5404799 := bstep (se 1 (by rfl) ⟨4053599, by rfl⟩ : syracuseStep 5404799 = 8107199) B8107199
theorem B23339663 : Blo 1213424 23339663 := bstep (se 1 (by rfl) ⟨17504747, by rfl⟩ : syracuseStep 23339663 = 35009495) B35009495
theorem B1820543 : Blo 1213424 1820543 := bstep (se 1 (by rfl) ⟨1365407, by rfl⟩ : syracuseStep 1820543 = 2730815) B2730815
theorem B1820831 : Blo 1213424 1820831 := bstep (se 1 (by rfl) ⟨1365623, by rfl⟩ : syracuseStep 1820831 = 2731247) B2731247
theorem B3603199 : Blo 1213424 3603199 := bstep (se 1 (by rfl) ⟨2702399, by rfl⟩ : syracuseStep 3603199 = 5404799) B5404799
theorem B1213695 : Blo 1213424 1213695 := bstep (se 1 (by rfl) ⟨910271, by rfl⟩ : syracuseStep 1213695 = 1820543) B1820543
theorem B1213887 : Blo 1213424 1213887 := bstep (se 1 (by rfl) ⟨910415, by rfl⟩ : syracuseStep 1213887 = 1820831) B1820831
theorem B15559775 : Blo 1213424 15559775 := bstep (se 1 (by rfl) ⟨11669831, by rfl⟩ : syracuseStep 15559775 = 23339663) B23339663
theorem B4804265 : Blo 1213424 4804265 := bstep (se 2 (by rfl) ⟨1801599, by rfl⟩ : syracuseStep 4804265 = 3603199) B3603199
theorem B10373183 : Blo 1213424 10373183 := bstep (se 1 (by rfl) ⟨7779887, by rfl⟩ : syracuseStep 10373183 = 15559775) B15559775
theorem B3202843 : Blo 1213424 3202843 := bstep (se 1 (by rfl) ⟨2402132, by rfl⟩ : syracuseStep 3202843 = 4804265) B4804265
theorem B6915455 : Blo 1213424 6915455 := bstep (se 1 (by rfl) ⟨5186591, by rfl⟩ : syracuseStep 6915455 = 10373183) B10373183
theorem B4270457 : Blo 1213424 4270457 := bstep (se 2 (by rfl) ⟨1601421, by rfl⟩ : syracuseStep 4270457 = 3202843) B3202843
theorem B2846971 : Blo 1213424 2846971 := bstep (se 1 (by rfl) ⟨2135228, by rfl⟩ : syracuseStep 2846971 = 4270457) B4270457
theorem B4610303 : Blo 1213424 4610303 := bstep (se 1 (by rfl) ⟨3457727, by rfl⟩ : syracuseStep 4610303 = 6915455) B6915455
theorem B3073535 : Blo 1213424 3073535 := bstep (se 1 (by rfl) ⟨2305151, by rfl⟩ : syracuseStep 3073535 = 4610303) B4610303
theorem B15183845 : Blo 1213424 15183845 := bstep (se 4 (by rfl) ⟨1423485, by rfl⟩ : syracuseStep 15183845 = 2846971) B2846971
theorem B2049023 : Blo 1213424 2049023 := bstep (se 1 (by rfl) ⟨1536767, by rfl⟩ : syracuseStep 2049023 = 3073535) B3073535
theorem B10122563 : Blo 1213424 10122563 := bstep (se 1 (by rfl) ⟨7591922, by rfl⟩ : syracuseStep 10122563 = 15183845) B15183845
theorem B26993501 : Blo 1213424 26993501 := bstep (se 3 (by rfl) ⟨5061281, by rfl⟩ : syracuseStep 26993501 = 10122563) B10122563
theorem B1366015 : Blo 1213424 1366015 := bstep (se 1 (by rfl) ⟨1024511, by rfl⟩ : syracuseStep 1366015 = 2049023) B2049023
theorem B1821353 : Blo 1213424 1821353 := bstep (se 2 (by rfl) ⟨683007, by rfl⟩ : syracuseStep 1821353 = 1366015) B1366015
theorem B17995667 : Blo 1213424 17995667 := bstep (se 1 (by rfl) ⟨13496750, by rfl⟩ : syracuseStep 17995667 = 26993501) B26993501
theorem B1214235 : Blo 1213424 1214235 := bstep (se 1 (by rfl) ⟨910676, by rfl⟩ : syracuseStep 1214235 = 1821353) B1821353
theorem B47988445 : Blo 1213424 47988445 := bstep (se 3 (by rfl) ⟨8997833, by rfl⟩ : syracuseStep 47988445 = 17995667) B17995667
theorem B63984593 : Blo 1213424 63984593 := bstep (se 2 (by rfl) ⟨23994222, by rfl⟩ : syracuseStep 63984593 = 47988445) B47988445
theorem B42656395 : Blo 1213424 42656395 := bstep (se 1 (by rfl) ⟨31992296, by rfl⟩ : syracuseStep 42656395 = 63984593) B63984593
theorem B56875193 : Blo 1213424 56875193 := bstep (se 2 (by rfl) ⟨21328197, by rfl⟩ : syracuseStep 56875193 = 42656395) B42656395
theorem B37916795 : Blo 1213424 37916795 := bstep (se 1 (by rfl) ⟨28437596, by rfl⟩ : syracuseStep 37916795 = 56875193) B56875193
theorem B101111453 : Blo 1213424 101111453 := bstep (se 3 (by rfl) ⟨18958397, by rfl⟩ : syracuseStep 101111453 = 37916795) B37916795
theorem B67407635 : Blo 1213424 67407635 := bstep (se 1 (by rfl) ⟨50555726, by rfl⟩ : syracuseStep 67407635 = 101111453) B101111453
theorem B44938423 : Blo 1213424 44938423 := bstep (se 1 (by rfl) ⟨33703817, by rfl⟩ : syracuseStep 44938423 = 67407635) B67407635
theorem B59917897 : Blo 1213424 59917897 := bstep (se 2 (by rfl) ⟨22469211, by rfl⟩ : syracuseStep 59917897 = 44938423) B44938423
theorem B319562117 : Blo 1213424 319562117 := bstep (se 4 (by rfl) ⟨29958948, by rfl⟩ : syracuseStep 319562117 = 59917897) B59917897
theorem B213041411 : Blo 1213424 213041411 := bstep (se 1 (by rfl) ⟨159781058, by rfl⟩ : syracuseStep 213041411 = 319562117) B319562117
theorem B142027607 : Blo 1213424 142027607 := bstep (se 1 (by rfl) ⟨106520705, by rfl⟩ : syracuseStep 142027607 = 213041411) B213041411
theorem B94685071 : Blo 1213424 94685071 := bstep (se 1 (by rfl) ⟨71013803, by rfl⟩ : syracuseStep 94685071 = 142027607) B142027607
theorem B126246761 : Blo 1213424 126246761 := bstep (se 2 (by rfl) ⟨47342535, by rfl⟩ : syracuseStep 126246761 = 94685071) B94685071
theorem B84164507 : Blo 1213424 84164507 := bstep (se 1 (by rfl) ⟨63123380, by rfl⟩ : syracuseStep 84164507 = 126246761) B126246761
theorem B56109671 : Blo 1213424 56109671 := bstep (se 1 (by rfl) ⟨42082253, by rfl⟩ : syracuseStep 56109671 = 84164507) B84164507
theorem B37406447 : Blo 1213424 37406447 := bstep (se 1 (by rfl) ⟨28054835, by rfl⟩ : syracuseStep 37406447 = 56109671) B56109671
theorem B24937631 : Blo 1213424 24937631 := bstep (se 1 (by rfl) ⟨18703223, by rfl⟩ : syracuseStep 24937631 = 37406447) B37406447
theorem B16625087 : Blo 1213424 16625087 := bstep (se 1 (by rfl) ⟨12468815, by rfl⟩ : syracuseStep 16625087 = 24937631) B24937631
theorem B11083391 : Blo 1213424 11083391 := bstep (se 1 (by rfl) ⟨8312543, by rfl⟩ : syracuseStep 11083391 = 16625087) B16625087
theorem B7388927 : Blo 1213424 7388927 := bstep (se 1 (by rfl) ⟨5541695, by rfl⟩ : syracuseStep 7388927 = 11083391) B11083391
theorem B4925951 : Blo 1213424 4925951 := bstep (se 1 (by rfl) ⟨3694463, by rfl⟩ : syracuseStep 4925951 = 7388927) B7388927
theorem B3283967 : Blo 1213424 3283967 := bstep (se 1 (by rfl) ⟨2462975, by rfl⟩ : syracuseStep 3283967 = 4925951) B4925951
theorem B2189311 : Blo 1213424 2189311 := bstep (se 1 (by rfl) ⟨1641983, by rfl⟩ : syracuseStep 2189311 = 3283967) B3283967
theorem B11676325 : Blo 1213424 11676325 := bstep (se 4 (by rfl) ⟨1094655, by rfl⟩ : syracuseStep 11676325 = 2189311) B2189311
theorem B15568433 : Blo 1213424 15568433 := bstep (se 2 (by rfl) ⟨5838162, by rfl⟩ : syracuseStep 15568433 = 11676325) B11676325
theorem B10378955 : Blo 1213424 10378955 := bstep (se 1 (by rfl) ⟨7784216, by rfl⟩ : syracuseStep 10378955 = 15568433) B15568433
theorem B6919303 : Blo 1213424 6919303 := bstep (se 1 (by rfl) ⟨5189477, by rfl⟩ : syracuseStep 6919303 = 10378955) B10378955
theorem B9225737 : Blo 1213424 9225737 := bstep (se 2 (by rfl) ⟨3459651, by rfl⟩ : syracuseStep 9225737 = 6919303) B6919303
theorem B6150491 : Blo 1213424 6150491 := bstep (se 1 (by rfl) ⟨4612868, by rfl⟩ : syracuseStep 6150491 = 9225737) B9225737
theorem B4100327 : Blo 1213424 4100327 := bstep (se 1 (by rfl) ⟨3075245, by rfl⟩ : syracuseStep 4100327 = 6150491) B6150491
theorem B2733551 : Blo 1213424 2733551 := bstep (se 1 (by rfl) ⟨2050163, by rfl⟩ : syracuseStep 2733551 = 4100327) B4100327
theorem B1822367 : Blo 1213424 1822367 := bstep (se 1 (by rfl) ⟨1366775, by rfl⟩ : syracuseStep 1822367 = 2733551) B2733551
theorem B1214911 : Blo 1213424 1214911 := bstep (se 1 (by rfl) ⟨911183, by rfl⟩ : syracuseStep 1214911 = 1822367) B1822367

theorem C0 (j : ℕ) (h1 : 303356 ≤ j) (h2 : j ≤ 303855) : Blo 1213424 (4 * j + 3) := by
  interval_cases j
  · exact B1213427
  · exact B1213431
  · exact B1213435
  · exact B1213439
  · exact B1213443
  · exact B1213447
  · exact B1213451
  · exact B1213455
  · exact B1213459
  · exact B1213463
  · exact B1213467
  · exact B1213471
  · exact B1213475
  · exact B1213479
  · exact B1213483
  · exact B1213487
  · exact B1213491
  · exact B1213495
  · exact B1213499
  · exact B1213503
  · exact B1213507
  · exact B1213511
  · exact B1213515
  · exact B1213519
  · exact B1213523
  · exact B1213527
  · exact B1213531
  · exact B1213535
  · exact B1213539
  · exact B1213543
  · exact B1213547
  · exact B1213551
  · exact B1213555
  · exact B1213559
  · exact B1213563
  · exact B1213567
  · exact B1213571
  · exact B1213575
  · exact B1213579
  · exact B1213583
  · exact B1213587
  · exact B1213591
  · exact B1213595
  · exact B1213599
  · exact B1213603
  · exact B1213607
  · exact B1213611
  · exact B1213615
  · exact B1213619
  · exact B1213623
  · exact B1213627
  · exact B1213631
  · exact B1213635
  · exact B1213639
  · exact B1213643
  · exact B1213647
  · exact B1213651
  · exact B1213655
  · exact B1213659
  · exact B1213663
  · exact B1213667
  · exact B1213671
  · exact B1213675
  · exact B1213679
  · exact B1213683
  · exact B1213687
  · exact B1213691
  · exact B1213695
  · exact B1213699
  · exact B1213703
  · exact B1213707
  · exact B1213711
  · exact B1213715
  · exact B1213719
  · exact B1213723
  · exact B1213727
  · exact B1213731
  · exact B1213735
  · exact B1213739
  · exact B1213743
  · exact B1213747
  · exact B1213751
  · exact B1213755
  · exact B1213759
  · exact B1213763
  · exact B1213767
  · exact B1213771
  · exact B1213775
  · exact B1213779
  · exact B1213783
  · exact B1213787
  · exact B1213791
  · exact B1213795
  · exact B1213799
  · exact B1213803
  · exact B1213807
  · exact B1213811
  · exact B1213815
  · exact B1213819
  · exact B1213823
  · exact B1213827
  · exact B1213831
  · exact B1213835
  · exact B1213839
  · exact B1213843
  · exact B1213847
  · exact B1213851
  · exact B1213855
  · exact B1213859
  · exact B1213863
  · exact B1213867
  · exact B1213871
  · exact B1213875
  · exact B1213879
  · exact B1213883
  · exact B1213887
  · exact B1213891
  · exact B1213895
  · exact B1213899
  · exact B1213903
  · exact B1213907
  · exact B1213911
  · exact B1213915
  · exact B1213919
  · exact B1213923
  · exact B1213927
  · exact B1213931
  · exact B1213935
  · exact B1213939
  · exact B1213943
  · exact B1213947
  · exact B1213951
  · exact B1213955
  · exact B1213959
  · exact B1213963
  · exact B1213967
  · exact B1213971
  · exact B1213975
  · exact B1213979
  · exact B1213983
  · exact B1213987
  · exact B1213991
  · exact B1213995
  · exact B1213999
  · exact B1214003
  · exact B1214007
  · exact B1214011
  · exact B1214015
  · exact B1214019
  · exact B1214023
  · exact B1214027
  · exact B1214031
  · exact B1214035
  · exact B1214039
  · exact B1214043
  · exact B1214047
  · exact B1214051
  · exact B1214055
  · exact B1214059
  · exact B1214063
  · exact B1214067
  · exact B1214071
  · exact B1214075
  · exact B1214079
  · exact B1214083
  · exact B1214087
  · exact B1214091
  · exact B1214095
  · exact B1214099
  · exact B1214103
  · exact B1214107
  · exact B1214111
  · exact B1214115
  · exact B1214119
  · exact B1214123
  · exact B1214127
  · exact B1214131
  · exact B1214135
  · exact B1214139
  · exact B1214143
  · exact B1214147
  · exact B1214151
  · exact B1214155
  · exact B1214159
  · exact B1214163
  · exact B1214167
  · exact B1214171
  · exact B1214175
  · exact B1214179
  · exact B1214183
  · exact B1214187
  · exact B1214191
  · exact B1214195
  · exact B1214199
  · exact B1214203
  · exact B1214207
  · exact B1214211
  · exact B1214215
  · exact B1214219
  · exact B1214223
  · exact B1214227
  · exact B1214231
  · exact B1214235
  · exact B1214239
  · exact B1214243
  · exact B1214247
  · exact B1214251
  · exact B1214255
  · exact B1214259
  · exact B1214263
  · exact B1214267
  · exact B1214271
  · exact B1214275
  · exact B1214279
  · exact B1214283
  · exact B1214287
  · exact B1214291
  · exact B1214295
  · exact B1214299
  · exact B1214303
  · exact B1214307
  · exact B1214311
  · exact B1214315
  · exact B1214319
  · exact B1214323
  · exact B1214327
  · exact B1214331
  · exact B1214335
  · exact B1214339
  · exact B1214343
  · exact B1214347
  · exact B1214351
  · exact B1214355
  · exact B1214359
  · exact B1214363
  · exact B1214367
  · exact B1214371
  · exact B1214375
  · exact B1214379
  · exact B1214383
  · exact B1214387
  · exact B1214391
  · exact B1214395
  · exact B1214399
  · exact B1214403
  · exact B1214407
  · exact B1214411
  · exact B1214415
  · exact B1214419
  · exact B1214423
  · exact B1214427
  · exact B1214431
  · exact B1214435
  · exact B1214439
  · exact B1214443
  · exact B1214447
  · exact B1214451
  · exact B1214455
  · exact B1214459
  · exact B1214463
  · exact B1214467
  · exact B1214471
  · exact B1214475
  · exact B1214479
  · exact B1214483
  · exact B1214487
  · exact B1214491
  · exact B1214495
  · exact B1214499
  · exact B1214503
  · exact B1214507
  · exact B1214511
  · exact B1214515
  · exact B1214519
  · exact B1214523
  · exact B1214527
  · exact B1214531
  · exact B1214535
  · exact B1214539
  · exact B1214543
  · exact B1214547
  · exact B1214551
  · exact B1214555
  · exact B1214559
  · exact B1214563
  · exact B1214567
  · exact B1214571
  · exact B1214575
  · exact B1214579
  · exact B1214583
  · exact B1214587
  · exact B1214591
  · exact B1214595
  · exact B1214599
  · exact B1214603
  · exact B1214607
  · exact B1214611
  · exact B1214615
  · exact B1214619
  · exact B1214623
  · exact B1214627
  · exact B1214631
  · exact B1214635
  · exact B1214639
  · exact B1214643
  · exact B1214647
  · exact B1214651
  · exact B1214655
  · exact B1214659
  · exact B1214663
  · exact B1214667
  · exact B1214671
  · exact B1214675
  · exact B1214679
  · exact B1214683
  · exact B1214687
  · exact B1214691
  · exact B1214695
  · exact B1214699
  · exact B1214703
  · exact B1214707
  · exact B1214711
  · exact B1214715
  · exact B1214719
  · exact B1214723
  · exact B1214727
  · exact B1214731
  · exact B1214735
  · exact B1214739
  · exact B1214743
  · exact B1214747
  · exact B1214751
  · exact B1214755
  · exact B1214759
  · exact B1214763
  · exact B1214767
  · exact B1214771
  · exact B1214775
  · exact B1214779
  · exact B1214783
  · exact B1214787
  · exact B1214791
  · exact B1214795
  · exact B1214799
  · exact B1214803
  · exact B1214807
  · exact B1214811
  · exact B1214815
  · exact B1214819
  · exact B1214823
  · exact B1214827
  · exact B1214831
  · exact B1214835
  · exact B1214839
  · exact B1214843
  · exact B1214847
  · exact B1214851
  · exact B1214855
  · exact B1214859
  · exact B1214863
  · exact B1214867
  · exact B1214871
  · exact B1214875
  · exact B1214879
  · exact B1214883
  · exact B1214887
  · exact B1214891
  · exact B1214895
  · exact B1214899
  · exact B1214903
  · exact B1214907
  · exact B1214911
  · exact B1214915
  · exact B1214919
  · exact B1214923
  · exact B1214927
  · exact B1214931
  · exact B1214935
  · exact B1214939
  · exact B1214943
  · exact B1214947
  · exact B1214951
  · exact B1214955
  · exact B1214959
  · exact B1214963
  · exact B1214967
  · exact B1214971
  · exact B1214975
  · exact B1214979
  · exact B1214983
  · exact B1214987
  · exact B1214991
  · exact B1214995
  · exact B1214999
  · exact B1215003
  · exact B1215007
  · exact B1215011
  · exact B1215015
  · exact B1215019
  · exact B1215023
  · exact B1215027
  · exact B1215031
  · exact B1215035
  · exact B1215039
  · exact B1215043
  · exact B1215047
  · exact B1215051
  · exact B1215055
  · exact B1215059
  · exact B1215063
  · exact B1215067
  · exact B1215071
  · exact B1215075
  · exact B1215079
  · exact B1215083
  · exact B1215087
  · exact B1215091
  · exact B1215095
  · exact B1215099
  · exact B1215103
  · exact B1215107
  · exact B1215111
  · exact B1215115
  · exact B1215119
  · exact B1215123
  · exact B1215127
  · exact B1215131
  · exact B1215135
  · exact B1215139
  · exact B1215143
  · exact B1215147
  · exact B1215151
  · exact B1215155
  · exact B1215159
  · exact B1215163
  · exact B1215167
  · exact B1215171
  · exact B1215175
  · exact B1215179
  · exact B1215183
  · exact B1215187
  · exact B1215191
  · exact B1215195
  · exact B1215199
  · exact B1215203
  · exact B1215207
  · exact B1215211
  · exact B1215215
  · exact B1215219
  · exact B1215223
  · exact B1215227
  · exact B1215231
  · exact B1215235
  · exact B1215239
  · exact B1215243
  · exact B1215247
  · exact B1215251
  · exact B1215255
  · exact B1215259
  · exact B1215263
  · exact B1215267
  · exact B1215271
  · exact B1215275
  · exact B1215279
  · exact B1215283
  · exact B1215287
  · exact B1215291
  · exact B1215295
  · exact B1215299
  · exact B1215303
  · exact B1215307
  · exact B1215311
  · exact B1215315
  · exact B1215319
  · exact B1215323
  · exact B1215327
  · exact B1215331
  · exact B1215335
  · exact B1215339
  · exact B1215343
  · exact B1215347
  · exact B1215351
  · exact B1215355
  · exact B1215359
  · exact B1215363
  · exact B1215367
  · exact B1215371
  · exact B1215375
  · exact B1215379
  · exact B1215383
  · exact B1215387
  · exact B1215391
  · exact B1215395
  · exact B1215399
  · exact B1215403
  · exact B1215407
  · exact B1215411
  · exact B1215415
  · exact B1215419
  · exact B1215423

theorem solution (m : ℕ) (hlo : 1213424 ≤ m) (hhi : m ≤ 1215424) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 303356 ≤ j := by omega
    have hj2 : j ≤ 303855 := by omega
    have hb : Blo 1213424 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
