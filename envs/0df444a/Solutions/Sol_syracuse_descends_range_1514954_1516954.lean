-- Prove2me | solution 1 for syracuse_descends_range_1514954_1516954
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:15.984968+00:00
-- url     : https://prove2.me/submissions/635b71c0-dd66-460f-a198-22641ef01ddb

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


theorem B3457093 : Blo 1514954 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B4923461 : Blo 1514954 4923461 := bbase (se 4 (by rfl) ⟨461574, by rfl⟩ : syracuseStep 4923461 = 923149) (by norm_num)
theorem B1728697 : Blo 1514954 1728697 := bbase (se 2 (by rfl) ⟨648261, by rfl⟩ : syracuseStep 1728697 = 1296523) (by norm_num)
theorem B4735205 : Blo 1514954 4735205 := bbase (se 4 (by rfl) ⟨443925, by rfl⟩ : syracuseStep 4735205 = 887851) (by norm_num)
theorem B5759221 : Blo 1514954 5759221 := bbase (se 5 (by rfl) ⟨269963, by rfl⟩ : syracuseStep 5759221 = 539927) (by norm_num)
theorem B9716021 : Blo 1514954 9716021 := bbase (se 5 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 9716021 = 910877) (by norm_num)
theorem B1704325 : Blo 1514954 1704325 := bbase (se 4 (by rfl) ⟨159780, by rfl⟩ : syracuseStep 1704325 = 319561) (by norm_num)
theorem B19423637 : Blo 1514954 19423637 := bbase (se 6 (by rfl) ⟨455241, by rfl⟩ : syracuseStep 19423637 = 910483) (by norm_num)
theorem B1704361 : Blo 1514954 1704361 := bbase (se 2 (by rfl) ⟨639135, by rfl⟩ : syracuseStep 1704361 = 1278271) (by norm_num)
theorem B1704397 : Blo 1514954 1704397 := bbase (se 3 (by rfl) ⟨319574, by rfl⟩ : syracuseStep 1704397 = 639149) (by norm_num)
theorem B1704433 : Blo 1514954 1704433 := bbase (se 2 (by rfl) ⟨639162, by rfl⟩ : syracuseStep 1704433 = 1278325) (by norm_num)
theorem B8634869 : Blo 1514954 8634869 := bbase (se 5 (by rfl) ⟨404759, by rfl⟩ : syracuseStep 8634869 = 809519) (by norm_num)
theorem B1704469 : Blo 1514954 1704469 := bbase (se 6 (by rfl) ⟨39948, by rfl⟩ : syracuseStep 1704469 = 79897) (by norm_num)
theorem B5759525 : Blo 1514954 5759525 := bbase (se 4 (by rfl) ⟨539955, by rfl⟩ : syracuseStep 5759525 = 1079911) (by norm_num)
theorem B1704505 : Blo 1514954 1704505 := bbase (se 2 (by rfl) ⟨639189, by rfl⟩ : syracuseStep 1704505 = 1278379) (by norm_num)
theorem B1917533 : Blo 1514954 1917533 := bbase (se 3 (by rfl) ⟨359537, by rfl⟩ : syracuseStep 1917533 = 719075) (by norm_num)
theorem B1704541 : Blo 1514954 1704541 := bbase (se 3 (by rfl) ⟨319601, by rfl⟩ : syracuseStep 1704541 = 639203) (by norm_num)
theorem B3236453 : Blo 1514954 3236453 := bbase (se 4 (by rfl) ⟨303417, by rfl⟩ : syracuseStep 3236453 = 606835) (by norm_num)
theorem B1704577 : Blo 1514954 1704577 := bbase (se 2 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 1704577 = 1278433) (by norm_num)
theorem B6472325 : Blo 1514954 6472325 := bbase (se 4 (by rfl) ⟨606780, by rfl⟩ : syracuseStep 6472325 = 1213561) (by norm_num)
theorem B1917589 : Blo 1514954 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B1704613 : Blo 1514954 1704613 := bbase (se 4 (by rfl) ⟨159807, by rfl⟩ : syracuseStep 1704613 = 319615) (by norm_num)
theorem B2556589 : Blo 1514954 2556589 := bbase (se 3 (by rfl) ⟨479360, by rfl⟩ : syracuseStep 2556589 = 958721) (by norm_num)
theorem B1704649 : Blo 1514954 1704649 := bbase (se 2 (by rfl) ⟨639243, by rfl⟩ : syracuseStep 1704649 = 1278487) (by norm_num)
theorem B3236573 : Blo 1514954 3236573 := bbase (se 3 (by rfl) ⟨606857, by rfl⟩ : syracuseStep 3236573 = 1213715) (by norm_num)
theorem B2876141 : Blo 1514954 2876141 := bbase (se 3 (by rfl) ⟨539276, by rfl⟩ : syracuseStep 2876141 = 1078553) (by norm_num)
theorem B1704685 : Blo 1514954 1704685 := bbase (se 3 (by rfl) ⟨319628, by rfl⟩ : syracuseStep 1704685 = 639257) (by norm_num)
theorem B1917685 : Blo 1514954 1917685 := bbase (se 5 (by rfl) ⟨89891, by rfl⟩ : syracuseStep 1917685 = 179783) (by norm_num)
theorem B2556677 : Blo 1514954 2556677 := bbase (se 4 (by rfl) ⟨239688, by rfl⟩ : syracuseStep 2556677 = 479377) (by norm_num)
theorem B1704721 : Blo 1514954 1704721 := bbase (se 2 (by rfl) ⟨639270, by rfl⟩ : syracuseStep 1704721 = 1278541) (by norm_num)
theorem B7676693 : Blo 1514954 7676693 := bbase (se 6 (by rfl) ⟨179922, by rfl⟩ : syracuseStep 7676693 = 359845) (by norm_num)
theorem B3408677 : Blo 1514954 3408677 := bbase (se 4 (by rfl) ⟨319563, by rfl⟩ : syracuseStep 3408677 = 639127) (by norm_num)
theorem B1704757 : Blo 1514954 1704757 := bbase (se 5 (by rfl) ⟨79910, by rfl⟩ : syracuseStep 1704757 = 159821) (by norm_num)
theorem B1704793 : Blo 1514954 1704793 := bbase (se 2 (by rfl) ⟨639297, by rfl⟩ : syracuseStep 1704793 = 1278595) (by norm_num)
theorem B3408749 : Blo 1514954 3408749 := bbase (se 3 (by rfl) ⟨639140, by rfl⟩ : syracuseStep 3408749 = 1278281) (by norm_num)
theorem B2876285 : Blo 1514954 2876285 := bbase (se 3 (by rfl) ⟨539303, by rfl⟩ : syracuseStep 2876285 = 1078607) (by norm_num)
theorem B1704829 : Blo 1514954 1704829 := bbase (se 3 (by rfl) ⟨319655, by rfl⟩ : syracuseStep 1704829 = 639311) (by norm_num)
theorem B2556805 : Blo 1514954 2556805 := bbase (se 4 (by rfl) ⟨239700, by rfl⟩ : syracuseStep 2556805 = 479401) (by norm_num)
theorem B3834773 : Blo 1514954 3834773 := bbase (se 6 (by rfl) ⟨89877, by rfl⟩ : syracuseStep 3834773 = 179755) (by norm_num)
theorem B1917857 : Blo 1514954 1917857 := bbase (se 2 (by rfl) ⟨719196, by rfl⟩ : syracuseStep 1917857 = 1438393) (by norm_num)
theorem B1704865 : Blo 1514954 1704865 := bbase (se 2 (by rfl) ⟨639324, by rfl⟩ : syracuseStep 1704865 = 1278649) (by norm_num)
theorem B2048933 : Blo 1514954 2048933 := bbase (se 4 (by rfl) ⟨192087, by rfl⟩ : syracuseStep 2048933 = 384175) (by norm_num)
theorem B3408821 : Blo 1514954 3408821 := bbase (se 5 (by rfl) ⟨159788, by rfl⟩ : syracuseStep 3408821 = 319577) (by norm_num)
theorem B1704901 : Blo 1514954 1704901 := bbase (se 4 (by rfl) ⟨159834, by rfl⟩ : syracuseStep 1704901 = 319669) (by norm_num)
theorem B1917913 : Blo 1514954 1917913 := bbase (se 2 (by rfl) ⟨719217, by rfl⟩ : syracuseStep 1917913 = 1438435) (by norm_num)
theorem B2556893 : Blo 1514954 2556893 := bbase (se 3 (by rfl) ⟨479417, by rfl⟩ : syracuseStep 2556893 = 958835) (by norm_num)
theorem B1704937 : Blo 1514954 1704937 := bbase (se 2 (by rfl) ⟨639351, by rfl⟩ : syracuseStep 1704937 = 1278703) (by norm_num)
theorem B3408893 : Blo 1514954 3408893 := bbase (se 3 (by rfl) ⟨639167, by rfl⟩ : syracuseStep 3408893 = 1278335) (by norm_num)
theorem B1663997 : Blo 1514954 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B1704973 : Blo 1514954 1704973 := bbase (se 3 (by rfl) ⟨319682, by rfl⟩ : syracuseStep 1704973 = 639365) (by norm_num)
theorem B1705009 : Blo 1514954 1705009 := bbase (se 2 (by rfl) ⟨639378, by rfl⟩ : syracuseStep 1705009 = 1278757) (by norm_num)
theorem B1918009 : Blo 1514954 1918009 := bbase (se 2 (by rfl) ⟨719253, by rfl⟩ : syracuseStep 1918009 = 1438507) (by norm_num)
theorem B3408965 : Blo 1514954 3408965 := bbase (se 4 (by rfl) ⟨319590, by rfl⟩ : syracuseStep 3408965 = 639181) (by norm_num)
theorem B3834965 : Blo 1514954 3834965 := bbase (se 8 (by rfl) ⟨22470, by rfl⟩ : syracuseStep 3834965 = 44941) (by norm_num)
theorem B1705045 : Blo 1514954 1705045 := bbase (se 8 (by rfl) ⟨9990, by rfl⟩ : syracuseStep 1705045 = 19981) (by norm_num)
theorem B2557021 : Blo 1514954 2557021 := bbase (se 3 (by rfl) ⟨479441, by rfl⟩ : syracuseStep 2557021 = 958883) (by norm_num)
theorem B3458141 : Blo 1514954 3458141 := bbase (se 3 (by rfl) ⟨648401, by rfl⟩ : syracuseStep 3458141 = 1296803) (by norm_num)
theorem B1705081 : Blo 1514954 1705081 := bbase (se 2 (by rfl) ⟨639405, by rfl⟩ : syracuseStep 1705081 = 1278811) (by norm_num)
theorem B3409037 : Blo 1514954 3409037 := bbase (se 3 (by rfl) ⟨639194, by rfl⟩ : syracuseStep 3409037 = 1278389) (by norm_num)
theorem B3458189 : Blo 1514954 3458189 := bbase (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) (by norm_num)
theorem B6915221 : Blo 1514954 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B2876573 : Blo 1514954 2876573 := bbase (se 3 (by rfl) ⟨539357, by rfl⟩ : syracuseStep 2876573 = 1078715) (by norm_num)
theorem B1705117 : Blo 1514954 1705117 := bbase (se 3 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 1705117 = 639419) (by norm_num)
theorem B2557109 : Blo 1514954 2557109 := bbase (se 5 (by rfl) ⟨119864, by rfl⟩ : syracuseStep 2557109 = 239729) (by norm_num)
theorem B1705153 : Blo 1514954 1705153 := bbase (se 2 (by rfl) ⟨639432, by rfl⟩ : syracuseStep 1705153 = 1278865) (by norm_num)
theorem B3409109 : Blo 1514954 3409109 := bbase (se 7 (by rfl) ⟨39950, by rfl⟩ : syracuseStep 3409109 = 79901) (by norm_num)
theorem B1918181 : Blo 1514954 1918181 := bbase (se 4 (by rfl) ⟨179829, by rfl⟩ : syracuseStep 1918181 = 359659) (by norm_num)
theorem B1705189 : Blo 1514954 1705189 := bbase (se 4 (by rfl) ⟨159861, by rfl⟩ : syracuseStep 1705189 = 319723) (by norm_num)
theorem B1705225 : Blo 1514954 1705225 := bbase (se 2 (by rfl) ⟨639459, by rfl⟩ : syracuseStep 1705225 = 1278919) (by norm_num)
theorem B3409181 : Blo 1514954 3409181 := bbase (se 3 (by rfl) ⟨639221, by rfl⟩ : syracuseStep 3409181 = 1278443) (by norm_num)
theorem B1918237 : Blo 1514954 1918237 := bbase (se 3 (by rfl) ⟨359669, by rfl⟩ : syracuseStep 1918237 = 719339) (by norm_num)
theorem B1705261 : Blo 1514954 1705261 := bbase (se 3 (by rfl) ⟨319736, by rfl⟩ : syracuseStep 1705261 = 639473) (by norm_num)
theorem B2876725 : Blo 1514954 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B2557237 : Blo 1514954 2557237 := bbase (se 5 (by rfl) ⟨119870, by rfl⟩ : syracuseStep 2557237 = 239741) (by norm_num)
theorem B1705297 : Blo 1514954 1705297 := bbase (se 2 (by rfl) ⟨639486, by rfl⟩ : syracuseStep 1705297 = 1278973) (by norm_num)
theorem B3237205 : Blo 1514954 3237205 := bbase (se 12 (by rfl) ⟨1185, by rfl⟩ : syracuseStep 3237205 = 2371) (by norm_num)
theorem B132916565 : Blo 1514954 132916565 := bbase (se 12 (by rfl) ⟨48675, by rfl⟩ : syracuseStep 132916565 = 97351) (by norm_num)
theorem B3409253 : Blo 1514954 3409253 := bbase (se 4 (by rfl) ⟨319617, by rfl⟩ : syracuseStep 3409253 = 639235) (by norm_num)
theorem B5113205 : Blo 1514954 5113205 := bbase (se 5 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 5113205 = 479363) (by norm_num)
theorem B7775605 : Blo 1514954 7775605 := bbase (se 5 (by rfl) ⟨364481, by rfl⟩ : syracuseStep 7775605 = 728963) (by norm_num)
theorem B1705333 : Blo 1514954 1705333 := bbase (se 5 (by rfl) ⟨79937, by rfl⟩ : syracuseStep 1705333 = 159875) (by norm_num)
theorem B1918333 : Blo 1514954 1918333 := bbase (se 3 (by rfl) ⟨359687, by rfl⟩ : syracuseStep 1918333 = 719375) (by norm_num)
theorem B4097413 : Blo 1514954 4097413 := bbase (se 4 (by rfl) ⟨384132, by rfl⟩ : syracuseStep 4097413 = 768265) (by norm_num)
theorem B2557325 : Blo 1514954 2557325 := bbase (se 3 (by rfl) ⟨479498, by rfl⟩ : syracuseStep 2557325 = 958997) (by norm_num)
theorem B1705369 : Blo 1514954 1705369 := bbase (se 2 (by rfl) ⟨639513, by rfl⟩ : syracuseStep 1705369 = 1279027) (by norm_num)
theorem B3835309 : Blo 1514954 3835309 := bbase (se 3 (by rfl) ⟨719120, by rfl⟩ : syracuseStep 3835309 = 1438241) (by norm_num)
theorem B3409325 : Blo 1514954 3409325 := bbase (se 3 (by rfl) ⟨639248, by rfl⟩ : syracuseStep 3409325 = 1278497) (by norm_num)
theorem B1705405 : Blo 1514954 1705405 := bbase (se 3 (by rfl) ⟨319763, by rfl⟩ : syracuseStep 1705405 = 639527) (by norm_num)
theorem B13125077 : Blo 1514954 13125077 := bbase (se 7 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 13125077 = 307619) (by norm_num)
theorem B2917853 : Blo 1514954 2917853 := bbase (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) (by norm_num)
theorem B1705441 : Blo 1514954 1705441 := bbase (se 2 (by rfl) ⟨639540, by rfl⟩ : syracuseStep 1705441 = 1279081) (by norm_num)
theorem B3409397 : Blo 1514954 3409397 := bbase (se 5 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 3409397 = 319631) (by norm_num)
theorem B1705477 : Blo 1514954 1705477 := bbase (se 4 (by rfl) ⟨159888, by rfl⟩ : syracuseStep 1705477 = 319777) (by norm_num)
theorem B2557453 : Blo 1514954 2557453 := bbase (se 3 (by rfl) ⟨479522, by rfl⟩ : syracuseStep 2557453 = 959045) (by norm_num)
theorem B3835421 : Blo 1514954 3835421 := bbase (se 3 (by rfl) ⟨719141, by rfl⟩ : syracuseStep 3835421 = 1438283) (by norm_num)
theorem B1918505 : Blo 1514954 1918505 := bbase (se 2 (by rfl) ⟨719439, by rfl⟩ : syracuseStep 1918505 = 1438879) (by norm_num)
theorem B1705513 : Blo 1514954 1705513 := bbase (se 2 (by rfl) ⟨639567, by rfl⟩ : syracuseStep 1705513 = 1279135) (by norm_num)
theorem B3409469 : Blo 1514954 3409469 := bbase (se 3 (by rfl) ⟨639275, by rfl⟩ : syracuseStep 3409469 = 1278551) (by norm_num)
theorem B1705549 : Blo 1514954 1705549 := bbase (se 3 (by rfl) ⟨319790, by rfl⟩ : syracuseStep 1705549 = 639581) (by norm_num)
theorem B1918561 : Blo 1514954 1918561 := bbase (se 2 (by rfl) ⟨719460, by rfl⟩ : syracuseStep 1918561 = 1438921) (by norm_num)
theorem B2877029 : Blo 1514954 2877029 := bbase (se 4 (by rfl) ⟨269721, by rfl⟩ : syracuseStep 2877029 = 539443) (by norm_num)
theorem B2557541 : Blo 1514954 2557541 := bbase (se 4 (by rfl) ⟨239769, by rfl⟩ : syracuseStep 2557541 = 479539) (by norm_num)
theorem B1705585 : Blo 1514954 1705585 := bbase (se 2 (by rfl) ⟨639594, by rfl⟩ : syracuseStep 1705585 = 1279189) (by norm_num)
theorem B3409541 : Blo 1514954 3409541 := bbase (se 4 (by rfl) ⟨319644, by rfl⟩ : syracuseStep 3409541 = 639289) (by norm_num)
theorem B21849749 : Blo 1514954 21849749 := bbase (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) (by norm_num)
theorem B1705621 : Blo 1514954 1705621 := bbase (se 6 (by rfl) ⟨39975, by rfl⟩ : syracuseStep 1705621 = 79951) (by norm_num)
theorem B1705657 : Blo 1514954 1705657 := bbase (se 2 (by rfl) ⟨639621, by rfl⟩ : syracuseStep 1705657 = 1279243) (by norm_num)
theorem B1918657 : Blo 1514954 1918657 := bbase (se 2 (by rfl) ⟨719496, by rfl⟩ : syracuseStep 1918657 = 1438993) (by norm_num)
theorem B3409613 : Blo 1514954 3409613 := bbase (se 3 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 3409613 = 1278605) (by norm_num)
theorem B3835613 : Blo 1514954 3835613 := bbase (se 3 (by rfl) ⟨719177, by rfl⟩ : syracuseStep 3835613 = 1438355) (by norm_num)
theorem B1705693 : Blo 1514954 1705693 := bbase (se 3 (by rfl) ⟨319817, by rfl⟩ : syracuseStep 1705693 = 639635) (by norm_num)
theorem B2557669 : Blo 1514954 2557669 := bbase (se 4 (by rfl) ⟨239781, by rfl⟩ : syracuseStep 2557669 = 479563) (by norm_num)
theorem B1705729 : Blo 1514954 1705729 := bbase (se 2 (by rfl) ⟨639648, by rfl⟩ : syracuseStep 1705729 = 1279297) (by norm_num)
theorem B3409685 : Blo 1514954 3409685 := bbase (se 6 (by rfl) ⟨79914, by rfl⟩ : syracuseStep 3409685 = 159829) (by norm_num)
theorem B5113637 : Blo 1514954 5113637 := bbase (se 4 (by rfl) ⟨479403, by rfl⟩ : syracuseStep 5113637 = 958807) (by norm_num)
theorem B1705765 : Blo 1514954 1705765 := bbase (se 4 (by rfl) ⟨159915, by rfl⟩ : syracuseStep 1705765 = 319831) (by norm_num)
theorem B2557757 : Blo 1514954 2557757 := bbase (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) (by norm_num)
theorem B1705801 : Blo 1514954 1705801 := bbase (se 2 (by rfl) ⟨639675, by rfl⟩ : syracuseStep 1705801 = 1279351) (by norm_num)
theorem B3409757 : Blo 1514954 3409757 := bbase (se 3 (by rfl) ⟨639329, by rfl⟩ : syracuseStep 3409757 = 1278659) (by norm_num)
theorem B1918829 : Blo 1514954 1918829 := bbase (se 3 (by rfl) ⟨359780, by rfl⟩ : syracuseStep 1918829 = 719561) (by norm_num)
theorem B1705837 : Blo 1514954 1705837 := bbase (se 3 (by rfl) ⟨319844, by rfl⟩ : syracuseStep 1705837 = 639689) (by norm_num)
theorem B1705873 : Blo 1514954 1705873 := bbase (se 2 (by rfl) ⟨639702, by rfl⟩ : syracuseStep 1705873 = 1279405) (by norm_num)
theorem B3409829 : Blo 1514954 3409829 := bbase (se 4 (by rfl) ⟨319671, by rfl⟩ : syracuseStep 3409829 = 639343) (by norm_num)
theorem B1918885 : Blo 1514954 1918885 := bbase (se 4 (by rfl) ⟨179895, by rfl⟩ : syracuseStep 1918885 = 359791) (by norm_num)
theorem B1705909 : Blo 1514954 1705909 := bbase (se 5 (by rfl) ⟨79964, by rfl⟩ : syracuseStep 1705909 = 159929) (by norm_num)
theorem B2557885 : Blo 1514954 2557885 := bbase (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) (by norm_num)
theorem B4319189 : Blo 1514954 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B1705945 : Blo 1514954 1705945 := bbase (se 2 (by rfl) ⟨639729, by rfl⟩ : syracuseStep 1705945 = 1279459) (by norm_num)
theorem B3409901 : Blo 1514954 3409901 := bbase (se 3 (by rfl) ⟨639356, by rfl⟩ : syracuseStep 3409901 = 1278713) (by norm_num)
theorem B1705981 : Blo 1514954 1705981 := bbase (se 3 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 1705981 = 639743) (by norm_num)
theorem B1918981 : Blo 1514954 1918981 := bbase (se 4 (by rfl) ⟨179904, by rfl⟩ : syracuseStep 1918981 = 359809) (by norm_num)
theorem B2557973 : Blo 1514954 2557973 := bbase (se 6 (by rfl) ⟨59952, by rfl⟩ : syracuseStep 2557973 = 119905) (by norm_num)
theorem B1706017 : Blo 1514954 1706017 := bbase (se 2 (by rfl) ⟨639756, by rfl⟩ : syracuseStep 1706017 = 1279513) (by norm_num)
theorem B2426917 : Blo 1514954 2426917 := bbase (se 4 (by rfl) ⟨227523, by rfl⟩ : syracuseStep 2426917 = 455047) (by norm_num)
theorem B7677989 : Blo 1514954 7677989 := bbase (se 4 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 7677989 = 1439623) (by norm_num)
theorem B2730037 : Blo 1514954 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B3835957 : Blo 1514954 3835957 := bbase (se 5 (by rfl) ⟨179810, by rfl⟩ : syracuseStep 3835957 = 359621) (by norm_num)
theorem B3409973 : Blo 1514954 3409973 := bbase (se 5 (by rfl) ⟨159842, by rfl⟩ : syracuseStep 3409973 = 319685) (by norm_num)
theorem B1640513 : Blo 1514954 1640513 := bbase (se 2 (by rfl) ⟨615192, by rfl⟩ : syracuseStep 1640513 = 1230385) (by norm_num)
theorem B4671557 : Blo 1514954 4671557 := bbase (se 4 (by rfl) ⟨437958, by rfl⟩ : syracuseStep 4671557 = 875917) (by norm_num)
theorem B1706053 : Blo 1514954 1706053 := bbase (se 4 (by rfl) ⟨159942, by rfl⟩ : syracuseStep 1706053 = 319885) (by norm_num)
theorem B1820765 : Blo 1514954 1820765 := bbase (se 3 (by rfl) ⟨341393, by rfl⟩ : syracuseStep 1820765 = 682787) (by norm_num)
theorem B1706089 : Blo 1514954 1706089 := bbase (se 2 (by rfl) ⟨639783, by rfl⟩ : syracuseStep 1706089 = 1279567) (by norm_num)
theorem B3410045 : Blo 1514954 3410045 := bbase (se 3 (by rfl) ⟨639383, by rfl⟩ : syracuseStep 3410045 = 1278767) (by norm_num)
theorem B1706125 : Blo 1514954 1706125 := bbase (se 3 (by rfl) ⟨319898, by rfl⟩ : syracuseStep 1706125 = 639797) (by norm_num)
theorem B2558101 : Blo 1514954 2558101 := bbase (se 6 (by rfl) ⟨59955, by rfl⟩ : syracuseStep 2558101 = 119911) (by norm_num)
theorem B3836069 : Blo 1514954 3836069 := bbase (se 4 (by rfl) ⟨359631, by rfl⟩ : syracuseStep 3836069 = 719263) (by norm_num)
theorem B1919153 : Blo 1514954 1919153 := bbase (se 2 (by rfl) ⟨719682, by rfl⟩ : syracuseStep 1919153 = 1439365) (by norm_num)
theorem B1706161 : Blo 1514954 1706161 := bbase (se 2 (by rfl) ⟨639810, by rfl⟩ : syracuseStep 1706161 = 1279621) (by norm_num)
theorem B2730181 : Blo 1514954 2730181 := bbase (se 4 (by rfl) ⟨255954, by rfl⟩ : syracuseStep 2730181 = 511909) (by norm_num)
theorem B3410117 : Blo 1514954 3410117 := bbase (se 4 (by rfl) ⟨319698, by rfl⟩ : syracuseStep 3410117 = 639397) (by norm_num)
theorem B3238093 : Blo 1514954 3238093 := bbase (se 3 (by rfl) ⟨607142, by rfl⟩ : syracuseStep 3238093 = 1214285) (by norm_num)
theorem B5114069 : Blo 1514954 5114069 := bbase (se 7 (by rfl) ⟨59930, by rfl⟩ : syracuseStep 5114069 = 119861) (by norm_num)
theorem B1706197 : Blo 1514954 1706197 := bbase (se 7 (by rfl) ⟨19994, by rfl⟩ : syracuseStep 1706197 = 39989) (by norm_num)
theorem B13494485 : Blo 1514954 13494485 := bbase (se 7 (by rfl) ⟨158138, by rfl⟩ : syracuseStep 13494485 = 316277) (by norm_num)
theorem B1919209 : Blo 1514954 1919209 := bbase (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) (by norm_num)
theorem B2558189 : Blo 1514954 2558189 := bbase (se 3 (by rfl) ⟨479660, by rfl⟩ : syracuseStep 2558189 = 959321) (by norm_num)
theorem B1706233 : Blo 1514954 1706233 := bbase (se 2 (by rfl) ⟨639837, by rfl⟩ : syracuseStep 1706233 = 1279675) (by norm_num)
theorem B3410189 : Blo 1514954 3410189 := bbase (se 3 (by rfl) ⟨639410, by rfl⟩ : syracuseStep 3410189 = 1278821) (by norm_num)
theorem B1706269 : Blo 1514954 1706269 := bbase (se 3 (by rfl) ⟨319925, by rfl⟩ : syracuseStep 1706269 = 639851) (by norm_num)
theorem B1706305 : Blo 1514954 1706305 := bbase (se 2 (by rfl) ⟨639864, by rfl⟩ : syracuseStep 1706305 = 1279729) (by norm_num)
theorem B3238213 : Blo 1514954 3238213 := bbase (se 4 (by rfl) ⟨303582, by rfl⟩ : syracuseStep 3238213 = 607165) (by norm_num)
theorem B1919305 : Blo 1514954 1919305 := bbase (se 2 (by rfl) ⟨719739, by rfl⟩ : syracuseStep 1919305 = 1439479) (by norm_num)
theorem B3410261 : Blo 1514954 3410261 := bbase (se 10 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 3410261 = 9991) (by norm_num)
theorem B2877781 : Blo 1514954 2877781 := bbase (se 10 (by rfl) ⟨4215, by rfl⟩ : syracuseStep 2877781 = 8431) (by norm_num)
theorem B3836261 : Blo 1514954 3836261 := bbase (se 4 (by rfl) ⟨359649, by rfl⟩ : syracuseStep 3836261 = 719299) (by norm_num)
theorem B1706341 : Blo 1514954 1706341 := bbase (se 4 (by rfl) ⟨159969, by rfl⟩ : syracuseStep 1706341 = 319939) (by norm_num)
theorem B2558317 : Blo 1514954 2558317 := bbase (se 3 (by rfl) ⟨479684, by rfl⟩ : syracuseStep 2558317 = 959369) (by norm_num)
theorem B1706377 : Blo 1514954 1706377 := bbase (se 2 (by rfl) ⟨639891, by rfl⟩ : syracuseStep 1706377 = 1279783) (by norm_num)
theorem B8751509 : Blo 1514954 8751509 := bbase (se 6 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 8751509 = 410227) (by norm_num)
theorem B3410333 : Blo 1514954 3410333 := bbase (se 3 (by rfl) ⟨639437, by rfl⟩ : syracuseStep 3410333 = 1278875) (by norm_num)
theorem B1706413 : Blo 1514954 1706413 := bbase (se 3 (by rfl) ⟨319952, by rfl⟩ : syracuseStep 1706413 = 639905) (by norm_num)
theorem B7670213 : Blo 1514954 7670213 := bbase (se 4 (by rfl) ⟨719082, by rfl⟩ : syracuseStep 7670213 = 1438165) (by norm_num)
theorem B2558405 : Blo 1514954 2558405 := bbase (se 4 (by rfl) ⟨239850, by rfl⟩ : syracuseStep 2558405 = 479701) (by norm_num)
theorem B1706449 : Blo 1514954 1706449 := bbase (se 2 (by rfl) ⟨639918, by rfl⟩ : syracuseStep 1706449 = 1279837) (by norm_num)
theorem B2427365 : Blo 1514954 2427365 := bbase (se 4 (by rfl) ⟨227565, by rfl⟩ : syracuseStep 2427365 = 455131) (by norm_num)
theorem B3410405 : Blo 1514954 3410405 := bbase (se 4 (by rfl) ⟨319725, by rfl⟩ : syracuseStep 3410405 = 639451) (by norm_num)
theorem B2877925 : Blo 1514954 2877925 := bbase (se 4 (by rfl) ⟨269805, by rfl⟩ : syracuseStep 2877925 = 539611) (by norm_num)
theorem B1919477 : Blo 1514954 1919477 := bbase (se 5 (by rfl) ⟨89975, by rfl⟩ : syracuseStep 1919477 = 179951) (by norm_num)
theorem B1706485 : Blo 1514954 1706485 := bbase (se 5 (by rfl) ⟨79991, by rfl⟩ : syracuseStep 1706485 = 159983) (by norm_num)
theorem B2157077 : Blo 1514954 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B1706521 : Blo 1514954 1706521 := bbase (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) (by norm_num)
theorem B3410477 : Blo 1514954 3410477 := bbase (se 3 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 3410477 = 1278929) (by norm_num)
theorem B1919533 : Blo 1514954 1919533 := bbase (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) (by norm_num)
theorem B1706557 : Blo 1514954 1706557 := bbase (se 3 (by rfl) ⟨319979, by rfl⟩ : syracuseStep 1706557 = 639959) (by norm_num)
theorem B2558533 : Blo 1514954 2558533 := bbase (se 4 (by rfl) ⟨239862, by rfl⟩ : syracuseStep 2558533 = 479725) (by norm_num)
theorem B3238469 : Blo 1514954 3238469 := bbase (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) (by norm_num)
theorem B3410549 : Blo 1514954 3410549 := bbase (se 5 (by rfl) ⟨159869, by rfl⟩ : syracuseStep 3410549 = 319739) (by norm_num)
theorem B5114501 : Blo 1514954 5114501 := bbase (se 4 (by rfl) ⟨479484, by rfl⟩ : syracuseStep 5114501 = 958969) (by norm_num)
theorem B2878085 : Blo 1514954 2878085 := bbase (se 4 (by rfl) ⟨269820, by rfl⟩ : syracuseStep 2878085 = 539641) (by norm_num)
theorem B1919629 : Blo 1514954 1919629 := bbase (se 3 (by rfl) ⟨359930, by rfl⟩ : syracuseStep 1919629 = 719861) (by norm_num)
theorem B2558621 : Blo 1514954 2558621 := bbase (se 3 (by rfl) ⟨479741, by rfl⟩ : syracuseStep 2558621 = 959483) (by norm_num)
theorem B2427565 : Blo 1514954 2427565 := bbase (se 3 (by rfl) ⟨455168, by rfl⟩ : syracuseStep 2427565 = 910337) (by norm_num)
theorem B3836605 : Blo 1514954 3836605 := bbase (se 3 (by rfl) ⟨719363, by rfl⟩ : syracuseStep 3836605 = 1438727) (by norm_num)
theorem B3410621 : Blo 1514954 3410621 := bbase (se 3 (by rfl) ⟨639491, by rfl⟩ : syracuseStep 3410621 = 1278983) (by norm_num)
theorem B3410693 : Blo 1514954 3410693 := bbase (se 4 (by rfl) ⟨319752, by rfl⟩ : syracuseStep 3410693 = 639505) (by norm_num)
theorem B2878229 : Blo 1514954 2878229 := bbase (se 6 (by rfl) ⟨67458, by rfl⟩ : syracuseStep 2878229 = 134917) (by norm_num)
theorem B2558749 : Blo 1514954 2558749 := bbase (se 3 (by rfl) ⟨479765, by rfl⟩ : syracuseStep 2558749 = 959531) (by norm_num)
theorem B3836717 : Blo 1514954 3836717 := bbase (se 3 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 3836717 = 1438769) (by norm_num)
theorem B1821485 : Blo 1514954 1821485 := bbase (se 3 (by rfl) ⟨341528, by rfl⟩ : syracuseStep 1821485 = 683057) (by norm_num)
theorem B1919801 : Blo 1514954 1919801 := bbase (se 2 (by rfl) ⟨719925, by rfl⟩ : syracuseStep 1919801 = 1439851) (by norm_num)
theorem B3410765 : Blo 1514954 3410765 := bbase (se 3 (by rfl) ⟨639518, by rfl⟩ : syracuseStep 3410765 = 1279037) (by norm_num)
theorem B1919857 : Blo 1514954 1919857 := bbase (se 2 (by rfl) ⟨719946, by rfl⟩ : syracuseStep 1919857 = 1439893) (by norm_num)
theorem B2558837 : Blo 1514954 2558837 := bbase (se 5 (by rfl) ⟨119945, by rfl⟩ : syracuseStep 2558837 = 239891) (by norm_num)
theorem B3410837 : Blo 1514954 3410837 := bbase (se 6 (by rfl) ⟨79941, by rfl⟩ : syracuseStep 3410837 = 159883) (by norm_num)
theorem B2427821 : Blo 1514954 2427821 := bbase (se 3 (by rfl) ⟨455216, by rfl⟩ : syracuseStep 2427821 = 910433) (by norm_num)
theorem B3074989 : Blo 1514954 3074989 := bbase (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) (by norm_num)
theorem B1846201 : Blo 1514954 1846201 := bbase (se 2 (by rfl) ⟨692325, by rfl⟩ : syracuseStep 1846201 = 1384651) (by norm_num)
theorem B3410909 : Blo 1514954 3410909 := bbase (se 3 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 3410909 = 1279091) (by norm_num)
theorem B2730989 : Blo 1514954 2730989 := bbase (se 3 (by rfl) ⟨512060, by rfl⟩ : syracuseStep 2730989 = 1024121) (by norm_num)
theorem B3836909 : Blo 1514954 3836909 := bbase (se 3 (by rfl) ⟨719420, by rfl⟩ : syracuseStep 3836909 = 1438841) (by norm_num)
theorem B2558965 : Blo 1514954 2558965 := bbase (se 5 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 2558965 = 239903) (by norm_num)
theorem B5753861 : Blo 1514954 5753861 := bbase (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) (by norm_num)
theorem B11512853 : Blo 1514954 11512853 := bbase (se 6 (by rfl) ⟨269832, by rfl⟩ : syracuseStep 11512853 = 539665) (by norm_num)
theorem B3410981 : Blo 1514954 3410981 := bbase (se 4 (by rfl) ⟨319779, by rfl⟩ : syracuseStep 3410981 = 639559) (by norm_num)
theorem B5114933 : Blo 1514954 5114933 := bbase (se 5 (by rfl) ⟨239762, by rfl⟩ : syracuseStep 5114933 = 479525) (by norm_num)
theorem B2878517 : Blo 1514954 2878517 := bbase (se 5 (by rfl) ⟨134930, by rfl⟩ : syracuseStep 2878517 = 269861) (by norm_num)
theorem B2591813 : Blo 1514954 2591813 := bbase (se 4 (by rfl) ⟨242982, by rfl⟩ : syracuseStep 2591813 = 485965) (by norm_num)
theorem B2559053 : Blo 1514954 2559053 := bbase (se 3 (by rfl) ⟨479822, by rfl⟩ : syracuseStep 2559053 = 959645) (by norm_num)
theorem B1944661 : Blo 1514954 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B1821793 : Blo 1514954 1821793 := bbase (se 2 (by rfl) ⟨683172, by rfl⟩ : syracuseStep 1821793 = 1366345) (by norm_num)
theorem B3411053 : Blo 1514954 3411053 := bbase (se 3 (by rfl) ⟨639572, by rfl⟩ : syracuseStep 3411053 = 1279145) (by norm_num)
theorem B2731133 : Blo 1514954 2731133 := bbase (se 3 (by rfl) ⟨512087, by rfl⟩ : syracuseStep 2731133 = 1024175) (by norm_num)
theorem B3640501 : Blo 1514954 3640501 := bbase (se 5 (by rfl) ⟨170648, by rfl⟩ : syracuseStep 3640501 = 341297) (by norm_num)
theorem B3411125 : Blo 1514954 3411125 := bbase (se 5 (by rfl) ⟨159896, by rfl⟩ : syracuseStep 3411125 = 319793) (by norm_num)
theorem B2272445 : Blo 1514954 2272445 := bbase (se 3 (by rfl) ⟨426083, by rfl⟩ : syracuseStep 2272445 = 852167) (by norm_num)
theorem B1821889 : Blo 1514954 1821889 := bbase (se 2 (by rfl) ⟨683208, by rfl⟩ : syracuseStep 1821889 = 1366417) (by norm_num)
theorem B2731205 : Blo 1514954 2731205 := bbase (se 4 (by rfl) ⟨256050, by rfl⟩ : syracuseStep 2731205 = 512101) (by norm_num)
theorem B2878669 : Blo 1514954 2878669 := bbase (se 3 (by rfl) ⟨539750, by rfl⟩ : syracuseStep 2878669 = 1079501) (by norm_num)
theorem B2559181 : Blo 1514954 2559181 := bbase (se 3 (by rfl) ⟨479846, by rfl⟩ : syracuseStep 2559181 = 959693) (by norm_num)
theorem B2272469 : Blo 1514954 2272469 := bbase (se 7 (by rfl) ⟨26630, by rfl⟩ : syracuseStep 2272469 = 53261) (by norm_num)
theorem B3370205 : Blo 1514954 3370205 := bbase (se 3 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 3370205 = 1263827) (by norm_num)
theorem B2272493 : Blo 1514954 2272493 := bbase (se 3 (by rfl) ⟨426092, by rfl⟩ : syracuseStep 2272493 = 852185) (by norm_num)
theorem B3411197 : Blo 1514954 3411197 := bbase (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) (by norm_num)
theorem B2272517 : Blo 1514954 2272517 := bbase (se 4 (by rfl) ⟨213048, by rfl⟩ : syracuseStep 2272517 = 426097) (by norm_num)
theorem B2592005 : Blo 1514954 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B2272541 : Blo 1514954 2272541 := bbase (se 3 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 2272541 = 852203) (by norm_num)
theorem B5754149 : Blo 1514954 5754149 := bbase (se 4 (by rfl) ⟨539451, by rfl⟩ : syracuseStep 5754149 = 1078903) (by norm_num)
theorem B6917413 : Blo 1514954 6917413 := bbase (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) (by norm_num)
theorem B2559269 : Blo 1514954 2559269 := bbase (se 4 (by rfl) ⟨239931, by rfl⟩ : syracuseStep 2559269 = 479863) (by norm_num)
theorem B2272565 : Blo 1514954 2272565 := bbase (se 5 (by rfl) ⟨106526, by rfl⟩ : syracuseStep 2272565 = 213053) (by norm_num)
theorem B7679285 : Blo 1514954 7679285 := bbase (se 5 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 7679285 = 719933) (by norm_num)
theorem B3837253 : Blo 1514954 3837253 := bbase (se 4 (by rfl) ⟨359742, by rfl⟩ : syracuseStep 3837253 = 719485) (by norm_num)
theorem B3411269 : Blo 1514954 3411269 := bbase (se 4 (by rfl) ⟨319806, by rfl⟩ : syracuseStep 3411269 = 639613) (by norm_num)
theorem B2272589 : Blo 1514954 2272589 := bbase (se 3 (by rfl) ⟨426110, by rfl⟩ : syracuseStep 2272589 = 852221) (by norm_num)
theorem B1822033 : Blo 1514954 1822033 := bbase (se 2 (by rfl) ⟨683262, by rfl⟩ : syracuseStep 1822033 = 1366525) (by norm_num)
theorem B2272613 : Blo 1514954 2272613 := bbase (se 4 (by rfl) ⟨213057, by rfl⟩ : syracuseStep 2272613 = 426115) (by norm_num)
theorem B2272637 : Blo 1514954 2272637 := bbase (se 3 (by rfl) ⟨426119, by rfl⟩ : syracuseStep 2272637 = 852239) (by norm_num)
theorem B3411341 : Blo 1514954 3411341 := bbase (se 3 (by rfl) ⟨639626, by rfl⟩ : syracuseStep 3411341 = 1279253) (by norm_num)
theorem B2272661 : Blo 1514954 2272661 := bbase (se 6 (by rfl) ⟨53265, by rfl⟩ : syracuseStep 2272661 = 106531) (by norm_num)
theorem B3640733 : Blo 1514954 3640733 := bbase (se 3 (by rfl) ⟨682637, by rfl⟩ : syracuseStep 3640733 = 1365275) (by norm_num)
theorem B2731421 : Blo 1514954 2731421 := bbase (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) (by norm_num)
theorem B2559397 : Blo 1514954 2559397 := bbase (se 4 (by rfl) ⟨239943, by rfl⟩ : syracuseStep 2559397 = 479887) (by norm_num)
theorem B2272685 : Blo 1514954 2272685 := bbase (se 3 (by rfl) ⟨426128, by rfl⟩ : syracuseStep 2272685 = 852257) (by norm_num)
theorem B11505077 : Blo 1514954 11505077 := bbase (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) (by norm_num)
theorem B3837365 : Blo 1514954 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B6917557 : Blo 1514954 6917557 := bbase (se 5 (by rfl) ⟨324260, by rfl⟩ : syracuseStep 6917557 = 648521) (by norm_num)
theorem B3239357 : Blo 1514954 3239357 := bbase (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) (by norm_num)
theorem B2272709 : Blo 1514954 2272709 := bbase (se 4 (by rfl) ⟨213066, by rfl⟩ : syracuseStep 2272709 = 426133) (by norm_num)
theorem B25898453 : Blo 1514954 25898453 := bbase (se 7 (by rfl) ⟨303497, by rfl⟩ : syracuseStep 25898453 = 606995) (by norm_num)
theorem B3411413 : Blo 1514954 3411413 := bbase (se 7 (by rfl) ⟨39977, by rfl⟩ : syracuseStep 3411413 = 79955) (by norm_num)
theorem B2272733 : Blo 1514954 2272733 := bbase (se 3 (by rfl) ⟨426137, by rfl⟩ : syracuseStep 2272733 = 852275) (by norm_num)
theorem B5115365 : Blo 1514954 5115365 := bbase (se 4 (by rfl) ⟨479565, by rfl⟩ : syracuseStep 5115365 = 959131) (by norm_num)
theorem B2272757 : Blo 1514954 2272757 := bbase (se 5 (by rfl) ⟨106535, by rfl⟩ : syracuseStep 2272757 = 213071) (by norm_num)
theorem B2878973 : Blo 1514954 2878973 := bbase (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) (by norm_num)
theorem B2559485 : Blo 1514954 2559485 := bbase (se 3 (by rfl) ⟨479903, by rfl⟩ : syracuseStep 2559485 = 959807) (by norm_num)
theorem B2272781 : Blo 1514954 2272781 := bbase (se 3 (by rfl) ⟨426146, by rfl⟩ : syracuseStep 2272781 = 852293) (by norm_num)
theorem B3411485 : Blo 1514954 3411485 := bbase (se 3 (by rfl) ⟨639653, by rfl⟩ : syracuseStep 3411485 = 1279307) (by norm_num)
theorem B2272805 : Blo 1514954 2272805 := bbase (se 4 (by rfl) ⟨213075, by rfl⟩ : syracuseStep 2272805 = 426151) (by norm_num)
theorem B2272829 : Blo 1514954 2272829 := bbase (se 3 (by rfl) ⟨426155, by rfl⟩ : syracuseStep 2272829 = 852311) (by norm_num)
theorem B2272853 : Blo 1514954 2272853 := bbase (se 8 (by rfl) ⟨13317, by rfl⟩ : syracuseStep 2272853 = 26635) (by norm_num)
theorem B110587477 : Blo 1514954 110587477 := bbase (se 8 (by rfl) ⟨647973, by rfl⟩ : syracuseStep 110587477 = 1295947) (by norm_num)
theorem B10923605 : Blo 1514954 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B3411557 : Blo 1514954 3411557 := bbase (se 4 (by rfl) ⟨319833, by rfl⟩ : syracuseStep 3411557 = 639667) (by norm_num)
theorem B2272877 : Blo 1514954 2272877 := bbase (se 3 (by rfl) ⟨426164, by rfl⟩ : syracuseStep 2272877 = 852329) (by norm_num)
theorem B3837557 : Blo 1514954 3837557 := bbase (se 5 (by rfl) ⟨179885, by rfl⟩ : syracuseStep 3837557 = 359771) (by norm_num)
theorem B2559613 : Blo 1514954 2559613 := bbase (se 3 (by rfl) ⟨479927, by rfl⟩ : syracuseStep 2559613 = 959855) (by norm_num)
theorem B2272901 : Blo 1514954 2272901 := bbase (se 4 (by rfl) ⟨213084, by rfl⟩ : syracuseStep 2272901 = 426169) (by norm_num)
theorem B2272925 : Blo 1514954 2272925 := bbase (se 3 (by rfl) ⟨426173, by rfl⟩ : syracuseStep 2272925 = 852347) (by norm_num)
theorem B3411629 : Blo 1514954 3411629 := bbase (se 3 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 3411629 = 1279361) (by norm_num)
theorem B3239597 : Blo 1514954 3239597 := bbase (se 3 (by rfl) ⟨607424, by rfl⟩ : syracuseStep 3239597 = 1214849) (by norm_num)
theorem B2272949 : Blo 1514954 2272949 := bbase (se 5 (by rfl) ⟨106544, by rfl⟩ : syracuseStep 2272949 = 213089) (by norm_num)
theorem B2272973 : Blo 1514954 2272973 := bbase (se 3 (by rfl) ⟨426182, by rfl⟩ : syracuseStep 2272973 = 852365) (by norm_num)
theorem B7671509 : Blo 1514954 7671509 := bbase (se 7 (by rfl) ⟨89900, by rfl⟩ : syracuseStep 7671509 = 179801) (by norm_num)
theorem B2559701 : Blo 1514954 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B2272997 : Blo 1514954 2272997 := bbase (se 4 (by rfl) ⟨213093, by rfl⟩ : syracuseStep 2272997 = 426187) (by norm_num)
theorem B3411701 : Blo 1514954 3411701 := bbase (se 5 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 3411701 = 319847) (by norm_num)
theorem B2273021 : Blo 1514954 2273021 := bbase (se 3 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 2273021 = 852383) (by norm_num)
theorem B2273045 : Blo 1514954 2273045 := bbase (se 6 (by rfl) ⟨53274, by rfl⟩ : syracuseStep 2273045 = 106549) (by norm_num)
theorem B3641125 : Blo 1514954 3641125 := bbase (se 4 (by rfl) ⟨341355, by rfl⟩ : syracuseStep 3641125 = 682711) (by norm_num)
theorem B2273069 : Blo 1514954 2273069 := bbase (se 3 (by rfl) ⟨426200, by rfl⟩ : syracuseStep 2273069 = 852401) (by norm_num)
theorem B3411773 : Blo 1514954 3411773 := bbase (se 3 (by rfl) ⟨639707, by rfl⟩ : syracuseStep 3411773 = 1279415) (by norm_num)
theorem B2273093 : Blo 1514954 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B2559829 : Blo 1514954 2559829 := bbase (se 9 (by rfl) ⟨7499, by rfl⟩ : syracuseStep 2559829 = 14999) (by norm_num)
theorem B2273117 : Blo 1514954 2273117 := bbase (se 3 (by rfl) ⟨426209, by rfl⟩ : syracuseStep 2273117 = 852419) (by norm_num)
theorem B2273141 : Blo 1514954 2273141 := bbase (se 5 (by rfl) ⟨106553, by rfl⟩ : syracuseStep 2273141 = 213107) (by norm_num)
theorem B3411845 : Blo 1514954 3411845 := bbase (se 4 (by rfl) ⟨319860, by rfl⟩ : syracuseStep 3411845 = 639721) (by norm_num)
theorem B2273165 : Blo 1514954 2273165 := bbase (se 3 (by rfl) ⟨426218, by rfl⟩ : syracuseStep 2273165 = 852437) (by norm_num)
theorem B5115797 : Blo 1514954 5115797 := bbase (se 6 (by rfl) ⟨119901, by rfl⟩ : syracuseStep 5115797 = 239803) (by norm_num)
theorem B2273189 : Blo 1514954 2273189 := bbase (se 4 (by rfl) ⟨213111, by rfl⟩ : syracuseStep 2273189 = 426223) (by norm_num)
theorem B2158501 : Blo 1514954 2158501 := bbase (se 4 (by rfl) ⟨202359, by rfl⟩ : syracuseStep 2158501 = 404719) (by norm_num)
theorem B2273213 : Blo 1514954 2273213 := bbase (se 3 (by rfl) ⟨426227, by rfl⟩ : syracuseStep 2273213 = 852455) (by norm_num)
theorem B3837901 : Blo 1514954 3837901 := bbase (se 3 (by rfl) ⟨719606, by rfl⟩ : syracuseStep 3837901 = 1439213) (by norm_num)
theorem B3411917 : Blo 1514954 3411917 := bbase (se 3 (by rfl) ⟨639734, by rfl⟩ : syracuseStep 3411917 = 1279469) (by norm_num)
theorem B2273237 : Blo 1514954 2273237 := bbase (se 7 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 2273237 = 53279) (by norm_num)
theorem B2273261 : Blo 1514954 2273261 := bbase (se 3 (by rfl) ⟨426236, by rfl⟩ : syracuseStep 2273261 = 852473) (by norm_num)
theorem B2273285 : Blo 1514954 2273285 := bbase (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) (by norm_num)
theorem B2428949 : Blo 1514954 2428949 := bbase (se 6 (by rfl) ⟨56928, by rfl⟩ : syracuseStep 2428949 = 113857) (by norm_num)
theorem B3411989 : Blo 1514954 3411989 := bbase (se 6 (by rfl) ⟨79968, by rfl⟩ : syracuseStep 3411989 = 159937) (by norm_num)
theorem B2273309 : Blo 1514954 2273309 := bbase (se 3 (by rfl) ⟨426245, by rfl⟩ : syracuseStep 2273309 = 852491) (by norm_num)
theorem B1617953 : Blo 1514954 1617953 := bbase (se 2 (by rfl) ⟨606732, by rfl⟩ : syracuseStep 1617953 = 1213465) (by norm_num)
theorem B2273333 : Blo 1514954 2273333 := bbase (se 5 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 2273333 = 213125) (by norm_num)
theorem B3838013 : Blo 1514954 3838013 := bbase (se 3 (by rfl) ⟨719627, by rfl⟩ : syracuseStep 3838013 = 1439255) (by norm_num)
theorem B2273357 : Blo 1514954 2273357 := bbase (se 3 (by rfl) ⟨426254, by rfl⟩ : syracuseStep 2273357 = 852509) (by norm_num)
theorem B1618013 : Blo 1514954 1618013 := bbase (se 3 (by rfl) ⟨303377, by rfl⟩ : syracuseStep 1618013 = 606755) (by norm_num)
theorem B3412061 : Blo 1514954 3412061 := bbase (se 3 (by rfl) ⟨639761, by rfl⟩ : syracuseStep 3412061 = 1279523) (by norm_num)
theorem B2273381 : Blo 1514954 2273381 := bbase (se 4 (by rfl) ⟨213129, by rfl⟩ : syracuseStep 2273381 = 426259) (by norm_num)
theorem B2273405 : Blo 1514954 2273405 := bbase (se 3 (by rfl) ⟨426263, by rfl⟩ : syracuseStep 2273405 = 852527) (by norm_num)
theorem B2273429 : Blo 1514954 2273429 := bbase (se 6 (by rfl) ⟨53283, by rfl⟩ : syracuseStep 2273429 = 106567) (by norm_num)
theorem B3887261 : Blo 1514954 3887261 := bbase (se 3 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 3887261 = 1457723) (by norm_num)
theorem B3412133 : Blo 1514954 3412133 := bbase (se 4 (by rfl) ⟨319887, by rfl⟩ : syracuseStep 3412133 = 639775) (by norm_num)
theorem B2273453 : Blo 1514954 2273453 := bbase (se 3 (by rfl) ⟨426272, by rfl⟩ : syracuseStep 2273453 = 852545) (by norm_num)
theorem B2732221 : Blo 1514954 2732221 := bbase (se 3 (by rfl) ⟨512291, by rfl⟩ : syracuseStep 2732221 = 1024583) (by norm_num)
theorem B2306237 : Blo 1514954 2306237 := bbase (se 3 (by rfl) ⟨432419, by rfl⟩ : syracuseStep 2306237 = 864839) (by norm_num)
theorem B2273477 : Blo 1514954 2273477 := bbase (se 4 (by rfl) ⟨213138, by rfl⟩ : syracuseStep 2273477 = 426277) (by norm_num)
theorem B19435733 : Blo 1514954 19435733 := bbase (se 7 (by rfl) ⟨227762, by rfl⟩ : syracuseStep 19435733 = 455525) (by norm_num)
theorem B1618141 : Blo 1514954 1618141 := bbase (se 3 (by rfl) ⟨303401, by rfl⟩ : syracuseStep 1618141 = 606803) (by norm_num)
theorem B2273501 : Blo 1514954 2273501 := bbase (se 3 (by rfl) ⟨426281, by rfl⟩ : syracuseStep 2273501 = 852563) (by norm_num)
theorem B3412205 : Blo 1514954 3412205 := bbase (se 3 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 3412205 = 1279577) (by norm_num)
theorem B2306285 : Blo 1514954 2306285 := bbase (se 3 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 2306285 = 864857) (by norm_num)
theorem B2879725 : Blo 1514954 2879725 := bbase (se 3 (by rfl) ⟨539948, by rfl⟩ : syracuseStep 2879725 = 1079897) (by norm_num)
theorem B2273525 : Blo 1514954 2273525 := bbase (se 5 (by rfl) ⟨106571, by rfl⟩ : syracuseStep 2273525 = 213143) (by norm_num)
theorem B3838205 : Blo 1514954 3838205 := bbase (se 3 (by rfl) ⟨719663, by rfl⟩ : syracuseStep 3838205 = 1439327) (by norm_num)
theorem B2273549 : Blo 1514954 2273549 := bbase (se 3 (by rfl) ⟨426290, by rfl⟩ : syracuseStep 2273549 = 852581) (by norm_num)
theorem B2273573 : Blo 1514954 2273573 := bbase (se 4 (by rfl) ⟨213147, by rfl⟩ : syracuseStep 2273573 = 426295) (by norm_num)
theorem B3412277 : Blo 1514954 3412277 := bbase (se 5 (by rfl) ⟨159950, by rfl⟩ : syracuseStep 3412277 = 319901) (by norm_num)
theorem B2273597 : Blo 1514954 2273597 := bbase (se 3 (by rfl) ⟨426299, by rfl⟩ : syracuseStep 2273597 = 852599) (by norm_num)
theorem B5116229 : Blo 1514954 5116229 := bbase (se 4 (by rfl) ⟨479646, by rfl⟩ : syracuseStep 5116229 = 959293) (by norm_num)
theorem B2273621 : Blo 1514954 2273621 := bbase (se 10 (by rfl) ⟨3330, by rfl⟩ : syracuseStep 2273621 = 6661) (by norm_num)
theorem B2273645 : Blo 1514954 2273645 := bbase (se 3 (by rfl) ⟨426308, by rfl⟩ : syracuseStep 2273645 = 852617) (by norm_num)
theorem B3412349 : Blo 1514954 3412349 := bbase (se 3 (by rfl) ⟨639815, by rfl⟩ : syracuseStep 3412349 = 1279631) (by norm_num)
theorem B2273669 : Blo 1514954 2273669 := bbase (se 4 (by rfl) ⟨213156, by rfl⟩ : syracuseStep 2273669 = 426313) (by norm_num)
theorem B2273693 : Blo 1514954 2273693 := bbase (se 3 (by rfl) ⟨426317, by rfl⟩ : syracuseStep 2273693 = 852635) (by norm_num)
theorem B2273717 : Blo 1514954 2273717 := bbase (se 5 (by rfl) ⟨106580, by rfl⟩ : syracuseStep 2273717 = 213161) (by norm_num)
theorem B5755333 : Blo 1514954 5755333 := bbase (se 4 (by rfl) ⟨539562, by rfl⟩ : syracuseStep 5755333 = 1079125) (by norm_num)
theorem B3412421 : Blo 1514954 3412421 := bbase (se 4 (by rfl) ⟨319914, by rfl⟩ : syracuseStep 3412421 = 639829) (by norm_num)
theorem B2273741 : Blo 1514954 2273741 := bbase (se 3 (by rfl) ⟨426326, by rfl⟩ : syracuseStep 2273741 = 852653) (by norm_num)
theorem B2273765 : Blo 1514954 2273765 := bbase (se 4 (by rfl) ⟨213165, by rfl⟩ : syracuseStep 2273765 = 426331) (by norm_num)
theorem B2159093 : Blo 1514954 2159093 := bbase (se 5 (by rfl) ⟨101207, by rfl⟩ : syracuseStep 2159093 = 202415) (by norm_num)
theorem B2273789 : Blo 1514954 2273789 := bbase (se 3 (by rfl) ⟨426335, by rfl⟩ : syracuseStep 2273789 = 852671) (by norm_num)
theorem B3412493 : Blo 1514954 3412493 := bbase (se 3 (by rfl) ⟨639842, by rfl⟩ : syracuseStep 3412493 = 1279685) (by norm_num)
theorem B2273813 : Blo 1514954 2273813 := bbase (se 6 (by rfl) ⟨53292, by rfl⟩ : syracuseStep 2273813 = 106585) (by norm_num)
theorem B2429461 : Blo 1514954 2429461 := bbase (se 6 (by rfl) ⟨56940, by rfl⟩ : syracuseStep 2429461 = 113881) (by norm_num)
theorem B2273837 : Blo 1514954 2273837 := bbase (se 3 (by rfl) ⟨426344, by rfl⟩ : syracuseStep 2273837 = 852689) (by norm_num)
theorem B2273861 : Blo 1514954 2273861 := bbase (se 4 (by rfl) ⟨213174, by rfl⟩ : syracuseStep 2273861 = 426349) (by norm_num)
theorem B2159173 : Blo 1514954 2159173 := bbase (se 4 (by rfl) ⟨202422, by rfl⟩ : syracuseStep 2159173 = 404845) (by norm_num)
theorem B3838549 : Blo 1514954 3838549 := bbase (se 8 (by rfl) ⟨22491, by rfl⟩ : syracuseStep 3838549 = 44983) (by norm_num)
theorem B3412565 : Blo 1514954 3412565 := bbase (se 8 (by rfl) ⟨19995, by rfl⟩ : syracuseStep 3412565 = 39991) (by norm_num)
theorem B2273885 : Blo 1514954 2273885 := bbase (se 3 (by rfl) ⟨426353, by rfl⟩ : syracuseStep 2273885 = 852707) (by norm_num)
theorem B2273909 : Blo 1514954 2273909 := bbase (se 5 (by rfl) ⟨106589, by rfl⟩ : syracuseStep 2273909 = 213179) (by norm_num)
theorem B2273933 : Blo 1514954 2273933 := bbase (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) (by norm_num)
theorem B1618585 : Blo 1514954 1618585 := bbase (se 2 (by rfl) ⟨606969, by rfl⟩ : syracuseStep 1618585 = 1213939) (by norm_num)
theorem B3412637 : Blo 1514954 3412637 := bbase (se 3 (by rfl) ⟨639869, by rfl⟩ : syracuseStep 3412637 = 1279739) (by norm_num)
theorem B2273957 : Blo 1514954 2273957 := bbase (se 4 (by rfl) ⟨213183, by rfl⟩ : syracuseStep 2273957 = 426367) (by norm_num)
theorem B6402725 : Blo 1514954 6402725 := bbase (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) (by norm_num)
theorem B2273981 : Blo 1514954 2273981 := bbase (se 3 (by rfl) ⟨426371, by rfl⟩ : syracuseStep 2273981 = 852743) (by norm_num)
theorem B2159293 : Blo 1514954 2159293 := bbase (se 3 (by rfl) ⟨404867, by rfl⟩ : syracuseStep 2159293 = 809735) (by norm_num)
theorem B3838661 : Blo 1514954 3838661 := bbase (se 4 (by rfl) ⟨359874, by rfl⟩ : syracuseStep 3838661 = 719749) (by norm_num)
theorem B2274005 : Blo 1514954 2274005 := bbase (se 7 (by rfl) ⟨26648, by rfl⟩ : syracuseStep 2274005 = 53297) (by norm_num)
theorem B3412709 : Blo 1514954 3412709 := bbase (se 4 (by rfl) ⟨319941, by rfl⟩ : syracuseStep 3412709 = 639883) (by norm_num)
theorem B2274029 : Blo 1514954 2274029 := bbase (se 3 (by rfl) ⟨426380, by rfl⟩ : syracuseStep 2274029 = 852761) (by norm_num)
theorem B5755637 : Blo 1514954 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B5116661 : Blo 1514954 5116661 := bbase (se 5 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 5116661 = 479687) (by norm_num)
theorem B2274053 : Blo 1514954 2274053 := bbase (se 4 (by rfl) ⟨213192, by rfl⟩ : syracuseStep 2274053 = 426385) (by norm_num)
theorem B1618705 : Blo 1514954 1618705 := bbase (se 2 (by rfl) ⟨607014, by rfl⟩ : syracuseStep 1618705 = 1214029) (by norm_num)
theorem B2274077 : Blo 1514954 2274077 := bbase (se 3 (by rfl) ⟨426389, by rfl⟩ : syracuseStep 2274077 = 852779) (by norm_num)
theorem B2159389 : Blo 1514954 2159389 := bbase (se 3 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 2159389 = 809771) (by norm_num)
theorem B3412781 : Blo 1514954 3412781 := bbase (se 3 (by rfl) ⟨639896, by rfl⟩ : syracuseStep 3412781 = 1279793) (by norm_num)
theorem B2274101 : Blo 1514954 2274101 := bbase (se 5 (by rfl) ⟨106598, by rfl⟩ : syracuseStep 2274101 = 213197) (by norm_num)
theorem B6476597 : Blo 1514954 6476597 := bbase (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) (by norm_num)
theorem B2274125 : Blo 1514954 2274125 := bbase (se 3 (by rfl) ⟨426398, by rfl⟩ : syracuseStep 2274125 = 852797) (by norm_num)
theorem B2274149 : Blo 1514954 2274149 := bbase (se 4 (by rfl) ⟨213201, by rfl⟩ : syracuseStep 2274149 = 426403) (by norm_num)
theorem B3642221 : Blo 1514954 3642221 := bbase (se 3 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 3642221 = 1365833) (by norm_num)
theorem B3412853 : Blo 1514954 3412853 := bbase (se 5 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 3412853 = 319955) (by norm_num)
theorem B2274173 : Blo 1514954 2274173 := bbase (se 3 (by rfl) ⟨426407, by rfl⟩ : syracuseStep 2274173 = 852815) (by norm_num)
theorem B3838853 : Blo 1514954 3838853 := bbase (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) (by norm_num)
theorem B2274197 : Blo 1514954 2274197 := bbase (se 6 (by rfl) ⟨53301, by rfl⟩ : syracuseStep 2274197 = 106603) (by norm_num)
theorem B2274221 : Blo 1514954 2274221 := bbase (se 3 (by rfl) ⟨426416, by rfl⟩ : syracuseStep 2274221 = 852833) (by norm_num)
theorem B3412925 : Blo 1514954 3412925 := bbase (se 3 (by rfl) ⟨639923, by rfl⟩ : syracuseStep 3412925 = 1279847) (by norm_num)
theorem B2274245 : Blo 1514954 2274245 := bbase (se 4 (by rfl) ⟨213210, by rfl⟩ : syracuseStep 2274245 = 426421) (by norm_num)
theorem B2274269 : Blo 1514954 2274269 := bbase (se 3 (by rfl) ⟨426425, by rfl⟩ : syracuseStep 2274269 = 852851) (by norm_num)
theorem B2593757 : Blo 1514954 2593757 := bbase (se 3 (by rfl) ⟨486329, by rfl⟩ : syracuseStep 2593757 = 972659) (by norm_num)
theorem B7672805 : Blo 1514954 7672805 := bbase (se 4 (by rfl) ⟨719325, by rfl⟩ : syracuseStep 7672805 = 1438651) (by norm_num)
theorem B2733029 : Blo 1514954 2733029 := bbase (se 4 (by rfl) ⟨256221, by rfl⟩ : syracuseStep 2733029 = 512443) (by norm_num)
theorem B3888109 : Blo 1514954 3888109 := bbase (se 3 (by rfl) ⟨729020, by rfl⟩ : syracuseStep 3888109 = 1458041) (by norm_num)
theorem B2274293 : Blo 1514954 2274293 := bbase (se 5 (by rfl) ⟨106607, by rfl⟩ : syracuseStep 2274293 = 213215) (by norm_num)
theorem B3412997 : Blo 1514954 3412997 := bbase (se 4 (by rfl) ⟨319968, by rfl⟩ : syracuseStep 3412997 = 639937) (by norm_num)
theorem B1618957 : Blo 1514954 1618957 := bbase (se 3 (by rfl) ⟨303554, by rfl⟩ : syracuseStep 1618957 = 607109) (by norm_num)
theorem B2274317 : Blo 1514954 2274317 := bbase (se 3 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 2274317 = 852869) (by norm_num)
theorem B1618961 : Blo 1514954 1618961 := bbase (se 2 (by rfl) ⟨607110, by rfl⟩ : syracuseStep 1618961 = 1214221) (by norm_num)
theorem B2274341 : Blo 1514954 2274341 := bbase (se 4 (by rfl) ⟨213219, by rfl⟩ : syracuseStep 2274341 = 426439) (by norm_num)
theorem B2274365 : Blo 1514954 2274365 := bbase (se 3 (by rfl) ⟨426443, by rfl⟩ : syracuseStep 2274365 = 852887) (by norm_num)
theorem B3413069 : Blo 1514954 3413069 := bbase (se 3 (by rfl) ⟨639950, by rfl⟩ : syracuseStep 3413069 = 1279901) (by norm_num)
theorem B2274389 : Blo 1514954 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B2274413 : Blo 1514954 2274413 := bbase (se 3 (by rfl) ⟨426452, by rfl⟩ : syracuseStep 2274413 = 852905) (by norm_num)
theorem B2274437 : Blo 1514954 2274437 := bbase (se 4 (by rfl) ⟨213228, by rfl⟩ : syracuseStep 2274437 = 426457) (by norm_num)
theorem B3642509 : Blo 1514954 3642509 := bbase (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) (by norm_num)
theorem B3413141 : Blo 1514954 3413141 := bbase (se 6 (by rfl) ⟨79995, by rfl⟩ : syracuseStep 3413141 = 159991) (by norm_num)
theorem B2274461 : Blo 1514954 2274461 := bbase (se 3 (by rfl) ⟨426461, by rfl⟩ : syracuseStep 2274461 = 852923) (by norm_num)
theorem B5117093 : Blo 1514954 5117093 := bbase (se 4 (by rfl) ⟨479727, by rfl⟩ : syracuseStep 5117093 = 959455) (by norm_num)
theorem B4674725 : Blo 1514954 4674725 := bbase (se 4 (by rfl) ⟨438255, by rfl⟩ : syracuseStep 4674725 = 876511) (by norm_num)
theorem B7779509 : Blo 1514954 7779509 := bbase (se 5 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 7779509 = 729329) (by norm_num)
theorem B2274485 : Blo 1514954 2274485 := bbase (se 5 (by rfl) ⟨106616, by rfl⟩ : syracuseStep 2274485 = 213233) (by norm_num)
theorem B2274509 : Blo 1514954 2274509 := bbase (se 3 (by rfl) ⟨426470, by rfl⟩ : syracuseStep 2274509 = 852941) (by norm_num)
theorem B2495701 : Blo 1514954 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B3839197 : Blo 1514954 3839197 := bbase (se 3 (by rfl) ⟨719849, by rfl⟩ : syracuseStep 3839197 = 1439699) (by norm_num)
theorem B2274533 : Blo 1514954 2274533 := bbase (se 4 (by rfl) ⟨213237, by rfl⟩ : syracuseStep 2274533 = 426475) (by norm_num)
theorem B2274557 : Blo 1514954 2274557 := bbase (se 3 (by rfl) ⟨426479, by rfl⟩ : syracuseStep 2274557 = 852959) (by norm_num)
theorem B2274581 : Blo 1514954 2274581 := bbase (se 6 (by rfl) ⟨53310, by rfl⟩ : syracuseStep 2274581 = 106621) (by norm_num)
theorem B1537309 : Blo 1514954 1537309 := bbase (se 3 (by rfl) ⟨288245, by rfl⟩ : syracuseStep 1537309 = 576491) (by norm_num)
theorem B2274605 : Blo 1514954 2274605 := bbase (se 3 (by rfl) ⟨426488, by rfl⟩ : syracuseStep 2274605 = 852977) (by norm_num)
theorem B2274629 : Blo 1514954 2274629 := bbase (se 4 (by rfl) ⟨213246, by rfl⟩ : syracuseStep 2274629 = 426493) (by norm_num)
theorem B3839309 : Blo 1514954 3839309 := bbase (se 3 (by rfl) ⟨719870, by rfl⟩ : syracuseStep 3839309 = 1439741) (by norm_num)
theorem B2274653 : Blo 1514954 2274653 := bbase (se 3 (by rfl) ⟨426497, by rfl⟩ : syracuseStep 2274653 = 852995) (by norm_num)
theorem B4314485 : Blo 1514954 4314485 := bbase (se 5 (by rfl) ⟨202241, by rfl⟩ : syracuseStep 4314485 = 404483) (by norm_num)
theorem B2274677 : Blo 1514954 2274677 := bbase (se 5 (by rfl) ⟨106625, by rfl⟩ : syracuseStep 2274677 = 213251) (by norm_num)
theorem B2274701 : Blo 1514954 2274701 := bbase (se 3 (by rfl) ⟨426506, by rfl⟩ : syracuseStep 2274701 = 853013) (by norm_num)
theorem B2274725 : Blo 1514954 2274725 := bbase (se 4 (by rfl) ⟨213255, by rfl⟩ : syracuseStep 2274725 = 426511) (by norm_num)
theorem B2274749 : Blo 1514954 2274749 := bbase (se 3 (by rfl) ⟨426515, by rfl⟩ : syracuseStep 2274749 = 853031) (by norm_num)
theorem B5461445 : Blo 1514954 5461445 := bbase (se 4 (by rfl) ⟨512010, by rfl⟩ : syracuseStep 5461445 = 1024021) (by norm_num)
theorem B2274773 : Blo 1514954 2274773 := bbase (se 7 (by rfl) ⟨26657, by rfl⟩ : syracuseStep 2274773 = 53315) (by norm_num)
theorem B2274797 : Blo 1514954 2274797 := bbase (se 3 (by rfl) ⟨426524, by rfl⟩ : syracuseStep 2274797 = 853049) (by norm_num)
theorem B2274821 : Blo 1514954 2274821 := bbase (se 4 (by rfl) ⟨213264, by rfl⟩ : syracuseStep 2274821 = 426529) (by norm_num)
theorem B3839501 : Blo 1514954 3839501 := bbase (se 3 (by rfl) ⟨719906, by rfl⟩ : syracuseStep 3839501 = 1439813) (by norm_num)
theorem B2274845 : Blo 1514954 2274845 := bbase (se 3 (by rfl) ⟨426533, by rfl⟩ : syracuseStep 2274845 = 853067) (by norm_num)
theorem B2274869 : Blo 1514954 2274869 := bbase (se 5 (by rfl) ⟨106634, by rfl⟩ : syracuseStep 2274869 = 213269) (by norm_num)
theorem B1619525 : Blo 1514954 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B2274893 : Blo 1514954 2274893 := bbase (se 3 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 2274893 = 853085) (by norm_num)
theorem B5117525 : Blo 1514954 5117525 := bbase (se 8 (by rfl) ⟨29985, by rfl⟩ : syracuseStep 5117525 = 59971) (by norm_num)
theorem B2274917 : Blo 1514954 2274917 := bbase (se 4 (by rfl) ⟨213273, by rfl⟩ : syracuseStep 2274917 = 426547) (by norm_num)
theorem B2274941 : Blo 1514954 2274941 := bbase (se 3 (by rfl) ⟨426551, by rfl⟩ : syracuseStep 2274941 = 853103) (by norm_num)
theorem B2274965 : Blo 1514954 2274965 := bbase (se 6 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 2274965 = 106639) (by norm_num)
theorem B2274989 : Blo 1514954 2274989 := bbase (se 3 (by rfl) ⟨426560, by rfl⟩ : syracuseStep 2274989 = 853121) (by norm_num)
theorem B2275013 : Blo 1514954 2275013 := bbase (se 4 (by rfl) ⟨213282, by rfl⟩ : syracuseStep 2275013 = 426565) (by norm_num)
theorem B2275037 : Blo 1514954 2275037 := bbase (se 3 (by rfl) ⟨426569, by rfl⟩ : syracuseStep 2275037 = 853139) (by norm_num)
theorem B11671285 : Blo 1514954 11671285 := bbase (se 5 (by rfl) ⟨547091, by rfl⟩ : syracuseStep 11671285 = 1094183) (by norm_num)
theorem B2275061 : Blo 1514954 2275061 := bbase (se 5 (by rfl) ⟨106643, by rfl⟩ : syracuseStep 2275061 = 213287) (by norm_num)
theorem B1619713 : Blo 1514954 1619713 := bbase (se 2 (by rfl) ⟨607392, by rfl⟩ : syracuseStep 1619713 = 1214785) (by norm_num)
theorem B2275085 : Blo 1514954 2275085 := bbase (se 3 (by rfl) ⟨426578, by rfl⟩ : syracuseStep 2275085 = 853157) (by norm_num)
theorem B7280405 : Blo 1514954 7280405 := bbase (se 6 (by rfl) ⟨170634, by rfl⟩ : syracuseStep 7280405 = 341269) (by norm_num)
theorem B2275109 : Blo 1514954 2275109 := bbase (se 4 (by rfl) ⟨213291, by rfl⟩ : syracuseStep 2275109 = 426583) (by norm_num)
theorem B2275133 : Blo 1514954 2275133 := bbase (se 3 (by rfl) ⟨426587, by rfl⟩ : syracuseStep 2275133 = 853175) (by norm_num)
theorem B2275157 : Blo 1514954 2275157 := bbase (se 9 (by rfl) ⟨6665, by rfl⟩ : syracuseStep 2275157 = 13331) (by norm_num)
theorem B2275181 : Blo 1514954 2275181 := bbase (se 3 (by rfl) ⟨426596, by rfl⟩ : syracuseStep 2275181 = 853193) (by norm_num)
theorem B2275205 : Blo 1514954 2275205 := bbase (se 4 (by rfl) ⟨213300, by rfl⟩ : syracuseStep 2275205 = 426601) (by norm_num)
theorem B2594701 : Blo 1514954 2594701 := bbase (se 3 (by rfl) ⟨486506, by rfl⟩ : syracuseStep 2594701 = 973013) (by norm_num)
theorem B2275229 : Blo 1514954 2275229 := bbase (se 3 (by rfl) ⟨426605, by rfl⟩ : syracuseStep 2275229 = 853211) (by norm_num)
theorem B4437925 : Blo 1514954 4437925 := bbase (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) (by norm_num)
theorem B2275253 : Blo 1514954 2275253 := bbase (se 5 (by rfl) ⟨106652, by rfl⟩ : syracuseStep 2275253 = 213305) (by norm_num)
theorem B2275277 : Blo 1514954 2275277 := bbase (se 3 (by rfl) ⟨426614, by rfl⟩ : syracuseStep 2275277 = 853229) (by norm_num)
theorem B5183461 : Blo 1514954 5183461 := bbase (se 4 (by rfl) ⟨485949, by rfl⟩ : syracuseStep 5183461 = 971899) (by norm_num)
theorem B2275301 : Blo 1514954 2275301 := bbase (se 4 (by rfl) ⟨213309, by rfl⟩ : syracuseStep 2275301 = 426619) (by norm_num)
theorem B2275325 : Blo 1514954 2275325 := bbase (se 3 (by rfl) ⟨426623, by rfl⟩ : syracuseStep 2275325 = 853247) (by norm_num)
theorem B5117957 : Blo 1514954 5117957 := bbase (se 4 (by rfl) ⟨479808, by rfl⟩ : syracuseStep 5117957 = 959617) (by norm_num)
theorem B4315157 : Blo 1514954 4315157 := bbase (se 6 (by rfl) ⟨101136, by rfl⟩ : syracuseStep 4315157 = 202273) (by norm_num)
theorem B2275349 : Blo 1514954 2275349 := bbase (se 6 (by rfl) ⟨53328, by rfl⟩ : syracuseStep 2275349 = 106657) (by norm_num)
theorem B2275373 : Blo 1514954 2275373 := bbase (se 3 (by rfl) ⟨426632, by rfl⟩ : syracuseStep 2275373 = 853265) (by norm_num)
theorem B2275397 : Blo 1514954 2275397 := bbase (se 4 (by rfl) ⟨213318, by rfl⟩ : syracuseStep 2275397 = 426637) (by norm_num)
theorem B2275421 : Blo 1514954 2275421 := bbase (se 3 (by rfl) ⟨426641, by rfl⟩ : syracuseStep 2275421 = 853283) (by norm_num)
theorem B5462149 : Blo 1514954 5462149 := bbase (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) (by norm_num)
theorem B8190197 : Blo 1514954 8190197 := bbase (se 5 (by rfl) ⟨383915, by rfl⟩ : syracuseStep 8190197 = 767831) (by norm_num)
theorem B7674101 : Blo 1514954 7674101 := bbase (se 5 (by rfl) ⟨359723, by rfl⟩ : syracuseStep 7674101 = 719447) (by norm_num)
theorem B4921685 : Blo 1514954 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B17267093 : Blo 1514954 17267093 := bbase (se 6 (by rfl) ⟨404697, by rfl⟩ : syracuseStep 17267093 = 809395) (by norm_num)
theorem B5118389 : Blo 1514954 5118389 := bbase (se 5 (by rfl) ⟨239924, by rfl⟩ : syracuseStep 5118389 = 479849) (by norm_num)
theorem B4315589 : Blo 1514954 4315589 := bbase (se 4 (by rfl) ⟨404586, by rfl⟩ : syracuseStep 4315589 = 809173) (by norm_num)
theorem B3037637 : Blo 1514954 3037637 := bbase (se 4 (by rfl) ⟨284778, by rfl⟩ : syracuseStep 3037637 = 569557) (by norm_num)
theorem B7281173 : Blo 1514954 7281173 := bbase (se 6 (by rfl) ⟨170652, by rfl⟩ : syracuseStep 7281173 = 341305) (by norm_num)
theorem B6478373 : Blo 1514954 6478373 := bbase (se 4 (by rfl) ⟨607347, by rfl⟩ : syracuseStep 6478373 = 1214695) (by norm_num)
theorem B2808389 : Blo 1514954 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B7289477 : Blo 1514954 7289477 := bbase (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) (by norm_num)
theorem B6478613 : Blo 1514954 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B5757749 : Blo 1514954 5757749 := bbase (se 5 (by rfl) ⟨269894, by rfl⟩ : syracuseStep 5757749 = 539789) (by norm_num)
theorem B13130581 : Blo 1514954 13130581 := bbase (se 9 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 13130581 = 76937) (by norm_num)
theorem B5118821 : Blo 1514954 5118821 := bbase (se 4 (by rfl) ⟨479889, by rfl⟩ : syracuseStep 5118821 = 959779) (by norm_num)
theorem B2915389 : Blo 1514954 2915389 := bbase (se 3 (by rfl) ⟨546635, by rfl⟩ : syracuseStep 2915389 = 1093271) (by norm_num)
theorem B5758037 : Blo 1514954 5758037 := bbase (se 8 (by rfl) ⟨33738, by rfl⟩ : syracuseStep 5758037 = 67477) (by norm_num)
theorem B4316341 : Blo 1514954 4316341 := bbase (se 5 (by rfl) ⟨202328, by rfl⟩ : syracuseStep 4316341 = 404657) (by norm_num)
theorem B3644605 : Blo 1514954 3644605 := bbase (se 3 (by rfl) ⟨683363, by rfl⟩ : syracuseStep 3644605 = 1366727) (by norm_num)
theorem B4857077 : Blo 1514954 4857077 := bbase (se 5 (by rfl) ⟨227675, by rfl⟩ : syracuseStep 4857077 = 455351) (by norm_num)
theorem B5119253 : Blo 1514954 5119253 := bbase (se 6 (by rfl) ⟨119982, by rfl⟩ : syracuseStep 5119253 = 239965) (by norm_num)
theorem B11672885 : Blo 1514954 11672885 := bbase (se 5 (by rfl) ⟨547166, by rfl⟩ : syracuseStep 11672885 = 1094333) (by norm_num)
theorem B224255317 : Blo 1514954 224255317 := bbase (se 11 (by rfl) ⟨164249, by rfl⟩ : syracuseStep 224255317 = 328499) (by norm_num)
theorem B7675397 : Blo 1514954 7675397 := bbase (se 4 (by rfl) ⟨719568, by rfl⟩ : syracuseStep 7675397 = 1439137) (by norm_num)
theorem B16383637 : Blo 1514954 16383637 := bbase (se 6 (by rfl) ⟨383991, by rfl⟩ : syracuseStep 16383637 = 767983) (by norm_num)
theorem B8756885 : Blo 1514954 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B5119685 : Blo 1514954 5119685 := bbase (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) (by norm_num)
theorem B3235565 : Blo 1514954 3235565 := bbase (se 3 (by rfl) ⟨606668, by rfl⟩ : syracuseStep 3235565 = 1213337) (by norm_num)
theorem B20750165 : Blo 1514954 20750165 := bbase (se 9 (by rfl) ⟨60791, by rfl⟩ : syracuseStep 20750165 = 121583) (by norm_num)
theorem B31113173 : Blo 1514954 31113173 := bbase (se 7 (by rfl) ⟨364607, by rfl⟩ : syracuseStep 31113173 = 729215) (by norm_num)
theorem B1515523 : Blo 1514954 1515523 := bstep (se 1 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 1515523 = 2273285) B2273285
theorem B1515539 : Blo 1514954 1515539 := bstep (se 1 (by rfl) ⟨1136654, by rfl⟩ : syracuseStep 1515539 = 2273309) B2273309
theorem B1515555 : Blo 1514954 1515555 := bstep (se 1 (by rfl) ⟨1136666, by rfl⟩ : syracuseStep 1515555 = 2273333) B2273333
theorem B4317229 : Blo 1514954 4317229 := bstep (se 3 (by rfl) ⟨809480, by rfl⟩ : syracuseStep 4317229 = 1618961) B1618961
theorem B3235889 : Blo 1514954 3235889 := bstep (se 2 (by rfl) ⟨1213458, by rfl⟩ : syracuseStep 3235889 = 2426917) B2426917
theorem B1515571 : Blo 1514954 1515571 := bstep (se 1 (by rfl) ⟨1136678, by rfl⟩ : syracuseStep 1515571 = 2273357) B2273357
theorem B27648053 : Blo 1514954 27648053 := bstep (se 5 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 27648053 = 2592005) B2592005
theorem B1515587 : Blo 1514954 1515587 := bstep (se 1 (by rfl) ⟨1136690, by rfl⟩ : syracuseStep 1515587 = 2273381) B2273381
theorem B8634437 : Blo 1514954 8634437 := bstep (se 4 (by rfl) ⟨809478, by rfl⟩ : syracuseStep 8634437 = 1618957) B1618957
theorem B1515603 : Blo 1514954 1515603 := bstep (se 1 (by rfl) ⟨1136702, by rfl⟩ : syracuseStep 1515603 = 2273405) B2273405
theorem B1515619 : Blo 1514954 1515619 := bstep (se 1 (by rfl) ⟨1136714, by rfl⟩ : syracuseStep 1515619 = 2273429) B2273429
theorem B1515635 : Blo 1514954 1515635 := bstep (se 1 (by rfl) ⟨1136726, by rfl⟩ : syracuseStep 1515635 = 2273453) B2273453
theorem B1515651 : Blo 1514954 1515651 := bstep (se 1 (by rfl) ⟨1136738, by rfl⟩ : syracuseStep 1515651 = 2273477) B2273477
theorem B7676045 : Blo 1514954 7676045 := bstep (se 3 (by rfl) ⟨1439258, by rfl⟩ : syracuseStep 7676045 = 2878517) B2878517
theorem B1515667 : Blo 1514954 1515667 := bstep (se 1 (by rfl) ⟨1136750, by rfl⟩ : syracuseStep 1515667 = 2273501) B2273501
theorem B1515683 : Blo 1514954 1515683 := bstep (se 1 (by rfl) ⟨1136762, by rfl⟩ : syracuseStep 1515683 = 2273525) B2273525
theorem B4374701 : Blo 1514954 4374701 := bstep (se 3 (by rfl) ⟨820256, by rfl⟩ : syracuseStep 4374701 = 1640513) B1640513
theorem B7282865 : Blo 1514954 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B1515699 : Blo 1514954 1515699 := bstep (se 1 (by rfl) ⟨1136774, by rfl⟩ : syracuseStep 1515699 = 2273549) B2273549
theorem B1515715 : Blo 1514954 1515715 := bstep (se 1 (by rfl) ⟨1136786, by rfl⟩ : syracuseStep 1515715 = 2273573) B2273573
theorem B1515731 : Blo 1514954 1515731 := bstep (se 1 (by rfl) ⟨1136798, by rfl⟩ : syracuseStep 1515731 = 2273597) B2273597
theorem B1515747 : Blo 1514954 1515747 := bstep (se 1 (by rfl) ⟨1136810, by rfl⟩ : syracuseStep 1515747 = 2273621) B2273621
theorem B1515763 : Blo 1514954 1515763 := bstep (se 1 (by rfl) ⟨1136822, by rfl⟩ : syracuseStep 1515763 = 2273645) B2273645
theorem B1515779 : Blo 1514954 1515779 := bstep (se 1 (by rfl) ⟨1136834, by rfl⟩ : syracuseStep 1515779 = 2273669) B2273669
theorem B4317457 : Blo 1514954 4317457 := bstep (se 2 (by rfl) ⟨1619046, by rfl⟩ : syracuseStep 4317457 = 3238093) B3238093
theorem B1515795 : Blo 1514954 1515795 := bstep (se 1 (by rfl) ⟨1136846, by rfl⟩ : syracuseStep 1515795 = 2273693) B2273693
theorem B1515811 : Blo 1514954 1515811 := bstep (se 1 (by rfl) ⟨1136858, by rfl⟩ : syracuseStep 1515811 = 2273717) B2273717
theorem B1515827 : Blo 1514954 1515827 := bstep (se 1 (by rfl) ⟨1136870, by rfl⟩ : syracuseStep 1515827 = 2273741) B2273741
theorem B1515843 : Blo 1514954 1515843 := bstep (se 1 (by rfl) ⟨1136882, by rfl⟩ : syracuseStep 1515843 = 2273765) B2273765
theorem B1515859 : Blo 1514954 1515859 := bstep (se 1 (by rfl) ⟨1136894, by rfl⟩ : syracuseStep 1515859 = 2273789) B2273789
theorem B1515875 : Blo 1514954 1515875 := bstep (se 1 (by rfl) ⟨1136906, by rfl⟩ : syracuseStep 1515875 = 2273813) B2273813
theorem B1515891 : Blo 1514954 1515891 := bstep (se 1 (by rfl) ⟨1136918, by rfl⟩ : syracuseStep 1515891 = 2273837) B2273837
theorem B1515907 : Blo 1514954 1515907 := bstep (se 1 (by rfl) ⟨1136930, by rfl⟩ : syracuseStep 1515907 = 2273861) B2273861
theorem B1515923 : Blo 1514954 1515923 := bstep (se 1 (by rfl) ⟨1136942, by rfl⟩ : syracuseStep 1515923 = 2273885) B2273885
theorem B1515939 : Blo 1514954 1515939 := bstep (se 1 (by rfl) ⟨1136954, by rfl⟩ : syracuseStep 1515939 = 2273909) B2273909
theorem B4317617 : Blo 1514954 4317617 := bstep (se 2 (by rfl) ⟨1619106, by rfl⟩ : syracuseStep 4317617 = 3238213) B3238213
theorem B1515955 : Blo 1514954 1515955 := bstep (se 1 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 1515955 = 2273933) B2273933
theorem B1515971 : Blo 1514954 1515971 := bstep (se 1 (by rfl) ⟨1136978, by rfl⟩ : syracuseStep 1515971 = 2273957) B2273957
theorem B4268483 : Blo 1514954 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B1515987 : Blo 1514954 1515987 := bstep (se 1 (by rfl) ⟨1136990, by rfl⟩ : syracuseStep 1515987 = 2273981) B2273981
theorem B1516003 : Blo 1514954 1516003 := bstep (se 1 (by rfl) ⟨1137002, by rfl⟩ : syracuseStep 1516003 = 2274005) B2274005
theorem B1917427 : Blo 1514954 1917427 := bstep (se 1 (by rfl) ⟨1438070, by rfl⟩ : syracuseStep 1917427 = 2876141) B2876141
theorem B1516019 : Blo 1514954 1516019 := bstep (se 1 (by rfl) ⟨1137014, by rfl⟩ : syracuseStep 1516019 = 2274029) B2274029
theorem B1704451 : Blo 1514954 1704451 := bstep (se 1 (by rfl) ⟨1278338, by rfl⟩ : syracuseStep 1704451 = 2556677) B2556677
theorem B1516035 : Blo 1514954 1516035 := bstep (se 1 (by rfl) ⟨1137026, by rfl⟩ : syracuseStep 1516035 = 2274053) B2274053
theorem B1516051 : Blo 1514954 1516051 := bstep (se 1 (by rfl) ⟨1137038, by rfl⟩ : syracuseStep 1516051 = 2274077) B2274077
theorem B1516067 : Blo 1514954 1516067 := bstep (se 1 (by rfl) ⟨1137050, by rfl⟩ : syracuseStep 1516067 = 2274101) B2274101
theorem B4317731 : Blo 1514954 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B1516083 : Blo 1514954 1516083 := bstep (se 1 (by rfl) ⟨1137062, by rfl⟩ : syracuseStep 1516083 = 2274125) B2274125
theorem B1516099 : Blo 1514954 1516099 := bstep (se 1 (by rfl) ⟨1137074, by rfl⟩ : syracuseStep 1516099 = 2274149) B2274149
theorem B8987213 : Blo 1514954 8987213 := bstep (se 3 (by rfl) ⟨1685102, by rfl⟩ : syracuseStep 8987213 = 3370205) B3370205
theorem B1917523 : Blo 1514954 1917523 := bstep (se 1 (by rfl) ⟨1438142, by rfl⟩ : syracuseStep 1917523 = 2876285) B2876285
theorem B1516115 : Blo 1514954 1516115 := bstep (se 1 (by rfl) ⟨1137086, by rfl⟩ : syracuseStep 1516115 = 2274173) B2274173
theorem B2556515 : Blo 1514954 2556515 := bstep (se 1 (by rfl) ⟨1917386, by rfl⟩ : syracuseStep 2556515 = 3834773) B3834773
theorem B1516131 : Blo 1514954 1516131 := bstep (se 1 (by rfl) ⟨1137098, by rfl⟩ : syracuseStep 1516131 = 2274197) B2274197
theorem B1516147 : Blo 1514954 1516147 := bstep (se 1 (by rfl) ⟨1137110, by rfl⟩ : syracuseStep 1516147 = 2274221) B2274221
theorem B1516163 : Blo 1514954 1516163 := bstep (se 1 (by rfl) ⟨1137122, by rfl⟩ : syracuseStep 1516163 = 2274245) B2274245
theorem B1704595 : Blo 1514954 1704595 := bstep (se 1 (by rfl) ⟨1278446, by rfl⟩ : syracuseStep 1704595 = 2556893) B2556893
theorem B1516179 : Blo 1514954 1516179 := bstep (se 1 (by rfl) ⟨1137134, by rfl⟩ : syracuseStep 1516179 = 2274269) B2274269
theorem B1729171 : Blo 1514954 1729171 := bstep (se 1 (by rfl) ⟨1296878, by rfl⟩ : syracuseStep 1729171 = 2593757) B2593757
theorem B1516195 : Blo 1514954 1516195 := bstep (se 1 (by rfl) ⟨1137146, by rfl⟩ : syracuseStep 1516195 = 2274293) B2274293
theorem B1516211 : Blo 1514954 1516211 := bstep (se 1 (by rfl) ⟨1137158, by rfl⟩ : syracuseStep 1516211 = 2274317) B2274317
theorem B1516227 : Blo 1514954 1516227 := bstep (se 1 (by rfl) ⟨1137170, by rfl⟩ : syracuseStep 1516227 = 2274341) B2274341
theorem B1516243 : Blo 1514954 1516243 := bstep (se 1 (by rfl) ⟨1137182, by rfl⟩ : syracuseStep 1516243 = 2274365) B2274365
theorem B2556643 : Blo 1514954 2556643 := bstep (se 1 (by rfl) ⟨1917482, by rfl⟩ : syracuseStep 2556643 = 3834965) B3834965
theorem B1516259 : Blo 1514954 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B1516275 : Blo 1514954 1516275 := bstep (se 1 (by rfl) ⟨1137206, by rfl⟩ : syracuseStep 1516275 = 2274413) B2274413
theorem B1516291 : Blo 1514954 1516291 := bstep (se 1 (by rfl) ⟨1137218, by rfl⟩ : syracuseStep 1516291 = 2274437) B2274437
theorem B1516307 : Blo 1514954 1516307 := bstep (se 1 (by rfl) ⟨1137230, by rfl⟩ : syracuseStep 1516307 = 2274461) B2274461
theorem B1704739 : Blo 1514954 1704739 := bstep (se 1 (by rfl) ⟨1278554, by rfl⟩ : syracuseStep 1704739 = 2557109) B2557109
theorem B5186339 : Blo 1514954 5186339 := bstep (se 1 (by rfl) ⟨3889754, by rfl⟩ : syracuseStep 5186339 = 7779509) B7779509
theorem B1516323 : Blo 1514954 1516323 := bstep (se 1 (by rfl) ⟨1137242, by rfl⟩ : syracuseStep 1516323 = 2274485) B2274485
theorem B1516339 : Blo 1514954 1516339 := bstep (se 1 (by rfl) ⟨1137254, by rfl⟩ : syracuseStep 1516339 = 2274509) B2274509
theorem B1516355 : Blo 1514954 1516355 := bstep (se 1 (by rfl) ⟨1137266, by rfl⟩ : syracuseStep 1516355 = 2274533) B2274533
theorem B1516371 : Blo 1514954 1516371 := bstep (se 1 (by rfl) ⟨1137278, by rfl⟩ : syracuseStep 1516371 = 2274557) B2274557
theorem B1516387 : Blo 1514954 1516387 := bstep (se 1 (by rfl) ⟨1137290, by rfl⟩ : syracuseStep 1516387 = 2274581) B2274581
theorem B2556785 : Blo 1514954 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B1516403 : Blo 1514954 1516403 := bstep (se 1 (by rfl) ⟨1137302, by rfl⟩ : syracuseStep 1516403 = 2274605) B2274605
theorem B1516419 : Blo 1514954 1516419 := bstep (se 1 (by rfl) ⟨1137314, by rfl⟩ : syracuseStep 1516419 = 2274629) B2274629
theorem B3408785 : Blo 1514954 3408785 := bstep (se 2 (by rfl) ⟨1278294, by rfl⟩ : syracuseStep 3408785 = 2556589) B2556589
theorem B3236753 : Blo 1514954 3236753 := bstep (se 2 (by rfl) ⟨1213782, by rfl⟩ : syracuseStep 3236753 = 2427565) B2427565
theorem B1516435 : Blo 1514954 1516435 := bstep (se 1 (by rfl) ⟨1137326, by rfl⟩ : syracuseStep 1516435 = 2274653) B2274653
theorem B3408803 : Blo 1514954 3408803 := bstep (se 1 (by rfl) ⟨2556602, by rfl⟩ : syracuseStep 3408803 = 5113205) B5113205
theorem B2876323 : Blo 1514954 2876323 := bstep (se 1 (by rfl) ⟨2157242, by rfl⟩ : syracuseStep 2876323 = 4314485) B4314485
theorem B1516451 : Blo 1514954 1516451 := bstep (se 1 (by rfl) ⟨1137338, by rfl⟩ : syracuseStep 1516451 = 2274677) B2274677
theorem B1704883 : Blo 1514954 1704883 := bstep (se 1 (by rfl) ⟨1278662, by rfl⟩ : syracuseStep 1704883 = 2557325) B2557325
theorem B1516467 : Blo 1514954 1516467 := bstep (se 1 (by rfl) ⟨1137350, by rfl⟩ : syracuseStep 1516467 = 2274701) B2274701
theorem B1516483 : Blo 1514954 1516483 := bstep (se 1 (by rfl) ⟨1137362, by rfl⟩ : syracuseStep 1516483 = 2274725) B2274725
theorem B1516499 : Blo 1514954 1516499 := bstep (se 1 (by rfl) ⟨1137374, by rfl⟩ : syracuseStep 1516499 = 2274749) B2274749
theorem B8750051 : Blo 1514954 8750051 := bstep (se 1 (by rfl) ⟨6562538, by rfl⟩ : syracuseStep 8750051 = 13125077) B13125077
theorem B1516515 : Blo 1514954 1516515 := bstep (se 1 (by rfl) ⟨1137386, by rfl⟩ : syracuseStep 1516515 = 2274773) B2274773
theorem B2556913 : Blo 1514954 2556913 := bstep (se 2 (by rfl) ⟨958842, by rfl⟩ : syracuseStep 2556913 = 1917685) B1917685
theorem B1516531 : Blo 1514954 1516531 := bstep (se 1 (by rfl) ⟨1137398, by rfl⟩ : syracuseStep 1516531 = 2274797) B2274797
theorem B1516547 : Blo 1514954 1516547 := bstep (se 1 (by rfl) ⟨1137410, by rfl⟩ : syracuseStep 1516547 = 2274821) B2274821
theorem B2556947 : Blo 1514954 2556947 := bstep (se 1 (by rfl) ⟨1917710, by rfl⟩ : syracuseStep 2556947 = 3835421) B3835421
theorem B1516563 : Blo 1514954 1516563 := bstep (se 1 (by rfl) ⟨1137422, by rfl⟩ : syracuseStep 1516563 = 2274845) B2274845
theorem B1516579 : Blo 1514954 1516579 := bstep (se 1 (by rfl) ⟨1137434, by rfl⟩ : syracuseStep 1516579 = 2274869) B2274869
theorem B1516595 : Blo 1514954 1516595 := bstep (se 1 (by rfl) ⟨1137446, by rfl⟩ : syracuseStep 1516595 = 2274893) B2274893
theorem B1918019 : Blo 1514954 1918019 := bstep (se 1 (by rfl) ⟨1438514, by rfl⟩ : syracuseStep 1918019 = 2877029) B2877029
theorem B1705027 : Blo 1514954 1705027 := bstep (se 1 (by rfl) ⟨1278770, by rfl⟩ : syracuseStep 1705027 = 2557541) B2557541
theorem B1516611 : Blo 1514954 1516611 := bstep (se 1 (by rfl) ⟨1137458, by rfl⟩ : syracuseStep 1516611 = 2274917) B2274917
theorem B7283789 : Blo 1514954 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B1516627 : Blo 1514954 1516627 := bstep (se 1 (by rfl) ⟨1137470, by rfl⟩ : syracuseStep 1516627 = 2274941) B2274941
theorem B14566499 : Blo 1514954 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B1516643 : Blo 1514954 1516643 := bstep (se 1 (by rfl) ⟨1137482, by rfl⟩ : syracuseStep 1516643 = 2274965) B2274965
theorem B17507441 : Blo 1514954 17507441 := bstep (se 2 (by rfl) ⟨6565290, by rfl⟩ : syracuseStep 17507441 = 13130581) B13130581
theorem B1516659 : Blo 1514954 1516659 := bstep (se 1 (by rfl) ⟨1137494, by rfl⟩ : syracuseStep 1516659 = 2274989) B2274989
theorem B1516675 : Blo 1514954 1516675 := bstep (se 1 (by rfl) ⟨1137506, by rfl⟩ : syracuseStep 1516675 = 2275013) B2275013
theorem B2557075 : Blo 1514954 2557075 := bstep (se 1 (by rfl) ⟨1917806, by rfl⟩ : syracuseStep 2557075 = 3835613) B3835613
theorem B1516691 : Blo 1514954 1516691 := bstep (se 1 (by rfl) ⟨1137518, by rfl⟩ : syracuseStep 1516691 = 2275037) B2275037
theorem B1516707 : Blo 1514954 1516707 := bstep (se 1 (by rfl) ⟨1137530, by rfl⟩ : syracuseStep 1516707 = 2275061) B2275061
theorem B3409073 : Blo 1514954 3409073 := bstep (se 2 (by rfl) ⟨1278402, by rfl⟩ : syracuseStep 3409073 = 2556805) B2556805
theorem B1516723 : Blo 1514954 1516723 := bstep (se 1 (by rfl) ⟨1137542, by rfl⟩ : syracuseStep 1516723 = 2275085) B2275085
theorem B3409091 : Blo 1514954 3409091 := bstep (se 1 (by rfl) ⟨2556818, by rfl⟩ : syracuseStep 3409091 = 5113637) B5113637
theorem B1516739 : Blo 1514954 1516739 := bstep (se 1 (by rfl) ⟨1137554, by rfl⟩ : syracuseStep 1516739 = 2275109) B2275109
theorem B1705171 : Blo 1514954 1705171 := bstep (se 1 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 1705171 = 2557757) B2557757
theorem B1516755 : Blo 1514954 1516755 := bstep (se 1 (by rfl) ⟨1137566, by rfl⟩ : syracuseStep 1516755 = 2275133) B2275133
theorem B1516771 : Blo 1514954 1516771 := bstep (se 1 (by rfl) ⟨1137578, by rfl⟩ : syracuseStep 1516771 = 2275157) B2275157
theorem B1516787 : Blo 1514954 1516787 := bstep (se 1 (by rfl) ⟨1137590, by rfl⟩ : syracuseStep 1516787 = 2275181) B2275181
theorem B1516803 : Blo 1514954 1516803 := bstep (se 1 (by rfl) ⟨1137602, by rfl⟩ : syracuseStep 1516803 = 2275205) B2275205
theorem B6472973 : Blo 1514954 6472973 := bstep (se 3 (by rfl) ⟨1213682, by rfl⟩ : syracuseStep 6472973 = 2427365) B2427365
theorem B1516819 : Blo 1514954 1516819 := bstep (se 1 (by rfl) ⟨1137614, by rfl⟩ : syracuseStep 1516819 = 2275229) B2275229
theorem B2557217 : Blo 1514954 2557217 := bstep (se 2 (by rfl) ⟨958956, by rfl⟩ : syracuseStep 2557217 = 1917913) B1917913
theorem B1516835 : Blo 1514954 1516835 := bstep (se 1 (by rfl) ⟨1137626, by rfl⟩ : syracuseStep 1516835 = 2275253) B2275253
theorem B1516851 : Blo 1514954 1516851 := bstep (se 1 (by rfl) ⟨1137638, by rfl⟩ : syracuseStep 1516851 = 2275277) B2275277
theorem B1516867 : Blo 1514954 1516867 := bstep (se 1 (by rfl) ⟨1137650, by rfl⟩ : syracuseStep 1516867 = 2275301) B2275301
theorem B1516883 : Blo 1514954 1516883 := bstep (se 1 (by rfl) ⟨1137662, by rfl⟩ : syracuseStep 1516883 = 2275325) B2275325
theorem B2876771 : Blo 1514954 2876771 := bstep (se 1 (by rfl) ⟨2157578, by rfl⟩ : syracuseStep 2876771 = 4315157) B4315157
theorem B1705315 : Blo 1514954 1705315 := bstep (se 1 (by rfl) ⟨1278986, by rfl⟩ : syracuseStep 1705315 = 2557973) B2557973
theorem B1516899 : Blo 1514954 1516899 := bstep (se 1 (by rfl) ⟨1137674, by rfl⟩ : syracuseStep 1516899 = 2275349) B2275349
theorem B1516915 : Blo 1514954 1516915 := bstep (se 1 (by rfl) ⟨1137686, by rfl⟩ : syracuseStep 1516915 = 2275373) B2275373
theorem B3114371 : Blo 1514954 3114371 := bstep (se 1 (by rfl) ⟨2335778, by rfl⟩ : syracuseStep 3114371 = 4671557) B4671557
theorem B1516931 : Blo 1514954 1516931 := bstep (se 1 (by rfl) ⟨1137698, by rfl⟩ : syracuseStep 1516931 = 2275397) B2275397
theorem B5752205 : Blo 1514954 5752205 := bstep (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) B2157077
theorem B1516947 : Blo 1514954 1516947 := bstep (se 1 (by rfl) ⟨1137710, by rfl⟩ : syracuseStep 1516947 = 2275421) B2275421
theorem B2557345 : Blo 1514954 2557345 := bstep (se 2 (by rfl) ⟨959004, by rfl⟩ : syracuseStep 2557345 = 1918009) B1918009
theorem B2557379 : Blo 1514954 2557379 := bstep (se 1 (by rfl) ⟨1918034, by rfl⟩ : syracuseStep 2557379 = 3836069) B3836069
theorem B3409361 : Blo 1514954 3409361 := bstep (se 2 (by rfl) ⟨1278510, by rfl⟩ : syracuseStep 3409361 = 2557021) B2557021
theorem B3409379 : Blo 1514954 3409379 := bstep (se 1 (by rfl) ⟨2557034, by rfl⟩ : syracuseStep 3409379 = 5114069) B5114069
theorem B1705459 : Blo 1514954 1705459 := bstep (se 1 (by rfl) ⟨1279094, by rfl⟩ : syracuseStep 1705459 = 2558189) B2558189
theorem B4318733 : Blo 1514954 4318733 := bstep (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) B1619525
theorem B7489037 : Blo 1514954 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B2557507 : Blo 1514954 2557507 := bstep (se 1 (by rfl) ⟨1918130, by rfl⟩ : syracuseStep 2557507 = 3836261) B3836261
theorem B5113421 : Blo 1514954 5113421 := bstep (se 3 (by rfl) ⟨958766, by rfl⟩ : syracuseStep 5113421 = 1917533) B1917533
theorem B4859473 : Blo 1514954 4859473 := bstep (se 2 (by rfl) ⟨1822302, by rfl⟩ : syracuseStep 4859473 = 3644605) B3644605
theorem B11511395 : Blo 1514954 11511395 := bstep (se 1 (by rfl) ⟨8633546, by rfl⟩ : syracuseStep 11511395 = 17267093) B17267093
theorem B5834339 : Blo 1514954 5834339 := bstep (se 1 (by rfl) ⟨4375754, by rfl⟩ : syracuseStep 5834339 = 8751509) B8751509
theorem B3327601 : Blo 1514954 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B5113475 : Blo 1514954 5113475 := bstep (se 1 (by rfl) ⟨3835106, by rfl⟩ : syracuseStep 5113475 = 7670213) B7670213
theorem B2877059 : Blo 1514954 2877059 := bstep (se 1 (by rfl) ⟨2157794, by rfl⟩ : syracuseStep 2877059 = 4315589) B4315589
theorem B2025091 : Blo 1514954 2025091 := bstep (se 1 (by rfl) ⟨1518818, by rfl⟩ : syracuseStep 2025091 = 3037637) B3037637
theorem B1705603 : Blo 1514954 1705603 := bstep (se 1 (by rfl) ⟨1279202, by rfl⟩ : syracuseStep 1705603 = 2558405) B2558405
theorem B4318915 : Blo 1514954 4318915 := bstep (se 1 (by rfl) ⟨3239186, by rfl⟩ : syracuseStep 4318915 = 6478373) B6478373
theorem B2557649 : Blo 1514954 2557649 := bstep (se 2 (by rfl) ⟨959118, by rfl⟩ : syracuseStep 2557649 = 1918237) B1918237
theorem B3835633 : Blo 1514954 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B3409649 : Blo 1514954 3409649 := bstep (se 2 (by rfl) ⟨1278618, by rfl⟩ : syracuseStep 3409649 = 2557237) B2557237
theorem B3409667 : Blo 1514954 3409667 := bstep (se 1 (by rfl) ⟨2557250, by rfl⟩ : syracuseStep 3409667 = 5114501) B5114501
theorem B1918723 : Blo 1514954 1918723 := bstep (se 1 (by rfl) ⟨1439042, by rfl⟩ : syracuseStep 1918723 = 2878085) B2878085
theorem B9717509 : Blo 1514954 9717509 := bstep (se 4 (by rfl) ⟨911016, by rfl⟩ : syracuseStep 9717509 = 1822033) B1822033
theorem B4859651 : Blo 1514954 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B1705747 : Blo 1514954 1705747 := bstep (se 1 (by rfl) ⟨1279310, by rfl⟩ : syracuseStep 1705747 = 2558621) B2558621
theorem B2557777 : Blo 1514954 2557777 := bstep (se 2 (by rfl) ⟨959166, by rfl⟩ : syracuseStep 2557777 = 1918333) B1918333
theorem B1918819 : Blo 1514954 1918819 := bstep (se 1 (by rfl) ⟨1439114, by rfl⟩ : syracuseStep 1918819 = 2878229) B2878229
theorem B4319075 : Blo 1514954 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B2557811 : Blo 1514954 2557811 := bstep (se 1 (by rfl) ⟨1918358, by rfl⟩ : syracuseStep 2557811 = 3836717) B3836717
theorem B5113745 : Blo 1514954 5113745 := bstep (se 2 (by rfl) ⟨1917654, by rfl⟩ : syracuseStep 5113745 = 3835309) B3835309
theorem B1705891 : Blo 1514954 1705891 := bstep (se 1 (by rfl) ⟨1279418, by rfl⟩ : syracuseStep 1705891 = 2558837) B2558837
theorem B1820659 : Blo 1514954 1820659 := bstep (se 1 (by rfl) ⟨1365494, by rfl⟩ : syracuseStep 1820659 = 2730989) B2730989
theorem B2557939 : Blo 1514954 2557939 := bstep (se 1 (by rfl) ⟨1918454, by rfl⟩ : syracuseStep 2557939 = 3836909) B3836909
theorem B3835907 : Blo 1514954 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B3409937 : Blo 1514954 3409937 := bstep (se 2 (by rfl) ⟨1278726, by rfl⟩ : syracuseStep 3409937 = 2557453) B2557453
theorem B3409955 : Blo 1514954 3409955 := bstep (se 1 (by rfl) ⟨2557466, by rfl⟩ : syracuseStep 3409955 = 5114933) B5114933
theorem B1706035 : Blo 1514954 1706035 := bstep (se 1 (by rfl) ⟨1279526, by rfl⟩ : syracuseStep 1706035 = 2559053) B2559053
theorem B1820755 : Blo 1514954 1820755 := bstep (se 1 (by rfl) ⟨1365566, by rfl⟩ : syracuseStep 1820755 = 2731133) B2731133
theorem B147449969 : Blo 1514954 147449969 := bstep (se 2 (by rfl) ⟨55293738, by rfl⟩ : syracuseStep 147449969 = 110587477) B110587477
theorem B1820803 : Blo 1514954 1820803 := bstep (se 1 (by rfl) ⟨1365602, by rfl⟩ : syracuseStep 1820803 = 2731205) B2731205
theorem B2558081 : Blo 1514954 2558081 := bstep (se 2 (by rfl) ⟨959280, by rfl⟩ : syracuseStep 2558081 = 1918561) B1918561
theorem B3238051 : Blo 1514954 3238051 := bstep (se 1 (by rfl) ⟨2428538, by rfl⟩ : syracuseStep 3238051 = 4857077) B4857077
theorem B3836099 : Blo 1514954 3836099 := bstep (se 1 (by rfl) ⟨2877074, by rfl⟩ : syracuseStep 3836099 = 5754149) B5754149
theorem B1706179 : Blo 1514954 1706179 := bstep (se 1 (by rfl) ⟨1279634, by rfl⟩ : syracuseStep 1706179 = 2559269) B2559269
theorem B23668933 : Blo 1514954 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B2558209 : Blo 1514954 2558209 := bstep (se 2 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 2558209 = 1918657) B1918657
theorem B2427155 : Blo 1514954 2427155 := bstep (se 1 (by rfl) ⟨1820366, by rfl⟩ : syracuseStep 2427155 = 3640733) B3640733
theorem B7670051 : Blo 1514954 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B2558243 : Blo 1514954 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B3410225 : Blo 1514954 3410225 := bstep (se 2 (by rfl) ⟨1278834, by rfl⟩ : syracuseStep 3410225 = 2557669) B2557669
theorem B3410243 : Blo 1514954 3410243 := bstep (se 1 (by rfl) ⟨2557682, by rfl⟩ : syracuseStep 3410243 = 5115365) B5115365
theorem B1919315 : Blo 1514954 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B1706323 : Blo 1514954 1706323 := bstep (se 1 (by rfl) ⟨1279742, by rfl⟩ : syracuseStep 1706323 = 2559485) B2559485
theorem B2558371 : Blo 1514954 2558371 := bstep (se 1 (by rfl) ⟨1918778, by rfl⟩ : syracuseStep 2558371 = 3837557) B3837557
theorem B5114285 : Blo 1514954 5114285 := bstep (se 3 (by rfl) ⟨958928, by rfl⟩ : syracuseStep 5114285 = 1917857) B1917857
theorem B5114339 : Blo 1514954 5114339 := bstep (se 1 (by rfl) ⟨3835754, by rfl⟩ : syracuseStep 5114339 = 7671509) B7671509
theorem B1706467 : Blo 1514954 1706467 := bstep (se 1 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 1706467 = 2559701) B2559701
theorem B2157043 : Blo 1514954 2157043 := bstep (se 1 (by rfl) ⟨1617782, by rfl⟩ : syracuseStep 2157043 = 3235565) B3235565
theorem B3459601 : Blo 1514954 3459601 := bstep (se 2 (by rfl) ⟨1297350, by rfl⟩ : syracuseStep 3459601 = 2594701) B2594701
theorem B2878001 : Blo 1514954 2878001 := bstep (se 2 (by rfl) ⟨1079250, by rfl⟩ : syracuseStep 2878001 = 2158501) B2158501
theorem B2558513 : Blo 1514954 2558513 := bstep (se 2 (by rfl) ⟨959442, by rfl⟩ : syracuseStep 2558513 = 1918885) B1918885
theorem B3410513 : Blo 1514954 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B3410531 : Blo 1514954 3410531 := bstep (se 1 (by rfl) ⟨2557898, by rfl⟩ : syracuseStep 3410531 = 5115797) B5115797
theorem B2558641 : Blo 1514954 2558641 := bstep (se 2 (by rfl) ⟨959490, by rfl⟩ : syracuseStep 2558641 = 1918981) B1918981
theorem B2558675 : Blo 1514954 2558675 := bstep (se 1 (by rfl) ⟨1919006, by rfl⟩ : syracuseStep 2558675 = 3838013) B3838013
theorem B3640049 : Blo 1514954 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B5114609 : Blo 1514954 5114609 := bstep (se 2 (by rfl) ⟨1917978, by rfl⟩ : syracuseStep 5114609 = 3835957) B3835957
theorem B2591507 : Blo 1514954 2591507 := bstep (se 1 (by rfl) ⟨1943630, by rfl⟩ : syracuseStep 2591507 = 3887261) B3887261
theorem B3156803 : Blo 1514954 3156803 := bstep (se 1 (by rfl) ⟨2367602, by rfl⟩ : syracuseStep 3156803 = 4735205) B4735205
theorem B2558803 : Blo 1514954 2558803 := bstep (se 1 (by rfl) ⟨1919102, by rfl⟩ : syracuseStep 2558803 = 3838205) B3838205
theorem B3410801 : Blo 1514954 3410801 := bstep (se 2 (by rfl) ⟨1279050, by rfl⟩ : syracuseStep 3410801 = 2558101) B2558101
theorem B3410819 : Blo 1514954 3410819 := bstep (se 1 (by rfl) ⟨2558114, by rfl⟩ : syracuseStep 3410819 = 5116229) B5116229
theorem B2304929 : Blo 1514954 2304929 := bstep (se 2 (by rfl) ⟨864348, by rfl⟩ : syracuseStep 2304929 = 1728697) B1728697
theorem B3640241 : Blo 1514954 3640241 := bstep (se 2 (by rfl) ⟨1365090, by rfl⟩ : syracuseStep 3640241 = 2730181) B2730181
theorem B2157521 : Blo 1514954 2157521 := bstep (se 2 (by rfl) ⟨809070, by rfl⟩ : syracuseStep 2157521 = 1618141) B1618141
theorem B2558945 : Blo 1514954 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B7678961 : Blo 1514954 7678961 := bstep (se 2 (by rfl) ⟨2879610, by rfl⟩ : syracuseStep 7678961 = 5759221) B5759221
theorem B2157635 : Blo 1514954 2157635 := bstep (se 1 (by rfl) ⟨1618226, by rfl⟩ : syracuseStep 2157635 = 3236453) B3236453
theorem B7670861 : Blo 1514954 7670861 := bstep (se 3 (by rfl) ⟨1438286, by rfl⟩ : syracuseStep 7670861 = 2876573) B2876573
theorem B2559073 : Blo 1514954 2559073 := bstep (se 2 (by rfl) ⟨959652, by rfl⟩ : syracuseStep 2559073 = 1919305) B1919305
theorem B3837041 : Blo 1514954 3837041 := bstep (se 2 (by rfl) ⟨1438890, by rfl⟩ : syracuseStep 3837041 = 2877781) B2877781
theorem B2559107 : Blo 1514954 2559107 := bstep (se 1 (by rfl) ⟨1919330, by rfl⟩ : syracuseStep 2559107 = 3838661) B3838661
theorem B3411089 : Blo 1514954 3411089 := bstep (se 2 (by rfl) ⟨1279158, by rfl⟩ : syracuseStep 3411089 = 2558317) B2558317
theorem B2157715 : Blo 1514954 2157715 := bstep (se 1 (by rfl) ⟨1618286, by rfl⟩ : syracuseStep 2157715 = 3236573) B3236573
theorem B3837091 : Blo 1514954 3837091 := bstep (se 1 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 3837091 = 5755637) B5755637
theorem B3411107 : Blo 1514954 3411107 := bstep (se 1 (by rfl) ⟨2558330, by rfl⟩ : syracuseStep 3411107 = 5116661) B5116661
theorem B2272433 : Blo 1514954 2272433 := bstep (se 2 (by rfl) ⟨852162, by rfl⟩ : syracuseStep 2272433 = 1704325) B1704325
theorem B2272451 : Blo 1514954 2272451 := bstep (se 1 (by rfl) ⟨1704338, by rfl⟩ : syracuseStep 2272451 = 3408677) B3408677
theorem B2272481 : Blo 1514954 2272481 := bstep (se 2 (by rfl) ⟨852180, by rfl⟩ : syracuseStep 2272481 = 1704361) B1704361
theorem B2272499 : Blo 1514954 2272499 := bstep (se 1 (by rfl) ⟨1704374, by rfl⟩ : syracuseStep 2272499 = 3408749) B3408749
theorem B2428147 : Blo 1514954 2428147 := bstep (se 1 (by rfl) ⟨1821110, by rfl⟩ : syracuseStep 2428147 = 3642221) B3642221
theorem B2559235 : Blo 1514954 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B5115149 : Blo 1514954 5115149 := bstep (se 3 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 5115149 = 1918181) B1918181
theorem B2272529 : Blo 1514954 2272529 := bstep (se 2 (by rfl) ⟨852198, by rfl⟩ : syracuseStep 2272529 = 1704397) B1704397
theorem B2272547 : Blo 1514954 2272547 := bstep (se 1 (by rfl) ⟨1704410, by rfl⟩ : syracuseStep 2272547 = 3408821) B3408821
theorem B3837233 : Blo 1514954 3837233 := bstep (se 2 (by rfl) ⟨1438962, by rfl⟩ : syracuseStep 3837233 = 2877925) B2877925
theorem B2272577 : Blo 1514954 2272577 := bstep (se 2 (by rfl) ⟨852216, by rfl⟩ : syracuseStep 2272577 = 1704433) B1704433
theorem B5115203 : Blo 1514954 5115203 := bstep (se 1 (by rfl) ⟨3836402, by rfl⟩ : syracuseStep 5115203 = 7672805) B7672805
theorem B1822019 : Blo 1514954 1822019 := bstep (se 1 (by rfl) ⟨1366514, by rfl⟩ : syracuseStep 1822019 = 2733029) B2733029
theorem B2272595 : Blo 1514954 2272595 := bstep (se 1 (by rfl) ⟨1704446, by rfl⟩ : syracuseStep 2272595 = 3408893) B3408893
theorem B2272625 : Blo 1514954 2272625 := bstep (se 2 (by rfl) ⟨852234, by rfl⟩ : syracuseStep 2272625 = 1704469) B1704469
theorem B3239281 : Blo 1514954 3239281 := bstep (se 2 (by rfl) ⟨1214730, by rfl⟩ : syracuseStep 3239281 = 2429461) B2429461
theorem B2272643 : Blo 1514954 2272643 := bstep (se 1 (by rfl) ⟨1704482, by rfl⟩ : syracuseStep 2272643 = 3408965) B3408965
theorem B2559377 : Blo 1514954 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B2305427 : Blo 1514954 2305427 := bstep (se 1 (by rfl) ⟨1729070, by rfl⟩ : syracuseStep 2305427 = 3458141) B3458141
theorem B2272673 : Blo 1514954 2272673 := bstep (se 2 (by rfl) ⟨852252, by rfl⟩ : syracuseStep 2272673 = 1704505) B1704505
theorem B3411377 : Blo 1514954 3411377 := bstep (se 2 (by rfl) ⟨1279266, by rfl⟩ : syracuseStep 3411377 = 2558533) B2558533
theorem B2878897 : Blo 1514954 2878897 := bstep (se 2 (by rfl) ⟨1079586, by rfl⟩ : syracuseStep 2878897 = 2159173) B2159173
theorem B2272691 : Blo 1514954 2272691 := bstep (se 1 (by rfl) ⟨1704518, by rfl⟩ : syracuseStep 2272691 = 3409037) B3409037
theorem B2305459 : Blo 1514954 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B3411395 : Blo 1514954 3411395 := bstep (se 1 (by rfl) ⟨2558546, by rfl⟩ : syracuseStep 3411395 = 5117093) B5117093
theorem B3116483 : Blo 1514954 3116483 := bstep (se 1 (by rfl) ⟨2337362, by rfl⟩ : syracuseStep 3116483 = 4674725) B4674725
theorem B2272721 : Blo 1514954 2272721 := bstep (se 2 (by rfl) ⟨852270, by rfl⟩ : syracuseStep 2272721 = 1704541) B1704541
theorem B2272739 : Blo 1514954 2272739 := bstep (se 1 (by rfl) ⟨1704554, by rfl⟩ : syracuseStep 2272739 = 3409109) B3409109
theorem B2272769 : Blo 1514954 2272769 := bstep (se 2 (by rfl) ⟨852288, by rfl⟩ : syracuseStep 2272769 = 1704577) B1704577
theorem B2559505 : Blo 1514954 2559505 := bstep (se 2 (by rfl) ⟨959814, by rfl⟩ : syracuseStep 2559505 = 1919629) B1919629
theorem B2272787 : Blo 1514954 2272787 := bstep (se 1 (by rfl) ⟨1704590, by rfl⟩ : syracuseStep 2272787 = 3409181) B3409181
theorem B2272817 : Blo 1514954 2272817 := bstep (se 2 (by rfl) ⟨852306, by rfl⟩ : syracuseStep 2272817 = 1704613) B1704613
theorem B2559539 : Blo 1514954 2559539 := bstep (se 1 (by rfl) ⟨1919654, by rfl⟩ : syracuseStep 2559539 = 3839309) B3839309
theorem B2272835 : Blo 1514954 2272835 := bstep (se 1 (by rfl) ⟨1704626, by rfl⟩ : syracuseStep 2272835 = 3409253) B3409253
theorem B5115473 : Blo 1514954 5115473 := bstep (se 2 (by rfl) ⟨1918302, by rfl⟩ : syracuseStep 5115473 = 3836605) B3836605
theorem B2879057 : Blo 1514954 2879057 := bstep (se 2 (by rfl) ⟨1079646, by rfl⟩ : syracuseStep 2879057 = 2159293) B2159293
theorem B2272865 : Blo 1514954 2272865 := bstep (se 2 (by rfl) ⟨852324, by rfl⟩ : syracuseStep 2272865 = 1704649) B1704649
theorem B2272883 : Blo 1514954 2272883 := bstep (se 1 (by rfl) ⟨1704662, by rfl⟩ : syracuseStep 2272883 = 3409325) B3409325
theorem B3640963 : Blo 1514954 3640963 := bstep (se 1 (by rfl) ⟨2730722, by rfl⟩ : syracuseStep 3640963 = 5461445) B5461445
theorem B2272913 : Blo 1514954 2272913 := bstep (se 2 (by rfl) ⟨852342, by rfl⟩ : syracuseStep 2272913 = 1704685) B1704685
theorem B1945235 : Blo 1514954 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B2272931 : Blo 1514954 2272931 := bstep (se 1 (by rfl) ⟨1704698, by rfl⟩ : syracuseStep 2272931 = 3409397) B3409397
theorem B2559667 : Blo 1514954 2559667 := bstep (se 1 (by rfl) ⟨1919750, by rfl⟩ : syracuseStep 2559667 = 3839501) B3839501
theorem B2272961 : Blo 1514954 2272961 := bstep (se 2 (by rfl) ⟨852360, by rfl⟩ : syracuseStep 2272961 = 1704721) B1704721
theorem B2158273 : Blo 1514954 2158273 := bstep (se 2 (by rfl) ⟨809352, by rfl⟩ : syracuseStep 2158273 = 1618705) B1618705
theorem B3411665 : Blo 1514954 3411665 := bstep (se 2 (by rfl) ⟨1279374, by rfl⟩ : syracuseStep 3411665 = 2558749) B2558749
theorem B2272979 : Blo 1514954 2272979 := bstep (se 1 (by rfl) ⟨1704734, by rfl⟩ : syracuseStep 2272979 = 3409469) B3409469
theorem B3411683 : Blo 1514954 3411683 := bstep (se 1 (by rfl) ⟨2558762, by rfl⟩ : syracuseStep 3411683 = 5117525) B5117525
theorem B2273009 : Blo 1514954 2273009 := bstep (se 2 (by rfl) ⟨852378, by rfl⟩ : syracuseStep 2273009 = 1704757) B1704757
theorem B2273027 : Blo 1514954 2273027 := bstep (se 1 (by rfl) ⟨1704770, by rfl⟩ : syracuseStep 2273027 = 3409541) B3409541
theorem B2273057 : Blo 1514954 2273057 := bstep (se 2 (by rfl) ⟨852396, by rfl⟩ : syracuseStep 2273057 = 1704793) B1704793
theorem B2273075 : Blo 1514954 2273075 := bstep (se 1 (by rfl) ⟨1704806, by rfl⟩ : syracuseStep 2273075 = 3409613) B3409613
theorem B2559809 : Blo 1514954 2559809 := bstep (se 2 (by rfl) ⟨959928, by rfl⟩ : syracuseStep 2559809 = 1919857) B1919857
theorem B8638285 : Blo 1514954 8638285 := bstep (se 3 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 8638285 = 3239357) B3239357
theorem B2273105 : Blo 1514954 2273105 := bstep (se 2 (by rfl) ⟨852414, by rfl⟩ : syracuseStep 2273105 = 1704829) B1704829
theorem B4853603 : Blo 1514954 4853603 := bstep (se 1 (by rfl) ⟨3640202, by rfl⟩ : syracuseStep 4853603 = 7280405) B7280405
theorem B2273123 : Blo 1514954 2273123 := bstep (se 1 (by rfl) ⟨1704842, by rfl⟩ : syracuseStep 2273123 = 3409685) B3409685
theorem B2273153 : Blo 1514954 2273153 := bstep (se 2 (by rfl) ⟨852432, by rfl⟩ : syracuseStep 2273153 = 1704865) B1704865
theorem B4099985 : Blo 1514954 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B2273171 : Blo 1514954 2273171 := bstep (se 1 (by rfl) ⟨1704878, by rfl⟩ : syracuseStep 2273171 = 3409757) B3409757
theorem B2461601 : Blo 1514954 2461601 := bstep (se 2 (by rfl) ⟨923100, by rfl⟩ : syracuseStep 2461601 = 1846201) B1846201
theorem B2273201 : Blo 1514954 2273201 := bstep (se 2 (by rfl) ⟨852450, by rfl⟩ : syracuseStep 2273201 = 1704901) B1704901
theorem B2273219 : Blo 1514954 2273219 := bstep (se 1 (by rfl) ⟨1704914, by rfl⟩ : syracuseStep 2273219 = 3409829) B3409829
theorem B2273249 : Blo 1514954 2273249 := bstep (se 2 (by rfl) ⟨852468, by rfl⟩ : syracuseStep 2273249 = 1704937) B1704937
theorem B2879459 : Blo 1514954 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B3411953 : Blo 1514954 3411953 := bstep (se 2 (by rfl) ⟨1279482, by rfl⟩ : syracuseStep 3411953 = 2558965) B2558965
theorem B2273267 : Blo 1514954 2273267 := bstep (se 1 (by rfl) ⟨1704950, by rfl⟩ : syracuseStep 2273267 = 3409901) B3409901
theorem B3411971 : Blo 1514954 3411971 := bstep (se 1 (by rfl) ⟨2558978, by rfl⟩ : syracuseStep 3411971 = 5117957) B5117957
theorem B2273297 : Blo 1514954 2273297 := bstep (se 2 (by rfl) ⟨852486, by rfl⟩ : syracuseStep 2273297 = 1704973) B1704973
theorem B2273315 : Blo 1514954 2273315 := bstep (se 1 (by rfl) ⟨1704986, by rfl⟩ : syracuseStep 2273315 = 3409973) B3409973
theorem B2273345 : Blo 1514954 2273345 := bstep (se 2 (by rfl) ⟨852504, by rfl⟩ : syracuseStep 2273345 = 1705009) B1705009
theorem B3887185 : Blo 1514954 3887185 := bstep (se 2 (by rfl) ⟨1457694, by rfl⟩ : syracuseStep 3887185 = 2915389) B2915389
theorem B2273363 : Blo 1514954 2273363 := bstep (se 1 (by rfl) ⟨1705022, by rfl⟩ : syracuseStep 2273363 = 3410045) B3410045
theorem B5116013 : Blo 1514954 5116013 := bstep (se 3 (by rfl) ⟨959252, by rfl⟩ : syracuseStep 5116013 = 1918505) B1918505
theorem B2273393 : Blo 1514954 2273393 := bstep (se 2 (by rfl) ⟨852522, by rfl⟩ : syracuseStep 2273393 = 1705045) B1705045
theorem B2592881 : Blo 1514954 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B2429057 : Blo 1514954 2429057 := bstep (se 2 (by rfl) ⟨910896, by rfl⟩ : syracuseStep 2429057 = 1821793) B1821793
theorem B2273411 : Blo 1514954 2273411 := bstep (se 1 (by rfl) ⟨1705058, by rfl⟩ : syracuseStep 2273411 = 3410117) B3410117
theorem B2273441 : Blo 1514954 2273441 := bstep (se 2 (by rfl) ⟨852540, by rfl⟩ : syracuseStep 2273441 = 1705081) B1705081
theorem B5460131 : Blo 1514954 5460131 := bstep (se 1 (by rfl) ⟨4095098, by rfl⟩ : syracuseStep 5460131 = 8190197) B8190197
theorem B5116067 : Blo 1514954 5116067 := bstep (se 1 (by rfl) ⟨3837050, by rfl⟩ : syracuseStep 5116067 = 7674101) B7674101
theorem B2273459 : Blo 1514954 2273459 := bstep (se 1 (by rfl) ⟨1705094, by rfl⟩ : syracuseStep 2273459 = 3410189) B3410189
theorem B2273489 : Blo 1514954 2273489 := bstep (se 2 (by rfl) ⟨852558, by rfl⟩ : syracuseStep 2273489 = 1705117) B1705117
theorem B3281123 : Blo 1514954 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B2273507 : Blo 1514954 2273507 := bstep (se 1 (by rfl) ⟨1705130, by rfl⟩ : syracuseStep 2273507 = 3410261) B3410261
theorem B4854001 : Blo 1514954 4854001 := bstep (se 2 (by rfl) ⟨1820250, by rfl⟩ : syracuseStep 4854001 = 3640501) B3640501
theorem B5755121 : Blo 1514954 5755121 := bstep (se 2 (by rfl) ⟨2158170, by rfl⟩ : syracuseStep 5755121 = 4316341) B4316341
theorem B2273537 : Blo 1514954 2273537 := bstep (se 2 (by rfl) ⟨852576, by rfl⟩ : syracuseStep 2273537 = 1705153) B1705153
theorem B2429185 : Blo 1514954 2429185 := bstep (se 2 (by rfl) ⟨910944, by rfl⟩ : syracuseStep 2429185 = 1821889) B1821889
theorem B3838225 : Blo 1514954 3838225 := bstep (se 2 (by rfl) ⟨1439334, by rfl⟩ : syracuseStep 3838225 = 2878669) B2878669
theorem B3412241 : Blo 1514954 3412241 := bstep (se 2 (by rfl) ⟨1279590, by rfl⟩ : syracuseStep 3412241 = 2559181) B2559181
theorem B2273555 : Blo 1514954 2273555 := bstep (se 1 (by rfl) ⟨1705166, by rfl⟩ : syracuseStep 2273555 = 3410333) B3410333
theorem B3412259 : Blo 1514954 3412259 := bstep (se 1 (by rfl) ⟨2559194, by rfl⟩ : syracuseStep 3412259 = 5118389) B5118389
theorem B2273585 : Blo 1514954 2273585 := bstep (se 2 (by rfl) ⟨852594, by rfl⟩ : syracuseStep 2273585 = 1705189) B1705189
theorem B2273603 : Blo 1514954 2273603 := bstep (se 1 (by rfl) ⟨1705202, by rfl⟩ : syracuseStep 2273603 = 3410405) B3410405
theorem B2273633 : Blo 1514954 2273633 := bstep (se 2 (by rfl) ⟨852612, by rfl⟩ : syracuseStep 2273633 = 1705225) B1705225
theorem B4854115 : Blo 1514954 4854115 := bstep (se 1 (by rfl) ⟨3640586, by rfl⟩ : syracuseStep 4854115 = 7281173) B7281173
theorem B2273651 : Blo 1514954 2273651 := bstep (se 1 (by rfl) ⟨1705238, by rfl⟩ : syracuseStep 2273651 = 3410477) B3410477
theorem B2158979 : Blo 1514954 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B2273681 : Blo 1514954 2273681 := bstep (se 2 (by rfl) ⟨852630, by rfl⟩ : syracuseStep 2273681 = 1705261) B1705261
theorem B2273699 : Blo 1514954 2273699 := bstep (se 1 (by rfl) ⟨1705274, by rfl⟩ : syracuseStep 2273699 = 3410549) B3410549
theorem B5116337 : Blo 1514954 5116337 := bstep (se 2 (by rfl) ⟨1918626, by rfl⟩ : syracuseStep 5116337 = 3837253) B3837253
theorem B2273729 : Blo 1514954 2273729 := bstep (se 2 (by rfl) ⟨852648, by rfl⟩ : syracuseStep 2273729 = 1705297) B1705297
theorem B2273747 : Blo 1514954 2273747 := bstep (se 1 (by rfl) ⟨1705310, by rfl⟩ : syracuseStep 2273747 = 3410621) B3410621
theorem B10367473 : Blo 1514954 10367473 := bstep (se 2 (by rfl) ⟨3887802, by rfl⟩ : syracuseStep 10367473 = 7775605) B7775605
theorem B2273777 : Blo 1514954 2273777 := bstep (se 2 (by rfl) ⟨852666, by rfl⟩ : syracuseStep 2273777 = 1705333) B1705333
theorem B2273795 : Blo 1514954 2273795 := bstep (se 1 (by rfl) ⟨1705346, by rfl⟩ : syracuseStep 2273795 = 3410693) B3410693
theorem B2273825 : Blo 1514954 2273825 := bstep (se 2 (by rfl) ⟨852684, by rfl⟩ : syracuseStep 2273825 = 1705369) B1705369
theorem B3838499 : Blo 1514954 3838499 := bstep (se 1 (by rfl) ⟨2878874, by rfl⟩ : syracuseStep 3838499 = 5757749) B5757749
theorem B3412529 : Blo 1514954 3412529 := bstep (se 2 (by rfl) ⟨1279698, by rfl⟩ : syracuseStep 3412529 = 2559397) B2559397
theorem B2273843 : Blo 1514954 2273843 := bstep (se 1 (by rfl) ⟨1705382, by rfl⟩ : syracuseStep 2273843 = 3410765) B3410765
theorem B3412547 : Blo 1514954 3412547 := bstep (se 1 (by rfl) ⟨2559410, by rfl⟩ : syracuseStep 3412547 = 5118821) B5118821
theorem B2273873 : Blo 1514954 2273873 := bstep (se 2 (by rfl) ⟨852702, by rfl⟩ : syracuseStep 2273873 = 1705405) B1705405
theorem B2273891 : Blo 1514954 2273891 := bstep (se 1 (by rfl) ⟨1705418, by rfl⟩ : syracuseStep 2273891 = 3410837) B3410837
theorem B1618547 : Blo 1514954 1618547 := bstep (se 1 (by rfl) ⟨1213910, by rfl⟩ : syracuseStep 1618547 = 2427821) B2427821
theorem B2273921 : Blo 1514954 2273921 := bstep (se 2 (by rfl) ⟨852720, by rfl⟩ : syracuseStep 2273921 = 1705441) B1705441
theorem B2273939 : Blo 1514954 2273939 := bstep (se 1 (by rfl) ⟨1705454, by rfl⟩ : syracuseStep 2273939 = 3410909) B3410909
theorem B2273969 : Blo 1514954 2273969 := bstep (se 2 (by rfl) ⟨852738, by rfl⟩ : syracuseStep 2273969 = 1705477) B1705477
theorem B2273987 : Blo 1514954 2273987 := bstep (se 1 (by rfl) ⟨1705490, by rfl⟩ : syracuseStep 2273987 = 3410981) B3410981
theorem B2274017 : Blo 1514954 2274017 := bstep (se 2 (by rfl) ⟨852756, by rfl⟩ : syracuseStep 2274017 = 1705513) B1705513
theorem B3838691 : Blo 1514954 3838691 := bstep (se 1 (by rfl) ⟨2879018, by rfl⟩ : syracuseStep 3838691 = 5758037) B5758037
theorem B2274035 : Blo 1514954 2274035 := bstep (se 1 (by rfl) ⟨1705526, by rfl⟩ : syracuseStep 2274035 = 3411053) B3411053
theorem B2274065 : Blo 1514954 2274065 := bstep (se 2 (by rfl) ⟨852774, by rfl⟩ : syracuseStep 2274065 = 1705549) B1705549
theorem B2274083 : Blo 1514954 2274083 := bstep (se 1 (by rfl) ⟨1705562, by rfl⟩ : syracuseStep 2274083 = 3411125) B3411125
theorem B2274113 : Blo 1514954 2274113 := bstep (se 2 (by rfl) ⟨852792, by rfl⟩ : syracuseStep 2274113 = 1705585) B1705585
theorem B3412817 : Blo 1514954 3412817 := bstep (se 2 (by rfl) ⟨1279806, by rfl⟩ : syracuseStep 3412817 = 2559613) B2559613
theorem B2274131 : Blo 1514954 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B3412835 : Blo 1514954 3412835 := bstep (se 1 (by rfl) ⟨2559626, by rfl⟩ : syracuseStep 3412835 = 5119253) B5119253
theorem B21844849 : Blo 1514954 21844849 := bstep (se 2 (by rfl) ⟨8191818, by rfl⟩ : syracuseStep 21844849 = 16383637) B16383637
theorem B2274161 : Blo 1514954 2274161 := bstep (se 2 (by rfl) ⟨852810, by rfl⟩ : syracuseStep 2274161 = 1705621) B1705621
theorem B2274179 : Blo 1514954 2274179 := bstep (se 1 (by rfl) ⟨1705634, by rfl⟩ : syracuseStep 2274179 = 3411269) B3411269
theorem B2274209 : Blo 1514954 2274209 := bstep (se 2 (by rfl) ⟨852828, by rfl⟩ : syracuseStep 2274209 = 1705657) B1705657
theorem B2274227 : Blo 1514954 2274227 := bstep (se 1 (by rfl) ⟨1705670, by rfl⟩ : syracuseStep 2274227 = 3411341) B3411341
theorem B5116877 : Blo 1514954 5116877 := bstep (se 3 (by rfl) ⟨959414, by rfl⟩ : syracuseStep 5116877 = 1918829) B1918829
theorem B2274257 : Blo 1514954 2274257 := bstep (se 2 (by rfl) ⟨852846, by rfl⟩ : syracuseStep 2274257 = 1705693) B1705693
theorem B17265635 : Blo 1514954 17265635 := bstep (se 1 (by rfl) ⟨12949226, by rfl⟩ : syracuseStep 17265635 = 25898453) B25898453
theorem B2274275 : Blo 1514954 2274275 := bstep (se 1 (by rfl) ⟨1705706, by rfl⟩ : syracuseStep 2274275 = 3411413) B3411413
theorem B15561713 : Blo 1514954 15561713 := bstep (se 2 (by rfl) ⟨5835642, by rfl⟩ : syracuseStep 15561713 = 11671285) B11671285
theorem B2274305 : Blo 1514954 2274305 := bstep (se 2 (by rfl) ⟨852864, by rfl⟩ : syracuseStep 2274305 = 1705729) B1705729
theorem B2159617 : Blo 1514954 2159617 := bstep (se 2 (by rfl) ⟨809856, by rfl⟩ : syracuseStep 2159617 = 1619713) B1619713
theorem B5116931 : Blo 1514954 5116931 := bstep (se 1 (by rfl) ⟨3837698, by rfl⟩ : syracuseStep 5116931 = 7675397) B7675397
theorem B2274323 : Blo 1514954 2274323 := bstep (se 1 (by rfl) ⟨1705742, by rfl⟩ : syracuseStep 2274323 = 3411485) B3411485
theorem B4854833 : Blo 1514954 4854833 := bstep (se 2 (by rfl) ⟨1820562, by rfl⟩ : syracuseStep 4854833 = 3641125) B3641125
theorem B2274353 : Blo 1514954 2274353 := bstep (se 2 (by rfl) ⟨852882, by rfl⟩ : syracuseStep 2274353 = 1705765) B1705765
theorem B2274371 : Blo 1514954 2274371 := bstep (se 1 (by rfl) ⟨1705778, by rfl⟩ : syracuseStep 2274371 = 3411557) B3411557
theorem B2274401 : Blo 1514954 2274401 := bstep (se 2 (by rfl) ⟨852900, by rfl⟩ : syracuseStep 2274401 = 1705801) B1705801
theorem B5837923 : Blo 1514954 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B3413105 : Blo 1514954 3413105 := bstep (se 2 (by rfl) ⟨1279914, by rfl⟩ : syracuseStep 3413105 = 2559829) B2559829
theorem B2274419 : Blo 1514954 2274419 := bstep (se 1 (by rfl) ⟨1705814, by rfl⟩ : syracuseStep 2274419 = 3411629) B3411629
theorem B2159731 : Blo 1514954 2159731 := bstep (se 1 (by rfl) ⟨1619798, by rfl⟩ : syracuseStep 2159731 = 3239597) B3239597
theorem B3413123 : Blo 1514954 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B2274449 : Blo 1514954 2274449 := bstep (se 2 (by rfl) ⟨852918, by rfl⟩ : syracuseStep 2274449 = 1705837) B1705837
theorem B2274467 : Blo 1514954 2274467 := bstep (se 1 (by rfl) ⟨1705850, by rfl⟩ : syracuseStep 2274467 = 3411701) B3411701
theorem B2274497 : Blo 1514954 2274497 := bstep (se 2 (by rfl) ⟨852936, by rfl⟩ : syracuseStep 2274497 = 1705873) B1705873
theorem B2274515 : Blo 1514954 2274515 := bstep (se 1 (by rfl) ⟨1705886, by rfl⟩ : syracuseStep 2274515 = 3411773) B3411773
theorem B13833443 : Blo 1514954 13833443 := bstep (se 1 (by rfl) ⟨10375082, by rfl⟩ : syracuseStep 13833443 = 20750165) B20750165
theorem B2274545 : Blo 1514954 2274545 := bstep (se 2 (by rfl) ⟨852954, by rfl⟩ : syracuseStep 2274545 = 1705909) B1705909
theorem B2274563 : Blo 1514954 2274563 := bstep (se 1 (by rfl) ⟨1705922, by rfl⟩ : syracuseStep 2274563 = 3411845) B3411845
theorem B5117201 : Blo 1514954 5117201 := bstep (se 2 (by rfl) ⟨1918950, by rfl⟩ : syracuseStep 5117201 = 3837901) B3837901
theorem B2274593 : Blo 1514954 2274593 := bstep (se 2 (by rfl) ⟨852972, by rfl⟩ : syracuseStep 2274593 = 1705945) B1705945
theorem B6911281 : Blo 1514954 6911281 := bstep (se 2 (by rfl) ⟨2591730, by rfl⟩ : syracuseStep 6911281 = 5183461) B5183461
theorem B2274611 : Blo 1514954 2274611 := bstep (se 1 (by rfl) ⟨1705958, by rfl⟩ : syracuseStep 2274611 = 3411917) B3411917
theorem B4437325 : Blo 1514954 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B2274641 : Blo 1514954 2274641 := bstep (se 2 (by rfl) ⟨852990, by rfl⟩ : syracuseStep 2274641 = 1705981) B1705981
theorem B1619299 : Blo 1514954 1619299 := bstep (se 1 (by rfl) ⟨1214474, by rfl⟩ : syracuseStep 1619299 = 2428949) B2428949
theorem B2274659 : Blo 1514954 2274659 := bstep (se 1 (by rfl) ⟨1705994, by rfl⟩ : syracuseStep 2274659 = 3411989) B3411989
theorem B2274689 : Blo 1514954 2274689 := bstep (se 2 (by rfl) ⟨853008, by rfl⟩ : syracuseStep 2274689 = 1706017) B1706017
theorem B2274707 : Blo 1514954 2274707 := bstep (se 1 (by rfl) ⟨1706030, by rfl⟩ : syracuseStep 2274707 = 3412061) B3412061
theorem B4314541 : Blo 1514954 4314541 := bstep (se 3 (by rfl) ⟨808976, by rfl⟩ : syracuseStep 4314541 = 1617953) B1617953
theorem B4609457 : Blo 1514954 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B2274737 : Blo 1514954 2274737 := bstep (se 2 (by rfl) ⟨853026, by rfl⟩ : syracuseStep 2274737 = 1706053) B1706053
theorem B2274755 : Blo 1514954 2274755 := bstep (se 1 (by rfl) ⟨1706066, by rfl⟩ : syracuseStep 2274755 = 3412133) B3412133
theorem B2274785 : Blo 1514954 2274785 := bstep (se 2 (by rfl) ⟨853044, by rfl⟩ : syracuseStep 2274785 = 1706089) B1706089
theorem B12957155 : Blo 1514954 12957155 := bstep (se 1 (by rfl) ⟨9717866, by rfl⟩ : syracuseStep 12957155 = 19435733) B19435733
theorem B2274803 : Blo 1514954 2274803 := bstep (se 1 (by rfl) ⟨1706102, by rfl⟩ : syracuseStep 2274803 = 3412205) B3412205
theorem B1537523 : Blo 1514954 1537523 := bstep (se 1 (by rfl) ⟨1153142, by rfl⟩ : syracuseStep 1537523 = 2306285) B2306285
theorem B6911501 : Blo 1514954 6911501 := bstep (se 3 (by rfl) ⟨1295906, by rfl⟩ : syracuseStep 6911501 = 2591813) B2591813
theorem B13129229 : Blo 1514954 13129229 := bstep (se 3 (by rfl) ⟨2461730, by rfl⟩ : syracuseStep 13129229 = 4923461) B4923461
theorem B2274833 : Blo 1514954 2274833 := bstep (se 2 (by rfl) ⟨853062, by rfl⟩ : syracuseStep 2274833 = 1706125) B1706125
theorem B6477347 : Blo 1514954 6477347 := bstep (se 1 (by rfl) ⟨4858010, by rfl⟩ : syracuseStep 6477347 = 9716021) B9716021
theorem B2274851 : Blo 1514954 2274851 := bstep (se 1 (by rfl) ⟨1706138, by rfl⟩ : syracuseStep 2274851 = 3412277) B3412277
theorem B2274881 : Blo 1514954 2274881 := bstep (se 2 (by rfl) ⟨853080, by rfl⟩ : syracuseStep 2274881 = 1706161) B1706161
theorem B4855373 : Blo 1514954 4855373 := bstep (se 3 (by rfl) ⟨910382, by rfl⟩ : syracuseStep 4855373 = 1820765) B1820765
theorem B4314701 : Blo 1514954 4314701 := bstep (se 3 (by rfl) ⟨809006, by rfl⟩ : syracuseStep 4314701 = 1618013) B1618013
theorem B2274899 : Blo 1514954 2274899 := bstep (se 1 (by rfl) ⟨1706174, by rfl⟩ : syracuseStep 2274899 = 3412349) B3412349
theorem B12949091 : Blo 1514954 12949091 := bstep (se 1 (by rfl) ⟨9711818, by rfl⟩ : syracuseStep 12949091 = 19423637) B19423637
theorem B2274929 : Blo 1514954 2274929 := bstep (se 2 (by rfl) ⟨853098, by rfl⟩ : syracuseStep 2274929 = 1706197) B1706197
theorem B2274947 : Blo 1514954 2274947 := bstep (se 1 (by rfl) ⟨1706210, by rfl⟩ : syracuseStep 2274947 = 3412421) B3412421
theorem B3839633 : Blo 1514954 3839633 := bstep (se 2 (by rfl) ⟨1439862, by rfl⟩ : syracuseStep 3839633 = 2879725) B2879725
theorem B2274977 : Blo 1514954 2274977 := bstep (se 2 (by rfl) ⟨853116, by rfl⟩ : syracuseStep 2274977 = 1706233) B1706233
theorem B5756579 : Blo 1514954 5756579 := bstep (se 1 (by rfl) ⟨4317434, by rfl⟩ : syracuseStep 5756579 = 8634869) B8634869
theorem B2274995 : Blo 1514954 2274995 := bstep (se 1 (by rfl) ⟨1706246, by rfl⟩ : syracuseStep 2274995 = 3412493) B3412493
theorem B3839683 : Blo 1514954 3839683 := bstep (se 1 (by rfl) ⟨2879762, by rfl⟩ : syracuseStep 3839683 = 5759525) B5759525
theorem B9713357 : Blo 1514954 9713357 := bstep (se 3 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 9713357 = 3642509) B3642509
theorem B2275025 : Blo 1514954 2275025 := bstep (se 2 (by rfl) ⟨853134, by rfl⟩ : syracuseStep 2275025 = 1706269) B1706269
theorem B2275043 : Blo 1514954 2275043 := bstep (se 1 (by rfl) ⟨1706282, by rfl⟩ : syracuseStep 2275043 = 3412565) B3412565
theorem B2275073 : Blo 1514954 2275073 := bstep (se 2 (by rfl) ⟨853152, by rfl⟩ : syracuseStep 2275073 = 1706305) B1706305
theorem B4314883 : Blo 1514954 4314883 := bstep (se 1 (by rfl) ⟨3236162, by rfl⟩ : syracuseStep 4314883 = 6472325) B6472325
theorem B2275091 : Blo 1514954 2275091 := bstep (se 1 (by rfl) ⟨1706318, by rfl⟩ : syracuseStep 2275091 = 3412637) B3412637
theorem B5117741 : Blo 1514954 5117741 := bstep (se 3 (by rfl) ⟨959576, by rfl⟩ : syracuseStep 5117741 = 1919153) B1919153
theorem B2275121 : Blo 1514954 2275121 := bstep (se 2 (by rfl) ⟨853170, by rfl⟩ : syracuseStep 2275121 = 1706341) B1706341
theorem B2275139 : Blo 1514954 2275139 := bstep (se 1 (by rfl) ⟨1706354, by rfl⟩ : syracuseStep 2275139 = 3412709) B3412709
theorem B6149965 : Blo 1514954 6149965 := bstep (se 3 (by rfl) ⟨1153118, by rfl⟩ : syracuseStep 6149965 = 2306237) B2306237
theorem B2275169 : Blo 1514954 2275169 := bstep (se 2 (by rfl) ⟨853188, by rfl⟩ : syracuseStep 2275169 = 1706377) B1706377
theorem B5117795 : Blo 1514954 5117795 := bstep (se 1 (by rfl) ⟨3838346, by rfl⟩ : syracuseStep 5117795 = 7676693) B7676693
theorem B2275187 : Blo 1514954 2275187 := bstep (se 1 (by rfl) ⟨1706390, by rfl⟩ : syracuseStep 2275187 = 3412781) B3412781
theorem B35985293 : Blo 1514954 35985293 := bstep (se 3 (by rfl) ⟨6747242, by rfl⟩ : syracuseStep 35985293 = 13494485) B13494485
theorem B2275217 : Blo 1514954 2275217 := bstep (se 2 (by rfl) ⟨853206, by rfl⟩ : syracuseStep 2275217 = 1706413) B1706413
theorem B2275235 : Blo 1514954 2275235 := bstep (se 1 (by rfl) ⟨1706426, by rfl⟩ : syracuseStep 2275235 = 3412853) B3412853
theorem B7673777 : Blo 1514954 7673777 := bstep (se 2 (by rfl) ⟨2877666, by rfl⟩ : syracuseStep 7673777 = 5755333) B5755333
theorem B2275265 : Blo 1514954 2275265 := bstep (se 2 (by rfl) ⟨853224, by rfl⟩ : syracuseStep 2275265 = 1706449) B1706449
theorem B2275283 : Blo 1514954 2275283 := bstep (se 1 (by rfl) ⟨1706462, by rfl⟩ : syracuseStep 2275283 = 3412925) B3412925
theorem B2275313 : Blo 1514954 2275313 := bstep (se 2 (by rfl) ⟨853242, by rfl⟩ : syracuseStep 2275313 = 1706485) B1706485
theorem B2275331 : Blo 1514954 2275331 := bstep (se 1 (by rfl) ⟨1706498, by rfl⟩ : syracuseStep 2275331 = 3412997) B3412997
theorem B2275361 : Blo 1514954 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B2275379 : Blo 1514954 2275379 := bstep (se 1 (by rfl) ⟨1706534, by rfl⟩ : syracuseStep 2275379 = 3413069) B3413069
theorem B2275409 : Blo 1514954 2275409 := bstep (se 2 (by rfl) ⟨853278, by rfl⟩ : syracuseStep 2275409 = 1706557) B1706557
theorem B4610147 : Blo 1514954 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B2275427 : Blo 1514954 2275427 := bstep (se 1 (by rfl) ⟨1706570, by rfl⟩ : syracuseStep 2275427 = 3413141) B3413141
theorem B5118065 : Blo 1514954 5118065 := bstep (se 2 (by rfl) ⟨1919274, by rfl⟩ : syracuseStep 5118065 = 3838549) B3838549
theorem B8632453 : Blo 1514954 8632453 := bstep (se 4 (by rfl) ⟨809292, by rfl⟩ : syracuseStep 8632453 = 1618585) B1618585
theorem B88611043 : Blo 1514954 88611043 := bstep (se 1 (by rfl) ⟨66458282, by rfl⟩ : syracuseStep 88611043 = 132916565) B132916565
theorem B14571845 : Blo 1514954 14571845 := bstep (se 4 (by rfl) ⟨1366110, by rfl⟩ : syracuseStep 14571845 = 2732221) B2732221
theorem B5757581 : Blo 1514954 5757581 := bstep (se 3 (by rfl) ⟨1079546, by rfl⟩ : syracuseStep 5757581 = 2159093) B2159093
theorem B5118605 : Blo 1514954 5118605 := bstep (se 3 (by rfl) ⟨959738, by rfl⟩ : syracuseStep 5118605 = 1919477) B1919477
theorem B5184145 : Blo 1514954 5184145 := bstep (se 2 (by rfl) ⟨1944054, by rfl⟩ : syracuseStep 5184145 = 3888109) B3888109
theorem B5118659 : Blo 1514954 5118659 := bstep (se 1 (by rfl) ⟨3838994, by rfl⟩ : syracuseStep 5118659 = 7677989) B7677989
theorem B11516741 : Blo 1514954 11516741 := bstep (se 4 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 11516741 = 2159389) B2159389
theorem B8198981 : Blo 1514954 8198981 := bstep (se 4 (by rfl) ⟨768654, by rfl⟩ : syracuseStep 8198981 = 1537309) B1537309
theorem B5118929 : Blo 1514954 5118929 := bstep (se 2 (by rfl) ⟨1919598, by rfl⟩ : syracuseStep 5118929 = 3839197) B3839197
theorem B9223217 : Blo 1514954 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B299007089 : Blo 1514954 299007089 := bstep (se 2 (by rfl) ⟨112127658, by rfl⟩ : syracuseStep 299007089 = 224255317) B224255317
theorem B4316273 : Blo 1514954 4316273 := bstep (se 2 (by rfl) ⟨1618602, by rfl⟩ : syracuseStep 4316273 = 3237205) B3237205
theorem B5463217 : Blo 1514954 5463217 := bstep (se 2 (by rfl) ⟨2048706, by rfl⟩ : syracuseStep 5463217 = 4097413) B4097413
theorem B9223409 : Blo 1514954 9223409 := bstep (se 2 (by rfl) ⟨3458778, by rfl⟩ : syracuseStep 9223409 = 6917557) B6917557
theorem B7675235 : Blo 1514954 7675235 := bstep (se 1 (by rfl) ⟨5756426, by rfl⟩ : syracuseStep 7675235 = 11512853) B11512853
theorem B4857293 : Blo 1514954 4857293 := bstep (se 3 (by rfl) ⟨910742, by rfl⟩ : syracuseStep 4857293 = 1821485) B1821485
theorem B1514963 : Blo 1514954 1514963 := bstep (se 1 (by rfl) ⟨1136222, by rfl⟩ : syracuseStep 1514963 = 2272445) B2272445
theorem B1514979 : Blo 1514954 1514979 := bstep (se 1 (by rfl) ⟨1136234, by rfl⟩ : syracuseStep 1514979 = 2272469) B2272469
theorem B5119469 : Blo 1514954 5119469 := bstep (se 3 (by rfl) ⟨959900, by rfl⟩ : syracuseStep 5119469 = 1919801) B1919801
theorem B1514995 : Blo 1514954 1514995 := bstep (se 1 (by rfl) ⟨1136246, by rfl⟩ : syracuseStep 1514995 = 2272493) B2272493
theorem B1515011 : Blo 1514954 1515011 := bstep (se 1 (by rfl) ⟨1136258, by rfl⟩ : syracuseStep 1515011 = 2272517) B2272517
theorem B1515027 : Blo 1514954 1515027 := bstep (se 1 (by rfl) ⟨1136270, by rfl⟩ : syracuseStep 1515027 = 2272541) B2272541
theorem B1515043 : Blo 1514954 1515043 := bstep (se 1 (by rfl) ⟨1136282, by rfl⟩ : syracuseStep 1515043 = 2272565) B2272565
theorem B7781923 : Blo 1514954 7781923 := bstep (se 1 (by rfl) ⟨5836442, by rfl⟩ : syracuseStep 7781923 = 11672885) B11672885
theorem B5119523 : Blo 1514954 5119523 := bstep (se 1 (by rfl) ⟨3839642, by rfl⟩ : syracuseStep 5119523 = 7679285) B7679285
theorem B1515059 : Blo 1514954 1515059 := bstep (se 1 (by rfl) ⟨1136294, by rfl⟩ : syracuseStep 1515059 = 2272589) B2272589
theorem B1515075 : Blo 1514954 1515075 := bstep (se 1 (by rfl) ⟨1136306, by rfl⟩ : syracuseStep 1515075 = 2272613) B2272613
theorem B1515091 : Blo 1514954 1515091 := bstep (se 1 (by rfl) ⟨1136318, by rfl⟩ : syracuseStep 1515091 = 2272637) B2272637
theorem B1515107 : Blo 1514954 1515107 := bstep (se 1 (by rfl) ⟨1136330, by rfl⟩ : syracuseStep 1515107 = 2272661) B2272661
theorem B1515123 : Blo 1514954 1515123 := bstep (se 1 (by rfl) ⟨1136342, by rfl⟩ : syracuseStep 1515123 = 2272685) B2272685
theorem B1515139 : Blo 1514954 1515139 := bstep (se 1 (by rfl) ⟨1136354, by rfl⟩ : syracuseStep 1515139 = 2272709) B2272709
theorem B1515155 : Blo 1514954 1515155 := bstep (se 1 (by rfl) ⟨1136366, by rfl⟩ : syracuseStep 1515155 = 2272733) B2272733
theorem B1515171 : Blo 1514954 1515171 := bstep (se 1 (by rfl) ⟨1136378, by rfl⟩ : syracuseStep 1515171 = 2272757) B2272757
theorem B1515187 : Blo 1514954 1515187 := bstep (se 1 (by rfl) ⟨1136390, by rfl⟩ : syracuseStep 1515187 = 2272781) B2272781
theorem B1515203 : Blo 1514954 1515203 := bstep (se 1 (by rfl) ⟨1136402, by rfl⟩ : syracuseStep 1515203 = 2272805) B2272805
theorem B1515219 : Blo 1514954 1515219 := bstep (se 1 (by rfl) ⟨1136414, by rfl⟩ : syracuseStep 1515219 = 2272829) B2272829
theorem B1515235 : Blo 1514954 1515235 := bstep (se 1 (by rfl) ⟨1136426, by rfl⟩ : syracuseStep 1515235 = 2272853) B2272853
theorem B7282403 : Blo 1514954 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B1515251 : Blo 1514954 1515251 := bstep (se 1 (by rfl) ⟨1136438, by rfl⟩ : syracuseStep 1515251 = 2272877) B2272877
theorem B1515267 : Blo 1514954 1515267 := bstep (se 1 (by rfl) ⟨1136450, by rfl⟩ : syracuseStep 1515267 = 2272901) B2272901
theorem B5463821 : Blo 1514954 5463821 := bstep (se 3 (by rfl) ⟨1024466, by rfl⟩ : syracuseStep 5463821 = 2048933) B2048933
theorem B1515283 : Blo 1514954 1515283 := bstep (se 1 (by rfl) ⟨1136462, by rfl⟩ : syracuseStep 1515283 = 2272925) B2272925
theorem B1515299 : Blo 1514954 1515299 := bstep (se 1 (by rfl) ⟨1136474, by rfl⟩ : syracuseStep 1515299 = 2272949) B2272949
theorem B1515315 : Blo 1514954 1515315 := bstep (se 1 (by rfl) ⟨1136486, by rfl⟩ : syracuseStep 1515315 = 2272973) B2272973
theorem B1515331 : Blo 1514954 1515331 := bstep (se 1 (by rfl) ⟨1136498, by rfl⟩ : syracuseStep 1515331 = 2272997) B2272997
theorem B1515347 : Blo 1514954 1515347 := bstep (se 1 (by rfl) ⟨1136510, by rfl⟩ : syracuseStep 1515347 = 2273021) B2273021
theorem B1515363 : Blo 1514954 1515363 := bstep (se 1 (by rfl) ⟨1136522, by rfl⟩ : syracuseStep 1515363 = 2273045) B2273045
theorem B1515379 : Blo 1514954 1515379 := bstep (se 1 (by rfl) ⟨1136534, by rfl⟩ : syracuseStep 1515379 = 2273069) B2273069
theorem B1515395 : Blo 1514954 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B82968461 : Blo 1514954 82968461 := bstep (se 3 (by rfl) ⟨15556586, by rfl⟩ : syracuseStep 82968461 = 31113173) B31113173
theorem B1515411 : Blo 1514954 1515411 := bstep (se 1 (by rfl) ⟨1136558, by rfl⟩ : syracuseStep 1515411 = 2273117) B2273117
theorem B1515427 : Blo 1514954 1515427 := bstep (se 1 (by rfl) ⟨1136570, by rfl⟩ : syracuseStep 1515427 = 2273141) B2273141
theorem B1515443 : Blo 1514954 1515443 := bstep (se 1 (by rfl) ⟨1136582, by rfl⟩ : syracuseStep 1515443 = 2273165) B2273165
theorem B1515459 : Blo 1514954 1515459 := bstep (se 1 (by rfl) ⟨1136594, by rfl⟩ : syracuseStep 1515459 = 2273189) B2273189
theorem B1515475 : Blo 1514954 1515475 := bstep (se 1 (by rfl) ⟨1136606, by rfl⟩ : syracuseStep 1515475 = 2273213) B2273213
theorem B1515491 : Blo 1514954 1515491 := bstep (se 1 (by rfl) ⟨1136618, by rfl⟩ : syracuseStep 1515491 = 2273237) B2273237
theorem B1515507 : Blo 1514954 1515507 := bstep (se 1 (by rfl) ⟨1136630, by rfl⟩ : syracuseStep 1515507 = 2273261) B2273261
theorem B1515531 : Blo 1514954 1515531 := bstep (se 1 (by rfl) ⟨1136648, by rfl⟩ : syracuseStep 1515531 = 2273297) B2273297
theorem B1515543 : Blo 1514954 1515543 := bstep (se 1 (by rfl) ⟨1136657, by rfl⟩ : syracuseStep 1515543 = 2273315) B2273315
theorem B18432035 : Blo 1514954 18432035 := bstep (se 1 (by rfl) ⟨13824026, by rfl⟩ : syracuseStep 18432035 = 27648053) B27648053
theorem B1515563 : Blo 1514954 1515563 := bstep (se 1 (by rfl) ⟨1136672, by rfl⟩ : syracuseStep 1515563 = 2273345) B2273345
theorem B1515575 : Blo 1514954 1515575 := bstep (se 1 (by rfl) ⟨1136681, by rfl⟩ : syracuseStep 1515575 = 2273363) B2273363
theorem B1515595 : Blo 1514954 1515595 := bstep (se 1 (by rfl) ⟨1136696, by rfl⟩ : syracuseStep 1515595 = 2273393) B2273393
theorem B1728587 : Blo 1514954 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B1515607 : Blo 1514954 1515607 := bstep (se 1 (by rfl) ⟨1136705, by rfl⟩ : syracuseStep 1515607 = 2273411) B2273411
theorem B1515627 : Blo 1514954 1515627 := bstep (se 1 (by rfl) ⟨1136720, by rfl⟩ : syracuseStep 1515627 = 2273441) B2273441
theorem B2916467 : Blo 1514954 2916467 := bstep (se 1 (by rfl) ⟨2187350, by rfl⟩ : syracuseStep 2916467 = 4374701) B4374701
theorem B1515639 : Blo 1514954 1515639 := bstep (se 1 (by rfl) ⟨1136729, by rfl⟩ : syracuseStep 1515639 = 2273459) B2273459
theorem B1515659 : Blo 1514954 1515659 := bstep (se 1 (by rfl) ⟨1136744, by rfl⟩ : syracuseStep 1515659 = 2273489) B2273489
theorem B2187415 : Blo 1514954 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B1515671 : Blo 1514954 1515671 := bstep (se 1 (by rfl) ⟨1136753, by rfl⟩ : syracuseStep 1515671 = 2273507) B2273507
theorem B1515691 : Blo 1514954 1515691 := bstep (se 1 (by rfl) ⟨1136768, by rfl⟩ : syracuseStep 1515691 = 2273537) B2273537
theorem B11509937 : Blo 1514954 11509937 := bstep (se 2 (by rfl) ⟨4316226, by rfl⟩ : syracuseStep 11509937 = 8632453) B8632453
theorem B1515703 : Blo 1514954 1515703 := bstep (se 1 (by rfl) ⟨1136777, by rfl⟩ : syracuseStep 1515703 = 2273555) B2273555
theorem B1515723 : Blo 1514954 1515723 := bstep (se 1 (by rfl) ⟨1136792, by rfl⟩ : syracuseStep 1515723 = 2273585) B2273585
theorem B1515735 : Blo 1514954 1515735 := bstep (se 1 (by rfl) ⟨1136801, by rfl⟩ : syracuseStep 1515735 = 2273603) B2273603
theorem B4317401 : Blo 1514954 4317401 := bstep (se 2 (by rfl) ⟨1619025, by rfl⟩ : syracuseStep 4317401 = 3238051) B3238051
theorem B1515755 : Blo 1514954 1515755 := bstep (se 1 (by rfl) ⟨1136816, by rfl⟩ : syracuseStep 1515755 = 2273633) B2273633
theorem B1515767 : Blo 1514954 1515767 := bstep (se 1 (by rfl) ⟨1136825, by rfl⟩ : syracuseStep 1515767 = 2273651) B2273651
theorem B1515787 : Blo 1514954 1515787 := bstep (se 1 (by rfl) ⟨1136840, by rfl⟩ : syracuseStep 1515787 = 2273681) B2273681
theorem B1515799 : Blo 1514954 1515799 := bstep (se 1 (by rfl) ⟨1136849, by rfl⟩ : syracuseStep 1515799 = 2273699) B2273699
theorem B1515819 : Blo 1514954 1515819 := bstep (se 1 (by rfl) ⟨1136864, by rfl⟩ : syracuseStep 1515819 = 2273729) B2273729
theorem B1515831 : Blo 1514954 1515831 := bstep (se 1 (by rfl) ⟨1136873, by rfl⟩ : syracuseStep 1515831 = 2273747) B2273747
theorem B6472001 : Blo 1514954 6472001 := bstep (se 2 (by rfl) ⟨2427000, by rfl⟩ : syracuseStep 6472001 = 4854001) B4854001
theorem B1515851 : Blo 1514954 1515851 := bstep (se 1 (by rfl) ⟨1136888, by rfl⟩ : syracuseStep 1515851 = 2273777) B2273777
theorem B1515863 : Blo 1514954 1515863 := bstep (se 1 (by rfl) ⟨1136897, by rfl⟩ : syracuseStep 1515863 = 2273795) B2273795
theorem B1515883 : Blo 1514954 1515883 := bstep (se 1 (by rfl) ⟨1136912, by rfl⟩ : syracuseStep 1515883 = 2273825) B2273825
theorem B1515895 : Blo 1514954 1515895 := bstep (se 1 (by rfl) ⟨1136921, by rfl⟩ : syracuseStep 1515895 = 2273843) B2273843
theorem B1515915 : Blo 1514954 1515915 := bstep (se 1 (by rfl) ⟨1136936, by rfl⟩ : syracuseStep 1515915 = 2273873) B2273873
theorem B1704343 : Blo 1514954 1704343 := bstep (se 1 (by rfl) ⟨1278257, by rfl⟩ : syracuseStep 1704343 = 2556515) B2556515
theorem B1515927 : Blo 1514954 1515927 := bstep (se 1 (by rfl) ⟨1136945, by rfl⟩ : syracuseStep 1515927 = 2273891) B2273891
theorem B1515947 : Blo 1514954 1515947 := bstep (se 1 (by rfl) ⟨1136960, by rfl⟩ : syracuseStep 1515947 = 2273921) B2273921
theorem B1515959 : Blo 1514954 1515959 := bstep (se 1 (by rfl) ⟨1136969, by rfl⟩ : syracuseStep 1515959 = 2273939) B2273939
theorem B1515979 : Blo 1514954 1515979 := bstep (se 1 (by rfl) ⟨1136984, by rfl⟩ : syracuseStep 1515979 = 2273969) B2273969
theorem B1515991 : Blo 1514954 1515991 := bstep (se 1 (by rfl) ⟨1136993, by rfl⟩ : syracuseStep 1515991 = 2273987) B2273987
theorem B6472153 : Blo 1514954 6472153 := bstep (se 2 (by rfl) ⟨2427057, by rfl⟩ : syracuseStep 6472153 = 4854115) B4854115
theorem B1516011 : Blo 1514954 1516011 := bstep (se 1 (by rfl) ⟨1137008, by rfl⟩ : syracuseStep 1516011 = 2274017) B2274017
theorem B1516023 : Blo 1514954 1516023 := bstep (se 1 (by rfl) ⟨1137017, by rfl⟩ : syracuseStep 1516023 = 2274035) B2274035
theorem B1516043 : Blo 1514954 1516043 := bstep (se 1 (by rfl) ⟨1137032, by rfl⟩ : syracuseStep 1516043 = 2274065) B2274065
theorem B3457559 : Blo 1514954 3457559 := bstep (se 1 (by rfl) ⟨2593169, by rfl⟩ : syracuseStep 3457559 = 5186339) B5186339
theorem B1516055 : Blo 1514954 1516055 := bstep (se 1 (by rfl) ⟨1137041, by rfl⟩ : syracuseStep 1516055 = 2274083) B2274083
theorem B1516075 : Blo 1514954 1516075 := bstep (se 1 (by rfl) ⟨1137056, by rfl⟩ : syracuseStep 1516075 = 2274113) B2274113
theorem B1516087 : Blo 1514954 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B1704523 : Blo 1514954 1704523 := bstep (se 1 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 1704523 = 2556785) B2556785
theorem B1516107 : Blo 1514954 1516107 := bstep (se 1 (by rfl) ⟨1137080, by rfl⟩ : syracuseStep 1516107 = 2274161) B2274161
theorem B1516119 : Blo 1514954 1516119 := bstep (se 1 (by rfl) ⟨1137089, by rfl⟩ : syracuseStep 1516119 = 2274179) B2274179
theorem B1516139 : Blo 1514954 1516139 := bstep (se 1 (by rfl) ⟨1137104, by rfl⟩ : syracuseStep 1516139 = 2274209) B2274209
theorem B1516151 : Blo 1514954 1516151 := bstep (se 1 (by rfl) ⟨1137113, by rfl⟩ : syracuseStep 1516151 = 2274227) B2274227
theorem B1516171 : Blo 1514954 1516171 := bstep (se 1 (by rfl) ⟨1137128, by rfl⟩ : syracuseStep 1516171 = 2274257) B2274257
theorem B5833367 : Blo 1514954 5833367 := bstep (se 1 (by rfl) ⟨4375025, by rfl⟩ : syracuseStep 5833367 = 8750051) B8750051
theorem B2876057 : Blo 1514954 2876057 := bstep (se 2 (by rfl) ⟨1078521, by rfl⟩ : syracuseStep 2876057 = 2157043) B2157043
theorem B2556569 : Blo 1514954 2556569 := bstep (se 2 (by rfl) ⟨958713, by rfl⟩ : syracuseStep 2556569 = 1917427) B1917427
theorem B11510423 : Blo 1514954 11510423 := bstep (se 1 (by rfl) ⟨8632817, by rfl⟩ : syracuseStep 11510423 = 17265635) B17265635
theorem B1516183 : Blo 1514954 1516183 := bstep (se 1 (by rfl) ⟨1137137, by rfl⟩ : syracuseStep 1516183 = 2274275) B2274275
theorem B1516203 : Blo 1514954 1516203 := bstep (se 1 (by rfl) ⟨1137152, by rfl⟩ : syracuseStep 1516203 = 2274305) B2274305
theorem B1704631 : Blo 1514954 1704631 := bstep (se 1 (by rfl) ⟨1278473, by rfl⟩ : syracuseStep 1704631 = 2556947) B2556947
theorem B1516215 : Blo 1514954 1516215 := bstep (se 1 (by rfl) ⟨1137161, by rfl⟩ : syracuseStep 1516215 = 2274323) B2274323
theorem B4612801 : Blo 1514954 4612801 := bstep (se 2 (by rfl) ⟨1729800, by rfl⟩ : syracuseStep 4612801 = 3459601) B3459601
theorem B3236555 : Blo 1514954 3236555 := bstep (se 1 (by rfl) ⟨2427416, by rfl⟩ : syracuseStep 3236555 = 4854833) B4854833
theorem B1516235 : Blo 1514954 1516235 := bstep (se 1 (by rfl) ⟨1137176, by rfl⟩ : syracuseStep 1516235 = 2274353) B2274353
theorem B17261261 : Blo 1514954 17261261 := bstep (se 3 (by rfl) ⟨3236486, by rfl⟩ : syracuseStep 17261261 = 6472973) B6472973
theorem B1516247 : Blo 1514954 1516247 := bstep (se 1 (by rfl) ⟨1137185, by rfl⟩ : syracuseStep 1516247 = 2274371) B2274371
theorem B1516267 : Blo 1514954 1516267 := bstep (se 1 (by rfl) ⟨1137200, by rfl⟩ : syracuseStep 1516267 = 2274401) B2274401
theorem B1516279 : Blo 1514954 1516279 := bstep (se 1 (by rfl) ⟨1137209, by rfl⟩ : syracuseStep 1516279 = 2274419) B2274419
theorem B27648773 : Blo 1514954 27648773 := bstep (se 4 (by rfl) ⟨2592072, by rfl⟩ : syracuseStep 27648773 = 5184145) B5184145
theorem B1516299 : Blo 1514954 1516299 := bstep (se 1 (by rfl) ⟨1137224, by rfl⟩ : syracuseStep 1516299 = 2274449) B2274449
theorem B1516311 : Blo 1514954 1516311 := bstep (se 1 (by rfl) ⟨1137233, by rfl⟩ : syracuseStep 1516311 = 2274467) B2274467
theorem B2556697 : Blo 1514954 2556697 := bstep (se 2 (by rfl) ⟨958761, by rfl⟩ : syracuseStep 2556697 = 1917523) B1917523
theorem B1516331 : Blo 1514954 1516331 := bstep (se 1 (by rfl) ⟨1137248, by rfl⟩ : syracuseStep 1516331 = 2274497) B2274497
theorem B1516343 : Blo 1514954 1516343 := bstep (se 1 (by rfl) ⟨1137257, by rfl⟩ : syracuseStep 1516343 = 2274515) B2274515
theorem B1516363 : Blo 1514954 1516363 := bstep (se 1 (by rfl) ⟨1137272, by rfl⟩ : syracuseStep 1516363 = 2274545) B2274545
theorem B1516375 : Blo 1514954 1516375 := bstep (se 1 (by rfl) ⟨1137281, by rfl⟩ : syracuseStep 1516375 = 2274563) B2274563
theorem B4858717 : Blo 1514954 4858717 := bstep (se 3 (by rfl) ⟨911009, by rfl⟩ : syracuseStep 4858717 = 1822019) B1822019
theorem B1704811 : Blo 1514954 1704811 := bstep (se 1 (by rfl) ⟨1278608, by rfl⟩ : syracuseStep 1704811 = 2557217) B2557217
theorem B1516395 : Blo 1514954 1516395 := bstep (se 1 (by rfl) ⟨1137296, by rfl⟩ : syracuseStep 1516395 = 2274593) B2274593
theorem B1516407 : Blo 1514954 1516407 := bstep (se 1 (by rfl) ⟨1137305, by rfl⟩ : syracuseStep 1516407 = 2274611) B2274611
theorem B1516427 : Blo 1514954 1516427 := bstep (se 1 (by rfl) ⟨1137320, by rfl⟩ : syracuseStep 1516427 = 2274641) B2274641
theorem B1917847 : Blo 1514954 1917847 := bstep (se 1 (by rfl) ⟨1438385, by rfl⟩ : syracuseStep 1917847 = 2876771) B2876771
theorem B1516439 : Blo 1514954 1516439 := bstep (se 1 (by rfl) ⟨1137329, by rfl⟩ : syracuseStep 1516439 = 2274659) B2274659
theorem B1516459 : Blo 1514954 1516459 := bstep (se 1 (by rfl) ⟨1137344, by rfl⟩ : syracuseStep 1516459 = 2274689) B2274689
theorem B3834803 : Blo 1514954 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B1516471 : Blo 1514954 1516471 := bstep (se 1 (by rfl) ⟨1137353, by rfl⟩ : syracuseStep 1516471 = 2274707) B2274707
theorem B3072971 : Blo 1514954 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B1516491 : Blo 1514954 1516491 := bstep (se 1 (by rfl) ⟨1137368, by rfl⟩ : syracuseStep 1516491 = 2274737) B2274737
theorem B1704919 : Blo 1514954 1704919 := bstep (se 1 (by rfl) ⟨1278689, by rfl⟩ : syracuseStep 1704919 = 2557379) B2557379
theorem B1516503 : Blo 1514954 1516503 := bstep (se 1 (by rfl) ⟨1137377, by rfl⟩ : syracuseStep 1516503 = 2274755) B2274755
theorem B3408857 : Blo 1514954 3408857 := bstep (se 2 (by rfl) ⟨1278321, by rfl⟩ : syracuseStep 3408857 = 2556643) B2556643
theorem B1516523 : Blo 1514954 1516523 := bstep (se 1 (by rfl) ⟨1137392, by rfl⟩ : syracuseStep 1516523 = 2274785) B2274785
theorem B1516535 : Blo 1514954 1516535 := bstep (se 1 (by rfl) ⟨1137401, by rfl⟩ : syracuseStep 1516535 = 2274803) B2274803
theorem B1516555 : Blo 1514954 1516555 := bstep (se 1 (by rfl) ⟨1137416, by rfl⟩ : syracuseStep 1516555 = 2274833) B2274833
theorem B1516567 : Blo 1514954 1516567 := bstep (se 1 (by rfl) ⟨1137425, by rfl⟩ : syracuseStep 1516567 = 2274851) B2274851
theorem B1516587 : Blo 1514954 1516587 := bstep (se 1 (by rfl) ⟨1137440, by rfl⟩ : syracuseStep 1516587 = 2274881) B2274881
theorem B3408947 : Blo 1514954 3408947 := bstep (se 1 (by rfl) ⟨2556710, by rfl⟩ : syracuseStep 3408947 = 5113421) B5113421
theorem B2876467 : Blo 1514954 2876467 := bstep (se 1 (by rfl) ⟨2157350, by rfl⟩ : syracuseStep 2876467 = 4314701) B4314701
theorem B3236915 : Blo 1514954 3236915 := bstep (se 1 (by rfl) ⟨2427686, by rfl⟩ : syracuseStep 3236915 = 4855373) B4855373
theorem B1516599 : Blo 1514954 1516599 := bstep (se 1 (by rfl) ⟨1137449, by rfl⟩ : syracuseStep 1516599 = 2274899) B2274899
theorem B1516619 : Blo 1514954 1516619 := bstep (se 1 (by rfl) ⟨1137464, by rfl⟩ : syracuseStep 1516619 = 2274929) B2274929
theorem B3408983 : Blo 1514954 3408983 := bstep (se 1 (by rfl) ⟨2556737, by rfl⟩ : syracuseStep 3408983 = 5113475) B5113475
theorem B1516631 : Blo 1514954 1516631 := bstep (se 1 (by rfl) ⟨1137473, by rfl⟩ : syracuseStep 1516631 = 2274947) B2274947
theorem B1516651 : Blo 1514954 1516651 := bstep (se 1 (by rfl) ⟨1137488, by rfl⟩ : syracuseStep 1516651 = 2274977) B2274977
theorem B1516663 : Blo 1514954 1516663 := bstep (se 1 (by rfl) ⟨1137497, by rfl⟩ : syracuseStep 1516663 = 2274995) B2274995
theorem B1705099 : Blo 1514954 1705099 := bstep (se 1 (by rfl) ⟨1278824, by rfl⟩ : syracuseStep 1705099 = 2557649) B2557649
theorem B1516683 : Blo 1514954 1516683 := bstep (se 1 (by rfl) ⟨1137512, by rfl⟩ : syracuseStep 1516683 = 2275025) B2275025
theorem B1516695 : Blo 1514954 1516695 := bstep (se 1 (by rfl) ⟨1137521, by rfl⟩ : syracuseStep 1516695 = 2275043) B2275043
theorem B1516715 : Blo 1514954 1516715 := bstep (se 1 (by rfl) ⟨1137536, by rfl⟩ : syracuseStep 1516715 = 2275073) B2275073
theorem B1516727 : Blo 1514954 1516727 := bstep (se 1 (by rfl) ⟨1137545, by rfl⟩ : syracuseStep 1516727 = 2275091) B2275091
theorem B1516747 : Blo 1514954 1516747 := bstep (se 1 (by rfl) ⟨1137560, by rfl⟩ : syracuseStep 1516747 = 2275121) B2275121
theorem B12952781 : Blo 1514954 12952781 := bstep (se 3 (by rfl) ⟨2428646, by rfl⟩ : syracuseStep 12952781 = 4857293) B4857293
theorem B1516759 : Blo 1514954 1516759 := bstep (se 1 (by rfl) ⟨1137569, by rfl⟩ : syracuseStep 1516759 = 2275139) B2275139
theorem B3835097 : Blo 1514954 3835097 := bstep (se 2 (by rfl) ⟨1438161, by rfl⟩ : syracuseStep 3835097 = 2876323) B2876323
theorem B1516779 : Blo 1514954 1516779 := bstep (se 1 (by rfl) ⟨1137584, by rfl⟩ : syracuseStep 1516779 = 2275169) B2275169
theorem B1705207 : Blo 1514954 1705207 := bstep (se 1 (by rfl) ⟨1278905, by rfl⟩ : syracuseStep 1705207 = 2557811) B2557811
theorem B1516791 : Blo 1514954 1516791 := bstep (se 1 (by rfl) ⟨1137593, by rfl⟩ : syracuseStep 1516791 = 2275187) B2275187
theorem B3409163 : Blo 1514954 3409163 := bstep (se 1 (by rfl) ⟨2556872, by rfl⟩ : syracuseStep 3409163 = 5113745) B5113745
theorem B1516811 : Blo 1514954 1516811 := bstep (se 1 (by rfl) ⟨1137608, by rfl⟩ : syracuseStep 1516811 = 2275217) B2275217
theorem B1516823 : Blo 1514954 1516823 := bstep (se 1 (by rfl) ⟨1137617, by rfl⟩ : syracuseStep 1516823 = 2275235) B2275235
theorem B1516843 : Blo 1514954 1516843 := bstep (se 1 (by rfl) ⟨1137632, by rfl⟩ : syracuseStep 1516843 = 2275265) B2275265
theorem B1516855 : Blo 1514954 1516855 := bstep (se 1 (by rfl) ⟨1137641, by rfl⟩ : syracuseStep 1516855 = 2275283) B2275283
theorem B3409217 : Blo 1514954 3409217 := bstep (se 2 (by rfl) ⟨1278456, by rfl⟩ : syracuseStep 3409217 = 2556913) B2556913
theorem B1516875 : Blo 1514954 1516875 := bstep (se 1 (by rfl) ⟨1137656, by rfl⟩ : syracuseStep 1516875 = 2275313) B2275313
theorem B2557271 : Blo 1514954 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B1516887 : Blo 1514954 1516887 := bstep (se 1 (by rfl) ⟨1137665, by rfl⟩ : syracuseStep 1516887 = 2275331) B2275331
theorem B1516907 : Blo 1514954 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B1516919 : Blo 1514954 1516919 := bstep (se 1 (by rfl) ⟨1137689, by rfl⟩ : syracuseStep 1516919 = 2275379) B2275379
theorem B1516939 : Blo 1514954 1516939 := bstep (se 1 (by rfl) ⟨1137704, by rfl⟩ : syracuseStep 1516939 = 2275409) B2275409
theorem B1516951 : Blo 1514954 1516951 := bstep (se 1 (by rfl) ⟨1137713, by rfl⟩ : syracuseStep 1516951 = 2275427) B2275427
theorem B1705387 : Blo 1514954 1705387 := bstep (se 1 (by rfl) ⟨1279040, by rfl⟩ : syracuseStep 1705387 = 2558081) B2558081
theorem B2557399 : Blo 1514954 2557399 := bstep (se 1 (by rfl) ⟨1918049, by rfl⟩ : syracuseStep 2557399 = 3836099) B3836099
theorem B5113367 : Blo 1514954 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B1705495 : Blo 1514954 1705495 := bstep (se 1 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 1705495 = 2558243) B2558243
theorem B3409433 : Blo 1514954 3409433 := bstep (se 2 (by rfl) ⟨1278537, by rfl⟩ : syracuseStep 3409433 = 2557075) B2557075
theorem B2876953 : Blo 1514954 2876953 := bstep (se 2 (by rfl) ⟨1078857, by rfl⟩ : syracuseStep 2876953 = 2157715) B2157715
theorem B7284289 : Blo 1514954 7284289 := bstep (se 2 (by rfl) ⟨2731608, by rfl⟩ : syracuseStep 7284289 = 5463217) B5463217
theorem B3409523 : Blo 1514954 3409523 := bstep (se 1 (by rfl) ⟨2557142, by rfl⟩ : syracuseStep 3409523 = 5114285) B5114285
theorem B3409559 : Blo 1514954 3409559 := bstep (se 1 (by rfl) ⟨2557169, by rfl⟩ : syracuseStep 3409559 = 5114339) B5114339
theorem B1918667 : Blo 1514954 1918667 := bstep (se 1 (by rfl) ⟨1439000, by rfl⟩ : syracuseStep 1918667 = 2878001) B2878001
theorem B1705675 : Blo 1514954 1705675 := bstep (se 1 (by rfl) ⟨1279256, by rfl⟩ : syracuseStep 1705675 = 2558513) B2558513
theorem B5187293 : Blo 1514954 5187293 := bstep (se 3 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 5187293 = 1945235) B1945235
theorem B5916433 : Blo 1514954 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B1705783 : Blo 1514954 1705783 := bstep (se 1 (by rfl) ⟨1279337, by rfl⟩ : syracuseStep 1705783 = 2558675) B2558675
theorem B4319041 : Blo 1514954 4319041 := bstep (se 2 (by rfl) ⟨1619640, by rfl⟩ : syracuseStep 4319041 = 3239281) B3239281
theorem B2426699 : Blo 1514954 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B3409739 : Blo 1514954 3409739 := bstep (se 1 (by rfl) ⟨2557304, by rfl⟩ : syracuseStep 3409739 = 5114609) B5114609
theorem B3409793 : Blo 1514954 3409793 := bstep (se 2 (by rfl) ⟨1278672, by rfl⟩ : syracuseStep 3409793 = 2557345) B2557345
theorem B7677827 : Blo 1514954 7677827 := bstep (se 1 (by rfl) ⟨5758370, by rfl⟩ : syracuseStep 7677827 = 11516741) B11516741
theorem B5465987 : Blo 1514954 5465987 := bstep (se 1 (by rfl) ⟨4099490, by rfl⟩ : syracuseStep 5465987 = 8198981) B8198981
theorem B5752721 : Blo 1514954 5752721 := bstep (se 2 (by rfl) ⟨2157270, by rfl⟩ : syracuseStep 5752721 = 4314541) B4314541
theorem B3073945 : Blo 1514954 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B1705963 : Blo 1514954 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B5113907 : Blo 1514954 5113907 := bstep (se 1 (by rfl) ⟨3835430, by rfl⟩ : syracuseStep 5113907 = 7670861) B7670861
theorem B199338059 : Blo 1514954 199338059 := bstep (se 1 (by rfl) ⟨149503544, by rfl⟩ : syracuseStep 199338059 = 299007089) B299007089
theorem B2877515 : Blo 1514954 2877515 := bstep (se 1 (by rfl) ⟨2158136, by rfl⟩ : syracuseStep 2877515 = 4316273) B4316273
theorem B2558027 : Blo 1514954 2558027 := bstep (se 1 (by rfl) ⟨1918520, by rfl⟩ : syracuseStep 2558027 = 3837041) B3837041
theorem B1706071 : Blo 1514954 1706071 := bstep (se 1 (by rfl) ⟨1279553, by rfl⟩ : syracuseStep 1706071 = 2559107) B2559107
theorem B3410009 : Blo 1514954 3410009 := bstep (se 2 (by rfl) ⟨1278753, by rfl⟩ : syracuseStep 3410009 = 2557507) B2557507
theorem B3410099 : Blo 1514954 3410099 := bstep (se 1 (by rfl) ⟨2557574, by rfl⟩ : syracuseStep 3410099 = 5115149) B5115149
theorem B2558155 : Blo 1514954 2558155 := bstep (se 1 (by rfl) ⟨1918616, by rfl⟩ : syracuseStep 2558155 = 3837233) B3837233
theorem B3410135 : Blo 1514954 3410135 := bstep (se 1 (by rfl) ⟨2557601, by rfl⟩ : syracuseStep 3410135 = 5115203) B5115203
theorem B2877697 : Blo 1514954 2877697 := bstep (se 2 (by rfl) ⟨1079136, by rfl⟩ : syracuseStep 2877697 = 2158273) B2158273
theorem B1706251 : Blo 1514954 1706251 := bstep (se 1 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 1706251 = 2559377) B2559377
theorem B5114177 : Blo 1514954 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B5753177 : Blo 1514954 5753177 := bstep (se 2 (by rfl) ⟨2157441, by rfl⟩ : syracuseStep 5753177 = 4314883) B4314883
theorem B2558297 : Blo 1514954 2558297 := bstep (se 2 (by rfl) ⟨959361, by rfl⟩ : syracuseStep 2558297 = 1918723) B1918723
theorem B1706359 : Blo 1514954 1706359 := bstep (se 1 (by rfl) ⟨1279769, by rfl⟩ : syracuseStep 1706359 = 2559539) B2559539
theorem B3410315 : Blo 1514954 3410315 := bstep (se 1 (by rfl) ⟨2557736, by rfl⟩ : syracuseStep 3410315 = 5115473) B5115473
theorem B1919371 : Blo 1514954 1919371 := bstep (se 1 (by rfl) ⟨1439528, by rfl⟩ : syracuseStep 1919371 = 2879057) B2879057
theorem B3410369 : Blo 1514954 3410369 := bstep (se 2 (by rfl) ⟨1278888, by rfl⟩ : syracuseStep 3410369 = 2557777) B2557777
theorem B2558425 : Blo 1514954 2558425 := bstep (se 2 (by rfl) ⟨959409, by rfl⟩ : syracuseStep 2558425 = 1918819) B1918819
theorem B1706539 : Blo 1514954 1706539 := bstep (se 1 (by rfl) ⟨1279904, by rfl⟩ : syracuseStep 1706539 = 2559809) B2559809
theorem B5753389 : Blo 1514954 5753389 := bstep (se 3 (by rfl) ⟨1078760, by rfl⟩ : syracuseStep 5753389 = 2157521) B2157521
theorem B1641067 : Blo 1514954 1641067 := bstep (se 1 (by rfl) ⟨1230800, by rfl⟩ : syracuseStep 1641067 = 2461601) B2461601
theorem B1919639 : Blo 1514954 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B2427545 : Blo 1514954 2427545 := bstep (se 2 (by rfl) ⟨910329, by rfl⟩ : syracuseStep 2427545 = 1820659) B1820659
theorem B3410585 : Blo 1514954 3410585 := bstep (se 2 (by rfl) ⟨1278969, by rfl⟩ : syracuseStep 3410585 = 2557939) B2557939
theorem B3410675 : Blo 1514954 3410675 := bstep (se 1 (by rfl) ⟨2558006, by rfl⟩ : syracuseStep 3410675 = 5116013) B5116013
theorem B3640087 : Blo 1514954 3640087 := bstep (se 1 (by rfl) ⟨2730065, by rfl⟩ : syracuseStep 3640087 = 5460131) B5460131
theorem B3410711 : Blo 1514954 3410711 := bstep (se 1 (by rfl) ⟨2558033, by rfl⟩ : syracuseStep 3410711 = 5116067) B5116067
theorem B2427673 : Blo 1514954 2427673 := bstep (se 2 (by rfl) ⟨910377, by rfl⟩ : syracuseStep 2427673 = 1820755) B1820755
theorem B8629037 : Blo 1514954 8629037 := bstep (se 3 (by rfl) ⟨1617944, by rfl⟩ : syracuseStep 8629037 = 3235889) B3235889
theorem B3836747 : Blo 1514954 3836747 := bstep (se 1 (by rfl) ⟨2877560, by rfl⟩ : syracuseStep 3836747 = 5755121) B5755121
theorem B2427737 : Blo 1514954 2427737 := bstep (se 2 (by rfl) ⟨910401, by rfl⟩ : syracuseStep 2427737 = 1820803) B1820803
theorem B5753693 : Blo 1514954 5753693 := bstep (se 3 (by rfl) ⟨1078817, by rfl⟩ : syracuseStep 5753693 = 2157635) B2157635
theorem B5114717 : Blo 1514954 5114717 := bstep (se 3 (by rfl) ⟨959009, by rfl⟩ : syracuseStep 5114717 = 1918019) B1918019
theorem B41503589 : Blo 1514954 41503589 := bstep (se 4 (by rfl) ⟨3890961, by rfl⟩ : syracuseStep 41503589 = 7781923) B7781923
theorem B31558577 : Blo 1514954 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B3410891 : Blo 1514954 3410891 := bstep (se 1 (by rfl) ⟨2558168, by rfl⟩ : syracuseStep 3410891 = 5116337) B5116337
theorem B2878411 : Blo 1514954 2878411 := bstep (se 1 (by rfl) ⟨2158808, by rfl⟩ : syracuseStep 2878411 = 4317617) B4317617
theorem B2845655 : Blo 1514954 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B118148057 : Blo 1514954 118148057 := bstep (se 2 (by rfl) ⟨44305521, by rfl⟩ : syracuseStep 118148057 = 88611043) B88611043
theorem B3410945 : Blo 1514954 3410945 := bstep (se 2 (by rfl) ⟨1279104, by rfl⟩ : syracuseStep 3410945 = 2558209) B2558209
theorem B3238913 : Blo 1514954 3238913 := bstep (se 2 (by rfl) ⟨1214592, by rfl⟩ : syracuseStep 3238913 = 2429185) B2429185
theorem B2878487 : Blo 1514954 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B2558999 : Blo 1514954 2558999 := bstep (se 1 (by rfl) ⟨1919249, by rfl⟩ : syracuseStep 2558999 = 3838499) B3838499
theorem B5991475 : Blo 1514954 5991475 := bstep (se 1 (by rfl) ⟨4493606, by rfl⟩ : syracuseStep 5991475 = 8987213) B8987213
theorem B2559127 : Blo 1514954 2559127 := bstep (se 1 (by rfl) ⟨1919345, by rfl⟩ : syracuseStep 2559127 = 3838691) B3838691
theorem B3411161 : Blo 1514954 3411161 := bstep (se 2 (by rfl) ⟨1279185, by rfl⟩ : syracuseStep 3411161 = 2558371) B2558371
theorem B2272523 : Blo 1514954 2272523 := bstep (se 1 (by rfl) ⟨1704392, by rfl⟩ : syracuseStep 2272523 = 3408785) B3408785
theorem B2157835 : Blo 1514954 2157835 := bstep (se 1 (by rfl) ⟨1618376, by rfl⟩ : syracuseStep 2157835 = 3236753) B3236753
theorem B2272535 : Blo 1514954 2272535 := bstep (se 1 (by rfl) ⟨1704401, by rfl⟩ : syracuseStep 2272535 = 3408803) B3408803
theorem B3411251 : Blo 1514954 3411251 := bstep (se 1 (by rfl) ⟨2558438, by rfl⟩ : syracuseStep 3411251 = 5116877) B5116877
theorem B13823297 : Blo 1514954 13823297 := bstep (se 2 (by rfl) ⟨5183736, by rfl⟩ : syracuseStep 13823297 = 10367473) B10367473
theorem B10374475 : Blo 1514954 10374475 := bstep (se 1 (by rfl) ⟨7780856, by rfl⟩ : syracuseStep 10374475 = 15561713) B15561713
theorem B3411287 : Blo 1514954 3411287 := bstep (se 1 (by rfl) ⟨2558465, by rfl⟩ : syracuseStep 3411287 = 5116931) B5116931
theorem B2272601 : Blo 1514954 2272601 := bstep (se 2 (by rfl) ⟨852225, by rfl⟩ : syracuseStep 2272601 = 1704451) B1704451
theorem B10800485 : Blo 1514954 10800485 := bstep (se 4 (by rfl) ⟨1012545, by rfl⟩ : syracuseStep 10800485 = 2025091) B2025091
theorem B9710999 : Blo 1514954 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B2272715 : Blo 1514954 2272715 := bstep (se 1 (by rfl) ⟨1704536, by rfl⟩ : syracuseStep 2272715 = 3409073) B3409073
theorem B2272727 : Blo 1514954 2272727 := bstep (se 1 (by rfl) ⟨1704545, by rfl⟩ : syracuseStep 2272727 = 3409091) B3409091
theorem B3411467 : Blo 1514954 3411467 := bstep (se 1 (by rfl) ⟨2558600, by rfl⟩ : syracuseStep 3411467 = 5117201) B5117201
theorem B2272793 : Blo 1514954 2272793 := bstep (se 2 (by rfl) ⟨852297, by rfl⟩ : syracuseStep 2272793 = 1704595) B1704595
theorem B3411521 : Blo 1514954 3411521 := bstep (se 2 (by rfl) ⟨1279320, by rfl⟩ : syracuseStep 3411521 = 2558641) B2558641
theorem B2076247 : Blo 1514954 2076247 := bstep (se 1 (by rfl) ⟨1557185, by rfl⟩ : syracuseStep 2076247 = 3114371) B3114371
theorem B2272907 : Blo 1514954 2272907 := bstep (se 1 (by rfl) ⟨1704680, by rfl⟩ : syracuseStep 2272907 = 3409361) B3409361
theorem B2272919 : Blo 1514954 2272919 := bstep (se 1 (by rfl) ⟨1704689, by rfl⟩ : syracuseStep 2272919 = 3409379) B3409379
theorem B8638103 : Blo 1514954 8638103 := bstep (se 1 (by rfl) ⟨6478577, by rfl⟩ : syracuseStep 8638103 = 12957155) B12957155
theorem B8752819 : Blo 1514954 8752819 := bstep (se 1 (by rfl) ⟨6564614, by rfl⟩ : syracuseStep 8752819 = 13129229) B13129229
theorem B2879155 : Blo 1514954 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B4992691 : Blo 1514954 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B2272985 : Blo 1514954 2272985 := bstep (se 2 (by rfl) ⟨852369, by rfl⟩ : syracuseStep 2272985 = 1704739) B1704739
theorem B2559755 : Blo 1514954 2559755 := bstep (se 1 (by rfl) ⟨1919816, by rfl⟩ : syracuseStep 2559755 = 3839633) B3839633
theorem B3837719 : Blo 1514954 3837719 := bstep (se 1 (by rfl) ⟨2878289, by rfl⟩ : syracuseStep 3837719 = 5756579) B5756579
theorem B3411737 : Blo 1514954 3411737 := bstep (se 2 (by rfl) ⟨1279401, by rfl⟩ : syracuseStep 3411737 = 2558803) B2558803
theorem B6475571 : Blo 1514954 6475571 := bstep (se 1 (by rfl) ⟨4856678, by rfl⟩ : syracuseStep 6475571 = 9713357) B9713357
theorem B29126465 : Blo 1514954 29126465 := bstep (se 2 (by rfl) ⟨10922424, by rfl⟩ : syracuseStep 29126465 = 21844849) B21844849
theorem B2273099 : Blo 1514954 2273099 := bstep (se 1 (by rfl) ⟨1704824, by rfl⟩ : syracuseStep 2273099 = 3409649) B3409649
theorem B2273111 : Blo 1514954 2273111 := bstep (se 1 (by rfl) ⟨1704833, by rfl⟩ : syracuseStep 2273111 = 3409667) B3409667
theorem B3239767 : Blo 1514954 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B3411827 : Blo 1514954 3411827 := bstep (se 1 (by rfl) ⟨2558870, by rfl⟩ : syracuseStep 3411827 = 5117741) B5117741
theorem B3411863 : Blo 1514954 3411863 := bstep (se 1 (by rfl) ⟨2558897, by rfl⟩ : syracuseStep 3411863 = 5117795) B5117795
theorem B2879383 : Blo 1514954 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B2273177 : Blo 1514954 2273177 := bstep (se 2 (by rfl) ⟨852441, by rfl⟩ : syracuseStep 2273177 = 1704883) B1704883
theorem B23990195 : Blo 1514954 23990195 := bstep (se 1 (by rfl) ⟨17992646, by rfl⟩ : syracuseStep 23990195 = 35985293) B35985293
theorem B5115851 : Blo 1514954 5115851 := bstep (se 1 (by rfl) ⟨3836888, by rfl⟩ : syracuseStep 5115851 = 7673777) B7673777
theorem B2879489 : Blo 1514954 2879489 := bstep (se 2 (by rfl) ⟨1079808, by rfl⟩ : syracuseStep 2879489 = 2159617) B2159617
theorem B2273291 : Blo 1514954 2273291 := bstep (se 1 (by rfl) ⟨1704968, by rfl⟩ : syracuseStep 2273291 = 3409937) B3409937
theorem B2273303 : Blo 1514954 2273303 := bstep (se 1 (by rfl) ⟨1704977, by rfl⟩ : syracuseStep 2273303 = 3409955) B3409955
theorem B98299979 : Blo 1514954 98299979 := bstep (se 1 (by rfl) ⟨73724984, by rfl⟩ : syracuseStep 98299979 = 147449969) B147449969
theorem B3412043 : Blo 1514954 3412043 := bstep (se 1 (by rfl) ⟨2559032, by rfl⟩ : syracuseStep 3412043 = 5118065) B5118065
theorem B2273369 : Blo 1514954 2273369 := bstep (se 2 (by rfl) ⟨852513, by rfl⟩ : syracuseStep 2273369 = 1705027) B1705027
theorem B17272925 : Blo 1514954 17272925 := bstep (se 3 (by rfl) ⟨3238673, by rfl⟩ : syracuseStep 17272925 = 6477347) B6477347
theorem B3412097 : Blo 1514954 3412097 := bstep (se 2 (by rfl) ⟨1279536, by rfl⟩ : syracuseStep 3412097 = 2559073) B2559073
theorem B2879641 : Blo 1514954 2879641 := bstep (se 2 (by rfl) ⟨1079865, by rfl⟩ : syracuseStep 2879641 = 2159731) B2159731
theorem B1618103 : Blo 1514954 1618103 := bstep (se 1 (by rfl) ⟨1213577, by rfl⟩ : syracuseStep 1618103 = 2427155) B2427155
theorem B2273483 : Blo 1514954 2273483 := bstep (se 1 (by rfl) ⟨1705112, by rfl⟩ : syracuseStep 2273483 = 3410225) B3410225
theorem B2273495 : Blo 1514954 2273495 := bstep (se 1 (by rfl) ⟨1705121, by rfl⟩ : syracuseStep 2273495 = 3410243) B3410243
theorem B5116121 : Blo 1514954 5116121 := bstep (se 2 (by rfl) ⟨1918545, by rfl⟩ : syracuseStep 5116121 = 3837091) B3837091
theorem B2273561 : Blo 1514954 2273561 := bstep (se 2 (by rfl) ⟨852585, by rfl⟩ : syracuseStep 2273561 = 1705171) B1705171
theorem B3412313 : Blo 1514954 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B7672157 : Blo 1514954 7672157 := bstep (se 3 (by rfl) ⟨1438529, by rfl⟩ : syracuseStep 7672157 = 2877059) B2877059
theorem B2273675 : Blo 1514954 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B2273687 : Blo 1514954 2273687 := bstep (se 1 (by rfl) ⟨1705265, by rfl⟩ : syracuseStep 2273687 = 3410531) B3410531
theorem B3838387 : Blo 1514954 3838387 := bstep (se 1 (by rfl) ⟨2878790, by rfl⟩ : syracuseStep 3838387 = 5757581) B5757581
theorem B3412403 : Blo 1514954 3412403 := bstep (se 1 (by rfl) ⟨2559302, by rfl⟩ : syracuseStep 3412403 = 5118605) B5118605
theorem B3412439 : Blo 1514954 3412439 := bstep (se 1 (by rfl) ⟨2559329, by rfl⟩ : syracuseStep 3412439 = 5118659) B5118659
theorem B2273753 : Blo 1514954 2273753 := bstep (se 2 (by rfl) ⟨852657, by rfl⟩ : syracuseStep 2273753 = 1705315) B1705315
theorem B2159065 : Blo 1514954 2159065 := bstep (se 2 (by rfl) ⟨809649, by rfl⟩ : syracuseStep 2159065 = 1619299) B1619299
theorem B3838529 : Blo 1514954 3838529 := bstep (se 2 (by rfl) ⟨1439448, by rfl⟩ : syracuseStep 3838529 = 2878897) B2878897
theorem B2273867 : Blo 1514954 2273867 := bstep (se 1 (by rfl) ⟨1705400, by rfl⟩ : syracuseStep 2273867 = 3410801) B3410801
theorem B2273879 : Blo 1514954 2273879 := bstep (se 1 (by rfl) ⟨1705409, by rfl⟩ : syracuseStep 2273879 = 3410819) B3410819
theorem B1536619 : Blo 1514954 1536619 := bstep (se 1 (by rfl) ⟨1152464, by rfl⟩ : syracuseStep 1536619 = 2304929) B2304929
theorem B3412619 : Blo 1514954 3412619 := bstep (se 1 (by rfl) ⟨2559464, by rfl⟩ : syracuseStep 3412619 = 5118929) B5118929
theorem B2273945 : Blo 1514954 2273945 := bstep (se 2 (by rfl) ⟨852729, by rfl⟩ : syracuseStep 2273945 = 1705459) B1705459
theorem B3412673 : Blo 1514954 3412673 := bstep (se 2 (by rfl) ⟨1279752, by rfl⟩ : syracuseStep 3412673 = 2559505) B2559505
theorem B6148811 : Blo 1514954 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B14570189 : Blo 1514954 14570189 := bstep (se 3 (by rfl) ⟨2731910, by rfl⟩ : syracuseStep 14570189 = 5463821) B5463821
theorem B2274059 : Blo 1514954 2274059 := bstep (se 1 (by rfl) ⟨1705544, by rfl⟩ : syracuseStep 2274059 = 3411089) B3411089
theorem B2274071 : Blo 1514954 2274071 := bstep (se 1 (by rfl) ⟨1705553, by rfl⟩ : syracuseStep 2274071 = 3411107) B3411107
theorem B4436801 : Blo 1514954 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B6148939 : Blo 1514954 6148939 := bstep (se 1 (by rfl) ⟨4611704, by rfl⟩ : syracuseStep 6148939 = 9223409) B9223409
theorem B4854617 : Blo 1514954 4854617 := bstep (se 2 (by rfl) ⟨1820481, by rfl⟩ : syracuseStep 4854617 = 3640963) B3640963
theorem B2274137 : Blo 1514954 2274137 := bstep (se 2 (by rfl) ⟨852801, by rfl⟩ : syracuseStep 2274137 = 1705603) B1705603
theorem B5116823 : Blo 1514954 5116823 := bstep (se 1 (by rfl) ⟨3837617, by rfl⟩ : syracuseStep 5116823 = 7675235) B7675235
theorem B3412889 : Blo 1514954 3412889 := bstep (se 2 (by rfl) ⟨1279833, by rfl⟩ : syracuseStep 3412889 = 2559667) B2559667
theorem B2274251 : Blo 1514954 2274251 := bstep (se 1 (by rfl) ⟨1705688, by rfl⟩ : syracuseStep 2274251 = 3411377) B3411377
theorem B2274263 : Blo 1514954 2274263 := bstep (se 1 (by rfl) ⟨1705697, by rfl⟩ : syracuseStep 2274263 = 3411395) B3411395
theorem B2077655 : Blo 1514954 2077655 := bstep (se 1 (by rfl) ⟨1558241, by rfl⟩ : syracuseStep 2077655 = 3116483) B3116483
theorem B3412979 : Blo 1514954 3412979 := bstep (se 1 (by rfl) ⟨2559734, by rfl⟩ : syracuseStep 3412979 = 5119469) B5119469
theorem B3413015 : Blo 1514954 3413015 := bstep (se 1 (by rfl) ⟨2559761, by rfl⟩ : syracuseStep 3413015 = 5119523) B5119523
theorem B2274329 : Blo 1514954 2274329 := bstep (se 2 (by rfl) ⟨852873, by rfl⟩ : syracuseStep 2274329 = 1705747) B1705747
theorem B2274443 : Blo 1514954 2274443 := bstep (se 1 (by rfl) ⟨1705832, by rfl⟩ : syracuseStep 2274443 = 3411665) B3411665
theorem B4854935 : Blo 1514954 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B2274455 : Blo 1514954 2274455 := bstep (se 1 (by rfl) ⟨1705841, by rfl⟩ : syracuseStep 2274455 = 3411683) B3411683
theorem B2274521 : Blo 1514954 2274521 := bstep (se 2 (by rfl) ⟨852945, by rfl⟩ : syracuseStep 2274521 = 1705891) B1705891
theorem B2733323 : Blo 1514954 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B2274635 : Blo 1514954 2274635 := bstep (se 1 (by rfl) ⟨1705976, by rfl⟩ : syracuseStep 2274635 = 3411953) B3411953
theorem B2274647 : Blo 1514954 2274647 := bstep (se 1 (by rfl) ⟨1705985, by rfl⟩ : syracuseStep 2274647 = 3411971) B3411971
theorem B5756291 : Blo 1514954 5756291 := bstep (se 1 (by rfl) ⟨4317218, by rfl⟩ : syracuseStep 5756291 = 8634437) B8634437
theorem B5756305 : Blo 1514954 5756305 := bstep (se 2 (by rfl) ⟨2158614, by rfl⟩ : syracuseStep 5756305 = 4317229) B4317229
theorem B2274713 : Blo 1514954 2274713 := bstep (se 2 (by rfl) ⟨853017, by rfl⟩ : syracuseStep 2274713 = 1706035) B1706035
theorem B1619371 : Blo 1514954 1619371 := bstep (se 1 (by rfl) ⟨1214528, by rfl⟩ : syracuseStep 1619371 = 2429057) B2429057
theorem B5117363 : Blo 1514954 5117363 := bstep (se 1 (by rfl) ⟨3838022, by rfl⟩ : syracuseStep 5117363 = 7676045) B7676045
theorem B5182913 : Blo 1514954 5182913 := bstep (se 2 (by rfl) ⟨1943592, by rfl⟩ : syracuseStep 5182913 = 3887185) B3887185
theorem B4855243 : Blo 1514954 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B2274827 : Blo 1514954 2274827 := bstep (se 1 (by rfl) ⟨1706120, by rfl⟩ : syracuseStep 2274827 = 3412241) B3412241
theorem B2274839 : Blo 1514954 2274839 := bstep (se 1 (by rfl) ⟨1706129, by rfl⟩ : syracuseStep 2274839 = 3412259) B3412259
theorem B2274905 : Blo 1514954 2274905 := bstep (se 2 (by rfl) ⟨853089, by rfl⟩ : syracuseStep 2274905 = 1706179) B1706179
theorem B5756609 : Blo 1514954 5756609 := bstep (se 2 (by rfl) ⟨2158728, by rfl⟩ : syracuseStep 5756609 = 4317457) B4317457
theorem B5117633 : Blo 1514954 5117633 := bstep (se 2 (by rfl) ⟨1919112, by rfl⟩ : syracuseStep 5117633 = 3838225) B3838225
theorem B2275019 : Blo 1514954 2275019 := bstep (se 1 (by rfl) ⟨1706264, by rfl⟩ : syracuseStep 2275019 = 3412529) B3412529
theorem B2275031 : Blo 1514954 2275031 := bstep (se 1 (by rfl) ⟨1706273, by rfl⟩ : syracuseStep 2275031 = 3412547) B3412547
theorem B2275097 : Blo 1514954 2275097 := bstep (se 2 (by rfl) ⟨853161, by rfl⟩ : syracuseStep 2275097 = 1706323) B1706323
theorem B31135589 : Blo 1514954 31135589 := bstep (se 4 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 31135589 = 5837923) B5837923
theorem B2275211 : Blo 1514954 2275211 := bstep (se 1 (by rfl) ⟨1706408, by rfl⟩ : syracuseStep 2275211 = 3412817) B3412817
theorem B2275223 : Blo 1514954 2275223 := bstep (se 1 (by rfl) ⟨1706417, by rfl⟩ : syracuseStep 2275223 = 3412835) B3412835
theorem B2275289 : Blo 1514954 2275289 := bstep (se 2 (by rfl) ⟨853233, by rfl⟩ : syracuseStep 2275289 = 1706467) B1706467
theorem B4855859 : Blo 1514954 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B11671627 : Blo 1514954 11671627 := bstep (se 1 (by rfl) ⟨8753720, by rfl⟩ : syracuseStep 11671627 = 17507441) B17507441
theorem B2275403 : Blo 1514954 2275403 := bstep (se 1 (by rfl) ⟨1706552, by rfl⟩ : syracuseStep 2275403 = 3413105) B3413105
theorem B2275415 : Blo 1514954 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B9222245 : Blo 1514954 9222245 := bstep (se 4 (by rfl) ⟨864585, by rfl⟩ : syracuseStep 9222245 = 1729171) B1729171
theorem B9222295 : Blo 1514954 9222295 := bstep (se 1 (by rfl) ⟨6916721, by rfl⟩ : syracuseStep 9222295 = 13833443) B13833443
theorem B5118173 : Blo 1514954 5118173 := bstep (se 3 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 5118173 = 1919315) B1919315
theorem B5757277 : Blo 1514954 5757277 := bstep (se 3 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 5757277 = 2158979) B2158979
theorem B49174901 : Blo 1514954 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B8632727 : Blo 1514954 8632727 := bstep (se 1 (by rfl) ⟨6474545, by rfl⟩ : syracuseStep 8632727 = 12949091) B12949091
theorem B7674263 : Blo 1514954 7674263 := bstep (se 1 (by rfl) ⟨5755697, by rfl⟩ : syracuseStep 7674263 = 11511395) B11511395
theorem B3889559 : Blo 1514954 3889559 := bstep (se 1 (by rfl) ⟨2917169, by rfl⟩ : syracuseStep 3889559 = 5834339) B5834339
theorem B6478339 : Blo 1514954 6478339 := bstep (se 1 (by rfl) ⟨4858754, by rfl⟩ : syracuseStep 6478339 = 9717509) B9717509
theorem B12950117 : Blo 1514954 12950117 := bstep (se 4 (by rfl) ⟨1214073, by rfl⟩ : syracuseStep 12950117 = 2428147) B2428147
theorem B18430669 : Blo 1514954 18430669 := bstep (se 3 (by rfl) ⟨3455750, by rfl⟩ : syracuseStep 18430669 = 6911501) B6911501
theorem B24591221 : Blo 1514954 24591221 := bstep (se 5 (by rfl) ⟨1152713, by rfl⟩ : syracuseStep 24591221 = 2305427) B2305427
theorem B9714563 : Blo 1514954 9714563 := bstep (se 1 (by rfl) ⟨7285922, by rfl⟩ : syracuseStep 9714563 = 14571845) B14571845
theorem B4316125 : Blo 1514954 4316125 := bstep (se 3 (by rfl) ⟨809273, by rfl⟩ : syracuseStep 4316125 = 1618547) B1618547
theorem B9215041 : Blo 1514954 9215041 := bstep (se 2 (by rfl) ⟨3455640, by rfl⟩ : syracuseStep 9215041 = 6911281) B6911281
theorem B1727671 : Blo 1514954 1727671 := bstep (se 1 (by rfl) ⟨1295753, by rfl⟩ : syracuseStep 1727671 = 2591507) B2591507
theorem B2104535 : Blo 1514954 2104535 := bstep (se 1 (by rfl) ⟨1578401, by rfl⟩ : syracuseStep 2104535 = 3156803) B3156803
theorem B5119307 : Blo 1514954 5119307 := bstep (se 1 (by rfl) ⟨3839480, by rfl⟩ : syracuseStep 5119307 = 7678961) B7678961
theorem B6479297 : Blo 1514954 6479297 := bstep (se 2 (by rfl) ⟨2429736, by rfl⟩ : syracuseStep 6479297 = 4859473) B4859473
theorem B1514955 : Blo 1514954 1514955 := bstep (se 1 (by rfl) ⟨1136216, by rfl⟩ : syracuseStep 1514955 = 2272433) B2272433
theorem B1514967 : Blo 1514954 1514967 := bstep (se 1 (by rfl) ⟨1136225, by rfl⟩ : syracuseStep 1514967 = 2272451) B2272451
theorem B1514987 : Blo 1514954 1514987 := bstep (se 1 (by rfl) ⟨1136240, by rfl⟩ : syracuseStep 1514987 = 2272481) B2272481
theorem B1514999 : Blo 1514954 1514999 := bstep (se 1 (by rfl) ⟨1136249, by rfl⟩ : syracuseStep 1514999 = 2272499) B2272499
theorem B1515019 : Blo 1514954 1515019 := bstep (se 1 (by rfl) ⟨1136264, by rfl⟩ : syracuseStep 1515019 = 2272529) B2272529
theorem B1515031 : Blo 1514954 1515031 := bstep (se 1 (by rfl) ⟨1136273, by rfl⟩ : syracuseStep 1515031 = 2272547) B2272547
theorem B1515051 : Blo 1514954 1515051 := bstep (se 1 (by rfl) ⟨1136288, by rfl⟩ : syracuseStep 1515051 = 2272577) B2272577
theorem B1515063 : Blo 1514954 1515063 := bstep (se 1 (by rfl) ⟨1136297, by rfl⟩ : syracuseStep 1515063 = 2272595) B2272595
theorem B1515083 : Blo 1514954 1515083 := bstep (se 1 (by rfl) ⟨1136312, by rfl⟩ : syracuseStep 1515083 = 2272625) B2272625
theorem B1515095 : Blo 1514954 1515095 := bstep (se 1 (by rfl) ⟨1136321, by rfl⟩ : syracuseStep 1515095 = 2272643) B2272643
theorem B5758553 : Blo 1514954 5758553 := bstep (se 2 (by rfl) ⟨2159457, by rfl⟩ : syracuseStep 5758553 = 4318915) B4318915
theorem B5119577 : Blo 1514954 5119577 := bstep (se 2 (by rfl) ⟨1919841, by rfl⟩ : syracuseStep 5119577 = 3839683) B3839683
theorem B1515115 : Blo 1514954 1515115 := bstep (se 1 (by rfl) ⟨1136336, by rfl⟩ : syracuseStep 1515115 = 2272673) B2272673
theorem B1515127 : Blo 1514954 1515127 := bstep (se 1 (by rfl) ⟨1136345, by rfl⟩ : syracuseStep 1515127 = 2272691) B2272691
theorem B1515147 : Blo 1514954 1515147 := bstep (se 1 (by rfl) ⟨1136360, by rfl⟩ : syracuseStep 1515147 = 2272721) B2272721
theorem B1515159 : Blo 1514954 1515159 := bstep (se 1 (by rfl) ⟨1136369, by rfl⟩ : syracuseStep 1515159 = 2272739) B2272739
theorem B1515179 : Blo 1514954 1515179 := bstep (se 1 (by rfl) ⟨1136384, by rfl⟩ : syracuseStep 1515179 = 2272769) B2272769
theorem B1515191 : Blo 1514954 1515191 := bstep (se 1 (by rfl) ⟨1136393, by rfl⟩ : syracuseStep 1515191 = 2272787) B2272787
theorem B1515211 : Blo 1514954 1515211 := bstep (se 1 (by rfl) ⟨1136408, by rfl⟩ : syracuseStep 1515211 = 2272817) B2272817
theorem B1515223 : Blo 1514954 1515223 := bstep (se 1 (by rfl) ⟨1136417, by rfl⟩ : syracuseStep 1515223 = 2272835) B2272835
theorem B1515243 : Blo 1514954 1515243 := bstep (se 1 (by rfl) ⟨1136432, by rfl⟩ : syracuseStep 1515243 = 2272865) B2272865
theorem B1515255 : Blo 1514954 1515255 := bstep (se 1 (by rfl) ⟨1136441, by rfl⟩ : syracuseStep 1515255 = 2272883) B2272883
theorem B1515275 : Blo 1514954 1515275 := bstep (se 1 (by rfl) ⟨1136456, by rfl⟩ : syracuseStep 1515275 = 2272913) B2272913
theorem B11517713 : Blo 1514954 11517713 := bstep (se 2 (by rfl) ⟨4319142, by rfl⟩ : syracuseStep 11517713 = 8638285) B8638285
theorem B8199953 : Blo 1514954 8199953 := bstep (se 2 (by rfl) ⟨3074982, by rfl⟩ : syracuseStep 8199953 = 6149965) B6149965
theorem B1515287 : Blo 1514954 1515287 := bstep (se 1 (by rfl) ⟨1136465, by rfl⟩ : syracuseStep 1515287 = 2272931) B2272931
theorem B1515307 : Blo 1514954 1515307 := bstep (se 1 (by rfl) ⟨1136480, by rfl⟩ : syracuseStep 1515307 = 2272961) B2272961
theorem B9707309 : Blo 1514954 9707309 := bstep (se 3 (by rfl) ⟨1820120, by rfl⟩ : syracuseStep 9707309 = 3640241) B3640241
theorem B1515319 : Blo 1514954 1515319 := bstep (se 1 (by rfl) ⟨1136489, by rfl⟩ : syracuseStep 1515319 = 2272979) B2272979
theorem B1515339 : Blo 1514954 1515339 := bstep (se 1 (by rfl) ⟨1136504, by rfl⟩ : syracuseStep 1515339 = 2273009) B2273009
theorem B1515351 : Blo 1514954 1515351 := bstep (se 1 (by rfl) ⟨1136513, by rfl⟩ : syracuseStep 1515351 = 2273027) B2273027
theorem B1515371 : Blo 1514954 1515371 := bstep (se 1 (by rfl) ⟨1136528, by rfl⟩ : syracuseStep 1515371 = 2273057) B2273057
theorem B16400245 : Blo 1514954 16400245 := bstep (se 5 (by rfl) ⟨768761, by rfl⟩ : syracuseStep 16400245 = 1537523) B1537523
theorem B1515383 : Blo 1514954 1515383 := bstep (se 1 (by rfl) ⟨1136537, by rfl⟩ : syracuseStep 1515383 = 2273075) B2273075
theorem B1515403 : Blo 1514954 1515403 := bstep (se 1 (by rfl) ⟨1136552, by rfl⟩ : syracuseStep 1515403 = 2273105) B2273105
theorem B3235735 : Blo 1514954 3235735 := bstep (se 1 (by rfl) ⟨2426801, by rfl⟩ : syracuseStep 3235735 = 4853603) B4853603
theorem B1515415 : Blo 1514954 1515415 := bstep (se 1 (by rfl) ⟨1136561, by rfl⟩ : syracuseStep 1515415 = 2273123) B2273123
theorem B1515435 : Blo 1514954 1515435 := bstep (se 1 (by rfl) ⟨1136576, by rfl⟩ : syracuseStep 1515435 = 2273153) B2273153
theorem B55312307 : Blo 1514954 55312307 := bstep (se 1 (by rfl) ⟨41484230, by rfl⟩ : syracuseStep 55312307 = 82968461) B82968461
theorem B1515447 : Blo 1514954 1515447 := bstep (se 1 (by rfl) ⟨1136585, by rfl⟩ : syracuseStep 1515447 = 2273171) B2273171
theorem B1515467 : Blo 1514954 1515467 := bstep (se 1 (by rfl) ⟨1136600, by rfl⟩ : syracuseStep 1515467 = 2273201) B2273201
theorem B1515479 : Blo 1514954 1515479 := bstep (se 1 (by rfl) ⟨1136609, by rfl⟩ : syracuseStep 1515479 = 2273219) B2273219
theorem B1515499 : Blo 1514954 1515499 := bstep (se 1 (by rfl) ⟨1136624, by rfl⟩ : syracuseStep 1515499 = 2273249) B2273249
theorem B1515511 : Blo 1514954 1515511 := bstep (se 1 (by rfl) ⟨1136633, by rfl⟩ : syracuseStep 1515511 = 2273267) B2273267
theorem B1515527 : Blo 1514954 1515527 := bstep (se 1 (by rfl) ⟨1136645, by rfl⟩ : syracuseStep 1515527 = 2273291) B2273291
theorem B1515535 : Blo 1514954 1515535 := bstep (se 1 (by rfl) ⟨1136651, by rfl⟩ : syracuseStep 1515535 = 2273303) B2273303
theorem B12288023 : Blo 1514954 12288023 := bstep (se 1 (by rfl) ⟨9216017, by rfl⟩ : syracuseStep 12288023 = 18432035) B18432035
theorem B1515579 : Blo 1514954 1515579 := bstep (se 1 (by rfl) ⟨1136684, by rfl⟩ : syracuseStep 1515579 = 2273369) B2273369
theorem B1515655 : Blo 1514954 1515655 := bstep (se 1 (by rfl) ⟨1136741, by rfl⟩ : syracuseStep 1515655 = 2273483) B2273483
theorem B1515663 : Blo 1514954 1515663 := bstep (se 1 (by rfl) ⟨1136747, by rfl⟩ : syracuseStep 1515663 = 2273495) B2273495
theorem B1515707 : Blo 1514954 1515707 := bstep (se 1 (by rfl) ⟨1136780, by rfl⟩ : syracuseStep 1515707 = 2273561) B2273561
theorem B2916553 : Blo 1514954 2916553 := bstep (se 2 (by rfl) ⟨1093707, by rfl⟩ : syracuseStep 2916553 = 2187415) B2187415
theorem B12296393 : Blo 1514954 12296393 := bstep (se 2 (by rfl) ⟨4611147, by rfl⟩ : syracuseStep 12296393 = 9222295) B9222295
theorem B1515783 : Blo 1514954 1515783 := bstep (se 1 (by rfl) ⟨1136837, by rfl⟩ : syracuseStep 1515783 = 2273675) B2273675
theorem B1515791 : Blo 1514954 1515791 := bstep (se 1 (by rfl) ⟨1136843, by rfl⟩ : syracuseStep 1515791 = 2273687) B2273687
theorem B1515835 : Blo 1514954 1515835 := bstep (se 1 (by rfl) ⟨1136876, by rfl⟩ : syracuseStep 1515835 = 2273753) B2273753
theorem B1515911 : Blo 1514954 1515911 := bstep (se 1 (by rfl) ⟨1136933, by rfl⟩ : syracuseStep 1515911 = 2273867) B2273867
theorem B1515919 : Blo 1514954 1515919 := bstep (se 1 (by rfl) ⟨1136939, by rfl⟩ : syracuseStep 1515919 = 2273879) B2273879
theorem B1917371 : Blo 1514954 1917371 := bstep (se 1 (by rfl) ⟨1438028, by rfl⟩ : syracuseStep 1917371 = 2876057) B2876057
theorem B1704379 : Blo 1514954 1704379 := bstep (se 1 (by rfl) ⟨1278284, by rfl⟩ : syracuseStep 1704379 = 2556569) B2556569
theorem B1515963 : Blo 1514954 1515963 := bstep (se 1 (by rfl) ⟨1136972, by rfl⟩ : syracuseStep 1515963 = 2273945) B2273945
theorem B7676369 : Blo 1514954 7676369 := bstep (se 2 (by rfl) ⟨2878638, by rfl⟩ : syracuseStep 7676369 = 5757277) B5757277
theorem B18432515 : Blo 1514954 18432515 := bstep (se 1 (by rfl) ⟨13824386, by rfl⟩ : syracuseStep 18432515 = 27648773) B27648773
theorem B1516039 : Blo 1514954 1516039 := bstep (se 1 (by rfl) ⟨1137029, by rfl⟩ : syracuseStep 1516039 = 2274059) B2274059
theorem B1516047 : Blo 1514954 1516047 := bstep (se 1 (by rfl) ⟨1137035, by rfl⟩ : syracuseStep 1516047 = 2274071) B2274071
theorem B2957867 : Blo 1514954 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B3236411 : Blo 1514954 3236411 := bstep (se 1 (by rfl) ⟨2427308, by rfl⟩ : syracuseStep 3236411 = 4854617) B4854617
theorem B1516091 : Blo 1514954 1516091 := bstep (se 1 (by rfl) ⟨1137068, by rfl⟩ : syracuseStep 1516091 = 2274137) B2274137
theorem B5612093 : Blo 1514954 5612093 := bstep (se 3 (by rfl) ⟨1052267, by rfl⟩ : syracuseStep 5612093 = 2104535) B2104535
theorem B2556535 : Blo 1514954 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B2048647 : Blo 1514954 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B1516167 : Blo 1514954 1516167 := bstep (se 1 (by rfl) ⟨1137125, by rfl⟩ : syracuseStep 1516167 = 2274251) B2274251
theorem B1516175 : Blo 1514954 1516175 := bstep (se 1 (by rfl) ⟨1137131, by rfl⟩ : syracuseStep 1516175 = 2274263) B2274263
theorem B1516219 : Blo 1514954 1516219 := bstep (se 1 (by rfl) ⟨1137164, by rfl⟩ : syracuseStep 1516219 = 2274329) B2274329
theorem B1516295 : Blo 1514954 1516295 := bstep (se 1 (by rfl) ⟨1137221, by rfl⟩ : syracuseStep 1516295 = 2274443) B2274443
theorem B1516303 : Blo 1514954 1516303 := bstep (se 1 (by rfl) ⟨1137227, by rfl⟩ : syracuseStep 1516303 = 2274455) B2274455
theorem B8635187 : Blo 1514954 8635187 := bstep (se 1 (by rfl) ⟨6476390, by rfl⟩ : syracuseStep 8635187 = 12952781) B12952781
theorem B2048825 : Blo 1514954 2048825 := bstep (se 2 (by rfl) ⟨768309, by rfl⟩ : syracuseStep 2048825 = 1536619) B1536619
theorem B2556731 : Blo 1514954 2556731 := bstep (se 1 (by rfl) ⟨1917548, by rfl⟩ : syracuseStep 2556731 = 3835097) B3835097
theorem B1516347 : Blo 1514954 1516347 := bstep (se 1 (by rfl) ⟨1137260, by rfl⟩ : syracuseStep 1516347 = 2274521) B2274521
theorem B1516423 : Blo 1514954 1516423 := bstep (se 1 (by rfl) ⟨1137317, by rfl⟩ : syracuseStep 1516423 = 2274635) B2274635
theorem B1704847 : Blo 1514954 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B1516431 : Blo 1514954 1516431 := bstep (se 1 (by rfl) ⟨1137323, by rfl⟩ : syracuseStep 1516431 = 2274647) B2274647
theorem B1516475 : Blo 1514954 1516475 := bstep (se 1 (by rfl) ⟨1137356, by rfl⟩ : syracuseStep 1516475 = 2274713) B2274713
theorem B1516551 : Blo 1514954 1516551 := bstep (se 1 (by rfl) ⟨1137413, by rfl⟩ : syracuseStep 1516551 = 2274827) B2274827
theorem B3408911 : Blo 1514954 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B1516559 : Blo 1514954 1516559 := bstep (se 1 (by rfl) ⟨1137419, by rfl⟩ : syracuseStep 1516559 = 2274839) B2274839
theorem B3408929 : Blo 1514954 3408929 := bstep (se 2 (by rfl) ⟨1278348, by rfl⟩ : syracuseStep 3408929 = 2556697) B2556697
theorem B3236897 : Blo 1514954 3236897 := bstep (se 2 (by rfl) ⟨1213836, by rfl⟩ : syracuseStep 3236897 = 2427673) B2427673
theorem B1516603 : Blo 1514954 1516603 := bstep (se 1 (by rfl) ⟨1137452, by rfl⟩ : syracuseStep 1516603 = 2274905) B2274905
theorem B10372157 : Blo 1514954 10372157 := bstep (se 3 (by rfl) ⟨1944779, by rfl⟩ : syracuseStep 10372157 = 3889559) B3889559
theorem B1516679 : Blo 1514954 1516679 := bstep (se 1 (by rfl) ⟨1137509, by rfl⟩ : syracuseStep 1516679 = 2275019) B2275019
theorem B1516687 : Blo 1514954 1516687 := bstep (se 1 (by rfl) ⟨1137515, by rfl⟩ : syracuseStep 1516687 = 2275031) B2275031
theorem B3458195 : Blo 1514954 3458195 := bstep (se 1 (by rfl) ⟨2593646, by rfl⟩ : syracuseStep 3458195 = 5187293) B5187293
theorem B13821101 : Blo 1514954 13821101 := bstep (se 3 (by rfl) ⟨2591456, by rfl⟩ : syracuseStep 13821101 = 5182913) B5182913
theorem B1516731 : Blo 1514954 1516731 := bstep (se 1 (by rfl) ⟨1137548, by rfl⟩ : syracuseStep 1516731 = 2275097) B2275097
theorem B2557129 : Blo 1514954 2557129 := bstep (se 2 (by rfl) ⟨958923, by rfl⟩ : syracuseStep 2557129 = 1917847) B1917847
theorem B1516807 : Blo 1514954 1516807 := bstep (se 1 (by rfl) ⟨1137605, by rfl⟩ : syracuseStep 1516807 = 2275211) B2275211
theorem B3835147 : Blo 1514954 3835147 := bstep (se 1 (by rfl) ⟨2876360, by rfl⟩ : syracuseStep 3835147 = 5752721) B5752721
theorem B1516815 : Blo 1514954 1516815 := bstep (se 1 (by rfl) ⟨1137611, by rfl⟩ : syracuseStep 1516815 = 2275223) B2275223
theorem B1516859 : Blo 1514954 1516859 := bstep (se 1 (by rfl) ⟨1137644, by rfl⟩ : syracuseStep 1516859 = 2275289) B2275289
theorem B3237239 : Blo 1514954 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B3409271 : Blo 1514954 3409271 := bstep (se 1 (by rfl) ⟨2556953, by rfl⟩ : syracuseStep 3409271 = 5113907) B5113907
theorem B132892039 : Blo 1514954 132892039 := bstep (se 1 (by rfl) ⟨99669029, by rfl⟩ : syracuseStep 132892039 = 199338059) B199338059
theorem B1918343 : Blo 1514954 1918343 := bstep (se 1 (by rfl) ⟨1438757, by rfl⟩ : syracuseStep 1918343 = 2877515) B2877515
theorem B1705351 : Blo 1514954 1705351 := bstep (se 1 (by rfl) ⟨1279013, by rfl⟩ : syracuseStep 1705351 = 2558027) B2558027
theorem B1516935 : Blo 1514954 1516935 := bstep (se 1 (by rfl) ⟨1137701, by rfl⟩ : syracuseStep 1516935 = 2275403) B2275403
theorem B1516943 : Blo 1514954 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B7988633 : Blo 1514954 7988633 := bstep (se 2 (by rfl) ⟨2995737, by rfl⟩ : syracuseStep 7988633 = 5991475) B5991475
theorem B3835289 : Blo 1514954 3835289 := bstep (se 2 (by rfl) ⟨1438233, by rfl⟩ : syracuseStep 3835289 = 2876467) B2876467
theorem B3409451 : Blo 1514954 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B3835451 : Blo 1514954 3835451 := bstep (se 1 (by rfl) ⟨2876588, by rfl⟩ : syracuseStep 3835451 = 5753177) B5753177
theorem B1705531 : Blo 1514954 1705531 := bstep (se 1 (by rfl) ⟨1279148, by rfl⟩ : syracuseStep 1705531 = 2558297) B2558297
theorem B2303561 : Blo 1514954 2303561 := bstep (se 2 (by rfl) ⟨863835, by rfl⟩ : syracuseStep 2303561 = 1727671) B1727671
theorem B2877113 : Blo 1514954 2877113 := bstep (se 2 (by rfl) ⟨1078917, by rfl⟩ : syracuseStep 2877113 = 2157835) B2157835
theorem B17278757 : Blo 1514954 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B5752691 : Blo 1514954 5752691 := bstep (se 1 (by rfl) ⟨4314518, by rfl⟩ : syracuseStep 5752691 = 8629037) B8629037
theorem B2557831 : Blo 1514954 2557831 := bstep (se 1 (by rfl) ⟨1918373, by rfl⟩ : syracuseStep 2557831 = 3836747) B3836747
theorem B3835795 : Blo 1514954 3835795 := bstep (se 1 (by rfl) ⟨2876846, by rfl⟩ : syracuseStep 3835795 = 5753693) B5753693
theorem B3409811 : Blo 1514954 3409811 := bstep (se 1 (by rfl) ⟨2557358, by rfl⟩ : syracuseStep 3409811 = 5114717) B5114717
theorem B16394147 : Blo 1514954 16394147 := bstep (se 1 (by rfl) ⟨12295610, by rfl⟩ : syracuseStep 16394147 = 24591221) B24591221
theorem B6473657 : Blo 1514954 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B3409865 : Blo 1514954 3409865 := bstep (se 2 (by rfl) ⟨1278699, by rfl⟩ : syracuseStep 3409865 = 2557399) B2557399
theorem B1918991 : Blo 1514954 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B1705999 : Blo 1514954 1705999 := bstep (se 1 (by rfl) ⟨1279499, by rfl⟩ : syracuseStep 1705999 = 2558999) B2558999
theorem B3835937 : Blo 1514954 3835937 := bstep (se 2 (by rfl) ⟨1438476, by rfl⟩ : syracuseStep 3835937 = 2876953) B2876953
theorem B8636645 : Blo 1514954 8636645 := bstep (se 4 (by rfl) ⟨809685, by rfl⟩ : syracuseStep 8636645 = 1619371) B1619371
theorem B6473965 : Blo 1514954 6473965 := bstep (se 3 (by rfl) ⟨1213868, by rfl⟩ : syracuseStep 6473965 = 2427737) B2427737
theorem B6473999 : Blo 1514954 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B4319531 : Blo 1514954 4319531 := bstep (se 1 (by rfl) ⟨3239648, by rfl⟩ : syracuseStep 4319531 = 6479297) B6479297
theorem B21866993 : Blo 1514954 21866993 := bstep (se 2 (by rfl) ⟨8200122, by rfl⟩ : syracuseStep 21866993 = 16400245) B16400245
theorem B1706503 : Blo 1514954 1706503 := bstep (se 1 (by rfl) ⟨1279877, by rfl⟩ : syracuseStep 1706503 = 2559755) B2559755
theorem B7678475 : Blo 1514954 7678475 := bstep (se 1 (by rfl) ⟨5758856, by rfl⟩ : syracuseStep 7678475 = 11517713) B11517713
theorem B5466635 : Blo 1514954 5466635 := bstep (se 1 (by rfl) ⟨4099976, by rfl⟩ : syracuseStep 5466635 = 8199953) B8199953
theorem B2558479 : Blo 1514954 2558479 := bstep (se 1 (by rfl) ⟨1918859, by rfl⟩ : syracuseStep 2558479 = 3837719) B3837719
theorem B4098593 : Blo 1514954 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B19417643 : Blo 1514954 19417643 := bstep (se 1 (by rfl) ⟨14563232, by rfl⟩ : syracuseStep 19417643 = 29126465) B29126465
theorem B5540413 : Blo 1514954 5540413 := bstep (se 3 (by rfl) ⟨1038827, by rfl⟩ : syracuseStep 5540413 = 2077655) B2077655
theorem B36874871 : Blo 1514954 36874871 := bstep (se 1 (by rfl) ⟨27656153, by rfl⟩ : syracuseStep 36874871 = 55312307) B55312307
theorem B15993463 : Blo 1514954 15993463 := bstep (se 1 (by rfl) ⟨11995097, by rfl⟩ : syracuseStep 15993463 = 23990195) B23990195
theorem B3410567 : Blo 1514954 3410567 := bstep (se 1 (by rfl) ⟨2557925, by rfl⟩ : syracuseStep 3410567 = 5115851) B5115851
theorem B8637101 : Blo 1514954 8637101 := bstep (se 3 (by rfl) ⟨1619456, by rfl⟩ : syracuseStep 8637101 = 3238913) B3238913
theorem B7678637 : Blo 1514954 7678637 := bstep (se 3 (by rfl) ⟨1439744, by rfl⟩ : syracuseStep 7678637 = 2879489) B2879489
theorem B3410747 : Blo 1514954 3410747 := bstep (se 1 (by rfl) ⟨2558060, by rfl⟩ : syracuseStep 3410747 = 5116121) B5116121
theorem B2878267 : Blo 1514954 2878267 := bstep (se 1 (by rfl) ⟨2158700, by rfl⟩ : syracuseStep 2878267 = 4317401) B4317401
theorem B5114771 : Blo 1514954 5114771 := bstep (se 1 (by rfl) ⟨3836078, by rfl⟩ : syracuseStep 5114771 = 7672157) B7672157
theorem B3410873 : Blo 1514954 3410873 := bstep (se 2 (by rfl) ⟨1279077, by rfl⟩ : syracuseStep 3410873 = 2558155) B2558155
theorem B3836929 : Blo 1514954 3836929 := bstep (se 2 (by rfl) ⟨1438848, by rfl⟩ : syracuseStep 3836929 = 2877697) B2877697
theorem B2305039 : Blo 1514954 2305039 := bstep (se 1 (by rfl) ⟨1728779, by rfl⟩ : syracuseStep 2305039 = 3457559) B3457559
theorem B2559019 : Blo 1514954 2559019 := bstep (se 1 (by rfl) ⟨1919264, by rfl⟩ : syracuseStep 2559019 = 3838529) B3838529
theorem B12946493 : Blo 1514954 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B2559161 : Blo 1514954 2559161 := bstep (se 2 (by rfl) ⟨959685, by rfl⟩ : syracuseStep 2559161 = 1919371) B1919371
theorem B2272457 : Blo 1514954 2272457 := bstep (se 2 (by rfl) ⟨852171, by rfl⟩ : syracuseStep 2272457 = 1704343) B1704343
theorem B8752357 : Blo 1514954 8752357 := bstep (se 4 (by rfl) ⟨820533, by rfl⟩ : syracuseStep 8752357 = 1641067) B1641067
theorem B3411215 : Blo 1514954 3411215 := bstep (se 1 (by rfl) ⟨2558411, by rfl⟩ : syracuseStep 3411215 = 5116823) B5116823
theorem B8629537 : Blo 1514954 8629537 := bstep (se 2 (by rfl) ⟨3236076, by rfl⟩ : syracuseStep 8629537 = 6472153) B6472153
theorem B3411233 : Blo 1514954 3411233 := bstep (se 2 (by rfl) ⟨1279212, by rfl⟩ : syracuseStep 3411233 = 2558425) B2558425
theorem B2878753 : Blo 1514954 2878753 := bstep (se 2 (by rfl) ⟨1079532, by rfl⟩ : syracuseStep 2878753 = 2159065) B2159065
theorem B2272571 : Blo 1514954 2272571 := bstep (se 1 (by rfl) ⟨1704428, by rfl⟩ : syracuseStep 2272571 = 3408857) B3408857
theorem B8637785 : Blo 1514954 8637785 := bstep (se 2 (by rfl) ⟨3239169, by rfl⟩ : syracuseStep 8637785 = 6478339) B6478339
theorem B2272631 : Blo 1514954 2272631 := bstep (se 1 (by rfl) ⟨1704473, by rfl⟩ : syracuseStep 2272631 = 3408947) B3408947
theorem B2157943 : Blo 1514954 2157943 := bstep (se 1 (by rfl) ⟨1618457, by rfl⟩ : syracuseStep 2157943 = 3236915) B3236915
theorem B2272655 : Blo 1514954 2272655 := bstep (se 1 (by rfl) ⟨1704491, by rfl⟩ : syracuseStep 2272655 = 3408983) B3408983
theorem B7671185 : Blo 1514954 7671185 := bstep (se 2 (by rfl) ⟨2876694, by rfl⟩ : syracuseStep 7671185 = 5753389) B5753389
theorem B2272697 : Blo 1514954 2272697 := bstep (se 2 (by rfl) ⟨852261, by rfl⟩ : syracuseStep 2272697 = 1704523) B1704523
theorem B2272775 : Blo 1514954 2272775 := bstep (se 1 (by rfl) ⟨1704581, by rfl⟩ : syracuseStep 2272775 = 3409163) B3409163
theorem B2272811 : Blo 1514954 2272811 := bstep (se 1 (by rfl) ⟨1704608, by rfl⟩ : syracuseStep 2272811 = 3409217) B3409217
theorem B2272841 : Blo 1514954 2272841 := bstep (se 2 (by rfl) ⟨852315, by rfl⟩ : syracuseStep 2272841 = 1704631) B1704631
theorem B3837527 : Blo 1514954 3837527 := bstep (se 1 (by rfl) ⟨2878145, by rfl⟩ : syracuseStep 3837527 = 5756291) B5756291
theorem B3411575 : Blo 1514954 3411575 := bstep (se 1 (by rfl) ⟨2558681, by rfl⟩ : syracuseStep 3411575 = 5117363) B5117363
theorem B2272955 : Blo 1514954 2272955 := bstep (se 1 (by rfl) ⟨1704716, by rfl⟩ : syracuseStep 2272955 = 3409433) B3409433
theorem B4853449 : Blo 1514954 4853449 := bstep (se 2 (by rfl) ⟨1820043, by rfl⟩ : syracuseStep 4853449 = 3640087) B3640087
theorem B2273015 : Blo 1514954 2273015 := bstep (se 1 (by rfl) ⟨1704761, by rfl⟩ : syracuseStep 2273015 = 3409523) B3409523
theorem B2273039 : Blo 1514954 2273039 := bstep (se 1 (by rfl) ⟨1704779, by rfl⟩ : syracuseStep 2273039 = 3409559) B3409559
theorem B3837739 : Blo 1514954 3837739 := bstep (se 1 (by rfl) ⟨2878304, by rfl⟩ : syracuseStep 3837739 = 5756609) B5756609
theorem B3411755 : Blo 1514954 3411755 := bstep (se 1 (by rfl) ⟨2558816, by rfl⟩ : syracuseStep 3411755 = 5117633) B5117633
theorem B2273081 : Blo 1514954 2273081 := bstep (se 2 (by rfl) ⟨852405, by rfl⟩ : syracuseStep 2273081 = 1704811) B1704811
theorem B2273159 : Blo 1514954 2273159 := bstep (se 1 (by rfl) ⟨1704869, by rfl⟩ : syracuseStep 2273159 = 3409739) B3409739
theorem B2273195 : Blo 1514954 2273195 := bstep (se 1 (by rfl) ⟨1704896, by rfl⟩ : syracuseStep 2273195 = 3409793) B3409793
theorem B3837881 : Blo 1514954 3837881 := bstep (se 2 (by rfl) ⟨1439205, by rfl⟩ : syracuseStep 3837881 = 2878411) B2878411
theorem B2273225 : Blo 1514954 2273225 := bstep (se 2 (by rfl) ⟨852459, by rfl⟩ : syracuseStep 2273225 = 1704919) B1704919
theorem B5754833 : Blo 1514954 5754833 := bstep (se 2 (by rfl) ⟨2158062, by rfl⟩ : syracuseStep 5754833 = 4316125) B4316125
theorem B2273339 : Blo 1514954 2273339 := bstep (se 1 (by rfl) ⟨1705004, by rfl⟩ : syracuseStep 2273339 = 3410009) B3410009
theorem B6148163 : Blo 1514954 6148163 := bstep (se 1 (by rfl) ⟨4611122, by rfl⟩ : syracuseStep 6148163 = 9222245) B9222245
theorem B504868949 : Blo 1514954 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B2273399 : Blo 1514954 2273399 := bstep (se 1 (by rfl) ⟨1705049, by rfl⟩ : syracuseStep 2273399 = 3410099) B3410099
theorem B2273423 : Blo 1514954 2273423 := bstep (se 1 (by rfl) ⟨1705067, by rfl⟩ : syracuseStep 2273423 = 3410135) B3410135
theorem B3412115 : Blo 1514954 3412115 := bstep (se 1 (by rfl) ⟨2559086, by rfl⟩ : syracuseStep 3412115 = 5118173) B5118173
theorem B2273465 : Blo 1514954 2273465 := bstep (se 2 (by rfl) ⟨852549, by rfl⟩ : syracuseStep 2273465 = 1705099) B1705099
theorem B3412169 : Blo 1514954 3412169 := bstep (se 2 (by rfl) ⟨1279563, by rfl⟩ : syracuseStep 3412169 = 2559127) B2559127
theorem B2273543 : Blo 1514954 2273543 := bstep (se 1 (by rfl) ⟨1705157, by rfl⟩ : syracuseStep 2273543 = 3410315) B3410315
theorem B5755151 : Blo 1514954 5755151 := bstep (se 1 (by rfl) ⟨4316363, by rfl⟩ : syracuseStep 5755151 = 8632727) B8632727
theorem B5116175 : Blo 1514954 5116175 := bstep (se 1 (by rfl) ⟨3837131, by rfl⟩ : syracuseStep 5116175 = 7674263) B7674263
theorem B2273579 : Blo 1514954 2273579 := bstep (se 1 (by rfl) ⟨1705184, by rfl⟩ : syracuseStep 2273579 = 3410369) B3410369
theorem B2273609 : Blo 1514954 2273609 := bstep (se 2 (by rfl) ⟨852603, by rfl⟩ : syracuseStep 2273609 = 1705207) B1705207
theorem B13832633 : Blo 1514954 13832633 := bstep (se 2 (by rfl) ⟨5187237, by rfl⟩ : syracuseStep 13832633 = 10374475) B10374475
theorem B1618363 : Blo 1514954 1618363 := bstep (se 1 (by rfl) ⟨1213772, by rfl⟩ : syracuseStep 1618363 = 2427545) B2427545
theorem B2273723 : Blo 1514954 2273723 := bstep (se 1 (by rfl) ⟨1705292, by rfl⟩ : syracuseStep 2273723 = 3410585) B3410585
theorem B2273783 : Blo 1514954 2273783 := bstep (se 1 (by rfl) ⟨1705337, by rfl⟩ : syracuseStep 2273783 = 3410675) B3410675
theorem B2273807 : Blo 1514954 2273807 := bstep (se 1 (by rfl) ⟨1705355, by rfl⟩ : syracuseStep 2273807 = 3410711) B3410711
theorem B8630813 : Blo 1514954 8630813 := bstep (se 3 (by rfl) ⟨1618277, by rfl⟩ : syracuseStep 8630813 = 3236555) B3236555
theorem B5116445 : Blo 1514954 5116445 := bstep (se 3 (by rfl) ⟨959333, by rfl⟩ : syracuseStep 5116445 = 1918667) B1918667
theorem B16396829 : Blo 1514954 16396829 := bstep (se 3 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 16396829 = 6148811) B6148811
theorem B2273849 : Blo 1514954 2273849 := bstep (se 2 (by rfl) ⟨852693, by rfl⟩ : syracuseStep 2273849 = 1705387) B1705387
theorem B27669059 : Blo 1514954 27669059 := bstep (se 1 (by rfl) ⟨20751794, by rfl⟩ : syracuseStep 27669059 = 41503589) B41503589
theorem B6476375 : Blo 1514954 6476375 := bstep (se 1 (by rfl) ⟨4857281, by rfl⟩ : syracuseStep 6476375 = 9714563) B9714563
theorem B2273927 : Blo 1514954 2273927 := bstep (se 1 (by rfl) ⟨1705445, by rfl⟩ : syracuseStep 2273927 = 3410891) B3410891
theorem B1897103 : Blo 1514954 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B2273963 : Blo 1514954 2273963 := bstep (se 1 (by rfl) ⟨1705472, by rfl⟩ : syracuseStep 2273963 = 3410945) B3410945
theorem B2273993 : Blo 1514954 2273993 := bstep (se 2 (by rfl) ⟨852747, by rfl⟩ : syracuseStep 2273993 = 1705495) B1705495
theorem B9712385 : Blo 1514954 9712385 := bstep (se 2 (by rfl) ⟨3642144, by rfl⟩ : syracuseStep 9712385 = 7284289) B7284289
theorem B2274107 : Blo 1514954 2274107 := bstep (se 1 (by rfl) ⟨1705580, by rfl⟩ : syracuseStep 2274107 = 3411161) B3411161
theorem B2274167 : Blo 1514954 2274167 := bstep (se 1 (by rfl) ⟨1705625, by rfl⟩ : syracuseStep 2274167 = 3411251) B3411251
theorem B3412871 : Blo 1514954 3412871 := bstep (se 1 (by rfl) ⟨2559653, by rfl⟩ : syracuseStep 3412871 = 5119307) B5119307
theorem B2274191 : Blo 1514954 2274191 := bstep (se 1 (by rfl) ⟨1705643, by rfl⟩ : syracuseStep 2274191 = 3411287) B3411287
theorem B11670425 : Blo 1514954 11670425 := bstep (se 2 (by rfl) ⟨4376409, by rfl⟩ : syracuseStep 11670425 = 8752819) B8752819
theorem B3838873 : Blo 1514954 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B6656921 : Blo 1514954 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B2274233 : Blo 1514954 2274233 := bstep (se 2 (by rfl) ⟨852837, by rfl⟩ : syracuseStep 2274233 = 1705675) B1705675
theorem B2274311 : Blo 1514954 2274311 := bstep (se 1 (by rfl) ⟨1705733, by rfl⟩ : syracuseStep 2274311 = 3411467) B3411467
theorem B2274347 : Blo 1514954 2274347 := bstep (se 1 (by rfl) ⟨1705760, by rfl⟩ : syracuseStep 2274347 = 3411521) B3411521
theorem B3839035 : Blo 1514954 3839035 := bstep (se 1 (by rfl) ⟨2879276, by rfl⟩ : syracuseStep 3839035 = 5758553) B5758553
theorem B3413051 : Blo 1514954 3413051 := bstep (se 1 (by rfl) ⟨2559788, by rfl⟩ : syracuseStep 3413051 = 5119577) B5119577
theorem B2274377 : Blo 1514954 2274377 := bstep (se 2 (by rfl) ⟨852891, by rfl⟩ : syracuseStep 2274377 = 1705783) B1705783
theorem B2274491 : Blo 1514954 2274491 := bstep (se 1 (by rfl) ⟨1705868, by rfl⟩ : syracuseStep 2274491 = 3411737) B3411737
theorem B4314313 : Blo 1514954 4314313 := bstep (se 2 (by rfl) ⟨1617867, by rfl⟩ : syracuseStep 4314313 = 3235735) B3235735
theorem B3839177 : Blo 1514954 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B2274551 : Blo 1514954 2274551 := bstep (se 1 (by rfl) ⟨1705913, by rfl⟩ : syracuseStep 2274551 = 3411827) B3411827
theorem B2274575 : Blo 1514954 2274575 := bstep (se 1 (by rfl) ⟨1705931, by rfl⟩ : syracuseStep 2274575 = 3411863) B3411863
theorem B2274617 : Blo 1514954 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B65533319 : Blo 1514954 65533319 := bstep (se 1 (by rfl) ⟨49149989, by rfl⟩ : syracuseStep 65533319 = 98299979) B98299979
theorem B2274695 : Blo 1514954 2274695 := bstep (se 1 (by rfl) ⟨1706021, by rfl⟩ : syracuseStep 2274695 = 3412043) B3412043
theorem B11515283 : Blo 1514954 11515283 := bstep (se 1 (by rfl) ⟨8636462, by rfl⟩ : syracuseStep 11515283 = 17272925) B17272925
theorem B2274731 : Blo 1514954 2274731 := bstep (se 1 (by rfl) ⟨1706048, by rfl⟩ : syracuseStep 2274731 = 3412097) B3412097
theorem B15562169 : Blo 1514954 15562169 := bstep (se 2 (by rfl) ⟨5835813, by rfl⟩ : syracuseStep 15562169 = 11671627) B11671627
theorem B2274761 : Blo 1514954 2274761 := bstep (se 2 (by rfl) ⟨853035, by rfl⟩ : syracuseStep 2274761 = 1706071) B1706071
theorem B7673291 : Blo 1514954 7673291 := bstep (se 1 (by rfl) ⟨5754968, by rfl⟩ : syracuseStep 7673291 = 11509937) B11509937
theorem B4609565 : Blo 1514954 4609565 := bstep (se 3 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 4609565 = 1728587) B1728587
theorem B3839521 : Blo 1514954 3839521 := bstep (se 2 (by rfl) ⟨1439820, by rfl⟩ : syracuseStep 3839521 = 2879641) B2879641
theorem B4314667 : Blo 1514954 4314667 := bstep (se 1 (by rfl) ⟨3236000, by rfl⟩ : syracuseStep 4314667 = 6472001) B6472001
theorem B2274875 : Blo 1514954 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B2274935 : Blo 1514954 2274935 := bstep (se 1 (by rfl) ⟨1706201, by rfl⟩ : syracuseStep 2274935 = 3412403) B3412403
theorem B2274959 : Blo 1514954 2274959 := bstep (se 1 (by rfl) ⟨1706219, by rfl⟩ : syracuseStep 2274959 = 3412439) B3412439
theorem B2275001 : Blo 1514954 2275001 := bstep (se 2 (by rfl) ⟨853125, by rfl⟩ : syracuseStep 2275001 = 1706251) B1706251
theorem B2275079 : Blo 1514954 2275079 := bstep (se 1 (by rfl) ⟨1706309, by rfl⟩ : syracuseStep 2275079 = 3412619) B3412619
theorem B3888911 : Blo 1514954 3888911 := bstep (se 1 (by rfl) ⟨2916683, by rfl⟩ : syracuseStep 3888911 = 5833367) B5833367
theorem B7673615 : Blo 1514954 7673615 := bstep (se 1 (by rfl) ⟨5755211, by rfl⟩ : syracuseStep 7673615 = 11510423) B11510423
theorem B2275115 : Blo 1514954 2275115 := bstep (se 1 (by rfl) ⟨1706336, by rfl⟩ : syracuseStep 2275115 = 3412673) B3412673
theorem B11507507 : Blo 1514954 11507507 := bstep (se 1 (by rfl) ⟨8630630, by rfl⟩ : syracuseStep 11507507 = 17261261) B17261261
theorem B9713459 : Blo 1514954 9713459 := bstep (se 1 (by rfl) ⟨7285094, by rfl⟩ : syracuseStep 9713459 = 14570189) B14570189
theorem B4314941 : Blo 1514954 4314941 := bstep (se 3 (by rfl) ⟨809051, by rfl⟩ : syracuseStep 4314941 = 1618103) B1618103
theorem B2275145 : Blo 1514954 2275145 := bstep (se 2 (by rfl) ⟨853179, by rfl⟩ : syracuseStep 2275145 = 1706359) B1706359
theorem B5117849 : Blo 1514954 5117849 := bstep (se 2 (by rfl) ⟨1919193, by rfl⟩ : syracuseStep 5117849 = 3838387) B3838387
theorem B2275259 : Blo 1514954 2275259 := bstep (se 1 (by rfl) ⟨1706444, by rfl⟩ : syracuseStep 2275259 = 3412889) B3412889
theorem B2275319 : Blo 1514954 2275319 := bstep (se 1 (by rfl) ⟨1706489, by rfl⟩ : syracuseStep 2275319 = 3412979) B3412979
theorem B2275343 : Blo 1514954 2275343 := bstep (se 1 (by rfl) ⟨1706507, by rfl⟩ : syracuseStep 2275343 = 3413015) B3413015
theorem B7288861 : Blo 1514954 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B2275385 : Blo 1514954 2275385 := bstep (se 2 (by rfl) ⟨853269, by rfl⟩ : syracuseStep 2275385 = 1706539) B1706539
theorem B6150401 : Blo 1514954 6150401 := bstep (se 2 (by rfl) ⟨2306400, by rfl⟩ : syracuseStep 6150401 = 4612801) B4612801
theorem B24574225 : Blo 1514954 24574225 := bstep (se 2 (by rfl) ⟨9215334, by rfl⟩ : syracuseStep 24574225 = 18430669) B18430669
theorem B8198585 : Blo 1514954 8198585 := bstep (se 2 (by rfl) ⟨3074469, by rfl⟩ : syracuseStep 8198585 = 6148939) B6148939
theorem B6478289 : Blo 1514954 6478289 := bstep (se 2 (by rfl) ⟨2429358, by rfl⟩ : syracuseStep 6478289 = 4858717) B4858717
theorem B20757059 : Blo 1514954 20757059 := bstep (se 1 (by rfl) ⟨15567794, by rfl⟩ : syracuseStep 20757059 = 31135589) B31135589
theorem B5118551 : Blo 1514954 5118551 := bstep (se 1 (by rfl) ⟨3838913, by rfl⟩ : syracuseStep 5118551 = 7677827) B7677827
theorem B3643991 : Blo 1514954 3643991 := bstep (se 1 (by rfl) ⟨2732993, by rfl⟩ : syracuseStep 3643991 = 5465987) B5465987
theorem B12286721 : Blo 1514954 12286721 := bstep (se 2 (by rfl) ⟨4607520, by rfl⟩ : syracuseStep 12286721 = 9215041) B9215041
theorem B32783267 : Blo 1514954 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B5119037 : Blo 1514954 5119037 := bstep (se 3 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 5119037 = 1919639) B1919639
theorem B8633411 : Blo 1514954 8633411 := bstep (se 1 (by rfl) ⟨6475058, by rfl⟩ : syracuseStep 8633411 = 12950117) B12950117
theorem B7675073 : Blo 1514954 7675073 := bstep (se 2 (by rfl) ⟨2878152, by rfl⟩ : syracuseStep 7675073 = 5756305) B5756305
theorem B78765371 : Blo 1514954 78765371 := bstep (se 1 (by rfl) ⟨59074028, by rfl⟩ : syracuseStep 78765371 = 118148057) B118148057
theorem B2768329 : Blo 1514954 2768329 := bstep (se 2 (by rfl) ⟨1038123, by rfl⟩ : syracuseStep 2768329 = 2076247) B2076247
theorem B124435925 : Blo 1514954 124435925 := bstep (se 7 (by rfl) ⟨1458233, by rfl⟩ : syracuseStep 124435925 = 2916467) B2916467
theorem B1515015 : Blo 1514954 1515015 := bstep (se 1 (by rfl) ⟨1136261, by rfl⟩ : syracuseStep 1515015 = 2272523) B2272523
theorem B1515023 : Blo 1514954 1515023 := bstep (se 1 (by rfl) ⟨1136267, by rfl⟩ : syracuseStep 1515023 = 2272535) B2272535
theorem B6471197 : Blo 1514954 6471197 := bstep (se 3 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 6471197 = 2426699) B2426699
theorem B9215531 : Blo 1514954 9215531 := bstep (se 1 (by rfl) ⟨6911648, by rfl⟩ : syracuseStep 9215531 = 13823297) B13823297
theorem B1515067 : Blo 1514954 1515067 := bstep (se 1 (by rfl) ⟨1136300, by rfl⟩ : syracuseStep 1515067 = 2272601) B2272601
theorem B7200323 : Blo 1514954 7200323 := bstep (se 1 (by rfl) ⟨5400242, by rfl⟩ : syracuseStep 7200323 = 10800485) B10800485
theorem B1515143 : Blo 1514954 1515143 := bstep (se 1 (by rfl) ⟨1136357, by rfl⟩ : syracuseStep 1515143 = 2272715) B2272715
theorem B1515151 : Blo 1514954 1515151 := bstep (se 1 (by rfl) ⟨1136363, by rfl⟩ : syracuseStep 1515151 = 2272727) B2272727
theorem B1515195 : Blo 1514954 1515195 := bstep (se 1 (by rfl) ⟨1136396, by rfl⟩ : syracuseStep 1515195 = 2272793) B2272793
theorem B5758721 : Blo 1514954 5758721 := bstep (se 2 (by rfl) ⟨2159520, by rfl⟩ : syracuseStep 5758721 = 4319041) B4319041
theorem B1515271 : Blo 1514954 1515271 := bstep (se 1 (by rfl) ⟨1136453, by rfl⟩ : syracuseStep 1515271 = 2272907) B2272907
theorem B1515279 : Blo 1514954 1515279 := bstep (se 1 (by rfl) ⟨1136459, by rfl⟩ : syracuseStep 1515279 = 2272919) B2272919
theorem B5758735 : Blo 1514954 5758735 := bstep (se 1 (by rfl) ⟨4319051, by rfl⟩ : syracuseStep 5758735 = 8638103) B8638103
theorem B84156205 : Blo 1514954 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B1515323 : Blo 1514954 1515323 := bstep (se 1 (by rfl) ⟨1136492, by rfl⟩ : syracuseStep 1515323 = 2272985) B2272985
theorem B6471539 : Blo 1514954 6471539 := bstep (se 1 (by rfl) ⟨4853654, by rfl⟩ : syracuseStep 6471539 = 9707309) B9707309
theorem B4317047 : Blo 1514954 4317047 := bstep (se 1 (by rfl) ⟨3237785, by rfl⟩ : syracuseStep 4317047 = 6475571) B6475571
theorem B1515399 : Blo 1514954 1515399 := bstep (se 1 (by rfl) ⟨1136549, by rfl⟩ : syracuseStep 1515399 = 2273099) B2273099
theorem B1515407 : Blo 1514954 1515407 := bstep (se 1 (by rfl) ⟨1136555, by rfl⟩ : syracuseStep 1515407 = 2273111) B2273111
theorem B1515451 : Blo 1514954 1515451 := bstep (se 1 (by rfl) ⟨1136588, by rfl⟩ : syracuseStep 1515451 = 2273177) B2273177
theorem B8192015 : Blo 1514954 8192015 := bstep (se 1 (by rfl) ⟨6144011, by rfl⟩ : syracuseStep 8192015 = 12288023) B12288023
theorem B1515559 : Blo 1514954 1515559 := bstep (se 1 (by rfl) ⟨1136669, by rfl⟩ : syracuseStep 1515559 = 2273339) B2273339
theorem B1515599 : Blo 1514954 1515599 := bstep (se 1 (by rfl) ⟨1136699, by rfl⟩ : syracuseStep 1515599 = 2273399) B2273399
theorem B1515615 : Blo 1514954 1515615 := bstep (se 1 (by rfl) ⟨1136711, by rfl⟩ : syracuseStep 1515615 = 2273423) B2273423
theorem B1515643 : Blo 1514954 1515643 := bstep (se 1 (by rfl) ⟨1136732, by rfl⟩ : syracuseStep 1515643 = 2273465) B2273465
theorem B1515695 : Blo 1514954 1515695 := bstep (se 1 (by rfl) ⟨1136771, by rfl⟩ : syracuseStep 1515695 = 2273543) B2273543
theorem B1515719 : Blo 1514954 1515719 := bstep (se 1 (by rfl) ⟨1136789, by rfl⟩ : syracuseStep 1515719 = 2273579) B2273579
theorem B1515739 : Blo 1514954 1515739 := bstep (se 1 (by rfl) ⟨1136804, by rfl⟩ : syracuseStep 1515739 = 2273609) B2273609
theorem B1515815 : Blo 1514954 1515815 := bstep (se 1 (by rfl) ⟨1136861, by rfl⟩ : syracuseStep 1515815 = 2273723) B2273723
theorem B1515855 : Blo 1514954 1515855 := bstep (se 1 (by rfl) ⟨1136891, by rfl⟩ : syracuseStep 1515855 = 2273783) B2273783
theorem B12288343 : Blo 1514954 12288343 := bstep (se 1 (by rfl) ⟨9216257, by rfl⟩ : syracuseStep 12288343 = 18432515) B18432515
theorem B1515871 : Blo 1514954 1515871 := bstep (se 1 (by rfl) ⟨1136903, by rfl⟩ : syracuseStep 1515871 = 2273807) B2273807
theorem B1515899 : Blo 1514954 1515899 := bstep (se 1 (by rfl) ⟨1136924, by rfl⟩ : syracuseStep 1515899 = 2273849) B2273849
theorem B4317583 : Blo 1514954 4317583 := bstep (se 1 (by rfl) ⟨3238187, by rfl⟩ : syracuseStep 4317583 = 6476375) B6476375
theorem B1515951 : Blo 1514954 1515951 := bstep (se 1 (by rfl) ⟨1136963, by rfl⟩ : syracuseStep 1515951 = 2273927) B2273927
theorem B1515975 : Blo 1514954 1515975 := bstep (se 1 (by rfl) ⟨1136981, by rfl⟩ : syracuseStep 1515975 = 2273963) B2273963
theorem B1515995 : Blo 1514954 1515995 := bstep (se 1 (by rfl) ⟨1136996, by rfl⟩ : syracuseStep 1515995 = 2273993) B2273993
theorem B1704487 : Blo 1514954 1704487 := bstep (se 1 (by rfl) ⟨1278365, by rfl⟩ : syracuseStep 1704487 = 2556731) B2556731
theorem B1516071 : Blo 1514954 1516071 := bstep (se 1 (by rfl) ⟨1137053, by rfl⟩ : syracuseStep 1516071 = 2274107) B2274107
theorem B1516111 : Blo 1514954 1516111 := bstep (se 1 (by rfl) ⟨1137083, by rfl⟩ : syracuseStep 1516111 = 2274167) B2274167
theorem B1516127 : Blo 1514954 1516127 := bstep (se 1 (by rfl) ⟨1137095, by rfl⟩ : syracuseStep 1516127 = 2274191) B2274191
theorem B1516155 : Blo 1514954 1516155 := bstep (se 1 (by rfl) ⟨1137116, by rfl⟩ : syracuseStep 1516155 = 2274233) B2274233
theorem B1516207 : Blo 1514954 1516207 := bstep (se 1 (by rfl) ⟨1137155, by rfl⟩ : syracuseStep 1516207 = 2274311) B2274311
theorem B1516231 : Blo 1514954 1516231 := bstep (se 1 (by rfl) ⟨1137173, by rfl⟩ : syracuseStep 1516231 = 2274347) B2274347
theorem B6914771 : Blo 1514954 6914771 := bstep (se 1 (by rfl) ⟨5186078, by rfl⟩ : syracuseStep 6914771 = 10372157) B10372157
theorem B1516251 : Blo 1514954 1516251 := bstep (se 1 (by rfl) ⟨1137188, by rfl⟩ : syracuseStep 1516251 = 2274377) B2274377
theorem B1516327 : Blo 1514954 1516327 := bstep (se 1 (by rfl) ⟨1137245, by rfl⟩ : syracuseStep 1516327 = 2274491) B2274491
theorem B3408713 : Blo 1514954 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B21324617 : Blo 1514954 21324617 := bstep (se 2 (by rfl) ⟨7996731, by rfl⟩ : syracuseStep 21324617 = 15993463) B15993463
theorem B1516367 : Blo 1514954 1516367 := bstep (se 1 (by rfl) ⟨1137275, by rfl⟩ : syracuseStep 1516367 = 2274551) B2274551
theorem B1516383 : Blo 1514954 1516383 := bstep (se 1 (by rfl) ⟨1137287, by rfl⟩ : syracuseStep 1516383 = 2274575) B2274575
theorem B1516411 : Blo 1514954 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B43688879 : Blo 1514954 43688879 := bstep (se 1 (by rfl) ⟨32766659, by rfl⟩ : syracuseStep 43688879 = 65533319) B65533319
theorem B1516463 : Blo 1514954 1516463 := bstep (se 1 (by rfl) ⟨1137347, by rfl⟩ : syracuseStep 1516463 = 2274695) B2274695
theorem B7676855 : Blo 1514954 7676855 := bstep (se 1 (by rfl) ⟨5757641, by rfl⟩ : syracuseStep 7676855 = 11515283) B11515283
theorem B5325755 : Blo 1514954 5325755 := bstep (se 1 (by rfl) ⟨3994316, by rfl⟩ : syracuseStep 5325755 = 7988633) B7988633
theorem B2556859 : Blo 1514954 2556859 := bstep (se 1 (by rfl) ⟨1917644, by rfl⟩ : syracuseStep 2556859 = 3835289) B3835289
theorem B1516487 : Blo 1514954 1516487 := bstep (se 1 (by rfl) ⟨1137365, by rfl⟩ : syracuseStep 1516487 = 2274731) B2274731
theorem B1516507 : Blo 1514954 1516507 := bstep (se 1 (by rfl) ⟨1137380, by rfl⟩ : syracuseStep 1516507 = 2274761) B2274761
theorem B3073043 : Blo 1514954 3073043 := bstep (se 1 (by rfl) ⟨2304782, by rfl⟩ : syracuseStep 3073043 = 4609565) B4609565
theorem B2556967 : Blo 1514954 2556967 := bstep (se 1 (by rfl) ⟨1917725, by rfl⟩ : syracuseStep 2556967 = 3835451) B3835451
theorem B1516583 : Blo 1514954 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B1516623 : Blo 1514954 1516623 := bstep (se 1 (by rfl) ⟨1137467, by rfl⟩ : syracuseStep 1516623 = 2274935) B2274935
theorem B1516639 : Blo 1514954 1516639 := bstep (se 1 (by rfl) ⟨1137479, by rfl⟩ : syracuseStep 1516639 = 2274959) B2274959
theorem B1918075 : Blo 1514954 1918075 := bstep (se 1 (by rfl) ⟨1438556, by rfl⟩ : syracuseStep 1918075 = 2877113) B2877113
theorem B1516667 : Blo 1514954 1516667 := bstep (se 1 (by rfl) ⟨1137500, by rfl⟩ : syracuseStep 1516667 = 2275001) B2275001
theorem B5112989 : Blo 1514954 5112989 := bstep (se 3 (by rfl) ⟨958685, by rfl⟩ : syracuseStep 5112989 = 1917371) B1917371
theorem B1516719 : Blo 1514954 1516719 := bstep (se 1 (by rfl) ⟨1137539, by rfl⟩ : syracuseStep 1516719 = 2275079) B2275079
theorem B46679237 : Blo 1514954 46679237 := bstep (se 4 (by rfl) ⟨4376178, by rfl⟩ : syracuseStep 46679237 = 8752357) B8752357
theorem B11519171 : Blo 1514954 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B1516743 : Blo 1514954 1516743 := bstep (se 1 (by rfl) ⟨1137557, by rfl⟩ : syracuseStep 1516743 = 2275115) B2275115
theorem B2876627 : Blo 1514954 2876627 := bstep (se 1 (by rfl) ⟨2157470, by rfl⟩ : syracuseStep 2876627 = 4314941) B4314941
theorem B1516763 : Blo 1514954 1516763 := bstep (se 1 (by rfl) ⟨1137572, by rfl⟩ : syracuseStep 1516763 = 2275145) B2275145
theorem B3835127 : Blo 1514954 3835127 := bstep (se 1 (by rfl) ⟨2876345, by rfl⟩ : syracuseStep 3835127 = 5752691) B5752691
theorem B10929431 : Blo 1514954 10929431 := bstep (se 1 (by rfl) ⟨8197073, by rfl⟩ : syracuseStep 10929431 = 16394147) B16394147
theorem B1516839 : Blo 1514954 1516839 := bstep (se 1 (by rfl) ⟨1137629, by rfl⟩ : syracuseStep 1516839 = 2275259) B2275259
theorem B1516879 : Blo 1514954 1516879 := bstep (se 1 (by rfl) ⟨1137659, by rfl⟩ : syracuseStep 1516879 = 2275319) B2275319
theorem B1516895 : Blo 1514954 1516895 := bstep (se 1 (by rfl) ⟨1137671, by rfl⟩ : syracuseStep 1516895 = 2275343) B2275343
theorem B3073385 : Blo 1514954 3073385 := bstep (se 2 (by rfl) ⟨1152519, by rfl⟩ : syracuseStep 3073385 = 2305039) B2305039
theorem B2557291 : Blo 1514954 2557291 := bstep (se 1 (by rfl) ⟨1917968, by rfl⟩ : syracuseStep 2557291 = 3835937) B3835937
theorem B1516923 : Blo 1514954 1516923 := bstep (se 1 (by rfl) ⟨1137692, by rfl⟩ : syracuseStep 1516923 = 2275385) B2275385
theorem B5752417 : Blo 1514954 5752417 := bstep (se 2 (by rfl) ⟨2157156, by rfl⟩ : syracuseStep 5752417 = 4314313) B4314313
theorem B3409505 : Blo 1514954 3409505 := bstep (se 2 (by rfl) ⟨1278564, by rfl⟩ : syracuseStep 3409505 = 2557129) B2557129
theorem B5465723 : Blo 1514954 5465723 := bstep (se 1 (by rfl) ⟨4099292, by rfl⟩ : syracuseStep 5465723 = 8198585) B8198585
theorem B4318859 : Blo 1514954 4318859 := bstep (se 1 (by rfl) ⟨3239144, by rfl⟩ : syracuseStep 4318859 = 6478289) B6478289
theorem B5113529 : Blo 1514954 5113529 := bstep (se 2 (by rfl) ⟨1917573, by rfl⟩ : syracuseStep 5113529 = 3835147) B3835147
theorem B12945095 : Blo 1514954 12945095 := bstep (se 1 (by rfl) ⟨9708821, by rfl⟩ : syracuseStep 12945095 = 19417643) B19417643
theorem B13838039 : Blo 1514954 13838039 := bstep (se 1 (by rfl) ⟨10378529, by rfl⟩ : syracuseStep 13838039 = 20757059) B20757059
theorem B2877257 : Blo 1514954 2877257 := bstep (se 2 (by rfl) ⟨1078971, by rfl⟩ : syracuseStep 2877257 = 2157943) B2157943
theorem B3409847 : Blo 1514954 3409847 := bstep (se 1 (by rfl) ⟨2557385, by rfl⟩ : syracuseStep 3409847 = 5114771) B5114771
theorem B5752889 : Blo 1514954 5752889 := bstep (se 2 (by rfl) ⟨2157333, by rfl⟩ : syracuseStep 5752889 = 4314667) B4314667
theorem B1706107 : Blo 1514954 1706107 := bstep (se 1 (by rfl) ⟨1279580, by rfl⟩ : syracuseStep 1706107 = 2559161) B2559161
theorem B5114123 : Blo 1514954 5114123 := bstep (se 1 (by rfl) ⟨3835592, by rfl⟩ : syracuseStep 5114123 = 7671185) B7671185
theorem B7678313 : Blo 1514954 7678313 := bstep (se 2 (by rfl) ⟨2879367, by rfl⟩ : syracuseStep 7678313 = 5758735) B5758735
theorem B2558351 : Blo 1514954 2558351 := bstep (se 1 (by rfl) ⟨1918763, by rfl⟩ : syracuseStep 2558351 = 3837527) B3837527
theorem B112208273 : Blo 1514954 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B3410441 : Blo 1514954 3410441 := bstep (se 2 (by rfl) ⟨1278915, by rfl⟩ : syracuseStep 3410441 = 2557831) B2557831
theorem B5114393 : Blo 1514954 5114393 := bstep (se 2 (by rfl) ⟨1917897, by rfl⟩ : syracuseStep 5114393 = 3835795) B3835795
theorem B2878031 : Blo 1514954 2878031 := bstep (se 1 (by rfl) ⟨2158523, by rfl⟩ : syracuseStep 2878031 = 4317047) B4317047
theorem B2558587 : Blo 1514954 2558587 := bstep (se 1 (by rfl) ⟨1918940, by rfl⟩ : syracuseStep 2558587 = 3837881) B3837881
theorem B3836555 : Blo 1514954 3836555 := bstep (se 1 (by rfl) ⟨2877416, by rfl⟩ : syracuseStep 3836555 = 5754833) B5754833
theorem B9718481 : Blo 1514954 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B4098775 : Blo 1514954 4098775 := bstep (se 1 (by rfl) ⟨3074081, by rfl⟩ : syracuseStep 4098775 = 6148163) B6148163
theorem B336579299 : Blo 1514954 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B3836767 : Blo 1514954 3836767 := bstep (se 1 (by rfl) ⟨2877575, by rfl⟩ : syracuseStep 3836767 = 5755151) B5755151
theorem B3410783 : Blo 1514954 3410783 := bstep (se 1 (by rfl) ⟨2558087, by rfl⟩ : syracuseStep 3410783 = 5116175) B5116175
theorem B5753875 : Blo 1514954 5753875 := bstep (se 1 (by rfl) ⟨4315406, by rfl⟩ : syracuseStep 5753875 = 8630813) B8630813
theorem B3410963 : Blo 1514954 3410963 := bstep (se 1 (by rfl) ⟨2558222, by rfl⟩ : syracuseStep 3410963 = 5116445) B5116445
theorem B10931219 : Blo 1514954 10931219 := bstep (se 1 (by rfl) ⟨8198414, by rfl⟩ : syracuseStep 10931219 = 16396829) B16396829
theorem B2157607 : Blo 1514954 2157607 := bstep (se 1 (by rfl) ⟨1618205, by rfl⟩ : syracuseStep 2157607 = 3236411) B3236411
theorem B6474923 : Blo 1514954 6474923 := bstep (se 1 (by rfl) ⟨4856192, by rfl⟩ : syracuseStep 6474923 = 9712385) B9712385
theorem B2272505 : Blo 1514954 2272505 := bstep (se 2 (by rfl) ⟨852189, by rfl⟩ : syracuseStep 2272505 = 1704379) B1704379
theorem B2272607 : Blo 1514954 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B3411305 : Blo 1514954 3411305 := bstep (se 2 (by rfl) ⟨1279239, by rfl⟩ : syracuseStep 3411305 = 2558479) B2558479
theorem B2272619 : Blo 1514954 2272619 := bstep (se 1 (by rfl) ⟨1704464, by rfl⟩ : syracuseStep 2272619 = 3408929) B3408929
theorem B2157931 : Blo 1514954 2157931 := bstep (se 1 (by rfl) ⟨1618448, by rfl⟩ : syracuseStep 2157931 = 3236897) B3236897
theorem B2305463 : Blo 1514954 2305463 := bstep (se 1 (by rfl) ⟨1729097, by rfl⟩ : syracuseStep 2305463 = 3458195) B3458195
theorem B2559451 : Blo 1514954 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B2731529 : Blo 1514954 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B2272847 : Blo 1514954 2272847 := bstep (se 1 (by rfl) ⟨1704635, by rfl⟩ : syracuseStep 2272847 = 3409271) B3409271
theorem B2158159 : Blo 1514954 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B10374779 : Blo 1514954 10374779 := bstep (se 1 (by rfl) ⟨7781084, by rfl⟩ : syracuseStep 10374779 = 15562169) B15562169
theorem B5115527 : Blo 1514954 5115527 := bstep (se 1 (by rfl) ⟨3836645, by rfl⟩ : syracuseStep 5115527 = 7673291) B7673291
theorem B5115581 : Blo 1514954 5115581 := bstep (se 3 (by rfl) ⟨959171, by rfl⟩ : syracuseStep 5115581 = 1918343) B1918343
theorem B2272967 : Blo 1514954 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B1535707 : Blo 1514954 1535707 := bstep (se 1 (by rfl) ⟨1151780, by rfl⟩ : syracuseStep 1535707 = 2303561) B2303561
theorem B3837689 : Blo 1514954 3837689 := bstep (se 2 (by rfl) ⟨1439133, by rfl⟩ : syracuseStep 3837689 = 2878267) B2878267
theorem B2592607 : Blo 1514954 2592607 := bstep (se 1 (by rfl) ⟨1944455, by rfl⟩ : syracuseStep 2592607 = 3888911) B3888911
theorem B5115743 : Blo 1514954 5115743 := bstep (se 1 (by rfl) ⟨3836807, by rfl⟩ : syracuseStep 5115743 = 7673615) B7673615
theorem B2273129 : Blo 1514954 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B7671671 : Blo 1514954 7671671 := bstep (se 1 (by rfl) ⟨5753753, by rfl⟩ : syracuseStep 7671671 = 11507507) B11507507
theorem B6475639 : Blo 1514954 6475639 := bstep (se 1 (by rfl) ⟨4856729, by rfl⟩ : syracuseStep 6475639 = 9713459) B9713459
theorem B2273207 : Blo 1514954 2273207 := bstep (se 1 (by rfl) ⟨1704905, by rfl⟩ : syracuseStep 2273207 = 3409811) B3409811
theorem B3411899 : Blo 1514954 3411899 := bstep (se 1 (by rfl) ⟨2558924, by rfl⟩ : syracuseStep 3411899 = 5117849) B5117849
theorem B2273243 : Blo 1514954 2273243 := bstep (se 1 (by rfl) ⟨1704932, by rfl⟩ : syracuseStep 2273243 = 3409865) B3409865
theorem B5115905 : Blo 1514954 5115905 := bstep (se 2 (by rfl) ⟨1918464, by rfl⟩ : syracuseStep 5115905 = 3836929) B3836929
theorem B3412025 : Blo 1514954 3412025 := bstep (se 2 (by rfl) ⟨1279509, by rfl⟩ : syracuseStep 3412025 = 2559019) B2559019
theorem B4100267 : Blo 1514954 4100267 := bstep (se 1 (by rfl) ⟨3075200, by rfl⟩ : syracuseStep 4100267 = 6150401) B6150401
theorem B2879687 : Blo 1514954 2879687 := bstep (se 1 (by rfl) ⟨2159765, by rfl⟩ : syracuseStep 2879687 = 4319531) B4319531
theorem B14577995 : Blo 1514954 14577995 := bstep (se 1 (by rfl) ⟨10933496, by rfl⟩ : syracuseStep 14577995 = 21866993) B21866993
theorem B2732395 : Blo 1514954 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B5058941 : Blo 1514954 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B11506049 : Blo 1514954 11506049 := bstep (se 2 (by rfl) ⟨4314768, by rfl⟩ : syracuseStep 11506049 = 8629537) B8629537
theorem B3838337 : Blo 1514954 3838337 := bstep (se 2 (by rfl) ⟨1439376, by rfl⟩ : syracuseStep 3838337 = 2878753) B2878753
theorem B3412367 : Blo 1514954 3412367 := bstep (se 1 (by rfl) ⟨2559275, by rfl⟩ : syracuseStep 3412367 = 5118551) B5118551
theorem B2429327 : Blo 1514954 2429327 := bstep (se 1 (by rfl) ⟨1821995, by rfl⟩ : syracuseStep 2429327 = 3643991) B3643991
theorem B2273711 : Blo 1514954 2273711 := bstep (se 1 (by rfl) ⟨1705283, by rfl⟩ : syracuseStep 2273711 = 3410567) B3410567
theorem B177189385 : Blo 1514954 177189385 := bstep (se 2 (by rfl) ⟨66446019, by rfl⟩ : syracuseStep 177189385 = 132892039) B132892039
theorem B2273801 : Blo 1514954 2273801 := bstep (se 2 (by rfl) ⟨852675, by rfl⟩ : syracuseStep 2273801 = 1705351) B1705351
theorem B2273831 : Blo 1514954 2273831 := bstep (se 1 (by rfl) ⟨1705373, by rfl⟩ : syracuseStep 2273831 = 3410747) B3410747
theorem B3691105 : Blo 1514954 3691105 := bstep (se 2 (by rfl) ⟨1384164, by rfl⟩ : syracuseStep 3691105 = 2768329) B2768329
theorem B2273915 : Blo 1514954 2273915 := bstep (se 1 (by rfl) ⟨1705436, by rfl⟩ : syracuseStep 2273915 = 3410873) B3410873
theorem B8630995 : Blo 1514954 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B3412691 : Blo 1514954 3412691 := bstep (se 1 (by rfl) ⟨2559518, by rfl⟩ : syracuseStep 3412691 = 5119037) B5119037
theorem B5755607 : Blo 1514954 5755607 := bstep (se 1 (by rfl) ⟨4316705, by rfl⟩ : syracuseStep 5755607 = 8633411) B8633411
theorem B2274041 : Blo 1514954 2274041 := bstep (se 2 (by rfl) ⟨852765, by rfl⟩ : syracuseStep 2274041 = 1705531) B1705531
theorem B5116715 : Blo 1514954 5116715 := bstep (se 1 (by rfl) ⟨3837536, by rfl⟩ : syracuseStep 5116715 = 7675073) B7675073
theorem B2274143 : Blo 1514954 2274143 := bstep (se 1 (by rfl) ⟨1705607, by rfl⟩ : syracuseStep 2274143 = 3411215) B3411215
theorem B2274155 : Blo 1514954 2274155 := bstep (se 1 (by rfl) ⟨1705616, by rfl⟩ : syracuseStep 2274155 = 3411233) B3411233
theorem B82957283 : Blo 1514954 82957283 := bstep (se 1 (by rfl) ⟨62217962, by rfl⟩ : syracuseStep 82957283 = 124435925) B124435925
theorem B8631269 : Blo 1514954 8631269 := bstep (se 4 (by rfl) ⟨809181, by rfl⟩ : syracuseStep 8631269 = 1618363) B1618363
theorem B4314131 : Blo 1514954 4314131 := bstep (se 1 (by rfl) ⟨3235598, by rfl⟩ : syracuseStep 4314131 = 6471197) B6471197
theorem B5116985 : Blo 1514954 5116985 := bstep (se 2 (by rfl) ⟨1918869, by rfl⟩ : syracuseStep 5116985 = 3837739) B3837739
theorem B2274383 : Blo 1514954 2274383 := bstep (se 1 (by rfl) ⟨1705787, by rfl⟩ : syracuseStep 2274383 = 3411575) B3411575
theorem B3839147 : Blo 1514954 3839147 := bstep (se 1 (by rfl) ⟨2879360, by rfl⟩ : syracuseStep 3839147 = 5758721) B5758721
theorem B2274503 : Blo 1514954 2274503 := bstep (se 1 (by rfl) ⟨1705877, by rfl⟩ : syracuseStep 2274503 = 3411755) B3411755
theorem B4314359 : Blo 1514954 4314359 := bstep (se 1 (by rfl) ⟨3235769, by rfl⟩ : syracuseStep 4314359 = 6471539) B6471539
theorem B2274665 : Blo 1514954 2274665 := bstep (se 2 (by rfl) ⟨852999, by rfl⟩ : syracuseStep 2274665 = 1705999) B1705999
theorem B5117309 : Blo 1514954 5117309 := bstep (se 3 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 5117309 = 1918991) B1918991
theorem B2274743 : Blo 1514954 2274743 := bstep (se 1 (by rfl) ⟨1706057, by rfl⟩ : syracuseStep 2274743 = 3412115) B3412115
theorem B8197595 : Blo 1514954 8197595 := bstep (se 1 (by rfl) ⟨6148196, by rfl⟩ : syracuseStep 8197595 = 12296393) B12296393
theorem B2274779 : Blo 1514954 2274779 := bstep (se 1 (by rfl) ⟨1706084, by rfl⟩ : syracuseStep 2274779 = 3412169) B3412169
theorem B3888737 : Blo 1514954 3888737 := bstep (se 2 (by rfl) ⟨1458276, by rfl⟩ : syracuseStep 3888737 = 2916553) B2916553
theorem B5117579 : Blo 1514954 5117579 := bstep (se 1 (by rfl) ⟨3838184, by rfl⟩ : syracuseStep 5117579 = 7676369) B7676369
theorem B8631953 : Blo 1514954 8631953 := bstep (se 2 (by rfl) ⟨3236982, by rfl⟩ : syracuseStep 8631953 = 6473965) B6473965
theorem B32765633 : Blo 1514954 32765633 := bstep (se 2 (by rfl) ⟨12287112, by rfl⟩ : syracuseStep 32765633 = 24574225) B24574225
theorem B1971911 : Blo 1514954 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B3741395 : Blo 1514954 3741395 := bstep (se 1 (by rfl) ⟨2806046, by rfl⟩ : syracuseStep 3741395 = 5612093) B5612093
theorem B18446039 : Blo 1514954 18446039 := bstep (se 1 (by rfl) ⟨13834529, by rfl⟩ : syracuseStep 18446039 = 27669059) B27669059
theorem B5756791 : Blo 1514954 5756791 := bstep (se 1 (by rfl) ⟨4317593, by rfl⟩ : syracuseStep 5756791 = 8635187) B8635187
theorem B2275247 : Blo 1514954 2275247 := bstep (se 1 (by rfl) ⟨1706435, by rfl⟩ : syracuseStep 2275247 = 3412871) B3412871
theorem B7780283 : Blo 1514954 7780283 := bstep (se 1 (by rfl) ⟨5835212, by rfl⟩ : syracuseStep 7780283 = 11670425) B11670425
theorem B4437947 : Blo 1514954 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B2275337 : Blo 1514954 2275337 := bstep (se 2 (by rfl) ⟨853251, by rfl⟩ : syracuseStep 2275337 = 1706503) B1706503
theorem B2275367 : Blo 1514954 2275367 := bstep (se 1 (by rfl) ⟨1706525, by rfl⟩ : syracuseStep 2275367 = 3413051) B3413051
theorem B7387217 : Blo 1514954 7387217 := bstep (se 2 (by rfl) ⟨2770206, by rfl⟩ : syracuseStep 7387217 = 5540413) B5540413
theorem B9214067 : Blo 1514954 9214067 := bstep (se 1 (by rfl) ⟨6910550, by rfl⟩ : syracuseStep 9214067 = 13821101) B13821101
theorem B36887021 : Blo 1514954 36887021 := bstep (se 3 (by rfl) ⟨6916316, by rfl⟩ : syracuseStep 36887021 = 13832633) B13832633
theorem B5118497 : Blo 1514954 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B4315771 : Blo 1514954 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B5118713 : Blo 1514954 5118713 := bstep (se 2 (by rfl) ⟨1919517, by rfl⟩ : syracuseStep 5118713 = 3839035) B3839035
theorem B5757763 : Blo 1514954 5757763 := bstep (se 1 (by rfl) ⟨4318322, by rfl⟩ : syracuseStep 5757763 = 8636645) B8636645
theorem B4315999 : Blo 1514954 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B5118983 : Blo 1514954 5118983 := bstep (se 1 (by rfl) ⟨3839237, by rfl⟩ : syracuseStep 5118983 = 7678475) B7678475
theorem B3644423 : Blo 1514954 3644423 := bstep (se 1 (by rfl) ⟨2733317, by rfl⟩ : syracuseStep 3644423 = 5466635) B5466635
theorem B24583247 : Blo 1514954 24583247 := bstep (se 1 (by rfl) ⟨18437435, by rfl⟩ : syracuseStep 24583247 = 36874871) B36874871
theorem B5758067 : Blo 1514954 5758067 := bstep (se 1 (by rfl) ⟨4318550, by rfl⟩ : syracuseStep 5758067 = 8637101) B8637101
theorem B5119091 : Blo 1514954 5119091 := bstep (se 1 (by rfl) ⟨3839318, by rfl⟩ : syracuseStep 5119091 = 7678637) B7678637
theorem B8191147 : Blo 1514954 8191147 := bstep (se 1 (by rfl) ⟨6143360, by rfl⟩ : syracuseStep 8191147 = 12286721) B12286721
theorem B21855511 : Blo 1514954 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B5119361 : Blo 1514954 5119361 := bstep (se 2 (by rfl) ⟨1919760, by rfl⟩ : syracuseStep 5119361 = 3839521) B3839521
theorem B1514971 : Blo 1514954 1514971 := bstep (se 1 (by rfl) ⟨1136228, by rfl⟩ : syracuseStep 1514971 = 2272457) B2272457
theorem B5463533 : Blo 1514954 5463533 := bstep (se 3 (by rfl) ⟨1024412, by rfl⟩ : syracuseStep 5463533 = 2048825) B2048825
theorem B1515047 : Blo 1514954 1515047 := bstep (se 1 (by rfl) ⟨1136285, by rfl⟩ : syracuseStep 1515047 = 2272571) B2272571
theorem B52510247 : Blo 1514954 52510247 := bstep (se 1 (by rfl) ⟨39382685, by rfl⟩ : syracuseStep 52510247 = 78765371) B78765371
theorem B5758523 : Blo 1514954 5758523 := bstep (se 1 (by rfl) ⟨4318892, by rfl⟩ : syracuseStep 5758523 = 8637785) B8637785
theorem B1515087 : Blo 1514954 1515087 := bstep (se 1 (by rfl) ⟨1136315, by rfl⟩ : syracuseStep 1515087 = 2272631) B2272631
theorem B1515103 : Blo 1514954 1515103 := bstep (se 1 (by rfl) ⟨1136327, by rfl⟩ : syracuseStep 1515103 = 2272655) B2272655
theorem B6471265 : Blo 1514954 6471265 := bstep (se 2 (by rfl) ⟨2426724, by rfl⟩ : syracuseStep 6471265 = 4853449) B4853449
theorem B1515131 : Blo 1514954 1515131 := bstep (se 1 (by rfl) ⟨1136348, by rfl⟩ : syracuseStep 1515131 = 2272697) B2272697
theorem B1515183 : Blo 1514954 1515183 := bstep (se 1 (by rfl) ⟨1136387, by rfl⟩ : syracuseStep 1515183 = 2272775) B2272775
theorem B1515207 : Blo 1514954 1515207 := bstep (se 1 (by rfl) ⟨1136405, by rfl⟩ : syracuseStep 1515207 = 2272811) B2272811
theorem B6143687 : Blo 1514954 6143687 := bstep (se 1 (by rfl) ⟨4607765, by rfl⟩ : syracuseStep 6143687 = 9215531) B9215531
theorem B4800215 : Blo 1514954 4800215 := bstep (se 1 (by rfl) ⟨3600161, by rfl⟩ : syracuseStep 4800215 = 7200323) B7200323
theorem B1515227 : Blo 1514954 1515227 := bstep (se 1 (by rfl) ⟨1136420, by rfl⟩ : syracuseStep 1515227 = 2272841) B2272841
theorem B1515303 : Blo 1514954 1515303 := bstep (se 1 (by rfl) ⟨1136477, by rfl⟩ : syracuseStep 1515303 = 2272955) B2272955
theorem B1515343 : Blo 1514954 1515343 := bstep (se 1 (by rfl) ⟨1136507, by rfl⟩ : syracuseStep 1515343 = 2273015) B2273015
theorem B1515359 : Blo 1514954 1515359 := bstep (se 1 (by rfl) ⟨1136519, by rfl⟩ : syracuseStep 1515359 = 2273039) B2273039
theorem B1515387 : Blo 1514954 1515387 := bstep (se 1 (by rfl) ⟨1136540, by rfl⟩ : syracuseStep 1515387 = 2273081) B2273081
theorem B1515439 : Blo 1514954 1515439 := bstep (se 1 (by rfl) ⟨1136579, by rfl⟩ : syracuseStep 1515439 = 2273159) B2273159
theorem B1515463 : Blo 1514954 1515463 := bstep (se 1 (by rfl) ⟨1136597, by rfl⟩ : syracuseStep 1515463 = 2273195) B2273195
theorem B1515483 : Blo 1514954 1515483 := bstep (se 1 (by rfl) ⟨1136612, by rfl⟩ : syracuseStep 1515483 = 2273225) B2273225
theorem B1515807 : Blo 1514954 1515807 := bstep (se 1 (by rfl) ⟨1136855, by rfl⟩ : syracuseStep 1515807 = 2273711) B2273711
theorem B1515867 : Blo 1514954 1515867 := bstep (se 1 (by rfl) ⟨1136900, by rfl⟩ : syracuseStep 1515867 = 2273801) B2273801
theorem B1515887 : Blo 1514954 1515887 := bstep (se 1 (by rfl) ⟨1136915, by rfl⟩ : syracuseStep 1515887 = 2273831) B2273831
theorem B1515943 : Blo 1514954 1515943 := bstep (se 1 (by rfl) ⟨1136957, by rfl⟩ : syracuseStep 1515943 = 2273915) B2273915
theorem B16384457 : Blo 1514954 16384457 := bstep (se 2 (by rfl) ⟨6144171, by rfl⟩ : syracuseStep 16384457 = 12288343) B12288343
theorem B1516027 : Blo 1514954 1516027 := bstep (se 1 (by rfl) ⟨1137020, by rfl⟩ : syracuseStep 1516027 = 2274041) B2274041
theorem B1516095 : Blo 1514954 1516095 := bstep (se 1 (by rfl) ⟨1137071, by rfl⟩ : syracuseStep 1516095 = 2274143) B2274143
theorem B1516103 : Blo 1514954 1516103 := bstep (se 1 (by rfl) ⟨1137077, by rfl⟩ : syracuseStep 1516103 = 2274155) B2274155
theorem B55304855 : Blo 1514954 55304855 := bstep (se 1 (by rfl) ⟨41478641, by rfl⟩ : syracuseStep 55304855 = 82957283) B82957283
theorem B2876087 : Blo 1514954 2876087 := bstep (se 1 (by rfl) ⟨2157065, by rfl⟩ : syracuseStep 2876087 = 4314131) B4314131
theorem B2048695 : Blo 1514954 2048695 := bstep (se 1 (by rfl) ⟨1536521, by rfl⟩ : syracuseStep 2048695 = 3073043) B3073043
theorem B1516255 : Blo 1514954 1516255 := bstep (se 1 (by rfl) ⟨1137191, by rfl⟩ : syracuseStep 1516255 = 2274383) B2274383
theorem B3408659 : Blo 1514954 3408659 := bstep (se 1 (by rfl) ⟨2556494, by rfl⟩ : syracuseStep 3408659 = 5112989) B5112989
theorem B1516335 : Blo 1514954 1516335 := bstep (se 1 (by rfl) ⟨1137251, by rfl⟩ : syracuseStep 1516335 = 2274503) B2274503
theorem B1917751 : Blo 1514954 1917751 := bstep (se 1 (by rfl) ⟨1438313, by rfl⟩ : syracuseStep 1917751 = 2876627) B2876627
theorem B2876239 : Blo 1514954 2876239 := bstep (se 1 (by rfl) ⟨2157179, by rfl⟩ : syracuseStep 2876239 = 4314359) B4314359
theorem B2556751 : Blo 1514954 2556751 := bstep (se 1 (by rfl) ⟨1917563, by rfl⟩ : syracuseStep 2556751 = 3835127) B3835127
theorem B2048923 : Blo 1514954 2048923 := bstep (se 1 (by rfl) ⟨1536692, by rfl⟩ : syracuseStep 2048923 = 3073385) B3073385
theorem B1516443 : Blo 1514954 1516443 := bstep (se 1 (by rfl) ⟨1137332, by rfl⟩ : syracuseStep 1516443 = 2274665) B2274665
theorem B5465033 : Blo 1514954 5465033 := bstep (se 2 (by rfl) ⟨2049387, by rfl⟩ : syracuseStep 5465033 = 4098775) B4098775
theorem B1516495 : Blo 1514954 1516495 := bstep (se 1 (by rfl) ⟨1137371, by rfl⟩ : syracuseStep 1516495 = 2274743) B2274743
theorem B5465063 : Blo 1514954 5465063 := bstep (se 1 (by rfl) ⟨4098797, by rfl⟩ : syracuseStep 5465063 = 8197595) B8197595
theorem B1516519 : Blo 1514954 1516519 := bstep (se 1 (by rfl) ⟨1137389, by rfl⟩ : syracuseStep 1516519 = 2274779) B2274779
theorem B7677017 : Blo 1514954 7677017 := bstep (se 2 (by rfl) ⟨2878881, by rfl⟩ : syracuseStep 7677017 = 5757763) B5757763
theorem B3409019 : Blo 1514954 3409019 := bstep (se 1 (by rfl) ⟨2556764, by rfl⟩ : syracuseStep 3409019 = 5113529) B5113529
theorem B12297359 : Blo 1514954 12297359 := bstep (se 1 (by rfl) ⟨9223019, by rfl⟩ : syracuseStep 12297359 = 18446039) B18446039
theorem B9225359 : Blo 1514954 9225359 := bstep (se 1 (by rfl) ⟨6919019, by rfl⟩ : syracuseStep 9225359 = 13838039) B13838039
theorem B1918171 : Blo 1514954 1918171 := bstep (se 1 (by rfl) ⟨1438628, by rfl⟩ : syracuseStep 1918171 = 2877257) B2877257
theorem B3409145 : Blo 1514954 3409145 := bstep (se 2 (by rfl) ⟨1278429, by rfl⟩ : syracuseStep 3409145 = 2556859) B2556859
theorem B1516831 : Blo 1514954 1516831 := bstep (se 1 (by rfl) ⟨1137623, by rfl⟩ : syracuseStep 1516831 = 2275247) B2275247
theorem B5186855 : Blo 1514954 5186855 := bstep (se 1 (by rfl) ⟨3890141, by rfl⟩ : syracuseStep 5186855 = 7780283) B7780283
theorem B1516891 : Blo 1514954 1516891 := bstep (se 1 (by rfl) ⟨1137668, by rfl⟩ : syracuseStep 1516891 = 2275337) B2275337
theorem B7284077 : Blo 1514954 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B1516911 : Blo 1514954 1516911 := bstep (se 1 (by rfl) ⟨1137683, by rfl⟩ : syracuseStep 1516911 = 2275367) B2275367
theorem B3835259 : Blo 1514954 3835259 := bstep (se 1 (by rfl) ⟨2876444, by rfl⟩ : syracuseStep 3835259 = 5752889) B5752889
theorem B3409289 : Blo 1514954 3409289 := bstep (se 2 (by rfl) ⟨1278483, by rfl⟩ : syracuseStep 3409289 = 2556967) B2556967
theorem B2876809 : Blo 1514954 2876809 := bstep (se 2 (by rfl) ⟨1078803, by rfl⟩ : syracuseStep 2876809 = 2157607) B2157607
theorem B4924811 : Blo 1514954 4924811 := bstep (se 1 (by rfl) ⟨3693608, by rfl⟩ : syracuseStep 4924811 = 7387217) B7387217
theorem B2557433 : Blo 1514954 2557433 := bstep (se 2 (by rfl) ⟨959037, by rfl⟩ : syracuseStep 2557433 = 1918075) B1918075
theorem B3409415 : Blo 1514954 3409415 := bstep (se 1 (by rfl) ⟨2557061, by rfl⟩ : syracuseStep 3409415 = 5114123) B5114123
theorem B10921529 : Blo 1514954 10921529 := bstep (se 2 (by rfl) ⟨4095573, by rfl⟩ : syracuseStep 10921529 = 8191147) B8191147
theorem B1705567 : Blo 1514954 1705567 := bstep (se 1 (by rfl) ⟨1279175, by rfl⟩ : syracuseStep 1705567 = 2558351) B2558351
theorem B3409595 : Blo 1514954 3409595 := bstep (se 1 (by rfl) ⟨2557196, by rfl⟩ : syracuseStep 3409595 = 5114393) B5114393
theorem B29140681 : Blo 1514954 29140681 := bstep (se 2 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 29140681 = 21855511) B21855511
theorem B2557703 : Blo 1514954 2557703 := bstep (se 1 (by rfl) ⟨1918277, by rfl⟩ : syracuseStep 2557703 = 3836555) B3836555
theorem B3409721 : Blo 1514954 3409721 := bstep (se 2 (by rfl) ⟨1278645, by rfl⟩ : syracuseStep 3409721 = 2557291) B2557291
theorem B78743573 : Blo 1514954 78743573 := bstep (se 6 (by rfl) ⟨1845552, by rfl⟩ : syracuseStep 78743573 = 3691105) B3691105
theorem B2877545 : Blo 1514954 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B8628353 : Blo 1514954 8628353 := bstep (se 2 (by rfl) ⟨3235632, by rfl⟩ : syracuseStep 8628353 = 6471265) B6471265
theorem B7669889 : Blo 1514954 7669889 := bstep (se 2 (by rfl) ⟨2876208, by rfl⟩ : syracuseStep 7669889 = 5752417) B5752417
theorem B35006831 : Blo 1514954 35006831 := bstep (se 1 (by rfl) ⟨26255123, by rfl⟩ : syracuseStep 35006831 = 52510247) B52510247
theorem B6916519 : Blo 1514954 6916519 := bstep (se 1 (by rfl) ⟨5187389, by rfl⟩ : syracuseStep 6916519 = 10374779) B10374779
theorem B3410351 : Blo 1514954 3410351 := bstep (se 1 (by rfl) ⟨2557763, by rfl⟩ : syracuseStep 3410351 = 5115527) B5115527
theorem B3410387 : Blo 1514954 3410387 := bstep (se 1 (by rfl) ⟨2557790, by rfl⟩ : syracuseStep 3410387 = 5115581) B5115581
theorem B2558459 : Blo 1514954 2558459 := bstep (se 1 (by rfl) ⟨1918844, by rfl⟩ : syracuseStep 2558459 = 3837689) B3837689
theorem B3410495 : Blo 1514954 3410495 := bstep (se 1 (by rfl) ⟨2557871, by rfl⟩ : syracuseStep 3410495 = 5115743) B5115743
theorem B5114447 : Blo 1514954 5114447 := bstep (se 1 (by rfl) ⟨3835835, by rfl⟩ : syracuseStep 5114447 = 7671671) B7671671
theorem B3410603 : Blo 1514954 3410603 := bstep (se 1 (by rfl) ⟨2557952, by rfl⟩ : syracuseStep 3410603 = 5115905) B5115905
theorem B1919791 : Blo 1514954 1919791 := bstep (se 1 (by rfl) ⟨1439843, by rfl⟩ : syracuseStep 1919791 = 2879687) B2879687
theorem B9718663 : Blo 1514954 9718663 := bstep (se 1 (by rfl) ⟨7288997, by rfl⟩ : syracuseStep 9718663 = 14577995) B14577995
theorem B7670699 : Blo 1514954 7670699 := bstep (se 1 (by rfl) ⟨5753024, by rfl⟩ : syracuseStep 7670699 = 11506049) B11506049
theorem B2558891 : Blo 1514954 2558891 := bstep (se 1 (by rfl) ⟨1919168, by rfl⟩ : syracuseStep 2558891 = 3838337) B3838337
theorem B3837071 : Blo 1514954 3837071 := bstep (se 1 (by rfl) ⟨2877803, by rfl⟩ : syracuseStep 3837071 = 5755607) B5755607
theorem B3411143 : Blo 1514954 3411143 := bstep (se 1 (by rfl) ⟨2558357, by rfl⟩ : syracuseStep 3411143 = 5116715) B5116715
theorem B2272475 : Blo 1514954 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B14216411 : Blo 1514954 14216411 := bstep (se 1 (by rfl) ⟨10662308, by rfl⟩ : syracuseStep 14216411 = 21324617) B21324617
theorem B29125919 : Blo 1514954 29125919 := bstep (se 1 (by rfl) ⟨21844439, by rfl⟩ : syracuseStep 29125919 = 43688879) B43688879
theorem B5754179 : Blo 1514954 5754179 := bstep (se 1 (by rfl) ⟨4315634, by rfl⟩ : syracuseStep 5754179 = 8631269) B8631269
theorem B236252513 : Blo 1514954 236252513 := bstep (se 2 (by rfl) ⟨88594692, by rfl⟩ : syracuseStep 236252513 = 177189385) B177189385
theorem B3411323 : Blo 1514954 3411323 := bstep (se 1 (by rfl) ⟨2558492, by rfl⟩ : syracuseStep 3411323 = 5116985) B5116985
theorem B2272649 : Blo 1514954 2272649 := bstep (se 2 (by rfl) ⟨852243, by rfl⟩ : syracuseStep 2272649 = 1704487) B1704487
theorem B2559431 : Blo 1514954 2559431 := bstep (se 1 (by rfl) ⟨1919573, by rfl⟩ : syracuseStep 2559431 = 3839147) B3839147
theorem B7679447 : Blo 1514954 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B5754361 : Blo 1514954 5754361 := bstep (se 2 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 5754361 = 4315771) B4315771
theorem B3411449 : Blo 1514954 3411449 := bstep (se 2 (by rfl) ⟨1279293, by rfl⟩ : syracuseStep 3411449 = 2558587) B2558587
theorem B7286287 : Blo 1514954 7286287 := bstep (se 1 (by rfl) ⟨5464715, by rfl⟩ : syracuseStep 7286287 = 10929431) B10929431
theorem B3411539 : Blo 1514954 3411539 := bstep (se 1 (by rfl) ⟨2558654, by rfl⟩ : syracuseStep 3411539 = 5117309) B5117309
theorem B2273003 : Blo 1514954 2273003 := bstep (se 1 (by rfl) ⟨1704752, by rfl⟩ : syracuseStep 2273003 = 3409505) B3409505
theorem B2592491 : Blo 1514954 2592491 := bstep (se 1 (by rfl) ⟨1944368, by rfl⟩ : syracuseStep 2592491 = 3888737) B3888737
theorem B3411719 : Blo 1514954 3411719 := bstep (se 1 (by rfl) ⟨2558789, by rfl⟩ : syracuseStep 3411719 = 5117579) B5117579
theorem B2879239 : Blo 1514954 2879239 := bstep (se 1 (by rfl) ⟨2159429, by rfl⟩ : syracuseStep 2879239 = 4318859) B4318859
theorem B5754635 : Blo 1514954 5754635 := bstep (se 1 (by rfl) ⟨4315976, by rfl⟩ : syracuseStep 5754635 = 8631953) B8631953
theorem B5115689 : Blo 1514954 5115689 := bstep (se 2 (by rfl) ⟨1918383, by rfl⟩ : syracuseStep 5115689 = 3836767) B3836767
theorem B5754665 : Blo 1514954 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B21843755 : Blo 1514954 21843755 := bstep (se 1 (by rfl) ⟨16382816, by rfl⟩ : syracuseStep 21843755 = 32765633) B32765633
theorem B8630063 : Blo 1514954 8630063 := bstep (se 1 (by rfl) ⟨6472547, by rfl⟩ : syracuseStep 8630063 = 12945095) B12945095
theorem B6147901 : Blo 1514954 6147901 := bstep (se 3 (by rfl) ⟨1152731, by rfl⟩ : syracuseStep 6147901 = 2305463) B2305463
theorem B2273231 : Blo 1514954 2273231 := bstep (se 1 (by rfl) ⟨1704923, by rfl⟩ : syracuseStep 2273231 = 3409847) B3409847
theorem B7671833 : Blo 1514954 7671833 := bstep (se 2 (by rfl) ⟨2876937, by rfl⟩ : syracuseStep 7671833 = 5753875) B5753875
theorem B74805515 : Blo 1514954 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B2273627 : Blo 1514954 2273627 := bstep (se 1 (by rfl) ⟨1705220, by rfl⟩ : syracuseStep 2273627 = 3410441) B3410441
theorem B3412331 : Blo 1514954 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B3412475 : Blo 1514954 3412475 := bstep (se 1 (by rfl) ⟨2559356, by rfl⟩ : syracuseStep 3412475 = 5118713) B5118713
theorem B25915949 : Blo 1514954 25915949 := bstep (se 3 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 25915949 = 9718481) B9718481
theorem B2273855 : Blo 1514954 2273855 := bstep (se 1 (by rfl) ⟨1705391, by rfl⟩ : syracuseStep 2273855 = 3410783) B3410783
theorem B3412601 : Blo 1514954 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B3412655 : Blo 1514954 3412655 := bstep (se 1 (by rfl) ⟨2559491, by rfl⟩ : syracuseStep 3412655 = 5118983) B5118983
theorem B2429615 : Blo 1514954 2429615 := bstep (se 1 (by rfl) ⟨1822211, by rfl⟩ : syracuseStep 2429615 = 3644423) B3644423
theorem B2273975 : Blo 1514954 2273975 := bstep (se 1 (by rfl) ⟨1705481, by rfl⟩ : syracuseStep 2273975 = 3410963) B3410963
theorem B7287479 : Blo 1514954 7287479 := bstep (se 1 (by rfl) ⟨5465609, by rfl⟩ : syracuseStep 7287479 = 10931219) B10931219
theorem B16388831 : Blo 1514954 16388831 := bstep (se 1 (by rfl) ⟨12291623, by rfl⟩ : syracuseStep 16388831 = 24583247) B24583247
theorem B3838711 : Blo 1514954 3838711 := bstep (se 1 (by rfl) ⟨2879033, by rfl⟩ : syracuseStep 3838711 = 5758067) B5758067
theorem B3412727 : Blo 1514954 3412727 := bstep (se 1 (by rfl) ⟨2559545, by rfl⟩ : syracuseStep 3412727 = 5119091) B5119091
theorem B2274203 : Blo 1514954 2274203 := bstep (se 1 (by rfl) ⟨1705652, by rfl⟩ : syracuseStep 2274203 = 3411305) B3411305
theorem B3412907 : Blo 1514954 3412907 := bstep (se 1 (by rfl) ⟨2559680, by rfl⟩ : syracuseStep 3412907 = 5119361) B5119361
theorem B3642355 : Blo 1514954 3642355 := bstep (se 1 (by rfl) ⟨2731766, by rfl⟩ : syracuseStep 3642355 = 5463533) B5463533
theorem B3839015 : Blo 1514954 3839015 := bstep (se 1 (by rfl) ⟨2879261, by rfl⟩ : syracuseStep 3839015 = 5758523) B5758523
theorem B3200143 : Blo 1514954 3200143 := bstep (se 1 (by rfl) ⟨2400107, by rfl⟩ : syracuseStep 3200143 = 4800215) B4800215
theorem B14202013 : Blo 1514954 14202013 := bstep (se 3 (by rfl) ⟨2662877, by rfl⟩ : syracuseStep 14202013 = 5325755) B5325755
theorem B11834525 : Blo 1514954 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B2274599 : Blo 1514954 2274599 := bstep (se 1 (by rfl) ⟨1705949, by rfl⟩ : syracuseStep 2274599 = 3411899) B3411899
theorem B5461343 : Blo 1514954 5461343 := bstep (se 1 (by rfl) ⟨4096007, by rfl⟩ : syracuseStep 5461343 = 8192015) B8192015
theorem B2274683 : Blo 1514954 2274683 := bstep (se 1 (by rfl) ⟨1706012, by rfl⟩ : syracuseStep 2274683 = 3412025) B3412025
theorem B2733511 : Blo 1514954 2733511 := bstep (se 1 (by rfl) ⟨2050133, by rfl⟩ : syracuseStep 2733511 = 4100267) B4100267
theorem B2274809 : Blo 1514954 2274809 := bstep (se 2 (by rfl) ⟨853053, by rfl⟩ : syracuseStep 2274809 = 1706107) B1706107
theorem B2274911 : Blo 1514954 2274911 := bstep (se 1 (by rfl) ⟨1706183, by rfl⟩ : syracuseStep 2274911 = 3412367) B3412367
theorem B1619551 : Blo 1514954 1619551 := bstep (se 1 (by rfl) ⟨1214663, by rfl⟩ : syracuseStep 1619551 = 2429327) B2429327
theorem B4609847 : Blo 1514954 4609847 := bstep (se 1 (by rfl) ⟨3457385, by rfl⟩ : syracuseStep 4609847 = 6914771) B6914771
theorem B2275127 : Blo 1514954 2275127 := bstep (se 1 (by rfl) ⟨1706345, by rfl⟩ : syracuseStep 2275127 = 3412691) B3412691
theorem B3643193 : Blo 1514954 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B5756777 : Blo 1514954 5756777 := bstep (se 2 (by rfl) ⟨2158791, by rfl⟩ : syracuseStep 5756777 = 4317583) B4317583
theorem B5117903 : Blo 1514954 5117903 := bstep (se 1 (by rfl) ⟨3838427, by rfl⟩ : syracuseStep 5117903 = 7676855) B7676855
theorem B31119491 : Blo 1514954 31119491 := bstep (se 1 (by rfl) ⟨23339618, by rfl⟩ : syracuseStep 31119491 = 46679237) B46679237
theorem B11507993 : Blo 1514954 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B13490509 : Blo 1514954 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B58301045 : Blo 1514954 58301045 := bstep (se 5 (by rfl) ⟨2732861, by rfl⟩ : syracuseStep 58301045 = 5465723) B5465723
theorem B6142711 : Blo 1514954 6142711 := bstep (se 1 (by rfl) ⟨4607033, by rfl⟩ : syracuseStep 6142711 = 9214067) B9214067
theorem B7674749 : Blo 1514954 7674749 := bstep (se 3 (by rfl) ⟨1439015, by rfl⟩ : syracuseStep 7674749 = 2878031) B2878031
theorem B5118875 : Blo 1514954 5118875 := bstep (se 1 (by rfl) ⟨3839156, by rfl⟩ : syracuseStep 5118875 = 7678313) B7678313
theorem B24591347 : Blo 1514954 24591347 := bstep (se 1 (by rfl) ⟨18443510, by rfl⟩ : syracuseStep 24591347 = 36887021) B36887021
theorem B224386199 : Blo 1514954 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B5258429 : Blo 1514954 5258429 := bstep (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) B1971911
theorem B9977053 : Blo 1514954 9977053 := bstep (se 3 (by rfl) ⟨1870697, by rfl⟩ : syracuseStep 9977053 = 3741395) B3741395
theorem B11508965 : Blo 1514954 11508965 := bstep (se 4 (by rfl) ⟨1078965, by rfl⟩ : syracuseStep 11508965 = 2157931) B2157931
theorem B4316615 : Blo 1514954 4316615 := bstep (se 1 (by rfl) ⟨3237461, by rfl⟩ : syracuseStep 4316615 = 6474923) B6474923
theorem B1515003 : Blo 1514954 1515003 := bstep (se 1 (by rfl) ⟨1136252, by rfl⟩ : syracuseStep 1515003 = 2272505) B2272505
theorem B1515071 : Blo 1514954 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B1515079 : Blo 1514954 1515079 := bstep (se 1 (by rfl) ⟨1136309, by rfl⟩ : syracuseStep 1515079 = 2272619) B2272619
theorem B2047609 : Blo 1514954 2047609 := bstep (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) B1535707
theorem B1515231 : Blo 1514954 1515231 := bstep (se 1 (by rfl) ⟨1136423, by rfl⟩ : syracuseStep 1515231 = 2272847) B2272847
theorem B3456809 : Blo 1514954 3456809 := bstep (se 2 (by rfl) ⟨1296303, by rfl⟩ : syracuseStep 3456809 = 2592607) B2592607
theorem B4095791 : Blo 1514954 4095791 := bstep (se 1 (by rfl) ⟨3071843, by rfl⟩ : syracuseStep 4095791 = 6143687) B6143687
theorem B1515311 : Blo 1514954 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B8634185 : Blo 1514954 8634185 := bstep (se 2 (by rfl) ⟨3237819, by rfl⟩ : syracuseStep 8634185 = 6475639) B6475639
theorem B7675721 : Blo 1514954 7675721 := bstep (se 2 (by rfl) ⟨2878395, by rfl⟩ : syracuseStep 7675721 = 5756791) B5756791
theorem B1515419 : Blo 1514954 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B1515471 : Blo 1514954 1515471 := bstep (se 1 (by rfl) ⟨1136603, by rfl⟩ : syracuseStep 1515471 = 2273207) B2273207
theorem B1515495 : Blo 1514954 1515495 := bstep (se 1 (by rfl) ⟨1136621, by rfl⟩ : syracuseStep 1515495 = 2273243) B2273243
theorem B1515751 : Blo 1514954 1515751 := bstep (se 1 (by rfl) ⟨1136813, by rfl⟩ : syracuseStep 1515751 = 2273627) B2273627
theorem B17277299 : Blo 1514954 17277299 := bstep (se 1 (by rfl) ⟨12957974, by rfl⟩ : syracuseStep 17277299 = 25915949) B25915949
theorem B32792957 : Blo 1514954 32792957 := bstep (se 3 (by rfl) ⟨6148679, by rfl⟩ : syracuseStep 32792957 = 12297359) B12297359
theorem B1515903 : Blo 1514954 1515903 := bstep (se 1 (by rfl) ⟨1136927, by rfl⟩ : syracuseStep 1515903 = 2273855) B2273855
theorem B1515983 : Blo 1514954 1515983 := bstep (se 1 (by rfl) ⟨1136987, by rfl⟩ : syracuseStep 1515983 = 2273975) B2273975
theorem B4858319 : Blo 1514954 4858319 := bstep (se 1 (by rfl) ⟨3643739, by rfl⟩ : syracuseStep 4858319 = 7287479) B7287479
theorem B1516135 : Blo 1514954 1516135 := bstep (se 1 (by rfl) ⟨1137101, by rfl⟩ : syracuseStep 1516135 = 2274203) B2274203
theorem B10920581 : Blo 1514954 10920581 := bstep (se 4 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 10920581 = 2047609) B2047609
theorem B7889683 : Blo 1514954 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B3457903 : Blo 1514954 3457903 := bstep (se 1 (by rfl) ⟨2593427, by rfl⟩ : syracuseStep 3457903 = 5186855) B5186855
theorem B1516399 : Blo 1514954 1516399 := bstep (se 1 (by rfl) ⟨1137299, by rfl⟩ : syracuseStep 1516399 = 2274599) B2274599
theorem B2556839 : Blo 1514954 2556839 := bstep (se 1 (by rfl) ⟨1917629, by rfl⟩ : syracuseStep 2556839 = 3835259) B3835259
theorem B1516455 : Blo 1514954 1516455 := bstep (se 1 (by rfl) ⟨1137341, by rfl⟩ : syracuseStep 1516455 = 2274683) B2274683
theorem B1704955 : Blo 1514954 1704955 := bstep (se 1 (by rfl) ⟨1278716, by rfl⟩ : syracuseStep 1704955 = 2557433) B2557433
theorem B1516539 : Blo 1514954 1516539 := bstep (se 1 (by rfl) ⟨1137404, by rfl⟩ : syracuseStep 1516539 = 2274809) B2274809
theorem B13132829 : Blo 1514954 13132829 := bstep (se 3 (by rfl) ⟨2462405, by rfl⟩ : syracuseStep 13132829 = 4924811) B4924811
theorem B1516607 : Blo 1514954 1516607 := bstep (se 1 (by rfl) ⟨1137455, by rfl⟩ : syracuseStep 1516607 = 2274911) B2274911
theorem B2557001 : Blo 1514954 2557001 := bstep (se 2 (by rfl) ⟨958875, by rfl⟩ : syracuseStep 2557001 = 1917751) B1917751
theorem B3834985 : Blo 1514954 3834985 := bstep (se 2 (by rfl) ⟨1438119, by rfl⟩ : syracuseStep 3834985 = 2876239) B2876239
theorem B3409001 : Blo 1514954 3409001 := bstep (se 2 (by rfl) ⟨1278375, by rfl⟩ : syracuseStep 3409001 = 2556751) B2556751
theorem B1705135 : Blo 1514954 1705135 := bstep (se 1 (by rfl) ⟨1278851, by rfl⟩ : syracuseStep 1705135 = 2557703) B2557703
theorem B3073231 : Blo 1514954 3073231 := bstep (se 1 (by rfl) ⟨2304923, by rfl⟩ : syracuseStep 3073231 = 4609847) B4609847
theorem B1516751 : Blo 1514954 1516751 := bstep (se 1 (by rfl) ⟨1137563, by rfl⟩ : syracuseStep 1516751 = 2275127) B2275127
theorem B52495715 : Blo 1514954 52495715 := bstep (se 1 (by rfl) ⟨39371786, by rfl⟩ : syracuseStep 52495715 = 78743573) B78743573
theorem B5752235 : Blo 1514954 5752235 := bstep (se 1 (by rfl) ⟨4314176, by rfl⟩ : syracuseStep 5752235 = 8628353) B8628353
theorem B5113259 : Blo 1514954 5113259 := bstep (se 1 (by rfl) ⟨3834944, by rfl⟩ : syracuseStep 5113259 = 7669889) B7669889
theorem B2557561 : Blo 1514954 2557561 := bstep (se 2 (by rfl) ⟨959085, by rfl⟩ : syracuseStep 2557561 = 1918171) B1918171
theorem B1705639 : Blo 1514954 1705639 := bstep (se 1 (by rfl) ⟨1279229, by rfl⟩ : syracuseStep 1705639 = 2558459) B2558459
theorem B3409631 : Blo 1514954 3409631 := bstep (se 1 (by rfl) ⟨2557223, by rfl⟩ : syracuseStep 3409631 = 5114447) B5114447
theorem B7669565 : Blo 1514954 7669565 := bstep (se 3 (by rfl) ⟨1438043, by rfl⟩ : syracuseStep 7669565 = 2876087) B2876087
theorem B3835745 : Blo 1514954 3835745 := bstep (se 2 (by rfl) ⟨1438404, by rfl⟩ : syracuseStep 3835745 = 2876809) B2876809
theorem B5113799 : Blo 1514954 5113799 := bstep (se 1 (by rfl) ⟨3835349, by rfl⟩ : syracuseStep 5113799 = 7670699) B7670699
theorem B1705927 : Blo 1514954 1705927 := bstep (se 1 (by rfl) ⟨1279445, by rfl⟩ : syracuseStep 1705927 = 2558891) B2558891
theorem B16394231 : Blo 1514954 16394231 := bstep (se 1 (by rfl) ⟨12295673, by rfl⟩ : syracuseStep 16394231 = 24591347) B24591347
theorem B2558047 : Blo 1514954 2558047 := bstep (se 1 (by rfl) ⟨1918535, by rfl⟩ : syracuseStep 2558047 = 3837071) B3837071
theorem B19417279 : Blo 1514954 19417279 := bstep (se 1 (by rfl) ⟨14562959, by rfl⟩ : syracuseStep 19417279 = 29125919) B29125919
theorem B3836119 : Blo 1514954 3836119 := bstep (se 1 (by rfl) ⟨2877089, by rfl⟩ : syracuseStep 3836119 = 5754179) B5754179
theorem B157501675 : Blo 1514954 157501675 := bstep (se 1 (by rfl) ⟨118126256, by rfl⟩ : syracuseStep 157501675 = 236252513) B236252513
theorem B2877743 : Blo 1514954 2877743 := bstep (se 1 (by rfl) ⟨2158307, by rfl⟩ : syracuseStep 2877743 = 4316615) B4316615
theorem B1706287 : Blo 1514954 1706287 := bstep (se 1 (by rfl) ⟨1279715, by rfl⟩ : syracuseStep 1706287 = 2559431) B2559431
theorem B3836423 : Blo 1514954 3836423 := bstep (se 1 (by rfl) ⟨2877317, by rfl⟩ : syracuseStep 3836423 = 5754635) B5754635
theorem B3836443 : Blo 1514954 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B2304539 : Blo 1514954 2304539 := bstep (se 1 (by rfl) ⟨1728404, by rfl⟩ : syracuseStep 2304539 = 3456809) B3456809
theorem B3410459 : Blo 1514954 3410459 := bstep (se 1 (by rfl) ⟨2557844, by rfl⟩ : syracuseStep 3410459 = 5115689) B5115689
theorem B2730527 : Blo 1514954 2730527 := bstep (se 1 (by rfl) ⟨2047895, by rfl⟩ : syracuseStep 2730527 = 4095791) B4095791
theorem B5753375 : Blo 1514954 5753375 := bstep (se 1 (by rfl) ⟨4315031, by rfl⟩ : syracuseStep 5753375 = 8630063) B8630063
theorem B5114555 : Blo 1514954 5114555 := bstep (se 1 (by rfl) ⟨3835916, by rfl⟩ : syracuseStep 5114555 = 7671833) B7671833
theorem B2272439 : Blo 1514954 2272439 := bstep (se 1 (by rfl) ⟨1704329, by rfl⟩ : syracuseStep 2272439 = 3408659) B3408659
theorem B2559343 : Blo 1514954 2559343 := bstep (se 1 (by rfl) ⟨1919507, by rfl⟩ : syracuseStep 2559343 = 3839015) B3839015
theorem B2272679 : Blo 1514954 2272679 := bstep (se 1 (by rfl) ⟨1704509, by rfl⟩ : syracuseStep 2272679 = 3409019) B3409019
theorem B2272763 : Blo 1514954 2272763 := bstep (se 1 (by rfl) ⟨1704572, by rfl⟩ : syracuseStep 2272763 = 3409145) B3409145
theorem B3640895 : Blo 1514954 3640895 := bstep (se 1 (by rfl) ⟨2730671, by rfl⟩ : syracuseStep 3640895 = 5461343) B5461343
theorem B2272859 : Blo 1514954 2272859 := bstep (se 1 (by rfl) ⟨1704644, by rfl⟩ : syracuseStep 2272859 = 3409289) B3409289
theorem B2272943 : Blo 1514954 2272943 := bstep (se 1 (by rfl) ⟨1704707, by rfl⟩ : syracuseStep 2272943 = 3409415) B3409415
theorem B2559721 : Blo 1514954 2559721 := bstep (se 2 (by rfl) ⟨959895, by rfl⟩ : syracuseStep 2559721 = 1919791) B1919791
theorem B2273063 : Blo 1514954 2273063 := bstep (se 1 (by rfl) ⟨1704797, by rfl⟩ : syracuseStep 2273063 = 3409595) B3409595
theorem B43691885 : Blo 1514954 43691885 := bstep (se 3 (by rfl) ⟨8192228, by rfl⟩ : syracuseStep 43691885 = 16384457) B16384457
theorem B2731897 : Blo 1514954 2731897 := bstep (se 2 (by rfl) ⟨1024461, by rfl⟩ : syracuseStep 2731897 = 2048923) B2048923
theorem B2273147 : Blo 1514954 2273147 := bstep (se 1 (by rfl) ⟨1704860, by rfl⟩ : syracuseStep 2273147 = 3409721) B3409721
theorem B2428795 : Blo 1514954 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B3837851 : Blo 1514954 3837851 := bstep (se 1 (by rfl) ⟨2878388, by rfl⟩ : syracuseStep 3837851 = 5756777) B5756777
theorem B3411935 : Blo 1514954 3411935 := bstep (se 1 (by rfl) ⟨2558951, by rfl⟩ : syracuseStep 3411935 = 5117903) B5117903
theorem B20746327 : Blo 1514954 20746327 := bstep (se 1 (by rfl) ⟨15559745, by rfl⟩ : syracuseStep 20746327 = 31119491) B31119491
theorem B7671995 : Blo 1514954 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B18936017 : Blo 1514954 18936017 := bstep (se 2 (by rfl) ⟨7101006, by rfl⟩ : syracuseStep 18936017 = 14202013) B14202013
theorem B2273567 : Blo 1514954 2273567 := bstep (se 1 (by rfl) ⟨1705175, by rfl⟩ : syracuseStep 2273567 = 3410351) B3410351
theorem B2273591 : Blo 1514954 2273591 := bstep (se 1 (by rfl) ⟨1705193, by rfl⟩ : syracuseStep 2273591 = 3410387) B3410387
theorem B2273663 : Blo 1514954 2273663 := bstep (se 1 (by rfl) ⟨1705247, by rfl⟩ : syracuseStep 2273663 = 3410495) B3410495
theorem B38867363 : Blo 1514954 38867363 := bstep (se 1 (by rfl) ⟨29150522, by rfl⟩ : syracuseStep 38867363 = 58301045) B58301045
theorem B2273735 : Blo 1514954 2273735 := bstep (se 1 (by rfl) ⟨1705301, by rfl⟩ : syracuseStep 2273735 = 3410603) B3410603
theorem B5116499 : Blo 1514954 5116499 := bstep (se 1 (by rfl) ⟨3837374, by rfl⟩ : syracuseStep 5116499 = 7674749) B7674749
theorem B3412583 : Blo 1514954 3412583 := bstep (se 1 (by rfl) ⟨2559437, by rfl⟩ : syracuseStep 3412583 = 5118875) B5118875
theorem B7672481 : Blo 1514954 7672481 := bstep (se 2 (by rfl) ⟨2877180, by rfl⟩ : syracuseStep 7672481 = 5754361) B5754361
theorem B149590799 : Blo 1514954 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B2274089 : Blo 1514954 2274089 := bstep (se 2 (by rfl) ⟨852783, by rfl⟩ : syracuseStep 2274089 = 1705567) B1705567
theorem B2159401 : Blo 1514954 2159401 := bstep (se 2 (by rfl) ⟨809775, by rfl⟩ : syracuseStep 2159401 = 1619551) B1619551
theorem B2274095 : Blo 1514954 2274095 := bstep (se 1 (by rfl) ⟨1705571, by rfl⟩ : syracuseStep 2274095 = 3411143) B3411143
theorem B7672643 : Blo 1514954 7672643 := bstep (se 1 (by rfl) ⟨5754482, by rfl⟩ : syracuseStep 7672643 = 11508965) B11508965
theorem B2274215 : Blo 1514954 2274215 := bstep (se 1 (by rfl) ⟨1705661, by rfl⟩ : syracuseStep 2274215 = 3411323) B3411323
theorem B2274299 : Blo 1514954 2274299 := bstep (se 1 (by rfl) ⟨1705724, by rfl⟩ : syracuseStep 2274299 = 3411449) B3411449
theorem B3838985 : Blo 1514954 3838985 := bstep (se 2 (by rfl) ⟨1439619, by rfl⟩ : syracuseStep 3838985 = 2879239) B2879239
theorem B2274359 : Blo 1514954 2274359 := bstep (se 1 (by rfl) ⟨1705769, by rfl⟩ : syracuseStep 2274359 = 3411539) B3411539
theorem B8197201 : Blo 1514954 8197201 := bstep (se 2 (by rfl) ⟨3073950, by rfl⟩ : syracuseStep 8197201 = 6147901) B6147901
theorem B2274479 : Blo 1514954 2274479 := bstep (se 1 (by rfl) ⟨1705859, by rfl⟩ : syracuseStep 2274479 = 3411719) B3411719
theorem B14562503 : Blo 1514954 14562503 := bstep (se 1 (by rfl) ⟨10921877, by rfl⟩ : syracuseStep 14562503 = 21843755) B21843755
theorem B5756123 : Blo 1514954 5756123 := bstep (se 1 (by rfl) ⟨4317092, by rfl⟩ : syracuseStep 5756123 = 8634185) B8634185
theorem B5117147 : Blo 1514954 5117147 := bstep (se 1 (by rfl) ⟨3837860, by rfl⟩ : syracuseStep 5117147 = 7675721) B7675721
theorem B49870343 : Blo 1514954 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B2274887 : Blo 1514954 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B7673453 : Blo 1514954 7673453 := bstep (se 3 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 7673453 = 2877545) B2877545
theorem B2274983 : Blo 1514954 2274983 := bstep (se 1 (by rfl) ⟨1706237, by rfl⟩ : syracuseStep 2274983 = 3412475) B3412475
theorem B2275067 : Blo 1514954 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B36869903 : Blo 1514954 36869903 := bstep (se 1 (by rfl) ⟨27652427, by rfl⟩ : syracuseStep 36869903 = 55304855) B55304855
theorem B17987345 : Blo 1514954 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B2275103 : Blo 1514954 2275103 := bstep (se 1 (by rfl) ⟨1706327, by rfl⟩ : syracuseStep 2275103 = 3412655) B3412655
theorem B10925887 : Blo 1514954 10925887 := bstep (se 1 (by rfl) ⟨8194415, by rfl⟩ : syracuseStep 10925887 = 16388831) B16388831
theorem B2275151 : Blo 1514954 2275151 := bstep (se 1 (by rfl) ⟨1706363, by rfl⟩ : syracuseStep 2275151 = 3412727) B3412727
theorem B9222025 : Blo 1514954 9222025 := bstep (se 2 (by rfl) ⟨3458259, by rfl⟩ : syracuseStep 9222025 = 6916519) B6916519
theorem B37910429 : Blo 1514954 37910429 := bstep (se 3 (by rfl) ⟨7108205, by rfl⟩ : syracuseStep 37910429 = 14216411) B14216411
theorem B2275271 : Blo 1514954 2275271 := bstep (se 1 (by rfl) ⟨1706453, by rfl⟩ : syracuseStep 2275271 = 3412907) B3412907
theorem B3643355 : Blo 1514954 3643355 := bstep (se 1 (by rfl) ⟨2732516, by rfl⟩ : syracuseStep 3643355 = 5465033) B5465033
theorem B3643375 : Blo 1514954 3643375 := bstep (se 1 (by rfl) ⟨2732531, by rfl⟩ : syracuseStep 3643375 = 5465063) B5465063
theorem B5118011 : Blo 1514954 5118011 := bstep (se 1 (by rfl) ⟨3838508, by rfl⟩ : syracuseStep 5118011 = 7677017) B7677017
theorem B6150239 : Blo 1514954 6150239 := bstep (se 1 (by rfl) ⟨4612679, by rfl⟩ : syracuseStep 6150239 = 9225359) B9225359
theorem B4856051 : Blo 1514954 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B10926373 : Blo 1514954 10926373 := bstep (se 4 (by rfl) ⟨1024347, by rfl⟩ : syracuseStep 10926373 = 2048695) B2048695
theorem B8190281 : Blo 1514954 8190281 := bstep (se 2 (by rfl) ⟨3071355, by rfl⟩ : syracuseStep 8190281 = 6142711) B6142711
theorem B5118281 : Blo 1514954 5118281 := bstep (se 2 (by rfl) ⟨1919355, by rfl⟩ : syracuseStep 5118281 = 3838711) B3838711
theorem B7281019 : Blo 1514954 7281019 := bstep (se 1 (by rfl) ⟨5460764, by rfl⟩ : syracuseStep 7281019 = 10921529) B10921529
theorem B12958217 : Blo 1514954 12958217 := bstep (se 2 (by rfl) ⟨4859331, by rfl⟩ : syracuseStep 12958217 = 9718663) B9718663
theorem B4856473 : Blo 1514954 4856473 := bstep (se 2 (by rfl) ⟨1821177, by rfl⟩ : syracuseStep 4856473 = 3642355) B3642355
theorem B4266857 : Blo 1514954 4266857 := bstep (se 2 (by rfl) ⟨1600071, by rfl⟩ : syracuseStep 4266857 = 3200143) B3200143
theorem B23337887 : Blo 1514954 23337887 := bstep (se 1 (by rfl) ⟨17503415, by rfl⟩ : syracuseStep 23337887 = 35006831) B35006831
theorem B13302737 : Blo 1514954 13302737 := bstep (se 2 (by rfl) ⟨4988526, by rfl⟩ : syracuseStep 13302737 = 9977053) B9977053
theorem B6478973 : Blo 1514954 6478973 := bstep (se 3 (by rfl) ⟨1214807, by rfl⟩ : syracuseStep 6478973 = 2429615) B2429615
theorem B3644681 : Blo 1514954 3644681 := bstep (se 2 (by rfl) ⟨1366755, by rfl⟩ : syracuseStep 3644681 = 2733511) B2733511
theorem B6913309 : Blo 1514954 6913309 := bstep (se 3 (by rfl) ⟨1296245, by rfl⟩ : syracuseStep 6913309 = 2592491) B2592491
theorem B9715049 : Blo 1514954 9715049 := bstep (se 2 (by rfl) ⟨3643143, by rfl⟩ : syracuseStep 9715049 = 7286287) B7286287
theorem B3505619 : Blo 1514954 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B1514983 : Blo 1514954 1514983 := bstep (se 1 (by rfl) ⟨1136237, by rfl⟩ : syracuseStep 1514983 = 2272475) B2272475
theorem B1515099 : Blo 1514954 1515099 := bstep (se 1 (by rfl) ⟨1136324, by rfl⟩ : syracuseStep 1515099 = 2272649) B2272649
theorem B38854241 : Blo 1514954 38854241 := bstep (se 2 (by rfl) ⟨14570340, by rfl⟩ : syracuseStep 38854241 = 29140681) B29140681
theorem B5119631 : Blo 1514954 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B1515335 : Blo 1514954 1515335 := bstep (se 1 (by rfl) ⟨1136501, by rfl⟩ : syracuseStep 1515335 = 2273003) B2273003
theorem B1515487 : Blo 1514954 1515487 := bstep (se 1 (by rfl) ⟨1136615, by rfl⟩ : syracuseStep 1515487 = 2273231) B2273231
theorem B12624011 : Blo 1514954 12624011 := bstep (se 1 (by rfl) ⟨9468008, by rfl⟩ : syracuseStep 12624011 = 18936017) B18936017
theorem B1515711 : Blo 1514954 1515711 := bstep (se 1 (by rfl) ⟨1136783, by rfl⟩ : syracuseStep 1515711 = 2273567) B2273567
theorem B1515727 : Blo 1514954 1515727 := bstep (se 1 (by rfl) ⟨1136795, by rfl⟩ : syracuseStep 1515727 = 2273591) B2273591
theorem B11518199 : Blo 1514954 11518199 := bstep (se 1 (by rfl) ⟨8638649, by rfl⟩ : syracuseStep 11518199 = 17277299) B17277299
theorem B1515775 : Blo 1514954 1515775 := bstep (se 1 (by rfl) ⟨1136831, by rfl⟩ : syracuseStep 1515775 = 2273663) B2273663
theorem B25911575 : Blo 1514954 25911575 := bstep (se 1 (by rfl) ⟨19433681, by rfl⟩ : syracuseStep 25911575 = 38867363) B38867363
theorem B1515823 : Blo 1514954 1515823 := bstep (se 1 (by rfl) ⟨1136867, by rfl⟩ : syracuseStep 1515823 = 2273735) B2273735
theorem B210002233 : Blo 1514954 210002233 := bstep (se 2 (by rfl) ⟨78750837, by rfl⟩ : syracuseStep 210002233 = 157501675) B157501675
theorem B9708025 : Blo 1514954 9708025 := bstep (se 2 (by rfl) ⟨3640509, by rfl⟩ : syracuseStep 9708025 = 7281019) B7281019
theorem B1516059 : Blo 1514954 1516059 := bstep (se 1 (by rfl) ⟨1137044, by rfl⟩ : syracuseStep 1516059 = 2274089) B2274089
theorem B1516063 : Blo 1514954 1516063 := bstep (se 1 (by rfl) ⟨1137047, by rfl⟩ : syracuseStep 1516063 = 2274095) B2274095
theorem B1704559 : Blo 1514954 1704559 := bstep (se 1 (by rfl) ⟨1278419, by rfl⟩ : syracuseStep 1704559 = 2556839) B2556839
theorem B1516143 : Blo 1514954 1516143 := bstep (se 1 (by rfl) ⟨1137107, by rfl⟩ : syracuseStep 1516143 = 2274215) B2274215
theorem B1516199 : Blo 1514954 1516199 := bstep (se 1 (by rfl) ⟨1137149, by rfl⟩ : syracuseStep 1516199 = 2274299) B2274299
theorem B1516239 : Blo 1514954 1516239 := bstep (se 1 (by rfl) ⟨1137179, by rfl⟩ : syracuseStep 1516239 = 2274359) B2274359
theorem B1704667 : Blo 1514954 1704667 := bstep (se 1 (by rfl) ⟨1278500, by rfl⟩ : syracuseStep 1704667 = 2557001) B2557001
theorem B1516319 : Blo 1514954 1516319 := bstep (se 1 (by rfl) ⟨1137239, by rfl⟩ : syracuseStep 1516319 = 2274479) B2274479
theorem B9708335 : Blo 1514954 9708335 := bstep (se 1 (by rfl) ⟨7281251, by rfl⟩ : syracuseStep 9708335 = 14562503) B14562503
theorem B21840749 : Blo 1514954 21840749 := bstep (se 3 (by rfl) ⟨4095140, by rfl⟩ : syracuseStep 21840749 = 8190281) B8190281
theorem B3834823 : Blo 1514954 3834823 := bstep (se 1 (by rfl) ⟨2876117, by rfl⟩ : syracuseStep 3834823 = 5752235) B5752235
theorem B3408839 : Blo 1514954 3408839 := bstep (se 1 (by rfl) ⟨2556629, by rfl⟩ : syracuseStep 3408839 = 5113259) B5113259
theorem B10519577 : Blo 1514954 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B1516591 : Blo 1514954 1516591 := bstep (se 1 (by rfl) ⟨1137443, by rfl⟩ : syracuseStep 1516591 = 2274887) B2274887
theorem B1516655 : Blo 1514954 1516655 := bstep (se 1 (by rfl) ⟨1137491, by rfl⟩ : syracuseStep 1516655 = 2274983) B2274983
theorem B1516711 : Blo 1514954 1516711 := bstep (se 1 (by rfl) ⟨1137533, by rfl⟩ : syracuseStep 1516711 = 2275067) B2275067
theorem B1516735 : Blo 1514954 1516735 := bstep (se 1 (by rfl) ⟨1137551, by rfl⟩ : syracuseStep 1516735 = 2275103) B2275103
theorem B5113043 : Blo 1514954 5113043 := bstep (se 1 (by rfl) ⟨3834782, by rfl⟩ : syracuseStep 5113043 = 7669565) B7669565
theorem B9348317 : Blo 1514954 9348317 := bstep (se 3 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 9348317 = 3505619) B3505619
theorem B1516767 : Blo 1514954 1516767 := bstep (se 1 (by rfl) ⟨1137575, by rfl⟩ : syracuseStep 1516767 = 2275151) B2275151
theorem B2557163 : Blo 1514954 2557163 := bstep (se 1 (by rfl) ⟨1917872, by rfl⟩ : syracuseStep 2557163 = 3835745) B3835745
theorem B25273619 : Blo 1514954 25273619 := bstep (se 1 (by rfl) ⟨18955214, by rfl⟩ : syracuseStep 25273619 = 37910429) B37910429
theorem B3409199 : Blo 1514954 3409199 := bstep (se 1 (by rfl) ⟨2556899, by rfl⟩ : syracuseStep 3409199 = 5113799) B5113799
theorem B1516847 : Blo 1514954 1516847 := bstep (se 1 (by rfl) ⟨1137635, by rfl⟩ : syracuseStep 1516847 = 2275271) B2275271
theorem B10929487 : Blo 1514954 10929487 := bstep (se 1 (by rfl) ⟨8197115, by rfl⟩ : syracuseStep 10929487 = 16394231) B16394231
theorem B10929601 : Blo 1514954 10929601 := bstep (se 2 (by rfl) ⟨4098600, by rfl⟩ : syracuseStep 10929601 = 8197201) B8197201
theorem B5113313 : Blo 1514954 5113313 := bstep (se 2 (by rfl) ⟨1917492, by rfl⟩ : syracuseStep 5113313 = 3834985) B3834985
theorem B1918495 : Blo 1514954 1918495 := bstep (se 1 (by rfl) ⟨1438871, by rfl⟩ : syracuseStep 1918495 = 2877743) B2877743
theorem B4097641 : Blo 1514954 4097641 := bstep (se 2 (by rfl) ⟨1536615, by rfl⟩ : syracuseStep 4097641 = 3073231) B3073231
theorem B2557615 : Blo 1514954 2557615 := bstep (se 1 (by rfl) ⟨1918211, by rfl⟩ : syracuseStep 2557615 = 3836423) B3836423
theorem B1820351 : Blo 1514954 1820351 := bstep (se 1 (by rfl) ⟨1365263, by rfl⟩ : syracuseStep 1820351 = 2730527) B2730527
theorem B3835583 : Blo 1514954 3835583 := bstep (se 1 (by rfl) ⟨2876687, by rfl⟩ : syracuseStep 3835583 = 5753375) B5753375
theorem B9217745 : Blo 1514954 9217745 := bstep (se 2 (by rfl) ⟨3456654, by rfl⟩ : syracuseStep 9217745 = 6913309) B6913309
theorem B3409703 : Blo 1514954 3409703 := bstep (se 1 (by rfl) ⟨2557277, by rfl⟩ : syracuseStep 3409703 = 5114555) B5114555
theorem B2844571 : Blo 1514954 2844571 := bstep (se 1 (by rfl) ⟨2133428, by rfl⟩ : syracuseStep 2844571 = 4266857) B4266857
theorem B4319315 : Blo 1514954 4319315 := bstep (se 1 (by rfl) ⟨3239486, by rfl⟩ : syracuseStep 4319315 = 6478973) B6478973
theorem B3410081 : Blo 1514954 3410081 := bstep (se 2 (by rfl) ⟨1278780, by rfl⟩ : syracuseStep 3410081 = 2557561) B2557561
theorem B2427263 : Blo 1514954 2427263 := bstep (se 1 (by rfl) ⟨1820447, by rfl⟩ : syracuseStep 2427263 = 3640895) B3640895
theorem B14567849 : Blo 1514954 14567849 := bstep (se 2 (by rfl) ⟨5462943, by rfl⟩ : syracuseStep 14567849 = 10925887) B10925887
theorem B3238393 : Blo 1514954 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B2558567 : Blo 1514954 2558567 := bstep (se 1 (by rfl) ⟨1918925, by rfl⟩ : syracuseStep 2558567 = 3837851) B3837851
theorem B5114663 : Blo 1514954 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B3410729 : Blo 1514954 3410729 := bstep (se 2 (by rfl) ⟨1279023, by rfl⟩ : syracuseStep 3410729 = 2558047) B2558047
theorem B25889705 : Blo 1514954 25889705 := bstep (se 2 (by rfl) ⟨9708639, by rfl⟩ : syracuseStep 25889705 = 19417279) B19417279
theorem B5114825 : Blo 1514954 5114825 := bstep (se 2 (by rfl) ⟨1918059, by rfl⟩ : syracuseStep 5114825 = 3836119) B3836119
theorem B3238879 : Blo 1514954 3238879 := bstep (se 1 (by rfl) ⟨2429159, by rfl⟩ : syracuseStep 3238879 = 4858319) B4858319
theorem B14568497 : Blo 1514954 14568497 := bstep (se 2 (by rfl) ⟨5463186, by rfl⟩ : syracuseStep 14568497 = 10926373) B10926373
theorem B3410999 : Blo 1514954 3410999 := bstep (se 1 (by rfl) ⟨2558249, by rfl⟩ : syracuseStep 3410999 = 5116499) B5116499
theorem B5114987 : Blo 1514954 5114987 := bstep (se 1 (by rfl) ⟨3836240, by rfl⟩ : syracuseStep 5114987 = 7672481) B7672481
theorem B5115095 : Blo 1514954 5115095 := bstep (se 1 (by rfl) ⟨3836321, by rfl⟩ : syracuseStep 5115095 = 7672643) B7672643
theorem B2559323 : Blo 1514954 2559323 := bstep (se 1 (by rfl) ⟨1919492, by rfl⟩ : syracuseStep 2559323 = 3838985) B3838985
theorem B9719149 : Blo 1514954 9719149 := bstep (se 3 (by rfl) ⟨1822340, by rfl⟩ : syracuseStep 9719149 = 3644681) B3644681
theorem B5115257 : Blo 1514954 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B2272667 : Blo 1514954 2272667 := bstep (se 1 (by rfl) ⟨1704500, by rfl⟩ : syracuseStep 2272667 = 3409001) B3409001
theorem B3837415 : Blo 1514954 3837415 := bstep (se 1 (by rfl) ⟨2878061, by rfl⟩ : syracuseStep 3837415 = 5756123) B5756123
theorem B3411431 : Blo 1514954 3411431 := bstep (se 1 (by rfl) ⟨2558573, by rfl⟩ : syracuseStep 3411431 = 5117147) B5117147
theorem B6475297 : Blo 1514954 6475297 := bstep (se 2 (by rfl) ⟨2428236, by rfl⟩ : syracuseStep 6475297 = 4856473) B4856473
theorem B139988573 : Blo 1514954 139988573 := bstep (se 3 (by rfl) ⟨26247857, by rfl⟩ : syracuseStep 139988573 = 52495715) B52495715
theorem B33246895 : Blo 1514954 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B2879201 : Blo 1514954 2879201 := bstep (se 2 (by rfl) ⟨1079700, by rfl⟩ : syracuseStep 2879201 = 2159401) B2159401
theorem B5115635 : Blo 1514954 5115635 := bstep (se 1 (by rfl) ⟨3836726, by rfl⟩ : syracuseStep 5115635 = 7673453) B7673453
theorem B2273087 : Blo 1514954 2273087 := bstep (se 1 (by rfl) ⟨1704815, by rfl⟩ : syracuseStep 2273087 = 3409631) B3409631
theorem B24579935 : Blo 1514954 24579935 := bstep (se 1 (by rfl) ⟨18434951, by rfl⟩ : syracuseStep 24579935 = 36869903) B36869903
theorem B2428903 : Blo 1514954 2428903 := bstep (se 1 (by rfl) ⟨1821677, by rfl⟩ : syracuseStep 2428903 = 3643355) B3643355
theorem B2273273 : Blo 1514954 2273273 := bstep (se 2 (by rfl) ⟨852477, by rfl⟩ : syracuseStep 2273273 = 1704955) B1704955
theorem B3412007 : Blo 1514954 3412007 := bstep (se 1 (by rfl) ⟨2559005, by rfl⟩ : syracuseStep 3412007 = 5118011) B5118011
theorem B4100159 : Blo 1514954 4100159 := bstep (se 1 (by rfl) ⟨3075119, by rfl⟩ : syracuseStep 4100159 = 6150239) B6150239
theorem B3412187 : Blo 1514954 3412187 := bstep (se 1 (by rfl) ⟨2559140, by rfl⟩ : syracuseStep 3412187 = 5118281) B5118281
theorem B2273513 : Blo 1514954 2273513 := bstep (se 2 (by rfl) ⟨852567, by rfl⟩ : syracuseStep 2273513 = 1705135) B1705135
theorem B8638811 : Blo 1514954 8638811 := bstep (se 1 (by rfl) ⟨6479108, by rfl⟩ : syracuseStep 8638811 = 12958217) B12958217
theorem B1536359 : Blo 1514954 1536359 := bstep (se 1 (by rfl) ⟨1152269, by rfl⟩ : syracuseStep 1536359 = 2304539) B2304539
theorem B2273639 : Blo 1514954 2273639 := bstep (se 1 (by rfl) ⟨1705229, by rfl⟩ : syracuseStep 2273639 = 3410459) B3410459
theorem B3412457 : Blo 1514954 3412457 := bstep (se 2 (by rfl) ⟨1279671, by rfl⟩ : syracuseStep 3412457 = 2559343) B2559343
theorem B8868491 : Blo 1514954 8868491 := bstep (se 1 (by rfl) ⟨6651368, by rfl⟩ : syracuseStep 8868491 = 13302737) B13302737
theorem B2274185 : Blo 1514954 2274185 := bstep (se 2 (by rfl) ⟨852819, by rfl⟩ : syracuseStep 2274185 = 1705639) B1705639
theorem B6476699 : Blo 1514954 6476699 := bstep (se 1 (by rfl) ⟨4857524, by rfl⟩ : syracuseStep 6476699 = 9715049) B9715049
theorem B3412961 : Blo 1514954 3412961 := bstep (se 2 (by rfl) ⟨1279860, by rfl⟩ : syracuseStep 3412961 = 2559721) B2559721
theorem B3413087 : Blo 1514954 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B3642529 : Blo 1514954 3642529 := bstep (se 2 (by rfl) ⟨1365948, by rfl⟩ : syracuseStep 3642529 = 2731897) B2731897
theorem B29127923 : Blo 1514954 29127923 := bstep (se 1 (by rfl) ⟨21845942, by rfl⟩ : syracuseStep 29127923 = 43691885) B43691885
theorem B2274569 : Blo 1514954 2274569 := bstep (se 2 (by rfl) ⟨852963, by rfl⟩ : syracuseStep 2274569 = 1705927) B1705927
theorem B2274623 : Blo 1514954 2274623 := bstep (se 1 (by rfl) ⟨1705967, by rfl⟩ : syracuseStep 2274623 = 3411935) B3411935
theorem B27661769 : Blo 1514954 27661769 := bstep (se 2 (by rfl) ⟨10373163, by rfl⟩ : syracuseStep 27661769 = 20746327) B20746327
theorem B21861971 : Blo 1514954 21861971 := bstep (se 1 (by rfl) ⟨16396478, by rfl⟩ : syracuseStep 21861971 = 32792957) B32792957
theorem B2275049 : Blo 1514954 2275049 := bstep (se 2 (by rfl) ⟨853143, by rfl⟩ : syracuseStep 2275049 = 1706287) B1706287
theorem B2275055 : Blo 1514954 2275055 := bstep (se 1 (by rfl) ⟨1706291, by rfl⟩ : syracuseStep 2275055 = 3412583) B3412583
theorem B7280387 : Blo 1514954 7280387 := bstep (se 1 (by rfl) ⟨5460290, by rfl⟩ : syracuseStep 7280387 = 10920581) B10920581
theorem B99727199 : Blo 1514954 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B12949469 : Blo 1514954 12949469 := bstep (se 3 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 12949469 = 4856051) B4856051
theorem B8755219 : Blo 1514954 8755219 := bstep (se 1 (by rfl) ⟨6566414, by rfl⟩ : syracuseStep 8755219 = 13132829) B13132829
theorem B4610537 : Blo 1514954 4610537 := bstep (se 2 (by rfl) ⟨1728951, by rfl⟩ : syracuseStep 4610537 = 3457903) B3457903
theorem B11991563 : Blo 1514954 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B1514959 : Blo 1514954 1514959 := bstep (se 1 (by rfl) ⟨1136219, by rfl⟩ : syracuseStep 1514959 = 2272439) B2272439
theorem B1515119 : Blo 1514954 1515119 := bstep (se 1 (by rfl) ⟨1136339, by rfl⟩ : syracuseStep 1515119 = 2272679) B2272679
theorem B1515175 : Blo 1514954 1515175 := bstep (se 1 (by rfl) ⟨1136381, by rfl⟩ : syracuseStep 1515175 = 2272763) B2272763
theorem B1515239 : Blo 1514954 1515239 := bstep (se 1 (by rfl) ⟨1136429, by rfl⟩ : syracuseStep 1515239 = 2272859) B2272859
theorem B25902827 : Blo 1514954 25902827 := bstep (se 1 (by rfl) ⟨19427120, by rfl⟩ : syracuseStep 25902827 = 38854241) B38854241
theorem B62234365 : Blo 1514954 62234365 := bstep (se 3 (by rfl) ⟨11668943, by rfl⟩ : syracuseStep 62234365 = 23337887) B23337887
theorem B1515295 : Blo 1514954 1515295 := bstep (se 1 (by rfl) ⟨1136471, by rfl⟩ : syracuseStep 1515295 = 2272943) B2272943
theorem B12296033 : Blo 1514954 12296033 := bstep (se 2 (by rfl) ⟨4611012, by rfl⟩ : syracuseStep 12296033 = 9222025) B9222025
theorem B1515375 : Blo 1514954 1515375 := bstep (se 1 (by rfl) ⟨1136531, by rfl⟩ : syracuseStep 1515375 = 2273063) B2273063
theorem B1515431 : Blo 1514954 1515431 := bstep (se 1 (by rfl) ⟨1136573, by rfl⟩ : syracuseStep 1515431 = 2273147) B2273147
theorem B4857833 : Blo 1514954 4857833 := bstep (se 2 (by rfl) ⟨1821687, by rfl⟩ : syracuseStep 4857833 = 3643375) B3643375
theorem B46694501 : Blo 1514954 46694501 := bstep (se 4 (by rfl) ⟨4377609, by rfl⟩ : syracuseStep 46694501 = 8755219) B8755219
theorem B1515675 : Blo 1514954 1515675 := bstep (se 1 (by rfl) ⟨1136756, by rfl⟩ : syracuseStep 1515675 = 2273513) B2273513
theorem B5759207 : Blo 1514954 5759207 := bstep (se 1 (by rfl) ⟨4319405, by rfl⟩ : syracuseStep 5759207 = 8638811) B8638811
theorem B1515759 : Blo 1514954 1515759 := bstep (se 1 (by rfl) ⟨1136819, by rfl⟩ : syracuseStep 1515759 = 2273639) B2273639
theorem B280002977 : Blo 1514954 280002977 := bstep (se 2 (by rfl) ⟨105001116, by rfl⟩ : syracuseStep 280002977 = 210002233) B210002233
theorem B6472223 : Blo 1514954 6472223 := bstep (se 1 (by rfl) ⟨4854167, by rfl⟩ : syracuseStep 6472223 = 9708335) B9708335
theorem B1516123 : Blo 1514954 1516123 := bstep (se 1 (by rfl) ⟨1137092, by rfl⟩ : syracuseStep 1516123 = 2274185) B2274185
theorem B4317799 : Blo 1514954 4317799 := bstep (se 1 (by rfl) ⟨3238349, by rfl⟩ : syracuseStep 4317799 = 6476699) B6476699
theorem B12944033 : Blo 1514954 12944033 := bstep (se 2 (by rfl) ⟨4854012, by rfl⟩ : syracuseStep 12944033 = 9708025) B9708025
theorem B4317857 : Blo 1514954 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B7013051 : Blo 1514954 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B3408695 : Blo 1514954 3408695 := bstep (se 1 (by rfl) ⟨2556521, by rfl⟩ : syracuseStep 3408695 = 5113043) B5113043
theorem B1704775 : Blo 1514954 1704775 := bstep (se 1 (by rfl) ⟨1278581, by rfl⟩ : syracuseStep 1704775 = 2557163) B2557163
theorem B1516379 : Blo 1514954 1516379 := bstep (se 1 (by rfl) ⟨1137284, by rfl⟩ : syracuseStep 1516379 = 2274569) B2274569
theorem B1516415 : Blo 1514954 1516415 := bstep (se 1 (by rfl) ⟨1137311, by rfl⟩ : syracuseStep 1516415 = 2274623) B2274623
theorem B18441179 : Blo 1514954 18441179 := bstep (se 1 (by rfl) ⟨13830884, by rfl⟩ : syracuseStep 18441179 = 27661769) B27661769
theorem B3408875 : Blo 1514954 3408875 := bstep (se 1 (by rfl) ⟨2556656, by rfl⟩ : syracuseStep 3408875 = 5113313) B5113313
theorem B14574647 : Blo 1514954 14574647 := bstep (se 1 (by rfl) ⟨10930985, by rfl⟩ : syracuseStep 14574647 = 21861971) B21861971
theorem B2557055 : Blo 1514954 2557055 := bstep (se 1 (by rfl) ⟨1917791, by rfl⟩ : syracuseStep 2557055 = 3835583) B3835583
theorem B6145163 : Blo 1514954 6145163 := bstep (se 1 (by rfl) ⟨4608872, by rfl⟩ : syracuseStep 6145163 = 9217745) B9217745
theorem B1516699 : Blo 1514954 1516699 := bstep (se 1 (by rfl) ⟨1137524, by rfl⟩ : syracuseStep 1516699 = 2275049) B2275049
theorem B1516703 : Blo 1514954 1516703 := bstep (se 1 (by rfl) ⟨1137527, by rfl⟩ : syracuseStep 1516703 = 2275055) B2275055
theorem B5113097 : Blo 1514954 5113097 := bstep (se 2 (by rfl) ⟨1917411, by rfl⟩ : syracuseStep 5113097 = 3834823) B3834823
theorem B4318505 : Blo 1514954 4318505 := bstep (se 2 (by rfl) ⟨1619439, by rfl⟩ : syracuseStep 4318505 = 3238879) B3238879
theorem B3073691 : Blo 1514954 3073691 := bstep (se 1 (by rfl) ⟨2305268, by rfl⟩ : syracuseStep 3073691 = 4610537) B4610537
theorem B1705711 : Blo 1514954 1705711 := bstep (se 1 (by rfl) ⟨1279283, by rfl⟩ : syracuseStep 1705711 = 2558567) B2558567
theorem B3409775 : Blo 1514954 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B3409883 : Blo 1514954 3409883 := bstep (se 1 (by rfl) ⟨2557412, by rfl⟩ : syracuseStep 3409883 = 5114825) B5114825
theorem B2557993 : Blo 1514954 2557993 := bstep (se 2 (by rfl) ⟨959247, by rfl⟩ : syracuseStep 2557993 = 1918495) B1918495
theorem B3409991 : Blo 1514954 3409991 := bstep (se 1 (by rfl) ⟨2557493, by rfl⟩ : syracuseStep 3409991 = 5114987) B5114987
theorem B3410063 : Blo 1514954 3410063 := bstep (se 1 (by rfl) ⟨2557547, by rfl⟩ : syracuseStep 3410063 = 5115095) B5115095
theorem B1706215 : Blo 1514954 1706215 := bstep (se 1 (by rfl) ⟨1279661, by rfl⟩ : syracuseStep 1706215 = 2559323) B2559323
theorem B3410153 : Blo 1514954 3410153 := bstep (se 2 (by rfl) ⟨1278807, by rfl⟩ : syracuseStep 3410153 = 2557615) B2557615
theorem B44329193 : Blo 1514954 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B3410171 : Blo 1514954 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B82979153 : Blo 1514954 82979153 := bstep (se 2 (by rfl) ⟨31117182, by rfl⟩ : syracuseStep 82979153 = 62234365) B62234365
theorem B93325715 : Blo 1514954 93325715 := bstep (se 1 (by rfl) ⟨69994286, by rfl⟩ : syracuseStep 93325715 = 139988573) B139988573
theorem B1919467 : Blo 1514954 1919467 := bstep (se 1 (by rfl) ⟨1439600, by rfl⟩ : syracuseStep 1919467 = 2879201) B2879201
theorem B3410423 : Blo 1514954 3410423 := bstep (se 1 (by rfl) ⟨2557817, by rfl⟩ : syracuseStep 3410423 = 5115635) B5115635
theorem B16386623 : Blo 1514954 16386623 := bstep (se 1 (by rfl) ⟨12289967, by rfl⟩ : syracuseStep 16386623 = 24579935) B24579935
theorem B3238537 : Blo 1514954 3238537 := bstep (se 2 (by rfl) ⟨1214451, by rfl⟩ : syracuseStep 3238537 = 2428903) B2428903
theorem B3238555 : Blo 1514954 3238555 := bstep (se 1 (by rfl) ⟨2428916, by rfl⟩ : syracuseStep 3238555 = 4857833) B4857833
theorem B8416007 : Blo 1514954 8416007 := bstep (se 1 (by rfl) ⟨6312005, by rfl⟩ : syracuseStep 8416007 = 12624011) B12624011
theorem B7678799 : Blo 1514954 7678799 := bstep (se 1 (by rfl) ⟨5759099, by rfl⟩ : syracuseStep 7678799 = 11518199) B11518199
theorem B14560499 : Blo 1514954 14560499 := bstep (se 1 (by rfl) ⟨10920374, by rfl⟩ : syracuseStep 14560499 = 21840749) B21840749
theorem B2272559 : Blo 1514954 2272559 := bstep (se 1 (by rfl) ⟨1704419, by rfl⟩ : syracuseStep 2272559 = 3408839) B3408839
theorem B2272745 : Blo 1514954 2272745 := bstep (se 2 (by rfl) ⟨852279, by rfl⟩ : syracuseStep 2272745 = 1704559) B1704559
theorem B19418615 : Blo 1514954 19418615 := bstep (se 1 (by rfl) ⟨14563961, by rfl⟩ : syracuseStep 19418615 = 29127923) B29127923
theorem B2272799 : Blo 1514954 2272799 := bstep (se 1 (by rfl) ⟨1704599, by rfl⟩ : syracuseStep 2272799 = 3409199) B3409199
theorem B2272889 : Blo 1514954 2272889 := bstep (se 2 (by rfl) ⟨852333, by rfl⟩ : syracuseStep 2272889 = 1704667) B1704667
theorem B16387829 : Blo 1514954 16387829 := bstep (se 5 (by rfl) ⟨768179, by rfl⟩ : syracuseStep 16387829 = 1536359) B1536359
theorem B4853591 : Blo 1514954 4853591 := bstep (se 1 (by rfl) ⟨3640193, by rfl⟩ : syracuseStep 4853591 = 7280387) B7280387
theorem B2273135 : Blo 1514954 2273135 := bstep (se 1 (by rfl) ⟨1704851, by rfl⟩ : syracuseStep 2273135 = 3409703) B3409703
theorem B2879543 : Blo 1514954 2879543 := bstep (se 1 (by rfl) ⟨2159657, by rfl⟩ : syracuseStep 2879543 = 4319315) B4319315
theorem B2273387 : Blo 1514954 2273387 := bstep (se 1 (by rfl) ⟨1705040, by rfl⟩ : syracuseStep 2273387 = 3410081) B3410081
theorem B1618175 : Blo 1514954 1618175 := bstep (se 1 (by rfl) ⟨1213631, by rfl⟩ : syracuseStep 1618175 = 2427263) B2427263
theorem B9711899 : Blo 1514954 9711899 := bstep (se 1 (by rfl) ⟨7283924, by rfl⟩ : syracuseStep 9711899 = 14567849) B14567849
theorem B4854269 : Blo 1514954 4854269 := bstep (se 3 (by rfl) ⟨910175, by rfl⟩ : syracuseStep 4854269 = 1820351) B1820351
theorem B2273819 : Blo 1514954 2273819 := bstep (se 1 (by rfl) ⟨1705364, by rfl⟩ : syracuseStep 2273819 = 3410729) B3410729
theorem B5116553 : Blo 1514954 5116553 := bstep (se 2 (by rfl) ⟨1918707, by rfl⟩ : syracuseStep 5116553 = 3837415) B3837415
theorem B9712331 : Blo 1514954 9712331 := bstep (se 1 (by rfl) ⟨7284248, by rfl⟩ : syracuseStep 9712331 = 14568497) B14568497
theorem B2273999 : Blo 1514954 2273999 := bstep (se 1 (by rfl) ⟨1705499, by rfl⟩ : syracuseStep 2273999 = 3410999) B3410999
theorem B2274287 : Blo 1514954 2274287 := bstep (se 1 (by rfl) ⟨1705715, by rfl⟩ : syracuseStep 2274287 = 3411431) B3411431
theorem B8197355 : Blo 1514954 8197355 := bstep (se 1 (by rfl) ⟨6148016, by rfl⟩ : syracuseStep 8197355 = 12296033) B12296033
theorem B2274671 : Blo 1514954 2274671 := bstep (se 1 (by rfl) ⟨1706003, by rfl⟩ : syracuseStep 2274671 = 3412007) B3412007
theorem B2733439 : Blo 1514954 2733439 := bstep (se 1 (by rfl) ⟨2050079, by rfl⟩ : syracuseStep 2733439 = 4100159) B4100159
theorem B2274791 : Blo 1514954 2274791 := bstep (se 1 (by rfl) ⟨1706093, by rfl⟩ : syracuseStep 2274791 = 3412187) B3412187
theorem B17274383 : Blo 1514954 17274383 := bstep (se 1 (by rfl) ⟨12955787, by rfl⟩ : syracuseStep 17274383 = 25911575) B25911575
theorem B2274971 : Blo 1514954 2274971 := bstep (se 1 (by rfl) ⟨1706228, by rfl⟩ : syracuseStep 2274971 = 3412457) B3412457
theorem B5912327 : Blo 1514954 5912327 := bstep (se 1 (by rfl) ⟨4434245, by rfl⟩ : syracuseStep 5912327 = 8868491) B8868491
theorem B2275307 : Blo 1514954 2275307 := bstep (se 1 (by rfl) ⟨1706480, by rfl⟩ : syracuseStep 2275307 = 3412961) B3412961
theorem B2275391 : Blo 1514954 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B6232211 : Blo 1514954 6232211 := bstep (se 1 (by rfl) ⟨4674158, by rfl⟩ : syracuseStep 6232211 = 9348317) B9348317
theorem B16849079 : Blo 1514954 16849079 := bstep (se 1 (by rfl) ⟨12636809, by rfl⟩ : syracuseStep 16849079 = 25273619) B25273619
theorem B66484799 : Blo 1514954 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B8632979 : Blo 1514954 8632979 := bstep (se 1 (by rfl) ⟨6474734, by rfl⟩ : syracuseStep 8632979 = 12949469) B12949469
theorem B4856705 : Blo 1514954 4856705 := bstep (se 2 (by rfl) ⟨1821264, by rfl⟩ : syracuseStep 4856705 = 3642529) B3642529
theorem B7994375 : Blo 1514954 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B14572649 : Blo 1514954 14572649 := bstep (se 2 (by rfl) ⟨5464743, by rfl⟩ : syracuseStep 14572649 = 10929487) B10929487
theorem B12958865 : Blo 1514954 12958865 := bstep (se 2 (by rfl) ⟨4859574, by rfl⟩ : syracuseStep 12958865 = 9719149) B9719149
theorem B14572801 : Blo 1514954 14572801 := bstep (se 2 (by rfl) ⟨5464800, by rfl⟩ : syracuseStep 14572801 = 10929601) B10929601
theorem B17259803 : Blo 1514954 17259803 := bstep (se 1 (by rfl) ⟨12944852, by rfl⟩ : syracuseStep 17259803 = 25889705) B25889705
theorem B8633729 : Blo 1514954 8633729 := bstep (se 2 (by rfl) ⟨3237648, by rfl⟩ : syracuseStep 8633729 = 6475297) B6475297
theorem B5463521 : Blo 1514954 5463521 := bstep (se 2 (by rfl) ⟨2048820, by rfl⟩ : syracuseStep 5463521 = 4097641) B4097641
theorem B1515111 : Blo 1514954 1515111 := bstep (se 1 (by rfl) ⟨1136333, by rfl⟩ : syracuseStep 1515111 = 2272667) B2272667
theorem B17268551 : Blo 1514954 17268551 := bstep (se 1 (by rfl) ⟨12951413, by rfl⟩ : syracuseStep 17268551 = 25902827) B25902827
theorem B3792761 : Blo 1514954 3792761 := bstep (se 2 (by rfl) ⟨1422285, by rfl⟩ : syracuseStep 3792761 = 2844571) B2844571
theorem B1515391 : Blo 1514954 1515391 := bstep (se 1 (by rfl) ⟨1136543, by rfl⟩ : syracuseStep 1515391 = 2273087) B2273087
theorem B1515515 : Blo 1514954 1515515 := bstep (se 1 (by rfl) ⟨1136636, by rfl⟩ : syracuseStep 1515515 = 2273273) B2273273
theorem B31129667 : Blo 1514954 31129667 := bstep (se 1 (by rfl) ⟨23347250, by rfl⟩ : syracuseStep 31129667 = 46694501) B46694501
theorem B1515591 : Blo 1514954 1515591 := bstep (se 1 (by rfl) ⟨1136693, by rfl⟩ : syracuseStep 1515591 = 2273387) B2273387
theorem B1515879 : Blo 1514954 1515879 := bstep (se 1 (by rfl) ⟨1136909, by rfl⟩ : syracuseStep 1515879 = 2273819) B2273819
theorem B1515999 : Blo 1514954 1515999 := bstep (se 1 (by rfl) ⟨1136999, by rfl⟩ : syracuseStep 1515999 = 2273999) B2273999
theorem B1516191 : Blo 1514954 1516191 := bstep (se 1 (by rfl) ⟨1137143, by rfl⟩ : syracuseStep 1516191 = 2274287) B2274287
theorem B9716431 : Blo 1514954 9716431 := bstep (se 1 (by rfl) ⟨7287323, by rfl⟩ : syracuseStep 9716431 = 14574647) B14574647
theorem B1704703 : Blo 1514954 1704703 := bstep (se 1 (by rfl) ⟨1278527, by rfl⟩ : syracuseStep 1704703 = 2557055) B2557055
theorem B4096775 : Blo 1514954 4096775 := bstep (se 1 (by rfl) ⟨3072581, by rfl⟩ : syracuseStep 4096775 = 6145163) B6145163
theorem B5464903 : Blo 1514954 5464903 := bstep (se 1 (by rfl) ⟨4098677, by rfl⟩ : syracuseStep 5464903 = 8197355) B8197355
theorem B3408731 : Blo 1514954 3408731 := bstep (se 1 (by rfl) ⟨2556548, by rfl⟩ : syracuseStep 3408731 = 5113097) B5113097
theorem B4318049 : Blo 1514954 4318049 := bstep (se 2 (by rfl) ⟨1619268, by rfl⟩ : syracuseStep 4318049 = 3238537) B3238537
theorem B4318073 : Blo 1514954 4318073 := bstep (se 2 (by rfl) ⟨1619277, by rfl⟩ : syracuseStep 4318073 = 3238555) B3238555
theorem B1516447 : Blo 1514954 1516447 := bstep (se 1 (by rfl) ⟨1137335, by rfl⟩ : syracuseStep 1516447 = 2274671) B2274671
theorem B1516527 : Blo 1514954 1516527 := bstep (se 1 (by rfl) ⟨1137395, by rfl⟩ : syracuseStep 1516527 = 2274791) B2274791
theorem B1516647 : Blo 1514954 1516647 := bstep (se 1 (by rfl) ⟨1137485, by rfl⟩ : syracuseStep 1516647 = 2274971) B2274971
theorem B3941551 : Blo 1514954 3941551 := bstep (se 1 (by rfl) ⟨2956163, by rfl⟩ : syracuseStep 3941551 = 5912327) B5912327
theorem B1516871 : Blo 1514954 1516871 := bstep (se 1 (by rfl) ⟨1137653, by rfl⟩ : syracuseStep 1516871 = 2275307) B2275307
theorem B12944717 : Blo 1514954 12944717 := bstep (se 3 (by rfl) ⟨2427134, by rfl⟩ : syracuseStep 12944717 = 4854269) B4854269
theorem B1516927 : Blo 1514954 1516927 := bstep (se 1 (by rfl) ⟨1137695, by rfl⟩ : syracuseStep 1516927 = 2275391) B2275391
theorem B4154807 : Blo 1514954 4154807 := bstep (se 1 (by rfl) ⟨3116105, by rfl⟩ : syracuseStep 4154807 = 6232211) B6232211
theorem B11232719 : Blo 1514954 11232719 := bstep (se 1 (by rfl) ⟨8424539, by rfl⟩ : syracuseStep 11232719 = 16849079) B16849079
theorem B3237803 : Blo 1514954 3237803 := bstep (se 1 (by rfl) ⟨2428352, by rfl⟩ : syracuseStep 3237803 = 4856705) B4856705
theorem B12945743 : Blo 1514954 12945743 := bstep (se 1 (by rfl) ⟨9709307, by rfl⟩ : syracuseStep 12945743 = 19418615) B19418615
theorem B11512367 : Blo 1514954 11512367 := bstep (se 1 (by rfl) ⟨8634275, by rfl⟩ : syracuseStep 11512367 = 17268551) B17268551
theorem B1919695 : Blo 1514954 1919695 := bstep (se 1 (by rfl) ⟨1439771, by rfl⟩ : syracuseStep 1919695 = 2879543) B2879543
theorem B3410657 : Blo 1514954 3410657 := bstep (se 2 (by rfl) ⟨1278996, by rfl⟩ : syracuseStep 3410657 = 2557993) B2557993
theorem B6474599 : Blo 1514954 6474599 := bstep (se 1 (by rfl) ⟨4855949, by rfl⟩ : syracuseStep 6474599 = 9711899) B9711899
theorem B3411035 : Blo 1514954 3411035 := bstep (se 1 (by rfl) ⟨2558276, by rfl⟩ : syracuseStep 3411035 = 5116553) B5116553
theorem B8629355 : Blo 1514954 8629355 := bstep (se 1 (by rfl) ⟨6472016, by rfl⟩ : syracuseStep 8629355 = 12944033) B12944033
theorem B2878571 : Blo 1514954 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B6474887 : Blo 1514954 6474887 := bstep (se 1 (by rfl) ⟨4856165, by rfl⟩ : syracuseStep 6474887 = 9712331) B9712331
theorem B2272463 : Blo 1514954 2272463 := bstep (se 1 (by rfl) ⟨1704347, by rfl⟩ : syracuseStep 2272463 = 3408695) B3408695
theorem B2559289 : Blo 1514954 2559289 := bstep (se 2 (by rfl) ⟨959733, by rfl⟩ : syracuseStep 2559289 = 1919467) B1919467
theorem B2272583 : Blo 1514954 2272583 := bstep (se 1 (by rfl) ⟨1704437, by rfl⟩ : syracuseStep 2272583 = 3408875) B3408875
theorem B2879003 : Blo 1514954 2879003 := bstep (se 1 (by rfl) ⟨2159252, by rfl⟩ : syracuseStep 2879003 = 4318505) B4318505
theorem B2273033 : Blo 1514954 2273033 := bstep (se 2 (by rfl) ⟨852387, by rfl⟩ : syracuseStep 2273033 = 1704775) B1704775
theorem B2273183 : Blo 1514954 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B2273255 : Blo 1514954 2273255 := bstep (se 1 (by rfl) ⟨1704941, by rfl⟩ : syracuseStep 2273255 = 3409883) B3409883
theorem B2273327 : Blo 1514954 2273327 := bstep (se 1 (by rfl) ⟨1704995, by rfl⟩ : syracuseStep 2273327 = 3409991) B3409991
theorem B2273375 : Blo 1514954 2273375 := bstep (se 1 (by rfl) ⟨1705031, by rfl⟩ : syracuseStep 2273375 = 3410063) B3410063
theorem B2273435 : Blo 1514954 2273435 := bstep (se 1 (by rfl) ⟨1705076, by rfl⟩ : syracuseStep 2273435 = 3410153) B3410153
theorem B29552795 : Blo 1514954 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B2273447 : Blo 1514954 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B2273615 : Blo 1514954 2273615 := bstep (se 1 (by rfl) ⟨1705211, by rfl⟩ : syracuseStep 2273615 = 3410423) B3410423
theorem B10924415 : Blo 1514954 10924415 := bstep (se 1 (by rfl) ⟨8193311, by rfl⟩ : syracuseStep 10924415 = 16386623) B16386623
theorem B44323199 : Blo 1514954 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B8196509 : Blo 1514954 8196509 := bstep (se 3 (by rfl) ⟨1536845, by rfl⟩ : syracuseStep 8196509 = 3073691) B3073691
theorem B5755319 : Blo 1514954 5755319 := bstep (se 1 (by rfl) ⟨4316489, by rfl⟩ : syracuseStep 5755319 = 8632979) B8632979
theorem B5329583 : Blo 1514954 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B8639243 : Blo 1514954 8639243 := bstep (se 1 (by rfl) ⟨6479432, by rfl⟩ : syracuseStep 8639243 = 12958865) B12958865
theorem B11506535 : Blo 1514954 11506535 := bstep (se 1 (by rfl) ⟨8629901, by rfl⟩ : syracuseStep 11506535 = 17259803) B17259803
theorem B5755819 : Blo 1514954 5755819 := bstep (se 1 (by rfl) ⟨4316864, by rfl⟩ : syracuseStep 5755819 = 8633729) B8633729
theorem B2274281 : Blo 1514954 2274281 := bstep (se 2 (by rfl) ⟨852855, by rfl⟩ : syracuseStep 2274281 = 1705711) B1705711
theorem B3642347 : Blo 1514954 3642347 := bstep (se 1 (by rfl) ⟨2731760, by rfl⟩ : syracuseStep 3642347 = 5463521) B5463521
theorem B10925219 : Blo 1514954 10925219 := bstep (se 1 (by rfl) ⟨8193914, by rfl⟩ : syracuseStep 10925219 = 16387829) B16387829
theorem B2528507 : Blo 1514954 2528507 := bstep (se 1 (by rfl) ⟨1896380, by rfl⟩ : syracuseStep 2528507 = 3792761) B3792761
theorem B3839471 : Blo 1514954 3839471 := bstep (se 1 (by rfl) ⟨2879603, by rfl⟩ : syracuseStep 3839471 = 5759207) B5759207
theorem B186668651 : Blo 1514954 186668651 := bstep (se 1 (by rfl) ⟨140001488, by rfl⟩ : syracuseStep 186668651 = 280002977) B280002977
theorem B2274953 : Blo 1514954 2274953 := bstep (se 2 (by rfl) ⟨853107, by rfl⟩ : syracuseStep 2274953 = 1706215) B1706215
theorem B4314815 : Blo 1514954 4314815 := bstep (se 1 (by rfl) ⟨3236111, by rfl⟩ : syracuseStep 4314815 = 6472223) B6472223
theorem B4675367 : Blo 1514954 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B38827997 : Blo 1514954 38827997 := bstep (se 3 (by rfl) ⟨7280249, by rfl⟩ : syracuseStep 38827997 = 14560499) B14560499
theorem B12294119 : Blo 1514954 12294119 := bstep (se 1 (by rfl) ⟨9220589, by rfl⟩ : syracuseStep 12294119 = 18441179) B18441179
theorem B4315133 : Blo 1514954 4315133 := bstep (se 3 (by rfl) ⟨809087, by rfl⟩ : syracuseStep 4315133 = 1618175) B1618175
theorem B5757065 : Blo 1514954 5757065 := bstep (se 2 (by rfl) ⟨2158899, by rfl⟩ : syracuseStep 5757065 = 4317799) B4317799
theorem B11516255 : Blo 1514954 11516255 := bstep (se 1 (by rfl) ⟨8637191, by rfl⟩ : syracuseStep 11516255 = 17274383) B17274383
theorem B55319435 : Blo 1514954 55319435 := bstep (se 1 (by rfl) ⟨41489576, by rfl⟩ : syracuseStep 55319435 = 82979153) B82979153
theorem B62217143 : Blo 1514954 62217143 := bstep (se 1 (by rfl) ⟨46662857, by rfl⟩ : syracuseStep 62217143 = 93325715) B93325715
theorem B19430401 : Blo 1514954 19430401 := bstep (se 2 (by rfl) ⟨7286400, by rfl⟩ : syracuseStep 19430401 = 14572801) B14572801
theorem B3644585 : Blo 1514954 3644585 := bstep (se 2 (by rfl) ⟨1366719, by rfl⟩ : syracuseStep 3644585 = 2733439) B2733439
theorem B5610671 : Blo 1514954 5610671 := bstep (se 1 (by rfl) ⟨4208003, by rfl⟩ : syracuseStep 5610671 = 8416007) B8416007
theorem B5119199 : Blo 1514954 5119199 := bstep (se 1 (by rfl) ⟨3839399, by rfl⟩ : syracuseStep 5119199 = 7678799) B7678799
theorem B9715099 : Blo 1514954 9715099 := bstep (se 1 (by rfl) ⟨7286324, by rfl⟩ : syracuseStep 9715099 = 14572649) B14572649
theorem B1515039 : Blo 1514954 1515039 := bstep (se 1 (by rfl) ⟨1136279, by rfl⟩ : syracuseStep 1515039 = 2272559) B2272559
theorem B1515163 : Blo 1514954 1515163 := bstep (se 1 (by rfl) ⟨1136372, by rfl⟩ : syracuseStep 1515163 = 2272745) B2272745
theorem B1515199 : Blo 1514954 1515199 := bstep (se 1 (by rfl) ⟨1136399, by rfl⟩ : syracuseStep 1515199 = 2272799) B2272799
theorem B1515259 : Blo 1514954 1515259 := bstep (se 1 (by rfl) ⟨1136444, by rfl⟩ : syracuseStep 1515259 = 2272889) B2272889
theorem B3235727 : Blo 1514954 3235727 := bstep (se 1 (by rfl) ⟨2426795, by rfl⟩ : syracuseStep 3235727 = 4853591) B4853591
theorem B1515423 : Blo 1514954 1515423 := bstep (se 1 (by rfl) ⟨1136567, by rfl⟩ : syracuseStep 1515423 = 2273135) B2273135
theorem B1515551 : Blo 1514954 1515551 := bstep (se 1 (by rfl) ⟨1136663, by rfl⟩ : syracuseStep 1515551 = 2273327) B2273327
theorem B1515583 : Blo 1514954 1515583 := bstep (se 1 (by rfl) ⟨1136687, by rfl⟩ : syracuseStep 1515583 = 2273375) B2273375
theorem B1515623 : Blo 1514954 1515623 := bstep (se 1 (by rfl) ⟨1136717, by rfl⟩ : syracuseStep 1515623 = 2273435) B2273435
theorem B19701863 : Blo 1514954 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B1515631 : Blo 1514954 1515631 := bstep (se 1 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 1515631 = 2273447) B2273447
theorem B1515743 : Blo 1514954 1515743 := bstep (se 1 (by rfl) ⟨1136807, by rfl⟩ : syracuseStep 1515743 = 2273615) B2273615
theorem B7282943 : Blo 1514954 7282943 := bstep (se 1 (by rfl) ⟨5462207, by rfl⟩ : syracuseStep 7282943 = 10924415) B10924415
theorem B29548799 : Blo 1514954 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B5759495 : Blo 1514954 5759495 := bstep (se 1 (by rfl) ⟨4319621, by rfl⟩ : syracuseStep 5759495 = 8639243) B8639243
theorem B6742685 : Blo 1514954 6742685 := bstep (se 3 (by rfl) ⟨1264253, by rfl⟩ : syracuseStep 6742685 = 2528507) B2528507
theorem B1516187 : Blo 1514954 1516187 := bstep (se 1 (by rfl) ⟨1137140, by rfl⟩ : syracuseStep 1516187 = 2274281) B2274281
theorem B2769871 : Blo 1514954 2769871 := bstep (se 1 (by rfl) ⟨2077403, by rfl⟩ : syracuseStep 2769871 = 4154807) B4154807
theorem B7488479 : Blo 1514954 7488479 := bstep (se 1 (by rfl) ⟨5616359, by rfl⟩ : syracuseStep 7488479 = 11232719) B11232719
theorem B124445767 : Blo 1514954 124445767 := bstep (se 1 (by rfl) ⟨93334325, by rfl⟩ : syracuseStep 124445767 = 186668651) B186668651
theorem B21857357 : Blo 1514954 21857357 := bstep (se 3 (by rfl) ⟨4098254, by rfl⟩ : syracuseStep 21857357 = 8196509) B8196509
theorem B1516635 : Blo 1514954 1516635 := bstep (se 1 (by rfl) ⟨1137476, by rfl⟩ : syracuseStep 1516635 = 2274953) B2274953
theorem B2876543 : Blo 1514954 2876543 := bstep (se 1 (by rfl) ⟨2157407, by rfl⟩ : syracuseStep 2876543 = 4314815) B4314815
theorem B7677341 : Blo 1514954 7677341 := bstep (se 3 (by rfl) ⟨1439501, by rfl⟩ : syracuseStep 7677341 = 2879003) B2879003
theorem B7677503 : Blo 1514954 7677503 := bstep (se 1 (by rfl) ⟨5758127, by rfl⟩ : syracuseStep 7677503 = 11516255) B11516255
theorem B12953465 : Blo 1514954 12953465 := bstep (se 2 (by rfl) ⟨4857549, by rfl⟩ : syracuseStep 12953465 = 9715099) B9715099
theorem B41478095 : Blo 1514954 41478095 := bstep (se 1 (by rfl) ⟨31108571, by rfl⟩ : syracuseStep 41478095 = 62217143) B62217143
theorem B5752903 : Blo 1514954 5752903 := bstep (se 1 (by rfl) ⟨4314677, by rfl⟩ : syracuseStep 5752903 = 8629355) B8629355
theorem B1919047 : Blo 1514954 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B8628605 : Blo 1514954 8628605 := bstep (se 3 (by rfl) ⟨1617863, by rfl⟩ : syracuseStep 8628605 = 3235727) B3235727
theorem B20753111 : Blo 1514954 20753111 := bstep (se 1 (by rfl) ⟨15564833, by rfl⟩ : syracuseStep 20753111 = 31129667) B31129667
theorem B3836879 : Blo 1514954 3836879 := bstep (se 1 (by rfl) ⟨2877659, by rfl⟩ : syracuseStep 3836879 = 5755319) B5755319
theorem B29133917 : Blo 1514954 29133917 := bstep (se 3 (by rfl) ⟨5462609, by rfl⟩ : syracuseStep 29133917 = 10925219) B10925219
theorem B2272487 : Blo 1514954 2272487 := bstep (se 1 (by rfl) ⟨1704365, by rfl⟩ : syracuseStep 2272487 = 3408731) B3408731
theorem B7671023 : Blo 1514954 7671023 := bstep (se 1 (by rfl) ⟨5753267, by rfl⟩ : syracuseStep 7671023 = 11506535) B11506535
theorem B2878715 : Blo 1514954 2878715 := bstep (se 1 (by rfl) ⟨2159036, by rfl⟩ : syracuseStep 2878715 = 4318073) B4318073
theorem B2428231 : Blo 1514954 2428231 := bstep (se 1 (by rfl) ⟨1821173, by rfl⟩ : syracuseStep 2428231 = 3642347) B3642347
theorem B8629811 : Blo 1514954 8629811 := bstep (se 1 (by rfl) ⟨6472358, by rfl⟩ : syracuseStep 8629811 = 12944717) B12944717
theorem B12955241 : Blo 1514954 12955241 := bstep (se 2 (by rfl) ⟨4858215, by rfl⟩ : syracuseStep 12955241 = 9716431) B9716431
theorem B2559593 : Blo 1514954 2559593 := bstep (se 2 (by rfl) ⟨959847, by rfl⟩ : syracuseStep 2559593 = 1919695) B1919695
theorem B2559647 : Blo 1514954 2559647 := bstep (se 1 (by rfl) ⟨1919735, by rfl⟩ : syracuseStep 2559647 = 3839471) B3839471
theorem B2272937 : Blo 1514954 2272937 := bstep (se 2 (by rfl) ⟨852351, by rfl⟩ : syracuseStep 2272937 = 1704703) B1704703
theorem B7286537 : Blo 1514954 7286537 := bstep (se 2 (by rfl) ⟨2732451, by rfl⟩ : syracuseStep 7286537 = 5464903) B5464903
theorem B3116911 : Blo 1514954 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B2158535 : Blo 1514954 2158535 := bstep (se 1 (by rfl) ⟨1618901, by rfl⟩ : syracuseStep 2158535 = 3237803) B3237803
theorem B8196079 : Blo 1514954 8196079 := bstep (se 1 (by rfl) ⟨6147059, by rfl⟩ : syracuseStep 8196079 = 12294119) B12294119
theorem B25907201 : Blo 1514954 25907201 := bstep (se 2 (by rfl) ⟨9715200, by rfl⟩ : syracuseStep 25907201 = 19430401) B19430401
theorem B3838043 : Blo 1514954 3838043 := bstep (se 1 (by rfl) ⟨2878532, by rfl⟩ : syracuseStep 3838043 = 5757065) B5757065
theorem B8630495 : Blo 1514954 8630495 := bstep (se 1 (by rfl) ⟨6472871, by rfl⟩ : syracuseStep 8630495 = 12945743) B12945743
theorem B5255401 : Blo 1514954 5255401 := bstep (se 2 (by rfl) ⟨1970775, by rfl⟩ : syracuseStep 5255401 = 3941551) B3941551
theorem B3412385 : Blo 1514954 3412385 := bstep (se 2 (by rfl) ⟨1279644, by rfl⟩ : syracuseStep 3412385 = 2559289) B2559289
theorem B2273771 : Blo 1514954 2273771 := bstep (se 1 (by rfl) ⟨1705328, by rfl⟩ : syracuseStep 2273771 = 3410657) B3410657
theorem B10924733 : Blo 1514954 10924733 := bstep (se 3 (by rfl) ⟨2048387, by rfl⟩ : syracuseStep 10924733 = 4096775) B4096775
theorem B2274023 : Blo 1514954 2274023 := bstep (se 1 (by rfl) ⟨1705517, by rfl⟩ : syracuseStep 2274023 = 3411035) B3411035
theorem B2429723 : Blo 1514954 2429723 := bstep (se 1 (by rfl) ⟨1822292, by rfl⟩ : syracuseStep 2429723 = 3644585) B3644585
theorem B3740447 : Blo 1514954 3740447 := bstep (se 1 (by rfl) ⟨2805335, by rfl⟩ : syracuseStep 3740447 = 5610671) B5610671
theorem B3412799 : Blo 1514954 3412799 := bstep (se 1 (by rfl) ⟨2559599, by rfl⟩ : syracuseStep 3412799 = 5119199) B5119199
theorem B11514797 : Blo 1514954 11514797 := bstep (se 3 (by rfl) ⟨2159024, by rfl⟩ : syracuseStep 11514797 = 4318049) B4318049
theorem B11507021 : Blo 1514954 11507021 := bstep (se 3 (by rfl) ⟨2157566, by rfl⟩ : syracuseStep 11507021 = 4315133) B4315133
theorem B3553055 : Blo 1514954 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B7674425 : Blo 1514954 7674425 := bstep (se 2 (by rfl) ⟨2877909, by rfl⟩ : syracuseStep 7674425 = 5755819) B5755819
theorem B25885331 : Blo 1514954 25885331 := bstep (se 1 (by rfl) ⟨19413998, by rfl⟩ : syracuseStep 25885331 = 38827997) B38827997
theorem B7674911 : Blo 1514954 7674911 := bstep (se 1 (by rfl) ⟨5756183, by rfl⟩ : syracuseStep 7674911 = 11512367) B11512367
theorem B4316399 : Blo 1514954 4316399 := bstep (se 1 (by rfl) ⟨3237299, by rfl⟩ : syracuseStep 4316399 = 6474599) B6474599
theorem B36879623 : Blo 1514954 36879623 := bstep (se 1 (by rfl) ⟨27659717, by rfl⟩ : syracuseStep 36879623 = 55319435) B55319435
theorem B4316591 : Blo 1514954 4316591 := bstep (se 1 (by rfl) ⟨3237443, by rfl⟩ : syracuseStep 4316591 = 6474887) B6474887
theorem B1514975 : Blo 1514954 1514975 := bstep (se 1 (by rfl) ⟨1136231, by rfl⟩ : syracuseStep 1514975 = 2272463) B2272463
theorem B1515055 : Blo 1514954 1515055 := bstep (se 1 (by rfl) ⟨1136291, by rfl⟩ : syracuseStep 1515055 = 2272583) B2272583
theorem B1515355 : Blo 1514954 1515355 := bstep (se 1 (by rfl) ⟨1136516, by rfl⟩ : syracuseStep 1515355 = 2273033) B2273033
theorem B1515455 : Blo 1514954 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B1515503 : Blo 1514954 1515503 := bstep (se 1 (by rfl) ⟨1136627, by rfl⟩ : syracuseStep 1515503 = 2273255) B2273255
theorem B1515847 : Blo 1514954 1515847 := bstep (se 1 (by rfl) ⟨1136885, by rfl⟩ : syracuseStep 1515847 = 2273771) B2273771
theorem B7283155 : Blo 1514954 7283155 := bstep (se 1 (by rfl) ⟨5462366, by rfl⟩ : syracuseStep 7283155 = 10924733) B10924733
theorem B1516015 : Blo 1514954 1516015 := bstep (se 1 (by rfl) ⟨1137011, by rfl⟩ : syracuseStep 1516015 = 2274023) B2274023
theorem B7676531 : Blo 1514954 7676531 := bstep (se 1 (by rfl) ⟨5757398, by rfl⟩ : syracuseStep 7676531 = 11514797) B11514797
theorem B1917695 : Blo 1514954 1917695 := bstep (se 1 (by rfl) ⟨1438271, by rfl⟩ : syracuseStep 1917695 = 2876543) B2876543
theorem B11510909 : Blo 1514954 11510909 := bstep (se 3 (by rfl) ⟨2158295, by rfl⟩ : syracuseStep 11510909 = 4316591) B4316591
theorem B2368703 : Blo 1514954 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B8635643 : Blo 1514954 8635643 := bstep (se 1 (by rfl) ⟨6476732, by rfl⟩ : syracuseStep 8635643 = 12953465) B12953465
theorem B5752403 : Blo 1514954 5752403 := bstep (se 1 (by rfl) ⟨4314302, by rfl⟩ : syracuseStep 5752403 = 8628605) B8628605
theorem B3237641 : Blo 1514954 3237641 := bstep (se 2 (by rfl) ⟨1214115, by rfl⟩ : syracuseStep 3237641 = 2428231) B2428231
theorem B2557919 : Blo 1514954 2557919 := bstep (se 1 (by rfl) ⟨1918439, by rfl⟩ : syracuseStep 2557919 = 3836879) B3836879
theorem B5114015 : Blo 1514954 5114015 := bstep (se 1 (by rfl) ⟨3835511, by rfl⟩ : syracuseStep 5114015 = 7671023) B7671023
theorem B2877599 : Blo 1514954 2877599 := bstep (se 1 (by rfl) ⟨2158199, by rfl⟩ : syracuseStep 2877599 = 4316399) B4316399
theorem B1919143 : Blo 1514954 1919143 := bstep (se 1 (by rfl) ⟨1439357, by rfl⟩ : syracuseStep 1919143 = 2878715) B2878715
theorem B24586415 : Blo 1514954 24586415 := bstep (se 1 (by rfl) ⟨18439811, by rfl⟩ : syracuseStep 24586415 = 36879623) B36879623
theorem B5753207 : Blo 1514954 5753207 := bstep (se 1 (by rfl) ⟨4314905, by rfl⟩ : syracuseStep 5753207 = 8629811) B8629811
theorem B8636827 : Blo 1514954 8636827 := bstep (se 1 (by rfl) ⟨6477620, by rfl⟩ : syracuseStep 8636827 = 12955241) B12955241
theorem B1706395 : Blo 1514954 1706395 := bstep (se 1 (by rfl) ⟨1279796, by rfl⟩ : syracuseStep 1706395 = 2559593) B2559593
theorem B1706431 : Blo 1514954 1706431 := bstep (se 1 (by rfl) ⟨1279823, by rfl⟩ : syracuseStep 1706431 = 2559647) B2559647
theorem B4155881 : Blo 1514954 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B17271467 : Blo 1514954 17271467 := bstep (se 1 (by rfl) ⟨12953600, by rfl⟩ : syracuseStep 17271467 = 25907201) B25907201
theorem B2558695 : Blo 1514954 2558695 := bstep (se 1 (by rfl) ⟨1919021, by rfl⟩ : syracuseStep 2558695 = 3838043) B3838043
theorem B13134575 : Blo 1514954 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B7670537 : Blo 1514954 7670537 := bstep (se 2 (by rfl) ⟨2876451, by rfl⟩ : syracuseStep 7670537 = 5752903) B5752903
theorem B2558729 : Blo 1514954 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B5753663 : Blo 1514954 5753663 := bstep (se 1 (by rfl) ⟨4315247, by rfl⟩ : syracuseStep 5753663 = 8630495) B8630495
theorem B7007201 : Blo 1514954 7007201 := bstep (se 2 (by rfl) ⟨2627700, by rfl⟩ : syracuseStep 7007201 = 5255401) B5255401
theorem B2493631 : Blo 1514954 2493631 := bstep (se 1 (by rfl) ⟨1870223, by rfl⟩ : syracuseStep 2493631 = 3740447) B3740447
theorem B4992319 : Blo 1514954 4992319 := bstep (se 1 (by rfl) ⟨3744239, by rfl⟩ : syracuseStep 4992319 = 7488479) B7488479
theorem B7671347 : Blo 1514954 7671347 := bstep (se 1 (by rfl) ⟨5753510, by rfl⟩ : syracuseStep 7671347 = 11507021) B11507021
theorem B27652063 : Blo 1514954 27652063 := bstep (se 1 (by rfl) ⟨20739047, by rfl⟩ : syracuseStep 27652063 = 41478095) B41478095
theorem B5116283 : Blo 1514954 5116283 := bstep (se 1 (by rfl) ⟨3837212, by rfl⟩ : syracuseStep 5116283 = 7674425) B7674425
theorem B17256887 : Blo 1514954 17256887 := bstep (se 1 (by rfl) ⟨12942665, by rfl⟩ : syracuseStep 17256887 = 25885331) B25885331
theorem B5116607 : Blo 1514954 5116607 := bstep (se 1 (by rfl) ⟨3837455, by rfl⟩ : syracuseStep 5116607 = 7674911) B7674911
theorem B5756093 : Blo 1514954 5756093 := bstep (se 3 (by rfl) ⟨1079267, by rfl⟩ : syracuseStep 5756093 = 2158535) B2158535
theorem B4855295 : Blo 1514954 4855295 := bstep (se 1 (by rfl) ⟨3641471, by rfl⟩ : syracuseStep 4855295 = 7282943) B7282943
theorem B19699199 : Blo 1514954 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B2274923 : Blo 1514954 2274923 := bstep (se 1 (by rfl) ⟨1706192, by rfl⟩ : syracuseStep 2274923 = 3412385) B3412385
theorem B3839663 : Blo 1514954 3839663 := bstep (se 1 (by rfl) ⟨2879747, by rfl⟩ : syracuseStep 3839663 = 5759495) B5759495
theorem B4495123 : Blo 1514954 4495123 := bstep (se 1 (by rfl) ⟨3371342, by rfl⟩ : syracuseStep 4495123 = 6742685) B6742685
theorem B2275199 : Blo 1514954 2275199 := bstep (se 1 (by rfl) ⟨1706399, by rfl⟩ : syracuseStep 2275199 = 3412799) B3412799
theorem B14571571 : Blo 1514954 14571571 := bstep (se 1 (by rfl) ⟨10928678, by rfl⟩ : syracuseStep 14571571 = 21857357) B21857357
theorem B5118227 : Blo 1514954 5118227 := bstep (se 1 (by rfl) ⟨3838670, by rfl⟩ : syracuseStep 5118227 = 7677341) B7677341
theorem B5118335 : Blo 1514954 5118335 := bstep (se 1 (by rfl) ⟨3838751, by rfl⟩ : syracuseStep 5118335 = 7677503) B7677503
theorem B3693161 : Blo 1514954 3693161 := bstep (se 2 (by rfl) ⟨1384935, by rfl⟩ : syracuseStep 3693161 = 2769871) B2769871
theorem B165927689 : Blo 1514954 165927689 := bstep (se 2 (by rfl) ⟨62222883, by rfl⟩ : syracuseStep 165927689 = 124445767) B124445767
theorem B13835407 : Blo 1514954 13835407 := bstep (se 1 (by rfl) ⟨10376555, by rfl⟩ : syracuseStep 13835407 = 20753111) B20753111
theorem B19430765 : Blo 1514954 19430765 := bstep (se 3 (by rfl) ⟨3643268, by rfl⟩ : syracuseStep 19430765 = 7286537) B7286537
theorem B19422611 : Blo 1514954 19422611 := bstep (se 1 (by rfl) ⟨14566958, by rfl⟩ : syracuseStep 19422611 = 29133917) B29133917
theorem B6479261 : Blo 1514954 6479261 := bstep (se 3 (by rfl) ⟨1214861, by rfl⟩ : syracuseStep 6479261 = 2429723) B2429723
theorem B1514991 : Blo 1514954 1514991 := bstep (se 1 (by rfl) ⟨1136243, by rfl⟩ : syracuseStep 1514991 = 2272487) B2272487
theorem B1515291 : Blo 1514954 1515291 := bstep (se 1 (by rfl) ⟨1136468, by rfl⟩ : syracuseStep 1515291 = 2272937) B2272937
theorem B10928105 : Blo 1514954 10928105 := bstep (se 2 (by rfl) ⟨4098039, by rfl⟩ : syracuseStep 10928105 = 8196079) B8196079
theorem B6316541 : Blo 1514954 6316541 := bstep (se 3 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 6316541 = 2368703) B2368703
theorem B3236863 : Blo 1514954 3236863 := bstep (se 1 (by rfl) ⟨2427647, by rfl⟩ : syracuseStep 3236863 = 4855295) B4855295
theorem B13132799 : Blo 1514954 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B3834935 : Blo 1514954 3834935 := bstep (se 1 (by rfl) ⟨2876201, by rfl⟩ : syracuseStep 3834935 = 5752403) B5752403
theorem B1516615 : Blo 1514954 1516615 := bstep (se 1 (by rfl) ⟨1137461, by rfl⟩ : syracuseStep 1516615 = 2274923) B2274923
theorem B1516799 : Blo 1514954 1516799 := bstep (se 1 (by rfl) ⟨1137599, by rfl⟩ : syracuseStep 1516799 = 2275199) B2275199
theorem B1705279 : Blo 1514954 1705279 := bstep (se 1 (by rfl) ⟨1278959, by rfl⟩ : syracuseStep 1705279 = 2557919) B2557919
theorem B3409343 : Blo 1514954 3409343 := bstep (se 1 (by rfl) ⟨2557007, by rfl⟩ : syracuseStep 3409343 = 5114015) B5114015
theorem B1918399 : Blo 1514954 1918399 := bstep (se 1 (by rfl) ⟨1438799, by rfl⟩ : syracuseStep 1918399 = 2877599) B2877599
theorem B3835471 : Blo 1514954 3835471 := bstep (se 1 (by rfl) ⟨2876603, by rfl⟩ : syracuseStep 3835471 = 5753207) B5753207
theorem B26625701 : Blo 1514954 26625701 := bstep (se 4 (by rfl) ⟨2496159, by rfl⟩ : syracuseStep 26625701 = 4992319) B4992319
theorem B110618459 : Blo 1514954 110618459 := bstep (se 1 (by rfl) ⟨82963844, by rfl⟩ : syracuseStep 110618459 = 165927689) B165927689
theorem B5113691 : Blo 1514954 5113691 := bstep (se 1 (by rfl) ⟨3835268, by rfl⟩ : syracuseStep 5113691 = 7670537) B7670537
theorem B1705819 : Blo 1514954 1705819 := bstep (se 1 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 1705819 = 2558729) B2558729
theorem B3835775 : Blo 1514954 3835775 := bstep (se 1 (by rfl) ⟨2876831, by rfl⟩ : syracuseStep 3835775 = 5753663) B5753663
theorem B4671467 : Blo 1514954 4671467 := bstep (se 1 (by rfl) ⟨3503600, by rfl⟩ : syracuseStep 4671467 = 7007201) B7007201
theorem B5113853 : Blo 1514954 5113853 := bstep (se 3 (by rfl) ⟨958847, by rfl⟩ : syracuseStep 5113853 = 1917695) B1917695
theorem B12953843 : Blo 1514954 12953843 := bstep (se 1 (by rfl) ⟨9715382, by rfl⟩ : syracuseStep 12953843 = 19430765) B19430765
theorem B4319507 : Blo 1514954 4319507 := bstep (se 1 (by rfl) ⟨3239630, by rfl⟩ : syracuseStep 4319507 = 6479261) B6479261
theorem B5114231 : Blo 1514954 5114231 := bstep (se 1 (by rfl) ⟨3835673, by rfl⟩ : syracuseStep 5114231 = 7671347) B7671347
theorem B7285403 : Blo 1514954 7285403 := bstep (se 1 (by rfl) ⟨5464052, by rfl⟩ : syracuseStep 7285403 = 10928105) B10928105
theorem B2558857 : Blo 1514954 2558857 := bstep (se 2 (by rfl) ⟨959571, by rfl⟩ : syracuseStep 2558857 = 1919143) B1919143
theorem B3410855 : Blo 1514954 3410855 := bstep (se 1 (by rfl) ⟨2558141, by rfl⟩ : syracuseStep 3410855 = 5116283) B5116283
theorem B11504591 : Blo 1514954 11504591 := bstep (se 1 (by rfl) ⟨8628443, by rfl⟩ : syracuseStep 11504591 = 17256887) B17256887
theorem B3411071 : Blo 1514954 3411071 := bstep (se 1 (by rfl) ⟨2558303, by rfl⟩ : syracuseStep 3411071 = 5116607) B5116607
theorem B9710873 : Blo 1514954 9710873 := bstep (se 2 (by rfl) ⟨3641577, by rfl⟩ : syracuseStep 9710873 = 7283155) B7283155
theorem B3837395 : Blo 1514954 3837395 := bstep (se 1 (by rfl) ⟨2878046, by rfl⟩ : syracuseStep 3837395 = 5756093) B5756093
theorem B3411593 : Blo 1514954 3411593 := bstep (se 2 (by rfl) ⟨1279347, by rfl⟩ : syracuseStep 3411593 = 2558695) B2558695
theorem B13299365 : Blo 1514954 13299365 := bstep (se 4 (by rfl) ⟨1246815, by rfl⟩ : syracuseStep 13299365 = 2493631) B2493631
theorem B2559775 : Blo 1514954 2559775 := bstep (se 1 (by rfl) ⟨1919831, by rfl⟩ : syracuseStep 2559775 = 3839663) B3839663
theorem B2158427 : Blo 1514954 2158427 := bstep (se 1 (by rfl) ⟨1618820, by rfl⟩ : syracuseStep 2158427 = 3237641) B3237641
theorem B3412151 : Blo 1514954 3412151 := bstep (se 1 (by rfl) ⟨2559113, by rfl⟩ : syracuseStep 3412151 = 5118227) B5118227
theorem B3412223 : Blo 1514954 3412223 := bstep (se 1 (by rfl) ⟨2559167, by rfl⟩ : syracuseStep 3412223 = 5118335) B5118335
theorem B2462107 : Blo 1514954 2462107 := bstep (se 1 (by rfl) ⟨1846580, by rfl⟩ : syracuseStep 2462107 = 3693161) B3693161
theorem B11514311 : Blo 1514954 11514311 := bstep (se 1 (by rfl) ⟨8635733, by rfl⟩ : syracuseStep 11514311 = 17271467) B17271467
theorem B12948407 : Blo 1514954 12948407 := bstep (se 1 (by rfl) ⟨9711305, by rfl⟩ : syracuseStep 12948407 = 19422611) B19422611
theorem B5993497 : Blo 1514954 5993497 := bstep (se 2 (by rfl) ⟨2247561, by rfl⟩ : syracuseStep 5993497 = 4495123) B4495123
theorem B36869417 : Blo 1514954 36869417 := bstep (se 2 (by rfl) ⟨13826031, by rfl⟩ : syracuseStep 36869417 = 27652063) B27652063
theorem B19428761 : Blo 1514954 19428761 := bstep (se 2 (by rfl) ⟨7285785, by rfl⟩ : syracuseStep 19428761 = 14571571) B14571571
theorem B5117687 : Blo 1514954 5117687 := bstep (se 1 (by rfl) ⟨3838265, by rfl⟩ : syracuseStep 5117687 = 7676531) B7676531
theorem B11515769 : Blo 1514954 11515769 := bstep (se 2 (by rfl) ⟨4318413, by rfl⟩ : syracuseStep 11515769 = 8636827) B8636827
theorem B2275193 : Blo 1514954 2275193 := bstep (se 2 (by rfl) ⟨853197, by rfl⟩ : syracuseStep 2275193 = 1706395) B1706395
theorem B2275241 : Blo 1514954 2275241 := bstep (se 2 (by rfl) ⟨853215, by rfl⟩ : syracuseStep 2275241 = 1706431) B1706431
theorem B7673939 : Blo 1514954 7673939 := bstep (se 1 (by rfl) ⟨5755454, by rfl⟩ : syracuseStep 7673939 = 11510909) B11510909
theorem B5757095 : Blo 1514954 5757095 := bstep (se 1 (by rfl) ⟨4317821, by rfl⟩ : syracuseStep 5757095 = 8635643) B8635643
theorem B11082349 : Blo 1514954 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B16390943 : Blo 1514954 16390943 := bstep (se 1 (by rfl) ⟨12293207, by rfl⟩ : syracuseStep 16390943 = 24586415) B24586415
theorem B18447209 : Blo 1514954 18447209 := bstep (se 2 (by rfl) ⟨6917703, by rfl⟩ : syracuseStep 18447209 = 13835407) B13835407
theorem B8756383 : Blo 1514954 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B31965317 : Blo 1514954 31965317 := bstep (se 4 (by rfl) ⟨2996748, by rfl⟩ : syracuseStep 31965317 = 5993497) B5993497
theorem B7676207 : Blo 1514954 7676207 := bstep (se 1 (by rfl) ⟨5757155, by rfl⟩ : syracuseStep 7676207 = 11514311) B11514311
theorem B4211027 : Blo 1514954 4211027 := bstep (se 1 (by rfl) ⟨3158270, by rfl⟩ : syracuseStep 4211027 = 6316541) B6316541
theorem B2556623 : Blo 1514954 2556623 := bstep (se 1 (by rfl) ⟨1917467, by rfl⟩ : syracuseStep 2556623 = 3834935) B3834935
theorem B11518685 : Blo 1514954 11518685 := bstep (se 3 (by rfl) ⟨2159753, by rfl⟩ : syracuseStep 11518685 = 4319507) B4319507
theorem B12952507 : Blo 1514954 12952507 := bstep (se 1 (by rfl) ⟨9714380, by rfl⟩ : syracuseStep 12952507 = 19428761) B19428761
theorem B3409127 : Blo 1514954 3409127 := bstep (se 1 (by rfl) ⟨2556845, by rfl⟩ : syracuseStep 3409127 = 5113691) B5113691
theorem B73745639 : Blo 1514954 73745639 := bstep (se 1 (by rfl) ⟨55309229, by rfl⟩ : syracuseStep 73745639 = 110618459) B110618459
theorem B7677179 : Blo 1514954 7677179 := bstep (se 1 (by rfl) ⟨5757884, by rfl⟩ : syracuseStep 7677179 = 11515769) B11515769
theorem B1516795 : Blo 1514954 1516795 := bstep (se 1 (by rfl) ⟨1137596, by rfl⟩ : syracuseStep 1516795 = 2275193) B2275193
theorem B2557183 : Blo 1514954 2557183 := bstep (se 1 (by rfl) ⟨1917887, by rfl⟩ : syracuseStep 2557183 = 3835775) B3835775
theorem B1516827 : Blo 1514954 1516827 := bstep (se 1 (by rfl) ⟨1137620, by rfl⟩ : syracuseStep 1516827 = 2275241) B2275241
theorem B3114311 : Blo 1514954 3114311 := bstep (se 1 (by rfl) ⟨2335733, by rfl⟩ : syracuseStep 3114311 = 4671467) B4671467
theorem B3409235 : Blo 1514954 3409235 := bstep (se 1 (by rfl) ⟨2556926, by rfl⟩ : syracuseStep 3409235 = 5113853) B5113853
theorem B8635895 : Blo 1514954 8635895 := bstep (se 1 (by rfl) ⟨6476921, by rfl⟩ : syracuseStep 8635895 = 12953843) B12953843
theorem B11675177 : Blo 1514954 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B3409487 : Blo 1514954 3409487 := bstep (se 1 (by rfl) ⟨2557115, by rfl⟩ : syracuseStep 3409487 = 5114231) B5114231
theorem B35464973 : Blo 1514954 35464973 := bstep (se 3 (by rfl) ⟨6649682, by rfl⟩ : syracuseStep 35464973 = 13299365) B13299365
theorem B12298139 : Blo 1514954 12298139 := bstep (se 1 (by rfl) ⟨9223604, by rfl⟩ : syracuseStep 12298139 = 18447209) B18447209
theorem B2557865 : Blo 1514954 2557865 := bstep (se 2 (by rfl) ⟨959199, by rfl⟩ : syracuseStep 2557865 = 1918399) B1918399
theorem B7669727 : Blo 1514954 7669727 := bstep (se 1 (by rfl) ⟨5752295, by rfl⟩ : syracuseStep 7669727 = 11504591) B11504591
theorem B5113961 : Blo 1514954 5113961 := bstep (se 2 (by rfl) ⟨1917735, by rfl⟩ : syracuseStep 5113961 = 3835471) B3835471
theorem B6473915 : Blo 1514954 6473915 := bstep (se 1 (by rfl) ⟨4855436, by rfl⟩ : syracuseStep 6473915 = 9710873) B9710873
theorem B2558263 : Blo 1514954 2558263 := bstep (se 1 (by rfl) ⟨1918697, by rfl⟩ : syracuseStep 2558263 = 3837395) B3837395
theorem B24579611 : Blo 1514954 24579611 := bstep (se 1 (by rfl) ⟨18434708, by rfl⟩ : syracuseStep 24579611 = 36869417) B36869417
theorem B2272895 : Blo 1514954 2272895 := bstep (se 1 (by rfl) ⟨1704671, by rfl⟩ : syracuseStep 2272895 = 3409343) B3409343
theorem B3411791 : Blo 1514954 3411791 := bstep (se 1 (by rfl) ⟨2558843, by rfl⟩ : syracuseStep 3411791 = 5117687) B5117687
theorem B3411809 : Blo 1514954 3411809 := bstep (se 2 (by rfl) ⟨1279428, by rfl⟩ : syracuseStep 3411809 = 2558857) B2558857
theorem B5115959 : Blo 1514954 5115959 := bstep (se 1 (by rfl) ⟨3836969, by rfl⟩ : syracuseStep 5115959 = 7673939) B7673939
theorem B3838063 : Blo 1514954 3838063 := bstep (se 1 (by rfl) ⟨2878547, by rfl⟩ : syracuseStep 3838063 = 5757095) B5757095
theorem B2273705 : Blo 1514954 2273705 := bstep (se 2 (by rfl) ⟨852639, by rfl⟩ : syracuseStep 2273705 = 1705279) B1705279
theorem B2273903 : Blo 1514954 2273903 := bstep (se 1 (by rfl) ⟨1705427, by rfl⟩ : syracuseStep 2273903 = 3410855) B3410855
theorem B2274047 : Blo 1514954 2274047 := bstep (se 1 (by rfl) ⟨1705535, by rfl⟩ : syracuseStep 2274047 = 3411071) B3411071
theorem B5755805 : Blo 1514954 5755805 := bstep (se 3 (by rfl) ⟨1079213, by rfl⟩ : syracuseStep 5755805 = 2158427) B2158427
theorem B3413033 : Blo 1514954 3413033 := bstep (se 2 (by rfl) ⟨1279887, by rfl⟩ : syracuseStep 3413033 = 2559775) B2559775
theorem B2274395 : Blo 1514954 2274395 := bstep (se 1 (by rfl) ⟨1705796, by rfl⟩ : syracuseStep 2274395 = 3411593) B3411593
theorem B2274425 : Blo 1514954 2274425 := bstep (se 2 (by rfl) ⟨852909, by rfl⟩ : syracuseStep 2274425 = 1705819) B1705819
theorem B2274767 : Blo 1514954 2274767 := bstep (se 1 (by rfl) ⟨1706075, by rfl⟩ : syracuseStep 2274767 = 3412151) B3412151
theorem B2274815 : Blo 1514954 2274815 := bstep (se 1 (by rfl) ⟨1706111, by rfl⟩ : syracuseStep 2274815 = 3412223) B3412223
theorem B3282809 : Blo 1514954 3282809 := bstep (se 2 (by rfl) ⟨1231053, by rfl⟩ : syracuseStep 3282809 = 2462107) B2462107
theorem B8632271 : Blo 1514954 8632271 := bstep (se 1 (by rfl) ⟨6474203, by rfl⟩ : syracuseStep 8632271 = 12948407) B12948407
theorem B8755199 : Blo 1514954 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B14776465 : Blo 1514954 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B17750467 : Blo 1514954 17750467 := bstep (se 1 (by rfl) ⟨13312850, by rfl⟩ : syracuseStep 17750467 = 26625701) B26625701
theorem B4315817 : Blo 1514954 4315817 := bstep (se 2 (by rfl) ⟨1618431, by rfl⟩ : syracuseStep 4315817 = 3236863) B3236863
theorem B4856935 : Blo 1514954 4856935 := bstep (se 1 (by rfl) ⟨3642701, by rfl⟩ : syracuseStep 4856935 = 7285403) B7285403
theorem B10927295 : Blo 1514954 10927295 := bstep (se 1 (by rfl) ⟨8195471, by rfl⟩ : syracuseStep 10927295 = 16390943) B16390943
theorem B19701953 : Blo 1514954 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B1515803 : Blo 1514954 1515803 := bstep (se 1 (by rfl) ⟨1136852, by rfl⟩ : syracuseStep 1515803 = 2273705) B2273705
theorem B1515935 : Blo 1514954 1515935 := bstep (se 1 (by rfl) ⟨1136951, by rfl⟩ : syracuseStep 1515935 = 2273903) B2273903
theorem B1704415 : Blo 1514954 1704415 := bstep (se 1 (by rfl) ⟨1278311, by rfl⟩ : syracuseStep 1704415 = 2556623) B2556623
theorem B1516031 : Blo 1514954 1516031 := bstep (se 1 (by rfl) ⟨1137023, by rfl⟩ : syracuseStep 1516031 = 2274047) B2274047
theorem B1516263 : Blo 1514954 1516263 := bstep (se 1 (by rfl) ⟨1137197, by rfl⟩ : syracuseStep 1516263 = 2274395) B2274395
theorem B1516283 : Blo 1514954 1516283 := bstep (se 1 (by rfl) ⟨1137212, by rfl⟩ : syracuseStep 1516283 = 2274425) B2274425
theorem B1516511 : Blo 1514954 1516511 := bstep (se 1 (by rfl) ⟨1137383, by rfl⟩ : syracuseStep 1516511 = 2274767) B2274767
theorem B1516543 : Blo 1514954 1516543 := bstep (se 1 (by rfl) ⟨1137407, by rfl⟩ : syracuseStep 1516543 = 2274815) B2274815
theorem B7783451 : Blo 1514954 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B17270009 : Blo 1514954 17270009 := bstep (se 2 (by rfl) ⟨6476253, by rfl⟩ : syracuseStep 17270009 = 12952507) B12952507
theorem B1705243 : Blo 1514954 1705243 := bstep (se 1 (by rfl) ⟨1278932, by rfl⟩ : syracuseStep 1705243 = 2557865) B2557865
theorem B5113151 : Blo 1514954 5113151 := bstep (se 1 (by rfl) ⟨3834863, by rfl⟩ : syracuseStep 5113151 = 7669727) B7669727
theorem B3409307 : Blo 1514954 3409307 := bstep (se 1 (by rfl) ⟨2556980, by rfl⟩ : syracuseStep 3409307 = 5113961) B5113961
theorem B3409577 : Blo 1514954 3409577 := bstep (se 2 (by rfl) ⟨1278591, by rfl⟩ : syracuseStep 3409577 = 2557183) B2557183
theorem B2877211 : Blo 1514954 2877211 := bstep (se 1 (by rfl) ⟨2157908, by rfl⟩ : syracuseStep 2877211 = 4315817) B4315817
theorem B7284863 : Blo 1514954 7284863 := bstep (se 1 (by rfl) ⟨5463647, by rfl⟩ : syracuseStep 7284863 = 10927295) B10927295
theorem B94669157 : Blo 1514954 94669157 := bstep (se 4 (by rfl) ⟨8875233, by rfl⟩ : syracuseStep 94669157 = 17750467) B17750467
theorem B16386407 : Blo 1514954 16386407 := bstep (se 1 (by rfl) ⟨12289805, by rfl⟩ : syracuseStep 16386407 = 24579611) B24579611
theorem B3410639 : Blo 1514954 3410639 := bstep (se 1 (by rfl) ⟨2557979, by rfl⟩ : syracuseStep 3410639 = 5115959) B5115959
theorem B3411017 : Blo 1514954 3411017 := bstep (se 2 (by rfl) ⟨1279131, by rfl⟩ : syracuseStep 3411017 = 2558263) B2558263
theorem B7679123 : Blo 1514954 7679123 := bstep (se 1 (by rfl) ⟨5759342, by rfl⟩ : syracuseStep 7679123 = 11518685) B11518685
theorem B3837203 : Blo 1514954 3837203 := bstep (se 1 (by rfl) ⟨2877902, by rfl⟩ : syracuseStep 3837203 = 5755805) B5755805
theorem B2272751 : Blo 1514954 2272751 := bstep (se 1 (by rfl) ⟨1704563, by rfl⟩ : syracuseStep 2272751 = 3409127) B3409127
theorem B49163759 : Blo 1514954 49163759 := bstep (se 1 (by rfl) ⟨36872819, by rfl⟩ : syracuseStep 49163759 = 73745639) B73745639
theorem B2272823 : Blo 1514954 2272823 := bstep (se 1 (by rfl) ⟨1704617, by rfl⟩ : syracuseStep 2272823 = 3409235) B3409235
theorem B2272991 : Blo 1514954 2272991 := bstep (se 1 (by rfl) ⟨1704743, by rfl⟩ : syracuseStep 2272991 = 3409487) B3409487
theorem B5754847 : Blo 1514954 5754847 := bstep (se 1 (by rfl) ⟨4316135, by rfl⟩ : syracuseStep 5754847 = 8632271) B8632271
theorem B5836799 : Blo 1514954 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B340963381 : Blo 1514954 340963381 := bstep (se 5 (by rfl) ⟨15982658, by rfl⟩ : syracuseStep 340963381 = 31965317) B31965317
theorem B6475913 : Blo 1514954 6475913 := bstep (se 2 (by rfl) ⟨2428467, by rfl⟩ : syracuseStep 6475913 = 4856935) B4856935
theorem B94573261 : Blo 1514954 94573261 := bstep (se 3 (by rfl) ⟨17732486, by rfl⟩ : syracuseStep 94573261 = 35464973) B35464973
theorem B8754157 : Blo 1514954 8754157 := bstep (se 3 (by rfl) ⟨1641404, by rfl⟩ : syracuseStep 8754157 = 3282809) B3282809
theorem B2274527 : Blo 1514954 2274527 := bstep (se 1 (by rfl) ⟨1705895, by rfl⟩ : syracuseStep 2274527 = 3411791) B3411791
theorem B2274539 : Blo 1514954 2274539 := bstep (se 1 (by rfl) ⟨1705904, by rfl⟩ : syracuseStep 2274539 = 3411809) B3411809
theorem B5117417 : Blo 1514954 5117417 := bstep (se 2 (by rfl) ⟨1919031, by rfl⟩ : syracuseStep 5117417 = 3838063) B3838063
theorem B5117471 : Blo 1514954 5117471 := bstep (se 1 (by rfl) ⟨3838103, by rfl⟩ : syracuseStep 5117471 = 7676207) B7676207
theorem B2807351 : Blo 1514954 2807351 := bstep (se 1 (by rfl) ⟨2105513, by rfl⟩ : syracuseStep 2807351 = 4211027) B4211027
theorem B2275355 : Blo 1514954 2275355 := bstep (se 1 (by rfl) ⟨1706516, by rfl⟩ : syracuseStep 2275355 = 3413033) B3413033
theorem B5118119 : Blo 1514954 5118119 := bstep (se 1 (by rfl) ⟨3838589, by rfl⟩ : syracuseStep 5118119 = 7677179) B7677179
theorem B8304829 : Blo 1514954 8304829 := bstep (se 3 (by rfl) ⟨1557155, by rfl⟩ : syracuseStep 8304829 = 3114311) B3114311
theorem B5757263 : Blo 1514954 5757263 := bstep (se 1 (by rfl) ⟨4317947, by rfl⟩ : syracuseStep 5757263 = 8635895) B8635895
theorem B8198759 : Blo 1514954 8198759 := bstep (se 1 (by rfl) ⟨6149069, by rfl⟩ : syracuseStep 8198759 = 12298139) B12298139
theorem B4315943 : Blo 1514954 4315943 := bstep (se 1 (by rfl) ⟨3236957, by rfl⟩ : syracuseStep 4315943 = 6473915) B6473915
theorem B1515263 : Blo 1514954 1515263 := bstep (se 1 (by rfl) ⟨1136447, by rfl⟩ : syracuseStep 1515263 = 2272895) B2272895
theorem B4317275 : Blo 1514954 4317275 := bstep (se 1 (by rfl) ⟨3237956, by rfl⟩ : syracuseStep 4317275 = 6475913) B6475913
theorem B1516351 : Blo 1514954 1516351 := bstep (se 1 (by rfl) ⟨1137263, by rfl⟩ : syracuseStep 1516351 = 2274527) B2274527
theorem B1516359 : Blo 1514954 1516359 := bstep (se 1 (by rfl) ⟨1137269, by rfl⟩ : syracuseStep 1516359 = 2274539) B2274539
theorem B3408767 : Blo 1514954 3408767 := bstep (se 1 (by rfl) ⟨2556575, by rfl⟩ : syracuseStep 3408767 = 5113151) B5113151
theorem B1516903 : Blo 1514954 1516903 := bstep (se 1 (by rfl) ⟨1137677, by rfl⟩ : syracuseStep 1516903 = 2275355) B2275355
theorem B63112771 : Blo 1514954 63112771 := bstep (se 1 (by rfl) ⟨47334578, by rfl⟩ : syracuseStep 63112771 = 94669157) B94669157
theorem B2877295 : Blo 1514954 2877295 := bstep (se 1 (by rfl) ⟨2157971, by rfl⟩ : syracuseStep 2877295 = 4315943) B4315943
theorem B2558135 : Blo 1514954 2558135 := bstep (se 1 (by rfl) ⟨1918601, by rfl⟩ : syracuseStep 2558135 = 3837203) B3837203
theorem B3836281 : Blo 1514954 3836281 := bstep (se 2 (by rfl) ⟨1438605, by rfl⟩ : syracuseStep 3836281 = 2877211) B2877211
theorem B454617841 : Blo 1514954 454617841 := bstep (se 2 (by rfl) ⟨170481690, by rfl⟩ : syracuseStep 454617841 = 340963381) B340963381
theorem B13134635 : Blo 1514954 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B19426301 : Blo 1514954 19426301 := bstep (se 3 (by rfl) ⟨3642431, by rfl⟩ : syracuseStep 19426301 = 7284863) B7284863
theorem B2272553 : Blo 1514954 2272553 := bstep (se 2 (by rfl) ⟨852207, by rfl⟩ : syracuseStep 2272553 = 1704415) B1704415
theorem B5188967 : Blo 1514954 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B11513339 : Blo 1514954 11513339 := bstep (se 1 (by rfl) ⟨8635004, by rfl⟩ : syracuseStep 11513339 = 17270009) B17270009
theorem B2272871 : Blo 1514954 2272871 := bstep (se 1 (by rfl) ⟨1704653, by rfl⟩ : syracuseStep 2272871 = 3409307) B3409307
theorem B3411611 : Blo 1514954 3411611 := bstep (se 1 (by rfl) ⟨2558708, by rfl⟩ : syracuseStep 3411611 = 5117417) B5117417
theorem B3411647 : Blo 1514954 3411647 := bstep (se 1 (by rfl) ⟨2558735, by rfl⟩ : syracuseStep 3411647 = 5117471) B5117471
theorem B1871567 : Blo 1514954 1871567 := bstep (se 1 (by rfl) ⟨1403675, by rfl⟩ : syracuseStep 1871567 = 2807351) B2807351
theorem B2273051 : Blo 1514954 2273051 := bstep (se 1 (by rfl) ⟨1704788, by rfl⟩ : syracuseStep 2273051 = 3409577) B3409577
theorem B3412079 : Blo 1514954 3412079 := bstep (se 1 (by rfl) ⟨2559059, by rfl⟩ : syracuseStep 3412079 = 5118119) B5118119
theorem B3838175 : Blo 1514954 3838175 := bstep (se 1 (by rfl) ⟨2878631, by rfl⟩ : syracuseStep 3838175 = 5757263) B5757263
theorem B10924271 : Blo 1514954 10924271 := bstep (se 1 (by rfl) ⟨8193203, by rfl⟩ : syracuseStep 10924271 = 16386407) B16386407
theorem B2273657 : Blo 1514954 2273657 := bstep (se 2 (by rfl) ⟨852621, by rfl⟩ : syracuseStep 2273657 = 1705243) B1705243
theorem B2273759 : Blo 1514954 2273759 := bstep (se 1 (by rfl) ⟨1705319, by rfl⟩ : syracuseStep 2273759 = 3410639) B3410639
theorem B2274011 : Blo 1514954 2274011 := bstep (se 1 (by rfl) ⟨1705508, by rfl⟩ : syracuseStep 2274011 = 3411017) B3411017
theorem B7673129 : Blo 1514954 7673129 := bstep (se 2 (by rfl) ⟨2877423, by rfl⟩ : syracuseStep 7673129 = 5754847) B5754847
theorem B126097681 : Blo 1514954 126097681 := bstep (se 2 (by rfl) ⟨47286630, by rfl⟩ : syracuseStep 126097681 = 94573261) B94573261
theorem B44292421 : Blo 1514954 44292421 := bstep (se 4 (by rfl) ⟨4152414, by rfl⟩ : syracuseStep 44292421 = 8304829) B8304829
theorem B11672209 : Blo 1514954 11672209 := bstep (se 2 (by rfl) ⟨4377078, by rfl⟩ : syracuseStep 11672209 = 8754157) B8754157
theorem B3891199 : Blo 1514954 3891199 := bstep (se 1 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 3891199 = 5836799) B5836799
theorem B21863357 : Blo 1514954 21863357 := bstep (se 3 (by rfl) ⟨4099379, by rfl⟩ : syracuseStep 21863357 = 8198759) B8198759
theorem B5119415 : Blo 1514954 5119415 := bstep (se 1 (by rfl) ⟨3839561, by rfl⟩ : syracuseStep 5119415 = 7679123) B7679123
theorem B1515167 : Blo 1514954 1515167 := bstep (se 1 (by rfl) ⟨1136375, by rfl⟩ : syracuseStep 1515167 = 2272751) B2272751
theorem B32775839 : Blo 1514954 32775839 := bstep (se 1 (by rfl) ⟨24581879, by rfl⟩ : syracuseStep 32775839 = 49163759) B49163759
theorem B1515215 : Blo 1514954 1515215 := bstep (se 1 (by rfl) ⟨1136411, by rfl⟩ : syracuseStep 1515215 = 2272823) B2272823
theorem B1515327 : Blo 1514954 1515327 := bstep (se 1 (by rfl) ⟨1136495, by rfl⟩ : syracuseStep 1515327 = 2272991) B2272991
theorem B7282847 : Blo 1514954 7282847 := bstep (se 1 (by rfl) ⟨5462135, by rfl⟩ : syracuseStep 7282847 = 10924271) B10924271
theorem B1515771 : Blo 1514954 1515771 := bstep (se 1 (by rfl) ⟨1136828, by rfl⟩ : syracuseStep 1515771 = 2273657) B2273657
theorem B1515839 : Blo 1514954 1515839 := bstep (se 1 (by rfl) ⟨1136879, by rfl⟩ : syracuseStep 1515839 = 2273759) B2273759
theorem B59056561 : Blo 1514954 59056561 := bstep (se 2 (by rfl) ⟨22146210, by rfl⟩ : syracuseStep 59056561 = 44292421) B44292421
theorem B1516007 : Blo 1514954 1516007 := bstep (se 1 (by rfl) ⟨1137005, by rfl⟩ : syracuseStep 1516007 = 2274011) B2274011
theorem B1705423 : Blo 1514954 1705423 := bstep (se 1 (by rfl) ⟨1279067, by rfl⟩ : syracuseStep 1705423 = 2558135) B2558135
theorem B14575571 : Blo 1514954 14575571 := bstep (se 1 (by rfl) ⟨10931678, by rfl⟩ : syracuseStep 14575571 = 21863357) B21863357
theorem B84150361 : Blo 1514954 84150361 := bstep (se 2 (by rfl) ⟨31556385, by rfl⟩ : syracuseStep 84150361 = 63112771) B63112771
theorem B3459311 : Blo 1514954 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B21850559 : Blo 1514954 21850559 := bstep (se 1 (by rfl) ⟨16387919, by rfl⟩ : syracuseStep 21850559 = 32775839) B32775839
theorem B3836393 : Blo 1514954 3836393 := bstep (se 2 (by rfl) ⟨1438647, by rfl⟩ : syracuseStep 3836393 = 2877295) B2877295
theorem B5188265 : Blo 1514954 5188265 := bstep (se 2 (by rfl) ⟨1945599, by rfl⟩ : syracuseStep 5188265 = 3891199) B3891199
theorem B2878183 : Blo 1514954 2878183 := bstep (se 1 (by rfl) ⟨2158637, by rfl⟩ : syracuseStep 2878183 = 4317275) B4317275
theorem B2558783 : Blo 1514954 2558783 := bstep (se 1 (by rfl) ⟨1919087, by rfl⟩ : syracuseStep 2558783 = 3838175) B3838175
theorem B5115041 : Blo 1514954 5115041 := bstep (se 2 (by rfl) ⟨1918140, by rfl⟩ : syracuseStep 5115041 = 3836281) B3836281
theorem B2272511 : Blo 1514954 2272511 := bstep (se 1 (by rfl) ⟨1704383, by rfl⟩ : syracuseStep 2272511 = 3408767) B3408767
theorem B5115419 : Blo 1514954 5115419 := bstep (se 1 (by rfl) ⟨3836564, by rfl⟩ : syracuseStep 5115419 = 7673129) B7673129
theorem B3412943 : Blo 1514954 3412943 := bstep (se 1 (by rfl) ⟨2559707, by rfl⟩ : syracuseStep 3412943 = 5119415) B5119415
theorem B2274407 : Blo 1514954 2274407 := bstep (se 1 (by rfl) ⟨1705805, by rfl⟩ : syracuseStep 2274407 = 3411611) B3411611
theorem B2274431 : Blo 1514954 2274431 := bstep (se 1 (by rfl) ⟨1705823, by rfl⟩ : syracuseStep 2274431 = 3411647) B3411647
theorem B2274719 : Blo 1514954 2274719 := bstep (se 1 (by rfl) ⟨1706039, by rfl⟩ : syracuseStep 2274719 = 3412079) B3412079
theorem B168130241 : Blo 1514954 168130241 := bstep (se 2 (by rfl) ⟨63048840, by rfl⟩ : syracuseStep 168130241 = 126097681) B126097681
theorem B15562945 : Blo 1514954 15562945 := bstep (se 2 (by rfl) ⟨5836104, by rfl⟩ : syracuseStep 15562945 = 11672209) B11672209
theorem B606157121 : Blo 1514954 606157121 := bstep (se 2 (by rfl) ⟨227308920, by rfl⟩ : syracuseStep 606157121 = 454617841) B454617841
theorem B8756423 : Blo 1514954 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B12950867 : Blo 1514954 12950867 := bstep (se 1 (by rfl) ⟨9713150, by rfl⟩ : syracuseStep 12950867 = 19426301) B19426301
theorem B19963381 : Blo 1514954 19963381 := bstep (se 5 (by rfl) ⟨935783, by rfl⟩ : syracuseStep 19963381 = 1871567) B1871567
theorem B1515035 : Blo 1514954 1515035 := bstep (se 1 (by rfl) ⟨1136276, by rfl⟩ : syracuseStep 1515035 = 2272553) B2272553
theorem B7675559 : Blo 1514954 7675559 := bstep (se 1 (by rfl) ⟨5756669, by rfl⟩ : syracuseStep 7675559 = 11513339) B11513339
theorem B1515247 : Blo 1514954 1515247 := bstep (se 1 (by rfl) ⟨1136435, by rfl⟩ : syracuseStep 1515247 = 2272871) B2272871
theorem B1515367 : Blo 1514954 1515367 := bstep (se 1 (by rfl) ⟨1136525, by rfl⟩ : syracuseStep 1515367 = 2273051) B2273051
theorem B20750593 : Blo 1514954 20750593 := bstep (se 2 (by rfl) ⟨7781472, by rfl⟩ : syracuseStep 20750593 = 15562945) B15562945
theorem B78742081 : Blo 1514954 78742081 := bstep (se 2 (by rfl) ⟨29528280, by rfl⟩ : syracuseStep 78742081 = 59056561) B59056561
theorem B1516271 : Blo 1514954 1516271 := bstep (se 1 (by rfl) ⟨1137203, by rfl⟩ : syracuseStep 1516271 = 2274407) B2274407
theorem B1516287 : Blo 1514954 1516287 := bstep (se 1 (by rfl) ⟨1137215, by rfl⟩ : syracuseStep 1516287 = 2274431) B2274431
theorem B1516479 : Blo 1514954 1516479 := bstep (se 1 (by rfl) ⟨1137359, by rfl⟩ : syracuseStep 1516479 = 2274719) B2274719
theorem B9717047 : Blo 1514954 9717047 := bstep (se 1 (by rfl) ⟨7287785, by rfl⟩ : syracuseStep 9717047 = 14575571) B14575571
theorem B404104747 : Blo 1514954 404104747 := bstep (se 1 (by rfl) ⟨303078560, by rfl⟩ : syracuseStep 404104747 = 606157121) B606157121
theorem B14567039 : Blo 1514954 14567039 := bstep (se 1 (by rfl) ⟨10925279, by rfl⟩ : syracuseStep 14567039 = 21850559) B21850559
theorem B2557595 : Blo 1514954 2557595 := bstep (se 1 (by rfl) ⟨1918196, by rfl⟩ : syracuseStep 2557595 = 3836393) B3836393
theorem B3458843 : Blo 1514954 3458843 := bstep (se 1 (by rfl) ⟨2594132, by rfl⟩ : syracuseStep 3458843 = 5188265) B5188265
theorem B1705855 : Blo 1514954 1705855 := bstep (se 1 (by rfl) ⟨1279391, by rfl⟩ : syracuseStep 1705855 = 2558783) B2558783
theorem B26617841 : Blo 1514954 26617841 := bstep (se 2 (by rfl) ⟨9981690, by rfl⟩ : syracuseStep 26617841 = 19963381) B19963381
theorem B3410027 : Blo 1514954 3410027 := bstep (se 1 (by rfl) ⟨2557520, by rfl⟩ : syracuseStep 3410027 = 5115041) B5115041
theorem B3410279 : Blo 1514954 3410279 := bstep (se 1 (by rfl) ⟨2557709, by rfl⟩ : syracuseStep 3410279 = 5115419) B5115419
theorem B112200481 : Blo 1514954 112200481 := bstep (se 2 (by rfl) ⟨42075180, by rfl⟩ : syracuseStep 112200481 = 84150361) B84150361
theorem B3837577 : Blo 1514954 3837577 := bstep (se 2 (by rfl) ⟨1439091, by rfl⟩ : syracuseStep 3837577 = 2878183) B2878183
theorem B112086827 : Blo 1514954 112086827 := bstep (se 1 (by rfl) ⟨84065120, by rfl⟩ : syracuseStep 112086827 = 168130241) B168130241
theorem B2306207 : Blo 1514954 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B2273897 : Blo 1514954 2273897 := bstep (se 2 (by rfl) ⟨852711, by rfl⟩ : syracuseStep 2273897 = 1705423) B1705423
theorem B5837615 : Blo 1514954 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B5117039 : Blo 1514954 5117039 := bstep (se 1 (by rfl) ⟨3837779, by rfl⟩ : syracuseStep 5117039 = 7675559) B7675559
theorem B4855231 : Blo 1514954 4855231 := bstep (se 1 (by rfl) ⟨3641423, by rfl⟩ : syracuseStep 4855231 = 7282847) B7282847
theorem B2275295 : Blo 1514954 2275295 := bstep (se 1 (by rfl) ⟨1706471, by rfl⟩ : syracuseStep 2275295 = 3412943) B3412943
theorem B1515007 : Blo 1514954 1515007 := bstep (se 1 (by rfl) ⟨1136255, by rfl⟩ : syracuseStep 1515007 = 2272511) B2272511
theorem B8633911 : Blo 1514954 8633911 := bstep (se 1 (by rfl) ⟨6475433, by rfl⟩ : syracuseStep 8633911 = 12950867) B12950867
theorem B1515931 : Blo 1514954 1515931 := bstep (se 1 (by rfl) ⟨1136948, by rfl⟩ : syracuseStep 1515931 = 2273897) B2273897
theorem B3891743 : Blo 1514954 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B104989441 : Blo 1514954 104989441 := bstep (se 2 (by rfl) ⟨39371040, by rfl⟩ : syracuseStep 104989441 = 78742081) B78742081
theorem B1705063 : Blo 1514954 1705063 := bstep (se 1 (by rfl) ⟨1278797, by rfl⟩ : syracuseStep 1705063 = 2557595) B2557595
theorem B1516863 : Blo 1514954 1516863 := bstep (se 1 (by rfl) ⟨1137647, by rfl⟩ : syracuseStep 1516863 = 2275295) B2275295
theorem B17745227 : Blo 1514954 17745227 := bstep (se 1 (by rfl) ⟨13308920, by rfl⟩ : syracuseStep 17745227 = 26617841) B26617841
theorem B6473641 : Blo 1514954 6473641 := bstep (se 2 (by rfl) ⟨2427615, by rfl⟩ : syracuseStep 6473641 = 4855231) B4855231
theorem B538806329 : Blo 1514954 538806329 := bstep (se 2 (by rfl) ⟨202052373, by rfl⟩ : syracuseStep 538806329 = 404104747) B404104747
theorem B11511881 : Blo 1514954 11511881 := bstep (se 2 (by rfl) ⟨4316955, by rfl⟩ : syracuseStep 11511881 = 8633911) B8633911
theorem B27667457 : Blo 1514954 27667457 := bstep (se 2 (by rfl) ⟨10375296, by rfl⟩ : syracuseStep 27667457 = 20750593) B20750593
theorem B3411359 : Blo 1514954 3411359 := bstep (se 1 (by rfl) ⟨2558519, by rfl⟩ : syracuseStep 3411359 = 5117039) B5117039
theorem B9711359 : Blo 1514954 9711359 := bstep (se 1 (by rfl) ⟨7283519, by rfl⟩ : syracuseStep 9711359 = 14567039) B14567039
theorem B2273351 : Blo 1514954 2273351 := bstep (se 1 (by rfl) ⟨1705013, by rfl⟩ : syracuseStep 2273351 = 3410027) B3410027
theorem B2273519 : Blo 1514954 2273519 := bstep (se 1 (by rfl) ⟨1705139, by rfl⟩ : syracuseStep 2273519 = 3410279) B3410279
theorem B5116769 : Blo 1514954 5116769 := bstep (se 2 (by rfl) ⟨1918788, by rfl⟩ : syracuseStep 5116769 = 3837577) B3837577
theorem B2274473 : Blo 1514954 2274473 := bstep (se 2 (by rfl) ⟨852927, by rfl⟩ : syracuseStep 2274473 = 1705855) B1705855
theorem B74724551 : Blo 1514954 74724551 := bstep (se 1 (by rfl) ⟨56043413, by rfl⟩ : syracuseStep 74724551 = 112086827) B112086827
theorem B1537471 : Blo 1514954 1537471 := bstep (se 1 (by rfl) ⟨1153103, by rfl⟩ : syracuseStep 1537471 = 2306207) B2306207
theorem B36894325 : Blo 1514954 36894325 := bstep (se 5 (by rfl) ⟨1729421, by rfl⟩ : syracuseStep 36894325 = 3458843) B3458843
theorem B6478031 : Blo 1514954 6478031 := bstep (se 1 (by rfl) ⟨4858523, by rfl⟩ : syracuseStep 6478031 = 9717047) B9717047
theorem B149600641 : Blo 1514954 149600641 := bstep (se 2 (by rfl) ⟨56100240, by rfl⟩ : syracuseStep 149600641 = 112200481) B112200481
theorem B1515567 : Blo 1514954 1515567 := bstep (se 1 (by rfl) ⟨1136675, by rfl⟩ : syracuseStep 1515567 = 2273351) B2273351
theorem B1515679 : Blo 1514954 1515679 := bstep (se 1 (by rfl) ⟨1136759, by rfl⟩ : syracuseStep 1515679 = 2273519) B2273519
theorem B199467521 : Blo 1514954 199467521 := bstep (se 2 (by rfl) ⟨74800320, by rfl⟩ : syracuseStep 199467521 = 149600641) B149600641
theorem B1516315 : Blo 1514954 1516315 := bstep (se 1 (by rfl) ⟨1137236, by rfl⟩ : syracuseStep 1516315 = 2274473) B2274473
theorem B49816367 : Blo 1514954 49816367 := bstep (se 1 (by rfl) ⟨37362275, by rfl⟩ : syracuseStep 49816367 = 74724551) B74724551
theorem B11830151 : Blo 1514954 11830151 := bstep (se 1 (by rfl) ⟨8872613, by rfl⟩ : syracuseStep 11830151 = 17745227) B17745227
theorem B139985921 : Blo 1514954 139985921 := bstep (se 2 (by rfl) ⟨52494720, by rfl⟩ : syracuseStep 139985921 = 104989441) B104989441
theorem B359204219 : Blo 1514954 359204219 := bstep (se 1 (by rfl) ⟨269403164, by rfl⟩ : syracuseStep 359204219 = 538806329) B538806329
theorem B4318687 : Blo 1514954 4318687 := bstep (se 1 (by rfl) ⟨3239015, by rfl⟩ : syracuseStep 4318687 = 6478031) B6478031
theorem B2049961 : Blo 1514954 2049961 := bstep (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) B1537471
theorem B6474239 : Blo 1514954 6474239 := bstep (se 1 (by rfl) ⟨4855679, by rfl⟩ : syracuseStep 6474239 = 9711359) B9711359
theorem B3411179 : Blo 1514954 3411179 := bstep (se 1 (by rfl) ⟨2558384, by rfl⟩ : syracuseStep 3411179 = 5116769) B5116769
theorem B2273417 : Blo 1514954 2273417 := bstep (se 2 (by rfl) ⟨852531, by rfl⟩ : syracuseStep 2273417 = 1705063) B1705063
theorem B18444971 : Blo 1514954 18444971 := bstep (se 1 (by rfl) ⟨13833728, by rfl⟩ : syracuseStep 18444971 = 27667457) B27667457
theorem B2274239 : Blo 1514954 2274239 := bstep (se 1 (by rfl) ⟨1705679, by rfl⟩ : syracuseStep 2274239 = 3411359) B3411359
theorem B8631521 : Blo 1514954 8631521 := bstep (se 2 (by rfl) ⟨3236820, by rfl⟩ : syracuseStep 8631521 = 6473641) B6473641
theorem B2594495 : Blo 1514954 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B7674587 : Blo 1514954 7674587 := bstep (se 1 (by rfl) ⟨5755940, by rfl⟩ : syracuseStep 7674587 = 11511881) B11511881
theorem B49192433 : Blo 1514954 49192433 := bstep (se 2 (by rfl) ⟨18447162, by rfl⟩ : syracuseStep 49192433 = 36894325) B36894325
theorem B1515611 : Blo 1514954 1515611 := bstep (se 1 (by rfl) ⟨1136708, by rfl⟩ : syracuseStep 1515611 = 2273417) B2273417
theorem B12296647 : Blo 1514954 12296647 := bstep (se 1 (by rfl) ⟨9222485, by rfl⟩ : syracuseStep 12296647 = 18444971) B18444971
theorem B33210911 : Blo 1514954 33210911 := bstep (se 1 (by rfl) ⟨24908183, by rfl⟩ : syracuseStep 33210911 = 49816367) B49816367
theorem B1516159 : Blo 1514954 1516159 := bstep (se 1 (by rfl) ⟨1137119, by rfl⟩ : syracuseStep 1516159 = 2274239) B2274239
theorem B93323947 : Blo 1514954 93323947 := bstep (se 1 (by rfl) ⟨69992960, by rfl⟩ : syracuseStep 93323947 = 139985921) B139985921
theorem B239469479 : Blo 1514954 239469479 := bstep (se 1 (by rfl) ⟨179602109, by rfl⟩ : syracuseStep 239469479 = 359204219) B359204219
theorem B1729663 : Blo 1514954 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B32794955 : Blo 1514954 32794955 := bstep (se 1 (by rfl) ⟨24596216, by rfl⟩ : syracuseStep 32794955 = 49192433) B49192433
theorem B5754347 : Blo 1514954 5754347 := bstep (se 1 (by rfl) ⟨4315760, by rfl⟩ : syracuseStep 5754347 = 8631521) B8631521
theorem B5116391 : Blo 1514954 5116391 := bstep (se 1 (by rfl) ⟨3837293, by rfl⟩ : syracuseStep 5116391 = 7674587) B7674587
theorem B2274119 : Blo 1514954 2274119 := bstep (se 1 (by rfl) ⟨1705589, by rfl⟩ : syracuseStep 2274119 = 3411179) B3411179
theorem B2733281 : Blo 1514954 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B132978347 : Blo 1514954 132978347 := bstep (se 1 (by rfl) ⟨99733760, by rfl⟩ : syracuseStep 132978347 = 199467521) B199467521
theorem B7886767 : Blo 1514954 7886767 := bstep (se 1 (by rfl) ⟨5915075, by rfl⟩ : syracuseStep 7886767 = 11830151) B11830151
theorem B4316159 : Blo 1514954 4316159 := bstep (se 1 (by rfl) ⟨3237119, by rfl⟩ : syracuseStep 4316159 = 6474239) B6474239
theorem B5758249 : Blo 1514954 5758249 := bstep (se 2 (by rfl) ⟨2159343, by rfl⟩ : syracuseStep 5758249 = 4318687) B4318687
theorem B1516079 : Blo 1514954 1516079 := bstep (se 1 (by rfl) ⟨1137059, by rfl⟩ : syracuseStep 1516079 = 2274119) B2274119
theorem B159646319 : Blo 1514954 159646319 := bstep (se 1 (by rfl) ⟨119734739, by rfl⟩ : syracuseStep 159646319 = 239469479) B239469479
theorem B9224869 : Blo 1514954 9224869 := bstep (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) B1729663
theorem B7677665 : Blo 1514954 7677665 := bstep (se 2 (by rfl) ⟨2879124, by rfl⟩ : syracuseStep 7677665 = 5758249) B5758249
theorem B2877439 : Blo 1514954 2877439 := bstep (se 1 (by rfl) ⟨2158079, by rfl⟩ : syracuseStep 2877439 = 4316159) B4316159
theorem B3836231 : Blo 1514954 3836231 := bstep (se 1 (by rfl) ⟨2877173, by rfl⟩ : syracuseStep 3836231 = 5754347) B5754347
theorem B3410927 : Blo 1514954 3410927 := bstep (se 1 (by rfl) ⟨2558195, by rfl⟩ : syracuseStep 3410927 = 5116391) B5116391
theorem B16395529 : Blo 1514954 16395529 := bstep (se 2 (by rfl) ⟨6148323, by rfl⟩ : syracuseStep 16395529 = 12296647) B12296647
theorem B1822187 : Blo 1514954 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B124431929 : Blo 1514954 124431929 := bstep (se 2 (by rfl) ⟨46661973, by rfl⟩ : syracuseStep 124431929 = 93323947) B93323947
theorem B10515689 : Blo 1514954 10515689 := bstep (se 2 (by rfl) ⟨3943383, by rfl⟩ : syracuseStep 10515689 = 7886767) B7886767
theorem B88652231 : Blo 1514954 88652231 := bstep (se 1 (by rfl) ⟨66489173, by rfl⟩ : syracuseStep 88652231 = 132978347) B132978347
theorem B88562429 : Blo 1514954 88562429 := bstep (se 3 (by rfl) ⟨16605455, by rfl⟩ : syracuseStep 88562429 = 33210911) B33210911
theorem B21863303 : Blo 1514954 21863303 := bstep (se 1 (by rfl) ⟨16397477, by rfl⟩ : syracuseStep 21863303 = 32794955) B32794955
theorem B106430879 : Blo 1514954 106430879 := bstep (se 1 (by rfl) ⟨79823159, by rfl⟩ : syracuseStep 106430879 = 159646319) B159646319
theorem B4859165 : Blo 1514954 4859165 := bstep (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) B1822187
theorem B2557487 : Blo 1514954 2557487 := bstep (se 1 (by rfl) ⟨1918115, by rfl⟩ : syracuseStep 2557487 = 3836231) B3836231
theorem B59041619 : Blo 1514954 59041619 := bstep (se 1 (by rfl) ⟨44281214, by rfl⟩ : syracuseStep 59041619 = 88562429) B88562429
theorem B14575535 : Blo 1514954 14575535 := bstep (se 1 (by rfl) ⟨10931651, by rfl⟩ : syracuseStep 14575535 = 21863303) B21863303
theorem B82954619 : Blo 1514954 82954619 := bstep (se 1 (by rfl) ⟨62215964, by rfl⟩ : syracuseStep 82954619 = 124431929) B124431929
theorem B3836585 : Blo 1514954 3836585 := bstep (se 2 (by rfl) ⟨1438719, by rfl⟩ : syracuseStep 3836585 = 2877439) B2877439
theorem B12299825 : Blo 1514954 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B59101487 : Blo 1514954 59101487 := bstep (se 1 (by rfl) ⟨44326115, by rfl⟩ : syracuseStep 59101487 = 88652231) B88652231
theorem B21860705 : Blo 1514954 21860705 := bstep (se 2 (by rfl) ⟨8197764, by rfl⟩ : syracuseStep 21860705 = 16395529) B16395529
theorem B2273951 : Blo 1514954 2273951 := bstep (se 1 (by rfl) ⟨1705463, by rfl⟩ : syracuseStep 2273951 = 3410927) B3410927
theorem B7010459 : Blo 1514954 7010459 := bstep (se 1 (by rfl) ⟨5257844, by rfl⟩ : syracuseStep 7010459 = 10515689) B10515689
theorem B5118443 : Blo 1514954 5118443 := bstep (se 1 (by rfl) ⟨3838832, by rfl⟩ : syracuseStep 5118443 = 7677665) B7677665
theorem B14573803 : Blo 1514954 14573803 := bstep (se 1 (by rfl) ⟨10930352, by rfl⟩ : syracuseStep 14573803 = 21860705) B21860705
theorem B1515967 : Blo 1514954 1515967 := bstep (se 1 (by rfl) ⟨1136975, by rfl⟩ : syracuseStep 1515967 = 2273951) B2273951
theorem B1704991 : Blo 1514954 1704991 := bstep (se 1 (by rfl) ⟨1278743, by rfl⟩ : syracuseStep 1704991 = 2557487) B2557487
theorem B9717023 : Blo 1514954 9717023 := bstep (se 1 (by rfl) ⟨7287767, by rfl⟩ : syracuseStep 9717023 = 14575535) B14575535
theorem B2557723 : Blo 1514954 2557723 := bstep (se 1 (by rfl) ⟨1918292, by rfl⟩ : syracuseStep 2557723 = 3836585) B3836585
theorem B3239443 : Blo 1514954 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B283815677 : Blo 1514954 283815677 := bstep (se 3 (by rfl) ⟨53215439, by rfl⟩ : syracuseStep 283815677 = 106430879) B106430879
theorem B4673639 : Blo 1514954 4673639 := bstep (se 1 (by rfl) ⟨3505229, by rfl⟩ : syracuseStep 4673639 = 7010459) B7010459
theorem B3412295 : Blo 1514954 3412295 := bstep (se 1 (by rfl) ⟨2559221, by rfl⟩ : syracuseStep 3412295 = 5118443) B5118443
theorem B39400991 : Blo 1514954 39400991 := bstep (se 1 (by rfl) ⟨29550743, by rfl⟩ : syracuseStep 39400991 = 59101487) B59101487
theorem B39361079 : Blo 1514954 39361079 := bstep (se 1 (by rfl) ⟨29520809, by rfl⟩ : syracuseStep 39361079 = 59041619) B59041619
theorem B55303079 : Blo 1514954 55303079 := bstep (se 1 (by rfl) ⟨41477309, by rfl⟩ : syracuseStep 55303079 = 82954619) B82954619
theorem B8199883 : Blo 1514954 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B19431737 : Blo 1514954 19431737 := bstep (se 2 (by rfl) ⟨7286901, by rfl⟩ : syracuseStep 19431737 = 14573803) B14573803
theorem B26240719 : Blo 1514954 26240719 := bstep (se 1 (by rfl) ⟨19680539, by rfl⟩ : syracuseStep 26240719 = 39361079) B39361079
theorem B4319257 : Blo 1514954 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B3410297 : Blo 1514954 3410297 := bstep (se 2 (by rfl) ⟨1278861, by rfl⟩ : syracuseStep 3410297 = 2557723) B2557723
theorem B147474877 : Blo 1514954 147474877 := bstep (se 3 (by rfl) ⟨27651539, by rfl⟩ : syracuseStep 147474877 = 55303079) B55303079
theorem B3115759 : Blo 1514954 3115759 := bstep (se 1 (by rfl) ⟨2336819, by rfl⟩ : syracuseStep 3115759 = 4673639) B4673639
theorem B26267327 : Blo 1514954 26267327 := bstep (se 1 (by rfl) ⟨19700495, by rfl⟩ : syracuseStep 26267327 = 39400991) B39400991
theorem B43732709 : Blo 1514954 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B2273321 : Blo 1514954 2273321 := bstep (se 2 (by rfl) ⟨852495, by rfl⟩ : syracuseStep 2273321 = 1704991) B1704991
theorem B2274863 : Blo 1514954 2274863 := bstep (se 1 (by rfl) ⟨1706147, by rfl⟩ : syracuseStep 2274863 = 3412295) B3412295
theorem B6478015 : Blo 1514954 6478015 := bstep (se 1 (by rfl) ⟨4858511, by rfl⟩ : syracuseStep 6478015 = 9717023) B9717023
theorem B189210451 : Blo 1514954 189210451 := bstep (se 1 (by rfl) ⟨141907838, by rfl⟩ : syracuseStep 189210451 = 283815677) B283815677
theorem B1515547 : Blo 1514954 1515547 := bstep (se 1 (by rfl) ⟨1136660, by rfl⟩ : syracuseStep 1515547 = 2273321) B2273321
theorem B5759009 : Blo 1514954 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B196633169 : Blo 1514954 196633169 := bstep (se 2 (by rfl) ⟨73737438, by rfl⟩ : syracuseStep 196633169 = 147474877) B147474877
theorem B4154345 : Blo 1514954 4154345 := bstep (se 2 (by rfl) ⟨1557879, by rfl⟩ : syracuseStep 4154345 = 3115759) B3115759
theorem B1516575 : Blo 1514954 1516575 := bstep (se 1 (by rfl) ⟨1137431, by rfl⟩ : syracuseStep 1516575 = 2274863) B2274863
theorem B12954491 : Blo 1514954 12954491 := bstep (se 1 (by rfl) ⟨9715868, by rfl⟩ : syracuseStep 12954491 = 19431737) B19431737
theorem B8637353 : Blo 1514954 8637353 := bstep (se 2 (by rfl) ⟨3239007, by rfl⟩ : syracuseStep 8637353 = 6478015) B6478015
theorem B2273531 : Blo 1514954 2273531 := bstep (se 1 (by rfl) ⟨1705148, by rfl⟩ : syracuseStep 2273531 = 3410297) B3410297
theorem B17511551 : Blo 1514954 17511551 := bstep (se 1 (by rfl) ⟨13133663, by rfl⟩ : syracuseStep 17511551 = 26267327) B26267327
theorem B34987625 : Blo 1514954 34987625 := bstep (se 2 (by rfl) ⟨13120359, by rfl⟩ : syracuseStep 34987625 = 26240719) B26240719
theorem B252280601 : Blo 1514954 252280601 := bstep (se 2 (by rfl) ⟨94605225, by rfl⟩ : syracuseStep 252280601 = 189210451) B189210451
theorem B29155139 : Blo 1514954 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B1515687 : Blo 1514954 1515687 := bstep (se 1 (by rfl) ⟨1136765, by rfl⟩ : syracuseStep 1515687 = 2273531) B2273531
theorem B131088779 : Blo 1514954 131088779 := bstep (se 1 (by rfl) ⟨98316584, by rfl⟩ : syracuseStep 131088779 = 196633169) B196633169
theorem B2769563 : Blo 1514954 2769563 := bstep (se 1 (by rfl) ⟨2077172, by rfl⟩ : syracuseStep 2769563 = 4154345) B4154345
theorem B11674367 : Blo 1514954 11674367 := bstep (se 1 (by rfl) ⟨8755775, by rfl⟩ : syracuseStep 11674367 = 17511551) B17511551
theorem B8636327 : Blo 1514954 8636327 := bstep (se 1 (by rfl) ⟨6477245, by rfl⟩ : syracuseStep 8636327 = 12954491) B12954491
theorem B23325083 : Blo 1514954 23325083 := bstep (se 1 (by rfl) ⟨17493812, by rfl⟩ : syracuseStep 23325083 = 34987625) B34987625
theorem B168187067 : Blo 1514954 168187067 := bstep (se 1 (by rfl) ⟨126140300, by rfl⟩ : syracuseStep 168187067 = 252280601) B252280601
theorem B19436759 : Blo 1514954 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B3839339 : Blo 1514954 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B5758235 : Blo 1514954 5758235 := bstep (se 1 (by rfl) ⟨4318676, by rfl⟩ : syracuseStep 5758235 = 8637353) B8637353
theorem B87392519 : Blo 1514954 87392519 := bstep (se 1 (by rfl) ⟨65544389, by rfl⟩ : syracuseStep 87392519 = 131088779) B131088779
theorem B7782911 : Blo 1514954 7782911 := bstep (se 1 (by rfl) ⟨5837183, by rfl⟩ : syracuseStep 7782911 = 11674367) B11674367
theorem B112124711 : Blo 1514954 112124711 := bstep (se 1 (by rfl) ⟨84093533, by rfl⟩ : syracuseStep 112124711 = 168187067) B168187067
theorem B15550055 : Blo 1514954 15550055 := bstep (se 1 (by rfl) ⟨11662541, by rfl⟩ : syracuseStep 15550055 = 23325083) B23325083
theorem B2559559 : Blo 1514954 2559559 := bstep (se 1 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 2559559 = 3839339) B3839339
theorem B7385501 : Blo 1514954 7385501 := bstep (se 3 (by rfl) ⟨1384781, by rfl⟩ : syracuseStep 7385501 = 2769563) B2769563
theorem B3838823 : Blo 1514954 3838823 := bstep (se 1 (by rfl) ⟨2879117, by rfl⟩ : syracuseStep 3838823 = 5758235) B5758235
theorem B12957839 : Blo 1514954 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B5757551 : Blo 1514954 5757551 := bstep (se 1 (by rfl) ⟨4318163, by rfl⟩ : syracuseStep 5757551 = 8636327) B8636327
theorem B58261679 : Blo 1514954 58261679 := bstep (se 1 (by rfl) ⟨43696259, by rfl⟩ : syracuseStep 58261679 = 87392519) B87392519
theorem B4923667 : Blo 1514954 4923667 := bstep (se 1 (by rfl) ⟨3692750, by rfl⟩ : syracuseStep 4923667 = 7385501) B7385501
theorem B5188607 : Blo 1514954 5188607 := bstep (se 1 (by rfl) ⟨3891455, by rfl⟩ : syracuseStep 5188607 = 7782911) B7782911
theorem B2559215 : Blo 1514954 2559215 := bstep (se 1 (by rfl) ⟨1919411, by rfl⟩ : syracuseStep 2559215 = 3838823) B3838823
theorem B10366703 : Blo 1514954 10366703 := bstep (se 1 (by rfl) ⟨7775027, by rfl⟩ : syracuseStep 10366703 = 15550055) B15550055
theorem B8638559 : Blo 1514954 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B3838367 : Blo 1514954 3838367 := bstep (se 1 (by rfl) ⟨2878775, by rfl⟩ : syracuseStep 3838367 = 5757551) B5757551
theorem B3412745 : Blo 1514954 3412745 := bstep (se 2 (by rfl) ⟨1279779, by rfl⟩ : syracuseStep 3412745 = 2559559) B2559559
theorem B74749807 : Blo 1514954 74749807 := bstep (se 1 (by rfl) ⟨56062355, by rfl⟩ : syracuseStep 74749807 = 112124711) B112124711
theorem B5759039 : Blo 1514954 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B3459071 : Blo 1514954 3459071 := bstep (se 1 (by rfl) ⟨2594303, by rfl⟩ : syracuseStep 3459071 = 5188607) B5188607
theorem B1706143 : Blo 1514954 1706143 := bstep (se 1 (by rfl) ⟨1279607, by rfl⟩ : syracuseStep 1706143 = 2559215) B2559215
theorem B99666409 : Blo 1514954 99666409 := bstep (se 2 (by rfl) ⟨37374903, by rfl⟩ : syracuseStep 99666409 = 74749807) B74749807
theorem B38841119 : Blo 1514954 38841119 := bstep (se 1 (by rfl) ⟨29130839, by rfl⟩ : syracuseStep 38841119 = 58261679) B58261679
theorem B2558911 : Blo 1514954 2558911 := bstep (se 1 (by rfl) ⟨1919183, by rfl⟩ : syracuseStep 2558911 = 3838367) B3838367
theorem B26259557 : Blo 1514954 26259557 := bstep (se 4 (by rfl) ⟨2461833, by rfl⟩ : syracuseStep 26259557 = 4923667) B4923667
theorem B6911135 : Blo 1514954 6911135 := bstep (se 1 (by rfl) ⟨5183351, by rfl⟩ : syracuseStep 6911135 = 10366703) B10366703
theorem B2275163 : Blo 1514954 2275163 := bstep (se 1 (by rfl) ⟨1706372, by rfl⟩ : syracuseStep 2275163 = 3412745) B3412745
theorem B70025485 : Blo 1514954 70025485 := bstep (se 3 (by rfl) ⟨13129778, by rfl⟩ : syracuseStep 70025485 = 26259557) B26259557
theorem B1516775 : Blo 1514954 1516775 := bstep (se 1 (by rfl) ⟨1137581, by rfl⟩ : syracuseStep 1516775 = 2275163) B2275163
theorem B4607423 : Blo 1514954 4607423 := bstep (se 1 (by rfl) ⟨3455567, by rfl⟩ : syracuseStep 4607423 = 6911135) B6911135
theorem B3411881 : Blo 1514954 3411881 := bstep (se 2 (by rfl) ⟨1279455, by rfl⟩ : syracuseStep 3411881 = 2558911) B2558911
theorem B3839359 : Blo 1514954 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B2274857 : Blo 1514954 2274857 := bstep (se 2 (by rfl) ⟨853071, by rfl⟩ : syracuseStep 2274857 = 1706143) B1706143
theorem B132888545 : Blo 1514954 132888545 := bstep (se 2 (by rfl) ⟨49833204, by rfl⟩ : syracuseStep 132888545 = 99666409) B99666409
theorem B25894079 : Blo 1514954 25894079 := bstep (se 1 (by rfl) ⟨19420559, by rfl⟩ : syracuseStep 25894079 = 38841119) B38841119
theorem B9224189 : Blo 1514954 9224189 := bstep (se 3 (by rfl) ⟨1729535, by rfl⟩ : syracuseStep 9224189 = 3459071) B3459071
theorem B1516571 : Blo 1514954 1516571 := bstep (se 1 (by rfl) ⟨1137428, by rfl⟩ : syracuseStep 1516571 = 2274857) B2274857
theorem B17262719 : Blo 1514954 17262719 := bstep (se 1 (by rfl) ⟨12947039, by rfl⟩ : syracuseStep 17262719 = 25894079) B25894079
theorem B93367313 : Blo 1514954 93367313 := bstep (se 2 (by rfl) ⟨35012742, by rfl⟩ : syracuseStep 93367313 = 70025485) B70025485
theorem B88592363 : Blo 1514954 88592363 := bstep (se 1 (by rfl) ⟨66444272, by rfl⟩ : syracuseStep 88592363 = 132888545) B132888545
theorem B2274587 : Blo 1514954 2274587 := bstep (se 1 (by rfl) ⟨1705940, by rfl⟩ : syracuseStep 2274587 = 3411881) B3411881
theorem B6149459 : Blo 1514954 6149459 := bstep (se 1 (by rfl) ⟨4612094, by rfl⟩ : syracuseStep 6149459 = 9224189) B9224189
theorem B5119145 : Blo 1514954 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B3071615 : Blo 1514954 3071615 := bstep (se 1 (by rfl) ⟨2303711, by rfl⟩ : syracuseStep 3071615 = 4607423) B4607423
theorem B1516391 : Blo 1514954 1516391 := bstep (se 1 (by rfl) ⟨1137293, by rfl⟩ : syracuseStep 1516391 = 2274587) B2274587
theorem B62244875 : Blo 1514954 62244875 := bstep (se 1 (by rfl) ⟨46683656, by rfl⟩ : syracuseStep 62244875 = 93367313) B93367313
theorem B4099639 : Blo 1514954 4099639 := bstep (se 1 (by rfl) ⟨3074729, by rfl⟩ : syracuseStep 4099639 = 6149459) B6149459
theorem B3412763 : Blo 1514954 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B59061575 : Blo 1514954 59061575 := bstep (se 1 (by rfl) ⟨44296181, by rfl⟩ : syracuseStep 59061575 = 88592363) B88592363
theorem B11508479 : Blo 1514954 11508479 := bstep (se 1 (by rfl) ⟨8631359, by rfl⟩ : syracuseStep 11508479 = 17262719) B17262719
theorem B8190973 : Blo 1514954 8190973 := bstep (se 3 (by rfl) ⟨1535807, by rfl⟩ : syracuseStep 8190973 = 3071615) B3071615
theorem B5466185 : Blo 1514954 5466185 := bstep (se 2 (by rfl) ⟨2049819, by rfl⟩ : syracuseStep 5466185 = 4099639) B4099639
theorem B39374383 : Blo 1514954 39374383 := bstep (se 1 (by rfl) ⟨29530787, by rfl⟩ : syracuseStep 39374383 = 59061575) B59061575
theorem B41496583 : Blo 1514954 41496583 := bstep (se 1 (by rfl) ⟨31122437, by rfl⟩ : syracuseStep 41496583 = 62244875) B62244875
theorem B7672319 : Blo 1514954 7672319 := bstep (se 1 (by rfl) ⟨5754239, by rfl⟩ : syracuseStep 7672319 = 11508479) B11508479
theorem B43685189 : Blo 1514954 43685189 := bstep (se 4 (by rfl) ⟨4095486, by rfl⟩ : syracuseStep 43685189 = 8190973) B8190973
theorem B2275175 : Blo 1514954 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B55328777 : Blo 1514954 55328777 := bstep (se 2 (by rfl) ⟨20748291, by rfl⟩ : syracuseStep 55328777 = 41496583) B41496583
theorem B29123459 : Blo 1514954 29123459 := bstep (se 1 (by rfl) ⟨21842594, by rfl⟩ : syracuseStep 29123459 = 43685189) B43685189
theorem B1516783 : Blo 1514954 1516783 := bstep (se 1 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 1516783 = 2275175) B2275175
theorem B5114879 : Blo 1514954 5114879 := bstep (se 1 (by rfl) ⟨3836159, by rfl⟩ : syracuseStep 5114879 = 7672319) B7672319
theorem B52499177 : Blo 1514954 52499177 := bstep (se 2 (by rfl) ⟨19687191, by rfl⟩ : syracuseStep 52499177 = 39374383) B39374383
theorem B3644123 : Blo 1514954 3644123 := bstep (se 1 (by rfl) ⟨2733092, by rfl⟩ : syracuseStep 3644123 = 5466185) B5466185
theorem B19415639 : Blo 1514954 19415639 := bstep (se 1 (by rfl) ⟨14561729, by rfl⟩ : syracuseStep 19415639 = 29123459) B29123459
theorem B9717661 : Blo 1514954 9717661 := bstep (se 3 (by rfl) ⟨1822061, by rfl⟩ : syracuseStep 9717661 = 3644123) B3644123
theorem B3409919 : Blo 1514954 3409919 := bstep (se 1 (by rfl) ⟨2557439, by rfl⟩ : syracuseStep 3409919 = 5114879) B5114879
theorem B34999451 : Blo 1514954 34999451 := bstep (se 1 (by rfl) ⟨26249588, by rfl⟩ : syracuseStep 34999451 = 52499177) B52499177
theorem B36885851 : Blo 1514954 36885851 := bstep (se 1 (by rfl) ⟨27664388, by rfl⟩ : syracuseStep 36885851 = 55328777) B55328777
theorem B12943759 : Blo 1514954 12943759 := bstep (se 1 (by rfl) ⟨9707819, by rfl⟩ : syracuseStep 12943759 = 19415639) B19415639
theorem B23332967 : Blo 1514954 23332967 := bstep (se 1 (by rfl) ⟨17499725, by rfl⟩ : syracuseStep 23332967 = 34999451) B34999451
theorem B2273279 : Blo 1514954 2273279 := bstep (se 1 (by rfl) ⟨1704959, by rfl⟩ : syracuseStep 2273279 = 3409919) B3409919
theorem B12956881 : Blo 1514954 12956881 := bstep (se 2 (by rfl) ⟨4858830, by rfl⟩ : syracuseStep 12956881 = 9717661) B9717661
theorem B24590567 : Blo 1514954 24590567 := bstep (se 1 (by rfl) ⟨18442925, by rfl⟩ : syracuseStep 24590567 = 36885851) B36885851
theorem B16393711 : Blo 1514954 16393711 := bstep (se 1 (by rfl) ⟨12295283, by rfl⟩ : syracuseStep 16393711 = 24590567) B24590567
theorem B17258345 : Blo 1514954 17258345 := bstep (se 2 (by rfl) ⟨6471879, by rfl⟩ : syracuseStep 17258345 = 12943759) B12943759
theorem B15555311 : Blo 1514954 15555311 := bstep (se 1 (by rfl) ⟨11666483, by rfl⟩ : syracuseStep 15555311 = 23332967) B23332967
theorem B17275841 : Blo 1514954 17275841 := bstep (se 2 (by rfl) ⟨6478440, by rfl⟩ : syracuseStep 17275841 = 12956881) B12956881
theorem B1515519 : Blo 1514954 1515519 := bstep (se 1 (by rfl) ⟨1136639, by rfl⟩ : syracuseStep 1515519 = 2273279) B2273279
theorem B21858281 : Blo 1514954 21858281 := bstep (se 2 (by rfl) ⟨8196855, by rfl⟩ : syracuseStep 21858281 = 16393711) B16393711
theorem B11505563 : Blo 1514954 11505563 := bstep (se 1 (by rfl) ⟨8629172, by rfl⟩ : syracuseStep 11505563 = 17258345) B17258345
theorem B10370207 : Blo 1514954 10370207 := bstep (se 1 (by rfl) ⟨7777655, by rfl⟩ : syracuseStep 10370207 = 15555311) B15555311
theorem B11517227 : Blo 1514954 11517227 := bstep (se 1 (by rfl) ⟨8637920, by rfl⟩ : syracuseStep 11517227 = 17275841) B17275841
theorem B7678151 : Blo 1514954 7678151 := bstep (se 1 (by rfl) ⟨5758613, by rfl⟩ : syracuseStep 7678151 = 11517227) B11517227
theorem B7670375 : Blo 1514954 7670375 := bstep (se 1 (by rfl) ⟨5752781, by rfl⟩ : syracuseStep 7670375 = 11505563) B11505563
theorem B27653885 : Blo 1514954 27653885 := bstep (se 3 (by rfl) ⟨5185103, by rfl⟩ : syracuseStep 27653885 = 10370207) B10370207
theorem B14572187 : Blo 1514954 14572187 := bstep (se 1 (by rfl) ⟨10929140, by rfl⟩ : syracuseStep 14572187 = 21858281) B21858281
theorem B5113583 : Blo 1514954 5113583 := bstep (se 1 (by rfl) ⟨3835187, by rfl⟩ : syracuseStep 5113583 = 7670375) B7670375
theorem B18435923 : Blo 1514954 18435923 := bstep (se 1 (by rfl) ⟨13826942, by rfl⟩ : syracuseStep 18435923 = 27653885) B27653885
theorem B5118767 : Blo 1514954 5118767 := bstep (se 1 (by rfl) ⟨3839075, by rfl⟩ : syracuseStep 5118767 = 7678151) B7678151
theorem B9714791 : Blo 1514954 9714791 := bstep (se 1 (by rfl) ⟨7286093, by rfl⟩ : syracuseStep 9714791 = 14572187) B14572187
theorem B3409055 : Blo 1514954 3409055 := bstep (se 1 (by rfl) ⟨2556791, by rfl⟩ : syracuseStep 3409055 = 5113583) B5113583
theorem B12290615 : Blo 1514954 12290615 := bstep (se 1 (by rfl) ⟨9217961, by rfl⟩ : syracuseStep 12290615 = 18435923) B18435923
theorem B3412511 : Blo 1514954 3412511 := bstep (se 1 (by rfl) ⟨2559383, by rfl⟩ : syracuseStep 3412511 = 5118767) B5118767
theorem B6476527 : Blo 1514954 6476527 := bstep (se 1 (by rfl) ⟨4857395, by rfl⟩ : syracuseStep 6476527 = 9714791) B9714791
theorem B8635369 : Blo 1514954 8635369 := bstep (se 2 (by rfl) ⟨3238263, by rfl⟩ : syracuseStep 8635369 = 6476527) B6476527
theorem B8193743 : Blo 1514954 8193743 := bstep (se 1 (by rfl) ⟨6145307, by rfl⟩ : syracuseStep 8193743 = 12290615) B12290615
theorem B2272703 : Blo 1514954 2272703 := bstep (se 1 (by rfl) ⟨1704527, by rfl⟩ : syracuseStep 2272703 = 3409055) B3409055
theorem B2275007 : Blo 1514954 2275007 := bstep (se 1 (by rfl) ⟨1706255, by rfl⟩ : syracuseStep 2275007 = 3412511) B3412511
theorem B1516671 : Blo 1514954 1516671 := bstep (se 1 (by rfl) ⟨1137503, by rfl⟩ : syracuseStep 1516671 = 2275007) B2275007
theorem B11513825 : Blo 1514954 11513825 := bstep (se 2 (by rfl) ⟨4317684, by rfl⟩ : syracuseStep 11513825 = 8635369) B8635369
theorem B5462495 : Blo 1514954 5462495 := bstep (se 1 (by rfl) ⟨4096871, by rfl⟩ : syracuseStep 5462495 = 8193743) B8193743
theorem B1515135 : Blo 1514954 1515135 := bstep (se 1 (by rfl) ⟨1136351, by rfl⟩ : syracuseStep 1515135 = 2272703) B2272703
theorem B3641663 : Blo 1514954 3641663 := bstep (se 1 (by rfl) ⟨2731247, by rfl⟩ : syracuseStep 3641663 = 5462495) B5462495
theorem B7675883 : Blo 1514954 7675883 := bstep (se 1 (by rfl) ⟨5756912, by rfl⟩ : syracuseStep 7675883 = 11513825) B11513825
theorem B2427775 : Blo 1514954 2427775 := bstep (se 1 (by rfl) ⟨1820831, by rfl⟩ : syracuseStep 2427775 = 3641663) B3641663
theorem B5117255 : Blo 1514954 5117255 := bstep (se 1 (by rfl) ⟨3837941, by rfl⟩ : syracuseStep 5117255 = 7675883) B7675883
theorem B3411503 : Blo 1514954 3411503 := bstep (se 1 (by rfl) ⟨2558627, by rfl⟩ : syracuseStep 3411503 = 5117255) B5117255
theorem B12948133 : Blo 1514954 12948133 := bstep (se 4 (by rfl) ⟨1213887, by rfl⟩ : syracuseStep 12948133 = 2427775) B2427775
theorem B17264177 : Blo 1514954 17264177 := bstep (se 2 (by rfl) ⟨6474066, by rfl⟩ : syracuseStep 17264177 = 12948133) B12948133
theorem B2274335 : Blo 1514954 2274335 := bstep (se 1 (by rfl) ⟨1705751, by rfl⟩ : syracuseStep 2274335 = 3411503) B3411503
theorem B1516223 : Blo 1514954 1516223 := bstep (se 1 (by rfl) ⟨1137167, by rfl⟩ : syracuseStep 1516223 = 2274335) B2274335
theorem B11509451 : Blo 1514954 11509451 := bstep (se 1 (by rfl) ⟨8632088, by rfl⟩ : syracuseStep 11509451 = 17264177) B17264177
theorem B7672967 : Blo 1514954 7672967 := bstep (se 1 (by rfl) ⟨5754725, by rfl⟩ : syracuseStep 7672967 = 11509451) B11509451
theorem B5115311 : Blo 1514954 5115311 := bstep (se 1 (by rfl) ⟨3836483, by rfl⟩ : syracuseStep 5115311 = 7672967) B7672967
theorem B3410207 : Blo 1514954 3410207 := bstep (se 1 (by rfl) ⟨2557655, by rfl⟩ : syracuseStep 3410207 = 5115311) B5115311
theorem B2273471 : Blo 1514954 2273471 := bstep (se 1 (by rfl) ⟨1705103, by rfl⟩ : syracuseStep 2273471 = 3410207) B3410207
theorem B1515647 : Blo 1514954 1515647 := bstep (se 1 (by rfl) ⟨1136735, by rfl⟩ : syracuseStep 1515647 = 2273471) B2273471

theorem C0 (j : ℕ) (h1 : 378738 ≤ j) (h2 : j ≤ 379237) : Blo 1514954 (4 * j + 3) := by
  interval_cases j
  · exact B1514955
  · exact B1514959
  · exact B1514963
  · exact B1514967
  · exact B1514971
  · exact B1514975
  · exact B1514979
  · exact B1514983
  · exact B1514987
  · exact B1514991
  · exact B1514995
  · exact B1514999
  · exact B1515003
  · exact B1515007
  · exact B1515011
  · exact B1515015
  · exact B1515019
  · exact B1515023
  · exact B1515027
  · exact B1515031
  · exact B1515035
  · exact B1515039
  · exact B1515043
  · exact B1515047
  · exact B1515051
  · exact B1515055
  · exact B1515059
  · exact B1515063
  · exact B1515067
  · exact B1515071
  · exact B1515075
  · exact B1515079
  · exact B1515083
  · exact B1515087
  · exact B1515091
  · exact B1515095
  · exact B1515099
  · exact B1515103
  · exact B1515107
  · exact B1515111
  · exact B1515115
  · exact B1515119
  · exact B1515123
  · exact B1515127
  · exact B1515131
  · exact B1515135
  · exact B1515139
  · exact B1515143
  · exact B1515147
  · exact B1515151
  · exact B1515155
  · exact B1515159
  · exact B1515163
  · exact B1515167
  · exact B1515171
  · exact B1515175
  · exact B1515179
  · exact B1515183
  · exact B1515187
  · exact B1515191
  · exact B1515195
  · exact B1515199
  · exact B1515203
  · exact B1515207
  · exact B1515211
  · exact B1515215
  · exact B1515219
  · exact B1515223
  · exact B1515227
  · exact B1515231
  · exact B1515235
  · exact B1515239
  · exact B1515243
  · exact B1515247
  · exact B1515251
  · exact B1515255
  · exact B1515259
  · exact B1515263
  · exact B1515267
  · exact B1515271
  · exact B1515275
  · exact B1515279
  · exact B1515283
  · exact B1515287
  · exact B1515291
  · exact B1515295
  · exact B1515299
  · exact B1515303
  · exact B1515307
  · exact B1515311
  · exact B1515315
  · exact B1515319
  · exact B1515323
  · exact B1515327
  · exact B1515331
  · exact B1515335
  · exact B1515339
  · exact B1515343
  · exact B1515347
  · exact B1515351
  · exact B1515355
  · exact B1515359
  · exact B1515363
  · exact B1515367
  · exact B1515371
  · exact B1515375
  · exact B1515379
  · exact B1515383
  · exact B1515387
  · exact B1515391
  · exact B1515395
  · exact B1515399
  · exact B1515403
  · exact B1515407
  · exact B1515411
  · exact B1515415
  · exact B1515419
  · exact B1515423
  · exact B1515427
  · exact B1515431
  · exact B1515435
  · exact B1515439
  · exact B1515443
  · exact B1515447
  · exact B1515451
  · exact B1515455
  · exact B1515459
  · exact B1515463
  · exact B1515467
  · exact B1515471
  · exact B1515475
  · exact B1515479
  · exact B1515483
  · exact B1515487
  · exact B1515491
  · exact B1515495
  · exact B1515499
  · exact B1515503
  · exact B1515507
  · exact B1515511
  · exact B1515515
  · exact B1515519
  · exact B1515523
  · exact B1515527
  · exact B1515531
  · exact B1515535
  · exact B1515539
  · exact B1515543
  · exact B1515547
  · exact B1515551
  · exact B1515555
  · exact B1515559
  · exact B1515563
  · exact B1515567
  · exact B1515571
  · exact B1515575
  · exact B1515579
  · exact B1515583
  · exact B1515587
  · exact B1515591
  · exact B1515595
  · exact B1515599
  · exact B1515603
  · exact B1515607
  · exact B1515611
  · exact B1515615
  · exact B1515619
  · exact B1515623
  · exact B1515627
  · exact B1515631
  · exact B1515635
  · exact B1515639
  · exact B1515643
  · exact B1515647
  · exact B1515651
  · exact B1515655
  · exact B1515659
  · exact B1515663
  · exact B1515667
  · exact B1515671
  · exact B1515675
  · exact B1515679
  · exact B1515683
  · exact B1515687
  · exact B1515691
  · exact B1515695
  · exact B1515699
  · exact B1515703
  · exact B1515707
  · exact B1515711
  · exact B1515715
  · exact B1515719
  · exact B1515723
  · exact B1515727
  · exact B1515731
  · exact B1515735
  · exact B1515739
  · exact B1515743
  · exact B1515747
  · exact B1515751
  · exact B1515755
  · exact B1515759
  · exact B1515763
  · exact B1515767
  · exact B1515771
  · exact B1515775
  · exact B1515779
  · exact B1515783
  · exact B1515787
  · exact B1515791
  · exact B1515795
  · exact B1515799
  · exact B1515803
  · exact B1515807
  · exact B1515811
  · exact B1515815
  · exact B1515819
  · exact B1515823
  · exact B1515827
  · exact B1515831
  · exact B1515835
  · exact B1515839
  · exact B1515843
  · exact B1515847
  · exact B1515851
  · exact B1515855
  · exact B1515859
  · exact B1515863
  · exact B1515867
  · exact B1515871
  · exact B1515875
  · exact B1515879
  · exact B1515883
  · exact B1515887
  · exact B1515891
  · exact B1515895
  · exact B1515899
  · exact B1515903
  · exact B1515907
  · exact B1515911
  · exact B1515915
  · exact B1515919
  · exact B1515923
  · exact B1515927
  · exact B1515931
  · exact B1515935
  · exact B1515939
  · exact B1515943
  · exact B1515947
  · exact B1515951
  · exact B1515955
  · exact B1515959
  · exact B1515963
  · exact B1515967
  · exact B1515971
  · exact B1515975
  · exact B1515979
  · exact B1515983
  · exact B1515987
  · exact B1515991
  · exact B1515995
  · exact B1515999
  · exact B1516003
  · exact B1516007
  · exact B1516011
  · exact B1516015
  · exact B1516019
  · exact B1516023
  · exact B1516027
  · exact B1516031
  · exact B1516035
  · exact B1516039
  · exact B1516043
  · exact B1516047
  · exact B1516051
  · exact B1516055
  · exact B1516059
  · exact B1516063
  · exact B1516067
  · exact B1516071
  · exact B1516075
  · exact B1516079
  · exact B1516083
  · exact B1516087
  · exact B1516091
  · exact B1516095
  · exact B1516099
  · exact B1516103
  · exact B1516107
  · exact B1516111
  · exact B1516115
  · exact B1516119
  · exact B1516123
  · exact B1516127
  · exact B1516131
  · exact B1516135
  · exact B1516139
  · exact B1516143
  · exact B1516147
  · exact B1516151
  · exact B1516155
  · exact B1516159
  · exact B1516163
  · exact B1516167
  · exact B1516171
  · exact B1516175
  · exact B1516179
  · exact B1516183
  · exact B1516187
  · exact B1516191
  · exact B1516195
  · exact B1516199
  · exact B1516203
  · exact B1516207
  · exact B1516211
  · exact B1516215
  · exact B1516219
  · exact B1516223
  · exact B1516227
  · exact B1516231
  · exact B1516235
  · exact B1516239
  · exact B1516243
  · exact B1516247
  · exact B1516251
  · exact B1516255
  · exact B1516259
  · exact B1516263
  · exact B1516267
  · exact B1516271
  · exact B1516275
  · exact B1516279
  · exact B1516283
  · exact B1516287
  · exact B1516291
  · exact B1516295
  · exact B1516299
  · exact B1516303
  · exact B1516307
  · exact B1516311
  · exact B1516315
  · exact B1516319
  · exact B1516323
  · exact B1516327
  · exact B1516331
  · exact B1516335
  · exact B1516339
  · exact B1516343
  · exact B1516347
  · exact B1516351
  · exact B1516355
  · exact B1516359
  · exact B1516363
  · exact B1516367
  · exact B1516371
  · exact B1516375
  · exact B1516379
  · exact B1516383
  · exact B1516387
  · exact B1516391
  · exact B1516395
  · exact B1516399
  · exact B1516403
  · exact B1516407
  · exact B1516411
  · exact B1516415
  · exact B1516419
  · exact B1516423
  · exact B1516427
  · exact B1516431
  · exact B1516435
  · exact B1516439
  · exact B1516443
  · exact B1516447
  · exact B1516451
  · exact B1516455
  · exact B1516459
  · exact B1516463
  · exact B1516467
  · exact B1516471
  · exact B1516475
  · exact B1516479
  · exact B1516483
  · exact B1516487
  · exact B1516491
  · exact B1516495
  · exact B1516499
  · exact B1516503
  · exact B1516507
  · exact B1516511
  · exact B1516515
  · exact B1516519
  · exact B1516523
  · exact B1516527
  · exact B1516531
  · exact B1516535
  · exact B1516539
  · exact B1516543
  · exact B1516547
  · exact B1516551
  · exact B1516555
  · exact B1516559
  · exact B1516563
  · exact B1516567
  · exact B1516571
  · exact B1516575
  · exact B1516579
  · exact B1516583
  · exact B1516587
  · exact B1516591
  · exact B1516595
  · exact B1516599
  · exact B1516603
  · exact B1516607
  · exact B1516611
  · exact B1516615
  · exact B1516619
  · exact B1516623
  · exact B1516627
  · exact B1516631
  · exact B1516635
  · exact B1516639
  · exact B1516643
  · exact B1516647
  · exact B1516651
  · exact B1516655
  · exact B1516659
  · exact B1516663
  · exact B1516667
  · exact B1516671
  · exact B1516675
  · exact B1516679
  · exact B1516683
  · exact B1516687
  · exact B1516691
  · exact B1516695
  · exact B1516699
  · exact B1516703
  · exact B1516707
  · exact B1516711
  · exact B1516715
  · exact B1516719
  · exact B1516723
  · exact B1516727
  · exact B1516731
  · exact B1516735
  · exact B1516739
  · exact B1516743
  · exact B1516747
  · exact B1516751
  · exact B1516755
  · exact B1516759
  · exact B1516763
  · exact B1516767
  · exact B1516771
  · exact B1516775
  · exact B1516779
  · exact B1516783
  · exact B1516787
  · exact B1516791
  · exact B1516795
  · exact B1516799
  · exact B1516803
  · exact B1516807
  · exact B1516811
  · exact B1516815
  · exact B1516819
  · exact B1516823
  · exact B1516827
  · exact B1516831
  · exact B1516835
  · exact B1516839
  · exact B1516843
  · exact B1516847
  · exact B1516851
  · exact B1516855
  · exact B1516859
  · exact B1516863
  · exact B1516867
  · exact B1516871
  · exact B1516875
  · exact B1516879
  · exact B1516883
  · exact B1516887
  · exact B1516891
  · exact B1516895
  · exact B1516899
  · exact B1516903
  · exact B1516907
  · exact B1516911
  · exact B1516915
  · exact B1516919
  · exact B1516923
  · exact B1516927
  · exact B1516931
  · exact B1516935
  · exact B1516939
  · exact B1516943
  · exact B1516947
  · exact B1516951

theorem solution (m : ℕ) (hlo : 1514954 ≤ m) (hhi : m ≤ 1516954) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 378738 ≤ j := by omega
    have hj2 : j ≤ 379237 := by omega
    have hb : Blo 1514954 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
