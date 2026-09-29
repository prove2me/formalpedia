-- Prove2me | solution 1 for syracuse_descends_range_1817610_1819610
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:55:35.729933+00:00
-- url     : https://prove2.me/submissions/08bdba09-b864-48ad-9376-f53d726d04a2

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


theorem B2727941 : Blo 1817610 2727941 := bbase (se 4 (by rfl) ⟨255744, by rfl⟩ : syracuseStep 2727941 = 511489) (by norm_num)
theorem B2727965 : Blo 1817610 2727965 := bbase (se 3 (by rfl) ⟨511493, by rfl⟩ : syracuseStep 2727965 = 1022987) (by norm_num)
theorem B4603949 : Blo 1817610 4603949 := bbase (se 3 (by rfl) ⟨863240, by rfl⟩ : syracuseStep 4603949 = 1726481) (by norm_num)
theorem B2727989 : Blo 1817610 2727989 := bbase (se 5 (by rfl) ⟨127874, by rfl⟩ : syracuseStep 2727989 = 255749) (by norm_num)
theorem B2490437 : Blo 1817610 2490437 := bbase (se 4 (by rfl) ⟨233478, by rfl⟩ : syracuseStep 2490437 = 466957) (by norm_num)
theorem B2728013 : Blo 1817610 2728013 := bbase (se 3 (by rfl) ⟨511502, by rfl⟩ : syracuseStep 2728013 = 1023005) (by norm_num)
theorem B29491285 : Blo 1817610 29491285 := bbase (se 8 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 29491285 = 345601) (by norm_num)
theorem B3686485 : Blo 1817610 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B1867865 : Blo 1817610 1867865 := bbase (se 2 (by rfl) ⟨700449, by rfl⟩ : syracuseStep 1867865 = 1400899) (by norm_num)
theorem B2728037 : Blo 1817610 2728037 := bbase (se 4 (by rfl) ⟨255753, by rfl⟩ : syracuseStep 2728037 = 511507) (by norm_num)
theorem B1941629 : Blo 1817610 1941629 := bbase (se 3 (by rfl) ⟨364055, by rfl⟩ : syracuseStep 1941629 = 728111) (by norm_num)
theorem B2728061 : Blo 1817610 2728061 := bbase (se 3 (by rfl) ⟨511511, by rfl⟩ : syracuseStep 2728061 = 1023023) (by norm_num)
theorem B2728085 : Blo 1817610 2728085 := bbase (se 6 (by rfl) ⟨63939, by rfl⟩ : syracuseStep 2728085 = 127879) (by norm_num)
theorem B2302121 : Blo 1817610 2302121 := bbase (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) (by norm_num)
theorem B2728109 : Blo 1817610 2728109 := bbase (se 3 (by rfl) ⟨511520, by rfl⟩ : syracuseStep 2728109 = 1023041) (by norm_num)
theorem B1941689 : Blo 1817610 1941689 := bbase (se 2 (by rfl) ⟨728133, by rfl⟩ : syracuseStep 1941689 = 1456267) (by norm_num)
theorem B2728133 : Blo 1817610 2728133 := bbase (se 4 (by rfl) ⟨255762, by rfl⟩ : syracuseStep 2728133 = 511525) (by norm_num)
theorem B2728157 : Blo 1817610 2728157 := bbase (se 3 (by rfl) ⟨511529, by rfl⟩ : syracuseStep 2728157 = 1023059) (by norm_num)
theorem B2302177 : Blo 1817610 2302177 := bbase (se 2 (by rfl) ⟨863316, by rfl⟩ : syracuseStep 2302177 = 1726633) (by norm_num)
theorem B4604141 : Blo 1817610 4604141 := bbase (se 3 (by rfl) ⟨863276, by rfl⟩ : syracuseStep 4604141 = 1726553) (by norm_num)
theorem B2728181 : Blo 1817610 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B2728205 : Blo 1817610 2728205 := bbase (se 3 (by rfl) ⟨511538, by rfl⟩ : syracuseStep 2728205 = 1023077) (by norm_num)
theorem B5177621 : Blo 1817610 5177621 := bbase (se 6 (by rfl) ⟨121350, by rfl⟩ : syracuseStep 5177621 = 242701) (by norm_num)
theorem B2728229 : Blo 1817610 2728229 := bbase (se 4 (by rfl) ⟨255771, by rfl⟩ : syracuseStep 2728229 = 511543) (by norm_num)
theorem B1941817 : Blo 1817610 1941817 := bbase (se 2 (by rfl) ⟨728181, by rfl⟩ : syracuseStep 1941817 = 1456363) (by norm_num)
theorem B2728253 : Blo 1817610 2728253 := bbase (se 3 (by rfl) ⟨511547, by rfl⟩ : syracuseStep 2728253 = 1023095) (by norm_num)
theorem B2302273 : Blo 1817610 2302273 := bbase (se 2 (by rfl) ⟨863352, by rfl⟩ : syracuseStep 2302273 = 1726705) (by norm_num)
theorem B6906181 : Blo 1817610 6906181 := bbase (se 4 (by rfl) ⟨647454, by rfl⟩ : syracuseStep 6906181 = 1294909) (by norm_num)
theorem B11649365 : Blo 1817610 11649365 := bbase (se 10 (by rfl) ⟨17064, by rfl⟩ : syracuseStep 11649365 = 34129) (by norm_num)
theorem B2728277 : Blo 1817610 2728277 := bbase (se 10 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 2728277 = 7993) (by norm_num)
theorem B2728301 : Blo 1817610 2728301 := bbase (se 3 (by rfl) ⟨511556, by rfl⟩ : syracuseStep 2728301 = 1023113) (by norm_num)
theorem B6136181 : Blo 1817610 6136181 := bbase (se 5 (by rfl) ⟨287633, by rfl⟩ : syracuseStep 6136181 = 575267) (by norm_num)
theorem B2728325 : Blo 1817610 2728325 := bbase (se 4 (by rfl) ⟨255780, by rfl⟩ : syracuseStep 2728325 = 511561) (by norm_num)
theorem B2728349 : Blo 1817610 2728349 := bbase (se 3 (by rfl) ⟨511565, by rfl⟩ : syracuseStep 2728349 = 1023131) (by norm_num)
theorem B2728373 : Blo 1817610 2728373 := bbase (se 5 (by rfl) ⟨127892, by rfl⟩ : syracuseStep 2728373 = 255785) (by norm_num)
theorem B2728397 : Blo 1817610 2728397 := bbase (se 3 (by rfl) ⟨511574, by rfl⟩ : syracuseStep 2728397 = 1023149) (by norm_num)
theorem B2728421 : Blo 1817610 2728421 := bbase (se 4 (by rfl) ⟨255789, by rfl⟩ : syracuseStep 2728421 = 511579) (by norm_num)
theorem B2302445 : Blo 1817610 2302445 := bbase (se 3 (by rfl) ⟨431708, by rfl⟩ : syracuseStep 2302445 = 863417) (by norm_num)
theorem B2728445 : Blo 1817610 2728445 := bbase (se 3 (by rfl) ⟨511583, by rfl⟩ : syracuseStep 2728445 = 1023167) (by norm_num)
theorem B5825029 : Blo 1817610 5825029 := bbase (se 4 (by rfl) ⟨546096, by rfl⟩ : syracuseStep 5825029 = 1092193) (by norm_num)
theorem B2728469 : Blo 1817610 2728469 := bbase (se 6 (by rfl) ⟨63948, by rfl⟩ : syracuseStep 2728469 = 127897) (by norm_num)
theorem B2302501 : Blo 1817610 2302501 := bbase (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) (by norm_num)
theorem B2728493 : Blo 1817610 2728493 := bbase (se 3 (by rfl) ⟨511592, by rfl⟩ : syracuseStep 2728493 = 1023185) (by norm_num)
theorem B2728517 : Blo 1817610 2728517 := bbase (se 4 (by rfl) ⟨255798, by rfl⟩ : syracuseStep 2728517 = 511597) (by norm_num)
theorem B4604485 : Blo 1817610 4604485 := bbase (se 4 (by rfl) ⟨431670, by rfl⟩ : syracuseStep 4604485 = 863341) (by norm_num)
theorem B2728541 : Blo 1817610 2728541 := bbase (se 3 (by rfl) ⟨511601, by rfl⟩ : syracuseStep 2728541 = 1023203) (by norm_num)
theorem B6906485 : Blo 1817610 6906485 := bbase (se 5 (by rfl) ⟨323741, by rfl⟩ : syracuseStep 6906485 = 647483) (by norm_num)
theorem B2728565 : Blo 1817610 2728565 := bbase (se 5 (by rfl) ⟨127901, by rfl⟩ : syracuseStep 2728565 = 255803) (by norm_num)
theorem B2073209 : Blo 1817610 2073209 := bbase (se 2 (by rfl) ⟨777453, by rfl⟩ : syracuseStep 2073209 = 1554907) (by norm_num)
theorem B2302597 : Blo 1817610 2302597 := bbase (se 4 (by rfl) ⟨215868, by rfl⟩ : syracuseStep 2302597 = 431737) (by norm_num)
theorem B2728589 : Blo 1817610 2728589 := bbase (se 3 (by rfl) ⟨511610, by rfl⟩ : syracuseStep 2728589 = 1023221) (by norm_num)
theorem B2728613 : Blo 1817610 2728613 := bbase (se 4 (by rfl) ⟨255807, by rfl⟩ : syracuseStep 2728613 = 511615) (by norm_num)
theorem B4604597 : Blo 1817610 4604597 := bbase (se 5 (by rfl) ⟨215840, by rfl⟩ : syracuseStep 4604597 = 431681) (by norm_num)
theorem B2728637 : Blo 1817610 2728637 := bbase (se 3 (by rfl) ⟨511619, by rfl⟩ : syracuseStep 2728637 = 1023239) (by norm_num)
theorem B2728661 : Blo 1817610 2728661 := bbase (se 7 (by rfl) ⟨31976, by rfl⟩ : syracuseStep 2728661 = 63953) (by norm_num)
theorem B3687133 : Blo 1817610 3687133 := bbase (se 3 (by rfl) ⟨691337, by rfl⟩ : syracuseStep 3687133 = 1382675) (by norm_num)
theorem B2728685 : Blo 1817610 2728685 := bbase (se 3 (by rfl) ⟨511628, by rfl⟩ : syracuseStep 2728685 = 1023257) (by norm_num)
theorem B1942261 : Blo 1817610 1942261 := bbase (se 5 (by rfl) ⟨91043, by rfl⟩ : syracuseStep 1942261 = 182087) (by norm_num)
theorem B9208565 : Blo 1817610 9208565 := bbase (se 5 (by rfl) ⟨431651, by rfl⟩ : syracuseStep 9208565 = 863303) (by norm_num)
theorem B2728709 : Blo 1817610 2728709 := bbase (se 4 (by rfl) ⟨255816, by rfl⟩ : syracuseStep 2728709 = 511633) (by norm_num)
theorem B3883805 : Blo 1817610 3883805 := bbase (se 3 (by rfl) ⟨728213, by rfl⟩ : syracuseStep 3883805 = 1456427) (by norm_num)
theorem B2728733 : Blo 1817610 2728733 := bbase (se 3 (by rfl) ⟨511637, by rfl⟩ : syracuseStep 2728733 = 1023275) (by norm_num)
theorem B6136613 : Blo 1817610 6136613 := bbase (se 4 (by rfl) ⟨575307, by rfl⟩ : syracuseStep 6136613 = 1150615) (by norm_num)
theorem B2302769 : Blo 1817610 2302769 := bbase (se 2 (by rfl) ⟨863538, by rfl⟩ : syracuseStep 2302769 = 1727077) (by norm_num)
theorem B2728757 : Blo 1817610 2728757 := bbase (se 5 (by rfl) ⟨127910, by rfl⟩ : syracuseStep 2728757 = 255821) (by norm_num)
theorem B2728781 : Blo 1817610 2728781 := bbase (se 3 (by rfl) ⟨511646, by rfl⟩ : syracuseStep 2728781 = 1023293) (by norm_num)
theorem B19653461 : Blo 1817610 19653461 := bbase (se 9 (by rfl) ⟨57578, by rfl⟩ : syracuseStep 19653461 = 115157) (by norm_num)
theorem B2728805 : Blo 1817610 2728805 := bbase (se 4 (by rfl) ⟨255825, by rfl⟩ : syracuseStep 2728805 = 511651) (by norm_num)
theorem B2302825 : Blo 1817610 2302825 := bbase (se 2 (by rfl) ⟨863559, by rfl⟩ : syracuseStep 2302825 = 1727119) (by norm_num)
theorem B1942381 : Blo 1817610 1942381 := bbase (se 3 (by rfl) ⟨364196, by rfl⟩ : syracuseStep 1942381 = 728393) (by norm_num)
theorem B4604789 : Blo 1817610 4604789 := bbase (se 5 (by rfl) ⟨215849, by rfl⟩ : syracuseStep 4604789 = 431699) (by norm_num)
theorem B2728829 : Blo 1817610 2728829 := bbase (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) (by norm_num)
theorem B3883925 : Blo 1817610 3883925 := bbase (se 6 (by rfl) ⟨91029, by rfl⟩ : syracuseStep 3883925 = 182059) (by norm_num)
theorem B2728853 : Blo 1817610 2728853 := bbase (se 6 (by rfl) ⟨63957, by rfl⟩ : syracuseStep 2728853 = 127915) (by norm_num)
theorem B2728877 : Blo 1817610 2728877 := bbase (se 3 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 2728877 = 1023329) (by norm_num)
theorem B5178293 : Blo 1817610 5178293 := bbase (se 5 (by rfl) ⟨242732, by rfl⟩ : syracuseStep 5178293 = 485465) (by norm_num)
theorem B2728901 : Blo 1817610 2728901 := bbase (se 4 (by rfl) ⟨255834, by rfl⟩ : syracuseStep 2728901 = 511669) (by norm_num)
theorem B2302921 : Blo 1817610 2302921 := bbase (se 2 (by rfl) ⟨863595, by rfl⟩ : syracuseStep 2302921 = 1727191) (by norm_num)
theorem B2728925 : Blo 1817610 2728925 := bbase (se 3 (by rfl) ⟨511673, by rfl⟩ : syracuseStep 2728925 = 1023347) (by norm_num)
theorem B7767029 : Blo 1817610 7767029 := bbase (se 5 (by rfl) ⟨364079, by rfl⟩ : syracuseStep 7767029 = 728159) (by norm_num)
theorem B2728949 : Blo 1817610 2728949 := bbase (se 5 (by rfl) ⟨127919, by rfl⟩ : syracuseStep 2728949 = 255839) (by norm_num)
theorem B2728973 : Blo 1817610 2728973 := bbase (se 3 (by rfl) ⟨511682, by rfl⟩ : syracuseStep 2728973 = 1023365) (by norm_num)
theorem B7373861 : Blo 1817610 7373861 := bbase (se 4 (by rfl) ⟨691299, by rfl⟩ : syracuseStep 7373861 = 1382599) (by norm_num)
theorem B2728997 : Blo 1817610 2728997 := bbase (se 4 (by rfl) ⟨255843, by rfl⟩ : syracuseStep 2728997 = 511687) (by norm_num)
theorem B2729021 : Blo 1817610 2729021 := bbase (se 3 (by rfl) ⟨511691, by rfl⟩ : syracuseStep 2729021 = 1023383) (by norm_num)
theorem B2729045 : Blo 1817610 2729045 := bbase (se 8 (by rfl) ⟨15990, by rfl⟩ : syracuseStep 2729045 = 31981) (by norm_num)
theorem B1942633 : Blo 1817610 1942633 := bbase (se 2 (by rfl) ⟨728487, by rfl⟩ : syracuseStep 1942633 = 1456975) (by norm_num)
theorem B1942637 : Blo 1817610 1942637 := bbase (se 3 (by rfl) ⟨364244, by rfl⟩ : syracuseStep 1942637 = 728489) (by norm_num)
theorem B2729069 : Blo 1817610 2729069 := bbase (se 3 (by rfl) ⟨511700, by rfl⟩ : syracuseStep 2729069 = 1023401) (by norm_num)
theorem B2729093 : Blo 1817610 2729093 := bbase (se 4 (by rfl) ⟨255852, by rfl⟩ : syracuseStep 2729093 = 511705) (by norm_num)
theorem B6554773 : Blo 1817610 6554773 := bbase (se 6 (by rfl) ⟨153627, by rfl⟩ : syracuseStep 6554773 = 307255) (by norm_num)
theorem B2729117 : Blo 1817610 2729117 := bbase (se 3 (by rfl) ⟨511709, by rfl⟩ : syracuseStep 2729117 = 1023419) (by norm_num)
theorem B2729141 : Blo 1817610 2729141 := bbase (se 5 (by rfl) ⟨127928, by rfl⟩ : syracuseStep 2729141 = 255857) (by norm_num)
theorem B4605133 : Blo 1817610 4605133 := bbase (se 3 (by rfl) ⟨863462, by rfl⟩ : syracuseStep 4605133 = 1726925) (by norm_num)
theorem B2729165 : Blo 1817610 2729165 := bbase (se 3 (by rfl) ⟨511718, by rfl⟩ : syracuseStep 2729165 = 1023437) (by norm_num)
theorem B6137045 : Blo 1817610 6137045 := bbase (se 7 (by rfl) ⟨71918, by rfl⟩ : syracuseStep 6137045 = 143837) (by norm_num)
theorem B2729189 : Blo 1817610 2729189 := bbase (se 4 (by rfl) ⟨255861, by rfl⟩ : syracuseStep 2729189 = 511723) (by norm_num)
theorem B2729213 : Blo 1817610 2729213 := bbase (se 3 (by rfl) ⟨511727, by rfl⟩ : syracuseStep 2729213 = 1023455) (by norm_num)
theorem B2729237 : Blo 1817610 2729237 := bbase (se 6 (by rfl) ⟨63966, by rfl⟩ : syracuseStep 2729237 = 127933) (by norm_num)
theorem B2729261 : Blo 1817610 2729261 := bbase (se 3 (by rfl) ⟨511736, by rfl⟩ : syracuseStep 2729261 = 1023473) (by norm_num)
theorem B4605245 : Blo 1817610 4605245 := bbase (se 3 (by rfl) ⟨863483, by rfl⟩ : syracuseStep 4605245 = 1726967) (by norm_num)
theorem B5825861 : Blo 1817610 5825861 := bbase (se 4 (by rfl) ⟨546174, by rfl⟩ : syracuseStep 5825861 = 1092349) (by norm_num)
theorem B2729285 : Blo 1817610 2729285 := bbase (se 4 (by rfl) ⟨255870, by rfl⟩ : syracuseStep 2729285 = 511741) (by norm_num)
theorem B3499357 : Blo 1817610 3499357 := bbase (se 3 (by rfl) ⟨656129, by rfl⟩ : syracuseStep 3499357 = 1312259) (by norm_num)
theorem B2729309 : Blo 1817610 2729309 := bbase (se 3 (by rfl) ⟨511745, by rfl⟩ : syracuseStep 2729309 = 1023491) (by norm_num)
theorem B5178725 : Blo 1817610 5178725 := bbase (se 4 (by rfl) ⟨485505, by rfl⟩ : syracuseStep 5178725 = 971011) (by norm_num)
theorem B3687781 : Blo 1817610 3687781 := bbase (se 4 (by rfl) ⟨345729, by rfl⟩ : syracuseStep 3687781 = 691459) (by norm_num)
theorem B2590069 : Blo 1817610 2590069 := bbase (se 5 (by rfl) ⟨121409, by rfl⟩ : syracuseStep 2590069 = 242819) (by norm_num)
theorem B5907829 : Blo 1817610 5907829 := bbase (se 5 (by rfl) ⟨276929, by rfl⟩ : syracuseStep 5907829 = 553859) (by norm_num)
theorem B2729333 : Blo 1817610 2729333 := bbase (se 5 (by rfl) ⟨127937, by rfl⟩ : syracuseStep 2729333 = 255875) (by norm_num)
theorem B2729357 : Blo 1817610 2729357 := bbase (se 3 (by rfl) ⟨511754, by rfl⟩ : syracuseStep 2729357 = 1023509) (by norm_num)
theorem B4367773 : Blo 1817610 4367773 := bbase (se 3 (by rfl) ⟨818957, by rfl⟩ : syracuseStep 4367773 = 1637915) (by norm_num)
theorem B2729381 : Blo 1817610 2729381 := bbase (se 4 (by rfl) ⟨255879, by rfl⟩ : syracuseStep 2729381 = 511759) (by norm_num)
theorem B2729405 : Blo 1817610 2729405 := bbase (se 3 (by rfl) ⟨511763, by rfl⟩ : syracuseStep 2729405 = 1023527) (by norm_num)
theorem B1967557 : Blo 1817610 1967557 := bbase (se 4 (by rfl) ⟨184458, by rfl⟩ : syracuseStep 1967557 = 368917) (by norm_num)
theorem B4605437 : Blo 1817610 4605437 := bbase (se 3 (by rfl) ⟨863519, by rfl⟩ : syracuseStep 4605437 = 1727039) (by norm_num)
theorem B3884557 : Blo 1817610 3884557 := bbase (se 3 (by rfl) ⟨728354, by rfl⟩ : syracuseStep 3884557 = 1456709) (by norm_num)
theorem B30721621 : Blo 1817610 30721621 := bbase (se 8 (by rfl) ⟨180009, by rfl⟩ : syracuseStep 30721621 = 360019) (by norm_num)
theorem B3499645 : Blo 1817610 3499645 := bbase (se 3 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 3499645 = 1312367) (by norm_num)
theorem B6137477 : Blo 1817610 6137477 := bbase (se 4 (by rfl) ⟨575388, by rfl⟩ : syracuseStep 6137477 = 1150777) (by norm_num)
theorem B4089653 : Blo 1817610 4089653 := bbase (se 5 (by rfl) ⟨191702, by rfl⟩ : syracuseStep 4089653 = 383405) (by norm_num)
theorem B3737405 : Blo 1817610 3737405 := bbase (se 3 (by rfl) ⟨700763, by rfl⟩ : syracuseStep 3737405 = 1401527) (by norm_num)
theorem B4605781 : Blo 1817610 4605781 := bbase (se 9 (by rfl) ⟨13493, by rfl⟩ : syracuseStep 4605781 = 26987) (by norm_num)
theorem B4089725 : Blo 1817610 4089725 := bbase (se 3 (by rfl) ⟨766823, by rfl⟩ : syracuseStep 4089725 = 1533647) (by norm_num)
theorem B2074505 : Blo 1817610 2074505 := bbase (se 2 (by rfl) ⟨777939, by rfl⟩ : syracuseStep 2074505 = 1555879) (by norm_num)
theorem B4089797 : Blo 1817610 4089797 := bbase (se 4 (by rfl) ⟨383418, by rfl⟩ : syracuseStep 4089797 = 766837) (by norm_num)
theorem B2590661 : Blo 1817610 2590661 := bbase (se 4 (by rfl) ⟨242874, by rfl⟩ : syracuseStep 2590661 = 485749) (by norm_num)
theorem B9209861 : Blo 1817610 9209861 := bbase (se 4 (by rfl) ⟨863424, by rfl⟩ : syracuseStep 9209861 = 1726849) (by norm_num)
theorem B4089869 : Blo 1817610 4089869 := bbase (se 3 (by rfl) ⟨766850, by rfl⟩ : syracuseStep 4089869 = 1533701) (by norm_num)
theorem B20719637 : Blo 1817610 20719637 := bbase (se 6 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 20719637 = 971233) (by norm_num)
theorem B2590741 : Blo 1817610 2590741 := bbase (se 6 (by rfl) ⟨60720, by rfl⟩ : syracuseStep 2590741 = 121441) (by norm_num)
theorem B3278893 : Blo 1817610 3278893 := bbase (se 3 (by rfl) ⟨614792, by rfl⟩ : syracuseStep 3278893 = 1229585) (by norm_num)
theorem B6137909 : Blo 1817610 6137909 := bbase (se 5 (by rfl) ⟨287714, by rfl⟩ : syracuseStep 6137909 = 575429) (by norm_num)
theorem B4089941 : Blo 1817610 4089941 := bbase (se 8 (by rfl) ⟨23964, by rfl⟩ : syracuseStep 4089941 = 47929) (by norm_num)
theorem B5179477 : Blo 1817610 5179477 := bbase (se 8 (by rfl) ⟨30348, by rfl⟩ : syracuseStep 5179477 = 60697) (by norm_num)
theorem B4090013 : Blo 1817610 4090013 := bbase (se 3 (by rfl) ⟨766877, by rfl⟩ : syracuseStep 4090013 = 1533755) (by norm_num)
theorem B2074825 : Blo 1817610 2074825 := bbase (se 2 (by rfl) ⟨778059, by rfl⟩ : syracuseStep 2074825 = 1556119) (by norm_num)
theorem B4090085 : Blo 1817610 4090085 := bbase (se 4 (by rfl) ⟨383445, by rfl⟩ : syracuseStep 4090085 = 766891) (by norm_num)
theorem B15747317 : Blo 1817610 15747317 := bbase (se 5 (by rfl) ⟨738155, by rfl⟩ : syracuseStep 15747317 = 1476311) (by norm_num)
theorem B4090157 : Blo 1817610 4090157 := bbase (se 3 (by rfl) ⟨766904, by rfl⟩ : syracuseStep 4090157 = 1533809) (by norm_num)
theorem B4262213 : Blo 1817610 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B4090229 : Blo 1817610 4090229 := bbase (se 5 (by rfl) ⟨191729, by rfl⟩ : syracuseStep 4090229 = 383459) (by norm_num)
theorem B3451261 : Blo 1817610 3451261 := bbase (se 3 (by rfl) ⟨647111, by rfl⟩ : syracuseStep 3451261 = 1294223) (by norm_num)
theorem B3885445 : Blo 1817610 3885445 := bbase (se 4 (by rfl) ⟨364260, by rfl⟩ : syracuseStep 3885445 = 728521) (by norm_num)
theorem B9202085 : Blo 1817610 9202085 := bbase (se 4 (by rfl) ⟨862695, by rfl⟩ : syracuseStep 9202085 = 1725391) (by norm_num)
theorem B8735141 : Blo 1817610 8735141 := bbase (se 4 (by rfl) ⟨818919, by rfl⟩ : syracuseStep 8735141 = 1637839) (by norm_num)
theorem B4090301 : Blo 1817610 4090301 := bbase (se 3 (by rfl) ⟨766931, by rfl⟩ : syracuseStep 4090301 = 1533863) (by norm_num)
theorem B6138341 : Blo 1817610 6138341 := bbase (se 4 (by rfl) ⟨575469, by rfl⟩ : syracuseStep 6138341 = 1150939) (by norm_num)
theorem B3885565 : Blo 1817610 3885565 := bbase (se 3 (by rfl) ⟨728543, by rfl⟩ : syracuseStep 3885565 = 1457087) (by norm_num)
theorem B4090373 : Blo 1817610 4090373 := bbase (se 4 (by rfl) ⟨383472, by rfl⟩ : syracuseStep 4090373 = 766945) (by norm_num)
theorem B3451405 : Blo 1817610 3451405 := bbase (se 3 (by rfl) ⟨647138, by rfl⟩ : syracuseStep 3451405 = 1294277) (by norm_num)
theorem B4090445 : Blo 1817610 4090445 := bbase (se 3 (by rfl) ⟨766958, by rfl⟩ : syracuseStep 4090445 = 1533917) (by norm_num)
theorem B4368973 : Blo 1817610 4368973 := bbase (se 3 (by rfl) ⟨819182, by rfl⟩ : syracuseStep 4368973 = 1638365) (by norm_num)
theorem B4147805 : Blo 1817610 4147805 := bbase (se 3 (by rfl) ⟨777713, by rfl⟩ : syracuseStep 4147805 = 1555427) (by norm_num)
theorem B4090517 : Blo 1817610 4090517 := bbase (se 6 (by rfl) ⟨95871, by rfl⟩ : syracuseStep 4090517 = 191743) (by norm_num)
theorem B3451565 : Blo 1817610 3451565 := bbase (se 3 (by rfl) ⟨647168, by rfl⟩ : syracuseStep 3451565 = 1294337) (by norm_num)
theorem B6908597 : Blo 1817610 6908597 := bbase (se 5 (by rfl) ⟨323840, by rfl⟩ : syracuseStep 6908597 = 647681) (by norm_num)
theorem B4090589 : Blo 1817610 4090589 := bbase (se 3 (by rfl) ⟨766985, by rfl⟩ : syracuseStep 4090589 = 1533971) (by norm_num)
theorem B3885821 : Blo 1817610 3885821 := bbase (se 3 (by rfl) ⟨728591, by rfl⟩ : syracuseStep 3885821 = 1457183) (by norm_num)
theorem B4983557 : Blo 1817610 4983557 := bbase (se 4 (by rfl) ⟨467208, by rfl⟩ : syracuseStep 4983557 = 934417) (by norm_num)
theorem B13814549 : Blo 1817610 13814549 := bbase (se 6 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 13814549 = 647557) (by norm_num)
theorem B4090661 : Blo 1817610 4090661 := bbase (se 4 (by rfl) ⟨383499, by rfl⟩ : syracuseStep 4090661 = 766999) (by norm_num)
theorem B3451709 : Blo 1817610 3451709 := bbase (se 3 (by rfl) ⟨647195, by rfl⟩ : syracuseStep 3451709 = 1294391) (by norm_num)
theorem B4090733 : Blo 1817610 4090733 := bbase (se 3 (by rfl) ⟨767012, by rfl⟩ : syracuseStep 4090733 = 1534025) (by norm_num)
theorem B6138773 : Blo 1817610 6138773 := bbase (se 6 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 6138773 = 287755) (by norm_num)
theorem B4090805 : Blo 1817610 4090805 := bbase (se 5 (by rfl) ⟨191756, by rfl⟩ : syracuseStep 4090805 = 383513) (by norm_num)
theorem B4090877 : Blo 1817610 4090877 := bbase (se 3 (by rfl) ⟨767039, by rfl⟩ : syracuseStep 4090877 = 1534079) (by norm_num)
theorem B4090949 : Blo 1817610 4090949 := bbase (se 4 (by rfl) ⟨383526, by rfl⟩ : syracuseStep 4090949 = 767053) (by norm_num)
theorem B4148309 : Blo 1817610 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B3451997 : Blo 1817610 3451997 := bbase (se 3 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 3451997 = 1294499) (by norm_num)
theorem B5049461 : Blo 1817610 5049461 := bbase (se 5 (by rfl) ⟨236693, by rfl⟩ : syracuseStep 5049461 = 473387) (by norm_num)
theorem B2051201 : Blo 1817610 2051201 := bbase (se 2 (by rfl) ⟨769200, by rfl⟩ : syracuseStep 2051201 = 1538401) (by norm_num)
theorem B4091021 : Blo 1817610 4091021 := bbase (se 3 (by rfl) ⟨767066, by rfl⟩ : syracuseStep 4091021 = 1534133) (by norm_num)
theorem B5827733 : Blo 1817610 5827733 := bbase (se 6 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 5827733 = 273175) (by norm_num)
theorem B4148381 : Blo 1817610 4148381 := bbase (se 3 (by rfl) ⟨777821, by rfl⟩ : syracuseStep 4148381 = 1555643) (by norm_num)
theorem B13806773 : Blo 1817610 13806773 := bbase (se 5 (by rfl) ⟨647192, by rfl⟩ : syracuseStep 13806773 = 1294385) (by norm_num)
theorem B4369589 : Blo 1817610 4369589 := bbase (se 5 (by rfl) ⟨204824, by rfl⟩ : syracuseStep 4369589 = 409649) (by norm_num)
theorem B4091093 : Blo 1817610 4091093 := bbase (se 7 (by rfl) ⟨47942, by rfl⟩ : syracuseStep 4091093 = 95885) (by norm_num)
theorem B3452149 : Blo 1817610 3452149 := bbase (se 5 (by rfl) ⟨161819, by rfl⟩ : syracuseStep 3452149 = 323639) (by norm_num)
theorem B9211157 : Blo 1817610 9211157 := bbase (se 6 (by rfl) ⟨215886, by rfl⟩ : syracuseStep 9211157 = 431773) (by norm_num)
theorem B2764061 : Blo 1817610 2764061 := bbase (se 3 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 2764061 = 1036523) (by norm_num)
theorem B4091165 : Blo 1817610 4091165 := bbase (se 3 (by rfl) ⟨767093, by rfl⟩ : syracuseStep 4091165 = 1534187) (by norm_num)
theorem B6139205 : Blo 1817610 6139205 := bbase (se 4 (by rfl) ⟨575550, by rfl⟩ : syracuseStep 6139205 = 1151101) (by norm_num)
theorem B7376197 : Blo 1817610 7376197 := bbase (se 4 (by rfl) ⟨691518, by rfl⟩ : syracuseStep 7376197 = 1383037) (by norm_num)
theorem B4091237 : Blo 1817610 4091237 := bbase (se 4 (by rfl) ⟨383553, by rfl⟩ : syracuseStep 4091237 = 767107) (by norm_num)
theorem B4369781 : Blo 1817610 4369781 := bbase (se 5 (by rfl) ⟨204833, by rfl⟩ : syracuseStep 4369781 = 409667) (by norm_num)
theorem B3067301 : Blo 1817610 3067301 := bbase (se 4 (by rfl) ⟨287559, by rfl⟩ : syracuseStep 3067301 = 575119) (by norm_num)
theorem B4091309 : Blo 1817610 4091309 := bbase (se 3 (by rfl) ⟨767120, by rfl⟩ : syracuseStep 4091309 = 1534241) (by norm_num)
theorem B4369877 : Blo 1817610 4369877 := bbase (se 7 (by rfl) ⟨51209, by rfl⟩ : syracuseStep 4369877 = 102419) (by norm_num)
theorem B4091381 : Blo 1817610 4091381 := bbase (se 5 (by rfl) ⟨191783, by rfl⟩ : syracuseStep 4091381 = 383567) (by norm_num)
theorem B3067429 : Blo 1817610 3067429 := bbase (se 4 (by rfl) ⟨287571, by rfl⟩ : syracuseStep 3067429 = 575143) (by norm_num)
theorem B3452453 : Blo 1817610 3452453 := bbase (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) (by norm_num)
theorem B4091453 : Blo 1817610 4091453 := bbase (se 3 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 4091453 = 1534295) (by norm_num)
theorem B3067517 : Blo 1817610 3067517 := bbase (se 3 (by rfl) ⟨575159, by rfl⟩ : syracuseStep 3067517 = 1150319) (by norm_num)
theorem B4091525 : Blo 1817610 4091525 := bbase (se 4 (by rfl) ⟨383580, by rfl⟩ : syracuseStep 4091525 = 767161) (by norm_num)
theorem B9203381 : Blo 1817610 9203381 := bbase (se 5 (by rfl) ⟨431408, by rfl⟩ : syracuseStep 9203381 = 862817) (by norm_num)
theorem B4091597 : Blo 1817610 4091597 := bbase (se 3 (by rfl) ⟨767174, by rfl⟩ : syracuseStep 4091597 = 1534349) (by norm_num)
theorem B17051381 : Blo 1817610 17051381 := bbase (se 5 (by rfl) ⟨799283, by rfl⟩ : syracuseStep 17051381 = 1598567) (by norm_num)
theorem B6139637 : Blo 1817610 6139637 := bbase (se 5 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 6139637 = 575591) (by norm_num)
theorem B3067645 : Blo 1817610 3067645 := bbase (se 3 (by rfl) ⟨575183, by rfl⟩ : syracuseStep 3067645 = 1150367) (by norm_num)
theorem B4091669 : Blo 1817610 4091669 := bbase (se 6 (by rfl) ⟨95898, by rfl⟩ : syracuseStep 4091669 = 191797) (by norm_num)
theorem B3067733 : Blo 1817610 3067733 := bbase (se 9 (by rfl) ⟨8987, by rfl⟩ : syracuseStep 3067733 = 17975) (by norm_num)
theorem B4091741 : Blo 1817610 4091741 := bbase (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) (by norm_num)
theorem B2764693 : Blo 1817610 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B4091813 : Blo 1817610 4091813 := bbase (se 4 (by rfl) ⟨383607, by rfl⟩ : syracuseStep 4091813 = 767215) (by norm_num)
theorem B6221765 : Blo 1817610 6221765 := bbase (se 4 (by rfl) ⟨583290, by rfl⟩ : syracuseStep 6221765 = 1166581) (by norm_num)
theorem B3067861 : Blo 1817610 3067861 := bbase (se 7 (by rfl) ⟨35951, by rfl⟩ : syracuseStep 3067861 = 71903) (by norm_num)
theorem B2912213 : Blo 1817610 2912213 := bbase (se 7 (by rfl) ⟨34127, by rfl⟩ : syracuseStep 2912213 = 68255) (by norm_num)
theorem B2764765 : Blo 1817610 2764765 := bbase (se 3 (by rfl) ⟨518393, by rfl⟩ : syracuseStep 2764765 = 1036787) (by norm_num)
theorem B6557669 : Blo 1817610 6557669 := bbase (se 4 (by rfl) ⟨614781, by rfl⟩ : syracuseStep 6557669 = 1229563) (by norm_num)
theorem B4091885 : Blo 1817610 4091885 := bbase (se 3 (by rfl) ⟨767228, by rfl⟩ : syracuseStep 4091885 = 1534457) (by norm_num)
theorem B5246981 : Blo 1817610 5246981 := bbase (se 4 (by rfl) ⟨491904, by rfl⟩ : syracuseStep 5246981 = 983809) (by norm_num)
theorem B3067949 : Blo 1817610 3067949 := bbase (se 3 (by rfl) ⟨575240, by rfl⟩ : syracuseStep 3067949 = 1150481) (by norm_num)
theorem B11808821 : Blo 1817610 11808821 := bbase (se 5 (by rfl) ⟨553538, by rfl⟩ : syracuseStep 11808821 = 1107077) (by norm_num)
theorem B4091957 : Blo 1817610 4091957 := bbase (se 5 (by rfl) ⟨191810, by rfl⟩ : syracuseStep 4091957 = 383621) (by norm_num)
theorem B4092029 : Blo 1817610 4092029 := bbase (se 3 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 4092029 = 1534511) (by norm_num)
theorem B6140069 : Blo 1817610 6140069 := bbase (se 4 (by rfl) ⟨575631, by rfl⟩ : syracuseStep 6140069 = 1151263) (by norm_num)
theorem B3068077 : Blo 1817610 3068077 := bbase (se 3 (by rfl) ⟨575264, by rfl⟩ : syracuseStep 3068077 = 1150529) (by norm_num)
theorem B4092101 : Blo 1817610 4092101 := bbase (se 4 (by rfl) ⟨383634, by rfl⟩ : syracuseStep 4092101 = 767269) (by norm_num)
theorem B3068165 : Blo 1817610 3068165 := bbase (se 4 (by rfl) ⟨287640, by rfl⟩ : syracuseStep 3068165 = 575281) (by norm_num)
theorem B4092173 : Blo 1817610 4092173 := bbase (se 3 (by rfl) ⟨767282, by rfl⟩ : syracuseStep 4092173 = 1534565) (by norm_num)
theorem B3453205 : Blo 1817610 3453205 := bbase (se 6 (by rfl) ⟨80934, by rfl⟩ : syracuseStep 3453205 = 161869) (by norm_num)
theorem B4092245 : Blo 1817610 4092245 := bbase (se 10 (by rfl) ⟨5994, by rfl⟩ : syracuseStep 4092245 = 11989) (by norm_num)
theorem B3068293 : Blo 1817610 3068293 := bbase (se 4 (by rfl) ⟨287652, by rfl⟩ : syracuseStep 3068293 = 575305) (by norm_num)
theorem B2912669 : Blo 1817610 2912669 := bbase (se 3 (by rfl) ⟨546125, by rfl⟩ : syracuseStep 2912669 = 1092251) (by norm_num)
theorem B4092317 : Blo 1817610 4092317 := bbase (se 3 (by rfl) ⟨767309, by rfl⟩ : syracuseStep 4092317 = 1534619) (by norm_num)
theorem B3453349 : Blo 1817610 3453349 := bbase (se 4 (by rfl) ⟨323751, by rfl⟩ : syracuseStep 3453349 = 647503) (by norm_num)
theorem B2183617 : Blo 1817610 2183617 := bbase (se 2 (by rfl) ⟨818856, by rfl⟩ : syracuseStep 2183617 = 1637713) (by norm_num)
theorem B3068381 : Blo 1817610 3068381 := bbase (se 3 (by rfl) ⟨575321, by rfl⟩ : syracuseStep 3068381 = 1150643) (by norm_num)
theorem B7188965 : Blo 1817610 7188965 := bbase (se 4 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 7188965 = 1347931) (by norm_num)
theorem B4092389 : Blo 1817610 4092389 := bbase (se 4 (by rfl) ⟨383661, by rfl⟩ : syracuseStep 4092389 = 767323) (by norm_num)
theorem B6902293 : Blo 1817610 6902293 := bbase (se 6 (by rfl) ⟨161772, by rfl⟩ : syracuseStep 6902293 = 323545) (by norm_num)
theorem B4092461 : Blo 1817610 4092461 := bbase (se 3 (by rfl) ⟨767336, by rfl⟩ : syracuseStep 4092461 = 1534673) (by norm_num)
theorem B3453509 : Blo 1817610 3453509 := bbase (se 4 (by rfl) ⟨323766, by rfl⟩ : syracuseStep 3453509 = 647533) (by norm_num)
theorem B6140501 : Blo 1817610 6140501 := bbase (se 8 (by rfl) ⟨35979, by rfl⟩ : syracuseStep 6140501 = 71959) (by norm_num)
theorem B3068509 : Blo 1817610 3068509 := bbase (se 3 (by rfl) ⟨575345, by rfl⟩ : syracuseStep 3068509 = 1150691) (by norm_num)
theorem B4092533 : Blo 1817610 4092533 := bbase (se 5 (by rfl) ⟨191837, by rfl⟩ : syracuseStep 4092533 = 383675) (by norm_num)
theorem B3068597 : Blo 1817610 3068597 := bbase (se 5 (by rfl) ⟨143840, by rfl⟩ : syracuseStep 3068597 = 287681) (by norm_num)
theorem B4092605 : Blo 1817610 4092605 := bbase (se 3 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 4092605 = 1534727) (by norm_num)
theorem B34960085 : Blo 1817610 34960085 := bbase (se 7 (by rfl) ⟨409688, by rfl⟩ : syracuseStep 34960085 = 819377) (by norm_num)
theorem B3453653 : Blo 1817610 3453653 := bbase (se 7 (by rfl) ⟨40472, by rfl⟩ : syracuseStep 3453653 = 80945) (by norm_num)
theorem B7377637 : Blo 1817610 7377637 := bbase (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) (by norm_num)
theorem B8295173 : Blo 1817610 8295173 := bbase (se 4 (by rfl) ⟨777672, by rfl⟩ : syracuseStep 8295173 = 1555345) (by norm_num)
theorem B4092677 : Blo 1817610 4092677 := bbase (se 4 (by rfl) ⟨383688, by rfl⟩ : syracuseStep 4092677 = 767377) (by norm_num)
theorem B3068725 : Blo 1817610 3068725 := bbase (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) (by norm_num)
theorem B6902597 : Blo 1817610 6902597 := bbase (se 4 (by rfl) ⟨647118, by rfl⟩ : syracuseStep 6902597 = 1294237) (by norm_num)
theorem B4092749 : Blo 1817610 4092749 := bbase (se 3 (by rfl) ⟨767390, by rfl⟩ : syracuseStep 4092749 = 1534781) (by norm_num)
theorem B28365653 : Blo 1817610 28365653 := bbase (se 9 (by rfl) ⟨83102, by rfl⟩ : syracuseStep 28365653 = 166205) (by norm_num)
theorem B2044813 : Blo 1817610 2044813 := bbase (se 3 (by rfl) ⟨383402, by rfl⟩ : syracuseStep 2044813 = 766805) (by norm_num)
theorem B3068813 : Blo 1817610 3068813 := bbase (se 3 (by rfl) ⟨575402, by rfl⟩ : syracuseStep 3068813 = 1150805) (by norm_num)
theorem B31077269 : Blo 1817610 31077269 := bbase (se 6 (by rfl) ⟨728373, by rfl⟩ : syracuseStep 31077269 = 1456747) (by norm_num)
theorem B4092821 : Blo 1817610 4092821 := bbase (se 6 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 4092821 = 191851) (by norm_num)
theorem B2044849 : Blo 1817610 2044849 := bbase (se 2 (by rfl) ⟨766818, by rfl⟩ : syracuseStep 2044849 = 1533637) (by norm_num)
theorem B9204677 : Blo 1817610 9204677 := bbase (se 4 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 9204677 = 1725877) (by norm_num)
theorem B2044885 : Blo 1817610 2044885 := bbase (se 7 (by rfl) ⟨23963, by rfl⟩ : syracuseStep 2044885 = 47927) (by norm_num)
theorem B4092893 : Blo 1817610 4092893 := bbase (se 3 (by rfl) ⟨767417, by rfl⟩ : syracuseStep 4092893 = 1534835) (by norm_num)
theorem B3453941 : Blo 1817610 3453941 := bbase (se 5 (by rfl) ⟨161903, by rfl⟩ : syracuseStep 3453941 = 323807) (by norm_num)
theorem B2044921 : Blo 1817610 2044921 := bbase (se 2 (by rfl) ⟨766845, by rfl⟩ : syracuseStep 2044921 = 1533691) (by norm_num)
theorem B6140933 : Blo 1817610 6140933 := bbase (se 4 (by rfl) ⟨575712, by rfl⟩ : syracuseStep 6140933 = 1151425) (by norm_num)
theorem B3068941 : Blo 1817610 3068941 := bbase (se 3 (by rfl) ⟨575426, by rfl⟩ : syracuseStep 3068941 = 1150853) (by norm_num)
theorem B2044957 : Blo 1817610 2044957 := bbase (se 3 (by rfl) ⟨383429, by rfl⟩ : syracuseStep 2044957 = 766859) (by norm_num)
theorem B4092965 : Blo 1817610 4092965 := bbase (se 4 (by rfl) ⟨383715, by rfl⟩ : syracuseStep 4092965 = 767431) (by norm_num)
theorem B2044993 : Blo 1817610 2044993 := bbase (se 2 (by rfl) ⟨766872, by rfl⟩ : syracuseStep 2044993 = 1533745) (by norm_num)
theorem B4600901 : Blo 1817610 4600901 := bbase (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) (by norm_num)
theorem B2045029 : Blo 1817610 2045029 := bbase (se 4 (by rfl) ⟨191721, by rfl⟩ : syracuseStep 2045029 = 383443) (by norm_num)
theorem B3069029 : Blo 1817610 3069029 := bbase (se 4 (by rfl) ⟨287721, by rfl⟩ : syracuseStep 3069029 = 575443) (by norm_num)
theorem B4093037 : Blo 1817610 4093037 := bbase (se 3 (by rfl) ⟨767444, by rfl⟩ : syracuseStep 4093037 = 1534889) (by norm_num)
theorem B2765933 : Blo 1817610 2765933 := bbase (se 3 (by rfl) ⟨518612, by rfl⟩ : syracuseStep 2765933 = 1037225) (by norm_num)
theorem B2045065 : Blo 1817610 2045065 := bbase (se 2 (by rfl) ⟨766899, by rfl⟩ : syracuseStep 2045065 = 1533799) (by norm_num)
theorem B3454093 : Blo 1817610 3454093 := bbase (se 3 (by rfl) ⟨647642, by rfl⟩ : syracuseStep 3454093 = 1295285) (by norm_num)
theorem B7771301 : Blo 1817610 7771301 := bbase (se 4 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 7771301 = 1457119) (by norm_num)
theorem B2045101 : Blo 1817610 2045101 := bbase (se 3 (by rfl) ⟨383456, by rfl⟩ : syracuseStep 2045101 = 766913) (by norm_num)
theorem B4093109 : Blo 1817610 4093109 := bbase (se 5 (by rfl) ⟨191864, by rfl⟩ : syracuseStep 4093109 = 383729) (by norm_num)
theorem B2045137 : Blo 1817610 2045137 := bbase (se 2 (by rfl) ⟨766926, by rfl⟩ : syracuseStep 2045137 = 1533853) (by norm_num)
theorem B12440789 : Blo 1817610 12440789 := bbase (se 7 (by rfl) ⟨145790, by rfl⟩ : syracuseStep 12440789 = 291581) (by norm_num)
theorem B3069157 : Blo 1817610 3069157 := bbase (se 4 (by rfl) ⟨287733, by rfl⟩ : syracuseStep 3069157 = 575467) (by norm_num)
theorem B2045173 : Blo 1817610 2045173 := bbase (se 5 (by rfl) ⟨95867, by rfl⟩ : syracuseStep 2045173 = 191735) (by norm_num)
theorem B4093181 : Blo 1817610 4093181 := bbase (se 3 (by rfl) ⟨767471, by rfl⟩ : syracuseStep 4093181 = 1534943) (by norm_num)
theorem B25212181 : Blo 1817610 25212181 := bbase (se 6 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 25212181 = 1181821) (by norm_num)
theorem B2045209 : Blo 1817610 2045209 := bbase (se 2 (by rfl) ⟨766953, by rfl⟩ : syracuseStep 2045209 = 1533907) (by norm_num)
theorem B2045245 : Blo 1817610 2045245 := bbase (se 3 (by rfl) ⟨383483, by rfl⟩ : syracuseStep 2045245 = 766967) (by norm_num)
theorem B3069245 : Blo 1817610 3069245 := bbase (se 3 (by rfl) ⟨575483, by rfl⟩ : syracuseStep 3069245 = 1150967) (by norm_num)
theorem B4093253 : Blo 1817610 4093253 := bbase (se 4 (by rfl) ⟨383742, by rfl⟩ : syracuseStep 4093253 = 767485) (by norm_num)
theorem B2463053 : Blo 1817610 2463053 := bbase (se 3 (by rfl) ⟨461822, by rfl⟩ : syracuseStep 2463053 = 923645) (by norm_num)
theorem B2045281 : Blo 1817610 2045281 := bbase (se 2 (by rfl) ⟨766980, by rfl⟩ : syracuseStep 2045281 = 1533961) (by norm_num)
theorem B8295797 : Blo 1817610 8295797 := bbase (se 5 (by rfl) ⟨388865, by rfl⟩ : syracuseStep 8295797 = 777731) (by norm_num)
theorem B2913661 : Blo 1817610 2913661 := bbase (se 3 (by rfl) ⟨546311, by rfl⟩ : syracuseStep 2913661 = 1092623) (by norm_num)
theorem B2045317 : Blo 1817610 2045317 := bbase (se 4 (by rfl) ⟨191748, by rfl⟩ : syracuseStep 2045317 = 383497) (by norm_num)
theorem B4093325 : Blo 1817610 4093325 := bbase (se 3 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 4093325 = 1534997) (by norm_num)
theorem B4601245 : Blo 1817610 4601245 := bbase (se 3 (by rfl) ⟨862733, by rfl⟩ : syracuseStep 4601245 = 1725467) (by norm_num)
theorem B2045353 : Blo 1817610 2045353 := bbase (se 2 (by rfl) ⟨767007, by rfl⟩ : syracuseStep 2045353 = 1534015) (by norm_num)
theorem B2184617 : Blo 1817610 2184617 := bbase (se 2 (by rfl) ⟨819231, by rfl⟩ : syracuseStep 2184617 = 1638463) (by norm_num)
theorem B3069373 : Blo 1817610 3069373 := bbase (se 3 (by rfl) ⟨575507, by rfl⟩ : syracuseStep 3069373 = 1151015) (by norm_num)
theorem B3454397 : Blo 1817610 3454397 := bbase (se 3 (by rfl) ⟨647699, by rfl⟩ : syracuseStep 3454397 = 1295399) (by norm_num)
theorem B2045389 : Blo 1817610 2045389 := bbase (se 3 (by rfl) ⟨383510, by rfl⟩ : syracuseStep 2045389 = 767021) (by norm_num)
theorem B4093397 : Blo 1817610 4093397 := bbase (se 7 (by rfl) ⟨47969, by rfl⟩ : syracuseStep 4093397 = 95939) (by norm_num)
theorem B2045425 : Blo 1817610 2045425 := bbase (se 2 (by rfl) ⟨767034, by rfl⟩ : syracuseStep 2045425 = 1534069) (by norm_num)
theorem B4601357 : Blo 1817610 4601357 := bbase (se 3 (by rfl) ⟨862754, by rfl⟩ : syracuseStep 4601357 = 1725509) (by norm_num)
theorem B2045461 : Blo 1817610 2045461 := bbase (se 6 (by rfl) ⟨47940, by rfl⟩ : syracuseStep 2045461 = 95881) (by norm_num)
theorem B3069461 : Blo 1817610 3069461 := bbase (se 6 (by rfl) ⟨71940, by rfl⟩ : syracuseStep 3069461 = 143881) (by norm_num)
theorem B4093469 : Blo 1817610 4093469 := bbase (se 3 (by rfl) ⟨767525, by rfl⟩ : syracuseStep 4093469 = 1535051) (by norm_num)
theorem B2045497 : Blo 1817610 2045497 := bbase (se 2 (by rfl) ⟨767061, by rfl⟩ : syracuseStep 2045497 = 1534123) (by norm_num)
theorem B2045533 : Blo 1817610 2045533 := bbase (se 3 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 2045533 = 767075) (by norm_num)
theorem B4093541 : Blo 1817610 4093541 := bbase (se 4 (by rfl) ⟨383769, by rfl⟩ : syracuseStep 4093541 = 767539) (by norm_num)
theorem B2045569 : Blo 1817610 2045569 := bbase (se 2 (by rfl) ⟨767088, by rfl⟩ : syracuseStep 2045569 = 1534177) (by norm_num)
theorem B4667021 : Blo 1817610 4667021 := bbase (se 3 (by rfl) ⟨875066, by rfl⟩ : syracuseStep 4667021 = 1750133) (by norm_num)
theorem B3069589 : Blo 1817610 3069589 := bbase (se 6 (by rfl) ⟨71943, by rfl⟩ : syracuseStep 3069589 = 143887) (by norm_num)
theorem B2045605 : Blo 1817610 2045605 := bbase (se 4 (by rfl) ⟨191775, by rfl⟩ : syracuseStep 2045605 = 383551) (by norm_num)
theorem B4093613 : Blo 1817610 4093613 := bbase (se 3 (by rfl) ⟨767552, by rfl⟩ : syracuseStep 4093613 = 1535105) (by norm_num)
theorem B2045641 : Blo 1817610 2045641 := bbase (se 2 (by rfl) ⟨767115, by rfl⟩ : syracuseStep 2045641 = 1534231) (by norm_num)
theorem B4601549 : Blo 1817610 4601549 := bbase (se 3 (by rfl) ⟨862790, by rfl⟩ : syracuseStep 4601549 = 1725581) (by norm_num)
theorem B2045677 : Blo 1817610 2045677 := bbase (se 3 (by rfl) ⟨383564, by rfl⟩ : syracuseStep 2045677 = 767129) (by norm_num)
theorem B3069677 : Blo 1817610 3069677 := bbase (se 3 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 3069677 = 1151129) (by norm_num)
theorem B8296181 : Blo 1817610 8296181 := bbase (se 5 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 8296181 = 777767) (by norm_num)
theorem B4093685 : Blo 1817610 4093685 := bbase (se 5 (by rfl) ⟨191891, by rfl⟩ : syracuseStep 4093685 = 383783) (by norm_num)
theorem B2045713 : Blo 1817610 2045713 := bbase (se 2 (by rfl) ⟨767142, by rfl⟩ : syracuseStep 2045713 = 1534285) (by norm_num)
theorem B2045749 : Blo 1817610 2045749 := bbase (se 5 (by rfl) ⟨95894, by rfl⟩ : syracuseStep 2045749 = 191789) (by norm_num)
theorem B4093757 : Blo 1817610 4093757 := bbase (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) (by norm_num)
theorem B2045785 : Blo 1817610 2045785 := bbase (se 2 (by rfl) ⟨767169, by rfl⟩ : syracuseStep 2045785 = 1534339) (by norm_num)
theorem B3069805 : Blo 1817610 3069805 := bbase (se 3 (by rfl) ⟨575588, by rfl⟩ : syracuseStep 3069805 = 1151177) (by norm_num)
theorem B16824181 : Blo 1817610 16824181 := bbase (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) (by norm_num)
theorem B2045821 : Blo 1817610 2045821 := bbase (se 3 (by rfl) ⟨383591, by rfl⟩ : syracuseStep 2045821 = 767183) (by norm_num)
theorem B4093829 : Blo 1817610 4093829 := bbase (se 4 (by rfl) ⟨383796, by rfl⟩ : syracuseStep 4093829 = 767593) (by norm_num)
theorem B2332577 : Blo 1817610 2332577 := bbase (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) (by norm_num)
theorem B2045857 : Blo 1817610 2045857 := bbase (se 2 (by rfl) ⟨767196, by rfl⟩ : syracuseStep 2045857 = 1534393) (by norm_num)
theorem B2045893 : Blo 1817610 2045893 := bbase (se 4 (by rfl) ⟨191802, by rfl⟩ : syracuseStep 2045893 = 383605) (by norm_num)
theorem B3069893 : Blo 1817610 3069893 := bbase (se 4 (by rfl) ⟨287802, by rfl⟩ : syracuseStep 3069893 = 575605) (by norm_num)
theorem B4093901 : Blo 1817610 4093901 := bbase (se 3 (by rfl) ⟨767606, by rfl⟩ : syracuseStep 4093901 = 1535213) (by norm_num)
theorem B2045929 : Blo 1817610 2045929 := bbase (se 2 (by rfl) ⟨767223, by rfl⟩ : syracuseStep 2045929 = 1534447) (by norm_num)
theorem B7985141 : Blo 1817610 7985141 := bbase (se 5 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 7985141 = 748607) (by norm_num)
theorem B2914309 : Blo 1817610 2914309 := bbase (se 4 (by rfl) ⟨273216, by rfl⟩ : syracuseStep 2914309 = 546433) (by norm_num)
theorem B2045965 : Blo 1817610 2045965 := bbase (se 3 (by rfl) ⟨383618, by rfl⟩ : syracuseStep 2045965 = 767237) (by norm_num)
theorem B9828373 : Blo 1817610 9828373 := bbase (se 6 (by rfl) ⟨230352, by rfl⟩ : syracuseStep 9828373 = 460705) (by norm_num)
theorem B4093973 : Blo 1817610 4093973 := bbase (se 6 (by rfl) ⟨95952, by rfl⟩ : syracuseStep 4093973 = 191905) (by norm_num)
theorem B4601893 : Blo 1817610 4601893 := bbase (se 4 (by rfl) ⟨431427, by rfl⟩ : syracuseStep 4601893 = 862855) (by norm_num)
theorem B2046001 : Blo 1817610 2046001 := bbase (se 2 (by rfl) ⟨767250, by rfl⟩ : syracuseStep 2046001 = 1534501) (by norm_num)
theorem B3070021 : Blo 1817610 3070021 := bbase (se 4 (by rfl) ⟨287814, by rfl⟩ : syracuseStep 3070021 = 575629) (by norm_num)
theorem B4913237 : Blo 1817610 4913237 := bbase (se 8 (by rfl) ⟨28788, by rfl⟩ : syracuseStep 4913237 = 57577) (by norm_num)
theorem B2046037 : Blo 1817610 2046037 := bbase (se 8 (by rfl) ⟨11988, by rfl⟩ : syracuseStep 2046037 = 23977) (by norm_num)
theorem B2185309 : Blo 1817610 2185309 := bbase (se 3 (by rfl) ⟨409745, by rfl⟩ : syracuseStep 2185309 = 819491) (by norm_num)
theorem B4094045 : Blo 1817610 4094045 := bbase (se 3 (by rfl) ⟨767633, by rfl⟩ : syracuseStep 4094045 = 1535267) (by norm_num)
theorem B2185313 : Blo 1817610 2185313 := bbase (se 2 (by rfl) ⟨819492, by rfl⟩ : syracuseStep 2185313 = 1638985) (by norm_num)
theorem B2046073 : Blo 1817610 2046073 := bbase (se 2 (by rfl) ⟨767277, by rfl⟩ : syracuseStep 2046073 = 1534555) (by norm_num)
theorem B4602005 : Blo 1817610 4602005 := bbase (se 6 (by rfl) ⟨107859, by rfl⟩ : syracuseStep 4602005 = 215719) (by norm_num)
theorem B2046109 : Blo 1817610 2046109 := bbase (se 3 (by rfl) ⟨383645, by rfl⟩ : syracuseStep 2046109 = 767291) (by norm_num)
theorem B3070109 : Blo 1817610 3070109 := bbase (se 3 (by rfl) ⟨575645, by rfl⟩ : syracuseStep 3070109 = 1151291) (by norm_num)
theorem B4094117 : Blo 1817610 4094117 := bbase (se 4 (by rfl) ⟨383823, by rfl⟩ : syracuseStep 4094117 = 767647) (by norm_num)
theorem B2046145 : Blo 1817610 2046145 := bbase (se 2 (by rfl) ⟨767304, by rfl⟩ : syracuseStep 2046145 = 1534609) (by norm_num)
theorem B9205973 : Blo 1817610 9205973 := bbase (se 7 (by rfl) ⟨107882, by rfl⟩ : syracuseStep 9205973 = 215765) (by norm_num)
theorem B4430045 : Blo 1817610 4430045 := bbase (se 3 (by rfl) ⟨830633, by rfl⟩ : syracuseStep 4430045 = 1661267) (by norm_num)
theorem B2046181 : Blo 1817610 2046181 := bbase (se 4 (by rfl) ⟨191829, by rfl⟩ : syracuseStep 2046181 = 383659) (by norm_num)
theorem B2301949 : Blo 1817610 2301949 := bbase (se 3 (by rfl) ⟨431615, by rfl⟩ : syracuseStep 2301949 = 863231) (by norm_num)
theorem B11655413 : Blo 1817610 11655413 := bbase (se 5 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 11655413 = 1092695) (by norm_num)
theorem B2046217 : Blo 1817610 2046217 := bbase (se 2 (by rfl) ⟨767331, by rfl⟩ : syracuseStep 2046217 = 1534663) (by norm_num)
theorem B7764245 : Blo 1817610 7764245 := bbase (se 6 (by rfl) ⟨181974, by rfl⟩ : syracuseStep 7764245 = 363949) (by norm_num)
theorem B3070237 : Blo 1817610 3070237 := bbase (se 3 (by rfl) ⟨575669, by rfl⟩ : syracuseStep 3070237 = 1151339) (by norm_num)
theorem B2046253 : Blo 1817610 2046253 := bbase (se 3 (by rfl) ⟨383672, by rfl⟩ : syracuseStep 2046253 = 767345) (by norm_num)
theorem B10361141 : Blo 1817610 10361141 := bbase (se 5 (by rfl) ⟨485678, by rfl⟩ : syracuseStep 10361141 = 971357) (by norm_num)
theorem B2046289 : Blo 1817610 2046289 := bbase (se 2 (by rfl) ⟨767358, by rfl⟩ : syracuseStep 2046289 = 1534717) (by norm_num)
theorem B4602197 : Blo 1817610 4602197 := bbase (se 10 (by rfl) ⟨6741, by rfl⟩ : syracuseStep 4602197 = 13483) (by norm_num)
theorem B2046325 : Blo 1817610 2046325 := bbase (se 5 (by rfl) ⟨95921, by rfl⟩ : syracuseStep 2046325 = 191843) (by norm_num)
theorem B3070325 : Blo 1817610 3070325 := bbase (se 5 (by rfl) ⟨143921, by rfl⟩ : syracuseStep 3070325 = 287843) (by norm_num)
theorem B3414397 : Blo 1817610 3414397 := bbase (se 3 (by rfl) ⟨640199, by rfl⟩ : syracuseStep 3414397 = 1280399) (by norm_num)
theorem B2046361 : Blo 1817610 2046361 := bbase (se 2 (by rfl) ⟨767385, by rfl⟩ : syracuseStep 2046361 = 1534771) (by norm_num)
theorem B5527973 : Blo 1817610 5527973 := bbase (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) (by norm_num)
theorem B6642101 : Blo 1817610 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B2046397 : Blo 1817610 2046397 := bbase (se 3 (by rfl) ⟨383699, by rfl⟩ : syracuseStep 2046397 = 767399) (by norm_num)
theorem B2046433 : Blo 1817610 2046433 := bbase (se 2 (by rfl) ⟨767412, by rfl⟩ : syracuseStep 2046433 = 1534825) (by norm_num)
theorem B3070453 : Blo 1817610 3070453 := bbase (se 5 (by rfl) ⟨143927, by rfl⟩ : syracuseStep 3070453 = 287855) (by norm_num)
theorem B7371269 : Blo 1817610 7371269 := bbase (se 4 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 7371269 = 1382113) (by norm_num)
theorem B2046469 : Blo 1817610 2046469 := bbase (se 4 (by rfl) ⟨191856, by rfl⟩ : syracuseStep 2046469 = 383713) (by norm_num)
theorem B2726429 : Blo 1817610 2726429 := bbase (se 3 (by rfl) ⟨511205, by rfl⟩ : syracuseStep 2726429 = 1022411) (by norm_num)
theorem B2046505 : Blo 1817610 2046505 := bbase (se 2 (by rfl) ⟨767439, by rfl⟩ : syracuseStep 2046505 = 1534879) (by norm_num)
theorem B2726453 : Blo 1817610 2726453 := bbase (se 5 (by rfl) ⟨127802, by rfl⟩ : syracuseStep 2726453 = 255605) (by norm_num)
theorem B2726477 : Blo 1817610 2726477 := bbase (se 3 (by rfl) ⟨511214, by rfl⟩ : syracuseStep 2726477 = 1022429) (by norm_num)
theorem B2046541 : Blo 1817610 2046541 := bbase (se 3 (by rfl) ⟨383726, by rfl⟩ : syracuseStep 2046541 = 767453) (by norm_num)
theorem B3070541 : Blo 1817610 3070541 := bbase (se 3 (by rfl) ⟨575726, by rfl⟩ : syracuseStep 3070541 = 1151453) (by norm_num)
theorem B2300501 : Blo 1817610 2300501 := bbase (se 8 (by rfl) ⟨13479, by rfl⟩ : syracuseStep 2300501 = 26959) (by norm_num)
theorem B2185813 : Blo 1817610 2185813 := bbase (se 8 (by rfl) ⟨12807, by rfl⟩ : syracuseStep 2185813 = 25615) (by norm_num)
theorem B2726501 : Blo 1817610 2726501 := bbase (se 4 (by rfl) ⟨255609, by rfl⟩ : syracuseStep 2726501 = 511219) (by norm_num)
theorem B4668005 : Blo 1817610 4668005 := bbase (se 4 (by rfl) ⟨437625, by rfl⟩ : syracuseStep 4668005 = 875251) (by norm_num)
theorem B2046577 : Blo 1817610 2046577 := bbase (se 2 (by rfl) ⟨767466, by rfl⟩ : syracuseStep 2046577 = 1534933) (by norm_num)
theorem B2726525 : Blo 1817610 2726525 := bbase (se 3 (by rfl) ⟨511223, by rfl⟩ : syracuseStep 2726525 = 1022447) (by norm_num)
theorem B2300557 : Blo 1817610 2300557 := bbase (se 3 (by rfl) ⟨431354, by rfl⟩ : syracuseStep 2300557 = 862709) (by norm_num)
theorem B2726549 : Blo 1817610 2726549 := bbase (se 6 (by rfl) ⟨63903, by rfl⟩ : syracuseStep 2726549 = 127807) (by norm_num)
theorem B2046613 : Blo 1817610 2046613 := bbase (se 6 (by rfl) ⟨47967, by rfl⟩ : syracuseStep 2046613 = 95935) (by norm_num)
theorem B2726573 : Blo 1817610 2726573 := bbase (se 3 (by rfl) ⟨511232, by rfl⟩ : syracuseStep 2726573 = 1022465) (by norm_num)
theorem B4602541 : Blo 1817610 4602541 := bbase (se 3 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 4602541 = 1725953) (by norm_num)
theorem B6134453 : Blo 1817610 6134453 := bbase (se 5 (by rfl) ⟨287552, by rfl⟩ : syracuseStep 6134453 = 575105) (by norm_num)
theorem B2046649 : Blo 1817610 2046649 := bbase (se 2 (by rfl) ⟨767493, by rfl⟩ : syracuseStep 2046649 = 1534987) (by norm_num)
theorem B2726597 : Blo 1817610 2726597 := bbase (se 4 (by rfl) ⟨255618, by rfl⟩ : syracuseStep 2726597 = 511237) (by norm_num)
theorem B6224581 : Blo 1817610 6224581 := bbase (se 4 (by rfl) ⟨583554, by rfl⟩ : syracuseStep 6224581 = 1167109) (by norm_num)
theorem B2726621 : Blo 1817610 2726621 := bbase (se 3 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 2726621 = 1022483) (by norm_num)
theorem B2046685 : Blo 1817610 2046685 := bbase (se 3 (by rfl) ⟨383753, by rfl⟩ : syracuseStep 2046685 = 767507) (by norm_num)
theorem B5176037 : Blo 1817610 5176037 := bbase (se 4 (by rfl) ⟨485253, by rfl⟩ : syracuseStep 5176037 = 970507) (by norm_num)
theorem B2300653 : Blo 1817610 2300653 := bbase (se 3 (by rfl) ⟨431372, by rfl⟩ : syracuseStep 2300653 = 862745) (by norm_num)
theorem B2726645 : Blo 1817610 2726645 := bbase (se 5 (by rfl) ⟨127811, by rfl⟩ : syracuseStep 2726645 = 255623) (by norm_num)
theorem B2046721 : Blo 1817610 2046721 := bbase (se 2 (by rfl) ⟨767520, by rfl⟩ : syracuseStep 2046721 = 1535041) (by norm_num)
theorem B2726669 : Blo 1817610 2726669 := bbase (se 3 (by rfl) ⟨511250, by rfl⟩ : syracuseStep 2726669 = 1022501) (by norm_num)
theorem B3545869 : Blo 1817610 3545869 := bbase (se 3 (by rfl) ⟨664850, by rfl⟩ : syracuseStep 3545869 = 1329701) (by norm_num)
theorem B4602653 : Blo 1817610 4602653 := bbase (se 3 (by rfl) ⟨862997, by rfl⟩ : syracuseStep 4602653 = 1725995) (by norm_num)
theorem B2726693 : Blo 1817610 2726693 := bbase (se 4 (by rfl) ⟨255627, by rfl⟩ : syracuseStep 2726693 = 511255) (by norm_num)
theorem B2046757 : Blo 1817610 2046757 := bbase (se 4 (by rfl) ⟨191883, by rfl⟩ : syracuseStep 2046757 = 383767) (by norm_num)
theorem B2726717 : Blo 1817610 2726717 := bbase (se 3 (by rfl) ⟨511259, by rfl⟩ : syracuseStep 2726717 = 1022519) (by norm_num)
theorem B2046793 : Blo 1817610 2046793 := bbase (se 2 (by rfl) ⟨767547, by rfl⟩ : syracuseStep 2046793 = 1535095) (by norm_num)
theorem B3275605 : Blo 1817610 3275605 := bbase (se 9 (by rfl) ⟨9596, by rfl⟩ : syracuseStep 3275605 = 19193) (by norm_num)
theorem B2726741 : Blo 1817610 2726741 := bbase (se 9 (by rfl) ⟨7988, by rfl⟩ : syracuseStep 2726741 = 15977) (by norm_num)
theorem B2726765 : Blo 1817610 2726765 := bbase (se 3 (by rfl) ⟨511268, by rfl⟩ : syracuseStep 2726765 = 1022537) (by norm_num)
theorem B2046829 : Blo 1817610 2046829 := bbase (se 3 (by rfl) ⟨383780, by rfl⟩ : syracuseStep 2046829 = 767561) (by norm_num)
theorem B2726789 : Blo 1817610 2726789 := bbase (se 4 (by rfl) ⟨255636, by rfl⟩ : syracuseStep 2726789 = 511273) (by norm_num)
theorem B6904709 : Blo 1817610 6904709 := bbase (se 4 (by rfl) ⟨647316, by rfl⟩ : syracuseStep 6904709 = 1294633) (by norm_num)
theorem B2046865 : Blo 1817610 2046865 := bbase (se 2 (by rfl) ⟨767574, by rfl⟩ : syracuseStep 2046865 = 1535149) (by norm_num)
theorem B2300825 : Blo 1817610 2300825 := bbase (se 2 (by rfl) ⟨862809, by rfl⟩ : syracuseStep 2300825 = 1725619) (by norm_num)
theorem B2726813 : Blo 1817610 2726813 := bbase (se 3 (by rfl) ⟨511277, by rfl⟩ : syracuseStep 2726813 = 1022555) (by norm_num)
theorem B2726837 : Blo 1817610 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B4914101 : Blo 1817610 4914101 := bbase (se 5 (by rfl) ⟨230348, by rfl⟩ : syracuseStep 4914101 = 460697) (by norm_num)
theorem B2046901 : Blo 1817610 2046901 := bbase (se 5 (by rfl) ⟨95948, by rfl⟩ : syracuseStep 2046901 = 191897) (by norm_num)
theorem B2726861 : Blo 1817610 2726861 := bbase (se 3 (by rfl) ⟨511286, by rfl⟩ : syracuseStep 2726861 = 1022573) (by norm_num)
theorem B2300881 : Blo 1817610 2300881 := bbase (se 2 (by rfl) ⟨862830, by rfl⟩ : syracuseStep 2300881 = 1725661) (by norm_num)
theorem B2046937 : Blo 1817610 2046937 := bbase (se 2 (by rfl) ⟨767601, by rfl⟩ : syracuseStep 2046937 = 1535203) (by norm_num)
theorem B4602845 : Blo 1817610 4602845 := bbase (se 3 (by rfl) ⟨863033, by rfl⟩ : syracuseStep 4602845 = 1726067) (by norm_num)
theorem B2726885 : Blo 1817610 2726885 := bbase (se 4 (by rfl) ⟨255645, by rfl⟩ : syracuseStep 2726885 = 511291) (by norm_num)
theorem B2726909 : Blo 1817610 2726909 := bbase (se 3 (by rfl) ⟨511295, by rfl⟩ : syracuseStep 2726909 = 1022591) (by norm_num)
theorem B2046973 : Blo 1817610 2046973 := bbase (se 3 (by rfl) ⟨383807, by rfl⟩ : syracuseStep 2046973 = 767615) (by norm_num)
theorem B3111949 : Blo 1817610 3111949 := bbase (se 3 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 3111949 = 1166981) (by norm_num)
theorem B2726933 : Blo 1817610 2726933 := bbase (se 6 (by rfl) ⟨63912, by rfl⟩ : syracuseStep 2726933 = 127825) (by norm_num)
theorem B2047009 : Blo 1817610 2047009 := bbase (se 2 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 2047009 = 1535257) (by norm_num)
theorem B2726957 : Blo 1817610 2726957 := bbase (se 3 (by rfl) ⟨511304, by rfl⟩ : syracuseStep 2726957 = 1022609) (by norm_num)
theorem B2300977 : Blo 1817610 2300977 := bbase (se 2 (by rfl) ⟨862866, by rfl⟩ : syracuseStep 2300977 = 1725733) (by norm_num)
theorem B2726981 : Blo 1817610 2726981 := bbase (se 4 (by rfl) ⟨255654, by rfl⟩ : syracuseStep 2726981 = 511309) (by norm_num)
theorem B2047045 : Blo 1817610 2047045 := bbase (se 4 (by rfl) ⟨191910, by rfl⟩ : syracuseStep 2047045 = 383821) (by norm_num)
theorem B2727005 : Blo 1817610 2727005 := bbase (se 3 (by rfl) ⟨511313, by rfl⟩ : syracuseStep 2727005 = 1022627) (by norm_num)
theorem B6134885 : Blo 1817610 6134885 := bbase (se 4 (by rfl) ⟨575145, by rfl⟩ : syracuseStep 6134885 = 1150291) (by norm_num)
theorem B2727029 : Blo 1817610 2727029 := bbase (se 5 (by rfl) ⟨127829, by rfl⟩ : syracuseStep 2727029 = 255659) (by norm_num)
theorem B2727053 : Blo 1817610 2727053 := bbase (se 3 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 2727053 = 1022645) (by norm_num)
theorem B2727077 : Blo 1817610 2727077 := bbase (se 4 (by rfl) ⟨255663, by rfl⟩ : syracuseStep 2727077 = 511327) (by norm_num)
theorem B6904997 : Blo 1817610 6904997 := bbase (se 4 (by rfl) ⟨647343, by rfl⟩ : syracuseStep 6904997 = 1294687) (by norm_num)
theorem B2727101 : Blo 1817610 2727101 := bbase (se 3 (by rfl) ⟨511331, by rfl⟩ : syracuseStep 2727101 = 1022663) (by norm_num)
theorem B2727125 : Blo 1817610 2727125 := bbase (se 7 (by rfl) ⟨31958, by rfl⟩ : syracuseStep 2727125 = 63917) (by norm_num)
theorem B2301149 : Blo 1817610 2301149 := bbase (se 3 (by rfl) ⟨431465, by rfl⟩ : syracuseStep 2301149 = 862931) (by norm_num)
theorem B4431077 : Blo 1817610 4431077 := bbase (se 4 (by rfl) ⟨415413, by rfl⟩ : syracuseStep 4431077 = 830827) (by norm_num)
theorem B2727149 : Blo 1817610 2727149 := bbase (se 3 (by rfl) ⟨511340, by rfl⟩ : syracuseStep 2727149 = 1022681) (by norm_num)
theorem B7765253 : Blo 1817610 7765253 := bbase (se 4 (by rfl) ⟨727992, by rfl⟩ : syracuseStep 7765253 = 1455985) (by norm_num)
theorem B2727173 : Blo 1817610 2727173 := bbase (se 4 (by rfl) ⟨255672, by rfl⟩ : syracuseStep 2727173 = 511345) (by norm_num)
theorem B2301205 : Blo 1817610 2301205 := bbase (se 6 (by rfl) ⟨53934, by rfl⟩ : syracuseStep 2301205 = 107869) (by norm_num)
theorem B2727197 : Blo 1817610 2727197 := bbase (se 3 (by rfl) ⟨511349, by rfl⟩ : syracuseStep 2727197 = 1022699) (by norm_num)
theorem B2727221 : Blo 1817610 2727221 := bbase (se 5 (by rfl) ⟨127838, by rfl⟩ : syracuseStep 2727221 = 255677) (by norm_num)
theorem B4603189 : Blo 1817610 4603189 := bbase (se 5 (by rfl) ⟨215774, by rfl⟩ : syracuseStep 4603189 = 431549) (by norm_num)
theorem B2727245 : Blo 1817610 2727245 := bbase (se 3 (by rfl) ⟨511358, by rfl⟩ : syracuseStep 2727245 = 1022717) (by norm_num)
theorem B4914533 : Blo 1817610 4914533 := bbase (se 4 (by rfl) ⟨460737, by rfl⟩ : syracuseStep 4914533 = 921475) (by norm_num)
theorem B2727269 : Blo 1817610 2727269 := bbase (se 4 (by rfl) ⟨255681, by rfl⟩ : syracuseStep 2727269 = 511363) (by norm_num)
theorem B2301301 : Blo 1817610 2301301 := bbase (se 5 (by rfl) ⟨107873, by rfl⟩ : syracuseStep 2301301 = 215747) (by norm_num)
theorem B2727293 : Blo 1817610 2727293 := bbase (se 3 (by rfl) ⟨511367, by rfl⟩ : syracuseStep 2727293 = 1022735) (by norm_num)
theorem B2588053 : Blo 1817610 2588053 := bbase (se 6 (by rfl) ⟨60657, by rfl⟩ : syracuseStep 2588053 = 121315) (by norm_num)
theorem B2727317 : Blo 1817610 2727317 := bbase (se 6 (by rfl) ⟨63921, by rfl⟩ : syracuseStep 2727317 = 127843) (by norm_num)
theorem B1842593 : Blo 1817610 1842593 := bbase (se 2 (by rfl) ⟨690972, by rfl⟩ : syracuseStep 1842593 = 1381945) (by norm_num)
theorem B4603301 : Blo 1817610 4603301 := bbase (se 4 (by rfl) ⟨431559, by rfl⟩ : syracuseStep 4603301 = 863119) (by norm_num)
theorem B2727341 : Blo 1817610 2727341 := bbase (se 3 (by rfl) ⟨511376, by rfl⟩ : syracuseStep 2727341 = 1022753) (by norm_num)
theorem B3882421 : Blo 1817610 3882421 := bbase (se 5 (by rfl) ⟨181988, by rfl⟩ : syracuseStep 3882421 = 363977) (by norm_num)
theorem B2727365 : Blo 1817610 2727365 := bbase (se 4 (by rfl) ⟨255690, by rfl⟩ : syracuseStep 2727365 = 511381) (by norm_num)
theorem B2727389 : Blo 1817610 2727389 := bbase (se 3 (by rfl) ⟨511385, by rfl⟩ : syracuseStep 2727389 = 1022771) (by norm_num)
theorem B9207269 : Blo 1817610 9207269 := bbase (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) (by norm_num)
theorem B3276269 : Blo 1817610 3276269 := bbase (se 3 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 3276269 = 1228601) (by norm_num)
theorem B2727413 : Blo 1817610 2727413 := bbase (se 5 (by rfl) ⟨127847, by rfl⟩ : syracuseStep 2727413 = 255695) (by norm_num)
theorem B2727437 : Blo 1817610 2727437 := bbase (se 3 (by rfl) ⟨511394, by rfl⟩ : syracuseStep 2727437 = 1022789) (by norm_num)
theorem B6135317 : Blo 1817610 6135317 := bbase (se 6 (by rfl) ⟨143796, by rfl⟩ : syracuseStep 6135317 = 287593) (by norm_num)
theorem B2301473 : Blo 1817610 2301473 := bbase (se 2 (by rfl) ⟨863052, by rfl⟩ : syracuseStep 2301473 = 1726105) (by norm_num)
theorem B2727461 : Blo 1817610 2727461 := bbase (se 4 (by rfl) ⟨255699, by rfl⟩ : syracuseStep 2727461 = 511399) (by norm_num)
theorem B2727485 : Blo 1817610 2727485 := bbase (se 3 (by rfl) ⟨511403, by rfl⟩ : syracuseStep 2727485 = 1022807) (by norm_num)
theorem B2727509 : Blo 1817610 2727509 := bbase (se 8 (by rfl) ⟨15981, by rfl⟩ : syracuseStep 2727509 = 31963) (by norm_num)
theorem B2301529 : Blo 1817610 2301529 := bbase (se 2 (by rfl) ⟨863073, by rfl⟩ : syracuseStep 2301529 = 1726147) (by norm_num)
theorem B4603493 : Blo 1817610 4603493 := bbase (se 4 (by rfl) ⟨431577, by rfl⟩ : syracuseStep 4603493 = 863155) (by norm_num)
theorem B2588269 : Blo 1817610 2588269 := bbase (se 3 (by rfl) ⟨485300, by rfl⟩ : syracuseStep 2588269 = 970601) (by norm_num)
theorem B2727533 : Blo 1817610 2727533 := bbase (se 3 (by rfl) ⟨511412, by rfl⟩ : syracuseStep 2727533 = 1022825) (by norm_num)
theorem B2727557 : Blo 1817610 2727557 := bbase (se 4 (by rfl) ⟨255708, by rfl⟩ : syracuseStep 2727557 = 511417) (by norm_num)
theorem B2727581 : Blo 1817610 2727581 := bbase (se 3 (by rfl) ⟨511421, by rfl⟩ : syracuseStep 2727581 = 1022843) (by norm_num)
theorem B2727605 : Blo 1817610 2727605 := bbase (se 5 (by rfl) ⟨127856, by rfl⟩ : syracuseStep 2727605 = 255713) (by norm_num)
theorem B2301625 : Blo 1817610 2301625 := bbase (se 2 (by rfl) ⟨863109, by rfl⟩ : syracuseStep 2301625 = 1726219) (by norm_num)
theorem B1941185 : Blo 1817610 1941185 := bbase (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) (by norm_num)
theorem B2727629 : Blo 1817610 2727629 := bbase (se 3 (by rfl) ⟨511430, by rfl⟩ : syracuseStep 2727629 = 1022861) (by norm_num)
theorem B2727653 : Blo 1817610 2727653 := bbase (se 4 (by rfl) ⟨255717, by rfl⟩ : syracuseStep 2727653 = 511435) (by norm_num)
theorem B2727677 : Blo 1817610 2727677 := bbase (se 3 (by rfl) ⟨511439, by rfl⟩ : syracuseStep 2727677 = 1022879) (by norm_num)
theorem B4914965 : Blo 1817610 4914965 := bbase (se 6 (by rfl) ⟨115194, by rfl⟩ : syracuseStep 4914965 = 230389) (by norm_num)
theorem B2727701 : Blo 1817610 2727701 := bbase (se 6 (by rfl) ⟨63930, by rfl⟩ : syracuseStep 2727701 = 127861) (by norm_num)
theorem B2727725 : Blo 1817610 2727725 := bbase (se 3 (by rfl) ⟨511448, by rfl⟩ : syracuseStep 2727725 = 1022897) (by norm_num)
theorem B2727749 : Blo 1817610 2727749 := bbase (se 4 (by rfl) ⟨255726, by rfl⟩ : syracuseStep 2727749 = 511453) (by norm_num)
theorem B2727773 : Blo 1817610 2727773 := bbase (se 3 (by rfl) ⟨511457, by rfl⟩ : syracuseStep 2727773 = 1022915) (by norm_num)
theorem B2301797 : Blo 1817610 2301797 := bbase (se 4 (by rfl) ⟨215793, by rfl⟩ : syracuseStep 2301797 = 431587) (by norm_num)
theorem B2727797 : Blo 1817610 2727797 := bbase (se 5 (by rfl) ⟨127865, by rfl⟩ : syracuseStep 2727797 = 255731) (by norm_num)
theorem B2727821 : Blo 1817610 2727821 := bbase (se 3 (by rfl) ⟨511466, by rfl⟩ : syracuseStep 2727821 = 1022933) (by norm_num)
theorem B2301853 : Blo 1817610 2301853 := bbase (se 3 (by rfl) ⟨431597, by rfl⟩ : syracuseStep 2301853 = 863195) (by norm_num)
theorem B3882917 : Blo 1817610 3882917 := bbase (se 4 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 3882917 = 728047) (by norm_num)
theorem B2727845 : Blo 1817610 2727845 := bbase (se 4 (by rfl) ⟨255735, by rfl⟩ : syracuseStep 2727845 = 511471) (by norm_num)
theorem B14753717 : Blo 1817610 14753717 := bbase (se 5 (by rfl) ⟨691580, by rfl⟩ : syracuseStep 14753717 = 1383161) (by norm_num)
theorem B2727869 : Blo 1817610 2727869 := bbase (se 3 (by rfl) ⟨511475, by rfl⟩ : syracuseStep 2727869 = 1022951) (by norm_num)
theorem B4603837 : Blo 1817610 4603837 := bbase (se 3 (by rfl) ⟨863219, by rfl⟩ : syracuseStep 4603837 = 1726439) (by norm_num)
theorem B6135749 : Blo 1817610 6135749 := bbase (se 4 (by rfl) ⟨575226, by rfl⟩ : syracuseStep 6135749 = 1150453) (by norm_num)
theorem B2727893 : Blo 1817610 2727893 := bbase (se 7 (by rfl) ⟨31967, by rfl⟩ : syracuseStep 2727893 = 63935) (by norm_num)
theorem B2588645 : Blo 1817610 2588645 := bbase (se 4 (by rfl) ⟨242685, by rfl⟩ : syracuseStep 2588645 = 485371) (by norm_num)
theorem B2727917 : Blo 1817610 2727917 := bbase (se 3 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 2727917 = 1022969) (by norm_num)
theorem B3497987 : Blo 1817610 3497987 := bstep (se 1 (by rfl) ⟨2623490, by rfl⟩ : syracuseStep 3497987 = 5246981) B5246981
theorem B1818627 : Blo 1817610 1818627 := bstep (se 1 (by rfl) ⟨1363970, by rfl⟩ : syracuseStep 1818627 = 2727941) B2727941
theorem B2727953 : Blo 1817610 2727953 := bstep (se 2 (by rfl) ⟨1022982, by rfl⟩ : syracuseStep 2727953 = 2045965) B2045965
theorem B1818643 : Blo 1817610 1818643 := bstep (se 1 (by rfl) ⟨1363982, by rfl⟩ : syracuseStep 1818643 = 2727965) B2727965
theorem B7872547 : Blo 1817610 7872547 := bstep (se 1 (by rfl) ⟨5904410, by rfl⟩ : syracuseStep 7872547 = 11808821) B11808821
theorem B2727971 : Blo 1817610 2727971 := bstep (se 1 (by rfl) ⟨2045978, by rfl⟩ : syracuseStep 2727971 = 4091957) B4091957
theorem B1818659 : Blo 1817610 1818659 := bstep (se 1 (by rfl) ⟨1363994, by rfl⟩ : syracuseStep 1818659 = 2727989) B2727989
theorem B6135857 : Blo 1817610 6135857 := bstep (se 2 (by rfl) ⟨2300946, by rfl⟩ : syracuseStep 6135857 = 4601893) B4601893
theorem B1818675 : Blo 1817610 1818675 := bstep (se 1 (by rfl) ⟨1364006, by rfl⟩ : syracuseStep 1818675 = 2728013) B2728013
theorem B53157941 : Blo 1817610 53157941 := bstep (se 5 (by rfl) ⟨2491778, by rfl⟩ : syracuseStep 53157941 = 4983557) B4983557
theorem B2728001 : Blo 1817610 2728001 := bstep (se 2 (by rfl) ⟨1023000, by rfl⟩ : syracuseStep 2728001 = 2046001) B2046001
theorem B1818691 : Blo 1817610 1818691 := bstep (se 1 (by rfl) ⟨1364018, by rfl⟩ : syracuseStep 1818691 = 2728037) B2728037
theorem B16597061 : Blo 1817610 16597061 := bstep (se 4 (by rfl) ⟨1555974, by rfl⟩ : syracuseStep 16597061 = 3111949) B3111949
theorem B2728019 : Blo 1817610 2728019 := bstep (se 1 (by rfl) ⟨2046014, by rfl⟩ : syracuseStep 2728019 = 4092029) B4092029
theorem B1818707 : Blo 1817610 1818707 := bstep (se 1 (by rfl) ⟨1364030, by rfl⟩ : syracuseStep 1818707 = 2728061) B2728061
theorem B1818723 : Blo 1817610 1818723 := bstep (se 1 (by rfl) ⟨1364042, by rfl⟩ : syracuseStep 1818723 = 2728085) B2728085
theorem B39321713 : Blo 1817610 39321713 := bstep (se 2 (by rfl) ⟨14745642, by rfl⟩ : syracuseStep 39321713 = 29491285) B29491285
theorem B4915313 : Blo 1817610 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B2728049 : Blo 1817610 2728049 := bstep (se 2 (by rfl) ⟨1023018, by rfl⟩ : syracuseStep 2728049 = 2046037) B2046037
theorem B1818739 : Blo 1817610 1818739 := bstep (se 1 (by rfl) ⟨1364054, by rfl⟩ : syracuseStep 1818739 = 2728109) B2728109
theorem B6905969 : Blo 1817610 6905969 := bstep (se 2 (by rfl) ⟨2589738, by rfl⟩ : syracuseStep 6905969 = 5179477) B5179477
theorem B2728067 : Blo 1817610 2728067 := bstep (se 1 (by rfl) ⟨2046050, by rfl⟩ : syracuseStep 2728067 = 4092101) B4092101
theorem B1818755 : Blo 1817610 1818755 := bstep (se 1 (by rfl) ⟨1364066, by rfl⟩ : syracuseStep 1818755 = 2728133) B2728133
theorem B1818771 : Blo 1817610 1818771 := bstep (se 1 (by rfl) ⟨1364078, by rfl⟩ : syracuseStep 1818771 = 2728157) B2728157
theorem B2728097 : Blo 1817610 2728097 := bstep (se 2 (by rfl) ⟨1023036, by rfl⟩ : syracuseStep 2728097 = 2046073) B2046073
theorem B1818787 : Blo 1817610 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B2728115 : Blo 1817610 2728115 := bstep (se 1 (by rfl) ⟨2046086, by rfl⟩ : syracuseStep 2728115 = 4092173) B4092173
theorem B1818803 : Blo 1817610 1818803 := bstep (se 1 (by rfl) ⟨1364102, by rfl⟩ : syracuseStep 1818803 = 2728205) B2728205
theorem B1818819 : Blo 1817610 1818819 := bstep (se 1 (by rfl) ⟨1364114, by rfl⟩ : syracuseStep 1818819 = 2728229) B2728229
theorem B2728145 : Blo 1817610 2728145 := bstep (se 2 (by rfl) ⟨1023054, by rfl⟩ : syracuseStep 2728145 = 2046109) B2046109
theorem B1818835 : Blo 1817610 1818835 := bstep (se 1 (by rfl) ⟨1364126, by rfl⟩ : syracuseStep 1818835 = 2728253) B2728253
theorem B7766243 : Blo 1817610 7766243 := bstep (se 1 (by rfl) ⟨5824682, by rfl⟩ : syracuseStep 7766243 = 11649365) B11649365
theorem B2728163 : Blo 1817610 2728163 := bstep (se 1 (by rfl) ⟨2046122, by rfl⟩ : syracuseStep 2728163 = 4092245) B4092245
theorem B1818851 : Blo 1817610 1818851 := bstep (se 1 (by rfl) ⟨1364138, by rfl⟩ : syracuseStep 1818851 = 2728277) B2728277
theorem B4980973 : Blo 1817610 4980973 := bstep (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) B1867865
theorem B1818867 : Blo 1817610 1818867 := bstep (se 1 (by rfl) ⟨1364150, by rfl⟩ : syracuseStep 1818867 = 2728301) B2728301
theorem B2728193 : Blo 1817610 2728193 := bstep (se 2 (by rfl) ⟨1023072, by rfl⟩ : syracuseStep 2728193 = 2046145) B2046145
theorem B1818883 : Blo 1817610 1818883 := bstep (se 1 (by rfl) ⟨1364162, by rfl⟩ : syracuseStep 1818883 = 2728325) B2728325
theorem B1941779 : Blo 1817610 1941779 := bstep (se 1 (by rfl) ⟨1456334, by rfl⟩ : syracuseStep 1941779 = 2912669) B2912669
theorem B2728211 : Blo 1817610 2728211 := bstep (se 1 (by rfl) ⟨2046158, by rfl⟩ : syracuseStep 2728211 = 4092317) B4092317
theorem B1818899 : Blo 1817610 1818899 := bstep (se 1 (by rfl) ⟨1364174, by rfl⟩ : syracuseStep 1818899 = 2728349) B2728349
theorem B1818915 : Blo 1817610 1818915 := bstep (se 1 (by rfl) ⟨1364186, by rfl⟩ : syracuseStep 1818915 = 2728373) B2728373
theorem B2728241 : Blo 1817610 2728241 := bstep (se 2 (by rfl) ⟨1023090, by rfl⟩ : syracuseStep 2728241 = 2046181) B2046181
theorem B1818931 : Blo 1817610 1818931 := bstep (se 1 (by rfl) ⟨1364198, by rfl⟩ : syracuseStep 1818931 = 2728397) B2728397
theorem B4792643 : Blo 1817610 4792643 := bstep (se 1 (by rfl) ⟨3594482, by rfl⟩ : syracuseStep 4792643 = 7188965) B7188965
theorem B2728259 : Blo 1817610 2728259 := bstep (se 1 (by rfl) ⟨2046194, by rfl⟩ : syracuseStep 2728259 = 4092389) B4092389
theorem B1818947 : Blo 1817610 1818947 := bstep (se 1 (by rfl) ⟨1364210, by rfl⟩ : syracuseStep 1818947 = 2728421) B2728421
theorem B5177677 : Blo 1817610 5177677 := bstep (se 3 (by rfl) ⟨970814, by rfl⟩ : syracuseStep 5177677 = 1941629) B1941629
theorem B1818963 : Blo 1817610 1818963 := bstep (se 1 (by rfl) ⟨1364222, by rfl⟩ : syracuseStep 1818963 = 2728445) B2728445
theorem B2728289 : Blo 1817610 2728289 := bstep (se 2 (by rfl) ⟨1023108, by rfl⟩ : syracuseStep 2728289 = 2046217) B2046217
theorem B1818979 : Blo 1817610 1818979 := bstep (se 1 (by rfl) ⟨1364234, by rfl⟩ : syracuseStep 1818979 = 2728469) B2728469
theorem B4604273 : Blo 1817610 4604273 := bstep (se 2 (by rfl) ⟨1726602, by rfl⟩ : syracuseStep 4604273 = 3453205) B3453205
theorem B2728307 : Blo 1817610 2728307 := bstep (se 1 (by rfl) ⟨2046230, by rfl⟩ : syracuseStep 2728307 = 4092461) B4092461
theorem B1818995 : Blo 1817610 1818995 := bstep (se 1 (by rfl) ⟨1364246, by rfl⟩ : syracuseStep 1818995 = 2728493) B2728493
theorem B1819011 : Blo 1817610 1819011 := bstep (se 1 (by rfl) ⟨1364258, by rfl⟩ : syracuseStep 1819011 = 2728517) B2728517
theorem B2302339 : Blo 1817610 2302339 := bstep (se 1 (by rfl) ⟨1726754, by rfl⟩ : syracuseStep 2302339 = 3453509) B3453509
theorem B2728337 : Blo 1817610 2728337 := bstep (se 2 (by rfl) ⟨1023126, by rfl⟩ : syracuseStep 2728337 = 2046253) B2046253
theorem B1819027 : Blo 1817610 1819027 := bstep (se 1 (by rfl) ⟨1364270, by rfl⟩ : syracuseStep 1819027 = 2728541) B2728541
theorem B2589089 : Blo 1817610 2589089 := bstep (se 2 (by rfl) ⟨970908, by rfl⟩ : syracuseStep 2589089 = 1941817) B1941817
theorem B2728355 : Blo 1817610 2728355 := bstep (se 1 (by rfl) ⟨2046266, by rfl⟩ : syracuseStep 2728355 = 4092533) B4092533
theorem B4604323 : Blo 1817610 4604323 := bstep (se 1 (by rfl) ⟨3453242, by rfl⟩ : syracuseStep 4604323 = 6906485) B6906485
theorem B1819043 : Blo 1817610 1819043 := bstep (se 1 (by rfl) ⟨1364282, by rfl⟩ : syracuseStep 1819043 = 2728565) B2728565
theorem B9208241 : Blo 1817610 9208241 := bstep (se 2 (by rfl) ⟨3453090, by rfl⟩ : syracuseStep 9208241 = 6906181) B6906181
theorem B1819059 : Blo 1817610 1819059 := bstep (se 1 (by rfl) ⟨1364294, by rfl⟩ : syracuseStep 1819059 = 2728589) B2728589
theorem B2728385 : Blo 1817610 2728385 := bstep (se 2 (by rfl) ⟨1023144, by rfl⟩ : syracuseStep 2728385 = 2046289) B2046289
theorem B1819075 : Blo 1817610 1819075 := bstep (se 1 (by rfl) ⟨1364306, by rfl⟩ : syracuseStep 1819075 = 2728613) B2728613
theorem B2728403 : Blo 1817610 2728403 := bstep (se 1 (by rfl) ⟨2046302, by rfl⟩ : syracuseStep 2728403 = 4092605) B4092605
theorem B1819091 : Blo 1817610 1819091 := bstep (se 1 (by rfl) ⟨1364318, by rfl⟩ : syracuseStep 1819091 = 2728637) B2728637
theorem B23306723 : Blo 1817610 23306723 := bstep (se 1 (by rfl) ⟨17480042, by rfl⟩ : syracuseStep 23306723 = 34960085) B34960085
theorem B1819107 : Blo 1817610 1819107 := bstep (se 1 (by rfl) ⟨1364330, by rfl⟩ : syracuseStep 1819107 = 2728661) B2728661
theorem B2302435 : Blo 1817610 2302435 := bstep (se 1 (by rfl) ⟨1726826, by rfl⟩ : syracuseStep 2302435 = 3453653) B3453653
theorem B5177837 : Blo 1817610 5177837 := bstep (se 3 (by rfl) ⟨970844, by rfl⟩ : syracuseStep 5177837 = 1941689) B1941689
theorem B2728433 : Blo 1817610 2728433 := bstep (se 2 (by rfl) ⟨1023162, by rfl⟩ : syracuseStep 2728433 = 2046325) B2046325
theorem B1819123 : Blo 1817610 1819123 := bstep (se 1 (by rfl) ⟨1364342, by rfl⟩ : syracuseStep 1819123 = 2728685) B2728685
theorem B5530115 : Blo 1817610 5530115 := bstep (se 1 (by rfl) ⟨4147586, by rfl⟩ : syracuseStep 5530115 = 8295173) B8295173
theorem B2728451 : Blo 1817610 2728451 := bstep (se 1 (by rfl) ⟨2046338, by rfl⟩ : syracuseStep 2728451 = 4092677) B4092677
theorem B1819139 : Blo 1817610 1819139 := bstep (se 1 (by rfl) ⟨1364354, by rfl⟩ : syracuseStep 1819139 = 2728709) B2728709
theorem B2589203 : Blo 1817610 2589203 := bstep (se 1 (by rfl) ⟨1941902, by rfl⟩ : syracuseStep 2589203 = 3883805) B3883805
theorem B1819155 : Blo 1817610 1819155 := bstep (se 1 (by rfl) ⟨1364366, by rfl⟩ : syracuseStep 1819155 = 2728733) B2728733
theorem B2728481 : Blo 1817610 2728481 := bstep (se 2 (by rfl) ⟨1023180, by rfl⟩ : syracuseStep 2728481 = 2046361) B2046361
theorem B1819171 : Blo 1817610 1819171 := bstep (se 1 (by rfl) ⟨1364378, by rfl⟩ : syracuseStep 1819171 = 2728757) B2728757
theorem B4604465 : Blo 1817610 4604465 := bstep (se 2 (by rfl) ⟨1726674, by rfl⟩ : syracuseStep 4604465 = 3453349) B3453349
theorem B2728499 : Blo 1817610 2728499 := bstep (se 1 (by rfl) ⟨2046374, by rfl⟩ : syracuseStep 2728499 = 4092749) B4092749
theorem B1819187 : Blo 1817610 1819187 := bstep (se 1 (by rfl) ⟨1364390, by rfl⟩ : syracuseStep 1819187 = 2728781) B2728781
theorem B1819203 : Blo 1817610 1819203 := bstep (se 1 (by rfl) ⟨1364402, by rfl⟩ : syracuseStep 1819203 = 2728805) B2728805
theorem B6136397 : Blo 1817610 6136397 := bstep (se 3 (by rfl) ⟨1150574, by rfl⟩ : syracuseStep 6136397 = 2301149) B2301149
theorem B2728529 : Blo 1817610 2728529 := bstep (se 2 (by rfl) ⟨1023198, by rfl⟩ : syracuseStep 2728529 = 2046397) B2046397
theorem B1819219 : Blo 1817610 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B2589283 : Blo 1817610 2589283 := bstep (se 1 (by rfl) ⟨1941962, by rfl⟩ : syracuseStep 2589283 = 3883925) B3883925
theorem B20718179 : Blo 1817610 20718179 := bstep (se 1 (by rfl) ⟨15538634, by rfl⟩ : syracuseStep 20718179 = 31077269) B31077269
theorem B2728547 : Blo 1817610 2728547 := bstep (se 1 (by rfl) ⟨2046410, by rfl⟩ : syracuseStep 2728547 = 4092821) B4092821
theorem B1819235 : Blo 1817610 1819235 := bstep (se 1 (by rfl) ⟨1364426, by rfl⟩ : syracuseStep 1819235 = 2728853) B2728853
theorem B1819251 : Blo 1817610 1819251 := bstep (se 1 (by rfl) ⟨1364438, by rfl⟩ : syracuseStep 1819251 = 2728877) B2728877
theorem B2728577 : Blo 1817610 2728577 := bstep (se 2 (by rfl) ⟨1023216, by rfl⟩ : syracuseStep 2728577 = 2046433) B2046433
theorem B6136451 : Blo 1817610 6136451 := bstep (se 1 (by rfl) ⟨4602338, by rfl⟩ : syracuseStep 6136451 = 9204677) B9204677
theorem B1819267 : Blo 1817610 1819267 := bstep (se 1 (by rfl) ⟨1364450, by rfl⟩ : syracuseStep 1819267 = 2728901) B2728901
theorem B2728595 : Blo 1817610 2728595 := bstep (se 1 (by rfl) ⟨2046446, by rfl⟩ : syracuseStep 2728595 = 4092893) B4092893
theorem B1819283 : Blo 1817610 1819283 := bstep (se 1 (by rfl) ⟨1364462, by rfl⟩ : syracuseStep 1819283 = 2728925) B2728925
theorem B5178019 : Blo 1817610 5178019 := bstep (se 1 (by rfl) ⟨3883514, by rfl⟩ : syracuseStep 5178019 = 7767029) B7767029
theorem B1819299 : Blo 1817610 1819299 := bstep (se 1 (by rfl) ⟨1364474, by rfl⟩ : syracuseStep 1819299 = 2728949) B2728949
theorem B7766705 : Blo 1817610 7766705 := bstep (se 2 (by rfl) ⟨2912514, by rfl⟩ : syracuseStep 7766705 = 5825029) B5825029
theorem B2728625 : Blo 1817610 2728625 := bstep (se 2 (by rfl) ⟨1023234, by rfl⟩ : syracuseStep 2728625 = 2046469) B2046469
theorem B1819315 : Blo 1817610 1819315 := bstep (se 1 (by rfl) ⟨1364486, by rfl⟩ : syracuseStep 1819315 = 2728973) B2728973
theorem B4915907 : Blo 1817610 4915907 := bstep (se 1 (by rfl) ⟨3686930, by rfl⟩ : syracuseStep 4915907 = 7373861) B7373861
theorem B2728643 : Blo 1817610 2728643 := bstep (se 1 (by rfl) ⟨2046482, by rfl⟩ : syracuseStep 2728643 = 4092965) B4092965
theorem B1819331 : Blo 1817610 1819331 := bstep (se 1 (by rfl) ⟨1364498, by rfl⟩ : syracuseStep 1819331 = 2728997) B2728997
theorem B1819347 : Blo 1817610 1819347 := bstep (se 1 (by rfl) ⟨1364510, by rfl⟩ : syracuseStep 1819347 = 2729021) B2729021
theorem B2728673 : Blo 1817610 2728673 := bstep (se 2 (by rfl) ⟨1023252, by rfl⟩ : syracuseStep 2728673 = 2046505) B2046505
theorem B1819363 : Blo 1817610 1819363 := bstep (se 1 (by rfl) ⟨1364522, by rfl⟩ : syracuseStep 1819363 = 2729045) B2729045
theorem B2728691 : Blo 1817610 2728691 := bstep (se 1 (by rfl) ⟨2046518, by rfl⟩ : syracuseStep 2728691 = 4093037) B4093037
theorem B1843955 : Blo 1817610 1843955 := bstep (se 1 (by rfl) ⟨1382966, by rfl⟩ : syracuseStep 1843955 = 2765933) B2765933
theorem B1819379 : Blo 1817610 1819379 := bstep (se 1 (by rfl) ⟨1364534, by rfl⟩ : syracuseStep 1819379 = 2729069) B2729069
theorem B1819395 : Blo 1817610 1819395 := bstep (se 1 (by rfl) ⟨1364546, by rfl⟩ : syracuseStep 1819395 = 2729093) B2729093
theorem B5825297 : Blo 1817610 5825297 := bstep (se 2 (by rfl) ⟨2184486, by rfl⟩ : syracuseStep 5825297 = 4368973) B4368973
theorem B2728721 : Blo 1817610 2728721 := bstep (se 2 (by rfl) ⟨1023270, by rfl⟩ : syracuseStep 2728721 = 2046541) B2046541
theorem B1819411 : Blo 1817610 1819411 := bstep (se 1 (by rfl) ⟨1364558, by rfl⟩ : syracuseStep 1819411 = 2729117) B2729117
theorem B2728739 : Blo 1817610 2728739 := bstep (se 1 (by rfl) ⟨2046554, by rfl⟩ : syracuseStep 2728739 = 4093109) B4093109
theorem B1819427 : Blo 1817610 1819427 := bstep (se 1 (by rfl) ⟨1364570, by rfl⟩ : syracuseStep 1819427 = 2729141) B2729141
theorem B1819443 : Blo 1817610 1819443 := bstep (se 1 (by rfl) ⟨1364582, by rfl⟩ : syracuseStep 1819443 = 2729165) B2729165
theorem B26272565 : Blo 1817610 26272565 := bstep (se 5 (by rfl) ⟨1231526, by rfl⟩ : syracuseStep 26272565 = 2463053) B2463053
theorem B2728769 : Blo 1817610 2728769 := bstep (se 2 (by rfl) ⟨1023288, by rfl⟩ : syracuseStep 2728769 = 2046577) B2046577
theorem B1819459 : Blo 1817610 1819459 := bstep (se 1 (by rfl) ⟨1364594, by rfl⟩ : syracuseStep 1819459 = 2729189) B2729189
theorem B2728787 : Blo 1817610 2728787 := bstep (se 1 (by rfl) ⟨2046590, by rfl⟩ : syracuseStep 2728787 = 4093181) B4093181
theorem B1819475 : Blo 1817610 1819475 := bstep (se 1 (by rfl) ⟨1364606, by rfl⟩ : syracuseStep 1819475 = 2729213) B2729213
theorem B1819491 : Blo 1817610 1819491 := bstep (se 1 (by rfl) ⟨1364618, by rfl⟩ : syracuseStep 1819491 = 2729237) B2729237
theorem B2728817 : Blo 1817610 2728817 := bstep (se 2 (by rfl) ⟨1023306, by rfl⟩ : syracuseStep 2728817 = 2046613) B2046613
theorem B1819507 : Blo 1817610 1819507 := bstep (se 1 (by rfl) ⟨1364630, by rfl⟩ : syracuseStep 1819507 = 2729261) B2729261
theorem B3883907 : Blo 1817610 3883907 := bstep (se 1 (by rfl) ⟨2912930, by rfl⟩ : syracuseStep 3883907 = 5825861) B5825861
theorem B2728835 : Blo 1817610 2728835 := bstep (se 1 (by rfl) ⟨2046626, by rfl⟩ : syracuseStep 2728835 = 4093253) B4093253
theorem B1819523 : Blo 1817610 1819523 := bstep (se 1 (by rfl) ⟨1364642, by rfl⟩ : syracuseStep 1819523 = 2729285) B2729285
theorem B6136721 : Blo 1817610 6136721 := bstep (se 2 (by rfl) ⟨2301270, by rfl⟩ : syracuseStep 6136721 = 4602541) B4602541
theorem B1819539 : Blo 1817610 1819539 := bstep (se 1 (by rfl) ⟨1364654, by rfl⟩ : syracuseStep 1819539 = 2729309) B2729309
theorem B2728865 : Blo 1817610 2728865 := bstep (se 2 (by rfl) ⟨1023324, by rfl⟩ : syracuseStep 2728865 = 2046649) B2046649
theorem B5530531 : Blo 1817610 5530531 := bstep (se 1 (by rfl) ⟨4147898, by rfl⟩ : syracuseStep 5530531 = 8295797) B8295797
theorem B1819555 : Blo 1817610 1819555 := bstep (se 1 (by rfl) ⟨1364666, by rfl⟩ : syracuseStep 1819555 = 2729333) B2729333
theorem B8299441 : Blo 1817610 8299441 := bstep (se 2 (by rfl) ⟨3112290, by rfl⟩ : syracuseStep 8299441 = 6224581) B6224581
theorem B2728883 : Blo 1817610 2728883 := bstep (se 1 (by rfl) ⟨2046662, by rfl⟩ : syracuseStep 2728883 = 4093325) B4093325
theorem B1819571 : Blo 1817610 1819571 := bstep (se 1 (by rfl) ⟨1364678, by rfl⟩ : syracuseStep 1819571 = 2729357) B2729357
theorem B1819587 : Blo 1817610 1819587 := bstep (se 1 (by rfl) ⟨1364690, by rfl⟩ : syracuseStep 1819587 = 2729381) B2729381
theorem B4916177 : Blo 1817610 4916177 := bstep (se 2 (by rfl) ⟨1843566, by rfl⟩ : syracuseStep 4916177 = 3687133) B3687133
theorem B2728913 : Blo 1817610 2728913 := bstep (se 2 (by rfl) ⟨1023342, by rfl⟩ : syracuseStep 2728913 = 2046685) B2046685
theorem B2302931 : Blo 1817610 2302931 := bstep (se 1 (by rfl) ⟨1727198, by rfl⟩ : syracuseStep 2302931 = 3454397) B3454397
theorem B1819603 : Blo 1817610 1819603 := bstep (se 1 (by rfl) ⟨1364702, by rfl⟩ : syracuseStep 1819603 = 2729405) B2729405
theorem B2728931 : Blo 1817610 2728931 := bstep (se 1 (by rfl) ⟨2046698, by rfl⟩ : syracuseStep 2728931 = 4093397) B4093397
theorem B2728961 : Blo 1817610 2728961 := bstep (se 2 (by rfl) ⟨1023360, by rfl⟩ : syracuseStep 2728961 = 2046721) B2046721
theorem B4727825 : Blo 1817610 4727825 := bstep (se 2 (by rfl) ⟨1772934, by rfl⟩ : syracuseStep 4727825 = 3545869) B3545869
theorem B2728979 : Blo 1817610 2728979 := bstep (se 1 (by rfl) ⟨2046734, by rfl⟩ : syracuseStep 2728979 = 4093469) B4093469
theorem B2729009 : Blo 1817610 2729009 := bstep (se 2 (by rfl) ⟨1023378, by rfl⟩ : syracuseStep 2729009 = 2046757) B2046757
theorem B2729027 : Blo 1817610 2729027 := bstep (se 1 (by rfl) ⟨2046770, by rfl⟩ : syracuseStep 2729027 = 4093541) B4093541
theorem B2729057 : Blo 1817610 2729057 := bstep (se 2 (by rfl) ⟨1023396, by rfl⟩ : syracuseStep 2729057 = 2046793) B2046793
theorem B5825645 : Blo 1817610 5825645 := bstep (se 3 (by rfl) ⟨1092308, by rfl⟩ : syracuseStep 5825645 = 2184617) B2184617
theorem B2729075 : Blo 1817610 2729075 := bstep (se 1 (by rfl) ⟨2046806, by rfl⟩ : syracuseStep 2729075 = 4093613) B4093613
theorem B17712269 : Blo 1817610 17712269 := bstep (se 3 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 17712269 = 6642101) B6642101
theorem B2589841 : Blo 1817610 2589841 := bstep (se 2 (by rfl) ⟨971190, by rfl⟩ : syracuseStep 2589841 = 1942381) B1942381
theorem B2729105 : Blo 1817610 2729105 := bstep (se 2 (by rfl) ⟨1023414, by rfl⟩ : syracuseStep 2729105 = 2046829) B2046829
theorem B5530787 : Blo 1817610 5530787 := bstep (se 1 (by rfl) ⟨4148090, by rfl⟩ : syracuseStep 5530787 = 8296181) B8296181
theorem B2729123 : Blo 1817610 2729123 := bstep (se 1 (by rfl) ⟨2046842, by rfl⟩ : syracuseStep 2729123 = 4093685) B4093685
theorem B2729153 : Blo 1817610 2729153 := bstep (se 2 (by rfl) ⟨1023432, by rfl⟩ : syracuseStep 2729153 = 2046865) B2046865
theorem B2491603 : Blo 1817610 2491603 := bstep (se 1 (by rfl) ⟨1868702, by rfl⟩ : syracuseStep 2491603 = 3737405) B3737405
theorem B2729171 : Blo 1817610 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B2729201 : Blo 1817610 2729201 := bstep (se 2 (by rfl) ⟨1023450, by rfl⟩ : syracuseStep 2729201 = 2046901) B2046901
theorem B2729219 : Blo 1817610 2729219 := bstep (se 1 (by rfl) ⟨2046914, by rfl⟩ : syracuseStep 2729219 = 4093829) B4093829
theorem B2729249 : Blo 1817610 2729249 := bstep (se 2 (by rfl) ⟨1023468, by rfl⟩ : syracuseStep 2729249 = 2046937) B2046937
theorem B2729267 : Blo 1817610 2729267 := bstep (se 1 (by rfl) ⟨2046950, by rfl⟩ : syracuseStep 2729267 = 4093901) B4093901
theorem B2729297 : Blo 1817610 2729297 := bstep (se 2 (by rfl) ⟨1023486, by rfl⟩ : syracuseStep 2729297 = 2046973) B2046973
theorem B13813091 : Blo 1817610 13813091 := bstep (se 1 (by rfl) ⟨10359818, by rfl⟩ : syracuseStep 13813091 = 20719637) B20719637
theorem B2729315 : Blo 1817610 2729315 := bstep (se 1 (by rfl) ⟨2046986, by rfl⟩ : syracuseStep 2729315 = 4093973) B4093973
theorem B2729345 : Blo 1817610 2729345 := bstep (se 2 (by rfl) ⟨1023504, by rfl⟩ : syracuseStep 2729345 = 2047009) B2047009
theorem B2729363 : Blo 1817610 2729363 := bstep (se 1 (by rfl) ⟨2047022, by rfl⟩ : syracuseStep 2729363 = 4094045) B4094045
theorem B6137261 : Blo 1817610 6137261 := bstep (se 3 (by rfl) ⟨1150736, by rfl⟩ : syracuseStep 6137261 = 2301473) B2301473
theorem B2729393 : Blo 1817610 2729393 := bstep (se 2 (by rfl) ⟨1023522, by rfl⟩ : syracuseStep 2729393 = 2047045) B2047045
theorem B2729411 : Blo 1817610 2729411 := bstep (se 1 (by rfl) ⟨2047058, by rfl⟩ : syracuseStep 2729411 = 4094117) B4094117
theorem B6137315 : Blo 1817610 6137315 := bstep (se 1 (by rfl) ⟨4602986, by rfl⟩ : syracuseStep 6137315 = 9205973) B9205973
theorem B4605457 : Blo 1817610 4605457 := bstep (se 2 (by rfl) ⟨1727046, by rfl⟩ : syracuseStep 4605457 = 3454093) B3454093
theorem B6907427 : Blo 1817610 6907427 := bstep (se 1 (by rfl) ⟨5180570, by rfl⟩ : syracuseStep 6907427 = 10361141) B10361141
theorem B11060813 : Blo 1817610 11060813 := bstep (se 3 (by rfl) ⟨2073902, by rfl⟩ : syracuseStep 11060813 = 4147805) B4147805
theorem B19654325 : Blo 1817610 19654325 := bstep (se 5 (by rfl) ⟨921296, by rfl⟩ : syracuseStep 19654325 = 1842593) B1842593
theorem B6137585 : Blo 1817610 6137585 := bstep (se 2 (by rfl) ⟨2301594, by rfl⟩ : syracuseStep 6137585 = 4603189) B4603189
theorem B4089635 : Blo 1817610 4089635 := bstep (se 1 (by rfl) ⟨3067226, by rfl⟩ : syracuseStep 4089635 = 6134453) B6134453
theorem B4605731 : Blo 1817610 4605731 := bstep (se 1 (by rfl) ⟨3454298, by rfl⟩ : syracuseStep 4605731 = 6908597) B6908597
theorem B4917041 : Blo 1817610 4917041 := bstep (se 2 (by rfl) ⟨1843890, by rfl⟩ : syracuseStep 4917041 = 3687781) B3687781
theorem B3450691 : Blo 1817610 3450691 := bstep (se 1 (by rfl) ⟨2588018, by rfl⟩ : syracuseStep 3450691 = 5176037) B5176037
theorem B2590547 : Blo 1817610 2590547 := bstep (se 1 (by rfl) ⟨1942910, by rfl⟩ : syracuseStep 2590547 = 3885821) B3885821
theorem B9209699 : Blo 1817610 9209699 := bstep (se 1 (by rfl) ⟨6907274, by rfl⟩ : syracuseStep 9209699 = 13814549) B13814549
theorem B3450737 : Blo 1817610 3450737 := bstep (se 2 (by rfl) ⟨1294026, by rfl⟩ : syracuseStep 3450737 = 2588053) B2588053
theorem B2623409 : Blo 1817610 2623409 := bstep (se 2 (by rfl) ⟨983778, by rfl⟩ : syracuseStep 2623409 = 1967557) B1967557
theorem B5179409 : Blo 1817610 5179409 := bstep (se 2 (by rfl) ⟨1942278, by rfl⟩ : syracuseStep 5179409 = 3884557) B3884557
theorem B4089905 : Blo 1817610 4089905 := bstep (se 2 (by rfl) ⟨1533714, by rfl⟩ : syracuseStep 4089905 = 3067429) B3067429
theorem B4089923 : Blo 1817610 4089923 := bstep (se 1 (by rfl) ⟨3067442, by rfl⟩ : syracuseStep 4089923 = 6134885) B6134885
theorem B3885155 : Blo 1817610 3885155 := bstep (se 1 (by rfl) ⟨2913866, by rfl⟩ : syracuseStep 3885155 = 5827733) B5827733
theorem B40962161 : Blo 1817610 40962161 := bstep (se 2 (by rfl) ⟨15360810, by rfl⟩ : syracuseStep 40962161 = 30721621) B30721621
theorem B3451025 : Blo 1817610 3451025 := bstep (se 2 (by rfl) ⟨1294134, by rfl⟩ : syracuseStep 3451025 = 2588269) B2588269
theorem B6138125 : Blo 1817610 6138125 := bstep (se 3 (by rfl) ⟨1150898, by rfl⟩ : syracuseStep 6138125 = 2301797) B2301797
theorem B6138179 : Blo 1817610 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B4090193 : Blo 1817610 4090193 := bstep (se 2 (by rfl) ⟨1533822, by rfl⟩ : syracuseStep 4090193 = 3067645) B3067645
theorem B4090211 : Blo 1817610 4090211 := bstep (se 1 (by rfl) ⟨3067658, by rfl⟩ : syracuseStep 4090211 = 6135317) B6135317
theorem B5532013 : Blo 1817610 5532013 := bstep (se 3 (by rfl) ⟨1037252, by rfl⟩ : syracuseStep 5532013 = 2074505) B2074505
theorem B6220205 : Blo 1817610 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B22432241 : Blo 1817610 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B6908429 : Blo 1817610 6908429 := bstep (se 3 (by rfl) ⟨1295330, by rfl⟩ : syracuseStep 6908429 = 2590661) B2590661
theorem B6138449 : Blo 1817610 6138449 := bstep (se 2 (by rfl) ⟨2301918, by rfl⟩ : syracuseStep 6138449 = 4603837) B4603837
theorem B4090481 : Blo 1817610 4090481 := bstep (se 2 (by rfl) ⟨1533930, by rfl⟩ : syracuseStep 4090481 = 3067861) B3067861
theorem B4090499 : Blo 1817610 4090499 := bstep (se 1 (by rfl) ⟨3067874, by rfl⟩ : syracuseStep 4090499 = 6135749) B6135749
theorem B4147843 : Blo 1817610 4147843 := bstep (se 1 (by rfl) ⟨3110882, by rfl⟩ : syracuseStep 4147843 = 6221765) B6221765
theorem B9210509 : Blo 1817610 9210509 := bstep (se 3 (by rfl) ⟨1726970, by rfl⟩ : syracuseStep 9210509 = 3453941) B3453941
theorem B3885745 : Blo 1817610 3885745 := bstep (se 2 (by rfl) ⟨1457154, by rfl⟩ : syracuseStep 3885745 = 2914309) B2914309
theorem B3451747 : Blo 1817610 3451747 := bstep (se 1 (by rfl) ⟨2588810, by rfl⟩ : syracuseStep 3451747 = 5177621) B5177621
theorem B4090769 : Blo 1817610 4090769 := bstep (se 2 (by rfl) ⟨1534038, by rfl⟩ : syracuseStep 4090769 = 3068077) B3068077
theorem B4090787 : Blo 1817610 4090787 := bstep (se 1 (by rfl) ⟨3068090, by rfl⟩ : syracuseStep 4090787 = 6136181) B6136181
theorem B5827501 : Blo 1817610 5827501 := bstep (se 3 (by rfl) ⟨1092656, by rfl⟩ : syracuseStep 5827501 = 2185313) B2185313
theorem B5180365 : Blo 1817610 5180365 := bstep (se 3 (by rfl) ⟨971318, by rfl⟩ : syracuseStep 5180365 = 1942637) B1942637
theorem B6138989 : Blo 1817610 6138989 := bstep (se 3 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 6138989 = 2302121) B2302121
theorem B6139043 : Blo 1817610 6139043 := bstep (se 1 (by rfl) ⟨4604282, by rfl⟩ : syracuseStep 6139043 = 9208565) B9208565
theorem B4091057 : Blo 1817610 4091057 := bstep (se 2 (by rfl) ⟨1534146, by rfl⟩ : syracuseStep 4091057 = 3068293) B3068293
theorem B5180593 : Blo 1817610 5180593 := bstep (se 2 (by rfl) ⟨1942722, by rfl⟩ : syracuseStep 5180593 = 3885445) B3885445
theorem B4091075 : Blo 1817610 4091075 := bstep (se 1 (by rfl) ⟨3068306, by rfl⟩ : syracuseStep 4091075 = 6136613) B6136613
theorem B13102307 : Blo 1817610 13102307 := bstep (se 1 (by rfl) ⟨9826730, by rfl⟩ : syracuseStep 13102307 = 19653461) B19653461
theorem B18910435 : Blo 1817610 18910435 := bstep (se 1 (by rfl) ⟨14182826, by rfl⟩ : syracuseStep 18910435 = 28365653) B28365653
theorem B3452195 : Blo 1817610 3452195 := bstep (se 1 (by rfl) ⟨2589146, by rfl⟩ : syracuseStep 3452195 = 5178293) B5178293
theorem B5180753 : Blo 1817610 5180753 := bstep (se 2 (by rfl) ⟨1942782, by rfl⟩ : syracuseStep 5180753 = 3885565) B3885565
theorem B9203057 : Blo 1817610 9203057 := bstep (se 2 (by rfl) ⟨3451146, by rfl⟩ : syracuseStep 9203057 = 6902293) B6902293
theorem B3067267 : Blo 1817610 3067267 := bstep (se 1 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 3067267 = 4600901) B4600901
theorem B6139313 : Blo 1817610 6139313 := bstep (se 2 (by rfl) ⟨2302242, by rfl⟩ : syracuseStep 6139313 = 4604485) B4604485
theorem B5180867 : Blo 1817610 5180867 := bstep (se 1 (by rfl) ⟨3885650, by rfl⟩ : syracuseStep 5180867 = 7771301) B7771301
theorem B4091345 : Blo 1817610 4091345 := bstep (se 2 (by rfl) ⟨1534254, by rfl⟩ : syracuseStep 4091345 = 3068509) B3068509
theorem B8293859 : Blo 1817610 8293859 := bstep (se 1 (by rfl) ⟨6220394, by rfl⟩ : syracuseStep 8293859 = 12440789) B12440789
theorem B4091363 : Blo 1817610 4091363 := bstep (se 1 (by rfl) ⟨3068522, by rfl⟩ : syracuseStep 4091363 = 6137045) B6137045
theorem B3067409 : Blo 1817610 3067409 := bstep (se 2 (by rfl) ⟨1150278, by rfl⟩ : syracuseStep 3067409 = 2300557) B2300557
theorem B3452483 : Blo 1817610 3452483 := bstep (se 1 (by rfl) ⟨2589362, by rfl⟩ : syracuseStep 3452483 = 5178725) B5178725
theorem B3067537 : Blo 1817610 3067537 := bstep (se 2 (by rfl) ⟨1150326, by rfl⟩ : syracuseStep 3067537 = 2300653) B2300653
theorem B3067571 : Blo 1817610 3067571 := bstep (se 1 (by rfl) ⟨2300678, by rfl⟩ : syracuseStep 3067571 = 4601357) B4601357
theorem B4091633 : Blo 1817610 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B4091651 : Blo 1817610 4091651 := bstep (se 1 (by rfl) ⟨3068738, by rfl⟩ : syracuseStep 4091651 = 6137477) B6137477
theorem B14741261 : Blo 1817610 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B3067699 : Blo 1817610 3067699 := bstep (se 1 (by rfl) ⟨2300774, by rfl⟩ : syracuseStep 3067699 = 4601549) B4601549
theorem B3067841 : Blo 1817610 3067841 := bstep (se 2 (by rfl) ⟨1150440, by rfl⟩ : syracuseStep 3067841 = 2300881) B2300881
theorem B10358725 : Blo 1817610 10358725 := bstep (se 4 (by rfl) ⟨971130, by rfl⟩ : syracuseStep 10358725 = 1942261) B1942261
theorem B6139853 : Blo 1817610 6139853 := bstep (se 3 (by rfl) ⟨1151222, by rfl⟩ : syracuseStep 6139853 = 2302445) B2302445
theorem B6139907 : Blo 1817610 6139907 := bstep (se 1 (by rfl) ⟨4604930, by rfl⟩ : syracuseStep 6139907 = 9209861) B9209861
theorem B4091921 : Blo 1817610 4091921 := bstep (se 2 (by rfl) ⟨1534470, by rfl⟩ : syracuseStep 4091921 = 3068941) B3068941
theorem B4091939 : Blo 1817610 4091939 := bstep (se 1 (by rfl) ⟨3068954, by rfl⟩ : syracuseStep 4091939 = 6137909) B6137909
theorem B3067969 : Blo 1817610 3067969 := bstep (se 2 (by rfl) ⟨1150488, by rfl⟩ : syracuseStep 3067969 = 2300977) B2300977
theorem B3068003 : Blo 1817610 3068003 := bstep (se 1 (by rfl) ⟨2301002, by rfl⟩ : syracuseStep 3068003 = 4602005) B4602005
theorem B2953363 : Blo 1817610 2953363 := bstep (se 1 (by rfl) ⟨2215022, by rfl⟩ : syracuseStep 2953363 = 4430045) B4430045
theorem B10498211 : Blo 1817610 10498211 := bstep (se 1 (by rfl) ⟨7873658, by rfl⟩ : syracuseStep 10498211 = 15747317) B15747317
theorem B7770275 : Blo 1817610 7770275 := bstep (se 1 (by rfl) ⟨5827706, by rfl⟩ : syracuseStep 7770275 = 11655413) B11655413
theorem B3068131 : Blo 1817610 3068131 := bstep (se 1 (by rfl) ⟨2301098, by rfl⟩ : syracuseStep 3068131 = 4602197) B4602197
theorem B6140177 : Blo 1817610 6140177 := bstep (se 2 (by rfl) ⟨2302566, by rfl⟩ : syracuseStep 6140177 = 4605133) B4605133
theorem B4092209 : Blo 1817610 4092209 := bstep (se 2 (by rfl) ⟨1534578, by rfl⟩ : syracuseStep 4092209 = 3069157) B3069157
theorem B4092227 : Blo 1817610 4092227 := bstep (se 1 (by rfl) ⟨3069170, by rfl⟩ : syracuseStep 4092227 = 6138341) B6138341
theorem B33616241 : Blo 1817610 33616241 := bstep (se 2 (by rfl) ⟨12606090, by rfl⟩ : syracuseStep 33616241 = 25212181) B25212181
theorem B3068273 : Blo 1817610 3068273 := bstep (se 2 (by rfl) ⟨1150602, by rfl⟩ : syracuseStep 3068273 = 2301205) B2301205
theorem B9834929 : Blo 1817610 9834929 := bstep (se 2 (by rfl) ⟨3688098, by rfl⟩ : syracuseStep 9834929 = 7376197) B7376197
theorem B17469893 : Blo 1817610 17469893 := bstep (se 4 (by rfl) ⟨1637802, by rfl⟩ : syracuseStep 17469893 = 3275605) B3275605
theorem B4665809 : Blo 1817610 4665809 := bstep (se 2 (by rfl) ⟨1749678, by rfl⟩ : syracuseStep 4665809 = 3499357) B3499357
theorem B3068401 : Blo 1817610 3068401 := bstep (se 2 (by rfl) ⟨1150650, by rfl⟩ : syracuseStep 3068401 = 2301301) B2301301
theorem B3453425 : Blo 1817610 3453425 := bstep (se 2 (by rfl) ⟨1295034, by rfl⟩ : syracuseStep 3453425 = 2590069) B2590069
theorem B7877105 : Blo 1817610 7877105 := bstep (se 2 (by rfl) ⟨2953914, by rfl⟩ : syracuseStep 7877105 = 5907829) B5907829
theorem B3068435 : Blo 1817610 3068435 := bstep (se 1 (by rfl) ⟨2301326, by rfl⟩ : syracuseStep 3068435 = 4602653) B4602653
theorem B4092497 : Blo 1817610 4092497 := bstep (se 2 (by rfl) ⟨1534686, by rfl⟩ : syracuseStep 4092497 = 3069373) B3069373
theorem B4092515 : Blo 1817610 4092515 := bstep (se 1 (by rfl) ⟨3069386, by rfl⟩ : syracuseStep 4092515 = 6138773) B6138773
theorem B3068563 : Blo 1817610 3068563 := bstep (se 1 (by rfl) ⟨2301422, by rfl⟩ : syracuseStep 3068563 = 4602845) B4602845
theorem B2765539 : Blo 1817610 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B2765587 : Blo 1817610 2765587 := bstep (se 1 (by rfl) ⟨2074190, by rfl⟩ : syracuseStep 2765587 = 4148381) B4148381
theorem B3068705 : Blo 1817610 3068705 := bstep (se 2 (by rfl) ⟨1150764, by rfl⟩ : syracuseStep 3068705 = 2301529) B2301529
theorem B9204515 : Blo 1817610 9204515 := bstep (se 1 (by rfl) ⟨6903386, by rfl⟩ : syracuseStep 9204515 = 13806773) B13806773
theorem B2913059 : Blo 1817610 2913059 := bstep (se 1 (by rfl) ⟨2184794, by rfl⟩ : syracuseStep 2913059 = 4369589) B4369589
theorem B6140717 : Blo 1817610 6140717 := bstep (se 3 (by rfl) ⟨1151384, by rfl⟩ : syracuseStep 6140717 = 2302769) B2302769
theorem B2954051 : Blo 1817610 2954051 := bstep (se 1 (by rfl) ⟨2215538, by rfl⟩ : syracuseStep 2954051 = 4431077) B4431077
theorem B4666193 : Blo 1817610 4666193 := bstep (se 2 (by rfl) ⟨1749822, by rfl⟩ : syracuseStep 4666193 = 3499645) B3499645
theorem B6140771 : Blo 1817610 6140771 := bstep (se 1 (by rfl) ⟨4605578, by rfl⟩ : syracuseStep 6140771 = 9211157) B9211157
theorem B4092785 : Blo 1817610 4092785 := bstep (se 2 (by rfl) ⟨1534794, by rfl⟩ : syracuseStep 4092785 = 3069589) B3069589
theorem B4092803 : Blo 1817610 4092803 := bstep (se 1 (by rfl) ⟨3069602, by rfl⟩ : syracuseStep 4092803 = 6139205) B6139205
theorem B3068833 : Blo 1817610 3068833 := bstep (se 2 (by rfl) ⟨1150812, by rfl⟩ : syracuseStep 3068833 = 2301625) B2301625
theorem B2913187 : Blo 1817610 2913187 := bstep (se 1 (by rfl) ⟨2184890, by rfl⟩ : syracuseStep 2913187 = 4369781) B4369781
theorem B2044867 : Blo 1817610 2044867 := bstep (se 1 (by rfl) ⟨1533650, by rfl⟩ : syracuseStep 2044867 = 3067301) B3067301
theorem B3068867 : Blo 1817610 3068867 := bstep (se 1 (by rfl) ⟨2301650, by rfl⟩ : syracuseStep 3068867 = 4603301) B4603301
theorem B2913251 : Blo 1817610 2913251 := bstep (se 1 (by rfl) ⟨2184938, by rfl⟩ : syracuseStep 2913251 = 4369877) B4369877
theorem B2184179 : Blo 1817610 2184179 := bstep (se 1 (by rfl) ⟨1638134, by rfl⟩ : syracuseStep 2184179 = 3276269) B3276269
theorem B11645957 : Blo 1817610 11645957 := bstep (se 4 (by rfl) ⟨1091808, by rfl⟩ : syracuseStep 11645957 = 2183617) B2183617
theorem B3068995 : Blo 1817610 3068995 := bstep (se 1 (by rfl) ⟨2301746, by rfl⟩ : syracuseStep 3068995 = 4603493) B4603493
theorem B2045011 : Blo 1817610 2045011 := bstep (se 1 (by rfl) ⟨1533758, by rfl⟩ : syracuseStep 2045011 = 3067517) B3067517
theorem B6141041 : Blo 1817610 6141041 := bstep (se 2 (by rfl) ⟨2302890, by rfl⟩ : syracuseStep 6141041 = 4605781) B4605781
theorem B4093073 : Blo 1817610 4093073 := bstep (se 2 (by rfl) ⟨1534902, by rfl⟩ : syracuseStep 4093073 = 3069805) B3069805
theorem B11367587 : Blo 1817610 11367587 := bstep (se 1 (by rfl) ⟨8525690, by rfl⟩ : syracuseStep 11367587 = 17051381) B17051381
theorem B4093091 : Blo 1817610 4093091 := bstep (se 1 (by rfl) ⟨3069818, by rfl⟩ : syracuseStep 4093091 = 6139637) B6139637
theorem B3069137 : Blo 1817610 3069137 := bstep (se 2 (by rfl) ⟨1150926, by rfl⟩ : syracuseStep 3069137 = 2301853) B2301853
theorem B2045155 : Blo 1817610 2045155 := bstep (se 1 (by rfl) ⟨1533866, by rfl⟩ : syracuseStep 2045155 = 3067733) B3067733
theorem B6903053 : Blo 1817610 6903053 := bstep (se 3 (by rfl) ⟨1294322, by rfl⟩ : syracuseStep 6903053 = 2588645) B2588645
theorem B9835811 : Blo 1817610 9835811 := bstep (se 1 (by rfl) ⟨7376858, by rfl⟩ : syracuseStep 9835811 = 14753717) B14753717
theorem B4371779 : Blo 1817610 4371779 := bstep (se 1 (by rfl) ⟨3278834, by rfl⟩ : syracuseStep 4371779 = 6557669) B6557669
theorem B3069265 : Blo 1817610 3069265 := bstep (se 2 (by rfl) ⟨1150974, by rfl⟩ : syracuseStep 3069265 = 2301949) B2301949
theorem B13104497 : Blo 1817610 13104497 := bstep (se 2 (by rfl) ⟨4914186, by rfl⟩ : syracuseStep 13104497 = 9828373) B9828373
theorem B3454321 : Blo 1817610 3454321 := bstep (se 2 (by rfl) ⟨1295370, by rfl⟩ : syracuseStep 3454321 = 2590741) B2590741
theorem B2045299 : Blo 1817610 2045299 := bstep (se 1 (by rfl) ⟨1533974, by rfl⟩ : syracuseStep 2045299 = 3067949) B3067949
theorem B3069299 : Blo 1817610 3069299 := bstep (se 1 (by rfl) ⟨2301974, by rfl⟩ : syracuseStep 3069299 = 4603949) B4603949
theorem B4371857 : Blo 1817610 4371857 := bstep (se 2 (by rfl) ⟨1639446, by rfl⟩ : syracuseStep 4371857 = 3278893) B3278893
theorem B4093361 : Blo 1817610 4093361 := bstep (se 2 (by rfl) ⟨1535010, by rfl⟩ : syracuseStep 4093361 = 3070021) B3070021
theorem B4093379 : Blo 1817610 4093379 := bstep (se 1 (by rfl) ⟨3070034, by rfl⟩ : syracuseStep 4093379 = 6140069) B6140069
theorem B2913745 : Blo 1817610 2913745 := bstep (se 2 (by rfl) ⟨1092654, by rfl⟩ : syracuseStep 2913745 = 2185309) B2185309
theorem B3069427 : Blo 1817610 3069427 := bstep (se 1 (by rfl) ⟨2302070, by rfl⟩ : syracuseStep 3069427 = 4604141) B4604141
theorem B2045443 : Blo 1817610 2045443 := bstep (se 1 (by rfl) ⟨1534082, by rfl⟩ : syracuseStep 2045443 = 3068165) B3068165
theorem B6641165 : Blo 1817610 6641165 := bstep (se 3 (by rfl) ⟨1245218, by rfl⟩ : syracuseStep 6641165 = 2490437) B2490437
theorem B9205325 : Blo 1817610 9205325 := bstep (se 3 (by rfl) ⟨1725998, by rfl⟩ : syracuseStep 9205325 = 3451997) B3451997
theorem B3069569 : Blo 1817610 3069569 := bstep (se 2 (by rfl) ⟨1151088, by rfl⟩ : syracuseStep 3069569 = 2302177) B2302177
theorem B2045587 : Blo 1817610 2045587 := bstep (se 1 (by rfl) ⟨1534190, by rfl⟩ : syracuseStep 2045587 = 3068381) B3068381
theorem B5469869 : Blo 1817610 5469869 := bstep (se 3 (by rfl) ⟨1025600, by rfl⟩ : syracuseStep 5469869 = 2051201) B2051201
theorem B4093649 : Blo 1817610 4093649 := bstep (se 2 (by rfl) ⟨1535118, by rfl⟩ : syracuseStep 4093649 = 3070237) B3070237
theorem B4093667 : Blo 1817610 4093667 := bstep (se 1 (by rfl) ⟨3070250, by rfl⟩ : syracuseStep 4093667 = 6140501) B6140501
theorem B3069697 : Blo 1817610 3069697 := bstep (se 2 (by rfl) ⟨1151136, by rfl⟩ : syracuseStep 3069697 = 2302273) B2302273
theorem B2045731 : Blo 1817610 2045731 := bstep (se 1 (by rfl) ⟨1534298, by rfl⟩ : syracuseStep 2045731 = 3068597) B3068597
theorem B3069731 : Blo 1817610 3069731 := bstep (se 1 (by rfl) ⟨2302298, by rfl⟩ : syracuseStep 3069731 = 4604597) B4604597
theorem B4601681 : Blo 1817610 4601681 := bstep (se 2 (by rfl) ⟨1725630, by rfl⟩ : syracuseStep 4601681 = 3451261) B3451261
theorem B4552529 : Blo 1817610 4552529 := bstep (se 2 (by rfl) ⟨1707198, by rfl⟩ : syracuseStep 4552529 = 3414397) B3414397
theorem B4601731 : Blo 1817610 4601731 := bstep (se 1 (by rfl) ⟨3451298, by rfl⟩ : syracuseStep 4601731 = 6902597) B6902597
theorem B10360709 : Blo 1817610 10360709 := bstep (se 4 (by rfl) ⟨971316, by rfl⟩ : syracuseStep 10360709 = 1942633) B1942633
theorem B3069859 : Blo 1817610 3069859 := bstep (se 1 (by rfl) ⟨2302394, by rfl⟩ : syracuseStep 3069859 = 4604789) B4604789
theorem B2045875 : Blo 1817610 2045875 := bstep (se 1 (by rfl) ⟨1534406, by rfl⟩ : syracuseStep 2045875 = 3068813) B3068813
theorem B4093937 : Blo 1817610 4093937 := bstep (se 2 (by rfl) ⟨1535226, by rfl⟩ : syracuseStep 4093937 = 3070453) B3070453
theorem B4093955 : Blo 1817610 4093955 := bstep (se 1 (by rfl) ⟨3070466, by rfl⟩ : syracuseStep 4093955 = 6140933) B6140933
theorem B4601873 : Blo 1817610 4601873 := bstep (se 2 (by rfl) ⟨1725702, by rfl⟩ : syracuseStep 4601873 = 3451405) B3451405
theorem B3070001 : Blo 1817610 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B2046019 : Blo 1817610 2046019 := bstep (se 1 (by rfl) ⟨1534514, by rfl⟩ : syracuseStep 2046019 = 3069029) B3069029
theorem B2914417 : Blo 1817610 2914417 := bstep (se 2 (by rfl) ⟨1092906, by rfl⟩ : syracuseStep 2914417 = 2185813) B2185813
theorem B3070129 : Blo 1817610 3070129 := bstep (se 2 (by rfl) ⟨1151298, by rfl⟩ : syracuseStep 3070129 = 2302597) B2302597
theorem B2046163 : Blo 1817610 2046163 := bstep (se 1 (by rfl) ⟨1534622, by rfl⟩ : syracuseStep 2046163 = 3069245) B3069245
theorem B3070163 : Blo 1817610 3070163 := bstep (se 1 (by rfl) ⟨2302622, by rfl⟩ : syracuseStep 3070163 = 4605245) B4605245
theorem B13105421 : Blo 1817610 13105421 := bstep (se 3 (by rfl) ⟨2457266, by rfl⟩ : syracuseStep 13105421 = 4914533) B4914533
theorem B9836849 : Blo 1817610 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B3070291 : Blo 1817610 3070291 := bstep (se 1 (by rfl) ⟨2302718, by rfl⟩ : syracuseStep 3070291 = 4605437) B4605437
theorem B2046307 : Blo 1817610 2046307 := bstep (se 1 (by rfl) ⟨1534730, by rfl⟩ : syracuseStep 2046307 = 3069461) B3069461
theorem B11065733 : Blo 1817610 11065733 := bstep (se 4 (by rfl) ⟨1037412, by rfl⟩ : syracuseStep 11065733 = 2074825) B2074825
theorem B3111347 : Blo 1817610 3111347 := bstep (se 1 (by rfl) ⟨2333510, by rfl⟩ : syracuseStep 3111347 = 4667021) B4667021
theorem B3070433 : Blo 1817610 3070433 := bstep (se 2 (by rfl) ⟨1151412, by rfl⟩ : syracuseStep 3070433 = 2302825) B2302825
theorem B2046451 : Blo 1817610 2046451 := bstep (se 1 (by rfl) ⟨1534838, by rfl⟩ : syracuseStep 2046451 = 3069677) B3069677
theorem B2726417 : Blo 1817610 2726417 := bstep (se 2 (by rfl) ⟨1022406, by rfl⟩ : syracuseStep 2726417 = 2044813) B2044813
theorem B2726435 : Blo 1817610 2726435 := bstep (se 1 (by rfl) ⟨2044826, by rfl⟩ : syracuseStep 2726435 = 4089653) B4089653
theorem B2726465 : Blo 1817610 2726465 := bstep (se 2 (by rfl) ⟨1022424, by rfl⟩ : syracuseStep 2726465 = 2044849) B2044849
theorem B2726483 : Blo 1817610 2726483 := bstep (se 1 (by rfl) ⟨2044862, by rfl⟩ : syracuseStep 2726483 = 4089725) B4089725
theorem B3070561 : Blo 1817610 3070561 := bstep (se 2 (by rfl) ⟨1151460, by rfl⟩ : syracuseStep 3070561 = 2302921) B2302921
theorem B2726513 : Blo 1817610 2726513 := bstep (se 2 (by rfl) ⟨1022442, by rfl⟩ : syracuseStep 2726513 = 2044885) B2044885
theorem B2726531 : Blo 1817610 2726531 := bstep (se 1 (by rfl) ⟨2044898, by rfl⟩ : syracuseStep 2726531 = 4089797) B4089797
theorem B2046595 : Blo 1817610 2046595 := bstep (se 1 (by rfl) ⟨1534946, by rfl⟩ : syracuseStep 2046595 = 3069893) B3069893
theorem B2726561 : Blo 1817610 2726561 := bstep (se 2 (by rfl) ⟨1022460, by rfl⟩ : syracuseStep 2726561 = 2044921) B2044921
theorem B5323427 : Blo 1817610 5323427 := bstep (se 1 (by rfl) ⟨3992570, by rfl⟩ : syracuseStep 5323427 = 7985141) B7985141
theorem B2726579 : Blo 1817610 2726579 := bstep (se 1 (by rfl) ⟨2044934, by rfl⟩ : syracuseStep 2726579 = 4089869) B4089869
theorem B2726609 : Blo 1817610 2726609 := bstep (se 2 (by rfl) ⟨1022478, by rfl⟩ : syracuseStep 2726609 = 2044957) B2044957
theorem B3275491 : Blo 1817610 3275491 := bstep (se 1 (by rfl) ⟨2456618, by rfl⟩ : syracuseStep 3275491 = 4913237) B4913237
theorem B2726627 : Blo 1817610 2726627 := bstep (se 1 (by rfl) ⟨2044970, by rfl⟩ : syracuseStep 2726627 = 4089941) B4089941
theorem B2726657 : Blo 1817610 2726657 := bstep (se 2 (by rfl) ⟨1022496, by rfl⟩ : syracuseStep 2726657 = 2044993) B2044993
theorem B2726675 : Blo 1817610 2726675 := bstep (se 1 (by rfl) ⟨2045006, by rfl⟩ : syracuseStep 2726675 = 4090013) B4090013
theorem B2046739 : Blo 1817610 2046739 := bstep (se 1 (by rfl) ⟨1535054, by rfl⟩ : syracuseStep 2046739 = 3070109) B3070109
theorem B2726705 : Blo 1817610 2726705 := bstep (se 2 (by rfl) ⟨1022514, by rfl⟩ : syracuseStep 2726705 = 2045029) B2045029
theorem B2726723 : Blo 1817610 2726723 := bstep (se 1 (by rfl) ⟨2045042, by rfl⟩ : syracuseStep 2726723 = 4090085) B4090085
theorem B2726753 : Blo 1817610 2726753 := bstep (se 2 (by rfl) ⟨1022532, by rfl⟩ : syracuseStep 2726753 = 2045065) B2045065
theorem B5176163 : Blo 1817610 5176163 := bstep (se 1 (by rfl) ⟨3882122, by rfl⟩ : syracuseStep 5176163 = 7764245) B7764245
theorem B8739697 : Blo 1817610 8739697 := bstep (se 2 (by rfl) ⟨3277386, by rfl⟩ : syracuseStep 8739697 = 6554773) B6554773
theorem B2726771 : Blo 1817610 2726771 := bstep (se 1 (by rfl) ⟨2045078, by rfl⟩ : syracuseStep 2726771 = 4090157) B4090157
theorem B2841475 : Blo 1817610 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B6134669 : Blo 1817610 6134669 := bstep (se 3 (by rfl) ⟨1150250, by rfl⟩ : syracuseStep 6134669 = 2300501) B2300501
theorem B2726801 : Blo 1817610 2726801 := bstep (se 2 (by rfl) ⟨1022550, by rfl⟩ : syracuseStep 2726801 = 2045101) B2045101
theorem B2726819 : Blo 1817610 2726819 := bstep (se 1 (by rfl) ⟨2045114, by rfl⟩ : syracuseStep 2726819 = 4090229) B4090229
theorem B2046883 : Blo 1817610 2046883 := bstep (se 1 (by rfl) ⟨1535162, by rfl⟩ : syracuseStep 2046883 = 3070325) B3070325
theorem B2726849 : Blo 1817610 2726849 := bstep (se 2 (by rfl) ⟨1022568, by rfl⟩ : syracuseStep 2726849 = 2045137) B2045137
theorem B6134723 : Blo 1817610 6134723 := bstep (se 1 (by rfl) ⟨4601042, by rfl⟩ : syracuseStep 6134723 = 9202085) B9202085
theorem B5823427 : Blo 1817610 5823427 := bstep (se 1 (by rfl) ⟨4367570, by rfl⟩ : syracuseStep 5823427 = 8735141) B8735141
theorem B2726867 : Blo 1817610 2726867 := bstep (se 1 (by rfl) ⟨2045150, by rfl⟩ : syracuseStep 2726867 = 4090301) B4090301
theorem B5528557 : Blo 1817610 5528557 := bstep (se 3 (by rfl) ⟨1036604, by rfl⟩ : syracuseStep 5528557 = 2073209) B2073209
theorem B2726897 : Blo 1817610 2726897 := bstep (se 2 (by rfl) ⟨1022586, by rfl⟩ : syracuseStep 2726897 = 2045173) B2045173
theorem B4602865 : Blo 1817610 4602865 := bstep (se 2 (by rfl) ⟨1726074, by rfl⟩ : syracuseStep 4602865 = 3452149) B3452149
theorem B2726915 : Blo 1817610 2726915 := bstep (se 1 (by rfl) ⟨2045186, by rfl⟩ : syracuseStep 2726915 = 4090373) B4090373
theorem B4914179 : Blo 1817610 4914179 := bstep (se 1 (by rfl) ⟨3685634, by rfl⟩ : syracuseStep 4914179 = 7371269) B7371269
theorem B1817619 : Blo 1817610 1817619 := bstep (se 1 (by rfl) ⟨1363214, by rfl⟩ : syracuseStep 1817619 = 2726429) B2726429
theorem B2726945 : Blo 1817610 2726945 := bstep (se 2 (by rfl) ⟨1022604, by rfl⟩ : syracuseStep 2726945 = 2045209) B2045209
theorem B1817635 : Blo 1817610 1817635 := bstep (se 1 (by rfl) ⟨1363226, by rfl⟩ : syracuseStep 1817635 = 2726453) B2726453
theorem B1817651 : Blo 1817610 1817651 := bstep (se 1 (by rfl) ⟨1363238, by rfl⟩ : syracuseStep 1817651 = 2726477) B2726477
theorem B2726963 : Blo 1817610 2726963 := bstep (se 1 (by rfl) ⟨2045222, by rfl⟩ : syracuseStep 2726963 = 4090445) B4090445
theorem B2047027 : Blo 1817610 2047027 := bstep (se 1 (by rfl) ⟨1535270, by rfl⟩ : syracuseStep 2047027 = 3070541) B3070541
theorem B1817667 : Blo 1817610 1817667 := bstep (se 1 (by rfl) ⟨1363250, by rfl⟩ : syracuseStep 1817667 = 2726501) B2726501
theorem B3112003 : Blo 1817610 3112003 := bstep (se 1 (by rfl) ⟨2334002, by rfl⟩ : syracuseStep 3112003 = 4668005) B4668005
theorem B2726993 : Blo 1817610 2726993 := bstep (se 2 (by rfl) ⟨1022622, by rfl⟩ : syracuseStep 2726993 = 2045245) B2045245
theorem B1817683 : Blo 1817610 1817683 := bstep (se 1 (by rfl) ⟨1363262, by rfl⟩ : syracuseStep 1817683 = 2726525) B2726525
theorem B1817699 : Blo 1817610 1817699 := bstep (se 1 (by rfl) ⟨1363274, by rfl⟩ : syracuseStep 1817699 = 2726549) B2726549
theorem B2727011 : Blo 1817610 2727011 := bstep (se 1 (by rfl) ⟨2045258, by rfl⟩ : syracuseStep 2727011 = 4090517) B4090517
theorem B1817715 : Blo 1817610 1817715 := bstep (se 1 (by rfl) ⟨1363286, by rfl⟩ : syracuseStep 1817715 = 2726573) B2726573
theorem B2301043 : Blo 1817610 2301043 := bstep (se 1 (by rfl) ⟨1725782, by rfl⟩ : syracuseStep 2301043 = 3451565) B3451565
theorem B2727041 : Blo 1817610 2727041 := bstep (se 2 (by rfl) ⟨1022640, by rfl⟩ : syracuseStep 2727041 = 2045281) B2045281
theorem B1817731 : Blo 1817610 1817731 := bstep (se 1 (by rfl) ⟨1363298, by rfl⟩ : syracuseStep 1817731 = 2726597) B2726597
theorem B1817747 : Blo 1817610 1817747 := bstep (se 1 (by rfl) ⟨1363310, by rfl⟩ : syracuseStep 1817747 = 2726621) B2726621
theorem B2727059 : Blo 1817610 2727059 := bstep (se 1 (by rfl) ⟨2045294, by rfl⟩ : syracuseStep 2727059 = 4090589) B4090589
theorem B1817763 : Blo 1817610 1817763 := bstep (se 1 (by rfl) ⟨1363322, by rfl⟩ : syracuseStep 1817763 = 2726645) B2726645
theorem B5176493 : Blo 1817610 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B2727089 : Blo 1817610 2727089 := bstep (se 2 (by rfl) ⟨1022658, by rfl⟩ : syracuseStep 2727089 = 2045317) B2045317
theorem B1817779 : Blo 1817610 1817779 := bstep (se 1 (by rfl) ⟨1363334, by rfl⟩ : syracuseStep 1817779 = 2726669) B2726669
theorem B1817795 : Blo 1817610 1817795 := bstep (se 1 (by rfl) ⟨1363346, by rfl⟩ : syracuseStep 1817795 = 2726693) B2726693
theorem B2727107 : Blo 1817610 2727107 := bstep (se 1 (by rfl) ⟨2045330, by rfl⟩ : syracuseStep 2727107 = 4090661) B4090661
theorem B6134993 : Blo 1817610 6134993 := bstep (se 2 (by rfl) ⟨2300622, by rfl⟩ : syracuseStep 6134993 = 4601245) B4601245
theorem B5823697 : Blo 1817610 5823697 := bstep (se 2 (by rfl) ⟨2183886, by rfl⟩ : syracuseStep 5823697 = 4367773) B4367773
theorem B1817811 : Blo 1817610 1817811 := bstep (se 1 (by rfl) ⟨1363358, by rfl⟩ : syracuseStep 1817811 = 2726717) B2726717
theorem B2301139 : Blo 1817610 2301139 := bstep (se 1 (by rfl) ⟨1725854, by rfl⟩ : syracuseStep 2301139 = 3451709) B3451709
theorem B2727137 : Blo 1817610 2727137 := bstep (se 2 (by rfl) ⟨1022676, by rfl⟩ : syracuseStep 2727137 = 2045353) B2045353
theorem B1817827 : Blo 1817610 1817827 := bstep (se 1 (by rfl) ⟨1363370, by rfl⟩ : syracuseStep 1817827 = 2726741) B2726741
theorem B5176561 : Blo 1817610 5176561 := bstep (se 2 (by rfl) ⟨1941210, by rfl⟩ : syracuseStep 5176561 = 3882421) B3882421
theorem B1817843 : Blo 1817610 1817843 := bstep (se 1 (by rfl) ⟨1363382, by rfl⟩ : syracuseStep 1817843 = 2726765) B2726765
theorem B2727155 : Blo 1817610 2727155 := bstep (se 1 (by rfl) ⟨2045366, by rfl⟩ : syracuseStep 2727155 = 4090733) B4090733
theorem B1817859 : Blo 1817610 1817859 := bstep (se 1 (by rfl) ⟨1363394, by rfl⟩ : syracuseStep 1817859 = 2726789) B2726789
theorem B4603139 : Blo 1817610 4603139 := bstep (se 1 (by rfl) ⟨3452354, by rfl⟩ : syracuseStep 4603139 = 6904709) B6904709
theorem B2727185 : Blo 1817610 2727185 := bstep (se 2 (by rfl) ⟨1022694, by rfl⟩ : syracuseStep 2727185 = 2045389) B2045389
theorem B1817875 : Blo 1817610 1817875 := bstep (se 1 (by rfl) ⟨1363406, by rfl⟩ : syracuseStep 1817875 = 2726813) B2726813
theorem B1817891 : Blo 1817610 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B3276067 : Blo 1817610 3276067 := bstep (se 1 (by rfl) ⟨2457050, by rfl⟩ : syracuseStep 3276067 = 4914101) B4914101
theorem B2727203 : Blo 1817610 2727203 := bstep (se 1 (by rfl) ⟨2045402, by rfl⟩ : syracuseStep 2727203 = 4090805) B4090805
theorem B1817907 : Blo 1817610 1817907 := bstep (se 1 (by rfl) ⟨1363430, by rfl⟩ : syracuseStep 1817907 = 2726861) B2726861
theorem B2727233 : Blo 1817610 2727233 := bstep (se 2 (by rfl) ⟨1022712, by rfl⟩ : syracuseStep 2727233 = 2045425) B2045425
theorem B1817923 : Blo 1817610 1817923 := bstep (se 1 (by rfl) ⟨1363442, by rfl⟩ : syracuseStep 1817923 = 2726885) B2726885
theorem B15539525 : Blo 1817610 15539525 := bstep (se 4 (by rfl) ⟨1456830, by rfl⟩ : syracuseStep 15539525 = 2913661) B2913661
theorem B1817939 : Blo 1817610 1817939 := bstep (se 1 (by rfl) ⟨1363454, by rfl⟩ : syracuseStep 1817939 = 2726909) B2726909
theorem B2727251 : Blo 1817610 2727251 := bstep (se 1 (by rfl) ⟨2045438, by rfl⟩ : syracuseStep 2727251 = 4090877) B4090877
theorem B1817955 : Blo 1817610 1817955 := bstep (se 1 (by rfl) ⟨1363466, by rfl⟩ : syracuseStep 1817955 = 2726933) B2726933
theorem B2727281 : Blo 1817610 2727281 := bstep (se 2 (by rfl) ⟨1022730, by rfl⟩ : syracuseStep 2727281 = 2045461) B2045461
theorem B1817971 : Blo 1817610 1817971 := bstep (se 1 (by rfl) ⟨1363478, by rfl⟩ : syracuseStep 1817971 = 2726957) B2726957
theorem B1817987 : Blo 1817610 1817987 := bstep (se 1 (by rfl) ⟨1363490, by rfl⟩ : syracuseStep 1817987 = 2726981) B2726981
theorem B2727299 : Blo 1817610 2727299 := bstep (se 1 (by rfl) ⟨2045474, by rfl⟩ : syracuseStep 2727299 = 4090949) B4090949
theorem B13106573 : Blo 1817610 13106573 := bstep (se 3 (by rfl) ⟨2457482, by rfl⟩ : syracuseStep 13106573 = 4914965) B4914965
theorem B1818003 : Blo 1817610 1818003 := bstep (se 1 (by rfl) ⟨1363502, by rfl⟩ : syracuseStep 1818003 = 2727005) B2727005
theorem B2727329 : Blo 1817610 2727329 := bstep (se 2 (by rfl) ⟨1022748, by rfl⟩ : syracuseStep 2727329 = 2045497) B2045497
theorem B1818019 : Blo 1817610 1818019 := bstep (se 1 (by rfl) ⟨1363514, by rfl⟩ : syracuseStep 1818019 = 2727029) B2727029
theorem B3366307 : Blo 1817610 3366307 := bstep (se 1 (by rfl) ⟨2524730, by rfl⟩ : syracuseStep 3366307 = 5049461) B5049461
theorem B1818035 : Blo 1817610 1818035 := bstep (se 1 (by rfl) ⟨1363526, by rfl⟩ : syracuseStep 1818035 = 2727053) B2727053
theorem B2727347 : Blo 1817610 2727347 := bstep (se 1 (by rfl) ⟨2045510, by rfl⟩ : syracuseStep 2727347 = 4091021) B4091021
theorem B1818051 : Blo 1817610 1818051 := bstep (se 1 (by rfl) ⟨1363538, by rfl⟩ : syracuseStep 1818051 = 2727077) B2727077
theorem B4603331 : Blo 1817610 4603331 := bstep (se 1 (by rfl) ⟨3452498, by rfl⟩ : syracuseStep 4603331 = 6904997) B6904997
theorem B2727377 : Blo 1817610 2727377 := bstep (se 2 (by rfl) ⟨1022766, by rfl⟩ : syracuseStep 2727377 = 2045533) B2045533
theorem B1818067 : Blo 1817610 1818067 := bstep (se 1 (by rfl) ⟨1363550, by rfl⟩ : syracuseStep 1818067 = 2727101) B2727101
theorem B1818083 : Blo 1817610 1818083 := bstep (se 1 (by rfl) ⟨1363562, by rfl⟩ : syracuseStep 1818083 = 2727125) B2727125
theorem B2727395 : Blo 1817610 2727395 := bstep (se 1 (by rfl) ⟨2045546, by rfl⟩ : syracuseStep 2727395 = 4091093) B4091093
theorem B1818099 : Blo 1817610 1818099 := bstep (se 1 (by rfl) ⟨1363574, by rfl⟩ : syracuseStep 1818099 = 2727149) B2727149
theorem B2727425 : Blo 1817610 2727425 := bstep (se 2 (by rfl) ⟨1022784, by rfl⟩ : syracuseStep 2727425 = 2045569) B2045569
theorem B5176835 : Blo 1817610 5176835 := bstep (se 1 (by rfl) ⟨3882626, by rfl⟩ : syracuseStep 5176835 = 7765253) B7765253
theorem B1818115 : Blo 1817610 1818115 := bstep (se 1 (by rfl) ⟨1363586, by rfl⟩ : syracuseStep 1818115 = 2727173) B2727173
theorem B1842707 : Blo 1817610 1842707 := bstep (se 1 (by rfl) ⟨1382030, by rfl⟩ : syracuseStep 1842707 = 2764061) B2764061
theorem B1818131 : Blo 1817610 1818131 := bstep (se 1 (by rfl) ⟨1363598, by rfl⟩ : syracuseStep 1818131 = 2727197) B2727197
theorem B2727443 : Blo 1817610 2727443 := bstep (se 1 (by rfl) ⟨2045582, by rfl⟩ : syracuseStep 2727443 = 4091165) B4091165
theorem B1818147 : Blo 1817610 1818147 := bstep (se 1 (by rfl) ⟨1363610, by rfl⟩ : syracuseStep 1818147 = 2727221) B2727221
theorem B2727473 : Blo 1817610 2727473 := bstep (se 2 (by rfl) ⟨1022802, by rfl⟩ : syracuseStep 2727473 = 2045605) B2045605
theorem B1818163 : Blo 1817610 1818163 := bstep (se 1 (by rfl) ⟨1363622, by rfl⟩ : syracuseStep 1818163 = 2727245) B2727245
theorem B1818179 : Blo 1817610 1818179 := bstep (se 1 (by rfl) ⟨1363634, by rfl⟩ : syracuseStep 1818179 = 2727269) B2727269
theorem B2727491 : Blo 1817610 2727491 := bstep (se 1 (by rfl) ⟨2045618, by rfl⟩ : syracuseStep 2727491 = 4091237) B4091237
theorem B1818195 : Blo 1817610 1818195 := bstep (se 1 (by rfl) ⟨1363646, by rfl⟩ : syracuseStep 1818195 = 2727293) B2727293
theorem B2727521 : Blo 1817610 2727521 := bstep (se 2 (by rfl) ⟨1022820, by rfl⟩ : syracuseStep 2727521 = 2045641) B2045641
theorem B1818211 : Blo 1817610 1818211 := bstep (se 1 (by rfl) ⟨1363658, by rfl⟩ : syracuseStep 1818211 = 2727317) B2727317
theorem B1818227 : Blo 1817610 1818227 := bstep (se 1 (by rfl) ⟨1363670, by rfl⟩ : syracuseStep 1818227 = 2727341) B2727341
theorem B2727539 : Blo 1817610 2727539 := bstep (se 1 (by rfl) ⟨2045654, by rfl⟩ : syracuseStep 2727539 = 4091309) B4091309
theorem B1818243 : Blo 1817610 1818243 := bstep (se 1 (by rfl) ⟨1363682, by rfl⟩ : syracuseStep 1818243 = 2727365) B2727365
theorem B2727569 : Blo 1817610 2727569 := bstep (se 2 (by rfl) ⟨1022838, by rfl⟩ : syracuseStep 2727569 = 2045677) B2045677
theorem B1818259 : Blo 1817610 1818259 := bstep (se 1 (by rfl) ⟨1363694, by rfl⟩ : syracuseStep 1818259 = 2727389) B2727389
theorem B1818275 : Blo 1817610 1818275 := bstep (se 1 (by rfl) ⟨1363706, by rfl⟩ : syracuseStep 1818275 = 2727413) B2727413
theorem B2727587 : Blo 1817610 2727587 := bstep (se 1 (by rfl) ⟨2045690, by rfl⟩ : syracuseStep 2727587 = 4091381) B4091381
theorem B1818291 : Blo 1817610 1818291 := bstep (se 1 (by rfl) ⟨1363718, by rfl⟩ : syracuseStep 1818291 = 2727437) B2727437
theorem B2727617 : Blo 1817610 2727617 := bstep (se 2 (by rfl) ⟨1022856, by rfl⟩ : syracuseStep 2727617 = 2045713) B2045713
theorem B1818307 : Blo 1817610 1818307 := bstep (se 1 (by rfl) ⟨1363730, by rfl⟩ : syracuseStep 1818307 = 2727461) B2727461
theorem B2301635 : Blo 1817610 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B1818323 : Blo 1817610 1818323 := bstep (se 1 (by rfl) ⟨1363742, by rfl⟩ : syracuseStep 1818323 = 2727485) B2727485
theorem B2727635 : Blo 1817610 2727635 := bstep (se 1 (by rfl) ⟨2045726, by rfl⟩ : syracuseStep 2727635 = 4091453) B4091453
theorem B1818339 : Blo 1817610 1818339 := bstep (se 1 (by rfl) ⟨1363754, by rfl⟩ : syracuseStep 1818339 = 2727509) B2727509
theorem B6135533 : Blo 1817610 6135533 := bstep (se 3 (by rfl) ⟨1150412, by rfl⟩ : syracuseStep 6135533 = 2300825) B2300825
theorem B2727665 : Blo 1817610 2727665 := bstep (se 2 (by rfl) ⟨1022874, by rfl⟩ : syracuseStep 2727665 = 2045749) B2045749
theorem B1818355 : Blo 1817610 1818355 := bstep (se 1 (by rfl) ⟨1363766, by rfl⟩ : syracuseStep 1818355 = 2727533) B2727533
theorem B1818371 : Blo 1817610 1818371 := bstep (se 1 (by rfl) ⟨1363778, by rfl⟩ : syracuseStep 1818371 = 2727557) B2727557
theorem B2727683 : Blo 1817610 2727683 := bstep (se 1 (by rfl) ⟨2045762, by rfl⟩ : syracuseStep 2727683 = 4091525) B4091525
theorem B1818387 : Blo 1817610 1818387 := bstep (se 1 (by rfl) ⟨1363790, by rfl⟩ : syracuseStep 1818387 = 2727581) B2727581
theorem B2727713 : Blo 1817610 2727713 := bstep (se 2 (by rfl) ⟨1022892, by rfl⟩ : syracuseStep 2727713 = 2045785) B2045785
theorem B6135587 : Blo 1817610 6135587 := bstep (se 1 (by rfl) ⟨4601690, by rfl⟩ : syracuseStep 6135587 = 9203381) B9203381
theorem B1818403 : Blo 1817610 1818403 := bstep (se 1 (by rfl) ⟨1363802, by rfl⟩ : syracuseStep 1818403 = 2727605) B2727605
theorem B1818419 : Blo 1817610 1818419 := bstep (se 1 (by rfl) ⟨1363814, by rfl⟩ : syracuseStep 1818419 = 2727629) B2727629
theorem B2727731 : Blo 1817610 2727731 := bstep (se 1 (by rfl) ⟨2045798, by rfl⟩ : syracuseStep 2727731 = 4091597) B4091597
theorem B1818435 : Blo 1817610 1818435 := bstep (se 1 (by rfl) ⟨1363826, by rfl⟩ : syracuseStep 1818435 = 2727653) B2727653
theorem B2727761 : Blo 1817610 2727761 := bstep (se 2 (by rfl) ⟨1022910, by rfl⟩ : syracuseStep 2727761 = 2045821) B2045821
theorem B1818451 : Blo 1817610 1818451 := bstep (se 1 (by rfl) ⟨1363838, by rfl⟩ : syracuseStep 1818451 = 2727677) B2727677
theorem B1818467 : Blo 1817610 1818467 := bstep (se 1 (by rfl) ⟨1363850, by rfl⟩ : syracuseStep 1818467 = 2727701) B2727701
theorem B2727779 : Blo 1817610 2727779 := bstep (se 1 (by rfl) ⟨2045834, by rfl⟩ : syracuseStep 2727779 = 4091669) B4091669
theorem B3686257 : Blo 1817610 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B1818483 : Blo 1817610 1818483 := bstep (se 1 (by rfl) ⟨1363862, by rfl⟩ : syracuseStep 1818483 = 2727725) B2727725
theorem B2727809 : Blo 1817610 2727809 := bstep (se 2 (by rfl) ⟨1022928, by rfl⟩ : syracuseStep 2727809 = 2045857) B2045857
theorem B1818499 : Blo 1817610 1818499 := bstep (se 1 (by rfl) ⟨1363874, by rfl⟩ : syracuseStep 1818499 = 2727749) B2727749
theorem B7765901 : Blo 1817610 7765901 := bstep (se 3 (by rfl) ⟨1456106, by rfl⟩ : syracuseStep 7765901 = 2912213) B2912213
theorem B1818515 : Blo 1817610 1818515 := bstep (se 1 (by rfl) ⟨1363886, by rfl⟩ : syracuseStep 1818515 = 2727773) B2727773
theorem B2727827 : Blo 1817610 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B1818531 : Blo 1817610 1818531 := bstep (se 1 (by rfl) ⟨1363898, by rfl⟩ : syracuseStep 1818531 = 2727797) B2727797
theorem B2727857 : Blo 1817610 2727857 := bstep (se 2 (by rfl) ⟨1022946, by rfl⟩ : syracuseStep 2727857 = 2045893) B2045893
theorem B1818547 : Blo 1817610 1818547 := bstep (se 1 (by rfl) ⟨1363910, by rfl⟩ : syracuseStep 1818547 = 2727821) B2727821
theorem B2588611 : Blo 1817610 2588611 := bstep (se 1 (by rfl) ⟨1941458, by rfl⟩ : syracuseStep 2588611 = 3882917) B3882917
theorem B1818563 : Blo 1817610 1818563 := bstep (se 1 (by rfl) ⟨1363922, by rfl⟩ : syracuseStep 1818563 = 2727845) B2727845
theorem B2727875 : Blo 1817610 2727875 := bstep (se 1 (by rfl) ⟨2045906, by rfl⟩ : syracuseStep 2727875 = 4091813) B4091813
theorem B3686353 : Blo 1817610 3686353 := bstep (se 2 (by rfl) ⟨1382382, by rfl⟩ : syracuseStep 3686353 = 2764765) B2764765
theorem B1818579 : Blo 1817610 1818579 := bstep (se 1 (by rfl) ⟨1363934, by rfl⟩ : syracuseStep 1818579 = 2727869) B2727869
theorem B2727905 : Blo 1817610 2727905 := bstep (se 2 (by rfl) ⟨1022964, by rfl⟩ : syracuseStep 2727905 = 2045929) B2045929
theorem B1818595 : Blo 1817610 1818595 := bstep (se 1 (by rfl) ⟨1363946, by rfl⟩ : syracuseStep 1818595 = 2727893) B2727893
theorem B1818611 : Blo 1817610 1818611 := bstep (se 1 (by rfl) ⟨1363958, by rfl⟩ : syracuseStep 1818611 = 2727917) B2727917
theorem B2727923 : Blo 1817610 2727923 := bstep (se 1 (by rfl) ⟨2045942, by rfl⟩ : syracuseStep 2727923 = 4091885) B4091885
theorem B2727947 : Blo 1817610 2727947 := bstep (se 1 (by rfl) ⟨2045960, by rfl⟩ : syracuseStep 2727947 = 4091921) B4091921
theorem B1818635 : Blo 1817610 1818635 := bstep (se 1 (by rfl) ⟨1363976, by rfl⟩ : syracuseStep 1818635 = 2727953) B2727953
theorem B2727959 : Blo 1817610 2727959 := bstep (se 1 (by rfl) ⟨2045969, by rfl⟩ : syracuseStep 2727959 = 4091939) B4091939
theorem B1818647 : Blo 1817610 1818647 := bstep (se 1 (by rfl) ⟨1363985, by rfl⟩ : syracuseStep 1818647 = 2727971) B2727971
theorem B35438627 : Blo 1817610 35438627 := bstep (se 1 (by rfl) ⟨26578970, by rfl⟩ : syracuseStep 35438627 = 53157941) B53157941
theorem B1818667 : Blo 1817610 1818667 := bstep (se 1 (by rfl) ⟨1364000, by rfl⟩ : syracuseStep 1818667 = 2728001) B2728001
theorem B1818679 : Blo 1817610 1818679 := bstep (se 1 (by rfl) ⟨1364009, by rfl⟩ : syracuseStep 1818679 = 2728019) B2728019
theorem B26214475 : Blo 1817610 26214475 := bstep (se 1 (by rfl) ⟨19660856, by rfl⟩ : syracuseStep 26214475 = 39321713) B39321713
theorem B3276875 : Blo 1817610 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B1818699 : Blo 1817610 1818699 := bstep (se 1 (by rfl) ⟨1364024, by rfl⟩ : syracuseStep 1818699 = 2728049) B2728049
theorem B4603979 : Blo 1817610 4603979 := bstep (se 1 (by rfl) ⟨3452984, by rfl⟩ : syracuseStep 4603979 = 6905969) B6905969
theorem B1818711 : Blo 1817610 1818711 := bstep (se 1 (by rfl) ⟨1364033, by rfl⟩ : syracuseStep 1818711 = 2728067) B2728067
theorem B2728025 : Blo 1817610 2728025 := bstep (se 2 (by rfl) ⟨1023009, by rfl⟩ : syracuseStep 2728025 = 2046019) B2046019
theorem B1818731 : Blo 1817610 1818731 := bstep (se 1 (by rfl) ⟨1364048, by rfl⟩ : syracuseStep 1818731 = 2728097) B2728097
theorem B1818743 : Blo 1817610 1818743 := bstep (se 1 (by rfl) ⟨1364057, by rfl⟩ : syracuseStep 1818743 = 2728115) B2728115
theorem B1818763 : Blo 1817610 1818763 := bstep (se 1 (by rfl) ⟨1364072, by rfl⟩ : syracuseStep 1818763 = 2728145) B2728145
theorem B5177495 : Blo 1817610 5177495 := bstep (se 1 (by rfl) ⟨3883121, by rfl⟩ : syracuseStep 5177495 = 7766243) B7766243
theorem B1818775 : Blo 1817610 1818775 := bstep (se 1 (by rfl) ⟨1364081, by rfl⟩ : syracuseStep 1818775 = 2728163) B2728163
theorem B1818795 : Blo 1817610 1818795 := bstep (se 1 (by rfl) ⟨1364096, by rfl⟩ : syracuseStep 1818795 = 2728193) B2728193
theorem B1818807 : Blo 1817610 1818807 := bstep (se 1 (by rfl) ⟨1364105, by rfl⟩ : syracuseStep 1818807 = 2728211) B2728211
theorem B2728139 : Blo 1817610 2728139 := bstep (se 1 (by rfl) ⟨2046104, by rfl⟩ : syracuseStep 2728139 = 4092209) B4092209
theorem B1818827 : Blo 1817610 1818827 := bstep (se 1 (by rfl) ⟨1364120, by rfl⟩ : syracuseStep 1818827 = 2728241) B2728241
theorem B3195095 : Blo 1817610 3195095 := bstep (se 1 (by rfl) ⟨2396321, by rfl⟩ : syracuseStep 3195095 = 4792643) B4792643
theorem B2728151 : Blo 1817610 2728151 := bstep (se 1 (by rfl) ⟨2046113, by rfl⟩ : syracuseStep 2728151 = 4092227) B4092227
theorem B1818839 : Blo 1817610 1818839 := bstep (se 1 (by rfl) ⟨1364129, by rfl⟩ : syracuseStep 1818839 = 2728259) B2728259
theorem B1818859 : Blo 1817610 1818859 := bstep (se 1 (by rfl) ⟨1364144, by rfl⟩ : syracuseStep 1818859 = 2728289) B2728289
theorem B1818871 : Blo 1817610 1818871 := bstep (se 1 (by rfl) ⟨1364153, by rfl⟩ : syracuseStep 1818871 = 2728307) B2728307
theorem B1818891 : Blo 1817610 1818891 := bstep (se 1 (by rfl) ⟨1364168, by rfl⟩ : syracuseStep 1818891 = 2728337) B2728337
theorem B1818903 : Blo 1817610 1818903 := bstep (se 1 (by rfl) ⟨1364177, by rfl⟩ : syracuseStep 1818903 = 2728355) B2728355
theorem B2728217 : Blo 1817610 2728217 := bstep (se 2 (by rfl) ⟨1023081, by rfl⟩ : syracuseStep 2728217 = 2046163) B2046163
theorem B1818923 : Blo 1817610 1818923 := bstep (se 1 (by rfl) ⟨1364192, by rfl⟩ : syracuseStep 1818923 = 2728385) B2728385
theorem B1818935 : Blo 1817610 1818935 := bstep (se 1 (by rfl) ⟨1364201, by rfl⟩ : syracuseStep 1818935 = 2728403) B2728403
theorem B1818955 : Blo 1817610 1818955 := bstep (se 1 (by rfl) ⟨1364216, by rfl⟩ : syracuseStep 1818955 = 2728433) B2728433
theorem B2302283 : Blo 1817610 2302283 := bstep (se 1 (by rfl) ⟨1726712, by rfl⟩ : syracuseStep 2302283 = 3453425) B3453425
theorem B5251403 : Blo 1817610 5251403 := bstep (se 1 (by rfl) ⟨3938552, by rfl⟩ : syracuseStep 5251403 = 7877105) B7877105
theorem B3686743 : Blo 1817610 3686743 := bstep (se 1 (by rfl) ⟨2765057, by rfl⟩ : syracuseStep 3686743 = 5530115) B5530115
theorem B1818967 : Blo 1817610 1818967 := bstep (se 1 (by rfl) ⟨1364225, by rfl⟩ : syracuseStep 1818967 = 2728451) B2728451
theorem B16597349 : Blo 1817610 16597349 := bstep (se 4 (by rfl) ⟨1556001, by rfl⟩ : syracuseStep 16597349 = 3112003) B3112003
theorem B1818987 : Blo 1817610 1818987 := bstep (se 1 (by rfl) ⟨1364240, by rfl⟩ : syracuseStep 1818987 = 2728481) B2728481
theorem B1818999 : Blo 1817610 1818999 := bstep (se 1 (by rfl) ⟨1364249, by rfl⟩ : syracuseStep 1818999 = 2728499) B2728499
theorem B2728331 : Blo 1817610 2728331 := bstep (se 1 (by rfl) ⟨2046248, by rfl⟩ : syracuseStep 2728331 = 4092497) B4092497
theorem B1819019 : Blo 1817610 1819019 := bstep (se 1 (by rfl) ⟨1364264, by rfl⟩ : syracuseStep 1819019 = 2728529) B2728529
theorem B13812119 : Blo 1817610 13812119 := bstep (se 1 (by rfl) ⟨10359089, by rfl⟩ : syracuseStep 13812119 = 20718179) B20718179
theorem B2728343 : Blo 1817610 2728343 := bstep (se 1 (by rfl) ⟨2046257, by rfl⟩ : syracuseStep 2728343 = 4092515) B4092515
theorem B1819031 : Blo 1817610 1819031 := bstep (se 1 (by rfl) ⟨1364273, by rfl⟩ : syracuseStep 1819031 = 2728547) B2728547
theorem B1819051 : Blo 1817610 1819051 := bstep (se 1 (by rfl) ⟨1364288, by rfl⟩ : syracuseStep 1819051 = 2728577) B2728577
theorem B1819063 : Blo 1817610 1819063 := bstep (se 1 (by rfl) ⟨1364297, by rfl⟩ : syracuseStep 1819063 = 2728595) B2728595
theorem B5177803 : Blo 1817610 5177803 := bstep (se 1 (by rfl) ⟨3883352, by rfl⟩ : syracuseStep 5177803 = 7766705) B7766705
theorem B1819083 : Blo 1817610 1819083 := bstep (se 1 (by rfl) ⟨1364312, by rfl⟩ : syracuseStep 1819083 = 2728625) B2728625
theorem B3277271 : Blo 1817610 3277271 := bstep (se 1 (by rfl) ⟨2457953, by rfl⟩ : syracuseStep 3277271 = 4915907) B4915907
theorem B1819095 : Blo 1817610 1819095 := bstep (se 1 (by rfl) ⟨1364321, by rfl⟩ : syracuseStep 1819095 = 2728643) B2728643
theorem B2728409 : Blo 1817610 2728409 := bstep (se 2 (by rfl) ⟨1023153, by rfl⟩ : syracuseStep 2728409 = 2046307) B2046307
theorem B1819115 : Blo 1817610 1819115 := bstep (se 1 (by rfl) ⟨1364336, by rfl⟩ : syracuseStep 1819115 = 2728673) B2728673
theorem B1819127 : Blo 1817610 1819127 := bstep (se 1 (by rfl) ⟨1364345, by rfl⟩ : syracuseStep 1819127 = 2728691) B2728691
theorem B1819147 : Blo 1817610 1819147 := bstep (se 1 (by rfl) ⟨1364360, by rfl⟩ : syracuseStep 1819147 = 2728721) B2728721
theorem B6136343 : Blo 1817610 6136343 := bstep (se 1 (by rfl) ⟨4602257, by rfl⟩ : syracuseStep 6136343 = 9204515) B9204515
theorem B1942039 : Blo 1817610 1942039 := bstep (se 1 (by rfl) ⟨1456529, by rfl⟩ : syracuseStep 1942039 = 2913059) B2913059
theorem B1819159 : Blo 1817610 1819159 := bstep (se 1 (by rfl) ⟨1364369, by rfl⟩ : syracuseStep 1819159 = 2728739) B2728739
theorem B17515043 : Blo 1817610 17515043 := bstep (se 1 (by rfl) ⟨13136282, by rfl⟩ : syracuseStep 17515043 = 26272565) B26272565
theorem B1819179 : Blo 1817610 1819179 := bstep (se 1 (by rfl) ⟨1364384, by rfl⟩ : syracuseStep 1819179 = 2728769) B2728769
theorem B1819191 : Blo 1817610 1819191 := bstep (se 1 (by rfl) ⟨1364393, by rfl⟩ : syracuseStep 1819191 = 2728787) B2728787
theorem B2728523 : Blo 1817610 2728523 := bstep (se 1 (by rfl) ⟨2046392, by rfl⟩ : syracuseStep 2728523 = 4092785) B4092785
theorem B1819211 : Blo 1817610 1819211 := bstep (se 1 (by rfl) ⟨1364408, by rfl⟩ : syracuseStep 1819211 = 2728817) B2728817
theorem B2728535 : Blo 1817610 2728535 := bstep (se 1 (by rfl) ⟨2046401, by rfl⟩ : syracuseStep 2728535 = 4092803) B4092803
theorem B1819223 : Blo 1817610 1819223 := bstep (se 1 (by rfl) ⟨1364417, by rfl⟩ : syracuseStep 1819223 = 2728835) B2728835
theorem B1819243 : Blo 1817610 1819243 := bstep (se 1 (by rfl) ⟨1364432, by rfl⟩ : syracuseStep 1819243 = 2728865) B2728865
theorem B1819255 : Blo 1817610 1819255 := bstep (se 1 (by rfl) ⟨1364441, by rfl⟩ : syracuseStep 1819255 = 2728883) B2728883
theorem B3277451 : Blo 1817610 3277451 := bstep (se 1 (by rfl) ⟨2458088, by rfl⟩ : syracuseStep 3277451 = 4916177) B4916177
theorem B1819275 : Blo 1817610 1819275 := bstep (se 1 (by rfl) ⟨1364456, by rfl⟩ : syracuseStep 1819275 = 2728913) B2728913
theorem B1819287 : Blo 1817610 1819287 := bstep (se 1 (by rfl) ⟨1364465, by rfl⟩ : syracuseStep 1819287 = 2728931) B2728931
theorem B2728601 : Blo 1817610 2728601 := bstep (se 2 (by rfl) ⟨1023225, by rfl⟩ : syracuseStep 2728601 = 2046451) B2046451
theorem B1819307 : Blo 1817610 1819307 := bstep (se 1 (by rfl) ⟨1364480, by rfl⟩ : syracuseStep 1819307 = 2728961) B2728961
theorem B1819319 : Blo 1817610 1819319 := bstep (se 1 (by rfl) ⟨1364489, by rfl⟩ : syracuseStep 1819319 = 2728979) B2728979
theorem B1819339 : Blo 1817610 1819339 := bstep (se 1 (by rfl) ⟨1364504, by rfl⟩ : syracuseStep 1819339 = 2729009) B2729009
theorem B1819351 : Blo 1817610 1819351 := bstep (se 1 (by rfl) ⟨1364513, by rfl⟩ : syracuseStep 1819351 = 2729027) B2729027
theorem B5178077 : Blo 1817610 5178077 := bstep (se 3 (by rfl) ⟨970889, by rfl⟩ : syracuseStep 5178077 = 1941779) B1941779
theorem B1819371 : Blo 1817610 1819371 := bstep (se 1 (by rfl) ⟨1364528, by rfl⟩ : syracuseStep 1819371 = 2729057) B2729057
theorem B3883763 : Blo 1817610 3883763 := bstep (se 1 (by rfl) ⟨2912822, by rfl⟩ : syracuseStep 3883763 = 5825645) B5825645
theorem B1819383 : Blo 1817610 1819383 := bstep (se 1 (by rfl) ⟨1364537, by rfl⟩ : syracuseStep 1819383 = 2729075) B2729075
theorem B2728715 : Blo 1817610 2728715 := bstep (se 1 (by rfl) ⟨2046536, by rfl⟩ : syracuseStep 2728715 = 4093073) B4093073
theorem B1819403 : Blo 1817610 1819403 := bstep (se 1 (by rfl) ⟨1364552, by rfl⟩ : syracuseStep 1819403 = 2729105) B2729105
theorem B3687191 : Blo 1817610 3687191 := bstep (se 1 (by rfl) ⟨2765393, by rfl⟩ : syracuseStep 3687191 = 5530787) B5530787
theorem B7578391 : Blo 1817610 7578391 := bstep (se 1 (by rfl) ⟨5683793, by rfl⟩ : syracuseStep 7578391 = 11367587) B11367587
theorem B2728727 : Blo 1817610 2728727 := bstep (se 1 (by rfl) ⟨2046545, by rfl⟩ : syracuseStep 2728727 = 4093091) B4093091
theorem B1819415 : Blo 1817610 1819415 := bstep (se 1 (by rfl) ⟨1364561, by rfl⟩ : syracuseStep 1819415 = 2729123) B2729123
theorem B1819435 : Blo 1817610 1819435 := bstep (se 1 (by rfl) ⟨1364576, by rfl⟩ : syracuseStep 1819435 = 2729153) B2729153
theorem B26231597 : Blo 1817610 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B1819447 : Blo 1817610 1819447 := bstep (se 1 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 1819447 = 2729171) B2729171
theorem B1819467 : Blo 1817610 1819467 := bstep (se 1 (by rfl) ⟨1364600, by rfl⟩ : syracuseStep 1819467 = 2729201) B2729201
theorem B1819479 : Blo 1817610 1819479 := bstep (se 1 (by rfl) ⟨1364609, by rfl⟩ : syracuseStep 1819479 = 2729219) B2729219
theorem B5530457 : Blo 1817610 5530457 := bstep (se 2 (by rfl) ⟨2073921, by rfl⟩ : syracuseStep 5530457 = 4147843) B4147843
theorem B2728793 : Blo 1817610 2728793 := bstep (se 2 (by rfl) ⟨1023297, by rfl⟩ : syracuseStep 2728793 = 2046595) B2046595
theorem B11658077 : Blo 1817610 11658077 := bstep (se 3 (by rfl) ⟨2185889, by rfl⟩ : syracuseStep 11658077 = 4371779) B4371779
theorem B1819499 : Blo 1817610 1819499 := bstep (se 1 (by rfl) ⟨1364624, by rfl⟩ : syracuseStep 1819499 = 2729249) B2729249
theorem B1819511 : Blo 1817610 1819511 := bstep (se 1 (by rfl) ⟨1364633, by rfl⟩ : syracuseStep 1819511 = 2729267) B2729267
theorem B1819531 : Blo 1817610 1819531 := bstep (se 1 (by rfl) ⟨1364648, by rfl⟩ : syracuseStep 1819531 = 2729297) B2729297
theorem B9208727 : Blo 1817610 9208727 := bstep (se 1 (by rfl) ⟨6906545, by rfl⟩ : syracuseStep 9208727 = 13813091) B13813091
theorem B1819543 : Blo 1817610 1819543 := bstep (se 1 (by rfl) ⟨1364657, by rfl⟩ : syracuseStep 1819543 = 2729315) B2729315
theorem B1819563 : Blo 1817610 1819563 := bstep (se 1 (by rfl) ⟨1364672, by rfl⟩ : syracuseStep 1819563 = 2729345) B2729345
theorem B1819575 : Blo 1817610 1819575 := bstep (se 1 (by rfl) ⟨1364681, by rfl⟩ : syracuseStep 1819575 = 2729363) B2729363
theorem B2728907 : Blo 1817610 2728907 := bstep (se 1 (by rfl) ⟨2046680, by rfl⟩ : syracuseStep 2728907 = 4093361) B4093361
theorem B1819595 : Blo 1817610 1819595 := bstep (se 1 (by rfl) ⟨1364696, by rfl⟩ : syracuseStep 1819595 = 2729393) B2729393
theorem B2728919 : Blo 1817610 2728919 := bstep (se 1 (by rfl) ⟨2046689, by rfl⟩ : syracuseStep 2728919 = 4093379) B4093379
theorem B1819607 : Blo 1817610 1819607 := bstep (se 1 (by rfl) ⟨1364705, by rfl⟩ : syracuseStep 1819607 = 2729411) B2729411
theorem B4367321 : Blo 1817610 4367321 := bstep (se 2 (by rfl) ⟨1637745, by rfl⟩ : syracuseStep 4367321 = 3275491) B3275491
theorem B3687385 : Blo 1817610 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B4604951 : Blo 1817610 4604951 := bstep (se 1 (by rfl) ⟨3453713, by rfl⟩ : syracuseStep 4604951 = 6907427) B6907427
theorem B3687449 : Blo 1817610 3687449 := bstep (se 2 (by rfl) ⟨1382793, by rfl⟩ : syracuseStep 3687449 = 2765587) B2765587
theorem B2728985 : Blo 1817610 2728985 := bstep (se 2 (by rfl) ⟨1023369, by rfl⟩ : syracuseStep 2728985 = 2046739) B2046739
theorem B6136883 : Blo 1817610 6136883 := bstep (se 1 (by rfl) ⟨4602662, by rfl⟩ : syracuseStep 6136883 = 9205325) B9205325
theorem B13288549 : Blo 1817610 13288549 := bstep (se 4 (by rfl) ⟨1245801, by rfl⟩ : syracuseStep 13288549 = 2491603) B2491603
theorem B2729099 : Blo 1817610 2729099 := bstep (se 1 (by rfl) ⟨2046824, by rfl⟩ : syracuseStep 2729099 = 4093649) B4093649
theorem B2729111 : Blo 1817610 2729111 := bstep (se 1 (by rfl) ⟨2046833, by rfl⟩ : syracuseStep 2729111 = 4093667) B4093667
theorem B3278027 : Blo 1817610 3278027 := bstep (se 1 (by rfl) ⟨2458520, by rfl⟩ : syracuseStep 3278027 = 4917041) B4917041
theorem B3884249 : Blo 1817610 3884249 := bstep (se 2 (by rfl) ⟨1456593, by rfl⟩ : syracuseStep 3884249 = 2913187) B2913187
theorem B7374041 : Blo 1817610 7374041 := bstep (se 2 (by rfl) ⟨2765265, by rfl⟩ : syracuseStep 7374041 = 5530531) B5530531
theorem B2729177 : Blo 1817610 2729177 := bstep (se 2 (by rfl) ⟨1023441, by rfl⟩ : syracuseStep 2729177 = 2046883) B2046883
theorem B6907139 : Blo 1817610 6907139 := bstep (se 1 (by rfl) ⟨5180354, by rfl⟩ : syracuseStep 6907139 = 10360709) B10360709
theorem B6907153 : Blo 1817610 6907153 := bstep (se 2 (by rfl) ⟨2590182, by rfl⟩ : syracuseStep 6907153 = 5180365) B5180365
theorem B6137153 : Blo 1817610 6137153 := bstep (se 2 (by rfl) ⟨2301432, by rfl⟩ : syracuseStep 6137153 = 4602865) B4602865
theorem B2729291 : Blo 1817610 2729291 := bstep (se 1 (by rfl) ⟨2046968, by rfl⟩ : syracuseStep 2729291 = 4093937) B4093937
theorem B2729303 : Blo 1817610 2729303 := bstep (se 1 (by rfl) ⟨2046977, by rfl⟩ : syracuseStep 2729303 = 4093955) B4093955
theorem B2590103 : Blo 1817610 2590103 := bstep (se 1 (by rfl) ⟨1942577, by rfl⟩ : syracuseStep 2590103 = 3885155) B3885155
theorem B2729369 : Blo 1817610 2729369 := bstep (se 2 (by rfl) ⟨1023513, by rfl⟩ : syracuseStep 2729369 = 2047027) B2047027
theorem B6907457 : Blo 1817610 6907457 := bstep (se 2 (by rfl) ⟨2590296, by rfl⟩ : syracuseStep 6907457 = 5180593) B5180593
theorem B4146803 : Blo 1817610 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B2074231 : Blo 1817610 2074231 := bstep (se 1 (by rfl) ⟨1555673, by rfl⟩ : syracuseStep 2074231 = 3111347) B3111347
theorem B4605619 : Blo 1817610 4605619 := bstep (se 1 (by rfl) ⟨3454214, by rfl⟩ : syracuseStep 4605619 = 6908429) B6908429
theorem B4368089 : Blo 1817610 4368089 := bstep (se 2 (by rfl) ⟨1638033, by rfl⟩ : syracuseStep 4368089 = 3276067) B3276067
theorem B3548951 : Blo 1817610 3548951 := bstep (se 1 (by rfl) ⟨2661713, by rfl⟩ : syracuseStep 3548951 = 5323427) B5323427
theorem B4605761 : Blo 1817610 4605761 := bstep (se 2 (by rfl) ⟨1727160, by rfl⟩ : syracuseStep 4605761 = 3454321) B3454321
theorem B4089689 : Blo 1817610 4089689 := bstep (se 2 (by rfl) ⟨1533633, by rfl⟩ : syracuseStep 4089689 = 3067267) B3067267
theorem B6137693 : Blo 1817610 6137693 := bstep (se 3 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 6137693 = 2301635) B2301635
theorem B3450775 : Blo 1817610 3450775 := bstep (se 1 (by rfl) ⟨2588081, by rfl⟩ : syracuseStep 3450775 = 5176163) B5176163
theorem B4089779 : Blo 1817610 4089779 := bstep (se 1 (by rfl) ⟨3067334, by rfl⟩ : syracuseStep 4089779 = 6134669) B6134669
theorem B3884993 : Blo 1817610 3884993 := bstep (se 2 (by rfl) ⟨1456872, by rfl⟩ : syracuseStep 3884993 = 2913745) B2913745
theorem B4089815 : Blo 1817610 4089815 := bstep (se 1 (by rfl) ⟨3067361, by rfl⟩ : syracuseStep 4089815 = 6134723) B6134723
theorem B15534125 : Blo 1817610 15534125 := bstep (se 3 (by rfl) ⟨2912648, by rfl⟩ : syracuseStep 15534125 = 5825297) B5825297
theorem B3450995 : Blo 1817610 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B4089995 : Blo 1817610 4089995 := bstep (se 1 (by rfl) ⟨3067496, by rfl⟩ : syracuseStep 4089995 = 6134993) B6134993
theorem B8734871 : Blo 1817610 8734871 := bstep (se 1 (by rfl) ⟨6551153, by rfl⟩ : syracuseStep 8734871 = 13102307) B13102307
theorem B4090049 : Blo 1817610 4090049 := bstep (se 2 (by rfl) ⟨1533768, by rfl⟩ : syracuseStep 4090049 = 3067537) B3067537
theorem B6908125 : Blo 1817610 6908125 := bstep (se 3 (by rfl) ⟨1295273, by rfl⟩ : syracuseStep 6908125 = 2590547) B2590547
theorem B44263685 : Blo 1817610 44263685 := bstep (se 4 (by rfl) ⟨4149720, by rfl⟩ : syracuseStep 44263685 = 8299441) B8299441
theorem B3451223 : Blo 1817610 3451223 := bstep (se 1 (by rfl) ⟨2588417, by rfl⟩ : syracuseStep 3451223 = 5176835) B5176835
theorem B10357085 : Blo 1817610 10357085 := bstep (se 3 (by rfl) ⟨1941953, by rfl⟩ : syracuseStep 10357085 = 3883907) B3883907
theorem B4090265 : Blo 1817610 4090265 := bstep (se 2 (by rfl) ⟨1533849, by rfl⟩ : syracuseStep 4090265 = 3067699) B3067699
theorem B4090355 : Blo 1817610 4090355 := bstep (se 1 (by rfl) ⟨3067766, by rfl⟩ : syracuseStep 4090355 = 6135533) B6135533
theorem B4090391 : Blo 1817610 4090391 := bstep (se 1 (by rfl) ⟨3067793, by rfl⟩ : syracuseStep 4090391 = 6135587) B6135587
theorem B3451481 : Blo 1817610 3451481 := bstep (se 2 (by rfl) ⟨1294305, by rfl⟩ : syracuseStep 3451481 = 2588611) B2588611
theorem B7768669 : Blo 1817610 7768669 := bstep (se 3 (by rfl) ⟨1456625, by rfl⟩ : syracuseStep 7768669 = 2913251) B2913251
theorem B4090571 : Blo 1817610 4090571 := bstep (se 1 (by rfl) ⟨3067928, by rfl⟩ : syracuseStep 4090571 = 6135857) B6135857
theorem B10496729 : Blo 1817610 10496729 := bstep (se 2 (by rfl) ⟨3936273, by rfl⟩ : syracuseStep 10496729 = 7872547) B7872547
theorem B4090625 : Blo 1817610 4090625 := bstep (se 2 (by rfl) ⟨1533984, by rfl⟩ : syracuseStep 4090625 = 3067969) B3067969
theorem B6998807 : Blo 1817610 6998807 := bstep (se 1 (by rfl) ⟨5249105, by rfl⟩ : syracuseStep 6998807 = 10498211) B10498211
theorem B5180183 : Blo 1817610 5180183 := bstep (se 1 (by rfl) ⟨3885137, by rfl⟩ : syracuseStep 5180183 = 7770275) B7770275
theorem B3885889 : Blo 1817610 3885889 := bstep (se 2 (by rfl) ⟨1457208, by rfl⟩ : syracuseStep 3885889 = 2914417) B2914417
theorem B6138827 : Blo 1817610 6138827 := bstep (se 1 (by rfl) ⟨4604120, by rfl⟩ : syracuseStep 6138827 = 9208241) B9208241
theorem B6556619 : Blo 1817610 6556619 := bstep (se 1 (by rfl) ⟨4917464, by rfl⟩ : syracuseStep 6556619 = 9834929) B9834929
theorem B4090841 : Blo 1817610 4090841 := bstep (se 2 (by rfl) ⟨1534065, by rfl⟩ : syracuseStep 4090841 = 3068131) B3068131
theorem B3451891 : Blo 1817610 3451891 := bstep (se 1 (by rfl) ⟨2588918, by rfl⟩ : syracuseStep 3451891 = 5177837) B5177837
theorem B9202733 : Blo 1817610 9202733 := bstep (se 3 (by rfl) ⟨1725512, by rfl⟩ : syracuseStep 9202733 = 3451025) B3451025
theorem B4090931 : Blo 1817610 4090931 := bstep (se 1 (by rfl) ⟨3068198, by rfl⟩ : syracuseStep 4090931 = 6136397) B6136397
theorem B4090967 : Blo 1817610 4090967 := bstep (se 1 (by rfl) ⟨3068225, by rfl⟩ : syracuseStep 4090967 = 6136451) B6136451
theorem B7376017 : Blo 1817610 7376017 := bstep (se 2 (by rfl) ⟨2766006, by rfl⟩ : syracuseStep 7376017 = 5532013) B5532013
theorem B1969367 : Blo 1817610 1969367 := bstep (se 1 (by rfl) ⟨1477025, by rfl⟩ : syracuseStep 1969367 = 2954051) B2954051
theorem B6139097 : Blo 1817610 6139097 := bstep (se 2 (by rfl) ⟨2302161, by rfl⟩ : syracuseStep 6139097 = 4604323) B4604323
theorem B4091147 : Blo 1817610 4091147 := bstep (se 1 (by rfl) ⟨3068360, by rfl⟩ : syracuseStep 4091147 = 6136721) B6136721
theorem B4091201 : Blo 1817610 4091201 := bstep (se 2 (by rfl) ⟨1534200, by rfl⟩ : syracuseStep 4091201 = 3068401) B3068401
theorem B11808179 : Blo 1817610 11808179 := bstep (se 1 (by rfl) ⟨8856134, by rfl⟩ : syracuseStep 11808179 = 17712269) B17712269
theorem B3452377 : Blo 1817610 3452377 := bstep (se 2 (by rfl) ⟨1294641, by rfl⟩ : syracuseStep 3452377 = 2589283) B2589283
theorem B6557207 : Blo 1817610 6557207 := bstep (se 1 (by rfl) ⟨4917905, by rfl⟩ : syracuseStep 6557207 = 9835811) B9835811
theorem B4091417 : Blo 1817610 4091417 := bstep (se 2 (by rfl) ⟨1534281, by rfl⟩ : syracuseStep 4091417 = 3068563) B3068563
theorem B5180993 : Blo 1817610 5180993 := bstep (se 2 (by rfl) ⟨1942872, by rfl⟩ : syracuseStep 5180993 = 3885745) B3885745
theorem B8736331 : Blo 1817610 8736331 := bstep (se 1 (by rfl) ⟨6552248, by rfl⟩ : syracuseStep 8736331 = 13104497) B13104497
theorem B4091507 : Blo 1817610 4091507 := bstep (se 1 (by rfl) ⟨3068630, by rfl⟩ : syracuseStep 4091507 = 6137261) B6137261
theorem B4091543 : Blo 1817610 4091543 := bstep (se 1 (by rfl) ⟨3068657, by rfl⟩ : syracuseStep 4091543 = 6137315) B6137315
theorem B4427443 : Blo 1817610 4427443 := bstep (se 1 (by rfl) ⟨3320582, by rfl⟩ : syracuseStep 4427443 = 6641165) B6641165
theorem B13102883 : Blo 1817610 13102883 := bstep (se 1 (by rfl) ⟨9827162, by rfl⟩ : syracuseStep 13102883 = 19654325) B19654325
theorem B11652929 : Blo 1817610 11652929 := bstep (se 2 (by rfl) ⟨4369848, by rfl⟩ : syracuseStep 11652929 = 8739697) B8739697
theorem B4091723 : Blo 1817610 4091723 := bstep (se 1 (by rfl) ⟨3068792, by rfl⟩ : syracuseStep 4091723 = 6137585) B6137585
theorem B3788633 : Blo 1817610 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B4091777 : Blo 1817610 4091777 := bstep (se 2 (by rfl) ⟨1534416, by rfl⟩ : syracuseStep 4091777 = 3068833) B3068833
theorem B3067787 : Blo 1817610 3067787 := bstep (se 1 (by rfl) ⟨2300840, by rfl⟩ : syracuseStep 3067787 = 4601681) B4601681
theorem B7770001 : Blo 1817610 7770001 := bstep (se 2 (by rfl) ⟨2913750, by rfl⟩ : syracuseStep 7770001 = 5827501) B5827501
theorem B6139799 : Blo 1817610 6139799 := bstep (se 1 (by rfl) ⟨4604849, by rfl⟩ : syracuseStep 6139799 = 9209699) B9209699
theorem B3067915 : Blo 1817610 3067915 := bstep (se 1 (by rfl) ⟨2300936, by rfl⟩ : syracuseStep 3067915 = 4601873) B4601873
theorem B3452939 : Blo 1817610 3452939 := bstep (se 1 (by rfl) ⟨2589704, by rfl⟩ : syracuseStep 3452939 = 5179409) B5179409
theorem B27308107 : Blo 1817610 27308107 := bstep (se 1 (by rfl) ⟨20481080, by rfl⟩ : syracuseStep 27308107 = 40962161) B40962161
theorem B4091993 : Blo 1817610 4091993 := bstep (se 2 (by rfl) ⟨1534497, by rfl⟩ : syracuseStep 4091993 = 3068995) B3068995
theorem B3068057 : Blo 1817610 3068057 := bstep (se 2 (by rfl) ⟨1150521, by rfl⟩ : syracuseStep 3068057 = 2301043) B2301043
theorem B8736947 : Blo 1817610 8736947 := bstep (se 1 (by rfl) ⟨6552710, by rfl⟩ : syracuseStep 8736947 = 13105421) B13105421
theorem B4092083 : Blo 1817610 4092083 := bstep (se 1 (by rfl) ⟨3069062, by rfl⟩ : syracuseStep 4092083 = 6138125) B6138125
theorem B3453121 : Blo 1817610 3453121 := bstep (se 2 (by rfl) ⟨1294920, by rfl⟩ : syracuseStep 3453121 = 2589841) B2589841
theorem B29495501 : Blo 1817610 29495501 := bstep (se 3 (by rfl) ⟨5530406, by rfl⟩ : syracuseStep 29495501 = 11060813) B11060813
theorem B4092119 : Blo 1817610 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B7377155 : Blo 1817610 7377155 := bstep (se 1 (by rfl) ⟨5532866, by rfl⟩ : syracuseStep 7377155 = 11065733) B11065733
theorem B3068185 : Blo 1817610 3068185 := bstep (se 2 (by rfl) ⟨1150569, by rfl⟩ : syracuseStep 3068185 = 2301139) B2301139
theorem B6902081 : Blo 1817610 6902081 := bstep (se 2 (by rfl) ⟨2588280, by rfl⟩ : syracuseStep 6902081 = 5176561) B5176561
theorem B14954827 : Blo 1817610 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B4092299 : Blo 1817610 4092299 := bstep (se 1 (by rfl) ⟨3069224, by rfl⟩ : syracuseStep 4092299 = 6138449) B6138449
theorem B6140339 : Blo 1817610 6140339 := bstep (se 1 (by rfl) ⟨4605254, by rfl⟩ : syracuseStep 6140339 = 9210509) B9210509
theorem B4092353 : Blo 1817610 4092353 := bstep (se 2 (by rfl) ⟨1534632, by rfl⟩ : syracuseStep 4092353 = 3069265) B3069265
theorem B14586317 : Blo 1817610 14586317 := bstep (se 3 (by rfl) ⟨2734934, by rfl⟩ : syracuseStep 14586317 = 5469869) B5469869
theorem B4092569 : Blo 1817610 4092569 := bstep (se 2 (by rfl) ⟨1534713, by rfl⟩ : syracuseStep 4092569 = 3069427) B3069427
theorem B6140609 : Blo 1817610 6140609 := bstep (se 2 (by rfl) ⟨2302728, by rfl⟩ : syracuseStep 6140609 = 4605457) B4605457
theorem B111932117 : Blo 1817610 111932117 := bstep (se 7 (by rfl) ⟨1311704, by rfl⟩ : syracuseStep 111932117 = 2623409) B2623409
theorem B4092659 : Blo 1817610 4092659 := bstep (se 1 (by rfl) ⟨3069494, by rfl⟩ : syracuseStep 4092659 = 6138989) B6138989
theorem B4092695 : Blo 1817610 4092695 := bstep (se 1 (by rfl) ⟨3069521, by rfl⟩ : syracuseStep 4092695 = 6139043) B6139043
theorem B3068759 : Blo 1817610 3068759 := bstep (se 1 (by rfl) ⟨2301569, by rfl⟩ : syracuseStep 3068759 = 4603139) B4603139
theorem B10359683 : Blo 1817610 10359683 := bstep (se 1 (by rfl) ⟨7769762, by rfl⟩ : syracuseStep 10359683 = 15539525) B15539525
theorem B3453835 : Blo 1817610 3453835 := bstep (se 1 (by rfl) ⟨2590376, by rfl⟩ : syracuseStep 3453835 = 5180753) B5180753
theorem B8737715 : Blo 1817610 8737715 := bstep (se 1 (by rfl) ⟨6553286, by rfl⟩ : syracuseStep 8737715 = 13106573) B13106573
theorem B4092875 : Blo 1817610 4092875 := bstep (se 1 (by rfl) ⟨3069656, by rfl⟩ : syracuseStep 4092875 = 6139313) B6139313
theorem B3068887 : Blo 1817610 3068887 := bstep (se 1 (by rfl) ⟨2301665, by rfl⟩ : syracuseStep 3068887 = 4603331) B4603331
theorem B3453911 : Blo 1817610 3453911 := bstep (se 1 (by rfl) ⟨2590433, by rfl⟩ : syracuseStep 3453911 = 5180867) B5180867
theorem B4092929 : Blo 1817610 4092929 := bstep (se 2 (by rfl) ⟨1534848, by rfl⟩ : syracuseStep 4092929 = 3069697) B3069697
theorem B2044939 : Blo 1817610 2044939 := bstep (se 1 (by rfl) ⟨1533704, by rfl⟩ : syracuseStep 2044939 = 3067409) B3067409
theorem B4600921 : Blo 1817610 4600921 := bstep (se 2 (by rfl) ⟨1725345, by rfl⟩ : syracuseStep 4600921 = 3450691) B3450691
theorem B2045047 : Blo 1817610 2045047 := bstep (se 1 (by rfl) ⟨1533785, by rfl⟩ : syracuseStep 2045047 = 3067571) B3067571
theorem B9827507 : Blo 1817610 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B4093145 : Blo 1817610 4093145 := bstep (se 2 (by rfl) ⟨1534929, by rfl⟩ : syracuseStep 4093145 = 3069859) B3069859
theorem B6141149 : Blo 1817610 6141149 := bstep (se 3 (by rfl) ⟨1151465, by rfl⟩ : syracuseStep 6141149 = 2302931) B2302931
theorem B2045227 : Blo 1817610 2045227 := bstep (se 1 (by rfl) ⟨1533920, by rfl⟩ : syracuseStep 2045227 = 3067841) B3067841
theorem B4093235 : Blo 1817610 4093235 := bstep (se 1 (by rfl) ⟨3069926, by rfl⟩ : syracuseStep 4093235 = 6139853) B6139853
theorem B2331991 : Blo 1817610 2331991 := bstep (se 1 (by rfl) ⟨1748993, by rfl⟩ : syracuseStep 2331991 = 3497987) B3497987
theorem B4093271 : Blo 1817610 4093271 := bstep (se 1 (by rfl) ⟨3069953, by rfl⟩ : syracuseStep 4093271 = 6139907) B6139907
theorem B11064707 : Blo 1817610 11064707 := bstep (se 1 (by rfl) ⟨8298530, by rfl⟩ : syracuseStep 11064707 = 16597061) B16597061
theorem B2045335 : Blo 1817610 2045335 := bstep (se 1 (by rfl) ⟨1534001, by rfl⟩ : syracuseStep 2045335 = 3068003) B3068003
theorem B4093451 : Blo 1817610 4093451 := bstep (se 1 (by rfl) ⟨3070088, by rfl⟩ : syracuseStep 4093451 = 6140177) B6140177
theorem B3937817 : Blo 1817610 3937817 := bstep (se 2 (by rfl) ⟨1476681, by rfl⟩ : syracuseStep 3937817 = 2953363) B2953363
theorem B4093505 : Blo 1817610 4093505 := bstep (se 2 (by rfl) ⟨1535064, by rfl⟩ : syracuseStep 4093505 = 3070129) B3070129
theorem B22410827 : Blo 1817610 22410827 := bstep (se 1 (by rfl) ⟨16808120, by rfl⟩ : syracuseStep 22410827 = 33616241) B33616241
theorem B2045515 : Blo 1817610 2045515 := bstep (se 1 (by rfl) ⟨1534136, by rfl⟩ : syracuseStep 2045515 = 3068273) B3068273
theorem B3069515 : Blo 1817610 3069515 := bstep (se 1 (by rfl) ⟨2302136, by rfl⟩ : syracuseStep 3069515 = 4604273) B4604273
theorem B11646595 : Blo 1817610 11646595 := bstep (se 1 (by rfl) ⟨8734946, by rfl⟩ : syracuseStep 11646595 = 17469893) B17469893
theorem B3110539 : Blo 1817610 3110539 := bstep (se 1 (by rfl) ⟨2332904, by rfl⟩ : syracuseStep 3110539 = 4665809) B4665809
theorem B6641297 : Blo 1817610 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B15537815 : Blo 1817610 15537815 := bstep (se 1 (by rfl) ⟨11653361, by rfl⟩ : syracuseStep 15537815 = 23306723) B23306723
theorem B2045623 : Blo 1817610 2045623 := bstep (se 1 (by rfl) ⟨1534217, by rfl⟩ : syracuseStep 2045623 = 3068435) B3068435
theorem B3069643 : Blo 1817610 3069643 := bstep (se 1 (by rfl) ⟨2302232, by rfl⟩ : syracuseStep 3069643 = 4604465) B4604465
theorem B6903569 : Blo 1817610 6903569 := bstep (se 2 (by rfl) ⟨2588838, by rfl⟩ : syracuseStep 6903569 = 5177677) B5177677
theorem B4093721 : Blo 1817610 4093721 := bstep (se 2 (by rfl) ⟨1535145, by rfl⟩ : syracuseStep 4093721 = 3070291) B3070291
theorem B3069785 : Blo 1817610 3069785 := bstep (se 2 (by rfl) ⟨1151169, by rfl⟩ : syracuseStep 3069785 = 2302339) B2302339
theorem B2045803 : Blo 1817610 2045803 := bstep (se 1 (by rfl) ⟨1534352, by rfl⟩ : syracuseStep 2045803 = 3068705) B3068705
theorem B4093811 : Blo 1817610 4093811 := bstep (se 1 (by rfl) ⟨3070358, by rfl⟩ : syracuseStep 4093811 = 6140717) B6140717
theorem B3110795 : Blo 1817610 3110795 := bstep (se 1 (by rfl) ⟨2333096, by rfl⟩ : syracuseStep 3110795 = 4666193) B4666193
theorem B4093847 : Blo 1817610 4093847 := bstep (se 1 (by rfl) ⟨3070385, by rfl⟩ : syracuseStep 4093847 = 6140771) B6140771
theorem B2045911 : Blo 1817610 2045911 := bstep (se 1 (by rfl) ⟨1534433, by rfl⟩ : syracuseStep 2045911 = 3068867) B3068867
theorem B3069913 : Blo 1817610 3069913 := bstep (se 2 (by rfl) ⟨1151217, by rfl⟩ : syracuseStep 3069913 = 2302435) B2302435
theorem B7763971 : Blo 1817610 7763971 := bstep (se 1 (by rfl) ⟨5822978, by rfl⟩ : syracuseStep 7763971 = 11645957) B11645957
theorem B3151883 : Blo 1817610 3151883 := bstep (se 1 (by rfl) ⟨2363912, by rfl⟩ : syracuseStep 3151883 = 4727825) B4727825
theorem B4094027 : Blo 1817610 4094027 := bstep (se 1 (by rfl) ⟨3070520, by rfl⟩ : syracuseStep 4094027 = 6141041) B6141041
theorem B4094081 : Blo 1817610 4094081 := bstep (se 2 (by rfl) ⟨1535280, by rfl⟩ : syracuseStep 4094081 = 3070561) B3070561
theorem B2046091 : Blo 1817610 2046091 := bstep (se 1 (by rfl) ⟨1534568, by rfl⟩ : syracuseStep 2046091 = 3069137) B3069137
theorem B4602035 : Blo 1817610 4602035 := bstep (se 1 (by rfl) ⟨3451526, by rfl⟩ : syracuseStep 4602035 = 6903053) B6903053
theorem B48560309 : Blo 1817610 48560309 := bstep (se 5 (by rfl) ⟨2276264, by rfl⟩ : syracuseStep 48560309 = 4552529) B4552529
theorem B6904025 : Blo 1817610 6904025 := bstep (se 2 (by rfl) ⟨2589009, by rfl⟩ : syracuseStep 6904025 = 5178019) B5178019
theorem B2046199 : Blo 1817610 2046199 := bstep (se 1 (by rfl) ⟨1534649, by rfl⟩ : syracuseStep 2046199 = 3069299) B3069299
theorem B2914571 : Blo 1817610 2914571 := bstep (se 1 (by rfl) ⟨2185928, by rfl⟩ : syracuseStep 2914571 = 4371857) B4371857
theorem B2046379 : Blo 1817610 2046379 := bstep (se 1 (by rfl) ⟨1534784, by rfl⟩ : syracuseStep 2046379 = 3069569) B3069569
theorem B6904237 : Blo 1817610 6904237 := bstep (se 3 (by rfl) ⟨1294544, by rfl⟩ : syracuseStep 6904237 = 2589089) B2589089
theorem B4602329 : Blo 1817610 4602329 := bstep (se 2 (by rfl) ⟨1725873, by rfl⟩ : syracuseStep 4602329 = 3451747) B3451747
theorem B2726423 : Blo 1817610 2726423 := bstep (se 1 (by rfl) ⟨2044817, by rfl⟩ : syracuseStep 2726423 = 4089635) B4089635
theorem B2046487 : Blo 1817610 2046487 := bstep (se 1 (by rfl) ⟨1534865, by rfl⟩ : syracuseStep 2046487 = 3069731) B3069731
theorem B3070487 : Blo 1817610 3070487 := bstep (se 1 (by rfl) ⟨2302865, by rfl⟩ : syracuseStep 3070487 = 4605731) B4605731
theorem B2300491 : Blo 1817610 2300491 := bstep (se 1 (by rfl) ⟨1725368, by rfl⟩ : syracuseStep 2300491 = 3450737) B3450737
theorem B2726489 : Blo 1817610 2726489 := bstep (se 2 (by rfl) ⟨1022433, by rfl⟩ : syracuseStep 2726489 = 2044867) B2044867
theorem B7764569 : Blo 1817610 7764569 := bstep (se 2 (by rfl) ⟨2911713, by rfl⟩ : syracuseStep 7764569 = 5823427) B5823427
theorem B7371409 : Blo 1817610 7371409 := bstep (se 2 (by rfl) ⟨2764278, by rfl⟩ : syracuseStep 7371409 = 5528557) B5528557
theorem B2726603 : Blo 1817610 2726603 := bstep (se 1 (by rfl) ⟨2044952, by rfl⟩ : syracuseStep 2726603 = 4089905) B4089905
theorem B2046667 : Blo 1817610 2046667 := bstep (se 1 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 2046667 = 3070001) B3070001
theorem B2726615 : Blo 1817610 2726615 := bstep (se 1 (by rfl) ⟨2044961, by rfl⟩ : syracuseStep 2726615 = 4089923) B4089923
theorem B4913885 : Blo 1817610 4913885 := bstep (se 3 (by rfl) ⟨921353, by rfl⟩ : syracuseStep 4913885 = 1842707) B1842707
theorem B6904541 : Blo 1817610 6904541 := bstep (se 3 (by rfl) ⟨1294601, by rfl⟩ : syracuseStep 6904541 = 2589203) B2589203
theorem B2726681 : Blo 1817610 2726681 := bstep (se 2 (by rfl) ⟨1022505, by rfl⟩ : syracuseStep 2726681 = 2045011) B2045011
theorem B2046775 : Blo 1817610 2046775 := bstep (se 1 (by rfl) ⟨1535081, by rfl⟩ : syracuseStep 2046775 = 3070163) B3070163
theorem B9206621 : Blo 1817610 9206621 := bstep (se 3 (by rfl) ⟨1726241, by rfl⟩ : syracuseStep 9206621 = 3452483) B3452483
theorem B2726795 : Blo 1817610 2726795 := bstep (se 1 (by rfl) ⟨2045096, by rfl⟩ : syracuseStep 2726795 = 4090193) B4090193
theorem B2726807 : Blo 1817610 2726807 := bstep (se 1 (by rfl) ⟨2045105, by rfl⟩ : syracuseStep 2726807 = 4090211) B4090211
theorem B7764929 : Blo 1817610 7764929 := bstep (se 2 (by rfl) ⟨2911848, by rfl⟩ : syracuseStep 7764929 = 5823697) B5823697
theorem B25213913 : Blo 1817610 25213913 := bstep (se 2 (by rfl) ⟨9455217, by rfl⟩ : syracuseStep 25213913 = 18910435) B18910435
theorem B2726873 : Blo 1817610 2726873 := bstep (se 2 (by rfl) ⟨1022577, by rfl⟩ : syracuseStep 2726873 = 2045155) B2045155
theorem B2046955 : Blo 1817610 2046955 := bstep (se 1 (by rfl) ⟨1535216, by rfl⟩ : syracuseStep 2046955 = 3070433) B3070433
theorem B1817611 : Blo 1817610 1817611 := bstep (se 1 (by rfl) ⟨1363208, by rfl⟩ : syracuseStep 1817611 = 2726417) B2726417
theorem B78642197 : Blo 1817610 78642197 := bstep (se 6 (by rfl) ⟨1843176, by rfl⟩ : syracuseStep 78642197 = 3686353) B3686353
theorem B1817623 : Blo 1817610 1817623 := bstep (se 1 (by rfl) ⟨1363217, by rfl⟩ : syracuseStep 1817623 = 2726435) B2726435
theorem B1817643 : Blo 1817610 1817643 := bstep (se 1 (by rfl) ⟨1363232, by rfl⟩ : syracuseStep 1817643 = 2726465) B2726465
theorem B1817655 : Blo 1817610 1817655 := bstep (se 1 (by rfl) ⟨1363241, by rfl⟩ : syracuseStep 1817655 = 2726483) B2726483
theorem B1817675 : Blo 1817610 1817675 := bstep (se 1 (by rfl) ⟨1363256, by rfl⟩ : syracuseStep 1817675 = 2726513) B2726513
theorem B2726987 : Blo 1817610 2726987 := bstep (se 1 (by rfl) ⟨2045240, by rfl⟩ : syracuseStep 2726987 = 4090481) B4090481
theorem B1817687 : Blo 1817610 1817687 := bstep (se 1 (by rfl) ⟨1363265, by rfl⟩ : syracuseStep 1817687 = 2726531) B2726531
theorem B2726999 : Blo 1817610 2726999 := bstep (se 1 (by rfl) ⟨2045249, by rfl⟩ : syracuseStep 2726999 = 4090499) B4090499
theorem B1817707 : Blo 1817610 1817707 := bstep (se 1 (by rfl) ⟨1363280, by rfl⟩ : syracuseStep 1817707 = 2726561) B2726561
theorem B1817719 : Blo 1817610 1817719 := bstep (se 1 (by rfl) ⟨1363289, by rfl⟩ : syracuseStep 1817719 = 2726579) B2726579
theorem B1817739 : Blo 1817610 1817739 := bstep (se 1 (by rfl) ⟨1363304, by rfl⟩ : syracuseStep 1817739 = 2726609) B2726609
theorem B1817751 : Blo 1817610 1817751 := bstep (se 1 (by rfl) ⟨1363313, by rfl⟩ : syracuseStep 1817751 = 2726627) B2726627
theorem B2727065 : Blo 1817610 2727065 := bstep (se 2 (by rfl) ⟨1022649, by rfl⟩ : syracuseStep 2727065 = 2045299) B2045299
theorem B1817771 : Blo 1817610 1817771 := bstep (se 1 (by rfl) ⟨1363328, by rfl⟩ : syracuseStep 1817771 = 2726657) B2726657
theorem B1817783 : Blo 1817610 1817783 := bstep (se 1 (by rfl) ⟨1363337, by rfl⟩ : syracuseStep 1817783 = 2726675) B2726675
theorem B1817803 : Blo 1817610 1817803 := bstep (se 1 (by rfl) ⟨1363352, by rfl⟩ : syracuseStep 1817803 = 2726705) B2726705
theorem B1817815 : Blo 1817610 1817815 := bstep (se 1 (by rfl) ⟨1363361, by rfl⟩ : syracuseStep 1817815 = 2726723) B2726723
theorem B4488409 : Blo 1817610 4488409 := bstep (se 2 (by rfl) ⟨1683153, by rfl⟩ : syracuseStep 4488409 = 3366307) B3366307
theorem B1817835 : Blo 1817610 1817835 := bstep (se 1 (by rfl) ⟨1363376, by rfl⟩ : syracuseStep 1817835 = 2726753) B2726753
theorem B1817847 : Blo 1817610 1817847 := bstep (se 1 (by rfl) ⟨1363385, by rfl⟩ : syracuseStep 1817847 = 2726771) B2726771
theorem B1817867 : Blo 1817610 1817867 := bstep (se 1 (by rfl) ⟨1363400, by rfl⟩ : syracuseStep 1817867 = 2726801) B2726801
theorem B2727179 : Blo 1817610 2727179 := bstep (se 1 (by rfl) ⟨2045384, by rfl⟩ : syracuseStep 2727179 = 4090769) B4090769
theorem B1817879 : Blo 1817610 1817879 := bstep (se 1 (by rfl) ⟨1363409, by rfl⟩ : syracuseStep 1817879 = 2726819) B2726819
theorem B2727191 : Blo 1817610 2727191 := bstep (se 1 (by rfl) ⟨2045393, by rfl⟩ : syracuseStep 2727191 = 4090787) B4090787
theorem B1817899 : Blo 1817610 1817899 := bstep (se 1 (by rfl) ⟨1363424, by rfl⟩ : syracuseStep 1817899 = 2726849) B2726849
theorem B1817911 : Blo 1817610 1817911 := bstep (se 1 (by rfl) ⟨1363433, by rfl⟩ : syracuseStep 1817911 = 2726867) B2726867
theorem B1817931 : Blo 1817610 1817931 := bstep (se 1 (by rfl) ⟨1363448, by rfl⟩ : syracuseStep 1817931 = 2726897) B2726897
theorem B1817943 : Blo 1817610 1817943 := bstep (se 1 (by rfl) ⟨1363457, by rfl⟩ : syracuseStep 1817943 = 2726915) B2726915
theorem B3276119 : Blo 1817610 3276119 := bstep (se 1 (by rfl) ⟨2457089, by rfl⟩ : syracuseStep 3276119 = 4914179) B4914179
theorem B2727257 : Blo 1817610 2727257 := bstep (se 2 (by rfl) ⟨1022721, by rfl⟩ : syracuseStep 2727257 = 2045443) B2045443
theorem B1817963 : Blo 1817610 1817963 := bstep (se 1 (by rfl) ⟨1363472, by rfl⟩ : syracuseStep 1817963 = 2726945) B2726945
theorem B1817975 : Blo 1817610 1817975 := bstep (se 1 (by rfl) ⟨1363481, by rfl⟩ : syracuseStep 1817975 = 2726963) B2726963
theorem B1817995 : Blo 1817610 1817995 := bstep (se 1 (by rfl) ⟨1363496, by rfl⟩ : syracuseStep 1817995 = 2726993) B2726993
theorem B1818007 : Blo 1817610 1818007 := bstep (se 1 (by rfl) ⟨1363505, by rfl⟩ : syracuseStep 1818007 = 2727011) B2727011
theorem B1818027 : Blo 1817610 1818027 := bstep (se 1 (by rfl) ⟨1363520, by rfl⟩ : syracuseStep 1818027 = 2727041) B2727041
theorem B1818039 : Blo 1817610 1818039 := bstep (se 1 (by rfl) ⟨1363529, by rfl⟩ : syracuseStep 1818039 = 2727059) B2727059
theorem B1818059 : Blo 1817610 1818059 := bstep (se 1 (by rfl) ⟨1363544, by rfl⟩ : syracuseStep 1818059 = 2727089) B2727089
theorem B2727371 : Blo 1817610 2727371 := bstep (se 1 (by rfl) ⟨2045528, by rfl⟩ : syracuseStep 2727371 = 4091057) B4091057
theorem B1818071 : Blo 1817610 1818071 := bstep (se 1 (by rfl) ⟨1363553, by rfl⟩ : syracuseStep 1818071 = 2727107) B2727107
theorem B2727383 : Blo 1817610 2727383 := bstep (se 1 (by rfl) ⟨2045537, by rfl⟩ : syracuseStep 2727383 = 4091075) B4091075
theorem B1818091 : Blo 1817610 1818091 := bstep (se 1 (by rfl) ⟨1363568, by rfl⟩ : syracuseStep 1818091 = 2727137) B2727137
theorem B1818103 : Blo 1817610 1818103 := bstep (se 1 (by rfl) ⟨1363577, by rfl⟩ : syracuseStep 1818103 = 2727155) B2727155
theorem B1818123 : Blo 1817610 1818123 := bstep (se 1 (by rfl) ⟨1363592, by rfl⟩ : syracuseStep 1818123 = 2727185) B2727185
theorem B1818135 : Blo 1817610 1818135 := bstep (se 1 (by rfl) ⟨1363601, by rfl⟩ : syracuseStep 1818135 = 2727203) B2727203
theorem B2301463 : Blo 1817610 2301463 := bstep (se 1 (by rfl) ⟨1726097, by rfl⟩ : syracuseStep 2301463 = 3452195) B3452195
theorem B2727449 : Blo 1817610 2727449 := bstep (se 2 (by rfl) ⟨1022793, by rfl⟩ : syracuseStep 2727449 = 2045587) B2045587
theorem B1818155 : Blo 1817610 1818155 := bstep (se 1 (by rfl) ⟨1363616, by rfl⟩ : syracuseStep 1818155 = 2727233) B2727233
theorem B1818167 : Blo 1817610 1818167 := bstep (se 1 (by rfl) ⟨1363625, by rfl⟩ : syracuseStep 1818167 = 2727251) B2727251
theorem B6135371 : Blo 1817610 6135371 := bstep (se 1 (by rfl) ⟨4601528, by rfl⟩ : syracuseStep 6135371 = 9203057) B9203057
theorem B1818187 : Blo 1817610 1818187 := bstep (se 1 (by rfl) ⟨1363640, by rfl⟩ : syracuseStep 1818187 = 2727281) B2727281
theorem B1818199 : Blo 1817610 1818199 := bstep (se 1 (by rfl) ⟨1363649, by rfl⟩ : syracuseStep 1818199 = 2727299) B2727299
theorem B1818219 : Blo 1817610 1818219 := bstep (se 1 (by rfl) ⟨1363664, by rfl⟩ : syracuseStep 1818219 = 2727329) B2727329
theorem B1818231 : Blo 1817610 1818231 := bstep (se 1 (by rfl) ⟨1363673, by rfl⟩ : syracuseStep 1818231 = 2727347) B2727347
theorem B1818251 : Blo 1817610 1818251 := bstep (se 1 (by rfl) ⟨1363688, by rfl⟩ : syracuseStep 1818251 = 2727377) B2727377
theorem B2727563 : Blo 1817610 2727563 := bstep (se 1 (by rfl) ⟨2045672, by rfl⟩ : syracuseStep 2727563 = 4091345) B4091345
theorem B1818263 : Blo 1817610 1818263 := bstep (se 1 (by rfl) ⟨1363697, by rfl⟩ : syracuseStep 1818263 = 2727395) B2727395
theorem B5529239 : Blo 1817610 5529239 := bstep (se 1 (by rfl) ⟨4146929, by rfl⟩ : syracuseStep 5529239 = 8293859) B8293859
theorem B2727575 : Blo 1817610 2727575 := bstep (se 1 (by rfl) ⟨2045681, by rfl⟩ : syracuseStep 2727575 = 4091363) B4091363
theorem B1818283 : Blo 1817610 1818283 := bstep (se 1 (by rfl) ⟨1363712, by rfl⟩ : syracuseStep 1818283 = 2727425) B2727425
theorem B1818295 : Blo 1817610 1818295 := bstep (se 1 (by rfl) ⟨1363721, by rfl⟩ : syracuseStep 1818295 = 2727443) B2727443
theorem B1818315 : Blo 1817610 1818315 := bstep (se 1 (by rfl) ⟨1363736, by rfl⟩ : syracuseStep 1818315 = 2727473) B2727473
theorem B1818327 : Blo 1817610 1818327 := bstep (se 1 (by rfl) ⟨1363745, by rfl⟩ : syracuseStep 1818327 = 2727491) B2727491
theorem B2727641 : Blo 1817610 2727641 := bstep (se 2 (by rfl) ⟨1022865, by rfl⟩ : syracuseStep 2727641 = 2045731) B2045731
theorem B1818347 : Blo 1817610 1818347 := bstep (se 1 (by rfl) ⟨1363760, by rfl⟩ : syracuseStep 1818347 = 2727521) B2727521
theorem B1818359 : Blo 1817610 1818359 := bstep (se 1 (by rfl) ⟨1363769, by rfl⟩ : syracuseStep 1818359 = 2727539) B2727539
theorem B1818379 : Blo 1817610 1818379 := bstep (se 1 (by rfl) ⟨1363784, by rfl⟩ : syracuseStep 1818379 = 2727569) B2727569
theorem B1818391 : Blo 1817610 1818391 := bstep (se 1 (by rfl) ⟨1363793, by rfl⟩ : syracuseStep 1818391 = 2727587) B2727587
theorem B1818411 : Blo 1817610 1818411 := bstep (se 1 (by rfl) ⟨1363808, by rfl⟩ : syracuseStep 1818411 = 2727617) B2727617
theorem B1818423 : Blo 1817610 1818423 := bstep (se 1 (by rfl) ⟨1363817, by rfl⟩ : syracuseStep 1818423 = 2727635) B2727635
theorem B4915009 : Blo 1817610 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B1818443 : Blo 1817610 1818443 := bstep (se 1 (by rfl) ⟨1363832, by rfl⟩ : syracuseStep 1818443 = 2727665) B2727665
theorem B2727755 : Blo 1817610 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B1818455 : Blo 1817610 1818455 := bstep (se 1 (by rfl) ⟨1363841, by rfl⟩ : syracuseStep 1818455 = 2727683) B2727683
theorem B2727767 : Blo 1817610 2727767 := bstep (se 1 (by rfl) ⟨2045825, by rfl⟩ : syracuseStep 2727767 = 4091651) B4091651
theorem B6135641 : Blo 1817610 6135641 := bstep (se 2 (by rfl) ⟨2300865, by rfl⟩ : syracuseStep 6135641 = 4601731) B4601731
theorem B1818475 : Blo 1817610 1818475 := bstep (se 1 (by rfl) ⟨1363856, by rfl⟩ : syracuseStep 1818475 = 2727713) B2727713
theorem B19668853 : Blo 1817610 19668853 := bstep (se 5 (by rfl) ⟨921977, by rfl⟩ : syracuseStep 19668853 = 1843955) B1843955
theorem B1818487 : Blo 1817610 1818487 := bstep (se 1 (by rfl) ⟨1363865, by rfl⟩ : syracuseStep 1818487 = 2727731) B2727731
theorem B1818507 : Blo 1817610 1818507 := bstep (se 1 (by rfl) ⟨1363880, by rfl⟩ : syracuseStep 1818507 = 2727761) B2727761
theorem B1818519 : Blo 1817610 1818519 := bstep (se 1 (by rfl) ⟨1363889, by rfl⟩ : syracuseStep 1818519 = 2727779) B2727779
theorem B2727833 : Blo 1817610 2727833 := bstep (se 2 (by rfl) ⟨1022937, by rfl⟩ : syracuseStep 2727833 = 2045875) B2045875
theorem B1818539 : Blo 1817610 1818539 := bstep (se 1 (by rfl) ⟨1363904, by rfl⟩ : syracuseStep 1818539 = 2727809) B2727809
theorem B13811633 : Blo 1817610 13811633 := bstep (se 2 (by rfl) ⟨5179362, by rfl⟩ : syracuseStep 13811633 = 10358725) B10358725
theorem B5177267 : Blo 1817610 5177267 := bstep (se 1 (by rfl) ⟨3882950, by rfl⟩ : syracuseStep 5177267 = 7765901) B7765901
theorem B1818551 : Blo 1817610 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B1818571 : Blo 1817610 1818571 := bstep (se 1 (by rfl) ⟨1363928, by rfl⟩ : syracuseStep 1818571 = 2727857) B2727857
theorem B1818583 : Blo 1817610 1818583 := bstep (se 1 (by rfl) ⟨1363937, by rfl⟩ : syracuseStep 1818583 = 2727875) B2727875
theorem B5824477 : Blo 1817610 5824477 := bstep (se 3 (by rfl) ⟨1092089, by rfl⟩ : syracuseStep 5824477 = 2184179) B2184179
theorem B1818603 : Blo 1817610 1818603 := bstep (se 1 (by rfl) ⟨1363952, by rfl⟩ : syracuseStep 1818603 = 2727905) B2727905
theorem B1818615 : Blo 1817610 1818615 := bstep (se 1 (by rfl) ⟨1363961, by rfl⟩ : syracuseStep 1818615 = 2727923) B2727923
theorem B1818631 : Blo 1817610 1818631 := bstep (se 1 (by rfl) ⟨1363973, by rfl⟩ : syracuseStep 1818631 = 2727947) B2727947
theorem B2301959 : Blo 1817610 2301959 := bstep (se 1 (by rfl) ⟨1726469, by rfl⟩ : syracuseStep 2301959 = 3452939) B3452939
theorem B1818639 : Blo 1817610 1818639 := bstep (se 1 (by rfl) ⟨1363979, by rfl⟩ : syracuseStep 1818639 = 2727959) B2727959
theorem B23625751 : Blo 1817610 23625751 := bstep (se 1 (by rfl) ⟨17719313, by rfl⟩ : syracuseStep 23625751 = 35438627) B35438627
theorem B8405021 : Blo 1817610 8405021 := bstep (se 3 (by rfl) ⟨1575941, by rfl⟩ : syracuseStep 8405021 = 3151883) B3151883
theorem B2727995 : Blo 1817610 2727995 := bstep (se 1 (by rfl) ⟨2045996, by rfl⟩ : syracuseStep 2727995 = 4091993) B4091993
theorem B1818683 : Blo 1817610 1818683 := bstep (se 1 (by rfl) ⟨1364012, by rfl⟩ : syracuseStep 1818683 = 2728025) B2728025
theorem B5824631 : Blo 1817610 5824631 := bstep (se 1 (by rfl) ⟨4368473, by rfl⟩ : syracuseStep 5824631 = 8736947) B8736947
theorem B2728055 : Blo 1817610 2728055 := bstep (se 1 (by rfl) ⟨2046041, by rfl⟩ : syracuseStep 2728055 = 4092083) B4092083
theorem B1818759 : Blo 1817610 1818759 := bstep (se 1 (by rfl) ⟨1364069, by rfl⟩ : syracuseStep 1818759 = 2728139) B2728139
theorem B2728079 : Blo 1817610 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B1818767 : Blo 1817610 1818767 := bstep (se 1 (by rfl) ⟨1364075, by rfl⟩ : syracuseStep 1818767 = 2728151) B2728151
theorem B2728121 : Blo 1817610 2728121 := bstep (se 2 (by rfl) ⟨1023045, by rfl⟩ : syracuseStep 2728121 = 2046091) B2046091
theorem B1818811 : Blo 1817610 1818811 := bstep (se 1 (by rfl) ⟨1364108, by rfl⟩ : syracuseStep 1818811 = 2728217) B2728217
theorem B4604161 : Blo 1817610 4604161 := bstep (se 2 (by rfl) ⟨1726560, by rfl⟩ : syracuseStep 4604161 = 3453121) B3453121
theorem B2728199 : Blo 1817610 2728199 := bstep (se 1 (by rfl) ⟨2046149, by rfl⟩ : syracuseStep 2728199 = 4092299) B4092299
theorem B1818887 : Blo 1817610 1818887 := bstep (se 1 (by rfl) ⟨1364165, by rfl⟩ : syracuseStep 1818887 = 2728331) B2728331
theorem B9208079 : Blo 1817610 9208079 := bstep (se 1 (by rfl) ⟨6906059, by rfl⟩ : syracuseStep 9208079 = 13812119) B13812119
theorem B1818895 : Blo 1817610 1818895 := bstep (se 1 (by rfl) ⟨1364171, by rfl⟩ : syracuseStep 1818895 = 2728343) B2728343
theorem B2728235 : Blo 1817610 2728235 := bstep (se 1 (by rfl) ⟨2046176, by rfl⟩ : syracuseStep 2728235 = 4092353) B4092353
theorem B9724211 : Blo 1817610 9724211 := bstep (se 1 (by rfl) ⟨7293158, by rfl⟩ : syracuseStep 9724211 = 14586317) B14586317
theorem B1818939 : Blo 1817610 1818939 := bstep (se 1 (by rfl) ⟨1364204, by rfl⟩ : syracuseStep 1818939 = 2728409) B2728409
theorem B2728265 : Blo 1817610 2728265 := bstep (se 2 (by rfl) ⟨1023099, by rfl⟩ : syracuseStep 2728265 = 2046199) B2046199
theorem B1819015 : Blo 1817610 1819015 := bstep (se 1 (by rfl) ⟨1364261, by rfl⟩ : syracuseStep 1819015 = 2728523) B2728523
theorem B1819023 : Blo 1817610 1819023 := bstep (se 1 (by rfl) ⟨1364267, by rfl⟩ : syracuseStep 1819023 = 2728535) B2728535
theorem B19939769 : Blo 1817610 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B2728379 : Blo 1817610 2728379 := bstep (se 1 (by rfl) ⟨2046284, by rfl⟩ : syracuseStep 2728379 = 4092569) B4092569
theorem B1819067 : Blo 1817610 1819067 := bstep (se 1 (by rfl) ⟨1364300, by rfl⟩ : syracuseStep 1819067 = 2728601) B2728601
theorem B4915657 : Blo 1817610 4915657 := bstep (se 2 (by rfl) ⟨1843371, by rfl⟩ : syracuseStep 4915657 = 3686743) B3686743
theorem B26206685 : Blo 1817610 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B74621411 : Blo 1817610 74621411 := bstep (se 1 (by rfl) ⟨55966058, by rfl⟩ : syracuseStep 74621411 = 111932117) B111932117
theorem B2589175 : Blo 1817610 2589175 := bstep (se 1 (by rfl) ⟨1941881, by rfl⟩ : syracuseStep 2589175 = 3883763) B3883763
theorem B2728439 : Blo 1817610 2728439 := bstep (se 1 (by rfl) ⟨2046329, by rfl⟩ : syracuseStep 2728439 = 4092659) B4092659
theorem B1819143 : Blo 1817610 1819143 := bstep (se 1 (by rfl) ⟨1364357, by rfl⟩ : syracuseStep 1819143 = 2728715) B2728715
theorem B2458127 : Blo 1817610 2458127 := bstep (se 1 (by rfl) ⟨1843595, by rfl⟩ : syracuseStep 2458127 = 3687191) B3687191
theorem B2728463 : Blo 1817610 2728463 := bstep (se 1 (by rfl) ⟨2046347, by rfl⟩ : syracuseStep 2728463 = 4092695) B4092695
theorem B1819151 : Blo 1817610 1819151 := bstep (se 1 (by rfl) ⟨1364363, by rfl⟩ : syracuseStep 1819151 = 2728727) B2728727
theorem B8741405 : Blo 1817610 8741405 := bstep (se 3 (by rfl) ⟨1639013, by rfl⟩ : syracuseStep 8741405 = 3278027) B3278027
theorem B2728505 : Blo 1817610 2728505 := bstep (se 2 (by rfl) ⟨1023189, by rfl⟩ : syracuseStep 2728505 = 2046379) B2046379
theorem B3686971 : Blo 1817610 3686971 := bstep (se 1 (by rfl) ⟨2765228, by rfl⟩ : syracuseStep 3686971 = 5530457) B5530457
theorem B1819195 : Blo 1817610 1819195 := bstep (se 1 (by rfl) ⟨1364396, by rfl⟩ : syracuseStep 1819195 = 2728793) B2728793
theorem B5251645 : Blo 1817610 5251645 := bstep (se 3 (by rfl) ⟨984683, by rfl⟩ : syracuseStep 5251645 = 1969367) B1969367
theorem B6906455 : Blo 1817610 6906455 := bstep (se 1 (by rfl) ⟨5179841, by rfl⟩ : syracuseStep 6906455 = 10359683) B10359683
theorem B5825143 : Blo 1817610 5825143 := bstep (se 1 (by rfl) ⟨4368857, by rfl⟩ : syracuseStep 5825143 = 8737715) B8737715
theorem B2728583 : Blo 1817610 2728583 := bstep (se 1 (by rfl) ⟨2046437, by rfl⟩ : syracuseStep 2728583 = 4092875) B4092875
theorem B1819271 : Blo 1817610 1819271 := bstep (se 1 (by rfl) ⟨1364453, by rfl⟩ : syracuseStep 1819271 = 2728907) B2728907
theorem B1819279 : Blo 1817610 1819279 := bstep (se 1 (by rfl) ⟨1364459, by rfl⟩ : syracuseStep 1819279 = 2728919) B2728919
theorem B2302607 : Blo 1817610 2302607 := bstep (se 1 (by rfl) ⟨1726955, by rfl⟩ : syracuseStep 2302607 = 3453911) B3453911
theorem B2728619 : Blo 1817610 2728619 := bstep (se 1 (by rfl) ⟨2046464, by rfl⟩ : syracuseStep 2728619 = 4092929) B4092929
theorem B1819323 : Blo 1817610 1819323 := bstep (se 1 (by rfl) ⟨1364492, by rfl⟩ : syracuseStep 1819323 = 2728985) B2728985
theorem B2728649 : Blo 1817610 2728649 := bstep (se 2 (by rfl) ⟨1023243, by rfl⟩ : syracuseStep 2728649 = 2046487) B2046487
theorem B1819399 : Blo 1817610 1819399 := bstep (se 1 (by rfl) ⟨1364549, by rfl⟩ : syracuseStep 1819399 = 2729099) B2729099
theorem B1819407 : Blo 1817610 1819407 := bstep (se 1 (by rfl) ⟨1364555, by rfl⟩ : syracuseStep 1819407 = 2729111) B2729111
theorem B2589499 : Blo 1817610 2589499 := bstep (se 1 (by rfl) ⟨1942124, by rfl⟩ : syracuseStep 2589499 = 3884249) B3884249
theorem B4916027 : Blo 1817610 4916027 := bstep (se 1 (by rfl) ⟨3687020, by rfl⟩ : syracuseStep 4916027 = 7374041) B7374041
theorem B2728763 : Blo 1817610 2728763 := bstep (se 1 (by rfl) ⟨2046572, by rfl⟩ : syracuseStep 2728763 = 4093145) B4093145
theorem B1819451 : Blo 1817610 1819451 := bstep (se 1 (by rfl) ⟨1364588, by rfl⟩ : syracuseStep 1819451 = 2729177) B2729177
theorem B4604759 : Blo 1817610 4604759 := bstep (se 1 (by rfl) ⟨3453569, by rfl⟩ : syracuseStep 4604759 = 6907139) B6907139
theorem B2728823 : Blo 1817610 2728823 := bstep (se 1 (by rfl) ⟨2046617, by rfl⟩ : syracuseStep 2728823 = 4093235) B4093235
theorem B1819527 : Blo 1817610 1819527 := bstep (se 1 (by rfl) ⟨1364645, by rfl⟩ : syracuseStep 1819527 = 2729291) B2729291
theorem B2728847 : Blo 1817610 2728847 := bstep (se 1 (by rfl) ⟨2046635, by rfl⟩ : syracuseStep 2728847 = 4093271) B4093271
theorem B1819535 : Blo 1817610 1819535 := bstep (se 1 (by rfl) ⟨1364651, by rfl⟩ : syracuseStep 1819535 = 2729303) B2729303
theorem B2728889 : Blo 1817610 2728889 := bstep (se 2 (by rfl) ⟨1023333, by rfl⟩ : syracuseStep 2728889 = 2046667) B2046667
theorem B1819579 : Blo 1817610 1819579 := bstep (se 1 (by rfl) ⟨1364684, by rfl⟩ : syracuseStep 1819579 = 2729369) B2729369
theorem B2728967 : Blo 1817610 2728967 := bstep (se 1 (by rfl) ⟨2046725, by rfl⟩ : syracuseStep 2728967 = 4093451) B4093451
theorem B4604971 : Blo 1817610 4604971 := bstep (se 1 (by rfl) ⟨3453728, by rfl⟩ : syracuseStep 4604971 = 6907457) B6907457
theorem B2729003 : Blo 1817610 2729003 := bstep (se 1 (by rfl) ⟨2046752, by rfl⟩ : syracuseStep 2729003 = 4093505) B4093505
theorem B6906941 : Blo 1817610 6906941 := bstep (se 3 (by rfl) ⟨1295051, by rfl⟩ : syracuseStep 6906941 = 2590103) B2590103
theorem B2729033 : Blo 1817610 2729033 := bstep (se 2 (by rfl) ⟨1023387, by rfl⟩ : syracuseStep 2729033 = 2046775) B2046775
theorem B4605113 : Blo 1817610 4605113 := bstep (se 2 (by rfl) ⟨1726917, by rfl⟩ : syracuseStep 4605113 = 3453835) B3453835
theorem B2729147 : Blo 1817610 2729147 := bstep (se 1 (by rfl) ⟨2046860, by rfl⟩ : syracuseStep 2729147 = 4093721) B4093721
theorem B2729207 : Blo 1817610 2729207 := bstep (se 1 (by rfl) ⟨2046905, by rfl⟩ : syracuseStep 2729207 = 4093811) B4093811
theorem B2073863 : Blo 1817610 2073863 := bstep (se 1 (by rfl) ⟨1555397, by rfl⟩ : syracuseStep 2073863 = 3110795) B3110795
theorem B2729231 : Blo 1817610 2729231 := bstep (se 1 (by rfl) ⟨2046923, by rfl⟩ : syracuseStep 2729231 = 4093847) B4093847
theorem B4916513 : Blo 1817610 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B2589995 : Blo 1817610 2589995 := bstep (se 1 (by rfl) ⟨1942496, by rfl⟩ : syracuseStep 2589995 = 3884993) B3884993
theorem B2729273 : Blo 1817610 2729273 := bstep (se 2 (by rfl) ⟨1023477, by rfl⟩ : syracuseStep 2729273 = 2046955) B2046955
theorem B10356083 : Blo 1817610 10356083 := bstep (se 1 (by rfl) ⟨7767062, by rfl⟩ : syracuseStep 10356083 = 15534125) B15534125
theorem B2729351 : Blo 1817610 2729351 := bstep (se 1 (by rfl) ⟨2047013, by rfl⟩ : syracuseStep 2729351 = 4094027) B4094027
theorem B2729387 : Blo 1817610 2729387 := bstep (se 1 (by rfl) ⟨2047040, by rfl⟩ : syracuseStep 2729387 = 4094081) B4094081
theorem B29509123 : Blo 1817610 29509123 := bstep (se 1 (by rfl) ⟨22131842, by rfl⟩ : syracuseStep 29509123 = 44263685) B44263685
theorem B1943047 : Blo 1817610 1943047 := bstep (se 1 (by rfl) ⟨1457285, by rfl⟩ : syracuseStep 1943047 = 2914571) B2914571
theorem B9209537 : Blo 1817610 9209537 := bstep (se 2 (by rfl) ⟨3453576, by rfl⟩ : syracuseStep 9209537 = 6907153) B6907153
theorem B6997819 : Blo 1817610 6997819 := bstep (se 1 (by rfl) ⟨5248364, by rfl⟩ : syracuseStep 6997819 = 10496729) B10496729
theorem B6137747 : Blo 1817610 6137747 := bstep (se 1 (by rfl) ⟨4603310, by rfl⟩ : syracuseStep 6137747 = 9206621) B9206621
theorem B4147385 : Blo 1817610 4147385 := bstep (se 2 (by rfl) ⟨1555269, by rfl⟩ : syracuseStep 4147385 = 3110539) B3110539
theorem B34081013 : Blo 1817610 34081013 := bstep (se 5 (by rfl) ⟨1597547, by rfl⟩ : syracuseStep 34081013 = 3195095) B3195095
theorem B4090247 : Blo 1817610 4090247 := bstep (se 1 (by rfl) ⟨3067685, by rfl⟩ : syracuseStep 4090247 = 6135371) B6135371
theorem B26225137 : Blo 1817610 26225137 := bstep (se 2 (by rfl) ⟨9834426, by rfl⟩ : syracuseStep 26225137 = 19668853) B19668853
theorem B8735255 : Blo 1817610 8735255 := bstep (se 1 (by rfl) ⟨6551441, by rfl⟩ : syracuseStep 8735255 = 13102883) B13102883
theorem B7768619 : Blo 1817610 7768619 := bstep (se 1 (by rfl) ⟨5826464, by rfl⟩ : syracuseStep 7768619 = 11652929) B11652929
theorem B4090427 : Blo 1817610 4090427 := bstep (se 1 (by rfl) ⟨3067820, by rfl⟩ : syracuseStep 4090427 = 6135641) B6135641
theorem B2525755 : Blo 1817610 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B3451511 : Blo 1817610 3451511 := bstep (se 1 (by rfl) ⟨2588633, by rfl⟩ : syracuseStep 3451511 = 5177267) B5177267
theorem B4090553 : Blo 1817610 4090553 := bstep (se 2 (by rfl) ⟨1533957, by rfl⟩ : syracuseStep 4090553 = 3067915) B3067915
theorem B9833197 : Blo 1817610 9833197 := bstep (se 3 (by rfl) ⟨1843724, by rfl⟩ : syracuseStep 9833197 = 3687449) B3687449
theorem B3451663 : Blo 1817610 3451663 := bstep (se 1 (by rfl) ⟨2588747, by rfl⟩ : syracuseStep 3451663 = 5177495) B5177495
theorem B10357541 : Blo 1817610 10357541 := bstep (se 4 (by rfl) ⟨971019, by rfl⟩ : syracuseStep 10357541 = 1942039) B1942039
theorem B19663667 : Blo 1817610 19663667 := bstep (se 1 (by rfl) ⟨14747750, by rfl⟩ : syracuseStep 19663667 = 29495501) B29495501
theorem B4918103 : Blo 1817610 4918103 := bstep (se 1 (by rfl) ⟨3688577, by rfl⟩ : syracuseStep 4918103 = 7377155) B7377155
theorem B9210833 : Blo 1817610 9210833 := bstep (se 2 (by rfl) ⟨3454062, by rfl⟩ : syracuseStep 9210833 = 6908125) B6908125
theorem B4090895 : Blo 1817610 4090895 := bstep (se 1 (by rfl) ⟨3068171, by rfl⟩ : syracuseStep 4090895 = 6136343) B6136343
theorem B11676695 : Blo 1817610 11676695 := bstep (se 1 (by rfl) ⟨8757521, by rfl⟩ : syracuseStep 11676695 = 17515043) B17515043
theorem B4090913 : Blo 1817610 4090913 := bstep (se 2 (by rfl) ⟨1534092, by rfl⟩ : syracuseStep 4090913 = 3068185) B3068185
theorem B3452051 : Blo 1817610 3452051 := bstep (se 1 (by rfl) ⟨2589038, by rfl⟩ : syracuseStep 3452051 = 5178077) B5178077
theorem B6139151 : Blo 1817610 6139151 := bstep (se 1 (by rfl) ⟨4604363, by rfl⟩ : syracuseStep 6139151 = 9208727) B9208727
theorem B11062565 : Blo 1817610 11062565 := bstep (se 4 (by rfl) ⟨1037115, by rfl⟩ : syracuseStep 11062565 = 2074231) B2074231
theorem B2911547 : Blo 1817610 2911547 := bstep (se 1 (by rfl) ⟨2183660, by rfl⟩ : syracuseStep 2911547 = 4367321) B4367321
theorem B4091255 : Blo 1817610 4091255 := bstep (se 1 (by rfl) ⟨3068441, by rfl⟩ : syracuseStep 4091255 = 6136883) B6136883
theorem B3067321 : Blo 1817610 3067321 := bstep (se 2 (by rfl) ⟨1150245, by rfl⟩ : syracuseStep 3067321 = 2300491) B2300491
theorem B10358225 : Blo 1817610 10358225 := bstep (se 2 (by rfl) ⟨3884334, by rfl⟩ : syracuseStep 10358225 = 7768669) B7768669
theorem B6139421 : Blo 1817610 6139421 := bstep (se 3 (by rfl) ⟨1151141, by rfl⟩ : syracuseStep 6139421 = 2302283) B2302283
theorem B14003741 : Blo 1817610 14003741 := bstep (se 3 (by rfl) ⟨2625701, by rfl⟩ : syracuseStep 14003741 = 5251403) B5251403
theorem B4091435 : Blo 1817610 4091435 := bstep (se 1 (by rfl) ⟨3068576, by rfl⟩ : syracuseStep 4091435 = 6137153) B6137153
theorem B7376471 : Blo 1817610 7376471 := bstep (se 1 (by rfl) ⟨5532353, by rfl⟩ : syracuseStep 7376471 = 11064707) B11064707
theorem B23613029 : Blo 1817610 23613029 := bstep (se 4 (by rfl) ⟨2213721, by rfl⟩ : syracuseStep 23613029 = 4427443) B4427443
theorem B2625211 : Blo 1817610 2625211 := bstep (se 1 (by rfl) ⟨1968908, by rfl⟩ : syracuseStep 2625211 = 3937817) B3937817
theorem B10104521 : Blo 1817610 10104521 := bstep (se 2 (by rfl) ⟨3789195, by rfl⟩ : syracuseStep 10104521 = 7578391) B7578391
theorem B2764535 : Blo 1817610 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B5181185 : Blo 1817610 5181185 := bstep (se 2 (by rfl) ⟨1942944, by rfl⟩ : syracuseStep 5181185 = 3885889) B3885889
theorem B4427531 : Blo 1817610 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B10358543 : Blo 1817610 10358543 := bstep (se 1 (by rfl) ⟨7768907, by rfl⟩ : syracuseStep 10358543 = 15537815) B15537815
theorem B2912059 : Blo 1817610 2912059 := bstep (se 1 (by rfl) ⟨2184044, by rfl⟩ : syracuseStep 2912059 = 4368089) B4368089
theorem B4091795 : Blo 1817610 4091795 := bstep (se 1 (by rfl) ⟨3068846, by rfl⟩ : syracuseStep 4091795 = 6137693) B6137693
theorem B4091849 : Blo 1817610 4091849 := bstep (se 2 (by rfl) ⟨1534443, by rfl⟩ : syracuseStep 4091849 = 3068887) B3068887
theorem B17485885 : Blo 1817610 17485885 := bstep (se 3 (by rfl) ⟨3278603, by rfl⟩ : syracuseStep 17485885 = 6557207) B6557207
theorem B3068023 : Blo 1817610 3068023 := bstep (se 1 (by rfl) ⟨2301017, by rfl⟩ : syracuseStep 3068023 = 4602035) B4602035
theorem B9834689 : Blo 1817610 9834689 := bstep (se 2 (by rfl) ⟨3688008, by rfl⟩ : syracuseStep 9834689 = 7376017) B7376017
theorem B5984545 : Blo 1817610 5984545 := bstep (se 2 (by rfl) ⟨2244204, by rfl⟩ : syracuseStep 5984545 = 4488409) B4488409
theorem B3068219 : Blo 1817610 3068219 := bstep (se 1 (by rfl) ⟨2301164, by rfl⟩ : syracuseStep 3068219 = 4602329) B4602329
theorem B3109321 : Blo 1817610 3109321 := bstep (se 2 (by rfl) ⟨1165995, by rfl⟩ : syracuseStep 3109321 = 2331991) B2331991
theorem B4665871 : Blo 1817610 4665871 := bstep (se 1 (by rfl) ⟨3499403, by rfl⟩ : syracuseStep 4665871 = 6998807) B6998807
theorem B3453455 : Blo 1817610 3453455 := bstep (se 1 (by rfl) ⟨2590091, by rfl⟩ : syracuseStep 3453455 = 5180183) B5180183
theorem B13103693 : Blo 1817610 13103693 := bstep (se 3 (by rfl) ⟨2456942, by rfl⟩ : syracuseStep 13103693 = 4913885) B4913885
theorem B4092551 : Blo 1817610 4092551 := bstep (se 1 (by rfl) ⟨3069413, by rfl⟩ : syracuseStep 4092551 = 6138827) B6138827
theorem B4371079 : Blo 1817610 4371079 := bstep (se 1 (by rfl) ⟨3278309, by rfl⟩ : syracuseStep 4371079 = 6556619) B6556619
theorem B3068617 : Blo 1817610 3068617 := bstep (se 2 (by rfl) ⟨1150731, by rfl⟩ : syracuseStep 3068617 = 2301463) B2301463
theorem B4092731 : Blo 1817610 4092731 := bstep (se 1 (by rfl) ⟨3069548, by rfl⟩ : syracuseStep 4092731 = 6139097) B6139097
theorem B15528793 : Blo 1817610 15528793 := bstep (se 2 (by rfl) ⟨5823297, by rfl⟩ : syracuseStep 15528793 = 11646595) B11646595
theorem B2184079 : Blo 1817610 2184079 := bstep (se 1 (by rfl) ⟨1638059, by rfl⟩ : syracuseStep 2184079 = 3276119) B3276119
theorem B6140825 : Blo 1817610 6140825 := bstep (se 2 (by rfl) ⟨2302809, by rfl⟩ : syracuseStep 6140825 = 4605619) B4605619
theorem B4092857 : Blo 1817610 4092857 := bstep (se 2 (by rfl) ⟨1534821, by rfl⟩ : syracuseStep 4092857 = 3069643) B3069643
theorem B3453995 : Blo 1817610 3453995 := bstep (se 1 (by rfl) ⟨2590496, by rfl⟩ : syracuseStep 3453995 = 5180993) B5180993
theorem B10360001 : Blo 1817610 10360001 := bstep (se 2 (by rfl) ⟨3885000, by rfl⟩ : syracuseStep 10360001 = 7770001) B7770001
theorem B4601033 : Blo 1817610 4601033 := bstep (se 2 (by rfl) ⟨1725387, by rfl⟩ : syracuseStep 4601033 = 3450775) B3450775
theorem B2045191 : Blo 1817610 2045191 := bstep (se 1 (by rfl) ⟨1533893, by rfl⟩ : syracuseStep 2045191 = 3067787) B3067787
theorem B4093199 : Blo 1817610 4093199 := bstep (se 1 (by rfl) ⟨3069899, by rfl⟩ : syracuseStep 4093199 = 6139799) B6139799
theorem B4093217 : Blo 1817610 4093217 := bstep (se 2 (by rfl) ⟨1534956, by rfl⟩ : syracuseStep 4093217 = 3069913) B3069913
theorem B10351961 : Blo 1817610 10351961 := bstep (se 2 (by rfl) ⟨3881985, by rfl⟩ : syracuseStep 10351961 = 7763971) B7763971
theorem B2184583 : Blo 1817610 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B3069319 : Blo 1817610 3069319 := bstep (se 1 (by rfl) ⟨2301989, by rfl⟩ : syracuseStep 3069319 = 4603979) B4603979
theorem B34952633 : Blo 1817610 34952633 := bstep (se 2 (by rfl) ⟨13107237, by rfl⟩ : syracuseStep 34952633 = 26214475) B26214475
theorem B36410809 : Blo 1817610 36410809 := bstep (se 2 (by rfl) ⟨13654053, by rfl⟩ : syracuseStep 36410809 = 27308107) B27308107
theorem B2045371 : Blo 1817610 2045371 := bstep (se 1 (by rfl) ⟨1534028, by rfl⟩ : syracuseStep 2045371 = 3068057) B3068057
theorem B4601387 : Blo 1817610 4601387 := bstep (se 1 (by rfl) ⟨3451040, by rfl⟩ : syracuseStep 4601387 = 6902081) B6902081
theorem B11064899 : Blo 1817610 11064899 := bstep (se 1 (by rfl) ⟨8298674, by rfl⟩ : syracuseStep 11064899 = 16597349) B16597349
theorem B4093559 : Blo 1817610 4093559 := bstep (se 1 (by rfl) ⟨3070169, by rfl⟩ : syracuseStep 4093559 = 6140339) B6140339
theorem B2184967 : Blo 1817610 2184967 := bstep (se 1 (by rfl) ⟨1638725, by rfl⟩ : syracuseStep 2184967 = 3277451) B3277451
theorem B4093739 : Blo 1817610 4093739 := bstep (se 1 (by rfl) ⟨3070304, by rfl⟩ : syracuseStep 4093739 = 6140609) B6140609
theorem B17487731 : Blo 1817610 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B2045839 : Blo 1817610 2045839 := bstep (se 1 (by rfl) ⟨1534379, by rfl⟩ : syracuseStep 2045839 = 3068759) B3068759
theorem B9205649 : Blo 1817610 9205649 := bstep (se 2 (by rfl) ⟨3452118, by rfl⟩ : syracuseStep 9205649 = 6904237) B6904237
theorem B7772051 : Blo 1817610 7772051 := bstep (se 1 (by rfl) ⟨5829038, by rfl⟩ : syracuseStep 7772051 = 11658077) B11658077
theorem B6903737 : Blo 1817610 6903737 := bstep (se 2 (by rfl) ⟨2588901, by rfl⟩ : syracuseStep 6903737 = 5177803) B5177803
theorem B3069967 : Blo 1817610 3069967 := bstep (se 1 (by rfl) ⟨2302475, by rfl⟩ : syracuseStep 3069967 = 4604951) B4604951
theorem B4094099 : Blo 1817610 4094099 := bstep (se 1 (by rfl) ⟨3070574, by rfl⟩ : syracuseStep 4094099 = 6141149) B6141149
theorem B9828545 : Blo 1817610 9828545 := bstep (se 2 (by rfl) ⟨3685704, by rfl⟩ : syracuseStep 9828545 = 7371409) B7371409
theorem B14940551 : Blo 1817610 14940551 := bstep (se 1 (by rfl) ⟨11205413, by rfl⟩ : syracuseStep 14940551 = 22410827) B22410827
theorem B2046343 : Blo 1817610 2046343 := bstep (se 1 (by rfl) ⟨1534757, by rfl⟩ : syracuseStep 2046343 = 3069515) B3069515
theorem B4602379 : Blo 1817610 4602379 := bstep (se 1 (by rfl) ⟨3451784, by rfl⟩ : syracuseStep 4602379 = 6903569) B6903569
theorem B2365967 : Blo 1817610 2365967 := bstep (se 1 (by rfl) ⟨1774475, by rfl⟩ : syracuseStep 2365967 = 3548951) B3548951
theorem B3070507 : Blo 1817610 3070507 := bstep (se 1 (by rfl) ⟨2302880, by rfl⟩ : syracuseStep 3070507 = 4605761) B4605761
theorem B2726459 : Blo 1817610 2726459 := bstep (se 1 (by rfl) ⟨2044844, by rfl⟩ : syracuseStep 2726459 = 4089689) B4089689
theorem B2046523 : Blo 1817610 2046523 := bstep (se 1 (by rfl) ⟨1534892, by rfl⟩ : syracuseStep 2046523 = 3069785) B3069785
theorem B8739389 : Blo 1817610 8739389 := bstep (se 3 (by rfl) ⟨1638635, by rfl⟩ : syracuseStep 8739389 = 3277271) B3277271
theorem B2726519 : Blo 1817610 2726519 := bstep (se 1 (by rfl) ⟨2044889, by rfl⟩ : syracuseStep 2726519 = 4089779) B4089779
theorem B2726543 : Blo 1817610 2726543 := bstep (se 1 (by rfl) ⟨2044907, by rfl⟩ : syracuseStep 2726543 = 4089815) B4089815
theorem B4602521 : Blo 1817610 4602521 := bstep (se 2 (by rfl) ⟨1725945, by rfl⟩ : syracuseStep 4602521 = 3451891) B3451891
theorem B2726585 : Blo 1817610 2726585 := bstep (se 2 (by rfl) ⟨1022469, by rfl⟩ : syracuseStep 2726585 = 2044939) B2044939
theorem B2300663 : Blo 1817610 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B2726663 : Blo 1817610 2726663 := bstep (se 1 (by rfl) ⟨2044997, by rfl⟩ : syracuseStep 2726663 = 4089995) B4089995
theorem B5823247 : Blo 1817610 5823247 := bstep (se 1 (by rfl) ⟨4367435, by rfl⟩ : syracuseStep 5823247 = 8734871) B8734871
theorem B6134561 : Blo 1817610 6134561 := bstep (se 2 (by rfl) ⟨2300460, by rfl⟩ : syracuseStep 6134561 = 4600921) B4600921
theorem B32373539 : Blo 1817610 32373539 := bstep (se 1 (by rfl) ⟨24280154, by rfl⟩ : syracuseStep 32373539 = 48560309) B48560309
theorem B2726699 : Blo 1817610 2726699 := bstep (se 1 (by rfl) ⟨2045024, by rfl⟩ : syracuseStep 2726699 = 4090049) B4090049
theorem B17718065 : Blo 1817610 17718065 := bstep (se 2 (by rfl) ⟨6644274, by rfl⟩ : syracuseStep 17718065 = 13288549) B13288549
theorem B4602683 : Blo 1817610 4602683 := bstep (se 1 (by rfl) ⟨3452012, by rfl⟩ : syracuseStep 4602683 = 6904025) B6904025
theorem B2726729 : Blo 1817610 2726729 := bstep (se 2 (by rfl) ⟨1022523, by rfl⟩ : syracuseStep 2726729 = 2045047) B2045047
theorem B2300815 : Blo 1817610 2300815 := bstep (se 1 (by rfl) ⟨1725611, by rfl⟩ : syracuseStep 2300815 = 3451223) B3451223
theorem B6904723 : Blo 1817610 6904723 := bstep (se 1 (by rfl) ⟨5178542, by rfl⟩ : syracuseStep 6904723 = 10357085) B10357085
theorem B2726843 : Blo 1817610 2726843 := bstep (se 1 (by rfl) ⟨2045132, by rfl⟩ : syracuseStep 2726843 = 4090265) B4090265
theorem B2726903 : Blo 1817610 2726903 := bstep (se 1 (by rfl) ⟨2045177, by rfl⟩ : syracuseStep 2726903 = 4090355) B4090355
theorem B26213381 : Blo 1817610 26213381 := bstep (se 4 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 26213381 = 4915009) B4915009
theorem B1817615 : Blo 1817610 1817615 := bstep (se 1 (by rfl) ⟨1363211, by rfl⟩ : syracuseStep 1817615 = 2726423) B2726423
theorem B2726927 : Blo 1817610 2726927 := bstep (se 1 (by rfl) ⟨2045195, by rfl⟩ : syracuseStep 2726927 = 4090391) B4090391
theorem B2046991 : Blo 1817610 2046991 := bstep (se 1 (by rfl) ⟨1535243, by rfl⟩ : syracuseStep 2046991 = 3070487) B3070487
theorem B2726969 : Blo 1817610 2726969 := bstep (se 2 (by rfl) ⟨1022613, by rfl⟩ : syracuseStep 2726969 = 2045227) B2045227
theorem B1817659 : Blo 1817610 1817659 := bstep (se 1 (by rfl) ⟨1363244, by rfl⟩ : syracuseStep 1817659 = 2726489) B2726489
theorem B5176379 : Blo 1817610 5176379 := bstep (se 1 (by rfl) ⟨3882284, by rfl⟩ : syracuseStep 5176379 = 7764569) B7764569
theorem B2300987 : Blo 1817610 2300987 := bstep (se 1 (by rfl) ⟨1725740, by rfl⟩ : syracuseStep 2300987 = 3451481) B3451481
theorem B1817735 : Blo 1817610 1817735 := bstep (se 1 (by rfl) ⟨1363301, by rfl⟩ : syracuseStep 1817735 = 2726603) B2726603
theorem B2727047 : Blo 1817610 2727047 := bstep (se 1 (by rfl) ⟨2045285, by rfl⟩ : syracuseStep 2727047 = 4090571) B4090571
theorem B1817743 : Blo 1817610 1817743 := bstep (se 1 (by rfl) ⟨1363307, by rfl⟩ : syracuseStep 1817743 = 2726615) B2726615
theorem B4603027 : Blo 1817610 4603027 := bstep (se 1 (by rfl) ⟨3452270, by rfl⟩ : syracuseStep 4603027 = 6904541) B6904541
theorem B2727083 : Blo 1817610 2727083 := bstep (se 1 (by rfl) ⟨2045312, by rfl⟩ : syracuseStep 2727083 = 4090625) B4090625
theorem B1817787 : Blo 1817610 1817787 := bstep (se 1 (by rfl) ⟨1363340, by rfl⟩ : syracuseStep 1817787 = 2726681) B2726681
theorem B2727113 : Blo 1817610 2727113 := bstep (se 2 (by rfl) ⟨1022667, by rfl⟩ : syracuseStep 2727113 = 2045335) B2045335
theorem B1817863 : Blo 1817610 1817863 := bstep (se 1 (by rfl) ⟨1363397, by rfl⟩ : syracuseStep 1817863 = 2726795) B2726795
theorem B1817871 : Blo 1817610 1817871 := bstep (se 1 (by rfl) ⟨1363403, by rfl⟩ : syracuseStep 1817871 = 2726807) B2726807
theorem B4603169 : Blo 1817610 4603169 := bstep (se 2 (by rfl) ⟨1726188, by rfl⟩ : syracuseStep 4603169 = 3452377) B3452377
theorem B5176619 : Blo 1817610 5176619 := bstep (se 1 (by rfl) ⟨3882464, by rfl⟩ : syracuseStep 5176619 = 7764929) B7764929
theorem B16809275 : Blo 1817610 16809275 := bstep (se 1 (by rfl) ⟨12606956, by rfl⟩ : syracuseStep 16809275 = 25213913) B25213913
theorem B1817915 : Blo 1817610 1817915 := bstep (se 1 (by rfl) ⟨1363436, by rfl⟩ : syracuseStep 1817915 = 2726873) B2726873
theorem B2727227 : Blo 1817610 2727227 := bstep (se 1 (by rfl) ⟨2045420, by rfl⟩ : syracuseStep 2727227 = 4090841) B4090841
theorem B52428131 : Blo 1817610 52428131 := bstep (se 1 (by rfl) ⟨39321098, by rfl⟩ : syracuseStep 52428131 = 78642197) B78642197
theorem B6135155 : Blo 1817610 6135155 := bstep (se 1 (by rfl) ⟨4601366, by rfl⟩ : syracuseStep 6135155 = 9202733) B9202733
theorem B2727287 : Blo 1817610 2727287 := bstep (se 1 (by rfl) ⟨2045465, by rfl⟩ : syracuseStep 2727287 = 4090931) B4090931
theorem B1817991 : Blo 1817610 1817991 := bstep (se 1 (by rfl) ⟨1363493, by rfl⟩ : syracuseStep 1817991 = 2726987) B2726987
theorem B1817999 : Blo 1817610 1817999 := bstep (se 1 (by rfl) ⟨1363499, by rfl⟩ : syracuseStep 1817999 = 2726999) B2726999
theorem B2727311 : Blo 1817610 2727311 := bstep (se 1 (by rfl) ⟨2045483, by rfl⟩ : syracuseStep 2727311 = 4090967) B4090967
theorem B11648441 : Blo 1817610 11648441 := bstep (se 2 (by rfl) ⟨4368165, by rfl⟩ : syracuseStep 11648441 = 8736331) B8736331
theorem B2727353 : Blo 1817610 2727353 := bstep (se 2 (by rfl) ⟨1022757, by rfl⟩ : syracuseStep 2727353 = 2045515) B2045515
theorem B1818043 : Blo 1817610 1818043 := bstep (se 1 (by rfl) ⟨1363532, by rfl⟩ : syracuseStep 1818043 = 2727065) B2727065
theorem B1818119 : Blo 1817610 1818119 := bstep (se 1 (by rfl) ⟨1363589, by rfl⟩ : syracuseStep 1818119 = 2727179) B2727179
theorem B2727431 : Blo 1817610 2727431 := bstep (se 1 (by rfl) ⟨2045573, by rfl⟩ : syracuseStep 2727431 = 4091147) B4091147
theorem B1818127 : Blo 1817610 1818127 := bstep (se 1 (by rfl) ⟨1363595, by rfl⟩ : syracuseStep 1818127 = 2727191) B2727191
theorem B2727467 : Blo 1817610 2727467 := bstep (se 1 (by rfl) ⟨2045600, by rfl⟩ : syracuseStep 2727467 = 4091201) B4091201
theorem B1818171 : Blo 1817610 1818171 := bstep (se 1 (by rfl) ⟨1363628, by rfl⟩ : syracuseStep 1818171 = 2727257) B2727257
theorem B2727497 : Blo 1817610 2727497 := bstep (se 2 (by rfl) ⟨1022811, by rfl⟩ : syracuseStep 2727497 = 2045623) B2045623
theorem B7872119 : Blo 1817610 7872119 := bstep (se 1 (by rfl) ⟨5904089, by rfl⟩ : syracuseStep 7872119 = 11808179) B11808179
theorem B1818247 : Blo 1817610 1818247 := bstep (se 1 (by rfl) ⟨1363685, by rfl⟩ : syracuseStep 1818247 = 2727371) B2727371
theorem B1818255 : Blo 1817610 1818255 := bstep (se 1 (by rfl) ⟨1363691, by rfl⟩ : syracuseStep 1818255 = 2727383) B2727383
theorem B1818299 : Blo 1817610 1818299 := bstep (se 1 (by rfl) ⟨1363724, by rfl⟩ : syracuseStep 1818299 = 2727449) B2727449
theorem B2727611 : Blo 1817610 2727611 := bstep (se 1 (by rfl) ⟨2045708, by rfl⟩ : syracuseStep 2727611 = 4091417) B4091417
theorem B2727671 : Blo 1817610 2727671 := bstep (se 1 (by rfl) ⟨2045753, by rfl⟩ : syracuseStep 2727671 = 4091507) B4091507
theorem B1818375 : Blo 1817610 1818375 := bstep (se 1 (by rfl) ⟨1363781, by rfl⟩ : syracuseStep 1818375 = 2727563) B2727563
theorem B3686159 : Blo 1817610 3686159 := bstep (se 1 (by rfl) ⟨2764619, by rfl⟩ : syracuseStep 3686159 = 5529239) B5529239
theorem B1818383 : Blo 1817610 1818383 := bstep (se 1 (by rfl) ⟨1363787, by rfl⟩ : syracuseStep 1818383 = 2727575) B2727575
theorem B2727695 : Blo 1817610 2727695 := bstep (se 1 (by rfl) ⟨2045771, by rfl⟩ : syracuseStep 2727695 = 4091543) B4091543
theorem B2727737 : Blo 1817610 2727737 := bstep (se 2 (by rfl) ⟨1022901, by rfl⟩ : syracuseStep 2727737 = 2045803) B2045803
theorem B1818427 : Blo 1817610 1818427 := bstep (se 1 (by rfl) ⟨1363820, by rfl⟩ : syracuseStep 1818427 = 2727641) B2727641
theorem B1818503 : Blo 1817610 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B2727815 : Blo 1817610 2727815 := bstep (se 1 (by rfl) ⟨2045861, by rfl⟩ : syracuseStep 2727815 = 4091723) B4091723
theorem B1818511 : Blo 1817610 1818511 := bstep (se 1 (by rfl) ⟨1363883, by rfl⟩ : syracuseStep 1818511 = 2727767) B2727767
theorem B2727851 : Blo 1817610 2727851 := bstep (se 1 (by rfl) ⟨2045888, by rfl⟩ : syracuseStep 2727851 = 4091777) B4091777
theorem B1818555 : Blo 1817610 1818555 := bstep (se 1 (by rfl) ⟨1363916, by rfl⟩ : syracuseStep 1818555 = 2727833) B2727833
theorem B2727881 : Blo 1817610 2727881 := bstep (se 2 (by rfl) ⟨1022955, by rfl⟩ : syracuseStep 2727881 = 2045911) B2045911
theorem B9207755 : Blo 1817610 9207755 := bstep (se 1 (by rfl) ⟨6905816, by rfl⟩ : syracuseStep 9207755 = 13811633) B13811633
theorem B7765969 : Blo 1817610 7765969 := bstep (se 2 (by rfl) ⟨2912238, by rfl⟩ : syracuseStep 7765969 = 5824477) B5824477
theorem B5603347 : Blo 1817610 5603347 := bstep (se 1 (by rfl) ⟨4202510, by rfl⟩ : syracuseStep 5603347 = 8405021) B8405021
theorem B1818663 : Blo 1817610 1818663 := bstep (se 1 (by rfl) ⟨1363997, by rfl⟩ : syracuseStep 1818663 = 2727995) B2727995
theorem B10362917 : Blo 1817610 10362917 := bstep (se 4 (by rfl) ⟨971523, by rfl⟩ : syracuseStep 10362917 = 1943047) B1943047
theorem B31137853 : Blo 1817610 31137853 := bstep (se 3 (by rfl) ⟨5838347, by rfl⟩ : syracuseStep 31137853 = 11676695) B11676695
theorem B3883087 : Blo 1817610 3883087 := bstep (se 1 (by rfl) ⟨2912315, by rfl⟩ : syracuseStep 3883087 = 5824631) B5824631
theorem B1818703 : Blo 1817610 1818703 := bstep (se 1 (by rfl) ⟨1364027, by rfl⟩ : syracuseStep 1818703 = 2728055) B2728055
theorem B1818719 : Blo 1817610 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B1818747 : Blo 1817610 1818747 := bstep (se 1 (by rfl) ⟨1364060, by rfl⟩ : syracuseStep 1818747 = 2728121) B2728121
theorem B6135965 : Blo 1817610 6135965 := bstep (se 3 (by rfl) ⟨1150493, by rfl⟩ : syracuseStep 6135965 = 2300987) B2300987
theorem B1818799 : Blo 1817610 1818799 := bstep (se 1 (by rfl) ⟨1364099, by rfl⟩ : syracuseStep 1818799 = 2728199) B2728199
theorem B1818823 : Blo 1817610 1818823 := bstep (se 1 (by rfl) ⟨1364117, by rfl⟩ : syracuseStep 1818823 = 2728235) B2728235
theorem B1818843 : Blo 1817610 1818843 := bstep (se 1 (by rfl) ⟨1364132, by rfl⟩ : syracuseStep 1818843 = 2728265) B2728265
theorem B1818919 : Blo 1817610 1818919 := bstep (se 1 (by rfl) ⟨1364189, by rfl⟩ : syracuseStep 1818919 = 2728379) B2728379
theorem B28008773 : Blo 1817610 28008773 := bstep (se 4 (by rfl) ⟨2625822, by rfl⟩ : syracuseStep 28008773 = 5251645) B5251645
theorem B1818959 : Blo 1817610 1818959 := bstep (se 1 (by rfl) ⟨1364219, by rfl⟩ : syracuseStep 1818959 = 2728439) B2728439
theorem B1818975 : Blo 1817610 1818975 := bstep (se 1 (by rfl) ⟨1364231, by rfl⟩ : syracuseStep 1818975 = 2728463) B2728463
theorem B1819003 : Blo 1817610 1819003 := bstep (se 1 (by rfl) ⟨1364252, by rfl⟩ : syracuseStep 1819003 = 2728505) B2728505
theorem B7979393 : Blo 1817610 7979393 := bstep (se 2 (by rfl) ⟨2992272, by rfl⟩ : syracuseStep 7979393 = 5984545) B5984545
theorem B4604303 : Blo 1817610 4604303 := bstep (se 1 (by rfl) ⟨3453227, by rfl⟩ : syracuseStep 4604303 = 6906455) B6906455
theorem B2728367 : Blo 1817610 2728367 := bstep (se 1 (by rfl) ⟨2046275, by rfl⟩ : syracuseStep 2728367 = 4092551) B4092551
theorem B1819055 : Blo 1817610 1819055 := bstep (se 1 (by rfl) ⟨1364291, by rfl⟩ : syracuseStep 1819055 = 2728583) B2728583
theorem B1819079 : Blo 1817610 1819079 := bstep (se 1 (by rfl) ⟨1364309, by rfl⟩ : syracuseStep 1819079 = 2728619) B2728619
theorem B1819099 : Blo 1817610 1819099 := bstep (se 1 (by rfl) ⟨1364324, by rfl⟩ : syracuseStep 1819099 = 2728649) B2728649
theorem B2728457 : Blo 1817610 2728457 := bstep (se 2 (by rfl) ⟨1023171, by rfl⟩ : syracuseStep 2728457 = 2046343) B2046343
theorem B3277351 : Blo 1817610 3277351 := bstep (se 1 (by rfl) ⟨2458013, by rfl⟩ : syracuseStep 3277351 = 4916027) B4916027
theorem B2728487 : Blo 1817610 2728487 := bstep (se 1 (by rfl) ⟨2046365, by rfl⟩ : syracuseStep 2728487 = 4092731) B4092731
theorem B1819175 : Blo 1817610 1819175 := bstep (se 1 (by rfl) ⟨1364381, by rfl⟩ : syracuseStep 1819175 = 2728763) B2728763
theorem B1819215 : Blo 1817610 1819215 := bstep (se 1 (by rfl) ⟨1364411, by rfl⟩ : syracuseStep 1819215 = 2728823) B2728823
theorem B1819231 : Blo 1817610 1819231 := bstep (se 1 (by rfl) ⟨1364423, by rfl⟩ : syracuseStep 1819231 = 2728847) B2728847
theorem B4145761 : Blo 1817610 4145761 := bstep (se 2 (by rfl) ⟨1554660, by rfl⟩ : syracuseStep 4145761 = 3109321) B3109321
theorem B6554209 : Blo 1817610 6554209 := bstep (se 2 (by rfl) ⟨2457828, by rfl⟩ : syracuseStep 6554209 = 4915657) B4915657
theorem B2728571 : Blo 1817610 2728571 := bstep (se 1 (by rfl) ⟨2046428, by rfl⟩ : syracuseStep 2728571 = 4092857) B4092857
theorem B1819259 : Blo 1817610 1819259 := bstep (se 1 (by rfl) ⟨1364444, by rfl⟩ : syracuseStep 1819259 = 2728889) B2728889
theorem B1819311 : Blo 1817610 1819311 := bstep (se 1 (by rfl) ⟨1364483, by rfl⟩ : syracuseStep 1819311 = 2728967) B2728967
theorem B6136505 : Blo 1817610 6136505 := bstep (se 2 (by rfl) ⟨2301189, by rfl⟩ : syracuseStep 6136505 = 4602379) B4602379
theorem B5530301 : Blo 1817610 5530301 := bstep (se 3 (by rfl) ⟨1036931, by rfl⟩ : syracuseStep 5530301 = 2073863) B2073863
theorem B1819335 : Blo 1817610 1819335 := bstep (se 1 (by rfl) ⟨1364501, by rfl⟩ : syracuseStep 1819335 = 2729003) B2729003
theorem B2302663 : Blo 1817610 2302663 := bstep (se 1 (by rfl) ⟨1726997, by rfl⟩ : syracuseStep 2302663 = 3453995) B3453995
theorem B4604627 : Blo 1817610 4604627 := bstep (se 1 (by rfl) ⟨3453470, by rfl⟩ : syracuseStep 4604627 = 6906941) B6906941
theorem B1819355 : Blo 1817610 1819355 := bstep (se 1 (by rfl) ⟨1364516, by rfl⟩ : syracuseStep 1819355 = 2729033) B2729033
theorem B4915961 : Blo 1817610 4915961 := bstep (se 2 (by rfl) ⟨1843485, by rfl⟩ : syracuseStep 4915961 = 3686971) B3686971
theorem B3367673 : Blo 1817610 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B2728697 : Blo 1817610 2728697 := bstep (se 2 (by rfl) ⟨1023261, by rfl⟩ : syracuseStep 2728697 = 2046523) B2046523
theorem B6906653 : Blo 1817610 6906653 := bstep (se 3 (by rfl) ⟨1294997, by rfl⟩ : syracuseStep 6906653 = 2589995) B2589995
theorem B1819431 : Blo 1817610 1819431 := bstep (se 1 (by rfl) ⟨1364573, by rfl⟩ : syracuseStep 1819431 = 2729147) B2729147
theorem B6906667 : Blo 1817610 6906667 := bstep (se 1 (by rfl) ⟨5180000, by rfl⟩ : syracuseStep 6906667 = 10360001) B10360001
theorem B7766857 : Blo 1817610 7766857 := bstep (se 2 (by rfl) ⟨2912571, by rfl⟩ : syracuseStep 7766857 = 5825143) B5825143
theorem B1819471 : Blo 1817610 1819471 := bstep (se 1 (by rfl) ⟨1364603, by rfl⟩ : syracuseStep 1819471 = 2729207) B2729207
theorem B2728799 : Blo 1817610 2728799 := bstep (se 1 (by rfl) ⟨2046599, by rfl⟩ : syracuseStep 2728799 = 4093199) B4093199
theorem B1819487 : Blo 1817610 1819487 := bstep (se 1 (by rfl) ⟨1364615, by rfl⟩ : syracuseStep 1819487 = 2729231) B2729231
theorem B3277675 : Blo 1817610 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B2728811 : Blo 1817610 2728811 := bstep (se 1 (by rfl) ⟨2046608, by rfl⟩ : syracuseStep 2728811 = 4093217) B4093217
theorem B1819515 : Blo 1817610 1819515 := bstep (se 1 (by rfl) ⟨1364636, by rfl⟩ : syracuseStep 1819515 = 2729273) B2729273
theorem B1819567 : Blo 1817610 1819567 := bstep (se 1 (by rfl) ⟨1364675, by rfl⟩ : syracuseStep 1819567 = 2729351) B2729351
theorem B1819591 : Blo 1817610 1819591 := bstep (se 1 (by rfl) ⟨1364693, by rfl⟩ : syracuseStep 1819591 = 2729387) B2729387
theorem B2729039 : Blo 1817610 2729039 := bstep (se 1 (by rfl) ⟨2046779, by rfl⟩ : syracuseStep 2729039 = 4093559) B4093559
theorem B2729159 : Blo 1817610 2729159 := bstep (se 1 (by rfl) ⟨2046869, by rfl⟩ : syracuseStep 2729159 = 4093739) B4093739
theorem B11658487 : Blo 1817610 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B6137099 : Blo 1817610 6137099 := bstep (se 1 (by rfl) ⟨4602824, by rfl⟩ : syracuseStep 6137099 = 9205649) B9205649
theorem B2729321 : Blo 1817610 2729321 := bstep (se 2 (by rfl) ⟨1023495, by rfl⟩ : syracuseStep 2729321 = 2046991) B2046991
theorem B6555005 : Blo 1817610 6555005 := bstep (se 3 (by rfl) ⟨1229063, by rfl⟩ : syracuseStep 6555005 = 2458127) B2458127
theorem B9209213 : Blo 1817610 9209213 := bstep (se 3 (by rfl) ⟨1726727, by rfl⟩ : syracuseStep 9209213 = 3453455) B3453455
theorem B6309245 : Blo 1817610 6309245 := bstep (se 3 (by rfl) ⟨1182983, by rfl⟩ : syracuseStep 6309245 = 2365967) B2365967
theorem B2729399 : Blo 1817610 2729399 := bstep (se 1 (by rfl) ⟨2047049, by rfl⟩ : syracuseStep 2729399 = 4094099) B4094099
theorem B6137369 : Blo 1817610 6137369 := bstep (se 2 (by rfl) ⟨2301513, by rfl⟩ : syracuseStep 6137369 = 4603027) B4603027
theorem B5179079 : Blo 1817610 5179079 := bstep (se 1 (by rfl) ⟨3884309, by rfl⟩ : syracuseStep 5179079 = 7768619) B7768619
theorem B5826259 : Blo 1817610 5826259 := bstep (se 1 (by rfl) ⟨4369694, by rfl⟩ : syracuseStep 5826259 = 8739389) B8739389
theorem B4089707 : Blo 1817610 4089707 := bstep (se 1 (by rfl) ⟨3067280, by rfl⟩ : syracuseStep 4089707 = 6134561) B6134561
theorem B26945389 : Blo 1817610 26945389 := bstep (se 3 (by rfl) ⟨5052260, by rfl⟩ : syracuseStep 26945389 = 10104521) B10104521
theorem B13109111 : Blo 1817610 13109111 := bstep (se 1 (by rfl) ⟨9831833, by rfl⟩ : syracuseStep 13109111 = 19663667) B19663667
theorem B3278735 : Blo 1817610 3278735 := bstep (se 1 (by rfl) ⟨2459051, by rfl⟩ : syracuseStep 3278735 = 4918103) B4918103
theorem B4089761 : Blo 1817610 4089761 := bstep (se 2 (by rfl) ⟨1533660, by rfl⟩ : syracuseStep 4089761 = 3067321) B3067321
theorem B48547745 : Blo 1817610 48547745 := bstep (se 2 (by rfl) ⟨18205404, by rfl⟩ : syracuseStep 48547745 = 36410809) B36410809
theorem B44238773 : Blo 1817610 44238773 := bstep (se 5 (by rfl) ⟨2073692, by rfl⟩ : syracuseStep 44238773 = 4147385) B4147385
theorem B17475587 : Blo 1817610 17475587 := bstep (se 1 (by rfl) ⟨13106690, by rfl⟩ : syracuseStep 17475587 = 26213381) B26213381
theorem B3450919 : Blo 1817610 3450919 := bstep (se 1 (by rfl) ⟨2588189, by rfl⟩ : syracuseStep 3450919 = 5176379) B5176379
theorem B7375043 : Blo 1817610 7375043 := bstep (se 1 (by rfl) ⟨5531282, by rfl⟩ : syracuseStep 7375043 = 11062565) B11062565
theorem B3451079 : Blo 1817610 3451079 := bstep (se 1 (by rfl) ⟨2588309, by rfl⟩ : syracuseStep 3451079 = 5176619) B5176619
theorem B4090103 : Blo 1817610 4090103 := bstep (se 1 (by rfl) ⟨3067577, by rfl⟩ : syracuseStep 4090103 = 6135155) B6135155
theorem B3500281 : Blo 1817610 3500281 := bstep (se 2 (by rfl) ⟨1312605, by rfl⟩ : syracuseStep 3500281 = 2625211) B2625211
theorem B4917647 : Blo 1817610 4917647 := bstep (se 1 (by rfl) ⟨3688235, by rfl⟩ : syracuseStep 4917647 = 7376471) B7376471
theorem B2951687 : Blo 1817610 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B6138503 : Blo 1817610 6138503 := bstep (se 1 (by rfl) ⟨4603877, by rfl⟩ : syracuseStep 6138503 = 9207755) B9207755
theorem B6138557 : Blo 1817610 6138557 := bstep (se 3 (by rfl) ⟨1150979, by rfl⟩ : syracuseStep 6138557 = 2301959) B2301959
theorem B31501001 : Blo 1817610 31501001 := bstep (se 2 (by rfl) ⟨11812875, by rfl⟩ : syracuseStep 31501001 = 23625751) B23625751
theorem B6556459 : Blo 1817610 6556459 := bstep (se 1 (by rfl) ⟨4917344, by rfl⟩ : syracuseStep 6556459 = 9834689) B9834689
theorem B4090697 : Blo 1817610 4090697 := bstep (se 2 (by rfl) ⟨1534011, by rfl⟩ : syracuseStep 4090697 = 3068023) B3068023
theorem B6138719 : Blo 1817610 6138719 := bstep (se 1 (by rfl) ⟨4604039, by rfl⟩ : syracuseStep 6138719 = 9208079) B9208079
theorem B6482807 : Blo 1817610 6482807 := bstep (se 1 (by rfl) ⟨4862105, by rfl⟩ : syracuseStep 6482807 = 9724211) B9724211
theorem B6138881 : Blo 1817610 6138881 := bstep (se 2 (by rfl) ⟨2302080, by rfl⟩ : syracuseStep 6138881 = 4604161) B4604161
theorem B8735795 : Blo 1817610 8735795 := bstep (se 1 (by rfl) ⟨6551846, by rfl⟩ : syracuseStep 8735795 = 13103693) B13103693
theorem B26209453 : Blo 1817610 26209453 := bstep (se 3 (by rfl) ⟨4914272, by rfl⟩ : syracuseStep 26209453 = 9828545) B9828545
theorem B34966849 : Blo 1817610 34966849 := bstep (se 2 (by rfl) ⟨13112568, by rfl⟩ : syracuseStep 34966849 = 26225137) B26225137
theorem B3452233 : Blo 1817610 3452233 := bstep (se 2 (by rfl) ⟨1294587, by rfl⟩ : syracuseStep 3452233 = 2589175) B2589175
theorem B6221161 : Blo 1817610 6221161 := bstep (se 2 (by rfl) ⟨2332935, by rfl⟩ : syracuseStep 6221161 = 4665871) B4665871
theorem B3067355 : Blo 1817610 3067355 := bstep (se 1 (by rfl) ⟨2300516, by rfl⟩ : syracuseStep 3067355 = 4601033) B4601033
theorem B5828105 : Blo 1817610 5828105 := bstep (se 2 (by rfl) ⟨2185539, by rfl⟩ : syracuseStep 5828105 = 4371079) B4371079
theorem B6901307 : Blo 1817610 6901307 := bstep (se 1 (by rfl) ⟨5175980, by rfl⟩ : syracuseStep 6901307 = 10351961) B10351961
theorem B4091489 : Blo 1817610 4091489 := bstep (se 2 (by rfl) ⟨1534308, by rfl⟩ : syracuseStep 4091489 = 3068617) B3068617
theorem B23301755 : Blo 1817610 23301755 := bstep (se 1 (by rfl) ⟨17476316, by rfl⟩ : syracuseStep 23301755 = 34952633) B34952633
theorem B13110929 : Blo 1817610 13110929 := bstep (se 2 (by rfl) ⟨4916598, by rfl⟩ : syracuseStep 13110929 = 9833197) B9833197
theorem B39841469 : Blo 1817610 39841469 := bstep (se 3 (by rfl) ⟨7470275, by rfl⟩ : syracuseStep 39841469 = 14940551) B14940551
theorem B3067591 : Blo 1817610 3067591 := bstep (se 1 (by rfl) ⟨2300693, by rfl⟩ : syracuseStep 3067591 = 4601387) B4601387
theorem B7376599 : Blo 1817610 7376599 := bstep (se 1 (by rfl) ⟨5532449, by rfl⟩ : syracuseStep 7376599 = 11064899) B11064899
theorem B20705057 : Blo 1817610 20705057 := bstep (se 2 (by rfl) ⟨7764396, by rfl⟩ : syracuseStep 20705057 = 15528793) B15528793
theorem B6139691 : Blo 1817610 6139691 := bstep (se 1 (by rfl) ⟨4604768, by rfl⟩ : syracuseStep 6139691 = 9209537) B9209537
theorem B3067753 : Blo 1817610 3067753 := bstep (se 2 (by rfl) ⟨1150407, by rfl⟩ : syracuseStep 3067753 = 2300815) B2300815
theorem B2912105 : Blo 1817610 2912105 := bstep (se 2 (by rfl) ⟨1092039, by rfl⟩ : syracuseStep 2912105 = 2184079) B2184079
theorem B4091831 : Blo 1817610 4091831 := bstep (se 1 (by rfl) ⟨3068873, by rfl⟩ : syracuseStep 4091831 = 6137747) B6137747
theorem B6139961 : Blo 1817610 6139961 := bstep (se 2 (by rfl) ⟨2302485, by rfl⟩ : syracuseStep 6139961 = 4604971) B4604971
theorem B23310413 : Blo 1817610 23310413 := bstep (se 3 (by rfl) ⟨4370702, by rfl⟩ : syracuseStep 23310413 = 8741405) B8741405
theorem B22720675 : Blo 1817610 22720675 := bstep (se 1 (by rfl) ⟨17040506, by rfl⟩ : syracuseStep 22720675 = 34081013) B34081013
theorem B9204029 : Blo 1817610 9204029 := bstep (se 3 (by rfl) ⟨1725755, by rfl⟩ : syracuseStep 9204029 = 3451511) B3451511
theorem B6140285 : Blo 1817610 6140285 := bstep (se 3 (by rfl) ⟨1151303, by rfl⟩ : syracuseStep 6140285 = 2302607) B2302607
theorem B3068347 : Blo 1817610 3068347 := bstep (se 1 (by rfl) ⟨2301260, by rfl⟩ : syracuseStep 3068347 = 4602521) B4602521
theorem B2912777 : Blo 1817610 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B4092425 : Blo 1817610 4092425 := bstep (se 2 (by rfl) ⟨1534659, by rfl⟩ : syracuseStep 4092425 = 3069319) B3069319
theorem B21582359 : Blo 1817610 21582359 := bstep (se 1 (by rfl) ⟨16186769, by rfl⟩ : syracuseStep 21582359 = 32373539) B32373539
theorem B3068455 : Blo 1817610 3068455 := bstep (se 1 (by rfl) ⟨2301341, by rfl⟩ : syracuseStep 3068455 = 4602683) B4602683
theorem B6140555 : Blo 1817610 6140555 := bstep (se 1 (by rfl) ⟨4605416, by rfl⟩ : syracuseStep 6140555 = 9210833) B9210833
theorem B13816493 : Blo 1817610 13816493 := bstep (se 3 (by rfl) ⟨2590592, by rfl⟩ : syracuseStep 13816493 = 5181185) B5181185
theorem B4092767 : Blo 1817610 4092767 := bstep (se 1 (by rfl) ⟨3069575, by rfl⟩ : syracuseStep 4092767 = 6139151) B6139151
theorem B3068779 : Blo 1817610 3068779 := bstep (se 1 (by rfl) ⟨2301584, by rfl⟩ : syracuseStep 3068779 = 4603169) B4603169
theorem B34952087 : Blo 1817610 34952087 := bstep (se 1 (by rfl) ⟨26214065, by rfl⟩ : syracuseStep 34952087 = 52428131) B52428131
theorem B2913289 : Blo 1817610 2913289 := bstep (se 2 (by rfl) ⟨1092483, by rfl⟩ : syracuseStep 2913289 = 2184967) B2184967
theorem B4092947 : Blo 1817610 4092947 := bstep (se 1 (by rfl) ⟨3069710, by rfl⟩ : syracuseStep 4092947 = 6139421) B6139421
theorem B9335827 : Blo 1817610 9335827 := bstep (se 1 (by rfl) ⟨7001870, by rfl⟩ : syracuseStep 9335827 = 14003741) B14003741
theorem B15742019 : Blo 1817610 15742019 := bstep (se 1 (by rfl) ⟨11806514, by rfl⟩ : syracuseStep 15742019 = 23613029) B23613029
theorem B5248079 : Blo 1817610 5248079 := bstep (se 1 (by rfl) ⟨3936059, by rfl⟩ : syracuseStep 5248079 = 7872119) B7872119
theorem B4093289 : Blo 1817610 4093289 := bstep (se 2 (by rfl) ⟨1534983, by rfl⟩ : syracuseStep 4093289 = 3069967) B3069967
theorem B2045479 : Blo 1817610 2045479 := bstep (se 1 (by rfl) ⟨1534109, by rfl⟩ : syracuseStep 2045479 = 3068219) B3068219
theorem B13293179 : Blo 1817610 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B17471123 : Blo 1817610 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B49747607 : Blo 1817610 49747607 := bstep (se 1 (by rfl) ⟨37310705, by rfl⟩ : syracuseStep 49747607 = 74621411) B74621411
theorem B3069839 : Blo 1817610 3069839 := bstep (se 1 (by rfl) ⟨2302379, by rfl⟩ : syracuseStep 3069839 = 4604759) B4604759
theorem B4093883 : Blo 1817610 4093883 := bstep (se 1 (by rfl) ⟨3070412, by rfl⟩ : syracuseStep 4093883 = 6140825) B6140825
theorem B4094009 : Blo 1817610 4094009 := bstep (se 2 (by rfl) ⟨1535253, by rfl⟩ : syracuseStep 4094009 = 3070507) B3070507
theorem B3070075 : Blo 1817610 3070075 := bstep (se 1 (by rfl) ⟨2302556, by rfl⟩ : syracuseStep 3070075 = 4605113) B4605113
theorem B6904055 : Blo 1817610 6904055 := bstep (se 1 (by rfl) ⟨5178041, by rfl⟩ : syracuseStep 6904055 = 10356083) B10356083
theorem B7764329 : Blo 1817610 7764329 := bstep (se 2 (by rfl) ⟨2911623, by rfl⟩ : syracuseStep 7764329 = 5823247) B5823247
theorem B4602217 : Blo 1817610 4602217 := bstep (se 2 (by rfl) ⟨1725831, by rfl⟩ : syracuseStep 4602217 = 3451663) B3451663
theorem B9206297 : Blo 1817610 9206297 := bstep (se 2 (by rfl) ⟨3452361, by rfl⟩ : syracuseStep 9206297 = 6904723) B6904723
theorem B4602491 : Blo 1817610 4602491 := bstep (se 1 (by rfl) ⟨3451868, by rfl⟩ : syracuseStep 4602491 = 6903737) B6903737
theorem B2726831 : Blo 1817610 2726831 := bstep (se 1 (by rfl) ⟨2045123, by rfl⟩ : syracuseStep 2726831 = 4090247) B4090247
theorem B13810661 : Blo 1817610 13810661 := bstep (se 4 (by rfl) ⟨1294749, by rfl⟩ : syracuseStep 13810661 = 2589499) B2589499
theorem B2726921 : Blo 1817610 2726921 := bstep (se 2 (by rfl) ⟨1022595, by rfl⟩ : syracuseStep 2726921 = 2045191) B2045191
theorem B5823503 : Blo 1817610 5823503 := bstep (se 1 (by rfl) ⟨4367627, by rfl⟩ : syracuseStep 5823503 = 8735255) B8735255
theorem B1817639 : Blo 1817610 1817639 := bstep (se 1 (by rfl) ⟨1363229, by rfl⟩ : syracuseStep 1817639 = 2726459) B2726459
theorem B2726951 : Blo 1817610 2726951 := bstep (se 1 (by rfl) ⟨2045213, by rfl⟩ : syracuseStep 2726951 = 4090427) B4090427
theorem B1817679 : Blo 1817610 1817679 := bstep (se 1 (by rfl) ⟨1363259, by rfl⟩ : syracuseStep 1817679 = 2726519) B2726519
theorem B1817695 : Blo 1817610 1817695 := bstep (se 1 (by rfl) ⟨1363271, by rfl⟩ : syracuseStep 1817695 = 2726543) B2726543
theorem B1817723 : Blo 1817610 1817723 := bstep (se 1 (by rfl) ⟨1363292, by rfl⟩ : syracuseStep 1817723 = 2726585) B2726585
theorem B2727035 : Blo 1817610 2727035 := bstep (se 1 (by rfl) ⟨2045276, by rfl⟩ : syracuseStep 2727035 = 4090553) B4090553
theorem B1817775 : Blo 1817610 1817775 := bstep (se 1 (by rfl) ⟨1363331, by rfl⟩ : syracuseStep 1817775 = 2726663) B2726663
theorem B6905027 : Blo 1817610 6905027 := bstep (se 1 (by rfl) ⟨5178770, by rfl⟩ : syracuseStep 6905027 = 10357541) B10357541
theorem B1817799 : Blo 1817610 1817799 := bstep (se 1 (by rfl) ⟨1363349, by rfl⟩ : syracuseStep 1817799 = 2726699) B2726699
theorem B11812043 : Blo 1817610 11812043 := bstep (se 1 (by rfl) ⟨8859032, by rfl⟩ : syracuseStep 11812043 = 17718065) B17718065
theorem B1817819 : Blo 1817610 1817819 := bstep (se 1 (by rfl) ⟨1363364, by rfl⟩ : syracuseStep 1817819 = 2726729) B2726729
theorem B2727161 : Blo 1817610 2727161 := bstep (se 2 (by rfl) ⟨1022685, by rfl⟩ : syracuseStep 2727161 = 2045371) B2045371
theorem B1817895 : Blo 1817610 1817895 := bstep (se 1 (by rfl) ⟨1363421, by rfl⟩ : syracuseStep 1817895 = 2726843) B2726843
theorem B6135101 : Blo 1817610 6135101 := bstep (se 3 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 6135101 = 2300663) B2300663
theorem B7372093 : Blo 1817610 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B1817935 : Blo 1817610 1817935 := bstep (se 1 (by rfl) ⟨1363451, by rfl⟩ : syracuseStep 1817935 = 2726903) B2726903
theorem B39345497 : Blo 1817610 39345497 := bstep (se 2 (by rfl) ⟨14754561, by rfl⟩ : syracuseStep 39345497 = 29509123) B29509123
theorem B1817951 : Blo 1817610 1817951 := bstep (se 1 (by rfl) ⟨1363463, by rfl⟩ : syracuseStep 1817951 = 2726927) B2726927
theorem B2727263 : Blo 1817610 2727263 := bstep (se 1 (by rfl) ⟨2045447, by rfl⟩ : syracuseStep 2727263 = 4090895) B4090895
theorem B2727275 : Blo 1817610 2727275 := bstep (se 1 (by rfl) ⟨2045456, by rfl⟩ : syracuseStep 2727275 = 4090913) B4090913
theorem B1817979 : Blo 1817610 1817979 := bstep (se 1 (by rfl) ⟨1363484, by rfl⟩ : syracuseStep 1817979 = 2726969) B2726969
theorem B9829757 : Blo 1817610 9829757 := bstep (se 3 (by rfl) ⟨1843079, by rfl⟩ : syracuseStep 9829757 = 3686159) B3686159
theorem B1818031 : Blo 1817610 1818031 := bstep (se 1 (by rfl) ⟨1363523, by rfl⟩ : syracuseStep 1818031 = 2727047) B2727047
theorem B2301367 : Blo 1817610 2301367 := bstep (se 1 (by rfl) ⟨1726025, by rfl⟩ : syracuseStep 2301367 = 3452051) B3452051
theorem B1818055 : Blo 1817610 1818055 := bstep (se 1 (by rfl) ⟨1363541, by rfl⟩ : syracuseStep 1818055 = 2727083) B2727083
theorem B1818075 : Blo 1817610 1818075 := bstep (se 1 (by rfl) ⟨1363556, by rfl⟩ : syracuseStep 1818075 = 2727113) B2727113
theorem B1941031 : Blo 1817610 1941031 := bstep (se 1 (by rfl) ⟨1455773, by rfl⟩ : syracuseStep 1941031 = 2911547) B2911547
theorem B11206183 : Blo 1817610 11206183 := bstep (se 1 (by rfl) ⟨8404637, by rfl⟩ : syracuseStep 11206183 = 16809275) B16809275
theorem B1818151 : Blo 1817610 1818151 := bstep (se 1 (by rfl) ⟨1363613, by rfl⟩ : syracuseStep 1818151 = 2727227) B2727227
theorem B1818191 : Blo 1817610 1818191 := bstep (se 1 (by rfl) ⟨1363643, by rfl⟩ : syracuseStep 1818191 = 2727287) B2727287
theorem B2727503 : Blo 1817610 2727503 := bstep (se 1 (by rfl) ⟨2045627, by rfl⟩ : syracuseStep 2727503 = 4091255) B4091255
theorem B1818207 : Blo 1817610 1818207 := bstep (se 1 (by rfl) ⟨1363655, by rfl⟩ : syracuseStep 1818207 = 2727311) B2727311
theorem B7765627 : Blo 1817610 7765627 := bstep (se 1 (by rfl) ⟨5824220, by rfl⟩ : syracuseStep 7765627 = 11648441) B11648441
theorem B1818235 : Blo 1817610 1818235 := bstep (se 1 (by rfl) ⟨1363676, by rfl⟩ : syracuseStep 1818235 = 2727353) B2727353
theorem B6905483 : Blo 1817610 6905483 := bstep (se 1 (by rfl) ⟨5179112, by rfl⟩ : syracuseStep 6905483 = 10358225) B10358225
theorem B1818287 : Blo 1817610 1818287 := bstep (se 1 (by rfl) ⟨1363715, by rfl⟩ : syracuseStep 1818287 = 2727431) B2727431
theorem B1818311 : Blo 1817610 1818311 := bstep (se 1 (by rfl) ⟨1363733, by rfl⟩ : syracuseStep 1818311 = 2727467) B2727467
theorem B2727623 : Blo 1817610 2727623 := bstep (se 1 (by rfl) ⟨2045717, by rfl⟩ : syracuseStep 2727623 = 4091435) B4091435
theorem B1818331 : Blo 1817610 1818331 := bstep (se 1 (by rfl) ⟨1363748, by rfl⟩ : syracuseStep 1818331 = 2727497) B2727497
theorem B20725469 : Blo 1817610 20725469 := bstep (se 3 (by rfl) ⟨3886025, by rfl⟩ : syracuseStep 20725469 = 7772051) B7772051
theorem B3882745 : Blo 1817610 3882745 := bstep (se 2 (by rfl) ⟨1456029, by rfl⟩ : syracuseStep 3882745 = 2912059) B2912059
theorem B9330425 : Blo 1817610 9330425 := bstep (se 2 (by rfl) ⟨3498909, by rfl⟩ : syracuseStep 9330425 = 6997819) B6997819
theorem B1818407 : Blo 1817610 1818407 := bstep (se 1 (by rfl) ⟨1363805, by rfl⟩ : syracuseStep 1818407 = 2727611) B2727611
theorem B1818447 : Blo 1817610 1818447 := bstep (se 1 (by rfl) ⟨1363835, by rfl⟩ : syracuseStep 1818447 = 2727671) B2727671
theorem B1818463 : Blo 1817610 1818463 := bstep (se 1 (by rfl) ⟨1363847, by rfl⟩ : syracuseStep 1818463 = 2727695) B2727695
theorem B6905695 : Blo 1817610 6905695 := bstep (se 1 (by rfl) ⟨5179271, by rfl⟩ : syracuseStep 6905695 = 10358543) B10358543
theorem B2727785 : Blo 1817610 2727785 := bstep (se 2 (by rfl) ⟨1022919, by rfl⟩ : syracuseStep 2727785 = 2045839) B2045839
theorem B1818491 : Blo 1817610 1818491 := bstep (se 1 (by rfl) ⟨1363868, by rfl⟩ : syracuseStep 1818491 = 2727737) B2727737
theorem B23314513 : Blo 1817610 23314513 := bstep (se 2 (by rfl) ⟨8742942, by rfl⟩ : syracuseStep 23314513 = 17485885) B17485885
theorem B1818543 : Blo 1817610 1818543 := bstep (se 1 (by rfl) ⟨1363907, by rfl⟩ : syracuseStep 1818543 = 2727815) B2727815
theorem B2727863 : Blo 1817610 2727863 := bstep (se 1 (by rfl) ⟨2045897, by rfl⟩ : syracuseStep 2727863 = 4091795) B4091795
theorem B10354625 : Blo 1817610 10354625 := bstep (se 2 (by rfl) ⟨3882984, by rfl⟩ : syracuseStep 10354625 = 7765969) B7765969
theorem B1818567 : Blo 1817610 1818567 := bstep (se 1 (by rfl) ⟨1363925, by rfl⟩ : syracuseStep 1818567 = 2727851) B2727851
theorem B1818587 : Blo 1817610 1818587 := bstep (se 1 (by rfl) ⟨1363940, by rfl⟩ : syracuseStep 1818587 = 2727881) B2727881
theorem B2727899 : Blo 1817610 2727899 := bstep (se 1 (by rfl) ⟨2045924, by rfl⟩ : syracuseStep 2727899 = 4091849) B4091849
theorem B7471129 : Blo 1817610 7471129 := bstep (se 2 (by rfl) ⟨2801673, by rfl⟩ : syracuseStep 7471129 = 5603347) B5603347
theorem B15540275 : Blo 1817610 15540275 := bstep (se 1 (by rfl) ⟨11655206, by rfl⟩ : syracuseStep 15540275 = 23310413) B23310413
theorem B41517137 : Blo 1817610 41517137 := bstep (se 2 (by rfl) ⟨15568926, by rfl⟩ : syracuseStep 41517137 = 31137853) B31137853
theorem B5177449 : Blo 1817610 5177449 := bstep (se 2 (by rfl) ⟨1941543, by rfl⟩ : syracuseStep 5177449 = 3883087) B3883087
theorem B6136019 : Blo 1817610 6136019 := bstep (se 1 (by rfl) ⟨4602014, by rfl⟩ : syracuseStep 6136019 = 9204029) B9204029
theorem B30294233 : Blo 1817610 30294233 := bstep (se 2 (by rfl) ⟨11360337, by rfl⟩ : syracuseStep 30294233 = 22720675) B22720675
theorem B1818911 : Blo 1817610 1818911 := bstep (se 1 (by rfl) ⟨1364183, by rfl⟩ : syracuseStep 1818911 = 2728367) B2728367
theorem B1941851 : Blo 1817610 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B2728283 : Blo 1817610 2728283 := bstep (se 1 (by rfl) ⟨2046212, by rfl⟩ : syracuseStep 2728283 = 4092425) B4092425
theorem B1818971 : Blo 1817610 1818971 := bstep (se 1 (by rfl) ⟨1364228, by rfl⟩ : syracuseStep 1818971 = 2728457) B2728457
theorem B1818991 : Blo 1817610 1818991 := bstep (se 1 (by rfl) ⟨1364243, by rfl⟩ : syracuseStep 1818991 = 2728487) B2728487
theorem B1819047 : Blo 1817610 1819047 := bstep (se 1 (by rfl) ⟨1364285, by rfl⟩ : syracuseStep 1819047 = 2728571) B2728571
theorem B3686867 : Blo 1817610 3686867 := bstep (se 1 (by rfl) ⟨2765150, by rfl⟩ : syracuseStep 3686867 = 5530301) B5530301
theorem B6136289 : Blo 1817610 6136289 := bstep (se 2 (by rfl) ⟨2301108, by rfl⟩ : syracuseStep 6136289 = 4602217) B4602217
theorem B3277307 : Blo 1817610 3277307 := bstep (se 1 (by rfl) ⟨2457980, by rfl⟩ : syracuseStep 3277307 = 4915961) B4915961
theorem B2245115 : Blo 1817610 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B1819131 : Blo 1817610 1819131 := bstep (se 1 (by rfl) ⟨1364348, by rfl⟩ : syracuseStep 1819131 = 2728697) B2728697
theorem B22110725 : Blo 1817610 22110725 := bstep (se 4 (by rfl) ⟨2072880, by rfl⟩ : syracuseStep 22110725 = 4145761) B4145761
theorem B4604435 : Blo 1817610 4604435 := bstep (se 1 (by rfl) ⟨3453326, by rfl⟩ : syracuseStep 4604435 = 6906653) B6906653
theorem B2728511 : Blo 1817610 2728511 := bstep (se 1 (by rfl) ⟨2046383, by rfl⟩ : syracuseStep 2728511 = 4092767) B4092767
theorem B1819199 : Blo 1817610 1819199 := bstep (se 1 (by rfl) ⟨1364399, by rfl⟩ : syracuseStep 1819199 = 2728799) B2728799
theorem B1819207 : Blo 1817610 1819207 := bstep (se 1 (by rfl) ⟨1364405, by rfl⟩ : syracuseStep 1819207 = 2728811) B2728811
theorem B2728631 : Blo 1817610 2728631 := bstep (se 1 (by rfl) ⟨2046473, by rfl⟩ : syracuseStep 2728631 = 4092947) B4092947
theorem B10494679 : Blo 1817610 10494679 := bstep (se 1 (by rfl) ⟨7871009, by rfl⟩ : syracuseStep 10494679 = 15742019) B15742019
theorem B3498719 : Blo 1817610 3498719 := bstep (se 1 (by rfl) ⟨2624039, by rfl⟩ : syracuseStep 3498719 = 5248079) B5248079
theorem B1819359 : Blo 1817610 1819359 := bstep (se 1 (by rfl) ⟨1364519, by rfl⟩ : syracuseStep 1819359 = 2729039) B2729039
theorem B1819439 : Blo 1817610 1819439 := bstep (se 1 (by rfl) ⟨1364579, by rfl⟩ : syracuseStep 1819439 = 2729159) B2729159
theorem B2728859 : Blo 1817610 2728859 := bstep (se 1 (by rfl) ⟨2046644, by rfl⟩ : syracuseStep 2728859 = 4093289) B4093289
theorem B1819547 : Blo 1817610 1819547 := bstep (se 1 (by rfl) ⟨1364660, by rfl⟩ : syracuseStep 1819547 = 2729321) B2729321
theorem B1819599 : Blo 1817610 1819599 := bstep (se 1 (by rfl) ⟨1364699, by rfl⟩ : syracuseStep 1819599 = 2729399) B2729399
theorem B9208889 : Blo 1817610 9208889 := bstep (se 2 (by rfl) ⟨3453333, by rfl⟩ : syracuseStep 9208889 = 6906667) B6906667
theorem B8741945 : Blo 1817610 8741945 := bstep (se 2 (by rfl) ⟨3278229, by rfl⟩ : syracuseStep 8741945 = 6556459) B6556459
theorem B10355809 : Blo 1817610 10355809 := bstep (se 2 (by rfl) ⟨3883428, by rfl⟩ : syracuseStep 10355809 = 7766857) B7766857
theorem B29492515 : Blo 1817610 29492515 := bstep (se 1 (by rfl) ⟨22119386, by rfl⟩ : syracuseStep 29492515 = 44238773) B44238773
theorem B2729255 : Blo 1817610 2729255 := bstep (se 1 (by rfl) ⟨2046941, by rfl⟩ : syracuseStep 2729255 = 4093883) B4093883
theorem B11650391 : Blo 1817610 11650391 := bstep (se 1 (by rfl) ⟨8737793, by rfl⟩ : syracuseStep 11650391 = 17475587) B17475587
theorem B2729339 : Blo 1817610 2729339 := bstep (se 1 (by rfl) ⟨2047004, by rfl⟩ : syracuseStep 2729339 = 4094009) B4094009
theorem B4916695 : Blo 1817610 4916695 := bstep (se 1 (by rfl) ⟨3687521, by rfl⟩ : syracuseStep 4916695 = 7375043) B7375043
theorem B3278431 : Blo 1817610 3278431 := bstep (se 1 (by rfl) ⟨2458823, by rfl⟩ : syracuseStep 3278431 = 4917647) B4917647
theorem B6137531 : Blo 1817610 6137531 := bstep (se 1 (by rfl) ⟨4603148, by rfl⟩ : syracuseStep 6137531 = 9206297) B9206297
theorem B46622465 : Blo 1817610 46622465 := bstep (se 2 (by rfl) ⟨17483424, by rfl⟩ : syracuseStep 46622465 = 34966849) B34966849
theorem B84002669 : Blo 1817610 84002669 := bstep (se 3 (by rfl) ⟨15750500, by rfl⟩ : syracuseStep 84002669 = 31501001) B31501001
theorem B7874695 : Blo 1817610 7874695 := bstep (se 1 (by rfl) ⟨5906021, by rfl⟩ : syracuseStep 7874695 = 11812043) B11812043
theorem B4090067 : Blo 1817610 4090067 := bstep (se 1 (by rfl) ⟨3067550, by rfl⟩ : syracuseStep 4090067 = 6135101) B6135101
theorem B4090121 : Blo 1817610 4090121 := bstep (se 2 (by rfl) ⟨1533795, by rfl⟩ : syracuseStep 4090121 = 3067591) B3067591
theorem B7768345 : Blo 1817610 7768345 := bstep (se 2 (by rfl) ⟨2913129, by rfl⟩ : syracuseStep 7768345 = 5826259) B5826259
theorem B3885403 : Blo 1817610 3885403 := bstep (se 1 (by rfl) ⟨2914052, by rfl⟩ : syracuseStep 3885403 = 5828105) B5828105
theorem B15534503 : Blo 1817610 15534503 := bstep (se 1 (by rfl) ⟨11650877, by rfl⟩ : syracuseStep 15534503 = 23301755) B23301755
theorem B26560979 : Blo 1817610 26560979 := bstep (se 1 (by rfl) ⟨19920734, by rfl⟩ : syracuseStep 26560979 = 39841469) B39841469
theorem B4090337 : Blo 1817610 4090337 := bstep (se 2 (by rfl) ⟨1533876, by rfl⟩ : syracuseStep 4090337 = 3067753) B3067753
theorem B6220283 : Blo 1817610 6220283 := bstep (se 1 (by rfl) ⟨4665212, by rfl⟩ : syracuseStep 6220283 = 9330425) B9330425
theorem B6908611 : Blo 1817610 6908611 := bstep (se 1 (by rfl) ⟨5181458, by rfl⟩ : syracuseStep 6908611 = 10362917) B10362917
theorem B4090643 : Blo 1817610 4090643 := bstep (se 1 (by rfl) ⟨3067982, by rfl⟩ : syracuseStep 4090643 = 6135965) B6135965
theorem B18672515 : Blo 1817610 18672515 := bstep (se 1 (by rfl) ⟨14004386, by rfl⟩ : syracuseStep 18672515 = 28008773) B28008773
theorem B5319595 : Blo 1817610 5319595 := bstep (se 1 (by rfl) ⟨3989696, by rfl⟩ : syracuseStep 5319595 = 7979393) B7979393
theorem B14388239 : Blo 1817610 14388239 := bstep (se 1 (by rfl) ⟨10791179, by rfl⟩ : syracuseStep 14388239 = 21582359) B21582359
theorem B9210995 : Blo 1817610 9210995 := bstep (se 1 (by rfl) ⟨6908246, by rfl⟩ : syracuseStep 9210995 = 13816493) B13816493
theorem B4091003 : Blo 1817610 4091003 := bstep (se 1 (by rfl) ⟨3068252, by rfl⟩ : syracuseStep 4091003 = 6136505) B6136505
theorem B4091129 : Blo 1817610 4091129 := bstep (se 2 (by rfl) ⟨1534173, by rfl⟩ : syracuseStep 4091129 = 3068347) B3068347
theorem B23301391 : Blo 1817610 23301391 := bstep (se 1 (by rfl) ⟨17476043, by rfl⟩ : syracuseStep 23301391 = 34952087) B34952087
theorem B4091273 : Blo 1817610 4091273 := bstep (se 2 (by rfl) ⟨1534227, by rfl⟩ : syracuseStep 4091273 = 3068455) B3068455
theorem B4369801 : Blo 1817610 4369801 := bstep (se 2 (by rfl) ⟨1638675, by rfl⟩ : syracuseStep 4369801 = 3277351) B3277351
theorem B4091399 : Blo 1817610 4091399 := bstep (se 1 (by rfl) ⟨3068549, by rfl⟩ : syracuseStep 4091399 = 6137099) B6137099
theorem B4370003 : Blo 1817610 4370003 := bstep (se 1 (by rfl) ⟨3277502, by rfl⟩ : syracuseStep 4370003 = 6555005) B6555005
theorem B6139475 : Blo 1817610 6139475 := bstep (se 1 (by rfl) ⟨4604606, by rfl⟩ : syracuseStep 6139475 = 9209213) B9209213
theorem B4206163 : Blo 1817610 4206163 := bstep (se 1 (by rfl) ⟨3154622, by rfl⟩ : syracuseStep 4206163 = 6309245) B6309245
theorem B4091579 : Blo 1817610 4091579 := bstep (se 1 (by rfl) ⟨3068684, by rfl⟩ : syracuseStep 4091579 = 6137369) B6137369
theorem B33165071 : Blo 1817610 33165071 := bstep (se 1 (by rfl) ⟨24873803, by rfl⟩ : syracuseStep 33165071 = 49747607) B49747607
theorem B39341861 : Blo 1817610 39341861 := bstep (se 4 (by rfl) ⟨3688299, by rfl⟩ : syracuseStep 39341861 = 7376599) B7376599
theorem B3452719 : Blo 1817610 3452719 := bstep (se 1 (by rfl) ⟨2589539, by rfl⟩ : syracuseStep 3452719 = 5179079) B5179079
theorem B4091705 : Blo 1817610 4091705 := bstep (se 2 (by rfl) ⟨1534389, by rfl⟩ : syracuseStep 4091705 = 3068779) B3068779
theorem B12447769 : Blo 1817610 12447769 := bstep (se 2 (by rfl) ⟨4667913, by rfl⟩ : syracuseStep 12447769 = 9335827) B9335827
theorem B15544649 : Blo 1817610 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B3068327 : Blo 1817610 3068327 := bstep (se 1 (by rfl) ⟨2301245, by rfl⟩ : syracuseStep 3068327 = 4602491) B4602491
theorem B4092335 : Blo 1817610 4092335 := bstep (se 1 (by rfl) ⟨3069251, by rfl⟩ : syracuseStep 4092335 = 6138503) B6138503
theorem B4092371 : Blo 1817610 4092371 := bstep (se 1 (by rfl) ⟨3069278, by rfl⟩ : syracuseStep 4092371 = 6138557) B6138557
theorem B8294881 : Blo 1817610 8294881 := bstep (se 2 (by rfl) ⟨3110580, by rfl⟩ : syracuseStep 8294881 = 6221161) B6221161
theorem B4092479 : Blo 1817610 4092479 := bstep (se 1 (by rfl) ⟨3069359, by rfl⟩ : syracuseStep 4092479 = 6138719) B6138719
theorem B3068489 : Blo 1817610 3068489 := bstep (se 2 (by rfl) ⟨1150683, by rfl⟩ : syracuseStep 3068489 = 2301367) B2301367
theorem B4321871 : Blo 1817610 4321871 := bstep (se 1 (by rfl) ⟨3241403, by rfl⟩ : syracuseStep 4321871 = 6482807) B6482807
theorem B4092587 : Blo 1817610 4092587 := bstep (se 1 (by rfl) ⟨3069440, by rfl⟩ : syracuseStep 4092587 = 6138881) B6138881
theorem B2044903 : Blo 1817610 2044903 := bstep (se 1 (by rfl) ⟨1533677, by rfl⟩ : syracuseStep 2044903 = 3067355) B3067355
theorem B4600871 : Blo 1817610 4600871 := bstep (se 1 (by rfl) ⟨3450653, by rfl⟩ : syracuseStep 4600871 = 6901307) B6901307
theorem B35927185 : Blo 1817610 35927185 := bstep (se 2 (by rfl) ⟨13472694, by rfl⟩ : syracuseStep 35927185 = 26945389) B26945389
theorem B13816979 : Blo 1817610 13816979 := bstep (se 1 (by rfl) ⟨10362734, by rfl⟩ : syracuseStep 13816979 = 20725469) B20725469
theorem B4093127 : Blo 1817610 4093127 := bstep (se 1 (by rfl) ⟨3069845, by rfl⟩ : syracuseStep 4093127 = 6139691) B6139691
theorem B6903083 : Blo 1817610 6903083 := bstep (se 1 (by rfl) ⟨5177312, by rfl⟩ : syracuseStep 6903083 = 10354625) B10354625
theorem B4093307 : Blo 1817610 4093307 := bstep (se 1 (by rfl) ⟨3069980, by rfl⟩ : syracuseStep 4093307 = 6139961) B6139961
theorem B15537541 : Blo 1817610 15537541 := bstep (se 4 (by rfl) ⟨1456644, by rfl⟩ : syracuseStep 15537541 = 2913289) B2913289
theorem B4601225 : Blo 1817610 4601225 := bstep (se 2 (by rfl) ⟨1725459, by rfl⟩ : syracuseStep 4601225 = 3450919) B3450919
theorem B31086017 : Blo 1817610 31086017 := bstep (se 2 (by rfl) ⟨11657256, by rfl⟩ : syracuseStep 31086017 = 23314513) B23314513
theorem B4093433 : Blo 1817610 4093433 := bstep (se 2 (by rfl) ⟨1535037, by rfl⟩ : syracuseStep 4093433 = 3070075) B3070075
theorem B4093523 : Blo 1817610 4093523 := bstep (se 1 (by rfl) ⟨3070142, by rfl⟩ : syracuseStep 4093523 = 6140285) B6140285
theorem B3069535 : Blo 1817610 3069535 := bstep (se 1 (by rfl) ⟨2302151, by rfl⟩ : syracuseStep 3069535 = 4604303) B4604303
theorem B4667041 : Blo 1817610 4667041 := bstep (se 2 (by rfl) ⟨1750140, by rfl⟩ : syracuseStep 4667041 = 3500281) B3500281
theorem B4093703 : Blo 1817610 4093703 := bstep (se 1 (by rfl) ⟨3070277, by rfl⟩ : syracuseStep 4093703 = 6140555) B6140555
theorem B3069751 : Blo 1817610 3069751 := bstep (se 1 (by rfl) ⟨2302313, by rfl⟩ : syracuseStep 3069751 = 4604627) B4604627
theorem B8738945 : Blo 1817610 8738945 := bstep (se 2 (by rfl) ⟨3277104, by rfl⟩ : syracuseStep 8738945 = 6554209) B6554209
theorem B3070217 : Blo 1817610 3070217 := bstep (se 2 (by rfl) ⟨1151331, by rfl⟩ : syracuseStep 3070217 = 2302663) B2302663
theorem B8862119 : Blo 1817610 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B11647415 : Blo 1817610 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B2726471 : Blo 1817610 2726471 := bstep (se 1 (by rfl) ⟨2044853, by rfl⟩ : syracuseStep 2726471 = 4089707) B4089707
theorem B8739407 : Blo 1817610 8739407 := bstep (se 1 (by rfl) ⟨6554555, by rfl⟩ : syracuseStep 8739407 = 13109111) B13109111
theorem B2046559 : Blo 1817610 2046559 := bstep (se 1 (by rfl) ⟨1534919, by rfl⟩ : syracuseStep 2046559 = 3069839) B3069839
theorem B2185823 : Blo 1817610 2185823 := bstep (se 1 (by rfl) ⟨1639367, by rfl⟩ : syracuseStep 2185823 = 3278735) B3278735
theorem B2726507 : Blo 1817610 2726507 := bstep (se 1 (by rfl) ⟨2044880, by rfl⟩ : syracuseStep 2726507 = 4089761) B4089761
theorem B32365163 : Blo 1817610 32365163 := bstep (se 1 (by rfl) ⟨24273872, by rfl⟩ : syracuseStep 32365163 = 48547745) B48547745
theorem B20707973 : Blo 1817610 20707973 := bstep (se 4 (by rfl) ⟨1941372, by rfl⟩ : syracuseStep 20707973 = 3882745) B3882745
theorem B7871165 : Blo 1817610 7871165 := bstep (se 3 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 7871165 = 2951687) B2951687
theorem B2300719 : Blo 1817610 2300719 := bstep (se 1 (by rfl) ⟨1725539, by rfl⟩ : syracuseStep 2300719 = 3451079) B3451079
theorem B2726735 : Blo 1817610 2726735 := bstep (se 1 (by rfl) ⟨2045051, by rfl⟩ : syracuseStep 2726735 = 4090103) B4090103
theorem B4602703 : Blo 1817610 4602703 := bstep (se 1 (by rfl) ⟨3452027, by rfl⟩ : syracuseStep 4602703 = 6904055) B6904055
theorem B34945937 : Blo 1817610 34945937 := bstep (se 2 (by rfl) ⟨13104726, by rfl⟩ : syracuseStep 34945937 = 26209453) B26209453
theorem B5176219 : Blo 1817610 5176219 := bstep (se 1 (by rfl) ⟨3882164, by rfl⟩ : syracuseStep 5176219 = 7764329) B7764329
theorem B9829457 : Blo 1817610 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B4602977 : Blo 1817610 4602977 := bstep (se 2 (by rfl) ⟨1726116, by rfl⟩ : syracuseStep 4602977 = 3452233) B3452233
theorem B2727131 : Blo 1817610 2727131 := bstep (se 1 (by rfl) ⟨2045348, by rfl⟩ : syracuseStep 2727131 = 4090697) B4090697
theorem B17480933 : Blo 1817610 17480933 := bstep (se 4 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 17480933 = 3277675) B3277675
theorem B1817887 : Blo 1817610 1817887 := bstep (se 1 (by rfl) ⟨1363415, by rfl⟩ : syracuseStep 1817887 = 2726831) B2726831
theorem B9207107 : Blo 1817610 9207107 := bstep (se 1 (by rfl) ⟨6905330, by rfl⟩ : syracuseStep 9207107 = 13810661) B13810661
theorem B1817947 : Blo 1817610 1817947 := bstep (se 1 (by rfl) ⟨1363460, by rfl⟩ : syracuseStep 1817947 = 2726921) B2726921
theorem B3882335 : Blo 1817610 3882335 := bstep (se 1 (by rfl) ⟨2911751, by rfl⟩ : syracuseStep 3882335 = 5823503) B5823503
theorem B1817967 : Blo 1817610 1817967 := bstep (se 1 (by rfl) ⟨1363475, by rfl⟩ : syracuseStep 1817967 = 2726951) B2726951
theorem B5823863 : Blo 1817610 5823863 := bstep (se 1 (by rfl) ⟨4367897, by rfl⟩ : syracuseStep 5823863 = 8735795) B8735795
theorem B2588041 : Blo 1817610 2588041 := bstep (se 2 (by rfl) ⟨970515, by rfl⟩ : syracuseStep 2588041 = 1941031) B1941031
theorem B14941577 : Blo 1817610 14941577 := bstep (se 2 (by rfl) ⟨5603091, by rfl⟩ : syracuseStep 14941577 = 11206183) B11206183
theorem B2727305 : Blo 1817610 2727305 := bstep (se 2 (by rfl) ⟨1022739, by rfl⟩ : syracuseStep 2727305 = 2045479) B2045479
theorem B1818023 : Blo 1817610 1818023 := bstep (se 1 (by rfl) ⟨1363517, by rfl⟩ : syracuseStep 1818023 = 2727035) B2727035
theorem B4603351 : Blo 1817610 4603351 := bstep (se 1 (by rfl) ⟨3452513, by rfl⟩ : syracuseStep 4603351 = 6905027) B6905027
theorem B10354169 : Blo 1817610 10354169 := bstep (se 2 (by rfl) ⟨3882813, by rfl⟩ : syracuseStep 10354169 = 7765627) B7765627
theorem B1818107 : Blo 1817610 1818107 := bstep (se 1 (by rfl) ⟨1363580, by rfl⟩ : syracuseStep 1818107 = 2727161) B2727161
theorem B26230331 : Blo 1817610 26230331 := bstep (se 1 (by rfl) ⟨19672748, by rfl⟩ : syracuseStep 26230331 = 39345497) B39345497
theorem B1818175 : Blo 1817610 1818175 := bstep (se 1 (by rfl) ⟨1363631, by rfl⟩ : syracuseStep 1818175 = 2727263) B2727263
theorem B1818183 : Blo 1817610 1818183 := bstep (se 1 (by rfl) ⟨1363637, by rfl⟩ : syracuseStep 1818183 = 2727275) B2727275
theorem B6553171 : Blo 1817610 6553171 := bstep (se 1 (by rfl) ⟨4914878, by rfl⟩ : syracuseStep 6553171 = 9829757) B9829757
theorem B1818335 : Blo 1817610 1818335 := bstep (se 1 (by rfl) ⟨1363751, by rfl⟩ : syracuseStep 1818335 = 2727503) B2727503
theorem B2727659 : Blo 1817610 2727659 := bstep (se 1 (by rfl) ⟨2045744, by rfl⟩ : syracuseStep 2727659 = 4091489) B4091489
theorem B4603655 : Blo 1817610 4603655 := bstep (se 1 (by rfl) ⟨3452741, by rfl⟩ : syracuseStep 4603655 = 6905483) B6905483
theorem B8740619 : Blo 1817610 8740619 := bstep (se 1 (by rfl) ⟨6555464, by rfl⟩ : syracuseStep 8740619 = 13110929) B13110929
theorem B9207593 : Blo 1817610 9207593 := bstep (se 2 (by rfl) ⟨3452847, by rfl⟩ : syracuseStep 9207593 = 6905695) B6905695
theorem B1818415 : Blo 1817610 1818415 := bstep (se 1 (by rfl) ⟨1363811, by rfl⟩ : syracuseStep 1818415 = 2727623) B2727623
theorem B13803371 : Blo 1817610 13803371 := bstep (se 1 (by rfl) ⟨10352528, by rfl⟩ : syracuseStep 13803371 = 20705057) B20705057
theorem B1941403 : Blo 1817610 1941403 := bstep (se 1 (by rfl) ⟨1456052, by rfl⟩ : syracuseStep 1941403 = 2912105) B2912105
theorem B1818523 : Blo 1817610 1818523 := bstep (se 1 (by rfl) ⟨1363892, by rfl⟩ : syracuseStep 1818523 = 2727785) B2727785
theorem B1818575 : Blo 1817610 1818575 := bstep (se 1 (by rfl) ⟨1363931, by rfl⟩ : syracuseStep 1818575 = 2727863) B2727863
theorem B2727887 : Blo 1817610 2727887 := bstep (se 1 (by rfl) ⟨2045915, by rfl⟩ : syracuseStep 2727887 = 4091831) B4091831
theorem B1818599 : Blo 1817610 1818599 := bstep (se 1 (by rfl) ⟨1363949, by rfl⟩ : syracuseStep 1818599 = 2727899) B2727899
theorem B9961505 : Blo 1817610 9961505 := bstep (se 2 (by rfl) ⟨3735564, by rfl⟩ : syracuseStep 9961505 = 7471129) B7471129
theorem B16597025 : Blo 1817610 16597025 := bstep (se 2 (by rfl) ⟨6223884, by rfl⟩ : syracuseStep 16597025 = 12447769) B12447769
theorem B10363099 : Blo 1817610 10363099 := bstep (se 1 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 10363099 = 15544649) B15544649
theorem B1818855 : Blo 1817610 1818855 := bstep (se 1 (by rfl) ⟨1364141, by rfl⟩ : syracuseStep 1818855 = 2728283) B2728283
theorem B2728223 : Blo 1817610 2728223 := bstep (se 1 (by rfl) ⟨2046167, by rfl⟩ : syracuseStep 2728223 = 4092335) B4092335
theorem B2457911 : Blo 1817610 2457911 := bstep (se 1 (by rfl) ⟨1843433, by rfl⟩ : syracuseStep 2457911 = 3686867) B3686867
theorem B2728247 : Blo 1817610 2728247 := bstep (se 1 (by rfl) ⟨2046185, by rfl⟩ : syracuseStep 2728247 = 4092371) B4092371
theorem B2728319 : Blo 1817610 2728319 := bstep (se 1 (by rfl) ⟨2046239, by rfl⟩ : syracuseStep 2728319 = 4092479) B4092479
theorem B1819007 : Blo 1817610 1819007 := bstep (se 1 (by rfl) ⟨1364255, by rfl⟩ : syracuseStep 1819007 = 2728511) B2728511
theorem B2728391 : Blo 1817610 2728391 := bstep (se 1 (by rfl) ⟨2046293, by rfl⟩ : syracuseStep 2728391 = 4092587) B4092587
theorem B1819087 : Blo 1817610 1819087 := bstep (se 1 (by rfl) ⟨1364315, by rfl⟩ : syracuseStep 1819087 = 2728631) B2728631
theorem B1819239 : Blo 1817610 1819239 := bstep (se 1 (by rfl) ⟨1364429, by rfl⟩ : syracuseStep 1819239 = 2728859) B2728859
theorem B11059841 : Blo 1817610 11059841 := bstep (se 2 (by rfl) ⟨4147440, by rfl⟩ : syracuseStep 11059841 = 8294881) B8294881
theorem B2728745 : Blo 1817610 2728745 := bstep (se 2 (by rfl) ⟨1023279, by rfl⟩ : syracuseStep 2728745 = 2046559) B2046559
theorem B2728751 : Blo 1817610 2728751 := bstep (se 1 (by rfl) ⟨2046563, by rfl⟩ : syracuseStep 2728751 = 4093127) B4093127
theorem B1819503 : Blo 1817610 1819503 := bstep (se 1 (by rfl) ⟨1364627, by rfl⟩ : syracuseStep 1819503 = 2729255) B2729255
theorem B7766927 : Blo 1817610 7766927 := bstep (se 1 (by rfl) ⟨5825195, by rfl⟩ : syracuseStep 7766927 = 11650391) B11650391
theorem B5178269 : Blo 1817610 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B2728871 : Blo 1817610 2728871 := bstep (se 1 (by rfl) ⟨2046653, by rfl⟩ : syracuseStep 2728871 = 4093307) B4093307
theorem B1819559 : Blo 1817610 1819559 := bstep (se 1 (by rfl) ⟨1364669, by rfl⟩ : syracuseStep 1819559 = 2729339) B2729339
theorem B13992905 : Blo 1817610 13992905 := bstep (se 2 (by rfl) ⟨5247339, by rfl⟩ : syracuseStep 13992905 = 10494679) B10494679
theorem B2728955 : Blo 1817610 2728955 := bstep (se 1 (by rfl) ⟨2046716, by rfl⟩ : syracuseStep 2728955 = 4093433) B4093433
theorem B2729015 : Blo 1817610 2729015 := bstep (se 1 (by rfl) ⟨2046761, by rfl⟩ : syracuseStep 2729015 = 4093523) B4093523
theorem B6136937 : Blo 1817610 6136937 := bstep (se 2 (by rfl) ⟨2301351, by rfl⟩ : syracuseStep 6136937 = 4602703) B4602703
theorem B31081643 : Blo 1817610 31081643 := bstep (se 1 (by rfl) ⟨23311232, by rfl⟩ : syracuseStep 31081643 = 46622465) B46622465
theorem B2729135 : Blo 1817610 2729135 := bstep (se 1 (by rfl) ⟨2046851, by rfl⟩ : syracuseStep 2729135 = 4093703) B4093703
theorem B56001779 : Blo 1817610 56001779 := bstep (se 1 (by rfl) ⟨42001334, by rfl⟩ : syracuseStep 56001779 = 84002669) B84002669
theorem B5825963 : Blo 1817610 5825963 := bstep (se 1 (by rfl) ⟨4369472, by rfl⟩ : syracuseStep 5825963 = 8738945) B8738945
theorem B10356335 : Blo 1817610 10356335 := bstep (se 1 (by rfl) ⟨7767251, by rfl⟩ : syracuseStep 10356335 = 15534503) B15534503
theorem B5908079 : Blo 1817610 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B39323353 : Blo 1817610 39323353 := bstep (se 2 (by rfl) ⟨14746257, by rfl⟩ : syracuseStep 39323353 = 29492515) B29492515
theorem B5826271 : Blo 1817610 5826271 := bstep (se 1 (by rfl) ⟨4369703, by rfl⟩ : syracuseStep 5826271 = 8739407) B8739407
theorem B13805315 : Blo 1817610 13805315 := bstep (se 1 (by rfl) ⟨10353986, by rfl⟩ : syracuseStep 13805315 = 20707973) B20707973
theorem B5826401 : Blo 1817610 5826401 := bstep (se 2 (by rfl) ⟨2184900, by rfl⟩ : syracuseStep 5826401 = 4369801) B4369801
theorem B6137801 : Blo 1817610 6137801 := bstep (se 2 (by rfl) ⟨2301675, by rfl⟩ : syracuseStep 6137801 = 4603351) B4603351
theorem B6555593 : Blo 1817610 6555593 := bstep (se 2 (by rfl) ⟨2458347, by rfl⟩ : syracuseStep 6555593 = 4916695) B4916695
theorem B6138071 : Blo 1817610 6138071 := bstep (se 1 (by rfl) ⟨4603553, by rfl⟩ : syracuseStep 6138071 = 9207107) B9207107
theorem B5827079 : Blo 1817610 5827079 := bstep (se 1 (by rfl) ⟨4370309, by rfl⟩ : syracuseStep 5827079 = 8740619) B8740619
theorem B6138395 : Blo 1817610 6138395 := bstep (se 1 (by rfl) ⟨4603796, by rfl⟩ : syracuseStep 6138395 = 9207593) B9207593
theorem B9202247 : Blo 1817610 9202247 := bstep (se 1 (by rfl) ⟨6901685, by rfl⟩ : syracuseStep 9202247 = 13803371) B13803371
theorem B66349685 : Blo 1817610 66349685 := bstep (se 5 (by rfl) ⟨3110141, by rfl⟩ : syracuseStep 66349685 = 6220283) B6220283
theorem B4090679 : Blo 1817610 4090679 := bstep (se 1 (by rfl) ⟨3068009, by rfl⟩ : syracuseStep 4090679 = 6136019) B6136019
theorem B20196155 : Blo 1817610 20196155 := bstep (se 1 (by rfl) ⟨15147116, by rfl⟩ : syracuseStep 20196155 = 30294233) B30294233
theorem B4090859 : Blo 1817610 4090859 := bstep (se 1 (by rfl) ⟨3068144, by rfl⟩ : syracuseStep 4090859 = 6136289) B6136289
theorem B14740483 : Blo 1817610 14740483 := bstep (se 1 (by rfl) ⟨11055362, by rfl⟩ : syracuseStep 14740483 = 22110725) B22110725
theorem B10357793 : Blo 1817610 10357793 := bstep (se 2 (by rfl) ⟨3884172, by rfl⟩ : syracuseStep 10357793 = 7768345) B7768345
theorem B5180537 : Blo 1817610 5180537 := bstep (se 2 (by rfl) ⟨1942701, by rfl⟩ : syracuseStep 5180537 = 3885403) B3885403
theorem B3067247 : Blo 1817610 3067247 := bstep (se 1 (by rfl) ⟨2300435, by rfl⟩ : syracuseStep 3067247 = 4600871) B4600871
theorem B6139259 : Blo 1817610 6139259 := bstep (se 1 (by rfl) ⟨4604444, by rfl⟩ : syracuseStep 6139259 = 9208889) B9208889
theorem B5827963 : Blo 1817610 5827963 := bstep (se 1 (by rfl) ⟨4370972, by rfl⟩ : syracuseStep 5827963 = 8741945) B8741945
theorem B9211319 : Blo 1817610 9211319 := bstep (se 1 (by rfl) ⟨6908489, by rfl⟩ : syracuseStep 9211319 = 13816979) B13816979
theorem B24890885 : Blo 1817610 24890885 := bstep (se 4 (by rfl) ⟨2333520, by rfl⟩ : syracuseStep 24890885 = 4667041) B4667041
theorem B9211481 : Blo 1817610 9211481 := bstep (se 2 (by rfl) ⟨3454305, by rfl⟩ : syracuseStep 9211481 = 6908611) B6908611
theorem B3067483 : Blo 1817610 3067483 := bstep (se 1 (by rfl) ⟨2300612, by rfl⟩ : syracuseStep 3067483 = 4601225) B4601225
theorem B3067625 : Blo 1817610 3067625 := bstep (se 2 (by rfl) ⟨1150359, by rfl⟩ : syracuseStep 3067625 = 2300719) B2300719
theorem B4091687 : Blo 1817610 4091687 := bstep (se 1 (by rfl) ⟨3068765, by rfl⟩ : syracuseStep 4091687 = 6137531) B6137531
theorem B31059773 : Blo 1817610 31059773 := bstep (se 3 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 31059773 = 11647415) B11647415
theorem B6901625 : Blo 1817610 6901625 := bstep (se 2 (by rfl) ⟨2588109, by rfl⟩ : syracuseStep 6901625 = 5176219) B5176219
theorem B13807745 : Blo 1817610 13807745 := bstep (se 2 (by rfl) ⟨5177904, by rfl⟩ : syracuseStep 13807745 = 10355809) B10355809
theorem B47902913 : Blo 1817610 47902913 := bstep (se 2 (by rfl) ⟨17963592, by rfl⟩ : syracuseStep 47902913 = 35927185) B35927185
theorem B5828861 : Blo 1817610 5828861 := bstep (se 3 (by rfl) ⟨1092911, by rfl⟩ : syracuseStep 5828861 = 2185823) B2185823
theorem B17707319 : Blo 1817610 17707319 := bstep (se 1 (by rfl) ⟨13280489, by rfl⟩ : syracuseStep 17707319 = 26560979) B26560979
theorem B31068521 : Blo 1817610 31068521 := bstep (se 2 (by rfl) ⟨11650695, by rfl⟩ : syracuseStep 31068521 = 23301391) B23301391
theorem B5247443 : Blo 1817610 5247443 := bstep (se 1 (by rfl) ⟨3935582, by rfl⟩ : syracuseStep 5247443 = 7871165) B7871165
theorem B12448343 : Blo 1817610 12448343 := bstep (se 1 (by rfl) ⟨9336257, by rfl⟩ : syracuseStep 12448343 = 18672515) B18672515
theorem B3068651 : Blo 1817610 3068651 := bstep (se 1 (by rfl) ⟨2301488, by rfl⟩ : syracuseStep 3068651 = 4602977) B4602977
theorem B6140663 : Blo 1817610 6140663 := bstep (se 1 (by rfl) ⟨4605497, by rfl⟩ : syracuseStep 6140663 = 9210995) B9210995
theorem B8737561 : Blo 1817610 8737561 := bstep (se 2 (by rfl) ⟨3276585, by rfl⟩ : syracuseStep 8737561 = 6553171) B6553171
theorem B5608217 : Blo 1817610 5608217 := bstep (se 2 (by rfl) ⟨2103081, by rfl⟩ : syracuseStep 5608217 = 4206163) B4206163
theorem B4092713 : Blo 1817610 4092713 := bstep (se 2 (by rfl) ⟨1534767, by rfl⟩ : syracuseStep 4092713 = 3069535) B3069535
theorem B4371241 : Blo 1817610 4371241 := bstep (se 2 (by rfl) ⟨1639215, by rfl⟩ : syracuseStep 4371241 = 3278431) B3278431
theorem B11653955 : Blo 1817610 11653955 := bstep (se 1 (by rfl) ⟨8740466, by rfl⟩ : syracuseStep 11653955 = 17480933) B17480933
theorem B6902779 : Blo 1817610 6902779 := bstep (se 1 (by rfl) ⟨5177084, by rfl⟩ : syracuseStep 6902779 = 10354169) B10354169
theorem B17486887 : Blo 1817610 17486887 := bstep (se 1 (by rfl) ⟨13115165, by rfl⟩ : syracuseStep 17486887 = 26230331) B26230331
theorem B2913335 : Blo 1817610 2913335 := bstep (se 1 (by rfl) ⟨2185001, by rfl⟩ : syracuseStep 2913335 = 4370003) B4370003
theorem B4092983 : Blo 1817610 4092983 := bstep (se 1 (by rfl) ⟨3069737, by rfl⟩ : syracuseStep 4092983 = 6139475) B6139475
theorem B4093001 : Blo 1817610 4093001 := bstep (se 2 (by rfl) ⟨1534875, by rfl⟩ : syracuseStep 4093001 = 3069751) B3069751
theorem B3069103 : Blo 1817610 3069103 := bstep (se 1 (by rfl) ⟨2301827, by rfl⟩ : syracuseStep 3069103 = 4603655) B4603655
theorem B26227907 : Blo 1817610 26227907 := bstep (se 1 (by rfl) ⟨19670930, by rfl⟩ : syracuseStep 26227907 = 39341861) B39341861
theorem B10360183 : Blo 1817610 10360183 := bstep (se 1 (by rfl) ⟨7770137, by rfl⟩ : syracuseStep 10360183 = 15540275) B15540275
theorem B38368637 : Blo 1817610 38368637 := bstep (se 3 (by rfl) ⟨7194119, by rfl⟩ : syracuseStep 38368637 = 14388239) B14388239
theorem B6903265 : Blo 1817610 6903265 := bstep (se 2 (by rfl) ⟨2588724, by rfl⟩ : syracuseStep 6903265 = 5177449) B5177449
theorem B10499593 : Blo 1817610 10499593 := bstep (se 2 (by rfl) ⟨3937347, by rfl⟩ : syracuseStep 10499593 = 7874695) B7874695
theorem B110712365 : Blo 1817610 110712365 := bstep (se 3 (by rfl) ⟨20758568, by rfl⟩ : syracuseStep 110712365 = 41517137) B41517137
theorem B2045551 : Blo 1817610 2045551 := bstep (se 1 (by rfl) ⟨1534163, by rfl⟩ : syracuseStep 2045551 = 3068327) B3068327
theorem B3069623 : Blo 1817610 3069623 := bstep (se 1 (by rfl) ⟨2302217, by rfl⟩ : syracuseStep 3069623 = 4604435) B4604435
theorem B2045659 : Blo 1817610 2045659 := bstep (se 1 (by rfl) ⟨1534244, by rfl⟩ : syracuseStep 2045659 = 3068489) B3068489
theorem B2881247 : Blo 1817610 2881247 := bstep (se 1 (by rfl) ⟨2160935, by rfl⟩ : syracuseStep 2881247 = 4321871) B4321871
theorem B4602055 : Blo 1817610 4602055 := bstep (se 1 (by rfl) ⟨3451541, by rfl⟩ : syracuseStep 4602055 = 6903083) B6903083
theorem B10352893 : Blo 1817610 10352893 := bstep (se 3 (by rfl) ⟨1941167, by rfl⟩ : syracuseStep 10352893 = 3882335) B3882335
theorem B20724011 : Blo 1817610 20724011 := bstep (se 1 (by rfl) ⟨15543008, by rfl⟩ : syracuseStep 20724011 = 31086017) B31086017
theorem B7092793 : Blo 1817610 7092793 := bstep (se 2 (by rfl) ⟨2659797, by rfl⟩ : syracuseStep 7092793 = 5319595) B5319595
theorem B2726537 : Blo 1817610 2726537 := bstep (se 2 (by rfl) ⟨1022451, by rfl⟩ : syracuseStep 2726537 = 2044903) B2044903
theorem B8739485 : Blo 1817610 8739485 := bstep (se 3 (by rfl) ⟨1638653, by rfl⟩ : syracuseStep 8739485 = 3277307) B3277307
theorem B5986973 : Blo 1817610 5986973 := bstep (se 3 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 5986973 = 2245115) B2245115
theorem B2726711 : Blo 1817610 2726711 := bstep (se 1 (by rfl) ⟨2045033, by rfl⟩ : syracuseStep 2726711 = 4090067) B4090067
theorem B2726747 : Blo 1817610 2726747 := bstep (se 1 (by rfl) ⟨2045060, by rfl⟩ : syracuseStep 2726747 = 4090121) B4090121
theorem B2046811 : Blo 1817610 2046811 := bstep (se 1 (by rfl) ⟨1535108, by rfl⟩ : syracuseStep 2046811 = 3070217) B3070217
theorem B2726891 : Blo 1817610 2726891 := bstep (se 1 (by rfl) ⟨2045168, by rfl⟩ : syracuseStep 2726891 = 4090337) B4090337
theorem B1817647 : Blo 1817610 1817647 := bstep (se 1 (by rfl) ⟨1363235, by rfl⟩ : syracuseStep 1817647 = 2726471) B2726471
theorem B1817671 : Blo 1817610 1817671 := bstep (se 1 (by rfl) ⟨1363253, by rfl⟩ : syracuseStep 1817671 = 2726507) B2726507
theorem B21576775 : Blo 1817610 21576775 := bstep (se 1 (by rfl) ⟨16182581, by rfl⟩ : syracuseStep 21576775 = 32365163) B32365163
theorem B20716721 : Blo 1817610 20716721 := bstep (se 2 (by rfl) ⟨7768770, by rfl⟩ : syracuseStep 20716721 = 15537541) B15537541
theorem B2727095 : Blo 1817610 2727095 := bstep (se 1 (by rfl) ⟨2045321, by rfl⟩ : syracuseStep 2727095 = 4090643) B4090643
theorem B1817823 : Blo 1817610 1817823 := bstep (se 1 (by rfl) ⟨1363367, by rfl⟩ : syracuseStep 1817823 = 2726735) B2726735
theorem B9329917 : Blo 1817610 9329917 := bstep (se 3 (by rfl) ⟨1749359, by rfl⟩ : syracuseStep 9329917 = 3498719) B3498719
theorem B23297291 : Blo 1817610 23297291 := bstep (se 1 (by rfl) ⟨17472968, by rfl⟩ : syracuseStep 23297291 = 34945937) B34945937
theorem B13802885 : Blo 1817610 13802885 := bstep (se 4 (by rfl) ⟨1294020, by rfl⟩ : syracuseStep 13802885 = 2588041) B2588041
theorem B6552971 : Blo 1817610 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B2727335 : Blo 1817610 2727335 := bstep (se 1 (by rfl) ⟨2045501, by rfl⟩ : syracuseStep 2727335 = 4091003) B4091003
theorem B1818087 : Blo 1817610 1818087 := bstep (se 1 (by rfl) ⟨1363565, by rfl⟩ : syracuseStep 1818087 = 2727131) B2727131
theorem B2727419 : Blo 1817610 2727419 := bstep (se 1 (by rfl) ⟨2045564, by rfl⟩ : syracuseStep 2727419 = 4091129) B4091129
theorem B3882575 : Blo 1817610 3882575 := bstep (se 1 (by rfl) ⟨2911931, by rfl⟩ : syracuseStep 3882575 = 5823863) B5823863
theorem B9961051 : Blo 1817610 9961051 := bstep (se 1 (by rfl) ⟨7470788, by rfl⟩ : syracuseStep 9961051 = 14941577) B14941577
theorem B1818203 : Blo 1817610 1818203 := bstep (se 1 (by rfl) ⟨1363652, by rfl⟩ : syracuseStep 1818203 = 2727305) B2727305
theorem B2727515 : Blo 1817610 2727515 := bstep (se 1 (by rfl) ⟨2045636, by rfl⟩ : syracuseStep 2727515 = 4091273) B4091273
theorem B2727599 : Blo 1817610 2727599 := bstep (se 1 (by rfl) ⟨2045699, by rfl⟩ : syracuseStep 2727599 = 4091399) B4091399
theorem B4603625 : Blo 1817610 4603625 := bstep (se 2 (by rfl) ⟨1726359, by rfl⟩ : syracuseStep 4603625 = 3452719) B3452719
theorem B2727719 : Blo 1817610 2727719 := bstep (se 1 (by rfl) ⟨2045789, by rfl⟩ : syracuseStep 2727719 = 4091579) B4091579
theorem B1818439 : Blo 1817610 1818439 := bstep (se 1 (by rfl) ⟨1363829, by rfl⟩ : syracuseStep 1818439 = 2727659) B2727659
theorem B22110047 : Blo 1817610 22110047 := bstep (se 1 (by rfl) ⟨16582535, by rfl⟩ : syracuseStep 22110047 = 33165071) B33165071
theorem B2588537 : Blo 1817610 2588537 := bstep (se 2 (by rfl) ⟨970701, by rfl⟩ : syracuseStep 2588537 = 1941403) B1941403
theorem B2727803 : Blo 1817610 2727803 := bstep (se 1 (by rfl) ⟨2045852, by rfl⟩ : syracuseStep 2727803 = 4091705) B4091705
theorem B1818591 : Blo 1817610 1818591 := bstep (se 1 (by rfl) ⟨1363943, by rfl⟩ : syracuseStep 1818591 = 2727887) B2727887
theorem B1818815 : Blo 1817610 1818815 := bstep (se 1 (by rfl) ⟨1364111, by rfl⟩ : syracuseStep 1818815 = 2728223) B2728223
theorem B11804879 : Blo 1817610 11804879 := bstep (se 1 (by rfl) ⟨8853659, by rfl⟩ : syracuseStep 11804879 = 17707319) B17707319
theorem B1818831 : Blo 1817610 1818831 := bstep (se 1 (by rfl) ⟨1364123, by rfl⟩ : syracuseStep 1818831 = 2728247) B2728247
theorem B1818879 : Blo 1817610 1818879 := bstep (se 1 (by rfl) ⟨1364159, by rfl⟩ : syracuseStep 1818879 = 2728319) B2728319
theorem B6136073 : Blo 1817610 6136073 := bstep (se 2 (by rfl) ⟨2301027, by rfl⟩ : syracuseStep 6136073 = 4602055) B4602055
theorem B1818927 : Blo 1817610 1818927 := bstep (se 1 (by rfl) ⟨1364195, by rfl⟩ : syracuseStep 1818927 = 2728391) B2728391
theorem B3498295 : Blo 1817610 3498295 := bstep (se 1 (by rfl) ⟨2623721, by rfl⟩ : syracuseStep 3498295 = 5247443) B5247443
theorem B13803857 : Blo 1817610 13803857 := bstep (se 2 (by rfl) ⟨5176446, by rfl⟩ : syracuseStep 13803857 = 10352893) B10352893
theorem B8298895 : Blo 1817610 8298895 := bstep (se 1 (by rfl) ⟨6224171, by rfl⟩ : syracuseStep 8298895 = 12448343) B12448343
theorem B7373227 : Blo 1817610 7373227 := bstep (se 1 (by rfl) ⟨5529920, by rfl⟩ : syracuseStep 7373227 = 11059841) B11059841
theorem B2728475 : Blo 1817610 2728475 := bstep (se 1 (by rfl) ⟨2046356, by rfl⟩ : syracuseStep 2728475 = 4092713) B4092713
theorem B1819163 : Blo 1817610 1819163 := bstep (se 1 (by rfl) ⟨1364372, by rfl⟩ : syracuseStep 1819163 = 2728745) B2728745
theorem B1819167 : Blo 1817610 1819167 := bstep (se 1 (by rfl) ⟨1364375, by rfl⟩ : syracuseStep 1819167 = 2728751) B2728751
theorem B5177951 : Blo 1817610 5177951 := bstep (se 1 (by rfl) ⟨3883463, by rfl⟩ : syracuseStep 5177951 = 7766927) B7766927
theorem B1819247 : Blo 1817610 1819247 := bstep (se 1 (by rfl) ⟨1364435, by rfl⟩ : syracuseStep 1819247 = 2728871) B2728871
theorem B1819303 : Blo 1817610 1819303 := bstep (se 1 (by rfl) ⟨1364477, by rfl⟩ : syracuseStep 1819303 = 2728955) B2728955
theorem B1942223 : Blo 1817610 1942223 := bstep (se 1 (by rfl) ⟨1456667, by rfl⟩ : syracuseStep 1942223 = 2913335) B2913335
theorem B2728655 : Blo 1817610 2728655 := bstep (se 1 (by rfl) ⟨2046491, by rfl⟩ : syracuseStep 2728655 = 4092983) B4092983
theorem B1819343 : Blo 1817610 1819343 := bstep (se 1 (by rfl) ⟨1364507, by rfl⟩ : syracuseStep 1819343 = 2729015) B2729015
theorem B2728667 : Blo 1817610 2728667 := bstep (se 1 (by rfl) ⟨2046500, by rfl⟩ : syracuseStep 2728667 = 4093001) B4093001
theorem B1819423 : Blo 1817610 1819423 := bstep (se 1 (by rfl) ⟨1364567, by rfl⟩ : syracuseStep 1819423 = 2729135) B2729135
theorem B6554429 : Blo 1817610 6554429 := bstep (se 3 (by rfl) ⟨1228955, by rfl⟩ : syracuseStep 6554429 = 2457911) B2457911
theorem B11650081 : Blo 1817610 11650081 := bstep (se 2 (by rfl) ⟨4368780, by rfl⟩ : syracuseStep 11650081 = 8737561) B8737561
theorem B2729081 : Blo 1817610 2729081 := bstep (se 2 (by rfl) ⟨1023405, by rfl⟩ : syracuseStep 2729081 = 2046811) B2046811
theorem B3884267 : Blo 1817610 3884267 := bstep (se 1 (by rfl) ⟨2913200, by rfl⟩ : syracuseStep 3884267 = 5826401) B5826401
theorem B19653977 : Blo 1817610 19653977 := bstep (se 2 (by rfl) ⟨7370241, by rfl⟩ : syracuseStep 19653977 = 14740483) B14740483
theorem B23315849 : Blo 1817610 23315849 := bstep (se 2 (by rfl) ⟨8743443, by rfl⟩ : syracuseStep 23315849 = 17486887) B17486887
theorem B5826323 : Blo 1817610 5826323 := bstep (se 1 (by rfl) ⟨4369742, by rfl⟩ : syracuseStep 5826323 = 8739485) B8739485
theorem B13813577 : Blo 1817610 13813577 := bstep (se 2 (by rfl) ⟨5180091, by rfl⟩ : syracuseStep 13813577 = 10360183) B10360183
theorem B13281401 : Blo 1817610 13281401 := bstep (se 2 (by rfl) ⟨4980525, by rfl⟩ : syracuseStep 13281401 = 9961051) B9961051
theorem B4089977 : Blo 1817610 4089977 := bstep (se 2 (by rfl) ⟨1533741, by rfl⟩ : syracuseStep 4089977 = 3067483) B3067483
theorem B9201923 : Blo 1817610 9201923 := bstep (se 1 (by rfl) ⟨6901442, by rfl⟩ : syracuseStep 9201923 = 13802885) B13802885
theorem B4368647 : Blo 1817610 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B52431137 : Blo 1817610 52431137 := bstep (se 2 (by rfl) ⟨19661676, by rfl⟩ : syracuseStep 52431137 = 39323353) B39323353
theorem B7768361 : Blo 1817610 7768361 := bstep (se 2 (by rfl) ⟨2913135, by rfl⟩ : syracuseStep 7768361 = 5826271) B5826271
theorem B14740031 : Blo 1817610 14740031 := bstep (se 1 (by rfl) ⟨11055023, by rfl⟩ : syracuseStep 14740031 = 22110047) B22110047
theorem B31935275 : Blo 1817610 31935275 := bstep (se 1 (by rfl) ⟨23951456, by rfl⟩ : syracuseStep 31935275 = 47902913) B47902913
theorem B3885907 : Blo 1817610 3885907 := bstep (se 1 (by rfl) ⟨2914430, by rfl⟩ : syracuseStep 3885907 = 5828861) B5828861
theorem B20712347 : Blo 1817610 20712347 := bstep (se 1 (by rfl) ⟨15534260, by rfl⟩ : syracuseStep 20712347 = 31068521) B31068521
theorem B3738811 : Blo 1817610 3738811 := bstep (se 1 (by rfl) ⟨2804108, by rfl⟩ : syracuseStep 3738811 = 5608217) B5608217
theorem B7769303 : Blo 1817610 7769303 := bstep (se 1 (by rfl) ⟨5826977, by rfl⟩ : syracuseStep 7769303 = 11653955) B11653955
theorem B4091291 : Blo 1817610 4091291 := bstep (se 1 (by rfl) ⟨3068468, by rfl⟩ : syracuseStep 4091291 = 6136937) B6136937
theorem B9457057 : Blo 1817610 9457057 := bstep (se 2 (by rfl) ⟨3546396, by rfl⟩ : syracuseStep 9457057 = 7092793) B7092793
theorem B20721095 : Blo 1817610 20721095 := bstep (se 1 (by rfl) ⟨15540821, by rfl⟩ : syracuseStep 20721095 = 31081643) B31081643
theorem B17485271 : Blo 1817610 17485271 := bstep (se 1 (by rfl) ⟨13113953, by rfl⟩ : syracuseStep 17485271 = 26227907) B26227907
theorem B37334519 : Blo 1817610 37334519 := bstep (se 1 (by rfl) ⟨28000889, by rfl⟩ : syracuseStep 37334519 = 56001779) B56001779
theorem B25579091 : Blo 1817610 25579091 := bstep (se 1 (by rfl) ⟨19184318, by rfl⟩ : syracuseStep 25579091 = 38368637) B38368637
theorem B5828321 : Blo 1817610 5828321 := bstep (se 2 (by rfl) ⟨2185620, by rfl⟩ : syracuseStep 5828321 = 4371241) B4371241
theorem B15535901 : Blo 1817610 15535901 := bstep (se 3 (by rfl) ⟨2912981, by rfl⟩ : syracuseStep 15535901 = 5825963) B5825963
theorem B9203543 : Blo 1817610 9203543 := bstep (se 1 (by rfl) ⟨6902657, by rfl⟩ : syracuseStep 9203543 = 13805315) B13805315
theorem B4091867 : Blo 1817610 4091867 := bstep (se 1 (by rfl) ⟨3068900, by rfl⟩ : syracuseStep 4091867 = 6137801) B6137801
theorem B9203705 : Blo 1817610 9203705 := bstep (se 2 (by rfl) ⟨3451389, by rfl⟩ : syracuseStep 9203705 = 6902779) B6902779
theorem B4092047 : Blo 1817610 4092047 := bstep (se 1 (by rfl) ⟨3069035, by rfl⟩ : syracuseStep 4092047 = 6138071) B6138071
theorem B13816007 : Blo 1817610 13816007 := bstep (se 1 (by rfl) ⟨10362005, by rfl⟩ : syracuseStep 13816007 = 20724011) B20724011
theorem B4092137 : Blo 1817610 4092137 := bstep (se 2 (by rfl) ⟨1534551, by rfl⟩ : syracuseStep 4092137 = 3069103) B3069103
theorem B12439889 : Blo 1817610 12439889 := bstep (se 2 (by rfl) ⟨4664958, by rfl⟩ : syracuseStep 12439889 = 9329917) B9329917
theorem B4092263 : Blo 1817610 4092263 := bstep (se 1 (by rfl) ⟨3069197, by rfl⟩ : syracuseStep 4092263 = 6138395) B6138395
theorem B44233123 : Blo 1817610 44233123 := bstep (se 1 (by rfl) ⟨33174842, by rfl⟩ : syracuseStep 44233123 = 66349685) B66349685
theorem B7770617 : Blo 1817610 7770617 := bstep (se 2 (by rfl) ⟨2913981, by rfl⟩ : syracuseStep 7770617 = 5827963) B5827963
theorem B13464103 : Blo 1817610 13464103 := bstep (se 1 (by rfl) ⟨10098077, by rfl⟩ : syracuseStep 13464103 = 20196155) B20196155
theorem B9204353 : Blo 1817610 9204353 := bstep (se 2 (by rfl) ⟨3451632, by rfl⟩ : syracuseStep 9204353 = 6903265) B6903265
theorem B3453691 : Blo 1817610 3453691 := bstep (se 1 (by rfl) ⟨2590268, by rfl⟩ : syracuseStep 3453691 = 5180537) B5180537
theorem B2044831 : Blo 1817610 2044831 := bstep (se 1 (by rfl) ⟨1533623, by rfl⟩ : syracuseStep 2044831 = 3067247) B3067247
theorem B4092839 : Blo 1817610 4092839 := bstep (se 1 (by rfl) ⟨3069629, by rfl⟩ : syracuseStep 4092839 = 6139259) B6139259
theorem B6140879 : Blo 1817610 6140879 := bstep (se 1 (by rfl) ⟨4605659, by rfl⟩ : syracuseStep 6140879 = 9211319) B9211319
theorem B6902765 : Blo 1817610 6902765 := bstep (se 3 (by rfl) ⟨1294268, by rfl⟩ : syracuseStep 6902765 = 2588537) B2588537
theorem B16593923 : Blo 1817610 16593923 := bstep (se 1 (by rfl) ⟨12445442, by rfl⟩ : syracuseStep 16593923 = 24890885) B24890885
theorem B6140987 : Blo 1817610 6140987 := bstep (se 1 (by rfl) ⟨4605740, by rfl⟩ : syracuseStep 6140987 = 9211481) B9211481
theorem B13808717 : Blo 1817610 13808717 := bstep (se 3 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 13808717 = 5178269) B5178269
theorem B2045083 : Blo 1817610 2045083 := bstep (se 1 (by rfl) ⟨1533812, by rfl⟩ : syracuseStep 2045083 = 3067625) B3067625
theorem B3069083 : Blo 1817610 3069083 := bstep (se 1 (by rfl) ⟨2301812, by rfl⟩ : syracuseStep 3069083 = 4603625) B4603625
theorem B20706515 : Blo 1817610 20706515 := bstep (se 1 (by rfl) ⟨15529886, by rfl⟩ : syracuseStep 20706515 = 31059773) B31059773
theorem B4601083 : Blo 1817610 4601083 := bstep (se 1 (by rfl) ⟨3450812, by rfl⟩ : syracuseStep 4601083 = 6901625) B6901625
theorem B6641003 : Blo 1817610 6641003 := bstep (se 1 (by rfl) ⟨4980752, by rfl⟩ : syracuseStep 6641003 = 9961505) B9961505
theorem B11064683 : Blo 1817610 11064683 := bstep (se 1 (by rfl) ⟨8298512, by rfl⟩ : syracuseStep 11064683 = 16597025) B16597025
theorem B9205163 : Blo 1817610 9205163 := bstep (se 1 (by rfl) ⟨6903872, by rfl⟩ : syracuseStep 9205163 = 13807745) B13807745
theorem B13817465 : Blo 1817610 13817465 := bstep (se 2 (by rfl) ⟨5181549, by rfl⟩ : syracuseStep 13817465 = 10363099) B10363099
theorem B2045767 : Blo 1817610 2045767 := bstep (se 1 (by rfl) ⟨1534325, by rfl⟩ : syracuseStep 2045767 = 3068651) B3068651
theorem B4093775 : Blo 1817610 4093775 := bstep (se 1 (by rfl) ⟨3070331, by rfl⟩ : syracuseStep 4093775 = 6140663) B6140663
theorem B9328603 : Blo 1817610 9328603 := bstep (se 1 (by rfl) ⟨6996452, by rfl⟩ : syracuseStep 9328603 = 13992905) B13992905
theorem B73808243 : Blo 1817610 73808243 := bstep (se 1 (by rfl) ⟨55356182, by rfl⟩ : syracuseStep 73808243 = 110712365) B110712365
theorem B6904223 : Blo 1817610 6904223 := bstep (se 1 (by rfl) ⟨5178167, by rfl⟩ : syracuseStep 6904223 = 10356335) B10356335
theorem B3938719 : Blo 1817610 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B2046415 : Blo 1817610 2046415 := bstep (se 1 (by rfl) ⟨1534811, by rfl⟩ : syracuseStep 2046415 = 3069623) B3069623
theorem B15538877 : Blo 1817610 15538877 := bstep (se 3 (by rfl) ⟨2913539, by rfl⟩ : syracuseStep 15538877 = 5827079) B5827079
theorem B7683325 : Blo 1817610 7683325 := bstep (se 3 (by rfl) ⟨1440623, by rfl⟩ : syracuseStep 7683325 = 2881247) B2881247
theorem B28769033 : Blo 1817610 28769033 := bstep (se 2 (by rfl) ⟨10788387, by rfl⟩ : syracuseStep 28769033 = 21576775) B21576775
theorem B6134831 : Blo 1817610 6134831 := bstep (se 1 (by rfl) ⟨4601123, by rfl⟩ : syracuseStep 6134831 = 9202247) B9202247
theorem B15965261 : Blo 1817610 15965261 := bstep (se 3 (by rfl) ⟨2993486, by rfl⟩ : syracuseStep 15965261 = 5986973) B5986973
theorem B1817691 : Blo 1817610 1817691 := bstep (se 1 (by rfl) ⟨1363268, by rfl⟩ : syracuseStep 1817691 = 2726537) B2726537
theorem B1817807 : Blo 1817610 1817807 := bstep (se 1 (by rfl) ⟨1363355, by rfl⟩ : syracuseStep 1817807 = 2726711) B2726711
theorem B2727119 : Blo 1817610 2727119 := bstep (se 1 (by rfl) ⟨2045339, by rfl⟩ : syracuseStep 2727119 = 4090679) B4090679
theorem B1817831 : Blo 1817610 1817831 := bstep (se 1 (by rfl) ⟨1363373, by rfl⟩ : syracuseStep 1817831 = 2726747) B2726747
theorem B1817927 : Blo 1817610 1817927 := bstep (se 1 (by rfl) ⟨1363445, by rfl⟩ : syracuseStep 1817927 = 2726891) B2726891
theorem B2727239 : Blo 1817610 2727239 := bstep (se 1 (by rfl) ⟨2045429, by rfl⟩ : syracuseStep 2727239 = 4090859) B4090859
theorem B13999457 : Blo 1817610 13999457 := bstep (se 2 (by rfl) ⟨5249796, by rfl⟩ : syracuseStep 13999457 = 10499593) B10499593
theorem B6905195 : Blo 1817610 6905195 := bstep (se 1 (by rfl) ⟨5178896, by rfl⟩ : syracuseStep 6905195 = 10357793) B10357793
theorem B13811147 : Blo 1817610 13811147 := bstep (se 1 (by rfl) ⟨10358360, by rfl⟩ : syracuseStep 13811147 = 20716721) B20716721
theorem B1818063 : Blo 1817610 1818063 := bstep (se 1 (by rfl) ⟨1363547, by rfl⟩ : syracuseStep 1818063 = 2727095) B2727095
theorem B2727401 : Blo 1817610 2727401 := bstep (se 2 (by rfl) ⟨1022775, by rfl⟩ : syracuseStep 2727401 = 2045551) B2045551
theorem B15531527 : Blo 1817610 15531527 := bstep (se 1 (by rfl) ⟨11648645, by rfl⟩ : syracuseStep 15531527 = 23297291) B23297291
theorem B1818223 : Blo 1817610 1818223 := bstep (se 1 (by rfl) ⟨1363667, by rfl⟩ : syracuseStep 1818223 = 2727335) B2727335
theorem B2727545 : Blo 1817610 2727545 := bstep (se 2 (by rfl) ⟨1022829, by rfl⟩ : syracuseStep 2727545 = 2045659) B2045659
theorem B1818279 : Blo 1817610 1818279 := bstep (se 1 (by rfl) ⟨1363709, by rfl⟩ : syracuseStep 1818279 = 2727419) B2727419
theorem B2588383 : Blo 1817610 2588383 := bstep (se 1 (by rfl) ⟨1941287, by rfl⟩ : syracuseStep 2588383 = 3882575) B3882575
theorem B1818343 : Blo 1817610 1818343 := bstep (se 1 (by rfl) ⟨1363757, by rfl⟩ : syracuseStep 1818343 = 2727515) B2727515
theorem B1818399 : Blo 1817610 1818399 := bstep (se 1 (by rfl) ⟨1363799, by rfl⟩ : syracuseStep 1818399 = 2727599) B2727599
theorem B17481581 : Blo 1817610 17481581 := bstep (se 3 (by rfl) ⟨3277796, by rfl⟩ : syracuseStep 17481581 = 6555593) B6555593
theorem B1818479 : Blo 1817610 1818479 := bstep (se 1 (by rfl) ⟨1363859, by rfl⟩ : syracuseStep 1818479 = 2727719) B2727719
theorem B2727791 : Blo 1817610 2727791 := bstep (se 1 (by rfl) ⟨2045843, by rfl⟩ : syracuseStep 2727791 = 4091687) B4091687
theorem B1818535 : Blo 1817610 1818535 := bstep (se 1 (by rfl) ⟨1363901, by rfl⟩ : syracuseStep 1818535 = 2727803) B2727803
theorem B2728031 : Blo 1817610 2728031 := bstep (se 1 (by rfl) ⟨2046023, by rfl⟩ : syracuseStep 2728031 = 4092047) B4092047
theorem B2728091 : Blo 1817610 2728091 := bstep (se 1 (by rfl) ⟨2046068, by rfl⟩ : syracuseStep 2728091 = 4092137) B4092137
theorem B2728175 : Blo 1817610 2728175 := bstep (se 1 (by rfl) ⟨2046131, by rfl⟩ : syracuseStep 2728175 = 4092263) B4092263
theorem B1818983 : Blo 1817610 1818983 := bstep (se 1 (by rfl) ⟨1364237, by rfl⟩ : syracuseStep 1818983 = 2728475) B2728475
theorem B6136235 : Blo 1817610 6136235 := bstep (se 1 (by rfl) ⟨4602176, by rfl⟩ : syracuseStep 6136235 = 9204353) B9204353
theorem B1819103 : Blo 1817610 1819103 := bstep (se 1 (by rfl) ⟨1364327, by rfl⟩ : syracuseStep 1819103 = 2728655) B2728655
theorem B1819111 : Blo 1817610 1819111 := bstep (se 1 (by rfl) ⟨1364333, by rfl⟩ : syracuseStep 1819111 = 2728667) B2728667
theorem B5251625 : Blo 1817610 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B9830969 : Blo 1817610 9830969 := bstep (se 2 (by rfl) ⟨3686613, by rfl⟩ : syracuseStep 9830969 = 7373227) B7373227
theorem B2728553 : Blo 1817610 2728553 := bstep (se 2 (by rfl) ⟨1023207, by rfl⟩ : syracuseStep 2728553 = 2046415) B2046415
theorem B2728559 : Blo 1817610 2728559 := bstep (se 1 (by rfl) ⟨2046419, by rfl⟩ : syracuseStep 2728559 = 4092839) B4092839
theorem B1819387 : Blo 1817610 1819387 := bstep (se 1 (by rfl) ⟨1364540, by rfl⟩ : syracuseStep 1819387 = 2729081) B2729081
theorem B13804343 : Blo 1817610 13804343 := bstep (se 1 (by rfl) ⟨10353257, by rfl⟩ : syracuseStep 13804343 = 20706515) B20706515
theorem B2589511 : Blo 1817610 2589511 := bstep (se 1 (by rfl) ⟨1942133, by rfl⟩ : syracuseStep 2589511 = 3884267) B3884267
theorem B37331885 : Blo 1817610 37331885 := bstep (se 3 (by rfl) ⟨6999728, by rfl⟩ : syracuseStep 37331885 = 13999457) B13999457
theorem B6136775 : Blo 1817610 6136775 := bstep (se 1 (by rfl) ⟨4602581, by rfl⟩ : syracuseStep 6136775 = 9205163) B9205163
theorem B4604921 : Blo 1817610 4604921 := bstep (se 2 (by rfl) ⟨1726845, by rfl⟩ : syracuseStep 4604921 = 3453691) B3453691
theorem B3884215 : Blo 1817610 3884215 := bstep (se 1 (by rfl) ⟨2913161, by rfl⟩ : syracuseStep 3884215 = 5826323) B5826323
theorem B9209051 : Blo 1817610 9209051 := bstep (se 1 (by rfl) ⟨6906788, by rfl⟩ : syracuseStep 9209051 = 13813577) B13813577
theorem B2729183 : Blo 1817610 2729183 := bstep (se 1 (by rfl) ⟨2046887, by rfl⟩ : syracuseStep 2729183 = 4093775) B4093775
theorem B40977733 : Blo 1817610 40977733 := bstep (se 4 (by rfl) ⟨3841662, by rfl⟩ : syracuseStep 40977733 = 7683325) B7683325
theorem B15533441 : Blo 1817610 15533441 := bstep (se 2 (by rfl) ⟨5825040, by rfl⟩ : syracuseStep 15533441 = 11650081) B11650081
theorem B5178907 : Blo 1817610 5178907 := bstep (se 1 (by rfl) ⟨3884180, by rfl⟩ : syracuseStep 5178907 = 7768361) B7768361
theorem B19179355 : Blo 1817610 19179355 := bstep (se 1 (by rfl) ⟨14384516, by rfl⟩ : syracuseStep 19179355 = 28769033) B28769033
theorem B5179261 : Blo 1817610 5179261 := bstep (se 3 (by rfl) ⟨971111, by rfl⟩ : syracuseStep 5179261 = 1942223) B1942223
theorem B12609409 : Blo 1817610 12609409 := bstep (se 2 (by rfl) ⟨4728528, by rfl⟩ : syracuseStep 12609409 = 9457057) B9457057
theorem B15542189 : Blo 1817610 15542189 := bstep (se 3 (by rfl) ⟨2914160, by rfl⟩ : syracuseStep 15542189 = 5828321) B5828321
theorem B4089887 : Blo 1817610 4089887 := bstep (se 1 (by rfl) ⟨3067415, by rfl⟩ : syracuseStep 4089887 = 6134831) B6134831
theorem B10643507 : Blo 1817610 10643507 := bstep (se 1 (by rfl) ⟨7982630, by rfl⟩ : syracuseStep 10643507 = 15965261) B15965261
theorem B5179535 : Blo 1817610 5179535 := bstep (se 1 (by rfl) ⟨3884651, by rfl⟩ : syracuseStep 5179535 = 7769303) B7769303
theorem B3451177 : Blo 1817610 3451177 := bstep (se 2 (by rfl) ⟨1294191, by rfl⟩ : syracuseStep 3451177 = 2588383) B2588383
theorem B13814063 : Blo 1817610 13814063 := bstep (se 1 (by rfl) ⟨10360547, by rfl⟩ : syracuseStep 13814063 = 20721095) B20721095
theorem B24889679 : Blo 1817610 24889679 := bstep (se 1 (by rfl) ⟨18667259, by rfl⟩ : syracuseStep 24889679 = 37334519) B37334519
theorem B10357267 : Blo 1817610 10357267 := bstep (se 1 (by rfl) ⟨7767950, by rfl⟩ : syracuseStep 10357267 = 15535901) B15535901
theorem B12438137 : Blo 1817610 12438137 := bstep (se 2 (by rfl) ⟨4664301, by rfl⟩ : syracuseStep 12438137 = 9328603) B9328603
theorem B9210671 : Blo 1817610 9210671 := bstep (se 1 (by rfl) ⟨6908003, by rfl⟩ : syracuseStep 9210671 = 13816007) B13816007
theorem B4090715 : Blo 1817610 4090715 := bstep (se 1 (by rfl) ⟨3068036, by rfl⟩ : syracuseStep 4090715 = 6136073) B6136073
theorem B9202571 : Blo 1817610 9202571 := bstep (se 1 (by rfl) ⟨6901928, by rfl⟩ : syracuseStep 9202571 = 13803857) B13803857
theorem B8293259 : Blo 1817610 8293259 := bstep (se 1 (by rfl) ⟨6219944, by rfl⟩ : syracuseStep 8293259 = 12439889) B12439889
theorem B5180411 : Blo 1817610 5180411 := bstep (se 1 (by rfl) ⟨3885308, by rfl⟩ : syracuseStep 5180411 = 7770617) B7770617
theorem B3451967 : Blo 1817610 3451967 := bstep (se 1 (by rfl) ⟨2588975, by rfl⟩ : syracuseStep 3451967 = 5177951) B5177951
theorem B4664393 : Blo 1817610 4664393 := bstep (se 2 (by rfl) ⟨1749147, by rfl⟩ : syracuseStep 4664393 = 3498295) B3498295
theorem B4369619 : Blo 1817610 4369619 := bstep (se 1 (by rfl) ⟨3277214, by rfl⟩ : syracuseStep 4369619 = 6554429) B6554429
theorem B58977497 : Blo 1817610 58977497 := bstep (se 2 (by rfl) ⟨22116561, by rfl⟩ : syracuseStep 58977497 = 44233123) B44233123
theorem B17952137 : Blo 1817610 17952137 := bstep (se 2 (by rfl) ⟨6732051, by rfl⟩ : syracuseStep 17952137 = 13464103) B13464103
theorem B13102651 : Blo 1817610 13102651 := bstep (se 1 (by rfl) ⟨9826988, by rfl⟩ : syracuseStep 13102651 = 19653977) B19653977
theorem B4427335 : Blo 1817610 4427335 := bstep (se 1 (by rfl) ⟨3320501, by rfl⟩ : syracuseStep 4427335 = 6641003) B6641003
theorem B7376455 : Blo 1817610 7376455 := bstep (se 1 (by rfl) ⟨5532341, by rfl⟩ : syracuseStep 7376455 = 11064683) B11064683
theorem B15543899 : Blo 1817610 15543899 := bstep (se 1 (by rfl) ⟨11657924, by rfl⟩ : syracuseStep 15543899 = 23315849) B23315849
theorem B9211643 : Blo 1817610 9211643 := bstep (se 1 (by rfl) ⟨6908732, by rfl⟩ : syracuseStep 9211643 = 13817465) B13817465
theorem B5181209 : Blo 1817610 5181209 := bstep (se 2 (by rfl) ⟨1942953, by rfl⟩ : syracuseStep 5181209 = 3885907) B3885907
theorem B2912431 : Blo 1817610 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B49205495 : Blo 1817610 49205495 := bstep (se 1 (by rfl) ⟨36904121, by rfl⟩ : syracuseStep 49205495 = 73808243) B73808243
theorem B4985081 : Blo 1817610 4985081 := bstep (se 2 (by rfl) ⟨1869405, by rfl⟩ : syracuseStep 4985081 = 3738811) B3738811
theorem B9826687 : Blo 1817610 9826687 := bstep (se 1 (by rfl) ⟨7370015, by rfl⟩ : syracuseStep 9826687 = 14740031) B14740031
theorem B10359251 : Blo 1817610 10359251 := bstep (se 1 (by rfl) ⟨7769438, by rfl⟩ : syracuseStep 10359251 = 15538877) B15538877
theorem B13808231 : Blo 1817610 13808231 := bstep (se 1 (by rfl) ⟨10356173, by rfl⟩ : syracuseStep 13808231 = 20712347) B20712347
theorem B17052727 : Blo 1817610 17052727 := bstep (se 1 (by rfl) ⟨12789545, by rfl⟩ : syracuseStep 17052727 = 25579091) B25579091
theorem B11654387 : Blo 1817610 11654387 := bstep (se 1 (by rfl) ⟨8740790, by rfl⟩ : syracuseStep 11654387 = 17481581) B17481581
theorem B44250461 : Blo 1817610 44250461 := bstep (se 3 (by rfl) ⟨8296961, by rfl⟩ : syracuseStep 44250461 = 16593923) B16593923
theorem B11065193 : Blo 1817610 11065193 := bstep (se 2 (by rfl) ⟨4149447, by rfl⟩ : syracuseStep 11065193 = 8298895) B8298895
theorem B31479677 : Blo 1817610 31479677 := bstep (se 3 (by rfl) ⟨5902439, by rfl⟩ : syracuseStep 31479677 = 11804879) B11804879
theorem B4093919 : Blo 1817610 4093919 := bstep (se 1 (by rfl) ⟨3070439, by rfl⟩ : syracuseStep 4093919 = 6140879) B6140879
theorem B4601843 : Blo 1817610 4601843 := bstep (se 1 (by rfl) ⟨3451382, by rfl⟩ : syracuseStep 4601843 = 6902765) B6902765
theorem B4093991 : Blo 1817610 4093991 := bstep (se 1 (by rfl) ⟨3070493, by rfl⟩ : syracuseStep 4093991 = 6140987) B6140987
theorem B9205811 : Blo 1817610 9205811 := bstep (se 1 (by rfl) ⟨6904358, by rfl⟩ : syracuseStep 9205811 = 13808717) B13808717
theorem B2046055 : Blo 1817610 2046055 := bstep (se 1 (by rfl) ⟨1534541, by rfl⟩ : syracuseStep 2046055 = 3069083) B3069083
theorem B2726441 : Blo 1817610 2726441 := bstep (se 2 (by rfl) ⟨1022415, by rfl⟩ : syracuseStep 2726441 = 2044831) B2044831
theorem B8854267 : Blo 1817610 8854267 := bstep (se 1 (by rfl) ⟨6640700, by rfl⟩ : syracuseStep 8854267 = 13281401) B13281401
theorem B2726651 : Blo 1817610 2726651 := bstep (se 1 (by rfl) ⟨2044988, by rfl⟩ : syracuseStep 2726651 = 4089977) B4089977
theorem B6134615 : Blo 1817610 6134615 := bstep (se 1 (by rfl) ⟨4600961, by rfl⟩ : syracuseStep 6134615 = 9201923) B9201923
theorem B34954091 : Blo 1817610 34954091 := bstep (se 1 (by rfl) ⟨26215568, by rfl⟩ : syracuseStep 34954091 = 52431137) B52431137
theorem B2726777 : Blo 1817610 2726777 := bstep (se 2 (by rfl) ⟨1022541, by rfl⟩ : syracuseStep 2726777 = 2045083) B2045083
theorem B4602815 : Blo 1817610 4602815 := bstep (se 1 (by rfl) ⟨3452111, by rfl⟩ : syracuseStep 4602815 = 6904223) B6904223
theorem B6134777 : Blo 1817610 6134777 := bstep (se 2 (by rfl) ⟨2300541, by rfl⟩ : syracuseStep 6134777 = 4601083) B4601083
theorem B21290183 : Blo 1817610 21290183 := bstep (se 1 (by rfl) ⟨15967637, by rfl⟩ : syracuseStep 21290183 = 31935275) B31935275
theorem B1818079 : Blo 1817610 1818079 := bstep (se 1 (by rfl) ⟨1363559, by rfl⟩ : syracuseStep 1818079 = 2727119) B2727119
theorem B1818159 : Blo 1817610 1818159 := bstep (se 1 (by rfl) ⟨1363619, by rfl⟩ : syracuseStep 1818159 = 2727239) B2727239
theorem B4603463 : Blo 1817610 4603463 := bstep (se 1 (by rfl) ⟨3452597, by rfl⟩ : syracuseStep 4603463 = 6905195) B6905195
theorem B2727527 : Blo 1817610 2727527 := bstep (se 1 (by rfl) ⟨2045645, by rfl⟩ : syracuseStep 2727527 = 4091291) B4091291
theorem B9207431 : Blo 1817610 9207431 := bstep (se 1 (by rfl) ⟨6905573, by rfl⟩ : syracuseStep 9207431 = 13811147) B13811147
theorem B11656847 : Blo 1817610 11656847 := bstep (se 1 (by rfl) ⟨8742635, by rfl⟩ : syracuseStep 11656847 = 17485271) B17485271
theorem B1818267 : Blo 1817610 1818267 := bstep (se 1 (by rfl) ⟨1363700, by rfl⟩ : syracuseStep 1818267 = 2727401) B2727401
theorem B10354351 : Blo 1817610 10354351 := bstep (se 1 (by rfl) ⟨7765763, by rfl⟩ : syracuseStep 10354351 = 15531527) B15531527
theorem B1818363 : Blo 1817610 1818363 := bstep (se 1 (by rfl) ⟨1363772, by rfl⟩ : syracuseStep 1818363 = 2727545) B2727545
theorem B2727689 : Blo 1817610 2727689 := bstep (se 2 (by rfl) ⟨1022883, by rfl⟩ : syracuseStep 2727689 = 2045767) B2045767
theorem B6135695 : Blo 1817610 6135695 := bstep (se 1 (by rfl) ⟨4601771, by rfl⟩ : syracuseStep 6135695 = 9203543) B9203543
theorem B1818527 : Blo 1817610 1818527 := bstep (se 1 (by rfl) ⟨1363895, by rfl⟩ : syracuseStep 1818527 = 2727791) B2727791
theorem B2727911 : Blo 1817610 2727911 := bstep (se 1 (by rfl) ⟨2045933, by rfl⟩ : syracuseStep 2727911 = 4091867) B4091867
theorem B6135803 : Blo 1817610 6135803 := bstep (se 1 (by rfl) ⟨4601852, by rfl⟩ : syracuseStep 6135803 = 9203705) B9203705
theorem B1818687 : Blo 1817610 1818687 := bstep (se 1 (by rfl) ⟨1364015, by rfl⟩ : syracuseStep 1818687 = 2728031) B2728031
theorem B1818727 : Blo 1817610 1818727 := bstep (se 1 (by rfl) ⟨1364045, by rfl⟩ : syracuseStep 1818727 = 2728091) B2728091
theorem B2728073 : Blo 1817610 2728073 := bstep (se 2 (by rfl) ⟨1023027, by rfl⟩ : syracuseStep 2728073 = 2046055) B2046055
theorem B1818783 : Blo 1817610 1818783 := bstep (se 1 (by rfl) ⟨1364087, by rfl⟩ : syracuseStep 1818783 = 2728175) B2728175
theorem B3883241 : Blo 1817610 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B6906167 : Blo 1817610 6906167 := bstep (se 1 (by rfl) ⟨5179625, by rfl⟩ : syracuseStep 6906167 = 10359251) B10359251
theorem B6553979 : Blo 1817610 6553979 := bstep (se 1 (by rfl) ⟨4915484, by rfl⟩ : syracuseStep 6553979 = 9830969) B9830969
theorem B1819035 : Blo 1817610 1819035 := bstep (se 1 (by rfl) ⟨1364276, by rfl⟩ : syracuseStep 1819035 = 2728553) B2728553
theorem B1819039 : Blo 1817610 1819039 := bstep (se 1 (by rfl) ⟨1364279, by rfl⟩ : syracuseStep 1819039 = 2728559) B2728559
theorem B1819455 : Blo 1817610 1819455 := bstep (se 1 (by rfl) ⟨1364591, by rfl⟩ : syracuseStep 1819455 = 2729183) B2729183
theorem B29500307 : Blo 1817610 29500307 := bstep (se 1 (by rfl) ⟨22125230, by rfl⟩ : syracuseStep 29500307 = 44250461) B44250461
theorem B10355627 : Blo 1817610 10355627 := bstep (se 1 (by rfl) ⟨7766720, by rfl⟩ : syracuseStep 10355627 = 15533441) B15533441
theorem B11805689 : Blo 1817610 11805689 := bstep (se 2 (by rfl) ⟨4427133, by rfl⟩ : syracuseStep 11805689 = 8854267) B8854267
theorem B2729279 : Blo 1817610 2729279 := bstep (se 1 (by rfl) ⟨2046959, by rfl⟩ : syracuseStep 2729279 = 4093919) B4093919
theorem B2729327 : Blo 1817610 2729327 := bstep (se 1 (by rfl) ⟨2046995, by rfl⟩ : syracuseStep 2729327 = 4093991) B4093991
theorem B6137207 : Blo 1817610 6137207 := bstep (se 1 (by rfl) ⟨4602905, by rfl⟩ : syracuseStep 6137207 = 9205811) B9205811
theorem B7095671 : Blo 1817610 7095671 := bstep (se 1 (by rfl) ⟨5321753, by rfl⟩ : syracuseStep 7095671 = 10643507) B10643507
theorem B9209375 : Blo 1817610 9209375 := bstep (se 1 (by rfl) ⟨6907031, by rfl⟩ : syracuseStep 9209375 = 13814063) B13814063
theorem B5178953 : Blo 1817610 5178953 := bstep (se 2 (by rfl) ⟨1942107, by rfl⟩ : syracuseStep 5178953 = 3884215) B3884215
theorem B8292091 : Blo 1817610 8292091 := bstep (se 1 (by rfl) ⟨6219068, by rfl⟩ : syracuseStep 8292091 = 12438137) B12438137
theorem B4089743 : Blo 1817610 4089743 := bstep (se 1 (by rfl) ⟨3067307, by rfl⟩ : syracuseStep 4089743 = 6134615) B6134615
theorem B4089851 : Blo 1817610 4089851 := bstep (se 1 (by rfl) ⟨3067388, by rfl⟩ : syracuseStep 4089851 = 6134777) B6134777
theorem B13805801 : Blo 1817610 13805801 := bstep (se 2 (by rfl) ⟨5177175, by rfl⟩ : syracuseStep 13805801 = 10354351) B10354351
theorem B6138287 : Blo 1817610 6138287 := bstep (se 1 (by rfl) ⟨4603715, by rfl⟩ : syracuseStep 6138287 = 9207431) B9207431
theorem B99551693 : Blo 1817610 99551693 := bstep (se 3 (by rfl) ⟨18665942, by rfl⟩ : syracuseStep 99551693 = 37331885) B37331885
theorem B16812545 : Blo 1817610 16812545 := bstep (se 2 (by rfl) ⟨6304704, by rfl⟩ : syracuseStep 16812545 = 12609409) B12609409
theorem B4090463 : Blo 1817610 4090463 := bstep (se 1 (by rfl) ⟨3067847, by rfl⟩ : syracuseStep 4090463 = 6135695) B6135695
theorem B4090535 : Blo 1817610 4090535 := bstep (se 1 (by rfl) ⟨3067901, by rfl⟩ : syracuseStep 4090535 = 6135803) B6135803
theorem B32803663 : Blo 1817610 32803663 := bstep (se 1 (by rfl) ⟨24602747, by rfl⟩ : syracuseStep 32803663 = 49205495) B49205495
theorem B4090823 : Blo 1817610 4090823 := bstep (se 1 (by rfl) ⟨3068117, by rfl⟩ : syracuseStep 4090823 = 6136235) B6136235
theorem B3501083 : Blo 1817610 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B13102249 : Blo 1817610 13102249 := bstep (se 2 (by rfl) ⟨4913343, by rfl⟩ : syracuseStep 13102249 = 9826687) B9826687
theorem B9202895 : Blo 1817610 9202895 := bstep (se 1 (by rfl) ⟨6902171, by rfl⟩ : syracuseStep 9202895 = 13804343) B13804343
theorem B4091183 : Blo 1817610 4091183 := bstep (se 1 (by rfl) ⟨3068387, by rfl⟩ : syracuseStep 4091183 = 6136775) B6136775
theorem B6139367 : Blo 1817610 6139367 := bstep (se 1 (by rfl) ⟨4604525, by rfl⟩ : syracuseStep 6139367 = 9209051) B9209051
theorem B7769591 : Blo 1817610 7769591 := bstep (se 1 (by rfl) ⟨5827193, by rfl⟩ : syracuseStep 7769591 = 11654387) B11654387
theorem B3452681 : Blo 1817610 3452681 := bstep (se 2 (by rfl) ⟨1294755, by rfl⟩ : syracuseStep 3452681 = 2589511) B2589511
theorem B7376795 : Blo 1817610 7376795 := bstep (se 1 (by rfl) ⟨5532596, by rfl⟩ : syracuseStep 7376795 = 11065193) B11065193
theorem B3067895 : Blo 1817610 3067895 := bstep (se 1 (by rfl) ⟨2300921, by rfl⟩ : syracuseStep 3067895 = 4601843) B4601843
theorem B22736969 : Blo 1817610 22736969 := bstep (se 2 (by rfl) ⟨8526363, by rfl⟩ : syracuseStep 22736969 = 17052727) B17052727
theorem B3453023 : Blo 1817610 3453023 := bstep (se 1 (by rfl) ⟨2589767, by rfl⟩ : syracuseStep 3453023 = 5179535) B5179535
theorem B16593119 : Blo 1817610 16593119 := bstep (se 1 (by rfl) ⟨12444839, by rfl⟩ : syracuseStep 16593119 = 24889679) B24889679
theorem B54636977 : Blo 1817610 54636977 := bstep (se 2 (by rfl) ⟨20488866, by rfl⟩ : syracuseStep 54636977 = 40977733) B40977733
theorem B6140447 : Blo 1817610 6140447 := bstep (se 1 (by rfl) ⟨4605335, by rfl⟩ : syracuseStep 6140447 = 9210671) B9210671
theorem B23302727 : Blo 1817610 23302727 := bstep (se 1 (by rfl) ⟨17477045, by rfl⟩ : syracuseStep 23302727 = 34954091) B34954091
theorem B3068543 : Blo 1817610 3068543 := bstep (se 1 (by rfl) ⟨2301407, by rfl⟩ : syracuseStep 3068543 = 4602815) B4602815
theorem B3453607 : Blo 1817610 3453607 := bstep (se 1 (by rfl) ⟨2590205, by rfl⟩ : syracuseStep 3453607 = 5180411) B5180411
theorem B3109595 : Blo 1817610 3109595 := bstep (se 1 (by rfl) ⟨2332196, by rfl⟩ : syracuseStep 3109595 = 4664393) B4664393
theorem B17470201 : Blo 1817610 17470201 := bstep (se 2 (by rfl) ⟨6551325, by rfl⟩ : syracuseStep 17470201 = 13102651) B13102651
theorem B5903113 : Blo 1817610 5903113 := bstep (se 2 (by rfl) ⟨2213667, by rfl⟩ : syracuseStep 5903113 = 4427335) B4427335
theorem B9835273 : Blo 1817610 9835273 := bstep (se 2 (by rfl) ⟨3688227, by rfl⟩ : syracuseStep 9835273 = 7376455) B7376455
theorem B14193455 : Blo 1817610 14193455 := bstep (se 1 (by rfl) ⟨10645091, by rfl⟩ : syracuseStep 14193455 = 21290183) B21290183
theorem B2913079 : Blo 1817610 2913079 := bstep (se 1 (by rfl) ⟨2184809, by rfl⟩ : syracuseStep 2913079 = 4369619) B4369619
theorem B39318331 : Blo 1817610 39318331 := bstep (se 1 (by rfl) ⟨29488748, by rfl⟩ : syracuseStep 39318331 = 58977497) B58977497
theorem B3068975 : Blo 1817610 3068975 := bstep (se 1 (by rfl) ⟨2301731, by rfl⟩ : syracuseStep 3068975 = 4603463) B4603463
theorem B7771231 : Blo 1817610 7771231 := bstep (se 1 (by rfl) ⟨5828423, by rfl⟩ : syracuseStep 7771231 = 11656847) B11656847
theorem B25572473 : Blo 1817610 25572473 := bstep (se 2 (by rfl) ⟨9589677, by rfl⟩ : syracuseStep 25572473 = 19179355) B19179355
theorem B6141095 : Blo 1817610 6141095 := bstep (se 1 (by rfl) ⟨4605821, by rfl⟩ : syracuseStep 6141095 = 9211643) B9211643
theorem B3454139 : Blo 1817610 3454139 := bstep (se 1 (by rfl) ⟨2590604, by rfl⟩ : syracuseStep 3454139 = 5181209) B5181209
theorem B3323387 : Blo 1817610 3323387 := bstep (se 1 (by rfl) ⟨2492540, by rfl⟩ : syracuseStep 3323387 = 4985081) B4985081
theorem B4601569 : Blo 1817610 4601569 := bstep (se 2 (by rfl) ⟨1725588, by rfl⟩ : syracuseStep 4601569 = 3451177) B3451177
theorem B9205487 : Blo 1817610 9205487 := bstep (se 1 (by rfl) ⟨6904115, by rfl⟩ : syracuseStep 9205487 = 13808231) B13808231
theorem B3069947 : Blo 1817610 3069947 := bstep (se 1 (by rfl) ⟨2302460, by rfl⟩ : syracuseStep 3069947 = 4604921) B4604921
theorem B13809689 : Blo 1817610 13809689 := bstep (se 2 (by rfl) ⟨5178633, by rfl⟩ : syracuseStep 13809689 = 10357267) B10357267
theorem B20986451 : Blo 1817610 20986451 := bstep (se 1 (by rfl) ⟨15739838, by rfl⟩ : syracuseStep 20986451 = 31479677) B31479677
theorem B10361459 : Blo 1817610 10361459 := bstep (se 1 (by rfl) ⟨7771094, by rfl⟩ : syracuseStep 10361459 = 15542189) B15542189
theorem B2726591 : Blo 1817610 2726591 := bstep (se 1 (by rfl) ⟨2044943, by rfl⟩ : syracuseStep 2726591 = 4089887) B4089887
theorem B1817627 : Blo 1817610 1817627 := bstep (se 1 (by rfl) ⟨1363220, by rfl⟩ : syracuseStep 1817627 = 2726441) B2726441
theorem B1817767 : Blo 1817610 1817767 := bstep (se 1 (by rfl) ⟨1363325, by rfl⟩ : syracuseStep 1817767 = 2726651) B2726651
theorem B2727143 : Blo 1817610 2727143 := bstep (se 1 (by rfl) ⟨2045357, by rfl⟩ : syracuseStep 2727143 = 4090715) B4090715
theorem B1817851 : Blo 1817610 1817851 := bstep (se 1 (by rfl) ⟨1363388, by rfl⟩ : syracuseStep 1817851 = 2726777) B2726777
theorem B6135047 : Blo 1817610 6135047 := bstep (se 1 (by rfl) ⟨4601285, by rfl⟩ : syracuseStep 6135047 = 9202571) B9202571
theorem B5528839 : Blo 1817610 5528839 := bstep (se 1 (by rfl) ⟨4146629, by rfl⟩ : syracuseStep 5528839 = 8293259) B8293259
theorem B6905209 : Blo 1817610 6905209 := bstep (se 2 (by rfl) ⟨2589453, by rfl⟩ : syracuseStep 6905209 = 5178907) B5178907
theorem B2301311 : Blo 1817610 2301311 := bstep (se 1 (by rfl) ⟨1725983, by rfl⟩ : syracuseStep 2301311 = 3451967) B3451967
theorem B11968091 : Blo 1817610 11968091 := bstep (se 1 (by rfl) ⟨8976068, by rfl⟩ : syracuseStep 11968091 = 17952137) B17952137
theorem B10362599 : Blo 1817610 10362599 := bstep (se 1 (by rfl) ⟨7771949, by rfl⟩ : syracuseStep 10362599 = 15543899) B15543899
theorem B1818351 : Blo 1817610 1818351 := bstep (se 1 (by rfl) ⟨1363763, by rfl⟩ : syracuseStep 1818351 = 2727527) B2727527
theorem B6905681 : Blo 1817610 6905681 := bstep (se 2 (by rfl) ⟨2589630, by rfl⟩ : syracuseStep 6905681 = 5179261) B5179261
theorem B1818459 : Blo 1817610 1818459 := bstep (se 1 (by rfl) ⟨1363844, by rfl⟩ : syracuseStep 1818459 = 2727689) B2727689
theorem B1818607 : Blo 1817610 1818607 := bstep (se 1 (by rfl) ⟨1363955, by rfl⟩ : syracuseStep 1818607 = 2727911) B2727911
theorem B2302015 : Blo 1817610 2302015 := bstep (se 1 (by rfl) ⟨1726511, by rfl⟩ : syracuseStep 2302015 = 3453023) B3453023
theorem B1818715 : Blo 1817610 1818715 := bstep (se 1 (by rfl) ⟨1364036, by rfl⟩ : syracuseStep 1818715 = 2728073) B2728073
theorem B4604111 : Blo 1817610 4604111 := bstep (se 1 (by rfl) ⟨3453083, by rfl⟩ : syracuseStep 4604111 = 6906167) B6906167
theorem B10355309 : Blo 1817610 10355309 := bstep (se 3 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 10355309 = 3883241) B3883241
theorem B17048315 : Blo 1817610 17048315 := bstep (se 1 (by rfl) ⟨12786236, by rfl⟩ : syracuseStep 17048315 = 25572473) B25572473
theorem B2302759 : Blo 1817610 2302759 := bstep (se 1 (by rfl) ⟨1727069, by rfl⟩ : syracuseStep 2302759 = 3454139) B3454139
theorem B1819519 : Blo 1817610 1819519 := bstep (se 1 (by rfl) ⟨1364639, by rfl⟩ : syracuseStep 1819519 = 2729279) B2729279
theorem B4604809 : Blo 1817610 4604809 := bstep (se 2 (by rfl) ⟨1726803, by rfl⟩ : syracuseStep 4604809 = 3453607) B3453607
theorem B1819551 : Blo 1817610 1819551 := bstep (se 1 (by rfl) ⟨1364663, by rfl⟩ : syracuseStep 1819551 = 2729327) B2729327
theorem B6136829 : Blo 1817610 6136829 := bstep (se 3 (by rfl) ⟨1150655, by rfl⟩ : syracuseStep 6136829 = 2301311) B2301311
theorem B3884105 : Blo 1817610 3884105 := bstep (se 2 (by rfl) ⟨1456539, by rfl⟩ : syracuseStep 3884105 = 2913079) B2913079
theorem B43738217 : Blo 1817610 43738217 := bstep (se 2 (by rfl) ⟨16401831, by rfl⟩ : syracuseStep 43738217 = 32803663) B32803663
theorem B6136991 : Blo 1817610 6136991 := bstep (se 1 (by rfl) ⟨4602743, by rfl⟩ : syracuseStep 6136991 = 9205487) B9205487
theorem B6907639 : Blo 1817610 6907639 := bstep (se 1 (by rfl) ⟨5180729, by rfl⟩ : syracuseStep 6907639 = 10361459) B10361459
theorem B37849213 : Blo 1817610 37849213 := bstep (se 3 (by rfl) ⟨7096727, by rfl⟩ : syracuseStep 37849213 = 14193455) B14193455
theorem B4090031 : Blo 1817610 4090031 := bstep (se 1 (by rfl) ⟨3067523, by rfl⟩ : syracuseStep 4090031 = 6135047) B6135047
theorem B5179727 : Blo 1817610 5179727 := bstep (se 1 (by rfl) ⟨3884795, by rfl⟩ : syracuseStep 5179727 = 7769591) B7769591
theorem B6908399 : Blo 1817610 6908399 := bstep (se 1 (by rfl) ⟨5181299, by rfl⟩ : syracuseStep 6908399 = 10362599) B10362599
theorem B4917863 : Blo 1817610 4917863 := bstep (se 1 (by rfl) ⟨3688397, by rfl⟩ : syracuseStep 4917863 = 7376795) B7376795
theorem B179333813 : Blo 1817610 179333813 := bstep (se 5 (by rfl) ⟨8406272, by rfl⟩ : syracuseStep 179333813 = 16812545) B16812545
theorem B15157979 : Blo 1817610 15157979 := bstep (se 1 (by rfl) ⟨11368484, by rfl⟩ : syracuseStep 15157979 = 22736969) B22736969
theorem B11062079 : Blo 1817610 11062079 := bstep (se 1 (by rfl) ⟨8296559, by rfl⟩ : syracuseStep 11062079 = 16593119) B16593119
theorem B4369319 : Blo 1817610 4369319 := bstep (se 1 (by rfl) ⟨3276989, by rfl⟩ : syracuseStep 4369319 = 6553979) B6553979
theorem B36424651 : Blo 1817610 36424651 := bstep (se 1 (by rfl) ⟨27318488, by rfl⟩ : syracuseStep 36424651 = 54636977) B54636977
theorem B15535151 : Blo 1817610 15535151 := bstep (se 1 (by rfl) ⟨11651363, by rfl⟩ : syracuseStep 15535151 = 23302727) B23302727
theorem B4091471 : Blo 1817610 4091471 := bstep (se 1 (by rfl) ⟨3068603, by rfl⟩ : syracuseStep 4091471 = 6137207) B6137207
theorem B4730447 : Blo 1817610 4730447 := bstep (se 1 (by rfl) ⟨3547835, by rfl⟩ : syracuseStep 4730447 = 7095671) B7095671
theorem B23293601 : Blo 1817610 23293601 := bstep (se 2 (by rfl) ⟨8735100, by rfl⟩ : syracuseStep 23293601 = 17470201) B17470201
theorem B6139583 : Blo 1817610 6139583 := bstep (se 1 (by rfl) ⟨4604687, by rfl⟩ : syracuseStep 6139583 = 9209375) B9209375
theorem B3452635 : Blo 1817610 3452635 := bstep (se 1 (by rfl) ⟨2589476, by rfl⟩ : syracuseStep 3452635 = 5178953) B5178953
theorem B52424441 : Blo 1817610 52424441 := bstep (se 2 (by rfl) ⟨19659165, by rfl⟩ : syracuseStep 52424441 = 39318331) B39318331
theorem B9203867 : Blo 1817610 9203867 := bstep (se 1 (by rfl) ⟨6902900, by rfl⟩ : syracuseStep 9203867 = 13805801) B13805801
theorem B17469665 : Blo 1817610 17469665 := bstep (se 2 (by rfl) ⟨6551124, by rfl⟩ : syracuseStep 17469665 = 13102249) B13102249
theorem B4092191 : Blo 1817610 4092191 := bstep (se 1 (by rfl) ⟨3069143, by rfl⟩ : syracuseStep 4092191 = 6138287) B6138287
theorem B66367795 : Blo 1817610 66367795 := bstep (se 1 (by rfl) ⟨49775846, by rfl⟩ : syracuseStep 66367795 = 99551693) B99551693
theorem B4092911 : Blo 1817610 4092911 := bstep (se 1 (by rfl) ⟨3069683, by rfl⟩ : syracuseStep 4092911 = 6139367) B6139367
theorem B11056121 : Blo 1817610 11056121 := bstep (se 2 (by rfl) ⟨4146045, by rfl⟩ : syracuseStep 11056121 = 8292091) B8292091
theorem B2045263 : Blo 1817610 2045263 := bstep (se 1 (by rfl) ⟨1533947, by rfl⟩ : syracuseStep 2045263 = 3067895) B3067895
theorem B9336221 : Blo 1817610 9336221 := bstep (se 3 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 9336221 = 3501083) B3501083
theorem B4093631 : Blo 1817610 4093631 := bstep (se 1 (by rfl) ⟨3070223, by rfl⟩ : syracuseStep 4093631 = 6140447) B6140447
theorem B2045695 : Blo 1817610 2045695 := bstep (se 1 (by rfl) ⟨1534271, by rfl⟩ : syracuseStep 2045695 = 3068543) B3068543
theorem B19666871 : Blo 1817610 19666871 := bstep (se 1 (by rfl) ⟨14750153, by rfl⟩ : syracuseStep 19666871 = 29500307) B29500307
theorem B6903751 : Blo 1817610 6903751 := bstep (se 1 (by rfl) ⟨5177813, by rfl⟩ : syracuseStep 6903751 = 10355627) B10355627
theorem B7870459 : Blo 1817610 7870459 := bstep (se 1 (by rfl) ⟨5902844, by rfl⟩ : syracuseStep 7870459 = 11805689) B11805689
theorem B2045983 : Blo 1817610 2045983 := bstep (se 1 (by rfl) ⟨1534487, by rfl⟩ : syracuseStep 2045983 = 3068975) B3068975
theorem B4094063 : Blo 1817610 4094063 := bstep (se 1 (by rfl) ⟨3070547, by rfl⟩ : syracuseStep 4094063 = 6141095) B6141095
theorem B7870817 : Blo 1817610 7870817 := bstep (se 2 (by rfl) ⟨2951556, by rfl⟩ : syracuseStep 7870817 = 5903113) B5903113
theorem B13113697 : Blo 1817610 13113697 := bstep (se 2 (by rfl) ⟨4917636, by rfl⟩ : syracuseStep 13113697 = 9835273) B9835273
theorem B2726495 : Blo 1817610 2726495 := bstep (se 1 (by rfl) ⟨2044871, by rfl⟩ : syracuseStep 2726495 = 4089743) B4089743
theorem B8862365 : Blo 1817610 8862365 := bstep (se 3 (by rfl) ⟨1661693, by rfl⟩ : syracuseStep 8862365 = 3323387) B3323387
theorem B2726567 : Blo 1817610 2726567 := bstep (se 1 (by rfl) ⟨2044925, by rfl⟩ : syracuseStep 2726567 = 4089851) B4089851
theorem B2046631 : Blo 1817610 2046631 := bstep (se 1 (by rfl) ⟨1534973, by rfl⟩ : syracuseStep 2046631 = 3069947) B3069947
theorem B9206459 : Blo 1817610 9206459 := bstep (se 1 (by rfl) ⟨6904844, by rfl⟩ : syracuseStep 9206459 = 13809689) B13809689
theorem B10361641 : Blo 1817610 10361641 := bstep (se 2 (by rfl) ⟨3885615, by rfl⟩ : syracuseStep 10361641 = 7771231) B7771231
theorem B7371785 : Blo 1817610 7371785 := bstep (se 2 (by rfl) ⟨2764419, by rfl⟩ : syracuseStep 7371785 = 5528839) B5528839
theorem B13990967 : Blo 1817610 13990967 := bstep (se 1 (by rfl) ⟨10493225, by rfl⟩ : syracuseStep 13990967 = 20986451) B20986451
theorem B2726975 : Blo 1817610 2726975 := bstep (se 1 (by rfl) ⟨2045231, by rfl⟩ : syracuseStep 2726975 = 4090463) B4090463
theorem B2727023 : Blo 1817610 2727023 := bstep (se 1 (by rfl) ⟨2045267, by rfl⟩ : syracuseStep 2727023 = 4090535) B4090535
theorem B1817727 : Blo 1817610 1817727 := bstep (se 1 (by rfl) ⟨1363295, by rfl⟩ : syracuseStep 1817727 = 2726591) B2726591
theorem B9206945 : Blo 1817610 9206945 := bstep (se 2 (by rfl) ⟨3452604, by rfl⟩ : syracuseStep 9206945 = 6905209) B6905209
theorem B2727215 : Blo 1817610 2727215 := bstep (se 1 (by rfl) ⟨2045411, by rfl⟩ : syracuseStep 2727215 = 4090823) B4090823
theorem B6135263 : Blo 1817610 6135263 := bstep (se 1 (by rfl) ⟨4601447, by rfl⟩ : syracuseStep 6135263 = 9202895) B9202895
theorem B1818095 : Blo 1817610 1818095 := bstep (se 1 (by rfl) ⟨1363571, by rfl⟩ : syracuseStep 1818095 = 2727143) B2727143
theorem B2727455 : Blo 1817610 2727455 := bstep (se 1 (by rfl) ⟨2045591, by rfl⟩ : syracuseStep 2727455 = 4091183) B4091183
theorem B33169013 : Blo 1817610 33169013 := bstep (se 5 (by rfl) ⟨1554797, by rfl⟩ : syracuseStep 33169013 = 3109595) B3109595
theorem B6135425 : Blo 1817610 6135425 := bstep (se 2 (by rfl) ⟨2300784, by rfl⟩ : syracuseStep 6135425 = 4601569) B4601569
theorem B7978727 : Blo 1817610 7978727 := bstep (se 1 (by rfl) ⟨5984045, by rfl⟩ : syracuseStep 7978727 = 11968091) B11968091
theorem B2301787 : Blo 1817610 2301787 := bstep (se 1 (by rfl) ⟨1726340, by rfl⟩ : syracuseStep 2301787 = 3452681) B3452681
theorem B4603787 : Blo 1817610 4603787 := bstep (se 1 (by rfl) ⟨3452840, by rfl⟩ : syracuseStep 4603787 = 6905681) B6905681
theorem B2727977 : Blo 1817610 2727977 := bstep (se 2 (by rfl) ⟨1022991, by rfl⟩ : syracuseStep 2727977 = 2045983) B2045983
theorem B6135911 : Blo 1817610 6135911 := bstep (se 1 (by rfl) ⟨4601933, by rfl⟩ : syracuseStep 6135911 = 9203867) B9203867
theorem B2728127 : Blo 1817610 2728127 := bstep (se 1 (by rfl) ⟨2046095, by rfl⟩ : syracuseStep 2728127 = 4092191) B4092191
theorem B88490393 : Blo 1817610 88490393 := bstep (se 2 (by rfl) ⟨33183897, by rfl⟩ : syracuseStep 88490393 = 66367795) B66367795
theorem B2728607 : Blo 1817610 2728607 := bstep (se 1 (by rfl) ⟨2046455, by rfl⟩ : syracuseStep 2728607 = 4092911) B4092911
theorem B2589403 : Blo 1817610 2589403 := bstep (se 1 (by rfl) ⟨1942052, by rfl⟩ : syracuseStep 2589403 = 3884105) B3884105
theorem B13812605 : Blo 1817610 13812605 := bstep (se 3 (by rfl) ⟨2589863, by rfl⟩ : syracuseStep 13812605 = 5179727) B5179727
theorem B2728841 : Blo 1817610 2728841 := bstep (se 2 (by rfl) ⟨1023315, by rfl⟩ : syracuseStep 2728841 = 2046631) B2046631
theorem B20988845 : Blo 1817610 20988845 := bstep (se 3 (by rfl) ⟨3935408, by rfl⟩ : syracuseStep 20988845 = 7870817) B7870817
theorem B2729087 : Blo 1817610 2729087 := bstep (se 1 (by rfl) ⟨2046815, by rfl⟩ : syracuseStep 2729087 = 4093631) B4093631
theorem B2729375 : Blo 1817610 2729375 := bstep (se 1 (by rfl) ⟨2047031, by rfl⟩ : syracuseStep 2729375 = 4094063) B4094063
theorem B4605599 : Blo 1817610 4605599 := bstep (se 1 (by rfl) ⟨3454199, by rfl⟩ : syracuseStep 4605599 = 6908399) B6908399
theorem B3278575 : Blo 1817610 3278575 := bstep (se 1 (by rfl) ⟨2458931, by rfl⟩ : syracuseStep 3278575 = 4917863) B4917863
theorem B119555875 : Blo 1817610 119555875 := bstep (se 1 (by rfl) ⟨89666906, by rfl⟩ : syracuseStep 119555875 = 179333813) B179333813
theorem B6137639 : Blo 1817610 6137639 := bstep (se 1 (by rfl) ⟨4603229, by rfl⟩ : syracuseStep 6137639 = 9206459) B9206459
theorem B7374719 : Blo 1817610 7374719 := bstep (se 1 (by rfl) ⟨5531039, by rfl⟩ : syracuseStep 7374719 = 11062079) B11062079
theorem B21276605 : Blo 1817610 21276605 := bstep (se 3 (by rfl) ⟨3989363, by rfl⟩ : syracuseStep 21276605 = 7978727) B7978727
theorem B10356767 : Blo 1817610 10356767 := bstep (se 1 (by rfl) ⟨7767575, by rfl⟩ : syracuseStep 10356767 = 15535151) B15535151
theorem B6137963 : Blo 1817610 6137963 := bstep (se 1 (by rfl) ⟨4603472, by rfl⟩ : syracuseStep 6137963 = 9206945) B9206945
theorem B4090175 : Blo 1817610 4090175 := bstep (se 1 (by rfl) ⟨3067631, by rfl⟩ : syracuseStep 4090175 = 6135263) B6135263
theorem B9210185 : Blo 1817610 9210185 := bstep (se 2 (by rfl) ⟨3453819, by rfl⟩ : syracuseStep 9210185 = 6907639) B6907639
theorem B22112675 : Blo 1817610 22112675 := bstep (se 1 (by rfl) ⟨16584506, by rfl⟩ : syracuseStep 22112675 = 33169013) B33169013
theorem B4090283 : Blo 1817610 4090283 := bstep (se 1 (by rfl) ⟨3067712, by rfl⟩ : syracuseStep 4090283 = 6135425) B6135425
theorem B34949627 : Blo 1817610 34949627 := bstep (se 1 (by rfl) ⟨26212220, by rfl⟩ : syracuseStep 34949627 = 52424441) B52424441
theorem B17484929 : Blo 1817610 17484929 := bstep (se 2 (by rfl) ⟨6556848, by rfl⟩ : syracuseStep 17484929 = 13113697) B13113697
theorem B11365543 : Blo 1817610 11365543 := bstep (se 1 (by rfl) ⟨8524157, by rfl⟩ : syracuseStep 11365543 = 17048315) B17048315
theorem B201862469 : Blo 1817610 201862469 := bstep (se 4 (by rfl) ⟨18924606, by rfl⟩ : syracuseStep 201862469 = 37849213) B37849213
theorem B4091219 : Blo 1817610 4091219 := bstep (se 1 (by rfl) ⟨3068414, by rfl⟩ : syracuseStep 4091219 = 6136829) B6136829
theorem B29158811 : Blo 1817610 29158811 := bstep (se 1 (by rfl) ⟨21869108, by rfl⟩ : syracuseStep 29158811 = 43738217) B43738217
theorem B4091327 : Blo 1817610 4091327 := bstep (se 1 (by rfl) ⟨3068495, by rfl⟩ : syracuseStep 4091327 = 6136991) B6136991
theorem B13815521 : Blo 1817610 13815521 := bstep (se 2 (by rfl) ⟨5180820, by rfl⟩ : syracuseStep 13815521 = 10361641) B10361641
theorem B6139745 : Blo 1817610 6139745 := bstep (se 2 (by rfl) ⟨2302404, by rfl⟩ : syracuseStep 6139745 = 4604809) B4604809
theorem B48566201 : Blo 1817610 48566201 := bstep (se 2 (by rfl) ⟨18212325, by rfl⟩ : syracuseStep 48566201 = 36424651) B36424651
theorem B13111247 : Blo 1817610 13111247 := bstep (se 1 (by rfl) ⟨9833435, by rfl⟩ : syracuseStep 13111247 = 19666871) B19666871
theorem B10105319 : Blo 1817610 10105319 := bstep (se 1 (by rfl) ⟨7578989, by rfl⟩ : syracuseStep 10105319 = 15157979) B15157979
theorem B2912879 : Blo 1817610 2912879 := bstep (se 1 (by rfl) ⟨2184659, by rfl⟩ : syracuseStep 2912879 = 4369319) B4369319
theorem B9327311 : Blo 1817610 9327311 := bstep (se 1 (by rfl) ⟨6995483, by rfl⟩ : syracuseStep 9327311 = 13990967) B13990967
theorem B15529067 : Blo 1817610 15529067 := bstep (se 1 (by rfl) ⟨11646800, by rfl⟩ : syracuseStep 15529067 = 23293601) B23293601
theorem B3069049 : Blo 1817610 3069049 := bstep (se 2 (by rfl) ⟨1150893, by rfl⟩ : syracuseStep 3069049 = 2301787) B2301787
theorem B4093055 : Blo 1817610 4093055 := bstep (se 1 (by rfl) ⟨3069791, by rfl⟩ : syracuseStep 4093055 = 6139583) B6139583
theorem B3069191 : Blo 1817610 3069191 := bstep (se 1 (by rfl) ⟨2301893, by rfl⟩ : syracuseStep 3069191 = 4603787) B4603787
theorem B9205001 : Blo 1817610 9205001 := bstep (se 2 (by rfl) ⟨3451875, by rfl⟩ : syracuseStep 9205001 = 6903751) B6903751
theorem B3069353 : Blo 1817610 3069353 := bstep (se 2 (by rfl) ⟨1151007, by rfl⟩ : syracuseStep 3069353 = 2302015) B2302015
theorem B3069407 : Blo 1817610 3069407 := bstep (se 1 (by rfl) ⟨2302055, by rfl⟩ : syracuseStep 3069407 = 4604111) B4604111
theorem B11646443 : Blo 1817610 11646443 := bstep (se 1 (by rfl) ⟨8734832, by rfl⟩ : syracuseStep 11646443 = 17469665) B17469665
theorem B6903539 : Blo 1817610 6903539 := bstep (se 1 (by rfl) ⟨5177654, by rfl⟩ : syracuseStep 6903539 = 10355309) B10355309
theorem B7370747 : Blo 1817610 7370747 := bstep (se 1 (by rfl) ⟨5528060, by rfl⟩ : syracuseStep 7370747 = 11056121) B11056121
theorem B6224147 : Blo 1817610 6224147 := bstep (se 1 (by rfl) ⟨4668110, by rfl⟩ : syracuseStep 6224147 = 9336221) B9336221
theorem B3070345 : Blo 1817610 3070345 := bstep (se 2 (by rfl) ⟨1151379, by rfl⟩ : syracuseStep 3070345 = 2302759) B2302759
theorem B2726687 : Blo 1817610 2726687 := bstep (se 1 (by rfl) ⟨2045015, by rfl⟩ : syracuseStep 2726687 = 4090031) B4090031
theorem B12614525 : Blo 1817610 12614525 := bstep (se 3 (by rfl) ⟨2365223, by rfl⟩ : syracuseStep 12614525 = 4730447) B4730447
theorem B1817663 : Blo 1817610 1817663 := bstep (se 1 (by rfl) ⟨1363247, by rfl⟩ : syracuseStep 1817663 = 2726495) B2726495
theorem B23632973 : Blo 1817610 23632973 := bstep (se 3 (by rfl) ⟨4431182, by rfl⟩ : syracuseStep 23632973 = 8862365) B8862365
theorem B2727017 : Blo 1817610 2727017 := bstep (se 2 (by rfl) ⟨1022631, by rfl⟩ : syracuseStep 2727017 = 2045263) B2045263
theorem B1817711 : Blo 1817610 1817711 := bstep (se 1 (by rfl) ⟨1363283, by rfl⟩ : syracuseStep 1817711 = 2726567) B2726567
theorem B4914523 : Blo 1817610 4914523 := bstep (se 1 (by rfl) ⟨3685892, by rfl⟩ : syracuseStep 4914523 = 7371785) B7371785
theorem B1817983 : Blo 1817610 1817983 := bstep (se 1 (by rfl) ⟨1363487, by rfl⟩ : syracuseStep 1817983 = 2726975) B2726975
theorem B1818015 : Blo 1817610 1818015 := bstep (se 1 (by rfl) ⟨1363511, by rfl⟩ : syracuseStep 1818015 = 2727023) B2727023
theorem B1818143 : Blo 1817610 1818143 := bstep (se 1 (by rfl) ⟨1363607, by rfl⟩ : syracuseStep 1818143 = 2727215) B2727215
theorem B4603513 : Blo 1817610 4603513 := bstep (se 2 (by rfl) ⟨1726317, by rfl⟩ : syracuseStep 4603513 = 3452635) B3452635
theorem B2727593 : Blo 1817610 2727593 := bstep (se 2 (by rfl) ⟨1022847, by rfl⟩ : syracuseStep 2727593 = 2045695) B2045695
theorem B1818303 : Blo 1817610 1818303 := bstep (se 1 (by rfl) ⟨1363727, by rfl⟩ : syracuseStep 1818303 = 2727455) B2727455
theorem B2727647 : Blo 1817610 2727647 := bstep (se 1 (by rfl) ⟨2045735, by rfl⟩ : syracuseStep 2727647 = 4091471) B4091471
theorem B10493945 : Blo 1817610 10493945 := bstep (se 2 (by rfl) ⟨3935229, by rfl⟩ : syracuseStep 10493945 = 7870459) B7870459
theorem B1818651 : Blo 1817610 1818651 := bstep (se 1 (by rfl) ⟨1363988, by rfl⟩ : syracuseStep 1818651 = 2727977) B2727977
theorem B1818751 : Blo 1817610 1818751 := bstep (se 1 (by rfl) ⟨1364063, by rfl⟩ : syracuseStep 1818751 = 2728127) B2728127
theorem B1819071 : Blo 1817610 1819071 := bstep (se 1 (by rfl) ⟨1364303, by rfl⟩ : syracuseStep 1819071 = 2728607) B2728607
theorem B6218207 : Blo 1817610 6218207 := bstep (se 1 (by rfl) ⟨4663655, by rfl⟩ : syracuseStep 6218207 = 9327311) B9327311
theorem B9208403 : Blo 1817610 9208403 := bstep (se 1 (by rfl) ⟨6906302, by rfl⟩ : syracuseStep 9208403 = 13812605) B13812605
theorem B1819227 : Blo 1817610 1819227 := bstep (se 1 (by rfl) ⟨1364420, by rfl⟩ : syracuseStep 1819227 = 2728841) B2728841
theorem B13992563 : Blo 1817610 13992563 := bstep (se 1 (by rfl) ⟨10494422, by rfl⟩ : syracuseStep 13992563 = 20988845) B20988845
theorem B2728703 : Blo 1817610 2728703 := bstep (se 1 (by rfl) ⟨2046527, by rfl⟩ : syracuseStep 2728703 = 4093055) B4093055
theorem B1819391 : Blo 1817610 1819391 := bstep (se 1 (by rfl) ⟨1364543, by rfl⟩ : syracuseStep 1819391 = 2729087) B2729087
theorem B6136667 : Blo 1817610 6136667 := bstep (se 1 (by rfl) ⟨4602500, by rfl⟩ : syracuseStep 6136667 = 9205001) B9205001
theorem B1819583 : Blo 1817610 1819583 := bstep (se 1 (by rfl) ⟨1364687, by rfl⟩ : syracuseStep 1819583 = 2729375) B2729375
theorem B4916479 : Blo 1817610 4916479 := bstep (se 1 (by rfl) ⟨3687359, by rfl⟩ : syracuseStep 4916479 = 7374719) B7374719
theorem B7767677 : Blo 1817610 7767677 := bstep (se 3 (by rfl) ⟨1456439, by rfl⟩ : syracuseStep 7767677 = 2912879) B2912879
theorem B23299751 : Blo 1817610 23299751 := bstep (se 1 (by rfl) ⟨17474813, by rfl⟩ : syracuseStep 23299751 = 34949627) B34949627
theorem B15755315 : Blo 1817610 15755315 := bstep (se 1 (by rfl) ⟨11816486, by rfl⟩ : syracuseStep 15755315 = 23632973) B23632973
theorem B6138017 : Blo 1817610 6138017 := bstep (se 2 (by rfl) ⟨2301756, by rfl⟩ : syracuseStep 6138017 = 4603513) B4603513
theorem B9210347 : Blo 1817610 9210347 := bstep (se 1 (by rfl) ⟨6907760, by rfl⟩ : syracuseStep 9210347 = 13815521) B13815521
theorem B129509869 : Blo 1817610 129509869 := bstep (se 3 (by rfl) ⟨24283100, by rfl⟩ : syracuseStep 129509869 = 48566201) B48566201
theorem B4090607 : Blo 1817610 4090607 := bstep (se 1 (by rfl) ⟨3067955, by rfl⟩ : syracuseStep 4090607 = 6135911) B6135911
theorem B58993595 : Blo 1817610 58993595 := bstep (se 1 (by rfl) ⟨44245196, by rfl⟩ : syracuseStep 58993595 = 88490393) B88490393
theorem B6736879 : Blo 1817610 6736879 := bstep (se 1 (by rfl) ⟨5052659, by rfl⟩ : syracuseStep 6736879 = 10105319) B10105319
theorem B3452537 : Blo 1817610 3452537 := bstep (se 2 (by rfl) ⟨1294701, by rfl⟩ : syracuseStep 3452537 = 2589403) B2589403
theorem B4091759 : Blo 1817610 4091759 := bstep (se 1 (by rfl) ⟨3068819, by rfl⟩ : syracuseStep 4091759 = 6137639) B6137639
theorem B17485733 : Blo 1817610 17485733 := bstep (se 4 (by rfl) ⟨1639287, by rfl⟩ : syracuseStep 17485733 = 3278575) B3278575
theorem B4091975 : Blo 1817610 4091975 := bstep (se 1 (by rfl) ⟨3068981, by rfl⟩ : syracuseStep 4091975 = 6137963) B6137963
theorem B4092065 : Blo 1817610 4092065 := bstep (se 2 (by rfl) ⟨1534524, by rfl⟩ : syracuseStep 4092065 = 3069049) B3069049
theorem B4149431 : Blo 1817610 4149431 := bstep (se 1 (by rfl) ⟨3112073, by rfl⟩ : syracuseStep 4149431 = 6224147) B6224147
theorem B6140123 : Blo 1817610 6140123 := bstep (se 1 (by rfl) ⟨4605092, by rfl⟩ : syracuseStep 6140123 = 9210185) B9210185
theorem B14741783 : Blo 1817610 14741783 := bstep (se 1 (by rfl) ⟨11056337, by rfl⟩ : syracuseStep 14741783 = 22112675) B22112675
theorem B8409683 : Blo 1817610 8409683 := bstep (se 1 (by rfl) ⟨6307262, by rfl⟩ : syracuseStep 8409683 = 12614525) B12614525
theorem B134574979 : Blo 1817610 134574979 := bstep (se 1 (by rfl) ⟨100931234, by rfl⟩ : syracuseStep 134574979 = 201862469) B201862469
theorem B4093163 : Blo 1817610 4093163 := bstep (se 1 (by rfl) ⟨3069872, by rfl⟩ : syracuseStep 4093163 = 6139745) B6139745
theorem B6995963 : Blo 1817610 6995963 := bstep (se 1 (by rfl) ⟨5246972, by rfl⟩ : syracuseStep 6995963 = 10493945) B10493945
theorem B4093793 : Blo 1817610 4093793 := bstep (se 2 (by rfl) ⟨1535172, by rfl⟩ : syracuseStep 4093793 = 3070345) B3070345
theorem B10352711 : Blo 1817610 10352711 := bstep (se 1 (by rfl) ⟨7764533, by rfl⟩ : syracuseStep 10352711 = 15529067) B15529067
theorem B2046127 : Blo 1817610 2046127 := bstep (se 1 (by rfl) ⟨1534595, by rfl⟩ : syracuseStep 2046127 = 3069191) B3069191
theorem B2046235 : Blo 1817610 2046235 := bstep (se 1 (by rfl) ⟨1534676, by rfl⟩ : syracuseStep 2046235 = 3069353) B3069353
theorem B2046271 : Blo 1817610 2046271 := bstep (se 1 (by rfl) ⟨1534703, by rfl⟩ : syracuseStep 2046271 = 3069407) B3069407
theorem B7764295 : Blo 1817610 7764295 := bstep (se 1 (by rfl) ⟨5823221, by rfl⟩ : syracuseStep 7764295 = 11646443) B11646443
theorem B3070399 : Blo 1817610 3070399 := bstep (se 1 (by rfl) ⟨2302799, by rfl⟩ : syracuseStep 3070399 = 4605599) B4605599
theorem B4602359 : Blo 1817610 4602359 := bstep (se 1 (by rfl) ⟨3451769, by rfl⟩ : syracuseStep 4602359 = 6903539) B6903539
theorem B4913831 : Blo 1817610 4913831 := bstep (se 1 (by rfl) ⟨3685373, by rfl⟩ : syracuseStep 4913831 = 7370747) B7370747
theorem B6904511 : Blo 1817610 6904511 := bstep (se 1 (by rfl) ⟨5178383, by rfl⟩ : syracuseStep 6904511 = 10356767) B10356767
theorem B2726783 : Blo 1817610 2726783 := bstep (se 1 (by rfl) ⟨2045087, by rfl⟩ : syracuseStep 2726783 = 4090175) B4090175
theorem B15154057 : Blo 1817610 15154057 := bstep (se 2 (by rfl) ⟨5682771, by rfl⟩ : syracuseStep 15154057 = 11365543) B11365543
theorem B2726855 : Blo 1817610 2726855 := bstep (se 1 (by rfl) ⟨2045141, by rfl⟩ : syracuseStep 2726855 = 4090283) B4090283
theorem B6552697 : Blo 1817610 6552697 := bstep (se 2 (by rfl) ⟨2457261, by rfl⟩ : syracuseStep 6552697 = 4914523) B4914523
theorem B1817791 : Blo 1817610 1817791 := bstep (se 1 (by rfl) ⟨1363343, by rfl⟩ : syracuseStep 1817791 = 2726687) B2726687
theorem B1818011 : Blo 1817610 1818011 := bstep (se 1 (by rfl) ⟨1363508, by rfl⟩ : syracuseStep 1818011 = 2727017) B2727017
theorem B11656619 : Blo 1817610 11656619 := bstep (se 1 (by rfl) ⟨8742464, by rfl⟩ : syracuseStep 11656619 = 17484929) B17484929
theorem B2727479 : Blo 1817610 2727479 := bstep (se 1 (by rfl) ⟨2045609, by rfl⟩ : syracuseStep 2727479 = 4091219) B4091219
theorem B19439207 : Blo 1817610 19439207 := bstep (se 1 (by rfl) ⟨14579405, by rfl⟩ : syracuseStep 19439207 = 29158811) B29158811
theorem B2727551 : Blo 1817610 2727551 := bstep (se 1 (by rfl) ⟨2045663, by rfl⟩ : syracuseStep 2727551 = 4091327) B4091327
theorem B159407833 : Blo 1817610 159407833 := bstep (se 2 (by rfl) ⟨59777937, by rfl⟩ : syracuseStep 159407833 = 119555875) B119555875
theorem B1818395 : Blo 1817610 1818395 := bstep (se 1 (by rfl) ⟨1363796, by rfl⟩ : syracuseStep 1818395 = 2727593) B2727593
theorem B1818431 : Blo 1817610 1818431 := bstep (se 1 (by rfl) ⟨1363823, by rfl⟩ : syracuseStep 1818431 = 2727647) B2727647
theorem B56737613 : Blo 1817610 56737613 := bstep (se 3 (by rfl) ⟨10638302, by rfl⟩ : syracuseStep 56737613 = 21276605) B21276605
theorem B8740831 : Blo 1817610 8740831 := bstep (se 1 (by rfl) ⟨6555623, by rfl⟩ : syracuseStep 8740831 = 13111247) B13111247
theorem B2727983 : Blo 1817610 2727983 := bstep (se 1 (by rfl) ⟨2045987, by rfl⟩ : syracuseStep 2727983 = 4091975) B4091975
theorem B2728043 : Blo 1817610 2728043 := bstep (se 1 (by rfl) ⟨2046032, by rfl⟩ : syracuseStep 2728043 = 4092065) B4092065
theorem B2728169 : Blo 1817610 2728169 := bstep (se 2 (by rfl) ⟨1023063, by rfl⟩ : syracuseStep 2728169 = 2046127) B2046127
theorem B4145471 : Blo 1817610 4145471 := bstep (se 1 (by rfl) ⟨3109103, by rfl⟩ : syracuseStep 4145471 = 6218207) B6218207
theorem B2728313 : Blo 1817610 2728313 := bstep (se 2 (by rfl) ⟨1023117, by rfl⟩ : syracuseStep 2728313 = 2046235) B2046235
theorem B2728361 : Blo 1817610 2728361 := bstep (se 2 (by rfl) ⟨1023135, by rfl⟩ : syracuseStep 2728361 = 2046271) B2046271
theorem B1819135 : Blo 1817610 1819135 := bstep (se 1 (by rfl) ⟨1364351, by rfl⟩ : syracuseStep 1819135 = 2728703) B2728703
theorem B172679825 : Blo 1817610 172679825 := bstep (se 2 (by rfl) ⟨64754934, by rfl⟩ : syracuseStep 172679825 = 129509869) B129509869
theorem B2728775 : Blo 1817610 2728775 := bstep (se 1 (by rfl) ⟨2046581, by rfl⟩ : syracuseStep 2728775 = 4093163) B4093163
theorem B15533167 : Blo 1817610 15533167 := bstep (se 1 (by rfl) ⟨11649875, by rfl⟩ : syracuseStep 15533167 = 23299751) B23299751
theorem B2729195 : Blo 1817610 2729195 := bstep (se 1 (by rfl) ⟨2046896, by rfl⟩ : syracuseStep 2729195 = 4093793) B4093793
theorem B6555305 : Blo 1817610 6555305 := bstep (se 2 (by rfl) ⟨2458239, by rfl⟩ : syracuseStep 6555305 = 4916479) B4916479
theorem B212543777 : Blo 1817610 212543777 := bstep (se 2 (by rfl) ⟨79703916, by rfl⟩ : syracuseStep 212543777 = 159407833) B159407833
theorem B37825075 : Blo 1817610 37825075 := bstep (se 1 (by rfl) ⟨28368806, by rfl⟩ : syracuseStep 37825075 = 56737613) B56737613
theorem B4663975 : Blo 1817610 4663975 := bstep (se 1 (by rfl) ⟨3497981, by rfl⟩ : syracuseStep 4663975 = 6995963) B6995963
theorem B5606455 : Blo 1817610 5606455 := bstep (se 1 (by rfl) ⟨4204841, by rfl⟩ : syracuseStep 5606455 = 8409683) B8409683
theorem B6138935 : Blo 1817610 6138935 := bstep (se 1 (by rfl) ⟨4604201, by rfl⟩ : syracuseStep 6138935 = 9208403) B9208403
theorem B4091111 : Blo 1817610 4091111 := bstep (se 1 (by rfl) ⟨3068333, by rfl⟩ : syracuseStep 4091111 = 6136667) B6136667
theorem B179433305 : Blo 1817610 179433305 := bstep (se 2 (by rfl) ⟨67287489, by rfl⟩ : syracuseStep 179433305 = 134574979) B134574979
theorem B20205409 : Blo 1817610 20205409 := bstep (se 2 (by rfl) ⟨7577028, by rfl⟩ : syracuseStep 20205409 = 15154057) B15154057
theorem B8982505 : Blo 1817610 8982505 := bstep (se 2 (by rfl) ⟨3368439, by rfl⟩ : syracuseStep 8982505 = 6736879) B6736879
theorem B6901807 : Blo 1817610 6901807 := bstep (se 1 (by rfl) ⟨5176355, by rfl⟩ : syracuseStep 6901807 = 10352711) B10352711
theorem B4092011 : Blo 1817610 4092011 := bstep (se 1 (by rfl) ⟨3069008, by rfl⟩ : syracuseStep 4092011 = 6138017) B6138017
theorem B8736929 : Blo 1817610 8736929 := bstep (se 2 (by rfl) ⟨3276348, by rfl⟩ : syracuseStep 8736929 = 6552697) B6552697
theorem B6140231 : Blo 1817610 6140231 := bstep (se 1 (by rfl) ⟨4605173, by rfl⟩ : syracuseStep 6140231 = 9210347) B9210347
theorem B20713805 : Blo 1817610 20713805 := bstep (se 3 (by rfl) ⟨3883838, by rfl⟩ : syracuseStep 20713805 = 7767677) B7767677
theorem B3068239 : Blo 1817610 3068239 := bstep (se 1 (by rfl) ⟨2301179, by rfl⟩ : syracuseStep 3068239 = 4602359) B4602359
theorem B7771079 : Blo 1817610 7771079 := bstep (se 1 (by rfl) ⟨5828309, by rfl⟩ : syracuseStep 7771079 = 11656619) B11656619
theorem B11654441 : Blo 1817610 11654441 := bstep (se 2 (by rfl) ⟨4370415, by rfl⟩ : syracuseStep 11654441 = 8740831) B8740831
theorem B2766287 : Blo 1817610 2766287 := bstep (se 1 (by rfl) ⟨2074715, by rfl⟩ : syracuseStep 2766287 = 4149431) B4149431
theorem B42014173 : Blo 1817610 42014173 := bstep (se 3 (by rfl) ⟨7877657, by rfl⟩ : syracuseStep 42014173 = 15755315) B15755315
theorem B4093415 : Blo 1817610 4093415 := bstep (se 1 (by rfl) ⟨3070061, by rfl⟩ : syracuseStep 4093415 = 6140123) B6140123
theorem B9827855 : Blo 1817610 9827855 := bstep (se 1 (by rfl) ⟨7370891, by rfl⟩ : syracuseStep 9827855 = 14741783) B14741783
theorem B9328375 : Blo 1817610 9328375 := bstep (se 1 (by rfl) ⟨6996281, by rfl⟩ : syracuseStep 9328375 = 13992563) B13992563
theorem B10352393 : Blo 1817610 10352393 := bstep (se 2 (by rfl) ⟨3882147, by rfl⟩ : syracuseStep 10352393 = 7764295) B7764295
theorem B4093865 : Blo 1817610 4093865 := bstep (se 2 (by rfl) ⟨1535199, by rfl⟩ : syracuseStep 4093865 = 3070399) B3070399
theorem B3275887 : Blo 1817610 3275887 := bstep (se 1 (by rfl) ⟨2456915, by rfl⟩ : syracuseStep 3275887 = 4913831) B4913831
theorem B4603007 : Blo 1817610 4603007 := bstep (se 1 (by rfl) ⟨3452255, by rfl⟩ : syracuseStep 4603007 = 6904511) B6904511
theorem B2727071 : Blo 1817610 2727071 := bstep (se 1 (by rfl) ⟨2045303, by rfl⟩ : syracuseStep 2727071 = 4090607) B4090607
theorem B1817855 : Blo 1817610 1817855 := bstep (se 1 (by rfl) ⟨1363391, by rfl⟩ : syracuseStep 1817855 = 2726783) B2726783
theorem B39329063 : Blo 1817610 39329063 := bstep (se 1 (by rfl) ⟨29496797, by rfl⟩ : syracuseStep 39329063 = 58993595) B58993595
theorem B1817903 : Blo 1817610 1817903 := bstep (se 1 (by rfl) ⟨1363427, by rfl⟩ : syracuseStep 1817903 = 2726855) B2726855
theorem B1818319 : Blo 1817610 1818319 := bstep (se 1 (by rfl) ⟨1363739, by rfl⟩ : syracuseStep 1818319 = 2727479) B2727479
theorem B12959471 : Blo 1817610 12959471 := bstep (se 1 (by rfl) ⟨9719603, by rfl⟩ : syracuseStep 12959471 = 19439207) B19439207
theorem B2301691 : Blo 1817610 2301691 := bstep (se 1 (by rfl) ⟨1726268, by rfl⟩ : syracuseStep 2301691 = 3452537) B3452537
theorem B1818367 : Blo 1817610 1818367 := bstep (se 1 (by rfl) ⟨1363775, by rfl⟩ : syracuseStep 1818367 = 2727551) B2727551
theorem B2727839 : Blo 1817610 2727839 := bstep (se 1 (by rfl) ⟨2045879, by rfl⟩ : syracuseStep 2727839 = 4091759) B4091759
theorem B11657155 : Blo 1817610 11657155 := bstep (se 1 (by rfl) ⟨8742866, by rfl⟩ : syracuseStep 11657155 = 17485733) B17485733
theorem B1818655 : Blo 1817610 1818655 := bstep (se 1 (by rfl) ⟨1363991, by rfl⟩ : syracuseStep 1818655 = 2727983) B2727983
theorem B2728007 : Blo 1817610 2728007 := bstep (se 1 (by rfl) ⟨2046005, by rfl⟩ : syracuseStep 2728007 = 4092011) B4092011
theorem B1818695 : Blo 1817610 1818695 := bstep (se 1 (by rfl) ⟨1364021, by rfl⟩ : syracuseStep 1818695 = 2728043) B2728043
theorem B5824619 : Blo 1817610 5824619 := bstep (se 1 (by rfl) ⟨4368464, by rfl⟩ : syracuseStep 5824619 = 8736929) B8736929
theorem B1818779 : Blo 1817610 1818779 := bstep (se 1 (by rfl) ⟨1364084, by rfl⟩ : syracuseStep 1818779 = 2728169) B2728169
theorem B1818875 : Blo 1817610 1818875 := bstep (se 1 (by rfl) ⟨1364156, by rfl⟩ : syracuseStep 1818875 = 2728313) B2728313
theorem B1818907 : Blo 1817610 1818907 := bstep (se 1 (by rfl) ⟨1364180, by rfl⟩ : syracuseStep 1818907 = 2728361) B2728361
theorem B1819183 : Blo 1817610 1819183 := bstep (se 1 (by rfl) ⟨1364387, by rfl⟩ : syracuseStep 1819183 = 2728775) B2728775
theorem B1819463 : Blo 1817610 1819463 := bstep (se 1 (by rfl) ⟨1364597, by rfl⟩ : syracuseStep 1819463 = 2729195) B2729195
theorem B6218633 : Blo 1817610 6218633 := bstep (se 2 (by rfl) ⟨2331987, by rfl⟩ : syracuseStep 6218633 = 4663975) B4663975
theorem B1844191 : Blo 1817610 1844191 := bstep (se 1 (by rfl) ⟨1383143, by rfl⟩ : syracuseStep 1844191 = 2766287) B2766287
theorem B2728943 : Blo 1817610 2728943 := bstep (se 1 (by rfl) ⟨2046707, by rfl⟩ : syracuseStep 2728943 = 4093415) B4093415
theorem B2729243 : Blo 1817610 2729243 := bstep (se 1 (by rfl) ⟨2046932, by rfl⟩ : syracuseStep 2729243 = 4093865) B4093865
theorem B4367849 : Blo 1817610 4367849 := bstep (se 2 (by rfl) ⟨1637943, by rfl⟩ : syracuseStep 4367849 = 3275887) B3275887
theorem B20710889 : Blo 1817610 20710889 := bstep (se 2 (by rfl) ⟨7766583, by rfl⟩ : syracuseStep 20710889 = 15533167) B15533167
theorem B56018897 : Blo 1817610 56018897 := bstep (se 2 (by rfl) ⟨21007086, by rfl⟩ : syracuseStep 56018897 = 42014173) B42014173
theorem B12437833 : Blo 1817610 12437833 := bstep (se 2 (by rfl) ⟨4664187, by rfl⟩ : syracuseStep 12437833 = 9328375) B9328375
theorem B119622203 : Blo 1817610 119622203 := bstep (se 1 (by rfl) ⟨89716652, by rfl⟩ : syracuseStep 119622203 = 179433305) B179433305
theorem B15542873 : Blo 1817610 15542873 := bstep (se 2 (by rfl) ⟨5828577, by rfl⟩ : syracuseStep 15542873 = 11657155) B11657155
theorem B9202409 : Blo 1817610 9202409 := bstep (se 2 (by rfl) ⟨3450903, by rfl⟩ : syracuseStep 9202409 = 6901807) B6901807
theorem B2763647 : Blo 1817610 2763647 := bstep (se 1 (by rfl) ⟨2072735, by rfl⟩ : syracuseStep 2763647 = 4145471) B4145471
theorem B4090985 : Blo 1817610 4090985 := bstep (se 2 (by rfl) ⟨1534119, by rfl⟩ : syracuseStep 4090985 = 3068239) B3068239
theorem B5180719 : Blo 1817610 5180719 := bstep (se 1 (by rfl) ⟨3885539, by rfl⟩ : syracuseStep 5180719 = 7771079) B7771079
theorem B7769627 : Blo 1817610 7769627 := bstep (se 1 (by rfl) ⟨5827220, by rfl⟩ : syracuseStep 7769627 = 11654441) B11654441
theorem B4370203 : Blo 1817610 4370203 := bstep (se 1 (by rfl) ⟨3277652, by rfl⟩ : syracuseStep 4370203 = 6555305) B6555305
theorem B6901595 : Blo 1817610 6901595 := bstep (se 1 (by rfl) ⟨5176196, by rfl⟩ : syracuseStep 6901595 = 10352393) B10352393
theorem B7475273 : Blo 1817610 7475273 := bstep (se 2 (by rfl) ⟨2803227, by rfl⟩ : syracuseStep 7475273 = 5606455) B5606455
theorem B34558589 : Blo 1817610 34558589 := bstep (se 3 (by rfl) ⟨6479735, by rfl⟩ : syracuseStep 34558589 = 12959471) B12959471
theorem B4092623 : Blo 1817610 4092623 := bstep (se 1 (by rfl) ⟨3069467, by rfl⟩ : syracuseStep 4092623 = 6138935) B6138935
theorem B3068671 : Blo 1817610 3068671 := bstep (se 1 (by rfl) ⟨2301503, by rfl⟩ : syracuseStep 3068671 = 4603007) B4603007
theorem B26219375 : Blo 1817610 26219375 := bstep (se 1 (by rfl) ⟨19664531, by rfl⟩ : syracuseStep 26219375 = 39329063) B39329063
theorem B3068921 : Blo 1817610 3068921 := bstep (se 2 (by rfl) ⟨1150845, by rfl⟩ : syracuseStep 3068921 = 2301691) B2301691
theorem B26940545 : Blo 1817610 26940545 := bstep (se 2 (by rfl) ⟨10102704, by rfl⟩ : syracuseStep 26940545 = 20205409) B20205409
theorem B4093487 : Blo 1817610 4093487 := bstep (se 1 (by rfl) ⟨3070115, by rfl⟩ : syracuseStep 4093487 = 6140231) B6140231
theorem B13809203 : Blo 1817610 13809203 := bstep (se 1 (by rfl) ⟨10356902, by rfl⟩ : syracuseStep 13809203 = 20713805) B20713805
theorem B201733733 : Blo 1817610 201733733 := bstep (se 4 (by rfl) ⟨18912537, by rfl⟩ : syracuseStep 201733733 = 37825075) B37825075
theorem B115119883 : Blo 1817610 115119883 := bstep (se 1 (by rfl) ⟨86339912, by rfl⟩ : syracuseStep 115119883 = 172679825) B172679825
theorem B6551903 : Blo 1817610 6551903 := bstep (se 1 (by rfl) ⟨4913927, by rfl⟩ : syracuseStep 6551903 = 9827855) B9827855
theorem B141695851 : Blo 1817610 141695851 := bstep (se 1 (by rfl) ⟨106271888, by rfl⟩ : syracuseStep 141695851 = 212543777) B212543777
theorem B1818047 : Blo 1817610 1818047 := bstep (se 1 (by rfl) ⟨1363535, by rfl⟩ : syracuseStep 1818047 = 2727071) B2727071
theorem B2727407 : Blo 1817610 2727407 := bstep (se 1 (by rfl) ⟨2045555, by rfl⟩ : syracuseStep 2727407 = 4091111) B4091111
theorem B1818559 : Blo 1817610 1818559 := bstep (se 1 (by rfl) ⟨1363919, by rfl⟩ : syracuseStep 1818559 = 2727839) B2727839
theorem B11976673 : Blo 1817610 11976673 := bstep (se 2 (by rfl) ⟨4491252, by rfl⟩ : syracuseStep 11976673 = 8982505) B8982505
theorem B1818671 : Blo 1817610 1818671 := bstep (se 1 (by rfl) ⟨1364003, by rfl⟩ : syracuseStep 1818671 = 2728007) B2728007
theorem B3883079 : Blo 1817610 3883079 := bstep (se 1 (by rfl) ⟨2912309, by rfl⟩ : syracuseStep 3883079 = 5824619) B5824619
theorem B2728415 : Blo 1817610 2728415 := bstep (se 1 (by rfl) ⟨2046311, by rfl⟩ : syracuseStep 2728415 = 4092623) B4092623
theorem B4145755 : Blo 1817610 4145755 := bstep (se 1 (by rfl) ⟨3109316, by rfl⟩ : syracuseStep 4145755 = 6218633) B6218633
theorem B1819295 : Blo 1817610 1819295 := bstep (se 1 (by rfl) ⟨1364471, by rfl⟩ : syracuseStep 1819295 = 2728943) B2728943
theorem B1819495 : Blo 1817610 1819495 := bstep (se 1 (by rfl) ⟨1364621, by rfl⟩ : syracuseStep 1819495 = 2729243) B2729243
theorem B2728991 : Blo 1817610 2728991 := bstep (se 1 (by rfl) ⟨2046743, by rfl⟩ : syracuseStep 2728991 = 4093487) B4093487
theorem B134489155 : Blo 1817610 134489155 := bstep (se 1 (by rfl) ⟨100866866, by rfl⟩ : syracuseStep 134489155 = 201733733) B201733733
theorem B2458921 : Blo 1817610 2458921 := bstep (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) B1844191
theorem B23307749 : Blo 1817610 23307749 := bstep (se 4 (by rfl) ⟨2185101, by rfl⟩ : syracuseStep 23307749 = 4370203) B4370203
theorem B4367935 : Blo 1817610 4367935 := bstep (se 1 (by rfl) ⟨3275951, by rfl⟩ : syracuseStep 4367935 = 6551903) B6551903
theorem B6907625 : Blo 1817610 6907625 := bstep (se 2 (by rfl) ⟨2590359, by rfl⟩ : syracuseStep 6907625 = 5180719) B5180719
theorem B5179751 : Blo 1817610 5179751 := bstep (se 1 (by rfl) ⟨3884813, by rfl⟩ : syracuseStep 5179751 = 7769627) B7769627
theorem B15968897 : Blo 1817610 15968897 := bstep (se 2 (by rfl) ⟨5988336, by rfl⟩ : syracuseStep 15968897 = 11976673) B11976673
theorem B4983515 : Blo 1817610 4983515 := bstep (se 1 (by rfl) ⟨3737636, by rfl⟩ : syracuseStep 4983515 = 7475273) B7475273
theorem B16583777 : Blo 1817610 16583777 := bstep (se 2 (by rfl) ⟨6218916, by rfl⟩ : syracuseStep 16583777 = 12437833) B12437833
theorem B17960363 : Blo 1817610 17960363 := bstep (se 1 (by rfl) ⟨13470272, by rfl⟩ : syracuseStep 17960363 = 26940545) B26940545
theorem B13807259 : Blo 1817610 13807259 := bstep (se 1 (by rfl) ⟨10355444, by rfl⟩ : syracuseStep 13807259 = 20710889) B20710889
theorem B4091561 : Blo 1817610 4091561 := bstep (se 2 (by rfl) ⟨1534335, by rfl⟩ : syracuseStep 4091561 = 3068671) B3068671
theorem B188927801 : Blo 1817610 188927801 := bstep (se 2 (by rfl) ⟨70847925, by rfl⟩ : syracuseStep 188927801 = 141695851) B141695851
theorem B92156237 : Blo 1817610 92156237 := bstep (se 3 (by rfl) ⟨17279294, by rfl⟩ : syracuseStep 92156237 = 34558589) B34558589
theorem B4601063 : Blo 1817610 4601063 := bstep (se 1 (by rfl) ⟨3450797, by rfl⟩ : syracuseStep 4601063 = 6901595) B6901595
theorem B17479583 : Blo 1817610 17479583 := bstep (se 1 (by rfl) ⟨13109687, by rfl⟩ : syracuseStep 17479583 = 26219375) B26219375
theorem B2045947 : Blo 1817610 2045947 := bstep (se 1 (by rfl) ⟨1534460, by rfl⟩ : syracuseStep 2045947 = 3068921) B3068921
theorem B9206135 : Blo 1817610 9206135 := bstep (se 1 (by rfl) ⟨6904601, by rfl⟩ : syracuseStep 9206135 = 13809203) B13809203
theorem B11647597 : Blo 1817610 11647597 := bstep (se 3 (by rfl) ⟨2183924, by rfl⟩ : syracuseStep 11647597 = 4367849) B4367849
theorem B37345931 : Blo 1817610 37345931 := bstep (se 1 (by rfl) ⟨28009448, by rfl⟩ : syracuseStep 37345931 = 56018897) B56018897
theorem B613972709 : Blo 1817610 613972709 := bstep (se 4 (by rfl) ⟨57559941, by rfl⟩ : syracuseStep 613972709 = 115119883) B115119883
theorem B79748135 : Blo 1817610 79748135 := bstep (se 1 (by rfl) ⟨59811101, by rfl⟩ : syracuseStep 79748135 = 119622203) B119622203
theorem B10361915 : Blo 1817610 10361915 := bstep (se 1 (by rfl) ⟨7771436, by rfl⟩ : syracuseStep 10361915 = 15542873) B15542873
theorem B6134939 : Blo 1817610 6134939 := bstep (se 1 (by rfl) ⟨4601204, by rfl⟩ : syracuseStep 6134939 = 9202409) B9202409
theorem B1842431 : Blo 1817610 1842431 := bstep (se 1 (by rfl) ⟨1381823, by rfl⟩ : syracuseStep 1842431 = 2763647) B2763647
theorem B2727323 : Blo 1817610 2727323 := bstep (se 1 (by rfl) ⟨2045492, by rfl⟩ : syracuseStep 2727323 = 4090985) B4090985
theorem B1818271 : Blo 1817610 1818271 := bstep (se 1 (by rfl) ⟨1363703, by rfl⟩ : syracuseStep 1818271 = 2727407) B2727407
theorem B10354877 : Blo 1817610 10354877 := bstep (se 3 (by rfl) ⟨1941539, by rfl⟩ : syracuseStep 10354877 = 3883079) B3883079
theorem B1818943 : Blo 1817610 1818943 := bstep (se 1 (by rfl) ⟨1364207, by rfl⟩ : syracuseStep 1818943 = 2728415) B2728415
theorem B1819327 : Blo 1817610 1819327 := bstep (se 1 (by rfl) ⟨1364495, by rfl⟩ : syracuseStep 1819327 = 2728991) B2728991
theorem B4605083 : Blo 1817610 4605083 := bstep (se 1 (by rfl) ⟨3453812, by rfl⟩ : syracuseStep 4605083 = 6907625) B6907625
theorem B6137423 : Blo 1817610 6137423 := bstep (se 1 (by rfl) ⟨4603067, by rfl⟩ : syracuseStep 6137423 = 9206135) B9206135
theorem B3278561 : Blo 1817610 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B24897287 : Blo 1817610 24897287 := bstep (se 1 (by rfl) ⟨18672965, by rfl⟩ : syracuseStep 24897287 = 37345931) B37345931
theorem B409315139 : Blo 1817610 409315139 := bstep (se 1 (by rfl) ⟨306986354, by rfl⟩ : syracuseStep 409315139 = 613972709) B613972709
theorem B6907943 : Blo 1817610 6907943 := bstep (se 1 (by rfl) ⟨5180957, by rfl⟩ : syracuseStep 6907943 = 10361915) B10361915
theorem B4089959 : Blo 1817610 4089959 := bstep (se 1 (by rfl) ⟨3067469, by rfl⟩ : syracuseStep 4089959 = 6134939) B6134939
theorem B2727929 : Blo 1817610 2727929 := bstep (se 2 (by rfl) ⟨1022973, by rfl⟩ : syracuseStep 2727929 = 2045947) B2045947
theorem B3067375 : Blo 1817610 3067375 := bstep (se 1 (by rfl) ⟨2300531, by rfl⟩ : syracuseStep 3067375 = 4601063) B4601063
theorem B11653055 : Blo 1817610 11653055 := bstep (se 1 (by rfl) ⟨8739791, by rfl⟩ : syracuseStep 11653055 = 17479583) B17479583
theorem B179318873 : Blo 1817610 179318873 := bstep (se 2 (by rfl) ⟨67244577, by rfl⟩ : syracuseStep 179318873 = 134489155) B134489155
theorem B3453167 : Blo 1817610 3453167 := bstep (se 1 (by rfl) ⟨2589875, by rfl⟩ : syracuseStep 3453167 = 5179751) B5179751
theorem B10645931 : Blo 1817610 10645931 := bstep (se 1 (by rfl) ⟨7984448, by rfl⟩ : syracuseStep 10645931 = 15968897) B15968897
theorem B3322343 : Blo 1817610 3322343 := bstep (se 1 (by rfl) ⟨2491757, by rfl⟩ : syracuseStep 3322343 = 4983515) B4983515
theorem B11055851 : Blo 1817610 11055851 := bstep (se 1 (by rfl) ⟨8291888, by rfl⟩ : syracuseStep 11055851 = 16583777) B16583777
theorem B11973575 : Blo 1817610 11973575 := bstep (se 1 (by rfl) ⟨8980181, by rfl⟩ : syracuseStep 11973575 = 17960363) B17960363
theorem B9204839 : Blo 1817610 9204839 := bstep (se 1 (by rfl) ⟨6903629, by rfl⟩ : syracuseStep 9204839 = 13807259) B13807259
theorem B61437491 : Blo 1817610 61437491 := bstep (se 1 (by rfl) ⟨46078118, by rfl⟩ : syracuseStep 61437491 = 92156237) B92156237
theorem B4913149 : Blo 1817610 4913149 := bstep (se 3 (by rfl) ⟨921215, by rfl⟩ : syracuseStep 4913149 = 1842431) B1842431
theorem B5527673 : Blo 1817610 5527673 := bstep (se 2 (by rfl) ⟨2072877, by rfl⟩ : syracuseStep 5527673 = 4145755) B4145755
theorem B15530129 : Blo 1817610 15530129 := bstep (se 2 (by rfl) ⟨5823798, by rfl⟩ : syracuseStep 15530129 = 11647597) B11647597
theorem B15538499 : Blo 1817610 15538499 := bstep (se 1 (by rfl) ⟨11653874, by rfl⟩ : syracuseStep 15538499 = 23307749) B23307749
theorem B53165423 : Blo 1817610 53165423 := bstep (se 1 (by rfl) ⟨39874067, by rfl⟩ : syracuseStep 53165423 = 79748135) B79748135
theorem B5823913 : Blo 1817610 5823913 := bstep (se 2 (by rfl) ⟨2183967, by rfl⟩ : syracuseStep 5823913 = 4367935) B4367935
theorem B1818215 : Blo 1817610 1818215 := bstep (se 1 (by rfl) ⟨1363661, by rfl⟩ : syracuseStep 1818215 = 2727323) B2727323
theorem B2727707 : Blo 1817610 2727707 := bstep (se 1 (by rfl) ⟨2045780, by rfl⟩ : syracuseStep 2727707 = 4091561) B4091561
theorem B125951867 : Blo 1817610 125951867 := bstep (se 1 (by rfl) ⟨94463900, by rfl⟩ : syracuseStep 125951867 = 188927801) B188927801
theorem B119545915 : Blo 1817610 119545915 := bstep (se 1 (by rfl) ⟨89659436, by rfl⟩ : syracuseStep 119545915 = 179318873) B179318873
theorem B2302111 : Blo 1817610 2302111 := bstep (se 1 (by rfl) ⟨1726583, by rfl⟩ : syracuseStep 2302111 = 3453167) B3453167
theorem B6136559 : Blo 1817610 6136559 := bstep (se 1 (by rfl) ⟨4602419, by rfl⟩ : syracuseStep 6136559 = 9204839) B9204839
theorem B16598191 : Blo 1817610 16598191 := bstep (se 1 (by rfl) ⟨12448643, by rfl⟩ : syracuseStep 16598191 = 24897287) B24897287
theorem B272876759 : Blo 1817610 272876759 := bstep (se 1 (by rfl) ⟨204657569, by rfl⟩ : syracuseStep 272876759 = 409315139) B409315139
theorem B4605295 : Blo 1817610 4605295 := bstep (se 1 (by rfl) ⟨3453971, by rfl⟩ : syracuseStep 4605295 = 6907943) B6907943
theorem B8742829 : Blo 1817610 8742829 := bstep (se 3 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 8742829 = 3278561) B3278561
theorem B4089833 : Blo 1817610 4089833 := bstep (se 2 (by rfl) ⟨1533687, by rfl⟩ : syracuseStep 4089833 = 3067375) B3067375
theorem B7768703 : Blo 1817610 7768703 := bstep (se 1 (by rfl) ⟨5826527, by rfl⟩ : syracuseStep 7768703 = 11653055) B11653055
theorem B7982383 : Blo 1817610 7982383 := bstep (se 1 (by rfl) ⟨5986787, by rfl⟩ : syracuseStep 7982383 = 11973575) B11973575
theorem B4091615 : Blo 1817610 4091615 := bstep (se 1 (by rfl) ⟨3068711, by rfl⟩ : syracuseStep 4091615 = 6137423) B6137423
theorem B28389149 : Blo 1817610 28389149 := bstep (se 3 (by rfl) ⟨5322965, by rfl⟩ : syracuseStep 28389149 = 10645931) B10645931
theorem B8859581 : Blo 1817610 8859581 := bstep (se 3 (by rfl) ⟨1661171, by rfl⟩ : syracuseStep 8859581 = 3322343) B3322343
theorem B10358999 : Blo 1817610 10358999 := bstep (se 1 (by rfl) ⟨7769249, by rfl⟩ : syracuseStep 10358999 = 15538499) B15538499
theorem B35443615 : Blo 1817610 35443615 := bstep (se 1 (by rfl) ⟨26582711, by rfl⟩ : syracuseStep 35443615 = 53165423) B53165423
theorem B6550865 : Blo 1817610 6550865 := bstep (se 2 (by rfl) ⟨2456574, by rfl⟩ : syracuseStep 6550865 = 4913149) B4913149
theorem B6903251 : Blo 1817610 6903251 := bstep (se 1 (by rfl) ⟨5177438, by rfl⟩ : syracuseStep 6903251 = 10354877) B10354877
theorem B7370567 : Blo 1817610 7370567 := bstep (se 1 (by rfl) ⟨5527925, by rfl⟩ : syracuseStep 7370567 = 11055851) B11055851
theorem B3070055 : Blo 1817610 3070055 := bstep (se 1 (by rfl) ⟨2302541, by rfl⟩ : syracuseStep 3070055 = 4605083) B4605083
theorem B40958327 : Blo 1817610 40958327 := bstep (se 1 (by rfl) ⟨30718745, by rfl⟩ : syracuseStep 40958327 = 61437491) B61437491
theorem B2726639 : Blo 1817610 2726639 := bstep (se 1 (by rfl) ⟨2044979, by rfl⟩ : syracuseStep 2726639 = 4089959) B4089959
theorem B3685115 : Blo 1817610 3685115 := bstep (se 1 (by rfl) ⟨2763836, by rfl⟩ : syracuseStep 3685115 = 5527673) B5527673
theorem B10353419 : Blo 1817610 10353419 := bstep (se 1 (by rfl) ⟨7765064, by rfl⟩ : syracuseStep 10353419 = 15530129) B15530129
theorem B7765217 : Blo 1817610 7765217 := bstep (se 2 (by rfl) ⟨2911956, by rfl⟩ : syracuseStep 7765217 = 5823913) B5823913
theorem B1818619 : Blo 1817610 1818619 := bstep (se 1 (by rfl) ⟨1363964, by rfl⟩ : syracuseStep 1818619 = 2727929) B2727929
theorem B1818471 : Blo 1817610 1818471 := bstep (se 1 (by rfl) ⟨1363853, by rfl⟩ : syracuseStep 1818471 = 2727707) B2727707
theorem B83967911 : Blo 1817610 83967911 := bstep (se 1 (by rfl) ⟨62975933, by rfl⟩ : syracuseStep 83967911 = 125951867) B125951867
theorem B6905999 : Blo 1817610 6905999 := bstep (se 1 (by rfl) ⟨5179499, by rfl⟩ : syracuseStep 6905999 = 10358999) B10358999
theorem B4367243 : Blo 1817610 4367243 := bstep (se 1 (by rfl) ⟨3275432, by rfl⟩ : syracuseStep 4367243 = 6550865) B6550865
theorem B27305551 : Blo 1817610 27305551 := bstep (se 1 (by rfl) ⟨20479163, by rfl⟩ : syracuseStep 27305551 = 40958327) B40958327
theorem B10643177 : Blo 1817610 10643177 := bstep (se 2 (by rfl) ⟨3991191, by rfl⟩ : syracuseStep 10643177 = 7982383) B7982383
theorem B5179135 : Blo 1817610 5179135 := bstep (se 1 (by rfl) ⟨3884351, by rfl⟩ : syracuseStep 5179135 = 7768703) B7768703
theorem B18926099 : Blo 1817610 18926099 := bstep (se 1 (by rfl) ⟨14194574, by rfl⟩ : syracuseStep 18926099 = 28389149) B28389149
theorem B55978607 : Blo 1817610 55978607 := bstep (se 1 (by rfl) ⟨41983955, by rfl⟩ : syracuseStep 55978607 = 83967911) B83967911
theorem B159394553 : Blo 1817610 159394553 := bstep (se 2 (by rfl) ⟨59772957, by rfl⟩ : syracuseStep 159394553 = 119545915) B119545915
theorem B4091039 : Blo 1817610 4091039 := bstep (se 1 (by rfl) ⟨3068279, by rfl⟩ : syracuseStep 4091039 = 6136559) B6136559
theorem B22130921 : Blo 1817610 22130921 := bstep (se 2 (by rfl) ⟨8299095, by rfl⟩ : syracuseStep 22130921 = 16598191) B16598191
theorem B6140393 : Blo 1817610 6140393 := bstep (se 2 (by rfl) ⟨2302647, by rfl⟩ : syracuseStep 6140393 = 4605295) B4605295
theorem B6902279 : Blo 1817610 6902279 := bstep (se 1 (by rfl) ⟨5176709, by rfl⟩ : syracuseStep 6902279 = 10353419) B10353419
theorem B3069481 : Blo 1817610 3069481 := bstep (se 2 (by rfl) ⟨1151055, by rfl⟩ : syracuseStep 3069481 = 2302111) B2302111
theorem B181917839 : Blo 1817610 181917839 := bstep (se 1 (by rfl) ⟨136438379, by rfl⟩ : syracuseStep 181917839 = 272876759) B272876759
theorem B4602167 : Blo 1817610 4602167 := bstep (se 1 (by rfl) ⟨3451625, by rfl⟩ : syracuseStep 4602167 = 6903251) B6903251
theorem B47258153 : Blo 1817610 47258153 := bstep (se 2 (by rfl) ⟨17721807, by rfl⟩ : syracuseStep 47258153 = 35443615) B35443615
theorem B4913711 : Blo 1817610 4913711 := bstep (se 1 (by rfl) ⟨3685283, by rfl⟩ : syracuseStep 4913711 = 7370567) B7370567
theorem B2726555 : Blo 1817610 2726555 := bstep (se 1 (by rfl) ⟨2044916, by rfl⟩ : syracuseStep 2726555 = 4089833) B4089833
theorem B2046703 : Blo 1817610 2046703 := bstep (se 1 (by rfl) ⟨1535027, by rfl⟩ : syracuseStep 2046703 = 3070055) B3070055
theorem B1817759 : Blo 1817610 1817759 := bstep (se 1 (by rfl) ⟨1363319, by rfl⟩ : syracuseStep 1817759 = 2726639) B2726639
theorem B2456743 : Blo 1817610 2456743 := bstep (se 1 (by rfl) ⟨1842557, by rfl⟩ : syracuseStep 2456743 = 3685115) B3685115
theorem B5176811 : Blo 1817610 5176811 := bstep (se 1 (by rfl) ⟨3882608, by rfl⟩ : syracuseStep 5176811 = 7765217) B7765217
theorem B2727743 : Blo 1817610 2727743 := bstep (se 1 (by rfl) ⟨2045807, by rfl⟩ : syracuseStep 2727743 = 4091615) B4091615
theorem B11657105 : Blo 1817610 11657105 := bstep (se 2 (by rfl) ⟨4371414, by rfl⟩ : syracuseStep 11657105 = 8742829) B8742829
theorem B5906387 : Blo 1817610 5906387 := bstep (se 1 (by rfl) ⟨4429790, by rfl⟩ : syracuseStep 5906387 = 8859581) B8859581
theorem B4603999 : Blo 1817610 4603999 := bstep (se 1 (by rfl) ⟨3452999, by rfl⟩ : syracuseStep 4603999 = 6905999) B6905999
theorem B14753947 : Blo 1817610 14753947 := bstep (se 1 (by rfl) ⟨11065460, by rfl⟩ : syracuseStep 14753947 = 22130921) B22130921
theorem B2728937 : Blo 1817610 2728937 := bstep (se 2 (by rfl) ⟨1023351, by rfl⟩ : syracuseStep 2728937 = 2046703) B2046703
theorem B7095451 : Blo 1817610 7095451 := bstep (se 1 (by rfl) ⟨5321588, by rfl⟩ : syracuseStep 7095451 = 10643177) B10643177
theorem B13804829 : Blo 1817610 13804829 := bstep (se 3 (by rfl) ⟨2588405, by rfl⟩ : syracuseStep 13804829 = 5176811) B5176811
theorem B12617399 : Blo 1817610 12617399 := bstep (se 1 (by rfl) ⟨9463049, by rfl⟩ : syracuseStep 12617399 = 18926099) B18926099
theorem B36407401 : Blo 1817610 36407401 := bstep (se 2 (by rfl) ⟨13652775, by rfl⟩ : syracuseStep 36407401 = 27305551) B27305551
theorem B121278559 : Blo 1817610 121278559 := bstep (se 1 (by rfl) ⟨90958919, by rfl⟩ : syracuseStep 121278559 = 181917839) B181917839
theorem B3068111 : Blo 1817610 3068111 := bstep (se 1 (by rfl) ⟨2301083, by rfl⟩ : syracuseStep 3068111 = 4602167) B4602167
theorem B37319071 : Blo 1817610 37319071 := bstep (se 1 (by rfl) ⟨27989303, by rfl⟩ : syracuseStep 37319071 = 55978607) B55978607
theorem B106263035 : Blo 1817610 106263035 := bstep (se 1 (by rfl) ⟨79697276, by rfl⟩ : syracuseStep 106263035 = 159394553) B159394553
theorem B4092641 : Blo 1817610 4092641 := bstep (se 2 (by rfl) ⟨1534740, by rfl⟩ : syracuseStep 4092641 = 3069481) B3069481
theorem B11645981 : Blo 1817610 11645981 := bstep (se 3 (by rfl) ⟨2183621, by rfl⟩ : syracuseStep 11645981 = 4367243) B4367243
theorem B7771403 : Blo 1817610 7771403 := bstep (se 1 (by rfl) ⟨5828552, by rfl⟩ : syracuseStep 7771403 = 11657105) B11657105
theorem B3937591 : Blo 1817610 3937591 := bstep (se 1 (by rfl) ⟨2953193, by rfl⟩ : syracuseStep 3937591 = 5906387) B5906387
theorem B4093595 : Blo 1817610 4093595 := bstep (se 1 (by rfl) ⟨3070196, by rfl⟩ : syracuseStep 4093595 = 6140393) B6140393
theorem B4601519 : Blo 1817610 4601519 := bstep (se 1 (by rfl) ⟨3451139, by rfl⟩ : syracuseStep 4601519 = 6902279) B6902279
theorem B3275657 : Blo 1817610 3275657 := bstep (se 2 (by rfl) ⟨1228371, by rfl⟩ : syracuseStep 3275657 = 2456743) B2456743
theorem B31505435 : Blo 1817610 31505435 := bstep (se 1 (by rfl) ⟨23629076, by rfl⟩ : syracuseStep 31505435 = 47258153) B47258153
theorem B3275807 : Blo 1817610 3275807 := bstep (se 1 (by rfl) ⟨2456855, by rfl⟩ : syracuseStep 3275807 = 4913711) B4913711
theorem B1817703 : Blo 1817610 1817703 := bstep (se 1 (by rfl) ⟨1363277, by rfl⟩ : syracuseStep 1817703 = 2726555) B2726555
theorem B2727359 : Blo 1817610 2727359 := bstep (se 1 (by rfl) ⟨2045519, by rfl⟩ : syracuseStep 2727359 = 4091039) B4091039
theorem B6905513 : Blo 1817610 6905513 := bstep (se 2 (by rfl) ⟨2589567, by rfl⟩ : syracuseStep 6905513 = 5179135) B5179135
theorem B1818495 : Blo 1817610 1818495 := bstep (se 1 (by rfl) ⟨1363871, by rfl⟩ : syracuseStep 1818495 = 2727743) B2727743
theorem B2728427 : Blo 1817610 2728427 := bstep (se 1 (by rfl) ⟨2046320, by rfl⟩ : syracuseStep 2728427 = 4092641) B4092641
theorem B49758761 : Blo 1817610 49758761 := bstep (se 2 (by rfl) ⟨18659535, by rfl⟩ : syracuseStep 49758761 = 37319071) B37319071
theorem B1819291 : Blo 1817610 1819291 := bstep (se 1 (by rfl) ⟨1364468, by rfl⟩ : syracuseStep 1819291 = 2728937) B2728937
theorem B2729063 : Blo 1817610 2729063 := bstep (se 1 (by rfl) ⟨2046797, by rfl⟩ : syracuseStep 2729063 = 4093595) B4093595
theorem B33646397 : Blo 1817610 33646397 := bstep (se 3 (by rfl) ⟨6308699, by rfl⟩ : syracuseStep 33646397 = 12617399) B12617399
theorem B6138665 : Blo 1817610 6138665 := bstep (se 2 (by rfl) ⟨2301999, by rfl⟩ : syracuseStep 6138665 = 4603999) B4603999
theorem B161704745 : Blo 1817610 161704745 := bstep (se 2 (by rfl) ⟨60639279, by rfl⟩ : syracuseStep 161704745 = 121278559) B121278559
theorem B19671929 : Blo 1817610 19671929 := bstep (se 2 (by rfl) ⟨7376973, by rfl⟩ : syracuseStep 19671929 = 14753947) B14753947
theorem B34941941 : Blo 1817610 34941941 := bstep (se 5 (by rfl) ⟨1637903, by rfl⟩ : syracuseStep 34941941 = 3275807) B3275807
theorem B5180935 : Blo 1817610 5180935 := bstep (se 1 (by rfl) ⟨3885701, by rfl⟩ : syracuseStep 5180935 = 7771403) B7771403
theorem B9203219 : Blo 1817610 9203219 := bstep (se 1 (by rfl) ⟨6902414, by rfl⟩ : syracuseStep 9203219 = 13804829) B13804829
theorem B3067679 : Blo 1817610 3067679 := bstep (se 1 (by rfl) ⟨2300759, by rfl⟩ : syracuseStep 3067679 = 4601519) B4601519
theorem B21000485 : Blo 1817610 21000485 := bstep (se 4 (by rfl) ⟨1968795, by rfl⟩ : syracuseStep 21000485 = 3937591) B3937591
theorem B2183771 : Blo 1817610 2183771 := bstep (se 1 (by rfl) ⟨1637828, by rfl⟩ : syracuseStep 2183771 = 3275657) B3275657
theorem B2045407 : Blo 1817610 2045407 := bstep (se 1 (by rfl) ⟨1534055, by rfl⟩ : syracuseStep 2045407 = 3068111) B3068111
theorem B70842023 : Blo 1817610 70842023 := bstep (se 1 (by rfl) ⟨53131517, by rfl⟩ : syracuseStep 70842023 = 106263035) B106263035
theorem B194172805 : Blo 1817610 194172805 := bstep (se 4 (by rfl) ⟨18203700, by rfl⟩ : syracuseStep 194172805 = 36407401) B36407401
theorem B7763987 : Blo 1817610 7763987 := bstep (se 1 (by rfl) ⟨5822990, by rfl⟩ : syracuseStep 7763987 = 11645981) B11645981
theorem B9460601 : Blo 1817610 9460601 := bstep (se 2 (by rfl) ⟨3547725, by rfl⟩ : syracuseStep 9460601 = 7095451) B7095451
theorem B21003623 : Blo 1817610 21003623 := bstep (se 1 (by rfl) ⟨15752717, by rfl⟩ : syracuseStep 21003623 = 31505435) B31505435
theorem B1818239 : Blo 1817610 1818239 := bstep (se 1 (by rfl) ⟨1363679, by rfl⟩ : syracuseStep 1818239 = 2727359) B2727359
theorem B4603675 : Blo 1817610 4603675 := bstep (se 1 (by rfl) ⟨3452756, by rfl⟩ : syracuseStep 4603675 = 6905513) B6905513
theorem B1818951 : Blo 1817610 1818951 := bstep (se 1 (by rfl) ⟨1364213, by rfl⟩ : syracuseStep 1818951 = 2728427) B2728427
theorem B1819375 : Blo 1817610 1819375 := bstep (se 1 (by rfl) ⟨1364531, by rfl⟩ : syracuseStep 1819375 = 2729063) B2729063
theorem B56001293 : Blo 1817610 56001293 := bstep (se 3 (by rfl) ⟨10500242, by rfl⟩ : syracuseStep 56001293 = 21000485) B21000485
theorem B47228015 : Blo 1817610 47228015 := bstep (se 1 (by rfl) ⟨35421011, by rfl⟩ : syracuseStep 47228015 = 70842023) B70842023
theorem B6907913 : Blo 1817610 6907913 := bstep (se 2 (by rfl) ⟨2590467, by rfl⟩ : syracuseStep 6907913 = 5180935) B5180935
theorem B14002415 : Blo 1817610 14002415 := bstep (se 1 (by rfl) ⟨10501811, by rfl⟩ : syracuseStep 14002415 = 21003623) B21003623
theorem B6138233 : Blo 1817610 6138233 := bstep (se 2 (by rfl) ⟨2301837, by rfl⟩ : syracuseStep 6138233 = 4603675) B4603675
theorem B33172507 : Blo 1817610 33172507 := bstep (se 1 (by rfl) ⟨24879380, by rfl⟩ : syracuseStep 33172507 = 49758761) B49758761
theorem B358894901 : Blo 1817610 358894901 := bstep (se 5 (by rfl) ⟨16823198, by rfl⟩ : syracuseStep 358894901 = 33646397) B33646397
theorem B4092443 : Blo 1817610 4092443 := bstep (se 1 (by rfl) ⟨3069332, by rfl⟩ : syracuseStep 4092443 = 6138665) B6138665
theorem B107803163 : Blo 1817610 107803163 := bstep (se 1 (by rfl) ⟨80852372, by rfl⟩ : syracuseStep 107803163 = 161704745) B161704745
theorem B23294627 : Blo 1817610 23294627 := bstep (se 1 (by rfl) ⟨17470970, by rfl⟩ : syracuseStep 23294627 = 34941941) B34941941
theorem B258897073 : Blo 1817610 258897073 := bstep (se 2 (by rfl) ⟨97086402, by rfl⟩ : syracuseStep 258897073 = 194172805) B194172805
theorem B2045119 : Blo 1817610 2045119 := bstep (se 1 (by rfl) ⟨1533839, by rfl⟩ : syracuseStep 2045119 = 3067679) B3067679
theorem B5175991 : Blo 1817610 5175991 := bstep (se 1 (by rfl) ⟨3881993, by rfl⟩ : syracuseStep 5175991 = 7763987) B7763987
theorem B5823389 : Blo 1817610 5823389 := bstep (se 3 (by rfl) ⟨1091885, by rfl⟩ : syracuseStep 5823389 = 2183771) B2183771
theorem B6307067 : Blo 1817610 6307067 := bstep (se 1 (by rfl) ⟨4730300, by rfl⟩ : syracuseStep 6307067 = 9460601) B9460601
theorem B13114619 : Blo 1817610 13114619 := bstep (se 1 (by rfl) ⟨9835964, by rfl⟩ : syracuseStep 13114619 = 19671929) B19671929
theorem B2727209 : Blo 1817610 2727209 := bstep (se 2 (by rfl) ⟨1022703, by rfl⟩ : syracuseStep 2727209 = 2045407) B2045407
theorem B6135479 : Blo 1817610 6135479 := bstep (se 1 (by rfl) ⟨4601609, by rfl⟩ : syracuseStep 6135479 = 9203219) B9203219
theorem B2728295 : Blo 1817610 2728295 := bstep (se 1 (by rfl) ⟨2046221, by rfl⟩ : syracuseStep 2728295 = 4092443) B4092443
theorem B71868775 : Blo 1817610 71868775 := bstep (se 1 (by rfl) ⟨53901581, by rfl⟩ : syracuseStep 71868775 = 107803163) B107803163
theorem B4605275 : Blo 1817610 4605275 := bstep (se 1 (by rfl) ⟨3453956, by rfl⟩ : syracuseStep 4605275 = 6907913) B6907913
theorem B44230009 : Blo 1817610 44230009 := bstep (se 2 (by rfl) ⟨16586253, by rfl⟩ : syracuseStep 44230009 = 33172507) B33172507
theorem B345196097 : Blo 1817610 345196097 := bstep (se 2 (by rfl) ⟨129448536, by rfl⟩ : syracuseStep 345196097 = 258897073) B258897073
theorem B4204711 : Blo 1817610 4204711 := bstep (se 1 (by rfl) ⟨3153533, by rfl⟩ : syracuseStep 4204711 = 6307067) B6307067
theorem B8743079 : Blo 1817610 8743079 := bstep (se 1 (by rfl) ⟨6557309, by rfl⟩ : syracuseStep 8743079 = 13114619) B13114619
theorem B4090319 : Blo 1817610 4090319 := bstep (se 1 (by rfl) ⟨3067739, by rfl⟩ : syracuseStep 4090319 = 6135479) B6135479
theorem B37334195 : Blo 1817610 37334195 := bstep (se 1 (by rfl) ⟨28000646, by rfl⟩ : syracuseStep 37334195 = 56001293) B56001293
theorem B31485343 : Blo 1817610 31485343 := bstep (se 1 (by rfl) ⟨23614007, by rfl⟩ : syracuseStep 31485343 = 47228015) B47228015
theorem B6901321 : Blo 1817610 6901321 := bstep (se 2 (by rfl) ⟨2587995, by rfl⟩ : syracuseStep 6901321 = 5175991) B5175991
theorem B9334943 : Blo 1817610 9334943 := bstep (se 1 (by rfl) ⟨7001207, by rfl⟩ : syracuseStep 9334943 = 14002415) B14002415
theorem B4092155 : Blo 1817610 4092155 := bstep (se 1 (by rfl) ⟨3069116, by rfl⟩ : syracuseStep 4092155 = 6138233) B6138233
theorem B15529751 : Blo 1817610 15529751 := bstep (se 1 (by rfl) ⟨11647313, by rfl⟩ : syracuseStep 15529751 = 23294627) B23294627
theorem B2726825 : Blo 1817610 2726825 := bstep (se 2 (by rfl) ⟨1022559, by rfl⟩ : syracuseStep 2726825 = 2045119) B2045119
theorem B3882259 : Blo 1817610 3882259 := bstep (se 1 (by rfl) ⟨2911694, by rfl⟩ : syracuseStep 3882259 = 5823389) B5823389
theorem B1818139 : Blo 1817610 1818139 := bstep (se 1 (by rfl) ⟨1363604, by rfl⟩ : syracuseStep 1818139 = 2727209) B2727209
theorem B239263267 : Blo 1817610 239263267 := bstep (se 1 (by rfl) ⟨179447450, by rfl⟩ : syracuseStep 239263267 = 358894901) B358894901
theorem B2728103 : Blo 1817610 2728103 := bstep (se 1 (by rfl) ⟨2046077, by rfl⟩ : syracuseStep 2728103 = 4092155) B4092155
theorem B1818863 : Blo 1817610 1818863 := bstep (se 1 (by rfl) ⟨1364147, by rfl⟩ : syracuseStep 1818863 = 2728295) B2728295
theorem B23314877 : Blo 1817610 23314877 := bstep (se 3 (by rfl) ⟨4371539, by rfl⟩ : syracuseStep 23314877 = 8743079) B8743079
theorem B230130731 : Blo 1817610 230130731 := bstep (se 1 (by rfl) ⟨172598048, by rfl⟩ : syracuseStep 230130731 = 345196097) B345196097
theorem B9201761 : Blo 1817610 9201761 := bstep (se 2 (by rfl) ⟨3450660, by rfl⟩ : syracuseStep 9201761 = 6901321) B6901321
theorem B24889463 : Blo 1817610 24889463 := bstep (se 1 (by rfl) ⟨18667097, by rfl⟩ : syracuseStep 24889463 = 37334195) B37334195
theorem B5606281 : Blo 1817610 5606281 := bstep (se 2 (by rfl) ⟨2102355, by rfl⟩ : syracuseStep 5606281 = 4204711) B4204711
theorem B95825033 : Blo 1817610 95825033 := bstep (se 2 (by rfl) ⟨35934387, by rfl⟩ : syracuseStep 95825033 = 71868775) B71868775
theorem B41980457 : Blo 1817610 41980457 := bstep (se 2 (by rfl) ⟨15742671, by rfl⟩ : syracuseStep 41980457 = 31485343) B31485343
theorem B319017689 : Blo 1817610 319017689 := bstep (se 2 (by rfl) ⟨119631633, by rfl⟩ : syracuseStep 319017689 = 239263267) B239263267
theorem B6223295 : Blo 1817610 6223295 := bstep (se 1 (by rfl) ⟨4667471, by rfl⟩ : syracuseStep 6223295 = 9334943) B9334943
theorem B3070183 : Blo 1817610 3070183 := bstep (se 1 (by rfl) ⟨2302637, by rfl⟩ : syracuseStep 3070183 = 4605275) B4605275
theorem B10353167 : Blo 1817610 10353167 := bstep (se 1 (by rfl) ⟨7764875, by rfl⟩ : syracuseStep 10353167 = 15529751) B15529751
theorem B2726879 : Blo 1817610 2726879 := bstep (se 1 (by rfl) ⟨2045159, by rfl⟩ : syracuseStep 2726879 = 4090319) B4090319
theorem B5176345 : Blo 1817610 5176345 := bstep (se 2 (by rfl) ⟨1941129, by rfl⟩ : syracuseStep 5176345 = 3882259) B3882259
theorem B58973345 : Blo 1817610 58973345 := bstep (se 2 (by rfl) ⟨22115004, by rfl⟩ : syracuseStep 58973345 = 44230009) B44230009
theorem B1817883 : Blo 1817610 1817883 := bstep (se 1 (by rfl) ⟨1363412, by rfl⟩ : syracuseStep 1817883 = 2726825) B2726825
theorem B1818735 : Blo 1817610 1818735 := bstep (se 1 (by rfl) ⟨1364051, by rfl⟩ : syracuseStep 1818735 = 2728103) B2728103
theorem B63883355 : Blo 1817610 63883355 := bstep (se 1 (by rfl) ⟨47912516, by rfl⟩ : syracuseStep 63883355 = 95825033) B95825033
theorem B39315563 : Blo 1817610 39315563 := bstep (se 1 (by rfl) ⟨29486672, by rfl⟩ : syracuseStep 39315563 = 58973345) B58973345
theorem B613681949 : Blo 1817610 613681949 := bstep (se 3 (by rfl) ⟨115065365, by rfl⟩ : syracuseStep 613681949 = 230130731) B230130731
theorem B15543251 : Blo 1817610 15543251 := bstep (se 1 (by rfl) ⟨11657438, by rfl⟩ : syracuseStep 15543251 = 23314877) B23314877
theorem B27986971 : Blo 1817610 27986971 := bstep (se 1 (by rfl) ⟨20990228, by rfl⟩ : syracuseStep 27986971 = 41980457) B41980457
theorem B4148863 : Blo 1817610 4148863 := bstep (se 1 (by rfl) ⟨3111647, by rfl⟩ : syracuseStep 4148863 = 6223295) B6223295
theorem B7475041 : Blo 1817610 7475041 := bstep (se 2 (by rfl) ⟨2803140, by rfl⟩ : syracuseStep 7475041 = 5606281) B5606281
theorem B6901793 : Blo 1817610 6901793 := bstep (se 2 (by rfl) ⟨2588172, by rfl⟩ : syracuseStep 6901793 = 5176345) B5176345
theorem B16592975 : Blo 1817610 16592975 := bstep (se 1 (by rfl) ⟨12444731, by rfl⟩ : syracuseStep 16592975 = 24889463) B24889463
theorem B6902111 : Blo 1817610 6902111 := bstep (se 1 (by rfl) ⟨5176583, by rfl⟩ : syracuseStep 6902111 = 10353167) B10353167
theorem B4093577 : Blo 1817610 4093577 := bstep (se 2 (by rfl) ⟨1535091, by rfl⟩ : syracuseStep 4093577 = 3070183) B3070183
theorem B212678459 : Blo 1817610 212678459 := bstep (se 1 (by rfl) ⟨159508844, by rfl⟩ : syracuseStep 212678459 = 319017689) B319017689
theorem B6134507 : Blo 1817610 6134507 := bstep (se 1 (by rfl) ⟨4600880, by rfl⟩ : syracuseStep 6134507 = 9201761) B9201761
theorem B1817919 : Blo 1817610 1817919 := bstep (se 1 (by rfl) ⟨1363439, by rfl⟩ : syracuseStep 1817919 = 2726879) B2726879
theorem B22127269 : Blo 1817610 22127269 := bstep (se 4 (by rfl) ⟨2074431, by rfl⟩ : syracuseStep 22127269 = 4148863) B4148863
theorem B2729051 : Blo 1817610 2729051 := bstep (se 1 (by rfl) ⟨2046788, by rfl⟩ : syracuseStep 2729051 = 4093577) B4093577
theorem B37315961 : Blo 1817610 37315961 := bstep (se 2 (by rfl) ⟨13993485, by rfl⟩ : syracuseStep 37315961 = 27986971) B27986971
theorem B4089671 : Blo 1817610 4089671 := bstep (se 1 (by rfl) ⟨3067253, by rfl⟩ : syracuseStep 4089671 = 6134507) B6134507
theorem B1636485197 : Blo 1817610 1636485197 := bstep (se 3 (by rfl) ⟨306840974, by rfl⟩ : syracuseStep 1636485197 = 613681949) B613681949
theorem B11061983 : Blo 1817610 11061983 := bstep (se 1 (by rfl) ⟨8296487, by rfl⟩ : syracuseStep 11061983 = 16592975) B16592975
theorem B681422453 : Blo 1817610 681422453 := bstep (se 5 (by rfl) ⟨31941677, by rfl⟩ : syracuseStep 681422453 = 63883355) B63883355
theorem B26210375 : Blo 1817610 26210375 := bstep (se 1 (by rfl) ⟨19657781, by rfl⟩ : syracuseStep 26210375 = 39315563) B39315563
theorem B9966721 : Blo 1817610 9966721 := bstep (se 2 (by rfl) ⟨3737520, by rfl⟩ : syracuseStep 9966721 = 7475041) B7475041
theorem B4601195 : Blo 1817610 4601195 := bstep (se 1 (by rfl) ⟨3450896, by rfl⟩ : syracuseStep 4601195 = 6901793) B6901793
theorem B4601407 : Blo 1817610 4601407 := bstep (se 1 (by rfl) ⟨3451055, by rfl⟩ : syracuseStep 4601407 = 6902111) B6902111
theorem B141785639 : Blo 1817610 141785639 := bstep (se 1 (by rfl) ⟨106339229, by rfl⟩ : syracuseStep 141785639 = 212678459) B212678459
theorem B10362167 : Blo 1817610 10362167 := bstep (se 1 (by rfl) ⟨7771625, by rfl⟩ : syracuseStep 10362167 = 15543251) B15543251
theorem B17473583 : Blo 1817610 17473583 := bstep (se 1 (by rfl) ⟨13105187, by rfl⟩ : syracuseStep 17473583 = 26210375) B26210375
theorem B1819367 : Blo 1817610 1819367 := bstep (se 1 (by rfl) ⟨1364525, by rfl⟩ : syracuseStep 1819367 = 2729051) B2729051
theorem B17455842101 : Blo 1817610 17455842101 := bstep (se 5 (by rfl) ⟨818242598, by rfl⟩ : syracuseStep 17455842101 = 1636485197) B1636485197
theorem B13288961 : Blo 1817610 13288961 := bstep (se 2 (by rfl) ⟨4983360, by rfl⟩ : syracuseStep 13288961 = 9966721) B9966721
theorem B7374655 : Blo 1817610 7374655 := bstep (se 1 (by rfl) ⟨5530991, by rfl⟩ : syracuseStep 7374655 = 11061983) B11061983
theorem B6908111 : Blo 1817610 6908111 := bstep (se 1 (by rfl) ⟨5181083, by rfl⟩ : syracuseStep 6908111 = 10362167) B10362167
theorem B454281635 : Blo 1817610 454281635 := bstep (se 1 (by rfl) ⟨340711226, by rfl⟩ : syracuseStep 454281635 = 681422453) B681422453
theorem B29503025 : Blo 1817610 29503025 := bstep (se 2 (by rfl) ⟨11063634, by rfl⟩ : syracuseStep 29503025 = 22127269) B22127269
theorem B3067463 : Blo 1817610 3067463 := bstep (se 1 (by rfl) ⟨2300597, by rfl⟩ : syracuseStep 3067463 = 4601195) B4601195
theorem B94523759 : Blo 1817610 94523759 := bstep (se 1 (by rfl) ⟨70892819, by rfl⟩ : syracuseStep 94523759 = 141785639) B141785639
theorem B24877307 : Blo 1817610 24877307 := bstep (se 1 (by rfl) ⟨18657980, by rfl⟩ : syracuseStep 24877307 = 37315961) B37315961
theorem B2726447 : Blo 1817610 2726447 := bstep (se 1 (by rfl) ⟨2044835, by rfl⟩ : syracuseStep 2726447 = 4089671) B4089671
theorem B6135209 : Blo 1817610 6135209 := bstep (se 2 (by rfl) ⟨2300703, by rfl⟩ : syracuseStep 6135209 = 4601407) B4601407
theorem B46596221 : Blo 1817610 46596221 := bstep (se 3 (by rfl) ⟨8736791, by rfl⟩ : syracuseStep 46596221 = 17473583) B17473583
theorem B4605407 : Blo 1817610 4605407 := bstep (se 1 (by rfl) ⟨3454055, by rfl⟩ : syracuseStep 4605407 = 6908111) B6908111
theorem B46548912269 : Blo 1817610 46548912269 := bstep (se 3 (by rfl) ⟨8727921050, by rfl⟩ : syracuseStep 46548912269 = 17455842101) B17455842101
theorem B4090139 : Blo 1817610 4090139 := bstep (se 1 (by rfl) ⟨3067604, by rfl⟩ : syracuseStep 4090139 = 6135209) B6135209
theorem B9832873 : Blo 1817610 9832873 := bstep (se 2 (by rfl) ⟨3687327, by rfl⟩ : syracuseStep 9832873 = 7374655) B7374655
theorem B63015839 : Blo 1817610 63015839 := bstep (se 1 (by rfl) ⟨47261879, by rfl⟩ : syracuseStep 63015839 = 94523759) B94523759
theorem B8859307 : Blo 1817610 8859307 := bstep (se 1 (by rfl) ⟨6644480, by rfl⟩ : syracuseStep 8859307 = 13288961) B13288961
theorem B16584871 : Blo 1817610 16584871 := bstep (se 1 (by rfl) ⟨12438653, by rfl⟩ : syracuseStep 16584871 = 24877307) B24877307
theorem B302854423 : Blo 1817610 302854423 := bstep (se 1 (by rfl) ⟨227140817, by rfl⟩ : syracuseStep 302854423 = 454281635) B454281635
theorem B2044975 : Blo 1817610 2044975 := bstep (se 1 (by rfl) ⟨1533731, by rfl⟩ : syracuseStep 2044975 = 3067463) B3067463
theorem B1817631 : Blo 1817610 1817631 := bstep (se 1 (by rfl) ⟨1363223, by rfl⟩ : syracuseStep 1817631 = 2726447) B2726447
theorem B19668683 : Blo 1817610 19668683 := bstep (se 1 (by rfl) ⟨14751512, by rfl⟩ : syracuseStep 19668683 = 29503025) B29503025
theorem B31064147 : Blo 1817610 31064147 := bstep (se 1 (by rfl) ⟨23298110, by rfl⟩ : syracuseStep 31064147 = 46596221) B46596221
theorem B31032608179 : Blo 1817610 31032608179 := bstep (se 1 (by rfl) ⟨23274456134, by rfl⟩ : syracuseStep 31032608179 = 46548912269) B46548912269
theorem B42010559 : Blo 1817610 42010559 := bstep (se 1 (by rfl) ⟨31507919, by rfl⟩ : syracuseStep 42010559 = 63015839) B63015839
theorem B22113161 : Blo 1817610 22113161 := bstep (se 2 (by rfl) ⟨8292435, by rfl⟩ : syracuseStep 22113161 = 16584871) B16584871
theorem B13110497 : Blo 1817610 13110497 := bstep (se 2 (by rfl) ⟨4916436, by rfl⟩ : syracuseStep 13110497 = 9832873) B9832873
theorem B13112455 : Blo 1817610 13112455 := bstep (se 1 (by rfl) ⟨9834341, by rfl⟩ : syracuseStep 13112455 = 19668683) B19668683
theorem B403805897 : Blo 1817610 403805897 := bstep (se 2 (by rfl) ⟨151427211, by rfl⟩ : syracuseStep 403805897 = 302854423) B302854423
theorem B3070271 : Blo 1817610 3070271 := bstep (se 1 (by rfl) ⟨2302703, by rfl⟩ : syracuseStep 3070271 = 4605407) B4605407
theorem B2726633 : Blo 1817610 2726633 := bstep (se 2 (by rfl) ⟨1022487, by rfl⟩ : syracuseStep 2726633 = 2044975) B2044975
theorem B2726759 : Blo 1817610 2726759 := bstep (se 1 (by rfl) ⟨2045069, by rfl⟩ : syracuseStep 2726759 = 4090139) B4090139
theorem B11812409 : Blo 1817610 11812409 := bstep (se 2 (by rfl) ⟨4429653, by rfl⟩ : syracuseStep 11812409 = 8859307) B8859307
theorem B20709431 : Blo 1817610 20709431 := bstep (se 1 (by rfl) ⟨15532073, by rfl⟩ : syracuseStep 20709431 = 31064147) B31064147
theorem B17483273 : Blo 1817610 17483273 := bstep (se 2 (by rfl) ⟨6556227, by rfl⟩ : syracuseStep 17483273 = 13112455) B13112455
theorem B41376810905 : Blo 1817610 41376810905 := bstep (se 2 (by rfl) ⟨15516304089, by rfl⟩ : syracuseStep 41376810905 = 31032608179) B31032608179
theorem B7874939 : Blo 1817610 7874939 := bstep (se 1 (by rfl) ⟨5906204, by rfl⟩ : syracuseStep 7874939 = 11812409) B11812409
theorem B14742107 : Blo 1817610 14742107 := bstep (se 1 (by rfl) ⟨11056580, by rfl⟩ : syracuseStep 14742107 = 22113161) B22113161
theorem B269203931 : Blo 1817610 269203931 := bstep (se 1 (by rfl) ⟨201902948, by rfl⟩ : syracuseStep 269203931 = 403805897) B403805897
theorem B28007039 : Blo 1817610 28007039 := bstep (se 1 (by rfl) ⟨21005279, by rfl⟩ : syracuseStep 28007039 = 42010559) B42010559
theorem B2046847 : Blo 1817610 2046847 := bstep (se 1 (by rfl) ⟨1535135, by rfl⟩ : syracuseStep 2046847 = 3070271) B3070271
theorem B1817755 : Blo 1817610 1817755 := bstep (se 1 (by rfl) ⟨1363316, by rfl⟩ : syracuseStep 1817755 = 2726633) B2726633
theorem B1817839 : Blo 1817610 1817839 := bstep (se 1 (by rfl) ⟨1363379, by rfl⟩ : syracuseStep 1817839 = 2726759) B2726759
theorem B8740331 : Blo 1817610 8740331 := bstep (se 1 (by rfl) ⟨6555248, by rfl⟩ : syracuseStep 8740331 = 13110497) B13110497
theorem B2729129 : Blo 1817610 2729129 := bstep (se 2 (by rfl) ⟨1023423, by rfl⟩ : syracuseStep 2729129 = 2046847) B2046847
theorem B18671359 : Blo 1817610 18671359 := bstep (se 1 (by rfl) ⟨14003519, by rfl⟩ : syracuseStep 18671359 = 28007039) B28007039
theorem B5826887 : Blo 1817610 5826887 := bstep (se 1 (by rfl) ⟨4370165, by rfl⟩ : syracuseStep 5826887 = 8740331) B8740331
theorem B13806287 : Blo 1817610 13806287 := bstep (se 1 (by rfl) ⟨10354715, by rfl⟩ : syracuseStep 13806287 = 20709431) B20709431
theorem B20999837 : Blo 1817610 20999837 := bstep (se 3 (by rfl) ⟨3937469, by rfl⟩ : syracuseStep 20999837 = 7874939) B7874939
theorem B27584540603 : Blo 1817610 27584540603 := bstep (se 1 (by rfl) ⟨20688405452, by rfl⟩ : syracuseStep 27584540603 = 41376810905) B41376810905
theorem B9828071 : Blo 1817610 9828071 := bstep (se 1 (by rfl) ⟨7371053, by rfl⟩ : syracuseStep 9828071 = 14742107) B14742107
theorem B11655515 : Blo 1817610 11655515 := bstep (se 1 (by rfl) ⟨8741636, by rfl⟩ : syracuseStep 11655515 = 17483273) B17483273
theorem B179469287 : Blo 1817610 179469287 := bstep (se 1 (by rfl) ⟨134601965, by rfl⟩ : syracuseStep 179469287 = 269203931) B269203931
theorem B1819419 : Blo 1817610 1819419 := bstep (se 1 (by rfl) ⟨1364564, by rfl⟩ : syracuseStep 1819419 = 2729129) B2729129
theorem B3884591 : Blo 1817610 3884591 := bstep (se 1 (by rfl) ⟨2913443, by rfl⟩ : syracuseStep 3884591 = 5826887) B5826887
theorem B119646191 : Blo 1817610 119646191 := bstep (se 1 (by rfl) ⟨89734643, by rfl⟩ : syracuseStep 119646191 = 179469287) B179469287
theorem B7770343 : Blo 1817610 7770343 := bstep (se 1 (by rfl) ⟨5827757, by rfl⟩ : syracuseStep 7770343 = 11655515) B11655515
theorem B9204191 : Blo 1817610 9204191 := bstep (se 1 (by rfl) ⟨6903143, by rfl⟩ : syracuseStep 9204191 = 13806287) B13806287
theorem B18389693735 : Blo 1817610 18389693735 := bstep (se 1 (by rfl) ⟨13792270301, by rfl⟩ : syracuseStep 18389693735 = 27584540603) B27584540603
theorem B6552047 : Blo 1817610 6552047 := bstep (se 1 (by rfl) ⟨4914035, by rfl⟩ : syracuseStep 6552047 = 9828071) B9828071
theorem B24895145 : Blo 1817610 24895145 := bstep (se 2 (by rfl) ⟨9335679, by rfl⟩ : syracuseStep 24895145 = 18671359) B18671359
theorem B13999891 : Blo 1817610 13999891 := bstep (se 1 (by rfl) ⟨10499918, by rfl⟩ : syracuseStep 13999891 = 20999837) B20999837
theorem B6136127 : Blo 1817610 6136127 := bstep (se 1 (by rfl) ⟨4602095, by rfl⟩ : syracuseStep 6136127 = 9204191) B9204191
theorem B12259795823 : Blo 1817610 12259795823 := bstep (se 1 (by rfl) ⟨9194846867, by rfl⟩ : syracuseStep 12259795823 = 18389693735) B18389693735
theorem B2589727 : Blo 1817610 2589727 := bstep (se 1 (by rfl) ⟨1942295, by rfl⟩ : syracuseStep 2589727 = 3884591) B3884591
theorem B319056509 : Blo 1817610 319056509 := bstep (se 3 (by rfl) ⟨59823095, by rfl⟩ : syracuseStep 319056509 = 119646191) B119646191
theorem B18666521 : Blo 1817610 18666521 := bstep (se 2 (by rfl) ⟨6999945, by rfl⟩ : syracuseStep 18666521 = 13999891) B13999891
theorem B10360457 : Blo 1817610 10360457 := bstep (se 2 (by rfl) ⟨3885171, by rfl⟩ : syracuseStep 10360457 = 7770343) B7770343
theorem B17472125 : Blo 1817610 17472125 := bstep (se 3 (by rfl) ⟨3276023, by rfl⟩ : syracuseStep 17472125 = 6552047) B6552047
theorem B66387053 : Blo 1817610 66387053 := bstep (se 3 (by rfl) ⟨12447572, by rfl⟩ : syracuseStep 66387053 = 24895145) B24895145
theorem B12444347 : Blo 1817610 12444347 := bstep (se 1 (by rfl) ⟨9333260, by rfl⟩ : syracuseStep 12444347 = 18666521) B18666521
theorem B6906971 : Blo 1817610 6906971 := bstep (se 1 (by rfl) ⟨5180228, by rfl⟩ : syracuseStep 6906971 = 10360457) B10360457
theorem B4090751 : Blo 1817610 4090751 := bstep (se 1 (by rfl) ⟨3068063, by rfl⟩ : syracuseStep 4090751 = 6136127) B6136127
theorem B3452969 : Blo 1817610 3452969 := bstep (se 2 (by rfl) ⟨1294863, by rfl⟩ : syracuseStep 3452969 = 2589727) B2589727
theorem B44258035 : Blo 1817610 44258035 := bstep (se 1 (by rfl) ⟨33193526, by rfl⟩ : syracuseStep 44258035 = 66387053) B66387053
theorem B8173197215 : Blo 1817610 8173197215 := bstep (se 1 (by rfl) ⟨6129897911, by rfl⟩ : syracuseStep 8173197215 = 12259795823) B12259795823
theorem B11648083 : Blo 1817610 11648083 := bstep (se 1 (by rfl) ⟨8736062, by rfl⟩ : syracuseStep 11648083 = 17472125) B17472125
theorem B212704339 : Blo 1817610 212704339 := bstep (se 1 (by rfl) ⟨159528254, by rfl⟩ : syracuseStep 212704339 = 319056509) B319056509
theorem B9207917 : Blo 1817610 9207917 := bstep (se 3 (by rfl) ⟨1726484, by rfl⟩ : syracuseStep 9207917 = 3452969) B3452969
theorem B4604647 : Blo 1817610 4604647 := bstep (se 1 (by rfl) ⟨3453485, by rfl⟩ : syracuseStep 4604647 = 6906971) B6906971
theorem B59010713 : Blo 1817610 59010713 := bstep (se 2 (by rfl) ⟨22129017, by rfl⟩ : syracuseStep 59010713 = 44258035) B44258035
theorem B5448798143 : Blo 1817610 5448798143 := bstep (se 1 (by rfl) ⟨4086598607, by rfl⟩ : syracuseStep 5448798143 = 8173197215) B8173197215
theorem B8296231 : Blo 1817610 8296231 := bstep (se 1 (by rfl) ⟨6222173, by rfl⟩ : syracuseStep 8296231 = 12444347) B12444347
theorem B15530777 : Blo 1817610 15530777 := bstep (se 2 (by rfl) ⟨5824041, by rfl⟩ : syracuseStep 15530777 = 11648083) B11648083
theorem B283605785 : Blo 1817610 283605785 := bstep (se 2 (by rfl) ⟨106352169, by rfl⟩ : syracuseStep 283605785 = 212704339) B212704339
theorem B2727167 : Blo 1817610 2727167 := bstep (se 1 (by rfl) ⟨2045375, by rfl⟩ : syracuseStep 2727167 = 4090751) B4090751
theorem B11061641 : Blo 1817610 11061641 := bstep (se 2 (by rfl) ⟨4148115, by rfl⟩ : syracuseStep 11061641 = 8296231) B8296231
theorem B39340475 : Blo 1817610 39340475 := bstep (se 1 (by rfl) ⟨29505356, by rfl⟩ : syracuseStep 39340475 = 59010713) B59010713
theorem B3632532095 : Blo 1817610 3632532095 := bstep (se 1 (by rfl) ⟨2724399071, by rfl⟩ : syracuseStep 3632532095 = 5448798143) B5448798143
theorem B6138611 : Blo 1817610 6138611 := bstep (se 1 (by rfl) ⟨4603958, by rfl⟩ : syracuseStep 6138611 = 9207917) B9207917
theorem B6139529 : Blo 1817610 6139529 := bstep (se 2 (by rfl) ⟨2302323, by rfl⟩ : syracuseStep 6139529 = 4604647) B4604647
theorem B10353851 : Blo 1817610 10353851 := bstep (se 1 (by rfl) ⟨7765388, by rfl⟩ : syracuseStep 10353851 = 15530777) B15530777
theorem B189070523 : Blo 1817610 189070523 := bstep (se 1 (by rfl) ⟨141802892, by rfl⟩ : syracuseStep 189070523 = 283605785) B283605785
theorem B1818111 : Blo 1817610 1818111 := bstep (se 1 (by rfl) ⟨1363583, by rfl⟩ : syracuseStep 1818111 = 2727167) B2727167
theorem B26226983 : Blo 1817610 26226983 := bstep (se 1 (by rfl) ⟨19670237, by rfl⟩ : syracuseStep 26226983 = 39340475) B39340475
theorem B4092407 : Blo 1817610 4092407 := bstep (se 1 (by rfl) ⟨3069305, by rfl⟩ : syracuseStep 4092407 = 6138611) B6138611
theorem B6902567 : Blo 1817610 6902567 := bstep (se 1 (by rfl) ⟨5176925, by rfl⟩ : syracuseStep 6902567 = 10353851) B10353851
theorem B126047015 : Blo 1817610 126047015 := bstep (se 1 (by rfl) ⟨94535261, by rfl⟩ : syracuseStep 126047015 = 189070523) B189070523
theorem B4093019 : Blo 1817610 4093019 := bstep (se 1 (by rfl) ⟨3069764, by rfl⟩ : syracuseStep 4093019 = 6139529) B6139529
theorem B29497709 : Blo 1817610 29497709 := bstep (se 3 (by rfl) ⟨5530820, by rfl⟩ : syracuseStep 29497709 = 11061641) B11061641
theorem B9686752253 : Blo 1817610 9686752253 := bstep (se 3 (by rfl) ⟨1816266047, by rfl⟩ : syracuseStep 9686752253 = 3632532095) B3632532095
theorem B2728271 : Blo 1817610 2728271 := bstep (se 1 (by rfl) ⟨2046203, by rfl⟩ : syracuseStep 2728271 = 4092407) B4092407
theorem B2728679 : Blo 1817610 2728679 := bstep (se 1 (by rfl) ⟨2046509, by rfl⟩ : syracuseStep 2728679 = 4093019) B4093019
theorem B17484655 : Blo 1817610 17484655 := bstep (se 1 (by rfl) ⟨13113491, by rfl⟩ : syracuseStep 17484655 = 26226983) B26226983
theorem B19665139 : Blo 1817610 19665139 := bstep (se 1 (by rfl) ⟨14748854, by rfl⟩ : syracuseStep 19665139 = 29497709) B29497709
theorem B4601711 : Blo 1817610 4601711 := bstep (se 1 (by rfl) ⟨3451283, by rfl⟩ : syracuseStep 4601711 = 6902567) B6902567
theorem B84031343 : Blo 1817610 84031343 := bstep (se 1 (by rfl) ⟨63023507, by rfl⟩ : syracuseStep 84031343 = 126047015) B126047015
theorem B6457834835 : Blo 1817610 6457834835 := bstep (se 1 (by rfl) ⟨4843376126, by rfl⟩ : syracuseStep 6457834835 = 9686752253) B9686752253
theorem B1818847 : Blo 1817610 1818847 := bstep (se 1 (by rfl) ⟨1364135, by rfl⟩ : syracuseStep 1818847 = 2728271) B2728271
theorem B1819119 : Blo 1817610 1819119 := bstep (se 1 (by rfl) ⟨1364339, by rfl⟩ : syracuseStep 1819119 = 2728679) B2728679
theorem B3067807 : Blo 1817610 3067807 := bstep (se 1 (by rfl) ⟨2300855, by rfl⟩ : syracuseStep 3067807 = 4601711) B4601711
theorem B56020895 : Blo 1817610 56020895 := bstep (se 1 (by rfl) ⟨42015671, by rfl⟩ : syracuseStep 56020895 = 84031343) B84031343
theorem B26220185 : Blo 1817610 26220185 := bstep (se 2 (by rfl) ⟨9832569, by rfl⟩ : syracuseStep 26220185 = 19665139) B19665139
theorem B23312873 : Blo 1817610 23312873 := bstep (se 2 (by rfl) ⟨8742327, by rfl⟩ : syracuseStep 23312873 = 17484655) B17484655
theorem B4305223223 : Blo 1817610 4305223223 := bstep (se 1 (by rfl) ⟨3228917417, by rfl⟩ : syracuseStep 4305223223 = 6457834835) B6457834835
theorem B15541915 : Blo 1817610 15541915 := bstep (se 1 (by rfl) ⟨11656436, by rfl⟩ : syracuseStep 15541915 = 23312873) B23312873
theorem B4090409 : Blo 1817610 4090409 := bstep (se 2 (by rfl) ⟨1533903, by rfl⟩ : syracuseStep 4090409 = 3067807) B3067807
theorem B17480123 : Blo 1817610 17480123 := bstep (se 1 (by rfl) ⟨13110092, by rfl⟩ : syracuseStep 17480123 = 26220185) B26220185
theorem B2870148815 : Blo 1817610 2870148815 := bstep (se 1 (by rfl) ⟨2152611611, by rfl⟩ : syracuseStep 2870148815 = 4305223223) B4305223223
theorem B37347263 : Blo 1817610 37347263 := bstep (se 1 (by rfl) ⟨28010447, by rfl⟩ : syracuseStep 37347263 = 56020895) B56020895
theorem B1913432543 : Blo 1817610 1913432543 := bstep (se 1 (by rfl) ⟨1435074407, by rfl⟩ : syracuseStep 1913432543 = 2870148815) B2870148815
theorem B24898175 : Blo 1817610 24898175 := bstep (se 1 (by rfl) ⟨18673631, by rfl⟩ : syracuseStep 24898175 = 37347263) B37347263
theorem B11653415 : Blo 1817610 11653415 := bstep (se 1 (by rfl) ⟨8740061, by rfl⟩ : syracuseStep 11653415 = 17480123) B17480123
theorem B20722553 : Blo 1817610 20722553 := bstep (se 2 (by rfl) ⟨7770957, by rfl⟩ : syracuseStep 20722553 = 15541915) B15541915
theorem B2726939 : Blo 1817610 2726939 := bstep (se 1 (by rfl) ⟨2045204, by rfl⟩ : syracuseStep 2726939 = 4090409) B4090409
theorem B16598783 : Blo 1817610 16598783 := bstep (se 1 (by rfl) ⟨12449087, by rfl⟩ : syracuseStep 16598783 = 24898175) B24898175
theorem B7768943 : Blo 1817610 7768943 := bstep (se 1 (by rfl) ⟨5826707, by rfl⟩ : syracuseStep 7768943 = 11653415) B11653415
theorem B13815035 : Blo 1817610 13815035 := bstep (se 1 (by rfl) ⟨10361276, by rfl⟩ : syracuseStep 13815035 = 20722553) B20722553
theorem B1275621695 : Blo 1817610 1275621695 := bstep (se 1 (by rfl) ⟨956716271, by rfl⟩ : syracuseStep 1275621695 = 1913432543) B1913432543
theorem B1817959 : Blo 1817610 1817959 := bstep (se 1 (by rfl) ⟨1363469, by rfl⟩ : syracuseStep 1817959 = 2726939) B2726939
theorem B5179295 : Blo 1817610 5179295 := bstep (se 1 (by rfl) ⟨3884471, by rfl⟩ : syracuseStep 5179295 = 7768943) B7768943
theorem B9210023 : Blo 1817610 9210023 := bstep (se 1 (by rfl) ⟨6907517, by rfl⟩ : syracuseStep 9210023 = 13815035) B13815035
theorem B850414463 : Blo 1817610 850414463 := bstep (se 1 (by rfl) ⟨637810847, by rfl⟩ : syracuseStep 850414463 = 1275621695) B1275621695
theorem B11065855 : Blo 1817610 11065855 := bstep (se 1 (by rfl) ⟨8299391, by rfl⟩ : syracuseStep 11065855 = 16598783) B16598783
theorem B14754473 : Blo 1817610 14754473 := bstep (se 2 (by rfl) ⟨5532927, by rfl⟩ : syracuseStep 14754473 = 11065855) B11065855
theorem B3452863 : Blo 1817610 3452863 := bstep (se 1 (by rfl) ⟨2589647, by rfl⟩ : syracuseStep 3452863 = 5179295) B5179295
theorem B6140015 : Blo 1817610 6140015 := bstep (se 1 (by rfl) ⟨4605011, by rfl⟩ : syracuseStep 6140015 = 9210023) B9210023
theorem B566942975 : Blo 1817610 566942975 := bstep (se 1 (by rfl) ⟨425207231, by rfl⟩ : syracuseStep 566942975 = 850414463) B850414463
theorem B4093343 : Blo 1817610 4093343 := bstep (se 1 (by rfl) ⟨3070007, by rfl⟩ : syracuseStep 4093343 = 6140015) B6140015
theorem B9836315 : Blo 1817610 9836315 := bstep (se 1 (by rfl) ⟨7377236, by rfl⟩ : syracuseStep 9836315 = 14754473) B14754473
theorem B377961983 : Blo 1817610 377961983 := bstep (se 1 (by rfl) ⟨283471487, by rfl⟩ : syracuseStep 377961983 = 566942975) B566942975
theorem B4603817 : Blo 1817610 4603817 := bstep (se 2 (by rfl) ⟨1726431, by rfl⟩ : syracuseStep 4603817 = 3452863) B3452863
theorem B2728895 : Blo 1817610 2728895 := bstep (se 1 (by rfl) ⟨2046671, by rfl⟩ : syracuseStep 2728895 = 4093343) B4093343
theorem B6557543 : Blo 1817610 6557543 := bstep (se 1 (by rfl) ⟨4918157, by rfl⟩ : syracuseStep 6557543 = 9836315) B9836315
theorem B251974655 : Blo 1817610 251974655 := bstep (se 1 (by rfl) ⟨188980991, by rfl⟩ : syracuseStep 251974655 = 377961983) B377961983
theorem B3069211 : Blo 1817610 3069211 := bstep (se 1 (by rfl) ⟨2301908, by rfl⟩ : syracuseStep 3069211 = 4603817) B4603817
theorem B1819263 : Blo 1817610 1819263 := bstep (se 1 (by rfl) ⟨1364447, by rfl⟩ : syracuseStep 1819263 = 2728895) B2728895
theorem B4092281 : Blo 1817610 4092281 := bstep (se 2 (by rfl) ⟨1534605, by rfl⟩ : syracuseStep 4092281 = 3069211) B3069211
theorem B4371695 : Blo 1817610 4371695 := bstep (se 1 (by rfl) ⟨3278771, by rfl⟩ : syracuseStep 4371695 = 6557543) B6557543
theorem B167983103 : Blo 1817610 167983103 := bstep (se 1 (by rfl) ⟨125987327, by rfl⟩ : syracuseStep 167983103 = 251974655) B251974655
theorem B2728187 : Blo 1817610 2728187 := bstep (se 1 (by rfl) ⟨2046140, by rfl⟩ : syracuseStep 2728187 = 4092281) B4092281
theorem B2914463 : Blo 1817610 2914463 := bstep (se 1 (by rfl) ⟨2185847, by rfl⟩ : syracuseStep 2914463 = 4371695) B4371695
theorem B447954941 : Blo 1817610 447954941 := bstep (se 3 (by rfl) ⟨83991551, by rfl⟩ : syracuseStep 447954941 = 167983103) B167983103
theorem B1818791 : Blo 1817610 1818791 := bstep (se 1 (by rfl) ⟨1364093, by rfl⟩ : syracuseStep 1818791 = 2728187) B2728187
theorem B1942975 : Blo 1817610 1942975 := bstep (se 1 (by rfl) ⟨1457231, by rfl⟩ : syracuseStep 1942975 = 2914463) B2914463
theorem B298636627 : Blo 1817610 298636627 := bstep (se 1 (by rfl) ⟨223977470, by rfl⟩ : syracuseStep 298636627 = 447954941) B447954941
theorem B398182169 : Blo 1817610 398182169 := bstep (se 2 (by rfl) ⟨149318313, by rfl⟩ : syracuseStep 398182169 = 298636627) B298636627
theorem B2590633 : Blo 1817610 2590633 := bstep (se 2 (by rfl) ⟨971487, by rfl⟩ : syracuseStep 2590633 = 1942975) B1942975
theorem B265454779 : Blo 1817610 265454779 := bstep (se 1 (by rfl) ⟨199091084, by rfl⟩ : syracuseStep 265454779 = 398182169) B398182169
theorem B3454177 : Blo 1817610 3454177 := bstep (se 2 (by rfl) ⟨1295316, by rfl⟩ : syracuseStep 3454177 = 2590633) B2590633
theorem B4605569 : Blo 1817610 4605569 := bstep (se 2 (by rfl) ⟨1727088, by rfl⟩ : syracuseStep 4605569 = 3454177) B3454177
theorem B353939705 : Blo 1817610 353939705 := bstep (se 2 (by rfl) ⟨132727389, by rfl⟩ : syracuseStep 353939705 = 265454779) B265454779
theorem B235959803 : Blo 1817610 235959803 := bstep (se 1 (by rfl) ⟨176969852, by rfl⟩ : syracuseStep 235959803 = 353939705) B353939705
theorem B3070379 : Blo 1817610 3070379 := bstep (se 1 (by rfl) ⟨2302784, by rfl⟩ : syracuseStep 3070379 = 4605569) B4605569
theorem B157306535 : Blo 1817610 157306535 := bstep (se 1 (by rfl) ⟨117979901, by rfl⟩ : syracuseStep 157306535 = 235959803) B235959803
theorem B2046919 : Blo 1817610 2046919 := bstep (se 1 (by rfl) ⟨1535189, by rfl⟩ : syracuseStep 2046919 = 3070379) B3070379
theorem B2729225 : Blo 1817610 2729225 := bstep (se 2 (by rfl) ⟨1023459, by rfl⟩ : syracuseStep 2729225 = 2046919) B2046919
theorem B104871023 : Blo 1817610 104871023 := bstep (se 1 (by rfl) ⟨78653267, by rfl⟩ : syracuseStep 104871023 = 157306535) B157306535
theorem B1819483 : Blo 1817610 1819483 := bstep (se 1 (by rfl) ⟨1364612, by rfl⟩ : syracuseStep 1819483 = 2729225) B2729225
theorem B69914015 : Blo 1817610 69914015 := bstep (se 1 (by rfl) ⟨52435511, by rfl⟩ : syracuseStep 69914015 = 104871023) B104871023
theorem B46609343 : Blo 1817610 46609343 := bstep (se 1 (by rfl) ⟨34957007, by rfl⟩ : syracuseStep 46609343 = 69914015) B69914015
theorem B31072895 : Blo 1817610 31072895 := bstep (se 1 (by rfl) ⟨23304671, by rfl⟩ : syracuseStep 31072895 = 46609343) B46609343
theorem B20715263 : Blo 1817610 20715263 := bstep (se 1 (by rfl) ⟨15536447, by rfl⟩ : syracuseStep 20715263 = 31072895) B31072895
theorem B13810175 : Blo 1817610 13810175 := bstep (se 1 (by rfl) ⟨10357631, by rfl⟩ : syracuseStep 13810175 = 20715263) B20715263
theorem B9206783 : Blo 1817610 9206783 := bstep (se 1 (by rfl) ⟨6905087, by rfl⟩ : syracuseStep 9206783 = 13810175) B13810175
theorem B6137855 : Blo 1817610 6137855 := bstep (se 1 (by rfl) ⟨4603391, by rfl⟩ : syracuseStep 6137855 = 9206783) B9206783
theorem B4091903 : Blo 1817610 4091903 := bstep (se 1 (by rfl) ⟨3068927, by rfl⟩ : syracuseStep 4091903 = 6137855) B6137855
theorem B2727935 : Blo 1817610 2727935 := bstep (se 1 (by rfl) ⟨2045951, by rfl⟩ : syracuseStep 2727935 = 4091903) B4091903
theorem B1818623 : Blo 1817610 1818623 := bstep (se 1 (by rfl) ⟨1363967, by rfl⟩ : syracuseStep 1818623 = 2727935) B2727935

theorem C0 (j : ℕ) (h1 : 454402 ≤ j) (h2 : j ≤ 454901) : Blo 1817610 (4 * j + 3) := by
  interval_cases j
  · exact B1817611
  · exact B1817615
  · exact B1817619
  · exact B1817623
  · exact B1817627
  · exact B1817631
  · exact B1817635
  · exact B1817639
  · exact B1817643
  · exact B1817647
  · exact B1817651
  · exact B1817655
  · exact B1817659
  · exact B1817663
  · exact B1817667
  · exact B1817671
  · exact B1817675
  · exact B1817679
  · exact B1817683
  · exact B1817687
  · exact B1817691
  · exact B1817695
  · exact B1817699
  · exact B1817703
  · exact B1817707
  · exact B1817711
  · exact B1817715
  · exact B1817719
  · exact B1817723
  · exact B1817727
  · exact B1817731
  · exact B1817735
  · exact B1817739
  · exact B1817743
  · exact B1817747
  · exact B1817751
  · exact B1817755
  · exact B1817759
  · exact B1817763
  · exact B1817767
  · exact B1817771
  · exact B1817775
  · exact B1817779
  · exact B1817783
  · exact B1817787
  · exact B1817791
  · exact B1817795
  · exact B1817799
  · exact B1817803
  · exact B1817807
  · exact B1817811
  · exact B1817815
  · exact B1817819
  · exact B1817823
  · exact B1817827
  · exact B1817831
  · exact B1817835
  · exact B1817839
  · exact B1817843
  · exact B1817847
  · exact B1817851
  · exact B1817855
  · exact B1817859
  · exact B1817863
  · exact B1817867
  · exact B1817871
  · exact B1817875
  · exact B1817879
  · exact B1817883
  · exact B1817887
  · exact B1817891
  · exact B1817895
  · exact B1817899
  · exact B1817903
  · exact B1817907
  · exact B1817911
  · exact B1817915
  · exact B1817919
  · exact B1817923
  · exact B1817927
  · exact B1817931
  · exact B1817935
  · exact B1817939
  · exact B1817943
  · exact B1817947
  · exact B1817951
  · exact B1817955
  · exact B1817959
  · exact B1817963
  · exact B1817967
  · exact B1817971
  · exact B1817975
  · exact B1817979
  · exact B1817983
  · exact B1817987
  · exact B1817991
  · exact B1817995
  · exact B1817999
  · exact B1818003
  · exact B1818007
  · exact B1818011
  · exact B1818015
  · exact B1818019
  · exact B1818023
  · exact B1818027
  · exact B1818031
  · exact B1818035
  · exact B1818039
  · exact B1818043
  · exact B1818047
  · exact B1818051
  · exact B1818055
  · exact B1818059
  · exact B1818063
  · exact B1818067
  · exact B1818071
  · exact B1818075
  · exact B1818079
  · exact B1818083
  · exact B1818087
  · exact B1818091
  · exact B1818095
  · exact B1818099
  · exact B1818103
  · exact B1818107
  · exact B1818111
  · exact B1818115
  · exact B1818119
  · exact B1818123
  · exact B1818127
  · exact B1818131
  · exact B1818135
  · exact B1818139
  · exact B1818143
  · exact B1818147
  · exact B1818151
  · exact B1818155
  · exact B1818159
  · exact B1818163
  · exact B1818167
  · exact B1818171
  · exact B1818175
  · exact B1818179
  · exact B1818183
  · exact B1818187
  · exact B1818191
  · exact B1818195
  · exact B1818199
  · exact B1818203
  · exact B1818207
  · exact B1818211
  · exact B1818215
  · exact B1818219
  · exact B1818223
  · exact B1818227
  · exact B1818231
  · exact B1818235
  · exact B1818239
  · exact B1818243
  · exact B1818247
  · exact B1818251
  · exact B1818255
  · exact B1818259
  · exact B1818263
  · exact B1818267
  · exact B1818271
  · exact B1818275
  · exact B1818279
  · exact B1818283
  · exact B1818287
  · exact B1818291
  · exact B1818295
  · exact B1818299
  · exact B1818303
  · exact B1818307
  · exact B1818311
  · exact B1818315
  · exact B1818319
  · exact B1818323
  · exact B1818327
  · exact B1818331
  · exact B1818335
  · exact B1818339
  · exact B1818343
  · exact B1818347
  · exact B1818351
  · exact B1818355
  · exact B1818359
  · exact B1818363
  · exact B1818367
  · exact B1818371
  · exact B1818375
  · exact B1818379
  · exact B1818383
  · exact B1818387
  · exact B1818391
  · exact B1818395
  · exact B1818399
  · exact B1818403
  · exact B1818407
  · exact B1818411
  · exact B1818415
  · exact B1818419
  · exact B1818423
  · exact B1818427
  · exact B1818431
  · exact B1818435
  · exact B1818439
  · exact B1818443
  · exact B1818447
  · exact B1818451
  · exact B1818455
  · exact B1818459
  · exact B1818463
  · exact B1818467
  · exact B1818471
  · exact B1818475
  · exact B1818479
  · exact B1818483
  · exact B1818487
  · exact B1818491
  · exact B1818495
  · exact B1818499
  · exact B1818503
  · exact B1818507
  · exact B1818511
  · exact B1818515
  · exact B1818519
  · exact B1818523
  · exact B1818527
  · exact B1818531
  · exact B1818535
  · exact B1818539
  · exact B1818543
  · exact B1818547
  · exact B1818551
  · exact B1818555
  · exact B1818559
  · exact B1818563
  · exact B1818567
  · exact B1818571
  · exact B1818575
  · exact B1818579
  · exact B1818583
  · exact B1818587
  · exact B1818591
  · exact B1818595
  · exact B1818599
  · exact B1818603
  · exact B1818607
  · exact B1818611
  · exact B1818615
  · exact B1818619
  · exact B1818623
  · exact B1818627
  · exact B1818631
  · exact B1818635
  · exact B1818639
  · exact B1818643
  · exact B1818647
  · exact B1818651
  · exact B1818655
  · exact B1818659
  · exact B1818663
  · exact B1818667
  · exact B1818671
  · exact B1818675
  · exact B1818679
  · exact B1818683
  · exact B1818687
  · exact B1818691
  · exact B1818695
  · exact B1818699
  · exact B1818703
  · exact B1818707
  · exact B1818711
  · exact B1818715
  · exact B1818719
  · exact B1818723
  · exact B1818727
  · exact B1818731
  · exact B1818735
  · exact B1818739
  · exact B1818743
  · exact B1818747
  · exact B1818751
  · exact B1818755
  · exact B1818759
  · exact B1818763
  · exact B1818767
  · exact B1818771
  · exact B1818775
  · exact B1818779
  · exact B1818783
  · exact B1818787
  · exact B1818791
  · exact B1818795
  · exact B1818799
  · exact B1818803
  · exact B1818807
  · exact B1818811
  · exact B1818815
  · exact B1818819
  · exact B1818823
  · exact B1818827
  · exact B1818831
  · exact B1818835
  · exact B1818839
  · exact B1818843
  · exact B1818847
  · exact B1818851
  · exact B1818855
  · exact B1818859
  · exact B1818863
  · exact B1818867
  · exact B1818871
  · exact B1818875
  · exact B1818879
  · exact B1818883
  · exact B1818887
  · exact B1818891
  · exact B1818895
  · exact B1818899
  · exact B1818903
  · exact B1818907
  · exact B1818911
  · exact B1818915
  · exact B1818919
  · exact B1818923
  · exact B1818927
  · exact B1818931
  · exact B1818935
  · exact B1818939
  · exact B1818943
  · exact B1818947
  · exact B1818951
  · exact B1818955
  · exact B1818959
  · exact B1818963
  · exact B1818967
  · exact B1818971
  · exact B1818975
  · exact B1818979
  · exact B1818983
  · exact B1818987
  · exact B1818991
  · exact B1818995
  · exact B1818999
  · exact B1819003
  · exact B1819007
  · exact B1819011
  · exact B1819015
  · exact B1819019
  · exact B1819023
  · exact B1819027
  · exact B1819031
  · exact B1819035
  · exact B1819039
  · exact B1819043
  · exact B1819047
  · exact B1819051
  · exact B1819055
  · exact B1819059
  · exact B1819063
  · exact B1819067
  · exact B1819071
  · exact B1819075
  · exact B1819079
  · exact B1819083
  · exact B1819087
  · exact B1819091
  · exact B1819095
  · exact B1819099
  · exact B1819103
  · exact B1819107
  · exact B1819111
  · exact B1819115
  · exact B1819119
  · exact B1819123
  · exact B1819127
  · exact B1819131
  · exact B1819135
  · exact B1819139
  · exact B1819143
  · exact B1819147
  · exact B1819151
  · exact B1819155
  · exact B1819159
  · exact B1819163
  · exact B1819167
  · exact B1819171
  · exact B1819175
  · exact B1819179
  · exact B1819183
  · exact B1819187
  · exact B1819191
  · exact B1819195
  · exact B1819199
  · exact B1819203
  · exact B1819207
  · exact B1819211
  · exact B1819215
  · exact B1819219
  · exact B1819223
  · exact B1819227
  · exact B1819231
  · exact B1819235
  · exact B1819239
  · exact B1819243
  · exact B1819247
  · exact B1819251
  · exact B1819255
  · exact B1819259
  · exact B1819263
  · exact B1819267
  · exact B1819271
  · exact B1819275
  · exact B1819279
  · exact B1819283
  · exact B1819287
  · exact B1819291
  · exact B1819295
  · exact B1819299
  · exact B1819303
  · exact B1819307
  · exact B1819311
  · exact B1819315
  · exact B1819319
  · exact B1819323
  · exact B1819327
  · exact B1819331
  · exact B1819335
  · exact B1819339
  · exact B1819343
  · exact B1819347
  · exact B1819351
  · exact B1819355
  · exact B1819359
  · exact B1819363
  · exact B1819367
  · exact B1819371
  · exact B1819375
  · exact B1819379
  · exact B1819383
  · exact B1819387
  · exact B1819391
  · exact B1819395
  · exact B1819399
  · exact B1819403
  · exact B1819407
  · exact B1819411
  · exact B1819415
  · exact B1819419
  · exact B1819423
  · exact B1819427
  · exact B1819431
  · exact B1819435
  · exact B1819439
  · exact B1819443
  · exact B1819447
  · exact B1819451
  · exact B1819455
  · exact B1819459
  · exact B1819463
  · exact B1819467
  · exact B1819471
  · exact B1819475
  · exact B1819479
  · exact B1819483
  · exact B1819487
  · exact B1819491
  · exact B1819495
  · exact B1819499
  · exact B1819503
  · exact B1819507
  · exact B1819511
  · exact B1819515
  · exact B1819519
  · exact B1819523
  · exact B1819527
  · exact B1819531
  · exact B1819535
  · exact B1819539
  · exact B1819543
  · exact B1819547
  · exact B1819551
  · exact B1819555
  · exact B1819559
  · exact B1819563
  · exact B1819567
  · exact B1819571
  · exact B1819575
  · exact B1819579
  · exact B1819583
  · exact B1819587
  · exact B1819591
  · exact B1819595
  · exact B1819599
  · exact B1819603
  · exact B1819607

theorem solution (m : ℕ) (hlo : 1817610 ≤ m) (hhi : m ≤ 1819610) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 454402 ≤ j := by omega
    have hj2 : j ≤ 454901 := by omega
    have hb : Blo 1817610 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
