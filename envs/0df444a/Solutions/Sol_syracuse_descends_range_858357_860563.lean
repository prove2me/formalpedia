-- Prove2me | solution 1 for syracuse_descends_range_858357_860563
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:58.741588+00:00
-- url     : https://prove2.me/submissions/83d111f4-d412-4d1e-8adb-e5293a8a4053

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


theorem B1032205 : Blo 858357 1032205 := bbase (se 3 (by rfl) ⟨193538, by rfl⟩ : syracuseStep 1032205 = 387077) (by norm_num)
theorem B1933325 : Blo 858357 1933325 := bbase (se 3 (by rfl) ⟨362498, by rfl⟩ : syracuseStep 1933325 = 724997) (by norm_num)
theorem B15687701 : Blo 858357 15687701 := bbase (se 6 (by rfl) ⟨367680, by rfl⟩ : syracuseStep 15687701 = 735361) (by norm_num)
theorem B2981909 : Blo 858357 2981909 := bbase (se 6 (by rfl) ⟨69888, by rfl⟩ : syracuseStep 2981909 = 139777) (by norm_num)
theorem B966685 : Blo 858357 966685 := bbase (se 3 (by rfl) ⟨181253, by rfl⟩ : syracuseStep 966685 = 362507) (by norm_num)
theorem B1450021 : Blo 858357 1450021 := bbase (se 4 (by rfl) ⟨135939, by rfl⟩ : syracuseStep 1450021 = 271879) (by norm_num)
theorem B3309605 : Blo 858357 3309605 := bbase (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) (by norm_num)
theorem B966721 : Blo 858357 966721 := bbase (se 2 (by rfl) ⟨362520, by rfl⟩ : syracuseStep 966721 = 725041) (by norm_num)
theorem B1933397 : Blo 858357 1933397 := bbase (se 8 (by rfl) ⟨11328, by rfl⟩ : syracuseStep 1933397 = 22657) (by norm_num)
theorem B2900069 : Blo 858357 2900069 := bbase (se 4 (by rfl) ⟨271881, by rfl⟩ : syracuseStep 2900069 = 543763) (by norm_num)
theorem B966757 : Blo 858357 966757 := bbase (se 4 (by rfl) ⟨90633, by rfl⟩ : syracuseStep 966757 = 181267) (by norm_num)
theorem B1450109 : Blo 858357 1450109 := bbase (se 3 (by rfl) ⟨271895, by rfl⟩ : syracuseStep 1450109 = 543791) (by norm_num)
theorem B966793 : Blo 858357 966793 := bbase (se 2 (by rfl) ⟨362547, by rfl⟩ : syracuseStep 966793 = 725095) (by norm_num)
theorem B1933469 : Blo 858357 1933469 := bbase (se 3 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 1933469 = 725051) (by norm_num)
theorem B3670181 : Blo 858357 3670181 := bbase (se 4 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 3670181 = 688159) (by norm_num)
theorem B917669 : Blo 858357 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B966829 : Blo 858357 966829 := bbase (se 3 (by rfl) ⟨181280, by rfl⟩ : syracuseStep 966829 = 362561) (by norm_num)
theorem B966865 : Blo 858357 966865 := bbase (se 2 (by rfl) ⟨362574, by rfl⟩ : syracuseStep 966865 = 725149) (by norm_num)
theorem B1933541 : Blo 858357 1933541 := bbase (se 4 (by rfl) ⟨181269, by rfl⟩ : syracuseStep 1933541 = 362539) (by norm_num)
theorem B966901 : Blo 858357 966901 := bbase (se 5 (by rfl) ⟨45323, by rfl⟩ : syracuseStep 966901 = 90647) (by norm_num)
theorem B1450237 : Blo 858357 1450237 := bbase (se 3 (by rfl) ⟨271919, by rfl⟩ : syracuseStep 1450237 = 543839) (by norm_num)
theorem B1630469 : Blo 858357 1630469 := bbase (se 4 (by rfl) ⟨152856, by rfl⟩ : syracuseStep 1630469 = 305713) (by norm_num)
theorem B1032469 : Blo 858357 1032469 := bbase (se 6 (by rfl) ⟨24198, by rfl⟩ : syracuseStep 1032469 = 48397) (by norm_num)
theorem B966937 : Blo 858357 966937 := bbase (se 2 (by rfl) ⟨362601, by rfl⟩ : syracuseStep 966937 = 725203) (by norm_num)
theorem B1933613 : Blo 858357 1933613 := bbase (se 3 (by rfl) ⟨362552, by rfl⟩ : syracuseStep 1933613 = 725105) (by norm_num)
theorem B966973 : Blo 858357 966973 := bbase (se 3 (by rfl) ⟨181307, by rfl⟩ : syracuseStep 966973 = 362615) (by norm_num)
theorem B1450325 : Blo 858357 1450325 := bbase (se 10 (by rfl) ⟨2124, by rfl⟩ : syracuseStep 1450325 = 4249) (by norm_num)
theorem B967009 : Blo 858357 967009 := bbase (se 2 (by rfl) ⟨362628, by rfl⟩ : syracuseStep 967009 = 725257) (by norm_num)
theorem B1933685 : Blo 858357 1933685 := bbase (se 5 (by rfl) ⟨90641, by rfl⟩ : syracuseStep 1933685 = 181283) (by norm_num)
theorem B1835389 : Blo 858357 1835389 := bbase (se 3 (by rfl) ⟨344135, by rfl⟩ : syracuseStep 1835389 = 688271) (by norm_num)
theorem B967045 : Blo 858357 967045 := bbase (se 4 (by rfl) ⟨90660, by rfl⟩ : syracuseStep 967045 = 181321) (by norm_num)
theorem B1032589 : Blo 858357 1032589 := bbase (se 3 (by rfl) ⟨193610, by rfl⟩ : syracuseStep 1032589 = 387221) (by norm_num)
theorem B1630621 : Blo 858357 1630621 := bbase (se 3 (by rfl) ⟨305741, by rfl⟩ : syracuseStep 1630621 = 611483) (by norm_num)
theorem B967081 : Blo 858357 967081 := bbase (se 2 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 967081 = 725311) (by norm_num)
theorem B1933757 : Blo 858357 1933757 := bbase (se 3 (by rfl) ⟨362579, by rfl⟩ : syracuseStep 1933757 = 725159) (by norm_num)
theorem B967117 : Blo 858357 967117 := bbase (se 3 (by rfl) ⟨181334, by rfl⟩ : syracuseStep 967117 = 362669) (by norm_num)
theorem B1450453 : Blo 858357 1450453 := bbase (se 7 (by rfl) ⟨16997, by rfl⟩ : syracuseStep 1450453 = 33995) (by norm_num)
theorem B967153 : Blo 858357 967153 := bbase (se 2 (by rfl) ⟨362682, by rfl⟩ : syracuseStep 967153 = 725365) (by norm_num)
theorem B1933829 : Blo 858357 1933829 := bbase (se 4 (by rfl) ⟨181296, by rfl⟩ : syracuseStep 1933829 = 362593) (by norm_num)
theorem B2900501 : Blo 858357 2900501 := bbase (se 6 (by rfl) ⟨67980, by rfl⟩ : syracuseStep 2900501 = 135961) (by norm_num)
theorem B967189 : Blo 858357 967189 := bbase (se 6 (by rfl) ⟨22668, by rfl⟩ : syracuseStep 967189 = 45337) (by norm_num)
theorem B1450541 : Blo 858357 1450541 := bbase (se 3 (by rfl) ⟨271976, by rfl⟩ : syracuseStep 1450541 = 543953) (by norm_num)
theorem B967225 : Blo 858357 967225 := bbase (se 2 (by rfl) ⟨362709, by rfl⟩ : syracuseStep 967225 = 725419) (by norm_num)
theorem B1933901 : Blo 858357 1933901 := bbase (se 3 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 1933901 = 725213) (by norm_num)
theorem B967261 : Blo 858357 967261 := bbase (se 3 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 967261 = 362723) (by norm_num)
theorem B918113 : Blo 858357 918113 := bbase (se 2 (by rfl) ⟨344292, by rfl⟩ : syracuseStep 918113 = 688585) (by norm_num)
theorem B967297 : Blo 858357 967297 := bbase (se 2 (by rfl) ⟨362736, by rfl⟩ : syracuseStep 967297 = 725473) (by norm_num)
theorem B1548941 : Blo 858357 1548941 := bbase (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) (by norm_num)
theorem B1933973 : Blo 858357 1933973 := bbase (se 6 (by rfl) ⟨45327, by rfl⟩ : syracuseStep 1933973 = 90655) (by norm_num)
theorem B918173 : Blo 858357 918173 := bbase (se 3 (by rfl) ⟨172157, by rfl⟩ : syracuseStep 918173 = 344315) (by norm_num)
theorem B967333 : Blo 858357 967333 := bbase (se 4 (by rfl) ⟨90687, by rfl⟩ : syracuseStep 967333 = 181375) (by norm_num)
theorem B1450669 : Blo 858357 1450669 := bbase (se 3 (by rfl) ⟨272000, by rfl⟩ : syracuseStep 1450669 = 544001) (by norm_num)
theorem B2450101 : Blo 858357 2450101 := bbase (se 5 (by rfl) ⟨114848, by rfl⟩ : syracuseStep 2450101 = 229697) (by norm_num)
theorem B967369 : Blo 858357 967369 := bbase (se 2 (by rfl) ⟨362763, by rfl⟩ : syracuseStep 967369 = 725527) (by norm_num)
theorem B1630925 : Blo 858357 1630925 := bbase (se 3 (by rfl) ⟨305798, by rfl⟩ : syracuseStep 1630925 = 611597) (by norm_num)
theorem B1934045 : Blo 858357 1934045 := bbase (se 3 (by rfl) ⟨362633, by rfl⟩ : syracuseStep 1934045 = 725267) (by norm_num)
theorem B1491677 : Blo 858357 1491677 := bbase (se 3 (by rfl) ⟨279689, by rfl⟩ : syracuseStep 1491677 = 559379) (by norm_num)
theorem B967405 : Blo 858357 967405 := bbase (se 3 (by rfl) ⟨181388, by rfl⟩ : syracuseStep 967405 = 362777) (by norm_num)
theorem B1450757 : Blo 858357 1450757 := bbase (se 4 (by rfl) ⟨136008, by rfl⟩ : syracuseStep 1450757 = 272017) (by norm_num)
theorem B967441 : Blo 858357 967441 := bbase (se 2 (by rfl) ⟨362790, by rfl⟩ : syracuseStep 967441 = 725581) (by norm_num)
theorem B918301 : Blo 858357 918301 := bbase (se 3 (by rfl) ⟨172181, by rfl⟩ : syracuseStep 918301 = 344363) (by norm_num)
theorem B1934117 : Blo 858357 1934117 := bbase (se 4 (by rfl) ⟨181323, by rfl⟩ : syracuseStep 1934117 = 362647) (by norm_num)
theorem B967477 : Blo 858357 967477 := bbase (se 5 (by rfl) ⟨45350, by rfl⟩ : syracuseStep 967477 = 90701) (by norm_num)
theorem B2753365 : Blo 858357 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B967513 : Blo 858357 967513 := bbase (se 2 (by rfl) ⟨362817, by rfl⟩ : syracuseStep 967513 = 725635) (by norm_num)
theorem B1835885 : Blo 858357 1835885 := bbase (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) (by norm_num)
theorem B1934189 : Blo 858357 1934189 := bbase (se 3 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 1934189 = 725321) (by norm_num)
theorem B967549 : Blo 858357 967549 := bbase (se 3 (by rfl) ⟨181415, by rfl⟩ : syracuseStep 967549 = 362831) (by norm_num)
theorem B1377157 : Blo 858357 1377157 := bbase (se 4 (by rfl) ⟨129108, by rfl⟩ : syracuseStep 1377157 = 258217) (by norm_num)
theorem B1450885 : Blo 858357 1450885 := bbase (se 4 (by rfl) ⟨136020, by rfl⟩ : syracuseStep 1450885 = 272041) (by norm_num)
theorem B967585 : Blo 858357 967585 := bbase (se 2 (by rfl) ⟨362844, by rfl⟩ : syracuseStep 967585 = 725689) (by norm_num)
theorem B1934261 : Blo 858357 1934261 := bbase (se 5 (by rfl) ⟨90668, by rfl⟩ : syracuseStep 1934261 = 181337) (by norm_num)
theorem B2900933 : Blo 858357 2900933 := bbase (se 4 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 2900933 = 543925) (by norm_num)
theorem B967621 : Blo 858357 967621 := bbase (se 4 (by rfl) ⟨90714, by rfl⟩ : syracuseStep 967621 = 181429) (by norm_num)
theorem B1450973 : Blo 858357 1450973 := bbase (se 3 (by rfl) ⟨272057, by rfl⟩ : syracuseStep 1450973 = 544115) (by norm_num)
theorem B967657 : Blo 858357 967657 := bbase (se 2 (by rfl) ⟨362871, by rfl⟩ : syracuseStep 967657 = 725743) (by norm_num)
theorem B1934333 : Blo 858357 1934333 := bbase (se 3 (by rfl) ⟨362687, by rfl⟩ : syracuseStep 1934333 = 725375) (by norm_num)
theorem B967693 : Blo 858357 967693 := bbase (se 3 (by rfl) ⟨181442, by rfl⟩ : syracuseStep 967693 = 362885) (by norm_num)
theorem B967729 : Blo 858357 967729 := bbase (se 2 (by rfl) ⟨362898, by rfl⟩ : syracuseStep 967729 = 725797) (by norm_num)
theorem B1934405 : Blo 858357 1934405 := bbase (se 4 (by rfl) ⟨181350, by rfl⟩ : syracuseStep 1934405 = 362701) (by norm_num)
theorem B967765 : Blo 858357 967765 := bbase (se 8 (by rfl) ⟨5670, by rfl⟩ : syracuseStep 967765 = 11341) (by norm_num)
theorem B6202453 : Blo 858357 6202453 := bbase (se 8 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 6202453 = 72685) (by norm_num)
theorem B1451101 : Blo 858357 1451101 := bbase (se 3 (by rfl) ⟨272081, by rfl⟩ : syracuseStep 1451101 = 544163) (by norm_num)
theorem B967801 : Blo 858357 967801 := bbase (se 2 (by rfl) ⟨362925, by rfl⟩ : syracuseStep 967801 = 725851) (by norm_num)
theorem B1934477 : Blo 858357 1934477 := bbase (se 3 (by rfl) ⟨362714, by rfl⟩ : syracuseStep 1934477 = 725429) (by norm_num)
theorem B3671189 : Blo 858357 3671189 := bbase (se 6 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 3671189 = 172087) (by norm_num)
theorem B967837 : Blo 858357 967837 := bbase (se 3 (by rfl) ⟨181469, by rfl⟩ : syracuseStep 967837 = 362939) (by norm_num)
theorem B4129973 : Blo 858357 4129973 := bbase (se 5 (by rfl) ⟨193592, by rfl⟩ : syracuseStep 4129973 = 387185) (by norm_num)
theorem B4351157 : Blo 858357 4351157 := bbase (se 5 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 4351157 = 407921) (by norm_num)
theorem B1451189 : Blo 858357 1451189 := bbase (se 5 (by rfl) ⟨68024, by rfl⟩ : syracuseStep 1451189 = 136049) (by norm_num)
theorem B967873 : Blo 858357 967873 := bbase (se 2 (by rfl) ⟨362952, by rfl⟩ : syracuseStep 967873 = 725905) (by norm_num)
theorem B3261653 : Blo 858357 3261653 := bbase (se 7 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 3261653 = 76445) (by norm_num)
theorem B1934549 : Blo 858357 1934549 := bbase (se 7 (by rfl) ⟨22670, by rfl⟩ : syracuseStep 1934549 = 45341) (by norm_num)
theorem B918745 : Blo 858357 918745 := bbase (se 2 (by rfl) ⟨344529, by rfl⟩ : syracuseStep 918745 = 689059) (by norm_num)
theorem B1033445 : Blo 858357 1033445 := bbase (se 4 (by rfl) ⟨96885, by rfl⟩ : syracuseStep 1033445 = 193771) (by norm_num)
theorem B967909 : Blo 858357 967909 := bbase (se 4 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 967909 = 181483) (by norm_num)
theorem B967945 : Blo 858357 967945 := bbase (se 2 (by rfl) ⟨362979, by rfl⟩ : syracuseStep 967945 = 725959) (by norm_num)
theorem B1934621 : Blo 858357 1934621 := bbase (se 3 (by rfl) ⟨362741, by rfl⟩ : syracuseStep 1934621 = 725483) (by norm_num)
theorem B967981 : Blo 858357 967981 := bbase (se 3 (by rfl) ⟨181496, by rfl⟩ : syracuseStep 967981 = 362993) (by norm_num)
theorem B1451317 : Blo 858357 1451317 := bbase (se 5 (by rfl) ⟨68030, by rfl⟩ : syracuseStep 1451317 = 136061) (by norm_num)
theorem B1377605 : Blo 858357 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B968017 : Blo 858357 968017 := bbase (se 2 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 968017 = 726013) (by norm_num)
theorem B918865 : Blo 858357 918865 := bbase (se 2 (by rfl) ⟨344574, by rfl⟩ : syracuseStep 918865 = 689149) (by norm_num)
theorem B1934693 : Blo 858357 1934693 := bbase (se 4 (by rfl) ⟨181377, by rfl⟩ : syracuseStep 1934693 = 362755) (by norm_num)
theorem B2901365 : Blo 858357 2901365 := bbase (se 5 (by rfl) ⟨136001, by rfl⟩ : syracuseStep 2901365 = 272003) (by norm_num)
theorem B968053 : Blo 858357 968053 := bbase (se 5 (by rfl) ⟨45377, by rfl⟩ : syracuseStep 968053 = 90755) (by norm_num)
theorem B1287557 : Blo 858357 1287557 := bbase (se 4 (by rfl) ⟨120708, by rfl⟩ : syracuseStep 1287557 = 241417) (by norm_num)
theorem B1451405 : Blo 858357 1451405 := bbase (se 3 (by rfl) ⟨272138, by rfl⟩ : syracuseStep 1451405 = 544277) (by norm_num)
theorem B968089 : Blo 858357 968089 := bbase (se 2 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 968089 = 726067) (by norm_num)
theorem B1287581 : Blo 858357 1287581 := bbase (se 3 (by rfl) ⟨241421, by rfl⟩ : syracuseStep 1287581 = 482843) (by norm_num)
theorem B1934765 : Blo 858357 1934765 := bbase (se 3 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 1934765 = 725537) (by norm_num)
theorem B1287605 : Blo 858357 1287605 := bbase (se 5 (by rfl) ⟨60356, by rfl⟩ : syracuseStep 1287605 = 120713) (by norm_num)
theorem B1631677 : Blo 858357 1631677 := bbase (se 3 (by rfl) ⟨305939, by rfl⟩ : syracuseStep 1631677 = 611879) (by norm_num)
theorem B968125 : Blo 858357 968125 := bbase (se 3 (by rfl) ⟨181523, by rfl⟩ : syracuseStep 968125 = 363047) (by norm_num)
theorem B2065861 : Blo 858357 2065861 := bbase (se 4 (by rfl) ⟨193674, by rfl⟩ : syracuseStep 2065861 = 387349) (by norm_num)
theorem B1287629 : Blo 858357 1287629 := bbase (se 3 (by rfl) ⟨241430, by rfl⟩ : syracuseStep 1287629 = 482861) (by norm_num)
theorem B1287653 : Blo 858357 1287653 := bbase (se 4 (by rfl) ⟨120717, by rfl⟩ : syracuseStep 1287653 = 241435) (by norm_num)
theorem B3261941 : Blo 858357 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B1934837 : Blo 858357 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B1287677 : Blo 858357 1287677 := bbase (se 3 (by rfl) ⟨241439, by rfl⟩ : syracuseStep 1287677 = 482879) (by norm_num)
theorem B1377805 : Blo 858357 1377805 := bbase (se 3 (by rfl) ⟨258338, by rfl⟩ : syracuseStep 1377805 = 516677) (by norm_num)
theorem B1451533 : Blo 858357 1451533 := bbase (se 3 (by rfl) ⟨272162, by rfl⟩ : syracuseStep 1451533 = 544325) (by norm_num)
theorem B1287701 : Blo 858357 1287701 := bbase (se 6 (by rfl) ⟨30180, by rfl⟩ : syracuseStep 1287701 = 60361) (by norm_num)
theorem B1287725 : Blo 858357 1287725 := bbase (se 3 (by rfl) ⟨241448, by rfl⟩ : syracuseStep 1287725 = 482897) (by norm_num)
theorem B1934909 : Blo 858357 1934909 := bbase (se 3 (by rfl) ⟨362795, by rfl⟩ : syracuseStep 1934909 = 725591) (by norm_num)
theorem B1287749 : Blo 858357 1287749 := bbase (se 4 (by rfl) ⟨120726, by rfl⟩ : syracuseStep 1287749 = 241453) (by norm_num)
theorem B1631821 : Blo 858357 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B1222237 : Blo 858357 1222237 := bbase (se 3 (by rfl) ⟨229169, by rfl⟩ : syracuseStep 1222237 = 458339) (by norm_num)
theorem B1287773 : Blo 858357 1287773 := bbase (se 3 (by rfl) ⟨241457, by rfl⟩ : syracuseStep 1287773 = 482915) (by norm_num)
theorem B1451621 : Blo 858357 1451621 := bbase (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) (by norm_num)
theorem B1287797 : Blo 858357 1287797 := bbase (se 5 (by rfl) ⟨60365, by rfl⟩ : syracuseStep 1287797 = 120731) (by norm_num)
theorem B1934981 : Blo 858357 1934981 := bbase (se 4 (by rfl) ⟨181404, by rfl⟩ : syracuseStep 1934981 = 362809) (by norm_num)
theorem B1287821 : Blo 858357 1287821 := bbase (se 3 (by rfl) ⟨241466, by rfl⟩ : syracuseStep 1287821 = 482933) (by norm_num)
theorem B1287845 : Blo 858357 1287845 := bbase (se 4 (by rfl) ⟨120735, by rfl⟩ : syracuseStep 1287845 = 241471) (by norm_num)
theorem B2066093 : Blo 858357 2066093 := bbase (se 3 (by rfl) ⟨387392, by rfl⟩ : syracuseStep 2066093 = 774785) (by norm_num)
theorem B1287869 : Blo 858357 1287869 := bbase (se 3 (by rfl) ⟨241475, by rfl⟩ : syracuseStep 1287869 = 482951) (by norm_num)
theorem B1935053 : Blo 858357 1935053 := bbase (se 3 (by rfl) ⟨362822, by rfl⟩ : syracuseStep 1935053 = 725645) (by norm_num)
theorem B1287893 : Blo 858357 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B1836773 : Blo 858357 1836773 := bbase (se 4 (by rfl) ⟨172197, by rfl⟩ : syracuseStep 1836773 = 344395) (by norm_num)
theorem B1451749 : Blo 858357 1451749 := bbase (se 4 (by rfl) ⟨136101, by rfl⟩ : syracuseStep 1451749 = 272203) (by norm_num)
theorem B1287917 : Blo 858357 1287917 := bbase (se 3 (by rfl) ⟨241484, by rfl⟩ : syracuseStep 1287917 = 482969) (by norm_num)
theorem B1631981 : Blo 858357 1631981 := bbase (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) (by norm_num)
theorem B1287941 : Blo 858357 1287941 := bbase (se 4 (by rfl) ⟨120744, by rfl⟩ : syracuseStep 1287941 = 241489) (by norm_num)
theorem B1378061 : Blo 858357 1378061 := bbase (se 3 (by rfl) ⟨258386, by rfl⟩ : syracuseStep 1378061 = 516773) (by norm_num)
theorem B1935125 : Blo 858357 1935125 := bbase (se 6 (by rfl) ⟨45354, by rfl⟩ : syracuseStep 1935125 = 90709) (by norm_num)
theorem B1287965 : Blo 858357 1287965 := bbase (se 3 (by rfl) ⟨241493, by rfl⟩ : syracuseStep 1287965 = 482987) (by norm_num)
theorem B2901797 : Blo 858357 2901797 := bbase (se 4 (by rfl) ⟨272043, by rfl⟩ : syracuseStep 2901797 = 544087) (by norm_num)
theorem B1287989 : Blo 858357 1287989 := bbase (se 5 (by rfl) ⟨60374, by rfl⟩ : syracuseStep 1287989 = 120749) (by norm_num)
theorem B1451837 : Blo 858357 1451837 := bbase (se 3 (by rfl) ⟨272219, by rfl⟩ : syracuseStep 1451837 = 544439) (by norm_num)
theorem B1288013 : Blo 858357 1288013 := bbase (se 3 (by rfl) ⟨241502, by rfl⟩ : syracuseStep 1288013 = 483005) (by norm_num)
theorem B4892501 : Blo 858357 4892501 := bbase (se 9 (by rfl) ⟨14333, by rfl⟩ : syracuseStep 4892501 = 28667) (by norm_num)
theorem B1836893 : Blo 858357 1836893 := bbase (se 3 (by rfl) ⟨344417, by rfl⟩ : syracuseStep 1836893 = 688835) (by norm_num)
theorem B1935197 : Blo 858357 1935197 := bbase (se 3 (by rfl) ⟨362849, by rfl⟩ : syracuseStep 1935197 = 725699) (by norm_num)
theorem B1288037 : Blo 858357 1288037 := bbase (se 4 (by rfl) ⟨120753, by rfl⟩ : syracuseStep 1288037 = 241507) (by norm_num)
theorem B1288061 : Blo 858357 1288061 := bbase (se 3 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 1288061 = 483023) (by norm_num)
theorem B1632125 : Blo 858357 1632125 := bbase (se 3 (by rfl) ⟨306023, by rfl⟩ : syracuseStep 1632125 = 612047) (by norm_num)
theorem B1468309 : Blo 858357 1468309 := bbase (se 6 (by rfl) ⟨34413, by rfl⟩ : syracuseStep 1468309 = 68827) (by norm_num)
theorem B1288085 : Blo 858357 1288085 := bbase (se 6 (by rfl) ⟨30189, by rfl⟩ : syracuseStep 1288085 = 60379) (by norm_num)
theorem B1935269 : Blo 858357 1935269 := bbase (se 4 (by rfl) ⟨181431, by rfl⟩ : syracuseStep 1935269 = 362863) (by norm_num)
theorem B2172845 : Blo 858357 2172845 := bbase (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) (by norm_num)
theorem B1288109 : Blo 858357 1288109 := bbase (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) (by norm_num)
theorem B1959869 : Blo 858357 1959869 := bbase (se 3 (by rfl) ⟨367475, by rfl⟩ : syracuseStep 1959869 = 734951) (by norm_num)
theorem B1451965 : Blo 858357 1451965 := bbase (se 3 (by rfl) ⟨272243, by rfl⟩ : syracuseStep 1451965 = 544487) (by norm_num)
theorem B1288133 : Blo 858357 1288133 := bbase (se 4 (by rfl) ⟨120762, by rfl⟩ : syracuseStep 1288133 = 241525) (by norm_num)
theorem B1288157 : Blo 858357 1288157 := bbase (se 3 (by rfl) ⟨241529, by rfl⟩ : syracuseStep 1288157 = 483059) (by norm_num)
theorem B1935341 : Blo 858357 1935341 := bbase (se 3 (by rfl) ⟨362876, by rfl⟩ : syracuseStep 1935341 = 725753) (by norm_num)
theorem B1288181 : Blo 858357 1288181 := bbase (se 5 (by rfl) ⟨60383, by rfl⟩ : syracuseStep 1288181 = 120767) (by norm_num)
theorem B1288205 : Blo 858357 1288205 := bbase (se 3 (by rfl) ⟨241538, by rfl⟩ : syracuseStep 1288205 = 483077) (by norm_num)
theorem B1452053 : Blo 858357 1452053 := bbase (se 6 (by rfl) ⟨34032, by rfl⟩ : syracuseStep 1452053 = 68065) (by norm_num)
theorem B1288229 : Blo 858357 1288229 := bbase (se 4 (by rfl) ⟨120771, by rfl⟩ : syracuseStep 1288229 = 241543) (by norm_num)
theorem B2066485 : Blo 858357 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1935413 : Blo 858357 1935413 := bbase (se 5 (by rfl) ⟨90722, by rfl⟩ : syracuseStep 1935413 = 181445) (by norm_num)
theorem B1288253 : Blo 858357 1288253 := bbase (se 3 (by rfl) ⟨241547, by rfl⟩ : syracuseStep 1288253 = 483095) (by norm_num)
theorem B1288277 : Blo 858357 1288277 := bbase (se 8 (by rfl) ⟨7548, by rfl⟩ : syracuseStep 1288277 = 15097) (by norm_num)
theorem B1288301 : Blo 858357 1288301 := bbase (se 3 (by rfl) ⟨241556, by rfl⟩ : syracuseStep 1288301 = 483113) (by norm_num)
theorem B1935485 : Blo 858357 1935485 := bbase (se 3 (by rfl) ⟨362903, by rfl⟩ : syracuseStep 1935485 = 725807) (by norm_num)
theorem B1288325 : Blo 858357 1288325 := bbase (se 4 (by rfl) ⟨120780, by rfl⟩ : syracuseStep 1288325 = 241561) (by norm_num)
theorem B5376149 : Blo 858357 5376149 := bbase (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) (by norm_num)
theorem B1452181 : Blo 858357 1452181 := bbase (se 6 (by rfl) ⟨34035, by rfl⟩ : syracuseStep 1452181 = 68071) (by norm_num)
theorem B1288349 : Blo 858357 1288349 := bbase (se 3 (by rfl) ⟨241565, by rfl⟩ : syracuseStep 1288349 = 483131) (by norm_num)
theorem B1632413 : Blo 858357 1632413 := bbase (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) (by norm_num)
theorem B1288373 : Blo 858357 1288373 := bbase (se 5 (by rfl) ⟨60392, by rfl⟩ : syracuseStep 1288373 = 120785) (by norm_num)
theorem B3582133 : Blo 858357 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B1935557 : Blo 858357 1935557 := bbase (se 4 (by rfl) ⟨181458, by rfl⟩ : syracuseStep 1935557 = 362917) (by norm_num)
theorem B1288397 : Blo 858357 1288397 := bbase (se 3 (by rfl) ⟨241574, by rfl⟩ : syracuseStep 1288397 = 483149) (by norm_num)
theorem B2902229 : Blo 858357 2902229 := bbase (se 7 (by rfl) ⟨34010, by rfl⟩ : syracuseStep 2902229 = 68021) (by norm_num)
theorem B1550549 : Blo 858357 1550549 := bbase (se 7 (by rfl) ⟨18170, by rfl⟩ : syracuseStep 1550549 = 36341) (by norm_num)
theorem B1288421 : Blo 858357 1288421 := bbase (se 4 (by rfl) ⟨120789, by rfl⟩ : syracuseStep 1288421 = 241579) (by norm_num)
theorem B1288445 : Blo 858357 1288445 := bbase (se 3 (by rfl) ⟨241583, by rfl⟩ : syracuseStep 1288445 = 483167) (by norm_num)
theorem B2173189 : Blo 858357 2173189 := bbase (se 4 (by rfl) ⟨203736, by rfl⟩ : syracuseStep 2173189 = 407473) (by norm_num)
theorem B1935629 : Blo 858357 1935629 := bbase (se 3 (by rfl) ⟨362930, by rfl⟩ : syracuseStep 1935629 = 725861) (by norm_num)
theorem B1288469 : Blo 858357 1288469 := bbase (se 6 (by rfl) ⟨30198, by rfl⟩ : syracuseStep 1288469 = 60397) (by norm_num)
theorem B10455317 : Blo 858357 10455317 := bbase (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) (by norm_num)
theorem B1288493 : Blo 858357 1288493 := bbase (se 3 (by rfl) ⟨241592, by rfl⟩ : syracuseStep 1288493 = 483185) (by norm_num)
theorem B4131125 : Blo 858357 4131125 := bbase (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) (by norm_num)
theorem B1632565 : Blo 858357 1632565 := bbase (se 5 (by rfl) ⟨76526, by rfl⟩ : syracuseStep 1632565 = 153053) (by norm_num)
theorem B1288517 : Blo 858357 1288517 := bbase (se 4 (by rfl) ⟨120798, by rfl⟩ : syracuseStep 1288517 = 241597) (by norm_num)
theorem B1935701 : Blo 858357 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B1288541 : Blo 858357 1288541 := bbase (se 3 (by rfl) ⟨241601, by rfl⟩ : syracuseStep 1288541 = 483203) (by norm_num)
theorem B2173301 : Blo 858357 2173301 := bbase (se 5 (by rfl) ⟨101873, by rfl⟩ : syracuseStep 2173301 = 203747) (by norm_num)
theorem B1223029 : Blo 858357 1223029 := bbase (se 5 (by rfl) ⟨57329, by rfl⟩ : syracuseStep 1223029 = 114659) (by norm_num)
theorem B1288565 : Blo 858357 1288565 := bbase (se 5 (by rfl) ⟨60401, by rfl⟩ : syracuseStep 1288565 = 120803) (by norm_num)
theorem B1288589 : Blo 858357 1288589 := bbase (se 3 (by rfl) ⟨241610, by rfl⟩ : syracuseStep 1288589 = 483221) (by norm_num)
theorem B5441941 : Blo 858357 5441941 := bbase (se 6 (by rfl) ⟨127545, by rfl⟩ : syracuseStep 5441941 = 255091) (by norm_num)
theorem B1935773 : Blo 858357 1935773 := bbase (se 3 (by rfl) ⟨362957, by rfl⟩ : syracuseStep 1935773 = 725915) (by norm_num)
theorem B1288613 : Blo 858357 1288613 := bbase (se 4 (by rfl) ⟨120807, by rfl⟩ : syracuseStep 1288613 = 241615) (by norm_num)
theorem B1288637 : Blo 858357 1288637 := bbase (se 3 (by rfl) ⟨241619, by rfl⟩ : syracuseStep 1288637 = 483239) (by norm_num)
theorem B4352453 : Blo 858357 4352453 := bbase (se 4 (by rfl) ⟨408042, by rfl⟩ : syracuseStep 4352453 = 816085) (by norm_num)
theorem B1288661 : Blo 858357 1288661 := bbase (se 7 (by rfl) ⟨15101, by rfl⟩ : syracuseStep 1288661 = 30203) (by norm_num)
theorem B1837525 : Blo 858357 1837525 := bbase (se 7 (by rfl) ⟨21533, by rfl⟩ : syracuseStep 1837525 = 43067) (by norm_num)
theorem B1935845 : Blo 858357 1935845 := bbase (se 4 (by rfl) ⟨181485, by rfl⟩ : syracuseStep 1935845 = 362971) (by norm_num)
theorem B1288685 : Blo 858357 1288685 := bbase (se 3 (by rfl) ⟨241628, by rfl⟩ : syracuseStep 1288685 = 483257) (by norm_num)
theorem B1288709 : Blo 858357 1288709 := bbase (se 4 (by rfl) ⟨120816, by rfl⟩ : syracuseStep 1288709 = 241633) (by norm_num)
theorem B11004437 : Blo 858357 11004437 := bbase (se 6 (by rfl) ⟨257916, by rfl⟩ : syracuseStep 11004437 = 515833) (by norm_num)
theorem B1288733 : Blo 858357 1288733 := bbase (se 3 (by rfl) ⟨241637, by rfl⟩ : syracuseStep 1288733 = 483275) (by norm_num)
theorem B1935917 : Blo 858357 1935917 := bbase (se 3 (by rfl) ⟨362984, by rfl⟩ : syracuseStep 1935917 = 725969) (by norm_num)
theorem B2173493 : Blo 858357 2173493 := bbase (se 5 (by rfl) ⟨101882, by rfl⟩ : syracuseStep 2173493 = 203765) (by norm_num)
theorem B1288757 : Blo 858357 1288757 := bbase (se 5 (by rfl) ⟨60410, by rfl⟩ : syracuseStep 1288757 = 120821) (by norm_num)
theorem B1288781 : Blo 858357 1288781 := bbase (se 3 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 1288781 = 483293) (by norm_num)
theorem B1288805 : Blo 858357 1288805 := bbase (se 4 (by rfl) ⟨120825, by rfl⟩ : syracuseStep 1288805 = 241651) (by norm_num)
theorem B1632869 : Blo 858357 1632869 := bbase (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) (by norm_num)
theorem B1935989 : Blo 858357 1935989 := bbase (se 5 (by rfl) ⟨90749, by rfl⟩ : syracuseStep 1935989 = 181499) (by norm_num)
theorem B1288829 : Blo 858357 1288829 := bbase (se 3 (by rfl) ⟨241655, by rfl⟩ : syracuseStep 1288829 = 483311) (by norm_num)
theorem B2902661 : Blo 858357 2902661 := bbase (se 4 (by rfl) ⟨272124, by rfl⟩ : syracuseStep 2902661 = 544249) (by norm_num)
theorem B1288853 : Blo 858357 1288853 := bbase (se 6 (by rfl) ⟨30207, by rfl⟩ : syracuseStep 1288853 = 60415) (by norm_num)
theorem B3263125 : Blo 858357 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B1288877 : Blo 858357 1288877 := bbase (se 3 (by rfl) ⟨241664, by rfl⟩ : syracuseStep 1288877 = 483329) (by norm_num)
theorem B1936061 : Blo 858357 1936061 := bbase (se 3 (by rfl) ⟨363011, by rfl⟩ : syracuseStep 1936061 = 726023) (by norm_num)
theorem B1223365 : Blo 858357 1223365 := bbase (se 4 (by rfl) ⟨114690, by rfl⟩ : syracuseStep 1223365 = 229381) (by norm_num)
theorem B1288901 : Blo 858357 1288901 := bbase (se 4 (by rfl) ⟨120834, by rfl⟩ : syracuseStep 1288901 = 241669) (by norm_num)
theorem B871117 : Blo 858357 871117 := bbase (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) (by norm_num)
theorem B4467413 : Blo 858357 4467413 := bbase (se 7 (by rfl) ⟨52352, by rfl⟩ : syracuseStep 4467413 = 104705) (by norm_num)
theorem B1288925 : Blo 858357 1288925 := bbase (se 3 (by rfl) ⟨241673, by rfl⟩ : syracuseStep 1288925 = 483347) (by norm_num)
theorem B1288949 : Blo 858357 1288949 := bbase (se 5 (by rfl) ⟨60419, by rfl⟩ : syracuseStep 1288949 = 120839) (by norm_num)
theorem B1936133 : Blo 858357 1936133 := bbase (se 4 (by rfl) ⟨181512, by rfl⟩ : syracuseStep 1936133 = 363025) (by norm_num)
theorem B1288973 : Blo 858357 1288973 := bbase (se 3 (by rfl) ⟨241682, by rfl⟩ : syracuseStep 1288973 = 483365) (by norm_num)
theorem B1288997 : Blo 858357 1288997 := bbase (se 4 (by rfl) ⟨120843, by rfl⟩ : syracuseStep 1288997 = 241687) (by norm_num)
theorem B1059625 : Blo 858357 1059625 := bbase (se 2 (by rfl) ⟨397359, by rfl⟩ : syracuseStep 1059625 = 794719) (by norm_num)
theorem B1289021 : Blo 858357 1289021 := bbase (se 3 (by rfl) ⟨241691, by rfl⟩ : syracuseStep 1289021 = 483383) (by norm_num)
theorem B1936205 : Blo 858357 1936205 := bbase (se 3 (by rfl) ⟨363038, by rfl⟩ : syracuseStep 1936205 = 726077) (by norm_num)
theorem B1289045 : Blo 858357 1289045 := bbase (se 9 (by rfl) ⟨3776, by rfl⟩ : syracuseStep 1289045 = 7553) (by norm_num)
theorem B1289069 : Blo 858357 1289069 := bbase (se 3 (by rfl) ⟨241700, by rfl⟩ : syracuseStep 1289069 = 483401) (by norm_num)
theorem B1289093 : Blo 858357 1289093 := bbase (se 4 (by rfl) ⟨120852, by rfl⟩ : syracuseStep 1289093 = 241705) (by norm_num)
theorem B3672965 : Blo 858357 3672965 := bbase (se 4 (by rfl) ⟨344340, by rfl⟩ : syracuseStep 3672965 = 688681) (by norm_num)
theorem B2206597 : Blo 858357 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B2173837 : Blo 858357 2173837 := bbase (se 3 (by rfl) ⟨407594, by rfl⟩ : syracuseStep 2173837 = 815189) (by norm_num)
theorem B1223581 : Blo 858357 1223581 := bbase (se 3 (by rfl) ⟨229421, by rfl⟩ : syracuseStep 1223581 = 458843) (by norm_num)
theorem B1289117 : Blo 858357 1289117 := bbase (se 3 (by rfl) ⟨241709, by rfl⟩ : syracuseStep 1289117 = 483419) (by norm_num)
theorem B871345 : Blo 858357 871345 := bbase (se 2 (by rfl) ⟨326754, by rfl⟩ : syracuseStep 871345 = 653509) (by norm_num)
theorem B1289141 : Blo 858357 1289141 := bbase (se 5 (by rfl) ⟨60428, by rfl⟩ : syracuseStep 1289141 = 120857) (by norm_num)
theorem B3263429 : Blo 858357 3263429 := bbase (se 4 (by rfl) ⟨305946, by rfl⟩ : syracuseStep 3263429 = 611893) (by norm_num)
theorem B1289165 : Blo 858357 1289165 := bbase (se 3 (by rfl) ⟨241718, by rfl⟩ : syracuseStep 1289165 = 483437) (by norm_num)
theorem B1289189 : Blo 858357 1289189 := bbase (se 4 (by rfl) ⟨120861, by rfl⟩ : syracuseStep 1289189 = 241723) (by norm_num)
theorem B2173949 : Blo 858357 2173949 := bbase (se 3 (by rfl) ⟨407615, by rfl⟩ : syracuseStep 2173949 = 815231) (by norm_num)
theorem B1289213 : Blo 858357 1289213 := bbase (se 3 (by rfl) ⟨241727, by rfl⟩ : syracuseStep 1289213 = 483455) (by norm_num)
theorem B1289237 : Blo 858357 1289237 := bbase (se 6 (by rfl) ⟨30216, by rfl⟩ : syracuseStep 1289237 = 60433) (by norm_num)
theorem B1289261 : Blo 858357 1289261 := bbase (se 3 (by rfl) ⟨241736, by rfl⟩ : syracuseStep 1289261 = 483473) (by norm_num)
theorem B4131893 : Blo 858357 4131893 := bbase (se 5 (by rfl) ⟨193682, by rfl⟩ : syracuseStep 4131893 = 387365) (by norm_num)
theorem B2903093 : Blo 858357 2903093 := bbase (se 5 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 2903093 = 272165) (by norm_num)
theorem B1289285 : Blo 858357 1289285 := bbase (se 4 (by rfl) ⟨120870, by rfl⟩ : syracuseStep 1289285 = 241741) (by norm_num)
theorem B1289309 : Blo 858357 1289309 := bbase (se 3 (by rfl) ⟨241745, by rfl⟩ : syracuseStep 1289309 = 483491) (by norm_num)
theorem B1289333 : Blo 858357 1289333 := bbase (se 5 (by rfl) ⟨60437, by rfl⟩ : syracuseStep 1289333 = 120875) (by norm_num)
theorem B2067581 : Blo 858357 2067581 := bbase (se 3 (by rfl) ⟨387671, by rfl⟩ : syracuseStep 2067581 = 775343) (by norm_num)
theorem B1289357 : Blo 858357 1289357 := bbase (se 3 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 1289357 = 483509) (by norm_num)
theorem B1289381 : Blo 858357 1289381 := bbase (se 4 (by rfl) ⟨120879, by rfl⟩ : syracuseStep 1289381 = 241759) (by norm_num)
theorem B7834805 : Blo 858357 7834805 := bbase (se 5 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 7834805 = 734513) (by norm_num)
theorem B2174141 : Blo 858357 2174141 := bbase (se 3 (by rfl) ⟨407651, by rfl⟩ : syracuseStep 2174141 = 815303) (by norm_num)
theorem B1289405 : Blo 858357 1289405 := bbase (se 3 (by rfl) ⟨241763, by rfl⟩ : syracuseStep 1289405 = 483527) (by norm_num)
theorem B1289429 : Blo 858357 1289429 := bbase (se 7 (by rfl) ⟨15110, by rfl⟩ : syracuseStep 1289429 = 30221) (by norm_num)
theorem B1289453 : Blo 858357 1289453 := bbase (se 3 (by rfl) ⟨241772, by rfl⟩ : syracuseStep 1289453 = 483545) (by norm_num)
theorem B1289477 : Blo 858357 1289477 := bbase (se 4 (by rfl) ⟨120888, by rfl⟩ : syracuseStep 1289477 = 241777) (by norm_num)
theorem B1223957 : Blo 858357 1223957 := bbase (se 6 (by rfl) ⟨28686, by rfl⟩ : syracuseStep 1223957 = 57373) (by norm_num)
theorem B1289501 : Blo 858357 1289501 := bbase (se 3 (by rfl) ⟨241781, by rfl⟩ : syracuseStep 1289501 = 483563) (by norm_num)
theorem B1289525 : Blo 858357 1289525 := bbase (se 5 (by rfl) ⟨60446, by rfl⟩ : syracuseStep 1289525 = 120893) (by norm_num)
theorem B1469765 : Blo 858357 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B1289549 : Blo 858357 1289549 := bbase (se 3 (by rfl) ⟨241790, by rfl⟩ : syracuseStep 1289549 = 483581) (by norm_num)
theorem B1633621 : Blo 858357 1633621 := bbase (se 11 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 1633621 = 2393) (by norm_num)
theorem B1289573 : Blo 858357 1289573 := bbase (se 4 (by rfl) ⟨120897, by rfl⟩ : syracuseStep 1289573 = 241795) (by norm_num)
theorem B1289597 : Blo 858357 1289597 := bbase (se 3 (by rfl) ⟨241799, by rfl⟩ : syracuseStep 1289597 = 483599) (by norm_num)
theorem B1289621 : Blo 858357 1289621 := bbase (se 6 (by rfl) ⟨30225, by rfl⟩ : syracuseStep 1289621 = 60451) (by norm_num)
theorem B1469861 : Blo 858357 1469861 := bbase (se 4 (by rfl) ⟨137799, by rfl⟩ : syracuseStep 1469861 = 275599) (by norm_num)
theorem B1289645 : Blo 858357 1289645 := bbase (se 3 (by rfl) ⟨241808, by rfl⟩ : syracuseStep 1289645 = 483617) (by norm_num)
theorem B6196661 : Blo 858357 6196661 := bbase (se 5 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 6196661 = 580937) (by norm_num)
theorem B1289669 : Blo 858357 1289669 := bbase (se 4 (by rfl) ⟨120906, by rfl⟩ : syracuseStep 1289669 = 241813) (by norm_num)
theorem B1289693 : Blo 858357 1289693 := bbase (se 3 (by rfl) ⟨241817, by rfl⟩ : syracuseStep 1289693 = 483635) (by norm_num)
theorem B2903525 : Blo 858357 2903525 := bbase (se 4 (by rfl) ⟨272205, by rfl⟩ : syracuseStep 2903525 = 544411) (by norm_num)
theorem B1289717 : Blo 858357 1289717 := bbase (se 5 (by rfl) ⟨60455, by rfl⟩ : syracuseStep 1289717 = 120911) (by norm_num)
theorem B1289741 : Blo 858357 1289741 := bbase (se 3 (by rfl) ⟨241826, by rfl⟩ : syracuseStep 1289741 = 483653) (by norm_num)
theorem B2321941 : Blo 858357 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B2174485 : Blo 858357 2174485 := bbase (se 6 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 2174485 = 101929) (by norm_num)
theorem B1289765 : Blo 858357 1289765 := bbase (se 4 (by rfl) ⟨120915, by rfl⟩ : syracuseStep 1289765 = 241831) (by norm_num)
theorem B1289789 : Blo 858357 1289789 := bbase (se 3 (by rfl) ⟨241835, by rfl⟩ : syracuseStep 1289789 = 483671) (by norm_num)
theorem B1289813 : Blo 858357 1289813 := bbase (se 8 (by rfl) ⟨7557, by rfl⟩ : syracuseStep 1289813 = 15115) (by norm_num)
theorem B1289837 : Blo 858357 1289837 := bbase (se 3 (by rfl) ⟨241844, by rfl⟩ : syracuseStep 1289837 = 483689) (by norm_num)
theorem B2174597 : Blo 858357 2174597 := bbase (se 4 (by rfl) ⟨203868, by rfl⟩ : syracuseStep 2174597 = 407737) (by norm_num)
theorem B1289861 : Blo 858357 1289861 := bbase (se 4 (by rfl) ⟨120924, by rfl⟩ : syracuseStep 1289861 = 241849) (by norm_num)
theorem B1961621 : Blo 858357 1961621 := bbase (se 6 (by rfl) ⟨45975, by rfl⟩ : syracuseStep 1961621 = 91951) (by norm_num)
theorem B1289885 : Blo 858357 1289885 := bbase (se 3 (by rfl) ⟨241853, by rfl⟩ : syracuseStep 1289885 = 483707) (by norm_num)
theorem B1289909 : Blo 858357 1289909 := bbase (se 5 (by rfl) ⟨60464, by rfl⟩ : syracuseStep 1289909 = 120929) (by norm_num)
theorem B1289933 : Blo 858357 1289933 := bbase (se 3 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 1289933 = 483725) (by norm_num)
theorem B4353749 : Blo 858357 4353749 := bbase (se 7 (by rfl) ⟨51020, by rfl⟩ : syracuseStep 4353749 = 102041) (by norm_num)
theorem B1289957 : Blo 858357 1289957 := bbase (se 4 (by rfl) ⟨120933, by rfl⟩ : syracuseStep 1289957 = 241867) (by norm_num)
theorem B1289981 : Blo 858357 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B1290005 : Blo 858357 1290005 := bbase (se 6 (by rfl) ⟨30234, by rfl⟩ : syracuseStep 1290005 = 60469) (by norm_num)
theorem B1290029 : Blo 858357 1290029 := bbase (se 3 (by rfl) ⟨241880, by rfl⟩ : syracuseStep 1290029 = 483761) (by norm_num)
theorem B929593 : Blo 858357 929593 := bbase (se 2 (by rfl) ⟨348597, by rfl⟩ : syracuseStep 929593 = 697195) (by norm_num)
theorem B1740613 : Blo 858357 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B2322245 : Blo 858357 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B2174789 : Blo 858357 2174789 := bbase (se 4 (by rfl) ⟨203886, by rfl⟩ : syracuseStep 2174789 = 407773) (by norm_num)
theorem B1290053 : Blo 858357 1290053 := bbase (se 4 (by rfl) ⟨120942, by rfl⟩ : syracuseStep 1290053 = 241885) (by norm_num)
theorem B1290077 : Blo 858357 1290077 := bbase (se 3 (by rfl) ⟨241889, by rfl⟩ : syracuseStep 1290077 = 483779) (by norm_num)
theorem B2445157 : Blo 858357 2445157 := bbase (se 4 (by rfl) ⟨229233, by rfl⟩ : syracuseStep 2445157 = 458467) (by norm_num)
theorem B1290101 : Blo 858357 1290101 := bbase (se 5 (by rfl) ⟨60473, by rfl⟩ : syracuseStep 1290101 = 120947) (by norm_num)
theorem B1740677 : Blo 858357 1740677 := bbase (se 4 (by rfl) ⟨163188, by rfl⟩ : syracuseStep 1740677 = 326377) (by norm_num)
theorem B1290125 : Blo 858357 1290125 := bbase (se 3 (by rfl) ⟨241898, by rfl⟩ : syracuseStep 1290125 = 483797) (by norm_num)
theorem B2903957 : Blo 858357 2903957 := bbase (se 6 (by rfl) ⟨68061, by rfl⟩ : syracuseStep 2903957 = 136123) (by norm_num)
theorem B1306525 : Blo 858357 1306525 := bbase (se 3 (by rfl) ⟨244973, by rfl⟩ : syracuseStep 1306525 = 489947) (by norm_num)
theorem B1290149 : Blo 858357 1290149 := bbase (se 4 (by rfl) ⟨120951, by rfl⟩ : syracuseStep 1290149 = 241903) (by norm_num)
theorem B1290173 : Blo 858357 1290173 := bbase (se 3 (by rfl) ⟨241907, by rfl⟩ : syracuseStep 1290173 = 483815) (by norm_num)
theorem B1290197 : Blo 858357 1290197 := bbase (se 7 (by rfl) ⟨15119, by rfl⟩ : syracuseStep 1290197 = 30239) (by norm_num)
theorem B1290221 : Blo 858357 1290221 := bbase (se 3 (by rfl) ⟨241916, by rfl⟩ : syracuseStep 1290221 = 483833) (by norm_num)
theorem B1290245 : Blo 858357 1290245 := bbase (se 4 (by rfl) ⟨120960, by rfl⟩ : syracuseStep 1290245 = 241921) (by norm_num)
theorem B1290269 : Blo 858357 1290269 := bbase (se 3 (by rfl) ⟨241925, by rfl⟩ : syracuseStep 1290269 = 483851) (by norm_num)
theorem B1290293 : Blo 858357 1290293 := bbase (se 5 (by rfl) ⟨60482, by rfl⟩ : syracuseStep 1290293 = 120965) (by norm_num)
theorem B1290317 : Blo 858357 1290317 := bbase (se 3 (by rfl) ⟨241934, by rfl⟩ : syracuseStep 1290317 = 483869) (by norm_num)
theorem B1290341 : Blo 858357 1290341 := bbase (se 4 (by rfl) ⟨120969, by rfl⟩ : syracuseStep 1290341 = 241939) (by norm_num)
theorem B4345973 : Blo 858357 4345973 := bbase (se 5 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 4345973 = 407435) (by norm_num)
theorem B1290365 : Blo 858357 1290365 := bbase (se 3 (by rfl) ⟨241943, by rfl⟩ : syracuseStep 1290365 = 483887) (by norm_num)
theorem B1568909 : Blo 858357 1568909 := bbase (se 3 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 1568909 = 588341) (by norm_num)
theorem B1290389 : Blo 858357 1290389 := bbase (se 6 (by rfl) ⟨30243, by rfl⟩ : syracuseStep 1290389 = 60487) (by norm_num)
theorem B2175133 : Blo 858357 2175133 := bbase (se 3 (by rfl) ⟨407837, by rfl⟩ : syracuseStep 2175133 = 815675) (by norm_num)
theorem B1290413 : Blo 858357 1290413 := bbase (se 3 (by rfl) ⟨241952, by rfl⟩ : syracuseStep 1290413 = 483905) (by norm_num)
theorem B1290437 : Blo 858357 1290437 := bbase (se 4 (by rfl) ⟨120978, by rfl⟩ : syracuseStep 1290437 = 241957) (by norm_num)
theorem B1323221 : Blo 858357 1323221 := bbase (se 7 (by rfl) ⟨15506, by rfl⟩ : syracuseStep 1323221 = 31013) (by norm_num)
theorem B1290461 : Blo 858357 1290461 := bbase (se 3 (by rfl) ⟨241961, by rfl⟩ : syracuseStep 1290461 = 483923) (by norm_num)
theorem B1290485 : Blo 858357 1290485 := bbase (se 5 (by rfl) ⟨60491, by rfl⟩ : syracuseStep 1290485 = 120983) (by norm_num)
theorem B2175245 : Blo 858357 2175245 := bbase (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) (by norm_num)
theorem B1290509 : Blo 858357 1290509 := bbase (se 3 (by rfl) ⟨241970, by rfl⟩ : syracuseStep 1290509 = 483941) (by norm_num)
theorem B1290533 : Blo 858357 1290533 := bbase (se 4 (by rfl) ⟨120987, by rfl⟩ : syracuseStep 1290533 = 241975) (by norm_num)
theorem B1290557 : Blo 858357 1290557 := bbase (se 3 (by rfl) ⟨241979, by rfl⟩ : syracuseStep 1290557 = 483959) (by norm_num)
theorem B2904389 : Blo 858357 2904389 := bbase (se 4 (by rfl) ⟨272286, by rfl⟩ : syracuseStep 2904389 = 544573) (by norm_num)
theorem B1290581 : Blo 858357 1290581 := bbase (se 10 (by rfl) ⟨1890, by rfl⟩ : syracuseStep 1290581 = 3781) (by norm_num)
theorem B1290605 : Blo 858357 1290605 := bbase (se 3 (by rfl) ⟨241988, by rfl⟩ : syracuseStep 1290605 = 483977) (by norm_num)
theorem B1290629 : Blo 858357 1290629 := bbase (se 4 (by rfl) ⟨120996, by rfl⟩ : syracuseStep 1290629 = 241993) (by norm_num)
theorem B7942549 : Blo 858357 7942549 := bbase (se 6 (by rfl) ⟨186153, by rfl⟩ : syracuseStep 7942549 = 372307) (by norm_num)
theorem B9802133 : Blo 858357 9802133 := bbase (se 6 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 9802133 = 459475) (by norm_num)
theorem B1290653 : Blo 858357 1290653 := bbase (se 3 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 1290653 = 483995) (by norm_num)
theorem B3535285 : Blo 858357 3535285 := bbase (se 5 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 3535285 = 331433) (by norm_num)
theorem B1290677 : Blo 858357 1290677 := bbase (se 5 (by rfl) ⟨60500, by rfl⟩ : syracuseStep 1290677 = 121001) (by norm_num)
theorem B2175437 : Blo 858357 2175437 := bbase (se 3 (by rfl) ⟨407894, by rfl⟩ : syracuseStep 2175437 = 815789) (by norm_num)
theorem B1290701 : Blo 858357 1290701 := bbase (se 3 (by rfl) ⟨242006, by rfl⟩ : syracuseStep 1290701 = 484013) (by norm_num)
theorem B14701013 : Blo 858357 14701013 := bbase (se 7 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 14701013 = 344555) (by norm_num)
theorem B1290725 : Blo 858357 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B1290749 : Blo 858357 1290749 := bbase (se 3 (by rfl) ⟨242015, by rfl⟩ : syracuseStep 1290749 = 484031) (by norm_num)
theorem B1470997 : Blo 858357 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B1290773 : Blo 858357 1290773 := bbase (se 6 (by rfl) ⟨30252, by rfl⟩ : syracuseStep 1290773 = 60505) (by norm_num)
theorem B1290797 : Blo 858357 1290797 := bbase (se 3 (by rfl) ⟨242024, by rfl⟩ : syracuseStep 1290797 = 484049) (by norm_num)
theorem B1290821 : Blo 858357 1290821 := bbase (se 4 (by rfl) ⟨121014, by rfl⟩ : syracuseStep 1290821 = 242029) (by norm_num)
theorem B1290845 : Blo 858357 1290845 := bbase (se 3 (by rfl) ⟨242033, by rfl⟩ : syracuseStep 1290845 = 484067) (by norm_num)
theorem B7336565 : Blo 858357 7336565 := bbase (se 5 (by rfl) ⟨343901, by rfl⟩ : syracuseStep 7336565 = 687803) (by norm_num)
theorem B930449 : Blo 858357 930449 := bbase (se 2 (by rfl) ⟨348918, by rfl⟩ : syracuseStep 930449 = 697837) (by norm_num)
theorem B2175781 : Blo 858357 2175781 := bbase (se 4 (by rfl) ⟨203979, by rfl⟩ : syracuseStep 2175781 = 407959) (by norm_num)
theorem B2356037 : Blo 858357 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B979861 : Blo 858357 979861 := bbase (se 6 (by rfl) ⟨22965, by rfl⟩ : syracuseStep 979861 = 45931) (by norm_num)
theorem B2175893 : Blo 858357 2175893 := bbase (se 6 (by rfl) ⟨50997, by rfl⟩ : syracuseStep 2175893 = 101995) (by norm_num)
theorem B1160101 : Blo 858357 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B4355045 : Blo 858357 4355045 := bbase (se 4 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 4355045 = 816571) (by norm_num)
theorem B1102837 : Blo 858357 1102837 := bbase (se 5 (by rfl) ⟨51695, by rfl⟩ : syracuseStep 1102837 = 103391) (by norm_num)
theorem B3265541 : Blo 858357 3265541 := bbase (se 4 (by rfl) ⟨306144, by rfl⟩ : syracuseStep 3265541 = 612289) (by norm_num)
theorem B1086473 : Blo 858357 1086473 := bbase (se 2 (by rfl) ⟨407427, by rfl⟩ : syracuseStep 1086473 = 814855) (by norm_num)
theorem B1471517 : Blo 858357 1471517 := bbase (se 3 (by rfl) ⟨275909, by rfl⟩ : syracuseStep 1471517 = 551819) (by norm_num)
theorem B1086529 : Blo 858357 1086529 := bbase (se 2 (by rfl) ⟨407448, by rfl⟩ : syracuseStep 1086529 = 814897) (by norm_num)
theorem B2176085 : Blo 858357 2176085 := bbase (se 8 (by rfl) ⟨12750, by rfl⟩ : syracuseStep 2176085 = 25501) (by norm_num)
theorem B2897045 : Blo 858357 2897045 := bbase (se 6 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 2897045 = 135799) (by norm_num)
theorem B1086625 : Blo 858357 1086625 := bbase (se 2 (by rfl) ⟨407484, by rfl⟩ : syracuseStep 1086625 = 814969) (by norm_num)
theorem B1307821 : Blo 858357 1307821 := bbase (se 3 (by rfl) ⟨245216, by rfl⟩ : syracuseStep 1307821 = 490433) (by norm_num)
theorem B1471709 : Blo 858357 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B3667189 : Blo 858357 3667189 := bbase (se 5 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 3667189 = 343799) (by norm_num)
theorem B1307893 : Blo 858357 1307893 := bbase (se 5 (by rfl) ⟨61307, by rfl⟩ : syracuseStep 1307893 = 122615) (by norm_num)
theorem B4125973 : Blo 858357 4125973 := bbase (se 6 (by rfl) ⟨96702, by rfl⟩ : syracuseStep 4125973 = 193405) (by norm_num)
theorem B3265829 : Blo 858357 3265829 := bbase (se 4 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 3265829 = 612343) (by norm_num)
theorem B980281 : Blo 858357 980281 := bbase (se 2 (by rfl) ⟨367605, by rfl⟩ : syracuseStep 980281 = 735211) (by norm_num)
theorem B2446661 : Blo 858357 2446661 := bbase (se 4 (by rfl) ⟨229374, by rfl⟩ : syracuseStep 2446661 = 458749) (by norm_num)
theorem B1086797 : Blo 858357 1086797 := bbase (se 3 (by rfl) ⟨203774, by rfl⟩ : syracuseStep 1086797 = 407549) (by norm_num)
theorem B4347269 : Blo 858357 4347269 := bbase (se 4 (by rfl) ⟨407556, by rfl⟩ : syracuseStep 4347269 = 815113) (by norm_num)
theorem B1086853 : Blo 858357 1086853 := bbase (se 4 (by rfl) ⟨101892, by rfl⟩ : syracuseStep 1086853 = 203785) (by norm_num)
theorem B2651525 : Blo 858357 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B2176429 : Blo 858357 2176429 := bbase (se 3 (by rfl) ⟨408080, by rfl⟩ : syracuseStep 2176429 = 816161) (by norm_num)
theorem B3716533 : Blo 858357 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B1086949 : Blo 858357 1086949 := bbase (se 4 (by rfl) ⟨101901, by rfl⟩ : syracuseStep 1086949 = 203803) (by norm_num)
theorem B10589717 : Blo 858357 10589717 := bbase (se 6 (by rfl) ⟨248196, by rfl⟩ : syracuseStep 10589717 = 496393) (by norm_num)
theorem B2176541 : Blo 858357 2176541 := bbase (se 3 (by rfl) ⟨408101, by rfl⟩ : syracuseStep 2176541 = 816203) (by norm_num)
theorem B2897477 : Blo 858357 2897477 := bbase (se 4 (by rfl) ⟨271638, by rfl⟩ : syracuseStep 2897477 = 543277) (by norm_num)
theorem B931429 : Blo 858357 931429 := bbase (se 4 (by rfl) ⟨87321, by rfl⟩ : syracuseStep 931429 = 174643) (by norm_num)
theorem B1087121 : Blo 858357 1087121 := bbase (se 2 (by rfl) ⟨407670, by rfl⟩ : syracuseStep 1087121 = 815341) (by norm_num)
theorem B1087177 : Blo 858357 1087177 := bbase (se 2 (by rfl) ⟨407691, by rfl⟩ : syracuseStep 1087177 = 815383) (by norm_num)
theorem B6190805 : Blo 858357 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B2176733 : Blo 858357 2176733 := bbase (se 3 (by rfl) ⟨408137, by rfl⟩ : syracuseStep 2176733 = 816275) (by norm_num)
theorem B2750213 : Blo 858357 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B1652501 : Blo 858357 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B9418517 : Blo 858357 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B1087273 : Blo 858357 1087273 := bbase (se 2 (by rfl) ⟨407727, by rfl⟩ : syracuseStep 1087273 = 815455) (by norm_num)
theorem B1046405 : Blo 858357 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B1161101 : Blo 858357 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B1087445 : Blo 858357 1087445 := bbase (se 7 (by rfl) ⟨12743, by rfl⟩ : syracuseStep 1087445 = 25487) (by norm_num)
theorem B980957 : Blo 858357 980957 := bbase (se 3 (by rfl) ⟨183929, by rfl⟩ : syracuseStep 980957 = 367859) (by norm_num)
theorem B2897909 : Blo 858357 2897909 := bbase (se 5 (by rfl) ⟨135839, by rfl⟩ : syracuseStep 2897909 = 271679) (by norm_num)
theorem B1087501 : Blo 858357 1087501 := bbase (se 3 (by rfl) ⟨203906, by rfl⟩ : syracuseStep 1087501 = 407813) (by norm_num)
theorem B2095141 : Blo 858357 2095141 := bbase (se 4 (by rfl) ⟨196419, by rfl⟩ : syracuseStep 2095141 = 392839) (by norm_num)
theorem B981029 : Blo 858357 981029 := bbase (se 4 (by rfl) ⟨91971, by rfl⟩ : syracuseStep 981029 = 183943) (by norm_num)
theorem B1931309 : Blo 858357 1931309 := bbase (se 3 (by rfl) ⟨362120, by rfl⟩ : syracuseStep 1931309 = 724241) (by norm_num)
theorem B2177077 : Blo 858357 2177077 := bbase (se 5 (by rfl) ⟨102050, by rfl⟩ : syracuseStep 2177077 = 204101) (by norm_num)
theorem B1087597 : Blo 858357 1087597 := bbase (se 3 (by rfl) ⟨203924, by rfl⟩ : syracuseStep 1087597 = 407849) (by norm_num)
theorem B1931381 : Blo 858357 1931381 := bbase (se 5 (by rfl) ⟨90533, by rfl⟩ : syracuseStep 1931381 = 181067) (by norm_num)
theorem B4642933 : Blo 858357 4642933 := bbase (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) (by norm_num)
theorem B2177189 : Blo 858357 2177189 := bbase (se 4 (by rfl) ⟨204111, by rfl⟩ : syracuseStep 2177189 = 408223) (by norm_num)
theorem B1931453 : Blo 858357 1931453 := bbase (se 3 (by rfl) ⟨362147, by rfl⟩ : syracuseStep 1931453 = 724295) (by norm_num)
theorem B4356341 : Blo 858357 4356341 := bbase (se 5 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 4356341 = 408407) (by norm_num)
theorem B1931525 : Blo 858357 1931525 := bbase (se 4 (by rfl) ⟨181080, by rfl⟩ : syracuseStep 1931525 = 362161) (by norm_num)
theorem B1087769 : Blo 858357 1087769 := bbase (se 2 (by rfl) ⟨407913, by rfl⟩ : syracuseStep 1087769 = 815827) (by norm_num)
theorem B2611493 : Blo 858357 2611493 := bbase (se 4 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 2611493 = 489655) (by norm_num)
theorem B1931597 : Blo 858357 1931597 := bbase (se 3 (by rfl) ⟨362174, by rfl⟩ : syracuseStep 1931597 = 724349) (by norm_num)
theorem B1087825 : Blo 858357 1087825 := bbase (se 2 (by rfl) ⟨407934, by rfl⟩ : syracuseStep 1087825 = 815869) (by norm_num)
theorem B2177381 : Blo 858357 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B1931669 : Blo 858357 1931669 := bbase (se 6 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 1931669 = 90547) (by norm_num)
theorem B3307925 : Blo 858357 3307925 := bbase (se 6 (by rfl) ⟨77529, by rfl⟩ : syracuseStep 3307925 = 155059) (by norm_num)
theorem B2898341 : Blo 858357 2898341 := bbase (se 4 (by rfl) ⟨271719, by rfl⟩ : syracuseStep 2898341 = 543439) (by norm_num)
theorem B1087921 : Blo 858357 1087921 := bbase (se 2 (by rfl) ⟨407970, by rfl⟩ : syracuseStep 1087921 = 815941) (by norm_num)
theorem B3267013 : Blo 858357 3267013 := bbase (se 4 (by rfl) ⟨306282, by rfl⟩ : syracuseStep 3267013 = 612565) (by norm_num)
theorem B1931741 : Blo 858357 1931741 := bbase (se 3 (by rfl) ⟨362201, by rfl⟩ : syracuseStep 1931741 = 724403) (by norm_num)
theorem B1931813 : Blo 858357 1931813 := bbase (se 4 (by rfl) ⟨181107, by rfl⟩ : syracuseStep 1931813 = 362215) (by norm_num)
theorem B1448509 : Blo 858357 1448509 := bbase (se 3 (by rfl) ⟨271595, by rfl⟩ : syracuseStep 1448509 = 543191) (by norm_num)
theorem B1088093 : Blo 858357 1088093 := bbase (se 3 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 1088093 = 408035) (by norm_num)
theorem B1743461 : Blo 858357 1743461 := bbase (se 4 (by rfl) ⟨163449, by rfl⟩ : syracuseStep 1743461 = 326899) (by norm_num)
theorem B1931885 : Blo 858357 1931885 := bbase (se 3 (by rfl) ⟨362228, by rfl⟩ : syracuseStep 1931885 = 724457) (by norm_num)
theorem B1432205 : Blo 858357 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B1448597 : Blo 858357 1448597 := bbase (se 6 (by rfl) ⟨33951, by rfl⟩ : syracuseStep 1448597 = 67903) (by norm_num)
theorem B4348565 : Blo 858357 4348565 := bbase (se 6 (by rfl) ⟨101919, by rfl⟩ : syracuseStep 4348565 = 203839) (by norm_num)
theorem B1088149 : Blo 858357 1088149 := bbase (se 6 (by rfl) ⟨25503, by rfl⟩ : syracuseStep 1088149 = 51007) (by norm_num)
theorem B1161901 : Blo 858357 1161901 := bbase (se 3 (by rfl) ⟨217856, by rfl⟩ : syracuseStep 1161901 = 435713) (by norm_num)
theorem B1931957 : Blo 858357 1931957 := bbase (se 5 (by rfl) ⟨90560, by rfl⟩ : syracuseStep 1931957 = 181121) (by norm_num)
theorem B2177725 : Blo 858357 2177725 := bbase (se 3 (by rfl) ⟨408323, by rfl⟩ : syracuseStep 2177725 = 816647) (by norm_num)
theorem B1088245 : Blo 858357 1088245 := bbase (se 5 (by rfl) ⟨51011, by rfl⟩ : syracuseStep 1088245 = 102023) (by norm_num)
theorem B3267317 : Blo 858357 3267317 := bbase (se 5 (by rfl) ⟨153155, by rfl⟩ : syracuseStep 3267317 = 306311) (by norm_num)
theorem B1932029 : Blo 858357 1932029 := bbase (se 3 (by rfl) ⟨362255, by rfl⟩ : syracuseStep 1932029 = 724511) (by norm_num)
theorem B1448725 : Blo 858357 1448725 := bbase (se 6 (by rfl) ⟨33954, by rfl⟩ : syracuseStep 1448725 = 67909) (by norm_num)
theorem B1833749 : Blo 858357 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B1178389 : Blo 858357 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B2063141 : Blo 858357 2063141 := bbase (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) (by norm_num)
theorem B2177837 : Blo 858357 2177837 := bbase (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) (by norm_num)
theorem B1932101 : Blo 858357 1932101 := bbase (se 4 (by rfl) ⟨181134, by rfl⟩ : syracuseStep 1932101 = 362269) (by norm_num)
theorem B2898773 : Blo 858357 2898773 := bbase (se 9 (by rfl) ⟨8492, by rfl⟩ : syracuseStep 2898773 = 16985) (by norm_num)
theorem B3259237 : Blo 858357 3259237 := bbase (se 4 (by rfl) ⟨305553, by rfl⟩ : syracuseStep 3259237 = 611107) (by norm_num)
theorem B1858405 : Blo 858357 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B1448813 : Blo 858357 1448813 := bbase (se 3 (by rfl) ⟨271652, by rfl⟩ : syracuseStep 1448813 = 543305) (by norm_num)
theorem B2448245 : Blo 858357 2448245 := bbase (se 5 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 2448245 = 229523) (by norm_num)
theorem B1932173 : Blo 858357 1932173 := bbase (se 3 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 1932173 = 724565) (by norm_num)
theorem B1489805 : Blo 858357 1489805 := bbase (se 3 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 1489805 = 558677) (by norm_num)
theorem B1088417 : Blo 858357 1088417 := bbase (se 2 (by rfl) ⟨408156, by rfl⟩ : syracuseStep 1088417 = 816313) (by norm_num)
theorem B1932245 : Blo 858357 1932245 := bbase (se 7 (by rfl) ⟨22643, by rfl⟩ : syracuseStep 1932245 = 45287) (by norm_num)
theorem B4709333 : Blo 858357 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B1088473 : Blo 858357 1088473 := bbase (se 2 (by rfl) ⟨408177, by rfl⟩ : syracuseStep 1088473 = 816355) (by norm_num)
theorem B1448941 : Blo 858357 1448941 := bbase (se 3 (by rfl) ⟨271676, by rfl⟩ : syracuseStep 1448941 = 543353) (by norm_num)
theorem B2178029 : Blo 858357 2178029 := bbase (se 3 (by rfl) ⟨408380, by rfl⟩ : syracuseStep 2178029 = 816761) (by norm_num)
theorem B1833997 : Blo 858357 1833997 := bbase (se 3 (by rfl) ⟨343874, by rfl⟩ : syracuseStep 1833997 = 687749) (by norm_num)
theorem B2751509 : Blo 858357 2751509 := bbase (se 6 (by rfl) ⟨64488, by rfl⟩ : syracuseStep 2751509 = 128977) (by norm_num)
theorem B1932317 : Blo 858357 1932317 := bbase (se 3 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 1932317 = 724619) (by norm_num)
theorem B965677 : Blo 858357 965677 := bbase (se 3 (by rfl) ⟨181064, by rfl⟩ : syracuseStep 965677 = 362129) (by norm_num)
theorem B1088569 : Blo 858357 1088569 := bbase (se 2 (by rfl) ⟨408213, by rfl⟩ : syracuseStep 1088569 = 816427) (by norm_num)
theorem B1449029 : Blo 858357 1449029 := bbase (se 4 (by rfl) ⟨135846, by rfl⟩ : syracuseStep 1449029 = 271693) (by norm_num)
theorem B965713 : Blo 858357 965713 := bbase (se 2 (by rfl) ⟨362142, by rfl⟩ : syracuseStep 965713 = 724285) (by norm_num)
theorem B1932389 : Blo 858357 1932389 := bbase (se 4 (by rfl) ⟨181161, by rfl⟩ : syracuseStep 1932389 = 362323) (by norm_num)
theorem B965749 : Blo 858357 965749 := bbase (se 5 (by rfl) ⟨45269, by rfl⟩ : syracuseStep 965749 = 90539) (by norm_num)
theorem B3259541 : Blo 858357 3259541 := bbase (se 6 (by rfl) ⟨76395, by rfl⟩ : syracuseStep 3259541 = 152791) (by norm_num)
theorem B11025557 : Blo 858357 11025557 := bbase (se 6 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 11025557 = 516823) (by norm_num)
theorem B965785 : Blo 858357 965785 := bbase (se 2 (by rfl) ⟨362169, by rfl⟩ : syracuseStep 965785 = 724339) (by norm_num)
theorem B1932461 : Blo 858357 1932461 := bbase (se 3 (by rfl) ⟨362336, by rfl⟩ : syracuseStep 1932461 = 724673) (by norm_num)
theorem B965821 : Blo 858357 965821 := bbase (se 3 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 965821 = 362183) (by norm_num)
theorem B1449157 : Blo 858357 1449157 := bbase (se 4 (by rfl) ⟨135858, by rfl⟩ : syracuseStep 1449157 = 271717) (by norm_num)
theorem B1031393 : Blo 858357 1031393 := bbase (se 2 (by rfl) ⟨386772, by rfl⟩ : syracuseStep 1031393 = 773545) (by norm_num)
theorem B965857 : Blo 858357 965857 := bbase (se 2 (by rfl) ⟨362196, by rfl⟩ : syracuseStep 965857 = 724393) (by norm_num)
theorem B1088741 : Blo 858357 1088741 := bbase (se 4 (by rfl) ⟨102069, by rfl⟩ : syracuseStep 1088741 = 204139) (by norm_num)
theorem B1932533 : Blo 858357 1932533 := bbase (se 5 (by rfl) ⟨90587, by rfl⟩ : syracuseStep 1932533 = 181175) (by norm_num)
theorem B965893 : Blo 858357 965893 := bbase (se 4 (by rfl) ⟨90552, by rfl⟩ : syracuseStep 965893 = 181105) (by norm_num)
theorem B2899205 : Blo 858357 2899205 := bbase (se 4 (by rfl) ⟨271800, by rfl⟩ : syracuseStep 2899205 = 543601) (by norm_num)
theorem B1375517 : Blo 858357 1375517 := bbase (se 3 (by rfl) ⟨257909, by rfl⟩ : syracuseStep 1375517 = 515819) (by norm_num)
theorem B1449245 : Blo 858357 1449245 := bbase (se 3 (by rfl) ⟨271733, by rfl⟩ : syracuseStep 1449245 = 543467) (by norm_num)
theorem B1088797 : Blo 858357 1088797 := bbase (se 3 (by rfl) ⟨204149, by rfl⟩ : syracuseStep 1088797 = 408299) (by norm_num)
theorem B965929 : Blo 858357 965929 := bbase (se 2 (by rfl) ⟨362223, by rfl⟩ : syracuseStep 965929 = 724447) (by norm_num)
theorem B1932605 : Blo 858357 1932605 := bbase (se 3 (by rfl) ⟨362363, by rfl⟩ : syracuseStep 1932605 = 724727) (by norm_num)
theorem B965965 : Blo 858357 965965 := bbase (se 3 (by rfl) ⟨181118, by rfl⟩ : syracuseStep 965965 = 362237) (by norm_num)
theorem B916849 : Blo 858357 916849 := bbase (se 2 (by rfl) ⟨343818, by rfl⟩ : syracuseStep 916849 = 687637) (by norm_num)
theorem B966001 : Blo 858357 966001 := bbase (se 2 (by rfl) ⟨362250, by rfl⟩ : syracuseStep 966001 = 724501) (by norm_num)
theorem B1088893 : Blo 858357 1088893 := bbase (se 3 (by rfl) ⟨204167, by rfl⟩ : syracuseStep 1088893 = 408335) (by norm_num)
theorem B1932677 : Blo 858357 1932677 := bbase (se 4 (by rfl) ⟨181188, by rfl⟩ : syracuseStep 1932677 = 362377) (by norm_num)
theorem B966037 : Blo 858357 966037 := bbase (se 6 (by rfl) ⟨22641, by rfl⟩ : syracuseStep 966037 = 45283) (by norm_num)
theorem B1449373 : Blo 858357 1449373 := bbase (se 3 (by rfl) ⟨271757, by rfl⟩ : syracuseStep 1449373 = 543515) (by norm_num)
theorem B1162669 : Blo 858357 1162669 := bbase (se 3 (by rfl) ⟨218000, by rfl⟩ : syracuseStep 1162669 = 436001) (by norm_num)
theorem B6528437 : Blo 858357 6528437 := bbase (se 5 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 6528437 = 612041) (by norm_num)
theorem B966073 : Blo 858357 966073 := bbase (se 2 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 966073 = 724555) (by norm_num)
theorem B1932749 : Blo 858357 1932749 := bbase (se 3 (by rfl) ⟨362390, by rfl⟩ : syracuseStep 1932749 = 724781) (by norm_num)
theorem B966109 : Blo 858357 966109 := bbase (se 3 (by rfl) ⟨181145, by rfl⟩ : syracuseStep 966109 = 362291) (by norm_num)
theorem B1449461 : Blo 858357 1449461 := bbase (se 5 (by rfl) ⟨67943, by rfl⟩ : syracuseStep 1449461 = 135887) (by norm_num)
theorem B966145 : Blo 858357 966145 := bbase (se 2 (by rfl) ⟨362304, by rfl⟩ : syracuseStep 966145 = 724609) (by norm_num)
theorem B1834501 : Blo 858357 1834501 := bbase (se 4 (by rfl) ⟨171984, by rfl⟩ : syracuseStep 1834501 = 343969) (by norm_num)
theorem B1932821 : Blo 858357 1932821 := bbase (se 6 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 1932821 = 90601) (by norm_num)
theorem B2448917 : Blo 858357 2448917 := bbase (se 6 (by rfl) ⟨57396, by rfl⟩ : syracuseStep 2448917 = 114793) (by norm_num)
theorem B1629733 : Blo 858357 1629733 := bbase (se 4 (by rfl) ⟨152787, by rfl⟩ : syracuseStep 1629733 = 305575) (by norm_num)
theorem B966181 : Blo 858357 966181 := bbase (se 4 (by rfl) ⟨90579, by rfl⟩ : syracuseStep 966181 = 181159) (by norm_num)
theorem B1089065 : Blo 858357 1089065 := bbase (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) (by norm_num)
theorem B966217 : Blo 858357 966217 := bbase (se 2 (by rfl) ⟨362331, by rfl⟩ : syracuseStep 966217 = 724663) (by norm_num)
theorem B1932893 : Blo 858357 1932893 := bbase (se 3 (by rfl) ⟨362417, by rfl⟩ : syracuseStep 1932893 = 724835) (by norm_num)
theorem B1089121 : Blo 858357 1089121 := bbase (se 2 (by rfl) ⟨408420, by rfl⟩ : syracuseStep 1089121 = 816841) (by norm_num)
theorem B966253 : Blo 858357 966253 := bbase (se 3 (by rfl) ⟨181172, by rfl⟩ : syracuseStep 966253 = 362345) (by norm_num)
theorem B1449589 : Blo 858357 1449589 := bbase (se 5 (by rfl) ⟨67949, by rfl⟩ : syracuseStep 1449589 = 135899) (by norm_num)
theorem B966289 : Blo 858357 966289 := bbase (se 2 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 966289 = 724717) (by norm_num)
theorem B1932965 : Blo 858357 1932965 := bbase (se 4 (by rfl) ⟨181215, by rfl⟩ : syracuseStep 1932965 = 362431) (by norm_num)
theorem B1629877 : Blo 858357 1629877 := bbase (se 5 (by rfl) ⟨76400, by rfl⟩ : syracuseStep 1629877 = 152801) (by norm_num)
theorem B4890293 : Blo 858357 4890293 := bbase (se 5 (by rfl) ⟨229232, by rfl⟩ : syracuseStep 4890293 = 458465) (by norm_num)
theorem B966325 : Blo 858357 966325 := bbase (se 5 (by rfl) ⟨45296, by rfl⟩ : syracuseStep 966325 = 90593) (by norm_num)
theorem B2899637 : Blo 858357 2899637 := bbase (se 5 (by rfl) ⟨135920, by rfl⟩ : syracuseStep 2899637 = 271841) (by norm_num)
theorem B1449677 : Blo 858357 1449677 := bbase (se 3 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 1449677 = 543629) (by norm_num)
theorem B3776213 : Blo 858357 3776213 := bbase (se 7 (by rfl) ⟨44252, by rfl⟩ : syracuseStep 3776213 = 88505) (by norm_num)
theorem B1031897 : Blo 858357 1031897 := bbase (se 2 (by rfl) ⟨386961, by rfl⟩ : syracuseStep 1031897 = 773923) (by norm_num)
theorem B966361 : Blo 858357 966361 := bbase (se 2 (by rfl) ⟨362385, by rfl⟩ : syracuseStep 966361 = 724771) (by norm_num)
theorem B2064101 : Blo 858357 2064101 := bbase (se 4 (by rfl) ⟨193509, by rfl⟩ : syracuseStep 2064101 = 387019) (by norm_num)
theorem B1654501 : Blo 858357 1654501 := bbase (se 4 (by rfl) ⟨155109, by rfl⟩ : syracuseStep 1654501 = 310219) (by norm_num)
theorem B1933037 : Blo 858357 1933037 := bbase (se 3 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 1933037 = 724889) (by norm_num)
theorem B966397 : Blo 858357 966397 := bbase (se 3 (by rfl) ⟨181199, by rfl⟩ : syracuseStep 966397 = 362399) (by norm_num)
theorem B1031945 : Blo 858357 1031945 := bbase (se 2 (by rfl) ⟨386979, by rfl⟩ : syracuseStep 1031945 = 773959) (by norm_num)
theorem B966433 : Blo 858357 966433 := bbase (se 2 (by rfl) ⟨362412, by rfl⟩ : syracuseStep 966433 = 724825) (by norm_num)
theorem B917293 : Blo 858357 917293 := bbase (se 3 (by rfl) ⟨171992, by rfl⟩ : syracuseStep 917293 = 343985) (by norm_num)
theorem B1933109 : Blo 858357 1933109 := bbase (se 5 (by rfl) ⟨90614, by rfl⟩ : syracuseStep 1933109 = 181229) (by norm_num)
theorem B966469 : Blo 858357 966469 := bbase (se 4 (by rfl) ⟨90606, by rfl⟩ : syracuseStep 966469 = 181213) (by norm_num)
theorem B1449805 : Blo 858357 1449805 := bbase (se 3 (by rfl) ⟨271838, by rfl⟩ : syracuseStep 1449805 = 543677) (by norm_num)
theorem B1630037 : Blo 858357 1630037 := bbase (se 9 (by rfl) ⟨4775, by rfl⟩ : syracuseStep 1630037 = 9551) (by norm_num)
theorem B6520661 : Blo 858357 6520661 := bbase (se 9 (by rfl) ⟨19103, by rfl⟩ : syracuseStep 6520661 = 38207) (by norm_num)
theorem B917353 : Blo 858357 917353 := bbase (se 2 (by rfl) ⟨344007, by rfl⟩ : syracuseStep 917353 = 688015) (by norm_num)
theorem B966505 : Blo 858357 966505 := bbase (se 2 (by rfl) ⟨362439, by rfl⟩ : syracuseStep 966505 = 724879) (by norm_num)
theorem B5504885 : Blo 858357 5504885 := bbase (se 5 (by rfl) ⟨258041, by rfl⟩ : syracuseStep 5504885 = 516083) (by norm_num)
theorem B1933181 : Blo 858357 1933181 := bbase (se 3 (by rfl) ⟨362471, by rfl⟩ : syracuseStep 1933181 = 724943) (by norm_num)
theorem B966541 : Blo 858357 966541 := bbase (se 3 (by rfl) ⟨181226, by rfl⟩ : syracuseStep 966541 = 362453) (by norm_num)
theorem B1376165 : Blo 858357 1376165 := bbase (se 4 (by rfl) ⟨129015, by rfl⟩ : syracuseStep 1376165 = 258031) (by norm_num)
theorem B3096485 : Blo 858357 3096485 := bbase (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) (by norm_num)
theorem B1449893 : Blo 858357 1449893 := bbase (se 4 (by rfl) ⟨135927, by rfl⟩ : syracuseStep 1449893 = 271855) (by norm_num)
theorem B4349861 : Blo 858357 4349861 := bbase (se 4 (by rfl) ⟨407799, by rfl⟩ : syracuseStep 4349861 = 815599) (by norm_num)
theorem B966577 : Blo 858357 966577 := bbase (se 2 (by rfl) ⟨362466, by rfl⟩ : syracuseStep 966577 = 724933) (by norm_num)
theorem B1933253 : Blo 858357 1933253 := bbase (se 4 (by rfl) ⟨181242, by rfl⟩ : syracuseStep 1933253 = 362485) (by norm_num)
theorem B2449349 : Blo 858357 2449349 := bbase (se 4 (by rfl) ⟨229626, by rfl⟩ : syracuseStep 2449349 = 459253) (by norm_num)
theorem B966613 : Blo 858357 966613 := bbase (se 7 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 966613 = 22655) (by norm_num)
theorem B1630181 : Blo 858357 1630181 := bbase (se 4 (by rfl) ⟨152829, by rfl⟩ : syracuseStep 1630181 = 305659) (by norm_num)
theorem B966649 : Blo 858357 966649 := bbase (se 2 (by rfl) ⟨362493, by rfl⟩ : syracuseStep 966649 = 724987) (by norm_num)
theorem B860163 : Blo 858357 860163 := bstep (se 1 (by rfl) ⟨645122, by rfl⟩ : syracuseStep 860163 = 1290245) B1290245
theorem B1376273 : Blo 858357 1376273 := bstep (se 2 (by rfl) ⟨516102, by rfl⟩ : syracuseStep 1376273 = 1032205) B1032205
theorem B1450001 : Blo 858357 1450001 := bstep (se 2 (by rfl) ⟨543750, by rfl⟩ : syracuseStep 1450001 = 1087501) B1087501
theorem B860179 : Blo 858357 860179 := bstep (se 1 (by rfl) ⟨645134, by rfl⟩ : syracuseStep 860179 = 1290269) B1290269
theorem B860195 : Blo 858357 860195 := bstep (se 1 (by rfl) ⟨645146, by rfl⟩ : syracuseStep 860195 = 1290293) B1290293
theorem B1933361 : Blo 858357 1933361 := bstep (se 2 (by rfl) ⟨725010, by rfl⟩ : syracuseStep 1933361 = 1450021) B1450021
theorem B860211 : Blo 858357 860211 := bstep (se 1 (by rfl) ⟨645158, by rfl⟩ : syracuseStep 860211 = 1290317) B1290317
theorem B2793521 : Blo 858357 2793521 := bstep (se 2 (by rfl) ⟨1047570, by rfl⟩ : syracuseStep 2793521 = 2095141) B2095141
theorem B1933379 : Blo 858357 1933379 := bstep (se 1 (by rfl) ⟨1450034, by rfl⟩ : syracuseStep 1933379 = 2900069) B2900069
theorem B860227 : Blo 858357 860227 := bstep (se 1 (by rfl) ⟨645170, by rfl⟩ : syracuseStep 860227 = 1290341) B1290341
theorem B966739 : Blo 858357 966739 := bstep (se 1 (by rfl) ⟨725054, by rfl⟩ : syracuseStep 966739 = 1450109) B1450109
theorem B860243 : Blo 858357 860243 := bstep (se 1 (by rfl) ⟨645182, by rfl⟩ : syracuseStep 860243 = 1290365) B1290365
theorem B860259 : Blo 858357 860259 := bstep (se 1 (by rfl) ⟨645194, by rfl⟩ : syracuseStep 860259 = 1290389) B1290389
theorem B860275 : Blo 858357 860275 := bstep (se 1 (by rfl) ⟨645206, by rfl⟩ : syracuseStep 860275 = 1290413) B1290413
theorem B860291 : Blo 858357 860291 := bstep (se 1 (by rfl) ⟨645218, by rfl⟩ : syracuseStep 860291 = 1290437) B1290437
theorem B1450129 : Blo 858357 1450129 := bstep (se 2 (by rfl) ⟨543798, by rfl⟩ : syracuseStep 1450129 = 1087597) B1087597
theorem B860307 : Blo 858357 860307 := bstep (se 1 (by rfl) ⟨645230, by rfl⟩ : syracuseStep 860307 = 1290461) B1290461
theorem B860323 : Blo 858357 860323 := bstep (se 1 (by rfl) ⟨645242, by rfl⟩ : syracuseStep 860323 = 1290485) B1290485
theorem B1450163 : Blo 858357 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B860339 : Blo 858357 860339 := bstep (se 1 (by rfl) ⟨645254, by rfl⟩ : syracuseStep 860339 = 1290509) B1290509
theorem B860355 : Blo 858357 860355 := bstep (se 1 (by rfl) ⟨645266, by rfl⟩ : syracuseStep 860355 = 1290533) B1290533
theorem B2900177 : Blo 858357 2900177 := bstep (se 2 (by rfl) ⟨1087566, by rfl⟩ : syracuseStep 2900177 = 2175133) B2175133
theorem B860371 : Blo 858357 860371 := bstep (se 1 (by rfl) ⟨645278, by rfl⟩ : syracuseStep 860371 = 1290557) B1290557
theorem B966883 : Blo 858357 966883 := bstep (se 1 (by rfl) ⟨725162, by rfl⟩ : syracuseStep 966883 = 1450325) B1450325
theorem B860387 : Blo 858357 860387 := bstep (se 1 (by rfl) ⟨645290, by rfl⟩ : syracuseStep 860387 = 1290581) B1290581
theorem B860403 : Blo 858357 860403 := bstep (se 1 (by rfl) ⟨645302, by rfl⟩ : syracuseStep 860403 = 1290605) B1290605
theorem B860419 : Blo 858357 860419 := bstep (se 1 (by rfl) ⟨645314, by rfl⟩ : syracuseStep 860419 = 1290629) B1290629
theorem B860435 : Blo 858357 860435 := bstep (se 1 (by rfl) ⟨645326, by rfl⟩ : syracuseStep 860435 = 1290653) B1290653
theorem B860451 : Blo 858357 860451 := bstep (se 1 (by rfl) ⟨645338, by rfl⟩ : syracuseStep 860451 = 1290677) B1290677
theorem B1450291 : Blo 858357 1450291 := bstep (se 1 (by rfl) ⟨1087718, by rfl⟩ : syracuseStep 1450291 = 2175437) B2175437
theorem B860467 : Blo 858357 860467 := bstep (se 1 (by rfl) ⟨645350, by rfl⟩ : syracuseStep 860467 = 1290701) B1290701
theorem B860483 : Blo 858357 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B1933649 : Blo 858357 1933649 := bstep (se 2 (by rfl) ⟨725118, by rfl⟩ : syracuseStep 1933649 = 1450237) B1450237
theorem B860499 : Blo 858357 860499 := bstep (se 1 (by rfl) ⟨645374, by rfl⟩ : syracuseStep 860499 = 1290749) B1290749
theorem B1933667 : Blo 858357 1933667 := bstep (se 1 (by rfl) ⟨1450250, by rfl⟩ : syracuseStep 1933667 = 2900501) B2900501
theorem B860515 : Blo 858357 860515 := bstep (se 1 (by rfl) ⟨645386, by rfl⟩ : syracuseStep 860515 = 1290773) B1290773
theorem B967027 : Blo 858357 967027 := bstep (se 1 (by rfl) ⟨725270, by rfl⟩ : syracuseStep 967027 = 1450541) B1450541
theorem B860531 : Blo 858357 860531 := bstep (se 1 (by rfl) ⟨645398, by rfl⟩ : syracuseStep 860531 = 1290797) B1290797
theorem B860547 : Blo 858357 860547 := bstep (se 1 (by rfl) ⟨645410, by rfl⟩ : syracuseStep 860547 = 1290821) B1290821
theorem B860563 : Blo 858357 860563 := bstep (se 1 (by rfl) ⟨645422, by rfl⟩ : syracuseStep 860563 = 1290845) B1290845
theorem B4891043 : Blo 858357 4891043 := bstep (se 1 (by rfl) ⟨3668282, by rfl⟩ : syracuseStep 4891043 = 7336565) B7336565
theorem B1450433 : Blo 858357 1450433 := bstep (se 2 (by rfl) ⟨543912, by rfl⟩ : syracuseStep 1450433 = 1087825) B1087825
theorem B1630705 : Blo 858357 1630705 := bstep (se 2 (by rfl) ⟨611514, by rfl⟩ : syracuseStep 1630705 = 1223029) B1223029
theorem B967171 : Blo 858357 967171 := bstep (se 1 (by rfl) ⟨725378, by rfl⟩ : syracuseStep 967171 = 1450757) B1450757
theorem B1376785 : Blo 858357 1376785 := bstep (se 2 (by rfl) ⟨516294, by rfl⟩ : syracuseStep 1376785 = 1032589) B1032589
theorem B1450561 : Blo 858357 1450561 := bstep (se 2 (by rfl) ⟨543960, by rfl⟩ : syracuseStep 1450561 = 1087921) B1087921
theorem B3924557 : Blo 858357 3924557 := bstep (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) B1471709
theorem B1450595 : Blo 858357 1450595 := bstep (se 1 (by rfl) ⟨1087946, by rfl⟩ : syracuseStep 1450595 = 2175893) B2175893
theorem B1933937 : Blo 858357 1933937 := bstep (se 2 (by rfl) ⟨725226, by rfl⟩ : syracuseStep 1933937 = 1450453) B1450453
theorem B2450033 : Blo 858357 2450033 := bstep (se 2 (by rfl) ⟨918762, by rfl⟩ : syracuseStep 2450033 = 1837525) B1837525
theorem B1933955 : Blo 858357 1933955 := bstep (se 1 (by rfl) ⟨1450466, by rfl⟩ : syracuseStep 1933955 = 2900933) B2900933
theorem B967315 : Blo 858357 967315 := bstep (se 1 (by rfl) ⟨725486, by rfl⟩ : syracuseStep 967315 = 1450973) B1450973
theorem B1450723 : Blo 858357 1450723 := bstep (se 1 (by rfl) ⟨1088042, by rfl⟩ : syracuseStep 1450723 = 2176085) B2176085
theorem B2900717 : Blo 858357 2900717 := bstep (se 3 (by rfl) ⟨543884, by rfl⟩ : syracuseStep 2900717 = 1087769) B1087769
theorem B2753315 : Blo 858357 2753315 := bstep (se 1 (by rfl) ⟨2064986, by rfl⟩ : syracuseStep 2753315 = 4129973) B4129973
theorem B2900771 : Blo 858357 2900771 := bstep (se 1 (by rfl) ⟨2175578, by rfl⟩ : syracuseStep 2900771 = 4351157) B4351157
theorem B967459 : Blo 858357 967459 := bstep (se 1 (by rfl) ⟨725594, by rfl⟩ : syracuseStep 967459 = 1451189) B1451189
theorem B4350833 : Blo 858357 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B1450865 : Blo 858357 1450865 := bstep (se 2 (by rfl) ⟨544074, by rfl⟩ : syracuseStep 1450865 = 1088149) B1088149
theorem B1631107 : Blo 858357 1631107 := bstep (se 1 (by rfl) ⟨1223330, by rfl⟩ : syracuseStep 1631107 = 2446661) B2446661
theorem B1934225 : Blo 858357 1934225 := bstep (se 2 (by rfl) ⟨725334, by rfl⟩ : syracuseStep 1934225 = 1450669) B1450669
theorem B1549201 : Blo 858357 1549201 := bstep (se 2 (by rfl) ⟨580950, by rfl⟩ : syracuseStep 1549201 = 1161901) B1161901
theorem B1934243 : Blo 858357 1934243 := bstep (se 1 (by rfl) ⟨1450682, by rfl⟩ : syracuseStep 1934243 = 2901365) B2901365
theorem B1631153 : Blo 858357 1631153 := bstep (se 2 (by rfl) ⟨611682, by rfl⟩ : syracuseStep 1631153 = 1223365) B1223365
theorem B967603 : Blo 858357 967603 := bstep (se 1 (by rfl) ⟨725702, by rfl⟩ : syracuseStep 967603 = 1451405) B1451405
theorem B19104709 : Blo 858357 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1450993 : Blo 858357 1450993 := bstep (se 2 (by rfl) ⟨544122, by rfl⟩ : syracuseStep 1450993 = 1088245) B1088245
theorem B1451027 : Blo 858357 1451027 := bstep (se 1 (by rfl) ⟨1088270, by rfl⟩ : syracuseStep 1451027 = 2176541) B2176541
theorem B2901041 : Blo 858357 2901041 := bstep (se 2 (by rfl) ⟨1087890, by rfl⟩ : syracuseStep 2901041 = 2175781) B2175781
theorem B967747 : Blo 858357 967747 := bstep (se 1 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 967747 = 1451621) B1451621
theorem B3671153 : Blo 858357 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B1377395 : Blo 858357 1377395 := bstep (se 1 (by rfl) ⟨1033046, by rfl⟩ : syracuseStep 1377395 = 2066093) B2066093
theorem B4899973 : Blo 858357 4899973 := bstep (se 4 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 4899973 = 918745) B918745
theorem B1451155 : Blo 858357 1451155 := bstep (se 1 (by rfl) ⟨1088366, by rfl⟩ : syracuseStep 1451155 = 2176733) B2176733
theorem B1836209 : Blo 858357 1836209 := bstep (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) B1377157
theorem B1934513 : Blo 858357 1934513 := bstep (se 2 (by rfl) ⟨725442, by rfl⟩ : syracuseStep 1934513 = 1450885) B1450885
theorem B2942129 : Blo 858357 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B918707 : Blo 858357 918707 := bstep (se 1 (by rfl) ⟨689030, by rfl⟩ : syracuseStep 918707 = 1378061) B1378061
theorem B1934531 : Blo 858357 1934531 := bstep (se 1 (by rfl) ⟨1450898, by rfl⟩ : syracuseStep 1934531 = 2901797) B2901797
theorem B1631441 : Blo 858357 1631441 := bstep (se 2 (by rfl) ⟨611790, by rfl⟩ : syracuseStep 1631441 = 1223581) B1223581
theorem B967891 : Blo 858357 967891 := bstep (se 1 (by rfl) ⟨725918, by rfl⟩ : syracuseStep 967891 = 1451837) B1451837
theorem B3261667 : Blo 858357 3261667 := bstep (se 1 (by rfl) ⟨2446250, by rfl⟩ : syracuseStep 3261667 = 4892501) B4892501
theorem B1451297 : Blo 858357 1451297 := bstep (se 2 (by rfl) ⟨544236, by rfl⟩ : syracuseStep 1451297 = 1088473) B1088473
theorem B968035 : Blo 858357 968035 := bstep (se 1 (by rfl) ⟨726026, by rfl⟩ : syracuseStep 968035 = 1452053) B1452053
theorem B1287539 : Blo 858357 1287539 := bstep (se 1 (by rfl) ⟨965654, by rfl⟩ : syracuseStep 1287539 = 1931309) B1931309
theorem B1287569 : Blo 858357 1287569 := bstep (se 2 (by rfl) ⟨482838, by rfl⟩ : syracuseStep 1287569 = 965677) B965677
theorem B1451425 : Blo 858357 1451425 := bstep (se 2 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 1451425 = 1088569) B1088569
theorem B1287587 : Blo 858357 1287587 := bstep (se 1 (by rfl) ⟨965690, by rfl⟩ : syracuseStep 1287587 = 1931381) B1931381
theorem B1287617 : Blo 858357 1287617 := bstep (se 2 (by rfl) ⟨482856, by rfl⟩ : syracuseStep 1287617 = 965713) B965713
theorem B1451459 : Blo 858357 1451459 := bstep (se 1 (by rfl) ⟨1088594, by rfl⟩ : syracuseStep 1451459 = 2177189) B2177189
theorem B5506501 : Blo 858357 5506501 := bstep (se 4 (by rfl) ⟨516234, by rfl⟩ : syracuseStep 5506501 = 1032469) B1032469
theorem B1934801 : Blo 858357 1934801 := bstep (se 2 (by rfl) ⟨725550, by rfl⟩ : syracuseStep 1934801 = 1451101) B1451101
theorem B1287635 : Blo 858357 1287635 := bstep (se 1 (by rfl) ⟨965726, by rfl⟩ : syracuseStep 1287635 = 1931453) B1931453
theorem B1934819 : Blo 858357 1934819 := bstep (se 1 (by rfl) ⟨1451114, by rfl⟩ : syracuseStep 1934819 = 2902229) B2902229
theorem B1287665 : Blo 858357 1287665 := bstep (se 2 (by rfl) ⟨482874, by rfl⟩ : syracuseStep 1287665 = 965749) B965749
theorem B1287683 : Blo 858357 1287683 := bstep (se 1 (by rfl) ⟨965762, by rfl⟩ : syracuseStep 1287683 = 1931525) B1931525
theorem B1287713 : Blo 858357 1287713 := bstep (se 2 (by rfl) ⟨482892, by rfl⟩ : syracuseStep 1287713 = 965785) B965785
theorem B2754083 : Blo 858357 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B1287731 : Blo 858357 1287731 := bstep (se 1 (by rfl) ⟨965798, by rfl⟩ : syracuseStep 1287731 = 1931597) B1931597
theorem B1451587 : Blo 858357 1451587 := bstep (se 1 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 1451587 = 2177381) B2177381
theorem B2901581 : Blo 858357 2901581 := bstep (se 3 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 2901581 = 1088093) B1088093
theorem B1287761 : Blo 858357 1287761 := bstep (se 2 (by rfl) ⟨482910, by rfl⟩ : syracuseStep 1287761 = 965821) B965821
theorem B1287779 : Blo 858357 1287779 := bstep (se 1 (by rfl) ⟨965834, by rfl⟩ : syracuseStep 1287779 = 1931669) B1931669
theorem B1287809 : Blo 858357 1287809 := bstep (se 2 (by rfl) ⟨482928, by rfl⟩ : syracuseStep 1287809 = 965857) B965857
theorem B2901635 : Blo 858357 2901635 := bstep (se 1 (by rfl) ⟨2176226, by rfl⟩ : syracuseStep 2901635 = 4352453) B4352453
theorem B5228165 : Blo 858357 5228165 := bstep (se 4 (by rfl) ⟨490140, by rfl⟩ : syracuseStep 5228165 = 980281) B980281
theorem B1287827 : Blo 858357 1287827 := bstep (se 1 (by rfl) ⟨965870, by rfl⟩ : syracuseStep 1287827 = 1931741) B1931741
theorem B1287857 : Blo 858357 1287857 := bstep (se 2 (by rfl) ⟨482946, by rfl⟩ : syracuseStep 1287857 = 965893) B965893
theorem B1287875 : Blo 858357 1287875 := bstep (se 1 (by rfl) ⟨965906, by rfl⟩ : syracuseStep 1287875 = 1931813) B1931813
theorem B4130509 : Blo 858357 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B1451729 : Blo 858357 1451729 := bstep (se 2 (by rfl) ⟨544398, by rfl⟩ : syracuseStep 1451729 = 1088797) B1088797
theorem B1287905 : Blo 858357 1287905 := bstep (se 2 (by rfl) ⟨482964, by rfl⟩ : syracuseStep 1287905 = 965929) B965929
theorem B1935089 : Blo 858357 1935089 := bstep (se 2 (by rfl) ⟨725658, by rfl⟩ : syracuseStep 1935089 = 1451317) B1451317
theorem B1287923 : Blo 858357 1287923 := bstep (se 1 (by rfl) ⟨965942, by rfl⟩ : syracuseStep 1287923 = 1931885) B1931885
theorem B1935107 : Blo 858357 1935107 := bstep (se 1 (by rfl) ⟨1451330, by rfl⟩ : syracuseStep 1935107 = 2902661) B2902661
theorem B1287953 : Blo 858357 1287953 := bstep (se 2 (by rfl) ⟨482982, by rfl⟩ : syracuseStep 1287953 = 965965) B965965
theorem B1287971 : Blo 858357 1287971 := bstep (se 1 (by rfl) ⟨965978, by rfl⟩ : syracuseStep 1287971 = 1931957) B1931957
theorem B1222465 : Blo 858357 1222465 := bstep (se 2 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 1222465 = 916849) B916849
theorem B1288001 : Blo 858357 1288001 := bstep (se 2 (by rfl) ⟨483000, by rfl⟩ : syracuseStep 1288001 = 966001) B966001
theorem B1451857 : Blo 858357 1451857 := bstep (se 2 (by rfl) ⟨544446, by rfl⟩ : syracuseStep 1451857 = 1088893) B1088893
theorem B1288019 : Blo 858357 1288019 := bstep (se 1 (by rfl) ⟨966014, by rfl⟩ : syracuseStep 1288019 = 1932029) B1932029
theorem B1222499 : Blo 858357 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B1288049 : Blo 858357 1288049 := bstep (se 2 (by rfl) ⟨483018, by rfl⟩ : syracuseStep 1288049 = 966037) B966037
theorem B1451891 : Blo 858357 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B1288067 : Blo 858357 1288067 := bstep (se 1 (by rfl) ⟨966050, by rfl⟩ : syracuseStep 1288067 = 1932101) B1932101
theorem B11913101 : Blo 858357 11913101 := bstep (se 3 (by rfl) ⟨2233706, by rfl⟩ : syracuseStep 11913101 = 4467413) B4467413
theorem B2901905 : Blo 858357 2901905 := bstep (se 2 (by rfl) ⟨1088214, by rfl⟩ : syracuseStep 2901905 = 2176429) B2176429
theorem B1550225 : Blo 858357 1550225 := bstep (se 2 (by rfl) ⟨581334, by rfl⟩ : syracuseStep 1550225 = 1162669) B1162669
theorem B1288097 : Blo 858357 1288097 := bstep (se 2 (by rfl) ⟨483036, by rfl⟩ : syracuseStep 1288097 = 966073) B966073
theorem B1632163 : Blo 858357 1632163 := bstep (se 1 (by rfl) ⟨1224122, by rfl⟩ : syracuseStep 1632163 = 2448245) B2448245
theorem B2754481 : Blo 858357 2754481 := bstep (se 2 (by rfl) ⟨1032930, by rfl⟩ : syracuseStep 2754481 = 2065861) B2065861
theorem B1288115 : Blo 858357 1288115 := bstep (se 1 (by rfl) ⟨966086, by rfl⟩ : syracuseStep 1288115 = 1932173) B1932173
theorem B993203 : Blo 858357 993203 := bstep (se 1 (by rfl) ⟨744902, by rfl⟩ : syracuseStep 993203 = 1489805) B1489805
theorem B1288145 : Blo 858357 1288145 := bstep (se 2 (by rfl) ⟨483054, by rfl⟩ : syracuseStep 1288145 = 966109) B966109
theorem B1288163 : Blo 858357 1288163 := bstep (se 1 (by rfl) ⟨966122, by rfl⟩ : syracuseStep 1288163 = 1932245) B1932245
theorem B3139555 : Blo 858357 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B1452019 : Blo 858357 1452019 := bstep (se 1 (by rfl) ⟨1089014, by rfl⟩ : syracuseStep 1452019 = 2178029) B2178029
theorem B1288193 : Blo 858357 1288193 := bstep (se 2 (by rfl) ⟨483072, by rfl⟩ : syracuseStep 1288193 = 966145) B966145
theorem B7333901 : Blo 858357 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B1837073 : Blo 858357 1837073 := bstep (se 2 (by rfl) ⟨688902, by rfl⟩ : syracuseStep 1837073 = 1377805) B1377805
theorem B1935377 : Blo 858357 1935377 := bstep (se 2 (by rfl) ⟨725766, by rfl⟩ : syracuseStep 1935377 = 1451533) B1451533
theorem B1288211 : Blo 858357 1288211 := bstep (se 1 (by rfl) ⟨966158, by rfl⟩ : syracuseStep 1288211 = 1932317) B1932317
theorem B2754595 : Blo 858357 2754595 := bstep (se 1 (by rfl) ⟨2065946, by rfl⟩ : syracuseStep 2754595 = 4131893) B4131893
theorem B1935395 : Blo 858357 1935395 := bstep (se 1 (by rfl) ⟨1451546, by rfl⟩ : syracuseStep 1935395 = 2903093) B2903093
theorem B2172977 : Blo 858357 2172977 := bstep (se 2 (by rfl) ⟨814866, by rfl⟩ : syracuseStep 2172977 = 1629733) B1629733
theorem B1288241 : Blo 858357 1288241 := bstep (se 2 (by rfl) ⟨483090, by rfl⟩ : syracuseStep 1288241 = 966181) B966181
theorem B1288259 : Blo 858357 1288259 := bstep (se 1 (by rfl) ⟨966194, by rfl⟩ : syracuseStep 1288259 = 1932389) B1932389
theorem B1378387 : Blo 858357 1378387 := bstep (se 1 (by rfl) ⟨1033790, by rfl⟩ : syracuseStep 1378387 = 2067581) B2067581
theorem B1288289 : Blo 858357 1288289 := bstep (se 2 (by rfl) ⟨483108, by rfl⟩ : syracuseStep 1288289 = 966217) B966217
theorem B2173027 : Blo 858357 2173027 := bstep (se 1 (by rfl) ⟨1629770, by rfl⟩ : syracuseStep 2173027 = 3259541) B3259541
theorem B7350371 : Blo 858357 7350371 := bstep (se 1 (by rfl) ⟨5512778, by rfl⟩ : syracuseStep 7350371 = 11025557) B11025557
theorem B1288307 : Blo 858357 1288307 := bstep (se 1 (by rfl) ⟨966230, by rfl⟩ : syracuseStep 1288307 = 1932461) B1932461
theorem B1452161 : Blo 858357 1452161 := bstep (se 2 (by rfl) ⟨544560, by rfl⟩ : syracuseStep 1452161 = 1089121) B1089121
theorem B1288337 : Blo 858357 1288337 := bstep (se 2 (by rfl) ⟨483126, by rfl⟩ : syracuseStep 1288337 = 966253) B966253
theorem B1288355 : Blo 858357 1288355 := bstep (se 1 (by rfl) ⟨966266, by rfl⟩ : syracuseStep 1288355 = 1932533) B1932533
theorem B1288385 : Blo 858357 1288385 := bstep (se 2 (by rfl) ⟨483144, by rfl⟩ : syracuseStep 1288385 = 966289) B966289
theorem B6187205 : Blo 858357 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B1288403 : Blo 858357 1288403 := bstep (se 1 (by rfl) ⟨966302, by rfl⟩ : syracuseStep 1288403 = 1932605) B1932605
theorem B2173169 : Blo 858357 2173169 := bstep (se 2 (by rfl) ⟨814938, by rfl⟩ : syracuseStep 2173169 = 1629877) B1629877
theorem B1288433 : Blo 858357 1288433 := bstep (se 2 (by rfl) ⟨483162, by rfl⟩ : syracuseStep 1288433 = 966325) B966325
theorem B1288451 : Blo 858357 1288451 := bstep (se 1 (by rfl) ⟨966338, by rfl⟩ : syracuseStep 1288451 = 1932677) B1932677
theorem B1288481 : Blo 858357 1288481 := bstep (se 2 (by rfl) ⟨483180, by rfl⟩ : syracuseStep 1288481 = 966361) B966361
theorem B4131107 : Blo 858357 4131107 := bstep (se 1 (by rfl) ⟨3098330, by rfl⟩ : syracuseStep 4131107 = 6196661) B6196661
theorem B4352291 : Blo 858357 4352291 := bstep (se 1 (by rfl) ⟨3264218, by rfl⟩ : syracuseStep 4352291 = 6528437) B6528437
theorem B2206001 : Blo 858357 2206001 := bstep (se 2 (by rfl) ⟨827250, by rfl⟩ : syracuseStep 2206001 = 1654501) B1654501
theorem B1935665 : Blo 858357 1935665 := bstep (se 2 (by rfl) ⟨725874, by rfl⟩ : syracuseStep 1935665 = 1451749) B1451749
theorem B1288499 : Blo 858357 1288499 := bstep (se 1 (by rfl) ⟨966374, by rfl⟩ : syracuseStep 1288499 = 1932749) B1932749
theorem B1935683 : Blo 858357 1935683 := bstep (se 1 (by rfl) ⟨1451762, by rfl⟩ : syracuseStep 1935683 = 2903525) B2903525
theorem B1288529 : Blo 858357 1288529 := bstep (se 2 (by rfl) ⟨483198, by rfl⟩ : syracuseStep 1288529 = 966397) B966397
theorem B1288547 : Blo 858357 1288547 := bstep (se 1 (by rfl) ⟨966410, by rfl⟩ : syracuseStep 1288547 = 1932821) B1932821
theorem B1632611 : Blo 858357 1632611 := bstep (se 1 (by rfl) ⟨1224458, by rfl⟩ : syracuseStep 1632611 = 2448917) B2448917
theorem B1288577 : Blo 858357 1288577 := bstep (se 2 (by rfl) ⟨483216, by rfl⟩ : syracuseStep 1288577 = 966433) B966433
theorem B1223057 : Blo 858357 1223057 := bstep (se 2 (by rfl) ⟨458646, by rfl⟩ : syracuseStep 1223057 = 917293) B917293
theorem B1288595 : Blo 858357 1288595 := bstep (se 1 (by rfl) ⟨966446, by rfl⟩ : syracuseStep 1288595 = 1932893) B1932893
theorem B1239457 : Blo 858357 1239457 := bstep (se 2 (by rfl) ⟨464796, by rfl⟩ : syracuseStep 1239457 = 929593) B929593
theorem B2902445 : Blo 858357 2902445 := bstep (se 3 (by rfl) ⟨544208, by rfl⟩ : syracuseStep 2902445 = 1088417) B1088417
theorem B2320817 : Blo 858357 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B1288625 : Blo 858357 1288625 := bstep (se 2 (by rfl) ⟨483234, by rfl⟩ : syracuseStep 1288625 = 966469) B966469
theorem B1288643 : Blo 858357 1288643 := bstep (se 1 (by rfl) ⟨966482, by rfl⟩ : syracuseStep 1288643 = 1932965) B1932965
theorem B1223137 : Blo 858357 1223137 := bstep (se 2 (by rfl) ⟨458676, by rfl⟩ : syracuseStep 1223137 = 917353) B917353
theorem B1288673 : Blo 858357 1288673 := bstep (se 2 (by rfl) ⟨483252, by rfl⟩ : syracuseStep 1288673 = 966505) B966505
theorem B2902499 : Blo 858357 2902499 := bstep (se 1 (by rfl) ⟨2176874, by rfl⟩ : syracuseStep 2902499 = 4353749) B4353749
theorem B2517475 : Blo 858357 2517475 := bstep (se 1 (by rfl) ⟨1888106, by rfl⟩ : syracuseStep 2517475 = 3776213) B3776213
theorem B1288691 : Blo 858357 1288691 := bstep (se 1 (by rfl) ⟨966518, by rfl⟩ : syracuseStep 1288691 = 1933037) B1933037
theorem B1288721 : Blo 858357 1288721 := bstep (se 2 (by rfl) ⟨483270, by rfl⟩ : syracuseStep 1288721 = 966541) B966541
theorem B1288739 : Blo 858357 1288739 := bstep (se 1 (by rfl) ⟨966554, by rfl⟩ : syracuseStep 1288739 = 1933109) B1933109
theorem B1288769 : Blo 858357 1288769 := bstep (se 2 (by rfl) ⟨483288, by rfl⟩ : syracuseStep 1288769 = 966577) B966577
theorem B2615885 : Blo 858357 2615885 := bstep (se 3 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 2615885 = 980957) B980957
theorem B1935953 : Blo 858357 1935953 := bstep (se 2 (by rfl) ⟨725982, by rfl⟩ : syracuseStep 1935953 = 1451965) B1451965
theorem B1288787 : Blo 858357 1288787 := bstep (se 1 (by rfl) ⟨966590, by rfl⟩ : syracuseStep 1288787 = 1933181) B1933181
theorem B1935971 : Blo 858357 1935971 := bstep (se 1 (by rfl) ⟨1451978, by rfl⟩ : syracuseStep 1935971 = 2903957) B2903957
theorem B1288817 : Blo 858357 1288817 := bstep (se 2 (by rfl) ⟨483306, by rfl⟩ : syracuseStep 1288817 = 966613) B966613
theorem B1288835 : Blo 858357 1288835 := bstep (se 1 (by rfl) ⟨966626, by rfl⟩ : syracuseStep 1288835 = 1933253) B1933253
theorem B1632899 : Blo 858357 1632899 := bstep (se 1 (by rfl) ⟨1224674, by rfl⟩ : syracuseStep 1632899 = 2449349) B2449349
theorem B1288865 : Blo 858357 1288865 := bstep (se 2 (by rfl) ⟨483324, by rfl⟩ : syracuseStep 1288865 = 966649) B966649
theorem B1288883 : Blo 858357 1288883 := bstep (se 1 (by rfl) ⟨966662, by rfl⟩ : syracuseStep 1288883 = 1933325) B1933325
theorem B2206403 : Blo 858357 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B1288913 : Blo 858357 1288913 := bstep (se 2 (by rfl) ⟨483342, by rfl⟩ : syracuseStep 1288913 = 966685) B966685
theorem B1288931 : Blo 858357 1288931 := bstep (se 1 (by rfl) ⟨966698, by rfl⟩ : syracuseStep 1288931 = 1933397) B1933397
theorem B2755313 : Blo 858357 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B2902769 : Blo 858357 2902769 := bstep (se 2 (by rfl) ⟨1088538, by rfl⟩ : syracuseStep 2902769 = 2177077) B2177077
theorem B1288961 : Blo 858357 1288961 := bstep (se 2 (by rfl) ⟨483360, by rfl⟩ : syracuseStep 1288961 = 966721) B966721
theorem B2616077 : Blo 858357 2616077 := bstep (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) B981029
theorem B1288979 : Blo 858357 1288979 := bstep (se 1 (by rfl) ⟨966734, by rfl⟩ : syracuseStep 1288979 = 1933469) B1933469
theorem B1289009 : Blo 858357 1289009 := bstep (se 2 (by rfl) ⟨483378, by rfl⟩ : syracuseStep 1289009 = 966757) B966757
theorem B1289027 : Blo 858357 1289027 := bstep (se 1 (by rfl) ⟨966770, by rfl⟩ : syracuseStep 1289027 = 1933541) B1933541
theorem B1289057 : Blo 858357 1289057 := bstep (se 2 (by rfl) ⟨483396, by rfl⟩ : syracuseStep 1289057 = 966793) B966793
theorem B1936241 : Blo 858357 1936241 := bstep (se 2 (by rfl) ⟨726090, by rfl⟩ : syracuseStep 1936241 = 1452181) B1452181
theorem B1289075 : Blo 858357 1289075 := bstep (se 1 (by rfl) ⟨966806, by rfl⟩ : syracuseStep 1289075 = 1933613) B1933613
theorem B1936259 : Blo 858357 1936259 := bstep (se 1 (by rfl) ⟨1452194, by rfl⟩ : syracuseStep 1936259 = 2904389) B2904389
theorem B1289105 : Blo 858357 1289105 := bstep (se 2 (by rfl) ⟨483414, by rfl⟩ : syracuseStep 1289105 = 966829) B966829
theorem B1289123 : Blo 858357 1289123 := bstep (se 1 (by rfl) ⟨966842, by rfl⟩ : syracuseStep 1289123 = 1933685) B1933685
theorem B1289153 : Blo 858357 1289153 := bstep (se 2 (by rfl) ⟨483432, by rfl⟩ : syracuseStep 1289153 = 966865) B966865
theorem B1289171 : Blo 858357 1289171 := bstep (se 1 (by rfl) ⟨966878, by rfl⟩ : syracuseStep 1289171 = 1933757) B1933757
theorem B9800675 : Blo 858357 9800675 := bstep (se 1 (by rfl) ⟨7350506, by rfl⟩ : syracuseStep 9800675 = 14701013) B14701013
theorem B1289201 : Blo 858357 1289201 := bstep (se 2 (by rfl) ⟨483450, by rfl⟩ : syracuseStep 1289201 = 966901) B966901
theorem B1289219 : Blo 858357 1289219 := bstep (se 1 (by rfl) ⟨966914, by rfl⟩ : syracuseStep 1289219 = 1933829) B1933829
theorem B1289249 : Blo 858357 1289249 := bstep (se 2 (by rfl) ⟨483468, by rfl⟩ : syracuseStep 1289249 = 966937) B966937
theorem B1289267 : Blo 858357 1289267 := bstep (se 1 (by rfl) ⟨966950, by rfl⟩ : syracuseStep 1289267 = 1933901) B1933901
theorem B4353101 : Blo 858357 4353101 := bstep (se 3 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 4353101 = 1632413) B1632413
theorem B1289297 : Blo 858357 1289297 := bstep (se 2 (by rfl) ⟨483486, by rfl⟩ : syracuseStep 1289297 = 966973) B966973
theorem B1289315 : Blo 858357 1289315 := bstep (se 1 (by rfl) ⟨966986, by rfl⟩ : syracuseStep 1289315 = 1933973) B1933973
theorem B1289345 : Blo 858357 1289345 := bstep (se 2 (by rfl) ⟨483504, by rfl⟩ : syracuseStep 1289345 = 967009) B967009
theorem B1289363 : Blo 858357 1289363 := bstep (se 1 (by rfl) ⟨967022, by rfl⟩ : syracuseStep 1289363 = 1934045) B1934045
theorem B994451 : Blo 858357 994451 := bstep (se 1 (by rfl) ⟨745838, by rfl⟩ : syracuseStep 994451 = 1491677) B1491677
theorem B1289393 : Blo 858357 1289393 := bstep (se 2 (by rfl) ⟨483522, by rfl⟩ : syracuseStep 1289393 = 967045) B967045
theorem B1289411 : Blo 858357 1289411 := bstep (se 1 (by rfl) ⟨967058, by rfl⟩ : syracuseStep 1289411 = 1934117) B1934117
theorem B2174161 : Blo 858357 2174161 := bstep (se 2 (by rfl) ⟨815310, by rfl⟩ : syracuseStep 2174161 = 1630621) B1630621
theorem B1289441 : Blo 858357 1289441 := bstep (se 2 (by rfl) ⟨483540, by rfl⟩ : syracuseStep 1289441 = 967081) B967081
theorem B4713713 : Blo 858357 4713713 := bstep (se 2 (by rfl) ⟨1767642, by rfl⟩ : syracuseStep 4713713 = 3535285) B3535285
theorem B1223923 : Blo 858357 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B1289459 : Blo 858357 1289459 := bstep (se 1 (by rfl) ⟨967094, by rfl⟩ : syracuseStep 1289459 = 1934189) B1934189
theorem B2755853 : Blo 858357 2755853 := bstep (se 3 (by rfl) ⟨516722, by rfl⟩ : syracuseStep 2755853 = 1033445) B1033445
theorem B2903309 : Blo 858357 2903309 := bstep (se 3 (by rfl) ⟨544370, by rfl⟩ : syracuseStep 2903309 = 1088741) B1088741
theorem B1289489 : Blo 858357 1289489 := bstep (se 2 (by rfl) ⟨483558, by rfl⟩ : syracuseStep 1289489 = 967117) B967117
theorem B1289507 : Blo 858357 1289507 := bstep (se 1 (by rfl) ⟨967130, by rfl⟩ : syracuseStep 1289507 = 1934261) B1934261
theorem B1289537 : Blo 858357 1289537 := bstep (se 2 (by rfl) ⟨483576, by rfl⟩ : syracuseStep 1289537 = 967153) B967153
theorem B2903363 : Blo 858357 2903363 := bstep (se 1 (by rfl) ⟨2177522, by rfl⟩ : syracuseStep 2903363 = 4355045) B4355045
theorem B1289555 : Blo 858357 1289555 := bstep (se 1 (by rfl) ⟨967166, by rfl⟩ : syracuseStep 1289555 = 1934333) B1934333
theorem B1289585 : Blo 858357 1289585 := bstep (se 2 (by rfl) ⟨483594, by rfl⟩ : syracuseStep 1289585 = 967189) B967189
theorem B1961329 : Blo 858357 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B1289603 : Blo 858357 1289603 := bstep (se 1 (by rfl) ⟨967202, by rfl⟩ : syracuseStep 1289603 = 1934405) B1934405
theorem B3263885 : Blo 858357 3263885 := bstep (se 3 (by rfl) ⟨611978, by rfl⟩ : syracuseStep 3263885 = 1223957) B1223957
theorem B1289633 : Blo 858357 1289633 := bstep (se 2 (by rfl) ⟨483612, by rfl⟩ : syracuseStep 1289633 = 967225) B967225
theorem B1289651 : Blo 858357 1289651 := bstep (se 1 (by rfl) ⟨967238, by rfl⟩ : syracuseStep 1289651 = 1934477) B1934477
theorem B1289681 : Blo 858357 1289681 := bstep (se 2 (by rfl) ⟨483630, by rfl⟩ : syracuseStep 1289681 = 967261) B967261
theorem B2174435 : Blo 858357 2174435 := bstep (se 1 (by rfl) ⟨1630826, by rfl⟩ : syracuseStep 2174435 = 3261653) B3261653
theorem B1289699 : Blo 858357 1289699 := bstep (se 1 (by rfl) ⟨967274, by rfl⟩ : syracuseStep 1289699 = 1934549) B1934549
theorem B1289729 : Blo 858357 1289729 := bstep (se 2 (by rfl) ⟨483648, by rfl⟩ : syracuseStep 1289729 = 967297) B967297
theorem B3919373 : Blo 858357 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B3673613 : Blo 858357 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B1289747 : Blo 858357 1289747 := bstep (se 1 (by rfl) ⟨967310, by rfl⟩ : syracuseStep 1289747 = 1934621) B1934621
theorem B1289777 : Blo 858357 1289777 := bstep (se 2 (by rfl) ⟨483666, by rfl⟩ : syracuseStep 1289777 = 967333) B967333
theorem B1289795 : Blo 858357 1289795 := bstep (se 1 (by rfl) ⟨967346, by rfl⟩ : syracuseStep 1289795 = 1934693) B1934693
theorem B2903633 : Blo 858357 2903633 := bstep (se 2 (by rfl) ⟨1088862, by rfl⟩ : syracuseStep 2903633 = 2177725) B2177725
theorem B1289825 : Blo 858357 1289825 := bstep (se 2 (by rfl) ⟨483684, by rfl⟩ : syracuseStep 1289825 = 967369) B967369
theorem B1289843 : Blo 858357 1289843 := bstep (se 1 (by rfl) ⟨967382, by rfl⟩ : syracuseStep 1289843 = 1934765) B1934765
theorem B1289873 : Blo 858357 1289873 := bstep (se 2 (by rfl) ⟨483702, by rfl⟩ : syracuseStep 1289873 = 967405) B967405
theorem B2174627 : Blo 858357 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B1289891 : Blo 858357 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B1289921 : Blo 858357 1289921 := bstep (se 2 (by rfl) ⟨483720, by rfl⟩ : syracuseStep 1289921 = 967441) B967441
theorem B1224401 : Blo 858357 1224401 := bstep (se 2 (by rfl) ⟨459150, by rfl⟩ : syracuseStep 1224401 = 918301) B918301
theorem B1289939 : Blo 858357 1289939 := bstep (se 1 (by rfl) ⟨967454, by rfl⟩ : syracuseStep 1289939 = 1934909) B1934909
theorem B1289969 : Blo 858357 1289969 := bstep (se 2 (by rfl) ⟨483738, by rfl⟩ : syracuseStep 1289969 = 967477) B967477
theorem B1289987 : Blo 858357 1289987 := bstep (se 1 (by rfl) ⟨967490, by rfl⟩ : syracuseStep 1289987 = 1934981) B1934981
theorem B1290017 : Blo 858357 1290017 := bstep (se 2 (by rfl) ⟨483756, by rfl⟩ : syracuseStep 1290017 = 967513) B967513
theorem B4345649 : Blo 858357 4345649 := bstep (se 2 (by rfl) ⟨1629618, by rfl⟩ : syracuseStep 4345649 = 3259237) B3259237
theorem B2477873 : Blo 858357 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B1290035 : Blo 858357 1290035 := bstep (se 1 (by rfl) ⟨967526, by rfl⟩ : syracuseStep 1290035 = 1935053) B1935053
theorem B1224515 : Blo 858357 1224515 := bstep (se 1 (by rfl) ⟨918386, by rfl⟩ : syracuseStep 1224515 = 1836773) B1836773
theorem B1290065 : Blo 858357 1290065 := bstep (se 2 (by rfl) ⟨483774, by rfl⟩ : syracuseStep 1290065 = 967549) B967549
theorem B6279011 : Blo 858357 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B1290083 : Blo 858357 1290083 := bstep (se 1 (by rfl) ⟨967562, by rfl⟩ : syracuseStep 1290083 = 1935125) B1935125
theorem B1306481 : Blo 858357 1306481 := bstep (se 2 (by rfl) ⟨489930, by rfl⟩ : syracuseStep 1306481 = 979861) B979861
theorem B1290113 : Blo 858357 1290113 := bstep (se 2 (by rfl) ⟨483792, by rfl⟩ : syracuseStep 1290113 = 967585) B967585
theorem B1224595 : Blo 858357 1224595 := bstep (se 1 (by rfl) ⟨918446, by rfl⟩ : syracuseStep 1224595 = 1836893) B1836893
theorem B1290131 : Blo 858357 1290131 := bstep (se 1 (by rfl) ⟨967598, by rfl⟩ : syracuseStep 1290131 = 1935197) B1935197
theorem B1290161 : Blo 858357 1290161 := bstep (se 2 (by rfl) ⟨483810, by rfl⟩ : syracuseStep 1290161 = 967621) B967621
theorem B1290179 : Blo 858357 1290179 := bstep (se 1 (by rfl) ⟨967634, by rfl⟩ : syracuseStep 1290179 = 1935269) B1935269
theorem B1306579 : Blo 858357 1306579 := bstep (se 1 (by rfl) ⟨979934, by rfl⟩ : syracuseStep 1306579 = 1959869) B1959869
theorem B1290209 : Blo 858357 1290209 := bstep (se 2 (by rfl) ⟨483828, by rfl⟩ : syracuseStep 1290209 = 967657) B967657
theorem B1470449 : Blo 858357 1470449 := bstep (se 2 (by rfl) ⟨551418, by rfl⟩ : syracuseStep 1470449 = 1102837) B1102837
theorem B1290227 : Blo 858357 1290227 := bstep (se 1 (by rfl) ⟨967670, by rfl⟩ : syracuseStep 1290227 = 1935341) B1935341
theorem B2445329 : Blo 858357 2445329 := bstep (se 2 (by rfl) ⟨916998, by rfl⟩ : syracuseStep 2445329 = 1833997) B1833997
theorem B1290257 : Blo 858357 1290257 := bstep (se 2 (by rfl) ⟨483846, by rfl⟩ : syracuseStep 1290257 = 967693) B967693
theorem B1290275 : Blo 858357 1290275 := bstep (se 1 (by rfl) ⟨967706, by rfl⟩ : syracuseStep 1290275 = 1935413) B1935413
theorem B1290305 : Blo 858357 1290305 := bstep (se 2 (by rfl) ⟨483864, by rfl⟩ : syracuseStep 1290305 = 967729) B967729
theorem B1290323 : Blo 858357 1290323 := bstep (se 1 (by rfl) ⟨967742, by rfl⟩ : syracuseStep 1290323 = 1935485) B1935485
theorem B3584099 : Blo 858357 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B2904173 : Blo 858357 2904173 := bstep (se 3 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 2904173 = 1089065) B1089065
theorem B1290353 : Blo 858357 1290353 := bstep (se 2 (by rfl) ⟨483882, by rfl⟩ : syracuseStep 1290353 = 967765) B967765
theorem B8269937 : Blo 858357 8269937 := bstep (se 2 (by rfl) ⟨3101226, by rfl⟩ : syracuseStep 8269937 = 6202453) B6202453
theorem B1290371 : Blo 858357 1290371 := bstep (se 1 (by rfl) ⟨967778, by rfl⟩ : syracuseStep 1290371 = 1935557) B1935557
theorem B1290401 : Blo 858357 1290401 := bstep (se 2 (by rfl) ⟨483900, by rfl⟩ : syracuseStep 1290401 = 967801) B967801
theorem B2904227 : Blo 858357 2904227 := bstep (se 1 (by rfl) ⟨2178170, by rfl⟩ : syracuseStep 2904227 = 4356341) B4356341
theorem B1290419 : Blo 858357 1290419 := bstep (se 1 (by rfl) ⟨967814, by rfl⟩ : syracuseStep 1290419 = 1935629) B1935629
theorem B1740995 : Blo 858357 1740995 := bstep (se 1 (by rfl) ⟨1305746, by rfl⟩ : syracuseStep 1740995 = 2611493) B2611493
theorem B1290449 : Blo 858357 1290449 := bstep (se 2 (by rfl) ⟨483918, by rfl⟩ : syracuseStep 1290449 = 967837) B967837
theorem B1290467 : Blo 858357 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B1290497 : Blo 858357 1290497 := bstep (se 2 (by rfl) ⟨483936, by rfl⟩ : syracuseStep 1290497 = 967873) B967873
theorem B1290515 : Blo 858357 1290515 := bstep (se 1 (by rfl) ⟨967886, by rfl⟩ : syracuseStep 1290515 = 1935773) B1935773
theorem B18583829 : Blo 858357 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B1290545 : Blo 858357 1290545 := bstep (se 2 (by rfl) ⟨483954, by rfl⟩ : syracuseStep 1290545 = 967909) B967909
theorem B1290563 : Blo 858357 1290563 := bstep (se 1 (by rfl) ⟨967922, by rfl⟩ : syracuseStep 1290563 = 1935845) B1935845
theorem B1290593 : Blo 858357 1290593 := bstep (se 2 (by rfl) ⟨483972, by rfl⟩ : syracuseStep 1290593 = 967945) B967945
theorem B7336291 : Blo 858357 7336291 := bstep (se 1 (by rfl) ⟨5502218, by rfl⟩ : syracuseStep 7336291 = 11004437) B11004437
theorem B5501297 : Blo 858357 5501297 := bstep (se 2 (by rfl) ⟨2062986, by rfl⟩ : syracuseStep 5501297 = 4125973) B4125973
theorem B1290611 : Blo 858357 1290611 := bstep (se 1 (by rfl) ⟨967958, by rfl⟩ : syracuseStep 1290611 = 1935917) B1935917
theorem B1290641 : Blo 858357 1290641 := bstep (se 2 (by rfl) ⟨483990, by rfl⟩ : syracuseStep 1290641 = 967981) B967981
theorem B1290659 : Blo 858357 1290659 := bstep (se 1 (by rfl) ⟨967994, by rfl⟩ : syracuseStep 1290659 = 1935989) B1935989
theorem B1290689 : Blo 858357 1290689 := bstep (se 2 (by rfl) ⟨484008, by rfl⟩ : syracuseStep 1290689 = 968017) B968017
theorem B1225153 : Blo 858357 1225153 := bstep (se 2 (by rfl) ⟨459432, by rfl⟩ : syracuseStep 1225153 = 918865) B918865
theorem B1290707 : Blo 858357 1290707 := bstep (se 1 (by rfl) ⟨968030, by rfl⟩ : syracuseStep 1290707 = 1936061) B1936061
theorem B1290737 : Blo 858357 1290737 := bstep (se 2 (by rfl) ⟨484026, by rfl⟩ : syracuseStep 1290737 = 968053) B968053
theorem B1290755 : Blo 858357 1290755 := bstep (se 1 (by rfl) ⟨968066, by rfl⟩ : syracuseStep 1290755 = 1936133) B1936133
theorem B1290785 : Blo 858357 1290785 := bstep (se 2 (by rfl) ⟨484044, by rfl⟩ : syracuseStep 1290785 = 968089) B968089
theorem B1290803 : Blo 858357 1290803 := bstep (se 1 (by rfl) ⟨968102, by rfl⟩ : syracuseStep 1290803 = 1936205) B1936205
theorem B2175569 : Blo 858357 2175569 := bstep (se 2 (by rfl) ⟨815838, by rfl⟩ : syracuseStep 2175569 = 1631677) B1631677
theorem B1290833 : Blo 858357 1290833 := bstep (se 2 (by rfl) ⟨484062, by rfl⟩ : syracuseStep 1290833 = 968125) B968125
theorem B2175619 : Blo 858357 2175619 := bstep (se 1 (by rfl) ⟨1631714, by rfl⟩ : syracuseStep 2175619 = 3263429) B3263429
theorem B2446001 : Blo 858357 2446001 := bstep (se 2 (by rfl) ⟨917250, by rfl⟩ : syracuseStep 2446001 = 1834501) B1834501
theorem B2175761 : Blo 858357 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B5223203 : Blo 858357 5223203 := bstep (se 1 (by rfl) ⟨3917402, by rfl⟩ : syracuseStep 5223203 = 7834805) B7834805
theorem B1241905 : Blo 858357 1241905 := bstep (se 2 (by rfl) ⟨465714, by rfl⟩ : syracuseStep 1241905 = 931429) B931429
theorem B979907 : Blo 858357 979907 := bstep (se 1 (by rfl) ⟨734930, by rfl⟩ : syracuseStep 979907 = 1469861) B1469861
theorem B4641805 : Blo 858357 4641805 := bstep (se 3 (by rfl) ⟨870338, by rfl⟩ : syracuseStep 4641805 = 1740677) B1740677
theorem B2790413 : Blo 858357 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B1307747 : Blo 858357 1307747 := bstep (se 1 (by rfl) ⟨980810, by rfl⟩ : syracuseStep 1307747 = 1961621) B1961621
theorem B1742033 : Blo 858357 1742033 := bstep (se 2 (by rfl) ⟨653262, by rfl⟩ : syracuseStep 1742033 = 1306525) B1306525
theorem B1086691 : Blo 858357 1086691 := bstep (se 1 (by rfl) ⟨815018, by rfl⟩ : syracuseStep 1086691 = 1630037) B1630037
theorem B4347107 : Blo 858357 4347107 := bstep (se 1 (by rfl) ⟨3260330, by rfl⟩ : syracuseStep 4347107 = 6520661) B6520661
theorem B1086787 : Blo 858357 1086787 := bstep (se 1 (by rfl) ⟨815090, by rfl⟩ : syracuseStep 1086787 = 1630181) B1630181
theorem B10458467 : Blo 858357 10458467 := bstep (se 1 (by rfl) ⟨7843850, by rfl⟩ : syracuseStep 10458467 = 15687701) B15687701
theorem B1987939 : Blo 858357 1987939 := bstep (se 1 (by rfl) ⟨1490954, by rfl⟩ : syracuseStep 1987939 = 2981909) B2981909
theorem B2897261 : Blo 858357 2897261 := bstep (se 3 (by rfl) ⟨543236, by rfl⟩ : syracuseStep 2897261 = 1086473) B1086473
theorem B2897315 : Blo 858357 2897315 := bstep (se 1 (by rfl) ⟨2172986, by rfl⟩ : syracuseStep 2897315 = 4345973) B4345973
theorem B1045939 : Blo 858357 1045939 := bstep (se 1 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 1045939 = 1568909) B1568909
theorem B11007413 : Blo 858357 11007413 := bstep (se 5 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 11007413 = 1031945) B1031945
theorem B2446787 : Blo 858357 2446787 := bstep (se 1 (by rfl) ⟨1835090, by rfl⟩ : syracuseStep 2446787 = 3670181) B3670181
theorem B6190577 : Blo 858357 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B6534755 : Blo 858357 6534755 := bstep (se 1 (by rfl) ⟨4901066, by rfl⟩ : syracuseStep 6534755 = 9802133) B9802133
theorem B2897585 : Blo 858357 2897585 := bstep (se 2 (by rfl) ⟨1086594, by rfl⟩ : syracuseStep 2897585 = 2173189) B2173189
theorem B2176753 : Blo 858357 2176753 := bstep (se 2 (by rfl) ⟨816282, by rfl⟩ : syracuseStep 2176753 = 1632565) B1632565
theorem B2447117 : Blo 858357 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B1087283 : Blo 858357 1087283 := bstep (se 1 (by rfl) ⟨815462, by rfl⟩ : syracuseStep 1087283 = 1630925) B1630925
theorem B2447185 : Blo 858357 2447185 := bstep (se 2 (by rfl) ⟨917694, by rfl⟩ : syracuseStep 2447185 = 1835389) B1835389
theorem B10590065 : Blo 858357 10590065 := bstep (se 2 (by rfl) ⟨3971274, by rfl⟩ : syracuseStep 10590065 = 7942549) B7942549
theorem B7255921 : Blo 858357 7255921 := bstep (se 2 (by rfl) ⟨2720970, by rfl⟩ : syracuseStep 7255921 = 5441941) B5441941
theorem B1570691 : Blo 858357 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B4134797 : Blo 858357 4134797 := bstep (se 3 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 4134797 = 1550549) B1550549
theorem B2750381 : Blo 858357 2750381 := bstep (se 3 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 2750381 = 1031393) B1031393
theorem B4356017 : Blo 858357 4356017 := bstep (se 2 (by rfl) ⟨1633506, by rfl⟩ : syracuseStep 4356017 = 3267013) B3267013
theorem B2177027 : Blo 858357 2177027 := bstep (se 1 (by rfl) ⟨1632770, by rfl⟩ : syracuseStep 2177027 = 3265541) B3265541
theorem B4347917 : Blo 858357 4347917 := bstep (se 3 (by rfl) ⟨815234, by rfl⟩ : syracuseStep 4347917 = 1630469) B1630469
theorem B981011 : Blo 858357 981011 := bstep (se 1 (by rfl) ⟨735758, by rfl⟩ : syracuseStep 981011 = 1471517) B1471517
theorem B1931345 : Blo 858357 1931345 := bstep (se 2 (by rfl) ⟨724254, by rfl⟩ : syracuseStep 1931345 = 1448509) B1448509
theorem B1931363 : Blo 858357 1931363 := bstep (se 1 (by rfl) ⟨1448522, by rfl⟩ : syracuseStep 1931363 = 2897045) B2897045
theorem B2447459 : Blo 858357 2447459 := bstep (se 1 (by rfl) ⟨1835594, by rfl⟩ : syracuseStep 2447459 = 3671189) B3671189
theorem B2177219 : Blo 858357 2177219 := bstep (se 1 (by rfl) ⟨1632914, by rfl⟩ : syracuseStep 2177219 = 3265829) B3265829
theorem B2898125 : Blo 858357 2898125 := bstep (se 3 (by rfl) ⟨543398, by rfl⟩ : syracuseStep 2898125 = 1086797) B1086797
theorem B3266801 : Blo 858357 3266801 := bstep (se 2 (by rfl) ⟨1225050, by rfl⟩ : syracuseStep 3266801 = 2450101) B2450101
theorem B858371 : Blo 858357 858371 := bstep (se 1 (by rfl) ⟨643778, by rfl⟩ : syracuseStep 858371 = 1287557) B1287557
theorem B2898179 : Blo 858357 2898179 := bstep (se 1 (by rfl) ⟨2173634, by rfl⟩ : syracuseStep 2898179 = 4347269) B4347269
theorem B1767683 : Blo 858357 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B858387 : Blo 858357 858387 := bstep (se 1 (by rfl) ⟨643790, by rfl⟩ : syracuseStep 858387 = 1287581) B1287581
theorem B858403 : Blo 858357 858403 := bstep (se 1 (by rfl) ⟨643802, by rfl⟩ : syracuseStep 858403 = 1287605) B1287605
theorem B858419 : Blo 858357 858419 := bstep (se 1 (by rfl) ⟨643814, by rfl⟩ : syracuseStep 858419 = 1287629) B1287629
theorem B858435 : Blo 858357 858435 := bstep (se 1 (by rfl) ⟨643826, by rfl⟩ : syracuseStep 858435 = 1287653) B1287653
theorem B858451 : Blo 858357 858451 := bstep (se 1 (by rfl) ⟨643838, by rfl⟩ : syracuseStep 858451 = 1287677) B1287677
theorem B858467 : Blo 858357 858467 := bstep (se 1 (by rfl) ⟨643850, by rfl⟩ : syracuseStep 858467 = 1287701) B1287701
theorem B7059811 : Blo 858357 7059811 := bstep (se 1 (by rfl) ⟨5294858, by rfl⟩ : syracuseStep 7059811 = 10589717) B10589717
theorem B1931633 : Blo 858357 1931633 := bstep (se 2 (by rfl) ⟨724362, by rfl⟩ : syracuseStep 1931633 = 1448725) B1448725
theorem B1571185 : Blo 858357 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B858483 : Blo 858357 858483 := bstep (se 1 (by rfl) ⟨643862, by rfl⟩ : syracuseStep 858483 = 1287725) B1287725
theorem B858499 : Blo 858357 858499 := bstep (se 1 (by rfl) ⟨643874, by rfl⟩ : syracuseStep 858499 = 1287749) B1287749
theorem B1931651 : Blo 858357 1931651 := bstep (se 1 (by rfl) ⟨1448738, by rfl⟩ : syracuseStep 1931651 = 2897477) B2897477
theorem B8821133 : Blo 858357 8821133 := bstep (se 3 (by rfl) ⟨1653962, by rfl⟩ : syracuseStep 8821133 = 3307925) B3307925
theorem B858515 : Blo 858357 858515 := bstep (se 1 (by rfl) ⟨643886, by rfl⟩ : syracuseStep 858515 = 1287773) B1287773
theorem B858531 : Blo 858357 858531 := bstep (se 1 (by rfl) ⟨643898, by rfl⟩ : syracuseStep 858531 = 1287797) B1287797
theorem B858547 : Blo 858357 858547 := bstep (se 1 (by rfl) ⟨643910, by rfl⟩ : syracuseStep 858547 = 1287821) B1287821
theorem B858563 : Blo 858357 858563 := bstep (se 1 (by rfl) ⟨643922, by rfl⟩ : syracuseStep 858563 = 1287845) B1287845
theorem B858579 : Blo 858357 858579 := bstep (se 1 (by rfl) ⟨643934, by rfl⟩ : syracuseStep 858579 = 1287869) B1287869
theorem B858595 : Blo 858357 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B4127203 : Blo 858357 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B858611 : Blo 858357 858611 := bstep (se 1 (by rfl) ⟨643958, by rfl⟩ : syracuseStep 858611 = 1287917) B1287917
theorem B1087987 : Blo 858357 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B858627 : Blo 858357 858627 := bstep (se 1 (by rfl) ⟨643970, by rfl⟩ : syracuseStep 858627 = 1287941) B1287941
theorem B2898449 : Blo 858357 2898449 := bstep (se 2 (by rfl) ⟨1086918, by rfl⟩ : syracuseStep 2898449 = 2173837) B2173837
theorem B858643 : Blo 858357 858643 := bstep (se 1 (by rfl) ⟨643982, by rfl⟩ : syracuseStep 858643 = 1287965) B1287965
theorem B858659 : Blo 858357 858659 := bstep (se 1 (by rfl) ⟨643994, by rfl⟩ : syracuseStep 858659 = 1287989) B1287989
theorem B858675 : Blo 858357 858675 := bstep (se 1 (by rfl) ⟨644006, by rfl⟩ : syracuseStep 858675 = 1288013) B1288013
theorem B1161793 : Blo 858357 1161793 := bstep (se 2 (by rfl) ⟨435672, by rfl⟩ : syracuseStep 1161793 = 871345) B871345
theorem B858691 : Blo 858357 858691 := bstep (se 1 (by rfl) ⟨644018, by rfl⟩ : syracuseStep 858691 = 1288037) B1288037
theorem B858707 : Blo 858357 858707 := bstep (se 1 (by rfl) ⟨644030, by rfl⟩ : syracuseStep 858707 = 1288061) B1288061
theorem B1088083 : Blo 858357 1088083 := bstep (se 1 (by rfl) ⟨816062, by rfl⟩ : syracuseStep 1088083 = 1632125) B1632125
theorem B858723 : Blo 858357 858723 := bstep (se 1 (by rfl) ⟨644042, by rfl⟩ : syracuseStep 858723 = 1288085) B1288085
theorem B1448563 : Blo 858357 1448563 := bstep (se 1 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 1448563 = 2172845) B2172845
theorem B858739 : Blo 858357 858739 := bstep (se 1 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 858739 = 1288109) B1288109
theorem B858755 : Blo 858357 858755 := bstep (se 1 (by rfl) ⟨644066, by rfl⟩ : syracuseStep 858755 = 1288133) B1288133
theorem B1931921 : Blo 858357 1931921 := bstep (se 2 (by rfl) ⟨724470, by rfl⟩ : syracuseStep 1931921 = 1448941) B1448941
theorem B858771 : Blo 858357 858771 := bstep (se 1 (by rfl) ⟨644078, by rfl⟩ : syracuseStep 858771 = 1288157) B1288157
theorem B1931939 : Blo 858357 1931939 := bstep (se 1 (by rfl) ⟨1448954, by rfl⟩ : syracuseStep 1931939 = 2897909) B2897909
theorem B858787 : Blo 858357 858787 := bstep (se 1 (by rfl) ⟨644090, by rfl⟩ : syracuseStep 858787 = 1288181) B1288181
theorem B858803 : Blo 858357 858803 := bstep (se 1 (by rfl) ⟨644102, by rfl⟩ : syracuseStep 858803 = 1288205) B1288205
theorem B858819 : Blo 858357 858819 := bstep (se 1 (by rfl) ⟨644114, by rfl⟩ : syracuseStep 858819 = 1288229) B1288229
theorem B858835 : Blo 858357 858835 := bstep (se 1 (by rfl) ⟨644126, by rfl⟩ : syracuseStep 858835 = 1288253) B1288253
theorem B858851 : Blo 858357 858851 := bstep (se 1 (by rfl) ⟨644138, by rfl⟩ : syracuseStep 858851 = 1288277) B1288277
theorem B858867 : Blo 858357 858867 := bstep (se 1 (by rfl) ⟨644150, by rfl⟩ : syracuseStep 858867 = 1288301) B1288301
theorem B1448705 : Blo 858357 1448705 := bstep (se 2 (by rfl) ⟨543264, by rfl⟩ : syracuseStep 1448705 = 1086529) B1086529
theorem B858883 : Blo 858357 858883 := bstep (se 1 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 858883 = 1288325) B1288325
theorem B858899 : Blo 858357 858899 := bstep (se 1 (by rfl) ⟨644174, by rfl⟩ : syracuseStep 858899 = 1288349) B1288349
theorem B858915 : Blo 858357 858915 := bstep (se 1 (by rfl) ⟨644186, by rfl⟩ : syracuseStep 858915 = 1288373) B1288373
theorem B858931 : Blo 858357 858931 := bstep (se 1 (by rfl) ⟨644198, by rfl⟩ : syracuseStep 858931 = 1288397) B1288397
theorem B15276853 : Blo 858357 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B858947 : Blo 858357 858947 := bstep (se 1 (by rfl) ⟨644210, by rfl⟩ : syracuseStep 858947 = 1288421) B1288421
theorem B858963 : Blo 858357 858963 := bstep (se 1 (by rfl) ⟨644222, by rfl⟩ : syracuseStep 858963 = 1288445) B1288445
theorem B858979 : Blo 858357 858979 := bstep (se 1 (by rfl) ⟨644234, by rfl⟩ : syracuseStep 858979 = 1288469) B1288469
theorem B6970211 : Blo 858357 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B858995 : Blo 858357 858995 := bstep (se 1 (by rfl) ⟨644246, by rfl⟩ : syracuseStep 858995 = 1288493) B1288493
theorem B1448833 : Blo 858357 1448833 := bstep (se 2 (by rfl) ⟨543312, by rfl⟩ : syracuseStep 1448833 = 1086625) B1086625
theorem B859011 : Blo 858357 859011 := bstep (se 1 (by rfl) ⟨644258, by rfl⟩ : syracuseStep 859011 = 1288517) B1288517
theorem B5651333 : Blo 858357 5651333 := bstep (se 4 (by rfl) ⟨529812, by rfl⟩ : syracuseStep 5651333 = 1059625) B1059625
theorem B1743761 : Blo 858357 1743761 := bstep (se 2 (by rfl) ⟨653910, by rfl⟩ : syracuseStep 1743761 = 1307821) B1307821
theorem B859027 : Blo 858357 859027 := bstep (se 1 (by rfl) ⟨644270, by rfl⟩ : syracuseStep 859027 = 1288541) B1288541
theorem B1448867 : Blo 858357 1448867 := bstep (se 1 (by rfl) ⟨1086650, by rfl⟩ : syracuseStep 1448867 = 2173301) B2173301
theorem B859043 : Blo 858357 859043 := bstep (se 1 (by rfl) ⟨644282, by rfl⟩ : syracuseStep 859043 = 1288565) B1288565
theorem B2448301 : Blo 858357 2448301 := bstep (se 3 (by rfl) ⟨459056, by rfl⟩ : syracuseStep 2448301 = 918113) B918113
theorem B1932209 : Blo 858357 1932209 := bstep (se 2 (by rfl) ⟨724578, by rfl⟩ : syracuseStep 1932209 = 1449157) B1449157
theorem B859059 : Blo 858357 859059 := bstep (se 1 (by rfl) ⟨644294, by rfl⟩ : syracuseStep 859059 = 1288589) B1288589
theorem B1932227 : Blo 858357 1932227 := bstep (se 1 (by rfl) ⟨1449170, by rfl⟩ : syracuseStep 1932227 = 2898341) B2898341
theorem B859075 : Blo 858357 859075 := bstep (se 1 (by rfl) ⟨644306, by rfl⟩ : syracuseStep 859075 = 1288613) B1288613
theorem B859091 : Blo 858357 859091 := bstep (se 1 (by rfl) ⟨644318, by rfl⟩ : syracuseStep 859091 = 1288637) B1288637
theorem B859107 : Blo 858357 859107 := bstep (se 1 (by rfl) ⟨644330, by rfl⟩ : syracuseStep 859107 = 1288661) B1288661
theorem B4889585 : Blo 858357 4889585 := bstep (se 2 (by rfl) ⟨1833594, by rfl⟩ : syracuseStep 4889585 = 3667189) B3667189
theorem B1743857 : Blo 858357 1743857 := bstep (se 2 (by rfl) ⟨653946, by rfl⟩ : syracuseStep 1743857 = 1307893) B1307893
theorem B859123 : Blo 858357 859123 := bstep (se 1 (by rfl) ⟨644342, by rfl⟩ : syracuseStep 859123 = 1288685) B1288685
theorem B859139 : Blo 858357 859139 := bstep (se 1 (by rfl) ⟨644354, by rfl⟩ : syracuseStep 859139 = 1288709) B1288709
theorem B859155 : Blo 858357 859155 := bstep (se 1 (by rfl) ⟨644366, by rfl⟩ : syracuseStep 859155 = 1288733) B1288733
theorem B1448995 : Blo 858357 1448995 := bstep (se 1 (by rfl) ⟨1086746, by rfl⟩ : syracuseStep 1448995 = 2173493) B2173493
theorem B859171 : Blo 858357 859171 := bstep (se 1 (by rfl) ⟨644378, by rfl⟩ : syracuseStep 859171 = 1288757) B1288757
theorem B2898989 : Blo 858357 2898989 := bstep (se 3 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 2898989 = 1087121) B1087121
theorem B2481197 : Blo 858357 2481197 := bstep (se 3 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 2481197 = 930449) B930449
theorem B859187 : Blo 858357 859187 := bstep (se 1 (by rfl) ⟨644390, by rfl⟩ : syracuseStep 859187 = 1288781) B1288781
theorem B859203 : Blo 858357 859203 := bstep (se 1 (by rfl) ⟨644402, by rfl⟩ : syracuseStep 859203 = 1288805) B1288805
theorem B1162307 : Blo 858357 1162307 := bstep (se 1 (by rfl) ⟨871730, by rfl⟩ : syracuseStep 1162307 = 1743461) B1743461
theorem B1088579 : Blo 858357 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B2448461 : Blo 858357 2448461 := bstep (se 3 (by rfl) ⟨459086, by rfl⟩ : syracuseStep 2448461 = 918173) B918173
theorem B859219 : Blo 858357 859219 := bstep (se 1 (by rfl) ⟨644414, by rfl⟩ : syracuseStep 859219 = 1288829) B1288829
theorem B965731 : Blo 858357 965731 := bstep (se 1 (by rfl) ⟨724298, by rfl⟩ : syracuseStep 965731 = 1448597) B1448597
theorem B2899043 : Blo 858357 2899043 := bstep (se 1 (by rfl) ⟨2174282, by rfl⟩ : syracuseStep 2899043 = 4348565) B4348565
theorem B859235 : Blo 858357 859235 := bstep (se 1 (by rfl) ⟨644426, by rfl⟩ : syracuseStep 859235 = 1288853) B1288853
theorem B2178161 : Blo 858357 2178161 := bstep (se 2 (by rfl) ⟨816810, by rfl⟩ : syracuseStep 2178161 = 1633621) B1633621
theorem B859251 : Blo 858357 859251 := bstep (se 1 (by rfl) ⟨644438, by rfl⟩ : syracuseStep 859251 = 1288877) B1288877
theorem B859267 : Blo 858357 859267 := bstep (se 1 (by rfl) ⟨644450, by rfl⟩ : syracuseStep 859267 = 1288901) B1288901
theorem B859283 : Blo 858357 859283 := bstep (se 1 (by rfl) ⟨644462, by rfl⟩ : syracuseStep 859283 = 1288925) B1288925
theorem B859299 : Blo 858357 859299 := bstep (se 1 (by rfl) ⟨644474, by rfl⟩ : syracuseStep 859299 = 1288949) B1288949
theorem B2178211 : Blo 858357 2178211 := bstep (se 1 (by rfl) ⟨1633658, by rfl⟩ : syracuseStep 2178211 = 3267317) B3267317
theorem B1449137 : Blo 858357 1449137 := bstep (se 2 (by rfl) ⟨543426, by rfl⟩ : syracuseStep 1449137 = 1086853) B1086853
theorem B859315 : Blo 858357 859315 := bstep (se 1 (by rfl) ⟨644486, by rfl⟩ : syracuseStep 859315 = 1288973) B1288973
theorem B1375427 : Blo 858357 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B859331 : Blo 858357 859331 := bstep (se 1 (by rfl) ⟨644498, by rfl⟩ : syracuseStep 859331 = 1288997) B1288997
theorem B1932497 : Blo 858357 1932497 := bstep (se 2 (by rfl) ⟨724686, by rfl⟩ : syracuseStep 1932497 = 1449373) B1449373
theorem B859347 : Blo 858357 859347 := bstep (se 1 (by rfl) ⟨644510, by rfl⟩ : syracuseStep 859347 = 1289021) B1289021
theorem B1932515 : Blo 858357 1932515 := bstep (se 1 (by rfl) ⟨1449386, by rfl⟩ : syracuseStep 1932515 = 2898773) B2898773
theorem B859363 : Blo 858357 859363 := bstep (se 1 (by rfl) ⟨644522, by rfl⟩ : syracuseStep 859363 = 1289045) B1289045
theorem B2751725 : Blo 858357 2751725 := bstep (se 3 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 2751725 = 1031897) B1031897
theorem B4955377 : Blo 858357 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B965875 : Blo 858357 965875 := bstep (se 1 (by rfl) ⟨724406, by rfl⟩ : syracuseStep 965875 = 1448813) B1448813
theorem B859379 : Blo 858357 859379 := bstep (se 1 (by rfl) ⟨644534, by rfl⟩ : syracuseStep 859379 = 1289069) B1289069
theorem B859395 : Blo 858357 859395 := bstep (se 1 (by rfl) ⟨644546, by rfl⟩ : syracuseStep 859395 = 1289093) B1289093
theorem B2448643 : Blo 858357 2448643 := bstep (se 1 (by rfl) ⟨1836482, by rfl⟩ : syracuseStep 2448643 = 3672965) B3672965
theorem B5504269 : Blo 858357 5504269 := bstep (se 3 (by rfl) ⟨1032050, by rfl⟩ : syracuseStep 5504269 = 2064101) B2064101
theorem B859411 : Blo 858357 859411 := bstep (se 1 (by rfl) ⟨644558, by rfl⟩ : syracuseStep 859411 = 1289117) B1289117
theorem B859427 : Blo 858357 859427 := bstep (se 1 (by rfl) ⟨644570, by rfl⟩ : syracuseStep 859427 = 1289141) B1289141
theorem B1449265 : Blo 858357 1449265 := bstep (se 2 (by rfl) ⟨543474, by rfl⟩ : syracuseStep 1449265 = 1086949) B1086949
theorem B859443 : Blo 858357 859443 := bstep (se 1 (by rfl) ⟨644582, by rfl⟩ : syracuseStep 859443 = 1289165) B1289165
theorem B859459 : Blo 858357 859459 := bstep (se 1 (by rfl) ⟨644594, by rfl⟩ : syracuseStep 859459 = 1289189) B1289189
theorem B1449299 : Blo 858357 1449299 := bstep (se 1 (by rfl) ⟨1086974, by rfl⟩ : syracuseStep 1449299 = 2173949) B2173949
theorem B859475 : Blo 858357 859475 := bstep (se 1 (by rfl) ⟨644606, by rfl⟩ : syracuseStep 859475 = 1289213) B1289213
theorem B1834339 : Blo 858357 1834339 := bstep (se 1 (by rfl) ⟨1375754, by rfl⟩ : syracuseStep 1834339 = 2751509) B2751509
theorem B859491 : Blo 858357 859491 := bstep (se 1 (by rfl) ⟨644618, by rfl⟩ : syracuseStep 859491 = 1289237) B1289237
theorem B3095921 : Blo 858357 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B2899313 : Blo 858357 2899313 := bstep (se 2 (by rfl) ⟨1087242, by rfl⟩ : syracuseStep 2899313 = 2174485) B2174485
theorem B859507 : Blo 858357 859507 := bstep (se 1 (by rfl) ⟨644630, by rfl⟩ : syracuseStep 859507 = 1289261) B1289261
theorem B966019 : Blo 858357 966019 := bstep (se 1 (by rfl) ⟨724514, by rfl⟩ : syracuseStep 966019 = 1449029) B1449029
theorem B859523 : Blo 858357 859523 := bstep (se 1 (by rfl) ⟨644642, by rfl⟩ : syracuseStep 859523 = 1289285) B1289285
theorem B4406669 : Blo 858357 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B859539 : Blo 858357 859539 := bstep (se 1 (by rfl) ⟨644654, by rfl⟩ : syracuseStep 859539 = 1289309) B1289309
theorem B859555 : Blo 858357 859555 := bstep (se 1 (by rfl) ⟨644666, by rfl⟩ : syracuseStep 859555 = 1289333) B1289333
theorem B859571 : Blo 858357 859571 := bstep (se 1 (by rfl) ⟨644678, by rfl⟩ : syracuseStep 859571 = 1289357) B1289357
theorem B859587 : Blo 858357 859587 := bstep (se 1 (by rfl) ⟨644690, by rfl⟩ : syracuseStep 859587 = 1289381) B1289381
theorem B1629649 : Blo 858357 1629649 := bstep (se 2 (by rfl) ⟨611118, by rfl⟩ : syracuseStep 1629649 = 1222237) B1222237
theorem B1449427 : Blo 858357 1449427 := bstep (se 1 (by rfl) ⟨1087070, by rfl⟩ : syracuseStep 1449427 = 2174141) B2174141
theorem B859603 : Blo 858357 859603 := bstep (se 1 (by rfl) ⟨644702, by rfl⟩ : syracuseStep 859603 = 1289405) B1289405
theorem B859619 : Blo 858357 859619 := bstep (se 1 (by rfl) ⟨644714, by rfl⟩ : syracuseStep 859619 = 1289429) B1289429
theorem B1932785 : Blo 858357 1932785 := bstep (se 2 (by rfl) ⟨724794, by rfl⟩ : syracuseStep 1932785 = 1449589) B1449589
theorem B859635 : Blo 858357 859635 := bstep (se 1 (by rfl) ⟨644726, by rfl⟩ : syracuseStep 859635 = 1289453) B1289453
theorem B1932803 : Blo 858357 1932803 := bstep (se 1 (by rfl) ⟨1449602, by rfl⟩ : syracuseStep 1932803 = 2899205) B2899205
theorem B859651 : Blo 858357 859651 := bstep (se 1 (by rfl) ⟨644738, by rfl⟩ : syracuseStep 859651 = 1289477) B1289477
theorem B917011 : Blo 858357 917011 := bstep (se 1 (by rfl) ⟨687758, by rfl⟩ : syracuseStep 917011 = 1375517) B1375517
theorem B966163 : Blo 858357 966163 := bstep (se 1 (by rfl) ⟨724622, by rfl⟩ : syracuseStep 966163 = 1449245) B1449245
theorem B859667 : Blo 858357 859667 := bstep (se 1 (by rfl) ⟨644750, by rfl⟩ : syracuseStep 859667 = 1289501) B1289501
theorem B859683 : Blo 858357 859683 := bstep (se 1 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 859683 = 1289525) B1289525
theorem B859699 : Blo 858357 859699 := bstep (se 1 (by rfl) ⟨644774, by rfl⟩ : syracuseStep 859699 = 1289549) B1289549
theorem B14114357 : Blo 858357 14114357 := bstep (se 5 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 14114357 = 1323221) B1323221
theorem B859715 : Blo 858357 859715 := bstep (se 1 (by rfl) ⟨644786, by rfl⟩ : syracuseStep 859715 = 1289573) B1289573
theorem B859731 : Blo 858357 859731 := bstep (se 1 (by rfl) ⟨644798, by rfl⟩ : syracuseStep 859731 = 1289597) B1289597
theorem B1449569 : Blo 858357 1449569 := bstep (se 2 (by rfl) ⟨543588, by rfl⟩ : syracuseStep 1449569 = 1087177) B1087177
theorem B859747 : Blo 858357 859747 := bstep (se 1 (by rfl) ⟨644810, by rfl⟩ : syracuseStep 859747 = 1289621) B1289621
theorem B859763 : Blo 858357 859763 := bstep (se 1 (by rfl) ⟨644822, by rfl⟩ : syracuseStep 859763 = 1289645) B1289645
theorem B859779 : Blo 858357 859779 := bstep (se 1 (by rfl) ⟨644834, by rfl⟩ : syracuseStep 859779 = 1289669) B1289669
theorem B859795 : Blo 858357 859795 := bstep (se 1 (by rfl) ⟨644846, by rfl⟩ : syracuseStep 859795 = 1289693) B1289693
theorem B966307 : Blo 858357 966307 := bstep (se 1 (by rfl) ⟨724730, by rfl⟩ : syracuseStep 966307 = 1449461) B1449461
theorem B859811 : Blo 858357 859811 := bstep (se 1 (by rfl) ⟨644858, by rfl⟩ : syracuseStep 859811 = 1289717) B1289717
theorem B859827 : Blo 858357 859827 := bstep (se 1 (by rfl) ⟨644870, by rfl⟩ : syracuseStep 859827 = 1289741) B1289741
theorem B859843 : Blo 858357 859843 := bstep (se 1 (by rfl) ⟨644882, by rfl⟩ : syracuseStep 859843 = 1289765) B1289765
theorem B3096269 : Blo 858357 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B859859 : Blo 858357 859859 := bstep (se 1 (by rfl) ⟨644894, by rfl⟩ : syracuseStep 859859 = 1289789) B1289789
theorem B1449697 : Blo 858357 1449697 := bstep (se 2 (by rfl) ⟨543636, by rfl⟩ : syracuseStep 1449697 = 1087273) B1087273
theorem B859875 : Blo 858357 859875 := bstep (se 1 (by rfl) ⟨644906, by rfl⟩ : syracuseStep 859875 = 1289813) B1289813
theorem B859891 : Blo 858357 859891 := bstep (se 1 (by rfl) ⟨644918, by rfl⟩ : syracuseStep 859891 = 1289837) B1289837
theorem B1449731 : Blo 858357 1449731 := bstep (se 1 (by rfl) ⟨1087298, by rfl⟩ : syracuseStep 1449731 = 2174597) B2174597
theorem B859907 : Blo 858357 859907 := bstep (se 1 (by rfl) ⟨644930, by rfl⟩ : syracuseStep 859907 = 1289861) B1289861
theorem B1933073 : Blo 858357 1933073 := bstep (se 2 (by rfl) ⟨724902, by rfl⟩ : syracuseStep 1933073 = 1449805) B1449805
theorem B859923 : Blo 858357 859923 := bstep (se 1 (by rfl) ⟨644942, by rfl⟩ : syracuseStep 859923 = 1289885) B1289885
theorem B3260195 : Blo 858357 3260195 := bstep (se 1 (by rfl) ⟨2445146, by rfl⟩ : syracuseStep 3260195 = 4890293) B4890293
theorem B1933091 : Blo 858357 1933091 := bstep (se 1 (by rfl) ⟨1449818, by rfl⟩ : syracuseStep 1933091 = 2899637) B2899637
theorem B859939 : Blo 858357 859939 := bstep (se 1 (by rfl) ⟨644954, by rfl⟩ : syracuseStep 859939 = 1289909) B1289909
theorem B3260209 : Blo 858357 3260209 := bstep (se 2 (by rfl) ⟨1222578, by rfl⟩ : syracuseStep 3260209 = 2445157) B2445157
theorem B966451 : Blo 858357 966451 := bstep (se 1 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 966451 = 1449677) B1449677
theorem B859955 : Blo 858357 859955 := bstep (se 1 (by rfl) ⟨644966, by rfl⟩ : syracuseStep 859955 = 1289933) B1289933
theorem B859971 : Blo 858357 859971 := bstep (se 1 (by rfl) ⟨644978, by rfl⟩ : syracuseStep 859971 = 1289957) B1289957
theorem B859987 : Blo 858357 859987 := bstep (se 1 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 859987 = 1289981) B1289981
theorem B860003 : Blo 858357 860003 := bstep (se 1 (by rfl) ⟨645002, by rfl⟩ : syracuseStep 860003 = 1290005) B1290005
theorem B1957745 : Blo 858357 1957745 := bstep (se 2 (by rfl) ⟨734154, by rfl⟩ : syracuseStep 1957745 = 1468309) B1468309
theorem B860019 : Blo 858357 860019 := bstep (se 1 (by rfl) ⟨645014, by rfl⟩ : syracuseStep 860019 = 1290029) B1290029
theorem B1548163 : Blo 858357 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B1449859 : Blo 858357 1449859 := bstep (se 1 (by rfl) ⟨1087394, by rfl⟩ : syracuseStep 1449859 = 2174789) B2174789
theorem B860035 : Blo 858357 860035 := bstep (se 1 (by rfl) ⟨645026, by rfl⟩ : syracuseStep 860035 = 1290053) B1290053
theorem B2899853 : Blo 858357 2899853 := bstep (se 3 (by rfl) ⟨543722, by rfl⟩ : syracuseStep 2899853 = 1087445) B1087445
theorem B860051 : Blo 858357 860051 := bstep (se 1 (by rfl) ⟨645038, by rfl⟩ : syracuseStep 860051 = 1290077) B1290077
theorem B3669923 : Blo 858357 3669923 := bstep (se 1 (by rfl) ⟨2752442, by rfl⟩ : syracuseStep 3669923 = 5504885) B5504885
theorem B860067 : Blo 858357 860067 := bstep (se 1 (by rfl) ⟨645050, by rfl⟩ : syracuseStep 860067 = 1290101) B1290101
theorem B860083 : Blo 858357 860083 := bstep (se 1 (by rfl) ⟨645062, by rfl⟩ : syracuseStep 860083 = 1290125) B1290125
theorem B917443 : Blo 858357 917443 := bstep (se 1 (by rfl) ⟨688082, by rfl⟩ : syracuseStep 917443 = 1376165) B1376165
theorem B2064323 : Blo 858357 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B966595 : Blo 858357 966595 := bstep (se 1 (by rfl) ⟨724946, by rfl⟩ : syracuseStep 966595 = 1449893) B1449893
theorem B2899907 : Blo 858357 2899907 := bstep (se 1 (by rfl) ⟨2174930, by rfl⟩ : syracuseStep 2899907 = 4349861) B4349861
theorem B860099 : Blo 858357 860099 := bstep (se 1 (by rfl) ⟨645074, by rfl⟩ : syracuseStep 860099 = 1290149) B1290149
theorem B860115 : Blo 858357 860115 := bstep (se 1 (by rfl) ⟨645086, by rfl⟩ : syracuseStep 860115 = 1290173) B1290173
theorem B860131 : Blo 858357 860131 := bstep (se 1 (by rfl) ⟨645098, by rfl⟩ : syracuseStep 860131 = 1290197) B1290197
theorem B860147 : Blo 858357 860147 := bstep (se 1 (by rfl) ⟨645110, by rfl⟩ : syracuseStep 860147 = 1290221) B1290221
theorem B1630219 : Blo 858357 1630219 := bstep (se 1 (by rfl) ⟨1222664, by rfl⟩ : syracuseStep 1630219 = 2445329) B2445329
theorem B917515 : Blo 858357 917515 := bstep (se 1 (by rfl) ⟨688136, by rfl⟩ : syracuseStep 917515 = 1376273) B1376273
theorem B966667 : Blo 858357 966667 := bstep (se 1 (by rfl) ⟨725000, by rfl⟩ : syracuseStep 966667 = 1450001) B1450001
theorem B860171 : Blo 858357 860171 := bstep (se 1 (by rfl) ⟨645128, by rfl⟩ : syracuseStep 860171 = 1290257) B1290257
theorem B860183 : Blo 858357 860183 := bstep (se 1 (by rfl) ⟨645137, by rfl⟩ : syracuseStep 860183 = 1290275) B1290275
theorem B860203 : Blo 858357 860203 := bstep (se 1 (by rfl) ⟨645152, by rfl⟩ : syracuseStep 860203 = 1290305) B1290305
theorem B860215 : Blo 858357 860215 := bstep (se 1 (by rfl) ⟨645161, by rfl⟩ : syracuseStep 860215 = 1290323) B1290323
theorem B24756293 : Blo 858357 24756293 := bstep (se 4 (by rfl) ⟨2320902, by rfl⟩ : syracuseStep 24756293 = 4641805) B4641805
theorem B860235 : Blo 858357 860235 := bstep (se 1 (by rfl) ⟨645176, by rfl⟩ : syracuseStep 860235 = 1290353) B1290353
theorem B5513291 : Blo 858357 5513291 := bstep (se 1 (by rfl) ⟨4134968, by rfl⟩ : syracuseStep 5513291 = 8269937) B8269937
theorem B860247 : Blo 858357 860247 := bstep (se 1 (by rfl) ⟨645185, by rfl⟩ : syracuseStep 860247 = 1290371) B1290371
theorem B4890725 : Blo 858357 4890725 := bstep (se 4 (by rfl) ⟨458505, by rfl⟩ : syracuseStep 4890725 = 917011) B917011
theorem B860267 : Blo 858357 860267 := bstep (se 1 (by rfl) ⟨645200, by rfl⟩ : syracuseStep 860267 = 1290401) B1290401
theorem B966775 : Blo 858357 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B860279 : Blo 858357 860279 := bstep (se 1 (by rfl) ⟨645209, by rfl⟩ : syracuseStep 860279 = 1290419) B1290419
theorem B1933451 : Blo 858357 1933451 := bstep (se 1 (by rfl) ⟨1450088, by rfl⟩ : syracuseStep 1933451 = 2900177) B2900177
theorem B860299 : Blo 858357 860299 := bstep (se 1 (by rfl) ⟨645224, by rfl⟩ : syracuseStep 860299 = 1290449) B1290449
theorem B860311 : Blo 858357 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B860331 : Blo 858357 860331 := bstep (se 1 (by rfl) ⟨645248, by rfl⟩ : syracuseStep 860331 = 1290497) B1290497
theorem B860343 : Blo 858357 860343 := bstep (se 1 (by rfl) ⟨645257, by rfl⟩ : syracuseStep 860343 = 1290515) B1290515
theorem B1933505 : Blo 858357 1933505 := bstep (se 2 (by rfl) ⟨725064, by rfl⟩ : syracuseStep 1933505 = 1450129) B1450129
theorem B860363 : Blo 858357 860363 := bstep (se 1 (by rfl) ⟨645272, by rfl⟩ : syracuseStep 860363 = 1290545) B1290545
theorem B860375 : Blo 858357 860375 := bstep (se 1 (by rfl) ⟨645281, by rfl⟩ : syracuseStep 860375 = 1290563) B1290563
theorem B860395 : Blo 858357 860395 := bstep (se 1 (by rfl) ⟨645296, by rfl⟩ : syracuseStep 860395 = 1290593) B1290593
theorem B860407 : Blo 858357 860407 := bstep (se 1 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 860407 = 1290611) B1290611
theorem B860427 : Blo 858357 860427 := bstep (se 1 (by rfl) ⟨645320, by rfl⟩ : syracuseStep 860427 = 1290641) B1290641
theorem B3260695 : Blo 858357 3260695 := bstep (se 1 (by rfl) ⟨2445521, by rfl⟩ : syracuseStep 3260695 = 4891043) B4891043
theorem B860439 : Blo 858357 860439 := bstep (se 1 (by rfl) ⟨645329, by rfl⟩ : syracuseStep 860439 = 1290659) B1290659
theorem B966955 : Blo 858357 966955 := bstep (se 1 (by rfl) ⟨725216, by rfl⟩ : syracuseStep 966955 = 1450433) B1450433
theorem B860459 : Blo 858357 860459 := bstep (se 1 (by rfl) ⟨645344, by rfl⟩ : syracuseStep 860459 = 1290689) B1290689
theorem B860471 : Blo 858357 860471 := bstep (se 1 (by rfl) ⟨645353, by rfl⟩ : syracuseStep 860471 = 1290707) B1290707
theorem B860491 : Blo 858357 860491 := bstep (se 1 (by rfl) ⟨645368, by rfl⟩ : syracuseStep 860491 = 1290737) B1290737
theorem B860503 : Blo 858357 860503 := bstep (se 1 (by rfl) ⟨645377, by rfl⟩ : syracuseStep 860503 = 1290755) B1290755
theorem B860523 : Blo 858357 860523 := bstep (se 1 (by rfl) ⟨645392, by rfl⟩ : syracuseStep 860523 = 1290785) B1290785
theorem B860535 : Blo 858357 860535 := bstep (se 1 (by rfl) ⟨645401, by rfl⟩ : syracuseStep 860535 = 1290803) B1290803
theorem B1450379 : Blo 858357 1450379 := bstep (se 1 (by rfl) ⟨1087784, by rfl⟩ : syracuseStep 1450379 = 2175569) B2175569
theorem B860555 : Blo 858357 860555 := bstep (se 1 (by rfl) ⟨645416, by rfl⟩ : syracuseStep 860555 = 1290833) B1290833
theorem B967063 : Blo 858357 967063 := bstep (se 1 (by rfl) ⟨725297, by rfl⟩ : syracuseStep 967063 = 1450595) B1450595
theorem B1933721 : Blo 858357 1933721 := bstep (se 2 (by rfl) ⟨725145, by rfl⟩ : syracuseStep 1933721 = 1450291) B1450291
theorem B1630667 : Blo 858357 1630667 := bstep (se 1 (by rfl) ⟨1223000, by rfl⟩ : syracuseStep 1630667 = 2446001) B2446001
theorem B9781721 : Blo 858357 9781721 := bstep (se 2 (by rfl) ⟨3668145, by rfl⟩ : syracuseStep 9781721 = 7336291) B7336291
theorem B9413081 : Blo 858357 9413081 := bstep (se 2 (by rfl) ⟨3529905, by rfl⟩ : syracuseStep 9413081 = 7059811) B7059811
theorem B2449885 : Blo 858357 2449885 := bstep (se 3 (by rfl) ⟨459353, by rfl⟩ : syracuseStep 2449885 = 918707) B918707
theorem B1933811 : Blo 858357 1933811 := bstep (se 1 (by rfl) ⟨1450358, by rfl⟩ : syracuseStep 1933811 = 2900717) B2900717
theorem B1450507 : Blo 858357 1450507 := bstep (se 1 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 1450507 = 2175761) B2175761
theorem B3482135 : Blo 858357 3482135 := bstep (se 1 (by rfl) ⟨2611601, by rfl⟩ : syracuseStep 3482135 = 5223203) B5223203
theorem B1835543 : Blo 858357 1835543 := bstep (se 1 (by rfl) ⟨1376657, by rfl⟩ : syracuseStep 1835543 = 2753315) B2753315
theorem B1933847 : Blo 858357 1933847 := bstep (se 1 (by rfl) ⟨1450385, by rfl⟩ : syracuseStep 1933847 = 2900771) B2900771
theorem B4645421 : Blo 858357 4645421 := bstep (se 3 (by rfl) ⟨871016, by rfl⟩ : syracuseStep 4645421 = 1742033) B1742033
theorem B4350509 : Blo 858357 4350509 := bstep (se 3 (by rfl) ⟨815720, by rfl⟩ : syracuseStep 4350509 = 1631441) B1631441
theorem B2900555 : Blo 858357 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B967243 : Blo 858357 967243 := bstep (se 1 (by rfl) ⟨725432, by rfl⟩ : syracuseStep 967243 = 1450865) B1450865
theorem B1630849 : Blo 858357 1630849 := bstep (se 2 (by rfl) ⟨611568, by rfl⟩ : syracuseStep 1630849 = 1223137) B1223137
theorem B1450649 : Blo 858357 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B1860275 : Blo 858357 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B967351 : Blo 858357 967351 := bstep (se 1 (by rfl) ⟨725513, by rfl⟩ : syracuseStep 967351 = 1451027) B1451027
theorem B1835713 : Blo 858357 1835713 := bstep (se 2 (by rfl) ⟨688392, by rfl⟩ : syracuseStep 1835713 = 1376785) B1376785
theorem B1934027 : Blo 858357 1934027 := bstep (se 1 (by rfl) ⟨1450520, by rfl⟩ : syracuseStep 1934027 = 2901041) B2901041
theorem B918263 : Blo 858357 918263 := bstep (se 1 (by rfl) ⟨688697, by rfl⟩ : syracuseStep 918263 = 1377395) B1377395
theorem B1934081 : Blo 858357 1934081 := bstep (se 2 (by rfl) ⟨725280, by rfl⟩ : syracuseStep 1934081 = 1450561) B1450561
theorem B1549057 : Blo 858357 1549057 := bstep (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) B1161793
theorem B1450777 : Blo 858357 1450777 := bstep (se 2 (by rfl) ⟨544041, by rfl⟩ : syracuseStep 1450777 = 1088083) B1088083
theorem B5882669 : Blo 858357 5882669 := bstep (se 3 (by rfl) ⟨1103000, by rfl⟩ : syracuseStep 5882669 = 2206001) B2206001
theorem B2900825 : Blo 858357 2900825 := bstep (se 2 (by rfl) ⟨1087809, by rfl⟩ : syracuseStep 2900825 = 2175619) B2175619
theorem B967531 : Blo 858357 967531 := bstep (se 1 (by rfl) ⟨725648, by rfl⟩ : syracuseStep 967531 = 1451297) B1451297
theorem B6972311 : Blo 858357 6972311 := bstep (se 1 (by rfl) ⟨5229233, by rfl⟩ : syracuseStep 6972311 = 10458467) B10458467
theorem B1631191 : Blo 858357 1631191 := bstep (se 1 (by rfl) ⟨1223393, by rfl⟩ : syracuseStep 1631191 = 2446787) B2446787
theorem B967639 : Blo 858357 967639 := bstep (se 1 (by rfl) ⟨725729, by rfl⟩ : syracuseStep 967639 = 1451459) B1451459
theorem B1934297 : Blo 858357 1934297 := bstep (se 2 (by rfl) ⟨725361, by rfl⟩ : syracuseStep 1934297 = 1450723) B1450723
theorem B1836055 : Blo 858357 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B3261485 : Blo 858357 3261485 := bstep (se 3 (by rfl) ⟨611528, by rfl⟩ : syracuseStep 3261485 = 1223057) B1223057
theorem B1934387 : Blo 858357 1934387 := bstep (se 1 (by rfl) ⟨1450790, by rfl⟩ : syracuseStep 1934387 = 2901581) B2901581
theorem B1655873 : Blo 858357 1655873 := bstep (se 2 (by rfl) ⟨620952, by rfl⟩ : syracuseStep 1655873 = 1241905) B1241905
theorem B1934423 : Blo 858357 1934423 := bstep (se 1 (by rfl) ⟨1450817, by rfl⟩ : syracuseStep 1934423 = 2901635) B2901635
theorem B967819 : Blo 858357 967819 := bstep (se 1 (by rfl) ⟨725864, by rfl⟩ : syracuseStep 967819 = 1451729) B1451729
theorem B1631411 : Blo 858357 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B13935797 : Blo 858357 13935797 := bstep (se 5 (by rfl) ⟨653240, by rfl⟩ : syracuseStep 13935797 = 1306481) B1306481
theorem B2065601 : Blo 858357 2065601 := bstep (se 2 (by rfl) ⟨774600, by rfl⟩ : syracuseStep 2065601 = 1549201) B1549201
theorem B967927 : Blo 858357 967927 := bstep (se 1 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 967927 = 1451891) B1451891
theorem B1934603 : Blo 858357 1934603 := bstep (se 1 (by rfl) ⟨1450952, by rfl⟩ : syracuseStep 1934603 = 2901905) B2901905
theorem B1033483 : Blo 858357 1033483 := bstep (se 1 (by rfl) ⟨775112, by rfl⟩ : syracuseStep 1033483 = 1550225) B1550225
theorem B1934657 : Blo 858357 1934657 := bstep (se 2 (by rfl) ⟨725496, by rfl⟩ : syracuseStep 1934657 = 1450993) B1450993
theorem B1451351 : Blo 858357 1451351 := bstep (se 1 (by rfl) ⟨1088513, by rfl⟩ : syracuseStep 1451351 = 2177027) B2177027
theorem B1287563 : Blo 858357 1287563 := bstep (se 1 (by rfl) ⟨965672, by rfl⟩ : syracuseStep 1287563 = 1931345) B1931345
theorem B1287575 : Blo 858357 1287575 := bstep (se 1 (by rfl) ⟨965681, by rfl⟩ : syracuseStep 1287575 = 1931363) B1931363
theorem B1631639 : Blo 858357 1631639 := bstep (se 1 (by rfl) ⟨1223729, by rfl⟩ : syracuseStep 1631639 = 2447459) B2447459
theorem B4900247 : Blo 858357 4900247 := bstep (se 1 (by rfl) ⟨3675185, by rfl⟩ : syracuseStep 4900247 = 7350371) B7350371
theorem B968107 : Blo 858357 968107 := bstep (se 1 (by rfl) ⟨726080, by rfl⟩ : syracuseStep 968107 = 1452161) B1452161
theorem B1451479 : Blo 858357 1451479 := bstep (se 1 (by rfl) ⟨1088609, by rfl⟩ : syracuseStep 1451479 = 2177219) B2177219
theorem B1287641 : Blo 858357 1287641 := bstep (se 2 (by rfl) ⟨482865, by rfl⟩ : syracuseStep 1287641 = 965731) B965731
theorem B2754071 : Blo 858357 2754071 := bstep (se 1 (by rfl) ⟨2065553, by rfl⟩ : syracuseStep 2754071 = 4131107) B4131107
theorem B2901527 : Blo 858357 2901527 := bstep (se 1 (by rfl) ⟨2176145, by rfl⟩ : syracuseStep 2901527 = 4352291) B4352291
theorem B1934873 : Blo 858357 1934873 := bstep (se 2 (by rfl) ⟨725577, by rfl⟩ : syracuseStep 1934873 = 1451155) B1451155
theorem B1287755 : Blo 858357 1287755 := bstep (se 1 (by rfl) ⟨965816, by rfl⟩ : syracuseStep 1287755 = 1931633) B1931633
theorem B1287767 : Blo 858357 1287767 := bstep (se 1 (by rfl) ⟨965825, by rfl⟩ : syracuseStep 1287767 = 1931651) B1931651
theorem B1934963 : Blo 858357 1934963 := bstep (se 1 (by rfl) ⟨1451222, by rfl⟩ : syracuseStep 1934963 = 2902445) B2902445
theorem B1934999 : Blo 858357 1934999 := bstep (se 1 (by rfl) ⟨1451249, by rfl⟩ : syracuseStep 1934999 = 2902499) B2902499
theorem B1287833 : Blo 858357 1287833 := bstep (se 2 (by rfl) ⟨482937, by rfl⟩ : syracuseStep 1287833 = 965875) B965875
theorem B1631897 : Blo 858357 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B1287947 : Blo 858357 1287947 := bstep (se 1 (by rfl) ⟨965960, by rfl⟩ : syracuseStep 1287947 = 1931921) B1931921
theorem B1287959 : Blo 858357 1287959 := bstep (se 1 (by rfl) ⟨965969, by rfl⟩ : syracuseStep 1287959 = 1931939) B1931939
theorem B2615105 : Blo 858357 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B1836875 : Blo 858357 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B1935179 : Blo 858357 1935179 := bstep (se 1 (by rfl) ⟨1451384, by rfl⟩ : syracuseStep 1935179 = 2902769) B2902769
theorem B1288025 : Blo 858357 1288025 := bstep (se 2 (by rfl) ⟨483009, by rfl⟩ : syracuseStep 1288025 = 966019) B966019
theorem B10594165 : Blo 858357 10594165 := bstep (se 5 (by rfl) ⟨496601, by rfl⟩ : syracuseStep 10594165 = 993203) B993203
theorem B1935233 : Blo 858357 1935233 := bstep (se 2 (by rfl) ⟨725712, by rfl⟩ : syracuseStep 1935233 = 1451425) B1451425
theorem B4646807 : Blo 858357 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B1394585 : Blo 858357 1394585 := bstep (se 2 (by rfl) ⟨522969, by rfl⟩ : syracuseStep 1394585 = 1045939) B1045939
theorem B7342001 : Blo 858357 7342001 := bstep (se 2 (by rfl) ⟨2753250, by rfl⟩ : syracuseStep 7342001 = 5506501) B5506501
theorem B2172865 : Blo 858357 2172865 := bstep (se 2 (by rfl) ⟨814824, by rfl⟩ : syracuseStep 2172865 = 1629649) B1629649
theorem B1288139 : Blo 858357 1288139 := bstep (se 1 (by rfl) ⟨966104, by rfl⟩ : syracuseStep 1288139 = 1932209) B1932209
theorem B1288151 : Blo 858357 1288151 := bstep (se 1 (by rfl) ⟨966113, by rfl⟩ : syracuseStep 1288151 = 1932227) B1932227
theorem B1288217 : Blo 858357 1288217 := bstep (se 2 (by rfl) ⟨483081, by rfl⟩ : syracuseStep 1288217 = 966163) B966163
theorem B1632307 : Blo 858357 1632307 := bstep (se 1 (by rfl) ⟨1224230, by rfl⟩ : syracuseStep 1632307 = 2448461) B2448461
theorem B2902067 : Blo 858357 2902067 := bstep (se 1 (by rfl) ⟨2176550, by rfl⟩ : syracuseStep 2902067 = 4353101) B4353101
theorem B1452107 : Blo 858357 1452107 := bstep (se 1 (by rfl) ⟨1089080, by rfl⟩ : syracuseStep 1452107 = 2178161) B2178161
theorem B1935449 : Blo 858357 1935449 := bstep (se 2 (by rfl) ⟨725793, by rfl⟩ : syracuseStep 1935449 = 1451587) B1451587
theorem B1288331 : Blo 858357 1288331 := bstep (se 1 (by rfl) ⟨966248, by rfl⟩ : syracuseStep 1288331 = 1932497) B1932497
theorem B1288343 : Blo 858357 1288343 := bstep (se 1 (by rfl) ⟨966257, by rfl⟩ : syracuseStep 1288343 = 1932515) B1932515
theorem B1837235 : Blo 858357 1837235 := bstep (se 1 (by rfl) ⟨1377926, by rfl⟩ : syracuseStep 1837235 = 2755853) B2755853
theorem B1935539 : Blo 858357 1935539 := bstep (se 1 (by rfl) ⟨1451654, by rfl⟩ : syracuseStep 1935539 = 2903309) B2903309
theorem B1935575 : Blo 858357 1935575 := bstep (se 1 (by rfl) ⟨1451681, by rfl⟩ : syracuseStep 1935575 = 2903363) B2903363
theorem B1288409 : Blo 858357 1288409 := bstep (se 2 (by rfl) ⟨483153, by rfl⟩ : syracuseStep 1288409 = 966307) B966307
theorem B5507345 : Blo 858357 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B2902337 : Blo 858357 2902337 := bstep (se 2 (by rfl) ⟨1088376, by rfl⟩ : syracuseStep 2902337 = 2176753) B2176753
theorem B1288523 : Blo 858357 1288523 := bstep (se 1 (by rfl) ⟨966392, by rfl⟩ : syracuseStep 1288523 = 1932785) B1932785
theorem B1288535 : Blo 858357 1288535 := bstep (se 1 (by rfl) ⟨966401, by rfl⟩ : syracuseStep 1288535 = 1932803) B1932803
theorem B4188509 : Blo 858357 4188509 := bstep (se 3 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 4188509 = 1570691) B1570691
theorem B1935755 : Blo 858357 1935755 := bstep (se 1 (by rfl) ⟨1451816, by rfl⟩ : syracuseStep 1935755 = 2903633) B2903633
theorem B1288601 : Blo 858357 1288601 := bstep (se 2 (by rfl) ⟨483225, by rfl⟩ : syracuseStep 1288601 = 966451) B966451
theorem B3262913 : Blo 858357 3262913 := bstep (se 2 (by rfl) ⟨1223592, by rfl⟩ : syracuseStep 3262913 = 2447185) B2447185
theorem B1935809 : Blo 858357 1935809 := bstep (se 2 (by rfl) ⟨725928, by rfl⟩ : syracuseStep 1935809 = 1451857) B1451857
theorem B1288715 : Blo 858357 1288715 := bstep (se 1 (by rfl) ⟨966536, by rfl⟩ : syracuseStep 1288715 = 1933073) B1933073
theorem B2173463 : Blo 858357 2173463 := bstep (se 1 (by rfl) ⟨1630097, by rfl⟩ : syracuseStep 2173463 = 3260195) B3260195
theorem B1288727 : Blo 858357 1288727 := bstep (se 1 (by rfl) ⟨966545, by rfl⟩ : syracuseStep 1288727 = 1933091) B1933091
theorem B1632793 : Blo 858357 1632793 := bstep (se 2 (by rfl) ⟨612297, by rfl⟩ : syracuseStep 1632793 = 1224595) B1224595
theorem B3672641 : Blo 858357 3672641 := bstep (se 2 (by rfl) ⟨1377240, by rfl⟩ : syracuseStep 3672641 = 2754481) B2754481
theorem B1305163 : Blo 858357 1305163 := bstep (se 1 (by rfl) ⟨978872, by rfl⟩ : syracuseStep 1305163 = 1957745) B1957745
theorem B1223257 : Blo 858357 1223257 := bstep (se 2 (by rfl) ⟨458721, by rfl⟩ : syracuseStep 1223257 = 917443) B917443
theorem B1288793 : Blo 858357 1288793 := bstep (se 2 (by rfl) ⟨483297, by rfl⟩ : syracuseStep 1288793 = 966595) B966595
theorem B1936025 : Blo 858357 1936025 := bstep (se 2 (by rfl) ⟨726009, by rfl⟩ : syracuseStep 1936025 = 1452019) B1452019
theorem B1288907 : Blo 858357 1288907 := bstep (se 1 (by rfl) ⟨966680, by rfl⟩ : syracuseStep 1288907 = 1933361) B1933361
theorem B1862347 : Blo 858357 1862347 := bstep (se 1 (by rfl) ⟨1396760, by rfl⟩ : syracuseStep 1862347 = 2793521) B2793521
theorem B1288919 : Blo 858357 1288919 := bstep (se 1 (by rfl) ⟨966689, by rfl⟩ : syracuseStep 1288919 = 1933379) B1933379
theorem B3672793 : Blo 858357 3672793 := bstep (se 2 (by rfl) ⟨1377297, by rfl⟩ : syracuseStep 3672793 = 2754595) B2754595
theorem B2616029 : Blo 858357 2616029 := bstep (se 3 (by rfl) ⟨490505, by rfl⟩ : syracuseStep 2616029 = 981011) B981011
theorem B1936115 : Blo 858357 1936115 := bstep (se 1 (by rfl) ⟨1452086, by rfl⟩ : syracuseStep 1936115 = 2904173) B2904173
theorem B1936151 : Blo 858357 1936151 := bstep (se 1 (by rfl) ⟨1452113, by rfl⟩ : syracuseStep 1936151 = 2904227) B2904227
theorem B1288985 : Blo 858357 1288985 := bstep (se 2 (by rfl) ⟨483369, by rfl⟩ : syracuseStep 1288985 = 966739) B966739
theorem B3099485 : Blo 858357 3099485 := bstep (se 3 (by rfl) ⟨581153, by rfl⟩ : syracuseStep 3099485 = 1162307) B1162307
theorem B2902877 : Blo 858357 2902877 := bstep (se 3 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 2902877 = 1088579) B1088579
theorem B12389219 : Blo 858357 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B1289099 : Blo 858357 1289099 := bstep (se 1 (by rfl) ⟨966824, by rfl⟩ : syracuseStep 1289099 = 1933649) B1933649
theorem B1289111 : Blo 858357 1289111 := bstep (se 1 (by rfl) ⟨966833, by rfl⟩ : syracuseStep 1289111 = 1933667) B1933667
theorem B1289177 : Blo 858357 1289177 := bstep (se 2 (by rfl) ⟨483441, by rfl⟩ : syracuseStep 1289177 = 966883) B966883
theorem B2616371 : Blo 858357 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B1289291 : Blo 858357 1289291 := bstep (se 1 (by rfl) ⟨966968, by rfl⟩ : syracuseStep 1289291 = 1933937) B1933937
theorem B1633355 : Blo 858357 1633355 := bstep (se 1 (by rfl) ⟨1225016, by rfl⟩ : syracuseStep 1633355 = 2450033) B2450033
theorem B1289303 : Blo 858357 1289303 := bstep (se 1 (by rfl) ⟨966977, by rfl⟩ : syracuseStep 1289303 = 1933955) B1933955
theorem B7351397 : Blo 858357 7351397 := bstep (se 4 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 7351397 = 1378387) B1378387
theorem B1289369 : Blo 858357 1289369 := bstep (se 2 (by rfl) ⟨483513, by rfl⟩ : syracuseStep 1289369 = 967027) B967027
theorem B1633537 : Blo 858357 1633537 := bstep (se 2 (by rfl) ⟨612576, by rfl⟩ : syracuseStep 1633537 = 1225153) B1225153
theorem B1289483 : Blo 858357 1289483 := bstep (se 1 (by rfl) ⟨967112, by rfl⟩ : syracuseStep 1289483 = 1934225) B1934225
theorem B1289495 : Blo 858357 1289495 := bstep (se 1 (by rfl) ⟨967121, by rfl⟩ : syracuseStep 1289495 = 1934243) B1934243
theorem B2174273 : Blo 858357 2174273 := bstep (se 2 (by rfl) ⟨815352, by rfl⟩ : syracuseStep 2174273 = 1630705) B1630705
theorem B1289561 : Blo 858357 1289561 := bstep (se 2 (by rfl) ⟨483585, by rfl⟩ : syracuseStep 1289561 = 967171) B967171
theorem B4713821 : Blo 858357 4713821 := bstep (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) B1767683
theorem B871831 : Blo 858357 871831 := bstep (se 1 (by rfl) ⟨653873, by rfl⟩ : syracuseStep 871831 = 1307747) B1307747
theorem B1289675 : Blo 858357 1289675 := bstep (se 1 (by rfl) ⟨967256, by rfl⟩ : syracuseStep 1289675 = 1934513) B1934513
theorem B1961419 : Blo 858357 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B1289687 : Blo 858357 1289687 := bstep (se 1 (by rfl) ⟨967265, by rfl⟩ : syracuseStep 1289687 = 1934531) B1934531
theorem B1289753 : Blo 858357 1289753 := bstep (se 2 (by rfl) ⟨483657, by rfl⟩ : syracuseStep 1289753 = 967315) B967315
theorem B1289867 : Blo 858357 1289867 := bstep (se 1 (by rfl) ⟨967400, by rfl⟩ : syracuseStep 1289867 = 1934801) B1934801
theorem B1289879 : Blo 858357 1289879 := bstep (se 1 (by rfl) ⟨967409, by rfl⟩ : syracuseStep 1289879 = 1934819) B1934819
theorem B1289945 : Blo 858357 1289945 := bstep (se 2 (by rfl) ⟨483729, by rfl⟩ : syracuseStep 1289945 = 967459) B967459
theorem B3485443 : Blo 858357 3485443 := bstep (se 1 (by rfl) ⟨2614082, by rfl⟩ : syracuseStep 3485443 = 5228165) B5228165
theorem B6188845 : Blo 858357 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B1290059 : Blo 858357 1290059 := bstep (se 1 (by rfl) ⟨967544, by rfl⟩ : syracuseStep 1290059 = 1935089) B1935089
theorem B1290071 : Blo 858357 1290071 := bstep (se 1 (by rfl) ⟨967553, by rfl⟩ : syracuseStep 1290071 = 1935107) B1935107
theorem B2174809 : Blo 858357 2174809 := bstep (se 2 (by rfl) ⟨815553, by rfl⟩ : syracuseStep 2174809 = 1631107) B1631107
theorem B3264401 : Blo 858357 3264401 := bstep (se 2 (by rfl) ⟨1224150, by rfl⟩ : syracuseStep 3264401 = 2448301) B2448301
theorem B1290137 : Blo 858357 1290137 := bstep (se 2 (by rfl) ⟨483801, by rfl⟩ : syracuseStep 1290137 = 967603) B967603
theorem B25472945 : Blo 858357 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B7942067 : Blo 858357 7942067 := bstep (se 1 (by rfl) ⟨5956550, by rfl⟩ : syracuseStep 7942067 = 11913101) B11913101
theorem B2756531 : Blo 858357 2756531 := bstep (se 1 (by rfl) ⟨2067398, by rfl⟩ : syracuseStep 2756531 = 4134797) B4134797
theorem B2904011 : Blo 858357 2904011 := bstep (se 1 (by rfl) ⟨2178008, by rfl⟩ : syracuseStep 2904011 = 4356017) B4356017
theorem B1224715 : Blo 858357 1224715 := bstep (se 1 (by rfl) ⟨918536, by rfl⟩ : syracuseStep 1224715 = 1837073) B1837073
theorem B1290251 : Blo 858357 1290251 := bstep (se 1 (by rfl) ⟨967688, by rfl⟩ : syracuseStep 1290251 = 1935377) B1935377
theorem B1290263 : Blo 858357 1290263 := bstep (se 1 (by rfl) ⟨967697, by rfl⟩ : syracuseStep 1290263 = 1935395) B1935395
theorem B1290329 : Blo 858357 1290329 := bstep (se 2 (by rfl) ⟨483873, by rfl⟩ : syracuseStep 1290329 = 967747) B967747
theorem B4124803 : Blo 858357 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B6533297 : Blo 858357 6533297 := bstep (se 2 (by rfl) ⟨2449986, by rfl⟩ : syracuseStep 6533297 = 4899973) B4899973
theorem B1290443 : Blo 858357 1290443 := bstep (se 1 (by rfl) ⟨967832, by rfl⟩ : syracuseStep 1290443 = 1935665) B1935665
theorem B1290455 : Blo 858357 1290455 := bstep (se 1 (by rfl) ⟨967841, by rfl⟩ : syracuseStep 1290455 = 1935683) B1935683
theorem B2904281 : Blo 858357 2904281 := bstep (se 2 (by rfl) ⟨1089105, by rfl⟩ : syracuseStep 2904281 = 2178211) B2178211
theorem B1290521 : Blo 858357 1290521 := bstep (se 2 (by rfl) ⟨483945, by rfl⟩ : syracuseStep 1290521 = 967891) B967891
theorem B6607169 : Blo 858357 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B3264857 : Blo 858357 3264857 := bstep (se 2 (by rfl) ⟨1224321, by rfl⟩ : syracuseStep 3264857 = 2448643) B2448643
theorem B4354397 : Blo 858357 4354397 := bstep (se 3 (by rfl) ⟨816449, by rfl⟩ : syracuseStep 4354397 = 1632899) B1632899
theorem B1290635 : Blo 858357 1290635 := bstep (se 1 (by rfl) ⟨967976, by rfl⟩ : syracuseStep 1290635 = 1935953) B1935953
theorem B1290647 : Blo 858357 1290647 := bstep (se 1 (by rfl) ⟨967985, by rfl⟩ : syracuseStep 1290647 = 1935971) B1935971
theorem B1470935 : Blo 858357 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B2445785 : Blo 858357 2445785 := bstep (se 2 (by rfl) ⟨917169, by rfl⟩ : syracuseStep 2445785 = 1834339) B1834339
theorem B2650585 : Blo 858357 2650585 := bstep (se 2 (by rfl) ⟨993969, by rfl⟩ : syracuseStep 2650585 = 1987939) B1987939
theorem B1290713 : Blo 858357 1290713 := bstep (se 2 (by rfl) ⟨484017, by rfl⟩ : syracuseStep 1290713 = 968035) B968035
theorem B3265069 : Blo 858357 3265069 := bstep (se 3 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 3265069 = 1224401) B1224401
theorem B1290827 : Blo 858357 1290827 := bstep (se 1 (by rfl) ⟨968120, by rfl⟩ : syracuseStep 1290827 = 1936241) B1936241
theorem B1290839 : Blo 858357 1290839 := bstep (se 1 (by rfl) ⟨968129, by rfl⟩ : syracuseStep 1290839 = 1936259) B1936259
theorem B6533783 : Blo 858357 6533783 := bstep (se 1 (by rfl) ⟨4900337, by rfl⟩ : syracuseStep 6533783 = 9800675) B9800675
theorem B6976205 : Blo 858357 6976205 := bstep (se 3 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 6976205 = 2616077) B2616077
theorem B3142475 : Blo 858357 3142475 := bstep (se 1 (by rfl) ⟨2356856, by rfl⟩ : syracuseStep 3142475 = 4713713) B4713713
theorem B3265373 : Blo 858357 3265373 := bstep (se 3 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 3265373 = 1224515) B1224515
theorem B2937779 : Blo 858357 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B2175923 : Blo 858357 2175923 := bstep (se 1 (by rfl) ⟨1631942, by rfl⟩ : syracuseStep 2175923 = 3263885) B3263885
theorem B9409571 : Blo 858357 9409571 := bstep (se 1 (by rfl) ⟨7057178, by rfl⟩ : syracuseStep 9409571 = 14114357) B14114357
theorem B4346945 : Blo 858357 4346945 := bstep (se 2 (by rfl) ⟨1630104, by rfl⟩ : syracuseStep 4346945 = 3260209) B3260209
theorem B2897099 : Blo 858357 2897099 := bstep (se 1 (by rfl) ⟨2172824, by rfl⟩ : syracuseStep 2897099 = 4345649) B4345649
theorem B1651915 : Blo 858357 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B2176217 : Blo 858357 2176217 := bstep (se 2 (by rfl) ⟨816081, by rfl⟩ : syracuseStep 2176217 = 1632163) B1632163
theorem B2446615 : Blo 858357 2446615 := bstep (se 1 (by rfl) ⟨1834961, by rfl⟩ : syracuseStep 2446615 = 3669923) B3669923
theorem B1742105 : Blo 858357 1742105 := bstep (se 2 (by rfl) ⟨653289, by rfl⟩ : syracuseStep 1742105 = 1306579) B1306579
theorem B980299 : Blo 858357 980299 := bstep (se 1 (by rfl) ⟨735224, by rfl⟩ : syracuseStep 980299 = 1470449) B1470449
theorem B6616525 : Blo 858357 6616525 := bstep (se 3 (by rfl) ⟨1240598, by rfl⟩ : syracuseStep 6616525 = 2481197) B2481197
theorem B1160663 : Blo 858357 1160663 := bstep (se 1 (by rfl) ⟨870497, by rfl⟩ : syracuseStep 1160663 = 1740995) B1740995
theorem B2897369 : Blo 858357 2897369 := bstep (se 2 (by rfl) ⟨1086513, by rfl⟩ : syracuseStep 2897369 = 2173027) B2173027
theorem B3667531 : Blo 858357 3667531 := bstep (se 1 (by rfl) ⟨2750648, by rfl⟩ : syracuseStep 3667531 = 5501297) B5501297
theorem B9557597 : Blo 858357 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B2651869 : Blo 858357 2651869 := bstep (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) B994451
theorem B4896557 : Blo 858357 4896557 := bstep (se 3 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 4896557 = 1836209) B1836209
theorem B2094913 : Blo 858357 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B3667805 : Blo 858357 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B1652609 : Blo 858357 1652609 := bstep (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) B1239457
theorem B1087435 : Blo 858357 1087435 := bstep (se 1 (by rfl) ⟨815576, by rfl⟩ : syracuseStep 1087435 = 1631153) B1631153
theorem B5502937 : Blo 858357 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B3356633 : Blo 858357 3356633 := bstep (se 2 (by rfl) ⟨1258737, by rfl⟩ : syracuseStep 3356633 = 2517475) B2517475
theorem B2447435 : Blo 858357 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B2898071 : Blo 858357 2898071 := bstep (se 1 (by rfl) ⟨2173553, by rfl⟩ : syracuseStep 2898071 = 4347107) B4347107
theorem B1931417 : Blo 858357 1931417 := bstep (se 2 (by rfl) ⟨724281, by rfl⟩ : syracuseStep 1931417 = 1448563) B1448563
theorem B1931507 : Blo 858357 1931507 := bstep (se 1 (by rfl) ⟨1448630, by rfl⟩ : syracuseStep 1931507 = 2897261) B2897261
theorem B858359 : Blo 858357 858359 := bstep (se 1 (by rfl) ⟨643769, by rfl⟩ : syracuseStep 858359 = 1287539) B1287539
theorem B858379 : Blo 858357 858379 := bstep (se 1 (by rfl) ⟨643784, by rfl⟩ : syracuseStep 858379 = 1287569) B1287569
theorem B858391 : Blo 858357 858391 := bstep (se 1 (by rfl) ⟨643793, by rfl⟩ : syracuseStep 858391 = 1287587) B1287587
theorem B1931543 : Blo 858357 1931543 := bstep (se 1 (by rfl) ⟨1448657, by rfl⟩ : syracuseStep 1931543 = 2897315) B2897315
theorem B7338275 : Blo 858357 7338275 := bstep (se 1 (by rfl) ⟨5503706, by rfl⟩ : syracuseStep 7338275 = 11007413) B11007413
theorem B858411 : Blo 858357 858411 := bstep (se 1 (by rfl) ⟨643808, by rfl⟩ : syracuseStep 858411 = 1287617) B1287617
theorem B8255789 : Blo 858357 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B858423 : Blo 858357 858423 := bstep (se 1 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 858423 = 1287635) B1287635
theorem B858443 : Blo 858357 858443 := bstep (se 1 (by rfl) ⟨643832, by rfl⟩ : syracuseStep 858443 = 1287665) B1287665
theorem B4127051 : Blo 858357 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B858455 : Blo 858357 858455 := bstep (se 1 (by rfl) ⟨643841, by rfl⟩ : syracuseStep 858455 = 1287683) B1287683
theorem B858475 : Blo 858357 858475 := bstep (se 1 (by rfl) ⟨643856, by rfl⟩ : syracuseStep 858475 = 1287713) B1287713
theorem B858487 : Blo 858357 858487 := bstep (se 1 (by rfl) ⟨643865, by rfl⟩ : syracuseStep 858487 = 1287731) B1287731
theorem B858507 : Blo 858357 858507 := bstep (se 1 (by rfl) ⟨643880, by rfl⟩ : syracuseStep 858507 = 1287761) B1287761
theorem B858519 : Blo 858357 858519 := bstep (se 1 (by rfl) ⟨643889, by rfl⟩ : syracuseStep 858519 = 1287779) B1287779
theorem B4356503 : Blo 858357 4356503 := bstep (se 1 (by rfl) ⟨3267377, by rfl⟩ : syracuseStep 4356503 = 6534755) B6534755
theorem B858539 : Blo 858357 858539 := bstep (se 1 (by rfl) ⟨643904, by rfl⟩ : syracuseStep 858539 = 1287809) B1287809
theorem B858551 : Blo 858357 858551 := bstep (se 1 (by rfl) ⟨643913, by rfl⟩ : syracuseStep 858551 = 1287827) B1287827
theorem B1931723 : Blo 858357 1931723 := bstep (se 1 (by rfl) ⟨1448792, by rfl⟩ : syracuseStep 1931723 = 2897585) B2897585
theorem B858571 : Blo 858357 858571 := bstep (se 1 (by rfl) ⟨643928, by rfl⟩ : syracuseStep 858571 = 1287857) B1287857
theorem B858583 : Blo 858357 858583 := bstep (se 1 (by rfl) ⟨643937, by rfl⟩ : syracuseStep 858583 = 1287875) B1287875
theorem B858603 : Blo 858357 858603 := bstep (se 1 (by rfl) ⟨643952, by rfl⟩ : syracuseStep 858603 = 1287905) B1287905
theorem B858615 : Blo 858357 858615 := bstep (se 1 (by rfl) ⟨643961, by rfl⟩ : syracuseStep 858615 = 1287923) B1287923
theorem B1931777 : Blo 858357 1931777 := bstep (se 2 (by rfl) ⟨724416, by rfl⟩ : syracuseStep 1931777 = 1448833) B1448833
theorem B858635 : Blo 858357 858635 := bstep (se 1 (by rfl) ⟨643976, by rfl⟩ : syracuseStep 858635 = 1287953) B1287953
theorem B858647 : Blo 858357 858647 := bstep (se 1 (by rfl) ⟨643985, by rfl⟩ : syracuseStep 858647 = 1287971) B1287971
theorem B858667 : Blo 858357 858667 := bstep (se 1 (by rfl) ⟨644000, by rfl⟩ : syracuseStep 858667 = 1288001) B1288001
theorem B858679 : Blo 858357 858679 := bstep (se 1 (by rfl) ⟨644009, by rfl⟩ : syracuseStep 858679 = 1288019) B1288019
theorem B858699 : Blo 858357 858699 := bstep (se 1 (by rfl) ⟨644024, by rfl⟩ : syracuseStep 858699 = 1288049) B1288049
theorem B7060043 : Blo 858357 7060043 := bstep (se 1 (by rfl) ⟨5295032, by rfl⟩ : syracuseStep 7060043 = 10590065) B10590065
theorem B858711 : Blo 858357 858711 := bstep (se 1 (by rfl) ⟨644033, by rfl⟩ : syracuseStep 858711 = 1288067) B1288067
theorem B858731 : Blo 858357 858731 := bstep (se 1 (by rfl) ⟨644048, by rfl⟩ : syracuseStep 858731 = 1288097) B1288097
theorem B1833587 : Blo 858357 1833587 := bstep (se 1 (by rfl) ⟨1375190, by rfl⟩ : syracuseStep 1833587 = 2750381) B2750381
theorem B858743 : Blo 858357 858743 := bstep (se 1 (by rfl) ⟨644057, by rfl⟩ : syracuseStep 858743 = 1288115) B1288115
theorem B858763 : Blo 858357 858763 := bstep (se 1 (by rfl) ⟨644072, by rfl⟩ : syracuseStep 858763 = 1288145) B1288145
theorem B858775 : Blo 858357 858775 := bstep (se 1 (by rfl) ⟨644081, by rfl⟩ : syracuseStep 858775 = 1288163) B1288163
theorem B858795 : Blo 858357 858795 := bstep (se 1 (by rfl) ⟨644096, by rfl⟩ : syracuseStep 858795 = 1288193) B1288193
theorem B4889267 : Blo 858357 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B2898611 : Blo 858357 2898611 := bstep (se 1 (by rfl) ⟨2173958, by rfl⟩ : syracuseStep 2898611 = 4347917) B4347917
theorem B858807 : Blo 858357 858807 := bstep (se 1 (by rfl) ⟨644105, by rfl⟩ : syracuseStep 858807 = 1288211) B1288211
theorem B1448651 : Blo 858357 1448651 := bstep (se 1 (by rfl) ⟨1086488, by rfl⟩ : syracuseStep 1448651 = 2172977) B2172977
theorem B858827 : Blo 858357 858827 := bstep (se 1 (by rfl) ⟨644120, by rfl⟩ : syracuseStep 858827 = 1288241) B1288241
theorem B9796301 : Blo 858357 9796301 := bstep (se 3 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 9796301 = 3673613) B3673613
theorem B858839 : Blo 858357 858839 := bstep (se 1 (by rfl) ⟨644129, by rfl⟩ : syracuseStep 858839 = 1288259) B1288259
theorem B1931993 : Blo 858357 1931993 := bstep (se 2 (by rfl) ⟨724497, by rfl⟩ : syracuseStep 1931993 = 1448995) B1448995
theorem B858859 : Blo 858357 858859 := bstep (se 1 (by rfl) ⟨644144, by rfl⟩ : syracuseStep 858859 = 1288289) B1288289
theorem B858871 : Blo 858357 858871 := bstep (se 1 (by rfl) ⟨644153, by rfl⟩ : syracuseStep 858871 = 1288307) B1288307
theorem B858891 : Blo 858357 858891 := bstep (se 1 (by rfl) ⟨644168, by rfl⟩ : syracuseStep 858891 = 1288337) B1288337
theorem B858903 : Blo 858357 858903 := bstep (se 1 (by rfl) ⟨644177, by rfl⟩ : syracuseStep 858903 = 1288355) B1288355
theorem B858923 : Blo 858357 858923 := bstep (se 1 (by rfl) ⟨644192, by rfl⟩ : syracuseStep 858923 = 1288385) B1288385
theorem B1932083 : Blo 858357 1932083 := bstep (se 1 (by rfl) ⟨1449062, by rfl⟩ : syracuseStep 1932083 = 2898125) B2898125
theorem B858935 : Blo 858357 858935 := bstep (se 1 (by rfl) ⟨644201, by rfl⟩ : syracuseStep 858935 = 1288403) B1288403
theorem B1448779 : Blo 858357 1448779 := bstep (se 1 (by rfl) ⟨1086584, by rfl⟩ : syracuseStep 1448779 = 2173169) B2173169
theorem B858955 : Blo 858357 858955 := bstep (se 1 (by rfl) ⟨644216, by rfl⟩ : syracuseStep 858955 = 1288433) B1288433
theorem B2177867 : Blo 858357 2177867 := bstep (se 1 (by rfl) ⟨1633400, by rfl⟩ : syracuseStep 2177867 = 3266801) B3266801
theorem B1932119 : Blo 858357 1932119 := bstep (se 1 (by rfl) ⟨1449089, by rfl⟩ : syracuseStep 1932119 = 2898179) B2898179
theorem B858967 : Blo 858357 858967 := bstep (se 1 (by rfl) ⟨644225, by rfl⟩ : syracuseStep 858967 = 1288451) B1288451
theorem B858987 : Blo 858357 858987 := bstep (se 1 (by rfl) ⟨644240, by rfl⟩ : syracuseStep 858987 = 1288481) B1288481
theorem B858999 : Blo 858357 858999 := bstep (se 1 (by rfl) ⟨644249, by rfl⟩ : syracuseStep 858999 = 1288499) B1288499
theorem B859019 : Blo 858357 859019 := bstep (se 1 (by rfl) ⟨644264, by rfl⟩ : syracuseStep 859019 = 1288529) B1288529
theorem B859031 : Blo 858357 859031 := bstep (se 1 (by rfl) ⟨644273, by rfl⟩ : syracuseStep 859031 = 1288547) B1288547
theorem B1088407 : Blo 858357 1088407 := bstep (se 1 (by rfl) ⟨816305, by rfl⟩ : syracuseStep 1088407 = 1632611) B1632611
theorem B859051 : Blo 858357 859051 := bstep (se 1 (by rfl) ⟨644288, by rfl⟩ : syracuseStep 859051 = 1288577) B1288577
theorem B5880755 : Blo 858357 5880755 := bstep (se 1 (by rfl) ⟨4410566, by rfl⟩ : syracuseStep 5880755 = 8821133) B8821133
theorem B859063 : Blo 858357 859063 := bstep (se 1 (by rfl) ⟨644297, by rfl⟩ : syracuseStep 859063 = 1288595) B1288595
theorem B2898881 : Blo 858357 2898881 := bstep (se 2 (by rfl) ⟨1087080, by rfl⟩ : syracuseStep 2898881 = 2174161) B2174161
theorem B81476549 : Blo 858357 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B859083 : Blo 858357 859083 := bstep (se 1 (by rfl) ⟨644312, by rfl⟩ : syracuseStep 859083 = 1288625) B1288625
theorem B859095 : Blo 858357 859095 := bstep (se 1 (by rfl) ⟨644321, by rfl⟩ : syracuseStep 859095 = 1288643) B1288643
theorem B1448921 : Blo 858357 1448921 := bstep (se 2 (by rfl) ⟨543345, by rfl⟩ : syracuseStep 1448921 = 1086691) B1086691
theorem B4348889 : Blo 858357 4348889 := bstep (se 2 (by rfl) ⟨1630833, by rfl⟩ : syracuseStep 4348889 = 3261667) B3261667
theorem B859115 : Blo 858357 859115 := bstep (se 1 (by rfl) ⟨644336, by rfl⟩ : syracuseStep 859115 = 1288673) B1288673
theorem B859127 : Blo 858357 859127 := bstep (se 1 (by rfl) ⟨644345, by rfl⟩ : syracuseStep 859127 = 1288691) B1288691
theorem B1932299 : Blo 858357 1932299 := bstep (se 1 (by rfl) ⟨1449224, by rfl⟩ : syracuseStep 1932299 = 2898449) B2898449
theorem B859147 : Blo 858357 859147 := bstep (se 1 (by rfl) ⟨644360, by rfl⟩ : syracuseStep 859147 = 1288721) B1288721
theorem B7339025 : Blo 858357 7339025 := bstep (se 2 (by rfl) ⟨2752134, by rfl⟩ : syracuseStep 7339025 = 5504269) B5504269
theorem B859159 : Blo 858357 859159 := bstep (se 1 (by rfl) ⟨644369, by rfl⟩ : syracuseStep 859159 = 1288739) B1288739
theorem B859179 : Blo 858357 859179 := bstep (se 1 (by rfl) ⟨644384, by rfl⟩ : syracuseStep 859179 = 1288769) B1288769
theorem B1743923 : Blo 858357 1743923 := bstep (se 1 (by rfl) ⟨1307942, by rfl⟩ : syracuseStep 1743923 = 2615885) B2615885
theorem B859191 : Blo 858357 859191 := bstep (se 1 (by rfl) ⟨644393, by rfl⟩ : syracuseStep 859191 = 1288787) B1288787
theorem B1932353 : Blo 858357 1932353 := bstep (se 2 (by rfl) ⟨724632, by rfl⟩ : syracuseStep 1932353 = 1449265) B1449265
theorem B859211 : Blo 858357 859211 := bstep (se 1 (by rfl) ⟨644408, by rfl⟩ : syracuseStep 859211 = 1288817) B1288817
theorem B859223 : Blo 858357 859223 := bstep (se 1 (by rfl) ⟨644417, by rfl⟩ : syracuseStep 859223 = 1288835) B1288835
theorem B1449049 : Blo 858357 1449049 := bstep (se 2 (by rfl) ⟨543393, by rfl⟩ : syracuseStep 1449049 = 1086787) B1086787
theorem B859243 : Blo 858357 859243 := bstep (se 1 (by rfl) ⟨644432, by rfl⟩ : syracuseStep 859243 = 1288865) B1288865
theorem B859255 : Blo 858357 859255 := bstep (se 1 (by rfl) ⟨644441, by rfl⟩ : syracuseStep 859255 = 1288883) B1288883
theorem B859275 : Blo 858357 859275 := bstep (se 1 (by rfl) ⟨644456, by rfl⟩ : syracuseStep 859275 = 1288913) B1288913
theorem B859287 : Blo 858357 859287 := bstep (se 1 (by rfl) ⟨644465, by rfl⟩ : syracuseStep 859287 = 1288931) B1288931
theorem B965803 : Blo 858357 965803 := bstep (se 1 (by rfl) ⟨724352, by rfl⟩ : syracuseStep 965803 = 1448705) B1448705
theorem B859307 : Blo 858357 859307 := bstep (se 1 (by rfl) ⟨644480, by rfl⟩ : syracuseStep 859307 = 1288961) B1288961
theorem B859319 : Blo 858357 859319 := bstep (se 1 (by rfl) ⟨644489, by rfl⟩ : syracuseStep 859319 = 1288979) B1288979
theorem B859339 : Blo 858357 859339 := bstep (se 1 (by rfl) ⟨644504, by rfl⟩ : syracuseStep 859339 = 1289009) B1289009
theorem B859351 : Blo 858357 859351 := bstep (se 1 (by rfl) ⟨644513, by rfl⟩ : syracuseStep 859351 = 1289027) B1289027
theorem B859371 : Blo 858357 859371 := bstep (se 1 (by rfl) ⟨644528, by rfl⟩ : syracuseStep 859371 = 1289057) B1289057
theorem B859383 : Blo 858357 859383 := bstep (se 1 (by rfl) ⟨644537, by rfl⟩ : syracuseStep 859383 = 1289075) B1289075
theorem B3767555 : Blo 858357 3767555 := bstep (se 1 (by rfl) ⟨2825666, by rfl⟩ : syracuseStep 3767555 = 5651333) B5651333
theorem B859403 : Blo 858357 859403 := bstep (se 1 (by rfl) ⟨644552, by rfl⟩ : syracuseStep 859403 = 1289105) B1289105
theorem B1162507 : Blo 858357 1162507 := bstep (se 1 (by rfl) ⟨871880, by rfl⟩ : syracuseStep 1162507 = 1743761) B1743761
theorem B965911 : Blo 858357 965911 := bstep (se 1 (by rfl) ⟨724433, by rfl⟩ : syracuseStep 965911 = 1448867) B1448867
theorem B859415 : Blo 858357 859415 := bstep (se 1 (by rfl) ⟨644561, by rfl⟩ : syracuseStep 859415 = 1289123) B1289123
theorem B1932569 : Blo 858357 1932569 := bstep (se 2 (by rfl) ⟨724713, by rfl⟩ : syracuseStep 1932569 = 1449427) B1449427
theorem B859435 : Blo 858357 859435 := bstep (se 1 (by rfl) ⟨644576, by rfl⟩ : syracuseStep 859435 = 1289153) B1289153
theorem B859447 : Blo 858357 859447 := bstep (se 1 (by rfl) ⟨644585, by rfl⟩ : syracuseStep 859447 = 1289171) B1289171
theorem B3259723 : Blo 858357 3259723 := bstep (se 1 (by rfl) ⟨2444792, by rfl⟩ : syracuseStep 3259723 = 4889585) B4889585
theorem B859467 : Blo 858357 859467 := bstep (se 1 (by rfl) ⟨644600, by rfl⟩ : syracuseStep 859467 = 1289201) B1289201
theorem B1162571 : Blo 858357 1162571 := bstep (se 1 (by rfl) ⟨871928, by rfl⟩ : syracuseStep 1162571 = 1743857) B1743857
theorem B859479 : Blo 858357 859479 := bstep (se 1 (by rfl) ⟨644609, by rfl⟩ : syracuseStep 859479 = 1289219) B1289219
theorem B859499 : Blo 858357 859499 := bstep (se 1 (by rfl) ⟨644624, by rfl⟩ : syracuseStep 859499 = 1289249) B1289249
theorem B1932659 : Blo 858357 1932659 := bstep (se 1 (by rfl) ⟨1449494, by rfl⟩ : syracuseStep 1932659 = 2898989) B2898989
theorem B10452341 : Blo 858357 10452341 := bstep (se 5 (by rfl) ⟨489953, by rfl⟩ : syracuseStep 10452341 = 979907) B979907
theorem B859511 : Blo 858357 859511 := bstep (se 1 (by rfl) ⟨644633, by rfl⟩ : syracuseStep 859511 = 1289267) B1289267
theorem B859531 : Blo 858357 859531 := bstep (se 1 (by rfl) ⟨644648, by rfl⟩ : syracuseStep 859531 = 1289297) B1289297
theorem B1932695 : Blo 858357 1932695 := bstep (se 1 (by rfl) ⟨1449521, by rfl⟩ : syracuseStep 1932695 = 2899043) B2899043
theorem B859543 : Blo 858357 859543 := bstep (se 1 (by rfl) ⟨644657, by rfl⟩ : syracuseStep 859543 = 1289315) B1289315
theorem B859563 : Blo 858357 859563 := bstep (se 1 (by rfl) ⟨644672, by rfl⟩ : syracuseStep 859563 = 1289345) B1289345
theorem B859575 : Blo 858357 859575 := bstep (se 1 (by rfl) ⟨644681, by rfl⟩ : syracuseStep 859575 = 1289363) B1289363
theorem B966091 : Blo 858357 966091 := bstep (se 1 (by rfl) ⟨724568, by rfl⟩ : syracuseStep 966091 = 1449137) B1449137
theorem B859595 : Blo 858357 859595 := bstep (se 1 (by rfl) ⟨644696, by rfl⟩ : syracuseStep 859595 = 1289393) B1289393
theorem B859607 : Blo 858357 859607 := bstep (se 1 (by rfl) ⟨644705, by rfl⟩ : syracuseStep 859607 = 1289411) B1289411
theorem B2899421 : Blo 858357 2899421 := bstep (se 3 (by rfl) ⟨543641, by rfl⟩ : syracuseStep 2899421 = 1087283) B1087283
theorem B859627 : Blo 858357 859627 := bstep (se 1 (by rfl) ⟨644720, by rfl⟩ : syracuseStep 859627 = 1289441) B1289441
theorem B1834483 : Blo 858357 1834483 := bstep (se 1 (by rfl) ⟨1375862, by rfl⟩ : syracuseStep 1834483 = 2751725) B2751725
theorem B859639 : Blo 858357 859639 := bstep (se 1 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 859639 = 1289459) B1289459
theorem B859659 : Blo 858357 859659 := bstep (se 1 (by rfl) ⟨644744, by rfl⟩ : syracuseStep 859659 = 1289489) B1289489
theorem B859671 : Blo 858357 859671 := bstep (se 1 (by rfl) ⟨644753, by rfl⟩ : syracuseStep 859671 = 1289507) B1289507
theorem B859691 : Blo 858357 859691 := bstep (se 1 (by rfl) ⟨644768, by rfl⟩ : syracuseStep 859691 = 1289537) B1289537
theorem B966199 : Blo 858357 966199 := bstep (se 1 (by rfl) ⟨724649, by rfl⟩ : syracuseStep 966199 = 1449299) B1449299
theorem B859703 : Blo 858357 859703 := bstep (se 1 (by rfl) ⟨644777, by rfl⟩ : syracuseStep 859703 = 1289555) B1289555
theorem B1932875 : Blo 858357 1932875 := bstep (se 1 (by rfl) ⟨1449656, by rfl⟩ : syracuseStep 1932875 = 2899313) B2899313
theorem B859723 : Blo 858357 859723 := bstep (se 1 (by rfl) ⟨644792, by rfl⟩ : syracuseStep 859723 = 1289585) B1289585
theorem B859735 : Blo 858357 859735 := bstep (se 1 (by rfl) ⟨644801, by rfl⟩ : syracuseStep 859735 = 1289603) B1289603
theorem B3259997 : Blo 858357 3259997 := bstep (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) B1222499
theorem B859755 : Blo 858357 859755 := bstep (se 1 (by rfl) ⟨644816, by rfl⟩ : syracuseStep 859755 = 1289633) B1289633
theorem B859767 : Blo 858357 859767 := bstep (se 1 (by rfl) ⟨644825, by rfl⟩ : syracuseStep 859767 = 1289651) B1289651
theorem B1932929 : Blo 858357 1932929 := bstep (se 2 (by rfl) ⟨724848, by rfl⟩ : syracuseStep 1932929 = 1449697) B1449697
theorem B859787 : Blo 858357 859787 := bstep (se 1 (by rfl) ⟨644840, by rfl⟩ : syracuseStep 859787 = 1289681) B1289681
theorem B1449623 : Blo 858357 1449623 := bstep (se 1 (by rfl) ⟨1087217, by rfl⟩ : syracuseStep 1449623 = 2174435) B2174435
theorem B859799 : Blo 858357 859799 := bstep (se 1 (by rfl) ⟨644849, by rfl⟩ : syracuseStep 859799 = 1289699) B1289699
theorem B859819 : Blo 858357 859819 := bstep (se 1 (by rfl) ⟨644864, by rfl⟩ : syracuseStep 859819 = 1289729) B1289729
theorem B2612915 : Blo 858357 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B859831 : Blo 858357 859831 := bstep (se 1 (by rfl) ⟨644873, by rfl⟩ : syracuseStep 859831 = 1289747) B1289747
theorem B859851 : Blo 858357 859851 := bstep (se 1 (by rfl) ⟨644888, by rfl⟩ : syracuseStep 859851 = 1289777) B1289777
theorem B859863 : Blo 858357 859863 := bstep (se 1 (by rfl) ⟨644897, by rfl⟩ : syracuseStep 859863 = 1289795) B1289795
theorem B966379 : Blo 858357 966379 := bstep (se 1 (by rfl) ⟨724784, by rfl⟩ : syracuseStep 966379 = 1449569) B1449569
theorem B859883 : Blo 858357 859883 := bstep (se 1 (by rfl) ⟨644912, by rfl⟩ : syracuseStep 859883 = 1289825) B1289825
theorem B859895 : Blo 858357 859895 := bstep (se 1 (by rfl) ⟨644921, by rfl⟩ : syracuseStep 859895 = 1289843) B1289843
theorem B1629953 : Blo 858357 1629953 := bstep (se 2 (by rfl) ⟨611232, by rfl⟩ : syracuseStep 1629953 = 1222465) B1222465
theorem B859915 : Blo 858357 859915 := bstep (se 1 (by rfl) ⟨644936, by rfl⟩ : syracuseStep 859915 = 1289873) B1289873
theorem B1449751 : Blo 858357 1449751 := bstep (se 1 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 1449751 = 2174627) B2174627
theorem B859927 : Blo 858357 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B859947 : Blo 858357 859947 := bstep (se 1 (by rfl) ⟨644960, by rfl⟩ : syracuseStep 859947 = 1289921) B1289921
theorem B2064179 : Blo 858357 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B859959 : Blo 858357 859959 := bstep (se 1 (by rfl) ⟨644969, by rfl⟩ : syracuseStep 859959 = 1289939) B1289939
theorem B9674561 : Blo 858357 9674561 := bstep (se 2 (by rfl) ⟨3627960, by rfl⟩ : syracuseStep 9674561 = 7255921) B7255921
theorem B859979 : Blo 858357 859979 := bstep (se 1 (by rfl) ⟨644984, by rfl⟩ : syracuseStep 859979 = 1289969) B1289969
theorem B966487 : Blo 858357 966487 := bstep (se 1 (by rfl) ⟨724865, by rfl⟩ : syracuseStep 966487 = 1449731) B1449731
theorem B2064217 : Blo 858357 2064217 := bstep (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) B1548163
theorem B1933145 : Blo 858357 1933145 := bstep (se 2 (by rfl) ⟨724929, by rfl⟩ : syracuseStep 1933145 = 1449859) B1449859
theorem B859991 : Blo 858357 859991 := bstep (se 1 (by rfl) ⟨644993, by rfl⟩ : syracuseStep 859991 = 1289987) B1289987
theorem B5504861 : Blo 858357 5504861 := bstep (se 3 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 5504861 = 2064323) B2064323
theorem B860011 : Blo 858357 860011 := bstep (se 1 (by rfl) ⟨645008, by rfl⟩ : syracuseStep 860011 = 1290017) B1290017
theorem B860023 : Blo 858357 860023 := bstep (se 1 (by rfl) ⟨645017, by rfl⟩ : syracuseStep 860023 = 1290035) B1290035
theorem B860043 : Blo 858357 860043 := bstep (se 1 (by rfl) ⟨645032, by rfl⟩ : syracuseStep 860043 = 1290065) B1290065
theorem B4186007 : Blo 858357 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B860055 : Blo 858357 860055 := bstep (se 1 (by rfl) ⟨645041, by rfl⟩ : syracuseStep 860055 = 1290083) B1290083
theorem B860075 : Blo 858357 860075 := bstep (se 1 (by rfl) ⟨645056, by rfl⟩ : syracuseStep 860075 = 1290113) B1290113
theorem B1933235 : Blo 858357 1933235 := bstep (se 1 (by rfl) ⟨1449926, by rfl⟩ : syracuseStep 1933235 = 2899853) B2899853
theorem B860087 : Blo 858357 860087 := bstep (se 1 (by rfl) ⟨645065, by rfl⟩ : syracuseStep 860087 = 1290131) B1290131
theorem B860107 : Blo 858357 860107 := bstep (se 1 (by rfl) ⟨645080, by rfl⟩ : syracuseStep 860107 = 1290161) B1290161
theorem B1933271 : Blo 858357 1933271 := bstep (se 1 (by rfl) ⟨1449953, by rfl⟩ : syracuseStep 1933271 = 2899907) B2899907
theorem B4186073 : Blo 858357 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B860119 : Blo 858357 860119 := bstep (se 1 (by rfl) ⟨645089, by rfl⟩ : syracuseStep 860119 = 1290179) B1290179
theorem B860139 : Blo 858357 860139 := bstep (se 1 (by rfl) ⟨645104, by rfl⟩ : syracuseStep 860139 = 1290209) B1290209
theorem B860151 : Blo 858357 860151 := bstep (se 1 (by rfl) ⟨645113, by rfl⟩ : syracuseStep 860151 = 1290227) B1290227
theorem B860167 : Blo 858357 860167 := bstep (se 1 (by rfl) ⟨645125, by rfl⟩ : syracuseStep 860167 = 1290251) B1290251
theorem B860175 : Blo 858357 860175 := bstep (se 1 (by rfl) ⟨645131, by rfl⟩ : syracuseStep 860175 = 1290263) B1290263
theorem B860219 : Blo 858357 860219 := bstep (se 1 (by rfl) ⟨645164, by rfl⟩ : syracuseStep 860219 = 1290329) B1290329
theorem B3260483 : Blo 858357 3260483 := bstep (se 1 (by rfl) ⟨2445362, by rfl⟩ : syracuseStep 3260483 = 4890725) B4890725
theorem B860295 : Blo 858357 860295 := bstep (se 1 (by rfl) ⟨645221, by rfl⟩ : syracuseStep 860295 = 1290443) B1290443
theorem B860303 : Blo 858357 860303 := bstep (se 1 (by rfl) ⟨645227, by rfl⟩ : syracuseStep 860303 = 1290455) B1290455
theorem B860347 : Blo 858357 860347 := bstep (se 1 (by rfl) ⟨645260, by rfl⟩ : syracuseStep 860347 = 1290521) B1290521
theorem B966919 : Blo 858357 966919 := bstep (se 1 (by rfl) ⟨725189, by rfl⟩ : syracuseStep 966919 = 1450379) B1450379
theorem B860423 : Blo 858357 860423 := bstep (se 1 (by rfl) ⟨645317, by rfl⟩ : syracuseStep 860423 = 1290635) B1290635
theorem B860431 : Blo 858357 860431 := bstep (se 1 (by rfl) ⟨645323, by rfl⟩ : syracuseStep 860431 = 1290647) B1290647
theorem B6521147 : Blo 858357 6521147 := bstep (se 1 (by rfl) ⟨4890860, by rfl⟩ : syracuseStep 6521147 = 9781721) B9781721
theorem B1630523 : Blo 858357 1630523 := bstep (se 1 (by rfl) ⟨1222892, by rfl⟩ : syracuseStep 1630523 = 2445785) B2445785
theorem B6275387 : Blo 858357 6275387 := bstep (se 1 (by rfl) ⟨4706540, by rfl⟩ : syracuseStep 6275387 = 9413081) B9413081
theorem B860475 : Blo 858357 860475 := bstep (se 1 (by rfl) ⟨645356, by rfl⟩ : syracuseStep 860475 = 1290713) B1290713
theorem B3096947 : Blo 858357 3096947 := bstep (se 1 (by rfl) ⟨2322710, by rfl⟩ : syracuseStep 3096947 = 4645421) B4645421
theorem B2900339 : Blo 858357 2900339 := bstep (se 1 (by rfl) ⟨2175254, by rfl⟩ : syracuseStep 2900339 = 4350509) B4350509
theorem B1933703 : Blo 858357 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B860551 : Blo 858357 860551 := bstep (se 1 (by rfl) ⟨645413, by rfl⟩ : syracuseStep 860551 = 1290827) B1290827
theorem B860559 : Blo 858357 860559 := bstep (se 1 (by rfl) ⟨645419, by rfl⟩ : syracuseStep 860559 = 1290839) B1290839
theorem B967099 : Blo 858357 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B1933883 : Blo 858357 1933883 := bstep (se 1 (by rfl) ⟨1450412, by rfl⟩ : syracuseStep 1933883 = 2900825) B2900825
theorem B1958519 : Blo 858357 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B1450615 : Blo 858357 1450615 := bstep (se 1 (by rfl) ⟨1087961, by rfl⟩ : syracuseStep 1450615 = 2175923) B2175923
theorem B1934009 : Blo 858357 1934009 := bstep (se 2 (by rfl) ⟨725253, by rfl⟩ : syracuseStep 1934009 = 1450507) B1450507
theorem B4645613 : Blo 858357 4645613 := bstep (se 3 (by rfl) ⟨871052, by rfl⟩ : syracuseStep 4645613 = 1742105) B1742105
theorem B1631009 : Blo 858357 1631009 := bstep (se 2 (by rfl) ⟨611628, by rfl⟩ : syracuseStep 1631009 = 1223257) B1223257
theorem B9290531 : Blo 858357 9290531 := bstep (se 1 (by rfl) ⟨6967898, by rfl⟩ : syracuseStep 9290531 = 13935797) B13935797
theorem B1450811 : Blo 858357 1450811 := bstep (se 1 (by rfl) ⟨1088108, by rfl⟩ : syracuseStep 1450811 = 2176217) B2176217
theorem B967567 : Blo 858357 967567 := bstep (se 1 (by rfl) ⟨725675, by rfl⟩ : syracuseStep 967567 = 1451351) B1451351
theorem B2483129 : Blo 858357 2483129 := bstep (se 2 (by rfl) ⟨931173, by rfl⟩ : syracuseStep 2483129 = 1862347) B1862347
theorem B2065409 : Blo 858357 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B9790469 : Blo 858357 9790469 := bstep (se 4 (by rfl) ⟨917856, by rfl⟩ : syracuseStep 9790469 = 1835713) B1835713
theorem B1836047 : Blo 858357 1836047 := bstep (se 1 (by rfl) ⟨1377035, by rfl⟩ : syracuseStep 1836047 = 2754071) B2754071
theorem B1934351 : Blo 858357 1934351 := bstep (se 1 (by rfl) ⟨1450763, by rfl⟩ : syracuseStep 1934351 = 2901527) B2901527
theorem B1934369 : Blo 858357 1934369 := bstep (se 2 (by rfl) ⟨725388, by rfl⟩ : syracuseStep 1934369 = 1450777) B1450777
theorem B1451209 : Blo 858357 1451209 := bstep (se 2 (by rfl) ⟨544203, by rfl⟩ : syracuseStep 1451209 = 1088407) B1088407
theorem B3097871 : Blo 858357 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B2237755 : Blo 858357 2237755 := bstep (se 1 (by rfl) ⟨1678316, by rfl⟩ : syracuseStep 2237755 = 3356633) B3356633
theorem B1934711 : Blo 858357 1934711 := bstep (se 1 (by rfl) ⟨1451033, by rfl⟩ : syracuseStep 1934711 = 2902067) B2902067
theorem B968071 : Blo 858357 968071 := bstep (se 1 (by rfl) ⟨726053, by rfl⟩ : syracuseStep 968071 = 1452107) B1452107
theorem B1287611 : Blo 858357 1287611 := bstep (se 1 (by rfl) ⟨965708, by rfl⟩ : syracuseStep 1287611 = 1931417) B1931417
theorem B1287671 : Blo 858357 1287671 := bstep (se 1 (by rfl) ⟨965753, by rfl⟩ : syracuseStep 1287671 = 1931507) B1931507
theorem B3671563 : Blo 858357 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B1287695 : Blo 858357 1287695 := bstep (se 1 (by rfl) ⟨965771, by rfl⟩ : syracuseStep 1287695 = 1931543) B1931543
theorem B4892183 : Blo 858357 4892183 := bstep (se 1 (by rfl) ⟨3669137, by rfl⟩ : syracuseStep 4892183 = 7338275) B7338275
theorem B1934891 : Blo 858357 1934891 := bstep (se 1 (by rfl) ⟨1451168, by rfl⟩ : syracuseStep 1934891 = 2902337) B2902337
theorem B1287737 : Blo 858357 1287737 := bstep (se 2 (by rfl) ⟨482901, by rfl⟩ : syracuseStep 1287737 = 965803) B965803
theorem B1287815 : Blo 858357 1287815 := bstep (se 1 (by rfl) ⟨965861, by rfl⟩ : syracuseStep 1287815 = 1931723) B1931723
theorem B1287851 : Blo 858357 1287851 := bstep (se 1 (by rfl) ⟨965888, by rfl⟩ : syracuseStep 1287851 = 1931777) B1931777
theorem B1550009 : Blo 858357 1550009 := bstep (se 2 (by rfl) ⟨581253, by rfl⟩ : syracuseStep 1550009 = 1162507) B1162507
theorem B1377977 : Blo 858357 1377977 := bstep (se 2 (by rfl) ⟨516741, by rfl⟩ : syracuseStep 1377977 = 1033483) B1033483
theorem B1287881 : Blo 858357 1287881 := bstep (se 2 (by rfl) ⟨482955, by rfl⟩ : syracuseStep 1287881 = 965911) B965911
theorem B3262153 : Blo 858357 3262153 := bstep (se 2 (by rfl) ⟨1223307, by rfl⟩ : syracuseStep 3262153 = 2446615) B2446615
theorem B1222391 : Blo 858357 1222391 := bstep (se 1 (by rfl) ⟨916793, by rfl⟩ : syracuseStep 1222391 = 1833587) B1833587
theorem B6530867 : Blo 858357 6530867 := bstep (se 1 (by rfl) ⟨4898150, by rfl⟩ : syracuseStep 6530867 = 9796301) B9796301
theorem B1287995 : Blo 858357 1287995 := bstep (se 1 (by rfl) ⟨965996, by rfl⟩ : syracuseStep 1287995 = 1931993) B1931993
theorem B1288055 : Blo 858357 1288055 := bstep (se 1 (by rfl) ⟨966041, by rfl⟩ : syracuseStep 1288055 = 1932083) B1932083
theorem B1451911 : Blo 858357 1451911 := bstep (se 1 (by rfl) ⟨1088933, by rfl⟩ : syracuseStep 1451911 = 2177867) B2177867
theorem B1288079 : Blo 858357 1288079 := bstep (se 1 (by rfl) ⟨966059, by rfl⟩ : syracuseStep 1288079 = 1932119) B1932119
theorem B2066323 : Blo 858357 2066323 := bstep (se 1 (by rfl) ⟨1549742, by rfl⟩ : syracuseStep 2066323 = 3099485) B3099485
theorem B1935251 : Blo 858357 1935251 := bstep (se 1 (by rfl) ⟨1451438, by rfl⟩ : syracuseStep 1935251 = 2902877) B2902877
theorem B8259479 : Blo 858357 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B1288121 : Blo 858357 1288121 := bstep (se 2 (by rfl) ⟨483045, by rfl⟩ : syracuseStep 1288121 = 966091) B966091
theorem B2615225 : Blo 858357 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B1935305 : Blo 858357 1935305 := bstep (se 2 (by rfl) ⟨725739, by rfl⟩ : syracuseStep 1935305 = 1451479) B1451479
theorem B1288199 : Blo 858357 1288199 := bstep (se 1 (by rfl) ⟨966149, by rfl⟩ : syracuseStep 1288199 = 1932299) B1932299
theorem B4892683 : Blo 858357 4892683 := bstep (se 1 (by rfl) ⟨3669512, by rfl⟩ : syracuseStep 4892683 = 7339025) B7339025
theorem B1288235 : Blo 858357 1288235 := bstep (se 1 (by rfl) ⟨966176, by rfl⟩ : syracuseStep 1288235 = 1932353) B1932353
theorem B4900931 : Blo 858357 4900931 := bstep (se 1 (by rfl) ⟨3675698, by rfl⟩ : syracuseStep 4900931 = 7351397) B7351397
theorem B1288265 : Blo 858357 1288265 := bstep (se 2 (by rfl) ⟨483099, by rfl⟩ : syracuseStep 1288265 = 966199) B966199
theorem B6973613 : Blo 858357 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B1288379 : Blo 858357 1288379 := bstep (se 1 (by rfl) ⟨966284, by rfl⟩ : syracuseStep 1288379 = 1932569) B1932569
theorem B1288439 : Blo 858357 1288439 := bstep (se 1 (by rfl) ⟨966329, by rfl⟩ : syracuseStep 1288439 = 1932659) B1932659
theorem B1288463 : Blo 858357 1288463 := bstep (se 1 (by rfl) ⟨966347, by rfl⟩ : syracuseStep 1288463 = 1932695) B1932695
theorem B1288505 : Blo 858357 1288505 := bstep (se 2 (by rfl) ⟨483189, by rfl⟩ : syracuseStep 1288505 = 966379) B966379
theorem B4647257 : Blo 858357 4647257 := bstep (se 2 (by rfl) ⟨1742721, by rfl⟩ : syracuseStep 4647257 = 3485443) B3485443
theorem B1288583 : Blo 858357 1288583 := bstep (se 1 (by rfl) ⟨966437, by rfl⟩ : syracuseStep 1288583 = 1932875) B1932875
theorem B8251793 : Blo 858357 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B2173331 : Blo 858357 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B1288619 : Blo 858357 1288619 := bstep (se 1 (by rfl) ⟨966464, by rfl⟩ : syracuseStep 1288619 = 1932929) B1932929
theorem B1288649 : Blo 858357 1288649 := bstep (se 2 (by rfl) ⟨483243, by rfl⟩ : syracuseStep 1288649 = 966487) B966487
theorem B7350749 : Blo 858357 7350749 := bstep (se 3 (by rfl) ⟨1378265, by rfl⟩ : syracuseStep 7350749 = 2756531) B2756531
theorem B14125553 : Blo 858357 14125553 := bstep (se 2 (by rfl) ⟨5297082, by rfl⟩ : syracuseStep 14125553 = 10594165) B10594165
theorem B6449707 : Blo 858357 6449707 := bstep (se 1 (by rfl) ⟨4837280, by rfl⟩ : syracuseStep 6449707 = 9674561) B9674561
theorem B1288763 : Blo 858357 1288763 := bstep (se 1 (by rfl) ⟨966572, by rfl⟩ : syracuseStep 1288763 = 1933145) B1933145
theorem B5294711 : Blo 858357 5294711 := bstep (se 1 (by rfl) ⟨3971033, by rfl⟩ : syracuseStep 5294711 = 7942067) B7942067
theorem B1288823 : Blo 858357 1288823 := bstep (se 1 (by rfl) ⟨966617, by rfl⟩ : syracuseStep 1288823 = 1933235) B1933235
theorem B1936007 : Blo 858357 1936007 := bstep (se 1 (by rfl) ⟨1452005, by rfl⟩ : syracuseStep 1936007 = 2904011) B2904011
theorem B1288847 : Blo 858357 1288847 := bstep (se 1 (by rfl) ⟨966635, by rfl⟩ : syracuseStep 1288847 = 1933271) B1933271
theorem B2173625 : Blo 858357 2173625 := bstep (se 2 (by rfl) ⟨815109, by rfl⟩ : syracuseStep 2173625 = 1630219) B1630219
theorem B1223353 : Blo 858357 1223353 := bstep (se 2 (by rfl) ⟨458757, by rfl⟩ : syracuseStep 1223353 = 917515) B917515
theorem B1288889 : Blo 858357 1288889 := bstep (se 2 (by rfl) ⟨483333, by rfl⟩ : syracuseStep 1288889 = 966667) B966667
theorem B1632953 : Blo 858357 1632953 := bstep (se 2 (by rfl) ⟨612357, by rfl⟩ : syracuseStep 1632953 = 1224715) B1224715
theorem B1288967 : Blo 858357 1288967 := bstep (se 1 (by rfl) ⟨966725, by rfl⟩ : syracuseStep 1288967 = 1933451) B1933451
theorem B1289003 : Blo 858357 1289003 := bstep (se 1 (by rfl) ⟨966752, by rfl⟩ : syracuseStep 1289003 = 1933505) B1933505
theorem B1936187 : Blo 858357 1936187 := bstep (se 1 (by rfl) ⟨1452140, by rfl⟩ : syracuseStep 1936187 = 2904281) B2904281
theorem B1289033 : Blo 858357 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B5499737 : Blo 858357 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B2902931 : Blo 858357 2902931 := bstep (se 1 (by rfl) ⟨2177198, by rfl⟩ : syracuseStep 2902931 = 4354397) B4354397
theorem B1289147 : Blo 858357 1289147 := bstep (se 1 (by rfl) ⟨966860, by rfl⟩ : syracuseStep 1289147 = 1933721) B1933721
theorem B1289207 : Blo 858357 1289207 := bstep (se 1 (by rfl) ⟨966905, by rfl⟩ : syracuseStep 1289207 = 1933811) B1933811
theorem B2321423 : Blo 858357 2321423 := bstep (se 1 (by rfl) ⟨1741067, by rfl⟩ : syracuseStep 2321423 = 3482135) B3482135
theorem B1223695 : Blo 858357 1223695 := bstep (se 1 (by rfl) ⟨917771, by rfl⟩ : syracuseStep 1223695 = 1835543) B1835543
theorem B1289231 : Blo 858357 1289231 := bstep (se 1 (by rfl) ⟨966923, by rfl⟩ : syracuseStep 1289231 = 1933847) B1933847
theorem B1289273 : Blo 858357 1289273 := bstep (se 2 (by rfl) ⟨483477, by rfl⟩ : syracuseStep 1289273 = 966955) B966955
theorem B1240183 : Blo 858357 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B1289351 : Blo 858357 1289351 := bstep (se 1 (by rfl) ⟨967013, by rfl⟩ : syracuseStep 1289351 = 1934027) B1934027
theorem B1289387 : Blo 858357 1289387 := bstep (se 1 (by rfl) ⟨967040, by rfl⟩ : syracuseStep 1289387 = 1934081) B1934081
theorem B5508269 : Blo 858357 5508269 := bstep (se 3 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 5508269 = 2065601) B2065601
theorem B1289417 : Blo 858357 1289417 := bstep (se 2 (by rfl) ⟨483531, by rfl⟩ : syracuseStep 1289417 = 967063) B967063
theorem B4648207 : Blo 858357 4648207 := bstep (se 1 (by rfl) ⟨3486155, by rfl⟩ : syracuseStep 4648207 = 6972311) B6972311
theorem B3534113 : Blo 858357 3534113 := bstep (se 2 (by rfl) ⟨1325292, by rfl⟩ : syracuseStep 3534113 = 2650585) B2650585
theorem B1289531 : Blo 858357 1289531 := bstep (se 1 (by rfl) ⟨967148, by rfl⟩ : syracuseStep 1289531 = 1934297) B1934297
theorem B2174323 : Blo 858357 2174323 := bstep (se 1 (by rfl) ⟨1630742, by rfl⟩ : syracuseStep 2174323 = 3261485) B3261485
theorem B1289591 : Blo 858357 1289591 := bstep (se 1 (by rfl) ⟨967193, by rfl⟩ : syracuseStep 1289591 = 1934387) B1934387
theorem B1289615 : Blo 858357 1289615 := bstep (se 1 (by rfl) ⟨967211, by rfl⟩ : syracuseStep 1289615 = 1934423) B1934423
theorem B4353425 : Blo 858357 4353425 := bstep (se 2 (by rfl) ⟨1632534, by rfl⟩ : syracuseStep 4353425 = 3265069) B3265069
theorem B1740217 : Blo 858357 1740217 := bstep (se 2 (by rfl) ⟨652581, by rfl⟩ : syracuseStep 1740217 = 1305163) B1305163
theorem B1289657 : Blo 858357 1289657 := bstep (se 2 (by rfl) ⟨483621, by rfl⟩ : syracuseStep 1289657 = 967243) B967243
theorem B2174465 : Blo 858357 2174465 := bstep (se 2 (by rfl) ⟨815424, by rfl⟩ : syracuseStep 2174465 = 1630849) B1630849
theorem B1289735 : Blo 858357 1289735 := bstep (se 1 (by rfl) ⟨967301, by rfl⟩ : syracuseStep 1289735 = 1934603) B1934603
theorem B3100189 : Blo 858357 3100189 := bstep (se 3 (by rfl) ⟨581285, by rfl⟩ : syracuseStep 3100189 = 1162571) B1162571
theorem B1289771 : Blo 858357 1289771 := bstep (se 1 (by rfl) ⟨967328, by rfl⟩ : syracuseStep 1289771 = 1934657) B1934657
theorem B1289801 : Blo 858357 1289801 := bstep (se 2 (by rfl) ⟨483675, by rfl⟩ : syracuseStep 1289801 = 967351) B967351
theorem B1289915 : Blo 858357 1289915 := bstep (se 1 (by rfl) ⟨967436, by rfl⟩ : syracuseStep 1289915 = 1934873) B1934873
theorem B1289975 : Blo 858357 1289975 := bstep (se 1 (by rfl) ⟨967481, by rfl⟩ : syracuseStep 1289975 = 1934963) B1934963
theorem B1289999 : Blo 858357 1289999 := bstep (se 1 (by rfl) ⟨967499, by rfl⟩ : syracuseStep 1289999 = 1934999) B1934999
theorem B1290041 : Blo 858357 1290041 := bstep (se 2 (by rfl) ⟨483765, by rfl⟩ : syracuseStep 1290041 = 967531) B967531
theorem B3264371 : Blo 858357 3264371 := bstep (se 1 (by rfl) ⟨2448278, by rfl⟩ : syracuseStep 3264371 = 4896557) B4896557
theorem B1290119 : Blo 858357 1290119 := bstep (se 1 (by rfl) ⟨967589, by rfl⟩ : syracuseStep 1290119 = 1935179) B1935179
theorem B2445203 : Blo 858357 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B1290155 : Blo 858357 1290155 := bstep (se 1 (by rfl) ⟨967616, by rfl⟩ : syracuseStep 1290155 = 1935233) B1935233
theorem B929723 : Blo 858357 929723 := bstep (se 1 (by rfl) ⟨697292, by rfl⟩ : syracuseStep 929723 = 1394585) B1394585
theorem B2174921 : Blo 858357 2174921 := bstep (se 2 (by rfl) ⟨815595, by rfl⟩ : syracuseStep 2174921 = 1631191) B1631191
theorem B1290185 : Blo 858357 1290185 := bstep (se 2 (by rfl) ⟨483819, by rfl⟩ : syracuseStep 1290185 = 967639) B967639
theorem B4894667 : Blo 858357 4894667 := bstep (se 1 (by rfl) ⟨3671000, by rfl⟩ : syracuseStep 4894667 = 7342001) B7342001
theorem B1290299 : Blo 858357 1290299 := bstep (se 1 (by rfl) ⟨967724, by rfl⟩ : syracuseStep 1290299 = 1935449) B1935449
theorem B1224823 : Blo 858357 1224823 := bstep (se 1 (by rfl) ⟨918617, by rfl⟩ : syracuseStep 1224823 = 1837235) B1837235
theorem B1290359 : Blo 858357 1290359 := bstep (se 1 (by rfl) ⟨967769, by rfl⟩ : syracuseStep 1290359 = 1935539) B1935539
theorem B1290383 : Blo 858357 1290383 := bstep (se 1 (by rfl) ⟨967787, by rfl⟩ : syracuseStep 1290383 = 1935575) B1935575
theorem B1290425 : Blo 858357 1290425 := bstep (se 2 (by rfl) ⟨483909, by rfl⟩ : syracuseStep 1290425 = 967819) B967819
theorem B1290503 : Blo 858357 1290503 := bstep (se 1 (by rfl) ⟨967877, by rfl⟩ : syracuseStep 1290503 = 1935755) B1935755
theorem B2904335 : Blo 858357 2904335 := bstep (se 1 (by rfl) ⟨2178251, by rfl⟩ : syracuseStep 2904335 = 4356503) B4356503
theorem B2175275 : Blo 858357 2175275 := bstep (se 1 (by rfl) ⟨1631456, by rfl⟩ : syracuseStep 2175275 = 3262913) B3262913
theorem B1290539 : Blo 858357 1290539 := bstep (se 1 (by rfl) ⟨967904, by rfl⟩ : syracuseStep 1290539 = 1935809) B1935809
theorem B1290569 : Blo 858357 1290569 := bstep (se 2 (by rfl) ⟨483963, by rfl⟩ : syracuseStep 1290569 = 967927) B967927
theorem B4706695 : Blo 858357 4706695 := bstep (se 1 (by rfl) ⟨3530021, by rfl⟩ : syracuseStep 4706695 = 7060043) B7060043
theorem B4346297 : Blo 858357 4346297 := bstep (se 2 (by rfl) ⟨1629861, by rfl⟩ : syracuseStep 4346297 = 3259723) B3259723
theorem B1307065 : Blo 858357 1307065 := bstep (se 2 (by rfl) ⟨490149, by rfl⟩ : syracuseStep 1307065 = 980299) B980299
theorem B1290683 : Blo 858357 1290683 := bstep (se 1 (by rfl) ⟨968012, by rfl⟩ : syracuseStep 1290683 = 1936025) B1936025
theorem B1290743 : Blo 858357 1290743 := bstep (se 1 (by rfl) ⟨968057, by rfl⟩ : syracuseStep 1290743 = 1936115) B1936115
theorem B1290767 : Blo 858357 1290767 := bstep (se 1 (by rfl) ⟨968075, by rfl⟩ : syracuseStep 1290767 = 1936151) B1936151
theorem B1290809 : Blo 858357 1290809 := bstep (se 2 (by rfl) ⟨484053, by rfl⟩ : syracuseStep 1290809 = 968107) B968107
theorem B3920503 : Blo 858357 3920503 := bstep (se 1 (by rfl) ⟨2940377, by rfl⟩ : syracuseStep 3920503 = 5880755) B5880755
theorem B54317699 : Blo 858357 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B2445977 : Blo 858357 2445977 := bstep (se 2 (by rfl) ⟨917241, by rfl⟩ : syracuseStep 2445977 = 1834483) B1834483
theorem B2511703 : Blo 858357 2511703 := bstep (se 1 (by rfl) ⟨1883777, by rfl⟩ : syracuseStep 2511703 = 3767555) B3767555
theorem B3142547 : Blo 858357 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B6968227 : Blo 858357 6968227 := bstep (se 1 (by rfl) ⟨5226170, by rfl⟩ : syracuseStep 6968227 = 10452341) B10452341
theorem B3535825 : Blo 858357 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B1741943 : Blo 858357 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B1086635 : Blo 858357 1086635 := bstep (se 1 (by rfl) ⟨814976, by rfl⟩ : syracuseStep 1086635 = 1629953) B1629953
theorem B2897153 : Blo 858357 2897153 := bstep (se 2 (by rfl) ⟨1086432, by rfl⟩ : syracuseStep 2897153 = 2172865) B2172865
theorem B2176267 : Blo 858357 2176267 := bstep (se 1 (by rfl) ⟨1632200, by rfl⟩ : syracuseStep 2176267 = 3264401) B3264401
theorem B2790671 : Blo 858357 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B7337249 : Blo 858357 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B2790715 : Blo 858357 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B16504195 : Blo 858357 16504195 := bstep (se 1 (by rfl) ⟨12378146, by rfl⟩ : syracuseStep 16504195 = 24756293) B24756293
theorem B3675527 : Blo 858357 3675527 := bstep (se 1 (by rfl) ⟨2756645, by rfl⟩ : syracuseStep 3675527 = 5513291) B5513291
theorem B2176409 : Blo 858357 2176409 := bstep (se 2 (by rfl) ⟨816153, by rfl⟩ : syracuseStep 2176409 = 1632307) B1632307
theorem B4355531 : Blo 858357 4355531 := bstep (se 1 (by rfl) ⟨3266648, by rfl⟩ : syracuseStep 4355531 = 6533297) B6533297
theorem B6526493 : Blo 858357 6526493 := bstep (se 3 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 6526493 = 2447435) B2447435
theorem B4404779 : Blo 858357 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B2176571 : Blo 858357 2176571 := bstep (se 1 (by rfl) ⟨1632428, by rfl⟩ : syracuseStep 2176571 = 3264857) B3264857
theorem B1087111 : Blo 858357 1087111 := bstep (se 1 (by rfl) ⟨815333, by rfl⟩ : syracuseStep 1087111 = 1630667) B1630667
theorem B980623 : Blo 858357 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B4347593 : Blo 858357 4347593 := bstep (se 2 (by rfl) ⟨1630347, by rfl⟩ : syracuseStep 4347593 = 3260695) B3260695
theorem B4355855 : Blo 858357 4355855 := bstep (se 1 (by rfl) ⟨3266891, by rfl⟩ : syracuseStep 4355855 = 6533783) B6533783
theorem B4650803 : Blo 858357 4650803 := bstep (se 1 (by rfl) ⟨3488102, by rfl⟩ : syracuseStep 4650803 = 6976205) B6976205
theorem B3921779 : Blo 858357 3921779 := bstep (se 1 (by rfl) ⟨2941334, by rfl⟩ : syracuseStep 3921779 = 5882669) B5882669
theorem B2094983 : Blo 858357 2094983 := bstep (se 1 (by rfl) ⟨1571237, by rfl⟩ : syracuseStep 2094983 = 3142475) B3142475
theorem B2176915 : Blo 858357 2176915 := bstep (se 1 (by rfl) ⟨1632686, by rfl⟩ : syracuseStep 2176915 = 3265373) B3265373
theorem B3266513 : Blo 858357 3266513 := bstep (se 2 (by rfl) ⟨1224942, by rfl⟩ : syracuseStep 3266513 = 2449885) B2449885
theorem B6273047 : Blo 858357 6273047 := bstep (se 1 (by rfl) ⟨4704785, by rfl⟩ : syracuseStep 6273047 = 9409571) B9409571
theorem B2177057 : Blo 858357 2177057 := bstep (se 2 (by rfl) ⟨816396, by rfl⟩ : syracuseStep 2177057 = 1632793) B1632793
theorem B2897963 : Blo 858357 2897963 := bstep (se 1 (by rfl) ⟨2173472, by rfl⟩ : syracuseStep 2897963 = 4346945) B4346945
theorem B1103915 : Blo 858357 1103915 := bstep (se 1 (by rfl) ⟨827936, by rfl⟩ : syracuseStep 1103915 = 1655873) B1655873
theorem B1087607 : Blo 858357 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B1931399 : Blo 858357 1931399 := bstep (se 1 (by rfl) ⟨1448549, by rfl⟩ : syracuseStep 1931399 = 2897099) B2897099
theorem B858375 : Blo 858357 858375 := bstep (se 1 (by rfl) ⟨643781, by rfl⟩ : syracuseStep 858375 = 1287563) B1287563
theorem B858383 : Blo 858357 858383 := bstep (se 1 (by rfl) ⟨643787, by rfl⟩ : syracuseStep 858383 = 1287575) B1287575
theorem B1087759 : Blo 858357 1087759 := bstep (se 1 (by rfl) ⟨815819, by rfl⟩ : syracuseStep 1087759 = 1631639) B1631639
theorem B3266831 : Blo 858357 3266831 := bstep (se 1 (by rfl) ⟨2450123, by rfl⟩ : syracuseStep 3266831 = 4900247) B4900247
theorem B4897057 : Blo 858357 4897057 := bstep (se 2 (by rfl) ⟨1836396, by rfl⟩ : syracuseStep 4897057 = 3672793) B3672793
theorem B858427 : Blo 858357 858427 := bstep (se 1 (by rfl) ⟨643820, by rfl⟩ : syracuseStep 858427 = 1287641) B1287641
theorem B1931579 : Blo 858357 1931579 := bstep (se 1 (by rfl) ⟨1448684, by rfl⟩ : syracuseStep 1931579 = 2897369) B2897369
theorem B858503 : Blo 858357 858503 := bstep (se 1 (by rfl) ⟨643877, by rfl⟩ : syracuseStep 858503 = 1287755) B1287755
theorem B858511 : Blo 858357 858511 := bstep (se 1 (by rfl) ⟨643883, by rfl⟩ : syracuseStep 858511 = 1287767) B1287767
theorem B6371731 : Blo 858357 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B1931705 : Blo 858357 1931705 := bstep (se 2 (by rfl) ⟨724389, by rfl⟩ : syracuseStep 1931705 = 1448779) B1448779
theorem B858555 : Blo 858357 858555 := bstep (se 1 (by rfl) ⟨643916, by rfl⟩ : syracuseStep 858555 = 1287833) B1287833
theorem B1087931 : Blo 858357 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B858631 : Blo 858357 858631 := bstep (se 1 (by rfl) ⟨643973, by rfl⟩ : syracuseStep 858631 = 1287947) B1287947
theorem B858639 : Blo 858357 858639 := bstep (se 1 (by rfl) ⟨643979, by rfl⟩ : syracuseStep 858639 = 1287959) B1287959
theorem B858683 : Blo 858357 858683 := bstep (se 1 (by rfl) ⟨644012, by rfl⟩ : syracuseStep 858683 = 1288025) B1288025
theorem B3095101 : Blo 858357 3095101 := bstep (se 3 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 3095101 = 1160663) B1160663
theorem B858759 : Blo 858357 858759 := bstep (se 1 (by rfl) ⟨644069, by rfl⟩ : syracuseStep 858759 = 1288139) B1288139
theorem B858767 : Blo 858357 858767 := bstep (se 1 (by rfl) ⟨644075, by rfl⟩ : syracuseStep 858767 = 1288151) B1288151
theorem B858811 : Blo 858357 858811 := bstep (se 1 (by rfl) ⟨644108, by rfl⟩ : syracuseStep 858811 = 1288217) B1288217
theorem B2448073 : Blo 858357 2448073 := bstep (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) B1836055
theorem B858887 : Blo 858357 858887 := bstep (se 1 (by rfl) ⟨644165, by rfl⟩ : syracuseStep 858887 = 1288331) B1288331
theorem B1932047 : Blo 858357 1932047 := bstep (se 1 (by rfl) ⟨1449035, by rfl⟩ : syracuseStep 1932047 = 2898071) B2898071
theorem B858895 : Blo 858357 858895 := bstep (se 1 (by rfl) ⟨644171, by rfl⟩ : syracuseStep 858895 = 1288343) B1288343
theorem B1932065 : Blo 858357 1932065 := bstep (se 2 (by rfl) ⟨724524, by rfl⟩ : syracuseStep 1932065 = 1449049) B1449049
theorem B858939 : Blo 858357 858939 := bstep (se 1 (by rfl) ⟨644204, by rfl⟩ : syracuseStep 858939 = 1288409) B1288409
theorem B5503859 : Blo 858357 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B2751367 : Blo 858357 2751367 := bstep (se 1 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 2751367 = 4127051) B4127051
theorem B859015 : Blo 858357 859015 := bstep (se 1 (by rfl) ⟨644261, by rfl⟩ : syracuseStep 859015 = 1288523) B1288523
theorem B859023 : Blo 858357 859023 := bstep (se 1 (by rfl) ⟨644267, by rfl⟩ : syracuseStep 859023 = 1288535) B1288535
theorem B2792339 : Blo 858357 2792339 := bstep (se 1 (by rfl) ⟨2094254, by rfl⟩ : syracuseStep 2792339 = 4188509) B4188509
theorem B2202553 : Blo 858357 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B859067 : Blo 858357 859067 := bstep (se 1 (by rfl) ⟨644300, by rfl⟩ : syracuseStep 859067 = 1288601) B1288601
theorem B2178049 : Blo 858357 2178049 := bstep (se 2 (by rfl) ⟨816768, by rfl⟩ : syracuseStep 2178049 = 1633537) B1633537
theorem B859143 : Blo 858357 859143 := bstep (se 1 (by rfl) ⟨644357, by rfl⟩ : syracuseStep 859143 = 1288715) B1288715
theorem B1448975 : Blo 858357 1448975 := bstep (se 1 (by rfl) ⟨1086731, by rfl⟩ : syracuseStep 1448975 = 2173463) B2173463
theorem B859151 : Blo 858357 859151 := bstep (se 1 (by rfl) ⟨644363, by rfl⟩ : syracuseStep 859151 = 1288727) B1288727
theorem B2448427 : Blo 858357 2448427 := bstep (se 1 (by rfl) ⟨1836320, by rfl⟩ : syracuseStep 2448427 = 3672641) B3672641
theorem B859195 : Blo 858357 859195 := bstep (se 1 (by rfl) ⟨644396, by rfl⟩ : syracuseStep 859195 = 1288793) B1288793
theorem B3259511 : Blo 858357 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B1932407 : Blo 858357 1932407 := bstep (se 1 (by rfl) ⟨1449305, by rfl⟩ : syracuseStep 1932407 = 2898611) B2898611
theorem B965767 : Blo 858357 965767 := bstep (se 1 (by rfl) ⟨724325, by rfl⟩ : syracuseStep 965767 = 1448651) B1448651
theorem B859271 : Blo 858357 859271 := bstep (se 1 (by rfl) ⟨644453, by rfl⟩ : syracuseStep 859271 = 1288907) B1288907
theorem B859279 : Blo 858357 859279 := bstep (se 1 (by rfl) ⟨644459, by rfl⟩ : syracuseStep 859279 = 1288919) B1288919
theorem B1744019 : Blo 858357 1744019 := bstep (se 1 (by rfl) ⟨1308014, by rfl⟩ : syracuseStep 1744019 = 2616029) B2616029
theorem B859323 : Blo 858357 859323 := bstep (se 1 (by rfl) ⟨644492, by rfl⟩ : syracuseStep 859323 = 1288985) B1288985
theorem B1162441 : Blo 858357 1162441 := bstep (se 2 (by rfl) ⟨435915, by rfl⟩ : syracuseStep 1162441 = 871831) B871831
theorem B859399 : Blo 858357 859399 := bstep (se 1 (by rfl) ⟨644549, by rfl⟩ : syracuseStep 859399 = 1289099) B1289099
theorem B859407 : Blo 858357 859407 := bstep (se 1 (by rfl) ⟨644555, by rfl⟩ : syracuseStep 859407 = 1289111) B1289111
theorem B8822033 : Blo 858357 8822033 := bstep (se 2 (by rfl) ⟨3308262, by rfl⟩ : syracuseStep 8822033 = 6616525) B6616525
theorem B1932587 : Blo 858357 1932587 := bstep (se 1 (by rfl) ⟨1449440, by rfl⟩ : syracuseStep 1932587 = 2898881) B2898881
theorem B965947 : Blo 858357 965947 := bstep (se 1 (by rfl) ⟨724460, by rfl⟩ : syracuseStep 965947 = 1448921) B1448921
theorem B2899259 : Blo 858357 2899259 := bstep (se 1 (by rfl) ⟨2174444, by rfl⟩ : syracuseStep 2899259 = 4348889) B4348889
theorem B859451 : Blo 858357 859451 := bstep (se 1 (by rfl) ⟨644588, by rfl⟩ : syracuseStep 859451 = 1289177) B1289177
theorem B2448701 : Blo 858357 2448701 := bstep (se 3 (by rfl) ⟨459131, by rfl⟩ : syracuseStep 2448701 = 918263) B918263
theorem B1162615 : Blo 858357 1162615 := bstep (se 1 (by rfl) ⟨871961, by rfl⟩ : syracuseStep 1162615 = 1743923) B1743923
theorem B1744247 : Blo 858357 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B859527 : Blo 858357 859527 := bstep (se 1 (by rfl) ⟨644645, by rfl⟩ : syracuseStep 859527 = 1289291) B1289291
theorem B1088903 : Blo 858357 1088903 := bstep (se 1 (by rfl) ⟨816677, by rfl⟩ : syracuseStep 1088903 = 1633355) B1633355
theorem B859535 : Blo 858357 859535 := bstep (se 1 (by rfl) ⟨644651, by rfl⟩ : syracuseStep 859535 = 1289303) B1289303
theorem B4890041 : Blo 858357 4890041 := bstep (se 2 (by rfl) ⟨1833765, by rfl⟩ : syracuseStep 4890041 = 3667531) B3667531
theorem B859579 : Blo 858357 859579 := bstep (se 1 (by rfl) ⟨644684, by rfl⟩ : syracuseStep 859579 = 1289369) B1289369
theorem B859655 : Blo 858357 859655 := bstep (se 1 (by rfl) ⟨644741, by rfl⟩ : syracuseStep 859655 = 1289483) B1289483
theorem B859663 : Blo 858357 859663 := bstep (se 1 (by rfl) ⟨644747, by rfl⟩ : syracuseStep 859663 = 1289495) B1289495
theorem B4898333 : Blo 858357 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B1449515 : Blo 858357 1449515 := bstep (se 1 (by rfl) ⟨1087136, by rfl⟩ : syracuseStep 1449515 = 2174273) B2174273
theorem B859707 : Blo 858357 859707 := bstep (se 1 (by rfl) ⟨644780, by rfl⟩ : syracuseStep 859707 = 1289561) B1289561
theorem B859783 : Blo 858357 859783 := bstep (se 1 (by rfl) ⟨644837, by rfl⟩ : syracuseStep 859783 = 1289675) B1289675
theorem B859791 : Blo 858357 859791 := bstep (se 1 (by rfl) ⟨644843, by rfl⟩ : syracuseStep 859791 = 1289687) B1289687
theorem B1932947 : Blo 858357 1932947 := bstep (se 1 (by rfl) ⟨1449710, by rfl⟩ : syracuseStep 1932947 = 2899421) B2899421
theorem B4406957 : Blo 858357 4406957 := bstep (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) B1652609
theorem B859835 : Blo 858357 859835 := bstep (se 1 (by rfl) ⟨644876, by rfl⟩ : syracuseStep 859835 = 1289753) B1289753
theorem B1933001 : Blo 858357 1933001 := bstep (se 2 (by rfl) ⟨724875, by rfl⟩ : syracuseStep 1933001 = 1449751) B1449751
theorem B859911 : Blo 858357 859911 := bstep (se 1 (by rfl) ⟨644933, by rfl⟩ : syracuseStep 859911 = 1289867) B1289867
theorem B2793217 : Blo 858357 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B966415 : Blo 858357 966415 := bstep (se 1 (by rfl) ⟨724811, by rfl⟩ : syracuseStep 966415 = 1449623) B1449623
theorem B859919 : Blo 858357 859919 := bstep (se 1 (by rfl) ⟨644939, by rfl⟩ : syracuseStep 859919 = 1289879) B1289879
theorem B2752289 : Blo 858357 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B2899745 : Blo 858357 2899745 := bstep (se 2 (by rfl) ⟨1087404, by rfl⟩ : syracuseStep 2899745 = 2174809) B2174809
theorem B67927853 : Blo 858357 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B859963 : Blo 858357 859963 := bstep (se 1 (by rfl) ⟨644972, by rfl⟩ : syracuseStep 859963 = 1289945) B1289945
theorem B1376119 : Blo 858357 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B860039 : Blo 858357 860039 := bstep (se 1 (by rfl) ⟨645029, by rfl⟩ : syracuseStep 860039 = 1290059) B1290059
theorem B860047 : Blo 858357 860047 := bstep (se 1 (by rfl) ⟨645035, by rfl⟩ : syracuseStep 860047 = 1290071) B1290071
theorem B3669907 : Blo 858357 3669907 := bstep (se 1 (by rfl) ⟨2752430, by rfl⟩ : syracuseStep 3669907 = 5504861) B5504861
theorem B1449913 : Blo 858357 1449913 := bstep (se 2 (by rfl) ⟨543717, by rfl⟩ : syracuseStep 1449913 = 1087435) B1087435
theorem B860091 : Blo 858357 860091 := bstep (se 1 (by rfl) ⟨645068, by rfl⟩ : syracuseStep 860091 = 1290137) B1290137
theorem B860199 : Blo 858357 860199 := bstep (se 1 (by rfl) ⟨645149, by rfl⟩ : syracuseStep 860199 = 1290299) B1290299
theorem B860239 : Blo 858357 860239 := bstep (se 1 (by rfl) ⟨645179, by rfl⟩ : syracuseStep 860239 = 1290359) B1290359
theorem B860255 : Blo 858357 860255 := bstep (se 1 (by rfl) ⟨645191, by rfl⟩ : syracuseStep 860255 = 1290383) B1290383
theorem B860283 : Blo 858357 860283 := bstep (se 1 (by rfl) ⟨645212, by rfl⟩ : syracuseStep 860283 = 1290425) B1290425
theorem B860335 : Blo 858357 860335 := bstep (se 1 (by rfl) ⟨645251, by rfl⟩ : syracuseStep 860335 = 1290503) B1290503
theorem B1450183 : Blo 858357 1450183 := bstep (se 1 (by rfl) ⟨1087637, by rfl⟩ : syracuseStep 1450183 = 2175275) B2175275
theorem B860359 : Blo 858357 860359 := bstep (se 1 (by rfl) ⟨645269, by rfl⟩ : syracuseStep 860359 = 1290539) B1290539
theorem B860379 : Blo 858357 860379 := bstep (se 1 (by rfl) ⟨645284, by rfl⟩ : syracuseStep 860379 = 1290569) B1290569
theorem B2064631 : Blo 858357 2064631 := bstep (se 1 (by rfl) ⟨1548473, by rfl⟩ : syracuseStep 2064631 = 3096947) B3096947
theorem B1933559 : Blo 858357 1933559 := bstep (se 1 (by rfl) ⟨1450169, by rfl⟩ : syracuseStep 1933559 = 2900339) B2900339
theorem B860455 : Blo 858357 860455 := bstep (se 1 (by rfl) ⟨645341, by rfl⟩ : syracuseStep 860455 = 1290683) B1290683
theorem B4645181 : Blo 858357 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B2900285 : Blo 858357 2900285 := bstep (se 3 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 2900285 = 1087607) B1087607
theorem B860495 : Blo 858357 860495 := bstep (se 1 (by rfl) ⟨645371, by rfl⟩ : syracuseStep 860495 = 1290743) B1290743
theorem B860511 : Blo 858357 860511 := bstep (se 1 (by rfl) ⟨645383, by rfl⟩ : syracuseStep 860511 = 1290767) B1290767
theorem B1450345 : Blo 858357 1450345 := bstep (se 2 (by rfl) ⟨543879, by rfl⟩ : syracuseStep 1450345 = 1087759) B1087759
theorem B860539 : Blo 858357 860539 := bstep (se 1 (by rfl) ⟨645404, by rfl⟩ : syracuseStep 860539 = 1290809) B1290809
theorem B6529409 : Blo 858357 6529409 := bstep (se 2 (by rfl) ⟨2448528, by rfl⟩ : syracuseStep 6529409 = 4897057) B4897057
theorem B3097075 : Blo 858357 3097075 := bstep (se 1 (by rfl) ⟨2322806, by rfl⟩ : syracuseStep 3097075 = 4645613) B4645613
theorem B6275593 : Blo 858357 6275593 := bstep (se 2 (by rfl) ⟨2353347, by rfl⟩ : syracuseStep 6275593 = 4706695) B4706695
theorem B6193687 : Blo 858357 6193687 := bstep (se 1 (by rfl) ⟨4645265, by rfl⟩ : syracuseStep 6193687 = 9290531) B9290531
theorem B8495641 : Blo 858357 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B967207 : Blo 858357 967207 := bstep (se 1 (by rfl) ⟨725405, by rfl⟩ : syracuseStep 967207 = 1450811) B1450811
theorem B1655419 : Blo 858357 1655419 := bstep (se 1 (by rfl) ⟨1241564, by rfl⟩ : syracuseStep 1655419 = 2483129) B2483129
theorem B1376939 : Blo 858357 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B5227337 : Blo 858357 5227337 := bstep (se 2 (by rfl) ⟨1960251, by rfl⟩ : syracuseStep 5227337 = 3920503) B3920503
theorem B1934153 : Blo 858357 1934153 := bstep (se 2 (by rfl) ⟨725307, by rfl⟩ : syracuseStep 1934153 = 1450615) B1450615
theorem B2065247 : Blo 858357 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B4891499 : Blo 858357 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B2450351 : Blo 858357 2450351 := bstep (se 1 (by rfl) ⟨1837763, by rfl⟩ : syracuseStep 2450351 = 3675527) B3675527
theorem B1450939 : Blo 858357 1450939 := bstep (se 1 (by rfl) ⟨1088204, by rfl⟩ : syracuseStep 1450939 = 2176409) B2176409
theorem B3261455 : Blo 858357 3261455 := bstep (se 1 (by rfl) ⟨2446091, by rfl⟩ : syracuseStep 3261455 = 4892183) B4892183
theorem B4350995 : Blo 858357 4350995 := bstep (se 1 (by rfl) ⟨3263246, by rfl⟩ : syracuseStep 4350995 = 6526493) B6526493
theorem B1451047 : Blo 858357 1451047 := bstep (se 1 (by rfl) ⟨1088285, by rfl⟩ : syracuseStep 1451047 = 2176571) B2176571
theorem B1033339 : Blo 858357 1033339 := bstep (se 1 (by rfl) ⟨775004, by rfl⟩ : syracuseStep 1033339 = 1550009) B1550009
theorem B2901149 : Blo 858357 2901149 := bstep (se 3 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 2901149 = 1087931) B1087931
theorem B9290969 : Blo 858357 9290969 := bstep (se 2 (by rfl) ⟨3484113, by rfl⟩ : syracuseStep 9290969 = 6968227) B6968227
theorem B2614519 : Blo 858357 2614519 := bstep (se 1 (by rfl) ⟨1960889, by rfl⟩ : syracuseStep 2614519 = 3921779) B3921779
theorem B5506319 : Blo 858357 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B1631593 : Blo 858357 1631593 := bstep (se 2 (by rfl) ⟨611847, by rfl⟩ : syracuseStep 1631593 = 1223695) B1223695
theorem B1451371 : Blo 858357 1451371 := bstep (se 1 (by rfl) ⟨1088528, by rfl⟩ : syracuseStep 1451371 = 2177057) B2177057
theorem B1287599 : Blo 858357 1287599 := bstep (se 1 (by rfl) ⟨965699, by rfl⟩ : syracuseStep 1287599 = 1931399) B1931399
theorem B1287689 : Blo 858357 1287689 := bstep (se 2 (by rfl) ⟨482883, by rfl⟩ : syracuseStep 1287689 = 965767) B965767
theorem B1287719 : Blo 858357 1287719 := bstep (se 1 (by rfl) ⟨965789, by rfl⟩ : syracuseStep 1287719 = 1931579) B1931579
theorem B3098171 : Blo 858357 3098171 := bstep (se 1 (by rfl) ⟨2323628, by rfl⟩ : syracuseStep 3098171 = 4647257) B4647257
theorem B1934945 : Blo 858357 1934945 := bstep (se 2 (by rfl) ⟨725604, by rfl⟩ : syracuseStep 1934945 = 1451209) B1451209
theorem B1287803 : Blo 858357 1287803 := bstep (se 1 (by rfl) ⟨965852, by rfl⟩ : syracuseStep 1287803 = 1931705) B1931705
theorem B4900499 : Blo 858357 4900499 := bstep (se 1 (by rfl) ⟨3675374, by rfl⟩ : syracuseStep 4900499 = 7350749) B7350749
theorem B2901689 : Blo 858357 2901689 := bstep (se 2 (by rfl) ⟨1088133, by rfl⟩ : syracuseStep 2901689 = 2176267) B2176267
theorem B6522605 : Blo 858357 6522605 := bstep (se 3 (by rfl) ⟨1222988, by rfl⟩ : syracuseStep 6522605 = 2445977) B2445977
theorem B1287929 : Blo 858357 1287929 := bstep (se 2 (by rfl) ⟨482973, by rfl⟩ : syracuseStep 1287929 = 965947) B965947
theorem B3720953 : Blo 858357 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B2983673 : Blo 858357 2983673 := bstep (se 2 (by rfl) ⟨1118877, by rfl⟩ : syracuseStep 2983673 = 2237755) B2237755
theorem B1550153 : Blo 858357 1550153 := bstep (se 2 (by rfl) ⟨581307, by rfl⟩ : syracuseStep 1550153 = 1162615) B1162615
theorem B22005593 : Blo 858357 22005593 := bstep (se 2 (by rfl) ⟨8252097, by rfl⟩ : syracuseStep 22005593 = 16504195) B16504195
theorem B1288031 : Blo 858357 1288031 := bstep (se 1 (by rfl) ⟨966023, by rfl⟩ : syracuseStep 1288031 = 1932047) B1932047
theorem B1288043 : Blo 858357 1288043 := bstep (se 1 (by rfl) ⟨966032, by rfl⟩ : syracuseStep 1288043 = 1932065) B1932065
theorem B2320289 : Blo 858357 2320289 := bstep (se 2 (by rfl) ⟨870108, by rfl⟩ : syracuseStep 2320289 = 1740217) B1740217
theorem B1861559 : Blo 858357 1861559 := bstep (se 1 (by rfl) ⟨1396169, by rfl⟩ : syracuseStep 1861559 = 2792339) B2792339
theorem B1935287 : Blo 858357 1935287 := bstep (se 1 (by rfl) ⟨1451465, by rfl⟩ : syracuseStep 1935287 = 2902931) B2902931
theorem B2173007 : Blo 858357 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B1288271 : Blo 858357 1288271 := bstep (se 1 (by rfl) ⟨966203, by rfl⟩ : syracuseStep 1288271 = 1932407) B1932407
theorem B3672179 : Blo 858357 3672179 := bstep (se 1 (by rfl) ⟨2754134, by rfl⟩ : syracuseStep 3672179 = 5508269) B5508269
theorem B1288391 : Blo 858357 1288391 := bstep (se 1 (by rfl) ⟨966293, by rfl⟩ : syracuseStep 1288391 = 1932587) B1932587
theorem B1632467 : Blo 858357 1632467 := bstep (se 1 (by rfl) ⟨1224350, by rfl⟩ : syracuseStep 1632467 = 2448701) B2448701
theorem B2902283 : Blo 858357 2902283 := bstep (se 1 (by rfl) ⟨2176712, by rfl⟩ : syracuseStep 2902283 = 4353425) B4353425
theorem B1288553 : Blo 858357 1288553 := bstep (se 2 (by rfl) ⟨483207, by rfl⟩ : syracuseStep 1288553 = 966415) B966415
theorem B1288631 : Blo 858357 1288631 := bstep (se 1 (by rfl) ⟨966473, by rfl⟩ : syracuseStep 1288631 = 1932947) B1932947
theorem B1288667 : Blo 858357 1288667 := bstep (se 1 (by rfl) ⟨966500, by rfl⟩ : syracuseStep 1288667 = 1933001) B1933001
theorem B6973933 : Blo 858357 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B1935881 : Blo 858357 1935881 := bstep (se 2 (by rfl) ⟨725955, by rfl⟩ : syracuseStep 1935881 = 1451911) B1451911
theorem B4893209 : Blo 858357 4893209 := bstep (se 2 (by rfl) ⟨1834953, by rfl⟩ : syracuseStep 4893209 = 3669907) B3669907
theorem B2755097 : Blo 858357 2755097 := bstep (se 2 (by rfl) ⟨1033161, by rfl⟩ : syracuseStep 2755097 = 2066323) B2066323
theorem B2902553 : Blo 858357 2902553 := bstep (se 2 (by rfl) ⟨1088457, by rfl⟩ : syracuseStep 2902553 = 2176915) B2176915
theorem B3263111 : Blo 858357 3263111 := bstep (se 1 (by rfl) ⟨2447333, by rfl⟩ : syracuseStep 3263111 = 4894667) B4894667
theorem B6523577 : Blo 858357 6523577 := bstep (se 2 (by rfl) ⟨2446341, by rfl⟩ : syracuseStep 6523577 = 4892683) B4892683
theorem B2173655 : Blo 858357 2173655 := bstep (se 1 (by rfl) ⟨1630241, by rfl⟩ : syracuseStep 2173655 = 3260483) B3260483
theorem B2943773 : Blo 858357 2943773 := bstep (se 3 (by rfl) ⟨551957, by rfl⟩ : syracuseStep 2943773 = 1103915) B1103915
theorem B1633097 : Blo 858357 1633097 := bstep (se 2 (by rfl) ⟨612411, by rfl⟩ : syracuseStep 1633097 = 1224823) B1224823
theorem B1936223 : Blo 858357 1936223 := bstep (se 1 (by rfl) ⟨1452167, by rfl⟩ : syracuseStep 1936223 = 2904335) B2904335
theorem B1289135 : Blo 858357 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B1289225 : Blo 858357 1289225 := bstep (se 2 (by rfl) ⟨483459, by rfl⟩ : syracuseStep 1289225 = 966919) B966919
theorem B1289255 : Blo 858357 1289255 := bstep (se 1 (by rfl) ⟨966941, by rfl⟩ : syracuseStep 1289255 = 1933883) B1933883
theorem B36211799 : Blo 858357 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B1289339 : Blo 858357 1289339 := bstep (se 1 (by rfl) ⟨967004, by rfl⟩ : syracuseStep 1289339 = 1934009) B1934009
theorem B1289465 : Blo 858357 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B1289567 : Blo 858357 1289567 := bstep (se 1 (by rfl) ⟨967175, by rfl⟩ : syracuseStep 1289567 = 1934351) B1934351
theorem B1289579 : Blo 858357 1289579 := bstep (se 1 (by rfl) ⟨967184, by rfl⟩ : syracuseStep 1289579 = 1934369) B1934369
theorem B7441789 : Blo 858357 7441789 := bstep (se 3 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 7441789 = 2790671) B2790671
theorem B5229989 : Blo 858357 5229989 := bstep (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) B980623
theorem B1289807 : Blo 858357 1289807 := bstep (se 1 (by rfl) ⟨967355, by rfl⟩ : syracuseStep 1289807 = 1934711) B1934711
theorem B3264097 : Blo 858357 3264097 := bstep (se 2 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 3264097 = 2448073) B2448073
theorem B6524549 : Blo 858357 6524549 := bstep (se 4 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 6524549 = 1223353) B1223353
theorem B2903687 : Blo 858357 2903687 := bstep (se 1 (by rfl) ⟨2177765, by rfl⟩ : syracuseStep 2903687 = 4355531) B4355531
theorem B2903741 : Blo 858357 2903741 := bstep (se 3 (by rfl) ⟨544451, by rfl⟩ : syracuseStep 2903741 = 1088903) B1088903
theorem B2936519 : Blo 858357 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B1289927 : Blo 858357 1289927 := bstep (se 1 (by rfl) ⟨967445, by rfl⟩ : syracuseStep 1289927 = 1934891) B1934891
theorem B2903903 : Blo 858357 2903903 := bstep (se 1 (by rfl) ⟨2177927, by rfl⟩ : syracuseStep 2903903 = 4355855) B4355855
theorem B1290089 : Blo 858357 1290089 := bstep (se 2 (by rfl) ⟨483783, by rfl⟩ : syracuseStep 1290089 = 967567) B967567
theorem B4353911 : Blo 858357 4353911 := bstep (se 1 (by rfl) ⟨3265433, by rfl⟩ : syracuseStep 4353911 = 6530867) B6530867
theorem B3100535 : Blo 858357 3100535 := bstep (se 1 (by rfl) ⟨2325401, by rfl⟩ : syracuseStep 3100535 = 4650803) B4650803
theorem B2936737 : Blo 858357 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B1396655 : Blo 858357 1396655 := bstep (se 1 (by rfl) ⟨1047491, by rfl⟩ : syracuseStep 1396655 = 2094983) B2094983
theorem B1290167 : Blo 858357 1290167 := bstep (se 1 (by rfl) ⟨967625, by rfl⟩ : syracuseStep 1290167 = 1935251) B1935251
theorem B4714433 : Blo 858357 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B1290203 : Blo 858357 1290203 := bstep (se 1 (by rfl) ⟨967652, by rfl⟩ : syracuseStep 1290203 = 1935305) B1935305
theorem B2904065 : Blo 858357 2904065 := bstep (se 2 (by rfl) ⟨1089024, by rfl⟩ : syracuseStep 2904065 = 2178049) B2178049
theorem B4182031 : Blo 858357 4182031 := bstep (se 1 (by rfl) ⟨3136523, by rfl⟩ : syracuseStep 4182031 = 6273047) B6273047
theorem B3264569 : Blo 858357 3264569 := bstep (se 2 (by rfl) ⟨1224213, by rfl⟩ : syracuseStep 3264569 = 2448427) B2448427
theorem B4649075 : Blo 858357 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B5501195 : Blo 858357 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B5222717 : Blo 858357 5222717 := bstep (se 3 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 5222717 = 1958519) B1958519
theorem B9417035 : Blo 858357 9417035 := bstep (se 1 (by rfl) ⟨7062776, by rfl⟩ : syracuseStep 9417035 = 14125553) B14125553
theorem B6197609 : Blo 858357 6197609 := bstep (se 2 (by rfl) ⟨2324103, by rfl⟩ : syracuseStep 6197609 = 4648207) B4648207
theorem B1290671 : Blo 858357 1290671 := bstep (se 1 (by rfl) ⟨968003, by rfl⟩ : syracuseStep 1290671 = 1936007) B1936007
theorem B3674605 : Blo 858357 3674605 := bstep (se 3 (by rfl) ⟨688988, by rfl⟩ : syracuseStep 3674605 = 1377977) B1377977
theorem B1290761 : Blo 858357 1290761 := bstep (se 2 (by rfl) ⟨484035, by rfl⟩ : syracuseStep 1290761 = 968071) B968071
theorem B1290791 : Blo 858357 1290791 := bstep (se 1 (by rfl) ⟨968093, by rfl⟩ : syracuseStep 1290791 = 1936187) B1936187
theorem B3666491 : Blo 858357 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B4895417 : Blo 858357 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B4133585 : Blo 858357 4133585 := bstep (se 2 (by rfl) ⟨1550094, by rfl⟩ : syracuseStep 4133585 = 3100189) B3100189
theorem B2356075 : Blo 858357 2356075 := bstep (se 1 (by rfl) ⟨1767056, by rfl⟩ : syracuseStep 2356075 = 3534113) B3534113
theorem B3724289 : Blo 858357 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B3265555 : Blo 858357 3265555 := bstep (se 1 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 3265555 = 4898333) B4898333
theorem B2937971 : Blo 858357 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B2479261 : Blo 858357 2479261 := bstep (se 3 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 2479261 = 929723) B929723
theorem B2176247 : Blo 858357 2176247 := bstep (se 1 (by rfl) ⟨1632185, by rfl⟩ : syracuseStep 2176247 = 3264371) B3264371
theorem B4896125 : Blo 858357 4896125 := bstep (se 3 (by rfl) ⟨918023, by rfl⟩ : syracuseStep 4896125 = 1836047) B1836047
theorem B4347431 : Blo 858357 4347431 := bstep (se 1 (by rfl) ⟨3260573, by rfl⟩ : syracuseStep 4347431 = 6521147) B6521147
theorem B1087015 : Blo 858357 1087015 := bstep (se 1 (by rfl) ⟨815261, by rfl⟩ : syracuseStep 1087015 = 1630523) B1630523
theorem B4183591 : Blo 858357 4183591 := bstep (se 1 (by rfl) ⟨3137693, by rfl⟩ : syracuseStep 4183591 = 6275387) B6275387
theorem B2897531 : Blo 858357 2897531 := bstep (se 1 (by rfl) ⟨2173148, by rfl⟩ : syracuseStep 2897531 = 4346297) B4346297
theorem B2897693 : Blo 858357 2897693 := bstep (se 3 (by rfl) ⟨543317, by rfl⟩ : syracuseStep 2897693 = 1086635) B1086635
theorem B1087339 : Blo 858357 1087339 := bstep (se 1 (by rfl) ⟨815504, by rfl⟩ : syracuseStep 1087339 = 1631009) B1631009
theorem B1742753 : Blo 858357 1742753 := bstep (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) B1307065
theorem B2095031 : Blo 858357 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B6526979 : Blo 858357 6526979 := bstep (se 1 (by rfl) ⟨4895234, by rfl⟩ : syracuseStep 6526979 = 9790469) B9790469
theorem B8599609 : Blo 858357 8599609 := bstep (se 2 (by rfl) ⟨3224853, by rfl⟩ : syracuseStep 8599609 = 6449707) B6449707
theorem B4126801 : Blo 858357 4126801 := bstep (se 2 (by rfl) ⟨1547550, by rfl⟩ : syracuseStep 4126801 = 3095101) B3095101
theorem B1931435 : Blo 858357 1931435 := bstep (se 1 (by rfl) ⟨1448576, by rfl⟩ : syracuseStep 1931435 = 2897153) B2897153
theorem B858407 : Blo 858357 858407 := bstep (se 1 (by rfl) ⟨643805, by rfl⟩ : syracuseStep 858407 = 1287611) B1287611
theorem B858447 : Blo 858357 858447 := bstep (se 1 (by rfl) ⟨643835, by rfl⟩ : syracuseStep 858447 = 1287671) B1287671
theorem B858463 : Blo 858357 858463 := bstep (se 1 (by rfl) ⟨643847, by rfl⟩ : syracuseStep 858463 = 1287695) B1287695
theorem B858491 : Blo 858357 858491 := bstep (se 1 (by rfl) ⟨643868, by rfl⟩ : syracuseStep 858491 = 1287737) B1287737
theorem B6199685 : Blo 858357 6199685 := bstep (se 4 (by rfl) ⟨581220, by rfl⟩ : syracuseStep 6199685 = 1162441) B1162441
theorem B858543 : Blo 858357 858543 := bstep (se 1 (by rfl) ⟨643907, by rfl⟩ : syracuseStep 858543 = 1287815) B1287815
theorem B858567 : Blo 858357 858567 := bstep (se 1 (by rfl) ⟨643925, by rfl⟩ : syracuseStep 858567 = 1287851) B1287851
theorem B3348937 : Blo 858357 3348937 := bstep (se 2 (by rfl) ⟨1255851, by rfl⟩ : syracuseStep 3348937 = 2511703) B2511703
theorem B858587 : Blo 858357 858587 := bstep (se 1 (by rfl) ⟨643940, by rfl⟩ : syracuseStep 858587 = 1287881) B1287881
theorem B2898395 : Blo 858357 2898395 := bstep (se 1 (by rfl) ⟨2173796, by rfl⟩ : syracuseStep 2898395 = 4347593) B4347593
theorem B3668489 : Blo 858357 3668489 := bstep (se 2 (by rfl) ⟨1375683, by rfl⟩ : syracuseStep 3668489 = 2751367) B2751367
theorem B858663 : Blo 858357 858663 := bstep (se 1 (by rfl) ⟨643997, by rfl⟩ : syracuseStep 858663 = 1287995) B1287995
theorem B858703 : Blo 858357 858703 := bstep (se 1 (by rfl) ⟨644027, by rfl⟩ : syracuseStep 858703 = 1288055) B1288055
theorem B858719 : Blo 858357 858719 := bstep (se 1 (by rfl) ⟨644039, by rfl⟩ : syracuseStep 858719 = 1288079) B1288079
theorem B858747 : Blo 858357 858747 := bstep (se 1 (by rfl) ⟨644060, by rfl⟩ : syracuseStep 858747 = 1288121) B1288121
theorem B2177675 : Blo 858357 2177675 := bstep (se 1 (by rfl) ⟨1633256, by rfl⟩ : syracuseStep 2177675 = 3266513) B3266513
theorem B858799 : Blo 858357 858799 := bstep (se 1 (by rfl) ⟨644099, by rfl⟩ : syracuseStep 858799 = 1288199) B1288199
theorem B1931975 : Blo 858357 1931975 := bstep (se 1 (by rfl) ⟨1448981, by rfl⟩ : syracuseStep 1931975 = 2897963) B2897963
theorem B858823 : Blo 858357 858823 := bstep (se 1 (by rfl) ⟨644117, by rfl⟩ : syracuseStep 858823 = 1288235) B1288235
theorem B3267287 : Blo 858357 3267287 := bstep (se 1 (by rfl) ⟨2450465, by rfl⟩ : syracuseStep 3267287 = 4900931) B4900931
theorem B858843 : Blo 858357 858843 := bstep (se 1 (by rfl) ⟨644132, by rfl⟩ : syracuseStep 858843 = 1288265) B1288265
theorem B858919 : Blo 858357 858919 := bstep (se 1 (by rfl) ⟨644189, by rfl⟩ : syracuseStep 858919 = 1288379) B1288379
theorem B1653577 : Blo 858357 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B858959 : Blo 858357 858959 := bstep (se 1 (by rfl) ⟨644219, by rfl⟩ : syracuseStep 858959 = 1288439) B1288439
theorem B858975 : Blo 858357 858975 := bstep (se 1 (by rfl) ⟨644231, by rfl⟩ : syracuseStep 858975 = 1288463) B1288463
theorem B2177887 : Blo 858357 2177887 := bstep (se 1 (by rfl) ⟨1633415, by rfl⟩ : syracuseStep 2177887 = 3266831) B3266831
theorem B859003 : Blo 858357 859003 := bstep (se 1 (by rfl) ⟨644252, by rfl⟩ : syracuseStep 859003 = 1288505) B1288505
theorem B859055 : Blo 858357 859055 := bstep (se 1 (by rfl) ⟨644291, by rfl⟩ : syracuseStep 859055 = 1288583) B1288583
theorem B1448887 : Blo 858357 1448887 := bstep (se 1 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 1448887 = 2173331) B2173331
theorem B859079 : Blo 858357 859079 := bstep (se 1 (by rfl) ⟨644309, by rfl⟩ : syracuseStep 859079 = 1288619) B1288619
theorem B859099 : Blo 858357 859099 := bstep (se 1 (by rfl) ⟨644324, by rfl⟩ : syracuseStep 859099 = 1288649) B1288649
theorem B859175 : Blo 858357 859175 := bstep (se 1 (by rfl) ⟨644381, by rfl⟩ : syracuseStep 859175 = 1288763) B1288763
theorem B3529807 : Blo 858357 3529807 := bstep (se 1 (by rfl) ⟨2647355, by rfl⟩ : syracuseStep 3529807 = 5294711) B5294711
theorem B859215 : Blo 858357 859215 := bstep (se 1 (by rfl) ⟨644411, by rfl⟩ : syracuseStep 859215 = 1288823) B1288823
theorem B859231 : Blo 858357 859231 := bstep (se 1 (by rfl) ⟨644423, by rfl⟩ : syracuseStep 859231 = 1288847) B1288847
theorem B1449083 : Blo 858357 1449083 := bstep (se 1 (by rfl) ⟨1086812, by rfl⟩ : syracuseStep 1449083 = 2173625) B2173625
theorem B859259 : Blo 858357 859259 := bstep (se 1 (by rfl) ⟨644444, by rfl⟩ : syracuseStep 859259 = 1288889) B1288889
theorem B1088635 : Blo 858357 1088635 := bstep (se 1 (by rfl) ⟨816476, by rfl⟩ : syracuseStep 1088635 = 1632953) B1632953
theorem B2899097 : Blo 858357 2899097 := bstep (se 2 (by rfl) ⟨1087161, by rfl⟩ : syracuseStep 2899097 = 2174323) B2174323
theorem B859311 : Blo 858357 859311 := bstep (se 1 (by rfl) ⟨644483, by rfl⟩ : syracuseStep 859311 = 1288967) B1288967
theorem B859335 : Blo 858357 859335 := bstep (se 1 (by rfl) ⟨644501, by rfl⟩ : syracuseStep 859335 = 1289003) B1289003
theorem B859355 : Blo 858357 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B3669239 : Blo 858357 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B859431 : Blo 858357 859431 := bstep (se 1 (by rfl) ⟨644573, by rfl⟩ : syracuseStep 859431 = 1289147) B1289147
theorem B3259709 : Blo 858357 3259709 := bstep (se 3 (by rfl) ⟨611195, by rfl⟩ : syracuseStep 3259709 = 1222391) B1222391
theorem B859471 : Blo 858357 859471 := bstep (se 1 (by rfl) ⟨644603, by rfl⟩ : syracuseStep 859471 = 1289207) B1289207
theorem B965983 : Blo 858357 965983 := bstep (se 1 (by rfl) ⟨724487, by rfl⟩ : syracuseStep 965983 = 1448975) B1448975
theorem B1547615 : Blo 858357 1547615 := bstep (se 1 (by rfl) ⟨1160711, by rfl⟩ : syracuseStep 1547615 = 2321423) B2321423
theorem B859487 : Blo 858357 859487 := bstep (se 1 (by rfl) ⟨644615, by rfl⟩ : syracuseStep 859487 = 1289231) B1289231
theorem B859515 : Blo 858357 859515 := bstep (se 1 (by rfl) ⟨644636, by rfl⟩ : syracuseStep 859515 = 1289273) B1289273
theorem B859567 : Blo 858357 859567 := bstep (se 1 (by rfl) ⟨644675, by rfl⟩ : syracuseStep 859567 = 1289351) B1289351
theorem B1162679 : Blo 858357 1162679 := bstep (se 1 (by rfl) ⟨872009, by rfl⟩ : syracuseStep 1162679 = 1744019) B1744019
theorem B859591 : Blo 858357 859591 := bstep (se 1 (by rfl) ⟨644693, by rfl⟩ : syracuseStep 859591 = 1289387) B1289387
theorem B181140941 : Blo 858357 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B859611 : Blo 858357 859611 := bstep (se 1 (by rfl) ⟨644708, by rfl⟩ : syracuseStep 859611 = 1289417) B1289417
theorem B1449481 : Blo 858357 1449481 := bstep (se 2 (by rfl) ⟨543555, by rfl⟩ : syracuseStep 1449481 = 1087111) B1087111
theorem B5881355 : Blo 858357 5881355 := bstep (se 1 (by rfl) ⟨4411016, by rfl⟩ : syracuseStep 5881355 = 8822033) B8822033
theorem B1932839 : Blo 858357 1932839 := bstep (se 1 (by rfl) ⟨1449629, by rfl⟩ : syracuseStep 1932839 = 2899259) B2899259
theorem B859687 : Blo 858357 859687 := bstep (se 1 (by rfl) ⟨644765, by rfl⟩ : syracuseStep 859687 = 1289531) B1289531
theorem B859727 : Blo 858357 859727 := bstep (se 1 (by rfl) ⟨644795, by rfl⟩ : syracuseStep 859727 = 1289591) B1289591
theorem B1162831 : Blo 858357 1162831 := bstep (se 1 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 1162831 = 1744247) B1744247
theorem B859743 : Blo 858357 859743 := bstep (se 1 (by rfl) ⟨644807, by rfl⟩ : syracuseStep 859743 = 1289615) B1289615
theorem B4349537 : Blo 858357 4349537 := bstep (se 2 (by rfl) ⟨1631076, by rfl⟩ : syracuseStep 4349537 = 3262153) B3262153
theorem B3260027 : Blo 858357 3260027 := bstep (se 1 (by rfl) ⟨2445020, by rfl⟩ : syracuseStep 3260027 = 4890041) B4890041
theorem B859771 : Blo 858357 859771 := bstep (se 1 (by rfl) ⟨644828, by rfl⟩ : syracuseStep 859771 = 1289657) B1289657
theorem B1449643 : Blo 858357 1449643 := bstep (se 1 (by rfl) ⟨1087232, by rfl⟩ : syracuseStep 1449643 = 2174465) B2174465
theorem B859823 : Blo 858357 859823 := bstep (se 1 (by rfl) ⟨644867, by rfl⟩ : syracuseStep 859823 = 1289735) B1289735
theorem B966343 : Blo 858357 966343 := bstep (se 1 (by rfl) ⟨724757, by rfl⟩ : syracuseStep 966343 = 1449515) B1449515
theorem B859847 : Blo 858357 859847 := bstep (se 1 (by rfl) ⟨644885, by rfl⟩ : syracuseStep 859847 = 1289771) B1289771
theorem B859867 : Blo 858357 859867 := bstep (se 1 (by rfl) ⟨644900, by rfl⟩ : syracuseStep 859867 = 1289801) B1289801
theorem B859943 : Blo 858357 859943 := bstep (se 1 (by rfl) ⟨644957, by rfl⟩ : syracuseStep 859943 = 1289915) B1289915
theorem B1834825 : Blo 858357 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B859983 : Blo 858357 859983 := bstep (se 1 (by rfl) ⟨644987, by rfl⟩ : syracuseStep 859983 = 1289975) B1289975
theorem B859999 : Blo 858357 859999 := bstep (se 1 (by rfl) ⟨644999, by rfl⟩ : syracuseStep 859999 = 1289999) B1289999
theorem B1933163 : Blo 858357 1933163 := bstep (se 1 (by rfl) ⟨1449872, by rfl⟩ : syracuseStep 1933163 = 2899745) B2899745
theorem B1834859 : Blo 858357 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B860027 : Blo 858357 860027 := bstep (se 1 (by rfl) ⟨645020, by rfl⟩ : syracuseStep 860027 = 1290041) B1290041
theorem B1933217 : Blo 858357 1933217 := bstep (se 2 (by rfl) ⟨724956, by rfl⟩ : syracuseStep 1933217 = 1449913) B1449913
theorem B860079 : Blo 858357 860079 := bstep (se 1 (by rfl) ⟨645059, by rfl⟩ : syracuseStep 860079 = 1290119) B1290119
theorem B1630135 : Blo 858357 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B860103 : Blo 858357 860103 := bstep (se 1 (by rfl) ⟨645077, by rfl⟩ : syracuseStep 860103 = 1290155) B1290155
theorem B1449947 : Blo 858357 1449947 := bstep (se 1 (by rfl) ⟨1087460, by rfl⟩ : syracuseStep 1449947 = 2174921) B2174921
theorem B860123 : Blo 858357 860123 := bstep (se 1 (by rfl) ⟨645092, by rfl⟩ : syracuseStep 860123 = 1290185) B1290185
theorem B3481811 : Blo 858357 3481811 := bstep (se 1 (by rfl) ⟨2611358, by rfl⟩ : syracuseStep 3481811 = 5222717) B5222717
theorem B3096787 : Blo 858357 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B1933523 : Blo 858357 1933523 := bstep (se 1 (by rfl) ⟨1450142, by rfl⟩ : syracuseStep 1933523 = 2900285) B2900285
theorem B1933577 : Blo 858357 1933577 := bstep (se 2 (by rfl) ⟨725091, by rfl⟩ : syracuseStep 1933577 = 1450183) B1450183
theorem B860447 : Blo 858357 860447 := bstep (se 1 (by rfl) ⟨645335, by rfl⟩ : syracuseStep 860447 = 1290671) B1290671
theorem B2752841 : Blo 858357 2752841 := bstep (se 2 (by rfl) ⟨1032315, by rfl⟩ : syracuseStep 2752841 = 2064631) B2064631
theorem B860507 : Blo 858357 860507 := bstep (se 1 (by rfl) ⟨645380, by rfl⟩ : syracuseStep 860507 = 1290761) B1290761
theorem B860527 : Blo 858357 860527 := bstep (se 1 (by rfl) ⟨645395, by rfl⟩ : syracuseStep 860527 = 1290791) B1290791
theorem B18825637 : Blo 858357 18825637 := bstep (se 4 (by rfl) ⟨1764903, by rfl⟩ : syracuseStep 18825637 = 3529807) B3529807
theorem B1933793 : Blo 858357 1933793 := bstep (se 2 (by rfl) ⟨725172, by rfl⟩ : syracuseStep 1933793 = 1450345) B1450345
theorem B1376831 : Blo 858357 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B3260999 : Blo 858357 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B4465249 : Blo 858357 4465249 := bstep (se 2 (by rfl) ⟨1674468, by rfl⟩ : syracuseStep 4465249 = 3348937) B3348937
theorem B9298577 : Blo 858357 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B4899473 : Blo 858357 4899473 := bstep (se 2 (by rfl) ⟨1837302, by rfl⟩ : syracuseStep 4899473 = 3674605) B3674605
theorem B4129433 : Blo 858357 4129433 := bstep (se 2 (by rfl) ⟨1548537, by rfl⟩ : syracuseStep 4129433 = 3097075) B3097075
theorem B2482859 : Blo 858357 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B2900663 : Blo 858357 2900663 := bstep (se 1 (by rfl) ⟨2175497, by rfl⟩ : syracuseStep 2900663 = 4350995) B4350995
theorem B8258249 : Blo 858357 8258249 := bstep (se 2 (by rfl) ⟨3096843, by rfl⟩ : syracuseStep 8258249 = 6193687) B6193687
theorem B1958647 : Blo 858357 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B1934099 : Blo 858357 1934099 := bstep (se 1 (by rfl) ⟨1450574, by rfl⟩ : syracuseStep 1934099 = 2901149) B2901149
theorem B6193979 : Blo 858357 6193979 := bstep (se 1 (by rfl) ⟨4645484, by rfl⟩ : syracuseStep 6193979 = 9290969) B9290969
theorem B1450831 : Blo 858357 1450831 := bstep (se 1 (by rfl) ⟨1088123, by rfl⟩ : syracuseStep 1450831 = 2176247) B2176247
theorem B2065447 : Blo 858357 2065447 := bstep (se 1 (by rfl) ⟨1549085, by rfl⟩ : syracuseStep 2065447 = 3098171) B3098171
theorem B1934459 : Blo 858357 1934459 := bstep (se 1 (by rfl) ⟨1450844, by rfl⟩ : syracuseStep 1934459 = 2901689) B2901689
theorem B1033435 : Blo 858357 1033435 := bstep (se 1 (by rfl) ⟨775076, by rfl⟩ : syracuseStep 1033435 = 1550153) B1550153
theorem B1934585 : Blo 858357 1934585 := bstep (se 2 (by rfl) ⟨725469, by rfl⟩ : syracuseStep 1934585 = 1450939) B1450939
theorem B4351319 : Blo 858357 4351319 := bstep (se 1 (by rfl) ⟨3263489, by rfl⟩ : syracuseStep 4351319 = 6526979) B6526979
theorem B1934729 : Blo 858357 1934729 := bstep (se 2 (by rfl) ⟨725523, by rfl⟩ : syracuseStep 1934729 = 1451047) B1451047
theorem B1287623 : Blo 858357 1287623 := bstep (se 1 (by rfl) ⟨965717, by rfl⟩ : syracuseStep 1287623 = 1931435) B1931435
theorem B1377785 : Blo 858357 1377785 := bstep (se 2 (by rfl) ⟨516669, by rfl⟩ : syracuseStep 1377785 = 1033339) B1033339
theorem B1451513 : Blo 858357 1451513 := bstep (se 2 (by rfl) ⟨544317, by rfl⟩ : syracuseStep 1451513 = 1088635) B1088635
theorem B1934855 : Blo 858357 1934855 := bstep (se 1 (by rfl) ⟨1451141, by rfl⟩ : syracuseStep 1934855 = 2902283) B2902283
theorem B35276309 : Blo 858357 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B3262139 : Blo 858357 3262139 := bstep (se 1 (by rfl) ⟨2446604, by rfl⟩ : syracuseStep 3262139 = 4893209) B4893209
theorem B1836731 : Blo 858357 1836731 := bstep (se 1 (by rfl) ⟨1377548, by rfl⟩ : syracuseStep 1836731 = 2755097) B2755097
theorem B1935035 : Blo 858357 1935035 := bstep (se 1 (by rfl) ⟨1451276, by rfl⟩ : syracuseStep 1935035 = 2902553) B2902553
theorem B1451783 : Blo 858357 1451783 := bstep (se 1 (by rfl) ⟨1088837, by rfl⟩ : syracuseStep 1451783 = 2177675) B2177675
theorem B3671837 : Blo 858357 3671837 := bstep (se 3 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 3671837 = 1376939) B1376939
theorem B1287977 : Blo 858357 1287977 := bstep (se 2 (by rfl) ⟨482991, by rfl⟩ : syracuseStep 1287977 = 965983) B965983
theorem B1287983 : Blo 858357 1287983 := bstep (se 1 (by rfl) ⟨965987, by rfl⟩ : syracuseStep 1287983 = 1931975) B1931975
theorem B1935161 : Blo 858357 1935161 := bstep (se 2 (by rfl) ⟨725685, by rfl⟩ : syracuseStep 1935161 = 1451371) B1451371
theorem B9922385 : Blo 858357 9922385 := bstep (se 2 (by rfl) ⟨3720894, by rfl⟩ : syracuseStep 9922385 = 7441789) B7441789
theorem B7956461 : Blo 858357 7956461 := bstep (se 3 (by rfl) ⟨1491836, by rfl⟩ : syracuseStep 7956461 = 2983673) B2983673
theorem B1550441 : Blo 858357 1550441 := bstep (se 2 (by rfl) ⟨581415, by rfl⟩ : syracuseStep 1550441 = 1162831) B1162831
theorem B4352129 : Blo 858357 4352129 := bstep (se 2 (by rfl) ⟨1632048, by rfl⟩ : syracuseStep 4352129 = 3264097) B3264097
theorem B2173139 : Blo 858357 2173139 := bstep (se 1 (by rfl) ⟨1629854, by rfl⟩ : syracuseStep 2173139 = 3259709) B3259709
theorem B1288457 : Blo 858357 1288457 := bstep (se 2 (by rfl) ⟨483171, by rfl⟩ : syracuseStep 1288457 = 966343) B966343
theorem B4892957 : Blo 858357 4892957 := bstep (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) B1834859
theorem B120760627 : Blo 858357 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B1288559 : Blo 858357 1288559 := bstep (se 1 (by rfl) ⟨966419, by rfl⟩ : syracuseStep 1288559 = 1932839) B1932839
theorem B2173351 : Blo 858357 2173351 := bstep (se 1 (by rfl) ⟨1630013, by rfl⟩ : syracuseStep 2173351 = 3260027) B3260027
theorem B4647341 : Blo 858357 4647341 := bstep (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) B1742753
theorem B1935791 : Blo 858357 1935791 := bstep (se 1 (by rfl) ⟨1451843, by rfl⟩ : syracuseStep 1935791 = 2903687) B2903687
theorem B1935827 : Blo 858357 1935827 := bstep (se 1 (by rfl) ⟨1451870, by rfl⟩ : syracuseStep 1935827 = 2903741) B2903741
theorem B1935935 : Blo 858357 1935935 := bstep (se 1 (by rfl) ⟨1451951, by rfl⟩ : syracuseStep 1935935 = 2903903) B2903903
theorem B1288775 : Blo 858357 1288775 := bstep (se 1 (by rfl) ⟨966581, by rfl⟩ : syracuseStep 1288775 = 1933163) B1933163
theorem B2173513 : Blo 858357 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B2902607 : Blo 858357 2902607 := bstep (se 1 (by rfl) ⟨2176955, by rfl⟩ : syracuseStep 2902607 = 4353911) B4353911
theorem B2067023 : Blo 858357 2067023 := bstep (se 1 (by rfl) ⟨1550267, by rfl⟩ : syracuseStep 2067023 = 3100535) B3100535
theorem B1288811 : Blo 858357 1288811 := bstep (se 1 (by rfl) ⟨966608, by rfl⟩ : syracuseStep 1288811 = 1933217) B1933217
theorem B1936043 : Blo 858357 1936043 := bstep (se 1 (by rfl) ⟨1452032, by rfl⟩ : syracuseStep 1936043 = 2904065) B2904065
theorem B3099383 : Blo 858357 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B1289039 : Blo 858357 1289039 := bstep (se 1 (by rfl) ⟨966779, by rfl⟩ : syracuseStep 1289039 = 1933559) B1933559
theorem B6278023 : Blo 858357 6278023 := bstep (se 1 (by rfl) ⟨4708517, by rfl⟩ : syracuseStep 6278023 = 9417035) B9417035
theorem B4131739 : Blo 858357 4131739 := bstep (se 1 (by rfl) ⟨3098804, by rfl⟩ : syracuseStep 4131739 = 6197609) B6197609
theorem B4352939 : Blo 858357 4352939 := bstep (se 1 (by rfl) ⟨3264704, by rfl⟩ : syracuseStep 4352939 = 6529409) B6529409
theorem B2444327 : Blo 858357 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B3263611 : Blo 858357 3263611 := bstep (se 1 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 3263611 = 4895417) B4895417
theorem B2755723 : Blo 858357 2755723 := bstep (se 1 (by rfl) ⟨2066792, by rfl⟩ : syracuseStep 2755723 = 4133585) B4133585
theorem B3484891 : Blo 858357 3484891 := bstep (se 1 (by rfl) ⟨2613668, by rfl⟩ : syracuseStep 3484891 = 5227337) B5227337
theorem B1289435 : Blo 858357 1289435 := bstep (se 1 (by rfl) ⟨967076, by rfl⟩ : syracuseStep 1289435 = 1934153) B1934153
theorem B9784637 : Blo 858357 9784637 := bstep (se 3 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 9784637 = 3669239) B3669239
theorem B2174303 : Blo 858357 2174303 := bstep (se 1 (by rfl) ⟨1630727, by rfl⟩ : syracuseStep 2174303 = 3261455) B3261455
theorem B8367457 : Blo 858357 8367457 := bstep (se 2 (by rfl) ⟨3137796, by rfl⟩ : syracuseStep 8367457 = 6275593) B6275593
theorem B14683517 : Blo 858357 14683517 := bstep (se 3 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 14683517 = 5506319) B5506319
theorem B1289609 : Blo 858357 1289609 := bstep (se 2 (by rfl) ⟨483603, by rfl⟩ : syracuseStep 1289609 = 967207) B967207
theorem B2207225 : Blo 858357 2207225 := bstep (se 2 (by rfl) ⟨827709, by rfl⟩ : syracuseStep 2207225 = 1655419) B1655419
theorem B3264083 : Blo 858357 3264083 := bstep (se 1 (by rfl) ⟨2448062, by rfl⟩ : syracuseStep 3264083 = 4896125) B4896125
theorem B1289963 : Blo 858357 1289963 := bstep (se 1 (by rfl) ⟨967472, by rfl⟩ : syracuseStep 1289963 = 1934945) B1934945
theorem B2903849 : Blo 858357 2903849 := bstep (se 2 (by rfl) ⟨1088943, by rfl⟩ : syracuseStep 2903849 = 2177887) B2177887
theorem B3141433 : Blo 858357 3141433 := bstep (se 2 (by rfl) ⟨1178037, by rfl⟩ : syracuseStep 3141433 = 2356075) B2356075
theorem B1241039 : Blo 858357 1241039 := bstep (se 1 (by rfl) ⟨930779, by rfl⟩ : syracuseStep 1241039 = 1861559) B1861559
theorem B1290191 : Blo 858357 1290191 := bstep (se 1 (by rfl) ⟨967643, by rfl⟩ : syracuseStep 1290191 = 1935287) B1935287
theorem B4354073 : Blo 858357 4354073 := bstep (se 2 (by rfl) ⟨1632777, by rfl⟩ : syracuseStep 4354073 = 3265555) B3265555
theorem B3305681 : Blo 858357 3305681 := bstep (se 2 (by rfl) ⟨1239630, by rfl⟩ : syracuseStep 3305681 = 2479261) B2479261
theorem B4133123 : Blo 858357 4133123 := bstep (se 1 (by rfl) ⟨3099842, by rfl⟩ : syracuseStep 4133123 = 6199685) B6199685
theorem B3486025 : Blo 858357 3486025 := bstep (se 2 (by rfl) ⟨1307259, by rfl⟩ : syracuseStep 3486025 = 2614519) B2614519
theorem B2445659 : Blo 858357 2445659 := bstep (se 1 (by rfl) ⟨1834244, by rfl⟩ : syracuseStep 2445659 = 3668489) B3668489
theorem B1290587 : Blo 858357 1290587 := bstep (se 1 (by rfl) ⟨967940, by rfl⟩ : syracuseStep 1290587 = 1935881) B1935881
theorem B2175407 : Blo 858357 2175407 := bstep (se 1 (by rfl) ⟨1631555, by rfl⟩ : syracuseStep 2175407 = 3263111) B3263111
theorem B2175457 : Blo 858357 2175457 := bstep (se 2 (by rfl) ⟨815796, by rfl⟩ : syracuseStep 2175457 = 1631593) B1631593
theorem B1962515 : Blo 858357 1962515 := bstep (se 1 (by rfl) ⟨1471886, by rfl⟩ : syracuseStep 1962515 = 2943773) B2943773
theorem B1290815 : Blo 858357 1290815 := bstep (se 1 (by rfl) ⟨968111, by rfl⟩ : syracuseStep 1290815 = 1936223) B1936223
theorem B3486659 : Blo 858357 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B3920903 : Blo 858357 3920903 := bstep (se 1 (by rfl) ⟨2940677, by rfl⟩ : syracuseStep 3920903 = 5881355) B5881355
theorem B2446433 : Blo 858357 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B6534269 : Blo 858357 6534269 := bstep (se 3 (by rfl) ⟨1225175, by rfl⟩ : syracuseStep 6534269 = 2450351) B2450351
theorem B931103 : Blo 858357 931103 := bstep (se 1 (by rfl) ⟨698327, by rfl⟩ : syracuseStep 931103 = 1396655) B1396655
theorem B3142955 : Blo 858357 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B2176379 : Blo 858357 2176379 := bstep (se 1 (by rfl) ⟨1632284, by rfl⟩ : syracuseStep 2176379 = 3264569) B3264569
theorem B22304165 : Blo 858357 22304165 := bstep (se 4 (by rfl) ⟨2091015, by rfl⟩ : syracuseStep 22304165 = 4182031) B4182031
theorem B5502401 : Blo 858357 5502401 := bstep (se 2 (by rfl) ⟨2063400, by rfl⟩ : syracuseStep 5502401 = 4126801) B4126801
theorem B3667463 : Blo 858357 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B45864581 : Blo 858357 45864581 := bstep (se 4 (by rfl) ⟨4299804, by rfl⟩ : syracuseStep 45864581 = 8599609) B8599609
theorem B11327521 : Blo 858357 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B2178191 : Blo 858357 2178191 := bstep (se 1 (by rfl) ⟨1633643, by rfl⟩ : syracuseStep 2178191 = 3267287) B3267287
theorem B858399 : Blo 858357 858399 := bstep (se 1 (by rfl) ⟨643799, by rfl⟩ : syracuseStep 858399 = 1287599) B1287599
theorem B858459 : Blo 858357 858459 := bstep (se 1 (by rfl) ⟨643844, by rfl⟩ : syracuseStep 858459 = 1287689) B1287689
theorem B858479 : Blo 858357 858479 := bstep (se 1 (by rfl) ⟨643859, by rfl⟩ : syracuseStep 858479 = 1287719) B1287719
theorem B2898287 : Blo 858357 2898287 := bstep (se 1 (by rfl) ⟨2173715, by rfl⟩ : syracuseStep 2898287 = 4347431) B4347431
theorem B1931687 : Blo 858357 1931687 := bstep (se 1 (by rfl) ⟨1448765, by rfl⟩ : syracuseStep 1931687 = 2897531) B2897531
theorem B858535 : Blo 858357 858535 := bstep (se 1 (by rfl) ⟨643901, by rfl⟩ : syracuseStep 858535 = 1287803) B1287803
theorem B3266999 : Blo 858357 3266999 := bstep (se 1 (by rfl) ⟨2450249, by rfl⟩ : syracuseStep 3266999 = 4900499) B4900499
theorem B4348403 : Blo 858357 4348403 := bstep (se 1 (by rfl) ⟨3261302, by rfl⟩ : syracuseStep 4348403 = 6522605) B6522605
theorem B858619 : Blo 858357 858619 := bstep (se 1 (by rfl) ⟨643964, by rfl⟩ : syracuseStep 858619 = 1287929) B1287929
theorem B2480635 : Blo 858357 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B1931795 : Blo 858357 1931795 := bstep (se 1 (by rfl) ⟨1448846, by rfl⟩ : syracuseStep 1931795 = 2897693) B2897693
theorem B14670395 : Blo 858357 14670395 := bstep (se 1 (by rfl) ⟨11002796, by rfl⟩ : syracuseStep 14670395 = 22005593) B22005593
theorem B858687 : Blo 858357 858687 := bstep (se 1 (by rfl) ⟨644015, by rfl⟩ : syracuseStep 858687 = 1288031) B1288031
theorem B858695 : Blo 858357 858695 := bstep (se 1 (by rfl) ⟨644021, by rfl⟩ : syracuseStep 858695 = 1288043) B1288043
theorem B1931849 : Blo 858357 1931849 := bstep (se 2 (by rfl) ⟨724443, by rfl⟩ : syracuseStep 1931849 = 1448887) B1448887
theorem B1546859 : Blo 858357 1546859 := bstep (se 1 (by rfl) ⟨1160144, by rfl⟩ : syracuseStep 1546859 = 2320289) B2320289
theorem B1448671 : Blo 858357 1448671 := bstep (se 1 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 1448671 = 2173007) B2173007
theorem B858847 : Blo 858357 858847 := bstep (se 1 (by rfl) ⟨644135, by rfl⟩ : syracuseStep 858847 = 1288271) B1288271
theorem B2448119 : Blo 858357 2448119 := bstep (se 1 (by rfl) ⟨1836089, by rfl⟩ : syracuseStep 2448119 = 3672179) B3672179
theorem B858927 : Blo 858357 858927 := bstep (se 1 (by rfl) ⟨644195, by rfl⟩ : syracuseStep 858927 = 1288391) B1288391
theorem B1088311 : Blo 858357 1088311 := bstep (se 1 (by rfl) ⟨816233, by rfl⟩ : syracuseStep 1088311 = 1632467) B1632467
theorem B859035 : Blo 858357 859035 := bstep (se 1 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 859035 = 1288553) B1288553
theorem B859087 : Blo 858357 859087 := bstep (se 1 (by rfl) ⟨644315, by rfl⟩ : syracuseStep 859087 = 1288631) B1288631
theorem B1932263 : Blo 858357 1932263 := bstep (se 1 (by rfl) ⟨1449197, by rfl⟩ : syracuseStep 1932263 = 2898395) B2898395
theorem B859111 : Blo 858357 859111 := bstep (se 1 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 859111 = 1288667) B1288667
theorem B4349051 : Blo 858357 4349051 := bstep (se 1 (by rfl) ⟨3261788, by rfl⟩ : syracuseStep 4349051 = 6523577) B6523577
theorem B1449103 : Blo 858357 1449103 := bstep (se 1 (by rfl) ⟨1086827, by rfl⟩ : syracuseStep 1449103 = 2173655) B2173655
theorem B1088731 : Blo 858357 1088731 := bstep (se 1 (by rfl) ⟨816548, by rfl⟩ : syracuseStep 1088731 = 1633097) B1633097
theorem B12401909 : Blo 858357 12401909 := bstep (se 5 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 12401909 = 1162679) B1162679
theorem B859423 : Blo 858357 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B859483 : Blo 858357 859483 := bstep (se 1 (by rfl) ⟨644612, by rfl⟩ : syracuseStep 859483 = 1289225) B1289225
theorem B1932641 : Blo 858357 1932641 := bstep (se 2 (by rfl) ⟨724740, by rfl⟩ : syracuseStep 1932641 = 1449481) B1449481
theorem B859503 : Blo 858357 859503 := bstep (se 1 (by rfl) ⟨644627, by rfl⟩ : syracuseStep 859503 = 1289255) B1289255
theorem B1449353 : Blo 858357 1449353 := bstep (se 2 (by rfl) ⟨543507, by rfl⟩ : syracuseStep 1449353 = 1087015) B1087015
theorem B5578121 : Blo 858357 5578121 := bstep (se 2 (by rfl) ⟨2091795, by rfl⟩ : syracuseStep 5578121 = 4183591) B4183591
theorem B24141199 : Blo 858357 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B966055 : Blo 858357 966055 := bstep (se 1 (by rfl) ⟨724541, by rfl⟩ : syracuseStep 966055 = 1449083) B1449083
theorem B859559 : Blo 858357 859559 := bstep (se 1 (by rfl) ⟨644669, by rfl⟩ : syracuseStep 859559 = 1289339) B1289339
theorem B1932731 : Blo 858357 1932731 := bstep (se 1 (by rfl) ⟨1449548, by rfl⟩ : syracuseStep 1932731 = 2899097) B2899097
theorem B859643 : Blo 858357 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B1932857 : Blo 858357 1932857 := bstep (se 2 (by rfl) ⟨724821, by rfl⟩ : syracuseStep 1932857 = 1449643) B1449643
theorem B1031743 : Blo 858357 1031743 := bstep (se 1 (by rfl) ⟨773807, by rfl⟩ : syracuseStep 1031743 = 1547615) B1547615
theorem B859711 : Blo 858357 859711 := bstep (se 1 (by rfl) ⟨644783, by rfl⟩ : syracuseStep 859711 = 1289567) B1289567
theorem B859719 : Blo 858357 859719 := bstep (se 1 (by rfl) ⟨644789, by rfl⟩ : syracuseStep 859719 = 1289579) B1289579
theorem B859871 : Blo 858357 859871 := bstep (se 1 (by rfl) ⟨644903, by rfl⟩ : syracuseStep 859871 = 1289807) B1289807
theorem B2899691 : Blo 858357 2899691 := bstep (se 1 (by rfl) ⟨2174768, by rfl⟩ : syracuseStep 2899691 = 4349537) B4349537
theorem B4349699 : Blo 858357 4349699 := bstep (se 1 (by rfl) ⟨3262274, by rfl⟩ : syracuseStep 4349699 = 6524549) B6524549
theorem B1957679 : Blo 858357 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B859951 : Blo 858357 859951 := bstep (se 1 (by rfl) ⟨644963, by rfl⟩ : syracuseStep 859951 = 1289927) B1289927
theorem B1449785 : Blo 858357 1449785 := bstep (se 2 (by rfl) ⟨543669, by rfl⟩ : syracuseStep 1449785 = 1087339) B1087339
theorem B5586749 : Blo 858357 5586749 := bstep (se 3 (by rfl) ⟨1047515, by rfl⟩ : syracuseStep 5586749 = 2095031) B2095031
theorem B3915649 : Blo 858357 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B860059 : Blo 858357 860059 := bstep (se 1 (by rfl) ⟨645044, by rfl⟩ : syracuseStep 860059 = 1290089) B1290089
theorem B860111 : Blo 858357 860111 := bstep (se 1 (by rfl) ⟨645083, by rfl⟩ : syracuseStep 860111 = 1290167) B1290167
theorem B966631 : Blo 858357 966631 := bstep (se 1 (by rfl) ⟨724973, by rfl⟩ : syracuseStep 966631 = 1449947) B1449947
theorem B860135 : Blo 858357 860135 := bstep (se 1 (by rfl) ⟨645101, by rfl⟩ : syracuseStep 860135 = 1290203) B1290203
theorem B2203787 : Blo 858357 2203787 := bstep (se 1 (by rfl) ⟨1652840, by rfl⟩ : syracuseStep 2203787 = 3305681) B3305681
theorem B1835227 : Blo 858357 1835227 := bstep (se 1 (by rfl) ⟨1376420, by rfl⟩ : syracuseStep 1835227 = 2752841) B2752841
theorem B1630439 : Blo 858357 1630439 := bstep (se 1 (by rfl) ⟨1222829, by rfl⟩ : syracuseStep 1630439 = 2445659) B2445659
theorem B860391 : Blo 858357 860391 := bstep (se 1 (by rfl) ⟨645293, by rfl⟩ : syracuseStep 860391 = 1290587) B1290587
theorem B4129049 : Blo 858357 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B1450271 : Blo 858357 1450271 := bstep (se 1 (by rfl) ⟨1087703, by rfl⟩ : syracuseStep 1450271 = 2175407) B2175407
theorem B917887 : Blo 858357 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B860543 : Blo 858357 860543 := bstep (se 1 (by rfl) ⟨645407, by rfl⟩ : syracuseStep 860543 = 1290815) B1290815
theorem B161014169 : Blo 858357 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B2752955 : Blo 858357 2752955 := bstep (se 1 (by rfl) ⟨2064716, by rfl⟩ : syracuseStep 2752955 = 4129433) B4129433
theorem B1933775 : Blo 858357 1933775 := bstep (se 1 (by rfl) ⟨1450331, by rfl⟩ : syracuseStep 1933775 = 2900663) B2900663
theorem B5505499 : Blo 858357 5505499 := bstep (se 1 (by rfl) ⟨4129124, by rfl⟩ : syracuseStep 5505499 = 8258249) B8258249
theorem B23814661 : Blo 858357 23814661 := bstep (se 4 (by rfl) ⟨2232624, by rfl⟩ : syracuseStep 23814661 = 4465249) B4465249
theorem B4129319 : Blo 858357 4129319 := bstep (se 1 (by rfl) ⟨3096989, by rfl⟩ : syracuseStep 4129319 = 6193979) B6193979
theorem B25100849 : Blo 858357 25100849 := bstep (se 2 (by rfl) ⟨9412818, by rfl⟩ : syracuseStep 25100849 = 18825637) B18825637
theorem B2900609 : Blo 858357 2900609 := bstep (se 2 (by rfl) ⟨1087728, by rfl⟩ : syracuseStep 2900609 = 2175457) B2175457
theorem B2613935 : Blo 858357 2613935 := bstep (se 1 (by rfl) ⟨1960451, by rfl⟩ : syracuseStep 2613935 = 3920903) B3920903
theorem B1630955 : Blo 858357 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B2900879 : Blo 858357 2900879 := bstep (se 1 (by rfl) ⟨2175659, by rfl⟩ : syracuseStep 2900879 = 4351319) B4351319
theorem B1450919 : Blo 858357 1450919 := bstep (se 1 (by rfl) ⟨1088189, by rfl⟩ : syracuseStep 1450919 = 2176379) B2176379
theorem B918523 : Blo 858357 918523 := bstep (se 1 (by rfl) ⟨688892, by rfl⟩ : syracuseStep 918523 = 1377785) B1377785
theorem B967675 : Blo 858357 967675 := bstep (se 1 (by rfl) ⟨725756, by rfl⟩ : syracuseStep 967675 = 1451513) B1451513
theorem B1451081 : Blo 858357 1451081 := bstep (se 2 (by rfl) ⟨544155, by rfl⟩ : syracuseStep 1451081 = 1088311) B1088311
theorem B1934441 : Blo 858357 1934441 := bstep (se 2 (by rfl) ⟨725415, by rfl⟩ : syracuseStep 1934441 = 1450831) B1450831
theorem B967855 : Blo 858357 967855 := bstep (se 1 (by rfl) ⟨725891, by rfl⟩ : syracuseStep 967855 = 1451783) B1451783
theorem B2753929 : Blo 858357 2753929 := bstep (se 2 (by rfl) ⟨1032723, by rfl⟩ : syracuseStep 2753929 = 2065447) B2065447
theorem B2901419 : Blo 858357 2901419 := bstep (se 1 (by rfl) ⟨2176064, by rfl⟩ : syracuseStep 2901419 = 4352129) B4352129
theorem B4351481 : Blo 858357 4351481 := bstep (se 2 (by rfl) ⟨1631805, by rfl⟩ : syracuseStep 4351481 = 3263611) B3263611
theorem B3261971 : Blo 858357 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B1287791 : Blo 858357 1287791 := bstep (se 1 (by rfl) ⟨965843, by rfl⟩ : syracuseStep 1287791 = 1931687) B1931687
theorem B4646521 : Blo 858357 4646521 := bstep (se 2 (by rfl) ⟨1742445, by rfl⟩ : syracuseStep 4646521 = 3484891) B3484891
theorem B1377913 : Blo 858357 1377913 := bstep (se 2 (by rfl) ⟨516717, by rfl⟩ : syracuseStep 1377913 = 1033435) B1033435
theorem B1451641 : Blo 858357 1451641 := bstep (se 2 (by rfl) ⟨544365, by rfl⟩ : syracuseStep 1451641 = 1088731) B1088731
theorem B1287863 : Blo 858357 1287863 := bstep (se 1 (by rfl) ⟨965897, by rfl⟩ : syracuseStep 1287863 = 1931795) B1931795
theorem B1287899 : Blo 858357 1287899 := bstep (se 1 (by rfl) ⟨965924, by rfl⟩ : syracuseStep 1287899 = 1931849) B1931849
theorem B1935071 : Blo 858357 1935071 := bstep (se 1 (by rfl) ⟨1451303, by rfl⟩ : syracuseStep 1935071 = 2902607) B2902607
theorem B1378015 : Blo 858357 1378015 := bstep (se 1 (by rfl) ⟨1033511, by rfl⟩ : syracuseStep 1378015 = 2067023) B2067023
theorem B6620957 : Blo 858357 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B1632079 : Blo 858357 1632079 := bstep (se 1 (by rfl) ⟨1224059, by rfl⟩ : syracuseStep 1632079 = 2448119) B2448119
theorem B2066255 : Blo 858357 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B32188265 : Blo 858357 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B1288073 : Blo 858357 1288073 := bstep (se 2 (by rfl) ⟨483027, by rfl⟩ : syracuseStep 1288073 = 966055) B966055
theorem B2901959 : Blo 858357 2901959 := bstep (se 1 (by rfl) ⟨2176469, by rfl⟩ : syracuseStep 2901959 = 4352939) B4352939
theorem B1288175 : Blo 858357 1288175 := bstep (se 1 (by rfl) ⟨966131, by rfl⟩ : syracuseStep 1288175 = 1932263) B1932263
theorem B1452127 : Blo 858357 1452127 := bstep (se 1 (by rfl) ⟨1089095, by rfl⟩ : syracuseStep 1452127 = 2178191) B2178191
theorem B8267939 : Blo 858357 8267939 := bstep (se 1 (by rfl) ⟨6200954, by rfl⟩ : syracuseStep 8267939 = 12401909) B12401909
theorem B6523091 : Blo 858357 6523091 := bstep (se 1 (by rfl) ⟨4892318, by rfl⟩ : syracuseStep 6523091 = 9784637) B9784637
theorem B1288427 : Blo 858357 1288427 := bstep (se 1 (by rfl) ⟨966320, by rfl⟩ : syracuseStep 1288427 = 1932641) B1932641
theorem B1288487 : Blo 858357 1288487 := bstep (se 1 (by rfl) ⟨966365, by rfl⟩ : syracuseStep 1288487 = 1932731) B1932731
theorem B1288571 : Blo 858357 1288571 := bstep (se 1 (by rfl) ⟨966428, by rfl⟩ : syracuseStep 1288571 = 1932857) B1932857
theorem B4188577 : Blo 858357 4188577 := bstep (se 2 (by rfl) ⟨1570716, by rfl⟩ : syracuseStep 4188577 = 3141433) B3141433
theorem B5220865 : Blo 858357 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B1935899 : Blo 858357 1935899 := bstep (se 1 (by rfl) ⟨1451924, by rfl⟩ : syracuseStep 1935899 = 2903849) B2903849
theorem B1305119 : Blo 858357 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B1288841 : Blo 858357 1288841 := bstep (se 2 (by rfl) ⟨483315, by rfl⟩ : syracuseStep 1288841 = 966631) B966631
theorem B2902715 : Blo 858357 2902715 := bstep (se 1 (by rfl) ⟨2177036, by rfl⟩ : syracuseStep 2902715 = 4354073) B4354073
theorem B2321207 : Blo 858357 2321207 := bstep (se 1 (by rfl) ⟨1740905, by rfl⟩ : syracuseStep 2321207 = 3481811) B3481811
theorem B1289015 : Blo 858357 1289015 := bstep (se 1 (by rfl) ⟨966761, by rfl⟩ : syracuseStep 1289015 = 1933523) B1933523
theorem B2755415 : Blo 858357 2755415 := bstep (se 1 (by rfl) ⟨2066561, by rfl⟩ : syracuseStep 2755415 = 4133123) B4133123
theorem B1289051 : Blo 858357 1289051 := bstep (se 1 (by rfl) ⟨966788, by rfl⟩ : syracuseStep 1289051 = 1933577) B1933577
theorem B1289195 : Blo 858357 1289195 := bstep (se 1 (by rfl) ⟨966896, by rfl⟩ : syracuseStep 1289195 = 1933793) B1933793
theorem B2173999 : Blo 858357 2173999 := bstep (se 1 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 2173999 = 3260999) B3260999
theorem B4648033 : Blo 858357 4648033 := bstep (se 2 (by rfl) ⟨1743012, by rfl⟩ : syracuseStep 4648033 = 3486025) B3486025
theorem B1289399 : Blo 858357 1289399 := bstep (se 1 (by rfl) ⟨967049, by rfl⟩ : syracuseStep 1289399 = 1934099) B1934099
theorem B1289639 : Blo 858357 1289639 := bstep (se 1 (by rfl) ⟨967229, by rfl⟩ : syracuseStep 1289639 = 1934459) B1934459
theorem B1289723 : Blo 858357 1289723 := bstep (se 1 (by rfl) ⟨967292, by rfl⟩ : syracuseStep 1289723 = 1934585) B1934585
theorem B1289819 : Blo 858357 1289819 := bstep (se 1 (by rfl) ⟨967364, by rfl⟩ : syracuseStep 1289819 = 1934729) B1934729
theorem B2444975 : Blo 858357 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B1289903 : Blo 858357 1289903 := bstep (se 1 (by rfl) ⟨967427, by rfl⟩ : syracuseStep 1289903 = 1934855) B1934855
theorem B59477773 : Blo 858357 59477773 := bstep (se 3 (by rfl) ⟨11152082, by rfl⟩ : syracuseStep 59477773 = 22304165) B22304165
theorem B2174759 : Blo 858357 2174759 := bstep (se 1 (by rfl) ⟨1631069, by rfl⟩ : syracuseStep 2174759 = 3262139) B3262139
theorem B1224487 : Blo 858357 1224487 := bstep (se 1 (by rfl) ⟨918365, by rfl⟩ : syracuseStep 1224487 = 1836731) B1836731
theorem B1290023 : Blo 858357 1290023 := bstep (se 1 (by rfl) ⟨967517, by rfl⟩ : syracuseStep 1290023 = 1935035) B1935035
theorem B5508985 : Blo 858357 5508985 := bstep (se 2 (by rfl) ⟨2065869, by rfl⟩ : syracuseStep 5508985 = 4131739) B4131739
theorem B1290107 : Blo 858357 1290107 := bstep (se 1 (by rfl) ⟨967580, by rfl⟩ : syracuseStep 1290107 = 1935161) B1935161
theorem B39727061 : Blo 858357 39727061 := bstep (se 7 (by rfl) ⟨465551, by rfl⟩ : syracuseStep 39727061 = 931103) B931103
theorem B5304307 : Blo 858357 5304307 := bstep (se 1 (by rfl) ⟨3978230, by rfl⟩ : syracuseStep 5304307 = 7956461) B7956461
theorem B3674297 : Blo 858357 3674297 := bstep (se 2 (by rfl) ⟨1377861, by rfl⟩ : syracuseStep 3674297 = 2755723) B2755723
theorem B1290527 : Blo 858357 1290527 := bstep (se 1 (by rfl) ⟨967895, by rfl⟩ : syracuseStep 1290527 = 1935791) B1935791
theorem B1290551 : Blo 858357 1290551 := bstep (se 1 (by rfl) ⟨967913, by rfl⟩ : syracuseStep 1290551 = 1935827) B1935827
theorem B1290623 : Blo 858357 1290623 := bstep (se 1 (by rfl) ⟨967967, by rfl⟩ : syracuseStep 1290623 = 1935935) B1935935
theorem B1290695 : Blo 858357 1290695 := bstep (se 1 (by rfl) ⟨968021, by rfl⟩ : syracuseStep 1290695 = 1936043) B1936043
theorem B1471483 : Blo 858357 1471483 := bstep (se 1 (by rfl) ⟨1103612, by rfl⟩ : syracuseStep 1471483 = 2207225) B2207225
theorem B2176055 : Blo 858357 2176055 := bstep (se 1 (by rfl) ⟨1632041, by rfl⟩ : syracuseStep 2176055 = 3264083) B3264083
theorem B3724499 : Blo 858357 3724499 := bstep (se 1 (by rfl) ⟨2793374, by rfl⟩ : syracuseStep 3724499 = 5586749) B5586749
theorem B15103361 : Blo 858357 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B4134509 : Blo 858357 4134509 := bstep (se 3 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 4134509 = 1550441) B1550441
theorem B5502629 : Blo 858357 5502629 := bstep (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) B1031743
theorem B3266315 : Blo 858357 3266315 := bstep (se 1 (by rfl) ⟨2449736, by rfl⟩ : syracuseStep 3266315 = 4899473) B4899473
theorem B2897801 : Blo 858357 2897801 := bstep (se 2 (by rfl) ⟨1086675, by rfl⟩ : syracuseStep 2897801 = 2173351) B2173351
theorem B4356179 : Blo 858357 4356179 := bstep (se 1 (by rfl) ⟨3267134, by rfl⟩ : syracuseStep 4356179 = 6534269) B6534269
theorem B2898017 : Blo 858357 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B2095303 : Blo 858357 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B1931561 : Blo 858357 1931561 := bstep (se 2 (by rfl) ⟨724335, by rfl⟩ : syracuseStep 1931561 = 1448671) B1448671
theorem B3668267 : Blo 858357 3668267 := bstep (se 1 (by rfl) ⟨2751200, by rfl⟩ : syracuseStep 3668267 = 5502401) B5502401
theorem B858415 : Blo 858357 858415 := bstep (se 1 (by rfl) ⟨643811, by rfl⟩ : syracuseStep 858415 = 1287623) B1287623
theorem B2611529 : Blo 858357 2611529 := bstep (se 2 (by rfl) ⟨979323, by rfl⟩ : syracuseStep 2611529 = 1958647) B1958647
theorem B23517539 : Blo 858357 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B12392909 : Blo 858357 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B8370697 : Blo 858357 8370697 := bstep (se 2 (by rfl) ⟨3139011, by rfl⟩ : syracuseStep 8370697 = 6278023) B6278023
theorem B2447891 : Blo 858357 2447891 := bstep (se 1 (by rfl) ⟨1835918, by rfl⟩ : syracuseStep 2447891 = 3671837) B3671837
theorem B858651 : Blo 858357 858651 := bstep (se 1 (by rfl) ⟨643988, by rfl⟩ : syracuseStep 858651 = 1287977) B1287977
theorem B858655 : Blo 858357 858655 := bstep (se 1 (by rfl) ⟨643991, by rfl⟩ : syracuseStep 858655 = 1287983) B1287983
theorem B5233373 : Blo 858357 5233373 := bstep (se 3 (by rfl) ⟨981257, by rfl⟩ : syracuseStep 5233373 = 1962515) B1962515
theorem B1448759 : Blo 858357 1448759 := bstep (se 1 (by rfl) ⟨1086569, by rfl⟩ : syracuseStep 1448759 = 2173139) B2173139
theorem B858971 : Blo 858357 858971 := bstep (se 1 (by rfl) ⟨644228, by rfl⟩ : syracuseStep 858971 = 1288457) B1288457
theorem B1932137 : Blo 858357 1932137 := bstep (se 2 (by rfl) ⟨724551, by rfl⟩ : syracuseStep 1932137 = 1449103) B1449103
theorem B1932191 : Blo 858357 1932191 := bstep (se 1 (by rfl) ⟨1449143, by rfl⟩ : syracuseStep 1932191 = 2898287) B2898287
theorem B859039 : Blo 858357 859039 := bstep (se 1 (by rfl) ⟨644279, by rfl⟩ : syracuseStep 859039 = 1288559) B1288559
theorem B2177999 : Blo 858357 2177999 := bstep (se 1 (by rfl) ⟨1633499, by rfl⟩ : syracuseStep 2177999 = 3266999) B3266999
theorem B2898935 : Blo 858357 2898935 := bstep (se 1 (by rfl) ⟨2174201, by rfl⟩ : syracuseStep 2898935 = 4348403) B4348403
theorem B122305549 : Blo 858357 122305549 := bstep (se 3 (by rfl) ⟨22932290, by rfl⟩ : syracuseStep 122305549 = 45864581) B45864581
theorem B9780263 : Blo 858357 9780263 := bstep (se 1 (by rfl) ⟨7335197, by rfl⟩ : syracuseStep 9780263 = 14670395) B14670395
theorem B859183 : Blo 858357 859183 := bstep (se 1 (by rfl) ⟨644387, by rfl⟩ : syracuseStep 859183 = 1288775) B1288775
theorem B24796205 : Blo 858357 24796205 := bstep (se 3 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 24796205 = 9298577) B9298577
theorem B1031239 : Blo 858357 1031239 := bstep (se 1 (by rfl) ⟨773429, by rfl⟩ : syracuseStep 1031239 = 1546859) B1546859
theorem B859207 : Blo 858357 859207 := bstep (se 1 (by rfl) ⟨644405, by rfl⟩ : syracuseStep 859207 = 1288811) B1288811
theorem B11156609 : Blo 858357 11156609 := bstep (se 2 (by rfl) ⟨4183728, by rfl⟩ : syracuseStep 11156609 = 8367457) B8367457
theorem B859359 : Blo 858357 859359 := bstep (se 1 (by rfl) ⟨644519, by rfl⟩ : syracuseStep 859359 = 1289039) B1289039
theorem B1629551 : Blo 858357 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B2899367 : Blo 858357 2899367 := bstep (se 1 (by rfl) ⟨2174525, by rfl⟩ : syracuseStep 2899367 = 4349051) B4349051
theorem B859623 : Blo 858357 859623 := bstep (se 1 (by rfl) ⟨644717, by rfl⟩ : syracuseStep 859623 = 1289435) B1289435
theorem B26459693 : Blo 858357 26459693 := bstep (se 3 (by rfl) ⟨4961192, by rfl⟩ : syracuseStep 26459693 = 9922385) B9922385
theorem B1449535 : Blo 858357 1449535 := bstep (se 1 (by rfl) ⟨1087151, by rfl⟩ : syracuseStep 1449535 = 2174303) B2174303
theorem B9789011 : Blo 858357 9789011 := bstep (se 1 (by rfl) ⟨7341758, by rfl⟩ : syracuseStep 9789011 = 14683517) B14683517
theorem B966235 : Blo 858357 966235 := bstep (se 1 (by rfl) ⟨724676, by rfl⟩ : syracuseStep 966235 = 1449353) B1449353
theorem B3718747 : Blo 858357 3718747 := bstep (se 1 (by rfl) ⟨2789060, by rfl⟩ : syracuseStep 3718747 = 5578121) B5578121
theorem B859739 : Blo 858357 859739 := bstep (se 1 (by rfl) ⟨644804, by rfl⟩ : syracuseStep 859739 = 1289609) B1289609
theorem B1933127 : Blo 858357 1933127 := bstep (se 1 (by rfl) ⟨1449845, by rfl⟩ : syracuseStep 1933127 = 2899691) B2899691
theorem B859975 : Blo 858357 859975 := bstep (se 1 (by rfl) ⟨644981, by rfl⟩ : syracuseStep 859975 = 1289963) B1289963
theorem B2899799 : Blo 858357 2899799 := bstep (se 1 (by rfl) ⟨2174849, by rfl⟩ : syracuseStep 2899799 = 4349699) B4349699
theorem B9297757 : Blo 858357 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B966523 : Blo 858357 966523 := bstep (se 1 (by rfl) ⟨724892, by rfl⟩ : syracuseStep 966523 = 1449785) B1449785
theorem B3309437 : Blo 858357 3309437 := bstep (se 3 (by rfl) ⟨620519, by rfl⟩ : syracuseStep 3309437 = 1241039) B1241039
theorem B860127 : Blo 858357 860127 := bstep (se 1 (by rfl) ⟨645095, by rfl⟩ : syracuseStep 860127 = 1290191) B1290191
theorem B13230053 : Blo 858357 13230053 := bstep (se 4 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 13230053 = 2480635) B2480635
theorem B2449531 : Blo 858357 2449531 := bstep (se 1 (by rfl) ⟨1837148, by rfl⟩ : syracuseStep 2449531 = 3674297) B3674297
theorem B2752699 : Blo 858357 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B966847 : Blo 858357 966847 := bstep (se 1 (by rfl) ⟨725135, by rfl⟩ : syracuseStep 966847 = 1450271) B1450271
theorem B860351 : Blo 858357 860351 := bstep (se 1 (by rfl) ⟨645263, by rfl⟩ : syracuseStep 860351 = 1290527) B1290527
theorem B860367 : Blo 858357 860367 := bstep (se 1 (by rfl) ⟨645275, by rfl⟩ : syracuseStep 860367 = 1290551) B1290551
theorem B860415 : Blo 858357 860415 := bstep (se 1 (by rfl) ⟨645311, by rfl⟩ : syracuseStep 860415 = 1290623) B1290623
theorem B2793737 : Blo 858357 2793737 := bstep (se 2 (by rfl) ⟨1047651, by rfl⟩ : syracuseStep 2793737 = 2095303) B2095303
theorem B1835303 : Blo 858357 1835303 := bstep (se 1 (by rfl) ⟨1376477, by rfl⟩ : syracuseStep 1835303 = 2752955) B2752955
theorem B860463 : Blo 858357 860463 := bstep (se 1 (by rfl) ⟨645347, by rfl⟩ : syracuseStep 860463 = 1290695) B1290695
theorem B2752879 : Blo 858357 2752879 := bstep (se 1 (by rfl) ⟨2064659, by rfl⟩ : syracuseStep 2752879 = 4129319) B4129319
theorem B1933739 : Blo 858357 1933739 := bstep (se 1 (by rfl) ⟨1450304, by rfl⟩ : syracuseStep 1933739 = 2900609) B2900609
theorem B24789509 : Blo 858357 24789509 := bstep (se 4 (by rfl) ⟨2324016, by rfl⟩ : syracuseStep 24789509 = 4648033) B4648033
theorem B1933919 : Blo 858357 1933919 := bstep (se 1 (by rfl) ⟨1450439, by rfl⟩ : syracuseStep 1933919 = 2900879) B2900879
theorem B967279 : Blo 858357 967279 := bstep (se 1 (by rfl) ⟨725459, by rfl⟩ : syracuseStep 967279 = 1450919) B1450919
theorem B7340665 : Blo 858357 7340665 := bstep (se 2 (by rfl) ⟨2752749, by rfl⟩ : syracuseStep 7340665 = 5505499) B5505499
theorem B31752881 : Blo 858357 31752881 := bstep (se 2 (by rfl) ⟨11907330, by rfl⟩ : syracuseStep 31752881 = 23814661) B23814661
theorem B1450703 : Blo 858357 1450703 := bstep (se 1 (by rfl) ⟨1088027, by rfl⟩ : syracuseStep 1450703 = 2176055) B2176055
theorem B967387 : Blo 858357 967387 := bstep (se 1 (by rfl) ⟨725540, by rfl⟩ : syracuseStep 967387 = 1451081) B1451081
theorem B10068907 : Blo 858357 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B1934279 : Blo 858357 1934279 := bstep (se 1 (by rfl) ⟨1450709, by rfl⟩ : syracuseStep 1934279 = 2901419) B2901419
theorem B2900987 : Blo 858357 2900987 := bstep (se 1 (by rfl) ⟨2175740, by rfl⟩ : syracuseStep 2900987 = 4351481) B4351481
theorem B7349413 : Blo 858357 7349413 := bstep (se 4 (by rfl) ⟨689007, by rfl⟩ : syracuseStep 7349413 = 1378015) B1378015
theorem B1377503 : Blo 858357 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B1934639 : Blo 858357 1934639 := bstep (se 1 (by rfl) ⟨1450979, by rfl⟩ : syracuseStep 1934639 = 2901959) B2901959
theorem B1287707 : Blo 858357 1287707 := bstep (se 1 (by rfl) ⟨965780, by rfl⟩ : syracuseStep 1287707 = 1931561) B1931561
theorem B1631927 : Blo 858357 1631927 := bstep (se 1 (by rfl) ⟨1223945, by rfl⟩ : syracuseStep 1631927 = 2447891) B2447891
theorem B1935143 : Blo 858357 1935143 := bstep (se 1 (by rfl) ⟨1451357, by rfl⟩ : syracuseStep 1935143 = 2902715) B2902715
theorem B3671905 : Blo 858357 3671905 := bstep (se 2 (by rfl) ⟨1376964, by rfl⟩ : syracuseStep 3671905 = 2753929) B2753929
theorem B1288091 : Blo 858357 1288091 := bstep (se 1 (by rfl) ⟨966068, by rfl⟩ : syracuseStep 1288091 = 1932137) B1932137
theorem B1288127 : Blo 858357 1288127 := bstep (se 1 (by rfl) ⟨966095, by rfl⟩ : syracuseStep 1288127 = 1932191) B1932191
theorem B1451999 : Blo 858357 1451999 := bstep (se 1 (by rfl) ⟨1088999, by rfl⟩ : syracuseStep 1451999 = 2177999) B2177999
theorem B1288313 : Blo 858357 1288313 := bstep (se 2 (by rfl) ⟨483117, by rfl⟩ : syracuseStep 1288313 = 966235) B966235
theorem B4958329 : Blo 858357 4958329 := bstep (se 2 (by rfl) ⟨1859373, by rfl⟩ : syracuseStep 4958329 = 3718747) B3718747
theorem B6195361 : Blo 858357 6195361 := bstep (se 2 (by rfl) ⟨2323260, by rfl⟩ : syracuseStep 6195361 = 4646521) B4646521
theorem B1837217 : Blo 858357 1837217 := bstep (se 2 (by rfl) ⟨688956, by rfl⟩ : syracuseStep 1837217 = 1377913) B1377913
theorem B1935521 : Blo 858357 1935521 := bstep (se 2 (by rfl) ⟨725820, by rfl⟩ : syracuseStep 1935521 = 1451641) B1451641
theorem B17639795 : Blo 858357 17639795 := bstep (se 1 (by rfl) ⟨13229846, by rfl⟩ : syracuseStep 17639795 = 26459693) B26459693
theorem B1632649 : Blo 858357 1632649 := bstep (se 2 (by rfl) ⟨612243, by rfl⟩ : syracuseStep 1632649 = 1224487) B1224487
theorem B12397009 : Blo 858357 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B1288697 : Blo 858357 1288697 := bstep (se 2 (by rfl) ⟨483261, by rfl⟩ : syracuseStep 1288697 = 966523) B966523
theorem B1288751 : Blo 858357 1288751 := bstep (se 1 (by rfl) ⟨966563, by rfl⟩ : syracuseStep 1288751 = 1933127) B1933127
theorem B2206291 : Blo 858357 2206291 := bstep (se 1 (by rfl) ⟨1654718, by rfl⟩ : syracuseStep 2206291 = 3309437) B3309437
theorem B7072409 : Blo 858357 7072409 := bstep (se 2 (by rfl) ⟨2652153, by rfl⟩ : syracuseStep 7072409 = 5304307) B5304307
theorem B1469191 : Blo 858357 1469191 := bstep (se 1 (by rfl) ⟨1101893, by rfl⟩ : syracuseStep 1469191 = 2203787) B2203787
theorem B1936169 : Blo 858357 1936169 := bstep (se 2 (by rfl) ⟨726063, by rfl⟩ : syracuseStep 1936169 = 1452127) B1452127
theorem B107342779 : Blo 858357 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B1289183 : Blo 858357 1289183 := bstep (se 1 (by rfl) ⟨966887, by rfl⟩ : syracuseStep 1289183 = 1933775) B1933775
theorem B1223849 : Blo 858357 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B9931997 : Blo 858357 9931997 := bstep (se 3 (by rfl) ⟨1862249, by rfl⟩ : syracuseStep 9931997 = 3724499) B3724499
theorem B11160929 : Blo 858357 11160929 := bstep (se 2 (by rfl) ⟨4185348, by rfl⟩ : syracuseStep 11160929 = 8370697) B8370697
theorem B1289627 : Blo 858357 1289627 := bstep (se 1 (by rfl) ⟨967220, by rfl⟩ : syracuseStep 1289627 = 1934441) B1934441
theorem B2174647 : Blo 858357 2174647 := bstep (se 1 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 2174647 = 3261971) B3261971
theorem B2756339 : Blo 858357 2756339 := bstep (se 1 (by rfl) ⟨2067254, by rfl⟩ : syracuseStep 2756339 = 4134509) B4134509
theorem B1290047 : Blo 858357 1290047 := bstep (se 1 (by rfl) ⟨967535, by rfl⟩ : syracuseStep 1290047 = 1935071) B1935071
theorem B21458843 : Blo 858357 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B1290233 : Blo 858357 1290233 := bstep (se 2 (by rfl) ⟨483837, by rfl⟩ : syracuseStep 1290233 = 967675) B967675
theorem B1961977 : Blo 858357 1961977 := bstep (se 2 (by rfl) ⟨735741, by rfl⟩ : syracuseStep 1961977 = 1471483) B1471483
theorem B163074065 : Blo 858357 163074065 := bstep (se 2 (by rfl) ⟨61152774, by rfl⟩ : syracuseStep 163074065 = 122305549) B122305549
theorem B2904119 : Blo 858357 2904119 := bstep (se 1 (by rfl) ⟨2178089, by rfl⟩ : syracuseStep 2904119 = 4356179) B4356179
theorem B2445511 : Blo 858357 2445511 := bstep (se 1 (by rfl) ⟨1834133, by rfl⟩ : syracuseStep 2445511 = 3668267) B3668267
theorem B1741019 : Blo 858357 1741019 := bstep (se 1 (by rfl) ⟨1305764, by rfl⟩ : syracuseStep 1741019 = 2611529) B2611529
theorem B1290473 : Blo 858357 1290473 := bstep (se 2 (by rfl) ⟨483927, by rfl⟩ : syracuseStep 1290473 = 967855) B967855
theorem B8261939 : Blo 858357 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B1290599 : Blo 858357 1290599 := bstep (se 1 (by rfl) ⟨967949, by rfl⟩ : syracuseStep 1290599 = 1935899) B1935899
theorem B1086367 : Blo 858357 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B79303697 : Blo 858357 79303697 := bstep (se 2 (by rfl) ⟨29738886, by rfl⟩ : syracuseStep 79303697 = 59477773) B59477773
theorem B6526007 : Blo 858357 6526007 := bstep (se 1 (by rfl) ⟨4894505, by rfl⟩ : syracuseStep 6526007 = 9789011) B9789011
theorem B2176105 : Blo 858357 2176105 := bstep (se 2 (by rfl) ⟨816039, by rfl⟩ : syracuseStep 2176105 = 1632079) B1632079
theorem B7345313 : Blo 858357 7345313 := bstep (se 2 (by rfl) ⟨2754492, by rfl⟩ : syracuseStep 7345313 = 5508985) B5508985
theorem B8820035 : Blo 858357 8820035 := bstep (se 1 (by rfl) ⟨6615026, by rfl⟩ : syracuseStep 8820035 = 13230053) B13230053
theorem B1086959 : Blo 858357 1086959 := bstep (se 1 (by rfl) ⟨815219, by rfl⟩ : syracuseStep 1086959 = 1630439) B1630439
theorem B2446969 : Blo 858357 2446969 := bstep (se 2 (by rfl) ⟨917613, by rfl⟩ : syracuseStep 2446969 = 1835227) B1835227
theorem B16733899 : Blo 858357 16733899 := bstep (se 1 (by rfl) ⟨12550424, by rfl⟩ : syracuseStep 16733899 = 25100849) B25100849
theorem B5584769 : Blo 858357 5584769 := bstep (se 2 (by rfl) ⟨2094288, by rfl⟩ : syracuseStep 5584769 = 4188577) B4188577
theorem B6961153 : Blo 858357 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B858527 : Blo 858357 858527 := bstep (se 1 (by rfl) ⟨643895, by rfl⟩ : syracuseStep 858527 = 1287791) B1287791
theorem B3668419 : Blo 858357 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B858575 : Blo 858357 858575 := bstep (se 1 (by rfl) ⟨643931, by rfl⟩ : syracuseStep 858575 = 1287863) B1287863
theorem B858599 : Blo 858357 858599 := bstep (se 1 (by rfl) ⟨643949, by rfl⟩ : syracuseStep 858599 = 1287899) B1287899
theorem B2177543 : Blo 858357 2177543 := bstep (se 1 (by rfl) ⟨1633157, by rfl⟩ : syracuseStep 2177543 = 3266315) B3266315
theorem B4413971 : Blo 858357 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B1931867 : Blo 858357 1931867 := bstep (se 1 (by rfl) ⟨1448900, by rfl⟩ : syracuseStep 1931867 = 2897801) B2897801
theorem B858715 : Blo 858357 858715 := bstep (se 1 (by rfl) ⟨644036, by rfl⟩ : syracuseStep 858715 = 1288073) B1288073
theorem B858783 : Blo 858357 858783 := bstep (se 1 (by rfl) ⟨644087, by rfl⟩ : syracuseStep 858783 = 1288175) B1288175
theorem B2898665 : Blo 858357 2898665 := bstep (se 2 (by rfl) ⟨1086999, by rfl⟩ : syracuseStep 2898665 = 2173999) B2173999
theorem B1932011 : Blo 858357 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B3480317 : Blo 858357 3480317 := bstep (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) B1305119
theorem B1374985 : Blo 858357 1374985 := bstep (se 2 (by rfl) ⟨515619, by rfl⟩ : syracuseStep 1374985 = 1031239) B1031239
theorem B5511959 : Blo 858357 5511959 := bstep (se 1 (by rfl) ⟨4133969, by rfl⟩ : syracuseStep 5511959 = 8267939) B8267939
theorem B4348727 : Blo 858357 4348727 := bstep (se 1 (by rfl) ⟨3261545, by rfl⟩ : syracuseStep 4348727 = 6523091) B6523091
theorem B858951 : Blo 858357 858951 := bstep (se 1 (by rfl) ⟨644213, by rfl⟩ : syracuseStep 858951 = 1288427) B1288427
theorem B858991 : Blo 858357 858991 := bstep (se 1 (by rfl) ⟨644243, by rfl⟩ : syracuseStep 858991 = 1288487) B1288487
theorem B15678359 : Blo 858357 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B859047 : Blo 858357 859047 := bstep (se 1 (by rfl) ⟨644285, by rfl⟩ : syracuseStep 859047 = 1288571) B1288571
theorem B859227 : Blo 858357 859227 := bstep (se 1 (by rfl) ⟨644420, by rfl⟩ : syracuseStep 859227 = 1288841) B1288841
theorem B6970493 : Blo 858357 6970493 := bstep (se 3 (by rfl) ⟨1306967, by rfl⟩ : syracuseStep 6970493 = 2613935) B2613935
theorem B3488915 : Blo 858357 3488915 := bstep (se 1 (by rfl) ⟨2616686, by rfl⟩ : syracuseStep 3488915 = 5233373) B5233373
theorem B965839 : Blo 858357 965839 := bstep (se 1 (by rfl) ⟨724379, by rfl⟩ : syracuseStep 965839 = 1448759) B1448759
theorem B1547471 : Blo 858357 1547471 := bstep (se 1 (by rfl) ⟨1160603, by rfl⟩ : syracuseStep 1547471 = 2321207) B2321207
theorem B859343 : Blo 858357 859343 := bstep (se 1 (by rfl) ⟨644507, by rfl⟩ : syracuseStep 859343 = 1289015) B1289015
theorem B859367 : Blo 858357 859367 := bstep (se 1 (by rfl) ⟨644525, by rfl⟩ : syracuseStep 859367 = 1289051) B1289051
theorem B4349213 : Blo 858357 4349213 := bstep (se 3 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 4349213 = 1630955) B1630955
theorem B859463 : Blo 858357 859463 := bstep (se 1 (by rfl) ⟨644597, by rfl⟩ : syracuseStep 859463 = 1289195) B1289195
theorem B1932623 : Blo 858357 1932623 := bstep (se 1 (by rfl) ⟨1449467, by rfl⟩ : syracuseStep 1932623 = 2898935) B2898935
theorem B6520175 : Blo 858357 6520175 := bstep (se 1 (by rfl) ⟨4890131, by rfl⟩ : syracuseStep 6520175 = 9780263) B9780263
theorem B16530803 : Blo 858357 16530803 := bstep (se 1 (by rfl) ⟨12398102, by rfl⟩ : syracuseStep 16530803 = 24796205) B24796205
theorem B1932713 : Blo 858357 1932713 := bstep (se 2 (by rfl) ⟨724767, by rfl⟩ : syracuseStep 1932713 = 1449535) B1449535
theorem B7437739 : Blo 858357 7437739 := bstep (se 1 (by rfl) ⟨5578304, by rfl⟩ : syracuseStep 7437739 = 11156609) B11156609
theorem B859599 : Blo 858357 859599 := bstep (se 1 (by rfl) ⟨644699, by rfl⟩ : syracuseStep 859599 = 1289399) B1289399
theorem B7347773 : Blo 858357 7347773 := bstep (se 3 (by rfl) ⟨1377707, by rfl⟩ : syracuseStep 7347773 = 2755415) B2755415
theorem B1932911 : Blo 858357 1932911 := bstep (se 1 (by rfl) ⟨1449683, by rfl⟩ : syracuseStep 1932911 = 2899367) B2899367
theorem B859759 : Blo 858357 859759 := bstep (se 1 (by rfl) ⟨644819, by rfl⟩ : syracuseStep 859759 = 1289639) B1289639
theorem B859815 : Blo 858357 859815 := bstep (se 1 (by rfl) ⟨644861, by rfl⟩ : syracuseStep 859815 = 1289723) B1289723
theorem B859879 : Blo 858357 859879 := bstep (se 1 (by rfl) ⟨644909, by rfl⟩ : syracuseStep 859879 = 1289819) B1289819
theorem B1629983 : Blo 858357 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B859935 : Blo 858357 859935 := bstep (se 1 (by rfl) ⟨644951, by rfl⟩ : syracuseStep 859935 = 1289903) B1289903
theorem B1449839 : Blo 858357 1449839 := bstep (se 1 (by rfl) ⟨1087379, by rfl⟩ : syracuseStep 1449839 = 2174759) B2174759
theorem B860015 : Blo 858357 860015 := bstep (se 1 (by rfl) ⟨645011, by rfl⟩ : syracuseStep 860015 = 1290023) B1290023
theorem B1933199 : Blo 858357 1933199 := bstep (se 1 (by rfl) ⟨1449899, by rfl⟩ : syracuseStep 1933199 = 2899799) B2899799
theorem B860071 : Blo 858357 860071 := bstep (se 1 (by rfl) ⟨645053, by rfl⟩ : syracuseStep 860071 = 1290107) B1290107
theorem B26484707 : Blo 858357 26484707 := bstep (se 1 (by rfl) ⟨19863530, by rfl⟩ : syracuseStep 26484707 = 39727061) B39727061
theorem B4898789 : Blo 858357 4898789 := bstep (se 4 (by rfl) ⟨459261, by rfl⟩ : syracuseStep 4898789 = 918523) B918523
theorem B9281537 : Blo 858357 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B434864173 : Blo 858357 434864173 := bstep (se 3 (by rfl) ⟨81537032, by rfl⟩ : syracuseStep 434864173 = 163074065) B163074065
theorem B860315 : Blo 858357 860315 := bstep (se 1 (by rfl) ⟨645236, by rfl⟩ : syracuseStep 860315 = 1290473) B1290473
theorem B6611105 : Blo 858357 6611105 := bstep (se 2 (by rfl) ⟨2479164, by rfl⟩ : syracuseStep 6611105 = 4958329) B4958329
theorem B860399 : Blo 858357 860399 := bstep (se 1 (by rfl) ⟨645299, by rfl⟩ : syracuseStep 860399 = 1290599) B1290599
theorem B3670265 : Blo 858357 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B3260681 : Blo 858357 3260681 := bstep (se 2 (by rfl) ⟨1222755, by rfl⟩ : syracuseStep 3260681 = 2445511) B2445511
theorem B18587981 : Blo 858357 18587981 := bstep (se 3 (by rfl) ⟨3485246, by rfl⟩ : syracuseStep 18587981 = 6970493) B6970493
theorem B21168587 : Blo 858357 21168587 := bstep (se 1 (by rfl) ⟨15876440, by rfl⟩ : syracuseStep 21168587 = 31752881) B31752881
theorem B967135 : Blo 858357 967135 := bstep (se 1 (by rfl) ⟨725351, by rfl⟩ : syracuseStep 967135 = 1450703) B1450703
theorem B3670505 : Blo 858357 3670505 := bstep (se 2 (by rfl) ⟨1376439, by rfl⟩ : syracuseStep 3670505 = 2752879) B2752879
theorem B4891225 : Blo 858357 4891225 := bstep (se 2 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 4891225 = 3668419) B3668419
theorem B1933991 : Blo 858357 1933991 := bstep (se 1 (by rfl) ⟨1450493, by rfl⟩ : syracuseStep 1933991 = 2900987) B2900987
theorem B4350671 : Blo 858357 4350671 := bstep (se 1 (by rfl) ⟨3263003, by rfl⟩ : syracuseStep 4350671 = 6526007) B6526007
theorem B2941721 : Blo 858357 2941721 := bstep (se 2 (by rfl) ⟨1103145, by rfl⟩ : syracuseStep 2941721 = 2206291) B2206291
theorem B918335 : Blo 858357 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B47039453 : Blo 858357 47039453 := bstep (se 3 (by rfl) ⟨8819897, by rfl⟩ : syracuseStep 47039453 = 17639795) B17639795
theorem B1958921 : Blo 858357 1958921 := bstep (se 2 (by rfl) ⟨734595, by rfl⟩ : syracuseStep 1958921 = 1469191) B1469191
theorem B143123705 : Blo 858357 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B967999 : Blo 858357 967999 := bstep (se 1 (by rfl) ⟨725999, by rfl⟩ : syracuseStep 967999 = 1451999) B1451999
theorem B7333253 : Blo 858357 7333253 := bstep (se 4 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 7333253 = 1374985) B1374985
theorem B2901473 : Blo 858357 2901473 := bstep (se 2 (by rfl) ⟨1088052, by rfl⟩ : syracuseStep 2901473 = 2176105) B2176105
theorem B9799217 : Blo 858357 9799217 := bstep (se 2 (by rfl) ⟨3674706, by rfl⟩ : syracuseStep 9799217 = 7349413) B7349413
theorem B1287785 : Blo 858357 1287785 := bstep (se 2 (by rfl) ⟨482919, by rfl⟩ : syracuseStep 1287785 = 965839) B965839
theorem B1451695 : Blo 858357 1451695 := bstep (se 1 (by rfl) ⟨1088771, by rfl⟩ : syracuseStep 1451695 = 2177543) B2177543
theorem B2942647 : Blo 858357 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B1287911 : Blo 858357 1287911 := bstep (se 1 (by rfl) ⟨965933, by rfl⟩ : syracuseStep 1287911 = 1931867) B1931867
theorem B4351805 : Blo 858357 4351805 := bstep (se 3 (by rfl) ⟨815963, by rfl⟩ : syracuseStep 4351805 = 1631927) B1631927
theorem B1288007 : Blo 858357 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B2320211 : Blo 858357 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B6621331 : Blo 858357 6621331 := bstep (se 1 (by rfl) ⟨4965998, by rfl⟩ : syracuseStep 6621331 = 9931997) B9931997
theorem B3262625 : Blo 858357 3262625 := bstep (se 2 (by rfl) ⟨1223484, by rfl⟩ : syracuseStep 3262625 = 2446969) B2446969
theorem B1288415 : Blo 858357 1288415 := bstep (se 1 (by rfl) ⟨966311, by rfl⟩ : syracuseStep 1288415 = 1932623) B1932623
theorem B860155 : Blo 858357 860155 := bstep (se 1 (by rfl) ⟨645116, by rfl⟩ : syracuseStep 860155 = 1290233) B1290233
theorem B7440619 : Blo 858357 7440619 := bstep (se 1 (by rfl) ⟨5580464, by rfl⟩ : syracuseStep 7440619 = 11160929) B11160929
theorem B11020535 : Blo 858357 11020535 := bstep (se 1 (by rfl) ⟨8265401, by rfl⟩ : syracuseStep 11020535 = 16530803) B16530803
theorem B1288475 : Blo 858357 1288475 := bstep (se 1 (by rfl) ⟨966356, by rfl⟩ : syracuseStep 1288475 = 1932713) B1932713
theorem B1288607 : Blo 858357 1288607 := bstep (se 1 (by rfl) ⟨966455, by rfl⟩ : syracuseStep 1288607 = 1932911) B1932911
theorem B1837559 : Blo 858357 1837559 := bstep (se 1 (by rfl) ⟨1378169, by rfl⟩ : syracuseStep 1837559 = 2756339) B2756339
theorem B1288799 : Blo 858357 1288799 := bstep (se 1 (by rfl) ⟨966599, by rfl⟩ : syracuseStep 1288799 = 1933199) B1933199
theorem B14305895 : Blo 858357 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B17656471 : Blo 858357 17656471 := bstep (se 1 (by rfl) ⟨13242353, by rfl⟩ : syracuseStep 17656471 = 26484707) B26484707
theorem B2615969 : Blo 858357 2615969 := bstep (se 2 (by rfl) ⟨980988, by rfl⟩ : syracuseStep 2615969 = 1961977) B1961977
theorem B1936079 : Blo 858357 1936079 := bstep (se 1 (by rfl) ⟨1452059, by rfl⟩ : syracuseStep 1936079 = 2904119) B2904119
theorem B238283477 : Blo 858357 238283477 := bstep (se 7 (by rfl) ⟨2792384, by rfl⟩ : syracuseStep 238283477 = 5584769) B5584769
theorem B8260481 : Blo 858357 8260481 := bstep (se 2 (by rfl) ⟨3097680, by rfl⟩ : syracuseStep 8260481 = 6195361) B6195361
theorem B1289129 : Blo 858357 1289129 := bstep (se 2 (by rfl) ⟨483423, by rfl⟩ : syracuseStep 1289129 = 966847) B966847
theorem B1289159 : Blo 858357 1289159 := bstep (se 1 (by rfl) ⟨966869, by rfl⟩ : syracuseStep 1289159 = 1933739) B1933739
theorem B16526339 : Blo 858357 16526339 := bstep (se 1 (by rfl) ⟨12394754, by rfl⟩ : syracuseStep 16526339 = 24789509) B24789509
theorem B1289279 : Blo 858357 1289279 := bstep (se 1 (by rfl) ⟨966959, by rfl⟩ : syracuseStep 1289279 = 1933919) B1933919
theorem B3263597 : Blo 858357 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B1289519 : Blo 858357 1289519 := bstep (se 1 (by rfl) ⟨967139, by rfl⟩ : syracuseStep 1289519 = 1934279) B1934279
theorem B7449965 : Blo 858357 7449965 := bstep (se 3 (by rfl) ⟨1396868, by rfl⟩ : syracuseStep 7449965 = 2793737) B2793737
theorem B4894141 : Blo 858357 4894141 := bstep (se 3 (by rfl) ⟨917651, by rfl⟩ : syracuseStep 4894141 = 1835303) B1835303
theorem B22031837 : Blo 858357 22031837 := bstep (se 3 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 22031837 = 8261939) B8261939
theorem B1289705 : Blo 858357 1289705 := bstep (se 2 (by rfl) ⟨483639, by rfl⟩ : syracuseStep 1289705 = 967279) B967279
theorem B1289759 : Blo 858357 1289759 := bstep (se 1 (by rfl) ⟨967319, by rfl⟩ : syracuseStep 1289759 = 1934639) B1934639
theorem B1289849 : Blo 858357 1289849 := bstep (se 2 (by rfl) ⟨483693, by rfl⟩ : syracuseStep 1289849 = 967387) B967387
theorem B1290095 : Blo 858357 1290095 := bstep (se 1 (by rfl) ⟨967571, by rfl⟩ : syracuseStep 1290095 = 1935143) B1935143
theorem B1224811 : Blo 858357 1224811 := bstep (se 1 (by rfl) ⟨918608, by rfl⟩ : syracuseStep 1224811 = 1837217) B1837217
theorem B1290347 : Blo 858357 1290347 := bstep (se 1 (by rfl) ⟨967760, by rfl⟩ : syracuseStep 1290347 = 1935521) B1935521
theorem B4714939 : Blo 858357 4714939 := bstep (se 1 (by rfl) ⟨3536204, by rfl⟩ : syracuseStep 4714939 = 7072409) B7072409
theorem B3674639 : Blo 858357 3674639 := bstep (se 1 (by rfl) ⟨2755979, by rfl⟩ : syracuseStep 3674639 = 5511959) B5511959
theorem B1290779 : Blo 858357 1290779 := bstep (se 1 (by rfl) ⟨968084, by rfl⟩ : syracuseStep 1290779 = 1936169) B1936169
theorem B9916985 : Blo 858357 9916985 := bstep (se 2 (by rfl) ⟨3718869, by rfl⟩ : syracuseStep 9916985 = 7437739) B7437739
theorem B4346621 : Blo 858357 4346621 := bstep (se 3 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 4346621 = 1629983) B1629983
theorem B4346783 : Blo 858357 4346783 := bstep (se 1 (by rfl) ⟨3260087, by rfl⟩ : syracuseStep 4346783 = 6520175) B6520175
theorem B22311865 : Blo 858357 22311865 := bstep (se 2 (by rfl) ⟨8366949, by rfl⟩ : syracuseStep 22311865 = 16733899) B16733899
theorem B4895873 : Blo 858357 4895873 := bstep (se 2 (by rfl) ⟨1835952, by rfl⟩ : syracuseStep 4895873 = 3671905) B3671905
theorem B3265859 : Blo 858357 3265859 := bstep (se 1 (by rfl) ⟨2449394, by rfl⟩ : syracuseStep 3265859 = 4898789) B4898789
theorem B3266041 : Blo 858357 3266041 := bstep (se 2 (by rfl) ⟨1224765, by rfl⟩ : syracuseStep 3266041 = 2449531) B2449531
theorem B2176865 : Blo 858357 2176865 := bstep (se 2 (by rfl) ⟨816324, by rfl⟩ : syracuseStep 2176865 = 1632649) B1632649
theorem B4126589 : Blo 858357 4126589 := bstep (se 3 (by rfl) ⟨773735, by rfl⟩ : syracuseStep 4126589 = 1547471) B1547471
theorem B4642717 : Blo 858357 4642717 := bstep (se 3 (by rfl) ⟨870509, by rfl⟩ : syracuseStep 4642717 = 1741019) B1741019
theorem B16529345 : Blo 858357 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B52869131 : Blo 858357 52869131 := bstep (se 1 (by rfl) ⟨39651848, by rfl⟩ : syracuseStep 52869131 = 79303697) B79303697
theorem B4896875 : Blo 858357 4896875 := bstep (se 1 (by rfl) ⟨3672656, by rfl⟩ : syracuseStep 4896875 = 7345313) B7345313
theorem B9787553 : Blo 858357 9787553 := bstep (se 2 (by rfl) ⟨3670332, by rfl⟩ : syracuseStep 9787553 = 7340665) B7340665
theorem B5880023 : Blo 858357 5880023 := bstep (se 1 (by rfl) ⟨4410017, by rfl⟩ : syracuseStep 5880023 = 8820035) B8820035
theorem B858471 : Blo 858357 858471 := bstep (se 1 (by rfl) ⟨643853, by rfl⟩ : syracuseStep 858471 = 1287707) B1287707
theorem B1448489 : Blo 858357 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B13425209 : Blo 858357 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B858727 : Blo 858357 858727 := bstep (se 1 (by rfl) ⟨644045, by rfl⟩ : syracuseStep 858727 = 1288091) B1288091
theorem B2898557 : Blo 858357 2898557 := bstep (se 3 (by rfl) ⟨543479, by rfl⟩ : syracuseStep 2898557 = 1086959) B1086959
theorem B858751 : Blo 858357 858751 := bstep (se 1 (by rfl) ⟨644063, by rfl⟩ : syracuseStep 858751 = 1288127) B1288127
theorem B858875 : Blo 858357 858875 := bstep (se 1 (by rfl) ⟨644156, by rfl⟩ : syracuseStep 858875 = 1288313) B1288313
theorem B859131 : Blo 858357 859131 := bstep (se 1 (by rfl) ⟨644348, by rfl⟩ : syracuseStep 859131 = 1288697) B1288697
theorem B859167 : Blo 858357 859167 := bstep (se 1 (by rfl) ⟨644375, by rfl⟩ : syracuseStep 859167 = 1288751) B1288751
theorem B1932443 : Blo 858357 1932443 := bstep (se 1 (by rfl) ⟨1449332, by rfl⟩ : syracuseStep 1932443 = 2898665) B2898665
theorem B2899151 : Blo 858357 2899151 := bstep (se 1 (by rfl) ⟨2174363, by rfl⟩ : syracuseStep 2899151 = 4348727) B4348727
theorem B10452239 : Blo 858357 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B859455 : Blo 858357 859455 := bstep (se 1 (by rfl) ⟨644591, by rfl⟩ : syracuseStep 859455 = 1289183) B1289183
theorem B2325943 : Blo 858357 2325943 := bstep (se 1 (by rfl) ⟨1744457, by rfl⟩ : syracuseStep 2325943 = 3488915) B3488915
theorem B2899475 : Blo 858357 2899475 := bstep (se 1 (by rfl) ⟨2174606, by rfl⟩ : syracuseStep 2899475 = 4349213) B4349213
theorem B2899529 : Blo 858357 2899529 := bstep (se 2 (by rfl) ⟨1087323, by rfl⟩ : syracuseStep 2899529 = 2174647) B2174647
theorem B859751 : Blo 858357 859751 := bstep (se 1 (by rfl) ⟨644813, by rfl⟩ : syracuseStep 859751 = 1289627) B1289627
theorem B4898515 : Blo 858357 4898515 := bstep (se 1 (by rfl) ⟨3673886, by rfl⟩ : syracuseStep 4898515 = 7347773) B7347773
theorem B860031 : Blo 858357 860031 := bstep (se 1 (by rfl) ⟨645023, by rfl⟩ : syracuseStep 860031 = 1290047) B1290047
theorem B966559 : Blo 858357 966559 := bstep (se 1 (by rfl) ⟨724919, by rfl⟩ : syracuseStep 966559 = 1449839) B1449839
theorem B860231 : Blo 858357 860231 := bstep (se 1 (by rfl) ⟨645173, by rfl⟩ : syracuseStep 860231 = 1290347) B1290347
theorem B9920825 : Blo 858357 9920825 := bstep (se 2 (by rfl) ⟨3720309, by rfl⟩ : syracuseStep 9920825 = 7440619) B7440619
theorem B2449759 : Blo 858357 2449759 := bstep (se 1 (by rfl) ⟨1837319, by rfl⟩ : syracuseStep 2449759 = 3674639) B3674639
theorem B860519 : Blo 858357 860519 := bstep (se 1 (by rfl) ⟨645389, by rfl⟩ : syracuseStep 860519 = 1290779) B1290779
theorem B6611323 : Blo 858357 6611323 := bstep (se 1 (by rfl) ⟨4958492, by rfl⟩ : syracuseStep 6611323 = 9916985) B9916985
theorem B17629613 : Blo 858357 17629613 := bstep (se 3 (by rfl) ⟨3305552, by rfl⟩ : syracuseStep 17629613 = 6611105) B6611105
theorem B2900447 : Blo 858357 2900447 := bstep (se 1 (by rfl) ⟨2175335, by rfl⟩ : syracuseStep 2900447 = 4350671) B4350671
theorem B31359635 : Blo 858357 31359635 := bstep (se 1 (by rfl) ⟨23519726, by rfl⟩ : syracuseStep 31359635 = 47039453) B47039453
theorem B6521633 : Blo 858357 6521633 := bstep (se 2 (by rfl) ⟨2445612, by rfl⟩ : syracuseStep 6521633 = 4891225) B4891225
theorem B1934315 : Blo 858357 1934315 := bstep (se 1 (by rfl) ⟨1450736, by rfl⟩ : syracuseStep 1934315 = 2901473) B2901473
theorem B2901203 : Blo 858357 2901203 := bstep (se 1 (by rfl) ⟨2175902, by rfl⟩ : syracuseStep 2901203 = 4351805) B4351805
theorem B1451243 : Blo 858357 1451243 := bstep (se 1 (by rfl) ⟨1088432, by rfl⟩ : syracuseStep 1451243 = 2176865) B2176865
theorem B11019563 : Blo 858357 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B9537263 : Blo 858357 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B5506987 : Blo 858357 5506987 := bstep (se 1 (by rfl) ⟨4130240, by rfl⟩ : syracuseStep 5506987 = 8260481) B8260481
theorem B1288295 : Blo 858357 1288295 := bstep (se 1 (by rfl) ⟨966221, by rfl⟩ : syracuseStep 1288295 = 1932443) B1932443
theorem B6187229 : Blo 858357 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B1935593 : Blo 858357 1935593 := bstep (se 2 (by rfl) ⟨725847, by rfl⟩ : syracuseStep 1935593 = 1451695) B1451695
theorem B4966643 : Blo 858357 4966643 := bstep (se 1 (by rfl) ⟨3724982, by rfl⟩ : syracuseStep 4966643 = 7449965) B7449965
theorem B6531353 : Blo 858357 6531353 := bstep (se 2 (by rfl) ⟨2449257, by rfl⟩ : syracuseStep 6531353 = 4898515) B4898515
theorem B1288745 : Blo 858357 1288745 := bstep (se 2 (by rfl) ⟨483279, by rfl⟩ : syracuseStep 1288745 = 966559) B966559
theorem B6187691 : Blo 858357 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B2173787 : Blo 858357 2173787 := bstep (se 1 (by rfl) ⟨1630340, by rfl⟩ : syracuseStep 2173787 = 3260681) B3260681
theorem B1289327 : Blo 858357 1289327 := bstep (se 1 (by rfl) ⟨966995, by rfl⟩ : syracuseStep 1289327 = 1933991) B1933991
theorem B1961147 : Blo 858357 1961147 := bstep (se 1 (by rfl) ⟨1470860, by rfl⟩ : syracuseStep 1961147 = 2941721) B2941721
theorem B6532325 : Blo 858357 6532325 := bstep (se 4 (by rfl) ⟨612405, by rfl⟩ : syracuseStep 6532325 = 1224811) B1224811
theorem B6286585 : Blo 858357 6286585 := bstep (se 2 (by rfl) ⟨2357469, by rfl⟩ : syracuseStep 6286585 = 4714939) B4714939
theorem B1289513 : Blo 858357 1289513 := bstep (se 2 (by rfl) ⟨483567, by rfl⟩ : syracuseStep 1289513 = 967135) B967135
theorem B1305947 : Blo 858357 1305947 := bstep (se 1 (by rfl) ⟨979460, by rfl⟩ : syracuseStep 1305947 = 1958921) B1958921
theorem B3263915 : Blo 858357 3263915 := bstep (se 1 (by rfl) ⟨2447936, by rfl⟩ : syracuseStep 3263915 = 4895873) B4895873
theorem B95415803 : Blo 858357 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B6532811 : Blo 858357 6532811 := bstep (se 1 (by rfl) ⟨4899608, by rfl⟩ : syracuseStep 6532811 = 9799217) B9799217
theorem B29749153 : Blo 858357 29749153 := bstep (se 2 (by rfl) ⟨11155932, by rfl⟩ : syracuseStep 29749153 = 22311865) B22311865
theorem B35246087 : Blo 858357 35246087 := bstep (se 1 (by rfl) ⟨26434565, by rfl⟩ : syracuseStep 35246087 = 52869131) B52869131
theorem B3264583 : Blo 858357 3264583 := bstep (se 1 (by rfl) ⟨2448437, by rfl⟩ : syracuseStep 3264583 = 4896875) B4896875
theorem B6525035 : Blo 858357 6525035 := bstep (se 1 (by rfl) ⟨4893776, by rfl⟩ : syracuseStep 6525035 = 9787553) B9787553
theorem B2175083 : Blo 858357 2175083 := bstep (se 1 (by rfl) ⟨1631312, by rfl⟩ : syracuseStep 2175083 = 3262625) B3262625
theorem B3920015 : Blo 858357 3920015 := bstep (se 1 (by rfl) ⟨2940011, by rfl⟩ : syracuseStep 3920015 = 5880023) B5880023
theorem B1225039 : Blo 858357 1225039 := bstep (se 1 (by rfl) ⟨918779, by rfl⟩ : syracuseStep 1225039 = 1837559) B1837559
theorem B8950139 : Blo 858357 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B1290665 : Blo 858357 1290665 := bstep (se 2 (by rfl) ⟨483999, by rfl⟩ : syracuseStep 1290665 = 967999) B967999
theorem B1290719 : Blo 858357 1290719 := bstep (se 1 (by rfl) ⟨968039, by rfl⟩ : syracuseStep 1290719 = 1936079) B1936079
theorem B158855651 : Blo 858357 158855651 := bstep (se 1 (by rfl) ⟨119141738, by rfl⟩ : syracuseStep 158855651 = 238283477) B238283477
theorem B3101257 : Blo 858357 3101257 := bstep (se 2 (by rfl) ⟨1162971, by rfl⟩ : syracuseStep 3101257 = 2325943) B2325943
theorem B6525521 : Blo 858357 6525521 := bstep (se 2 (by rfl) ⟨2447070, by rfl⟩ : syracuseStep 6525521 = 4894141) B4894141
theorem B4354721 : Blo 858357 4354721 := bstep (se 2 (by rfl) ⟨1633020, by rfl⟩ : syracuseStep 4354721 = 3266041) B3266041
theorem B2175731 : Blo 858357 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B6968159 : Blo 858357 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B6190289 : Blo 858357 6190289 := bstep (se 2 (by rfl) ⟨2321358, by rfl⟩ : syracuseStep 6190289 = 4642717) B4642717
theorem B579818897 : Blo 858357 579818897 := bstep (se 2 (by rfl) ⟨217432086, by rfl⟩ : syracuseStep 579818897 = 434864173) B434864173
theorem B2446843 : Blo 858357 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B8828441 : Blo 858357 8828441 := bstep (se 2 (by rfl) ⟨3310665, by rfl⟩ : syracuseStep 8828441 = 6621331) B6621331
theorem B12391987 : Blo 858357 12391987 := bstep (se 1 (by rfl) ⟨9293990, by rfl⟩ : syracuseStep 12391987 = 18587981) B18587981
theorem B14112391 : Blo 858357 14112391 := bstep (se 1 (by rfl) ⟨10584293, by rfl⟩ : syracuseStep 14112391 = 21168587) B21168587
theorem B2447003 : Blo 858357 2447003 := bstep (se 1 (by rfl) ⟨1835252, by rfl⟩ : syracuseStep 2447003 = 3670505) B3670505
theorem B2897747 : Blo 858357 2897747 := bstep (se 1 (by rfl) ⟨2173310, by rfl⟩ : syracuseStep 2897747 = 4346621) B4346621
theorem B2897855 : Blo 858357 2897855 := bstep (se 1 (by rfl) ⟨2173391, by rfl⟩ : syracuseStep 2897855 = 4346783) B4346783
theorem B23541961 : Blo 858357 23541961 := bstep (se 2 (by rfl) ⟨8828235, by rfl⟩ : syracuseStep 23541961 = 17656471) B17656471
theorem B2177239 : Blo 858357 2177239 := bstep (se 1 (by rfl) ⟨1632929, by rfl⟩ : syracuseStep 2177239 = 3265859) B3265859
theorem B4888835 : Blo 858357 4888835 := bstep (se 1 (by rfl) ⟨3666626, by rfl⟩ : syracuseStep 4888835 = 7333253) B7333253
theorem B15694117 : Blo 858357 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B858523 : Blo 858357 858523 := bstep (se 1 (by rfl) ⟨643892, by rfl⟩ : syracuseStep 858523 = 1287785) B1287785
theorem B858607 : Blo 858357 858607 := bstep (se 1 (by rfl) ⟨643955, by rfl⟩ : syracuseStep 858607 = 1287911) B1287911
theorem B858671 : Blo 858357 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B2751059 : Blo 858357 2751059 := bstep (se 1 (by rfl) ⟨2063294, by rfl⟩ : syracuseStep 2751059 = 4126589) B4126589
theorem B858943 : Blo 858357 858943 := bstep (se 1 (by rfl) ⟨644207, by rfl⟩ : syracuseStep 858943 = 1288415) B1288415
theorem B7347023 : Blo 858357 7347023 := bstep (se 1 (by rfl) ⟨5510267, by rfl⟩ : syracuseStep 7347023 = 11020535) B11020535
theorem B858983 : Blo 858357 858983 := bstep (se 1 (by rfl) ⟨644237, by rfl⟩ : syracuseStep 858983 = 1288475) B1288475
theorem B859071 : Blo 858357 859071 := bstep (se 1 (by rfl) ⟨644303, by rfl⟩ : syracuseStep 859071 = 1288607) B1288607
theorem B965659 : Blo 858357 965659 := bstep (se 1 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 965659 = 1448489) B1448489
theorem B859199 : Blo 858357 859199 := bstep (se 1 (by rfl) ⟨644399, by rfl⟩ : syracuseStep 859199 = 1288799) B1288799
theorem B1932371 : Blo 858357 1932371 := bstep (se 1 (by rfl) ⟨1449278, by rfl⟩ : syracuseStep 1932371 = 2898557) B2898557
theorem B1743979 : Blo 858357 1743979 := bstep (se 1 (by rfl) ⟨1307984, by rfl⟩ : syracuseStep 1743979 = 2615969) B2615969
theorem B859419 : Blo 858357 859419 := bstep (se 1 (by rfl) ⟨644564, by rfl⟩ : syracuseStep 859419 = 1289129) B1289129
theorem B859439 : Blo 858357 859439 := bstep (se 1 (by rfl) ⟨644579, by rfl⟩ : syracuseStep 859439 = 1289159) B1289159
theorem B11017559 : Blo 858357 11017559 := bstep (se 1 (by rfl) ⟨8263169, by rfl⟩ : syracuseStep 11017559 = 16526339) B16526339
theorem B859519 : Blo 858357 859519 := bstep (se 1 (by rfl) ⟨644639, by rfl⟩ : syracuseStep 859519 = 1289279) B1289279
theorem B1932767 : Blo 858357 1932767 := bstep (se 1 (by rfl) ⟨1449575, by rfl⟩ : syracuseStep 1932767 = 2899151) B2899151
theorem B2448893 : Blo 858357 2448893 := bstep (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) B918335
theorem B859679 : Blo 858357 859679 := bstep (se 1 (by rfl) ⟨644759, by rfl⟩ : syracuseStep 859679 = 1289519) B1289519
theorem B14687891 : Blo 858357 14687891 := bstep (se 1 (by rfl) ⟨11015918, by rfl⟩ : syracuseStep 14687891 = 22031837) B22031837
theorem B859803 : Blo 858357 859803 := bstep (se 1 (by rfl) ⟨644852, by rfl⟩ : syracuseStep 859803 = 1289705) B1289705
theorem B1932983 : Blo 858357 1932983 := bstep (se 1 (by rfl) ⟨1449737, by rfl⟩ : syracuseStep 1932983 = 2899475) B2899475
theorem B859839 : Blo 858357 859839 := bstep (se 1 (by rfl) ⟨644879, by rfl⟩ : syracuseStep 859839 = 1289759) B1289759
theorem B1933019 : Blo 858357 1933019 := bstep (se 1 (by rfl) ⟨1449764, by rfl⟩ : syracuseStep 1933019 = 2899529) B2899529
theorem B859899 : Blo 858357 859899 := bstep (se 1 (by rfl) ⟨644924, by rfl⟩ : syracuseStep 859899 = 1289849) B1289849
theorem B860063 : Blo 858357 860063 := bstep (se 1 (by rfl) ⟨645047, by rfl⟩ : syracuseStep 860063 = 1290095) B1290095
theorem B4350023 : Blo 858357 4350023 := bstep (se 1 (by rfl) ⟨3262517, by rfl⟩ : syracuseStep 4350023 = 6525035) B6525035
theorem B1450055 : Blo 858357 1450055 := bstep (se 1 (by rfl) ⟨1087541, by rfl⟩ : syracuseStep 1450055 = 2175083) B2175083
theorem B2613343 : Blo 858357 2613343 := bstep (se 1 (by rfl) ⟨1960007, by rfl⟩ : syracuseStep 2613343 = 3920015) B3920015
theorem B860443 : Blo 858357 860443 := bstep (se 1 (by rfl) ⟨645332, by rfl⟩ : syracuseStep 860443 = 1290665) B1290665
theorem B1933631 : Blo 858357 1933631 := bstep (se 1 (by rfl) ⟨1450223, by rfl⟩ : syracuseStep 1933631 = 2900447) B2900447
theorem B860479 : Blo 858357 860479 := bstep (se 1 (by rfl) ⟨645359, by rfl⟩ : syracuseStep 860479 = 1290719) B1290719
theorem B4350347 : Blo 858357 4350347 := bstep (se 1 (by rfl) ⟨3262760, by rfl⟩ : syracuseStep 4350347 = 6525521) B6525521
theorem B20906423 : Blo 858357 20906423 := bstep (se 1 (by rfl) ⟨15679817, by rfl⟩ : syracuseStep 20906423 = 31359635) B31359635
theorem B1450487 : Blo 858357 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B8815097 : Blo 858357 8815097 := bstep (se 2 (by rfl) ⟨3305661, by rfl⟩ : syracuseStep 8815097 = 6611323) B6611323
theorem B4645439 : Blo 858357 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B1934135 : Blo 858357 1934135 := bstep (se 1 (by rfl) ⟨1450601, by rfl⟩ : syracuseStep 1934135 = 2901203) B2901203
theorem B967495 : Blo 858357 967495 := bstep (se 1 (by rfl) ⟨725621, by rfl⟩ : syracuseStep 967495 = 1451243) B1451243
theorem B1631335 : Blo 858357 1631335 := bstep (se 1 (by rfl) ⟨1223501, by rfl⟩ : syracuseStep 1631335 = 2447003) B2447003
theorem B6358175 : Blo 858357 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B6530381 : Blo 858357 6530381 := bstep (se 3 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 6530381 = 2448893) B2448893
theorem B1287545 : Blo 858357 1287545 := bstep (se 2 (by rfl) ⟨482829, by rfl⟩ : syracuseStep 1287545 = 965659) B965659
theorem B8382113 : Blo 858357 8382113 := bstep (se 2 (by rfl) ⟨3143292, by rfl⟩ : syracuseStep 8382113 = 6286585) B6286585
theorem B3262457 : Blo 858357 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B1288247 : Blo 858357 1288247 := bstep (se 1 (by rfl) ⟨966185, by rfl⟩ : syracuseStep 1288247 = 1932371) B1932371
theorem B870631 : Blo 858357 870631 := bstep (se 1 (by rfl) ⟨652973, by rfl⟩ : syracuseStep 870631 = 1305947) B1305947
theorem B1288511 : Blo 858357 1288511 := bstep (se 1 (by rfl) ⟨966383, by rfl⟩ : syracuseStep 1288511 = 1932767) B1932767
theorem B9791927 : Blo 858357 9791927 := bstep (se 1 (by rfl) ⟨7343945, by rfl⟩ : syracuseStep 9791927 = 14687891) B14687891
theorem B1288655 : Blo 858357 1288655 := bstep (se 1 (by rfl) ⟨966491, by rfl⟩ : syracuseStep 1288655 = 1932983) B1932983
theorem B1288679 : Blo 858357 1288679 := bstep (se 1 (by rfl) ⟨966509, by rfl⟩ : syracuseStep 1288679 = 1933019) B1933019
theorem B7342649 : Blo 858357 7342649 := bstep (se 2 (by rfl) ⟨2753493, by rfl⟩ : syracuseStep 7342649 = 5506987) B5506987
theorem B23497391 : Blo 858357 23497391 := bstep (se 1 (by rfl) ⟨17623043, by rfl⟩ : syracuseStep 23497391 = 35246087) B35246087
theorem B4352777 : Blo 858357 4352777 := bstep (se 2 (by rfl) ⟨1632291, by rfl⟩ : syracuseStep 4352777 = 3264583) B3264583
theorem B6613883 : Blo 858357 6613883 := bstep (se 1 (by rfl) ⟨4960412, by rfl⟩ : syracuseStep 6613883 = 9920825) B9920825
theorem B5966759 : Blo 858357 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B2902985 : Blo 858357 2902985 := bstep (se 2 (by rfl) ⟨1088619, by rfl⟩ : syracuseStep 2902985 = 2177239) B2177239
theorem B1633385 : Blo 858357 1633385 := bstep (se 2 (by rfl) ⟨612519, by rfl⟩ : syracuseStep 1633385 = 1225039) B1225039
theorem B2903147 : Blo 858357 2903147 := bstep (se 1 (by rfl) ⟨2177360, by rfl⟩ : syracuseStep 2903147 = 4354721) B4354721
theorem B1289543 : Blo 858357 1289543 := bstep (se 1 (by rfl) ⟨967157, by rfl⟩ : syracuseStep 1289543 = 1934315) B1934315
theorem B5885627 : Blo 858357 5885627 := bstep (se 1 (by rfl) ⟨4414220, by rfl⟩ : syracuseStep 5885627 = 8828441) B8828441
theorem B4124819 : Blo 858357 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B1290395 : Blo 858357 1290395 := bstep (se 1 (by rfl) ⟨967796, by rfl⟩ : syracuseStep 1290395 = 1935593) B1935593
theorem B4354235 : Blo 858357 4354235 := bstep (se 1 (by rfl) ⟨3265676, by rfl⟩ : syracuseStep 4354235 = 6531353) B6531353
theorem B83701957 : Blo 858357 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B4125127 : Blo 858357 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B1307431 : Blo 858357 1307431 := bstep (se 1 (by rfl) ⟨980573, by rfl⟩ : syracuseStep 1307431 = 1961147) B1961147
theorem B4354883 : Blo 858357 4354883 := bstep (se 1 (by rfl) ⟨3266162, by rfl⟩ : syracuseStep 4354883 = 6532325) B6532325
theorem B7345039 : Blo 858357 7345039 := bstep (se 1 (by rfl) ⟨5508779, by rfl⟩ : syracuseStep 7345039 = 11017559) B11017559
theorem B2175943 : Blo 858357 2175943 := bstep (se 1 (by rfl) ⟨1631957, by rfl⟩ : syracuseStep 2175943 = 3263915) B3263915
theorem B4355207 : Blo 858357 4355207 := bstep (se 1 (by rfl) ⟨3266405, by rfl⟩ : syracuseStep 4355207 = 6532811) B6532811
theorem B31389281 : Blo 858357 31389281 := bstep (se 2 (by rfl) ⟨11770980, by rfl⟩ : syracuseStep 31389281 = 23541961) B23541961
theorem B11753075 : Blo 858357 11753075 := bstep (se 1 (by rfl) ⟨8814806, by rfl⟩ : syracuseStep 11753075 = 17629613) B17629613
theorem B105903767 : Blo 858357 105903767 := bstep (se 1 (by rfl) ⟨79427825, by rfl⟩ : syracuseStep 105903767 = 158855651) B158855651
theorem B3266345 : Blo 858357 3266345 := bstep (se 2 (by rfl) ⟨1224879, by rfl⟩ : syracuseStep 3266345 = 2449759) B2449759
theorem B4347755 : Blo 858357 4347755 := bstep (se 1 (by rfl) ⟨3260816, by rfl⟩ : syracuseStep 4347755 = 6521633) B6521633
theorem B13244381 : Blo 858357 13244381 := bstep (se 3 (by rfl) ⟨2483321, by rfl⟩ : syracuseStep 13244381 = 4966643) B4966643
theorem B4135009 : Blo 858357 4135009 := bstep (se 2 (by rfl) ⟨1550628, by rfl⟩ : syracuseStep 4135009 = 3101257) B3101257
theorem B4126859 : Blo 858357 4126859 := bstep (se 1 (by rfl) ⟨3095144, by rfl⟩ : syracuseStep 4126859 = 6190289) B6190289
theorem B7346375 : Blo 858357 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B386545931 : Blo 858357 386545931 := bstep (se 1 (by rfl) ⟨289909448, by rfl⟩ : syracuseStep 386545931 = 579818897) B579818897
theorem B1931831 : Blo 858357 1931831 := bstep (se 1 (by rfl) ⟨1448873, by rfl⟩ : syracuseStep 1931831 = 2897747) B2897747
theorem B1931903 : Blo 858357 1931903 := bstep (se 1 (by rfl) ⟨1448927, by rfl⟩ : syracuseStep 1931903 = 2897855) B2897855
theorem B858863 : Blo 858357 858863 := bstep (se 1 (by rfl) ⟨644147, by rfl⟩ : syracuseStep 858863 = 1288295) B1288295
theorem B2325305 : Blo 858357 2325305 := bstep (se 2 (by rfl) ⟨871989, by rfl⟩ : syracuseStep 2325305 = 1743979) B1743979
theorem B3259223 : Blo 858357 3259223 := bstep (se 1 (by rfl) ⟨2444417, by rfl⟩ : syracuseStep 3259223 = 4888835) B4888835
theorem B859163 : Blo 858357 859163 := bstep (se 1 (by rfl) ⟨644372, by rfl⟩ : syracuseStep 859163 = 1288745) B1288745
theorem B1834039 : Blo 858357 1834039 := bstep (se 1 (by rfl) ⟨1375529, by rfl⟩ : syracuseStep 1834039 = 2751059) B2751059
theorem B4898015 : Blo 858357 4898015 := bstep (se 1 (by rfl) ⟨3673511, by rfl⟩ : syracuseStep 4898015 = 7347023) B7347023
theorem B1449191 : Blo 858357 1449191 := bstep (se 1 (by rfl) ⟨1086893, by rfl⟩ : syracuseStep 1449191 = 2173787) B2173787
theorem B16522649 : Blo 858357 16522649 := bstep (se 2 (by rfl) ⟨6195993, by rfl⟩ : syracuseStep 16522649 = 12391987) B12391987
theorem B859551 : Blo 858357 859551 := bstep (se 1 (by rfl) ⟨644663, by rfl⟩ : syracuseStep 859551 = 1289327) B1289327
theorem B18816521 : Blo 858357 18816521 := bstep (se 2 (by rfl) ⟨7056195, by rfl⟩ : syracuseStep 18816521 = 14112391) B14112391
theorem B859675 : Blo 858357 859675 := bstep (se 1 (by rfl) ⟨644756, by rfl⟩ : syracuseStep 859675 = 1289513) B1289513
theorem B63610535 : Blo 858357 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B39665537 : Blo 858357 39665537 := bstep (se 2 (by rfl) ⟨14874576, by rfl⟩ : syracuseStep 39665537 = 29749153) B29749153
theorem B2900015 : Blo 858357 2900015 := bstep (se 1 (by rfl) ⟨2175011, by rfl⟩ : syracuseStep 2900015 = 4350023) B4350023
theorem B966703 : Blo 858357 966703 := bstep (se 1 (by rfl) ⟨725027, by rfl⟩ : syracuseStep 966703 = 1450055) B1450055
theorem B860263 : Blo 858357 860263 := bstep (se 1 (by rfl) ⟨645197, by rfl⟩ : syracuseStep 860263 = 1290395) B1290395
theorem B5513345 : Blo 858357 5513345 := bstep (se 2 (by rfl) ⟨2067504, by rfl⟩ : syracuseStep 5513345 = 4135009) B4135009
theorem B2900231 : Blo 858357 2900231 := bstep (se 1 (by rfl) ⟨2175173, by rfl⟩ : syracuseStep 2900231 = 4350347) B4350347
theorem B966991 : Blo 858357 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B3096959 : Blo 858357 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B5588075 : Blo 858357 5588075 := bstep (se 1 (by rfl) ⟨4191056, by rfl⟩ : syracuseStep 5588075 = 8382113) B8382113
theorem B2901257 : Blo 858357 2901257 := bstep (se 2 (by rfl) ⟨1087971, by rfl⟩ : syracuseStep 2901257 = 2175943) B2175943
theorem B50177389 : Blo 858357 50177389 := bstep (se 3 (by rfl) ⟨9408260, by rfl⟩ : syracuseStep 50177389 = 18816521) B18816521
theorem B257697287 : Blo 858357 257697287 := bstep (se 1 (by rfl) ⟨193272965, by rfl⟩ : syracuseStep 257697287 = 386545931) B386545931
theorem B1287887 : Blo 858357 1287887 := bstep (se 1 (by rfl) ⟨965915, by rfl⟩ : syracuseStep 1287887 = 1931831) B1931831
theorem B1287935 : Blo 858357 1287935 := bstep (se 1 (by rfl) ⟨965951, by rfl⟩ : syracuseStep 1287935 = 1931903) B1931903
theorem B15664927 : Blo 858357 15664927 := bstep (se 1 (by rfl) ⟨11748695, by rfl⟩ : syracuseStep 15664927 = 23497391) B23497391
theorem B2901851 : Blo 858357 2901851 := bstep (se 1 (by rfl) ⟨2176388, by rfl⟩ : syracuseStep 2901851 = 4352777) B4352777
theorem B2172815 : Blo 858357 2172815 := bstep (se 1 (by rfl) ⟨1629611, by rfl⟩ : syracuseStep 2172815 = 3259223) B3259223
theorem B4409255 : Blo 858357 4409255 := bstep (se 1 (by rfl) ⟨3306941, by rfl⟩ : syracuseStep 4409255 = 6613883) B6613883
theorem B1935323 : Blo 858357 1935323 := bstep (se 1 (by rfl) ⟨1451492, by rfl⟩ : syracuseStep 1935323 = 2902985) B2902985
theorem B1935431 : Blo 858357 1935431 := bstep (se 1 (by rfl) ⟨1451573, by rfl⟩ : syracuseStep 1935431 = 2903147) B2903147
theorem B2902823 : Blo 858357 2902823 := bstep (se 1 (by rfl) ⟨2177117, by rfl⟩ : syracuseStep 2902823 = 4354235) B4354235
theorem B3484457 : Blo 858357 3484457 := bstep (se 2 (by rfl) ⟨1306671, by rfl⟩ : syracuseStep 3484457 = 2613343) B2613343
theorem B1289087 : Blo 858357 1289087 := bstep (se 1 (by rfl) ⟨966815, by rfl⟩ : syracuseStep 1289087 = 1933631) B1933631
theorem B111602609 : Blo 858357 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B13937615 : Blo 858357 13937615 := bstep (se 1 (by rfl) ⟨10453211, by rfl⟩ : syracuseStep 13937615 = 20906423) B20906423
theorem B5876731 : Blo 858357 5876731 := bstep (se 1 (by rfl) ⟨4407548, by rfl⟩ : syracuseStep 5876731 = 8815097) B8815097
theorem B1289423 : Blo 858357 1289423 := bstep (se 1 (by rfl) ⟨967067, by rfl⟩ : syracuseStep 1289423 = 1934135) B1934135
theorem B2903255 : Blo 858357 2903255 := bstep (se 1 (by rfl) ⟨2177441, by rfl⟩ : syracuseStep 2903255 = 4354883) B4354883
theorem B5500169 : Blo 858357 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B2903471 : Blo 858357 2903471 := bstep (se 1 (by rfl) ⟨2177603, by rfl⟩ : syracuseStep 2903471 = 4355207) B4355207
theorem B4238783 : Blo 858357 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B4353587 : Blo 858357 4353587 := bstep (se 1 (by rfl) ⟨3265190, by rfl⟩ : syracuseStep 4353587 = 6530381) B6530381
theorem B20926187 : Blo 858357 20926187 := bstep (se 1 (by rfl) ⟨15694640, by rfl⟩ : syracuseStep 20926187 = 31389281) B31389281
theorem B7835383 : Blo 858357 7835383 := bstep (se 1 (by rfl) ⟨5876537, by rfl⟩ : syracuseStep 7835383 = 11753075) B11753075
theorem B1289993 : Blo 858357 1289993 := bstep (se 2 (by rfl) ⟨483747, by rfl⟩ : syracuseStep 1289993 = 967495) B967495
theorem B70602511 : Blo 858357 70602511 := bstep (se 1 (by rfl) ⟨52951883, by rfl⟩ : syracuseStep 70602511 = 105903767) B105903767
theorem B9793385 : Blo 858357 9793385 := bstep (se 2 (by rfl) ⟨3672519, by rfl⟩ : syracuseStep 9793385 = 7345039) B7345039
theorem B2174971 : Blo 858357 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B2445385 : Blo 858357 2445385 := bstep (se 2 (by rfl) ⟨917019, by rfl⟩ : syracuseStep 2445385 = 1834039) B1834039
theorem B2175113 : Blo 858357 2175113 := bstep (se 2 (by rfl) ⟨815667, by rfl⟩ : syracuseStep 2175113 = 1631335) B1631335
theorem B4895099 : Blo 858357 4895099 := bstep (se 1 (by rfl) ⟨3671324, by rfl⟩ : syracuseStep 4895099 = 7342649) B7342649
theorem B3977839 : Blo 858357 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B3265343 : Blo 858357 3265343 := bstep (se 1 (by rfl) ⟨2449007, by rfl⟩ : syracuseStep 3265343 = 4898015) B4898015
theorem B11015099 : Blo 858357 11015099 := bstep (se 1 (by rfl) ⟨8261324, by rfl⟩ : syracuseStep 11015099 = 16522649) B16522649
theorem B42407023 : Blo 858357 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B2749879 : Blo 858357 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B4355693 : Blo 858357 4355693 := bstep (se 3 (by rfl) ⟨816692, by rfl⟩ : syracuseStep 4355693 = 1633385) B1633385
theorem B858363 : Blo 858357 858363 := bstep (se 1 (by rfl) ⟨643772, by rfl⟩ : syracuseStep 858363 = 1287545) B1287545
theorem B1743241 : Blo 858357 1743241 := bstep (se 2 (by rfl) ⟨653715, by rfl⟩ : syracuseStep 1743241 = 1307431) B1307431
theorem B2177563 : Blo 858357 2177563 := bstep (se 1 (by rfl) ⟨1633172, by rfl⟩ : syracuseStep 2177563 = 3266345) B3266345
theorem B4643365 : Blo 858357 4643365 := bstep (se 4 (by rfl) ⟨435315, by rfl⟩ : syracuseStep 4643365 = 870631) B870631
theorem B2898503 : Blo 858357 2898503 := bstep (se 1 (by rfl) ⟨2173877, by rfl⟩ : syracuseStep 2898503 = 4347755) B4347755
theorem B8829587 : Blo 858357 8829587 := bstep (se 1 (by rfl) ⟨6622190, by rfl⟩ : syracuseStep 8829587 = 13244381) B13244381
theorem B858831 : Blo 858357 858831 := bstep (se 1 (by rfl) ⟨644123, by rfl⟩ : syracuseStep 858831 = 1288247) B1288247
theorem B2751239 : Blo 858357 2751239 := bstep (se 1 (by rfl) ⟨2063429, by rfl⟩ : syracuseStep 2751239 = 4126859) B4126859
theorem B4897583 : Blo 858357 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B859007 : Blo 858357 859007 := bstep (se 1 (by rfl) ⟨644255, by rfl⟩ : syracuseStep 859007 = 1288511) B1288511
theorem B6527951 : Blo 858357 6527951 := bstep (se 1 (by rfl) ⟨4895963, by rfl⟩ : syracuseStep 6527951 = 9791927) B9791927
theorem B859103 : Blo 858357 859103 := bstep (se 1 (by rfl) ⟨644327, by rfl⟩ : syracuseStep 859103 = 1288655) B1288655
theorem B859119 : Blo 858357 859119 := bstep (se 1 (by rfl) ⟨644339, by rfl⟩ : syracuseStep 859119 = 1288679) B1288679
theorem B15695005 : Blo 858357 15695005 := bstep (se 3 (by rfl) ⟨2942813, by rfl⟩ : syracuseStep 15695005 = 5885627) B5885627
theorem B6200813 : Blo 858357 6200813 := bstep (se 3 (by rfl) ⟨1162652, by rfl⟩ : syracuseStep 6200813 = 2325305) B2325305
theorem B966127 : Blo 858357 966127 := bstep (se 1 (by rfl) ⟨724595, by rfl⟩ : syracuseStep 966127 = 1449191) B1449191
theorem B859695 : Blo 858357 859695 := bstep (se 1 (by rfl) ⟨644771, by rfl⟩ : syracuseStep 859695 = 1289543) B1289543
theorem B26443691 : Blo 858357 26443691 := bstep (se 1 (by rfl) ⟨19832768, by rfl⟩ : syracuseStep 26443691 = 39665537) B39665537
theorem B1933343 : Blo 858357 1933343 := bstep (se 1 (by rfl) ⟨1450007, by rfl⟩ : syracuseStep 1933343 = 2900015) B2900015
theorem B1450075 : Blo 858357 1450075 := bstep (se 1 (by rfl) ⟨1087556, by rfl⟩ : syracuseStep 1450075 = 2175113) B2175113
theorem B3260513 : Blo 858357 3260513 := bstep (se 2 (by rfl) ⟨1222692, by rfl⟩ : syracuseStep 3260513 = 2445385) B2445385
theorem B1933487 : Blo 858357 1933487 := bstep (se 1 (by rfl) ⟨1450115, by rfl⟩ : syracuseStep 1933487 = 2900231) B2900231
theorem B2899961 : Blo 858357 2899961 := bstep (se 2 (by rfl) ⟨1087485, by rfl⟩ : syracuseStep 2899961 = 2174971) B2174971
theorem B1934171 : Blo 858357 1934171 := bstep (se 1 (by rfl) ⟨1450628, by rfl⟩ : syracuseStep 1934171 = 2901257) B2901257
theorem B8258557 : Blo 858357 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B1934567 : Blo 858357 1934567 := bstep (se 1 (by rfl) ⟨1450925, by rfl⟩ : syracuseStep 1934567 = 2901851) B2901851
theorem B56542697 : Blo 858357 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B1935215 : Blo 858357 1935215 := bstep (se 1 (by rfl) ⟨1451411, by rfl⟩ : syracuseStep 1935215 = 2902823) B2902823
theorem B74401739 : Blo 858357 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B9291743 : Blo 858357 9291743 := bstep (se 1 (by rfl) ⟨6968807, by rfl⟩ : syracuseStep 9291743 = 13937615) B13937615
theorem B4351967 : Blo 858357 4351967 := bstep (se 1 (by rfl) ⟨3263975, by rfl⟩ : syracuseStep 4351967 = 6527951) B6527951
theorem B1288169 : Blo 858357 1288169 := bstep (se 2 (by rfl) ⟨483063, by rfl⟩ : syracuseStep 1288169 = 966127) B966127
theorem B1935503 : Blo 858357 1935503 := bstep (se 1 (by rfl) ⟨1451627, by rfl⟩ : syracuseStep 1935503 = 2903255) B2903255
theorem B1935647 : Blo 858357 1935647 := bstep (se 1 (by rfl) ⟨1451735, by rfl⟩ : syracuseStep 1935647 = 2903471) B2903471
theorem B14666021 : Blo 858357 14666021 := bstep (se 4 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 14666021 = 2749879) B2749879
theorem B10447177 : Blo 858357 10447177 := bstep (se 2 (by rfl) ⟨3917691, by rfl⟩ : syracuseStep 10447177 = 7835383) B7835383
theorem B94136681 : Blo 858357 94136681 := bstep (se 2 (by rfl) ⟨35301255, by rfl⟩ : syracuseStep 94136681 = 70602511) B70602511
theorem B2902391 : Blo 858357 2902391 := bstep (se 1 (by rfl) ⟨2176793, by rfl⟩ : syracuseStep 2902391 = 4353587) B4353587
theorem B1288937 : Blo 858357 1288937 := bstep (se 2 (by rfl) ⟨483351, by rfl⟩ : syracuseStep 1288937 = 966703) B966703
theorem B3263399 : Blo 858357 3263399 := bstep (se 1 (by rfl) ⟨2447549, by rfl⟩ : syracuseStep 3263399 = 4895099) B4895099
theorem B1289321 : Blo 858357 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B7343399 : Blo 858357 7343399 := bstep (se 1 (by rfl) ⟨5507549, by rfl⟩ : syracuseStep 7343399 = 11015099) B11015099
theorem B2903417 : Blo 858357 2903417 := bstep (se 2 (by rfl) ⟨1088781, by rfl⟩ : syracuseStep 2903417 = 2177563) B2177563
theorem B171798191 : Blo 858357 171798191 := bstep (se 1 (by rfl) ⟨128848643, by rfl⟩ : syracuseStep 171798191 = 257697287) B257697287
theorem B2903795 : Blo 858357 2903795 := bstep (se 1 (by rfl) ⟨2177846, by rfl⟩ : syracuseStep 2903795 = 4355693) B4355693
theorem B1290215 : Blo 858357 1290215 := bstep (se 1 (by rfl) ⟨967661, by rfl⟩ : syracuseStep 1290215 = 1935323) B1935323
theorem B1290287 : Blo 858357 1290287 := bstep (se 1 (by rfl) ⟨967715, by rfl⟩ : syracuseStep 1290287 = 1935431) B1935431
theorem B20926673 : Blo 858357 20926673 := bstep (se 2 (by rfl) ⟨7847502, by rfl⟩ : syracuseStep 20926673 = 15695005) B15695005
theorem B5886391 : Blo 858357 5886391 := bstep (se 1 (by rfl) ⟨4414793, by rfl⟩ : syracuseStep 5886391 = 8829587) B8829587
theorem B2322971 : Blo 858357 2322971 := bstep (se 1 (by rfl) ⟨1742228, by rfl⟩ : syracuseStep 2322971 = 3484457) B3484457
theorem B3265055 : Blo 858357 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B3666779 : Blo 858357 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B4133875 : Blo 858357 4133875 := bstep (se 1 (by rfl) ⟨3100406, by rfl⟩ : syracuseStep 4133875 = 6200813) B6200813
theorem B20886569 : Blo 858357 20886569 := bstep (se 2 (by rfl) ⟨7832463, by rfl⟩ : syracuseStep 20886569 = 15664927) B15664927
theorem B3675563 : Blo 858357 3675563 := bstep (se 1 (by rfl) ⟨2756672, by rfl⟩ : syracuseStep 3675563 = 5513345) B5513345
theorem B2324321 : Blo 858357 2324321 := bstep (se 2 (by rfl) ⟨871620, by rfl⟩ : syracuseStep 2324321 = 1743241) B1743241
theorem B2176895 : Blo 858357 2176895 := bstep (se 1 (by rfl) ⟨1632671, by rfl⟩ : syracuseStep 2176895 = 3265343) B3265343
theorem B21215141 : Blo 858357 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B6191153 : Blo 858357 6191153 := bstep (se 2 (by rfl) ⟨2321682, by rfl⟩ : syracuseStep 6191153 = 4643365) B4643365
theorem B3725383 : Blo 858357 3725383 := bstep (se 1 (by rfl) ⟨2794037, by rfl⟩ : syracuseStep 3725383 = 5588075) B5588075
theorem B858591 : Blo 858357 858591 := bstep (se 1 (by rfl) ⟨643943, by rfl⟩ : syracuseStep 858591 = 1287887) B1287887
theorem B858623 : Blo 858357 858623 := bstep (se 1 (by rfl) ⟨643967, by rfl⟩ : syracuseStep 858623 = 1287935) B1287935
theorem B1448543 : Blo 858357 1448543 := bstep (se 1 (by rfl) ⟨1086407, by rfl⟩ : syracuseStep 1448543 = 2172815) B2172815
theorem B2939503 : Blo 858357 2939503 := bstep (se 1 (by rfl) ⟨2204627, by rfl⟩ : syracuseStep 2939503 = 4409255) B4409255
theorem B1932335 : Blo 858357 1932335 := bstep (se 1 (by rfl) ⟨1449251, by rfl⟩ : syracuseStep 1932335 = 2898503) B2898503
theorem B66903185 : Blo 858357 66903185 := bstep (se 2 (by rfl) ⟨25088694, by rfl⟩ : syracuseStep 66903185 = 50177389) B50177389
theorem B1834159 : Blo 858357 1834159 := bstep (se 1 (by rfl) ⟨1375619, by rfl⟩ : syracuseStep 1834159 = 2751239) B2751239
theorem B859391 : Blo 858357 859391 := bstep (se 1 (by rfl) ⟨644543, by rfl⟩ : syracuseStep 859391 = 1289087) B1289087
theorem B859615 : Blo 858357 859615 := bstep (se 1 (by rfl) ⟨644711, by rfl⟩ : syracuseStep 859615 = 1289423) B1289423
theorem B2825855 : Blo 858357 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B13950791 : Blo 858357 13950791 := bstep (se 1 (by rfl) ⟨10463093, by rfl⟩ : syracuseStep 13950791 = 20926187) B20926187
theorem B859995 : Blo 858357 859995 := bstep (se 1 (by rfl) ⟨644996, by rfl⟩ : syracuseStep 859995 = 1289993) B1289993
theorem B6528923 : Blo 858357 6528923 := bstep (se 1 (by rfl) ⟨4896692, by rfl⟩ : syracuseStep 6528923 = 9793385) B9793385
theorem B17629127 : Blo 858357 17629127 := bstep (se 1 (by rfl) ⟨13221845, by rfl⟩ : syracuseStep 17629127 = 26443691) B26443691
theorem B31342565 : Blo 858357 31342565 := bstep (se 4 (by rfl) ⟨2938365, by rfl⟩ : syracuseStep 31342565 = 5876731) B5876731
theorem B860191 : Blo 858357 860191 := bstep (se 1 (by rfl) ⟨645143, by rfl⟩ : syracuseStep 860191 = 1290287) B1290287
theorem B1933433 : Blo 858357 1933433 := bstep (se 2 (by rfl) ⟨725037, by rfl⟩ : syracuseStep 1933433 = 1450075) B1450075
theorem B13951115 : Blo 858357 13951115 := bstep (se 1 (by rfl) ⟨10463336, by rfl⟩ : syracuseStep 13951115 = 20926673) B20926673
theorem B1548647 : Blo 858357 1548647 := bstep (se 1 (by rfl) ⟨1161485, by rfl⟩ : syracuseStep 1548647 = 2322971) B2322971
theorem B7848521 : Blo 858357 7848521 := bstep (se 2 (by rfl) ⟨2943195, by rfl⟩ : syracuseStep 7848521 = 5886391) B5886391
theorem B2450375 : Blo 858357 2450375 := bstep (se 1 (by rfl) ⟨1837781, by rfl⟩ : syracuseStep 2450375 = 3675563) B3675563
theorem B1549547 : Blo 858357 1549547 := bstep (se 1 (by rfl) ⟨1162160, by rfl⟩ : syracuseStep 1549547 = 2324321) B2324321
theorem B1451263 : Blo 858357 1451263 := bstep (se 1 (by rfl) ⟨1088447, by rfl⟩ : syracuseStep 1451263 = 2176895) B2176895
theorem B6194495 : Blo 858357 6194495 := bstep (se 1 (by rfl) ⟨4645871, by rfl⟩ : syracuseStep 6194495 = 9291743) B9291743
theorem B2901311 : Blo 858357 2901311 := bstep (se 1 (by rfl) ⟨2175983, by rfl⟩ : syracuseStep 2901311 = 4351967) B4351967
theorem B11011409 : Blo 858357 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B1934927 : Blo 858357 1934927 := bstep (se 1 (by rfl) ⟨1451195, by rfl⟩ : syracuseStep 1934927 = 2902391) B2902391
theorem B1288223 : Blo 858357 1288223 := bstep (se 1 (by rfl) ⟨966167, by rfl⟩ : syracuseStep 1288223 = 1932335) B1932335
theorem B1935611 : Blo 858357 1935611 := bstep (se 1 (by rfl) ⟨1451708, by rfl⟩ : syracuseStep 1935611 = 2903417) B2903417
theorem B1935863 : Blo 858357 1935863 := bstep (se 1 (by rfl) ⟨1451897, by rfl⟩ : syracuseStep 1935863 = 2903795) B2903795
theorem B9300527 : Blo 858357 9300527 := bstep (se 1 (by rfl) ⟨6975395, by rfl⟩ : syracuseStep 9300527 = 13950791) B13950791
theorem B4352615 : Blo 858357 4352615 := bstep (se 1 (by rfl) ⟨3264461, by rfl⟩ : syracuseStep 4352615 = 6528923) B6528923
theorem B1288895 : Blo 858357 1288895 := bstep (se 1 (by rfl) ⟨966671, by rfl⟩ : syracuseStep 1288895 = 1933343) B1933343
theorem B2173675 : Blo 858357 2173675 := bstep (se 1 (by rfl) ⟨1630256, by rfl⟩ : syracuseStep 2173675 = 3260513) B3260513
theorem B4967177 : Blo 858357 4967177 := bstep (se 2 (by rfl) ⟨1862691, by rfl⟩ : syracuseStep 4967177 = 3725383) B3725383
theorem B1288991 : Blo 858357 1288991 := bstep (se 1 (by rfl) ⟨966743, by rfl⟩ : syracuseStep 1288991 = 1933487) B1933487
theorem B13929569 : Blo 858357 13929569 := bstep (se 2 (by rfl) ⟨5223588, by rfl⟩ : syracuseStep 13929569 = 10447177) B10447177
theorem B2444519 : Blo 858357 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B1289447 : Blo 858357 1289447 := bstep (se 1 (by rfl) ⟨967085, by rfl⟩ : syracuseStep 1289447 = 1934171) B1934171
theorem B3919337 : Blo 858357 3919337 := bstep (se 2 (by rfl) ⟨1469751, by rfl⟩ : syracuseStep 3919337 = 2939503) B2939503
theorem B1289711 : Blo 858357 1289711 := bstep (se 1 (by rfl) ⟨967283, by rfl⟩ : syracuseStep 1289711 = 1934567) B1934567
theorem B37695131 : Blo 858357 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B1290143 : Blo 858357 1290143 := bstep (se 1 (by rfl) ⟨967607, by rfl⟩ : syracuseStep 1290143 = 1935215) B1935215
theorem B14143427 : Blo 858357 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B1290335 : Blo 858357 1290335 := bstep (se 1 (by rfl) ⟨967751, by rfl⟩ : syracuseStep 1290335 = 1935503) B1935503
theorem B1290431 : Blo 858357 1290431 := bstep (se 1 (by rfl) ⟨967823, by rfl⟩ : syracuseStep 1290431 = 1935647) B1935647
theorem B9777347 : Blo 858357 9777347 := bstep (se 1 (by rfl) ⟨7333010, by rfl⟩ : syracuseStep 9777347 = 14666021) B14666021
theorem B2445545 : Blo 858357 2445545 := bstep (se 2 (by rfl) ⟨917079, by rfl⟩ : syracuseStep 2445545 = 1834159) B1834159
theorem B2175599 : Blo 858357 2175599 := bstep (se 1 (by rfl) ⟨1631699, by rfl⟩ : syracuseStep 2175599 = 3263399) B3263399
theorem B44602123 : Blo 858357 44602123 := bstep (se 1 (by rfl) ⟨33451592, by rfl⟩ : syracuseStep 44602123 = 66903185) B66903185
theorem B4895599 : Blo 858357 4895599 := bstep (se 1 (by rfl) ⟨3671699, by rfl⟩ : syracuseStep 4895599 = 7343399) B7343399
theorem B11752751 : Blo 858357 11752751 := bstep (se 1 (by rfl) ⟨8814563, by rfl⟩ : syracuseStep 11752751 = 17629127) B17629127
theorem B20895043 : Blo 858357 20895043 := bstep (se 1 (by rfl) ⟨15671282, by rfl⟩ : syracuseStep 20895043 = 31342565) B31342565
theorem B2176703 : Blo 858357 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B13924379 : Blo 858357 13924379 := bstep (se 1 (by rfl) ⟨10443284, by rfl⟩ : syracuseStep 13924379 = 20886569) B20886569
theorem B49601159 : Blo 858357 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B5511833 : Blo 858357 5511833 := bstep (se 2 (by rfl) ⟨2066937, by rfl⟩ : syracuseStep 5511833 = 4133875) B4133875
theorem B858779 : Blo 858357 858779 := bstep (se 1 (by rfl) ⟨644084, by rfl⟩ : syracuseStep 858779 = 1288169) B1288169
theorem B4127435 : Blo 858357 4127435 := bstep (se 1 (by rfl) ⟨3095576, by rfl⟩ : syracuseStep 4127435 = 6191153) B6191153
theorem B62757787 : Blo 858357 62757787 := bstep (se 1 (by rfl) ⟨47068340, by rfl⟩ : syracuseStep 62757787 = 94136681) B94136681
theorem B965695 : Blo 858357 965695 := bstep (se 1 (by rfl) ⟨724271, by rfl⟩ : syracuseStep 965695 = 1448543) B1448543
theorem B859291 : Blo 858357 859291 := bstep (se 1 (by rfl) ⟨644468, by rfl⟩ : syracuseStep 859291 = 1288937) B1288937
theorem B859547 : Blo 858357 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B1883903 : Blo 858357 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B114532127 : Blo 858357 114532127 := bstep (se 1 (by rfl) ⟨85899095, by rfl⟩ : syracuseStep 114532127 = 171798191) B171798191
theorem B860143 : Blo 858357 860143 := bstep (se 1 (by rfl) ⟨645107, by rfl⟩ : syracuseStep 860143 = 1290215) B1290215
theorem B1933307 : Blo 858357 1933307 := bstep (se 1 (by rfl) ⟨1449980, by rfl⟩ : syracuseStep 1933307 = 2899961) B2899961
theorem B860223 : Blo 858357 860223 := bstep (se 1 (by rfl) ⟨645167, by rfl⟩ : syracuseStep 860223 = 1290335) B1290335
theorem B860287 : Blo 858357 860287 := bstep (se 1 (by rfl) ⟨645215, by rfl⟩ : syracuseStep 860287 = 1290431) B1290431
theorem B1630363 : Blo 858357 1630363 := bstep (se 1 (by rfl) ⟨1222772, by rfl⟩ : syracuseStep 1630363 = 2445545) B2445545
theorem B1032431 : Blo 858357 1032431 := bstep (se 1 (by rfl) ⟨774323, by rfl⟩ : syracuseStep 1032431 = 1548647) B1548647
theorem B1450399 : Blo 858357 1450399 := bstep (se 1 (by rfl) ⟨1087799, by rfl⟩ : syracuseStep 1450399 = 2175599) B2175599
theorem B1033031 : Blo 858357 1033031 := bstep (se 1 (by rfl) ⟨774773, by rfl⟩ : syracuseStep 1033031 = 1549547) B1549547
theorem B1934207 : Blo 858357 1934207 := bstep (se 1 (by rfl) ⟨1450655, by rfl⟩ : syracuseStep 1934207 = 2901311) B2901311
theorem B7340939 : Blo 858357 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B1451135 : Blo 858357 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B9282919 : Blo 858357 9282919 := bstep (se 1 (by rfl) ⟨6962189, by rfl⟩ : syracuseStep 9282919 = 13924379) B13924379
theorem B1287593 : Blo 858357 1287593 := bstep (se 2 (by rfl) ⟨482847, by rfl⟩ : syracuseStep 1287593 = 965695) B965695
theorem B1935017 : Blo 858357 1935017 := bstep (se 2 (by rfl) ⟨725631, by rfl⟩ : syracuseStep 1935017 = 1451263) B1451263
theorem B2901743 : Blo 858357 2901743 := bstep (se 1 (by rfl) ⟨2176307, by rfl⟩ : syracuseStep 2901743 = 4352615) B4352615
theorem B5023741 : Blo 858357 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B1288871 : Blo 858357 1288871 := bstep (se 1 (by rfl) ⟨966653, by rfl⟩ : syracuseStep 1288871 = 1933307) B1933307
theorem B1288955 : Blo 858357 1288955 := bstep (se 1 (by rfl) ⟨966716, by rfl⟩ : syracuseStep 1288955 = 1933433) B1933433
theorem B9300743 : Blo 858357 9300743 := bstep (se 1 (by rfl) ⟨6975557, by rfl⟩ : syracuseStep 9300743 = 13951115) B13951115
theorem B1633583 : Blo 858357 1633583 := bstep (se 1 (by rfl) ⟨1225187, by rfl⟩ : syracuseStep 1633583 = 2450375) B2450375
theorem B16518653 : Blo 858357 16518653 := bstep (se 3 (by rfl) ⟨3097247, by rfl⟩ : syracuseStep 16518653 = 6194495) B6194495
theorem B7835167 : Blo 858357 7835167 := bstep (se 1 (by rfl) ⟨5876375, by rfl⟩ : syracuseStep 7835167 = 11752751) B11752751
theorem B59469497 : Blo 858357 59469497 := bstep (se 2 (by rfl) ⟨22301061, by rfl⟩ : syracuseStep 59469497 = 44602123) B44602123
theorem B1289951 : Blo 858357 1289951 := bstep (se 1 (by rfl) ⟨967463, by rfl⟩ : syracuseStep 1289951 = 1934927) B1934927
theorem B83677049 : Blo 858357 83677049 := bstep (se 2 (by rfl) ⟨31378893, by rfl⟩ : syracuseStep 83677049 = 62757787) B62757787
theorem B1290407 : Blo 858357 1290407 := bstep (se 1 (by rfl) ⟨967805, by rfl⟩ : syracuseStep 1290407 = 1935611) B1935611
theorem B1290575 : Blo 858357 1290575 := bstep (se 1 (by rfl) ⟨967931, by rfl⟩ : syracuseStep 1290575 = 1935863) B1935863
theorem B33067439 : Blo 858357 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B3674555 : Blo 858357 3674555 := bstep (se 1 (by rfl) ⟨2755916, by rfl⟩ : syracuseStep 3674555 = 5511833) B5511833
theorem B9286379 : Blo 858357 9286379 := bstep (se 1 (by rfl) ⟨6964784, by rfl⟩ : syracuseStep 9286379 = 13929569) B13929569
theorem B25130087 : Blo 858357 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B76354751 : Blo 858357 76354751 := bstep (se 1 (by rfl) ⟨57266063, by rfl⟩ : syracuseStep 76354751 = 114532127) B114532127
theorem B6518231 : Blo 858357 6518231 := bstep (se 1 (by rfl) ⟨4888673, by rfl⟩ : syracuseStep 6518231 = 9777347) B9777347
theorem B5232347 : Blo 858357 5232347 := bstep (se 1 (by rfl) ⟨3924260, by rfl⟩ : syracuseStep 5232347 = 7848521) B7848521
theorem B6518717 : Blo 858357 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B2898233 : Blo 858357 2898233 := bstep (se 2 (by rfl) ⟨1086837, by rfl⟩ : syracuseStep 2898233 = 2173675) B2173675
theorem B6527465 : Blo 858357 6527465 := bstep (se 2 (by rfl) ⟨2447799, by rfl⟩ : syracuseStep 6527465 = 4895599) B4895599
theorem B858815 : Blo 858357 858815 := bstep (se 1 (by rfl) ⟨644111, by rfl⟩ : syracuseStep 858815 = 1288223) B1288223
theorem B6200351 : Blo 858357 6200351 := bstep (se 1 (by rfl) ⟨4650263, by rfl⟩ : syracuseStep 6200351 = 9300527) B9300527
theorem B27860057 : Blo 858357 27860057 := bstep (se 2 (by rfl) ⟨10447521, by rfl⟩ : syracuseStep 27860057 = 20895043) B20895043
theorem B859263 : Blo 858357 859263 := bstep (se 1 (by rfl) ⟨644447, by rfl⟩ : syracuseStep 859263 = 1288895) B1288895
theorem B2751623 : Blo 858357 2751623 := bstep (se 1 (by rfl) ⟨2063717, by rfl⟩ : syracuseStep 2751623 = 4127435) B4127435
theorem B859327 : Blo 858357 859327 := bstep (se 1 (by rfl) ⟨644495, by rfl⟩ : syracuseStep 859327 = 1288991) B1288991
theorem B13245805 : Blo 858357 13245805 := bstep (se 3 (by rfl) ⟨2483588, by rfl⟩ : syracuseStep 13245805 = 4967177) B4967177
theorem B859631 : Blo 858357 859631 := bstep (se 1 (by rfl) ⟨644723, by rfl⟩ : syracuseStep 859631 = 1289447) B1289447
theorem B2612891 : Blo 858357 2612891 := bstep (se 1 (by rfl) ⟨1959668, by rfl⟩ : syracuseStep 2612891 = 3919337) B3919337
theorem B859807 : Blo 858357 859807 := bstep (se 1 (by rfl) ⟨644855, by rfl⟩ : syracuseStep 859807 = 1289711) B1289711
theorem B860095 : Blo 858357 860095 := bstep (se 1 (by rfl) ⟨645071, by rfl⟩ : syracuseStep 860095 = 1290143) B1290143
theorem B9428951 : Blo 858357 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B860271 : Blo 858357 860271 := bstep (se 1 (by rfl) ⟨645203, by rfl⟩ : syracuseStep 860271 = 1290407) B1290407
theorem B860383 : Blo 858357 860383 := bstep (se 1 (by rfl) ⟨645287, by rfl⟩ : syracuseStep 860383 = 1290575) B1290575
theorem B22044959 : Blo 858357 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B2449703 : Blo 858357 2449703 := bstep (se 1 (by rfl) ⟨1837277, by rfl⟩ : syracuseStep 2449703 = 3674555) B3674555
theorem B203612669 : Blo 858357 203612669 := bstep (se 3 (by rfl) ⟨38177375, by rfl⟩ : syracuseStep 203612669 = 76354751) B76354751
theorem B1933865 : Blo 858357 1933865 := bstep (se 2 (by rfl) ⟨725199, by rfl⟩ : syracuseStep 1933865 = 1450399) B1450399
theorem B2753149 : Blo 858357 2753149 := bstep (se 3 (by rfl) ⟨516215, by rfl⟩ : syracuseStep 2753149 = 1032431) B1032431
theorem B16753391 : Blo 858357 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B967423 : Blo 858357 967423 := bstep (se 1 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 967423 = 1451135) B1451135
theorem B1934495 : Blo 858357 1934495 := bstep (se 1 (by rfl) ⟨1450871, by rfl⟩ : syracuseStep 1934495 = 2901743) B2901743
theorem B4351643 : Blo 858357 4351643 := bstep (se 1 (by rfl) ⟨3263732, by rfl⟩ : syracuseStep 4351643 = 6527465) B6527465
theorem B10446889 : Blo 858357 10446889 := bstep (se 2 (by rfl) ⟨3917583, by rfl⟩ : syracuseStep 10446889 = 7835167) B7835167
theorem B18573371 : Blo 858357 18573371 := bstep (se 1 (by rfl) ⟨13930028, by rfl⟩ : syracuseStep 18573371 = 27860057) B27860057
theorem B2754749 : Blo 858357 2754749 := bstep (se 3 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 2754749 = 1033031) B1033031
theorem B11012435 : Blo 858357 11012435 := bstep (se 1 (by rfl) ⟨8259326, by rfl⟩ : syracuseStep 11012435 = 16518653) B16518653
theorem B6285967 : Blo 858357 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B2173817 : Blo 858357 2173817 := bstep (se 2 (by rfl) ⟨815181, by rfl⟩ : syracuseStep 2173817 = 1630363) B1630363
theorem B1289471 : Blo 858357 1289471 := bstep (se 1 (by rfl) ⟨967103, by rfl⟩ : syracuseStep 1289471 = 1934207) B1934207
theorem B4893959 : Blo 858357 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B4345487 : Blo 858357 4345487 := bstep (se 1 (by rfl) ⟨3259115, by rfl⟩ : syracuseStep 4345487 = 6518231) B6518231
theorem B1290011 : Blo 858357 1290011 := bstep (se 1 (by rfl) ⟨967508, by rfl⟩ : syracuseStep 1290011 = 1935017) B1935017
theorem B4345811 : Blo 858357 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B4133567 : Blo 858357 4133567 := bstep (se 1 (by rfl) ⟨3100175, by rfl⟩ : syracuseStep 4133567 = 6200351) B6200351
theorem B1741927 : Blo 858357 1741927 := bstep (se 1 (by rfl) ⟨1306445, by rfl⟩ : syracuseStep 1741927 = 2612891) B2612891
theorem B39646331 : Blo 858357 39646331 := bstep (se 1 (by rfl) ⟨29734748, by rfl⟩ : syracuseStep 39646331 = 59469497) B59469497
theorem B55784699 : Blo 858357 55784699 := bstep (se 1 (by rfl) ⟨41838524, by rfl⟩ : syracuseStep 55784699 = 83677049) B83677049
theorem B6698321 : Blo 858357 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B6190919 : Blo 858357 6190919 := bstep (se 1 (by rfl) ⟨4643189, by rfl⟩ : syracuseStep 6190919 = 9286379) B9286379
theorem B858395 : Blo 858357 858395 := bstep (se 1 (by rfl) ⟨643796, by rfl⟩ : syracuseStep 858395 = 1287593) B1287593
theorem B3488231 : Blo 858357 3488231 := bstep (se 1 (by rfl) ⟨2616173, by rfl⟩ : syracuseStep 3488231 = 5232347) B5232347
theorem B1932155 : Blo 858357 1932155 := bstep (se 1 (by rfl) ⟨1449116, by rfl⟩ : syracuseStep 1932155 = 2898233) B2898233
theorem B859247 : Blo 858357 859247 := bstep (se 1 (by rfl) ⟨644435, by rfl⟩ : syracuseStep 859247 = 1288871) B1288871
theorem B12377225 : Blo 858357 12377225 := bstep (se 2 (by rfl) ⟨4641459, by rfl⟩ : syracuseStep 12377225 = 9282919) B9282919
theorem B17661073 : Blo 858357 17661073 := bstep (se 2 (by rfl) ⟨6622902, by rfl⟩ : syracuseStep 17661073 = 13245805) B13245805
theorem B859303 : Blo 858357 859303 := bstep (se 1 (by rfl) ⟨644477, by rfl⟩ : syracuseStep 859303 = 1288955) B1288955
theorem B6200495 : Blo 858357 6200495 := bstep (se 1 (by rfl) ⟨4650371, by rfl⟩ : syracuseStep 6200495 = 9300743) B9300743
theorem B1834415 : Blo 858357 1834415 := bstep (se 1 (by rfl) ⟨1375811, by rfl⟩ : syracuseStep 1834415 = 2751623) B2751623
theorem B1089055 : Blo 858357 1089055 := bstep (se 1 (by rfl) ⟨816791, by rfl⟩ : syracuseStep 1089055 = 1633583) B1633583
theorem B859967 : Blo 858357 859967 := bstep (se 1 (by rfl) ⟨644975, by rfl⟩ : syracuseStep 859967 = 1289951) B1289951
theorem B14696639 : Blo 858357 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B135741779 : Blo 858357 135741779 := bstep (se 1 (by rfl) ⟨101806334, by rfl⟩ : syracuseStep 135741779 = 203612669) B203612669
theorem B3670865 : Blo 858357 3670865 := bstep (se 2 (by rfl) ⟨1376574, by rfl⟩ : syracuseStep 3670865 = 2753149) B2753149
theorem B4465547 : Blo 858357 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B2901095 : Blo 858357 2901095 := bstep (se 1 (by rfl) ⟨2175821, by rfl⟩ : syracuseStep 2901095 = 4351643) B4351643
theorem B7341623 : Blo 858357 7341623 := bstep (se 1 (by rfl) ⟨5506217, by rfl⟩ : syracuseStep 7341623 = 11012435) B11012435
theorem B1288103 : Blo 858357 1288103 := bstep (se 1 (by rfl) ⟨966077, by rfl⟩ : syracuseStep 1288103 = 1932155) B1932155
theorem B1452073 : Blo 858357 1452073 := bstep (se 2 (by rfl) ⟨544527, by rfl⟩ : syracuseStep 1452073 = 1089055) B1089055
theorem B8251483 : Blo 858357 8251483 := bstep (se 1 (by rfl) ⟨6188612, by rfl⟩ : syracuseStep 8251483 = 12377225) B12377225
theorem B3262639 : Blo 858357 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B1222943 : Blo 858357 1222943 := bstep (se 1 (by rfl) ⟨917207, by rfl⟩ : syracuseStep 1222943 = 1834415) B1834415
theorem B13929185 : Blo 858357 13929185 := bstep (se 2 (by rfl) ⟨5223444, by rfl⟩ : syracuseStep 13929185 = 10446889) B10446889
theorem B1633135 : Blo 858357 1633135 := bstep (se 1 (by rfl) ⟨1224851, by rfl⟩ : syracuseStep 1633135 = 2449703) B2449703
theorem B1289243 : Blo 858357 1289243 := bstep (se 1 (by rfl) ⟨966932, by rfl⟩ : syracuseStep 1289243 = 1933865) B1933865
theorem B2755711 : Blo 858357 2755711 := bstep (se 1 (by rfl) ⟨2066783, by rfl⟩ : syracuseStep 2755711 = 4133567) B4133567
theorem B11168927 : Blo 858357 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B26430887 : Blo 858357 26430887 := bstep (se 1 (by rfl) ⟨19823165, by rfl⟩ : syracuseStep 26430887 = 39646331) B39646331
theorem B1289663 : Blo 858357 1289663 := bstep (se 1 (by rfl) ⟨967247, by rfl⟩ : syracuseStep 1289663 = 1934495) B1934495
theorem B1289897 : Blo 858357 1289897 := bstep (se 2 (by rfl) ⟨483711, by rfl⟩ : syracuseStep 1289897 = 967423) B967423
theorem B9301949 : Blo 858357 9301949 := bstep (se 3 (by rfl) ⟨1744115, by rfl⟩ : syracuseStep 9301949 = 3488231) B3488231
theorem B12382247 : Blo 858357 12382247 := bstep (se 1 (by rfl) ⟨9286685, by rfl⟩ : syracuseStep 12382247 = 18573371) B18573371
theorem B2322569 : Blo 858357 2322569 := bstep (se 2 (by rfl) ⟨870963, by rfl⟩ : syracuseStep 2322569 = 1741927) B1741927
theorem B23548097 : Blo 858357 23548097 := bstep (se 2 (by rfl) ⟨8830536, by rfl⟩ : syracuseStep 23548097 = 17661073) B17661073
theorem B4133663 : Blo 858357 4133663 := bstep (se 1 (by rfl) ⟨3100247, by rfl⟩ : syracuseStep 4133663 = 6200495) B6200495
theorem B2896991 : Blo 858357 2896991 := bstep (se 1 (by rfl) ⟨2172743, by rfl⟩ : syracuseStep 2896991 = 4345487) B4345487
theorem B2897207 : Blo 858357 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B134100629 : Blo 858357 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B7345997 : Blo 858357 7345997 := bstep (se 3 (by rfl) ⟨1377374, by rfl⟩ : syracuseStep 7345997 = 2754749) B2754749
theorem B37189799 : Blo 858357 37189799 := bstep (se 1 (by rfl) ⟨27892349, by rfl⟩ : syracuseStep 37189799 = 55784699) B55784699
theorem B4127279 : Blo 858357 4127279 := bstep (se 1 (by rfl) ⟨3095459, by rfl⟩ : syracuseStep 4127279 = 6190919) B6190919
theorem B1449211 : Blo 858357 1449211 := bstep (se 1 (by rfl) ⟨1086908, by rfl⟩ : syracuseStep 1449211 = 2173817) B2173817
theorem B859647 : Blo 858357 859647 := bstep (se 1 (by rfl) ⟨644735, by rfl⟩ : syracuseStep 859647 = 1289471) B1289471
theorem B860007 : Blo 858357 860007 := bstep (se 1 (by rfl) ⟨645005, by rfl⟩ : syracuseStep 860007 = 1290011) B1290011
theorem B1548379 : Blo 858357 1548379 := bstep (se 1 (by rfl) ⟨1161284, by rfl⟩ : syracuseStep 1548379 = 2322569) B2322569
theorem B11001977 : Blo 858357 11001977 := bstep (se 2 (by rfl) ⟨4125741, by rfl⟩ : syracuseStep 11001977 = 8251483) B8251483
theorem B9797759 : Blo 858357 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B4350185 : Blo 858357 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B1934063 : Blo 858357 1934063 := bstep (se 1 (by rfl) ⟨1450547, by rfl⟩ : syracuseStep 1934063 = 2901095) B2901095
theorem B3261181 : Blo 858357 3261181 := bstep (se 3 (by rfl) ⟨611471, by rfl⟩ : syracuseStep 3261181 = 1222943) B1222943
theorem B89400419 : Blo 858357 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B1936097 : Blo 858357 1936097 := bstep (se 2 (by rfl) ⟨726036, by rfl⟩ : syracuseStep 1936097 = 1452073) B1452073
theorem B15698731 : Blo 858357 15698731 := bstep (se 1 (by rfl) ⟨11774048, by rfl⟩ : syracuseStep 15698731 = 23548097) B23548097
theorem B2755775 : Blo 858357 2755775 := bstep (se 1 (by rfl) ⟨2066831, by rfl⟩ : syracuseStep 2755775 = 4133663) B4133663
theorem B2977031 : Blo 858357 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B4894415 : Blo 858357 4894415 := bstep (se 1 (by rfl) ⟨3670811, by rfl⟩ : syracuseStep 4894415 = 7341623) B7341623
theorem B24793199 : Blo 858357 24793199 := bstep (se 1 (by rfl) ⟨18594899, by rfl⟩ : syracuseStep 24793199 = 37189799) B37189799
theorem B11006077 : Blo 858357 11006077 := bstep (se 3 (by rfl) ⟨2063639, by rfl⟩ : syracuseStep 11006077 = 4127279) B4127279
theorem B3674281 : Blo 858357 3674281 := bstep (se 2 (by rfl) ⟨1377855, by rfl⟩ : syracuseStep 3674281 = 2755711) B2755711
theorem B9286123 : Blo 858357 9286123 := bstep (se 1 (by rfl) ⟨6964592, by rfl⟩ : syracuseStep 9286123 = 13929185) B13929185
theorem B8254831 : Blo 858357 8254831 := bstep (se 1 (by rfl) ⟨6191123, by rfl⟩ : syracuseStep 8254831 = 12382247) B12382247
theorem B90494519 : Blo 858357 90494519 := bstep (se 1 (by rfl) ⟨67870889, by rfl⟩ : syracuseStep 90494519 = 135741779) B135741779
theorem B2447243 : Blo 858357 2447243 := bstep (se 1 (by rfl) ⟨1835432, by rfl⟩ : syracuseStep 2447243 = 3670865) B3670865
theorem B1931327 : Blo 858357 1931327 := bstep (se 1 (by rfl) ⟨1448495, by rfl⟩ : syracuseStep 1931327 = 2896991) B2896991
theorem B1931471 : Blo 858357 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B2177513 : Blo 858357 2177513 := bstep (se 2 (by rfl) ⟨816567, by rfl⟩ : syracuseStep 2177513 = 1633135) B1633135
theorem B4897331 : Blo 858357 4897331 := bstep (se 1 (by rfl) ⟨3672998, by rfl⟩ : syracuseStep 4897331 = 7345997) B7345997
theorem B858735 : Blo 858357 858735 := bstep (se 1 (by rfl) ⟨644051, by rfl⟩ : syracuseStep 858735 = 1288103) B1288103
theorem B1932281 : Blo 858357 1932281 := bstep (se 2 (by rfl) ⟨724605, by rfl⟩ : syracuseStep 1932281 = 1449211) B1449211
theorem B859495 : Blo 858357 859495 := bstep (se 1 (by rfl) ⟨644621, by rfl⟩ : syracuseStep 859495 = 1289243) B1289243
theorem B7445951 : Blo 858357 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B17620591 : Blo 858357 17620591 := bstep (se 1 (by rfl) ⟨13215443, by rfl⟩ : syracuseStep 17620591 = 26430887) B26430887
theorem B859775 : Blo 858357 859775 := bstep (se 1 (by rfl) ⟨644831, by rfl⟩ : syracuseStep 859775 = 1289663) B1289663
theorem B859931 : Blo 858357 859931 := bstep (se 1 (by rfl) ⟨644948, by rfl⟩ : syracuseStep 859931 = 1289897) B1289897
theorem B6201299 : Blo 858357 6201299 := bstep (se 1 (by rfl) ⟨4650974, by rfl⟩ : syracuseStep 6201299 = 9301949) B9301949
theorem B2900123 : Blo 858357 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B4899041 : Blo 858357 4899041 := bstep (se 2 (by rfl) ⟨1837140, by rfl⟩ : syracuseStep 4899041 = 3674281) B3674281
theorem B8258021 : Blo 858357 8258021 := bstep (se 4 (by rfl) ⟨774189, by rfl⟩ : syracuseStep 8258021 = 1548379) B1548379
theorem B7938749 : Blo 858357 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B20931641 : Blo 858357 20931641 := bstep (se 2 (by rfl) ⟨7849365, by rfl⟩ : syracuseStep 20931641 = 15698731) B15698731
theorem B1631495 : Blo 858357 1631495 := bstep (se 1 (by rfl) ⟨1223621, by rfl⟩ : syracuseStep 1631495 = 2447243) B2447243
theorem B1287551 : Blo 858357 1287551 := bstep (se 1 (by rfl) ⟨965663, by rfl⟩ : syracuseStep 1287551 = 1931327) B1931327
theorem B1287647 : Blo 858357 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B1451675 : Blo 858357 1451675 := bstep (se 1 (by rfl) ⟨1088756, by rfl⟩ : syracuseStep 1451675 = 2177513) B2177513
theorem B1288187 : Blo 858357 1288187 := bstep (se 1 (by rfl) ⟨966140, by rfl⟩ : syracuseStep 1288187 = 1932281) B1932281
theorem B1837183 : Blo 858357 1837183 := bstep (se 1 (by rfl) ⟨1377887, by rfl⟩ : syracuseStep 1837183 = 2755775) B2755775
theorem B3262943 : Blo 858357 3262943 := bstep (se 1 (by rfl) ⟨2447207, by rfl⟩ : syracuseStep 3262943 = 4894415) B4894415
theorem B7334651 : Blo 858357 7334651 := bstep (se 1 (by rfl) ⟨5500988, by rfl⟩ : syracuseStep 7334651 = 11001977) B11001977
theorem B6531839 : Blo 858357 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B14674769 : Blo 858357 14674769 := bstep (se 2 (by rfl) ⟨5503038, by rfl⟩ : syracuseStep 14674769 = 11006077) B11006077
theorem B1289375 : Blo 858357 1289375 := bstep (se 1 (by rfl) ⟨967031, by rfl⟩ : syracuseStep 1289375 = 1934063) B1934063
theorem B965274869 : Blo 858357 965274869 := bstep (se 5 (by rfl) ⟨45247259, by rfl⟩ : syracuseStep 965274869 = 90494519) B90494519
theorem B12381497 : Blo 858357 12381497 := bstep (se 2 (by rfl) ⟨4643061, by rfl⟩ : syracuseStep 12381497 = 9286123) B9286123
theorem B59600279 : Blo 858357 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B3264887 : Blo 858357 3264887 := bstep (se 1 (by rfl) ⟨2448665, by rfl⟩ : syracuseStep 3264887 = 4897331) B4897331
theorem B11006441 : Blo 858357 11006441 := bstep (se 2 (by rfl) ⟨4127415, by rfl⟩ : syracuseStep 11006441 = 8254831) B8254831
theorem B1290731 : Blo 858357 1290731 := bstep (se 1 (by rfl) ⟨968048, by rfl⟩ : syracuseStep 1290731 = 1936097) B1936097
theorem B16536797 : Blo 858357 16536797 := bstep (se 3 (by rfl) ⟨3100649, by rfl⟩ : syracuseStep 16536797 = 6201299) B6201299
theorem B16528799 : Blo 858357 16528799 := bstep (se 1 (by rfl) ⟨12396599, by rfl⟩ : syracuseStep 16528799 = 24793199) B24793199
theorem B4348241 : Blo 858357 4348241 := bstep (se 2 (by rfl) ⟨1630590, by rfl⟩ : syracuseStep 4348241 = 3261181) B3261181
theorem B23494121 : Blo 858357 23494121 := bstep (se 2 (by rfl) ⟨8810295, by rfl⟩ : syracuseStep 23494121 = 17620591) B17620591
theorem B4963967 : Blo 858357 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B1933415 : Blo 858357 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B2449577 : Blo 858357 2449577 := bstep (se 2 (by rfl) ⟨918591, by rfl⟩ : syracuseStep 2449577 = 1837183) B1837183
theorem B5505347 : Blo 858357 5505347 := bstep (se 1 (by rfl) ⟨4129010, by rfl⟩ : syracuseStep 5505347 = 8258021) B8258021
theorem B860487 : Blo 858357 860487 := bstep (se 1 (by rfl) ⟨645365, by rfl⟩ : syracuseStep 860487 = 1290731) B1290731
theorem B5292499 : Blo 858357 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B11019199 : Blo 858357 11019199 := bstep (se 1 (by rfl) ⟨8264399, by rfl⟩ : syracuseStep 11019199 = 16528799) B16528799
theorem B967783 : Blo 858357 967783 := bstep (se 1 (by rfl) ⟨725837, by rfl⟩ : syracuseStep 967783 = 1451675) B1451675
theorem B9783179 : Blo 858357 9783179 := bstep (se 1 (by rfl) ⟨7337384, by rfl⟩ : syracuseStep 9783179 = 14674769) B14674769
theorem B643516579 : Blo 858357 643516579 := bstep (se 1 (by rfl) ⟨482637434, by rfl⟩ : syracuseStep 643516579 = 965274869) B965274869
theorem B39733519 : Blo 858357 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B13954427 : Blo 858357 13954427 := bstep (se 1 (by rfl) ⟨10465820, by rfl⟩ : syracuseStep 13954427 = 20931641) B20931641
theorem B2175295 : Blo 858357 2175295 := bstep (se 1 (by rfl) ⟨1631471, by rfl⟩ : syracuseStep 2175295 = 3262943) B3262943
theorem B4354559 : Blo 858357 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B8254331 : Blo 858357 8254331 := bstep (se 1 (by rfl) ⟨6190748, by rfl⟩ : syracuseStep 8254331 = 12381497) B12381497
theorem B3266027 : Blo 858357 3266027 := bstep (se 1 (by rfl) ⟨2449520, by rfl⟩ : syracuseStep 3266027 = 4899041) B4899041
theorem B2176591 : Blo 858357 2176591 := bstep (se 1 (by rfl) ⟨1632443, by rfl⟩ : syracuseStep 2176591 = 3264887) B3264887
theorem B7337627 : Blo 858357 7337627 := bstep (se 1 (by rfl) ⟨5503220, by rfl⟩ : syracuseStep 7337627 = 11006441) B11006441
theorem B11024531 : Blo 858357 11024531 := bstep (se 1 (by rfl) ⟨8268398, by rfl⟩ : syracuseStep 11024531 = 16536797) B16536797
theorem B1087663 : Blo 858357 1087663 := bstep (se 1 (by rfl) ⟨815747, by rfl⟩ : syracuseStep 1087663 = 1631495) B1631495
theorem B858367 : Blo 858357 858367 := bstep (se 1 (by rfl) ⟨643775, by rfl⟩ : syracuseStep 858367 = 1287551) B1287551
theorem B858431 : Blo 858357 858431 := bstep (se 1 (by rfl) ⟨643823, by rfl⟩ : syracuseStep 858431 = 1287647) B1287647
theorem B858791 : Blo 858357 858791 := bstep (se 1 (by rfl) ⟨644093, by rfl⟩ : syracuseStep 858791 = 1288187) B1288187
theorem B2898827 : Blo 858357 2898827 := bstep (se 1 (by rfl) ⟨2174120, by rfl⟩ : syracuseStep 2898827 = 4348241) B4348241
theorem B4889767 : Blo 858357 4889767 := bstep (se 1 (by rfl) ⟨3667325, by rfl⟩ : syracuseStep 4889767 = 7334651) B7334651
theorem B859583 : Blo 858357 859583 := bstep (se 1 (by rfl) ⟨644687, by rfl⟩ : syracuseStep 859583 = 1289375) B1289375
theorem B15662747 : Blo 858357 15662747 := bstep (se 1 (by rfl) ⟨11747060, by rfl⟩ : syracuseStep 15662747 = 23494121) B23494121
theorem B3309311 : Blo 858357 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B3670231 : Blo 858357 3670231 := bstep (se 1 (by rfl) ⟨2752673, by rfl⟩ : syracuseStep 3670231 = 5505347) B5505347
theorem B1450217 : Blo 858357 1450217 := bstep (se 2 (by rfl) ⟨543831, by rfl⟩ : syracuseStep 1450217 = 1087663) B1087663
theorem B52978025 : Blo 858357 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B2900393 : Blo 858357 2900393 := bstep (se 2 (by rfl) ⟨1087647, by rfl⟩ : syracuseStep 2900393 = 2175295) B2175295
theorem B3432088421 : Blo 858357 3432088421 := bstep (se 4 (by rfl) ⟨321758289, by rfl⟩ : syracuseStep 3432088421 = 643516579) B643516579
theorem B4891751 : Blo 858357 4891751 := bstep (se 1 (by rfl) ⟨3668813, by rfl⟩ : syracuseStep 4891751 = 7337627) B7337627
theorem B6522119 : Blo 858357 6522119 := bstep (se 1 (by rfl) ⟨4891589, by rfl⟩ : syracuseStep 6522119 = 9783179) B9783179
theorem B7349687 : Blo 858357 7349687 := bstep (se 1 (by rfl) ⟨5512265, by rfl⟩ : syracuseStep 7349687 = 11024531) B11024531
theorem B2902121 : Blo 858357 2902121 := bstep (se 2 (by rfl) ⟨1088295, by rfl⟩ : syracuseStep 2902121 = 2176591) B2176591
theorem B2206207 : Blo 858357 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B1288943 : Blo 858357 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B1633051 : Blo 858357 1633051 := bstep (se 1 (by rfl) ⟨1224788, by rfl⟩ : syracuseStep 1633051 = 2449577) B2449577
theorem B2903039 : Blo 858357 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B7056665 : Blo 858357 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B14692265 : Blo 858357 14692265 := bstep (se 2 (by rfl) ⟨5509599, by rfl⟩ : syracuseStep 14692265 = 11019199) B11019199
theorem B1290377 : Blo 858357 1290377 := bstep (se 2 (by rfl) ⟨483891, by rfl⟩ : syracuseStep 1290377 = 967783) B967783
theorem B41767325 : Blo 858357 41767325 := bstep (se 3 (by rfl) ⟨7831373, by rfl⟩ : syracuseStep 41767325 = 15662747) B15662747
theorem B9302951 : Blo 858357 9302951 := bstep (se 1 (by rfl) ⟨6977213, by rfl⟩ : syracuseStep 9302951 = 13954427) B13954427
theorem B5502887 : Blo 858357 5502887 := bstep (se 1 (by rfl) ⟨4127165, by rfl⟩ : syracuseStep 5502887 = 8254331) B8254331
theorem B2177351 : Blo 858357 2177351 := bstep (se 1 (by rfl) ⟨1633013, by rfl⟩ : syracuseStep 2177351 = 3266027) B3266027
theorem B6519689 : Blo 858357 6519689 := bstep (se 2 (by rfl) ⟨2444883, by rfl⟩ : syracuseStep 6519689 = 4889767) B4889767
theorem B1932551 : Blo 858357 1932551 := bstep (se 1 (by rfl) ⟨1449413, by rfl⟩ : syracuseStep 1932551 = 2898827) B2898827
theorem B860251 : Blo 858357 860251 := bstep (se 1 (by rfl) ⟨645188, by rfl⟩ : syracuseStep 860251 = 1290377) B1290377
theorem B966811 : Blo 858357 966811 := bstep (se 1 (by rfl) ⟨725108, by rfl⟩ : syracuseStep 966811 = 1450217) B1450217
theorem B27844883 : Blo 858357 27844883 := bstep (se 1 (by rfl) ⟨20883662, by rfl⟩ : syracuseStep 27844883 = 41767325) B41767325
theorem B1933595 : Blo 858357 1933595 := bstep (se 1 (by rfl) ⟨1450196, by rfl⟩ : syracuseStep 1933595 = 2900393) B2900393
theorem B2288058947 : Blo 858357 2288058947 := bstep (se 1 (by rfl) ⟨1716044210, by rfl⟩ : syracuseStep 2288058947 = 3432088421) B3432088421
theorem B6201967 : Blo 858357 6201967 := bstep (se 1 (by rfl) ⟨4651475, by rfl⟩ : syracuseStep 6201967 = 9302951) B9302951
theorem B3261167 : Blo 858357 3261167 := bstep (se 1 (by rfl) ⟨2445875, by rfl⟩ : syracuseStep 3261167 = 4891751) B4891751
theorem B4899791 : Blo 858357 4899791 := bstep (se 1 (by rfl) ⟨3674843, by rfl⟩ : syracuseStep 4899791 = 7349687) B7349687
theorem B1934747 : Blo 858357 1934747 := bstep (se 1 (by rfl) ⟨1451060, by rfl⟩ : syracuseStep 1934747 = 2902121) B2902121
theorem B1451567 : Blo 858357 1451567 := bstep (se 1 (by rfl) ⟨1088675, by rfl⟩ : syracuseStep 1451567 = 2177351) B2177351
theorem B1935359 : Blo 858357 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B1288367 : Blo 858357 1288367 := bstep (se 1 (by rfl) ⟨966275, by rfl⟩ : syracuseStep 1288367 = 1932551) B1932551
theorem B4704443 : Blo 858357 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B11766437 : Blo 858357 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B35318683 : Blo 858357 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B4893641 : Blo 858357 4893641 := bstep (se 2 (by rfl) ⟨1835115, by rfl⟩ : syracuseStep 4893641 = 3670231) B3670231
theorem B4346459 : Blo 858357 4346459 := bstep (se 1 (by rfl) ⟨3259844, by rfl⟩ : syracuseStep 4346459 = 6519689) B6519689
theorem B9794843 : Blo 858357 9794843 := bstep (se 1 (by rfl) ⟨7346132, by rfl⟩ : syracuseStep 9794843 = 14692265) B14692265
theorem B4348079 : Blo 858357 4348079 := bstep (se 1 (by rfl) ⟨3261059, by rfl⟩ : syracuseStep 4348079 = 6522119) B6522119
theorem B2177401 : Blo 858357 2177401 := bstep (se 2 (by rfl) ⟨816525, by rfl⟩ : syracuseStep 2177401 = 1633051) B1633051
theorem B3668591 : Blo 858357 3668591 := bstep (se 1 (by rfl) ⟨2751443, by rfl⟩ : syracuseStep 3668591 = 5502887) B5502887
theorem B859295 : Blo 858357 859295 := bstep (se 1 (by rfl) ⟨644471, by rfl⟩ : syracuseStep 859295 = 1288943) B1288943
theorem B18563255 : Blo 858357 18563255 := bstep (se 1 (by rfl) ⟨13922441, by rfl⟩ : syracuseStep 18563255 = 27844883) B27844883
theorem B6529895 : Blo 858357 6529895 := bstep (se 1 (by rfl) ⟨4897421, by rfl⟩ : syracuseStep 6529895 = 9794843) B9794843
theorem B967711 : Blo 858357 967711 := bstep (se 1 (by rfl) ⟨725783, by rfl⟩ : syracuseStep 967711 = 1451567) B1451567
theorem B3262427 : Blo 858357 3262427 := bstep (se 1 (by rfl) ⟨2446820, by rfl⟩ : syracuseStep 3262427 = 4893641) B4893641
theorem B1289063 : Blo 858357 1289063 := bstep (se 1 (by rfl) ⟨966797, by rfl⟩ : syracuseStep 1289063 = 1933595) B1933595
theorem B1289081 : Blo 858357 1289081 := bstep (se 2 (by rfl) ⟨483405, by rfl⟩ : syracuseStep 1289081 = 966811) B966811
theorem B2174111 : Blo 858357 2174111 := bstep (se 1 (by rfl) ⟨1630583, by rfl⟩ : syracuseStep 2174111 = 3261167) B3261167
theorem B2903201 : Blo 858357 2903201 := bstep (se 2 (by rfl) ⟨1088700, by rfl⟩ : syracuseStep 2903201 = 2177401) B2177401
theorem B8269289 : Blo 858357 8269289 := bstep (se 2 (by rfl) ⟨3100983, by rfl⟩ : syracuseStep 8269289 = 6201967) B6201967
theorem B1289831 : Blo 858357 1289831 := bstep (se 1 (by rfl) ⟨967373, by rfl⟩ : syracuseStep 1289831 = 1934747) B1934747
theorem B47091577 : Blo 858357 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B1290239 : Blo 858357 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B2445727 : Blo 858357 2445727 := bstep (se 1 (by rfl) ⟨1834295, by rfl⟩ : syracuseStep 2445727 = 3668591) B3668591
theorem B7844291 : Blo 858357 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B1525372631 : Blo 858357 1525372631 := bstep (se 1 (by rfl) ⟨1144029473, by rfl⟩ : syracuseStep 1525372631 = 2288058947) B2288058947
theorem B2897639 : Blo 858357 2897639 := bstep (se 1 (by rfl) ⟨2173229, by rfl⟩ : syracuseStep 2897639 = 4346459) B4346459
theorem B3266527 : Blo 858357 3266527 := bstep (se 1 (by rfl) ⟨2449895, by rfl⟩ : syracuseStep 3266527 = 4899791) B4899791
theorem B2898719 : Blo 858357 2898719 := bstep (se 1 (by rfl) ⟨2174039, by rfl⟩ : syracuseStep 2898719 = 4348079) B4348079
theorem B858911 : Blo 858357 858911 := bstep (se 1 (by rfl) ⟨644183, by rfl⟩ : syracuseStep 858911 = 1288367) B1288367
theorem B3136295 : Blo 858357 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B3260969 : Blo 858357 3260969 := bstep (se 2 (by rfl) ⟨1222863, by rfl⟩ : syracuseStep 3260969 = 2445727) B2445727
theorem B1016915087 : Blo 858357 1016915087 := bstep (se 1 (by rfl) ⟨762686315, by rfl⟩ : syracuseStep 1016915087 = 1525372631) B1525372631
theorem B2090863 : Blo 858357 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B1935467 : Blo 858357 1935467 := bstep (se 1 (by rfl) ⟨1451600, by rfl⟩ : syracuseStep 1935467 = 2903201) B2903201
theorem B5229527 : Blo 858357 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B4353263 : Blo 858357 4353263 := bstep (se 1 (by rfl) ⟨3264947, by rfl⟩ : syracuseStep 4353263 = 6529895) B6529895
theorem B2174951 : Blo 858357 2174951 := bstep (se 1 (by rfl) ⟨1631213, by rfl⟩ : syracuseStep 2174951 = 3262427) B3262427
theorem B1290281 : Blo 858357 1290281 := bstep (se 2 (by rfl) ⟨483855, by rfl⟩ : syracuseStep 1290281 = 967711) B967711
theorem B62788769 : Blo 858357 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B4355369 : Blo 858357 4355369 := bstep (se 2 (by rfl) ⟨1633263, by rfl⟩ : syracuseStep 4355369 = 3266527) B3266527
theorem B12375503 : Blo 858357 12375503 := bstep (se 1 (by rfl) ⟨9281627, by rfl⟩ : syracuseStep 12375503 = 18563255) B18563255
theorem B1931759 : Blo 858357 1931759 := bstep (se 1 (by rfl) ⟨1448819, by rfl⟩ : syracuseStep 1931759 = 2897639) B2897639
theorem B1932479 : Blo 858357 1932479 := bstep (se 1 (by rfl) ⟨1449359, by rfl⟩ : syracuseStep 1932479 = 2898719) B2898719
theorem B859375 : Blo 858357 859375 := bstep (se 1 (by rfl) ⟨644531, by rfl⟩ : syracuseStep 859375 = 1289063) B1289063
theorem B859387 : Blo 858357 859387 := bstep (se 1 (by rfl) ⟨644540, by rfl⟩ : syracuseStep 859387 = 1289081) B1289081
theorem B1449407 : Blo 858357 1449407 := bstep (se 1 (by rfl) ⟨1087055, by rfl⟩ : syracuseStep 1449407 = 2174111) B2174111
theorem B5512859 : Blo 858357 5512859 := bstep (se 1 (by rfl) ⟨4134644, by rfl⟩ : syracuseStep 5512859 = 8269289) B8269289
theorem B859887 : Blo 858357 859887 := bstep (se 1 (by rfl) ⟨644915, by rfl⟩ : syracuseStep 859887 = 1289831) B1289831
theorem B860159 : Blo 858357 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B860187 : Blo 858357 860187 := bstep (se 1 (by rfl) ⟨645140, by rfl⟩ : syracuseStep 860187 = 1290281) B1290281
theorem B8250335 : Blo 858357 8250335 := bstep (se 1 (by rfl) ⟨6187751, by rfl⟩ : syracuseStep 8250335 = 12375503) B12375503
theorem B1287839 : Blo 858357 1287839 := bstep (se 1 (by rfl) ⟨965879, by rfl⟩ : syracuseStep 1287839 = 1931759) B1931759
theorem B11151269 : Blo 858357 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B1288319 : Blo 858357 1288319 := bstep (se 1 (by rfl) ⟨966239, by rfl⟩ : syracuseStep 1288319 = 1932479) B1932479
theorem B2902175 : Blo 858357 2902175 := bstep (se 1 (by rfl) ⟨2176631, by rfl⟩ : syracuseStep 2902175 = 4353263) B4353263
theorem B13945405 : Blo 858357 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B2173979 : Blo 858357 2173979 := bstep (se 1 (by rfl) ⟨1630484, by rfl⟩ : syracuseStep 2173979 = 3260969) B3260969
theorem B2903579 : Blo 858357 2903579 := bstep (se 1 (by rfl) ⟨2177684, by rfl⟩ : syracuseStep 2903579 = 4355369) B4355369
theorem B1290311 : Blo 858357 1290311 := bstep (se 1 (by rfl) ⟨967733, by rfl⟩ : syracuseStep 1290311 = 1935467) B1935467
theorem B3675239 : Blo 858357 3675239 := bstep (se 1 (by rfl) ⟨2756429, by rfl⟩ : syracuseStep 3675239 = 5512859) B5512859
theorem B677943391 : Blo 858357 677943391 := bstep (se 1 (by rfl) ⟨508457543, by rfl⟩ : syracuseStep 677943391 = 1016915087) B1016915087
theorem B41859179 : Blo 858357 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B966271 : Blo 858357 966271 := bstep (se 1 (by rfl) ⟨724703, by rfl⟩ : syracuseStep 966271 = 1449407) B1449407
theorem B1449967 : Blo 858357 1449967 := bstep (se 1 (by rfl) ⟨1087475, by rfl⟩ : syracuseStep 1449967 = 2174951) B2174951
theorem B860207 : Blo 858357 860207 := bstep (se 1 (by rfl) ⟨645155, by rfl⟩ : syracuseStep 860207 = 1290311) B1290311
theorem B2450159 : Blo 858357 2450159 := bstep (se 1 (by rfl) ⟨1837619, by rfl⟩ : syracuseStep 2450159 = 3675239) B3675239
theorem B1934783 : Blo 858357 1934783 := bstep (se 1 (by rfl) ⟨1451087, by rfl⟩ : syracuseStep 1934783 = 2902175) B2902175
theorem B1288361 : Blo 858357 1288361 := bstep (se 2 (by rfl) ⟨483135, by rfl⟩ : syracuseStep 1288361 = 966271) B966271
theorem B1935719 : Blo 858357 1935719 := bstep (se 1 (by rfl) ⟨1451789, by rfl⟩ : syracuseStep 1935719 = 2903579) B2903579
theorem B903924521 : Blo 858357 903924521 := bstep (se 2 (by rfl) ⟨338971695, by rfl⟩ : syracuseStep 903924521 = 677943391) B677943391
theorem B5500223 : Blo 858357 5500223 := bstep (se 1 (by rfl) ⟨4125167, by rfl⟩ : syracuseStep 5500223 = 8250335) B8250335
theorem B7434179 : Blo 858357 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B27906119 : Blo 858357 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B18593873 : Blo 858357 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B858559 : Blo 858357 858559 := bstep (se 1 (by rfl) ⟨643919, by rfl⟩ : syracuseStep 858559 = 1287839) B1287839
theorem B858879 : Blo 858357 858879 := bstep (se 1 (by rfl) ⟨644159, by rfl⟩ : syracuseStep 858879 = 1288319) B1288319
theorem B1449319 : Blo 858357 1449319 := bstep (se 1 (by rfl) ⟨1086989, by rfl⟩ : syracuseStep 1449319 = 2173979) B2173979
theorem B1933289 : Blo 858357 1933289 := bstep (se 2 (by rfl) ⟨724983, by rfl⟩ : syracuseStep 1933289 = 1449967) B1449967
theorem B18604079 : Blo 858357 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B12395915 : Blo 858357 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B1288859 : Blo 858357 1288859 := bstep (se 1 (by rfl) ⟨966644, by rfl⟩ : syracuseStep 1288859 = 1933289) B1933289
theorem B1633439 : Blo 858357 1633439 := bstep (se 1 (by rfl) ⟨1225079, by rfl⟩ : syracuseStep 1633439 = 2450159) B2450159
theorem B1289855 : Blo 858357 1289855 := bstep (se 1 (by rfl) ⟨967391, by rfl⟩ : syracuseStep 1289855 = 1934783) B1934783
theorem B1290479 : Blo 858357 1290479 := bstep (se 1 (by rfl) ⟨967859, by rfl⟩ : syracuseStep 1290479 = 1935719) B1935719
theorem B602616347 : Blo 858357 602616347 := bstep (se 1 (by rfl) ⟨451962260, by rfl⟩ : syracuseStep 602616347 = 903924521) B903924521
theorem B3666815 : Blo 858357 3666815 := bstep (se 1 (by rfl) ⟨2750111, by rfl⟩ : syracuseStep 3666815 = 5500223) B5500223
theorem B858907 : Blo 858357 858907 := bstep (se 1 (by rfl) ⟨644180, by rfl⟩ : syracuseStep 858907 = 1288361) B1288361
theorem B1932425 : Blo 858357 1932425 := bstep (se 2 (by rfl) ⟨724659, by rfl⟩ : syracuseStep 1932425 = 1449319) B1449319
theorem B4956119 : Blo 858357 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B12402719 : Blo 858357 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B860319 : Blo 858357 860319 := bstep (se 1 (by rfl) ⟨645239, by rfl⟩ : syracuseStep 860319 = 1290479) B1290479
theorem B401744231 : Blo 858357 401744231 := bstep (se 1 (by rfl) ⟨301308173, by rfl⟩ : syracuseStep 401744231 = 602616347) B602616347
theorem B1288283 : Blo 858357 1288283 := bstep (se 1 (by rfl) ⟨966212, by rfl⟩ : syracuseStep 1288283 = 1932425) B1932425
theorem B3304079 : Blo 858357 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B2444543 : Blo 858357 2444543 := bstep (se 1 (by rfl) ⟨1833407, by rfl⟩ : syracuseStep 2444543 = 3666815) B3666815
theorem B8263943 : Blo 858357 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B859239 : Blo 858357 859239 := bstep (se 1 (by rfl) ⟨644429, by rfl⟩ : syracuseStep 859239 = 1288859) B1288859
theorem B1088959 : Blo 858357 1088959 := bstep (se 1 (by rfl) ⟨816719, by rfl⟩ : syracuseStep 1088959 = 1633439) B1633439
theorem B859903 : Blo 858357 859903 := bstep (se 1 (by rfl) ⟨644927, by rfl⟩ : syracuseStep 859903 = 1289855) B1289855
theorem B267829487 : Blo 858357 267829487 := bstep (se 1 (by rfl) ⟨200872115, by rfl⟩ : syracuseStep 267829487 = 401744231) B401744231
theorem B1451945 : Blo 858357 1451945 := bstep (se 2 (by rfl) ⟨544479, by rfl⟩ : syracuseStep 1451945 = 1088959) B1088959
theorem B8268479 : Blo 858357 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B5509295 : Blo 858357 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B858855 : Blo 858357 858855 := bstep (se 1 (by rfl) ⟨644141, by rfl⟩ : syracuseStep 858855 = 1288283) B1288283
theorem B2202719 : Blo 858357 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B1629695 : Blo 858357 1629695 := bstep (se 1 (by rfl) ⟨1222271, by rfl⟩ : syracuseStep 1629695 = 2444543) B2444543
theorem B178552991 : Blo 858357 178552991 := bstep (se 1 (by rfl) ⟨133914743, by rfl⟩ : syracuseStep 178552991 = 267829487) B267829487
theorem B5873917 : Blo 858357 5873917 := bstep (se 3 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 5873917 = 2202719) B2202719
theorem B967963 : Blo 858357 967963 := bstep (se 1 (by rfl) ⟨725972, by rfl⟩ : syracuseStep 967963 = 1451945) B1451945
theorem B3672863 : Blo 858357 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B1086463 : Blo 858357 1086463 := bstep (se 1 (by rfl) ⟨814847, by rfl⟩ : syracuseStep 1086463 = 1629695) B1629695
theorem B5512319 : Blo 858357 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B7831889 : Blo 858357 7831889 := bstep (se 2 (by rfl) ⟨2936958, by rfl⟩ : syracuseStep 7831889 = 5873917) B5873917
theorem B1290617 : Blo 858357 1290617 := bstep (se 2 (by rfl) ⟨483981, by rfl⟩ : syracuseStep 1290617 = 967963) B967963
theorem B3674879 : Blo 858357 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B119035327 : Blo 858357 119035327 := bstep (se 1 (by rfl) ⟨89276495, by rfl⟩ : syracuseStep 119035327 = 178552991) B178552991
theorem B1448617 : Blo 858357 1448617 := bstep (se 2 (by rfl) ⟨543231, by rfl⟩ : syracuseStep 1448617 = 1086463) B1086463
theorem B2448575 : Blo 858357 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B860411 : Blo 858357 860411 := bstep (se 1 (by rfl) ⟨645308, by rfl⟩ : syracuseStep 860411 = 1290617) B1290617
theorem B2449919 : Blo 858357 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B158713769 : Blo 858357 158713769 := bstep (se 2 (by rfl) ⟨59517663, by rfl⟩ : syracuseStep 158713769 = 119035327) B119035327
theorem B1632383 : Blo 858357 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B5221259 : Blo 858357 5221259 := bstep (se 1 (by rfl) ⟨3915944, by rfl⟩ : syracuseStep 5221259 = 7831889) B7831889
theorem B1931489 : Blo 858357 1931489 := bstep (se 2 (by rfl) ⟨724308, by rfl⟩ : syracuseStep 1931489 = 1448617) B1448617
theorem B105809179 : Blo 858357 105809179 := bstep (se 1 (by rfl) ⟨79356884, by rfl⟩ : syracuseStep 105809179 = 158713769) B158713769
theorem B1287659 : Blo 858357 1287659 := bstep (se 1 (by rfl) ⟨965744, by rfl⟩ : syracuseStep 1287659 = 1931489) B1931489
theorem B1633279 : Blo 858357 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B1088255 : Blo 858357 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B3480839 : Blo 858357 3480839 := bstep (se 1 (by rfl) ⟨2610629, by rfl⟩ : syracuseStep 3480839 = 5221259) B5221259
theorem B2902013 : Blo 858357 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B2320559 : Blo 858357 2320559 := bstep (se 1 (by rfl) ⟨1740419, by rfl⟩ : syracuseStep 2320559 = 3480839) B3480839
theorem B141078905 : Blo 858357 141078905 := bstep (se 2 (by rfl) ⟨52904589, by rfl⟩ : syracuseStep 141078905 = 105809179) B105809179
theorem B858439 : Blo 858357 858439 := bstep (se 1 (by rfl) ⟨643829, by rfl⟩ : syracuseStep 858439 = 1287659) B1287659
theorem B2177705 : Blo 858357 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B94052603 : Blo 858357 94052603 := bstep (se 1 (by rfl) ⟨70539452, by rfl⟩ : syracuseStep 94052603 = 141078905) B141078905
theorem B1934675 : Blo 858357 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B1451803 : Blo 858357 1451803 := bstep (se 1 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 1451803 = 2177705) B2177705
theorem B1547039 : Blo 858357 1547039 := bstep (se 1 (by rfl) ⟨1160279, by rfl⟩ : syracuseStep 1547039 = 2320559) B2320559
theorem B62701735 : Blo 858357 62701735 := bstep (se 1 (by rfl) ⟨47026301, by rfl⟩ : syracuseStep 62701735 = 94052603) B94052603
theorem B1935737 : Blo 858357 1935737 := bstep (se 2 (by rfl) ⟨725901, by rfl⟩ : syracuseStep 1935737 = 1451803) B1451803
theorem B1289783 : Blo 858357 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B1031359 : Blo 858357 1031359 := bstep (se 1 (by rfl) ⟨773519, by rfl⟩ : syracuseStep 1031359 = 1547039) B1547039
theorem B83602313 : Blo 858357 83602313 := bstep (se 2 (by rfl) ⟨31350867, by rfl⟩ : syracuseStep 83602313 = 62701735) B62701735
theorem B1290491 : Blo 858357 1290491 := bstep (se 1 (by rfl) ⟨967868, by rfl⟩ : syracuseStep 1290491 = 1935737) B1935737
theorem B1375145 : Blo 858357 1375145 := bstep (se 2 (by rfl) ⟨515679, by rfl⟩ : syracuseStep 1375145 = 1031359) B1031359
theorem B859855 : Blo 858357 859855 := bstep (se 1 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 859855 = 1289783) B1289783
theorem B860327 : Blo 858357 860327 := bstep (se 1 (by rfl) ⟨645245, by rfl⟩ : syracuseStep 860327 = 1290491) B1290491
theorem B55734875 : Blo 858357 55734875 := bstep (se 1 (by rfl) ⟨41801156, by rfl⟩ : syracuseStep 55734875 = 83602313) B83602313
theorem B916763 : Blo 858357 916763 := bstep (se 1 (by rfl) ⟨687572, by rfl⟩ : syracuseStep 916763 = 1375145) B1375145
theorem B9778805 : Blo 858357 9778805 := bstep (se 5 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 9778805 = 916763) B916763
theorem B37156583 : Blo 858357 37156583 := bstep (se 1 (by rfl) ⟨27867437, by rfl⟩ : syracuseStep 37156583 = 55734875) B55734875
theorem B6519203 : Blo 858357 6519203 := bstep (se 1 (by rfl) ⟨4889402, by rfl⟩ : syracuseStep 6519203 = 9778805) B9778805
theorem B24771055 : Blo 858357 24771055 := bstep (se 1 (by rfl) ⟨18578291, by rfl⟩ : syracuseStep 24771055 = 37156583) B37156583
theorem B4346135 : Blo 858357 4346135 := bstep (se 1 (by rfl) ⟨3259601, by rfl⟩ : syracuseStep 4346135 = 6519203) B6519203
theorem B33028073 : Blo 858357 33028073 := bstep (se 2 (by rfl) ⟨12385527, by rfl⟩ : syracuseStep 33028073 = 24771055) B24771055
theorem B2897423 : Blo 858357 2897423 := bstep (se 1 (by rfl) ⟨2173067, by rfl⟩ : syracuseStep 2897423 = 4346135) B4346135
theorem B22018715 : Blo 858357 22018715 := bstep (se 1 (by rfl) ⟨16514036, by rfl⟩ : syracuseStep 22018715 = 33028073) B33028073
theorem B1931615 : Blo 858357 1931615 := bstep (se 1 (by rfl) ⟨1448711, by rfl⟩ : syracuseStep 1931615 = 2897423) B2897423
theorem B14679143 : Blo 858357 14679143 := bstep (se 1 (by rfl) ⟨11009357, by rfl⟩ : syracuseStep 14679143 = 22018715) B22018715
theorem B1287743 : Blo 858357 1287743 := bstep (se 1 (by rfl) ⟨965807, by rfl⟩ : syracuseStep 1287743 = 1931615) B1931615
theorem B9786095 : Blo 858357 9786095 := bstep (se 1 (by rfl) ⟨7339571, by rfl⟩ : syracuseStep 9786095 = 14679143) B14679143
theorem B6524063 : Blo 858357 6524063 := bstep (se 1 (by rfl) ⟨4893047, by rfl⟩ : syracuseStep 6524063 = 9786095) B9786095
theorem B858495 : Blo 858357 858495 := bstep (se 1 (by rfl) ⟨643871, by rfl⟩ : syracuseStep 858495 = 1287743) B1287743
theorem B4349375 : Blo 858357 4349375 := bstep (se 1 (by rfl) ⟨3262031, by rfl⟩ : syracuseStep 4349375 = 6524063) B6524063
theorem B2899583 : Blo 858357 2899583 := bstep (se 1 (by rfl) ⟨2174687, by rfl⟩ : syracuseStep 2899583 = 4349375) B4349375
theorem B1933055 : Blo 858357 1933055 := bstep (se 1 (by rfl) ⟨1449791, by rfl⟩ : syracuseStep 1933055 = 2899583) B2899583
theorem B1288703 : Blo 858357 1288703 := bstep (se 1 (by rfl) ⟨966527, by rfl⟩ : syracuseStep 1288703 = 1933055) B1933055
theorem B859135 : Blo 858357 859135 := bstep (se 1 (by rfl) ⟨644351, by rfl⟩ : syracuseStep 859135 = 1288703) B1288703

theorem C0 (j : ℕ) (h1 : 214589 ≤ j) (h2 : j ≤ 215140) : Blo 858357 (4 * j + 3) := by
  interval_cases j
  · exact B858359
  · exact B858363
  · exact B858367
  · exact B858371
  · exact B858375
  · exact B858379
  · exact B858383
  · exact B858387
  · exact B858391
  · exact B858395
  · exact B858399
  · exact B858403
  · exact B858407
  · exact B858411
  · exact B858415
  · exact B858419
  · exact B858423
  · exact B858427
  · exact B858431
  · exact B858435
  · exact B858439
  · exact B858443
  · exact B858447
  · exact B858451
  · exact B858455
  · exact B858459
  · exact B858463
  · exact B858467
  · exact B858471
  · exact B858475
  · exact B858479
  · exact B858483
  · exact B858487
  · exact B858491
  · exact B858495
  · exact B858499
  · exact B858503
  · exact B858507
  · exact B858511
  · exact B858515
  · exact B858519
  · exact B858523
  · exact B858527
  · exact B858531
  · exact B858535
  · exact B858539
  · exact B858543
  · exact B858547
  · exact B858551
  · exact B858555
  · exact B858559
  · exact B858563
  · exact B858567
  · exact B858571
  · exact B858575
  · exact B858579
  · exact B858583
  · exact B858587
  · exact B858591
  · exact B858595
  · exact B858599
  · exact B858603
  · exact B858607
  · exact B858611
  · exact B858615
  · exact B858619
  · exact B858623
  · exact B858627
  · exact B858631
  · exact B858635
  · exact B858639
  · exact B858643
  · exact B858647
  · exact B858651
  · exact B858655
  · exact B858659
  · exact B858663
  · exact B858667
  · exact B858671
  · exact B858675
  · exact B858679
  · exact B858683
  · exact B858687
  · exact B858691
  · exact B858695
  · exact B858699
  · exact B858703
  · exact B858707
  · exact B858711
  · exact B858715
  · exact B858719
  · exact B858723
  · exact B858727
  · exact B858731
  · exact B858735
  · exact B858739
  · exact B858743
  · exact B858747
  · exact B858751
  · exact B858755
  · exact B858759
  · exact B858763
  · exact B858767
  · exact B858771
  · exact B858775
  · exact B858779
  · exact B858783
  · exact B858787
  · exact B858791
  · exact B858795
  · exact B858799
  · exact B858803
  · exact B858807
  · exact B858811
  · exact B858815
  · exact B858819
  · exact B858823
  · exact B858827
  · exact B858831
  · exact B858835
  · exact B858839
  · exact B858843
  · exact B858847
  · exact B858851
  · exact B858855
  · exact B858859
  · exact B858863
  · exact B858867
  · exact B858871
  · exact B858875
  · exact B858879
  · exact B858883
  · exact B858887
  · exact B858891
  · exact B858895
  · exact B858899
  · exact B858903
  · exact B858907
  · exact B858911
  · exact B858915
  · exact B858919
  · exact B858923
  · exact B858927
  · exact B858931
  · exact B858935
  · exact B858939
  · exact B858943
  · exact B858947
  · exact B858951
  · exact B858955
  · exact B858959
  · exact B858963
  · exact B858967
  · exact B858971
  · exact B858975
  · exact B858979
  · exact B858983
  · exact B858987
  · exact B858991
  · exact B858995
  · exact B858999
  · exact B859003
  · exact B859007
  · exact B859011
  · exact B859015
  · exact B859019
  · exact B859023
  · exact B859027
  · exact B859031
  · exact B859035
  · exact B859039
  · exact B859043
  · exact B859047
  · exact B859051
  · exact B859055
  · exact B859059
  · exact B859063
  · exact B859067
  · exact B859071
  · exact B859075
  · exact B859079
  · exact B859083
  · exact B859087
  · exact B859091
  · exact B859095
  · exact B859099
  · exact B859103
  · exact B859107
  · exact B859111
  · exact B859115
  · exact B859119
  · exact B859123
  · exact B859127
  · exact B859131
  · exact B859135
  · exact B859139
  · exact B859143
  · exact B859147
  · exact B859151
  · exact B859155
  · exact B859159
  · exact B859163
  · exact B859167
  · exact B859171
  · exact B859175
  · exact B859179
  · exact B859183
  · exact B859187
  · exact B859191
  · exact B859195
  · exact B859199
  · exact B859203
  · exact B859207
  · exact B859211
  · exact B859215
  · exact B859219
  · exact B859223
  · exact B859227
  · exact B859231
  · exact B859235
  · exact B859239
  · exact B859243
  · exact B859247
  · exact B859251
  · exact B859255
  · exact B859259
  · exact B859263
  · exact B859267
  · exact B859271
  · exact B859275
  · exact B859279
  · exact B859283
  · exact B859287
  · exact B859291
  · exact B859295
  · exact B859299
  · exact B859303
  · exact B859307
  · exact B859311
  · exact B859315
  · exact B859319
  · exact B859323
  · exact B859327
  · exact B859331
  · exact B859335
  · exact B859339
  · exact B859343
  · exact B859347
  · exact B859351
  · exact B859355
  · exact B859359
  · exact B859363
  · exact B859367
  · exact B859371
  · exact B859375
  · exact B859379
  · exact B859383
  · exact B859387
  · exact B859391
  · exact B859395
  · exact B859399
  · exact B859403
  · exact B859407
  · exact B859411
  · exact B859415
  · exact B859419
  · exact B859423
  · exact B859427
  · exact B859431
  · exact B859435
  · exact B859439
  · exact B859443
  · exact B859447
  · exact B859451
  · exact B859455
  · exact B859459
  · exact B859463
  · exact B859467
  · exact B859471
  · exact B859475
  · exact B859479
  · exact B859483
  · exact B859487
  · exact B859491
  · exact B859495
  · exact B859499
  · exact B859503
  · exact B859507
  · exact B859511
  · exact B859515
  · exact B859519
  · exact B859523
  · exact B859527
  · exact B859531
  · exact B859535
  · exact B859539
  · exact B859543
  · exact B859547
  · exact B859551
  · exact B859555
  · exact B859559
  · exact B859563
  · exact B859567
  · exact B859571
  · exact B859575
  · exact B859579
  · exact B859583
  · exact B859587
  · exact B859591
  · exact B859595
  · exact B859599
  · exact B859603
  · exact B859607
  · exact B859611
  · exact B859615
  · exact B859619
  · exact B859623
  · exact B859627
  · exact B859631
  · exact B859635
  · exact B859639
  · exact B859643
  · exact B859647
  · exact B859651
  · exact B859655
  · exact B859659
  · exact B859663
  · exact B859667
  · exact B859671
  · exact B859675
  · exact B859679
  · exact B859683
  · exact B859687
  · exact B859691
  · exact B859695
  · exact B859699
  · exact B859703
  · exact B859707
  · exact B859711
  · exact B859715
  · exact B859719
  · exact B859723
  · exact B859727
  · exact B859731
  · exact B859735
  · exact B859739
  · exact B859743
  · exact B859747
  · exact B859751
  · exact B859755
  · exact B859759
  · exact B859763
  · exact B859767
  · exact B859771
  · exact B859775
  · exact B859779
  · exact B859783
  · exact B859787
  · exact B859791
  · exact B859795
  · exact B859799
  · exact B859803
  · exact B859807
  · exact B859811
  · exact B859815
  · exact B859819
  · exact B859823
  · exact B859827
  · exact B859831
  · exact B859835
  · exact B859839
  · exact B859843
  · exact B859847
  · exact B859851
  · exact B859855
  · exact B859859
  · exact B859863
  · exact B859867
  · exact B859871
  · exact B859875
  · exact B859879
  · exact B859883
  · exact B859887
  · exact B859891
  · exact B859895
  · exact B859899
  · exact B859903
  · exact B859907
  · exact B859911
  · exact B859915
  · exact B859919
  · exact B859923
  · exact B859927
  · exact B859931
  · exact B859935
  · exact B859939
  · exact B859943
  · exact B859947
  · exact B859951
  · exact B859955
  · exact B859959
  · exact B859963
  · exact B859967
  · exact B859971
  · exact B859975
  · exact B859979
  · exact B859983
  · exact B859987
  · exact B859991
  · exact B859995
  · exact B859999
  · exact B860003
  · exact B860007
  · exact B860011
  · exact B860015
  · exact B860019
  · exact B860023
  · exact B860027
  · exact B860031
  · exact B860035
  · exact B860039
  · exact B860043
  · exact B860047
  · exact B860051
  · exact B860055
  · exact B860059
  · exact B860063
  · exact B860067
  · exact B860071
  · exact B860075
  · exact B860079
  · exact B860083
  · exact B860087
  · exact B860091
  · exact B860095
  · exact B860099
  · exact B860103
  · exact B860107
  · exact B860111
  · exact B860115
  · exact B860119
  · exact B860123
  · exact B860127
  · exact B860131
  · exact B860135
  · exact B860139
  · exact B860143
  · exact B860147
  · exact B860151
  · exact B860155
  · exact B860159
  · exact B860163
  · exact B860167
  · exact B860171
  · exact B860175
  · exact B860179
  · exact B860183
  · exact B860187
  · exact B860191
  · exact B860195
  · exact B860199
  · exact B860203
  · exact B860207
  · exact B860211
  · exact B860215
  · exact B860219
  · exact B860223
  · exact B860227
  · exact B860231
  · exact B860235
  · exact B860239
  · exact B860243
  · exact B860247
  · exact B860251
  · exact B860255
  · exact B860259
  · exact B860263
  · exact B860267
  · exact B860271
  · exact B860275
  · exact B860279
  · exact B860283
  · exact B860287
  · exact B860291
  · exact B860295
  · exact B860299
  · exact B860303
  · exact B860307
  · exact B860311
  · exact B860315
  · exact B860319
  · exact B860323
  · exact B860327
  · exact B860331
  · exact B860335
  · exact B860339
  · exact B860343
  · exact B860347
  · exact B860351
  · exact B860355
  · exact B860359
  · exact B860363
  · exact B860367
  · exact B860371
  · exact B860375
  · exact B860379
  · exact B860383
  · exact B860387
  · exact B860391
  · exact B860395
  · exact B860399
  · exact B860403
  · exact B860407
  · exact B860411
  · exact B860415
  · exact B860419
  · exact B860423
  · exact B860427
  · exact B860431
  · exact B860435
  · exact B860439
  · exact B860443
  · exact B860447
  · exact B860451
  · exact B860455
  · exact B860459
  · exact B860463
  · exact B860467
  · exact B860471
  · exact B860475
  · exact B860479
  · exact B860483
  · exact B860487
  · exact B860491
  · exact B860495
  · exact B860499
  · exact B860503
  · exact B860507
  · exact B860511
  · exact B860515
  · exact B860519
  · exact B860523
  · exact B860527
  · exact B860531
  · exact B860535
  · exact B860539
  · exact B860543
  · exact B860547
  · exact B860551
  · exact B860555
  · exact B860559
  · exact B860563

theorem solution (m : ℕ) (hlo : 858357 ≤ m) (hhi : m ≤ 860563) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 214589 ≤ j := by omega
    have hj2 : j ≤ 215140 := by omega
    have hb : Blo 858357 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
