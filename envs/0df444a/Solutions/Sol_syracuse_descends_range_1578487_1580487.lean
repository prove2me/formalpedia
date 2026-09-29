-- Prove2me | solution 1 for syracuse_descends_range_1578487_1580487
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:07:37.739286+00:00
-- url     : https://prove2.me/submissions/9a2b848a-3578-4329-b0e0-0ed430d0cfd7

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


theorem B1998857 : Blo 1578487 1998857 := bbase (se 2 (by rfl) ⟨749571, by rfl⟩ : syracuseStep 1998857 = 1499143) (by norm_num)
theorem B3555341 : Blo 1578487 3555341 := bbase (se 3 (by rfl) ⟨666626, by rfl⟩ : syracuseStep 3555341 = 1333253) (by norm_num)
theorem B1777693 : Blo 1578487 1777693 := bbase (se 3 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 1777693 = 666635) (by norm_num)
theorem B2998309 : Blo 1578487 2998309 := bbase (se 4 (by rfl) ⟨281091, by rfl⟩ : syracuseStep 2998309 = 562183) (by norm_num)
theorem B4055093 : Blo 1578487 4055093 := bbase (se 5 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 4055093 = 380165) (by norm_num)
theorem B1998913 : Blo 1578487 1998913 := bbase (se 2 (by rfl) ⟨749592, by rfl⟩ : syracuseStep 1998913 = 1499185) (by norm_num)
theorem B1777729 : Blo 1578487 1777729 := bbase (se 2 (by rfl) ⟨666648, by rfl⟩ : syracuseStep 1777729 = 1333297) (by norm_num)
theorem B6406229 : Blo 1578487 6406229 := bbase (se 8 (by rfl) ⟨37536, by rfl⟩ : syracuseStep 6406229 = 75073) (by norm_num)
theorem B3555413 : Blo 1578487 3555413 := bbase (se 8 (by rfl) ⟨20832, by rfl⟩ : syracuseStep 3555413 = 41665) (by norm_num)
theorem B5333093 : Blo 1578487 5333093 := bbase (se 4 (by rfl) ⟨499977, by rfl⟩ : syracuseStep 5333093 = 999955) (by norm_num)
theorem B1777765 : Blo 1578487 1777765 := bbase (se 4 (by rfl) ⟨166665, by rfl⟩ : syracuseStep 1777765 = 333331) (by norm_num)
theorem B1622125 : Blo 1578487 1622125 := bbase (se 3 (by rfl) ⟨304148, by rfl⟩ : syracuseStep 1622125 = 608297) (by norm_num)
theorem B7995509 : Blo 1578487 7995509 := bbase (se 5 (by rfl) ⟨374789, by rfl⟩ : syracuseStep 7995509 = 749579) (by norm_num)
theorem B1777801 : Blo 1578487 1777801 := bbase (se 2 (by rfl) ⟨666675, by rfl⟩ : syracuseStep 1777801 = 1333351) (by norm_num)
theorem B5996693 : Blo 1578487 5996693 := bbase (se 6 (by rfl) ⟨140547, by rfl⟩ : syracuseStep 5996693 = 281095) (by norm_num)
theorem B3555485 : Blo 1578487 3555485 := bbase (se 3 (by rfl) ⟨666653, by rfl⟩ : syracuseStep 3555485 = 1333307) (by norm_num)
theorem B1999009 : Blo 1578487 1999009 := bbase (se 2 (by rfl) ⟨749628, by rfl⟩ : syracuseStep 1999009 = 1499257) (by norm_num)
theorem B1777837 : Blo 1578487 1777837 := bbase (se 3 (by rfl) ⟨333344, by rfl⟩ : syracuseStep 1777837 = 666689) (by norm_num)
theorem B2998453 : Blo 1578487 2998453 := bbase (se 5 (by rfl) ⟨140552, by rfl⟩ : syracuseStep 2998453 = 281105) (by norm_num)
theorem B5062837 : Blo 1578487 5062837 := bbase (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) (by norm_num)
theorem B1851589 : Blo 1578487 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B7594181 : Blo 1578487 7594181 := bbase (se 4 (by rfl) ⟨711954, by rfl⟩ : syracuseStep 7594181 = 1423909) (by norm_num)
theorem B1777873 : Blo 1578487 1777873 := bbase (se 2 (by rfl) ⟨666702, by rfl⟩ : syracuseStep 1777873 = 1333405) (by norm_num)
theorem B3555557 : Blo 1578487 3555557 := bbase (se 4 (by rfl) ⟨333333, by rfl⟩ : syracuseStep 3555557 = 666667) (by norm_num)
theorem B13156597 : Blo 1578487 13156597 := bbase (se 5 (by rfl) ⟨616715, by rfl⟩ : syracuseStep 13156597 = 1233431) (by norm_num)
theorem B3465461 : Blo 1578487 3465461 := bbase (se 5 (by rfl) ⟨162443, by rfl⟩ : syracuseStep 3465461 = 324887) (by norm_num)
theorem B1777909 : Blo 1578487 1777909 := bbase (se 5 (by rfl) ⟨83339, by rfl⟩ : syracuseStep 1777909 = 166679) (by norm_num)
theorem B2367749 : Blo 1578487 2367749 := bbase (se 4 (by rfl) ⟨221976, by rfl⟩ : syracuseStep 2367749 = 443953) (by norm_num)
theorem B3997957 : Blo 1578487 3997957 := bbase (se 4 (by rfl) ⟨374808, by rfl⟩ : syracuseStep 3997957 = 749617) (by norm_num)
theorem B6750485 : Blo 1578487 6750485 := bbase (se 6 (by rfl) ⟨158214, by rfl⟩ : syracuseStep 6750485 = 316429) (by norm_num)
theorem B1777945 : Blo 1578487 1777945 := bbase (se 2 (by rfl) ⟨666729, by rfl⟩ : syracuseStep 1777945 = 1333459) (by norm_num)
theorem B2367773 : Blo 1578487 2367773 := bbase (se 3 (by rfl) ⟨443957, by rfl⟩ : syracuseStep 2367773 = 887915) (by norm_num)
theorem B3555629 : Blo 1578487 3555629 := bbase (se 3 (by rfl) ⟨666680, by rfl⟩ : syracuseStep 3555629 = 1333361) (by norm_num)
theorem B2367797 : Blo 1578487 2367797 := bbase (se 5 (by rfl) ⟨110990, by rfl⟩ : syracuseStep 2367797 = 221981) (by norm_num)
theorem B1777981 : Blo 1578487 1777981 := bbase (se 3 (by rfl) ⟨333371, by rfl⟩ : syracuseStep 1777981 = 666743) (by norm_num)
theorem B2433349 : Blo 1578487 2433349 := bbase (se 4 (by rfl) ⟨228126, by rfl⟩ : syracuseStep 2433349 = 456253) (by norm_num)
theorem B2367821 : Blo 1578487 2367821 := bbase (se 3 (by rfl) ⟨443966, by rfl⟩ : syracuseStep 2367821 = 887933) (by norm_num)
theorem B1999181 : Blo 1578487 1999181 := bbase (se 3 (by rfl) ⟨374846, by rfl⟩ : syracuseStep 1999181 = 749693) (by norm_num)
theorem B2998613 : Blo 1578487 2998613 := bbase (se 10 (by rfl) ⟨4392, by rfl⟩ : syracuseStep 2998613 = 8785) (by norm_num)
theorem B32440661 : Blo 1578487 32440661 := bbase (se 10 (by rfl) ⟨47520, by rfl⟩ : syracuseStep 32440661 = 95041) (by norm_num)
theorem B1778017 : Blo 1578487 1778017 := bbase (se 2 (by rfl) ⟨666756, by rfl⟩ : syracuseStep 1778017 = 1333513) (by norm_num)
theorem B2367845 : Blo 1578487 2367845 := bbase (se 4 (by rfl) ⟨221985, by rfl⟩ : syracuseStep 2367845 = 443971) (by norm_num)
theorem B3998069 : Blo 1578487 3998069 := bbase (se 5 (by rfl) ⟨187409, by rfl⟩ : syracuseStep 3998069 = 374819) (by norm_num)
theorem B3555701 : Blo 1578487 3555701 := bbase (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) (by norm_num)
theorem B2367869 : Blo 1578487 2367869 := bbase (se 3 (by rfl) ⟨443975, by rfl⟩ : syracuseStep 2367869 = 887951) (by norm_num)
theorem B1999237 : Blo 1578487 1999237 := bbase (se 4 (by rfl) ⟨187428, by rfl⟩ : syracuseStep 1999237 = 374857) (by norm_num)
theorem B2367893 : Blo 1578487 2367893 := bbase (se 6 (by rfl) ⟨55497, by rfl⟩ : syracuseStep 2367893 = 110995) (by norm_num)
theorem B2367917 : Blo 1578487 2367917 := bbase (se 3 (by rfl) ⟨443984, by rfl⟩ : syracuseStep 2367917 = 887969) (by norm_num)
theorem B3555773 : Blo 1578487 3555773 := bbase (se 3 (by rfl) ⟨666707, by rfl⟩ : syracuseStep 3555773 = 1333415) (by norm_num)
theorem B2367941 : Blo 1578487 2367941 := bbase (se 4 (by rfl) ⟨221994, by rfl⟩ : syracuseStep 2367941 = 443989) (by norm_num)
theorem B2367965 : Blo 1578487 2367965 := bbase (se 3 (by rfl) ⟨443993, by rfl⟩ : syracuseStep 2367965 = 887987) (by norm_num)
theorem B2998757 : Blo 1578487 2998757 := bbase (se 4 (by rfl) ⟨281133, by rfl⟩ : syracuseStep 2998757 = 562267) (by norm_num)
theorem B1999333 : Blo 1578487 1999333 := bbase (se 4 (by rfl) ⟨187437, by rfl⟩ : syracuseStep 1999333 = 374875) (by norm_num)
theorem B2367989 : Blo 1578487 2367989 := bbase (se 5 (by rfl) ⟨110999, by rfl⟩ : syracuseStep 2367989 = 221999) (by norm_num)
theorem B2564605 : Blo 1578487 2564605 := bbase (se 3 (by rfl) ⟨480863, by rfl⟩ : syracuseStep 2564605 = 961727) (by norm_num)
theorem B3555845 : Blo 1578487 3555845 := bbase (se 4 (by rfl) ⟨333360, by rfl⟩ : syracuseStep 3555845 = 666721) (by norm_num)
theorem B2368013 : Blo 1578487 2368013 := bbase (se 3 (by rfl) ⟨444002, by rfl⟩ : syracuseStep 2368013 = 888005) (by norm_num)
theorem B25960981 : Blo 1578487 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B5333525 : Blo 1578487 5333525 := bbase (se 6 (by rfl) ⟨125004, by rfl⟩ : syracuseStep 5333525 = 250009) (by norm_num)
theorem B2368037 : Blo 1578487 2368037 := bbase (se 4 (by rfl) ⟨222003, by rfl⟩ : syracuseStep 2368037 = 444007) (by norm_num)
theorem B3998261 : Blo 1578487 3998261 := bbase (se 5 (by rfl) ⟨187418, by rfl⟩ : syracuseStep 3998261 = 374837) (by norm_num)
theorem B2368061 : Blo 1578487 2368061 := bbase (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) (by norm_num)
theorem B3555917 : Blo 1578487 3555917 := bbase (se 3 (by rfl) ⟨666734, by rfl⟩ : syracuseStep 3555917 = 1333469) (by norm_num)
theorem B2368085 : Blo 1578487 2368085 := bbase (se 8 (by rfl) ⟨13875, by rfl⟩ : syracuseStep 2368085 = 27751) (by norm_num)
theorem B16212565 : Blo 1578487 16212565 := bbase (se 8 (by rfl) ⟨94995, by rfl⟩ : syracuseStep 16212565 = 189991) (by norm_num)
theorem B4498021 : Blo 1578487 4498021 := bbase (se 4 (by rfl) ⟨421689, by rfl⟩ : syracuseStep 4498021 = 843379) (by norm_num)
theorem B2368109 : Blo 1578487 2368109 := bbase (se 3 (by rfl) ⟨444020, by rfl⟩ : syracuseStep 2368109 = 888041) (by norm_num)
theorem B2368133 : Blo 1578487 2368133 := bbase (se 4 (by rfl) ⟨222012, by rfl⟩ : syracuseStep 2368133 = 444025) (by norm_num)
theorem B1999505 : Blo 1578487 1999505 := bbase (se 2 (by rfl) ⟨749814, by rfl⟩ : syracuseStep 1999505 = 1499629) (by norm_num)
theorem B7586453 : Blo 1578487 7586453 := bbase (se 6 (by rfl) ⟨177807, by rfl⟩ : syracuseStep 7586453 = 355615) (by norm_num)
theorem B10117781 : Blo 1578487 10117781 := bbase (se 6 (by rfl) ⟨237135, by rfl⟩ : syracuseStep 10117781 = 474271) (by norm_num)
theorem B3555989 : Blo 1578487 3555989 := bbase (se 6 (by rfl) ⟨83343, by rfl⟩ : syracuseStep 3555989 = 166687) (by norm_num)
theorem B2368157 : Blo 1578487 2368157 := bbase (se 3 (by rfl) ⟨444029, by rfl⟩ : syracuseStep 2368157 = 888059) (by norm_num)
theorem B2368181 : Blo 1578487 2368181 := bbase (se 5 (by rfl) ⟨111008, by rfl⟩ : syracuseStep 2368181 = 222017) (by norm_num)
theorem B1999561 : Blo 1578487 1999561 := bbase (se 2 (by rfl) ⟨749835, by rfl⟩ : syracuseStep 1999561 = 1499671) (by norm_num)
theorem B2368205 : Blo 1578487 2368205 := bbase (se 3 (by rfl) ⟨444038, by rfl⟩ : syracuseStep 2368205 = 888077) (by norm_num)
theorem B3556061 : Blo 1578487 3556061 := bbase (se 3 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 3556061 = 1333523) (by norm_num)
theorem B2368229 : Blo 1578487 2368229 := bbase (se 4 (by rfl) ⟨222021, by rfl⟩ : syracuseStep 2368229 = 444043) (by norm_num)
theorem B2368253 : Blo 1578487 2368253 := bbase (se 3 (by rfl) ⟨444047, by rfl⟩ : syracuseStep 2368253 = 888095) (by norm_num)
theorem B2999045 : Blo 1578487 2999045 := bbase (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) (by norm_num)
theorem B2368277 : Blo 1578487 2368277 := bbase (se 6 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 2368277 = 111013) (by norm_num)
theorem B1999657 : Blo 1578487 1999657 := bbase (se 2 (by rfl) ⟨749871, by rfl⟩ : syracuseStep 1999657 = 1499743) (by norm_num)
theorem B2368301 : Blo 1578487 2368301 := bbase (se 3 (by rfl) ⟨444056, by rfl⟩ : syracuseStep 2368301 = 888113) (by norm_num)
theorem B1622849 : Blo 1578487 1622849 := bbase (se 2 (by rfl) ⟨608568, by rfl⟩ : syracuseStep 1622849 = 1217137) (by norm_num)
theorem B2368325 : Blo 1578487 2368325 := bbase (se 4 (by rfl) ⟨222030, by rfl⟩ : syracuseStep 2368325 = 444061) (by norm_num)
theorem B2368349 : Blo 1578487 2368349 := bbase (se 3 (by rfl) ⟨444065, by rfl⟩ : syracuseStep 2368349 = 888131) (by norm_num)
theorem B2368373 : Blo 1578487 2368373 := bbase (se 5 (by rfl) ⟨111017, by rfl⟩ : syracuseStep 2368373 = 222035) (by norm_num)
theorem B2368397 : Blo 1578487 2368397 := bbase (se 3 (by rfl) ⟨444074, by rfl⟩ : syracuseStep 2368397 = 888149) (by norm_num)
theorem B3998605 : Blo 1578487 3998605 := bbase (se 3 (by rfl) ⟨749738, by rfl⟩ : syracuseStep 3998605 = 1499477) (by norm_num)
theorem B2999197 : Blo 1578487 2999197 := bbase (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) (by norm_num)
theorem B2368421 : Blo 1578487 2368421 := bbase (se 4 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 2368421 = 444079) (by norm_num)
theorem B2368445 : Blo 1578487 2368445 := bbase (se 3 (by rfl) ⟨444083, by rfl⟩ : syracuseStep 2368445 = 888167) (by norm_num)
theorem B5333957 : Blo 1578487 5333957 := bbase (se 4 (by rfl) ⟨500058, by rfl⟩ : syracuseStep 5333957 = 1000117) (by norm_num)
theorem B2368469 : Blo 1578487 2368469 := bbase (se 7 (by rfl) ⟨27755, by rfl⟩ : syracuseStep 2368469 = 55511) (by norm_num)
theorem B1999829 : Blo 1578487 1999829 := bbase (se 7 (by rfl) ⟨23435, by rfl⟩ : syracuseStep 1999829 = 46871) (by norm_num)
theorem B2368493 : Blo 1578487 2368493 := bbase (se 3 (by rfl) ⟨444092, by rfl⟩ : syracuseStep 2368493 = 888185) (by norm_num)
theorem B3998717 : Blo 1578487 3998717 := bbase (se 3 (by rfl) ⟨749759, by rfl⟩ : syracuseStep 3998717 = 1499519) (by norm_num)
theorem B2368517 : Blo 1578487 2368517 := bbase (se 4 (by rfl) ⟨222048, by rfl⟩ : syracuseStep 2368517 = 444097) (by norm_num)
theorem B1999885 : Blo 1578487 1999885 := bbase (se 3 (by rfl) ⟨374978, by rfl⟩ : syracuseStep 1999885 = 749957) (by norm_num)
theorem B2368541 : Blo 1578487 2368541 := bbase (se 3 (by rfl) ⟨444101, by rfl⟩ : syracuseStep 2368541 = 888203) (by norm_num)
theorem B2368565 : Blo 1578487 2368565 := bbase (se 5 (by rfl) ⟨111026, by rfl⟩ : syracuseStep 2368565 = 222053) (by norm_num)
theorem B2368589 : Blo 1578487 2368589 := bbase (se 3 (by rfl) ⟨444110, by rfl⟩ : syracuseStep 2368589 = 888221) (by norm_num)
theorem B2368613 : Blo 1578487 2368613 := bbase (se 4 (by rfl) ⟨222057, by rfl⟩ : syracuseStep 2368613 = 444115) (by norm_num)
theorem B1999981 : Blo 1578487 1999981 := bbase (se 3 (by rfl) ⟨374996, by rfl⟩ : syracuseStep 1999981 = 749993) (by norm_num)
theorem B2368637 : Blo 1578487 2368637 := bbase (se 3 (by rfl) ⟨444119, by rfl⟩ : syracuseStep 2368637 = 888239) (by norm_num)
theorem B3794053 : Blo 1578487 3794053 := bbase (se 4 (by rfl) ⟨355692, by rfl⟩ : syracuseStep 3794053 = 711385) (by norm_num)
theorem B6743189 : Blo 1578487 6743189 := bbase (se 6 (by rfl) ⟨158043, by rfl⟩ : syracuseStep 6743189 = 316087) (by norm_num)
theorem B2368661 : Blo 1578487 2368661 := bbase (se 6 (by rfl) ⟨55515, by rfl⟩ : syracuseStep 2368661 = 111031) (by norm_num)
theorem B2925733 : Blo 1578487 2925733 := bbase (se 4 (by rfl) ⟨274287, by rfl⟩ : syracuseStep 2925733 = 548575) (by norm_num)
theorem B2368685 : Blo 1578487 2368685 := bbase (se 3 (by rfl) ⟨444128, by rfl⟩ : syracuseStep 2368685 = 888257) (by norm_num)
theorem B8996021 : Blo 1578487 8996021 := bbase (se 5 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 8996021 = 843377) (by norm_num)
theorem B3998909 : Blo 1578487 3998909 := bbase (se 3 (by rfl) ⟨749795, by rfl⟩ : syracuseStep 3998909 = 1499591) (by norm_num)
theorem B2368709 : Blo 1578487 2368709 := bbase (se 4 (by rfl) ⟨222066, by rfl⟩ : syracuseStep 2368709 = 444133) (by norm_num)
theorem B2999501 : Blo 1578487 2999501 := bbase (se 3 (by rfl) ⟨562406, by rfl⟩ : syracuseStep 2999501 = 1124813) (by norm_num)
theorem B2368733 : Blo 1578487 2368733 := bbase (se 3 (by rfl) ⟨444137, by rfl⟩ : syracuseStep 2368733 = 888275) (by norm_num)
theorem B3794149 : Blo 1578487 3794149 := bbase (se 4 (by rfl) ⟨355701, by rfl⟩ : syracuseStep 3794149 = 711403) (by norm_num)
theorem B2368757 : Blo 1578487 2368757 := bbase (se 5 (by rfl) ⟨111035, by rfl⟩ : syracuseStep 2368757 = 222071) (by norm_num)
theorem B2368781 : Blo 1578487 2368781 := bbase (se 3 (by rfl) ⟨444146, by rfl⟩ : syracuseStep 2368781 = 888293) (by norm_num)
theorem B2000153 : Blo 1578487 2000153 := bbase (se 2 (by rfl) ⟨750057, by rfl⟩ : syracuseStep 2000153 = 1500115) (by norm_num)
theorem B2368805 : Blo 1578487 2368805 := bbase (se 4 (by rfl) ⟨222075, by rfl⟩ : syracuseStep 2368805 = 444151) (by norm_num)
theorem B2663725 : Blo 1578487 2663725 := bbase (se 3 (by rfl) ⟨499448, by rfl⟩ : syracuseStep 2663725 = 998897) (by norm_num)
theorem B2368829 : Blo 1578487 2368829 := bbase (se 3 (by rfl) ⟨444155, by rfl⟩ : syracuseStep 2368829 = 888311) (by norm_num)
theorem B2000209 : Blo 1578487 2000209 := bbase (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) (by norm_num)
theorem B2368853 : Blo 1578487 2368853 := bbase (se 12 (by rfl) ⟨867, by rfl⟩ : syracuseStep 2368853 = 1735) (by norm_num)
theorem B2368877 : Blo 1578487 2368877 := bbase (se 3 (by rfl) ⟨444164, by rfl⟩ : syracuseStep 2368877 = 888329) (by norm_num)
theorem B2663813 : Blo 1578487 2663813 := bbase (se 4 (by rfl) ⟨249732, by rfl⟩ : syracuseStep 2663813 = 499465) (by norm_num)
theorem B2368901 : Blo 1578487 2368901 := bbase (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) (by norm_num)
theorem B7996805 : Blo 1578487 7996805 := bbase (se 4 (by rfl) ⟨749700, by rfl⟩ : syracuseStep 7996805 = 1499401) (by norm_num)
theorem B2368925 : Blo 1578487 2368925 := bbase (se 3 (by rfl) ⟨444173, by rfl⟩ : syracuseStep 2368925 = 888347) (by norm_num)
theorem B2000305 : Blo 1578487 2000305 := bbase (se 2 (by rfl) ⟨750114, by rfl⟩ : syracuseStep 2000305 = 1500229) (by norm_num)
theorem B2368949 : Blo 1578487 2368949 := bbase (se 5 (by rfl) ⟨111044, by rfl⟩ : syracuseStep 2368949 = 222089) (by norm_num)
theorem B3417533 : Blo 1578487 3417533 := bbase (se 3 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 3417533 = 1281575) (by norm_num)
theorem B2368973 : Blo 1578487 2368973 := bbase (se 3 (by rfl) ⟨444182, by rfl⟩ : syracuseStep 2368973 = 888365) (by norm_num)
theorem B2368997 : Blo 1578487 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B2164205 : Blo 1578487 2164205 := bbase (se 3 (by rfl) ⟨405788, by rfl⟩ : syracuseStep 2164205 = 811577) (by norm_num)
theorem B3802621 : Blo 1578487 3802621 := bbase (se 3 (by rfl) ⟨712991, by rfl⟩ : syracuseStep 3802621 = 1425983) (by norm_num)
theorem B2369021 : Blo 1578487 2369021 := bbase (se 3 (by rfl) ⟨444191, by rfl⟩ : syracuseStep 2369021 = 888383) (by norm_num)
theorem B2663941 : Blo 1578487 2663941 := bbase (se 4 (by rfl) ⟨249744, by rfl⟩ : syracuseStep 2663941 = 499489) (by norm_num)
theorem B2369045 : Blo 1578487 2369045 := bbase (se 6 (by rfl) ⟨55524, by rfl⟩ : syracuseStep 2369045 = 111049) (by norm_num)
theorem B3999253 : Blo 1578487 3999253 := bbase (se 6 (by rfl) ⟨93732, by rfl⟩ : syracuseStep 3999253 = 187465) (by norm_num)
theorem B2369069 : Blo 1578487 2369069 := bbase (se 3 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 2369069 = 888401) (by norm_num)
theorem B2369093 : Blo 1578487 2369093 := bbase (se 4 (by rfl) ⟨222102, by rfl⟩ : syracuseStep 2369093 = 444205) (by norm_num)
theorem B2664029 : Blo 1578487 2664029 := bbase (se 3 (by rfl) ⟨499505, by rfl⟩ : syracuseStep 2664029 = 999011) (by norm_num)
theorem B2369117 : Blo 1578487 2369117 := bbase (se 3 (by rfl) ⟨444209, by rfl⟩ : syracuseStep 2369117 = 888419) (by norm_num)
theorem B2737781 : Blo 1578487 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B2369141 : Blo 1578487 2369141 := bbase (se 5 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 2369141 = 222107) (by norm_num)
theorem B3999365 : Blo 1578487 3999365 := bbase (se 4 (by rfl) ⟨374940, by rfl⟩ : syracuseStep 3999365 = 749881) (by norm_num)
theorem B2369165 : Blo 1578487 2369165 := bbase (se 3 (by rfl) ⟨444218, by rfl⟩ : syracuseStep 2369165 = 888437) (by norm_num)
theorem B2369189 : Blo 1578487 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B2369213 : Blo 1578487 2369213 := bbase (se 3 (by rfl) ⟨444227, by rfl⟩ : syracuseStep 2369213 = 888455) (by norm_num)
theorem B2369237 : Blo 1578487 2369237 := bbase (se 7 (by rfl) ⟨27764, by rfl⟩ : syracuseStep 2369237 = 55529) (by norm_num)
theorem B2664157 : Blo 1578487 2664157 := bbase (se 3 (by rfl) ⟨499529, by rfl⟩ : syracuseStep 2664157 = 999059) (by norm_num)
theorem B2369261 : Blo 1578487 2369261 := bbase (se 3 (by rfl) ⟨444236, by rfl⟩ : syracuseStep 2369261 = 888473) (by norm_num)
theorem B2369285 : Blo 1578487 2369285 := bbase (se 4 (by rfl) ⟨222120, by rfl⟩ : syracuseStep 2369285 = 444241) (by norm_num)
theorem B2369309 : Blo 1578487 2369309 := bbase (se 3 (by rfl) ⟨444245, by rfl⟩ : syracuseStep 2369309 = 888491) (by norm_num)
theorem B2664245 : Blo 1578487 2664245 := bbase (se 5 (by rfl) ⟨124886, by rfl⟩ : syracuseStep 2664245 = 249773) (by norm_num)
theorem B2369333 : Blo 1578487 2369333 := bbase (se 5 (by rfl) ⟨111062, by rfl⟩ : syracuseStep 2369333 = 222125) (by norm_num)
theorem B3999557 : Blo 1578487 3999557 := bbase (se 4 (by rfl) ⟨374958, by rfl⟩ : syracuseStep 3999557 = 749917) (by norm_num)
theorem B2369357 : Blo 1578487 2369357 := bbase (se 3 (by rfl) ⟨444254, by rfl⟩ : syracuseStep 2369357 = 888509) (by norm_num)
theorem B11994965 : Blo 1578487 11994965 := bbase (se 9 (by rfl) ⟨35141, by rfl⟩ : syracuseStep 11994965 = 70283) (by norm_num)
theorem B2369381 : Blo 1578487 2369381 := bbase (se 4 (by rfl) ⟨222129, by rfl⟩ : syracuseStep 2369381 = 444259) (by norm_num)
theorem B11700085 : Blo 1578487 11700085 := bbase (se 5 (by rfl) ⟨548441, by rfl⟩ : syracuseStep 11700085 = 1096883) (by norm_num)
theorem B2369405 : Blo 1578487 2369405 := bbase (se 3 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 2369405 = 888527) (by norm_num)
theorem B2369429 : Blo 1578487 2369429 := bbase (se 6 (by rfl) ⟨55533, by rfl⟩ : syracuseStep 2369429 = 111067) (by norm_num)
theorem B2369453 : Blo 1578487 2369453 := bbase (se 3 (by rfl) ⟨444272, by rfl⟩ : syracuseStep 2369453 = 888545) (by norm_num)
theorem B11380661 : Blo 1578487 11380661 := bbase (se 5 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 11380661 = 1066937) (by norm_num)
theorem B2664373 : Blo 1578487 2664373 := bbase (se 5 (by rfl) ⟨124892, by rfl⟩ : syracuseStep 2664373 = 249785) (by norm_num)
theorem B3000253 : Blo 1578487 3000253 := bbase (se 3 (by rfl) ⟨562547, by rfl⟩ : syracuseStep 3000253 = 1125095) (by norm_num)
theorem B2369477 : Blo 1578487 2369477 := bbase (se 4 (by rfl) ⟨222138, by rfl⟩ : syracuseStep 2369477 = 444277) (by norm_num)
theorem B2369501 : Blo 1578487 2369501 := bbase (se 3 (by rfl) ⟨444281, by rfl⟩ : syracuseStep 2369501 = 888563) (by norm_num)
theorem B2369525 : Blo 1578487 2369525 := bbase (se 5 (by rfl) ⟨111071, by rfl⟩ : syracuseStep 2369525 = 222143) (by norm_num)
theorem B2664461 : Blo 1578487 2664461 := bbase (se 3 (by rfl) ⟨499586, by rfl⟩ : syracuseStep 2664461 = 999173) (by norm_num)
theorem B2369549 : Blo 1578487 2369549 := bbase (se 3 (by rfl) ⟨444290, by rfl⟩ : syracuseStep 2369549 = 888581) (by norm_num)
theorem B2369573 : Blo 1578487 2369573 := bbase (se 4 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 2369573 = 444295) (by norm_num)
theorem B2369597 : Blo 1578487 2369597 := bbase (se 3 (by rfl) ⟨444299, by rfl⟩ : syracuseStep 2369597 = 888599) (by norm_num)
theorem B4499525 : Blo 1578487 4499525 := bbase (se 4 (by rfl) ⟨421830, by rfl⟩ : syracuseStep 4499525 = 843661) (by norm_num)
theorem B3000397 : Blo 1578487 3000397 := bbase (se 3 (by rfl) ⟨562574, by rfl⟩ : syracuseStep 3000397 = 1125149) (by norm_num)
theorem B2369621 : Blo 1578487 2369621 := bbase (se 8 (by rfl) ⟨13884, by rfl⟩ : syracuseStep 2369621 = 27769) (by norm_num)
theorem B3041381 : Blo 1578487 3041381 := bbase (se 4 (by rfl) ⟨285129, by rfl⟩ : syracuseStep 3041381 = 570259) (by norm_num)
theorem B2369645 : Blo 1578487 2369645 := bbase (se 3 (by rfl) ⟨444308, by rfl⟩ : syracuseStep 2369645 = 888617) (by norm_num)
theorem B2369669 : Blo 1578487 2369669 := bbase (se 4 (by rfl) ⟨222156, by rfl⟩ : syracuseStep 2369669 = 444313) (by norm_num)
theorem B2664589 : Blo 1578487 2664589 := bbase (se 3 (by rfl) ⟨499610, by rfl⟩ : syracuseStep 2664589 = 999221) (by norm_num)
theorem B2369693 : Blo 1578487 2369693 := bbase (se 3 (by rfl) ⟨444317, by rfl⟩ : syracuseStep 2369693 = 888635) (by norm_num)
theorem B3999901 : Blo 1578487 3999901 := bbase (se 3 (by rfl) ⟨749981, by rfl⟩ : syracuseStep 3999901 = 1499963) (by norm_num)
theorem B2369717 : Blo 1578487 2369717 := bbase (se 5 (by rfl) ⟨111080, by rfl⟩ : syracuseStep 2369717 = 222161) (by norm_num)
theorem B2844877 : Blo 1578487 2844877 := bbase (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) (by norm_num)
theorem B2369741 : Blo 1578487 2369741 := bbase (se 3 (by rfl) ⟨444326, by rfl⟩ : syracuseStep 2369741 = 888653) (by norm_num)
theorem B5998805 : Blo 1578487 5998805 := bbase (se 7 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 5998805 = 140597) (by norm_num)
theorem B2664677 : Blo 1578487 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B2369765 : Blo 1578487 2369765 := bbase (se 4 (by rfl) ⟨222165, by rfl⟩ : syracuseStep 2369765 = 444331) (by norm_num)
theorem B11987189 : Blo 1578487 11987189 := bbase (se 5 (by rfl) ⟨561899, by rfl⟩ : syracuseStep 11987189 = 1123799) (by norm_num)
theorem B2369789 : Blo 1578487 2369789 := bbase (se 3 (by rfl) ⟨444335, by rfl⟩ : syracuseStep 2369789 = 888671) (by norm_num)
theorem B4000013 : Blo 1578487 4000013 := bbase (se 3 (by rfl) ⟨750002, by rfl⟩ : syracuseStep 4000013 = 1500005) (by norm_num)
theorem B2369813 : Blo 1578487 2369813 := bbase (se 6 (by rfl) ⟨55542, by rfl⟩ : syracuseStep 2369813 = 111085) (by norm_num)
theorem B3795245 : Blo 1578487 3795245 := bbase (se 3 (by rfl) ⟨711608, by rfl⟩ : syracuseStep 3795245 = 1423217) (by norm_num)
theorem B2369837 : Blo 1578487 2369837 := bbase (se 3 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 2369837 = 888689) (by norm_num)
theorem B2369861 : Blo 1578487 2369861 := bbase (se 4 (by rfl) ⟨222174, by rfl⟩ : syracuseStep 2369861 = 444349) (by norm_num)
theorem B2369885 : Blo 1578487 2369885 := bbase (se 3 (by rfl) ⟨444353, by rfl⟩ : syracuseStep 2369885 = 888707) (by norm_num)
theorem B2664805 : Blo 1578487 2664805 := bbase (se 4 (by rfl) ⟨249825, by rfl⟩ : syracuseStep 2664805 = 499651) (by norm_num)
theorem B2369909 : Blo 1578487 2369909 := bbase (se 5 (by rfl) ⟨111089, by rfl⟩ : syracuseStep 2369909 = 222179) (by norm_num)
theorem B2369933 : Blo 1578487 2369933 := bbase (se 3 (by rfl) ⟨444362, by rfl⟩ : syracuseStep 2369933 = 888725) (by norm_num)
theorem B2369957 : Blo 1578487 2369957 := bbase (se 4 (by rfl) ⟨222183, by rfl⟩ : syracuseStep 2369957 = 444367) (by norm_num)
theorem B2664893 : Blo 1578487 2664893 := bbase (se 3 (by rfl) ⟨499667, by rfl⟩ : syracuseStep 2664893 = 999335) (by norm_num)
theorem B2369981 : Blo 1578487 2369981 := bbase (se 3 (by rfl) ⟨444371, by rfl⟩ : syracuseStep 2369981 = 888743) (by norm_num)
theorem B4000205 : Blo 1578487 4000205 := bbase (se 3 (by rfl) ⟨750038, by rfl⟩ : syracuseStep 4000205 = 1500077) (by norm_num)
theorem B2370005 : Blo 1578487 2370005 := bbase (se 7 (by rfl) ⟨27773, by rfl⟩ : syracuseStep 2370005 = 55547) (by norm_num)
theorem B2370029 : Blo 1578487 2370029 := bbase (se 3 (by rfl) ⟨444380, by rfl⟩ : syracuseStep 2370029 = 888761) (by norm_num)
theorem B5999093 : Blo 1578487 5999093 := bbase (se 5 (by rfl) ⟨281207, by rfl⟩ : syracuseStep 5999093 = 562415) (by norm_num)
theorem B2370053 : Blo 1578487 2370053 := bbase (se 4 (by rfl) ⟨222192, by rfl⟩ : syracuseStep 2370053 = 444385) (by norm_num)
theorem B2370077 : Blo 1578487 2370077 := bbase (se 3 (by rfl) ⟨444389, by rfl⟩ : syracuseStep 2370077 = 888779) (by norm_num)
theorem B2370101 : Blo 1578487 2370101 := bbase (se 5 (by rfl) ⟨111098, by rfl⟩ : syracuseStep 2370101 = 222197) (by norm_num)
theorem B2665021 : Blo 1578487 2665021 := bbase (se 3 (by rfl) ⟨499691, by rfl⟩ : syracuseStep 2665021 = 999383) (by norm_num)
theorem B2370125 : Blo 1578487 2370125 := bbase (se 3 (by rfl) ⟨444398, by rfl⟩ : syracuseStep 2370125 = 888797) (by norm_num)
theorem B1600081 : Blo 1578487 1600081 := bbase (se 2 (by rfl) ⟨600030, by rfl⟩ : syracuseStep 1600081 = 1200061) (by norm_num)
theorem B2370149 : Blo 1578487 2370149 := bbase (se 4 (by rfl) ⟨222201, by rfl⟩ : syracuseStep 2370149 = 444403) (by norm_num)
theorem B5327477 : Blo 1578487 5327477 := bbase (se 5 (by rfl) ⟨249725, by rfl⟩ : syracuseStep 5327477 = 499451) (by norm_num)
theorem B2845309 : Blo 1578487 2845309 := bbase (se 3 (by rfl) ⟨533495, by rfl⟩ : syracuseStep 2845309 = 1066991) (by norm_num)
theorem B2370173 : Blo 1578487 2370173 := bbase (se 3 (by rfl) ⟨444407, by rfl⟩ : syracuseStep 2370173 = 888815) (by norm_num)
theorem B2665109 : Blo 1578487 2665109 := bbase (se 6 (by rfl) ⟨62463, by rfl⟩ : syracuseStep 2665109 = 124927) (by norm_num)
theorem B7998101 : Blo 1578487 7998101 := bbase (se 6 (by rfl) ⟨187455, by rfl⟩ : syracuseStep 7998101 = 374911) (by norm_num)
theorem B2370197 : Blo 1578487 2370197 := bbase (se 6 (by rfl) ⟨55551, by rfl⟩ : syracuseStep 2370197 = 111103) (by norm_num)
theorem B2370221 : Blo 1578487 2370221 := bbase (se 3 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 2370221 = 888833) (by norm_num)
theorem B2370245 : Blo 1578487 2370245 := bbase (se 4 (by rfl) ⟨222210, by rfl⟩ : syracuseStep 2370245 = 444421) (by norm_num)
theorem B2370269 : Blo 1578487 2370269 := bbase (se 3 (by rfl) ⟨444425, by rfl⟩ : syracuseStep 2370269 = 888851) (by norm_num)
theorem B2370293 : Blo 1578487 2370293 := bbase (se 5 (by rfl) ⟨111107, by rfl⟩ : syracuseStep 2370293 = 222215) (by norm_num)
theorem B2370317 : Blo 1578487 2370317 := bbase (se 3 (by rfl) ⟨444434, by rfl⟩ : syracuseStep 2370317 = 888869) (by norm_num)
theorem B2665237 : Blo 1578487 2665237 := bbase (se 6 (by rfl) ⟨62466, by rfl⟩ : syracuseStep 2665237 = 124933) (by norm_num)
theorem B2370341 : Blo 1578487 2370341 := bbase (se 4 (by rfl) ⟨222219, by rfl⟩ : syracuseStep 2370341 = 444439) (by norm_num)
theorem B4000549 : Blo 1578487 4000549 := bbase (se 4 (by rfl) ⟨375051, by rfl⟩ : syracuseStep 4000549 = 750103) (by norm_num)
theorem B2370365 : Blo 1578487 2370365 := bbase (se 3 (by rfl) ⟨444443, by rfl⟩ : syracuseStep 2370365 = 888887) (by norm_num)
theorem B2370389 : Blo 1578487 2370389 := bbase (se 9 (by rfl) ⟨6944, by rfl⟩ : syracuseStep 2370389 = 13889) (by norm_num)
theorem B2665325 : Blo 1578487 2665325 := bbase (se 3 (by rfl) ⟨499748, by rfl⟩ : syracuseStep 2665325 = 999497) (by norm_num)
theorem B2370413 : Blo 1578487 2370413 := bbase (se 3 (by rfl) ⟨444452, by rfl⟩ : syracuseStep 2370413 = 888905) (by norm_num)
theorem B13495157 : Blo 1578487 13495157 := bbase (se 5 (by rfl) ⟨632585, by rfl⟩ : syracuseStep 13495157 = 1265171) (by norm_num)
theorem B4270981 : Blo 1578487 4270981 := bbase (se 4 (by rfl) ⟨400404, by rfl⟩ : syracuseStep 4270981 = 800809) (by norm_num)
theorem B2370437 : Blo 1578487 2370437 := bbase (se 4 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 2370437 = 444457) (by norm_num)
theorem B2370461 : Blo 1578487 2370461 := bbase (se 3 (by rfl) ⟨444461, by rfl⟩ : syracuseStep 2370461 = 888923) (by norm_num)
theorem B2370485 : Blo 1578487 2370485 := bbase (se 5 (by rfl) ⟨111116, by rfl⟩ : syracuseStep 2370485 = 222233) (by norm_num)
theorem B2370509 : Blo 1578487 2370509 := bbase (se 3 (by rfl) ⟨444470, by rfl⟩ : syracuseStep 2370509 = 888941) (by norm_num)
theorem B40455125 : Blo 1578487 40455125 := bbase (se 7 (by rfl) ⟨474083, by rfl⟩ : syracuseStep 40455125 = 948167) (by norm_num)
theorem B2370533 : Blo 1578487 2370533 := bbase (se 4 (by rfl) ⟨222237, by rfl⟩ : syracuseStep 2370533 = 444475) (by norm_num)
theorem B2665453 : Blo 1578487 2665453 := bbase (se 3 (by rfl) ⟨499772, by rfl⟩ : syracuseStep 2665453 = 999545) (by norm_num)
theorem B13487093 : Blo 1578487 13487093 := bbase (se 5 (by rfl) ⟨632207, by rfl⟩ : syracuseStep 13487093 = 1264415) (by norm_num)
theorem B2370557 : Blo 1578487 2370557 := bbase (se 3 (by rfl) ⟨444479, by rfl⟩ : syracuseStep 2370557 = 888959) (by norm_num)
theorem B2370581 : Blo 1578487 2370581 := bbase (se 6 (by rfl) ⟨55560, by rfl⟩ : syracuseStep 2370581 = 111121) (by norm_num)
theorem B5327909 : Blo 1578487 5327909 := bbase (se 4 (by rfl) ⟨499491, by rfl⟩ : syracuseStep 5327909 = 998983) (by norm_num)
theorem B3124261 : Blo 1578487 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B2370605 : Blo 1578487 2370605 := bbase (se 3 (by rfl) ⟨444488, by rfl⟩ : syracuseStep 2370605 = 888977) (by norm_num)
theorem B2665541 : Blo 1578487 2665541 := bbase (se 4 (by rfl) ⟨249894, by rfl⟩ : syracuseStep 2665541 = 499789) (by norm_num)
theorem B2370629 : Blo 1578487 2370629 := bbase (se 4 (by rfl) ⟨222246, by rfl⟩ : syracuseStep 2370629 = 444493) (by norm_num)
theorem B2370653 : Blo 1578487 2370653 := bbase (se 3 (by rfl) ⟨444497, by rfl⟩ : syracuseStep 2370653 = 888995) (by norm_num)
theorem B7203941 : Blo 1578487 7203941 := bbase (se 4 (by rfl) ⟨675369, by rfl⟩ : syracuseStep 7203941 = 1350739) (by norm_num)
theorem B2370677 : Blo 1578487 2370677 := bbase (se 5 (by rfl) ⟨111125, by rfl⟩ : syracuseStep 2370677 = 222251) (by norm_num)
theorem B1600645 : Blo 1578487 1600645 := bbase (se 4 (by rfl) ⟨150060, by rfl⟩ : syracuseStep 1600645 = 300121) (by norm_num)
theorem B2845829 : Blo 1578487 2845829 := bbase (se 4 (by rfl) ⟨266796, by rfl⟩ : syracuseStep 2845829 = 533593) (by norm_num)
theorem B2370701 : Blo 1578487 2370701 := bbase (se 3 (by rfl) ⟨444506, by rfl⟩ : syracuseStep 2370701 = 889013) (by norm_num)
theorem B2370725 : Blo 1578487 2370725 := bbase (se 4 (by rfl) ⟨222255, by rfl⟩ : syracuseStep 2370725 = 444511) (by norm_num)
theorem B2665669 : Blo 1578487 2665669 := bbase (se 4 (by rfl) ⟨249906, by rfl⟩ : syracuseStep 2665669 = 499813) (by norm_num)
theorem B4050157 : Blo 1578487 4050157 := bbase (se 3 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 4050157 = 1518809) (by norm_num)
theorem B2247917 : Blo 1578487 2247917 := bbase (se 3 (by rfl) ⟨421484, by rfl⟩ : syracuseStep 2247917 = 842969) (by norm_num)
theorem B3796205 : Blo 1578487 3796205 := bbase (se 3 (by rfl) ⟨711788, by rfl⟩ : syracuseStep 3796205 = 1423577) (by norm_num)
theorem B2665757 : Blo 1578487 2665757 := bbase (se 3 (by rfl) ⟨499829, by rfl⟩ : syracuseStep 2665757 = 999659) (by norm_num)
theorem B8998229 : Blo 1578487 8998229 := bbase (se 11 (by rfl) ⟨6590, by rfl⟩ : syracuseStep 8998229 = 13181) (by norm_num)
theorem B4803941 : Blo 1578487 4803941 := bbase (se 4 (by rfl) ⟨450369, by rfl⟩ : syracuseStep 4803941 = 900739) (by norm_num)
theorem B2665885 : Blo 1578487 2665885 := bbase (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) (by norm_num)
theorem B2846117 : Blo 1578487 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B5328341 : Blo 1578487 5328341 := bbase (se 7 (by rfl) ⟨62441, by rfl⟩ : syracuseStep 5328341 = 124883) (by norm_num)
theorem B2665973 : Blo 1578487 2665973 := bbase (se 5 (by rfl) ⟨124967, by rfl⟩ : syracuseStep 2665973 = 249935) (by norm_num)
theorem B124833365 : Blo 1578487 124833365 := bbase (se 8 (by rfl) ⟨731445, by rfl⟩ : syracuseStep 124833365 = 1462891) (by norm_num)
theorem B2666101 : Blo 1578487 2666101 := bbase (se 5 (by rfl) ⟨124973, by rfl⟩ : syracuseStep 2666101 = 249947) (by norm_num)
theorem B6000277 : Blo 1578487 6000277 := bbase (se 6 (by rfl) ⟨140631, by rfl⟩ : syracuseStep 6000277 = 281263) (by norm_num)
theorem B2666189 : Blo 1578487 2666189 := bbase (se 3 (by rfl) ⟨499910, by rfl⟩ : syracuseStep 2666189 = 999821) (by norm_num)
theorem B2666317 : Blo 1578487 2666317 := bbase (se 3 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 2666317 = 999869) (by norm_num)
theorem B2846549 : Blo 1578487 2846549 := bbase (se 9 (by rfl) ⟨8339, by rfl⟩ : syracuseStep 2846549 = 16679) (by norm_num)
theorem B5328773 : Blo 1578487 5328773 := bbase (se 4 (by rfl) ⟨499572, by rfl⟩ : syracuseStep 5328773 = 999145) (by norm_num)
theorem B2666405 : Blo 1578487 2666405 := bbase (se 4 (by rfl) ⟨249975, by rfl⟩ : syracuseStep 2666405 = 499951) (by norm_num)
theorem B7999397 : Blo 1578487 7999397 := bbase (se 4 (by rfl) ⟨749943, by rfl⟩ : syracuseStep 7999397 = 1499887) (by norm_num)
theorem B1896373 : Blo 1578487 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B6000581 : Blo 1578487 6000581 := bbase (se 4 (by rfl) ⟨562554, by rfl⟩ : syracuseStep 6000581 = 1125109) (by norm_num)
theorem B2248669 : Blo 1578487 2248669 := bbase (se 3 (by rfl) ⟨421625, by rfl⟩ : syracuseStep 2248669 = 843251) (by norm_num)
theorem B2846693 : Blo 1578487 2846693 := bbase (se 4 (by rfl) ⟨266877, by rfl⟩ : syracuseStep 2846693 = 533755) (by norm_num)
theorem B2666533 : Blo 1578487 2666533 := bbase (se 4 (by rfl) ⟨249987, by rfl⟩ : syracuseStep 2666533 = 499975) (by norm_num)
theorem B1896565 : Blo 1578487 1896565 := bbase (se 5 (by rfl) ⟨88901, by rfl⟩ : syracuseStep 1896565 = 177803) (by norm_num)
theorem B2666621 : Blo 1578487 2666621 := bbase (se 3 (by rfl) ⟨499991, by rfl⟩ : syracuseStep 2666621 = 999983) (by norm_num)
theorem B25972949 : Blo 1578487 25972949 := bbase (se 7 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 25972949 = 608741) (by norm_num)
theorem B4329701 : Blo 1578487 4329701 := bbase (se 4 (by rfl) ⟨405909, by rfl⟩ : syracuseStep 4329701 = 811819) (by norm_num)
theorem B2666749 : Blo 1578487 2666749 := bbase (se 3 (by rfl) ⟨500015, by rfl⟩ : syracuseStep 2666749 = 1000031) (by norm_num)
theorem B7590181 : Blo 1578487 7590181 := bbase (se 4 (by rfl) ⟨711579, by rfl⟩ : syracuseStep 7590181 = 1423159) (by norm_num)
theorem B5329205 : Blo 1578487 5329205 := bbase (se 5 (by rfl) ⟨249806, by rfl⟩ : syracuseStep 5329205 = 499613) (by norm_num)
theorem B7991621 : Blo 1578487 7991621 := bbase (se 4 (by rfl) ⟨749214, by rfl⟩ : syracuseStep 7991621 = 1498429) (by norm_num)
theorem B2666837 : Blo 1578487 2666837 := bbase (se 10 (by rfl) ⟨3906, by rfl⟩ : syracuseStep 2666837 = 7813) (by norm_num)
theorem B3551597 : Blo 1578487 3551597 := bbase (se 3 (by rfl) ⟨665924, by rfl⟩ : syracuseStep 3551597 = 1331849) (by norm_num)
theorem B6746485 : Blo 1578487 6746485 := bbase (se 5 (by rfl) ⟨316241, by rfl⟩ : syracuseStep 6746485 = 632483) (by norm_num)
theorem B3420581 : Blo 1578487 3420581 := bbase (se 4 (by rfl) ⟨320679, by rfl⟩ : syracuseStep 3420581 = 641359) (by norm_num)
theorem B3551669 : Blo 1578487 3551669 := bbase (se 5 (by rfl) ⟨166484, by rfl⟩ : syracuseStep 3551669 = 332969) (by norm_num)
theorem B2134453 : Blo 1578487 2134453 := bbase (se 5 (by rfl) ⟨100052, by rfl⟩ : syracuseStep 2134453 = 200105) (by norm_num)
theorem B2666965 : Blo 1578487 2666965 := bbase (se 7 (by rfl) ⟨31253, by rfl⟩ : syracuseStep 2666965 = 62507) (by norm_num)
theorem B3551741 : Blo 1578487 3551741 := bbase (se 3 (by rfl) ⟨665951, by rfl⟩ : syracuseStep 3551741 = 1331903) (by norm_num)
theorem B4051469 : Blo 1578487 4051469 := bbase (se 3 (by rfl) ⟨759650, by rfl⟩ : syracuseStep 4051469 = 1519301) (by norm_num)
theorem B2667053 : Blo 1578487 2667053 := bbase (se 3 (by rfl) ⟨500072, by rfl⟩ : syracuseStep 2667053 = 1000145) (by norm_num)
theorem B3600949 : Blo 1578487 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B3551813 : Blo 1578487 3551813 := bbase (se 4 (by rfl) ⟨332982, by rfl⟩ : syracuseStep 3551813 = 665965) (by norm_num)
theorem B3551885 : Blo 1578487 3551885 := bbase (se 3 (by rfl) ⟨665978, by rfl⟩ : syracuseStep 3551885 = 1331957) (by norm_num)
theorem B6402725 : Blo 1578487 6402725 := bbase (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) (by norm_num)
theorem B2134717 : Blo 1578487 2134717 := bbase (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) (by norm_num)
theorem B3551957 : Blo 1578487 3551957 := bbase (se 7 (by rfl) ⟨41624, by rfl⟩ : syracuseStep 3551957 = 83249) (by norm_num)
theorem B5329637 : Blo 1578487 5329637 := bbase (se 4 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 5329637 = 999307) (by norm_num)
theorem B11383541 : Blo 1578487 11383541 := bbase (se 5 (by rfl) ⟨533603, by rfl⟩ : syracuseStep 11383541 = 1067207) (by norm_num)
theorem B2249461 : Blo 1578487 2249461 := bbase (se 5 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 2249461 = 210887) (by norm_num)
theorem B6583061 : Blo 1578487 6583061 := bbase (se 6 (by rfl) ⟨154290, by rfl⟩ : syracuseStep 6583061 = 308581) (by norm_num)
theorem B3552029 : Blo 1578487 3552029 := bbase (se 3 (by rfl) ⟨666005, by rfl⟩ : syracuseStep 3552029 = 1332011) (by norm_num)
theorem B3552101 : Blo 1578487 3552101 := bbase (se 4 (by rfl) ⟨333009, by rfl⟩ : syracuseStep 3552101 = 666019) (by norm_num)
theorem B3552173 : Blo 1578487 3552173 := bbase (se 3 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 3552173 = 1332065) (by norm_num)
theorem B3372005 : Blo 1578487 3372005 := bbase (se 4 (by rfl) ⟨316125, by rfl⟩ : syracuseStep 3372005 = 632251) (by norm_num)
theorem B1897445 : Blo 1578487 1897445 := bbase (se 4 (by rfl) ⟨177885, by rfl⟩ : syracuseStep 1897445 = 355771) (by norm_num)
theorem B2847725 : Blo 1578487 2847725 := bbase (se 3 (by rfl) ⟨533948, by rfl⟩ : syracuseStep 2847725 = 1067897) (by norm_num)
theorem B3552245 : Blo 1578487 3552245 := bbase (se 5 (by rfl) ⟨166511, by rfl⟩ : syracuseStep 3552245 = 333023) (by norm_num)
theorem B3552317 : Blo 1578487 3552317 := bbase (se 3 (by rfl) ⟨666059, by rfl⟩ : syracuseStep 3552317 = 1332119) (by norm_num)
theorem B2249797 : Blo 1578487 2249797 := bbase (se 4 (by rfl) ⟨210918, by rfl⟩ : syracuseStep 2249797 = 421837) (by norm_num)
theorem B4052045 : Blo 1578487 4052045 := bbase (se 3 (by rfl) ⟨759758, by rfl⟩ : syracuseStep 4052045 = 1519517) (by norm_num)
theorem B1709149 : Blo 1578487 1709149 := bbase (se 3 (by rfl) ⟨320465, by rfl⟩ : syracuseStep 1709149 = 640931) (by norm_num)
theorem B5059685 : Blo 1578487 5059685 := bbase (se 4 (by rfl) ⟨474345, by rfl⟩ : syracuseStep 5059685 = 948691) (by norm_num)
theorem B3372149 : Blo 1578487 3372149 := bbase (se 5 (by rfl) ⟨158069, by rfl⟩ : syracuseStep 3372149 = 316139) (by norm_num)
theorem B3552389 : Blo 1578487 3552389 := bbase (se 4 (by rfl) ⟨333036, by rfl⟩ : syracuseStep 3552389 = 666073) (by norm_num)
theorem B5330069 : Blo 1578487 5330069 := bbase (se 6 (by rfl) ⟨124923, by rfl⟩ : syracuseStep 5330069 = 249847) (by norm_num)
theorem B5690533 : Blo 1578487 5690533 := bbase (se 4 (by rfl) ⟨533487, by rfl⟩ : syracuseStep 5690533 = 1066975) (by norm_num)
theorem B8000693 : Blo 1578487 8000693 := bbase (se 5 (by rfl) ⟨375032, by rfl⟩ : syracuseStep 8000693 = 750065) (by norm_num)
theorem B3552461 : Blo 1578487 3552461 := bbase (se 3 (by rfl) ⟨666086, by rfl⟩ : syracuseStep 3552461 = 1332173) (by norm_num)
theorem B3552533 : Blo 1578487 3552533 := bbase (se 6 (by rfl) ⟨83262, by rfl⟩ : syracuseStep 3552533 = 166525) (by norm_num)
theorem B2250013 : Blo 1578487 2250013 := bbase (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) (by norm_num)
theorem B3552605 : Blo 1578487 3552605 := bbase (se 3 (by rfl) ⟨666113, by rfl⟩ : syracuseStep 3552605 = 1332227) (by norm_num)
theorem B3552677 : Blo 1578487 3552677 := bbase (se 4 (by rfl) ⟨333063, by rfl⟩ : syracuseStep 3552677 = 666127) (by norm_num)
theorem B5690837 : Blo 1578487 5690837 := bbase (se 7 (by rfl) ⟨66689, by rfl⟩ : syracuseStep 5690837 = 133379) (by norm_num)
theorem B3372509 : Blo 1578487 3372509 := bbase (se 3 (by rfl) ⟨632345, by rfl⟩ : syracuseStep 3372509 = 1264691) (by norm_num)
theorem B1897949 : Blo 1578487 1897949 := bbase (se 3 (by rfl) ⟨355865, by rfl⟩ : syracuseStep 1897949 = 711731) (by norm_num)
theorem B3552749 : Blo 1578487 3552749 := bbase (se 3 (by rfl) ⟨666140, by rfl⟩ : syracuseStep 3552749 = 1332281) (by norm_num)
theorem B1897997 : Blo 1578487 1897997 := bbase (se 3 (by rfl) ⟨355874, by rfl⟩ : syracuseStep 1897997 = 711749) (by norm_num)
theorem B3552821 : Blo 1578487 3552821 := bbase (se 5 (by rfl) ⟨166538, by rfl⟩ : syracuseStep 3552821 = 333077) (by norm_num)
theorem B5330501 : Blo 1578487 5330501 := bbase (se 4 (by rfl) ⟨499734, by rfl⟩ : syracuseStep 5330501 = 999469) (by norm_num)
theorem B7992917 : Blo 1578487 7992917 := bbase (se 8 (by rfl) ⟨46833, by rfl⟩ : syracuseStep 7992917 = 93667) (by norm_num)
theorem B3552893 : Blo 1578487 3552893 := bbase (se 3 (by rfl) ⟨666167, by rfl⟩ : syracuseStep 3552893 = 1332335) (by norm_num)
theorem B5404325 : Blo 1578487 5404325 := bbase (se 4 (by rfl) ⟨506655, by rfl⟩ : syracuseStep 5404325 = 1013311) (by norm_num)
theorem B3552965 : Blo 1578487 3552965 := bbase (se 4 (by rfl) ⟨333090, by rfl⟩ : syracuseStep 3552965 = 666181) (by norm_num)
theorem B3553037 : Blo 1578487 3553037 := bbase (se 3 (by rfl) ⟨666194, by rfl⟩ : syracuseStep 3553037 = 1332389) (by norm_num)
theorem B1898257 : Blo 1578487 1898257 := bbase (se 2 (by rfl) ⟨711846, by rfl⟩ : syracuseStep 1898257 = 1423693) (by norm_num)
theorem B3553109 : Blo 1578487 3553109 := bbase (se 9 (by rfl) ⟨10409, by rfl⟩ : syracuseStep 3553109 = 20819) (by norm_num)
theorem B3553181 : Blo 1578487 3553181 := bbase (se 3 (by rfl) ⟨666221, by rfl⟩ : syracuseStep 3553181 = 1332443) (by norm_num)
theorem B4495333 : Blo 1578487 4495333 := bbase (se 4 (by rfl) ⟨421437, by rfl⟩ : syracuseStep 4495333 = 842875) (by norm_num)
theorem B3553253 : Blo 1578487 3553253 := bbase (se 4 (by rfl) ⟨333117, by rfl⟩ : syracuseStep 3553253 = 666235) (by norm_num)
theorem B5330933 : Blo 1578487 5330933 := bbase (se 5 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 5330933 = 499775) (by norm_num)
theorem B1824781 : Blo 1578487 1824781 := bbase (se 3 (by rfl) ⟨342146, by rfl⟩ : syracuseStep 1824781 = 684293) (by norm_num)
theorem B3995669 : Blo 1578487 3995669 := bbase (se 6 (by rfl) ⟨93648, by rfl⟩ : syracuseStep 3995669 = 187297) (by norm_num)
theorem B1898521 : Blo 1578487 1898521 := bbase (se 2 (by rfl) ⟨711945, by rfl⟩ : syracuseStep 1898521 = 1423891) (by norm_num)
theorem B2529317 : Blo 1578487 2529317 := bbase (se 4 (by rfl) ⟨237123, by rfl⟩ : syracuseStep 2529317 = 474247) (by norm_num)
theorem B3553325 : Blo 1578487 3553325 := bbase (se 3 (by rfl) ⟨666248, by rfl⟩ : syracuseStep 3553325 = 1332497) (by norm_num)
theorem B8534069 : Blo 1578487 8534069 := bbase (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) (by norm_num)
theorem B8992853 : Blo 1578487 8992853 := bbase (se 8 (by rfl) ⟨52692, by rfl⟩ : syracuseStep 8992853 = 105385) (by norm_num)
theorem B3553397 : Blo 1578487 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B4495493 : Blo 1578487 4495493 := bbase (se 4 (by rfl) ⟨421452, by rfl⟩ : syracuseStep 4495493 = 842905) (by norm_num)
theorem B1898641 : Blo 1578487 1898641 := bbase (se 2 (by rfl) ⟨711990, by rfl⟩ : syracuseStep 1898641 = 1423981) (by norm_num)
theorem B1824925 : Blo 1578487 1824925 := bbase (se 3 (by rfl) ⟨342173, by rfl⟩ : syracuseStep 1824925 = 684347) (by norm_num)
theorem B3553469 : Blo 1578487 3553469 := bbase (se 3 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 3553469 = 1332551) (by norm_num)
theorem B1775821 : Blo 1578487 1775821 := bbase (se 3 (by rfl) ⟨332966, by rfl⟩ : syracuseStep 1775821 = 665933) (by norm_num)
theorem B1685729 : Blo 1578487 1685729 := bbase (se 2 (by rfl) ⟨632148, by rfl⟩ : syracuseStep 1685729 = 1264297) (by norm_num)
theorem B1775857 : Blo 1578487 1775857 := bbase (se 2 (by rfl) ⟨665946, by rfl⟩ : syracuseStep 1775857 = 1331893) (by norm_num)
theorem B3553541 : Blo 1578487 3553541 := bbase (se 4 (by rfl) ⟨333144, by rfl⟩ : syracuseStep 3553541 = 666289) (by norm_num)
theorem B1775893 : Blo 1578487 1775893 := bbase (se 6 (by rfl) ⟨41622, by rfl⟩ : syracuseStep 1775893 = 83245) (by norm_num)
theorem B1775929 : Blo 1578487 1775929 := bbase (se 2 (by rfl) ⟨665973, by rfl⟩ : syracuseStep 1775929 = 1331947) (by norm_num)
theorem B3553613 : Blo 1578487 3553613 := bbase (se 3 (by rfl) ⟨666302, by rfl⟩ : syracuseStep 3553613 = 1332605) (by norm_num)
theorem B3602765 : Blo 1578487 3602765 := bbase (se 3 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 3602765 = 1351037) (by norm_num)
theorem B3373397 : Blo 1578487 3373397 := bbase (se 10 (by rfl) ⟨4941, by rfl⟩ : syracuseStep 3373397 = 9883) (by norm_num)
theorem B1775965 : Blo 1578487 1775965 := bbase (se 3 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 1775965 = 665987) (by norm_num)
theorem B3996013 : Blo 1578487 3996013 := bbase (se 3 (by rfl) ⟨749252, by rfl⟩ : syracuseStep 3996013 = 1498505) (by norm_num)
theorem B4495733 : Blo 1578487 4495733 := bbase (se 5 (by rfl) ⟨210737, by rfl⟩ : syracuseStep 4495733 = 421475) (by norm_num)
theorem B5060981 : Blo 1578487 5060981 := bbase (se 5 (by rfl) ⟨237233, by rfl⟩ : syracuseStep 5060981 = 474467) (by norm_num)
theorem B1776001 : Blo 1578487 1776001 := bbase (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) (by norm_num)
theorem B3553685 : Blo 1578487 3553685 := bbase (se 6 (by rfl) ⟨83289, by rfl⟩ : syracuseStep 3553685 = 166579) (by norm_num)
theorem B1776037 : Blo 1578487 1776037 := bbase (se 4 (by rfl) ⟨166503, by rfl⟩ : syracuseStep 1776037 = 333007) (by norm_num)
theorem B5994917 : Blo 1578487 5994917 := bbase (se 4 (by rfl) ⟨562023, by rfl⟩ : syracuseStep 5994917 = 1124047) (by norm_num)
theorem B5331365 : Blo 1578487 5331365 := bbase (se 4 (by rfl) ⟨499815, by rfl⟩ : syracuseStep 5331365 = 999631) (by norm_num)
theorem B2996669 : Blo 1578487 2996669 := bbase (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) (by norm_num)
theorem B1776073 : Blo 1578487 1776073 := bbase (se 2 (by rfl) ⟨666027, by rfl⟩ : syracuseStep 1776073 = 1332055) (by norm_num)
theorem B3996125 : Blo 1578487 3996125 := bbase (se 3 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 3996125 = 1498547) (by norm_num)
theorem B1685981 : Blo 1578487 1685981 := bbase (se 3 (by rfl) ⟨316121, by rfl⟩ : syracuseStep 1685981 = 632243) (by norm_num)
theorem B3553757 : Blo 1578487 3553757 := bbase (se 3 (by rfl) ⟨666329, by rfl⟩ : syracuseStep 3553757 = 1332659) (by norm_num)
theorem B1776109 : Blo 1578487 1776109 := bbase (se 3 (by rfl) ⟨333020, by rfl⟩ : syracuseStep 1776109 = 666041) (by norm_num)
theorem B1776145 : Blo 1578487 1776145 := bbase (se 2 (by rfl) ⟨666054, by rfl⟩ : syracuseStep 1776145 = 1332109) (by norm_num)
theorem B3553829 : Blo 1578487 3553829 := bbase (se 4 (by rfl) ⟨333171, by rfl⟩ : syracuseStep 3553829 = 666343) (by norm_num)
theorem B4495925 : Blo 1578487 4495925 := bbase (se 5 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 4495925 = 421493) (by norm_num)
theorem B1776181 : Blo 1578487 1776181 := bbase (se 5 (by rfl) ⟨83258, by rfl⟩ : syracuseStep 1776181 = 166517) (by norm_num)
theorem B3201589 : Blo 1578487 3201589 := bbase (se 5 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 3201589 = 300149) (by norm_num)
theorem B10123829 : Blo 1578487 10123829 := bbase (se 5 (by rfl) ⟨474554, by rfl⟩ : syracuseStep 10123829 = 949109) (by norm_num)
theorem B2996813 : Blo 1578487 2996813 := bbase (se 3 (by rfl) ⟨561902, by rfl⟩ : syracuseStep 2996813 = 1123805) (by norm_num)
theorem B3373645 : Blo 1578487 3373645 := bbase (se 3 (by rfl) ⟨632558, by rfl⟩ : syracuseStep 3373645 = 1265117) (by norm_num)
theorem B1776217 : Blo 1578487 1776217 := bbase (se 2 (by rfl) ⟨666081, by rfl⟩ : syracuseStep 1776217 = 1332163) (by norm_num)
theorem B3553901 : Blo 1578487 3553901 := bbase (se 3 (by rfl) ⟨666356, by rfl⟩ : syracuseStep 3553901 = 1332713) (by norm_num)
theorem B1776253 : Blo 1578487 1776253 := bbase (se 3 (by rfl) ⟨333047, by rfl⟩ : syracuseStep 1776253 = 666095) (by norm_num)
theorem B3996317 : Blo 1578487 3996317 := bbase (se 3 (by rfl) ⟨749309, by rfl⟩ : syracuseStep 3996317 = 1498619) (by norm_num)
theorem B2054813 : Blo 1578487 2054813 := bbase (se 3 (by rfl) ⟨385277, by rfl⟩ : syracuseStep 2054813 = 770555) (by norm_num)
theorem B1776289 : Blo 1578487 1776289 := bbase (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) (by norm_num)
theorem B3553973 : Blo 1578487 3553973 := bbase (se 5 (by rfl) ⟨166592, by rfl⟩ : syracuseStep 3553973 = 333185) (by norm_num)
theorem B1776325 : Blo 1578487 1776325 := bbase (se 4 (by rfl) ⟨166530, by rfl⟩ : syracuseStep 1776325 = 333061) (by norm_num)
theorem B5995205 : Blo 1578487 5995205 := bbase (se 4 (by rfl) ⟨562050, by rfl⟩ : syracuseStep 5995205 = 1124101) (by norm_num)
theorem B1776361 : Blo 1578487 1776361 := bbase (se 2 (by rfl) ⟨666135, by rfl⟩ : syracuseStep 1776361 = 1332271) (by norm_num)
theorem B3554045 : Blo 1578487 3554045 := bbase (se 3 (by rfl) ⟨666383, by rfl⟩ : syracuseStep 3554045 = 1332767) (by norm_num)
theorem B1776397 : Blo 1578487 1776397 := bbase (se 3 (by rfl) ⟨333074, by rfl⟩ : syracuseStep 1776397 = 666149) (by norm_num)
theorem B1776433 : Blo 1578487 1776433 := bbase (se 2 (by rfl) ⟨666162, by rfl⟩ : syracuseStep 1776433 = 1332325) (by norm_num)
theorem B3554117 : Blo 1578487 3554117 := bbase (se 4 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 3554117 = 666397) (by norm_num)
theorem B1776469 : Blo 1578487 1776469 := bbase (se 9 (by rfl) ⟨5204, by rfl⟩ : syracuseStep 1776469 = 10409) (by norm_num)
theorem B5331797 : Blo 1578487 5331797 := bbase (se 9 (by rfl) ⟨15620, by rfl⟩ : syracuseStep 5331797 = 31241) (by norm_num)
theorem B7994213 : Blo 1578487 7994213 := bbase (se 4 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 7994213 = 1498915) (by norm_num)
theorem B2997101 : Blo 1578487 2997101 := bbase (se 3 (by rfl) ⟨561956, by rfl⟩ : syracuseStep 2997101 = 1123913) (by norm_num)
theorem B1776505 : Blo 1578487 1776505 := bbase (se 2 (by rfl) ⟨666189, by rfl⟩ : syracuseStep 1776505 = 1332379) (by norm_num)
theorem B3554189 : Blo 1578487 3554189 := bbase (se 3 (by rfl) ⟨666410, by rfl⟩ : syracuseStep 3554189 = 1332821) (by norm_num)
theorem B1686425 : Blo 1578487 1686425 := bbase (se 2 (by rfl) ⟨632409, by rfl⟩ : syracuseStep 1686425 = 1264819) (by norm_num)
theorem B1776541 : Blo 1578487 1776541 := bbase (se 3 (by rfl) ⟨333101, by rfl⟩ : syracuseStep 1776541 = 666203) (by norm_num)
theorem B1776577 : Blo 1578487 1776577 := bbase (se 2 (by rfl) ⟨666216, by rfl⟩ : syracuseStep 1776577 = 1332433) (by norm_num)
theorem B2530253 : Blo 1578487 2530253 := bbase (se 3 (by rfl) ⟨474422, by rfl⟩ : syracuseStep 2530253 = 948845) (by norm_num)
theorem B3554261 : Blo 1578487 3554261 := bbase (se 7 (by rfl) ⟨41651, by rfl⟩ : syracuseStep 3554261 = 83303) (by norm_num)
theorem B9608149 : Blo 1578487 9608149 := bbase (se 7 (by rfl) ⟨112595, by rfl⟩ : syracuseStep 9608149 = 225191) (by norm_num)
theorem B1776613 : Blo 1578487 1776613 := bbase (se 4 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 1776613 = 333115) (by norm_num)
theorem B3996661 : Blo 1578487 3996661 := bbase (se 5 (by rfl) ⟨187343, by rfl⟩ : syracuseStep 3996661 = 374687) (by norm_num)
theorem B2997253 : Blo 1578487 2997253 := bbase (se 4 (by rfl) ⟨280992, by rfl⟩ : syracuseStep 2997253 = 561985) (by norm_num)
theorem B1776649 : Blo 1578487 1776649 := bbase (se 2 (by rfl) ⟨666243, by rfl⟩ : syracuseStep 1776649 = 1332487) (by norm_num)
theorem B10959893 : Blo 1578487 10959893 := bbase (se 6 (by rfl) ⟨256872, by rfl⟩ : syracuseStep 10959893 = 513745) (by norm_num)
theorem B3554333 : Blo 1578487 3554333 := bbase (se 3 (by rfl) ⟨666437, by rfl⟩ : syracuseStep 3554333 = 1332875) (by norm_num)
theorem B1776685 : Blo 1578487 1776685 := bbase (se 3 (by rfl) ⟨333128, by rfl⟩ : syracuseStep 1776685 = 666257) (by norm_num)
theorem B1997885 : Blo 1578487 1997885 := bbase (se 3 (by rfl) ⟨374603, by rfl⟩ : syracuseStep 1997885 = 749207) (by norm_num)
theorem B3374149 : Blo 1578487 3374149 := bbase (se 4 (by rfl) ⟨316326, by rfl⟩ : syracuseStep 3374149 = 632653) (by norm_num)
theorem B1776721 : Blo 1578487 1776721 := bbase (se 2 (by rfl) ⟨666270, by rfl⟩ : syracuseStep 1776721 = 1332541) (by norm_num)
theorem B3603541 : Blo 1578487 3603541 := bbase (se 8 (by rfl) ⟨21114, by rfl⟩ : syracuseStep 3603541 = 42229) (by norm_num)
theorem B3996773 : Blo 1578487 3996773 := bbase (se 4 (by rfl) ⟨374697, by rfl⟩ : syracuseStep 3996773 = 749395) (by norm_num)
theorem B3554405 : Blo 1578487 3554405 := bbase (se 4 (by rfl) ⟨333225, by rfl⟩ : syracuseStep 3554405 = 666451) (by norm_num)
theorem B1997941 : Blo 1578487 1997941 := bbase (se 5 (by rfl) ⟨93653, by rfl⟩ : syracuseStep 1997941 = 187307) (by norm_num)
theorem B1776757 : Blo 1578487 1776757 := bbase (se 5 (by rfl) ⟨83285, by rfl⟩ : syracuseStep 1776757 = 166571) (by norm_num)
theorem B1686673 : Blo 1578487 1686673 := bbase (se 2 (by rfl) ⟨632502, by rfl⟩ : syracuseStep 1686673 = 1265005) (by norm_num)
theorem B1776793 : Blo 1578487 1776793 := bbase (se 2 (by rfl) ⟨666297, by rfl⟩ : syracuseStep 1776793 = 1332595) (by norm_num)
theorem B3554477 : Blo 1578487 3554477 := bbase (se 3 (by rfl) ⟨666464, by rfl⟩ : syracuseStep 3554477 = 1332929) (by norm_num)
theorem B1776829 : Blo 1578487 1776829 := bbase (se 3 (by rfl) ⟨333155, by rfl⟩ : syracuseStep 1776829 = 666311) (by norm_num)
theorem B1998037 : Blo 1578487 1998037 := bbase (se 7 (by rfl) ⟨23414, by rfl⟩ : syracuseStep 1998037 = 46829) (by norm_num)
theorem B1776865 : Blo 1578487 1776865 := bbase (se 2 (by rfl) ⟨666324, by rfl⟩ : syracuseStep 1776865 = 1332649) (by norm_num)
theorem B8994037 : Blo 1578487 8994037 := bbase (se 5 (by rfl) ⟨421595, by rfl⟩ : syracuseStep 8994037 = 843191) (by norm_num)
theorem B3554549 : Blo 1578487 3554549 := bbase (se 5 (by rfl) ⟨166619, by rfl⟩ : syracuseStep 3554549 = 333239) (by norm_num)
theorem B1776901 : Blo 1578487 1776901 := bbase (se 4 (by rfl) ⟨166584, by rfl⟩ : syracuseStep 1776901 = 333169) (by norm_num)
theorem B5332229 : Blo 1578487 5332229 := bbase (se 4 (by rfl) ⟨499896, by rfl⟩ : syracuseStep 5332229 = 999793) (by norm_num)
theorem B3996965 : Blo 1578487 3996965 := bbase (se 4 (by rfl) ⟨374715, by rfl⟩ : syracuseStep 3996965 = 749431) (by norm_num)
theorem B6749477 : Blo 1578487 6749477 := bbase (se 4 (by rfl) ⟨632763, by rfl⟩ : syracuseStep 6749477 = 1265527) (by norm_num)
theorem B1776937 : Blo 1578487 1776937 := bbase (se 2 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 1776937 = 1332703) (by norm_num)
theorem B2997557 : Blo 1578487 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B3554621 : Blo 1578487 3554621 := bbase (se 3 (by rfl) ⟨666491, by rfl⟩ : syracuseStep 3554621 = 1332983) (by norm_num)
theorem B1776973 : Blo 1578487 1776973 := bbase (se 3 (by rfl) ⟨333182, by rfl⟩ : syracuseStep 1776973 = 666365) (by norm_num)
theorem B1777009 : Blo 1578487 1777009 := bbase (se 2 (by rfl) ⟨666378, by rfl⟩ : syracuseStep 1777009 = 1332757) (by norm_num)
theorem B1998209 : Blo 1578487 1998209 := bbase (se 2 (by rfl) ⟨749328, by rfl⟩ : syracuseStep 1998209 = 1498657) (by norm_num)
theorem B3554693 : Blo 1578487 3554693 := bbase (se 4 (by rfl) ⟨333252, by rfl⟩ : syracuseStep 3554693 = 666505) (by norm_num)
theorem B1777045 : Blo 1578487 1777045 := bbase (se 6 (by rfl) ⟨41649, by rfl⟩ : syracuseStep 1777045 = 83299) (by norm_num)
theorem B1998265 : Blo 1578487 1998265 := bbase (se 2 (by rfl) ⟨749349, by rfl⟩ : syracuseStep 1998265 = 1498699) (by norm_num)
theorem B1777081 : Blo 1578487 1777081 := bbase (se 2 (by rfl) ⟨666405, by rfl⟩ : syracuseStep 1777081 = 1332811) (by norm_num)
theorem B3554765 : Blo 1578487 3554765 := bbase (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) (by norm_num)
theorem B1777117 : Blo 1578487 1777117 := bbase (se 3 (by rfl) ⟨333209, by rfl⟩ : syracuseStep 1777117 = 666419) (by norm_num)
theorem B3603941 : Blo 1578487 3603941 := bbase (se 4 (by rfl) ⟨337869, by rfl⟩ : syracuseStep 3603941 = 675739) (by norm_num)
theorem B1777153 : Blo 1578487 1777153 := bbase (se 2 (by rfl) ⟨666432, by rfl⟩ : syracuseStep 1777153 = 1332865) (by norm_num)
theorem B4496917 : Blo 1578487 4496917 := bbase (se 6 (by rfl) ⟨105396, by rfl⟩ : syracuseStep 4496917 = 210793) (by norm_num)
theorem B3554837 : Blo 1578487 3554837 := bbase (se 6 (by rfl) ⟨83316, by rfl⟩ : syracuseStep 3554837 = 166633) (by norm_num)
theorem B1998361 : Blo 1578487 1998361 := bbase (se 2 (by rfl) ⟨749385, by rfl⟩ : syracuseStep 1998361 = 1498771) (by norm_num)
theorem B1777189 : Blo 1578487 1777189 := bbase (se 4 (by rfl) ⟨166611, by rfl⟩ : syracuseStep 1777189 = 333223) (by norm_num)
theorem B1777225 : Blo 1578487 1777225 := bbase (se 2 (by rfl) ⟨666459, by rfl⟩ : syracuseStep 1777225 = 1332919) (by norm_num)
theorem B1687117 : Blo 1578487 1687117 := bbase (se 3 (by rfl) ⟨316334, by rfl⟩ : syracuseStep 1687117 = 632669) (by norm_num)
theorem B2530901 : Blo 1578487 2530901 := bbase (se 8 (by rfl) ⟨14829, by rfl⟩ : syracuseStep 2530901 = 29659) (by norm_num)
theorem B3554909 : Blo 1578487 3554909 := bbase (se 3 (by rfl) ⟨666545, by rfl⟩ : syracuseStep 3554909 = 1333091) (by norm_num)
theorem B1777261 : Blo 1578487 1777261 := bbase (se 3 (by rfl) ⟨333236, by rfl⟩ : syracuseStep 1777261 = 666473) (by norm_num)
theorem B3997309 : Blo 1578487 3997309 := bbase (se 3 (by rfl) ⟨749495, by rfl⟩ : syracuseStep 3997309 = 1498991) (by norm_num)
theorem B1687177 : Blo 1578487 1687177 := bbase (se 2 (by rfl) ⟨632691, by rfl⟩ : syracuseStep 1687177 = 1265383) (by norm_num)
theorem B1777297 : Blo 1578487 1777297 := bbase (se 2 (by rfl) ⟨666486, by rfl⟩ : syracuseStep 1777297 = 1332973) (by norm_num)
theorem B3554981 : Blo 1578487 3554981 := bbase (se 4 (by rfl) ⟨333279, by rfl⟩ : syracuseStep 3554981 = 666559) (by norm_num)
theorem B1777333 : Blo 1578487 1777333 := bbase (se 5 (by rfl) ⟨83312, by rfl⟩ : syracuseStep 1777333 = 166625) (by norm_num)
theorem B5332661 : Blo 1578487 5332661 := bbase (se 5 (by rfl) ⟨249968, by rfl⟩ : syracuseStep 5332661 = 499937) (by norm_num)
theorem B1998533 : Blo 1578487 1998533 := bbase (se 4 (by rfl) ⟨187362, by rfl⟩ : syracuseStep 1998533 = 374725) (by norm_num)
theorem B1777369 : Blo 1578487 1777369 := bbase (se 2 (by rfl) ⟨666513, by rfl⟩ : syracuseStep 1777369 = 1333027) (by norm_num)
theorem B3997421 : Blo 1578487 3997421 := bbase (se 3 (by rfl) ⟨749516, by rfl⟩ : syracuseStep 3997421 = 1499033) (by norm_num)
theorem B3555053 : Blo 1578487 3555053 := bbase (se 3 (by rfl) ⟨666572, by rfl⟩ : syracuseStep 3555053 = 1333145) (by norm_num)
theorem B1998589 : Blo 1578487 1998589 := bbase (se 3 (by rfl) ⟨374735, by rfl⟩ : syracuseStep 1998589 = 749471) (by norm_num)
theorem B1777405 : Blo 1578487 1777405 := bbase (se 3 (by rfl) ⟨333263, by rfl⟩ : syracuseStep 1777405 = 666527) (by norm_num)
theorem B1777441 : Blo 1578487 1777441 := bbase (se 2 (by rfl) ⟨666540, by rfl⟩ : syracuseStep 1777441 = 1333081) (by norm_num)
theorem B3555125 : Blo 1578487 3555125 := bbase (se 5 (by rfl) ⟨166646, by rfl⟩ : syracuseStep 3555125 = 333293) (by norm_num)
theorem B7692101 : Blo 1578487 7692101 := bbase (se 4 (by rfl) ⟨721134, by rfl⟩ : syracuseStep 7692101 = 1442269) (by norm_num)
theorem B1777477 : Blo 1578487 1777477 := bbase (se 4 (by rfl) ⟨166638, by rfl⟩ : syracuseStep 1777477 = 333277) (by norm_num)
theorem B1998685 : Blo 1578487 1998685 := bbase (se 3 (by rfl) ⟨374753, by rfl⟩ : syracuseStep 1998685 = 749507) (by norm_num)
theorem B5996389 : Blo 1578487 5996389 := bbase (se 4 (by rfl) ⟨562161, by rfl⟩ : syracuseStep 5996389 = 1124323) (by norm_num)
theorem B1777513 : Blo 1578487 1777513 := bbase (se 2 (by rfl) ⟨666567, by rfl⟩ : syracuseStep 1777513 = 1333135) (by norm_num)
theorem B3555197 : Blo 1578487 3555197 := bbase (se 3 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 3555197 = 1333199) (by norm_num)
theorem B6840197 : Blo 1578487 6840197 := bbase (se 4 (by rfl) ⟨641268, by rfl⟩ : syracuseStep 6840197 = 1282537) (by norm_num)
theorem B1777549 : Blo 1578487 1777549 := bbase (se 3 (by rfl) ⟨333290, by rfl⟩ : syracuseStep 1777549 = 666581) (by norm_num)
theorem B20242325 : Blo 1578487 20242325 := bbase (se 6 (by rfl) ⟨474429, by rfl⟩ : syracuseStep 20242325 = 948859) (by norm_num)
theorem B3997613 : Blo 1578487 3997613 := bbase (se 3 (by rfl) ⟨749552, by rfl⟩ : syracuseStep 3997613 = 1499105) (by norm_num)
theorem B3604397 : Blo 1578487 3604397 := bbase (se 3 (by rfl) ⟨675824, by rfl⟩ : syracuseStep 3604397 = 1351649) (by norm_num)
theorem B1777585 : Blo 1578487 1777585 := bbase (se 2 (by rfl) ⟨666594, by rfl⟩ : syracuseStep 1777585 = 1333189) (by norm_num)
theorem B3375037 : Blo 1578487 3375037 := bbase (se 3 (by rfl) ⟨632819, by rfl⟩ : syracuseStep 3375037 = 1265639) (by norm_num)
theorem B3555269 : Blo 1578487 3555269 := bbase (se 4 (by rfl) ⟨333306, by rfl⟩ : syracuseStep 3555269 = 666613) (by norm_num)
theorem B1687493 : Blo 1578487 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B1777621 : Blo 1578487 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B1777657 : Blo 1578487 1777657 := bbase (se 2 (by rfl) ⟨666621, by rfl⟩ : syracuseStep 1777657 = 1333243) (by norm_num)
theorem B2433041 : Blo 1578487 2433041 := bstep (se 2 (by rfl) ⟨912390, by rfl⟩ : syracuseStep 2433041 = 1824781) B1824781
theorem B2703395 : Blo 1578487 2703395 := bstep (se 1 (by rfl) ⟨2027546, by rfl⟩ : syracuseStep 2703395 = 4055093) B4055093
theorem B3997745 : Blo 1578487 3997745 := bstep (se 2 (by rfl) ⟨1499154, by rfl⟩ : syracuseStep 3997745 = 2998309) B2998309
theorem B3555377 : Blo 1578487 3555377 := bstep (se 2 (by rfl) ⟨1333266, by rfl⟩ : syracuseStep 3555377 = 2666533) B2666533
theorem B3555395 : Blo 1578487 3555395 := bstep (se 1 (by rfl) ⟨2666546, by rfl⟩ : syracuseStep 3555395 = 5333093) B5333093
theorem B1777747 : Blo 1578487 1777747 := bstep (se 1 (by rfl) ⟨1333310, by rfl⟩ : syracuseStep 1777747 = 2666621) B2666621
theorem B3997795 : Blo 1578487 3997795 := bstep (se 1 (by rfl) ⟨2998346, by rfl⟩ : syracuseStep 3997795 = 5996693) B5996693
theorem B5062787 : Blo 1578487 5062787 := bstep (se 1 (by rfl) ⟨3797090, by rfl⟩ : syracuseStep 5062787 = 7594181) B7594181
theorem B10125445 : Blo 1578487 10125445 := bstep (se 4 (by rfl) ⟨949260, by rfl⟩ : syracuseStep 10125445 = 1898521) B1898521
theorem B2531521 : Blo 1578487 2531521 := bstep (se 2 (by rfl) ⟨949320, by rfl⟩ : syracuseStep 2531521 = 1898641) B1898641
theorem B2433233 : Blo 1578487 2433233 := bstep (se 2 (by rfl) ⟨912462, by rfl⟩ : syracuseStep 2433233 = 1824925) B1824925
theorem B5333201 : Blo 1578487 5333201 := bstep (se 2 (by rfl) ⟨1999950, by rfl⟩ : syracuseStep 5333201 = 3999901) B3999901
theorem B1999075 : Blo 1578487 1999075 := bstep (se 1 (by rfl) ⟨1499306, by rfl⟩ : syracuseStep 1999075 = 2998613) B2998613
theorem B1777891 : Blo 1578487 1777891 := bstep (se 1 (by rfl) ⟨1333418, by rfl⟩ : syracuseStep 1777891 = 2666837) B2666837
theorem B21627107 : Blo 1578487 21627107 := bstep (se 1 (by rfl) ⟨16220330, by rfl⟩ : syracuseStep 21627107 = 32440661) B32440661
theorem B3997937 : Blo 1578487 3997937 := bstep (se 2 (by rfl) ⟨1499226, by rfl⟩ : syracuseStep 3997937 = 2998453) B2998453
theorem B6750449 : Blo 1578487 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B2367731 : Blo 1578487 2367731 := bstep (se 1 (by rfl) ⟨1775798, by rfl⟩ : syracuseStep 2367731 = 3551597) B3551597
theorem B13492493 : Blo 1578487 13492493 := bstep (se 3 (by rfl) ⟨2529842, by rfl⟩ : syracuseStep 13492493 = 5059685) B5059685
theorem B2367761 : Blo 1578487 2367761 := bstep (se 2 (by rfl) ⟨887910, by rfl⟩ : syracuseStep 2367761 = 1775821) B1775821
theorem B3793169 : Blo 1578487 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B2367779 : Blo 1578487 2367779 := bstep (se 1 (by rfl) ⟨1775834, by rfl⟩ : syracuseStep 2367779 = 3551669) B3551669
theorem B2367809 : Blo 1578487 2367809 := bstep (se 2 (by rfl) ⟨887928, by rfl⟩ : syracuseStep 2367809 = 1775857) B1775857
theorem B1999171 : Blo 1578487 1999171 := bstep (se 1 (by rfl) ⟨1499378, by rfl⟩ : syracuseStep 1999171 = 2998757) B2998757
theorem B3555665 : Blo 1578487 3555665 := bstep (se 2 (by rfl) ⟨1333374, by rfl⟩ : syracuseStep 3555665 = 2666749) B2666749
theorem B2367827 : Blo 1578487 2367827 := bstep (se 1 (by rfl) ⟨1775870, by rfl⟩ : syracuseStep 2367827 = 3551741) B3551741
theorem B3555683 : Blo 1578487 3555683 := bstep (se 1 (by rfl) ⟨2666762, by rfl⟩ : syracuseStep 3555683 = 5333525) B5333525
theorem B2367857 : Blo 1578487 2367857 := bstep (se 2 (by rfl) ⟨887946, by rfl⟩ : syracuseStep 2367857 = 1775893) B1775893
theorem B1778035 : Blo 1578487 1778035 := bstep (se 1 (by rfl) ⟨1333526, by rfl⟩ : syracuseStep 1778035 = 2667053) B2667053
theorem B2367875 : Blo 1578487 2367875 := bstep (se 1 (by rfl) ⟨1775906, by rfl⟩ : syracuseStep 2367875 = 3551813) B3551813
theorem B2367905 : Blo 1578487 2367905 := bstep (se 2 (by rfl) ⟨887964, by rfl⟩ : syracuseStep 2367905 = 1775929) B1775929
theorem B3244465 : Blo 1578487 3244465 := bstep (se 2 (by rfl) ⟨1216674, by rfl⟩ : syracuseStep 3244465 = 2433349) B2433349
theorem B2367923 : Blo 1578487 2367923 := bstep (se 1 (by rfl) ⟨1775942, by rfl⟩ : syracuseStep 2367923 = 3551885) B3551885
theorem B4268483 : Blo 1578487 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B2367953 : Blo 1578487 2367953 := bstep (se 2 (by rfl) ⟨887982, by rfl⟩ : syracuseStep 2367953 = 1775965) B1775965
theorem B2367971 : Blo 1578487 2367971 := bstep (se 1 (by rfl) ⟨1775978, by rfl⟩ : syracuseStep 2367971 = 3551957) B3551957
theorem B8995313 : Blo 1578487 8995313 := bstep (se 2 (by rfl) ⟨3373242, by rfl⟩ : syracuseStep 8995313 = 6746485) B6746485
theorem B2368001 : Blo 1578487 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B2368019 : Blo 1578487 2368019 := bstep (se 1 (by rfl) ⟨1776014, by rfl⟩ : syracuseStep 2368019 = 3552029) B3552029
theorem B2368049 : Blo 1578487 2368049 := bstep (se 2 (by rfl) ⟨888018, by rfl⟩ : syracuseStep 2368049 = 1776037) B1776037
theorem B2368067 : Blo 1578487 2368067 := bstep (se 1 (by rfl) ⟨1776050, by rfl⟩ : syracuseStep 2368067 = 3552101) B3552101
theorem B8651333 : Blo 1578487 8651333 := bstep (se 4 (by rfl) ⟨811062, by rfl⟩ : syracuseStep 8651333 = 1622125) B1622125
theorem B2368097 : Blo 1578487 2368097 := bstep (se 2 (by rfl) ⟨888036, by rfl⟩ : syracuseStep 2368097 = 1776073) B1776073
theorem B3555953 : Blo 1578487 3555953 := bstep (se 2 (by rfl) ⟨1333482, by rfl⟩ : syracuseStep 3555953 = 2666965) B2666965
theorem B2368115 : Blo 1578487 2368115 := bstep (se 1 (by rfl) ⟨1776086, by rfl⟩ : syracuseStep 2368115 = 3552173) B3552173
theorem B3555971 : Blo 1578487 3555971 := bstep (se 1 (by rfl) ⟨2666978, by rfl⟩ : syracuseStep 3555971 = 5333957) B5333957
theorem B9241229 : Blo 1578487 9241229 := bstep (se 3 (by rfl) ⟨1732730, by rfl⟩ : syracuseStep 9241229 = 3465461) B3465461
theorem B2368145 : Blo 1578487 2368145 := bstep (se 2 (by rfl) ⟨888054, by rfl⟩ : syracuseStep 2368145 = 1776109) B1776109
theorem B2368163 : Blo 1578487 2368163 := bstep (se 1 (by rfl) ⟨1776122, by rfl⟩ : syracuseStep 2368163 = 3552245) B3552245
theorem B2368193 : Blo 1578487 2368193 := bstep (se 2 (by rfl) ⟨888072, by rfl⟩ : syracuseStep 2368193 = 1776145) B1776145
theorem B2368211 : Blo 1578487 2368211 := bstep (se 1 (by rfl) ⟨1776158, by rfl⟩ : syracuseStep 2368211 = 3552317) B3552317
theorem B5333741 : Blo 1578487 5333741 := bstep (se 3 (by rfl) ⟨1000076, by rfl⟩ : syracuseStep 5333741 = 2000153) B2000153
theorem B2368241 : Blo 1578487 2368241 := bstep (se 2 (by rfl) ⟨888090, by rfl⟩ : syracuseStep 2368241 = 1776181) B1776181
theorem B4801265 : Blo 1578487 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B4268785 : Blo 1578487 4268785 := bstep (se 2 (by rfl) ⟨1600794, by rfl⟩ : syracuseStep 4268785 = 3201589) B3201589
theorem B2368259 : Blo 1578487 2368259 := bstep (se 1 (by rfl) ⟨1776194, by rfl⟩ : syracuseStep 2368259 = 3552389) B3552389
theorem B4498193 : Blo 1578487 4498193 := bstep (se 2 (by rfl) ⟨1686822, by rfl⟩ : syracuseStep 4498193 = 3373645) B3373645
theorem B2368289 : Blo 1578487 2368289 := bstep (se 2 (by rfl) ⟨888108, by rfl⟩ : syracuseStep 2368289 = 1776217) B1776217
theorem B5997347 : Blo 1578487 5997347 := bstep (se 1 (by rfl) ⟨4498010, by rfl⟩ : syracuseStep 5997347 = 8996021) B8996021
theorem B5333795 : Blo 1578487 5333795 := bstep (se 1 (by rfl) ⟨4000346, by rfl⟩ : syracuseStep 5333795 = 8000693) B8000693
theorem B5997361 : Blo 1578487 5997361 := bstep (se 2 (by rfl) ⟨2249010, by rfl⟩ : syracuseStep 5997361 = 4498021) B4498021
theorem B2368307 : Blo 1578487 2368307 := bstep (se 1 (by rfl) ⟨1776230, by rfl⟩ : syracuseStep 2368307 = 3552461) B3552461
theorem B1999667 : Blo 1578487 1999667 := bstep (se 1 (by rfl) ⟨1499750, by rfl⟩ : syracuseStep 1999667 = 2999501) B2999501
theorem B2368337 : Blo 1578487 2368337 := bstep (se 2 (by rfl) ⟨888126, by rfl⟩ : syracuseStep 2368337 = 1776253) B1776253
theorem B3793745 : Blo 1578487 3793745 := bstep (se 2 (by rfl) ⟨1422654, by rfl⟩ : syracuseStep 3793745 = 2845309) B2845309
theorem B2368355 : Blo 1578487 2368355 := bstep (se 1 (by rfl) ⟨1776266, by rfl⟩ : syracuseStep 2368355 = 3552533) B3552533
theorem B2368385 : Blo 1578487 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B2368403 : Blo 1578487 2368403 := bstep (se 1 (by rfl) ⟨1776302, by rfl⟩ : syracuseStep 2368403 = 3552605) B3552605
theorem B2368433 : Blo 1578487 2368433 := bstep (se 2 (by rfl) ⟨888162, by rfl⟩ : syracuseStep 2368433 = 1776325) B1776325
theorem B2368451 : Blo 1578487 2368451 := bstep (se 1 (by rfl) ⟨1776338, by rfl⟩ : syracuseStep 2368451 = 3552677) B3552677
theorem B2368481 : Blo 1578487 2368481 := bstep (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) B1776361
theorem B3793891 : Blo 1578487 3793891 := bstep (se 1 (by rfl) ⟨2845418, by rfl⟩ : syracuseStep 3793891 = 5690837) B5690837
theorem B2999281 : Blo 1578487 2999281 := bstep (se 2 (by rfl) ⟨1124730, by rfl⟩ : syracuseStep 2999281 = 2249461) B2249461
theorem B2368499 : Blo 1578487 2368499 := bstep (se 1 (by rfl) ⟨1776374, by rfl⟩ : syracuseStep 2368499 = 3552749) B3552749
theorem B2368529 : Blo 1578487 2368529 := bstep (se 2 (by rfl) ⟨888198, by rfl⟩ : syracuseStep 2368529 = 1776397) B1776397
theorem B2368547 : Blo 1578487 2368547 := bstep (se 1 (by rfl) ⟨1776410, by rfl⟩ : syracuseStep 2368547 = 3552821) B3552821
theorem B5334065 : Blo 1578487 5334065 := bstep (se 2 (by rfl) ⟨2000274, by rfl⟩ : syracuseStep 5334065 = 4000549) B4000549
theorem B2368577 : Blo 1578487 2368577 := bstep (se 2 (by rfl) ⟨888216, by rfl⟩ : syracuseStep 2368577 = 1776433) B1776433
theorem B2368595 : Blo 1578487 2368595 := bstep (se 1 (by rfl) ⟨1776446, by rfl⟩ : syracuseStep 2368595 = 3552893) B3552893
theorem B2368625 : Blo 1578487 2368625 := bstep (se 2 (by rfl) ⟨888234, by rfl⟩ : syracuseStep 2368625 = 1776469) B1776469
theorem B2368643 : Blo 1578487 2368643 := bstep (se 1 (by rfl) ⟨1776482, by rfl⟩ : syracuseStep 2368643 = 3552965) B3552965
theorem B2368673 : Blo 1578487 2368673 := bstep (se 2 (by rfl) ⟨888252, by rfl⟩ : syracuseStep 2368673 = 1776505) B1776505
theorem B5694641 : Blo 1578487 5694641 := bstep (se 2 (by rfl) ⟨2135490, by rfl⟩ : syracuseStep 5694641 = 4270981) B4270981
theorem B2368691 : Blo 1578487 2368691 := bstep (se 1 (by rfl) ⟨1776518, by rfl⟩ : syracuseStep 2368691 = 3553037) B3553037
theorem B2368721 : Blo 1578487 2368721 := bstep (se 2 (by rfl) ⟨888270, by rfl⟩ : syracuseStep 2368721 = 1776541) B1776541
theorem B3998929 : Blo 1578487 3998929 := bstep (se 2 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 3998929 = 2999197) B2999197
theorem B2368739 : Blo 1578487 2368739 := bstep (se 1 (by rfl) ⟨1776554, by rfl⟩ : syracuseStep 2368739 = 3553109) B3553109
theorem B7996643 : Blo 1578487 7996643 := bstep (se 1 (by rfl) ⟨5997482, by rfl⟩ : syracuseStep 7996643 = 11994965) B11994965
theorem B2368769 : Blo 1578487 2368769 := bstep (se 2 (by rfl) ⟨888288, by rfl⟩ : syracuseStep 2368769 = 1776577) B1776577
theorem B2368787 : Blo 1578487 2368787 := bstep (se 1 (by rfl) ⟨1776590, by rfl⟩ : syracuseStep 2368787 = 3553181) B3553181
theorem B7587107 : Blo 1578487 7587107 := bstep (se 1 (by rfl) ⟨5690330, by rfl⟩ : syracuseStep 7587107 = 11380661) B11380661
theorem B2368817 : Blo 1578487 2368817 := bstep (se 2 (by rfl) ⟨888306, by rfl⟩ : syracuseStep 2368817 = 1776613) B1776613
theorem B2368835 : Blo 1578487 2368835 := bstep (se 1 (by rfl) ⟨1776626, by rfl⟩ : syracuseStep 2368835 = 3553253) B3553253
theorem B2368865 : Blo 1578487 2368865 := bstep (se 2 (by rfl) ⟨888324, by rfl⟩ : syracuseStep 2368865 = 1776649) B1776649
theorem B2663779 : Blo 1578487 2663779 := bstep (se 1 (by rfl) ⟨1997834, by rfl⟩ : syracuseStep 2663779 = 3995669) B3995669
theorem B2368883 : Blo 1578487 2368883 := bstep (se 1 (by rfl) ⟨1776662, by rfl⟩ : syracuseStep 2368883 = 3553325) B3553325
theorem B2999683 : Blo 1578487 2999683 := bstep (se 1 (by rfl) ⟨2249762, by rfl⟩ : syracuseStep 2999683 = 4499525) B4499525
theorem B2368913 : Blo 1578487 2368913 := bstep (se 2 (by rfl) ⟨888342, by rfl⟩ : syracuseStep 2368913 = 1776685) B1776685
theorem B2368931 : Blo 1578487 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B4498865 : Blo 1578487 4498865 := bstep (se 2 (by rfl) ⟨1687074, by rfl⟩ : syracuseStep 4498865 = 3374149) B3374149
theorem B2999729 : Blo 1578487 2999729 := bstep (se 2 (by rfl) ⟨1124898, by rfl⟩ : syracuseStep 2999729 = 2249797) B2249797
theorem B2368961 : Blo 1578487 2368961 := bstep (se 2 (by rfl) ⟨888360, by rfl⟩ : syracuseStep 2368961 = 1776721) B1776721
theorem B2278865 : Blo 1578487 2278865 := bstep (se 2 (by rfl) ⟨854574, by rfl⟩ : syracuseStep 2278865 = 1709149) B1709149
theorem B2368979 : Blo 1578487 2368979 := bstep (se 1 (by rfl) ⟨1776734, by rfl⟩ : syracuseStep 2368979 = 3553469) B3553469
theorem B3999203 : Blo 1578487 3999203 := bstep (se 1 (by rfl) ⟨2999402, by rfl⟩ : syracuseStep 3999203 = 5998805) B5998805
theorem B2663921 : Blo 1578487 2663921 := bstep (se 2 (by rfl) ⟨998970, by rfl⟩ : syracuseStep 2663921 = 1997941) B1997941
theorem B2369009 : Blo 1578487 2369009 := bstep (se 2 (by rfl) ⟨888378, by rfl⟩ : syracuseStep 2369009 = 1776757) B1776757
theorem B2369027 : Blo 1578487 2369027 := bstep (se 1 (by rfl) ⟨1776770, by rfl⟩ : syracuseStep 2369027 = 3553541) B3553541
theorem B2369057 : Blo 1578487 2369057 := bstep (se 2 (by rfl) ⟨888396, by rfl⟩ : syracuseStep 2369057 = 1776793) B1776793
theorem B7587377 : Blo 1578487 7587377 := bstep (se 2 (by rfl) ⟨2845266, by rfl⟩ : syracuseStep 7587377 = 5690533) B5690533
theorem B3900977 : Blo 1578487 3900977 := bstep (se 2 (by rfl) ⟨1462866, by rfl⟩ : syracuseStep 3900977 = 2925733) B2925733
theorem B2369075 : Blo 1578487 2369075 := bstep (se 1 (by rfl) ⟨1776806, by rfl⟩ : syracuseStep 2369075 = 3553613) B3553613
theorem B2369105 : Blo 1578487 2369105 := bstep (se 2 (by rfl) ⟨888414, by rfl⟩ : syracuseStep 2369105 = 1776829) B1776829
theorem B2369123 : Blo 1578487 2369123 := bstep (se 1 (by rfl) ⟨1776842, by rfl⟩ : syracuseStep 2369123 = 3553685) B3553685
theorem B2664049 : Blo 1578487 2664049 := bstep (se 2 (by rfl) ⟨999018, by rfl⟩ : syracuseStep 2664049 = 1998037) B1998037
theorem B2369153 : Blo 1578487 2369153 := bstep (se 2 (by rfl) ⟨888432, by rfl⟩ : syracuseStep 2369153 = 1776865) B1776865
theorem B5400209 : Blo 1578487 5400209 := bstep (se 2 (by rfl) ⟨2025078, by rfl⟩ : syracuseStep 5400209 = 4050157) B4050157
theorem B2664083 : Blo 1578487 2664083 := bstep (se 1 (by rfl) ⟨1998062, by rfl⟩ : syracuseStep 2664083 = 3996125) B3996125
theorem B2369171 : Blo 1578487 2369171 := bstep (se 1 (by rfl) ⟨1776878, by rfl⟩ : syracuseStep 2369171 = 3553757) B3553757
theorem B3999395 : Blo 1578487 3999395 := bstep (se 1 (by rfl) ⟨2999546, by rfl⟩ : syracuseStep 3999395 = 5999093) B5999093
theorem B2369201 : Blo 1578487 2369201 := bstep (se 2 (by rfl) ⟨888450, by rfl⟩ : syracuseStep 2369201 = 1776901) B1776901
theorem B2369219 : Blo 1578487 2369219 := bstep (se 1 (by rfl) ⟨1776914, by rfl⟩ : syracuseStep 2369219 = 3553829) B3553829
theorem B3000017 : Blo 1578487 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B2369249 : Blo 1578487 2369249 := bstep (se 2 (by rfl) ⟨888468, by rfl⟩ : syracuseStep 2369249 = 1776937) B1776937
theorem B2369267 : Blo 1578487 2369267 := bstep (se 1 (by rfl) ⟨1776950, by rfl⟩ : syracuseStep 2369267 = 3553901) B3553901
theorem B14411533 : Blo 1578487 14411533 := bstep (se 3 (by rfl) ⟨2702162, by rfl⟩ : syracuseStep 14411533 = 5404325) B5404325
theorem B2369297 : Blo 1578487 2369297 := bstep (se 2 (by rfl) ⟨888486, by rfl⟩ : syracuseStep 2369297 = 1776973) B1776973
theorem B2664211 : Blo 1578487 2664211 := bstep (se 1 (by rfl) ⟨1998158, by rfl⟩ : syracuseStep 2664211 = 3996317) B3996317
theorem B2369315 : Blo 1578487 2369315 := bstep (se 1 (by rfl) ⟨1776986, by rfl⟩ : syracuseStep 2369315 = 3553973) B3553973
theorem B2369345 : Blo 1578487 2369345 := bstep (se 2 (by rfl) ⟨888504, by rfl⟩ : syracuseStep 2369345 = 1777009) B1777009
theorem B2369363 : Blo 1578487 2369363 := bstep (se 1 (by rfl) ⟨1777022, by rfl⟩ : syracuseStep 2369363 = 3554045) B3554045
theorem B2369393 : Blo 1578487 2369393 := bstep (se 2 (by rfl) ⟨888522, by rfl⟩ : syracuseStep 2369393 = 1777045) B1777045
theorem B2369411 : Blo 1578487 2369411 := bstep (se 1 (by rfl) ⟨1777058, by rfl⟩ : syracuseStep 2369411 = 3554117) B3554117
theorem B2664353 : Blo 1578487 2664353 := bstep (se 2 (by rfl) ⟨999132, by rfl⟩ : syracuseStep 2664353 = 1998265) B1998265
theorem B2369441 : Blo 1578487 2369441 := bstep (se 2 (by rfl) ⟨888540, by rfl⟩ : syracuseStep 2369441 = 1777081) B1777081
theorem B8996771 : Blo 1578487 8996771 := bstep (se 1 (by rfl) ⟨6747578, by rfl⟩ : syracuseStep 8996771 = 13495157) B13495157
theorem B2369459 : Blo 1578487 2369459 := bstep (se 1 (by rfl) ⟨1777094, by rfl⟩ : syracuseStep 2369459 = 3554189) B3554189
theorem B2369489 : Blo 1578487 2369489 := bstep (se 2 (by rfl) ⟨888558, by rfl⟩ : syracuseStep 2369489 = 1777117) B1777117
theorem B26970083 : Blo 1578487 26970083 := bstep (se 1 (by rfl) ⟨20227562, by rfl⟩ : syracuseStep 26970083 = 40455125) B40455125
theorem B2369507 : Blo 1578487 2369507 := bstep (se 1 (by rfl) ⟨1777130, by rfl⟩ : syracuseStep 2369507 = 3554261) B3554261
theorem B2369537 : Blo 1578487 2369537 := bstep (se 2 (by rfl) ⟨888576, by rfl⟩ : syracuseStep 2369537 = 1777153) B1777153
theorem B7997453 : Blo 1578487 7997453 := bstep (se 3 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 7997453 = 2999045) B2999045
theorem B2369555 : Blo 1578487 2369555 := bstep (se 1 (by rfl) ⟨1777166, by rfl⟩ : syracuseStep 2369555 = 3554333) B3554333
theorem B2664481 : Blo 1578487 2664481 := bstep (se 2 (by rfl) ⟨999180, by rfl⟩ : syracuseStep 2664481 = 1998361) B1998361
theorem B2369585 : Blo 1578487 2369585 := bstep (se 2 (by rfl) ⟨888594, by rfl⟩ : syracuseStep 2369585 = 1777189) B1777189
theorem B2664515 : Blo 1578487 2664515 := bstep (se 1 (by rfl) ⟨1998386, by rfl⟩ : syracuseStep 2664515 = 3996773) B3996773
theorem B4802627 : Blo 1578487 4802627 := bstep (se 1 (by rfl) ⟨3601970, by rfl⟩ : syracuseStep 4802627 = 7203941) B7203941
theorem B2369603 : Blo 1578487 2369603 := bstep (se 1 (by rfl) ⟨1777202, by rfl⟩ : syracuseStep 2369603 = 3554405) B3554405
theorem B2369633 : Blo 1578487 2369633 := bstep (se 2 (by rfl) ⟨888612, by rfl⟩ : syracuseStep 2369633 = 1777225) B1777225
theorem B2369651 : Blo 1578487 2369651 := bstep (se 1 (by rfl) ⟨1777238, by rfl⟩ : syracuseStep 2369651 = 3554477) B3554477
theorem B2369681 : Blo 1578487 2369681 := bstep (se 2 (by rfl) ⟨888630, by rfl⟩ : syracuseStep 2369681 = 1777261) B1777261
theorem B2369699 : Blo 1578487 2369699 := bstep (se 1 (by rfl) ⟨1777274, by rfl⟩ : syracuseStep 2369699 = 3554549) B3554549
theorem B4327597 : Blo 1578487 4327597 := bstep (se 3 (by rfl) ⟨811424, by rfl⟩ : syracuseStep 4327597 = 1622849) B1622849
theorem B2369729 : Blo 1578487 2369729 := bstep (se 2 (by rfl) ⟨888648, by rfl⟩ : syracuseStep 2369729 = 1777297) B1777297
theorem B2664643 : Blo 1578487 2664643 := bstep (se 1 (by rfl) ⟨1998482, by rfl⟩ : syracuseStep 2664643 = 3996965) B3996965
theorem B4499651 : Blo 1578487 4499651 := bstep (se 1 (by rfl) ⟨3374738, by rfl⟩ : syracuseStep 4499651 = 6749477) B6749477
theorem B2369747 : Blo 1578487 2369747 := bstep (se 1 (by rfl) ⟨1777310, by rfl⟩ : syracuseStep 2369747 = 3554621) B3554621
theorem B5998819 : Blo 1578487 5998819 := bstep (se 1 (by rfl) ⟨4499114, by rfl⟩ : syracuseStep 5998819 = 8998229) B8998229
theorem B2369777 : Blo 1578487 2369777 := bstep (se 2 (by rfl) ⟨888666, by rfl⟩ : syracuseStep 2369777 = 1777333) B1777333
theorem B2369795 : Blo 1578487 2369795 := bstep (se 1 (by rfl) ⟨1777346, by rfl⟩ : syracuseStep 2369795 = 3554693) B3554693
theorem B2369825 : Blo 1578487 2369825 := bstep (se 2 (by rfl) ⟨888684, by rfl⟩ : syracuseStep 2369825 = 1777369) B1777369
theorem B2369843 : Blo 1578487 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B2402627 : Blo 1578487 2402627 := bstep (se 1 (by rfl) ⟨1801970, by rfl⟩ : syracuseStep 2402627 = 3603941) B3603941
theorem B2664785 : Blo 1578487 2664785 := bstep (se 2 (by rfl) ⟨999294, by rfl⟩ : syracuseStep 2664785 = 1998589) B1998589
theorem B2369873 : Blo 1578487 2369873 := bstep (se 2 (by rfl) ⟨888702, by rfl⟩ : syracuseStep 2369873 = 1777405) B1777405
theorem B2369891 : Blo 1578487 2369891 := bstep (se 1 (by rfl) ⟨1777418, by rfl⟩ : syracuseStep 2369891 = 3554837) B3554837
theorem B2369921 : Blo 1578487 2369921 := bstep (se 2 (by rfl) ⟨888720, by rfl⟩ : syracuseStep 2369921 = 1777441) B1777441
theorem B2369939 : Blo 1578487 2369939 := bstep (se 1 (by rfl) ⟨1777454, by rfl⟩ : syracuseStep 2369939 = 3554909) B3554909
theorem B2369969 : Blo 1578487 2369969 := bstep (se 2 (by rfl) ⟨888738, by rfl⟩ : syracuseStep 2369969 = 1777477) B1777477
theorem B2369987 : Blo 1578487 2369987 := bstep (se 1 (by rfl) ⟨1777490, by rfl⟩ : syracuseStep 2369987 = 3554981) B3554981
theorem B51243461 : Blo 1578487 51243461 := bstep (se 4 (by rfl) ⟨4804074, by rfl⟩ : syracuseStep 51243461 = 9608149) B9608149
theorem B9611725 : Blo 1578487 9611725 := bstep (se 3 (by rfl) ⟨1802198, by rfl⟩ : syracuseStep 9611725 = 3604397) B3604397
theorem B2664913 : Blo 1578487 2664913 := bstep (se 2 (by rfl) ⟨999342, by rfl⟩ : syracuseStep 2664913 = 1998685) B1998685
theorem B2370017 : Blo 1578487 2370017 := bstep (se 2 (by rfl) ⟨888756, by rfl⟩ : syracuseStep 2370017 = 1777513) B1777513
theorem B15600113 : Blo 1578487 15600113 := bstep (se 2 (by rfl) ⟨5850042, by rfl⟩ : syracuseStep 15600113 = 11700085) B11700085
theorem B2664947 : Blo 1578487 2664947 := bstep (se 1 (by rfl) ⟨1998710, by rfl⟩ : syracuseStep 2664947 = 3997421) B3997421
theorem B2370035 : Blo 1578487 2370035 := bstep (se 1 (by rfl) ⟨1777526, by rfl⟩ : syracuseStep 2370035 = 3555053) B3555053
theorem B4499981 : Blo 1578487 4499981 := bstep (se 3 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 4499981 = 1687493) B1687493
theorem B2370065 : Blo 1578487 2370065 := bstep (se 2 (by rfl) ⟨888774, by rfl⟩ : syracuseStep 2370065 = 1777549) B1777549
theorem B2370083 : Blo 1578487 2370083 := bstep (se 1 (by rfl) ⟨1777562, by rfl⟩ : syracuseStep 2370083 = 3555125) B3555125
theorem B2370113 : Blo 1578487 2370113 := bstep (se 2 (by rfl) ⟨888792, by rfl⟩ : syracuseStep 2370113 = 1777585) B1777585
theorem B4500049 : Blo 1578487 4500049 := bstep (se 2 (by rfl) ⟨1687518, by rfl⟩ : syracuseStep 4500049 = 3375037) B3375037
theorem B2370131 : Blo 1578487 2370131 := bstep (se 1 (by rfl) ⟨1777598, by rfl⟩ : syracuseStep 2370131 = 3555197) B3555197
theorem B4000337 : Blo 1578487 4000337 := bstep (se 2 (by rfl) ⟨1500126, by rfl⟩ : syracuseStep 4000337 = 3000253) B3000253
theorem B13494883 : Blo 1578487 13494883 := bstep (se 1 (by rfl) ⟨10121162, by rfl⟩ : syracuseStep 13494883 = 20242325) B20242325
theorem B2370161 : Blo 1578487 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B2665075 : Blo 1578487 2665075 := bstep (se 1 (by rfl) ⟨1998806, by rfl⟩ : syracuseStep 2665075 = 3997613) B3997613
theorem B2370179 : Blo 1578487 2370179 := bstep (se 1 (by rfl) ⟨1777634, by rfl⟩ : syracuseStep 2370179 = 3555269) B3555269
theorem B4000387 : Blo 1578487 4000387 := bstep (se 1 (by rfl) ⟨3000290, by rfl⟩ : syracuseStep 4000387 = 6000581) B6000581
theorem B2370209 : Blo 1578487 2370209 := bstep (se 2 (by rfl) ⟨888828, by rfl⟩ : syracuseStep 2370209 = 1777657) B1777657
theorem B2370227 : Blo 1578487 2370227 := bstep (se 1 (by rfl) ⟨1777670, by rfl⟩ : syracuseStep 2370227 = 3555341) B3555341
theorem B2370257 : Blo 1578487 2370257 := bstep (se 2 (by rfl) ⟨888846, by rfl⟩ : syracuseStep 2370257 = 1777693) B1777693
theorem B4270819 : Blo 1578487 4270819 := bstep (se 1 (by rfl) ⟨3203114, by rfl⟩ : syracuseStep 4270819 = 6406229) B6406229
theorem B2370275 : Blo 1578487 2370275 := bstep (se 1 (by rfl) ⟨1777706, by rfl⟩ : syracuseStep 2370275 = 3555413) B3555413
theorem B2665217 : Blo 1578487 2665217 := bstep (se 2 (by rfl) ⟨999456, by rfl⟩ : syracuseStep 2665217 = 1998913) B1998913
theorem B2370305 : Blo 1578487 2370305 := bstep (se 2 (by rfl) ⟨888864, by rfl⟩ : syracuseStep 2370305 = 1777729) B1777729
theorem B6744845 : Blo 1578487 6744845 := bstep (se 3 (by rfl) ⟨1264658, by rfl⟩ : syracuseStep 6744845 = 2529317) B2529317
theorem B2370323 : Blo 1578487 2370323 := bstep (se 1 (by rfl) ⟨1777742, by rfl⟩ : syracuseStep 2370323 = 3555485) B3555485
theorem B4000529 : Blo 1578487 4000529 := bstep (se 2 (by rfl) ⟨1500198, by rfl⟩ : syracuseStep 4000529 = 3000397) B3000397
theorem B2370353 : Blo 1578487 2370353 := bstep (se 2 (by rfl) ⟨888882, by rfl⟩ : syracuseStep 2370353 = 1777765) B1777765
theorem B20245301 : Blo 1578487 20245301 := bstep (se 5 (by rfl) ⟨948998, by rfl⟩ : syracuseStep 20245301 = 1897997) B1897997
theorem B2886467 : Blo 1578487 2886467 := bstep (se 1 (by rfl) ⟨2164850, by rfl⟩ : syracuseStep 2886467 = 4329701) B4329701
theorem B2370371 : Blo 1578487 2370371 := bstep (se 1 (by rfl) ⟨1777778, by rfl⟩ : syracuseStep 2370371 = 3555557) B3555557
theorem B5327693 : Blo 1578487 5327693 := bstep (se 3 (by rfl) ⟨998942, by rfl⟩ : syracuseStep 5327693 = 1997885) B1997885
theorem B2370401 : Blo 1578487 2370401 := bstep (se 2 (by rfl) ⟨888900, by rfl⟩ : syracuseStep 2370401 = 1777801) B1777801
theorem B4500323 : Blo 1578487 4500323 := bstep (se 1 (by rfl) ⟨3375242, by rfl⟩ : syracuseStep 4500323 = 6750485) B6750485
theorem B2370419 : Blo 1578487 2370419 := bstep (se 1 (by rfl) ⟨1777814, by rfl⟩ : syracuseStep 2370419 = 3555629) B3555629
theorem B2665345 : Blo 1578487 2665345 := bstep (se 2 (by rfl) ⟨999504, by rfl⟩ : syracuseStep 2665345 = 1999009) B1999009
theorem B5327747 : Blo 1578487 5327747 := bstep (se 1 (by rfl) ⟨3995810, by rfl⟩ : syracuseStep 5327747 = 7991621) B7991621
theorem B2370449 : Blo 1578487 2370449 := bstep (se 2 (by rfl) ⟨888918, by rfl⟩ : syracuseStep 2370449 = 1777837) B1777837
theorem B2665379 : Blo 1578487 2665379 := bstep (se 1 (by rfl) ⟨1999034, by rfl⟩ : syracuseStep 2665379 = 3998069) B3998069
theorem B2370467 : Blo 1578487 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B2370497 : Blo 1578487 2370497 := bstep (se 2 (by rfl) ⟨888936, by rfl⟩ : syracuseStep 2370497 = 1777873) B1777873
theorem B2370515 : Blo 1578487 2370515 := bstep (se 1 (by rfl) ⟨1777886, by rfl⟩ : syracuseStep 2370515 = 3555773) B3555773
theorem B17542129 : Blo 1578487 17542129 := bstep (se 2 (by rfl) ⟨6578298, by rfl⟩ : syracuseStep 17542129 = 13156597) B13156597
theorem B2370545 : Blo 1578487 2370545 := bstep (se 2 (by rfl) ⟨888954, by rfl⟩ : syracuseStep 2370545 = 1777909) B1777909
theorem B2370563 : Blo 1578487 2370563 := bstep (se 1 (by rfl) ⟨1777922, by rfl⟩ : syracuseStep 2370563 = 3555845) B3555845
theorem B2370593 : Blo 1578487 2370593 := bstep (se 2 (by rfl) ⟨888972, by rfl⟩ : syracuseStep 2370593 = 1777945) B1777945
theorem B2665507 : Blo 1578487 2665507 := bstep (se 1 (by rfl) ⟨1999130, by rfl⟩ : syracuseStep 2665507 = 3998261) B3998261
theorem B10120241 : Blo 1578487 10120241 := bstep (se 2 (by rfl) ⟨3795090, by rfl⟩ : syracuseStep 10120241 = 7590181) B7590181
theorem B2370611 : Blo 1578487 2370611 := bstep (se 1 (by rfl) ⟨1777958, by rfl⟩ : syracuseStep 2370611 = 3555917) B3555917
theorem B2370641 : Blo 1578487 2370641 := bstep (se 2 (by rfl) ⟨888990, by rfl⟩ : syracuseStep 2370641 = 1777981) B1777981
theorem B5057635 : Blo 1578487 5057635 := bstep (se 1 (by rfl) ⟨3793226, by rfl⟩ : syracuseStep 5057635 = 7586453) B7586453
theorem B6745187 : Blo 1578487 6745187 := bstep (se 1 (by rfl) ⟨5058890, by rfl⟩ : syracuseStep 6745187 = 10117781) B10117781
theorem B2370659 : Blo 1578487 2370659 := bstep (se 1 (by rfl) ⟨1777994, by rfl⟩ : syracuseStep 2370659 = 3555989) B3555989
theorem B2370689 : Blo 1578487 2370689 := bstep (se 2 (by rfl) ⟨889008, by rfl⟩ : syracuseStep 2370689 = 1778017) B1778017
theorem B5328017 : Blo 1578487 5328017 := bstep (se 2 (by rfl) ⟨1998006, by rfl⟩ : syracuseStep 5328017 = 3996013) B3996013
theorem B2370707 : Blo 1578487 2370707 := bstep (se 1 (by rfl) ⟨1778030, by rfl⟩ : syracuseStep 2370707 = 3556061) B3556061
theorem B7589027 : Blo 1578487 7589027 := bstep (se 1 (by rfl) ⟨5691770, by rfl⟩ : syracuseStep 7589027 = 11383541) B11383541
theorem B2665649 : Blo 1578487 2665649 := bstep (se 2 (by rfl) ⟨999618, by rfl⟩ : syracuseStep 2665649 = 1999237) B1999237
theorem B2845937 : Blo 1578487 2845937 := bstep (se 2 (by rfl) ⟨1067226, by rfl⟩ : syracuseStep 2845937 = 2134453) B2134453
theorem B2665777 : Blo 1578487 2665777 := bstep (se 2 (by rfl) ⟨999666, by rfl⟩ : syracuseStep 2665777 = 1999333) B1999333
theorem B2248003 : Blo 1578487 2248003 := bstep (se 1 (by rfl) ⟨1686002, by rfl⟩ : syracuseStep 2248003 = 3372005) B3372005
theorem B3419473 : Blo 1578487 3419473 := bstep (se 2 (by rfl) ⟨1282302, by rfl⟩ : syracuseStep 3419473 = 2564605) B2564605
theorem B2665811 : Blo 1578487 2665811 := bstep (se 1 (by rfl) ⟨1999358, by rfl⟩ : syracuseStep 2665811 = 3998717) B3998717
theorem B34614641 : Blo 1578487 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B2665939 : Blo 1578487 2665939 := bstep (se 1 (by rfl) ⟨1999454, by rfl⟩ : syracuseStep 2665939 = 3998909) B3998909
theorem B2666081 : Blo 1578487 2666081 := bstep (se 2 (by rfl) ⟨999780, by rfl⟩ : syracuseStep 2666081 = 1999561) B1999561
theorem B2248339 : Blo 1578487 2248339 := bstep (se 1 (by rfl) ⟨1686254, by rfl⟩ : syracuseStep 2248339 = 3372509) B3372509
theorem B5328557 : Blo 1578487 5328557 := bstep (se 3 (by rfl) ⟨999104, by rfl⟩ : syracuseStep 5328557 = 1998209) B1998209
theorem B9875141 : Blo 1578487 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B2666209 : Blo 1578487 2666209 := bstep (se 2 (by rfl) ⟨999828, by rfl⟩ : syracuseStep 2666209 = 1999657) B1999657
theorem B5328611 : Blo 1578487 5328611 := bstep (se 1 (by rfl) ⟨3996458, by rfl⟩ : syracuseStep 5328611 = 7992917) B7992917
theorem B2666243 : Blo 1578487 2666243 := bstep (se 1 (by rfl) ⟨1999682, by rfl⟩ : syracuseStep 2666243 = 3999365) B3999365
theorem B2666371 : Blo 1578487 2666371 := bstep (se 1 (by rfl) ⟨1999778, by rfl⟩ : syracuseStep 2666371 = 3999557) B3999557
theorem B5771213 : Blo 1578487 5771213 := bstep (se 3 (by rfl) ⟨1082102, by rfl⟩ : syracuseStep 5771213 = 2164205) B2164205
theorem B5328881 : Blo 1578487 5328881 := bstep (se 2 (by rfl) ⟨1998330, by rfl⟩ : syracuseStep 5328881 = 3996661) B3996661
theorem B2666513 : Blo 1578487 2666513 := bstep (se 2 (by rfl) ⟨999942, by rfl⟩ : syracuseStep 2666513 = 1999885) B1999885
theorem B5689379 : Blo 1578487 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B4165681 : Blo 1578487 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B2027587 : Blo 1578487 2027587 := bstep (se 1 (by rfl) ⟨1520690, by rfl⟩ : syracuseStep 2027587 = 3041381) B3041381
theorem B4804721 : Blo 1578487 4804721 := bstep (se 2 (by rfl) ⟨1801770, by rfl⟩ : syracuseStep 4804721 = 3603541) B3603541
theorem B11989133 : Blo 1578487 11989133 := bstep (se 3 (by rfl) ⟨2247962, by rfl⟩ : syracuseStep 11989133 = 4495925) B4495925
theorem B2666641 : Blo 1578487 2666641 := bstep (se 2 (by rfl) ⟨999990, by rfl⟩ : syracuseStep 2666641 = 1999981) B1999981
theorem B7991459 : Blo 1578487 7991459 := bstep (se 1 (by rfl) ⟨5993594, by rfl⟩ : syracuseStep 7991459 = 11987189) B11987189
theorem B5058737 : Blo 1578487 5058737 := bstep (se 2 (by rfl) ⟨1897026, by rfl⟩ : syracuseStep 5058737 = 3794053) B3794053
theorem B2134193 : Blo 1578487 2134193 := bstep (se 2 (by rfl) ⟨800322, by rfl⟩ : syracuseStep 2134193 = 1600645) B1600645
theorem B2666675 : Blo 1578487 2666675 := bstep (se 1 (by rfl) ⟨2000006, by rfl⟩ : syracuseStep 2666675 = 4000013) B4000013
theorem B2248897 : Blo 1578487 2248897 := bstep (se 2 (by rfl) ⟨843336, by rfl⟩ : syracuseStep 2248897 = 1686673) B1686673
theorem B2248931 : Blo 1578487 2248931 := bstep (se 1 (by rfl) ⟨1686698, by rfl⟩ : syracuseStep 2248931 = 3373397) B3373397
theorem B5058865 : Blo 1578487 5058865 := bstep (se 2 (by rfl) ⟨1897074, by rfl⟩ : syracuseStep 5058865 = 3794149) B3794149
theorem B2666803 : Blo 1578487 2666803 := bstep (se 1 (by rfl) ⟨2000102, by rfl⟩ : syracuseStep 2666803 = 4000205) B4000205
theorem B3551633 : Blo 1578487 3551633 := bstep (se 2 (by rfl) ⟨1331862, by rfl⟩ : syracuseStep 3551633 = 2663725) B2663725
theorem B3551651 : Blo 1578487 3551651 := bstep (se 1 (by rfl) ⟨2663738, by rfl⟩ : syracuseStep 3551651 = 5327477) B5327477
theorem B2666945 : Blo 1578487 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B5329421 : Blo 1578487 5329421 := bstep (se 3 (by rfl) ⟨999266, by rfl⟩ : syracuseStep 5329421 = 1998533) B1998533
theorem B2667073 : Blo 1578487 2667073 := bstep (se 2 (by rfl) ⟨1000152, by rfl⟩ : syracuseStep 2667073 = 2000305) B2000305
theorem B5329475 : Blo 1578487 5329475 := bstep (se 1 (by rfl) ⟨3997106, by rfl⟩ : syracuseStep 5329475 = 7994213) B7994213
theorem B8991395 : Blo 1578487 8991395 := bstep (se 1 (by rfl) ⟨6743546, by rfl⟩ : syracuseStep 8991395 = 13487093) B13487093
theorem B3551921 : Blo 1578487 3551921 := bstep (se 2 (by rfl) ⟨1331970, by rfl⟩ : syracuseStep 3551921 = 2663941) B2663941
theorem B3551939 : Blo 1578487 3551939 := bstep (se 1 (by rfl) ⟨2663954, by rfl⟩ : syracuseStep 3551939 = 5327909) B5327909
theorem B1897219 : Blo 1578487 1897219 := bstep (se 1 (by rfl) ⟨1422914, by rfl⟩ : syracuseStep 1897219 = 2845829) B2845829
theorem B2249489 : Blo 1578487 2249489 := bstep (se 2 (by rfl) ⟨843558, by rfl⟩ : syracuseStep 2249489 = 1687117) B1687117
theorem B5329745 : Blo 1578487 5329745 := bstep (se 2 (by rfl) ⟨1998654, by rfl⟩ : syracuseStep 5329745 = 3997309) B3997309
theorem B2249569 : Blo 1578487 2249569 := bstep (se 2 (by rfl) ⟨843588, by rfl⟩ : syracuseStep 2249569 = 1687177) B1687177
theorem B8000369 : Blo 1578487 8000369 := bstep (se 2 (by rfl) ⟨3000138, by rfl⟩ : syracuseStep 8000369 = 6000277) B6000277
theorem B7590797 : Blo 1578487 7590797 := bstep (se 3 (by rfl) ⟨1423274, by rfl⟩ : syracuseStep 7590797 = 2846549) B2846549
theorem B1897411 : Blo 1578487 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B7992269 : Blo 1578487 7992269 := bstep (se 3 (by rfl) ⟨1498550, by rfl⟩ : syracuseStep 7992269 = 2997101) B2997101
theorem B3552209 : Blo 1578487 3552209 := bstep (se 2 (by rfl) ⟨1332078, by rfl⟩ : syracuseStep 3552209 = 2664157) B2664157
theorem B3552227 : Blo 1578487 3552227 := bstep (se 1 (by rfl) ⟨2664170, by rfl⟩ : syracuseStep 3552227 = 5328341) B5328341
theorem B145814741 : Blo 1578487 145814741 := bstep (se 7 (by rfl) ⟨1708766, by rfl⟩ : syracuseStep 145814741 = 3417533) B3417533
theorem B2528497 : Blo 1578487 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B3552497 : Blo 1578487 3552497 := bstep (se 2 (by rfl) ⟨1332186, by rfl⟩ : syracuseStep 3552497 = 2664373) B2664373
theorem B3552515 : Blo 1578487 3552515 := bstep (se 1 (by rfl) ⟨2664386, by rfl⟩ : syracuseStep 3552515 = 5328773) B5328773
theorem B4560131 : Blo 1578487 4560131 := bstep (se 1 (by rfl) ⟨3420098, by rfl⟩ : syracuseStep 4560131 = 6840197) B6840197
theorem B5059853 : Blo 1578487 5059853 := bstep (se 3 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 5059853 = 1897445) B1897445
theorem B5993777 : Blo 1578487 5993777 := bstep (se 2 (by rfl) ⟨2247666, by rfl⟩ : syracuseStep 5993777 = 4495333) B4495333
theorem B1897795 : Blo 1578487 1897795 := bstep (se 1 (by rfl) ⟨1423346, by rfl⟩ : syracuseStep 1897795 = 2846693) B2846693
theorem B5330285 : Blo 1578487 5330285 := bstep (se 3 (by rfl) ⟨999428, by rfl⟩ : syracuseStep 5330285 = 1998857) B1998857
theorem B5330339 : Blo 1578487 5330339 := bstep (se 1 (by rfl) ⟨3997754, by rfl⟩ : syracuseStep 5330339 = 7995509) B7995509
theorem B17315299 : Blo 1578487 17315299 := bstep (se 1 (by rfl) ⟨12986474, by rfl⟩ : syracuseStep 17315299 = 25972949) B25972949
theorem B2528753 : Blo 1578487 2528753 := bstep (se 2 (by rfl) ⟨948282, by rfl⟩ : syracuseStep 2528753 = 1896565) B1896565
theorem B1578499 : Blo 1578487 1578499 := bstep (se 1 (by rfl) ⟨1183874, by rfl⟩ : syracuseStep 1578499 = 2367749) B2367749
theorem B3552785 : Blo 1578487 3552785 := bstep (se 2 (by rfl) ⟨1332294, by rfl⟩ : syracuseStep 3552785 = 2664589) B2664589
theorem B1578515 : Blo 1578487 1578515 := bstep (se 1 (by rfl) ⟨1183886, by rfl⟩ : syracuseStep 1578515 = 2367773) B2367773
theorem B1578531 : Blo 1578487 1578531 := bstep (se 1 (by rfl) ⟨1183898, by rfl⟩ : syracuseStep 1578531 = 2367797) B2367797
theorem B3552803 : Blo 1578487 3552803 := bstep (se 1 (by rfl) ⟨2664602, by rfl⟩ : syracuseStep 3552803 = 5329205) B5329205
theorem B1578547 : Blo 1578487 1578547 := bstep (se 1 (by rfl) ⟨1183910, by rfl⟩ : syracuseStep 1578547 = 2367821) B2367821
theorem B1578563 : Blo 1578487 1578563 := bstep (se 1 (by rfl) ⟨1183922, by rfl⟩ : syracuseStep 1578563 = 2367845) B2367845
theorem B1578579 : Blo 1578487 1578579 := bstep (se 1 (by rfl) ⟨1183934, by rfl⟩ : syracuseStep 1578579 = 2367869) B2367869
theorem B1578595 : Blo 1578487 1578595 := bstep (se 1 (by rfl) ⟨1183946, by rfl⟩ : syracuseStep 1578595 = 2367893) B2367893
theorem B1578611 : Blo 1578487 1578611 := bstep (se 1 (by rfl) ⟨1183958, by rfl⟩ : syracuseStep 1578611 = 2367917) B2367917
theorem B1578627 : Blo 1578487 1578627 := bstep (se 1 (by rfl) ⟨1183970, by rfl⟩ : syracuseStep 1578627 = 2367941) B2367941
theorem B8992397 : Blo 1578487 8992397 := bstep (se 3 (by rfl) ⟨1686074, by rfl⟩ : syracuseStep 8992397 = 3372149) B3372149
theorem B1578643 : Blo 1578487 1578643 := bstep (se 1 (by rfl) ⟨1183982, by rfl⟩ : syracuseStep 1578643 = 2367965) B2367965
theorem B1578659 : Blo 1578487 1578659 := bstep (se 1 (by rfl) ⟨1183994, by rfl⟩ : syracuseStep 1578659 = 2367989) B2367989
theorem B5330609 : Blo 1578487 5330609 := bstep (se 2 (by rfl) ⟨1998978, by rfl⟩ : syracuseStep 5330609 = 3997957) B3997957
theorem B1578675 : Blo 1578487 1578675 := bstep (se 1 (by rfl) ⟨1184006, by rfl⟩ : syracuseStep 1578675 = 2368013) B2368013
theorem B1578691 : Blo 1578487 1578691 := bstep (se 1 (by rfl) ⟨1184018, by rfl⟩ : syracuseStep 1578691 = 2368037) B2368037
theorem B1578707 : Blo 1578487 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B1578723 : Blo 1578487 1578723 := bstep (se 1 (by rfl) ⟨1184042, by rfl⟩ : syracuseStep 1578723 = 2368085) B2368085
theorem B1578739 : Blo 1578487 1578739 := bstep (se 1 (by rfl) ⟨1184054, by rfl⟩ : syracuseStep 1578739 = 2368109) B2368109
theorem B1578755 : Blo 1578487 1578755 := bstep (se 1 (by rfl) ⟨1184066, by rfl⟩ : syracuseStep 1578755 = 2368133) B2368133
theorem B8533765 : Blo 1578487 8533765 := bstep (se 4 (by rfl) ⟨800040, by rfl⟩ : syracuseStep 8533765 = 1600081) B1600081
theorem B1578771 : Blo 1578487 1578771 := bstep (se 1 (by rfl) ⟨1184078, by rfl⟩ : syracuseStep 1578771 = 2368157) B2368157
theorem B1578787 : Blo 1578487 1578787 := bstep (se 1 (by rfl) ⟨1184090, by rfl⟩ : syracuseStep 1578787 = 2368181) B2368181
theorem B3553073 : Blo 1578487 3553073 := bstep (se 2 (by rfl) ⟨1332402, by rfl⟩ : syracuseStep 3553073 = 2664805) B2664805
theorem B1578803 : Blo 1578487 1578803 := bstep (se 1 (by rfl) ⟨1184102, by rfl⟩ : syracuseStep 1578803 = 2368205) B2368205
theorem B1578819 : Blo 1578487 1578819 := bstep (se 1 (by rfl) ⟨1184114, by rfl⟩ : syracuseStep 1578819 = 2368229) B2368229
theorem B3553091 : Blo 1578487 3553091 := bstep (se 1 (by rfl) ⟨2664818, by rfl⟩ : syracuseStep 3553091 = 5329637) B5329637
theorem B1578835 : Blo 1578487 1578835 := bstep (se 1 (by rfl) ⟨1184126, by rfl⟩ : syracuseStep 1578835 = 2368253) B2368253
theorem B1578851 : Blo 1578487 1578851 := bstep (se 1 (by rfl) ⟨1184138, by rfl⟩ : syracuseStep 1578851 = 2368277) B2368277
theorem B4388707 : Blo 1578487 4388707 := bstep (se 1 (by rfl) ⟨3291530, by rfl⟩ : syracuseStep 4388707 = 6583061) B6583061
theorem B1578867 : Blo 1578487 1578867 := bstep (se 1 (by rfl) ⟨1184150, by rfl⟩ : syracuseStep 1578867 = 2368301) B2368301
theorem B1578883 : Blo 1578487 1578883 := bstep (se 1 (by rfl) ⟨1184162, by rfl⟩ : syracuseStep 1578883 = 2368325) B2368325
theorem B1578899 : Blo 1578487 1578899 := bstep (se 1 (by rfl) ⟨1184174, by rfl⟩ : syracuseStep 1578899 = 2368349) B2368349
theorem B1578915 : Blo 1578487 1578915 := bstep (se 1 (by rfl) ⟨1184186, by rfl⟩ : syracuseStep 1578915 = 2368373) B2368373
theorem B4495277 : Blo 1578487 4495277 := bstep (se 3 (by rfl) ⟨842864, by rfl⟩ : syracuseStep 4495277 = 1685729) B1685729
theorem B1578931 : Blo 1578487 1578931 := bstep (se 1 (by rfl) ⟨1184198, by rfl⟩ : syracuseStep 1578931 = 2368397) B2368397
theorem B1578947 : Blo 1578487 1578947 := bstep (se 1 (by rfl) ⟨1184210, by rfl⟩ : syracuseStep 1578947 = 2368421) B2368421
theorem B5994445 : Blo 1578487 5994445 := bstep (se 3 (by rfl) ⟨1123958, by rfl⟩ : syracuseStep 5994445 = 2247917) B2247917
theorem B10123213 : Blo 1578487 10123213 := bstep (se 3 (by rfl) ⟨1898102, by rfl⟩ : syracuseStep 10123213 = 3796205) B3796205
theorem B1578963 : Blo 1578487 1578963 := bstep (se 1 (by rfl) ⟨1184222, by rfl⟩ : syracuseStep 1578963 = 2368445) B2368445
theorem B1578979 : Blo 1578487 1578979 := bstep (se 1 (by rfl) ⟨1184234, by rfl⟩ : syracuseStep 1578979 = 2368469) B2368469
theorem B1578995 : Blo 1578487 1578995 := bstep (se 1 (by rfl) ⟨1184246, by rfl⟩ : syracuseStep 1578995 = 2368493) B2368493
theorem B1898483 : Blo 1578487 1898483 := bstep (se 1 (by rfl) ⟨1423862, by rfl⟩ : syracuseStep 1898483 = 2847725) B2847725
theorem B1579011 : Blo 1578487 1579011 := bstep (se 1 (by rfl) ⟨1184258, by rfl⟩ : syracuseStep 1579011 = 2368517) B2368517
theorem B1579027 : Blo 1578487 1579027 := bstep (se 1 (by rfl) ⟨1184270, by rfl⟩ : syracuseStep 1579027 = 2368541) B2368541
theorem B1579043 : Blo 1578487 1579043 := bstep (se 1 (by rfl) ⟨1184282, by rfl⟩ : syracuseStep 1579043 = 2368565) B2368565
theorem B1579059 : Blo 1578487 1579059 := bstep (se 1 (by rfl) ⟨1184294, by rfl⟩ : syracuseStep 1579059 = 2368589) B2368589
theorem B2701363 : Blo 1578487 2701363 := bstep (se 1 (by rfl) ⟨2026022, by rfl⟩ : syracuseStep 2701363 = 4052045) B4052045
theorem B1579075 : Blo 1578487 1579075 := bstep (se 1 (by rfl) ⟨1184306, by rfl⟩ : syracuseStep 1579075 = 2368613) B2368613
theorem B3553361 : Blo 1578487 3553361 := bstep (se 2 (by rfl) ⟨1332510, by rfl⟩ : syracuseStep 3553361 = 2665021) B2665021
theorem B1579091 : Blo 1578487 1579091 := bstep (se 1 (by rfl) ⟨1184318, by rfl⟩ : syracuseStep 1579091 = 2368637) B2368637
theorem B4495459 : Blo 1578487 4495459 := bstep (se 1 (by rfl) ⟨3371594, by rfl⟩ : syracuseStep 4495459 = 6743189) B6743189
theorem B1579107 : Blo 1578487 1579107 := bstep (se 1 (by rfl) ⟨1184330, by rfl⟩ : syracuseStep 1579107 = 2368661) B2368661
theorem B3553379 : Blo 1578487 3553379 := bstep (se 1 (by rfl) ⟨2665034, by rfl⟩ : syracuseStep 3553379 = 5330069) B5330069
theorem B21616753 : Blo 1578487 21616753 := bstep (se 2 (by rfl) ⟨8106282, by rfl⟩ : syracuseStep 21616753 = 16212565) B16212565
theorem B1579123 : Blo 1578487 1579123 := bstep (se 1 (by rfl) ⟨1184342, by rfl⟩ : syracuseStep 1579123 = 2368685) B2368685
theorem B1579139 : Blo 1578487 1579139 := bstep (se 1 (by rfl) ⟨1184354, by rfl⟩ : syracuseStep 1579139 = 2368709) B2368709
theorem B1579155 : Blo 1578487 1579155 := bstep (se 1 (by rfl) ⟨1184366, by rfl⟩ : syracuseStep 1579155 = 2368733) B2368733
theorem B1579171 : Blo 1578487 1579171 := bstep (se 1 (by rfl) ⟨1184378, by rfl⟩ : syracuseStep 1579171 = 2368757) B2368757
theorem B1579187 : Blo 1578487 1579187 := bstep (se 1 (by rfl) ⟨1184390, by rfl⟩ : syracuseStep 1579187 = 2368781) B2368781
theorem B1579203 : Blo 1578487 1579203 := bstep (se 1 (by rfl) ⟨1184402, by rfl⟩ : syracuseStep 1579203 = 2368805) B2368805
theorem B5331149 : Blo 1578487 5331149 := bstep (se 3 (by rfl) ⟨999590, by rfl⟩ : syracuseStep 5331149 = 1999181) B1999181
theorem B9607373 : Blo 1578487 9607373 := bstep (se 3 (by rfl) ⟨1801382, by rfl⟩ : syracuseStep 9607373 = 3602765) B3602765
theorem B1579219 : Blo 1578487 1579219 := bstep (se 1 (by rfl) ⟨1184414, by rfl⟩ : syracuseStep 1579219 = 2368829) B2368829
theorem B1579235 : Blo 1578487 1579235 := bstep (se 1 (by rfl) ⟨1184426, by rfl⟩ : syracuseStep 1579235 = 2368853) B2368853
theorem B1579251 : Blo 1578487 1579251 := bstep (se 1 (by rfl) ⟨1184438, by rfl⟩ : syracuseStep 1579251 = 2368877) B2368877
theorem B1775875 : Blo 1578487 1775875 := bstep (se 1 (by rfl) ⟨1331906, by rfl⟩ : syracuseStep 1775875 = 2663813) B2663813
theorem B1579267 : Blo 1578487 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B5331203 : Blo 1578487 5331203 := bstep (se 1 (by rfl) ⟨3998402, by rfl⟩ : syracuseStep 5331203 = 7996805) B7996805
theorem B1579283 : Blo 1578487 1579283 := bstep (se 1 (by rfl) ⟨1184462, by rfl⟩ : syracuseStep 1579283 = 2368925) B2368925
theorem B1579299 : Blo 1578487 1579299 := bstep (se 1 (by rfl) ⟨1184474, by rfl⟩ : syracuseStep 1579299 = 2368949) B2368949
theorem B1579315 : Blo 1578487 1579315 := bstep (se 1 (by rfl) ⟨1184486, by rfl⟩ : syracuseStep 1579315 = 2368973) B2368973
theorem B1579331 : Blo 1578487 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B11385157 : Blo 1578487 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B1579347 : Blo 1578487 1579347 := bstep (se 1 (by rfl) ⟨1184510, by rfl⟩ : syracuseStep 1579347 = 2369021) B2369021
theorem B1579363 : Blo 1578487 1579363 := bstep (se 1 (by rfl) ⟨1184522, by rfl⟩ : syracuseStep 1579363 = 2369045) B2369045
theorem B3553649 : Blo 1578487 3553649 := bstep (se 2 (by rfl) ⟨1332618, by rfl⟩ : syracuseStep 3553649 = 2665237) B2665237
theorem B1579379 : Blo 1578487 1579379 := bstep (se 1 (by rfl) ⟨1184534, by rfl⟩ : syracuseStep 1579379 = 2369069) B2369069
theorem B1579395 : Blo 1578487 1579395 := bstep (se 1 (by rfl) ⟨1184546, by rfl⟩ : syracuseStep 1579395 = 2369093) B2369093
theorem B3553667 : Blo 1578487 3553667 := bstep (se 1 (by rfl) ⟨2665250, by rfl⟩ : syracuseStep 3553667 = 5330501) B5330501
theorem B1776019 : Blo 1578487 1776019 := bstep (se 1 (by rfl) ⟨1332014, by rfl⟩ : syracuseStep 1776019 = 2664029) B2664029
theorem B1579411 : Blo 1578487 1579411 := bstep (se 1 (by rfl) ⟨1184558, by rfl⟩ : syracuseStep 1579411 = 2369117) B2369117
theorem B1825187 : Blo 1578487 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B1579427 : Blo 1578487 1579427 := bstep (se 1 (by rfl) ⟨1184570, by rfl⟩ : syracuseStep 1579427 = 2369141) B2369141
theorem B1579443 : Blo 1578487 1579443 := bstep (se 1 (by rfl) ⟨1184582, by rfl⟩ : syracuseStep 1579443 = 2369165) B2369165
theorem B1579459 : Blo 1578487 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B1579475 : Blo 1578487 1579475 := bstep (se 1 (by rfl) ⟨1184606, by rfl⟩ : syracuseStep 1579475 = 2369213) B2369213
theorem B1579491 : Blo 1578487 1579491 := bstep (se 1 (by rfl) ⟨1184618, by rfl⟩ : syracuseStep 1579491 = 2369237) B2369237
theorem B1579507 : Blo 1578487 1579507 := bstep (se 1 (by rfl) ⟨1184630, by rfl⟩ : syracuseStep 1579507 = 2369261) B2369261
theorem B1579523 : Blo 1578487 1579523 := bstep (se 1 (by rfl) ⟨1184642, by rfl⟩ : syracuseStep 1579523 = 2369285) B2369285
theorem B5331473 : Blo 1578487 5331473 := bstep (se 2 (by rfl) ⟨1999302, by rfl⟩ : syracuseStep 5331473 = 3998605) B3998605
theorem B1579539 : Blo 1578487 1579539 := bstep (se 1 (by rfl) ⟨1184654, by rfl⟩ : syracuseStep 1579539 = 2369309) B2369309
theorem B1776163 : Blo 1578487 1776163 := bstep (se 1 (by rfl) ⟨1332122, by rfl⟩ : syracuseStep 1776163 = 2664245) B2664245
theorem B1579555 : Blo 1578487 1579555 := bstep (se 1 (by rfl) ⟨1184666, by rfl⟩ : syracuseStep 1579555 = 2369333) B2369333
theorem B1579571 : Blo 1578487 1579571 := bstep (se 1 (by rfl) ⟨1184678, by rfl⟩ : syracuseStep 1579571 = 2369357) B2369357
theorem B1579587 : Blo 1578487 1579587 := bstep (se 1 (by rfl) ⟨1184690, by rfl⟩ : syracuseStep 1579587 = 2369381) B2369381
theorem B4495949 : Blo 1578487 4495949 := bstep (se 3 (by rfl) ⟨842990, by rfl⟩ : syracuseStep 4495949 = 1685981) B1685981
theorem B5061197 : Blo 1578487 5061197 := bstep (se 3 (by rfl) ⟨948974, by rfl⟩ : syracuseStep 5061197 = 1897949) B1897949
theorem B1579603 : Blo 1578487 1579603 := bstep (se 1 (by rfl) ⟨1184702, by rfl⟩ : syracuseStep 1579603 = 2369405) B2369405
theorem B1579619 : Blo 1578487 1579619 := bstep (se 1 (by rfl) ⟨1184714, by rfl⟩ : syracuseStep 1579619 = 2369429) B2369429
theorem B1579635 : Blo 1578487 1579635 := bstep (se 1 (by rfl) ⟨1184726, by rfl⟩ : syracuseStep 1579635 = 2369453) B2369453
theorem B1579651 : Blo 1578487 1579651 := bstep (se 1 (by rfl) ⟨1184738, by rfl⟩ : syracuseStep 1579651 = 2369477) B2369477
theorem B3553937 : Blo 1578487 3553937 := bstep (se 2 (by rfl) ⟨1332726, by rfl⟩ : syracuseStep 3553937 = 2665453) B2665453
theorem B1579667 : Blo 1578487 1579667 := bstep (se 1 (by rfl) ⟨1184750, by rfl⟩ : syracuseStep 1579667 = 2369501) B2369501
theorem B3553955 : Blo 1578487 3553955 := bstep (se 1 (by rfl) ⟨2665466, by rfl⟩ : syracuseStep 3553955 = 5330933) B5330933
theorem B1579683 : Blo 1578487 1579683 := bstep (se 1 (by rfl) ⟨1184762, by rfl⟩ : syracuseStep 1579683 = 2369525) B2369525
theorem B3996337 : Blo 1578487 3996337 := bstep (se 2 (by rfl) ⟨1498626, by rfl⟩ : syracuseStep 3996337 = 2997253) B2997253
theorem B1776307 : Blo 1578487 1776307 := bstep (se 1 (by rfl) ⟨1332230, by rfl⟩ : syracuseStep 1776307 = 2664461) B2664461
theorem B1579699 : Blo 1578487 1579699 := bstep (se 1 (by rfl) ⟨1184774, by rfl⟩ : syracuseStep 1579699 = 2369549) B2369549
theorem B1579715 : Blo 1578487 1579715 := bstep (se 1 (by rfl) ⟨1184786, by rfl⟩ : syracuseStep 1579715 = 2369573) B2369573
theorem B10803917 : Blo 1578487 10803917 := bstep (se 3 (by rfl) ⟨2025734, by rfl⟩ : syracuseStep 10803917 = 4051469) B4051469
theorem B1579731 : Blo 1578487 1579731 := bstep (se 1 (by rfl) ⟨1184798, by rfl⟩ : syracuseStep 1579731 = 2369597) B2369597
theorem B5995235 : Blo 1578487 5995235 := bstep (se 1 (by rfl) ⟨4496426, by rfl⟩ : syracuseStep 5995235 = 8992853) B8992853
theorem B1579747 : Blo 1578487 1579747 := bstep (se 1 (by rfl) ⟨1184810, by rfl⟩ : syracuseStep 1579747 = 2369621) B2369621
theorem B1579763 : Blo 1578487 1579763 := bstep (se 1 (by rfl) ⟨1184822, by rfl⟩ : syracuseStep 1579763 = 2369645) B2369645
theorem B2996995 : Blo 1578487 2996995 := bstep (se 1 (by rfl) ⟨2247746, by rfl⟩ : syracuseStep 2996995 = 4495493) B4495493
theorem B1579779 : Blo 1578487 1579779 := bstep (se 1 (by rfl) ⟨1184834, by rfl⟩ : syracuseStep 1579779 = 2369669) B2369669
theorem B1579795 : Blo 1578487 1579795 := bstep (se 1 (by rfl) ⟨1184846, by rfl⟩ : syracuseStep 1579795 = 2369693) B2369693
theorem B1579811 : Blo 1578487 1579811 := bstep (se 1 (by rfl) ⟨1184858, by rfl⟩ : syracuseStep 1579811 = 2369717) B2369717
theorem B1579827 : Blo 1578487 1579827 := bstep (se 1 (by rfl) ⟨1184870, by rfl⟩ : syracuseStep 1579827 = 2369741) B2369741
theorem B1776451 : Blo 1578487 1776451 := bstep (se 1 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 1776451 = 2664677) B2664677
theorem B1579843 : Blo 1578487 1579843 := bstep (se 1 (by rfl) ⟨1184882, by rfl⟩ : syracuseStep 1579843 = 2369765) B2369765
theorem B1579859 : Blo 1578487 1579859 := bstep (se 1 (by rfl) ⟨1184894, by rfl⟩ : syracuseStep 1579859 = 2369789) B2369789
theorem B1579875 : Blo 1578487 1579875 := bstep (se 1 (by rfl) ⟨1184906, by rfl⟩ : syracuseStep 1579875 = 2369813) B2369813
theorem B2530163 : Blo 1578487 2530163 := bstep (se 1 (by rfl) ⟨1897622, by rfl⟩ : syracuseStep 2530163 = 3795245) B3795245
theorem B1579891 : Blo 1578487 1579891 := bstep (se 1 (by rfl) ⟨1184918, by rfl⟩ : syracuseStep 1579891 = 2369837) B2369837
theorem B1579907 : Blo 1578487 1579907 := bstep (se 1 (by rfl) ⟨1184930, by rfl⟩ : syracuseStep 1579907 = 2369861) B2369861
theorem B1579923 : Blo 1578487 1579923 := bstep (se 1 (by rfl) ⟨1184942, by rfl⟩ : syracuseStep 1579923 = 2369885) B2369885
theorem B2997155 : Blo 1578487 2997155 := bstep (se 1 (by rfl) ⟨2247866, by rfl⟩ : syracuseStep 2997155 = 4495733) B4495733
theorem B3373987 : Blo 1578487 3373987 := bstep (se 1 (by rfl) ⟨2530490, by rfl⟩ : syracuseStep 3373987 = 5060981) B5060981
theorem B1579939 : Blo 1578487 1579939 := bstep (se 1 (by rfl) ⟨1184954, by rfl⟩ : syracuseStep 1579939 = 2369909) B2369909
theorem B3554225 : Blo 1578487 3554225 := bstep (se 2 (by rfl) ⟨1332834, by rfl⟩ : syracuseStep 3554225 = 2665669) B2665669
theorem B1579955 : Blo 1578487 1579955 := bstep (se 1 (by rfl) ⟨1184966, by rfl⟩ : syracuseStep 1579955 = 2369933) B2369933
theorem B3996611 : Blo 1578487 3996611 := bstep (se 1 (by rfl) ⟨2997458, by rfl⟩ : syracuseStep 3996611 = 5994917) B5994917
theorem B3554243 : Blo 1578487 3554243 := bstep (se 1 (by rfl) ⟨2665682, by rfl⟩ : syracuseStep 3554243 = 5331365) B5331365
theorem B1579971 : Blo 1578487 1579971 := bstep (se 1 (by rfl) ⟨1184978, by rfl⟩ : syracuseStep 1579971 = 2369957) B2369957
theorem B1997779 : Blo 1578487 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B1776595 : Blo 1578487 1776595 := bstep (se 1 (by rfl) ⟨1332446, by rfl⟩ : syracuseStep 1776595 = 2664893) B2664893
theorem B1579987 : Blo 1578487 1579987 := bstep (se 1 (by rfl) ⟨1184990, by rfl⟩ : syracuseStep 1579987 = 2369981) B2369981
theorem B1580003 : Blo 1578487 1580003 := bstep (se 1 (by rfl) ⟨1185002, by rfl⟩ : syracuseStep 1580003 = 2370005) B2370005
theorem B11992049 : Blo 1578487 11992049 := bstep (se 2 (by rfl) ⟨4497018, by rfl⟩ : syracuseStep 11992049 = 8994037) B8994037
theorem B1580019 : Blo 1578487 1580019 := bstep (se 1 (by rfl) ⟨1185014, by rfl⟩ : syracuseStep 1580019 = 2370029) B2370029
theorem B1580035 : Blo 1578487 1580035 := bstep (se 1 (by rfl) ⟨1185026, by rfl⟩ : syracuseStep 1580035 = 2370053) B2370053
theorem B1580051 : Blo 1578487 1580051 := bstep (se 1 (by rfl) ⟨1185038, by rfl⟩ : syracuseStep 1580051 = 2370077) B2370077
theorem B6749219 : Blo 1578487 6749219 := bstep (se 1 (by rfl) ⟨5061914, by rfl⟩ : syracuseStep 6749219 = 10123829) B10123829
theorem B1580067 : Blo 1578487 1580067 := bstep (se 1 (by rfl) ⟨1185050, by rfl⟩ : syracuseStep 1580067 = 2370101) B2370101
theorem B5332013 : Blo 1578487 5332013 := bstep (se 3 (by rfl) ⟨999752, by rfl⟩ : syracuseStep 5332013 = 1999505) B1999505
theorem B1997875 : Blo 1578487 1997875 := bstep (se 1 (by rfl) ⟨1498406, by rfl⟩ : syracuseStep 1997875 = 2996813) B2996813
theorem B36486197 : Blo 1578487 36486197 := bstep (se 5 (by rfl) ⟨1710290, by rfl⟩ : syracuseStep 36486197 = 3420581) B3420581
theorem B1580083 : Blo 1578487 1580083 := bstep (se 1 (by rfl) ⟨1185062, by rfl⟩ : syracuseStep 1580083 = 2370125) B2370125
theorem B1580099 : Blo 1578487 1580099 := bstep (se 1 (by rfl) ⟨1185074, by rfl⟩ : syracuseStep 1580099 = 2370149) B2370149
theorem B5479501 : Blo 1578487 5479501 := bstep (se 3 (by rfl) ⟨1027406, by rfl⟩ : syracuseStep 5479501 = 2054813) B2054813
theorem B1580115 : Blo 1578487 1580115 := bstep (se 1 (by rfl) ⟨1185086, by rfl⟩ : syracuseStep 1580115 = 2370173) B2370173
theorem B1776739 : Blo 1578487 1776739 := bstep (se 1 (by rfl) ⟨1332554, by rfl⟩ : syracuseStep 1776739 = 2665109) B2665109
theorem B5332067 : Blo 1578487 5332067 := bstep (se 1 (by rfl) ⟨3999050, by rfl⟩ : syracuseStep 5332067 = 7998101) B7998101
theorem B1580131 : Blo 1578487 1580131 := bstep (se 1 (by rfl) ⟨1185098, by rfl⟩ : syracuseStep 1580131 = 2370197) B2370197
theorem B1580147 : Blo 1578487 1580147 := bstep (se 1 (by rfl) ⟨1185110, by rfl⟩ : syracuseStep 1580147 = 2370221) B2370221
theorem B3996803 : Blo 1578487 3996803 := bstep (se 1 (by rfl) ⟨2997602, by rfl⟩ : syracuseStep 3996803 = 5995205) B5995205
theorem B1580163 : Blo 1578487 1580163 := bstep (se 1 (by rfl) ⟨1185122, by rfl⟩ : syracuseStep 1580163 = 2370245) B2370245
theorem B1580179 : Blo 1578487 1580179 := bstep (se 1 (by rfl) ⟨1185134, by rfl⟩ : syracuseStep 1580179 = 2370269) B2370269
theorem B1580195 : Blo 1578487 1580195 := bstep (se 1 (by rfl) ⟨1185146, by rfl⟩ : syracuseStep 1580195 = 2370293) B2370293
theorem B1580211 : Blo 1578487 1580211 := bstep (se 1 (by rfl) ⟨1185158, by rfl⟩ : syracuseStep 1580211 = 2370317) B2370317
theorem B1580227 : Blo 1578487 1580227 := bstep (se 1 (by rfl) ⟨1185170, by rfl⟩ : syracuseStep 1580227 = 2370341) B2370341
theorem B3554513 : Blo 1578487 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B1580243 : Blo 1578487 1580243 := bstep (se 1 (by rfl) ⟨1185182, by rfl⟩ : syracuseStep 1580243 = 2370365) B2370365
theorem B3554531 : Blo 1578487 3554531 := bstep (se 1 (by rfl) ⟨2665898, by rfl⟩ : syracuseStep 3554531 = 5331797) B5331797
theorem B1580259 : Blo 1578487 1580259 := bstep (se 1 (by rfl) ⟨1185194, by rfl⟩ : syracuseStep 1580259 = 2370389) B2370389
theorem B1776883 : Blo 1578487 1776883 := bstep (se 1 (by rfl) ⟨1332662, by rfl⟩ : syracuseStep 1776883 = 2665325) B2665325
theorem B1580275 : Blo 1578487 1580275 := bstep (se 1 (by rfl) ⟨1185206, by rfl⟩ : syracuseStep 1580275 = 2370413) B2370413
theorem B1580291 : Blo 1578487 1580291 := bstep (se 1 (by rfl) ⟨1185218, by rfl⟩ : syracuseStep 1580291 = 2370437) B2370437
theorem B1580307 : Blo 1578487 1580307 := bstep (se 1 (by rfl) ⟨1185230, by rfl⟩ : syracuseStep 1580307 = 2370461) B2370461
theorem B1580323 : Blo 1578487 1580323 := bstep (se 1 (by rfl) ⟨1185242, by rfl⟩ : syracuseStep 1580323 = 2370485) B2370485
theorem B1686835 : Blo 1578487 1686835 := bstep (se 1 (by rfl) ⟨1265126, by rfl⟩ : syracuseStep 1686835 = 2530253) B2530253
theorem B1580339 : Blo 1578487 1580339 := bstep (se 1 (by rfl) ⟨1185254, by rfl⟩ : syracuseStep 1580339 = 2370509) B2370509
theorem B1580355 : Blo 1578487 1580355 := bstep (se 1 (by rfl) ⟨1185266, by rfl⟩ : syracuseStep 1580355 = 2370533) B2370533
theorem B5070161 : Blo 1578487 5070161 := bstep (se 2 (by rfl) ⟨1901310, by rfl⟩ : syracuseStep 5070161 = 3802621) B3802621
theorem B1580371 : Blo 1578487 1580371 := bstep (se 1 (by rfl) ⟨1185278, by rfl⟩ : syracuseStep 1580371 = 2370557) B2370557
theorem B7306595 : Blo 1578487 7306595 := bstep (se 1 (by rfl) ⟨5479946, by rfl⟩ : syracuseStep 7306595 = 10959893) B10959893
theorem B1580387 : Blo 1578487 1580387 := bstep (se 1 (by rfl) ⟨1185290, by rfl⟩ : syracuseStep 1580387 = 2370581) B2370581
theorem B5995889 : Blo 1578487 5995889 := bstep (se 2 (by rfl) ⟨2248458, by rfl⟩ : syracuseStep 5995889 = 4496917) B4496917
theorem B5332337 : Blo 1578487 5332337 := bstep (se 2 (by rfl) ⟨1999626, by rfl⟩ : syracuseStep 5332337 = 3999253) B3999253
theorem B1580403 : Blo 1578487 1580403 := bstep (se 1 (by rfl) ⟨1185302, by rfl⟩ : syracuseStep 1580403 = 2370605) B2370605
theorem B1777027 : Blo 1578487 1777027 := bstep (se 1 (by rfl) ⟨1332770, by rfl⟩ : syracuseStep 1777027 = 2665541) B2665541
theorem B1580419 : Blo 1578487 1580419 := bstep (se 1 (by rfl) ⟨1185314, by rfl⟩ : syracuseStep 1580419 = 2370629) B2370629
theorem B1580435 : Blo 1578487 1580435 := bstep (se 1 (by rfl) ⟨1185326, by rfl⟩ : syracuseStep 1580435 = 2370653) B2370653
theorem B1580451 : Blo 1578487 1580451 := bstep (se 1 (by rfl) ⟨1185338, by rfl⟩ : syracuseStep 1580451 = 2370677) B2370677
theorem B1580467 : Blo 1578487 1580467 := bstep (se 1 (by rfl) ⟨1185350, by rfl⟩ : syracuseStep 1580467 = 2370701) B2370701
theorem B1580483 : Blo 1578487 1580483 := bstep (se 1 (by rfl) ⟨1185362, by rfl⟩ : syracuseStep 1580483 = 2370725) B2370725
theorem B3554801 : Blo 1578487 3554801 := bstep (se 2 (by rfl) ⟨1333050, by rfl⟩ : syracuseStep 3554801 = 2666101) B2666101
theorem B3554819 : Blo 1578487 3554819 := bstep (se 1 (by rfl) ⟨2666114, by rfl⟩ : syracuseStep 3554819 = 5332229) B5332229
theorem B1777171 : Blo 1578487 1777171 := bstep (se 1 (by rfl) ⟨1332878, by rfl⟩ : syracuseStep 1777171 = 2665757) B2665757
theorem B1998371 : Blo 1578487 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B3202627 : Blo 1578487 3202627 := bstep (se 1 (by rfl) ⟨2401970, by rfl⟩ : syracuseStep 3202627 = 4803941) B4803941
theorem B1777315 : Blo 1578487 1777315 := bstep (se 1 (by rfl) ⟨1332986, by rfl⟩ : syracuseStep 1777315 = 2665973) B2665973
theorem B2531009 : Blo 1578487 2531009 := bstep (se 2 (by rfl) ⟨949128, by rfl⟩ : syracuseStep 2531009 = 1898257) B1898257
theorem B1687267 : Blo 1578487 1687267 := bstep (se 1 (by rfl) ⟨1265450, by rfl⟩ : syracuseStep 1687267 = 2530901) B2530901
theorem B83222243 : Blo 1578487 83222243 := bstep (se 1 (by rfl) ⟨62416682, by rfl⟩ : syracuseStep 83222243 = 124833365) B124833365
theorem B4497133 : Blo 1578487 4497133 := bstep (se 3 (by rfl) ⟨843212, by rfl⟩ : syracuseStep 4497133 = 1686425) B1686425
theorem B3555089 : Blo 1578487 3555089 := bstep (se 2 (by rfl) ⟨1333158, by rfl⟩ : syracuseStep 3555089 = 2666317) B2666317
theorem B3555107 : Blo 1578487 3555107 := bstep (se 1 (by rfl) ⟨2666330, by rfl⟩ : syracuseStep 3555107 = 5332661) B5332661
theorem B7995185 : Blo 1578487 7995185 := bstep (se 2 (by rfl) ⟨2998194, by rfl⟩ : syracuseStep 7995185 = 5996389) B5996389
theorem B1777459 : Blo 1578487 1777459 := bstep (se 1 (by rfl) ⟨1333094, by rfl⟩ : syracuseStep 1777459 = 2666189) B2666189
theorem B5128067 : Blo 1578487 5128067 := bstep (se 1 (by rfl) ⟨3846050, by rfl⟩ : syracuseStep 5128067 = 7692101) B7692101
theorem B5332877 : Blo 1578487 5332877 := bstep (se 3 (by rfl) ⟨999914, by rfl⟩ : syracuseStep 5332877 = 1999829) B1999829
theorem B1777603 : Blo 1578487 1777603 := bstep (se 1 (by rfl) ⟨1333202, by rfl⟩ : syracuseStep 1777603 = 2666405) B2666405
theorem B5332931 : Blo 1578487 5332931 := bstep (se 1 (by rfl) ⟨3999698, by rfl⟩ : syracuseStep 5332931 = 7999397) B7999397
theorem B2998225 : Blo 1578487 2998225 := bstep (se 2 (by rfl) ⟨1124334, by rfl⟩ : syracuseStep 2998225 = 2248669) B2248669
theorem B1622027 : Blo 1578487 1622027 := bstep (se 1 (by rfl) ⟨1216520, by rfl⟩ : syracuseStep 1622027 = 2433041) B2433041
theorem B1777675 : Blo 1578487 1777675 := bstep (se 1 (by rfl) ⟨1333256, by rfl⟩ : syracuseStep 1777675 = 2666513) B2666513
theorem B3792919 : Blo 1578487 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B1802263 : Blo 1578487 1802263 := bstep (se 1 (by rfl) ⟨1351697, by rfl⟩ : syracuseStep 1802263 = 2703395) B2703395
theorem B5554241 : Blo 1578487 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B3203147 : Blo 1578487 3203147 := bstep (se 1 (by rfl) ⟨2402360, by rfl⟩ : syracuseStep 3203147 = 4804721) B4804721
theorem B3375191 : Blo 1578487 3375191 := bstep (se 1 (by rfl) ⟨2531393, by rfl⟩ : syracuseStep 3375191 = 5062787) B5062787
theorem B2703449 : Blo 1578487 2703449 := bstep (se 2 (by rfl) ⟨1013793, by rfl⟩ : syracuseStep 2703449 = 2027587) B2027587
theorem B1777783 : Blo 1578487 1777783 := bstep (se 1 (by rfl) ⟨1333337, by rfl⟩ : syracuseStep 1777783 = 2666675) B2666675
theorem B1622155 : Blo 1578487 1622155 := bstep (se 1 (by rfl) ⟨1216616, by rfl⟩ : syracuseStep 1622155 = 2433233) B2433233
theorem B3555467 : Blo 1578487 3555467 := bstep (se 1 (by rfl) ⟨2666600, by rfl⟩ : syracuseStep 3555467 = 5333201) B5333201
theorem B14418071 : Blo 1578487 14418071 := bstep (se 1 (by rfl) ⟨10813553, by rfl⟩ : syracuseStep 14418071 = 21627107) B21627107
theorem B13500593 : Blo 1578487 13500593 := bstep (se 2 (by rfl) ⟨5062722, by rfl⟩ : syracuseStep 13500593 = 10125445) B10125445
theorem B8994995 : Blo 1578487 8994995 := bstep (se 1 (by rfl) ⟨6746246, by rfl⟩ : syracuseStep 8994995 = 13492493) B13492493
theorem B3555521 : Blo 1578487 3555521 := bstep (se 2 (by rfl) ⟨1333320, by rfl⟩ : syracuseStep 3555521 = 2666641) B2666641
theorem B2998529 : Blo 1578487 2998529 := bstep (se 2 (by rfl) ⟨1124448, by rfl⟩ : syracuseStep 2998529 = 2248897) B2248897
theorem B3375361 : Blo 1578487 3375361 := bstep (se 2 (by rfl) ⟨1265760, by rfl⟩ : syracuseStep 3375361 = 2531521) B2531521
theorem B2367755 : Blo 1578487 2367755 := bstep (se 1 (by rfl) ⟨1775816, by rfl⟩ : syracuseStep 2367755 = 3551633) B3551633
theorem B2367767 : Blo 1578487 2367767 := bstep (se 1 (by rfl) ⟨1775825, by rfl⟩ : syracuseStep 2367767 = 3551651) B3551651
theorem B1777963 : Blo 1578487 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B5996875 : Blo 1578487 5996875 := bstep (se 1 (by rfl) ⟨4497656, by rfl⟩ : syracuseStep 5996875 = 8995313) B8995313
theorem B2367833 : Blo 1578487 2367833 := bstep (se 2 (by rfl) ⟨887937, by rfl⟩ : syracuseStep 2367833 = 1775875) B1775875
theorem B5767555 : Blo 1578487 5767555 := bstep (se 1 (by rfl) ⟨4325666, by rfl⟩ : syracuseStep 5767555 = 8651333) B8651333
theorem B3555737 : Blo 1578487 3555737 := bstep (se 2 (by rfl) ⟨1333401, by rfl⟩ : syracuseStep 3555737 = 2666803) B2666803
theorem B15180209 : Blo 1578487 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B2367947 : Blo 1578487 2367947 := bstep (se 1 (by rfl) ⟨1775960, by rfl⟩ : syracuseStep 2367947 = 3551921) B3551921
theorem B2367959 : Blo 1578487 2367959 := bstep (se 1 (by rfl) ⟨1775969, by rfl⟩ : syracuseStep 2367959 = 3551939) B3551939
theorem B3555827 : Blo 1578487 3555827 := bstep (se 1 (by rfl) ⟨2666870, by rfl⟩ : syracuseStep 3555827 = 5333741) B5333741
theorem B2998795 : Blo 1578487 2998795 := bstep (se 1 (by rfl) ⟨2249096, by rfl⟩ : syracuseStep 2998795 = 4498193) B4498193
theorem B3998231 : Blo 1578487 3998231 := bstep (se 1 (by rfl) ⟨2998673, by rfl⟩ : syracuseStep 3998231 = 5997347) B5997347
theorem B2368025 : Blo 1578487 2368025 := bstep (se 2 (by rfl) ⟨888009, by rfl⟩ : syracuseStep 2368025 = 1776019) B1776019
theorem B3555863 : Blo 1578487 3555863 := bstep (se 1 (by rfl) ⟨2666897, by rfl⟩ : syracuseStep 3555863 = 5333795) B5333795
theorem B4325953 : Blo 1578487 4325953 := bstep (se 2 (by rfl) ⟨1622232, by rfl⟩ : syracuseStep 4325953 = 3244465) B3244465
theorem B5333579 : Blo 1578487 5333579 := bstep (se 1 (by rfl) ⟨4000184, by rfl⟩ : syracuseStep 5333579 = 8000369) B8000369
theorem B5997149 : Blo 1578487 5997149 := bstep (se 3 (by rfl) ⟨1124465, by rfl⟩ : syracuseStep 5997149 = 2248931) B2248931
theorem B2368139 : Blo 1578487 2368139 := bstep (se 1 (by rfl) ⟨1776104, by rfl⟩ : syracuseStep 2368139 = 3552209) B3552209
theorem B2368151 : Blo 1578487 2368151 := bstep (se 1 (by rfl) ⟨1776113, by rfl⟩ : syracuseStep 2368151 = 3552227) B3552227
theorem B3556043 : Blo 1578487 3556043 := bstep (se 1 (by rfl) ⟨2667032, by rfl⟩ : syracuseStep 3556043 = 5334065) B5334065
theorem B2368217 : Blo 1578487 2368217 := bstep (se 2 (by rfl) ⟨888081, by rfl⟩ : syracuseStep 2368217 = 1776163) B1776163
theorem B3556097 : Blo 1578487 3556097 := bstep (se 2 (by rfl) ⟨1333536, by rfl⟩ : syracuseStep 3556097 = 2667073) B2667073
theorem B2368331 : Blo 1578487 2368331 := bstep (se 1 (by rfl) ⟨1776248, by rfl⟩ : syracuseStep 2368331 = 3552497) B3552497
theorem B2368343 : Blo 1578487 2368343 := bstep (se 1 (by rfl) ⟨1776257, by rfl⟩ : syracuseStep 2368343 = 3552515) B3552515
theorem B3040087 : Blo 1578487 3040087 := bstep (se 1 (by rfl) ⟨2280065, by rfl⟩ : syracuseStep 3040087 = 4560131) B4560131
theorem B5333849 : Blo 1578487 5333849 := bstep (se 2 (by rfl) ⟨2000193, by rfl⟩ : syracuseStep 5333849 = 4000387) B4000387
theorem B6407005 : Blo 1578487 6407005 := bstep (se 3 (by rfl) ⟨1201313, by rfl⟩ : syracuseStep 6407005 = 2402627) B2402627
theorem B2368409 : Blo 1578487 2368409 := bstep (se 2 (by rfl) ⟨888153, by rfl⟩ : syracuseStep 2368409 = 1776307) B1776307
theorem B2999243 : Blo 1578487 2999243 := bstep (se 1 (by rfl) ⟨2249432, by rfl⟩ : syracuseStep 2999243 = 4498865) B4498865
theorem B1999819 : Blo 1578487 1999819 := bstep (se 1 (by rfl) ⟨1499864, by rfl⟩ : syracuseStep 1999819 = 2999729) B2999729
theorem B5694425 : Blo 1578487 5694425 := bstep (se 2 (by rfl) ⟨2135409, by rfl⟩ : syracuseStep 5694425 = 4270819) B4270819
theorem B2368523 : Blo 1578487 2368523 := bstep (se 1 (by rfl) ⟨1776392, by rfl⟩ : syracuseStep 2368523 = 3552785) B3552785
theorem B2368535 : Blo 1578487 2368535 := bstep (se 1 (by rfl) ⟨1776401, by rfl⟩ : syracuseStep 2368535 = 3552803) B3552803
theorem B7996481 : Blo 1578487 7996481 := bstep (se 2 (by rfl) ⟨2998680, by rfl⟩ : syracuseStep 7996481 = 5997361) B5997361
theorem B2368601 : Blo 1578487 2368601 := bstep (se 2 (by rfl) ⟨888225, by rfl⟩ : syracuseStep 2368601 = 1776451) B1776451
theorem B4867165 : Blo 1578487 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B2999425 : Blo 1578487 2999425 := bstep (se 2 (by rfl) ⟨1124784, by rfl⟩ : syracuseStep 2999425 = 2249569) B2249569
theorem B2368715 : Blo 1578487 2368715 := bstep (se 1 (by rfl) ⟨1776536, by rfl⟩ : syracuseStep 2368715 = 3553073) B3553073
theorem B2368727 : Blo 1578487 2368727 := bstep (se 1 (by rfl) ⟨1776545, by rfl⟩ : syracuseStep 2368727 = 3553091) B3553091
theorem B4498649 : Blo 1578487 4498649 := bstep (se 2 (by rfl) ⟨1686993, by rfl⟩ : syracuseStep 4498649 = 3373987) B3373987
theorem B5997847 : Blo 1578487 5997847 := bstep (se 1 (by rfl) ⟨4498385, by rfl⟩ : syracuseStep 5997847 = 8996771) B8996771
theorem B2663705 : Blo 1578487 2663705 := bstep (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) B1997779
theorem B2368793 : Blo 1578487 2368793 := bstep (se 2 (by rfl) ⟨888297, by rfl⟩ : syracuseStep 2368793 = 1776595) B1776595
theorem B6743341 : Blo 1578487 6743341 := bstep (se 3 (by rfl) ⟨1264376, by rfl⟩ : syracuseStep 6743341 = 2528753) B2528753
theorem B23389505 : Blo 1578487 23389505 := bstep (se 2 (by rfl) ⟨8771064, by rfl⟩ : syracuseStep 23389505 = 17542129) B17542129
theorem B3999041 : Blo 1578487 3999041 := bstep (se 2 (by rfl) ⟨1499640, by rfl⟩ : syracuseStep 3999041 = 2999281) B2999281
theorem B2368907 : Blo 1578487 2368907 := bstep (se 1 (by rfl) ⟨1776680, by rfl⟩ : syracuseStep 2368907 = 3553361) B3553361
theorem B2368919 : Blo 1578487 2368919 := bstep (se 1 (by rfl) ⟨1776689, by rfl⟩ : syracuseStep 2368919 = 3553379) B3553379
theorem B2663833 : Blo 1578487 2663833 := bstep (se 2 (by rfl) ⟨998937, by rfl⟩ : syracuseStep 2663833 = 1997875) B1997875
theorem B2999767 : Blo 1578487 2999767 := bstep (se 1 (by rfl) ⟨2249825, by rfl⟩ : syracuseStep 2999767 = 4499651) B4499651
theorem B6743513 : Blo 1578487 6743513 := bstep (se 2 (by rfl) ⟨2528817, by rfl⟩ : syracuseStep 6743513 = 5057635) B5057635
theorem B2368985 : Blo 1578487 2368985 := bstep (se 2 (by rfl) ⟨888369, by rfl⟩ : syracuseStep 2368985 = 1776739) B1776739
theorem B2369099 : Blo 1578487 2369099 := bstep (se 1 (by rfl) ⟨1776824, by rfl⟩ : syracuseStep 2369099 = 3553649) B3553649
theorem B2369111 : Blo 1578487 2369111 := bstep (se 1 (by rfl) ⟨1776833, by rfl⟩ : syracuseStep 2369111 = 3553667) B3553667
theorem B8996453 : Blo 1578487 8996453 := bstep (se 4 (by rfl) ⟨843417, by rfl⟩ : syracuseStep 8996453 = 1686835) B1686835
theorem B34162307 : Blo 1578487 34162307 := bstep (se 1 (by rfl) ⟨25621730, by rfl⟩ : syracuseStep 34162307 = 51243461) B51243461
theorem B2369177 : Blo 1578487 2369177 := bstep (se 2 (by rfl) ⟨888441, by rfl⟩ : syracuseStep 2369177 = 1776883) B1776883
theorem B2999987 : Blo 1578487 2999987 := bstep (se 1 (by rfl) ⟨2249990, by rfl⟩ : syracuseStep 2999987 = 4499981) B4499981
theorem B24643277 : Blo 1578487 24643277 := bstep (se 3 (by rfl) ⟨4620614, by rfl⟩ : syracuseStep 24643277 = 9241229) B9241229
theorem B2369291 : Blo 1578487 2369291 := bstep (se 1 (by rfl) ⟨1776968, by rfl⟩ : syracuseStep 2369291 = 3553937) B3553937
theorem B2369303 : Blo 1578487 2369303 := bstep (se 1 (by rfl) ⟨1776977, by rfl⟩ : syracuseStep 2369303 = 3553955) B3553955
theorem B7202611 : Blo 1578487 7202611 := bstep (se 1 (by rfl) ⟨5401958, by rfl⟩ : syracuseStep 7202611 = 10803917) B10803917
theorem B2369369 : Blo 1578487 2369369 := bstep (se 2 (by rfl) ⟨888513, by rfl⟩ : syracuseStep 2369369 = 1777027) B1777027
theorem B3999577 : Blo 1578487 3999577 := bstep (se 2 (by rfl) ⟨1499841, by rfl⟩ : syracuseStep 3999577 = 2999683) B2999683
theorem B3000215 : Blo 1578487 3000215 := bstep (se 1 (by rfl) ⟨2250161, by rfl⟩ : syracuseStep 3000215 = 4500323) B4500323
theorem B2369483 : Blo 1578487 2369483 := bstep (se 1 (by rfl) ⟨1777112, by rfl⟩ : syracuseStep 2369483 = 3554225) B3554225
theorem B2664407 : Blo 1578487 2664407 := bstep (se 1 (by rfl) ⟨1998305, by rfl⟩ : syracuseStep 2664407 = 3996611) B3996611
theorem B2369495 : Blo 1578487 2369495 := bstep (se 1 (by rfl) ⟨1777121, by rfl⟩ : syracuseStep 2369495 = 3554243) B3554243
theorem B4499479 : Blo 1578487 4499479 := bstep (se 1 (by rfl) ⟨3374609, by rfl⟩ : syracuseStep 4499479 = 6749219) B6749219
theorem B2369561 : Blo 1578487 2369561 := bstep (se 2 (by rfl) ⟨888585, by rfl⟩ : syracuseStep 2369561 = 1777171) B1777171
theorem B24324131 : Blo 1578487 24324131 := bstep (se 1 (by rfl) ⟨18243098, by rfl⟩ : syracuseStep 24324131 = 36486197) B36486197
theorem B5998637 : Blo 1578487 5998637 := bstep (se 3 (by rfl) ⟨1124744, by rfl⟩ : syracuseStep 5998637 = 2249489) B2249489
theorem B2664535 : Blo 1578487 2664535 := bstep (se 1 (by rfl) ⟨1998401, by rfl⟩ : syracuseStep 2664535 = 3996803) B3996803
theorem B4270169 : Blo 1578487 4270169 := bstep (se 2 (by rfl) ⟨1601313, by rfl⟩ : syracuseStep 4270169 = 3202627) B3202627
theorem B2369675 : Blo 1578487 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B2369687 : Blo 1578487 2369687 := bstep (se 1 (by rfl) ⟨1777265, by rfl⟩ : syracuseStep 2369687 = 3554531) B3554531
theorem B2369753 : Blo 1578487 2369753 := bstep (se 2 (by rfl) ⟨888657, by rfl⟩ : syracuseStep 2369753 = 1777315) B1777315
theorem B2369867 : Blo 1578487 2369867 := bstep (se 1 (by rfl) ⟨1777400, by rfl⟩ : syracuseStep 2369867 = 3554801) B3554801
theorem B2369879 : Blo 1578487 2369879 := bstep (se 1 (by rfl) ⟨1777409, by rfl⟩ : syracuseStep 2369879 = 3554819) B3554819
theorem B13674845 : Blo 1578487 13674845 := bstep (se 3 (by rfl) ⟨2564033, by rfl⟩ : syracuseStep 13674845 = 5128067) B5128067
theorem B2369945 : Blo 1578487 2369945 := bstep (se 2 (by rfl) ⟨888729, by rfl⟩ : syracuseStep 2369945 = 1777459) B1777459
theorem B5851609 : Blo 1578487 5851609 := bstep (se 2 (by rfl) ⟨2194353, by rfl⟩ : syracuseStep 5851609 = 4388707) B4388707
theorem B2370059 : Blo 1578487 2370059 := bstep (se 1 (by rfl) ⟨1777544, by rfl⟩ : syracuseStep 2370059 = 3555089) B3555089
theorem B2370071 : Blo 1578487 2370071 := bstep (se 1 (by rfl) ⟨1777553, by rfl⟩ : syracuseStep 2370071 = 3555107) B3555107
theorem B2370137 : Blo 1578487 2370137 := bstep (se 2 (by rfl) ⟨888801, by rfl⟩ : syracuseStep 2370137 = 1777603) B1777603
theorem B2665163 : Blo 1578487 2665163 := bstep (se 1 (by rfl) ⟨1998872, by rfl⟩ : syracuseStep 2665163 = 3997745) B3997745
theorem B2370251 : Blo 1578487 2370251 := bstep (se 1 (by rfl) ⟨1777688, by rfl⟩ : syracuseStep 2370251 = 3555377) B3555377
theorem B2370263 : Blo 1578487 2370263 := bstep (se 1 (by rfl) ⟨1777697, by rfl⟩ : syracuseStep 2370263 = 3555395) B3555395
theorem B5327639 : Blo 1578487 5327639 := bstep (se 1 (by rfl) ⟨3995729, by rfl⟩ : syracuseStep 5327639 = 7991459) B7991459
theorem B2370329 : Blo 1578487 2370329 := bstep (se 2 (by rfl) ⟨888873, by rfl⟩ : syracuseStep 2370329 = 1777747) B1777747
theorem B28822337 : Blo 1578487 28822337 := bstep (se 2 (by rfl) ⟨10808376, by rfl⟩ : syracuseStep 28822337 = 21616753) B21616753
theorem B2665291 : Blo 1578487 2665291 := bstep (se 1 (by rfl) ⟨1998968, by rfl⟩ : syracuseStep 2665291 = 3997937) B3997937
theorem B4500299 : Blo 1578487 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B2370443 : Blo 1578487 2370443 := bstep (se 1 (by rfl) ⟨1777832, by rfl⟩ : syracuseStep 2370443 = 3555665) B3555665
theorem B5770129 : Blo 1578487 5770129 := bstep (se 2 (by rfl) ⟨2163798, by rfl⟩ : syracuseStep 5770129 = 4327597) B4327597
theorem B2370455 : Blo 1578487 2370455 := bstep (se 1 (by rfl) ⟨1777841, by rfl⟩ : syracuseStep 2370455 = 3555683) B3555683
theorem B2845655 : Blo 1578487 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B2665433 : Blo 1578487 2665433 := bstep (se 2 (by rfl) ⟨999537, by rfl⟩ : syracuseStep 2665433 = 1999075) B1999075
theorem B7998425 : Blo 1578487 7998425 := bstep (se 2 (by rfl) ⟨2999409, by rfl⟩ : syracuseStep 7998425 = 5998819) B5998819
theorem B2370521 : Blo 1578487 2370521 := bstep (se 2 (by rfl) ⟨888945, by rfl⟩ : syracuseStep 2370521 = 1777891) B1777891
theorem B6745153 : Blo 1578487 6745153 := bstep (se 2 (by rfl) ⟨2529432, by rfl⟩ : syracuseStep 6745153 = 5058865) B5058865
theorem B2370635 : Blo 1578487 2370635 := bstep (se 1 (by rfl) ⟨1777976, by rfl⟩ : syracuseStep 2370635 = 3555953) B3555953
theorem B2370647 : Blo 1578487 2370647 := bstep (se 1 (by rfl) ⟨1777985, by rfl⟩ : syracuseStep 2370647 = 3555971) B3555971
theorem B2665561 : Blo 1578487 2665561 := bstep (se 2 (by rfl) ⟨999585, by rfl⟩ : syracuseStep 2665561 = 1999171) B1999171
theorem B2370713 : Blo 1578487 2370713 := bstep (se 2 (by rfl) ⟨889017, by rfl⟩ : syracuseStep 2370713 = 1778035) B1778035
theorem B12815633 : Blo 1578487 12815633 := bstep (se 2 (by rfl) ⟨4805862, by rfl⟩ : syracuseStep 12815633 = 9611725) B9611725
theorem B5328179 : Blo 1578487 5328179 := bstep (se 1 (by rfl) ⟨3996134, by rfl⟩ : syracuseStep 5328179 = 7992269) B7992269
theorem B6000065 : Blo 1578487 6000065 := bstep (se 2 (by rfl) ⟨2250024, by rfl⟩ : syracuseStep 6000065 = 4500049) B4500049
theorem B3796427 : Blo 1578487 3796427 := bstep (se 1 (by rfl) ⟨2847320, by rfl⟩ : syracuseStep 3796427 = 5694641) B5694641
theorem B17993177 : Blo 1578487 17993177 := bstep (se 2 (by rfl) ⟨6747441, by rfl⟩ : syracuseStep 17993177 = 13494883) B13494883
theorem B97209827 : Blo 1578487 97209827 := bstep (se 1 (by rfl) ⟨72907370, by rfl⟩ : syracuseStep 97209827 = 145814741) B145814741
theorem B5058071 : Blo 1578487 5058071 := bstep (se 1 (by rfl) ⟨3793553, by rfl⟩ : syracuseStep 5058071 = 7587107) B7587107
theorem B13520429 : Blo 1578487 13520429 := bstep (se 3 (by rfl) ⟨2535080, by rfl⟩ : syracuseStep 13520429 = 5070161) B5070161
theorem B5328449 : Blo 1578487 5328449 := bstep (se 2 (by rfl) ⟨1998168, by rfl⟩ : syracuseStep 5328449 = 3996337) B3996337
theorem B2666135 : Blo 1578487 2666135 := bstep (se 1 (by rfl) ⟨1999601, by rfl⟩ : syracuseStep 2666135 = 3999203) B3999203
theorem B5058251 : Blo 1578487 5058251 := bstep (se 1 (by rfl) ⟨3793688, by rfl⟩ : syracuseStep 5058251 = 7587377) B7587377
theorem B2600651 : Blo 1578487 2600651 := bstep (se 1 (by rfl) ⟨1950488, by rfl⟩ : syracuseStep 2600651 = 3900977) B3900977
theorem B3600139 : Blo 1578487 3600139 := bstep (se 1 (by rfl) ⟨2700104, by rfl⟩ : syracuseStep 3600139 = 5400209) B5400209
theorem B2666263 : Blo 1578487 2666263 := bstep (se 1 (by rfl) ⟨1999697, by rfl⟩ : syracuseStep 2666263 = 3999395) B3999395
theorem B5058521 : Blo 1578487 5058521 := bstep (se 2 (by rfl) ⟨1896945, by rfl⟩ : syracuseStep 5058521 = 3793891) B3793891
theorem B5328989 : Blo 1578487 5328989 := bstep (se 3 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 5328989 = 1998371) B1998371
theorem B3371329 : Blo 1578487 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B10400075 : Blo 1578487 10400075 := bstep (se 1 (by rfl) ⟨7800056, by rfl⟩ : syracuseStep 10400075 = 15600113) B15600113
theorem B10121573 : Blo 1578487 10121573 := bstep (se 4 (by rfl) ⟨948897, by rfl⟩ : syracuseStep 10121573 = 1897795) B1897795
theorem B2666891 : Blo 1578487 2666891 := bstep (se 1 (by rfl) ⟨2000168, by rfl⟩ : syracuseStep 2666891 = 4000337) B4000337
theorem B4559297 : Blo 1578487 4559297 := bstep (se 2 (by rfl) ⟨1709736, by rfl⟩ : syracuseStep 4559297 = 3419473) B3419473
theorem B3551705 : Blo 1578487 3551705 := bstep (se 2 (by rfl) ⟨1331889, by rfl⟩ : syracuseStep 3551705 = 2663779) B2663779
theorem B2667019 : Blo 1578487 2667019 := bstep (se 1 (by rfl) ⟨2000264, by rfl⟩ : syracuseStep 2667019 = 4000529) B4000529
theorem B13496867 : Blo 1578487 13496867 := bstep (se 1 (by rfl) ⟨10122650, by rfl⟩ : syracuseStep 13496867 = 20245301) B20245301
theorem B8000045 : Blo 1578487 8000045 := bstep (se 3 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 8000045 = 3000017) B3000017
theorem B3551795 : Blo 1578487 3551795 := bstep (se 1 (by rfl) ⟨2663846, by rfl⟩ : syracuseStep 3551795 = 5327693) B5327693
theorem B3551831 : Blo 1578487 3551831 := bstep (se 1 (by rfl) ⟨2663873, by rfl⟩ : syracuseStep 3551831 = 5327747) B5327747
theorem B6746827 : Blo 1578487 6746827 := bstep (se 1 (by rfl) ⟨5060120, by rfl⟩ : syracuseStep 6746827 = 10120241) B10120241
theorem B3552011 : Blo 1578487 3552011 := bstep (se 1 (by rfl) ⟨2664008, by rfl⟩ : syracuseStep 3552011 = 5328017) B5328017
theorem B5059351 : Blo 1578487 5059351 := bstep (se 1 (by rfl) ⟨3794513, by rfl⟩ : syracuseStep 5059351 = 7589027) B7589027
theorem B3552065 : Blo 1578487 3552065 := bstep (se 2 (by rfl) ⟨1332024, by rfl⟩ : syracuseStep 3552065 = 2664049) B2664049
theorem B1897291 : Blo 1578487 1897291 := bstep (se 1 (by rfl) ⟨1422968, by rfl⟩ : syracuseStep 1897291 = 2845937) B2845937
theorem B7697245 : Blo 1578487 7697245 := bstep (se 3 (by rfl) ⟨1443233, by rfl⟩ : syracuseStep 7697245 = 2886467) B2886467
theorem B4871063 : Blo 1578487 4871063 := bstep (se 1 (by rfl) ⟨3653297, by rfl⟩ : syracuseStep 4871063 = 7306595) B7306595
theorem B2249689 : Blo 1578487 2249689 := bstep (se 2 (by rfl) ⟨843633, by rfl⟩ : syracuseStep 2249689 = 1687267) B1687267
theorem B6747101 : Blo 1578487 6747101 := bstep (se 3 (by rfl) ⟨1265081, by rfl⟩ : syracuseStep 6747101 = 2530163) B2530163
theorem B19215377 : Blo 1578487 19215377 := bstep (se 2 (by rfl) ⟨7205766, by rfl⟩ : syracuseStep 19215377 = 14411533) B14411533
theorem B3552281 : Blo 1578487 3552281 := bstep (se 2 (by rfl) ⟨1332105, by rfl⟩ : syracuseStep 3552281 = 2664211) B2664211
theorem B3552371 : Blo 1578487 3552371 := bstep (se 1 (by rfl) ⟨2664278, by rfl⟩ : syracuseStep 3552371 = 5328557) B5328557
theorem B6583427 : Blo 1578487 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B3552407 : Blo 1578487 3552407 := bstep (se 1 (by rfl) ⟨2664305, by rfl⟩ : syracuseStep 3552407 = 5328611) B5328611
theorem B55481495 : Blo 1578487 55481495 := bstep (se 1 (by rfl) ⟨41611121, by rfl⟩ : syracuseStep 55481495 = 83222243) B83222243
theorem B5330123 : Blo 1578487 5330123 := bstep (se 1 (by rfl) ⟨3997592, by rfl⟩ : syracuseStep 5330123 = 7995185) B7995185
theorem B7992593 : Blo 1578487 7992593 := bstep (se 2 (by rfl) ⟨2997222, by rfl⟩ : syracuseStep 7992593 = 5994445) B5994445
theorem B13497617 : Blo 1578487 13497617 := bstep (se 2 (by rfl) ⟨5061606, by rfl⟩ : syracuseStep 13497617 = 10123213) B10123213
theorem B3847475 : Blo 1578487 3847475 := bstep (se 1 (by rfl) ⟨2885606, by rfl⟩ : syracuseStep 3847475 = 5771213) B5771213
theorem B3552587 : Blo 1578487 3552587 := bstep (se 1 (by rfl) ⟨2664440, by rfl⟩ : syracuseStep 3552587 = 5328881) B5328881
theorem B3552641 : Blo 1578487 3552641 := bstep (se 2 (by rfl) ⟨1332240, by rfl⟩ : syracuseStep 3552641 = 2664481) B2664481
theorem B3601817 : Blo 1578487 3601817 := bstep (se 2 (by rfl) ⟨1350681, by rfl⟩ : syracuseStep 3601817 = 2701363) B2701363
theorem B7992755 : Blo 1578487 7992755 := bstep (se 1 (by rfl) ⟨5994566, by rfl⟩ : syracuseStep 7992755 = 11989133) B11989133
theorem B3372491 : Blo 1578487 3372491 := bstep (se 1 (by rfl) ⟨2529368, by rfl⟩ : syracuseStep 3372491 = 5058737) B5058737
theorem B5993945 : Blo 1578487 5993945 := bstep (se 2 (by rfl) ⟨2247729, by rfl⟩ : syracuseStep 5993945 = 4495459) B4495459
theorem B5330393 : Blo 1578487 5330393 := bstep (se 2 (by rfl) ⟨1998897, by rfl⟩ : syracuseStep 5330393 = 3997795) B3997795
theorem B1578487 : Blo 1578487 1578487 := bstep (se 1 (by rfl) ⟨1183865, by rfl⟩ : syracuseStep 1578487 = 2367731) B2367731
theorem B1578507 : Blo 1578487 1578507 := bstep (se 1 (by rfl) ⟨1183880, by rfl⟩ : syracuseStep 1578507 = 2367761) B2367761
theorem B1578519 : Blo 1578487 1578519 := bstep (se 1 (by rfl) ⟨1183889, by rfl⟩ : syracuseStep 1578519 = 2367779) B2367779
theorem B1578539 : Blo 1578487 1578539 := bstep (se 1 (by rfl) ⟨1183904, by rfl⟩ : syracuseStep 1578539 = 2367809) B2367809
theorem B1578551 : Blo 1578487 1578551 := bstep (se 1 (by rfl) ⟨1183913, by rfl⟩ : syracuseStep 1578551 = 2367827) B2367827
theorem B1578571 : Blo 1578487 1578571 := bstep (se 1 (by rfl) ⟨1183928, by rfl⟩ : syracuseStep 1578571 = 2367857) B2367857
theorem B1578583 : Blo 1578487 1578583 := bstep (se 1 (by rfl) ⟨1183937, by rfl⟩ : syracuseStep 1578583 = 2367875) B2367875
theorem B3552857 : Blo 1578487 3552857 := bstep (se 2 (by rfl) ⟨1332321, by rfl⟩ : syracuseStep 3552857 = 2664643) B2664643
theorem B1578603 : Blo 1578487 1578603 := bstep (se 1 (by rfl) ⟨1183952, by rfl⟩ : syracuseStep 1578603 = 2367905) B2367905
theorem B1578615 : Blo 1578487 1578615 := bstep (se 1 (by rfl) ⟨1183961, by rfl⟩ : syracuseStep 1578615 = 2367923) B2367923
theorem B1578635 : Blo 1578487 1578635 := bstep (se 1 (by rfl) ⟨1183976, by rfl⟩ : syracuseStep 1578635 = 2367953) B2367953
theorem B1578647 : Blo 1578487 1578647 := bstep (se 1 (by rfl) ⟨1183985, by rfl⟩ : syracuseStep 1578647 = 2367971) B2367971
theorem B1578667 : Blo 1578487 1578667 := bstep (se 1 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 1578667 = 2368001) B2368001
theorem B3552947 : Blo 1578487 3552947 := bstep (se 1 (by rfl) ⟨2664710, by rfl⟩ : syracuseStep 3552947 = 5329421) B5329421
theorem B1578679 : Blo 1578487 1578679 := bstep (se 1 (by rfl) ⟨1184009, by rfl⟩ : syracuseStep 1578679 = 2368019) B2368019
theorem B1578699 : Blo 1578487 1578699 := bstep (se 1 (by rfl) ⟨1184024, by rfl⟩ : syracuseStep 1578699 = 2368049) B2368049
theorem B1578711 : Blo 1578487 1578711 := bstep (se 1 (by rfl) ⟨1184033, by rfl⟩ : syracuseStep 1578711 = 2368067) B2368067
theorem B3552983 : Blo 1578487 3552983 := bstep (se 1 (by rfl) ⟨2664737, by rfl⟩ : syracuseStep 3552983 = 5329475) B5329475
theorem B1578731 : Blo 1578487 1578731 := bstep (se 1 (by rfl) ⟨1184048, by rfl⟩ : syracuseStep 1578731 = 2368097) B2368097
theorem B1578743 : Blo 1578487 1578743 := bstep (se 1 (by rfl) ⟨1184057, by rfl⟩ : syracuseStep 1578743 = 2368115) B2368115
theorem B1578763 : Blo 1578487 1578763 := bstep (se 1 (by rfl) ⟨1184072, by rfl⟩ : syracuseStep 1578763 = 2368145) B2368145
theorem B5994263 : Blo 1578487 5994263 := bstep (se 1 (by rfl) ⟨4495697, by rfl⟩ : syracuseStep 5994263 = 8991395) B8991395
theorem B1578775 : Blo 1578487 1578775 := bstep (se 1 (by rfl) ⟨1184081, by rfl⟩ : syracuseStep 1578775 = 2368163) B2368163
theorem B1578795 : Blo 1578487 1578795 := bstep (se 1 (by rfl) ⟨1184096, by rfl⟩ : syracuseStep 1578795 = 2368193) B2368193
theorem B1578807 : Blo 1578487 1578807 := bstep (se 1 (by rfl) ⟨1184105, by rfl⟩ : syracuseStep 1578807 = 2368211) B2368211
theorem B1578827 : Blo 1578487 1578827 := bstep (se 1 (by rfl) ⟨1184120, by rfl⟩ : syracuseStep 1578827 = 2368241) B2368241
theorem B3200843 : Blo 1578487 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B1578839 : Blo 1578487 1578839 := bstep (se 1 (by rfl) ⟨1184129, by rfl⟩ : syracuseStep 1578839 = 2368259) B2368259
theorem B1578859 : Blo 1578487 1578859 := bstep (se 1 (by rfl) ⟨1184144, by rfl⟩ : syracuseStep 1578859 = 2368289) B2368289
theorem B1578871 : Blo 1578487 1578871 := bstep (se 1 (by rfl) ⟨1184153, by rfl⟩ : syracuseStep 1578871 = 2368307) B2368307
theorem B1578891 : Blo 1578487 1578891 := bstep (se 1 (by rfl) ⟨1184168, by rfl⟩ : syracuseStep 1578891 = 2368337) B2368337
theorem B2529163 : Blo 1578487 2529163 := bstep (se 1 (by rfl) ⟨1896872, by rfl⟩ : syracuseStep 2529163 = 3793745) B3793745
theorem B3553163 : Blo 1578487 3553163 := bstep (se 1 (by rfl) ⟨2664872, by rfl⟩ : syracuseStep 3553163 = 5329745) B5329745
theorem B1578903 : Blo 1578487 1578903 := bstep (se 1 (by rfl) ⟨1184177, by rfl⟩ : syracuseStep 1578903 = 2368355) B2368355
theorem B1578923 : Blo 1578487 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B5060531 : Blo 1578487 5060531 := bstep (se 1 (by rfl) ⟨3795398, by rfl⟩ : syracuseStep 5060531 = 7590797) B7590797
theorem B1578935 : Blo 1578487 1578935 := bstep (se 1 (by rfl) ⟨1184201, by rfl⟩ : syracuseStep 1578935 = 2368403) B2368403
theorem B3553217 : Blo 1578487 3553217 := bstep (se 2 (by rfl) ⟨1332456, by rfl⟩ : syracuseStep 3553217 = 2664913) B2664913
theorem B1578955 : Blo 1578487 1578955 := bstep (se 1 (by rfl) ⟨1184216, by rfl⟩ : syracuseStep 1578955 = 2368433) B2368433
theorem B1578967 : Blo 1578487 1578967 := bstep (se 1 (by rfl) ⟨1184225, by rfl⟩ : syracuseStep 1578967 = 2368451) B2368451
theorem B1578987 : Blo 1578487 1578987 := bstep (se 1 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 1578987 = 2368481) B2368481
theorem B1578999 : Blo 1578487 1578999 := bstep (se 1 (by rfl) ⟨1184249, by rfl⟩ : syracuseStep 1578999 = 2368499) B2368499
theorem B1579019 : Blo 1578487 1579019 := bstep (se 1 (by rfl) ⟨1184264, by rfl⟩ : syracuseStep 1579019 = 2368529) B2368529
theorem B1579031 : Blo 1578487 1579031 := bstep (se 1 (by rfl) ⟨1184273, by rfl⟩ : syracuseStep 1579031 = 2368547) B2368547
theorem B1579051 : Blo 1578487 1579051 := bstep (se 1 (by rfl) ⟨1184288, by rfl⟩ : syracuseStep 1579051 = 2368577) B2368577
theorem B10115117 : Blo 1578487 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B1579063 : Blo 1578487 1579063 := bstep (se 1 (by rfl) ⟨1184297, by rfl⟩ : syracuseStep 1579063 = 2368595) B2368595
theorem B1579083 : Blo 1578487 1579083 := bstep (se 1 (by rfl) ⟨1184312, by rfl⟩ : syracuseStep 1579083 = 2368625) B2368625
theorem B1579095 : Blo 1578487 1579095 := bstep (se 1 (by rfl) ⟨1184321, by rfl⟩ : syracuseStep 1579095 = 2368643) B2368643
theorem B1579115 : Blo 1578487 1579115 := bstep (se 1 (by rfl) ⟨1184336, by rfl⟩ : syracuseStep 1579115 = 2368673) B2368673
theorem B1579127 : Blo 1578487 1579127 := bstep (se 1 (by rfl) ⟨1184345, by rfl⟩ : syracuseStep 1579127 = 2368691) B2368691
theorem B1579147 : Blo 1578487 1579147 := bstep (se 1 (by rfl) ⟨1184360, by rfl⟩ : syracuseStep 1579147 = 2368721) B2368721
theorem B1579159 : Blo 1578487 1579159 := bstep (se 1 (by rfl) ⟨1184369, by rfl⟩ : syracuseStep 1579159 = 2368739) B2368739
theorem B5331095 : Blo 1578487 5331095 := bstep (se 1 (by rfl) ⟨3998321, by rfl⟩ : syracuseStep 5331095 = 7996643) B7996643
theorem B3553433 : Blo 1578487 3553433 := bstep (se 2 (by rfl) ⟨1332537, by rfl⟩ : syracuseStep 3553433 = 2665075) B2665075
theorem B1579179 : Blo 1578487 1579179 := bstep (se 1 (by rfl) ⟨1184384, by rfl⟩ : syracuseStep 1579179 = 2368769) B2368769
theorem B3373235 : Blo 1578487 3373235 := bstep (se 1 (by rfl) ⟨2529926, by rfl⟩ : syracuseStep 3373235 = 5059853) B5059853
theorem B1579191 : Blo 1578487 1579191 := bstep (se 1 (by rfl) ⟨1184393, by rfl⟩ : syracuseStep 1579191 = 2368787) B2368787
theorem B3995851 : Blo 1578487 3995851 := bstep (se 1 (by rfl) ⟨2996888, by rfl⟩ : syracuseStep 3995851 = 5993777) B5993777
theorem B1579211 : Blo 1578487 1579211 := bstep (se 1 (by rfl) ⟨1184408, by rfl⟩ : syracuseStep 1579211 = 2368817) B2368817
theorem B1579223 : Blo 1578487 1579223 := bstep (se 1 (by rfl) ⟨1184417, by rfl⟩ : syracuseStep 1579223 = 2368835) B2368835
theorem B1579243 : Blo 1578487 1579243 := bstep (se 1 (by rfl) ⟨1184432, by rfl⟩ : syracuseStep 1579243 = 2368865) B2368865
theorem B3553523 : Blo 1578487 3553523 := bstep (se 1 (by rfl) ⟨2665142, by rfl⟩ : syracuseStep 3553523 = 5330285) B5330285
theorem B1579255 : Blo 1578487 1579255 := bstep (se 1 (by rfl) ⟨1184441, by rfl⟩ : syracuseStep 1579255 = 2368883) B2368883
theorem B1579275 : Blo 1578487 1579275 := bstep (se 1 (by rfl) ⟨1184456, by rfl⟩ : syracuseStep 1579275 = 2368913) B2368913
theorem B1579287 : Blo 1578487 1579287 := bstep (se 1 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 1579287 = 2368931) B2368931
theorem B3553559 : Blo 1578487 3553559 := bstep (se 1 (by rfl) ⟨2665169, by rfl⟩ : syracuseStep 3553559 = 5330339) B5330339
theorem B1579307 : Blo 1578487 1579307 := bstep (se 1 (by rfl) ⟨1184480, by rfl⟩ : syracuseStep 1579307 = 2368961) B2368961
theorem B1579319 : Blo 1578487 1579319 := bstep (se 1 (by rfl) ⟨1184489, by rfl⟩ : syracuseStep 1579319 = 2368979) B2368979
theorem B5691713 : Blo 1578487 5691713 := bstep (se 2 (by rfl) ⟨2134392, by rfl⟩ : syracuseStep 5691713 = 4268785) B4268785
theorem B1775947 : Blo 1578487 1775947 := bstep (se 1 (by rfl) ⟨1331960, by rfl⟩ : syracuseStep 1775947 = 2663921) B2663921
theorem B1579339 : Blo 1578487 1579339 := bstep (se 1 (by rfl) ⟨1184504, by rfl⟩ : syracuseStep 1579339 = 2369009) B2369009
theorem B1579351 : Blo 1578487 1579351 := bstep (se 1 (by rfl) ⟨1184513, by rfl⟩ : syracuseStep 1579351 = 2369027) B2369027
theorem B3995993 : Blo 1578487 3995993 := bstep (se 2 (by rfl) ⟨1498497, by rfl⟩ : syracuseStep 3995993 = 2996995) B2996995
theorem B2529625 : Blo 1578487 2529625 := bstep (se 2 (by rfl) ⟨948609, by rfl⟩ : syracuseStep 2529625 = 1897219) B1897219
theorem B1579371 : Blo 1578487 1579371 := bstep (se 1 (by rfl) ⟨1184528, by rfl⟩ : syracuseStep 1579371 = 2369057) B2369057
theorem B1579383 : Blo 1578487 1579383 := bstep (se 1 (by rfl) ⟨1184537, by rfl⟩ : syracuseStep 1579383 = 2369075) B2369075
theorem B1579403 : Blo 1578487 1579403 := bstep (se 1 (by rfl) ⟨1184552, by rfl⟩ : syracuseStep 1579403 = 2369105) B2369105
theorem B1579415 : Blo 1578487 1579415 := bstep (se 1 (by rfl) ⟨1184561, by rfl⟩ : syracuseStep 1579415 = 2369123) B2369123
theorem B1579435 : Blo 1578487 1579435 := bstep (se 1 (by rfl) ⟨1184576, by rfl⟩ : syracuseStep 1579435 = 2369153) B2369153
theorem B5994931 : Blo 1578487 5994931 := bstep (se 1 (by rfl) ⟨4496198, by rfl⟩ : syracuseStep 5994931 = 8992397) B8992397
theorem B1776055 : Blo 1578487 1776055 := bstep (se 1 (by rfl) ⟨1332041, by rfl⟩ : syracuseStep 1776055 = 2664083) B2664083
theorem B1579447 : Blo 1578487 1579447 := bstep (se 1 (by rfl) ⟨1184585, by rfl⟩ : syracuseStep 1579447 = 2369171) B2369171
theorem B3553739 : Blo 1578487 3553739 := bstep (se 1 (by rfl) ⟨2665304, by rfl⟩ : syracuseStep 3553739 = 5330609) B5330609
theorem B1579467 : Blo 1578487 1579467 := bstep (se 1 (by rfl) ⟨1184600, by rfl⟩ : syracuseStep 1579467 = 2369201) B2369201
theorem B1579479 : Blo 1578487 1579479 := bstep (se 1 (by rfl) ⟨1184609, by rfl⟩ : syracuseStep 1579479 = 2369219) B2369219
theorem B1579499 : Blo 1578487 1579499 := bstep (se 1 (by rfl) ⟨1184624, by rfl⟩ : syracuseStep 1579499 = 2369249) B2369249
theorem B1579511 : Blo 1578487 1579511 := bstep (se 1 (by rfl) ⟨1184633, by rfl⟩ : syracuseStep 1579511 = 2369267) B2369267
theorem B3553793 : Blo 1578487 3553793 := bstep (se 2 (by rfl) ⟨1332672, by rfl⟩ : syracuseStep 3553793 = 2665345) B2665345
theorem B1579531 : Blo 1578487 1579531 := bstep (se 1 (by rfl) ⟨1184648, by rfl⟩ : syracuseStep 1579531 = 2369297) B2369297
theorem B1579543 : Blo 1578487 1579543 := bstep (se 1 (by rfl) ⟨1184657, by rfl⟩ : syracuseStep 1579543 = 2369315) B2369315
theorem B1579563 : Blo 1578487 1579563 := bstep (se 1 (by rfl) ⟨1184672, by rfl⟩ : syracuseStep 1579563 = 2369345) B2369345
theorem B6076973 : Blo 1578487 6076973 := bstep (se 3 (by rfl) ⟨1139432, by rfl⟩ : syracuseStep 6076973 = 2278865) B2278865
theorem B1579575 : Blo 1578487 1579575 := bstep (se 1 (by rfl) ⟨1184681, by rfl⟩ : syracuseStep 1579575 = 2369363) B2369363
theorem B1579595 : Blo 1578487 1579595 := bstep (se 1 (by rfl) ⟨1184696, by rfl⟩ : syracuseStep 1579595 = 2369393) B2369393
theorem B1579607 : Blo 1578487 1579607 := bstep (se 1 (by rfl) ⟨1184705, by rfl⟩ : syracuseStep 1579607 = 2369411) B2369411
theorem B2529881 : Blo 1578487 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B1776235 : Blo 1578487 1776235 := bstep (se 1 (by rfl) ⟨1332176, by rfl⟩ : syracuseStep 1776235 = 2664353) B2664353
theorem B1579627 : Blo 1578487 1579627 := bstep (se 1 (by rfl) ⟨1184720, by rfl⟩ : syracuseStep 1579627 = 2369441) B2369441
theorem B2996851 : Blo 1578487 2996851 := bstep (se 1 (by rfl) ⟨2247638, by rfl⟩ : syracuseStep 2996851 = 4495277) B4495277
theorem B1579639 : Blo 1578487 1579639 := bstep (se 1 (by rfl) ⟨1184729, by rfl⟩ : syracuseStep 1579639 = 2369459) B2369459
theorem B1579659 : Blo 1578487 1579659 := bstep (se 1 (by rfl) ⟨1184744, by rfl⟩ : syracuseStep 1579659 = 2369489) B2369489
theorem B17980055 : Blo 1578487 17980055 := bstep (se 1 (by rfl) ⟨13485041, by rfl⟩ : syracuseStep 17980055 = 26970083) B26970083
theorem B1579671 : Blo 1578487 1579671 := bstep (se 1 (by rfl) ⟨1184753, by rfl⟩ : syracuseStep 1579671 = 2369507) B2369507
theorem B1579691 : Blo 1578487 1579691 := bstep (se 1 (by rfl) ⟨1184768, by rfl⟩ : syracuseStep 1579691 = 2369537) B2369537
theorem B5331635 : Blo 1578487 5331635 := bstep (se 1 (by rfl) ⟨3998726, by rfl⟩ : syracuseStep 5331635 = 7997453) B7997453
theorem B1579703 : Blo 1578487 1579703 := bstep (se 1 (by rfl) ⟨1184777, by rfl⟩ : syracuseStep 1579703 = 2369555) B2369555
theorem B1579723 : Blo 1578487 1579723 := bstep (se 1 (by rfl) ⟨1184792, by rfl⟩ : syracuseStep 1579723 = 2369585) B2369585
theorem B1776343 : Blo 1578487 1776343 := bstep (se 1 (by rfl) ⟨1332257, by rfl⟩ : syracuseStep 1776343 = 2664515) B2664515
theorem B3201751 : Blo 1578487 3201751 := bstep (se 1 (by rfl) ⟨2401313, by rfl⟩ : syracuseStep 3201751 = 4802627) B4802627
theorem B3554009 : Blo 1578487 3554009 := bstep (se 2 (by rfl) ⟨1332753, by rfl⟩ : syracuseStep 3554009 = 2665507) B2665507
theorem B1579735 : Blo 1578487 1579735 := bstep (se 1 (by rfl) ⟨1184801, by rfl⟩ : syracuseStep 1579735 = 2369603) B2369603
theorem B1579755 : Blo 1578487 1579755 := bstep (se 1 (by rfl) ⟨1184816, by rfl⟩ : syracuseStep 1579755 = 2369633) B2369633
theorem B1579767 : Blo 1578487 1579767 := bstep (se 1 (by rfl) ⟨1184825, by rfl⟩ : syracuseStep 1579767 = 2369651) B2369651
theorem B1579787 : Blo 1578487 1579787 := bstep (se 1 (by rfl) ⟨1184840, by rfl⟩ : syracuseStep 1579787 = 2369681) B2369681
theorem B7306001 : Blo 1578487 7306001 := bstep (se 2 (by rfl) ⟨2739750, by rfl⟩ : syracuseStep 7306001 = 5479501) B5479501
theorem B1579799 : Blo 1578487 1579799 := bstep (se 1 (by rfl) ⟨1184849, by rfl⟩ : syracuseStep 1579799 = 2369699) B2369699
theorem B1579819 : Blo 1578487 1579819 := bstep (se 1 (by rfl) ⟨1184864, by rfl⟩ : syracuseStep 1579819 = 2369729) B2369729
theorem B3554099 : Blo 1578487 3554099 := bstep (se 1 (by rfl) ⟨2665574, by rfl⟩ : syracuseStep 3554099 = 5331149) B5331149
theorem B6404915 : Blo 1578487 6404915 := bstep (se 1 (by rfl) ⟨4803686, by rfl⟩ : syracuseStep 6404915 = 9607373) B9607373
theorem B1579831 : Blo 1578487 1579831 := bstep (se 1 (by rfl) ⟨1184873, by rfl⟩ : syracuseStep 1579831 = 2369747) B2369747
theorem B1579851 : Blo 1578487 1579851 := bstep (se 1 (by rfl) ⟨1184888, by rfl⟩ : syracuseStep 1579851 = 2369777) B2369777
theorem B3554135 : Blo 1578487 3554135 := bstep (se 1 (by rfl) ⟨2665601, by rfl⟩ : syracuseStep 3554135 = 5331203) B5331203
theorem B1579863 : Blo 1578487 1579863 := bstep (se 1 (by rfl) ⟨1184897, by rfl⟩ : syracuseStep 1579863 = 2369795) B2369795
theorem B1579883 : Blo 1578487 1579883 := bstep (se 1 (by rfl) ⟨1184912, by rfl⟩ : syracuseStep 1579883 = 2369825) B2369825
theorem B1579895 : Blo 1578487 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B1776523 : Blo 1578487 1776523 := bstep (se 1 (by rfl) ⟨1332392, by rfl⟩ : syracuseStep 1776523 = 2664785) B2664785
theorem B1579915 : Blo 1578487 1579915 := bstep (se 1 (by rfl) ⟨1184936, by rfl⟩ : syracuseStep 1579915 = 2369873) B2369873
theorem B1579927 : Blo 1578487 1579927 := bstep (se 1 (by rfl) ⟨1184945, by rfl⟩ : syracuseStep 1579927 = 2369891) B2369891
theorem B1579947 : Blo 1578487 1579947 := bstep (se 1 (by rfl) ⟨1184960, by rfl⟩ : syracuseStep 1579947 = 2369921) B2369921
theorem B1579959 : Blo 1578487 1579959 := bstep (se 1 (by rfl) ⟨1184969, by rfl⟩ : syracuseStep 1579959 = 2369939) B2369939
theorem B5331905 : Blo 1578487 5331905 := bstep (se 2 (by rfl) ⟨1999464, by rfl⟩ : syracuseStep 5331905 = 3998929) B3998929
theorem B1579979 : Blo 1578487 1579979 := bstep (se 1 (by rfl) ⟨1184984, by rfl⟩ : syracuseStep 1579979 = 2369969) B2369969
theorem B1579991 : Blo 1578487 1579991 := bstep (se 1 (by rfl) ⟨1184993, by rfl⟩ : syracuseStep 1579991 = 2369987) B2369987
theorem B1580011 : Blo 1578487 1580011 := bstep (se 1 (by rfl) ⟨1185008, by rfl⟩ : syracuseStep 1580011 = 2370017) B2370017
theorem B1776631 : Blo 1578487 1776631 := bstep (se 1 (by rfl) ⟨1332473, by rfl⟩ : syracuseStep 1776631 = 2664947) B2664947
theorem B1580023 : Blo 1578487 1580023 := bstep (se 1 (by rfl) ⟨1185017, by rfl⟩ : syracuseStep 1580023 = 2370035) B2370035
theorem B3554315 : Blo 1578487 3554315 := bstep (se 1 (by rfl) ⟨2665736, by rfl⟩ : syracuseStep 3554315 = 5331473) B5331473
theorem B1580043 : Blo 1578487 1580043 := bstep (se 1 (by rfl) ⟨1185032, by rfl⟩ : syracuseStep 1580043 = 2370065) B2370065
theorem B1580055 : Blo 1578487 1580055 := bstep (se 1 (by rfl) ⟨1185041, by rfl⟩ : syracuseStep 1580055 = 2370083) B2370083
theorem B1580075 : Blo 1578487 1580075 := bstep (se 1 (by rfl) ⟨1185056, by rfl⟩ : syracuseStep 1580075 = 2370113) B2370113
theorem B2997299 : Blo 1578487 2997299 := bstep (se 1 (by rfl) ⟨2247974, by rfl⟩ : syracuseStep 2997299 = 4495949) B4495949
theorem B3374131 : Blo 1578487 3374131 := bstep (se 1 (by rfl) ⟨2530598, by rfl⟩ : syracuseStep 3374131 = 5061197) B5061197
theorem B1580087 : Blo 1578487 1580087 := bstep (se 1 (by rfl) ⟨1185065, by rfl⟩ : syracuseStep 1580087 = 2370131) B2370131
theorem B3554369 : Blo 1578487 3554369 := bstep (se 2 (by rfl) ⟨1332888, by rfl⟩ : syracuseStep 3554369 = 2665777) B2665777
theorem B1580107 : Blo 1578487 1580107 := bstep (se 1 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 1580107 = 2370161) B2370161
theorem B1580119 : Blo 1578487 1580119 := bstep (se 1 (by rfl) ⟨1185089, by rfl⟩ : syracuseStep 1580119 = 2370179) B2370179
theorem B2997337 : Blo 1578487 2997337 := bstep (se 2 (by rfl) ⟨1124001, by rfl⟩ : syracuseStep 2997337 = 2248003) B2248003
theorem B1580139 : Blo 1578487 1580139 := bstep (se 1 (by rfl) ⟨1185104, by rfl⟩ : syracuseStep 1580139 = 2370209) B2370209
theorem B1580151 : Blo 1578487 1580151 := bstep (se 1 (by rfl) ⟨1185113, by rfl⟩ : syracuseStep 1580151 = 2370227) B2370227
theorem B1580171 : Blo 1578487 1580171 := bstep (se 1 (by rfl) ⟨1185128, by rfl⟩ : syracuseStep 1580171 = 2370257) B2370257
theorem B3996823 : Blo 1578487 3996823 := bstep (se 1 (by rfl) ⟨2997617, by rfl⟩ : syracuseStep 3996823 = 5995235) B5995235
theorem B1580183 : Blo 1578487 1580183 := bstep (se 1 (by rfl) ⟨1185137, by rfl⟩ : syracuseStep 1580183 = 2370275) B2370275
theorem B1776811 : Blo 1578487 1776811 := bstep (se 1 (by rfl) ⟨1332608, by rfl⟩ : syracuseStep 1776811 = 2665217) B2665217
theorem B1580203 : Blo 1578487 1580203 := bstep (se 1 (by rfl) ⟨1185152, by rfl⟩ : syracuseStep 1580203 = 2370305) B2370305
theorem B4496563 : Blo 1578487 4496563 := bstep (se 1 (by rfl) ⟨3372422, by rfl⟩ : syracuseStep 4496563 = 6744845) B6744845
theorem B22764725 : Blo 1578487 22764725 := bstep (se 5 (by rfl) ⟨1067096, by rfl⟩ : syracuseStep 22764725 = 2134193) B2134193
theorem B1580215 : Blo 1578487 1580215 := bstep (se 1 (by rfl) ⟨1185161, by rfl⟩ : syracuseStep 1580215 = 2370323) B2370323
theorem B1580235 : Blo 1578487 1580235 := bstep (se 1 (by rfl) ⟨1185176, by rfl⟩ : syracuseStep 1580235 = 2370353) B2370353
theorem B1580247 : Blo 1578487 1580247 := bstep (se 1 (by rfl) ⟨1185185, by rfl⟩ : syracuseStep 1580247 = 2370371) B2370371
theorem B1580267 : Blo 1578487 1580267 := bstep (se 1 (by rfl) ⟨1185200, by rfl⟩ : syracuseStep 1580267 = 2370401) B2370401
theorem B1580279 : Blo 1578487 1580279 := bstep (se 1 (by rfl) ⟨1185209, by rfl⟩ : syracuseStep 1580279 = 2370419) B2370419
theorem B1580299 : Blo 1578487 1580299 := bstep (se 1 (by rfl) ⟨1185224, by rfl⟩ : syracuseStep 1580299 = 2370449) B2370449
theorem B1998103 : Blo 1578487 1998103 := bstep (se 1 (by rfl) ⟨1498577, by rfl⟩ : syracuseStep 1998103 = 2997155) B2997155
theorem B1776919 : Blo 1578487 1776919 := bstep (se 1 (by rfl) ⟨1332689, by rfl⟩ : syracuseStep 1776919 = 2665379) B2665379
theorem B3554585 : Blo 1578487 3554585 := bstep (se 2 (by rfl) ⟨1332969, by rfl⟩ : syracuseStep 3554585 = 2665939) B2665939
theorem B1580311 : Blo 1578487 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B1580331 : Blo 1578487 1580331 := bstep (se 1 (by rfl) ⟨1185248, by rfl⟩ : syracuseStep 1580331 = 2370497) B2370497
theorem B1580343 : Blo 1578487 1580343 := bstep (se 1 (by rfl) ⟨1185257, by rfl⟩ : syracuseStep 1580343 = 2370515) B2370515
theorem B7994699 : Blo 1578487 7994699 := bstep (se 1 (by rfl) ⟨5996024, by rfl⟩ : syracuseStep 7994699 = 11992049) B11992049
theorem B1580363 : Blo 1578487 1580363 := bstep (se 1 (by rfl) ⟨1185272, by rfl⟩ : syracuseStep 1580363 = 2370545) B2370545
theorem B1580375 : Blo 1578487 1580375 := bstep (se 1 (by rfl) ⟨1185281, by rfl⟩ : syracuseStep 1580375 = 2370563) B2370563
theorem B1580395 : Blo 1578487 1580395 := bstep (se 1 (by rfl) ⟨1185296, by rfl⟩ : syracuseStep 1580395 = 2370593) B2370593
theorem B3554675 : Blo 1578487 3554675 := bstep (se 1 (by rfl) ⟨2666006, by rfl⟩ : syracuseStep 3554675 = 5332013) B5332013
theorem B1580407 : Blo 1578487 1580407 := bstep (se 1 (by rfl) ⟨1185305, by rfl⟩ : syracuseStep 1580407 = 2370611) B2370611
theorem B1580427 : Blo 1578487 1580427 := bstep (se 1 (by rfl) ⟨1185320, by rfl⟩ : syracuseStep 1580427 = 2370641) B2370641
theorem B4496791 : Blo 1578487 4496791 := bstep (se 1 (by rfl) ⟨3372593, by rfl⟩ : syracuseStep 4496791 = 6745187) B6745187
theorem B3554711 : Blo 1578487 3554711 := bstep (se 1 (by rfl) ⟨2666033, by rfl⟩ : syracuseStep 3554711 = 5332067) B5332067
theorem B1580439 : Blo 1578487 1580439 := bstep (se 1 (by rfl) ⟨1185329, by rfl⟩ : syracuseStep 1580439 = 2370659) B2370659
theorem B1580459 : Blo 1578487 1580459 := bstep (se 1 (by rfl) ⟨1185344, by rfl⟩ : syracuseStep 1580459 = 2370689) B2370689
theorem B1580471 : Blo 1578487 1580471 := bstep (se 1 (by rfl) ⟨1185353, by rfl⟩ : syracuseStep 1580471 = 2370707) B2370707
theorem B1777099 : Blo 1578487 1777099 := bstep (se 1 (by rfl) ⟨1332824, by rfl⟩ : syracuseStep 1777099 = 2665649) B2665649
theorem B5332445 : Blo 1578487 5332445 := bstep (se 3 (by rfl) ⟨999833, by rfl⟩ : syracuseStep 5332445 = 1999667) B1999667
theorem B2997785 : Blo 1578487 2997785 := bstep (se 2 (by rfl) ⟨1124169, by rfl⟩ : syracuseStep 2997785 = 2248339) B2248339
theorem B1777207 : Blo 1578487 1777207 := bstep (se 1 (by rfl) ⟨1332905, by rfl⟩ : syracuseStep 1777207 = 2665811) B2665811
theorem B3997259 : Blo 1578487 3997259 := bstep (se 1 (by rfl) ⟨2997944, by rfl⟩ : syracuseStep 3997259 = 5995889) B5995889
theorem B23076427 : Blo 1578487 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B3554891 : Blo 1578487 3554891 := bstep (se 1 (by rfl) ⟨2666168, by rfl⟩ : syracuseStep 3554891 = 5332337) B5332337
theorem B3554945 : Blo 1578487 3554945 := bstep (se 2 (by rfl) ⟨1333104, by rfl⟩ : syracuseStep 3554945 = 2666209) B2666209
theorem B5996177 : Blo 1578487 5996177 := bstep (se 2 (by rfl) ⟨2248566, by rfl⟩ : syracuseStep 5996177 = 4497133) B4497133
theorem B11378353 : Blo 1578487 11378353 := bstep (se 2 (by rfl) ⟨4266882, by rfl⟩ : syracuseStep 11378353 = 8533765) B8533765
theorem B1777387 : Blo 1578487 1777387 := bstep (se 1 (by rfl) ⟨1333040, by rfl⟩ : syracuseStep 1777387 = 2666081) B2666081
theorem B1687339 : Blo 1578487 1687339 := bstep (se 1 (by rfl) ⟨1265504, by rfl⟩ : syracuseStep 1687339 = 2531009) B2531009
theorem B1777495 : Blo 1578487 1777495 := bstep (se 1 (by rfl) ⟨1333121, by rfl⟩ : syracuseStep 1777495 = 2666243) B2666243
theorem B3555161 : Blo 1578487 3555161 := bstep (se 2 (by rfl) ⟨1333185, by rfl⟩ : syracuseStep 3555161 = 2666371) B2666371
theorem B92348261 : Blo 1578487 92348261 := bstep (se 4 (by rfl) ⟨8657649, by rfl⟩ : syracuseStep 92348261 = 17315299) B17315299
theorem B3555251 : Blo 1578487 3555251 := bstep (se 1 (by rfl) ⟨2666438, by rfl⟩ : syracuseStep 3555251 = 5332877) B5332877
theorem B3997633 : Blo 1578487 3997633 := bstep (se 2 (by rfl) ⟨1499112, by rfl⟩ : syracuseStep 3997633 = 2998225) B2998225
theorem B3555287 : Blo 1578487 3555287 := bstep (se 1 (by rfl) ⟨2666465, by rfl⟩ : syracuseStep 3555287 = 5332931) B5332931
theorem B5062621 : Blo 1578487 5062621 := bstep (se 3 (by rfl) ⟨949241, by rfl⟩ : syracuseStep 5062621 = 1898483) B1898483
theorem B4325405 : Blo 1578487 4325405 := bstep (se 3 (by rfl) ⟨811013, by rfl⟩ : syracuseStep 4325405 = 1622027) B1622027
theorem B3702827 : Blo 1578487 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B1802299 : Blo 1578487 1802299 := bstep (se 1 (by rfl) ⟨1351724, by rfl⟩ : syracuseStep 1802299 = 2703449) B2703449
theorem B5996663 : Blo 1578487 5996663 := bstep (se 1 (by rfl) ⟨4497497, by rfl⟩ : syracuseStep 5996663 = 8994995) B8994995
theorem B1999019 : Blo 1578487 1999019 := bstep (se 1 (by rfl) ⟨1499264, by rfl⟩ : syracuseStep 1999019 = 2998529) B2998529
theorem B2162873 : Blo 1578487 2162873 := bstep (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) B1622155
theorem B11387117 : Blo 1578487 11387117 := bstep (se 3 (by rfl) ⟨2135084, by rfl⟩ : syracuseStep 11387117 = 4270169) B4270169
theorem B1777927 : Blo 1578487 1777927 := bstep (se 1 (by rfl) ⟨1333445, by rfl⟩ : syracuseStep 1777927 = 2666891) B2666891
theorem B2367803 : Blo 1578487 2367803 := bstep (se 1 (by rfl) ⟨1775852, by rfl⟩ : syracuseStep 2367803 = 3551705) B3551705
theorem B5333363 : Blo 1578487 5333363 := bstep (se 1 (by rfl) ⟨4000022, by rfl⟩ : syracuseStep 5333363 = 8000045) B8000045
theorem B2367863 : Blo 1578487 2367863 := bstep (se 1 (by rfl) ⟨1775897, by rfl⟩ : syracuseStep 2367863 = 3551795) B3551795
theorem B3555719 : Blo 1578487 3555719 := bstep (se 1 (by rfl) ⟨2666789, by rfl⟩ : syracuseStep 3555719 = 5333579) B5333579
theorem B2367887 : Blo 1578487 2367887 := bstep (se 1 (by rfl) ⟨1775915, by rfl⟩ : syracuseStep 2367887 = 3551831) B3551831
theorem B3998099 : Blo 1578487 3998099 := bstep (se 1 (by rfl) ⟨2998574, by rfl⟩ : syracuseStep 3998099 = 5997149) B5997149
theorem B2367929 : Blo 1578487 2367929 := bstep (se 2 (by rfl) ⟨887973, by rfl⟩ : syracuseStep 2367929 = 1775947) B1775947
theorem B7995833 : Blo 1578487 7995833 := bstep (se 2 (by rfl) ⟨2998437, by rfl⟩ : syracuseStep 7995833 = 5996875) B5996875
theorem B2368007 : Blo 1578487 2368007 := bstep (se 1 (by rfl) ⟨1776005, by rfl⟩ : syracuseStep 2368007 = 3552011) B3552011
theorem B2368043 : Blo 1578487 2368043 := bstep (se 1 (by rfl) ⟨1776032, by rfl⟩ : syracuseStep 2368043 = 3552065) B3552065
theorem B3555899 : Blo 1578487 3555899 := bstep (se 1 (by rfl) ⟨2666924, by rfl⟩ : syracuseStep 3555899 = 5333849) B5333849
theorem B2368073 : Blo 1578487 2368073 := bstep (se 2 (by rfl) ⟨888027, by rfl⟩ : syracuseStep 2368073 = 1776055) B1776055
theorem B1999495 : Blo 1578487 1999495 := bstep (se 1 (by rfl) ⟨1499621, by rfl⟩ : syracuseStep 1999495 = 2999243) B2999243
theorem B4498067 : Blo 1578487 4498067 := bstep (se 1 (by rfl) ⟨3373550, by rfl⟩ : syracuseStep 4498067 = 6747101) B6747101
theorem B3998393 : Blo 1578487 3998393 := bstep (se 2 (by rfl) ⟨1499397, by rfl⟩ : syracuseStep 3998393 = 2998795) B2998795
theorem B3556025 : Blo 1578487 3556025 := bstep (se 2 (by rfl) ⟨1333509, by rfl⟩ : syracuseStep 3556025 = 2667019) B2667019
theorem B2368187 : Blo 1578487 2368187 := bstep (se 1 (by rfl) ⟨1776140, by rfl⟩ : syracuseStep 2368187 = 3552281) B3552281
theorem B2368247 : Blo 1578487 2368247 := bstep (se 1 (by rfl) ⟨1776185, by rfl⟩ : syracuseStep 2368247 = 3552371) B3552371
theorem B5767937 : Blo 1578487 5767937 := bstep (se 2 (by rfl) ⟨2162976, by rfl⟩ : syracuseStep 5767937 = 4325953) B4325953
theorem B2368271 : Blo 1578487 2368271 := bstep (se 1 (by rfl) ⟨1776203, by rfl⟩ : syracuseStep 2368271 = 3552407) B3552407
theorem B2368313 : Blo 1578487 2368313 := bstep (se 2 (by rfl) ⟨888117, by rfl⟩ : syracuseStep 2368313 = 1776235) B1776235
theorem B2999099 : Blo 1578487 2999099 := bstep (se 1 (by rfl) ⟨2249324, by rfl⟩ : syracuseStep 2999099 = 4498649) B4498649
theorem B2564983 : Blo 1578487 2564983 := bstep (se 1 (by rfl) ⟨1923737, by rfl⟩ : syracuseStep 2564983 = 3847475) B3847475
theorem B2368391 : Blo 1578487 2368391 := bstep (se 1 (by rfl) ⟨1776293, by rfl⟩ : syracuseStep 2368391 = 3552587) B3552587
theorem B2368427 : Blo 1578487 2368427 := bstep (se 1 (by rfl) ⟨1776320, by rfl⟩ : syracuseStep 2368427 = 3552641) B3552641
theorem B8995769 : Blo 1578487 8995769 := bstep (se 2 (by rfl) ⟨3373413, by rfl⟩ : syracuseStep 8995769 = 6746827) B6746827
theorem B2401211 : Blo 1578487 2401211 := bstep (se 1 (by rfl) ⟨1800908, by rfl⟩ : syracuseStep 2401211 = 3601817) B3601817
theorem B2368457 : Blo 1578487 2368457 := bstep (se 2 (by rfl) ⟨888171, by rfl⟩ : syracuseStep 2368457 = 1776343) B1776343
theorem B2368571 : Blo 1578487 2368571 := bstep (se 1 (by rfl) ⟨1776428, by rfl⟩ : syracuseStep 2368571 = 3552857) B3552857
theorem B5997635 : Blo 1578487 5997635 := bstep (se 1 (by rfl) ⟨4498226, by rfl⟩ : syracuseStep 5997635 = 8996453) B8996453
theorem B22774871 : Blo 1578487 22774871 := bstep (se 1 (by rfl) ⟨17081153, by rfl⟩ : syracuseStep 22774871 = 34162307) B34162307
theorem B2368631 : Blo 1578487 2368631 := bstep (se 1 (by rfl) ⟨1776473, by rfl⟩ : syracuseStep 2368631 = 3552947) B3552947
theorem B1999991 : Blo 1578487 1999991 := bstep (se 1 (by rfl) ⟨1499993, by rfl⟩ : syracuseStep 1999991 = 2999987) B2999987
theorem B2368655 : Blo 1578487 2368655 := bstep (se 1 (by rfl) ⟨1776491, by rfl⟩ : syracuseStep 2368655 = 3552983) B3552983
theorem B2368697 : Blo 1578487 2368697 := bstep (se 2 (by rfl) ⟨888261, by rfl⟩ : syracuseStep 2368697 = 1776523) B1776523
theorem B7693505 : Blo 1578487 7693505 := bstep (se 2 (by rfl) ⟨2885064, by rfl⟩ : syracuseStep 7693505 = 5770129) B5770129
theorem B2368775 : Blo 1578487 2368775 := bstep (se 1 (by rfl) ⟨1776581, by rfl⟩ : syracuseStep 2368775 = 3553163) B3553163
theorem B2000143 : Blo 1578487 2000143 := bstep (se 1 (by rfl) ⟨1500107, by rfl⟩ : syracuseStep 2000143 = 3000215) B3000215
theorem B2999585 : Blo 1578487 2999585 := bstep (se 2 (by rfl) ⟨1124844, by rfl⟩ : syracuseStep 2999585 = 2249689) B2249689
theorem B2368811 : Blo 1578487 2368811 := bstep (se 1 (by rfl) ⟨1776608, by rfl⟩ : syracuseStep 2368811 = 3553217) B3553217
theorem B2368841 : Blo 1578487 2368841 := bstep (se 2 (by rfl) ⟨888315, by rfl⟩ : syracuseStep 2368841 = 1776631) B1776631
theorem B6743411 : Blo 1578487 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B3999091 : Blo 1578487 3999091 := bstep (se 1 (by rfl) ⟨2999318, by rfl⟩ : syracuseStep 3999091 = 5998637) B5998637
theorem B4498841 : Blo 1578487 4498841 := bstep (se 2 (by rfl) ⟨1687065, by rfl⟩ : syracuseStep 4498841 = 3374131) B3374131
theorem B2368955 : Blo 1578487 2368955 := bstep (se 1 (by rfl) ⟨1776716, by rfl⟩ : syracuseStep 2368955 = 3553433) B3553433
theorem B6489553 : Blo 1578487 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B2369015 : Blo 1578487 2369015 := bstep (se 1 (by rfl) ⟨1776761, by rfl⟩ : syracuseStep 2369015 = 3553523) B3553523
theorem B3999233 : Blo 1578487 3999233 := bstep (se 2 (by rfl) ⟨1499712, by rfl⟩ : syracuseStep 3999233 = 2999425) B2999425
theorem B2369039 : Blo 1578487 2369039 := bstep (se 1 (by rfl) ⟨1776779, by rfl⟩ : syracuseStep 2369039 = 3553559) B3553559
theorem B2369081 : Blo 1578487 2369081 := bstep (se 2 (by rfl) ⟨888405, by rfl⟩ : syracuseStep 2369081 = 1776811) B1776811
theorem B2663995 : Blo 1578487 2663995 := bstep (se 1 (by rfl) ⟨1997996, by rfl⟩ : syracuseStep 2663995 = 3995993) B3995993
theorem B2369159 : Blo 1578487 2369159 := bstep (se 1 (by rfl) ⟨1776869, by rfl⟩ : syracuseStep 2369159 = 3553739) B3553739
theorem B2369195 : Blo 1578487 2369195 := bstep (se 1 (by rfl) ⟨1776896, by rfl⟩ : syracuseStep 2369195 = 3553793) B3553793
theorem B2664137 : Blo 1578487 2664137 := bstep (se 2 (by rfl) ⟨999051, by rfl⟩ : syracuseStep 2664137 = 1998103) B1998103
theorem B2369225 : Blo 1578487 2369225 := bstep (se 2 (by rfl) ⟨888459, by rfl⟩ : syracuseStep 2369225 = 1776919) B1776919
theorem B7997129 : Blo 1578487 7997129 := bstep (se 2 (by rfl) ⟨2998923, by rfl⟩ : syracuseStep 7997129 = 5997847) B5997847
theorem B11986703 : Blo 1578487 11986703 := bstep (se 1 (by rfl) ⟨8990027, by rfl⟩ : syracuseStep 11986703 = 17980055) B17980055
theorem B2369339 : Blo 1578487 2369339 := bstep (se 1 (by rfl) ⟨1777004, by rfl⟩ : syracuseStep 2369339 = 3554009) B3554009
theorem B2369399 : Blo 1578487 2369399 := bstep (se 1 (by rfl) ⟨1777049, by rfl⟩ : syracuseStep 2369399 = 3554099) B3554099
theorem B4269943 : Blo 1578487 4269943 := bstep (se 1 (by rfl) ⟨3202457, by rfl⟩ : syracuseStep 4269943 = 6404915) B6404915
theorem B2369423 : Blo 1578487 2369423 := bstep (se 1 (by rfl) ⟨1777067, by rfl⟩ : syracuseStep 2369423 = 3554135) B3554135
theorem B2369465 : Blo 1578487 2369465 := bstep (se 2 (by rfl) ⟨888549, by rfl⟩ : syracuseStep 2369465 = 1777099) B1777099
theorem B3999689 : Blo 1578487 3999689 := bstep (se 2 (by rfl) ⟨1499883, by rfl⟩ : syracuseStep 3999689 = 2999767) B2999767
theorem B2369543 : Blo 1578487 2369543 := bstep (se 1 (by rfl) ⟨1777157, by rfl⟩ : syracuseStep 2369543 = 3554315) B3554315
theorem B2369579 : Blo 1578487 2369579 := bstep (se 1 (by rfl) ⟨1777184, by rfl⟩ : syracuseStep 2369579 = 3554369) B3554369
theorem B2369609 : Blo 1578487 2369609 := bstep (se 2 (by rfl) ⟨888603, by rfl⟩ : syracuseStep 2369609 = 1777207) B1777207
theorem B2369723 : Blo 1578487 2369723 := bstep (se 1 (by rfl) ⟨1777292, by rfl⟩ : syracuseStep 2369723 = 3554585) B3554585
theorem B2369783 : Blo 1578487 2369783 := bstep (se 1 (by rfl) ⟨1777337, by rfl⟩ : syracuseStep 2369783 = 3554675) B3554675
theorem B2369807 : Blo 1578487 2369807 := bstep (se 1 (by rfl) ⟨1777355, by rfl⟩ : syracuseStep 2369807 = 3554711) B3554711
theorem B4000043 : Blo 1578487 4000043 := bstep (se 1 (by rfl) ⟨3000032, by rfl⟩ : syracuseStep 4000043 = 6000065) B6000065
theorem B2369849 : Blo 1578487 2369849 := bstep (se 2 (by rfl) ⟨888693, by rfl⟩ : syracuseStep 2369849 = 1777387) B1777387
theorem B11995451 : Blo 1578487 11995451 := bstep (se 1 (by rfl) ⟨8996588, by rfl⟩ : syracuseStep 11995451 = 17993177) B17993177
theorem B9013619 : Blo 1578487 9013619 := bstep (se 1 (by rfl) ⟨6760214, by rfl⟩ : syracuseStep 9013619 = 13520429) B13520429
theorem B2664839 : Blo 1578487 2664839 := bstep (se 1 (by rfl) ⟨1998629, by rfl⟩ : syracuseStep 2664839 = 3997259) B3997259
theorem B2369927 : Blo 1578487 2369927 := bstep (se 1 (by rfl) ⟨1777445, by rfl⟩ : syracuseStep 2369927 = 3554891) B3554891
theorem B9603481 : Blo 1578487 9603481 := bstep (se 2 (by rfl) ⟨3601305, by rfl⟩ : syracuseStep 9603481 = 7202611) B7202611
theorem B2369963 : Blo 1578487 2369963 := bstep (se 1 (by rfl) ⟨1777472, by rfl⟩ : syracuseStep 2369963 = 3554945) B3554945
theorem B2369993 : Blo 1578487 2369993 := bstep (se 2 (by rfl) ⟨888747, by rfl⟩ : syracuseStep 2369993 = 1777495) B1777495
theorem B2370107 : Blo 1578487 2370107 := bstep (se 1 (by rfl) ⟨1777580, by rfl⟩ : syracuseStep 2370107 = 3555161) B3555161
theorem B61565507 : Blo 1578487 61565507 := bstep (se 1 (by rfl) ⟨46174130, by rfl⟩ : syracuseStep 61565507 = 92348261) B92348261
theorem B2370167 : Blo 1578487 2370167 := bstep (se 1 (by rfl) ⟨1777625, by rfl⟩ : syracuseStep 2370167 = 3555251) B3555251
theorem B2370191 : Blo 1578487 2370191 := bstep (se 1 (by rfl) ⟨1777643, by rfl⟩ : syracuseStep 2370191 = 3555287) B3555287
theorem B2370233 : Blo 1578487 2370233 := bstep (se 2 (by rfl) ⟨888837, by rfl⟩ : syracuseStep 2370233 = 1777675) B1777675
theorem B5057225 : Blo 1578487 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B5999305 : Blo 1578487 5999305 := bstep (se 2 (by rfl) ⟨2249739, by rfl⟩ : syracuseStep 5999305 = 4499479) B4499479
theorem B2403017 : Blo 1578487 2403017 := bstep (se 2 (by rfl) ⟨901131, by rfl⟩ : syracuseStep 2403017 = 1802263) B1802263
theorem B2370311 : Blo 1578487 2370311 := bstep (se 1 (by rfl) ⟨1777733, by rfl⟩ : syracuseStep 2370311 = 3555467) B3555467
theorem B9612047 : Blo 1578487 9612047 := bstep (se 1 (by rfl) ⟨7209035, by rfl⟩ : syracuseStep 9612047 = 14418071) B14418071
theorem B2370347 : Blo 1578487 2370347 := bstep (se 1 (by rfl) ⟨1777760, by rfl⟩ : syracuseStep 2370347 = 3555521) B3555521
theorem B2370377 : Blo 1578487 2370377 := bstep (se 2 (by rfl) ⟨888891, by rfl⟩ : syracuseStep 2370377 = 1777783) B1777783
theorem B6933383 : Blo 1578487 6933383 := bstep (se 1 (by rfl) ⟨5200037, by rfl⟩ : syracuseStep 6933383 = 10400075) B10400075
theorem B5327801 : Blo 1578487 5327801 := bstep (se 2 (by rfl) ⟨1997925, by rfl⟩ : syracuseStep 5327801 = 3995851) B3995851
theorem B2370491 : Blo 1578487 2370491 := bstep (se 1 (by rfl) ⟨1777868, by rfl⟩ : syracuseStep 2370491 = 3555737) B3555737
theorem B10120139 : Blo 1578487 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B2370551 : Blo 1578487 2370551 := bstep (se 1 (by rfl) ⟨1777913, by rfl⟩ : syracuseStep 2370551 = 3555827) B3555827
theorem B2665487 : Blo 1578487 2665487 := bstep (se 1 (by rfl) ⟨1999115, by rfl⟩ : syracuseStep 2665487 = 3998231) B3998231
theorem B2370575 : Blo 1578487 2370575 := bstep (se 1 (by rfl) ⟨1777931, by rfl⟩ : syracuseStep 2370575 = 3555863) B3555863
theorem B8997911 : Blo 1578487 8997911 := bstep (se 1 (by rfl) ⟨6748433, by rfl⟩ : syracuseStep 8997911 = 13496867) B13496867
theorem B2370617 : Blo 1578487 2370617 := bstep (se 2 (by rfl) ⟨888981, by rfl⟩ : syracuseStep 2370617 = 1777963) B1777963
theorem B147950653 : Blo 1578487 147950653 := bstep (se 3 (by rfl) ⟨27740747, by rfl⟩ : syracuseStep 147950653 = 55481495) B55481495
theorem B2370695 : Blo 1578487 2370695 := bstep (se 1 (by rfl) ⟨1778021, by rfl⟩ : syracuseStep 2370695 = 3556043) B3556043
theorem B2370731 : Blo 1578487 2370731 := bstep (se 1 (by rfl) ⟨1778048, by rfl⟩ : syracuseStep 2370731 = 3556097) B3556097
theorem B3247375 : Blo 1578487 3247375 := bstep (se 1 (by rfl) ⟨2435531, by rfl⟩ : syracuseStep 3247375 = 4871063) B4871063
theorem B3796283 : Blo 1578487 3796283 := bstep (se 1 (by rfl) ⟨2847212, by rfl⟩ : syracuseStep 3796283 = 5694425) B5694425
theorem B5328395 : Blo 1578487 5328395 := bstep (se 1 (by rfl) ⟨3996296, by rfl⟩ : syracuseStep 5328395 = 7992593) B7992593
theorem B8998411 : Blo 1578487 8998411 := bstep (se 1 (by rfl) ⟨6748808, by rfl⟩ : syracuseStep 8998411 = 13497617) B13497617
theorem B15593003 : Blo 1578487 15593003 := bstep (se 1 (by rfl) ⟨11694752, by rfl⟩ : syracuseStep 15593003 = 23389505) B23389505
theorem B2666027 : Blo 1578487 2666027 := bstep (se 1 (by rfl) ⟨1999520, by rfl⟩ : syracuseStep 2666027 = 3999041) B3999041
theorem B5328503 : Blo 1578487 5328503 := bstep (se 1 (by rfl) ⟨3996377, by rfl⟩ : syracuseStep 5328503 = 7992755) B7992755
theorem B2248327 : Blo 1578487 2248327 := bstep (se 1 (by rfl) ⟨1686245, by rfl⟩ : syracuseStep 2248327 = 3372491) B3372491
theorem B17076005 : Blo 1578487 17076005 := bstep (se 4 (by rfl) ⟨1600875, by rfl⟩ : syracuseStep 17076005 = 3201751) B3201751
theorem B16428851 : Blo 1578487 16428851 := bstep (se 1 (by rfl) ⟨12321638, by rfl⟩ : syracuseStep 16428851 = 24643277) B24643277
theorem B2666425 : Blo 1578487 2666425 := bstep (se 2 (by rfl) ⟨999909, by rfl⟩ : syracuseStep 2666425 = 1999819) B1999819
theorem B18001925 : Blo 1578487 18001925 := bstep (se 4 (by rfl) ⟨1687680, by rfl⟩ : syracuseStep 18001925 = 3375361) B3375361
theorem B16216087 : Blo 1578487 16216087 := bstep (se 1 (by rfl) ⟨12162065, by rfl⟩ : syracuseStep 16216087 = 24324131) B24324131
theorem B2248823 : Blo 1578487 2248823 := bstep (se 1 (by rfl) ⟨1686617, by rfl⟩ : syracuseStep 2248823 = 3373235) B3373235
theorem B5329097 : Blo 1578487 5329097 := bstep (se 2 (by rfl) ⟨1998411, by rfl⟩ : syracuseStep 5329097 = 3996823) B3996823
theorem B4051315 : Blo 1578487 4051315 := bstep (se 1 (by rfl) ⟨3038486, by rfl⟩ : syracuseStep 4051315 = 6076973) B6076973
theorem B8991121 : Blo 1578487 8991121 := bstep (se 2 (by rfl) ⟨3371670, by rfl⟩ : syracuseStep 8991121 = 6743341) B6743341
theorem B4870667 : Blo 1578487 4870667 := bstep (se 1 (by rfl) ⟨3653000, by rfl⟩ : syracuseStep 4870667 = 7306001) B7306001
theorem B3551759 : Blo 1578487 3551759 := bstep (se 1 (by rfl) ⟨2663819, by rfl⟩ : syracuseStep 3551759 = 5327639) B5327639
theorem B3551777 : Blo 1578487 3551777 := bstep (se 2 (by rfl) ⟨1331916, by rfl⟩ : syracuseStep 3551777 = 2663833) B2663833
theorem B19214891 : Blo 1578487 19214891 := bstep (se 1 (by rfl) ⟨14411168, by rfl⟩ : syracuseStep 19214891 = 28822337) B28822337
theorem B1897103 : Blo 1578487 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B48632501 : Blo 1578487 48632501 := bstep (se 5 (by rfl) ⟨2279648, by rfl⟩ : syracuseStep 48632501 = 4559297) B4559297
theorem B13488869 : Blo 1578487 13488869 := bstep (se 4 (by rfl) ⟨1264581, by rfl⟩ : syracuseStep 13488869 = 2529163) B2529163
theorem B15176483 : Blo 1578487 15176483 := bstep (se 1 (by rfl) ⟨11382362, by rfl⟩ : syracuseStep 15176483 = 22764725) B22764725
theorem B3552119 : Blo 1578487 3552119 := bstep (se 1 (by rfl) ⟨2664089, by rfl⟩ : syracuseStep 3552119 = 5328179) B5328179
theorem B5329799 : Blo 1578487 5329799 := bstep (se 1 (by rfl) ⟨3997349, by rfl⟩ : syracuseStep 5329799 = 7994699) B7994699
theorem B3372047 : Blo 1578487 3372047 := bstep (se 1 (by rfl) ⟨2529035, by rfl⟩ : syracuseStep 3372047 = 5058071) B5058071
theorem B3552299 : Blo 1578487 3552299 := bstep (se 1 (by rfl) ⟨2664224, by rfl⟩ : syracuseStep 3552299 = 5328449) B5328449
theorem B2249785 : Blo 1578487 2249785 := bstep (se 2 (by rfl) ⟨843669, by rfl⟩ : syracuseStep 2249785 = 1687339) B1687339
theorem B31208581 : Blo 1578487 31208581 := bstep (se 4 (by rfl) ⟨2925804, by rfl⟩ : syracuseStep 31208581 = 5851609) B5851609
theorem B3372167 : Blo 1578487 3372167 := bstep (se 1 (by rfl) ⟨2529125, by rfl⟩ : syracuseStep 3372167 = 5058251) B5058251
theorem B1733767 : Blo 1578487 1733767 := bstep (se 1 (by rfl) ⟨1300325, by rfl⟩ : syracuseStep 1733767 = 2600651) B2600651
theorem B5330177 : Blo 1578487 5330177 := bstep (se 2 (by rfl) ⟨1998816, by rfl⟩ : syracuseStep 5330177 = 3997633) B3997633
theorem B3372347 : Blo 1578487 3372347 := bstep (se 1 (by rfl) ⟨2529260, by rfl⟩ : syracuseStep 3372347 = 5058521) B5058521
theorem B2135431 : Blo 1578487 2135431 := bstep (se 1 (by rfl) ⟨1601573, by rfl⟩ : syracuseStep 2135431 = 3203147) B3203147
theorem B2250127 : Blo 1578487 2250127 := bstep (se 1 (by rfl) ⟨1687595, by rfl⟩ : syracuseStep 2250127 = 3375191) B3375191
theorem B3552659 : Blo 1578487 3552659 := bstep (se 1 (by rfl) ⟨2664494, by rfl⟩ : syracuseStep 3552659 = 5328989) B5328989
theorem B3552713 : Blo 1578487 3552713 := bstep (se 2 (by rfl) ⟨1332267, by rfl⟩ : syracuseStep 3552713 = 2664535) B2664535
theorem B9000395 : Blo 1578487 9000395 := bstep (se 1 (by rfl) ⟨6750296, by rfl⟩ : syracuseStep 9000395 = 13500593) B13500593
theorem B1578503 : Blo 1578487 1578503 := bstep (se 1 (by rfl) ⟨1183877, by rfl⟩ : syracuseStep 1578503 = 2367755) B2367755
theorem B1578511 : Blo 1578487 1578511 := bstep (se 1 (by rfl) ⟨1183883, by rfl⟩ : syracuseStep 1578511 = 2367767) B2367767
theorem B1578555 : Blo 1578487 1578555 := bstep (se 1 (by rfl) ⟨1183916, by rfl⟩ : syracuseStep 1578555 = 2367833) B2367833
theorem B6747715 : Blo 1578487 6747715 := bstep (se 1 (by rfl) ⟨5060786, by rfl⟩ : syracuseStep 6747715 = 10121573) B10121573
theorem B1578631 : Blo 1578487 1578631 := bstep (se 1 (by rfl) ⟨1183973, by rfl⟩ : syracuseStep 1578631 = 2367947) B2367947
theorem B1578639 : Blo 1578487 1578639 := bstep (se 1 (by rfl) ⟨1183979, by rfl⟩ : syracuseStep 1578639 = 2367959) B2367959
theorem B1578683 : Blo 1578487 1578683 := bstep (se 1 (by rfl) ⟨1184012, by rfl⟩ : syracuseStep 1578683 = 2368025) B2368025
theorem B4495105 : Blo 1578487 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B1578759 : Blo 1578487 1578759 := bstep (se 1 (by rfl) ⟨1184069, by rfl⟩ : syracuseStep 1578759 = 2368139) B2368139
theorem B1578767 : Blo 1578487 1578767 := bstep (se 1 (by rfl) ⟨1184075, by rfl⟩ : syracuseStep 1578767 = 2368151) B2368151
theorem B3372833 : Blo 1578487 3372833 := bstep (se 2 (by rfl) ⟨1264812, by rfl⟩ : syracuseStep 3372833 = 2529625) B2529625
theorem B1578811 : Blo 1578487 1578811 := bstep (se 1 (by rfl) ⟨1184108, by rfl⟩ : syracuseStep 1578811 = 2368217) B2368217
theorem B7690073 : Blo 1578487 7690073 := bstep (se 2 (by rfl) ⟨2883777, by rfl⟩ : syracuseStep 7690073 = 5767555) B5767555
theorem B1578887 : Blo 1578487 1578887 := bstep (se 1 (by rfl) ⟨1184165, by rfl⟩ : syracuseStep 1578887 = 2368331) B2368331
theorem B1578895 : Blo 1578487 1578895 := bstep (se 1 (by rfl) ⟨1184171, by rfl⟩ : syracuseStep 1578895 = 2368343) B2368343
theorem B7993241 : Blo 1578487 7993241 := bstep (se 2 (by rfl) ⟨2997465, by rfl⟩ : syracuseStep 7993241 = 5994931) B5994931
theorem B1578939 : Blo 1578487 1578939 := bstep (se 1 (by rfl) ⟨1184204, by rfl⟩ : syracuseStep 1578939 = 2368409) B2368409
theorem B1579015 : Blo 1578487 1579015 := bstep (se 1 (by rfl) ⟨1184261, by rfl⟩ : syracuseStep 1579015 = 2368523) B2368523
theorem B12810251 : Blo 1578487 12810251 := bstep (se 1 (by rfl) ⟨9607688, by rfl⟩ : syracuseStep 12810251 = 19215377) B19215377
theorem B1579023 : Blo 1578487 1579023 := bstep (se 1 (by rfl) ⟨1184267, by rfl⟩ : syracuseStep 1579023 = 2368535) B2368535
theorem B5330987 : Blo 1578487 5330987 := bstep (se 1 (by rfl) ⟨3998240, by rfl⟩ : syracuseStep 5330987 = 7996481) B7996481
theorem B1579067 : Blo 1578487 1579067 := bstep (se 1 (by rfl) ⟨1184300, by rfl⟩ : syracuseStep 1579067 = 2368601) B2368601
theorem B4388951 : Blo 1578487 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B1579143 : Blo 1578487 1579143 := bstep (se 1 (by rfl) ⟨1184357, by rfl⟩ : syracuseStep 1579143 = 2368715) B2368715
theorem B3553415 : Blo 1578487 3553415 := bstep (se 1 (by rfl) ⟨2665061, by rfl⟩ : syracuseStep 3553415 = 5330123) B5330123
theorem B1579151 : Blo 1578487 1579151 := bstep (se 1 (by rfl) ⟨1184363, by rfl⟩ : syracuseStep 1579151 = 2368727) B2368727
theorem B3995801 : Blo 1578487 3995801 := bstep (se 2 (by rfl) ⟨1498425, by rfl⟩ : syracuseStep 3995801 = 2996851) B2996851
theorem B15177901 : Blo 1578487 15177901 := bstep (se 3 (by rfl) ⟨2845856, by rfl⟩ : syracuseStep 15177901 = 5691713) B5691713
theorem B1775803 : Blo 1578487 1775803 := bstep (se 1 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 1775803 = 2663705) B2663705
theorem B1579195 : Blo 1578487 1579195 := bstep (se 1 (by rfl) ⟨1184396, by rfl⟩ : syracuseStep 1579195 = 2368793) B2368793
theorem B1579271 : Blo 1578487 1579271 := bstep (se 1 (by rfl) ⟨1184453, by rfl⟩ : syracuseStep 1579271 = 2368907) B2368907
theorem B1579279 : Blo 1578487 1579279 := bstep (se 1 (by rfl) ⟨1184459, by rfl⟩ : syracuseStep 1579279 = 2368919) B2368919
theorem B3995963 : Blo 1578487 3995963 := bstep (se 1 (by rfl) ⟨2996972, by rfl⟩ : syracuseStep 3995963 = 5993945) B5993945
theorem B4495675 : Blo 1578487 4495675 := bstep (se 1 (by rfl) ⟨3371756, by rfl⟩ : syracuseStep 4495675 = 6743513) B6743513
theorem B1579323 : Blo 1578487 1579323 := bstep (se 1 (by rfl) ⟨1184492, by rfl⟩ : syracuseStep 1579323 = 2368985) B2368985
theorem B3553595 : Blo 1578487 3553595 := bstep (se 1 (by rfl) ⟨2665196, by rfl⟩ : syracuseStep 3553595 = 5330393) B5330393
theorem B1579399 : Blo 1578487 1579399 := bstep (se 1 (by rfl) ⟨1184549, by rfl⟩ : syracuseStep 1579399 = 2369099) B2369099
theorem B1579407 : Blo 1578487 1579407 := bstep (se 1 (by rfl) ⟨1184555, by rfl⟩ : syracuseStep 1579407 = 2369111) B2369111
theorem B2529721 : Blo 1578487 2529721 := bstep (se 2 (by rfl) ⟨948645, by rfl⟩ : syracuseStep 2529721 = 1897291) B1897291
theorem B3553721 : Blo 1578487 3553721 := bstep (se 2 (by rfl) ⟨1332645, by rfl⟩ : syracuseStep 3553721 = 2665291) B2665291
theorem B1579451 : Blo 1578487 1579451 := bstep (se 1 (by rfl) ⟨1184588, by rfl⟩ : syracuseStep 1579451 = 2369177) B2369177
theorem B4053449 : Blo 1578487 4053449 := bstep (se 2 (by rfl) ⟨1520043, by rfl⟩ : syracuseStep 4053449 = 3040087) B3040087
theorem B8542673 : Blo 1578487 8542673 := bstep (se 2 (by rfl) ⟨3203502, by rfl⟩ : syracuseStep 8542673 = 6407005) B6407005
theorem B10262993 : Blo 1578487 10262993 := bstep (se 2 (by rfl) ⟨3848622, by rfl⟩ : syracuseStep 10262993 = 7697245) B7697245
theorem B1579527 : Blo 1578487 1579527 := bstep (se 1 (by rfl) ⟨1184645, by rfl⟩ : syracuseStep 1579527 = 2369291) B2369291
theorem B3996175 : Blo 1578487 3996175 := bstep (se 1 (by rfl) ⟨2997131, by rfl⟩ : syracuseStep 3996175 = 5994263) B5994263
theorem B1579535 : Blo 1578487 1579535 := bstep (se 1 (by rfl) ⟨1184651, by rfl⟩ : syracuseStep 1579535 = 2369303) B2369303
theorem B10123805 : Blo 1578487 10123805 := bstep (se 3 (by rfl) ⟨1898213, by rfl⟩ : syracuseStep 10123805 = 3796427) B3796427
theorem B1579579 : Blo 1578487 1579579 := bstep (se 1 (by rfl) ⟨1184684, by rfl⟩ : syracuseStep 1579579 = 2369369) B2369369
theorem B3373687 : Blo 1578487 3373687 := bstep (se 1 (by rfl) ⟨2530265, by rfl⟩ : syracuseStep 3373687 = 5060531) B5060531
theorem B1579655 : Blo 1578487 1579655 := bstep (se 1 (by rfl) ⟨1184741, by rfl⟩ : syracuseStep 1579655 = 2369483) B2369483
theorem B1776271 : Blo 1578487 1776271 := bstep (se 1 (by rfl) ⟨1332203, by rfl⟩ : syracuseStep 1776271 = 2664407) B2664407
theorem B1579663 : Blo 1578487 1579663 := bstep (se 1 (by rfl) ⟨1184747, by rfl⟩ : syracuseStep 1579663 = 2369495) B2369495
theorem B1579707 : Blo 1578487 1579707 := bstep (se 1 (by rfl) ⟨1184780, by rfl⟩ : syracuseStep 1579707 = 2369561) B2369561
theorem B8993537 : Blo 1578487 8993537 := bstep (se 2 (by rfl) ⟨3372576, by rfl⟩ : syracuseStep 8993537 = 6745153) B6745153
theorem B1579783 : Blo 1578487 1579783 := bstep (se 1 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 1579783 = 2369675) B2369675
theorem B3554063 : Blo 1578487 3554063 := bstep (se 1 (by rfl) ⟨2665547, by rfl⟩ : syracuseStep 3554063 = 5331095) B5331095
theorem B1579791 : Blo 1578487 1579791 := bstep (se 1 (by rfl) ⟨1184843, by rfl⟩ : syracuseStep 1579791 = 2369687) B2369687
theorem B3996449 : Blo 1578487 3996449 := bstep (se 2 (by rfl) ⟨1498668, by rfl⟩ : syracuseStep 3996449 = 2997337) B2997337
theorem B3554081 : Blo 1578487 3554081 := bstep (se 2 (by rfl) ⟨1332780, by rfl⟩ : syracuseStep 3554081 = 2665561) B2665561
theorem B26983205 : Blo 1578487 26983205 := bstep (se 4 (by rfl) ⟨2529675, by rfl⟩ : syracuseStep 26983205 = 5059351) B5059351
theorem B1579835 : Blo 1578487 1579835 := bstep (se 1 (by rfl) ⟨1184876, by rfl⟩ : syracuseStep 1579835 = 2369753) B2369753
theorem B1579911 : Blo 1578487 1579911 := bstep (se 1 (by rfl) ⟨1184933, by rfl⟩ : syracuseStep 1579911 = 2369867) B2369867
theorem B1579919 : Blo 1578487 1579919 := bstep (se 1 (by rfl) ⟨1184939, by rfl⟩ : syracuseStep 1579919 = 2369879) B2369879
theorem B9116563 : Blo 1578487 9116563 := bstep (se 1 (by rfl) ⟨6837422, by rfl⟩ : syracuseStep 9116563 = 13674845) B13674845
theorem B5995417 : Blo 1578487 5995417 := bstep (se 2 (by rfl) ⟨2248281, by rfl⟩ : syracuseStep 5995417 = 4496563) B4496563
theorem B1579963 : Blo 1578487 1579963 := bstep (se 1 (by rfl) ⟨1184972, by rfl⟩ : syracuseStep 1579963 = 2369945) B2369945
theorem B1580039 : Blo 1578487 1580039 := bstep (se 1 (by rfl) ⟨1185029, by rfl⟩ : syracuseStep 1580039 = 2370059) B2370059
theorem B1580047 : Blo 1578487 1580047 := bstep (se 1 (by rfl) ⟨1185035, by rfl⟩ : syracuseStep 1580047 = 2370071) B2370071
theorem B1686587 : Blo 1578487 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B1580091 : Blo 1578487 1580091 := bstep (se 1 (by rfl) ⟨1185068, by rfl⟩ : syracuseStep 1580091 = 2370137) B2370137
theorem B3554423 : Blo 1578487 3554423 := bstep (se 1 (by rfl) ⟨2665817, by rfl⟩ : syracuseStep 3554423 = 5331635) B5331635
theorem B1776775 : Blo 1578487 1776775 := bstep (se 1 (by rfl) ⟨1332581, by rfl⟩ : syracuseStep 1776775 = 2665163) B2665163
theorem B1580167 : Blo 1578487 1580167 := bstep (se 1 (by rfl) ⟨1185125, by rfl⟩ : syracuseStep 1580167 = 2370251) B2370251
theorem B1580175 : Blo 1578487 1580175 := bstep (se 1 (by rfl) ⟨1185131, by rfl⟩ : syracuseStep 1580175 = 2370263) B2370263
theorem B1580219 : Blo 1578487 1580219 := bstep (se 1 (by rfl) ⟨1185164, by rfl⟩ : syracuseStep 1580219 = 2370329) B2370329
theorem B5995721 : Blo 1578487 5995721 := bstep (se 2 (by rfl) ⟨2248395, by rfl⟩ : syracuseStep 5995721 = 4496791) B4496791
theorem B1580295 : Blo 1578487 1580295 := bstep (se 1 (by rfl) ⟨1185221, by rfl⟩ : syracuseStep 1580295 = 2370443) B2370443
theorem B1580303 : Blo 1578487 1580303 := bstep (se 1 (by rfl) ⟨1185227, by rfl⟩ : syracuseStep 1580303 = 2370455) B2370455
theorem B3554603 : Blo 1578487 3554603 := bstep (se 1 (by rfl) ⟨2665952, by rfl⟩ : syracuseStep 3554603 = 5331905) B5331905
theorem B1776955 : Blo 1578487 1776955 := bstep (se 1 (by rfl) ⟨1332716, by rfl⟩ : syracuseStep 1776955 = 2665433) B2665433
theorem B5332283 : Blo 1578487 5332283 := bstep (se 1 (by rfl) ⟨3999212, by rfl⟩ : syracuseStep 5332283 = 7998425) B7998425
theorem B1580347 : Blo 1578487 1580347 := bstep (se 1 (by rfl) ⟨1185260, by rfl⟩ : syracuseStep 1580347 = 2370521) B2370521
theorem B1998199 : Blo 1578487 1998199 := bstep (se 1 (by rfl) ⟨1498649, by rfl⟩ : syracuseStep 1998199 = 2997299) B2997299
theorem B1580423 : Blo 1578487 1580423 := bstep (se 1 (by rfl) ⟨1185317, by rfl⟩ : syracuseStep 1580423 = 2370635) B2370635
theorem B1580431 : Blo 1578487 1580431 := bstep (se 1 (by rfl) ⟨1185323, by rfl⟩ : syracuseStep 1580431 = 2370647) B2370647
theorem B30768569 : Blo 1578487 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B1580475 : Blo 1578487 1580475 := bstep (se 1 (by rfl) ⟨1185356, by rfl⟩ : syracuseStep 1580475 = 2370713) B2370713
theorem B8543755 : Blo 1578487 8543755 := bstep (se 1 (by rfl) ⟨6407816, by rfl⟩ : syracuseStep 8543755 = 12815633) B12815633
theorem B8535581 : Blo 1578487 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B12000797 : Blo 1578487 12000797 := bstep (se 3 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 12000797 = 4500299) B4500299
theorem B15171137 : Blo 1578487 15171137 := bstep (se 2 (by rfl) ⟨5689176, by rfl⟩ : syracuseStep 15171137 = 11378353) B11378353
theorem B3554963 : Blo 1578487 3554963 := bstep (se 1 (by rfl) ⟨2666222, by rfl⟩ : syracuseStep 3554963 = 5332445) B5332445
theorem B64806551 : Blo 1578487 64806551 := bstep (se 1 (by rfl) ⟨48604913, by rfl⟩ : syracuseStep 64806551 = 97209827) B97209827
theorem B4800185 : Blo 1578487 4800185 := bstep (se 2 (by rfl) ⟨1800069, by rfl⟩ : syracuseStep 4800185 = 3600139) B3600139
theorem B1998523 : Blo 1578487 1998523 := bstep (se 1 (by rfl) ⟨1498892, by rfl⟩ : syracuseStep 1998523 = 2997785) B2997785
theorem B3555017 : Blo 1578487 3555017 := bstep (se 2 (by rfl) ⟨1333131, by rfl⟩ : syracuseStep 3555017 = 2666263) B2666263
theorem B3997451 : Blo 1578487 3997451 := bstep (se 1 (by rfl) ⟨2998088, by rfl⟩ : syracuseStep 3997451 = 5996177) B5996177
theorem B1777423 : Blo 1578487 1777423 := bstep (se 1 (by rfl) ⟨1333067, by rfl⟩ : syracuseStep 1777423 = 2666135) B2666135
theorem B5332769 : Blo 1578487 5332769 := bstep (se 2 (by rfl) ⟨1999788, by rfl⟩ : syracuseStep 5332769 = 3999577) B3999577
theorem B6750161 : Blo 1578487 6750161 := bstep (se 2 (by rfl) ⟨2531310, by rfl⟩ : syracuseStep 6750161 = 5062621) B5062621
theorem B12001283 : Blo 1578487 12001283 := bstep (se 1 (by rfl) ⟨9000962, by rfl⟩ : syracuseStep 12001283 = 18001925) B18001925
theorem B11534413 : Blo 1578487 11534413 := bstep (se 3 (by rfl) ⟨2162702, by rfl⟩ : syracuseStep 11534413 = 4325405) B4325405
theorem B3997775 : Blo 1578487 3997775 := bstep (se 1 (by rfl) ⟨2998331, by rfl⟩ : syracuseStep 3997775 = 5996663) B5996663
theorem B3555575 : Blo 1578487 3555575 := bstep (se 1 (by rfl) ⟨2666681, by rfl⟩ : syracuseStep 3555575 = 5333363) B5333363
theorem B2367737 : Blo 1578487 2367737 := bstep (se 2 (by rfl) ⟨887901, by rfl⟩ : syracuseStep 2367737 = 1775803) B1775803
theorem B5996861 : Blo 1578487 5996861 := bstep (se 3 (by rfl) ⟨1124411, by rfl⟩ : syracuseStep 5996861 = 2248823) B2248823
theorem B5333309 : Blo 1578487 5333309 := bstep (se 3 (by rfl) ⟨999995, by rfl⟩ : syracuseStep 5333309 = 1999991) B1999991
theorem B2367839 : Blo 1578487 2367839 := bstep (se 1 (by rfl) ⟨1775879, by rfl⟩ : syracuseStep 2367839 = 3551759) B3551759
theorem B2367851 : Blo 1578487 2367851 := bstep (se 1 (by rfl) ⟨1775888, by rfl⟩ : syracuseStep 2367851 = 3551777) B3551777
theorem B2998711 : Blo 1578487 2998711 := bstep (se 1 (by rfl) ⟨2249033, by rfl⟩ : syracuseStep 2998711 = 4498067) B4498067
theorem B5767661 : Blo 1578487 5767661 := bstep (se 3 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 5767661 = 2162873) B2162873
theorem B10117655 : Blo 1578487 10117655 := bstep (se 1 (by rfl) ⟨7588241, by rfl⟩ : syracuseStep 10117655 = 15176483) B15176483
theorem B12804641 : Blo 1578487 12804641 := bstep (se 2 (by rfl) ⟨4801740, by rfl⟩ : syracuseStep 12804641 = 9603481) B9603481
theorem B1999399 : Blo 1578487 1999399 := bstep (se 1 (by rfl) ⟨1499549, by rfl⟩ : syracuseStep 1999399 = 2999099) B2999099
theorem B2368079 : Blo 1578487 2368079 := bstep (se 1 (by rfl) ⟨1776059, by rfl⟩ : syracuseStep 2368079 = 3552119) B3552119
theorem B17990261 : Blo 1578487 17990261 := bstep (se 5 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 17990261 = 1686587) B1686587
theorem B5997179 : Blo 1578487 5997179 := bstep (se 1 (by rfl) ⟨4497884, by rfl⟩ : syracuseStep 5997179 = 8995769) B8995769
theorem B2368199 : Blo 1578487 2368199 := bstep (se 1 (by rfl) ⟨1776149, by rfl⟩ : syracuseStep 2368199 = 3552299) B3552299
theorem B3998423 : Blo 1578487 3998423 := bstep (se 1 (by rfl) ⟨2998817, by rfl⟩ : syracuseStep 3998423 = 5997635) B5997635
theorem B5129003 : Blo 1578487 5129003 := bstep (se 1 (by rfl) ⟨3846752, by rfl⟩ : syracuseStep 5129003 = 7693505) B7693505
theorem B4498249 : Blo 1578487 4498249 := bstep (se 2 (by rfl) ⟨1686843, by rfl⟩ : syracuseStep 4498249 = 3373687) B3373687
theorem B2368361 : Blo 1578487 2368361 := bstep (se 2 (by rfl) ⟨888135, by rfl⟩ : syracuseStep 2368361 = 1776271) B1776271
theorem B1999723 : Blo 1578487 1999723 := bstep (se 1 (by rfl) ⟨1499792, by rfl⟩ : syracuseStep 1999723 = 2999585) B2999585
theorem B2368439 : Blo 1578487 2368439 := bstep (se 1 (by rfl) ⟨1776329, by rfl⟩ : syracuseStep 2368439 = 3552659) B3552659
theorem B2368475 : Blo 1578487 2368475 := bstep (se 1 (by rfl) ⟨1776356, by rfl⟩ : syracuseStep 2368475 = 3552713) B3552713
theorem B24036317 : Blo 1578487 24036317 := bstep (se 3 (by rfl) ⟨4506809, by rfl⟩ : syracuseStep 24036317 = 9013619) B9013619
theorem B2925967 : Blo 1578487 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B2368943 : Blo 1578487 2368943 := bstep (se 1 (by rfl) ⟨1776707, by rfl⟩ : syracuseStep 2368943 = 3553415) B3553415
theorem B2663867 : Blo 1578487 2663867 := bstep (se 1 (by rfl) ⟨1997900, by rfl⟩ : syracuseStep 2663867 = 3995801) B3995801
theorem B2369033 : Blo 1578487 2369033 := bstep (se 2 (by rfl) ⟨888387, by rfl⟩ : syracuseStep 2369033 = 1776775) B1776775
theorem B2663975 : Blo 1578487 2663975 := bstep (se 1 (by rfl) ⟨1997981, by rfl⟩ : syracuseStep 2663975 = 3995963) B3995963
theorem B2369063 : Blo 1578487 2369063 := bstep (se 1 (by rfl) ⟨1776797, by rfl⟩ : syracuseStep 2369063 = 3553595) B3553595
theorem B7996967 : Blo 1578487 7996967 := bstep (se 1 (by rfl) ⟨5997725, by rfl⟩ : syracuseStep 7996967 = 11995451) B11995451
theorem B2369147 : Blo 1578487 2369147 := bstep (se 1 (by rfl) ⟨1776860, by rfl⟩ : syracuseStep 2369147 = 3553721) B3553721
theorem B5695115 : Blo 1578487 5695115 := bstep (se 1 (by rfl) ⟨4271336, by rfl⟩ : syracuseStep 5695115 = 8542673) B8542673
theorem B41043671 : Blo 1578487 41043671 := bstep (se 1 (by rfl) ⟨30782753, by rfl⟩ : syracuseStep 41043671 = 61565507) B61565507
theorem B2369273 : Blo 1578487 2369273 := bstep (se 2 (by rfl) ⟨888477, by rfl⟩ : syracuseStep 2369273 = 1776955) B1776955
theorem B2664265 : Blo 1578487 2664265 := bstep (se 2 (by rfl) ⟨999099, by rfl⟩ : syracuseStep 2664265 = 1998199) B1998199
theorem B2369375 : Blo 1578487 2369375 := bstep (se 1 (by rfl) ⟨1777031, by rfl⟩ : syracuseStep 2369375 = 3554063) B3554063
theorem B6408031 : Blo 1578487 6408031 := bstep (se 1 (by rfl) ⟨4806023, by rfl⟩ : syracuseStep 6408031 = 9612047) B9612047
theorem B2664299 : Blo 1578487 2664299 := bstep (se 1 (by rfl) ⟨1998224, by rfl⟩ : syracuseStep 2664299 = 3996449) B3996449
theorem B2369387 : Blo 1578487 2369387 := bstep (se 1 (by rfl) ⟨1777040, by rfl⟩ : syracuseStep 2369387 = 3554081) B3554081
theorem B3000169 : Blo 1578487 3000169 := bstep (se 2 (by rfl) ⟨1125063, by rfl⟩ : syracuseStep 3000169 = 2250127) B2250127
theorem B4622255 : Blo 1578487 4622255 := bstep (se 1 (by rfl) ⟨3466691, by rfl⟩ : syracuseStep 4622255 = 6933383) B6933383
theorem B8652737 : Blo 1578487 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B5998607 : Blo 1578487 5998607 := bstep (se 1 (by rfl) ⟨4498955, by rfl⟩ : syracuseStep 5998607 = 8997911) B8997911
theorem B2369615 : Blo 1578487 2369615 := bstep (se 1 (by rfl) ⟨1777211, by rfl⟩ : syracuseStep 2369615 = 3554423) B3554423
theorem B8996953 : Blo 1578487 8996953 := bstep (se 2 (by rfl) ⟨3373857, by rfl⟩ : syracuseStep 8996953 = 6747715) B6747715
theorem B109471925 : Blo 1578487 109471925 := bstep (se 5 (by rfl) ⟨5131496, by rfl⟩ : syracuseStep 109471925 = 10262993) B10262993
theorem B2369735 : Blo 1578487 2369735 := bstep (se 1 (by rfl) ⟨1777301, by rfl⟩ : syracuseStep 2369735 = 3554603) B3554603
theorem B20506861 : Blo 1578487 20506861 := bstep (se 3 (by rfl) ⟨3845036, by rfl⟩ : syracuseStep 20506861 = 7690073) B7690073
theorem B2664697 : Blo 1578487 2664697 := bstep (se 2 (by rfl) ⟨999261, by rfl⟩ : syracuseStep 2664697 = 1998523) B1998523
theorem B2369897 : Blo 1578487 2369897 := bstep (se 2 (by rfl) ⟨888711, by rfl⟩ : syracuseStep 2369897 = 1777423) B1777423
theorem B2369975 : Blo 1578487 2369975 := bstep (se 1 (by rfl) ⟨1777481, by rfl⟩ : syracuseStep 2369975 = 3554963) B3554963
theorem B2370011 : Blo 1578487 2370011 := bstep (se 1 (by rfl) ⟨1777508, by rfl⟩ : syracuseStep 2370011 = 3555017) B3555017
theorem B2664967 : Blo 1578487 2664967 := bstep (se 1 (by rfl) ⟨1998725, by rfl⟩ : syracuseStep 2664967 = 3997451) B3997451
theorem B4500107 : Blo 1578487 4500107 := bstep (se 1 (by rfl) ⟨3375080, by rfl⟩ : syracuseStep 4500107 = 6750161) B6750161
theorem B2468551 : Blo 1578487 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B21621449 : Blo 1578487 21621449 := bstep (se 2 (by rfl) ⟨8108043, by rfl⟩ : syracuseStep 21621449 = 16216087) B16216087
theorem B2403065 : Blo 1578487 2403065 := bstep (se 2 (by rfl) ⟨901149, by rfl⟩ : syracuseStep 2403065 = 1802299) B1802299
theorem B20237201 : Blo 1578487 20237201 := bstep (se 2 (by rfl) ⟨7588950, by rfl⟩ : syracuseStep 20237201 = 15177901) B15177901
theorem B2370479 : Blo 1578487 2370479 := bstep (se 1 (by rfl) ⟨1777859, by rfl⟩ : syracuseStep 2370479 = 3555719) B3555719
theorem B2665399 : Blo 1578487 2665399 := bstep (se 1 (by rfl) ⟨1999049, by rfl⟩ : syracuseStep 2665399 = 3998099) B3998099
theorem B2370569 : Blo 1578487 2370569 := bstep (se 2 (by rfl) ⟨888963, by rfl⟩ : syracuseStep 2370569 = 1777927) B1777927
theorem B2370599 : Blo 1578487 2370599 := bstep (se 1 (by rfl) ⟨1777949, by rfl⟩ : syracuseStep 2370599 = 3555899) B3555899
theorem B2665595 : Blo 1578487 2665595 := bstep (se 1 (by rfl) ⟨1999196, by rfl⟩ : syracuseStep 2665595 = 3998393) B3998393
theorem B2370683 : Blo 1578487 2370683 := bstep (se 1 (by rfl) ⟨1778012, by rfl⟩ : syracuseStep 2370683 = 3556025) B3556025
theorem B3845291 : Blo 1578487 3845291 := bstep (se 1 (by rfl) ⟨2883968, by rfl⟩ : syracuseStep 3845291 = 5767937) B5767937
theorem B11988161 : Blo 1578487 11988161 := bstep (se 2 (by rfl) ⟨4495560, by rfl⟩ : syracuseStep 11988161 = 8991121) B8991121
theorem B2248031 : Blo 1578487 2248031 := bstep (se 1 (by rfl) ⟨1686023, by rfl⟩ : syracuseStep 2248031 = 3372047) B3372047
theorem B5328233 : Blo 1578487 5328233 := bstep (se 2 (by rfl) ⟨1998087, by rfl⟩ : syracuseStep 5328233 = 3996175) B3996175
theorem B15183247 : Blo 1578487 15183247 := bstep (se 1 (by rfl) ⟨11387435, by rfl⟩ : syracuseStep 15183247 = 22774871) B22774871
theorem B2248111 : Blo 1578487 2248111 := bstep (se 1 (by rfl) ⟨1686083, by rfl⟩ : syracuseStep 2248111 = 3372167) B3372167
theorem B2665993 : Blo 1578487 2665993 := bstep (se 2 (by rfl) ⟨999747, by rfl⟩ : syracuseStep 2665993 = 1999495) B1999495
theorem B2248231 : Blo 1578487 2248231 := bstep (se 1 (by rfl) ⟨1686173, by rfl⟩ : syracuseStep 2248231 = 3372347) B3372347
theorem B7999073 : Blo 1578487 7999073 := bstep (se 2 (by rfl) ⟨2999652, by rfl⟩ : syracuseStep 7999073 = 5999305) B5999305
theorem B6000263 : Blo 1578487 6000263 := bstep (se 1 (by rfl) ⟨4500197, by rfl⟩ : syracuseStep 6000263 = 9000395) B9000395
theorem B2666155 : Blo 1578487 2666155 := bstep (se 1 (by rfl) ⟨1999616, by rfl⟩ : syracuseStep 2666155 = 3999233) B3999233
theorem B11996909 : Blo 1578487 11996909 := bstep (se 3 (by rfl) ⟨2249420, by rfl⟩ : syracuseStep 11996909 = 4498841) B4498841
theorem B3419977 : Blo 1578487 3419977 := bstep (se 2 (by rfl) ⟨1282491, by rfl⟩ : syracuseStep 3419977 = 2564983) B2564983
theorem B7991135 : Blo 1578487 7991135 := bstep (se 1 (by rfl) ⟨5993351, by rfl⟩ : syracuseStep 7991135 = 11986703) B11986703
theorem B2248555 : Blo 1578487 2248555 := bstep (se 1 (by rfl) ⟨1686416, by rfl⟩ : syracuseStep 2248555 = 3372833) B3372833
theorem B10809197 : Blo 1578487 10809197 := bstep (se 3 (by rfl) ⟨2026724, by rfl⟩ : syracuseStep 10809197 = 4053449) B4053449
theorem B5328827 : Blo 1578487 5328827 := bstep (se 1 (by rfl) ⟨3996620, by rfl⟩ : syracuseStep 5328827 = 7993241) B7993241
theorem B2666459 : Blo 1578487 2666459 := bstep (se 1 (by rfl) ⟨1999844, by rfl⟩ : syracuseStep 2666459 = 3999689) B3999689
theorem B8540167 : Blo 1578487 8540167 := bstep (se 1 (by rfl) ⟨6405125, by rfl⟩ : syracuseStep 8540167 = 12810251) B12810251
theorem B12988445 : Blo 1578487 12988445 := bstep (se 3 (by rfl) ⟨2435333, by rfl⟩ : syracuseStep 12988445 = 4870667) B4870667
theorem B197267537 : Blo 1578487 197267537 := bstep (se 2 (by rfl) ⟨73975326, by rfl⟩ : syracuseStep 197267537 = 147950653) B147950653
theorem B41611441 : Blo 1578487 41611441 := bstep (se 2 (by rfl) ⟨15604290, by rfl⟩ : syracuseStep 41611441 = 31208581) B31208581
theorem B2666695 : Blo 1578487 2666695 := bstep (se 1 (by rfl) ⟨2000021, by rfl⟩ : syracuseStep 2666695 = 4000043) B4000043
theorem B4329833 : Blo 1578487 4329833 := bstep (se 2 (by rfl) ⟨1623687, by rfl⟩ : syracuseStep 4329833 = 3247375) B3247375
theorem B2666857 : Blo 1578487 2666857 := bstep (se 2 (by rfl) ⟨1000071, by rfl⟩ : syracuseStep 2666857 = 2000143) B2000143
theorem B5058941 : Blo 1578487 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B3371483 : Blo 1578487 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B1602011 : Blo 1578487 1602011 := bstep (se 1 (by rfl) ⟨1201508, by rfl⟩ : syracuseStep 1602011 = 2403017) B2403017
theorem B2847241 : Blo 1578487 2847241 := bstep (se 2 (by rfl) ⟨1067715, by rfl⟩ : syracuseStep 2847241 = 2135431) B2135431
theorem B21607013 : Blo 1578487 21607013 := bstep (se 4 (by rfl) ⟨2025657, by rfl⟩ : syracuseStep 21607013 = 4051315) B4051315
theorem B3551867 : Blo 1578487 3551867 := bstep (se 1 (by rfl) ⟨2663900, by rfl⟩ : syracuseStep 3551867 = 5327801) B5327801
theorem B6746759 : Blo 1578487 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B11997881 : Blo 1578487 11997881 := bstep (se 2 (by rfl) ⟨4499205, by rfl⟩ : syracuseStep 11997881 = 8998411) B8998411
theorem B11391673 : Blo 1578487 11391673 := bstep (se 2 (by rfl) ⟨4271877, by rfl⟩ : syracuseStep 11391673 = 8543755) B8543755
theorem B3551993 : Blo 1578487 3551993 := bstep (se 2 (by rfl) ⟨1331997, by rfl⟩ : syracuseStep 3551993 = 2663995) B2663995
theorem B5993473 : Blo 1578487 5993473 := bstep (se 2 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 5993473 = 4495105) B4495105
theorem B3552263 : Blo 1578487 3552263 := bstep (se 1 (by rfl) ⟨2664197, by rfl⟩ : syracuseStep 3552263 = 5328395) B5328395
theorem B5690387 : Blo 1578487 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B8000531 : Blo 1578487 8000531 := bstep (se 1 (by rfl) ⟨6000398, by rfl⟩ : syracuseStep 8000531 = 12000797) B12000797
theorem B10114091 : Blo 1578487 10114091 := bstep (se 1 (by rfl) ⟨7585568, by rfl⟩ : syracuseStep 10114091 = 15171137) B15171137
theorem B3552335 : Blo 1578487 3552335 := bstep (se 1 (by rfl) ⟨2664251, by rfl⟩ : syracuseStep 3552335 = 5328503) B5328503
theorem B3200123 : Blo 1578487 3200123 := bstep (se 1 (by rfl) ⟨2400092, by rfl⟩ : syracuseStep 3200123 = 4800185) B4800185
theorem B6403229 : Blo 1578487 6403229 := bstep (se 3 (by rfl) ⟨1200605, by rfl⟩ : syracuseStep 6403229 = 2401211) B2401211
theorem B11384003 : Blo 1578487 11384003 := bstep (se 1 (by rfl) ⟨8538002, by rfl⟩ : syracuseStep 11384003 = 17076005) B17076005
theorem B3552731 : Blo 1578487 3552731 := bstep (se 1 (by rfl) ⟨2664548, by rfl⟩ : syracuseStep 3552731 = 5329097) B5329097
theorem B7591411 : Blo 1578487 7591411 := bstep (se 1 (by rfl) ⟨5693558, by rfl⟩ : syracuseStep 7591411 = 11387117) B11387117
theorem B1578535 : Blo 1578487 1578535 := bstep (se 1 (by rfl) ⟨1183901, by rfl⟩ : syracuseStep 1578535 = 2367803) B2367803
theorem B1578575 : Blo 1578487 1578575 := bstep (se 1 (by rfl) ⟨1183931, by rfl⟩ : syracuseStep 1578575 = 2367863) B2367863
theorem B1578591 : Blo 1578487 1578591 := bstep (se 1 (by rfl) ⟨1183943, by rfl⟩ : syracuseStep 1578591 = 2367887) B2367887
theorem B1578619 : Blo 1578487 1578619 := bstep (se 1 (by rfl) ⟨1183964, by rfl⟩ : syracuseStep 1578619 = 2367929) B2367929
theorem B5330555 : Blo 1578487 5330555 := bstep (se 1 (by rfl) ⟨3997916, by rfl⟩ : syracuseStep 5330555 = 7995833) B7995833
theorem B11998853 : Blo 1578487 11998853 := bstep (se 4 (by rfl) ⟨1124892, by rfl⟩ : syracuseStep 11998853 = 2249785) B2249785
theorem B1578671 : Blo 1578487 1578671 := bstep (se 1 (by rfl) ⟨1184003, by rfl⟩ : syracuseStep 1578671 = 2368007) B2368007
theorem B1578695 : Blo 1578487 1578695 := bstep (se 1 (by rfl) ⟨1184021, by rfl⟩ : syracuseStep 1578695 = 2368043) B2368043
theorem B12809927 : Blo 1578487 12809927 := bstep (se 1 (by rfl) ⟨9607445, by rfl⟩ : syracuseStep 12809927 = 19214891) B19214891
theorem B1578715 : Blo 1578487 1578715 := bstep (se 1 (by rfl) ⟨1184036, by rfl⟩ : syracuseStep 1578715 = 2368073) B2368073
theorem B5994233 : Blo 1578487 5994233 := bstep (se 2 (by rfl) ⟨2247837, by rfl⟩ : syracuseStep 5994233 = 4495675) B4495675
theorem B5330717 : Blo 1578487 5330717 := bstep (se 3 (by rfl) ⟨999509, by rfl⟩ : syracuseStep 5330717 = 1999019) B1999019
theorem B32421667 : Blo 1578487 32421667 := bstep (se 1 (by rfl) ⟨24316250, by rfl⟩ : syracuseStep 32421667 = 48632501) B48632501
theorem B1578791 : Blo 1578487 1578791 := bstep (se 1 (by rfl) ⟨1184093, by rfl⟩ : syracuseStep 1578791 = 2368187) B2368187
theorem B8992579 : Blo 1578487 8992579 := bstep (se 1 (by rfl) ⟨6744434, by rfl⟩ : syracuseStep 8992579 = 13488869) B13488869
theorem B1578831 : Blo 1578487 1578831 := bstep (se 1 (by rfl) ⟨1184123, by rfl⟩ : syracuseStep 1578831 = 2368247) B2368247
theorem B1578847 : Blo 1578487 1578847 := bstep (se 1 (by rfl) ⟨1184135, by rfl⟩ : syracuseStep 1578847 = 2368271) B2368271
theorem B1578875 : Blo 1578487 1578875 := bstep (se 1 (by rfl) ⟨1184156, by rfl⟩ : syracuseStep 1578875 = 2368313) B2368313
theorem B1578927 : Blo 1578487 1578927 := bstep (se 1 (by rfl) ⟨1184195, by rfl⟩ : syracuseStep 1578927 = 2368391) B2368391
theorem B3553199 : Blo 1578487 3553199 := bstep (se 1 (by rfl) ⟨2664899, by rfl⟩ : syracuseStep 3553199 = 5329799) B5329799
theorem B1578951 : Blo 1578487 1578951 := bstep (se 1 (by rfl) ⟨1184213, by rfl⟩ : syracuseStep 1578951 = 2368427) B2368427
theorem B1578971 : Blo 1578487 1578971 := bstep (se 1 (by rfl) ⟨1184228, by rfl⟩ : syracuseStep 1578971 = 2368457) B2368457
theorem B11991077 : Blo 1578487 11991077 := bstep (se 4 (by rfl) ⟨1124163, by rfl⟩ : syracuseStep 11991077 = 2248327) B2248327
theorem B1579047 : Blo 1578487 1579047 := bstep (se 1 (by rfl) ⟨1184285, by rfl⟩ : syracuseStep 1579047 = 2368571) B2368571
theorem B9246757 : Blo 1578487 9246757 := bstep (se 4 (by rfl) ⟨866883, by rfl⟩ : syracuseStep 9246757 = 1733767) B1733767
theorem B1579087 : Blo 1578487 1579087 := bstep (se 1 (by rfl) ⟨1184315, by rfl⟩ : syracuseStep 1579087 = 2368631) B2368631
theorem B1579103 : Blo 1578487 1579103 := bstep (se 1 (by rfl) ⟨1184327, by rfl⟩ : syracuseStep 1579103 = 2368655) B2368655
theorem B1579131 : Blo 1578487 1579131 := bstep (se 1 (by rfl) ⟨1184348, by rfl⟩ : syracuseStep 1579131 = 2368697) B2368697
theorem B3553451 : Blo 1578487 3553451 := bstep (se 1 (by rfl) ⟨2665088, by rfl⟩ : syracuseStep 3553451 = 5330177) B5330177
theorem B1579183 : Blo 1578487 1579183 := bstep (se 1 (by rfl) ⟨1184387, by rfl⟩ : syracuseStep 1579183 = 2368775) B2368775
theorem B1579207 : Blo 1578487 1579207 := bstep (se 1 (by rfl) ⟨1184405, by rfl⟩ : syracuseStep 1579207 = 2368811) B2368811
theorem B1579227 : Blo 1578487 1579227 := bstep (se 1 (by rfl) ⟨1184420, by rfl⟩ : syracuseStep 1579227 = 2368841) B2368841
theorem B4495607 : Blo 1578487 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B1579303 : Blo 1578487 1579303 := bstep (se 1 (by rfl) ⟨1184477, by rfl⟩ : syracuseStep 1579303 = 2368955) B2368955
theorem B1579343 : Blo 1578487 1579343 := bstep (se 1 (by rfl) ⟨1184507, by rfl⟩ : syracuseStep 1579343 = 2369015) B2369015
theorem B1579359 : Blo 1578487 1579359 := bstep (se 1 (by rfl) ⟨1184519, by rfl⟩ : syracuseStep 1579359 = 2369039) B2369039
theorem B1579387 : Blo 1578487 1579387 := bstep (se 1 (by rfl) ⟨1184540, by rfl⟩ : syracuseStep 1579387 = 2369081) B2369081
theorem B1579439 : Blo 1578487 1579439 := bstep (se 1 (by rfl) ⟨1184579, by rfl⟩ : syracuseStep 1579439 = 2369159) B2369159
theorem B1579463 : Blo 1578487 1579463 := bstep (se 1 (by rfl) ⟨1184597, by rfl⟩ : syracuseStep 1579463 = 2369195) B2369195
theorem B1776091 : Blo 1578487 1776091 := bstep (se 1 (by rfl) ⟨1332068, by rfl⟩ : syracuseStep 1776091 = 2664137) B2664137
theorem B1579483 : Blo 1578487 1579483 := bstep (se 1 (by rfl) ⟨1184612, by rfl⟩ : syracuseStep 1579483 = 2369225) B2369225
theorem B5331419 : Blo 1578487 5331419 := bstep (se 1 (by rfl) ⟨3998564, by rfl⟩ : syracuseStep 5331419 = 7997129) B7997129
theorem B12155417 : Blo 1578487 12155417 := bstep (se 2 (by rfl) ⟨4558281, by rfl⟩ : syracuseStep 12155417 = 9116563) B9116563
theorem B7993889 : Blo 1578487 7993889 := bstep (se 2 (by rfl) ⟨2997708, by rfl⟩ : syracuseStep 7993889 = 5995417) B5995417
theorem B1579559 : Blo 1578487 1579559 := bstep (se 1 (by rfl) ⟨1184669, by rfl⟩ : syracuseStep 1579559 = 2369339) B2369339
theorem B1579599 : Blo 1578487 1579599 := bstep (se 1 (by rfl) ⟨1184699, by rfl⟩ : syracuseStep 1579599 = 2369399) B2369399
theorem B1579615 : Blo 1578487 1579615 := bstep (se 1 (by rfl) ⟨1184711, by rfl⟩ : syracuseStep 1579615 = 2369423) B2369423
theorem B1579643 : Blo 1578487 1579643 := bstep (se 1 (by rfl) ⟨1184732, by rfl⟩ : syracuseStep 1579643 = 2369465) B2369465
theorem B1579695 : Blo 1578487 1579695 := bstep (se 1 (by rfl) ⟨1184771, by rfl⟩ : syracuseStep 1579695 = 2369543) B2369543
theorem B3553991 : Blo 1578487 3553991 := bstep (se 1 (by rfl) ⟨2665493, by rfl⟩ : syracuseStep 3553991 = 5330987) B5330987
theorem B1579719 : Blo 1578487 1579719 := bstep (se 1 (by rfl) ⟨1184789, by rfl⟩ : syracuseStep 1579719 = 2369579) B2369579
theorem B1579739 : Blo 1578487 1579739 := bstep (se 1 (by rfl) ⟨1184804, by rfl⟩ : syracuseStep 1579739 = 2369609) B2369609
theorem B1579815 : Blo 1578487 1579815 := bstep (se 1 (by rfl) ⟨1184861, by rfl⟩ : syracuseStep 1579815 = 2369723) B2369723
theorem B1579855 : Blo 1578487 1579855 := bstep (se 1 (by rfl) ⟨1184891, by rfl⟩ : syracuseStep 1579855 = 2369783) B2369783
theorem B1579871 : Blo 1578487 1579871 := bstep (se 1 (by rfl) ⟨1184903, by rfl⟩ : syracuseStep 1579871 = 2369807) B2369807
theorem B1579899 : Blo 1578487 1579899 := bstep (se 1 (by rfl) ⟨1184924, by rfl⟩ : syracuseStep 1579899 = 2369849) B2369849
theorem B1776559 : Blo 1578487 1776559 := bstep (se 1 (by rfl) ⟨1332419, by rfl⟩ : syracuseStep 1776559 = 2664839) B2664839
theorem B1579951 : Blo 1578487 1579951 := bstep (se 1 (by rfl) ⟨1184963, by rfl⟩ : syracuseStep 1579951 = 2369927) B2369927
theorem B1579975 : Blo 1578487 1579975 := bstep (se 1 (by rfl) ⟨1184981, by rfl⟩ : syracuseStep 1579975 = 2369963) B2369963
theorem B1579995 : Blo 1578487 1579995 := bstep (se 1 (by rfl) ⟨1184996, by rfl⟩ : syracuseStep 1579995 = 2369993) B2369993
theorem B6749203 : Blo 1578487 6749203 := bstep (se 1 (by rfl) ⟨5061902, by rfl⟩ : syracuseStep 6749203 = 10123805) B10123805
theorem B1580071 : Blo 1578487 1580071 := bstep (se 1 (by rfl) ⟨1185053, by rfl⟩ : syracuseStep 1580071 = 2370107) B2370107
theorem B1580111 : Blo 1578487 1580111 := bstep (se 1 (by rfl) ⟨1185083, by rfl⟩ : syracuseStep 1580111 = 2370167) B2370167
theorem B1580127 : Blo 1578487 1580127 := bstep (se 1 (by rfl) ⟨1185095, by rfl⟩ : syracuseStep 1580127 = 2370191) B2370191
theorem B1580155 : Blo 1578487 1580155 := bstep (se 1 (by rfl) ⟨1185116, by rfl⟩ : syracuseStep 1580155 = 2370233) B2370233
theorem B5332121 : Blo 1578487 5332121 := bstep (se 2 (by rfl) ⟨1999545, by rfl⟩ : syracuseStep 5332121 = 3999091) B3999091
theorem B5995691 : Blo 1578487 5995691 := bstep (se 1 (by rfl) ⟨4496768, by rfl⟩ : syracuseStep 5995691 = 8993537) B8993537
theorem B1580207 : Blo 1578487 1580207 := bstep (se 1 (by rfl) ⟨1185155, by rfl⟩ : syracuseStep 1580207 = 2370311) B2370311
theorem B17988803 : Blo 1578487 17988803 := bstep (se 1 (by rfl) ⟨13491602, by rfl⟩ : syracuseStep 17988803 = 26983205) B26983205
theorem B1580231 : Blo 1578487 1580231 := bstep (se 1 (by rfl) ⟨1185173, by rfl⟩ : syracuseStep 1580231 = 2370347) B2370347
theorem B1580251 : Blo 1578487 1580251 := bstep (se 1 (by rfl) ⟨1185188, by rfl⟩ : syracuseStep 1580251 = 2370377) B2370377
theorem B1580327 : Blo 1578487 1580327 := bstep (se 1 (by rfl) ⟨1185245, by rfl⟩ : syracuseStep 1580327 = 2370491) B2370491
theorem B1580367 : Blo 1578487 1580367 := bstep (se 1 (by rfl) ⟨1185275, by rfl⟩ : syracuseStep 1580367 = 2370551) B2370551
theorem B1776991 : Blo 1578487 1776991 := bstep (se 1 (by rfl) ⟨1332743, by rfl⟩ : syracuseStep 1776991 = 2665487) B2665487
theorem B1580383 : Blo 1578487 1580383 := bstep (se 1 (by rfl) ⟨1185287, by rfl⟩ : syracuseStep 1580383 = 2370575) B2370575
theorem B1580411 : Blo 1578487 1580411 := bstep (se 1 (by rfl) ⟨1185308, by rfl⟩ : syracuseStep 1580411 = 2370617) B2370617
theorem B1580463 : Blo 1578487 1580463 := bstep (se 1 (by rfl) ⟨1185347, by rfl⟩ : syracuseStep 1580463 = 2370695) B2370695
theorem B1580487 : Blo 1578487 1580487 := bstep (se 1 (by rfl) ⟨1185365, by rfl⟩ : syracuseStep 1580487 = 2370731) B2370731
theorem B3997147 : Blo 1578487 3997147 := bstep (se 1 (by rfl) ⟨2997860, by rfl⟩ : syracuseStep 3997147 = 5995721) B5995721
theorem B3554855 : Blo 1578487 3554855 := bstep (se 1 (by rfl) ⟨2666141, by rfl⟩ : syracuseStep 3554855 = 5332283) B5332283
theorem B2530855 : Blo 1578487 2530855 := bstep (se 1 (by rfl) ⟨1898141, by rfl⟩ : syracuseStep 2530855 = 3796283) B3796283
theorem B20512379 : Blo 1578487 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B13491845 : Blo 1578487 13491845 := bstep (se 4 (by rfl) ⟨1264860, by rfl⟩ : syracuseStep 13491845 = 2529721) B2529721
theorem B10395335 : Blo 1578487 10395335 := bstep (se 1 (by rfl) ⟨7796501, by rfl⟩ : syracuseStep 10395335 = 15593003) B15593003
theorem B1777351 : Blo 1578487 1777351 := bstep (se 1 (by rfl) ⟨1333013, by rfl⟩ : syracuseStep 1777351 = 2666027) B2666027
theorem B43204367 : Blo 1578487 43204367 := bstep (se 1 (by rfl) ⟨32403275, by rfl⟩ : syracuseStep 43204367 = 64806551) B64806551
theorem B5693257 : Blo 1578487 5693257 := bstep (se 2 (by rfl) ⟨2134971, by rfl⟩ : syracuseStep 5693257 = 4269943) B4269943
theorem B3555179 : Blo 1578487 3555179 := bstep (se 1 (by rfl) ⟨2666384, by rfl⟩ : syracuseStep 3555179 = 5332769) B5332769
theorem B10952567 : Blo 1578487 10952567 := bstep (se 1 (by rfl) ⟨8214425, by rfl⟩ : syracuseStep 10952567 = 16428851) B16428851
theorem B3555233 : Blo 1578487 3555233 := bstep (se 2 (by rfl) ⟨1333212, by rfl⟩ : syracuseStep 3555233 = 2666425) B2666425
theorem B11386889 : Blo 1578487 11386889 := bstep (se 2 (by rfl) ⟨4270083, by rfl⟩ : syracuseStep 11386889 = 8540167) B8540167
theorem B12329009 : Blo 1578487 12329009 := bstep (se 2 (by rfl) ⟨4623378, by rfl⟩ : syracuseStep 12329009 = 9246757) B9246757
theorem B34635853 : Blo 1578487 34635853 := bstep (se 3 (by rfl) ⟨6494222, by rfl⟩ : syracuseStep 34635853 = 12988445) B12988445
theorem B3997907 : Blo 1578487 3997907 := bstep (se 1 (by rfl) ⟨2998430, by rfl⟩ : syracuseStep 3997907 = 5996861) B5996861
theorem B3555539 : Blo 1578487 3555539 := bstep (se 1 (by rfl) ⟨2666654, by rfl⟩ : syracuseStep 3555539 = 5333309) B5333309
theorem B3555593 : Blo 1578487 3555593 := bstep (se 2 (by rfl) ⟨1333347, by rfl⟩ : syracuseStep 3555593 = 2666695) B2666695
theorem B8536427 : Blo 1578487 8536427 := bstep (se 1 (by rfl) ⟨6402320, by rfl⟩ : syracuseStep 8536427 = 12804641) B12804641
theorem B11993507 : Blo 1578487 11993507 := bstep (se 1 (by rfl) ⟨8995130, by rfl⟩ : syracuseStep 11993507 = 17990261) B17990261
theorem B2367911 : Blo 1578487 2367911 := bstep (se 1 (by rfl) ⟨1775933, by rfl⟩ : syracuseStep 2367911 = 3551867) B3551867
theorem B3998119 : Blo 1578487 3998119 := bstep (se 1 (by rfl) ⟨2998589, by rfl⟩ : syracuseStep 3998119 = 5997179) B5997179
theorem B4497839 : Blo 1578487 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B3555809 : Blo 1578487 3555809 := bstep (se 2 (by rfl) ⟨1333428, by rfl⟩ : syracuseStep 3555809 = 2666857) B2666857
theorem B2367995 : Blo 1578487 2367995 := bstep (se 1 (by rfl) ⟨1775996, by rfl⟩ : syracuseStep 2367995 = 3551993) B3551993
theorem B3998281 : Blo 1578487 3998281 := bstep (se 2 (by rfl) ⟨1499355, by rfl⟩ : syracuseStep 3998281 = 2998711) B2998711
theorem B2368121 : Blo 1578487 2368121 := bstep (se 2 (by rfl) ⟨888045, by rfl⟩ : syracuseStep 2368121 = 1776091) B1776091
theorem B16024211 : Blo 1578487 16024211 := bstep (se 1 (by rfl) ⟨12018158, by rfl⟩ : syracuseStep 16024211 = 24036317) B24036317
theorem B2368175 : Blo 1578487 2368175 := bstep (se 1 (by rfl) ⟨1776131, by rfl⟩ : syracuseStep 2368175 = 3552263) B3552263
theorem B3793591 : Blo 1578487 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B5333687 : Blo 1578487 5333687 := bstep (se 1 (by rfl) ⟨4000265, by rfl⟩ : syracuseStep 5333687 = 8000531) B8000531
theorem B6742727 : Blo 1578487 6742727 := bstep (se 1 (by rfl) ⟨5057045, by rfl⟩ : syracuseStep 6742727 = 10114091) B10114091
theorem B2368223 : Blo 1578487 2368223 := bstep (se 1 (by rfl) ⟨1776167, by rfl⟩ : syracuseStep 2368223 = 3552335) B3552335
theorem B4268819 : Blo 1578487 4268819 := bstep (se 1 (by rfl) ⟨3201614, by rfl⟩ : syracuseStep 4268819 = 6403229) B6403229
theorem B15188897 : Blo 1578487 15188897 := bstep (se 2 (by rfl) ⟨5695836, by rfl⟩ : syracuseStep 15188897 = 11391673) B11391673
theorem B2368487 : Blo 1578487 2368487 := bstep (se 1 (by rfl) ⟨1776365, by rfl⟩ : syracuseStep 2368487 = 3552731) B3552731
theorem B5997665 : Blo 1578487 5997665 := bstep (se 2 (by rfl) ⟨2249124, by rfl⟩ : syracuseStep 5997665 = 4498249) B4498249
theorem B27362447 : Blo 1578487 27362447 := bstep (se 1 (by rfl) ⟨20521835, by rfl⟩ : syracuseStep 27362447 = 41043671) B41043671
theorem B2368745 : Blo 1578487 2368745 := bstep (se 2 (by rfl) ⟨888279, by rfl⟩ : syracuseStep 2368745 = 1776559) B1776559
theorem B2368799 : Blo 1578487 2368799 := bstep (se 1 (by rfl) ⟨1776599, by rfl⟩ : syracuseStep 2368799 = 3553199) B3553199
theorem B3081503 : Blo 1578487 3081503 := bstep (se 1 (by rfl) ⟨2311127, by rfl⟩ : syracuseStep 3081503 = 4622255) B4622255
theorem B5768491 : Blo 1578487 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B3999071 : Blo 1578487 3999071 := bstep (se 1 (by rfl) ⟨2999303, by rfl⟩ : syracuseStep 3999071 = 5998607) B5998607
theorem B2368967 : Blo 1578487 2368967 := bstep (se 1 (by rfl) ⟨1776725, by rfl⟩ : syracuseStep 2368967 = 3553451) B3553451
theorem B8103611 : Blo 1578487 8103611 := bstep (se 1 (by rfl) ⟨6077708, by rfl⟩ : syracuseStep 8103611 = 12155417) B12155417
theorem B3000071 : Blo 1578487 3000071 := bstep (se 1 (by rfl) ⟨2250053, by rfl⟩ : syracuseStep 3000071 = 4500107) B4500107
theorem B2369321 : Blo 1578487 2369321 := bstep (se 2 (by rfl) ⟨888495, by rfl⟩ : syracuseStep 2369321 = 1776991) B1776991
theorem B2369327 : Blo 1578487 2369327 := bstep (se 1 (by rfl) ⟨1776995, by rfl⟩ : syracuseStep 2369327 = 3553991) B3553991
theorem B20244329 : Blo 1578487 20244329 := bstep (se 2 (by rfl) ⟨7591623, by rfl⟩ : syracuseStep 20244329 = 15183247) B15183247
theorem B3901289 : Blo 1578487 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B57657197 : Blo 1578487 57657197 := bstep (se 3 (by rfl) ⟨10810724, by rfl⟩ : syracuseStep 57657197 = 21621449) B21621449
theorem B2369801 : Blo 1578487 2369801 := bstep (se 2 (by rfl) ⟨888675, by rfl⟩ : syracuseStep 2369801 = 1777351) B1777351
theorem B2369903 : Blo 1578487 2369903 := bstep (se 1 (by rfl) ⟨1777427, by rfl⟩ : syracuseStep 2369903 = 3554855) B3554855
theorem B13674919 : Blo 1578487 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B4000175 : Blo 1578487 4000175 := bstep (se 1 (by rfl) ⟨3000131, by rfl⟩ : syracuseStep 4000175 = 6000263) B6000263
theorem B4000225 : Blo 1578487 4000225 := bstep (se 2 (by rfl) ⟨1500084, by rfl⟩ : syracuseStep 4000225 = 3000169) B3000169
theorem B7997939 : Blo 1578487 7997939 := bstep (se 1 (by rfl) ⟨5998454, by rfl⟩ : syracuseStep 7997939 = 11996909) B11996909
theorem B5327423 : Blo 1578487 5327423 := bstep (se 1 (by rfl) ⟨3995567, by rfl⟩ : syracuseStep 5327423 = 7991135) B7991135
theorem B2370119 : Blo 1578487 2370119 := bstep (se 1 (by rfl) ⟨1777589, by rfl⟩ : syracuseStep 2370119 = 3555179) B3555179
theorem B7301711 : Blo 1578487 7301711 := bstep (se 1 (by rfl) ⟨5476283, by rfl⟩ : syracuseStep 7301711 = 10952567) B10952567
theorem B2370155 : Blo 1578487 2370155 := bstep (se 1 (by rfl) ⟨1777616, by rfl⟩ : syracuseStep 2370155 = 3555233) B3555233
theorem B2665183 : Blo 1578487 2665183 := bstep (se 1 (by rfl) ⟨1998887, by rfl⟩ : syracuseStep 2665183 = 3997775) B3997775
theorem B15379217 : Blo 1578487 15379217 := bstep (se 2 (by rfl) ⟨5767206, by rfl⟩ : syracuseStep 15379217 = 11534413) B11534413
theorem B11995937 : Blo 1578487 11995937 := bstep (se 2 (by rfl) ⟨4498476, by rfl⟩ : syracuseStep 11995937 = 8996953) B8996953
theorem B2370383 : Blo 1578487 2370383 := bstep (se 1 (by rfl) ⟨1777787, by rfl⟩ : syracuseStep 2370383 = 3555575) B3555575
theorem B3845107 : Blo 1578487 3845107 := bstep (se 1 (by rfl) ⟨2883830, by rfl⟩ : syracuseStep 3845107 = 5767661) B5767661
theorem B6745103 : Blo 1578487 6745103 := bstep (se 1 (by rfl) ⟨5058827, by rfl⟩ : syracuseStep 6745103 = 10117655) B10117655
theorem B14404675 : Blo 1578487 14404675 := bstep (se 1 (by rfl) ⟨10803506, by rfl⟩ : syracuseStep 14404675 = 21607013) B21607013
theorem B7998587 : Blo 1578487 7998587 := bstep (se 1 (by rfl) ⟨5998940, by rfl⟩ : syracuseStep 7998587 = 11997881) B11997881
theorem B2665615 : Blo 1578487 2665615 := bstep (se 1 (by rfl) ⟨1999211, by rfl⟩ : syracuseStep 2665615 = 3998423) B3998423
theorem B3419335 : Blo 1578487 3419335 := bstep (se 1 (by rfl) ⟨2564501, by rfl⟩ : syracuseStep 3419335 = 5129003) B5129003
theorem B3796321 : Blo 1578487 3796321 := bstep (se 2 (by rfl) ⟨1423620, by rfl⟩ : syracuseStep 3796321 = 2847241) B2847241
theorem B2665865 : Blo 1578487 2665865 := bstep (se 2 (by rfl) ⟨999699, by rfl⟩ : syracuseStep 2665865 = 1999399) B1999399
theorem B2133415 : Blo 1578487 2133415 := bstep (se 1 (by rfl) ⟨1600061, by rfl⟩ : syracuseStep 2133415 = 3200123) B3200123
theorem B7589335 : Blo 1578487 7589335 := bstep (se 1 (by rfl) ⟨5692001, by rfl⟩ : syracuseStep 7589335 = 11384003) B11384003
theorem B11546221 : Blo 1578487 11546221 := bstep (se 3 (by rfl) ⟨2164916, by rfl⟩ : syracuseStep 11546221 = 4329833) B4329833
theorem B7999235 : Blo 1578487 7999235 := bstep (se 1 (by rfl) ⟨5999426, by rfl⟩ : syracuseStep 7999235 = 11998853) B11998853
theorem B8539951 : Blo 1578487 8539951 := bstep (se 1 (by rfl) ⟨6404963, by rfl⟩ : syracuseStep 8539951 = 12809927) B12809927
theorem B2666297 : Blo 1578487 2666297 := bstep (se 2 (by rfl) ⟨999861, by rfl⟩ : syracuseStep 2666297 = 1999723) B1999723
theorem B8990621 : Blo 1578487 8990621 := bstep (se 3 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 8990621 = 3371483) B3371483
theorem B4272029 : Blo 1578487 4272029 := bstep (se 3 (by rfl) ⟨801005, by rfl⟩ : syracuseStep 4272029 = 1602011) B1602011
theorem B7991297 : Blo 1578487 7991297 := bstep (se 2 (by rfl) ⟨2996736, by rfl⟩ : syracuseStep 7991297 = 5993473) B5993473
theorem B8998937 : Blo 1578487 8998937 := bstep (se 2 (by rfl) ⟨3374601, by rfl⟩ : syracuseStep 8998937 = 6749203) B6749203
theorem B5329259 : Blo 1578487 5329259 := bstep (se 1 (by rfl) ⟨3996944, by rfl⟩ : syracuseStep 5329259 = 7993889) B7993889
theorem B1602043 : Blo 1578487 1602043 := bstep (se 1 (by rfl) ⟨1201532, by rfl⟩ : syracuseStep 1602043 = 2403065) B2403065
theorem B5329529 : Blo 1578487 5329529 := bstep (se 2 (by rfl) ⟨1998573, by rfl⟩ : syracuseStep 5329529 = 3997147) B3997147
theorem B10121881 : Blo 1578487 10121881 := bstep (se 2 (by rfl) ⟨3795705, by rfl⟩ : syracuseStep 10121881 = 7591411) B7591411
theorem B7992107 : Blo 1578487 7992107 := bstep (se 1 (by rfl) ⟨5994080, by rfl⟩ : syracuseStep 7992107 = 11988161) B11988161
theorem B3552155 : Blo 1578487 3552155 := bstep (se 1 (by rfl) ⟨2664116, by rfl⟩ : syracuseStep 3552155 = 5328233) B5328233
theorem B11990105 : Blo 1578487 11990105 := bstep (se 2 (by rfl) ⟨4496289, by rfl⟩ : syracuseStep 11990105 = 8992579) B8992579
theorem B3552353 : Blo 1578487 3552353 := bstep (se 2 (by rfl) ⟨1332132, by rfl⟩ : syracuseStep 3552353 = 2664265) B2664265
theorem B7591009 : Blo 1578487 7591009 := bstep (se 2 (by rfl) ⟨2846628, by rfl⟩ : syracuseStep 7591009 = 5693257) B5693257
theorem B4559969 : Blo 1578487 4559969 := bstep (se 2 (by rfl) ⟨1709988, by rfl⟩ : syracuseStep 4559969 = 3419977) B3419977
theorem B7206131 : Blo 1578487 7206131 := bstep (se 1 (by rfl) ⟨5404598, by rfl⟩ : syracuseStep 7206131 = 10809197) B10809197
theorem B3552551 : Blo 1578487 3552551 := bstep (se 1 (by rfl) ⟨2664413, by rfl⟩ : syracuseStep 3552551 = 5328827) B5328827
theorem B8000855 : Blo 1578487 8000855 := bstep (se 1 (by rfl) ⟨6000641, by rfl⟩ : syracuseStep 8000855 = 12001283) B12001283
theorem B131511691 : Blo 1578487 131511691 := bstep (se 1 (by rfl) ⟨98633768, by rfl⟩ : syracuseStep 131511691 = 197267537) B197267537
theorem B1578491 : Blo 1578487 1578491 := bstep (se 1 (by rfl) ⟨1183868, by rfl⟩ : syracuseStep 1578491 = 2367737) B2367737
theorem B1578559 : Blo 1578487 1578559 := bstep (se 1 (by rfl) ⟨1183919, by rfl⟩ : syracuseStep 1578559 = 2367839) B2367839
theorem B55481921 : Blo 1578487 55481921 := bstep (se 2 (by rfl) ⟨20805720, by rfl⟩ : syracuseStep 55481921 = 41611441) B41611441
theorem B1578567 : Blo 1578487 1578567 := bstep (se 1 (by rfl) ⟨1183925, by rfl⟩ : syracuseStep 1578567 = 2367851) B2367851
theorem B3552929 : Blo 1578487 3552929 := bstep (se 2 (by rfl) ⟨1332348, by rfl⟩ : syracuseStep 3552929 = 2664697) B2664697
theorem B1578719 : Blo 1578487 1578719 := bstep (se 1 (by rfl) ⟨1184039, by rfl⟩ : syracuseStep 1578719 = 2368079) B2368079
theorem B10254109 : Blo 1578487 10254109 := bstep (se 3 (by rfl) ⟨1922645, by rfl⟩ : syracuseStep 10254109 = 3845291) B3845291
theorem B1578799 : Blo 1578487 1578799 := bstep (se 1 (by rfl) ⟨1184099, by rfl⟩ : syracuseStep 1578799 = 2368199) B2368199
theorem B1578907 : Blo 1578487 1578907 := bstep (se 1 (by rfl) ⟨1184180, by rfl⟩ : syracuseStep 1578907 = 2368361) B2368361
theorem B1578959 : Blo 1578487 1578959 := bstep (se 1 (by rfl) ⟨1184219, by rfl⟩ : syracuseStep 1578959 = 2368439) B2368439
theorem B1578983 : Blo 1578487 1578983 := bstep (se 1 (by rfl) ⟨1184237, by rfl⟩ : syracuseStep 1578983 = 2368475) B2368475
theorem B3553289 : Blo 1578487 3553289 := bstep (se 2 (by rfl) ⟨1332483, by rfl⟩ : syracuseStep 3553289 = 2664967) B2664967
theorem B5994749 : Blo 1578487 5994749 := bstep (se 3 (by rfl) ⟨1124015, by rfl⟩ : syracuseStep 5994749 = 2248031) B2248031
theorem B3291401 : Blo 1578487 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B1579295 : Blo 1578487 1579295 := bstep (se 1 (by rfl) ⟨1184471, by rfl⟩ : syracuseStep 1579295 = 2368943) B2368943
theorem B1775911 : Blo 1578487 1775911 := bstep (se 1 (by rfl) ⟨1331933, by rfl⟩ : syracuseStep 1775911 = 2663867) B2663867
theorem B13490509 : Blo 1578487 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B1579355 : Blo 1578487 1579355 := bstep (se 1 (by rfl) ⟨1184516, by rfl⟩ : syracuseStep 1579355 = 2369033) B2369033
theorem B1775983 : Blo 1578487 1775983 := bstep (se 1 (by rfl) ⟨1331987, by rfl⟩ : syracuseStep 1775983 = 2663975) B2663975
theorem B1579375 : Blo 1578487 1579375 := bstep (se 1 (by rfl) ⟨1184531, by rfl⟩ : syracuseStep 1579375 = 2369063) B2369063
theorem B5331311 : Blo 1578487 5331311 := bstep (se 1 (by rfl) ⟨3998483, by rfl⟩ : syracuseStep 5331311 = 7996967) B7996967
theorem B3553703 : Blo 1578487 3553703 := bstep (se 1 (by rfl) ⟨2665277, by rfl⟩ : syracuseStep 3553703 = 5330555) B5330555
theorem B1579431 : Blo 1578487 1579431 := bstep (se 1 (by rfl) ⟨1184573, by rfl⟩ : syracuseStep 1579431 = 2369147) B2369147
theorem B3996155 : Blo 1578487 3996155 := bstep (se 1 (by rfl) ⟨2997116, by rfl⟩ : syracuseStep 3996155 = 5994233) B5994233
theorem B1579515 : Blo 1578487 1579515 := bstep (se 1 (by rfl) ⟨1184636, by rfl⟩ : syracuseStep 1579515 = 2369273) B2369273
theorem B3553811 : Blo 1578487 3553811 := bstep (se 1 (by rfl) ⟨2665358, by rfl⟩ : syracuseStep 3553811 = 5330717) B5330717
theorem B1579583 : Blo 1578487 1579583 := bstep (se 1 (by rfl) ⟨1184687, by rfl⟩ : syracuseStep 1579583 = 2369375) B2369375
theorem B109369925 : Blo 1578487 109369925 := bstep (se 4 (by rfl) ⟨10253430, by rfl⟩ : syracuseStep 109369925 = 20506861) B20506861
theorem B1776199 : Blo 1578487 1776199 := bstep (se 1 (by rfl) ⟨1332149, by rfl⟩ : syracuseStep 1776199 = 2664299) B2664299
theorem B1579591 : Blo 1578487 1579591 := bstep (se 1 (by rfl) ⟨1184693, by rfl⟩ : syracuseStep 1579591 = 2369387) B2369387
theorem B3553865 : Blo 1578487 3553865 := bstep (se 2 (by rfl) ⟨1332699, by rfl⟩ : syracuseStep 3553865 = 2665399) B2665399
theorem B7994051 : Blo 1578487 7994051 := bstep (se 1 (by rfl) ⟨5995538, by rfl⟩ : syracuseStep 7994051 = 11991077) B11991077
theorem B1579743 : Blo 1578487 1579743 := bstep (se 1 (by rfl) ⟨1184807, by rfl⟩ : syracuseStep 1579743 = 2369615) B2369615
theorem B72981283 : Blo 1578487 72981283 := bstep (se 1 (by rfl) ⟨54735962, by rfl⟩ : syracuseStep 72981283 = 109471925) B109471925
theorem B1579823 : Blo 1578487 1579823 := bstep (se 1 (by rfl) ⟨1184867, by rfl⟩ : syracuseStep 1579823 = 2369735) B2369735
theorem B2997071 : Blo 1578487 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B1579931 : Blo 1578487 1579931 := bstep (se 1 (by rfl) ⟨1184948, by rfl⟩ : syracuseStep 1579931 = 2369897) B2369897
theorem B1579983 : Blo 1578487 1579983 := bstep (se 1 (by rfl) ⟨1184987, by rfl⟩ : syracuseStep 1579983 = 2369975) B2369975
theorem B3554279 : Blo 1578487 3554279 := bstep (se 1 (by rfl) ⟨2665709, by rfl⟩ : syracuseStep 3554279 = 5331419) B5331419
theorem B1580007 : Blo 1578487 1580007 := bstep (se 1 (by rfl) ⟨1185005, by rfl⟩ : syracuseStep 1580007 = 2370011) B2370011
theorem B15186973 : Blo 1578487 15186973 := bstep (se 3 (by rfl) ⟨2847557, by rfl⟩ : syracuseStep 15186973 = 5695115) B5695115
theorem B27720893 : Blo 1578487 27720893 := bstep (se 3 (by rfl) ⟨5197667, by rfl⟩ : syracuseStep 27720893 = 10395335) B10395335
theorem B2997481 : Blo 1578487 2997481 := bstep (se 2 (by rfl) ⟨1124055, by rfl⟩ : syracuseStep 2997481 = 2248111) B2248111
theorem B13491467 : Blo 1578487 13491467 := bstep (se 1 (by rfl) ⟨10118600, by rfl⟩ : syracuseStep 13491467 = 20237201) B20237201
theorem B1580319 : Blo 1578487 1580319 := bstep (se 1 (by rfl) ⟨1185239, by rfl⟩ : syracuseStep 1580319 = 2370479) B2370479
theorem B1580379 : Blo 1578487 1580379 := bstep (se 1 (by rfl) ⟨1185284, by rfl⟩ : syracuseStep 1580379 = 2370569) B2370569
theorem B3554657 : Blo 1578487 3554657 := bstep (se 2 (by rfl) ⟨1332996, by rfl⟩ : syracuseStep 3554657 = 2665993) B2665993
theorem B1580399 : Blo 1578487 1580399 := bstep (se 1 (by rfl) ⟨1185299, by rfl⟩ : syracuseStep 1580399 = 2370599) B2370599
theorem B2997641 : Blo 1578487 2997641 := bstep (se 2 (by rfl) ⟨1124115, by rfl⟩ : syracuseStep 2997641 = 2248231) B2248231
theorem B3374473 : Blo 1578487 3374473 := bstep (se 2 (by rfl) ⟨1265427, by rfl⟩ : syracuseStep 3374473 = 2530855) B2530855
theorem B1777063 : Blo 1578487 1777063 := bstep (se 1 (by rfl) ⟨1332797, by rfl⟩ : syracuseStep 1777063 = 2665595) B2665595
theorem B1580455 : Blo 1578487 1580455 := bstep (se 1 (by rfl) ⟨1185341, by rfl⟩ : syracuseStep 1580455 = 2370683) B2370683
theorem B3554747 : Blo 1578487 3554747 := bstep (se 1 (by rfl) ⟨2666060, by rfl⟩ : syracuseStep 3554747 = 5332121) B5332121
theorem B3997127 : Blo 1578487 3997127 := bstep (se 1 (by rfl) ⟨2997845, by rfl⟩ : syracuseStep 3997127 = 5995691) B5995691
theorem B11992535 : Blo 1578487 11992535 := bstep (se 1 (by rfl) ⟨8994401, by rfl⟩ : syracuseStep 11992535 = 17988803) B17988803
theorem B3554873 : Blo 1578487 3554873 := bstep (se 2 (by rfl) ⟨1333077, by rfl⟩ : syracuseStep 3554873 = 2666155) B2666155
theorem B43228889 : Blo 1578487 43228889 := bstep (se 2 (by rfl) ⟨16210833, by rfl⟩ : syracuseStep 43228889 = 32421667) B32421667
theorem B5332715 : Blo 1578487 5332715 := bstep (se 1 (by rfl) ⟨3999536, by rfl⟩ : syracuseStep 5332715 = 7999073) B7999073
theorem B8994563 : Blo 1578487 8994563 := bstep (se 1 (by rfl) ⟨6745922, by rfl⟩ : syracuseStep 8994563 = 13491845) B13491845
theorem B8544041 : Blo 1578487 8544041 := bstep (se 2 (by rfl) ⟨3204015, by rfl⟩ : syracuseStep 8544041 = 6408031) B6408031
theorem B2998073 : Blo 1578487 2998073 := bstep (se 2 (by rfl) ⟨1124277, by rfl⟩ : syracuseStep 2998073 = 2248555) B2248555
theorem B28802911 : Blo 1578487 28802911 := bstep (se 1 (by rfl) ⟨21602183, by rfl⟩ : syracuseStep 28802911 = 43204367) B43204367
theorem B1777639 : Blo 1578487 1777639 := bstep (se 1 (by rfl) ⟨1333229, by rfl⟩ : syracuseStep 1777639 = 2666459) B2666459
theorem B7995671 : Blo 1578487 7995671 := bstep (se 1 (by rfl) ⟨5996753, by rfl⟩ : syracuseStep 7995671 = 11993507) B11993507
theorem B2998559 : Blo 1578487 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B2367881 : Blo 1578487 2367881 := bstep (se 2 (by rfl) ⟨887955, by rfl⟩ : syracuseStep 2367881 = 1775911) B1775911
theorem B10682807 : Blo 1578487 10682807 := bstep (se 1 (by rfl) ⟨8012105, by rfl⟩ : syracuseStep 10682807 = 16024211) B16024211
theorem B3555791 : Blo 1578487 3555791 := bstep (se 1 (by rfl) ⟨2666843, by rfl⟩ : syracuseStep 3555791 = 5333687) B5333687
theorem B2367977 : Blo 1578487 2367977 := bstep (se 2 (by rfl) ⟨887991, by rfl⟩ : syracuseStep 2367977 = 1775983) B1775983
theorem B2368103 : Blo 1578487 2368103 := bstep (se 1 (by rfl) ⟨1776077, by rfl⟩ : syracuseStep 2368103 = 3552155) B3552155
theorem B10125931 : Blo 1578487 10125931 := bstep (se 1 (by rfl) ⟨7594448, by rfl⟩ : syracuseStep 10125931 = 15188897) B15188897
theorem B5333633 : Blo 1578487 5333633 := bstep (se 2 (by rfl) ⟨2000112, by rfl⟩ : syracuseStep 5333633 = 4000225) B4000225
theorem B2368235 : Blo 1578487 2368235 := bstep (se 1 (by rfl) ⟨1776176, by rfl⟩ : syracuseStep 2368235 = 3552353) B3552353
theorem B3998443 : Blo 1578487 3998443 := bstep (se 1 (by rfl) ⟨2998832, by rfl⟩ : syracuseStep 3998443 = 5997665) B5997665
theorem B3039979 : Blo 1578487 3039979 := bstep (se 1 (by rfl) ⟨2279984, by rfl⟩ : syracuseStep 3039979 = 4559969) B4559969
theorem B2368265 : Blo 1578487 2368265 := bstep (se 2 (by rfl) ⟨888099, by rfl⟩ : syracuseStep 2368265 = 1776199) B1776199
theorem B2368367 : Blo 1578487 2368367 := bstep (se 1 (by rfl) ⟨1776275, by rfl⟩ : syracuseStep 2368367 = 3552551) B3552551
theorem B5333903 : Blo 1578487 5333903 := bstep (se 1 (by rfl) ⟨4000427, by rfl⟩ : syracuseStep 5333903 = 8000855) B8000855
theorem B36987947 : Blo 1578487 36987947 := bstep (se 1 (by rfl) ⟨27740960, by rfl⟩ : syracuseStep 36987947 = 55481921) B55481921
theorem B2368619 : Blo 1578487 2368619 := bstep (se 1 (by rfl) ⟨1776464, by rfl⟩ : syracuseStep 2368619 = 3552929) B3552929
theorem B2000047 : Blo 1578487 2000047 := bstep (se 1 (by rfl) ⟨1500035, by rfl⟩ : syracuseStep 2000047 = 3000071) B3000071
theorem B2368859 : Blo 1578487 2368859 := bstep (se 1 (by rfl) ⟨1776644, by rfl⟩ : syracuseStep 2368859 = 3553289) B3553289
theorem B2369135 : Blo 1578487 2369135 := bstep (se 1 (by rfl) ⟨1776851, by rfl⟩ : syracuseStep 2369135 = 3553703) B3553703
theorem B2664103 : Blo 1578487 2664103 := bstep (se 1 (by rfl) ⟨1998077, by rfl⟩ : syracuseStep 2664103 = 3996155) B3996155
theorem B2369207 : Blo 1578487 2369207 := bstep (se 1 (by rfl) ⟨1776905, by rfl⟩ : syracuseStep 2369207 = 3553811) B3553811
theorem B2369243 : Blo 1578487 2369243 := bstep (se 1 (by rfl) ⟨1776932, by rfl⟩ : syracuseStep 2369243 = 3553865) B3553865
theorem B4867807 : Blo 1578487 4867807 := bstep (se 1 (by rfl) ⟨3650855, by rfl⟩ : syracuseStep 4867807 = 7301711) B7301711
theorem B4499297 : Blo 1578487 4499297 := bstep (se 2 (by rfl) ⟨1687236, by rfl⟩ : syracuseStep 4499297 = 3374473) B3374473
theorem B7997291 : Blo 1578487 7997291 := bstep (se 1 (by rfl) ⟨5997968, by rfl⟩ : syracuseStep 7997291 = 11995937) B11995937
theorem B2844553 : Blo 1578487 2844553 := bstep (se 2 (by rfl) ⟨1066707, by rfl⟩ : syracuseStep 2844553 = 2133415) B2133415
theorem B2369417 : Blo 1578487 2369417 := bstep (se 2 (by rfl) ⟨888531, by rfl⟩ : syracuseStep 2369417 = 1777063) B1777063
theorem B10119113 : Blo 1578487 10119113 := bstep (se 2 (by rfl) ⟨3794667, by rfl⟩ : syracuseStep 10119113 = 7589335) B7589335
theorem B2369519 : Blo 1578487 2369519 := bstep (se 1 (by rfl) ⟨1777139, by rfl⟩ : syracuseStep 2369519 = 3554279) B3554279
theorem B15394961 : Blo 1578487 15394961 := bstep (se 2 (by rfl) ⟨5773110, by rfl⟩ : syracuseStep 15394961 = 11546221) B11546221
theorem B2369771 : Blo 1578487 2369771 := bstep (se 1 (by rfl) ⟨1777328, by rfl⟩ : syracuseStep 2369771 = 3554657) B3554657
theorem B2369831 : Blo 1578487 2369831 := bstep (se 1 (by rfl) ⟨1777373, by rfl⟩ : syracuseStep 2369831 = 3554747) B3554747
theorem B2664751 : Blo 1578487 2664751 := bstep (se 1 (by rfl) ⟨1998563, by rfl⟩ : syracuseStep 2664751 = 3997127) B3997127
theorem B2369915 : Blo 1578487 2369915 := bstep (se 1 (by rfl) ⟨1777436, by rfl⟩ : syracuseStep 2369915 = 3554873) B3554873
theorem B5696027 : Blo 1578487 5696027 := bstep (se 1 (by rfl) ⟨4272020, by rfl⟩ : syracuseStep 5696027 = 8544041) B8544041
theorem B2370185 : Blo 1578487 2370185 := bstep (se 2 (by rfl) ⟨888819, by rfl⟩ : syracuseStep 2370185 = 1777639) B1777639
theorem B5327531 : Blo 1578487 5327531 := bstep (se 1 (by rfl) ⟨3995648, by rfl⟩ : syracuseStep 5327531 = 7991297) B7991297
theorem B5999291 : Blo 1578487 5999291 := bstep (se 1 (by rfl) ⟨4499468, by rfl⟩ : syracuseStep 5999291 = 8998937) B8998937
theorem B8219339 : Blo 1578487 8219339 := bstep (se 1 (by rfl) ⟨6164504, by rfl⟩ : syracuseStep 8219339 = 12329009) B12329009
theorem B46181137 : Blo 1578487 46181137 := bstep (se 2 (by rfl) ⟨17317926, by rfl⟩ : syracuseStep 46181137 = 34635853) B34635853
theorem B2665271 : Blo 1578487 2665271 := bstep (se 1 (by rfl) ⟨1998953, by rfl⟩ : syracuseStep 2665271 = 3997907) B3997907
theorem B2370359 : Blo 1578487 2370359 := bstep (se 1 (by rfl) ⟨1777769, by rfl⟩ : syracuseStep 2370359 = 3555539) B3555539
theorem B2370395 : Blo 1578487 2370395 := bstep (se 1 (by rfl) ⟨1777796, by rfl⟩ : syracuseStep 2370395 = 3555593) B3555593
theorem B2370539 : Blo 1578487 2370539 := bstep (se 1 (by rfl) ⟨1777904, by rfl⟩ : syracuseStep 2370539 = 3555809) B3555809
theorem B5328071 : Blo 1578487 5328071 := bstep (se 1 (by rfl) ⟨3996053, by rfl⟩ : syracuseStep 5328071 = 7992107) B7992107
theorem B8777069 : Blo 1578487 8777069 := bstep (se 3 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 8777069 = 3291401) B3291401
theorem B13495841 : Blo 1578487 13495841 := bstep (se 2 (by rfl) ⟨5060940, by rfl⟩ : syracuseStep 13495841 = 10121881) B10121881
theorem B2666047 : Blo 1578487 2666047 := bstep (se 1 (by rfl) ⟨1999535, by rfl⟩ : syracuseStep 2666047 = 3999071) B3999071
theorem B5058121 : Blo 1578487 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B97308377 : Blo 1578487 97308377 := bstep (se 2 (by rfl) ⟨36490641, by rfl⟩ : syracuseStep 97308377 = 72981283) B72981283
theorem B13496219 : Blo 1578487 13496219 := bstep (se 1 (by rfl) ⟨10122164, by rfl⟩ : syracuseStep 13496219 = 20244329) B20244329
theorem B19206233 : Blo 1578487 19206233 := bstep (se 2 (by rfl) ⟨7202337, by rfl⟩ : syracuseStep 19206233 = 14404675) B14404675
theorem B10121345 : Blo 1578487 10121345 := bstep (se 2 (by rfl) ⟨3795504, by rfl⟩ : syracuseStep 10121345 = 7591009) B7591009
theorem B4559113 : Blo 1578487 4559113 := bstep (se 2 (by rfl) ⟨1709667, by rfl⟩ : syracuseStep 4559113 = 3419335) B3419335
theorem B2666783 : Blo 1578487 2666783 := bstep (se 1 (by rfl) ⟨2000087, by rfl⟩ : syracuseStep 2666783 = 4000175) B4000175
theorem B3551615 : Blo 1578487 3551615 := bstep (se 1 (by rfl) ⟨2663711, by rfl⟩ : syracuseStep 3551615 = 5327423) B5327423
theorem B72913283 : Blo 1578487 72913283 := bstep (se 1 (by rfl) ⟨54684962, by rfl⟩ : syracuseStep 72913283 = 109369925) B109369925
theorem B5329367 : Blo 1578487 5329367 := bstep (se 1 (by rfl) ⟨3997025, by rfl⟩ : syracuseStep 5329367 = 7994051) B7994051
theorem B10252811 : Blo 1578487 10252811 := bstep (se 1 (by rfl) ⟨7689608, by rfl⟩ : syracuseStep 10252811 = 15379217) B15379217
theorem B11383517 : Blo 1578487 11383517 := bstep (se 3 (by rfl) ⟨2134409, by rfl⟩ : syracuseStep 11383517 = 4268819) B4268819
theorem B153752525 : Blo 1578487 153752525 := bstep (se 3 (by rfl) ⟨28828598, by rfl⟩ : syracuseStep 153752525 = 57657197) B57657197
theorem B5993747 : Blo 1578487 5993747 := bstep (se 1 (by rfl) ⟨4495310, by rfl⟩ : syracuseStep 5993747 = 8990621) B8990621
theorem B2848019 : Blo 1578487 2848019 := bstep (se 1 (by rfl) ⟨2136014, by rfl⟩ : syracuseStep 2848019 = 4272029) B4272029
theorem B7591259 : Blo 1578487 7591259 := bstep (se 1 (by rfl) ⟨5693444, by rfl⟩ : syracuseStep 7591259 = 11386889) B11386889
theorem B5690951 : Blo 1578487 5690951 := bstep (se 1 (by rfl) ⟨4268213, by rfl⟩ : syracuseStep 5690951 = 8536427) B8536427
theorem B3552839 : Blo 1578487 3552839 := bstep (se 1 (by rfl) ⟨2664629, by rfl⟩ : syracuseStep 3552839 = 5329259) B5329259
theorem B1578607 : Blo 1578487 1578607 := bstep (se 1 (by rfl) ⟨1183955, by rfl⟩ : syracuseStep 1578607 = 2367911) B2367911
theorem B1578663 : Blo 1578487 1578663 := bstep (se 1 (by rfl) ⟨1183997, by rfl⟩ : syracuseStep 1578663 = 2367995) B2367995
theorem B1578747 : Blo 1578487 1578747 := bstep (se 1 (by rfl) ⟨1184060, by rfl⟩ : syracuseStep 1578747 = 2368121) B2368121
theorem B3553019 : Blo 1578487 3553019 := bstep (se 1 (by rfl) ⟨2664764, by rfl⟩ : syracuseStep 3553019 = 5329529) B5329529
theorem B17987345 : Blo 1578487 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B1578783 : Blo 1578487 1578783 := bstep (se 1 (by rfl) ⟨1184087, by rfl⟩ : syracuseStep 1578783 = 2368175) B2368175
theorem B4495151 : Blo 1578487 4495151 := bstep (se 1 (by rfl) ⟨3371363, by rfl⟩ : syracuseStep 4495151 = 6742727) B6742727
theorem B1578815 : Blo 1578487 1578815 := bstep (se 1 (by rfl) ⟨1184111, by rfl⟩ : syracuseStep 1578815 = 2368223) B2368223
theorem B18233225 : Blo 1578487 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B5330825 : Blo 1578487 5330825 := bstep (se 2 (by rfl) ⟨1999059, by rfl⟩ : syracuseStep 5330825 = 3998119) B3998119
theorem B19216349 : Blo 1578487 19216349 := bstep (se 3 (by rfl) ⟨3603065, by rfl⟩ : syracuseStep 19216349 = 7206131) B7206131
theorem B1578991 : Blo 1578487 1578991 := bstep (se 1 (by rfl) ⟨1184243, by rfl⟩ : syracuseStep 1578991 = 2368487) B2368487
theorem B7993403 : Blo 1578487 7993403 := bstep (se 1 (by rfl) ⟨5995052, by rfl⟩ : syracuseStep 7993403 = 11990105) B11990105
theorem B18241631 : Blo 1578487 18241631 := bstep (se 1 (by rfl) ⟨13681223, by rfl⟩ : syracuseStep 18241631 = 27362447) B27362447
theorem B5331041 : Blo 1578487 5331041 := bstep (se 2 (by rfl) ⟨1999140, by rfl⟩ : syracuseStep 5331041 = 3998281) B3998281
theorem B1579163 : Blo 1578487 1579163 := bstep (se 1 (by rfl) ⟨1184372, by rfl⟩ : syracuseStep 1579163 = 2368745) B2368745
theorem B1579199 : Blo 1578487 1579199 := bstep (se 1 (by rfl) ⟨1184399, by rfl⟩ : syracuseStep 1579199 = 2368799) B2368799
theorem B2054335 : Blo 1578487 2054335 := bstep (se 1 (by rfl) ⟨1540751, by rfl⟩ : syracuseStep 2054335 = 3081503) B3081503
theorem B3553577 : Blo 1578487 3553577 := bstep (se 2 (by rfl) ⟨1332591, by rfl⟩ : syracuseStep 3553577 = 2665183) B2665183
theorem B1579311 : Blo 1578487 1579311 := bstep (se 1 (by rfl) ⟨1184483, by rfl⟩ : syracuseStep 1579311 = 2368967) B2368967
theorem B41613749 : Blo 1578487 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B1579547 : Blo 1578487 1579547 := bstep (se 1 (by rfl) ⟨1184660, by rfl⟩ : syracuseStep 1579547 = 2369321) B2369321
theorem B1579551 : Blo 1578487 1579551 := bstep (se 1 (by rfl) ⟨1184663, by rfl⟩ : syracuseStep 1579551 = 2369327) B2369327
theorem B5126809 : Blo 1578487 5126809 := bstep (se 2 (by rfl) ⟨1922553, by rfl⟩ : syracuseStep 5126809 = 3845107) B3845107
theorem B20249297 : Blo 1578487 20249297 := bstep (se 2 (by rfl) ⟨7593486, by rfl⟩ : syracuseStep 20249297 = 15186973) B15186973
theorem B3996499 : Blo 1578487 3996499 := bstep (se 1 (by rfl) ⟨2997374, by rfl⟩ : syracuseStep 3996499 = 5994749) B5994749
theorem B1579867 : Blo 1578487 1579867 := bstep (se 1 (by rfl) ⟨1184900, by rfl⟩ : syracuseStep 1579867 = 2369801) B2369801
theorem B3554153 : Blo 1578487 3554153 := bstep (se 2 (by rfl) ⟨1332807, by rfl⟩ : syracuseStep 3554153 = 2665615) B2665615
theorem B3554207 : Blo 1578487 3554207 := bstep (se 1 (by rfl) ⟨2665655, by rfl⟩ : syracuseStep 3554207 = 5331311) B5331311
theorem B1579935 : Blo 1578487 1579935 := bstep (se 1 (by rfl) ⟨1184951, by rfl⟩ : syracuseStep 1579935 = 2369903) B2369903
theorem B3996641 : Blo 1578487 3996641 := bstep (se 2 (by rfl) ⟨1498740, by rfl⟩ : syracuseStep 3996641 = 2997481) B2997481
theorem B5331959 : Blo 1578487 5331959 := bstep (se 1 (by rfl) ⟨3998969, by rfl⟩ : syracuseStep 5331959 = 7997939) B7997939
theorem B1580079 : Blo 1578487 1580079 := bstep (se 1 (by rfl) ⟨1185059, by rfl⟩ : syracuseStep 1580079 = 2370119) B2370119
theorem B7691321 : Blo 1578487 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B1580103 : Blo 1578487 1580103 := bstep (se 1 (by rfl) ⟨1185077, by rfl⟩ : syracuseStep 1580103 = 2370155) B2370155
theorem B5061761 : Blo 1578487 5061761 := bstep (se 2 (by rfl) ⟨1898160, by rfl⟩ : syracuseStep 5061761 = 3796321) B3796321
theorem B21609629 : Blo 1578487 21609629 := bstep (se 3 (by rfl) ⟨4051805, by rfl⟩ : syracuseStep 21609629 = 8103611) B8103611
theorem B175348921 : Blo 1578487 175348921 := bstep (se 2 (by rfl) ⟨65755845, by rfl⟩ : syracuseStep 175348921 = 131511691) B131511691
theorem B1998047 : Blo 1578487 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B1580255 : Blo 1578487 1580255 := bstep (se 1 (by rfl) ⟨1185191, by rfl⟩ : syracuseStep 1580255 = 2370383) B2370383
theorem B4496735 : Blo 1578487 4496735 := bstep (se 1 (by rfl) ⟨3372551, by rfl⟩ : syracuseStep 4496735 = 6745103) B6745103
theorem B5332391 : Blo 1578487 5332391 := bstep (se 1 (by rfl) ⟨3999293, by rfl⟩ : syracuseStep 5332391 = 7998587) B7998587
theorem B18480595 : Blo 1578487 18480595 := bstep (se 1 (by rfl) ⟨13860446, by rfl⟩ : syracuseStep 18480595 = 27720893) B27720893
theorem B7994861 : Blo 1578487 7994861 := bstep (se 3 (by rfl) ⟨1499036, by rfl⟩ : syracuseStep 7994861 = 2998073) B2998073
theorem B8994311 : Blo 1578487 8994311 := bstep (se 1 (by rfl) ⟨6745733, by rfl⟩ : syracuseStep 8994311 = 13491467) B13491467
theorem B1998427 : Blo 1578487 1998427 := bstep (se 1 (by rfl) ⟨1498820, by rfl⟩ : syracuseStep 1998427 = 2997641) B2997641
theorem B1777243 : Blo 1578487 1777243 := bstep (se 1 (by rfl) ⟨1332932, by rfl⟩ : syracuseStep 1777243 = 2665865) B2665865
theorem B7995023 : Blo 1578487 7995023 := bstep (se 1 (by rfl) ⟨5996267, by rfl⟩ : syracuseStep 7995023 = 11992535) B11992535
theorem B13672145 : Blo 1578487 13672145 := bstep (se 2 (by rfl) ⟨5127054, by rfl⟩ : syracuseStep 13672145 = 10254109) B10254109
theorem B11386601 : Blo 1578487 11386601 := bstep (se 2 (by rfl) ⟨4269975, by rfl⟩ : syracuseStep 11386601 = 8539951) B8539951
theorem B38403881 : Blo 1578487 38403881 := bstep (se 2 (by rfl) ⟨14401455, by rfl⟩ : syracuseStep 38403881 = 28802911) B28802911
theorem B28819259 : Blo 1578487 28819259 := bstep (se 1 (by rfl) ⟨21614444, by rfl⟩ : syracuseStep 28819259 = 43228889) B43228889
theorem B3555143 : Blo 1578487 3555143 := bstep (se 1 (by rfl) ⟨2666357, by rfl⟩ : syracuseStep 3555143 = 5332715) B5332715
theorem B5996375 : Blo 1578487 5996375 := bstep (se 1 (by rfl) ⟨4497281, by rfl⟩ : syracuseStep 5996375 = 8994563) B8994563
theorem B5332823 : Blo 1578487 5332823 := bstep (se 1 (by rfl) ⟨3999617, by rfl⟩ : syracuseStep 5332823 = 7999235) B7999235
theorem B1777531 : Blo 1578487 1777531 := bstep (se 1 (by rfl) ⟨1333148, by rfl⟩ : syracuseStep 1777531 = 2666297) B2666297
theorem B34176917 : Blo 1578487 34176917 := bstep (se 6 (by rfl) ⟨801021, by rfl⟩ : syracuseStep 34176917 = 1602043) B1602043
theorem B12804155 : Blo 1578487 12804155 := bstep (se 1 (by rfl) ⟨9603116, by rfl⟩ : syracuseStep 12804155 = 19206233) B19206233
theorem B1777855 : Blo 1578487 1777855 := bstep (se 1 (by rfl) ⟨1333391, by rfl⟩ : syracuseStep 1777855 = 2666783) B2666783
theorem B2367743 : Blo 1578487 2367743 := bstep (se 1 (by rfl) ⟨1775807, by rfl⟩ : syracuseStep 2367743 = 3551615) B3551615
theorem B6078817 : Blo 1578487 6078817 := bstep (se 2 (by rfl) ⟨2279556, by rfl⟩ : syracuseStep 6078817 = 4559113) B4559113
theorem B3555755 : Blo 1578487 3555755 := bstep (se 1 (by rfl) ⟨2666816, by rfl⟩ : syracuseStep 3555755 = 5333633) B5333633
theorem B3555935 : Blo 1578487 3555935 := bstep (se 1 (by rfl) ⟨2666951, by rfl⟩ : syracuseStep 3555935 = 5333903) B5333903
theorem B24658631 : Blo 1578487 24658631 := bstep (se 1 (by rfl) ⟨18493973, by rfl⟩ : syracuseStep 24658631 = 36987947) B36987947
theorem B7594717 : Blo 1578487 7594717 := bstep (se 3 (by rfl) ⟨1424009, by rfl⟩ : syracuseStep 7594717 = 2848019) B2848019
theorem B7996157 : Blo 1578487 7996157 := bstep (se 3 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 7996157 = 2998559) B2998559
theorem B13501241 : Blo 1578487 13501241 := bstep (se 2 (by rfl) ⟨5062965, by rfl⟩ : syracuseStep 13501241 = 10125931) B10125931
theorem B3793967 : Blo 1578487 3793967 := bstep (se 1 (by rfl) ⟨2845475, by rfl⟩ : syracuseStep 3793967 = 5690951) B5690951
theorem B2368559 : Blo 1578487 2368559 := bstep (se 1 (by rfl) ⟨1776419, by rfl⟩ : syracuseStep 2368559 = 3552839) B3552839
theorem B2368679 : Blo 1578487 2368679 := bstep (se 1 (by rfl) ⟨1776509, by rfl⟩ : syracuseStep 2368679 = 3553019) B3553019
theorem B2999531 : Blo 1578487 2999531 := bstep (se 1 (by rfl) ⟨2249648, by rfl⟩ : syracuseStep 2999531 = 4499297) B4499297
theorem B2369051 : Blo 1578487 2369051 := bstep (se 1 (by rfl) ⟨1776788, by rfl⟩ : syracuseStep 2369051 = 3553577) B3553577
theorem B3999527 : Blo 1578487 3999527 := bstep (se 1 (by rfl) ⟨2999645, by rfl⟩ : syracuseStep 3999527 = 5999291) B5999291
theorem B2369435 : Blo 1578487 2369435 := bstep (se 1 (by rfl) ⟨1777076, by rfl⟩ : syracuseStep 2369435 = 3554153) B3554153
theorem B2369471 : Blo 1578487 2369471 := bstep (se 1 (by rfl) ⟨1777103, by rfl⟩ : syracuseStep 2369471 = 3554207) B3554207
theorem B2664427 : Blo 1578487 2664427 := bstep (se 1 (by rfl) ⟨1998320, by rfl⟩ : syracuseStep 2664427 = 3996641) B3996641
theorem B6744161 : Blo 1578487 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B2664569 : Blo 1578487 2664569 := bstep (se 2 (by rfl) ⟨999213, by rfl⟩ : syracuseStep 2664569 = 1998427) B1998427
theorem B2369657 : Blo 1578487 2369657 := bstep (se 2 (by rfl) ⟨888621, by rfl⟩ : syracuseStep 2369657 = 1777243) B1777243
theorem B5851379 : Blo 1578487 5851379 := bstep (se 1 (by rfl) ⟨4388534, by rfl⟩ : syracuseStep 5851379 = 8777069) B8777069
theorem B6490409 : Blo 1578487 6490409 := bstep (se 2 (by rfl) ⟨2433903, by rfl⟩ : syracuseStep 6490409 = 4867807) B4867807
theorem B8997227 : Blo 1578487 8997227 := bstep (se 1 (by rfl) ⟨6747920, by rfl⟩ : syracuseStep 8997227 = 13495841) B13495841
theorem B2370041 : Blo 1578487 2370041 := bstep (se 2 (by rfl) ⟨888765, by rfl⟩ : syracuseStep 2370041 = 1777531) B1777531
theorem B25602587 : Blo 1578487 25602587 := bstep (se 1 (by rfl) ⟨19201940, by rfl⟩ : syracuseStep 25602587 = 38403881) B38403881
theorem B19212839 : Blo 1578487 19212839 := bstep (se 1 (by rfl) ⟨14409629, by rfl⟩ : syracuseStep 19212839 = 28819259) B28819259
theorem B2370095 : Blo 1578487 2370095 := bstep (se 1 (by rfl) ⟨1777571, by rfl⟩ : syracuseStep 2370095 = 3555143) B3555143
theorem B22784611 : Blo 1578487 22784611 := bstep (se 1 (by rfl) ⟨17088458, by rfl⟩ : syracuseStep 22784611 = 34176917) B34176917
theorem B8997479 : Blo 1578487 8997479 := bstep (se 1 (by rfl) ⟨6748109, by rfl⟩ : syracuseStep 8997479 = 13496219) B13496219
theorem B2739113 : Blo 1578487 2739113 := bstep (se 2 (by rfl) ⟨1027167, by rfl⟩ : syracuseStep 2739113 = 2054335) B2054335
theorem B2370527 : Blo 1578487 2370527 := bstep (se 1 (by rfl) ⟨1777895, by rfl⟩ : syracuseStep 2370527 = 3555791) B3555791
theorem B6835207 : Blo 1578487 6835207 := bstep (se 1 (by rfl) ⟨5126405, by rfl⟩ : syracuseStep 6835207 = 10252811) B10252811
theorem B7589011 : Blo 1578487 7589011 := bstep (se 1 (by rfl) ⟨5691758, by rfl⟩ : syracuseStep 7589011 = 11383517) B11383517
theorem B5328125 : Blo 1578487 5328125 := bstep (se 3 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 5328125 = 1998047) B1998047
theorem B102501683 : Blo 1578487 102501683 := bstep (se 1 (by rfl) ⟨76876262, by rfl⟩ : syracuseStep 102501683 = 153752525) B153752525
theorem B6835745 : Blo 1578487 6835745 := bstep (se 2 (by rfl) ⟨2563404, by rfl⟩ : syracuseStep 6835745 = 5126809) B5126809
theorem B61574849 : Blo 1578487 61574849 := bstep (se 2 (by rfl) ⟨23090568, by rfl⟩ : syracuseStep 61574849 = 46181137) B46181137
theorem B5328665 : Blo 1578487 5328665 := bstep (se 2 (by rfl) ⟨1998249, by rfl⟩ : syracuseStep 5328665 = 3996499) B3996499
theorem B28487485 : Blo 1578487 28487485 := bstep (se 3 (by rfl) ⟨5341403, by rfl⟩ : syracuseStep 28487485 = 10682807) B10682807
theorem B6746075 : Blo 1578487 6746075 := bstep (se 1 (by rfl) ⟨5059556, by rfl⟩ : syracuseStep 6746075 = 10119113) B10119113
theorem B5328935 : Blo 1578487 5328935 := bstep (se 1 (by rfl) ⟨3996701, by rfl⟩ : syracuseStep 5328935 = 7993403) B7993403
theorem B12161087 : Blo 1578487 12161087 := bstep (se 1 (by rfl) ⟨9120815, by rfl⟩ : syracuseStep 12161087 = 18241631) B18241631
theorem B2666729 : Blo 1578487 2666729 := bstep (se 2 (by rfl) ⟨1000023, by rfl⟩ : syracuseStep 2666729 = 2000047) B2000047
theorem B27742499 : Blo 1578487 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B3797351 : Blo 1578487 3797351 := bstep (se 1 (by rfl) ⟨2848013, by rfl⟩ : syracuseStep 3797351 = 5696027) B5696027
theorem B3551687 : Blo 1578487 3551687 := bstep (se 1 (by rfl) ⟨2663765, by rfl⟩ : syracuseStep 3551687 = 5327531) B5327531
theorem B14406419 : Blo 1578487 14406419 := bstep (se 1 (by rfl) ⟨10804814, by rfl⟩ : syracuseStep 14406419 = 21609629) B21609629
theorem B3552047 : Blo 1578487 3552047 := bstep (se 1 (by rfl) ⟨2664035, by rfl⟩ : syracuseStep 3552047 = 5328071) B5328071
theorem B3552137 : Blo 1578487 3552137 := bstep (se 2 (by rfl) ⟨1332051, by rfl⟩ : syracuseStep 3552137 = 2664103) B2664103
theorem B5329907 : Blo 1578487 5329907 := bstep (se 1 (by rfl) ⟨3997430, by rfl⟩ : syracuseStep 5329907 = 7994861) B7994861
theorem B5330015 : Blo 1578487 5330015 := bstep (se 1 (by rfl) ⟨3997511, by rfl⟩ : syracuseStep 5330015 = 7995023) B7995023
theorem B9114763 : Blo 1578487 9114763 := bstep (se 1 (by rfl) ⟨6836072, by rfl⟩ : syracuseStep 9114763 = 13672145) B13672145
theorem B7591067 : Blo 1578487 7591067 := bstep (se 1 (by rfl) ⟨5693300, by rfl⟩ : syracuseStep 7591067 = 11386601) B11386601
theorem B6747563 : Blo 1578487 6747563 := bstep (se 1 (by rfl) ⟨5060672, by rfl⟩ : syracuseStep 6747563 = 10121345) B10121345
theorem B5330447 : Blo 1578487 5330447 := bstep (se 1 (by rfl) ⟨3997835, by rfl⟩ : syracuseStep 5330447 = 7995671) B7995671
theorem B48608855 : Blo 1578487 48608855 := bstep (se 1 (by rfl) ⟨36456641, by rfl⟩ : syracuseStep 48608855 = 72913283) B72913283
theorem B1578587 : Blo 1578487 1578587 := bstep (se 1 (by rfl) ⟨1183940, by rfl⟩ : syracuseStep 1578587 = 2367881) B2367881
theorem B3552911 : Blo 1578487 3552911 := bstep (se 1 (by rfl) ⟨2664683, by rfl⟩ : syracuseStep 3552911 = 5329367) B5329367
theorem B1578651 : Blo 1578487 1578651 := bstep (se 1 (by rfl) ⟨1183988, by rfl⟩ : syracuseStep 1578651 = 2367977) B2367977
theorem B3553001 : Blo 1578487 3553001 := bstep (se 2 (by rfl) ⟨1332375, by rfl⟩ : syracuseStep 3553001 = 2664751) B2664751
theorem B1578735 : Blo 1578487 1578735 := bstep (se 1 (by rfl) ⟨1184051, by rfl⟩ : syracuseStep 1578735 = 2368103) B2368103
theorem B1578823 : Blo 1578487 1578823 := bstep (se 1 (by rfl) ⟨1184117, by rfl⟩ : syracuseStep 1578823 = 2368235) B2368235
theorem B1578843 : Blo 1578487 1578843 := bstep (se 1 (by rfl) ⟨1184132, by rfl⟩ : syracuseStep 1578843 = 2368265) B2368265
theorem B1578911 : Blo 1578487 1578911 := bstep (se 1 (by rfl) ⟨1184183, by rfl⟩ : syracuseStep 1578911 = 2368367) B2368367
theorem B1579079 : Blo 1578487 1579079 := bstep (se 1 (by rfl) ⟨1184309, by rfl⟩ : syracuseStep 1579079 = 2368619) B2368619
theorem B3995831 : Blo 1578487 3995831 := bstep (se 1 (by rfl) ⟨2996873, by rfl⟩ : syracuseStep 3995831 = 5993747) B5993747
theorem B1579239 : Blo 1578487 1579239 := bstep (se 1 (by rfl) ⟨1184429, by rfl⟩ : syracuseStep 1579239 = 2368859) B2368859
theorem B5060839 : Blo 1578487 5060839 := bstep (se 1 (by rfl) ⟨3795629, by rfl⟩ : syracuseStep 5060839 = 7591259) B7591259
theorem B5331257 : Blo 1578487 5331257 := bstep (se 2 (by rfl) ⟨1999221, by rfl⟩ : syracuseStep 5331257 = 3998443) B3998443
theorem B4053305 : Blo 1578487 4053305 := bstep (se 2 (by rfl) ⟨1519989, by rfl⟩ : syracuseStep 4053305 = 3039979) B3039979
theorem B1579423 : Blo 1578487 1579423 := bstep (se 1 (by rfl) ⟨1184567, by rfl⟩ : syracuseStep 1579423 = 2369135) B2369135
theorem B1579471 : Blo 1578487 1579471 := bstep (se 1 (by rfl) ⟨1184603, by rfl⟩ : syracuseStep 1579471 = 2369207) B2369207
theorem B1579495 : Blo 1578487 1579495 := bstep (se 1 (by rfl) ⟨1184621, by rfl⟩ : syracuseStep 1579495 = 2369243) B2369243
theorem B11991563 : Blo 1578487 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B2996767 : Blo 1578487 2996767 := bstep (se 1 (by rfl) ⟨2247575, by rfl⟩ : syracuseStep 2996767 = 4495151) B4495151
theorem B5331527 : Blo 1578487 5331527 := bstep (se 1 (by rfl) ⟨3998645, by rfl⟩ : syracuseStep 5331527 = 7997291) B7997291
theorem B12155483 : Blo 1578487 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B3553883 : Blo 1578487 3553883 := bstep (se 1 (by rfl) ⟨2665412, by rfl⟩ : syracuseStep 3553883 = 5330825) B5330825
theorem B1579611 : Blo 1578487 1579611 := bstep (se 1 (by rfl) ⟨1184708, by rfl⟩ : syracuseStep 1579611 = 2369417) B2369417
theorem B12810899 : Blo 1578487 12810899 := bstep (se 1 (by rfl) ⟨9608174, by rfl⟩ : syracuseStep 12810899 = 19216349) B19216349
theorem B1579679 : Blo 1578487 1579679 := bstep (se 1 (by rfl) ⟨1184759, by rfl⟩ : syracuseStep 1579679 = 2369519) B2369519
theorem B3554027 : Blo 1578487 3554027 := bstep (se 1 (by rfl) ⟨2665520, by rfl⟩ : syracuseStep 3554027 = 5331041) B5331041
theorem B10263307 : Blo 1578487 10263307 := bstep (se 1 (by rfl) ⟨7697480, by rfl⟩ : syracuseStep 10263307 = 15394961) B15394961
theorem B1579847 : Blo 1578487 1579847 := bstep (se 1 (by rfl) ⟨1184885, by rfl⟩ : syracuseStep 1579847 = 2369771) B2369771
theorem B1579887 : Blo 1578487 1579887 := bstep (se 1 (by rfl) ⟨1184915, by rfl⟩ : syracuseStep 1579887 = 2369831) B2369831
theorem B233798561 : Blo 1578487 233798561 := bstep (se 2 (by rfl) ⟨87674460, by rfl⟩ : syracuseStep 233798561 = 175348921) B175348921
theorem B1579943 : Blo 1578487 1579943 := bstep (se 1 (by rfl) ⟨1184957, by rfl⟩ : syracuseStep 1579943 = 2369915) B2369915
theorem B1580123 : Blo 1578487 1580123 := bstep (se 1 (by rfl) ⟨1185092, by rfl⟩ : syracuseStep 1580123 = 2370185) B2370185
theorem B5479559 : Blo 1578487 5479559 := bstep (se 1 (by rfl) ⟨4109669, by rfl⟩ : syracuseStep 5479559 = 8219339) B8219339
theorem B13499531 : Blo 1578487 13499531 := bstep (se 1 (by rfl) ⟨10124648, by rfl⟩ : syracuseStep 13499531 = 20249297) B20249297
theorem B1776847 : Blo 1578487 1776847 := bstep (se 1 (by rfl) ⟨1332635, by rfl⟩ : syracuseStep 1776847 = 2665271) B2665271
theorem B1580239 : Blo 1578487 1580239 := bstep (se 1 (by rfl) ⟨1185179, by rfl⟩ : syracuseStep 1580239 = 2370359) B2370359
theorem B1580263 : Blo 1578487 1580263 := bstep (se 1 (by rfl) ⟨1185197, by rfl⟩ : syracuseStep 1580263 = 2370395) B2370395
theorem B24640793 : Blo 1578487 24640793 := bstep (se 2 (by rfl) ⟨9240297, by rfl⟩ : syracuseStep 24640793 = 18480595) B18480595
theorem B1580359 : Blo 1578487 1580359 := bstep (se 1 (by rfl) ⟨1185269, by rfl⟩ : syracuseStep 1580359 = 2370539) B2370539
theorem B3554639 : Blo 1578487 3554639 := bstep (se 1 (by rfl) ⟨2665979, by rfl⟩ : syracuseStep 3554639 = 5331959) B5331959
theorem B5127547 : Blo 1578487 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B3554729 : Blo 1578487 3554729 := bstep (se 2 (by rfl) ⟨1333023, by rfl⟩ : syracuseStep 3554729 = 2666047) B2666047
theorem B3374507 : Blo 1578487 3374507 := bstep (se 1 (by rfl) ⟨2530880, by rfl⟩ : syracuseStep 3374507 = 5061761) B5061761
theorem B2997823 : Blo 1578487 2997823 := bstep (se 1 (by rfl) ⟨2248367, by rfl⟩ : syracuseStep 2997823 = 4496735) B4496735
theorem B3554927 : Blo 1578487 3554927 := bstep (se 1 (by rfl) ⟨2666195, by rfl⟩ : syracuseStep 3554927 = 5332391) B5332391
theorem B5996207 : Blo 1578487 5996207 := bstep (se 1 (by rfl) ⟨4497155, by rfl⟩ : syracuseStep 5996207 = 8994311) B8994311
theorem B64872251 : Blo 1578487 64872251 := bstep (se 1 (by rfl) ⟨48654188, by rfl⟩ : syracuseStep 64872251 = 97308377) B97308377
theorem B3792737 : Blo 1578487 3792737 := bstep (se 2 (by rfl) ⟨1422276, by rfl⟩ : syracuseStep 3792737 = 2844553) B2844553
theorem B3997583 : Blo 1578487 3997583 := bstep (se 1 (by rfl) ⟨2998187, by rfl⟩ : syracuseStep 3997583 = 5996375) B5996375
theorem B3555215 : Blo 1578487 3555215 := bstep (se 1 (by rfl) ⟨2666411, by rfl⟩ : syracuseStep 3555215 = 5332823) B5332823
theorem B8536103 : Blo 1578487 8536103 := bstep (se 1 (by rfl) ⟨6402077, by rfl⟩ : syracuseStep 8536103 = 12804155) B12804155
theorem B1777819 : Blo 1578487 1777819 := bstep (se 1 (by rfl) ⟨1333364, by rfl⟩ : syracuseStep 1777819 = 2666729) B2666729
theorem B2531567 : Blo 1578487 2531567 := bstep (se 1 (by rfl) ⟨1898675, by rfl⟩ : syracuseStep 2531567 = 3797351) B3797351
theorem B2367791 : Blo 1578487 2367791 := bstep (se 1 (by rfl) ⟨1775843, by rfl⟩ : syracuseStep 2367791 = 3551687) B3551687
theorem B2368031 : Blo 1578487 2368031 := bstep (se 1 (by rfl) ⟨1776023, by rfl⟩ : syracuseStep 2368031 = 3552047) B3552047
theorem B2368091 : Blo 1578487 2368091 := bstep (se 1 (by rfl) ⟨1776068, by rfl⟩ : syracuseStep 2368091 = 3552137) B3552137
theorem B4498375 : Blo 1578487 4498375 := bstep (se 1 (by rfl) ⟨3373781, by rfl⟩ : syracuseStep 4498375 = 6747563) B6747563
theorem B10126289 : Blo 1578487 10126289 := bstep (se 2 (by rfl) ⟨3797358, by rfl⟩ : syracuseStep 10126289 = 7594717) B7594717
theorem B2368607 : Blo 1578487 2368607 := bstep (se 1 (by rfl) ⟨1776455, by rfl⟩ : syracuseStep 2368607 = 3552911) B3552911
theorem B2368667 : Blo 1578487 2368667 := bstep (se 1 (by rfl) ⟨1776500, by rfl⟩ : syracuseStep 2368667 = 3553001) B3553001
theorem B2663887 : Blo 1578487 2663887 := bstep (se 1 (by rfl) ⟨1997915, by rfl⟩ : syracuseStep 2663887 = 3995831) B3995831
theorem B10118681 : Blo 1578487 10118681 := bstep (se 2 (by rfl) ⟨3794505, by rfl⟩ : syracuseStep 10118681 = 7589011) B7589011
theorem B5998151 : Blo 1578487 5998151 := bstep (se 1 (by rfl) ⟨4498613, by rfl⟩ : syracuseStep 5998151 = 8997227) B8997227
theorem B2369129 : Blo 1578487 2369129 := bstep (se 2 (by rfl) ⟨888423, by rfl⟩ : syracuseStep 2369129 = 1776847) B1776847
theorem B8103655 : Blo 1578487 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B2369255 : Blo 1578487 2369255 := bstep (se 1 (by rfl) ⟨1776941, by rfl⟩ : syracuseStep 2369255 = 3553883) B3553883
theorem B5998319 : Blo 1578487 5998319 := bstep (se 1 (by rfl) ⟨4498739, by rfl⟩ : syracuseStep 5998319 = 8997479) B8997479
theorem B2369351 : Blo 1578487 2369351 := bstep (se 1 (by rfl) ⟨1777013, by rfl⟩ : syracuseStep 2369351 = 3554027) B3554027
theorem B16427195 : Blo 1578487 16427195 := bstep (se 1 (by rfl) ⟨12320396, by rfl⟩ : syracuseStep 16427195 = 24640793) B24640793
theorem B2369759 : Blo 1578487 2369759 := bstep (se 1 (by rfl) ⟨1777319, by rfl⟩ : syracuseStep 2369759 = 3554639) B3554639
theorem B2369819 : Blo 1578487 2369819 := bstep (se 1 (by rfl) ⟨1777364, by rfl⟩ : syracuseStep 2369819 = 3554729) B3554729
theorem B4557163 : Blo 1578487 4557163 := bstep (se 1 (by rfl) ⟨3417872, by rfl⟩ : syracuseStep 4557163 = 6835745) B6835745
theorem B2369951 : Blo 1578487 2369951 := bstep (se 1 (by rfl) ⟨1777463, by rfl⟩ : syracuseStep 2369951 = 3554927) B3554927
theorem B43248167 : Blo 1578487 43248167 := bstep (se 1 (by rfl) ⟨32436125, by rfl⟩ : syracuseStep 43248167 = 64872251) B64872251
theorem B2665055 : Blo 1578487 2665055 := bstep (se 1 (by rfl) ⟨1998791, by rfl⟩ : syracuseStep 2665055 = 3997583) B3997583
theorem B2370143 : Blo 1578487 2370143 := bstep (se 1 (by rfl) ⟨1777607, by rfl⟩ : syracuseStep 2370143 = 3555215) B3555215
theorem B2370473 : Blo 1578487 2370473 := bstep (se 2 (by rfl) ⟨888927, by rfl⟩ : syracuseStep 2370473 = 1777855) B1777855
theorem B17984429 : Blo 1578487 17984429 := bstep (se 3 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 17984429 = 6744161) B6744161
theorem B2370503 : Blo 1578487 2370503 := bstep (se 1 (by rfl) ⟨1777877, by rfl⟩ : syracuseStep 2370503 = 3555755) B3555755
theorem B2370623 : Blo 1578487 2370623 := bstep (se 1 (by rfl) ⟨1777967, by rfl⟩ : syracuseStep 2370623 = 3555935) B3555935
theorem B8105089 : Blo 1578487 8105089 := bstep (se 2 (by rfl) ⟨3039408, by rfl⟩ : syracuseStep 8105089 = 6078817) B6078817
theorem B9604279 : Blo 1578487 9604279 := bstep (se 1 (by rfl) ⟨7203209, by rfl⟩ : syracuseStep 9604279 = 14406419) B14406419
theorem B7998749 : Blo 1578487 7998749 := bstep (se 3 (by rfl) ⟨1499765, by rfl⟩ : syracuseStep 7998749 = 2999531) B2999531
theorem B30379481 : Blo 1578487 30379481 := bstep (se 2 (by rfl) ⟨11392305, by rfl⟩ : syracuseStep 30379481 = 22784611) B22784611
theorem B13684409 : Blo 1578487 13684409 := bstep (se 2 (by rfl) ⟨5131653, by rfl⟩ : syracuseStep 13684409 = 10263307) B10263307
theorem B8998685 : Blo 1578487 8998685 := bstep (se 3 (by rfl) ⟨1687253, by rfl⟩ : syracuseStep 8998685 = 3374507) B3374507
theorem B2666351 : Blo 1578487 2666351 := bstep (se 1 (by rfl) ⟨1999763, by rfl⟩ : syracuseStep 2666351 = 3999527) B3999527
theorem B9113609 : Blo 1578487 9113609 := bstep (se 2 (by rfl) ⟨3417603, by rfl⟩ : syracuseStep 9113609 = 6835207) B6835207
theorem B12153017 : Blo 1578487 12153017 := bstep (se 2 (by rfl) ⟨4557381, by rfl⟩ : syracuseStep 12153017 = 9114763) B9114763
theorem B17068391 : Blo 1578487 17068391 := bstep (se 1 (by rfl) ⟨12801293, by rfl⟩ : syracuseStep 17068391 = 25602587) B25602587
theorem B12808559 : Blo 1578487 12808559 := bstep (se 1 (by rfl) ⟨9606419, by rfl⟩ : syracuseStep 12808559 = 19212839) B19212839
theorem B8540599 : Blo 1578487 8540599 := bstep (se 1 (by rfl) ⟨6405449, by rfl⟩ : syracuseStep 8540599 = 12810899) B12810899
theorem B6836729 : Blo 1578487 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B155865707 : Blo 1578487 155865707 := bstep (se 1 (by rfl) ⟨116899280, by rfl⟩ : syracuseStep 155865707 = 233798561) B233798561
theorem B8999687 : Blo 1578487 8999687 := bstep (se 1 (by rfl) ⟨6749765, by rfl⟩ : syracuseStep 8999687 = 13499531) B13499531
theorem B3552083 : Blo 1578487 3552083 := bstep (se 1 (by rfl) ⟨2664062, by rfl⟩ : syracuseStep 3552083 = 5328125) B5328125
theorem B68334455 : Blo 1578487 68334455 := bstep (se 1 (by rfl) ⟨51250841, by rfl⟩ : syracuseStep 68334455 = 102501683) B102501683
theorem B37983313 : Blo 1578487 37983313 := bstep (se 2 (by rfl) ⟨14243742, by rfl⟩ : syracuseStep 37983313 = 28487485) B28487485
theorem B3552443 : Blo 1578487 3552443 := bstep (se 1 (by rfl) ⟨2664332, by rfl⟩ : syracuseStep 3552443 = 5328665) B5328665
theorem B2528491 : Blo 1578487 2528491 := bstep (se 1 (by rfl) ⟨1896368, by rfl⟩ : syracuseStep 2528491 = 3792737) B3792737
theorem B3552569 : Blo 1578487 3552569 := bstep (se 2 (by rfl) ⟨1332213, by rfl⟩ : syracuseStep 3552569 = 2664427) B2664427
theorem B3552623 : Blo 1578487 3552623 := bstep (se 1 (by rfl) ⟨2664467, by rfl⟩ : syracuseStep 3552623 = 5328935) B5328935
theorem B8107391 : Blo 1578487 8107391 := bstep (se 1 (by rfl) ⟨6080543, by rfl⟩ : syracuseStep 8107391 = 12161087) B12161087
theorem B1578495 : Blo 1578487 1578495 := bstep (se 1 (by rfl) ⟨1183871, by rfl⟩ : syracuseStep 1578495 = 2367743) B2367743
theorem B18494999 : Blo 1578487 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B6747785 : Blo 1578487 6747785 := bstep (se 2 (by rfl) ⟨2530419, by rfl⟩ : syracuseStep 6747785 = 5060839) B5060839
theorem B16439087 : Blo 1578487 16439087 := bstep (se 1 (by rfl) ⟨12329315, by rfl⟩ : syracuseStep 16439087 = 24658631) B24658631
theorem B5330771 : Blo 1578487 5330771 := bstep (se 1 (by rfl) ⟨3998078, by rfl⟩ : syracuseStep 5330771 = 7996157) B7996157
theorem B9000827 : Blo 1578487 9000827 := bstep (se 1 (by rfl) ⟨6750620, by rfl⟩ : syracuseStep 9000827 = 13501241) B13501241
theorem B15603677 : Blo 1578487 15603677 := bstep (se 3 (by rfl) ⟨2925689, by rfl⟩ : syracuseStep 15603677 = 5851379) B5851379
theorem B3553271 : Blo 1578487 3553271 := bstep (se 1 (by rfl) ⟨2664953, by rfl⟩ : syracuseStep 3553271 = 5329907) B5329907
theorem B2529311 : Blo 1578487 2529311 := bstep (se 1 (by rfl) ⟨1896983, by rfl⟩ : syracuseStep 2529311 = 3793967) B3793967
theorem B1579039 : Blo 1578487 1579039 := bstep (se 1 (by rfl) ⟨1184279, by rfl⟩ : syracuseStep 1579039 = 2368559) B2368559
theorem B3995689 : Blo 1578487 3995689 := bstep (se 2 (by rfl) ⟨1498383, by rfl⟩ : syracuseStep 3995689 = 2996767) B2996767
theorem B3553343 : Blo 1578487 3553343 := bstep (se 1 (by rfl) ⟨2665007, by rfl⟩ : syracuseStep 3553343 = 5330015) B5330015
theorem B5060711 : Blo 1578487 5060711 := bstep (se 1 (by rfl) ⟨3795533, by rfl⟩ : syracuseStep 5060711 = 7591067) B7591067
theorem B17307757 : Blo 1578487 17307757 := bstep (se 3 (by rfl) ⟨3245204, by rfl⟩ : syracuseStep 17307757 = 6490409) B6490409
theorem B1579119 : Blo 1578487 1579119 := bstep (se 1 (by rfl) ⟨1184339, by rfl⟩ : syracuseStep 1579119 = 2368679) B2368679
theorem B3553631 : Blo 1578487 3553631 := bstep (se 1 (by rfl) ⟨2665223, by rfl⟩ : syracuseStep 3553631 = 5330447) B5330447
theorem B1579367 : Blo 1578487 1579367 := bstep (se 1 (by rfl) ⟨1184525, by rfl⟩ : syracuseStep 1579367 = 2369051) B2369051
theorem B32405903 : Blo 1578487 32405903 := bstep (se 1 (by rfl) ⟨24304427, by rfl⟩ : syracuseStep 32405903 = 48608855) B48608855
theorem B1579623 : Blo 1578487 1579623 := bstep (se 1 (by rfl) ⟨1184717, by rfl⟩ : syracuseStep 1579623 = 2369435) B2369435
theorem B1579647 : Blo 1578487 1579647 := bstep (se 1 (by rfl) ⟨1184735, by rfl⟩ : syracuseStep 1579647 = 2369471) B2369471
theorem B1776379 : Blo 1578487 1776379 := bstep (se 1 (by rfl) ⟨1332284, by rfl⟩ : syracuseStep 1776379 = 2664569) B2664569
theorem B1579771 : Blo 1578487 1579771 := bstep (se 1 (by rfl) ⟨1184828, by rfl⟩ : syracuseStep 1579771 = 2369657) B2369657
theorem B3554171 : Blo 1578487 3554171 := bstep (se 1 (by rfl) ⟨2665628, by rfl⟩ : syracuseStep 3554171 = 5331257) B5331257
theorem B2702203 : Blo 1578487 2702203 := bstep (se 1 (by rfl) ⟨2026652, by rfl⟩ : syracuseStep 2702203 = 4053305) B4053305
theorem B1580027 : Blo 1578487 1580027 := bstep (se 1 (by rfl) ⟨1185020, by rfl⟩ : syracuseStep 1580027 = 2370041) B2370041
theorem B7994375 : Blo 1578487 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B1580063 : Blo 1578487 1580063 := bstep (se 1 (by rfl) ⟨1185047, by rfl⟩ : syracuseStep 1580063 = 2370095) B2370095
theorem B3554351 : Blo 1578487 3554351 := bstep (se 1 (by rfl) ⟨2665763, by rfl⟩ : syracuseStep 3554351 = 5331527) B5331527
theorem B1826075 : Blo 1578487 1826075 := bstep (se 1 (by rfl) ⟨1369556, by rfl⟩ : syracuseStep 1826075 = 2739113) B2739113
theorem B1580351 : Blo 1578487 1580351 := bstep (se 1 (by rfl) ⟨1185263, by rfl⟩ : syracuseStep 1580351 = 2370527) B2370527
theorem B3997097 : Blo 1578487 3997097 := bstep (se 2 (by rfl) ⟨1498911, by rfl⟩ : syracuseStep 3997097 = 2997823) B2997823
theorem B3653039 : Blo 1578487 3653039 := bstep (se 1 (by rfl) ⟨2739779, by rfl⟩ : syracuseStep 3653039 = 5479559) B5479559
theorem B3997471 : Blo 1578487 3997471 := bstep (se 1 (by rfl) ⟨2998103, by rfl⟩ : syracuseStep 3997471 = 5996207) B5996207
theorem B41049899 : Blo 1578487 41049899 := bstep (se 1 (by rfl) ⟨30787424, by rfl⟩ : syracuseStep 41049899 = 61574849) B61574849
theorem B4497383 : Blo 1578487 4497383 := bstep (se 1 (by rfl) ⟨3373037, by rfl⟩ : syracuseStep 4497383 = 6746075) B6746075
theorem B23077009 : Blo 1578487 23077009 := bstep (se 2 (by rfl) ⟨8653878, by rfl⟩ : syracuseStep 23077009 = 17307757) B17307757
theorem B1687711 : Blo 1578487 1687711 := bstep (se 1 (by rfl) ⟨1265783, by rfl⟩ : syracuseStep 1687711 = 2531567) B2531567
theorem B11378927 : Blo 1578487 11378927 := bstep (se 1 (by rfl) ⟨8534195, by rfl⟩ : syracuseStep 11378927 = 17068391) B17068391
theorem B32408045 : Blo 1578487 32408045 := bstep (se 3 (by rfl) ⟨6076508, by rfl⟩ : syracuseStep 32408045 = 12153017) B12153017
theorem B2368055 : Blo 1578487 2368055 := bstep (se 1 (by rfl) ⟨1776041, by rfl⟩ : syracuseStep 2368055 = 3552083) B3552083
theorem B11387465 : Blo 1578487 11387465 := bstep (se 2 (by rfl) ⟨4270299, by rfl⟩ : syracuseStep 11387465 = 8540599) B8540599
theorem B45556303 : Blo 1578487 45556303 := bstep (se 1 (by rfl) ⟨34167227, by rfl⟩ : syracuseStep 45556303 = 68334455) B68334455
theorem B6750859 : Blo 1578487 6750859 := bstep (se 1 (by rfl) ⟨5063144, by rfl⟩ : syracuseStep 6750859 = 10126289) B10126289
theorem B2368295 : Blo 1578487 2368295 := bstep (se 1 (by rfl) ⟨1776221, by rfl⟩ : syracuseStep 2368295 = 3552443) B3552443
theorem B2368379 : Blo 1578487 2368379 := bstep (se 1 (by rfl) ⟨1776284, by rfl⟩ : syracuseStep 2368379 = 3552569) B3552569
theorem B2368415 : Blo 1578487 2368415 := bstep (se 1 (by rfl) ⟨1776311, by rfl⟩ : syracuseStep 2368415 = 3552623) B3552623
theorem B2368505 : Blo 1578487 2368505 := bstep (se 2 (by rfl) ⟨888189, by rfl⟩ : syracuseStep 2368505 = 1776379) B1776379
theorem B12329999 : Blo 1578487 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B3998767 : Blo 1578487 3998767 := bstep (se 1 (by rfl) ⟨2999075, by rfl⟩ : syracuseStep 3998767 = 5998151) B5998151
theorem B4498523 : Blo 1578487 4498523 := bstep (se 1 (by rfl) ⟨3373892, by rfl⟩ : syracuseStep 4498523 = 6747785) B6747785
theorem B3998879 : Blo 1578487 3998879 := bstep (se 1 (by rfl) ⟨2999159, by rfl⟩ : syracuseStep 3998879 = 5998319) B5998319
theorem B5997833 : Blo 1578487 5997833 := bstep (se 2 (by rfl) ⟨2249187, by rfl⟩ : syracuseStep 5997833 = 4498375) B4498375
theorem B2368847 : Blo 1578487 2368847 := bstep (se 1 (by rfl) ⟨1776635, by rfl⟩ : syracuseStep 2368847 = 3553271) B3553271
theorem B2368895 : Blo 1578487 2368895 := bstep (se 1 (by rfl) ⟨1776671, by rfl⟩ : syracuseStep 2368895 = 3553343) B3553343
theorem B50644417 : Blo 1578487 50644417 := bstep (se 2 (by rfl) ⟨18991656, by rfl⟩ : syracuseStep 50644417 = 37983313) B37983313
theorem B10806785 : Blo 1578487 10806785 := bstep (se 2 (by rfl) ⟨4052544, by rfl⟩ : syracuseStep 10806785 = 8105089) B8105089
theorem B2369087 : Blo 1578487 2369087 := bstep (se 1 (by rfl) ⟨1776815, by rfl⟩ : syracuseStep 2369087 = 3553631) B3553631
theorem B12805705 : Blo 1578487 12805705 := bstep (se 2 (by rfl) ⟨4802139, by rfl⟩ : syracuseStep 12805705 = 9604279) B9604279
theorem B21603935 : Blo 1578487 21603935 := bstep (se 1 (by rfl) ⟨16202951, by rfl⟩ : syracuseStep 21603935 = 32405903) B32405903
theorem B2369447 : Blo 1578487 2369447 := bstep (se 1 (by rfl) ⟨1777085, by rfl⟩ : syracuseStep 2369447 = 3554171) B3554171
theorem B2369567 : Blo 1578487 2369567 := bstep (se 1 (by rfl) ⟨1777175, by rfl⟩ : syracuseStep 2369567 = 3554351) B3554351
theorem B2664731 : Blo 1578487 2664731 := bstep (se 1 (by rfl) ⟨1998548, by rfl⟩ : syracuseStep 2664731 = 3997097) B3997097
theorem B2435359 : Blo 1578487 2435359 := bstep (se 1 (by rfl) ⟨1826519, by rfl⟩ : syracuseStep 2435359 = 3653039) B3653039
theorem B20252987 : Blo 1578487 20252987 := bstep (se 1 (by rfl) ⟨15189740, by rfl⟩ : syracuseStep 20252987 = 30379481) B30379481
theorem B5999123 : Blo 1578487 5999123 := bstep (se 1 (by rfl) ⟨4499342, by rfl⟩ : syracuseStep 5999123 = 8998685) B8998685
theorem B5327585 : Blo 1578487 5327585 := bstep (se 2 (by rfl) ⟨1997844, by rfl⟩ : syracuseStep 5327585 = 3995689) B3995689
theorem B6744829 : Blo 1578487 6744829 := bstep (se 3 (by rfl) ⟨1264655, by rfl⟩ : syracuseStep 6744829 = 2529311) B2529311
theorem B2370425 : Blo 1578487 2370425 := bstep (se 2 (by rfl) ⟨888909, by rfl⟩ : syracuseStep 2370425 = 1777819) B1777819
theorem B8539039 : Blo 1578487 8539039 := bstep (se 1 (by rfl) ⟨6404279, by rfl⟩ : syracuseStep 8539039 = 12808559) B12808559
theorem B103910471 : Blo 1578487 103910471 := bstep (se 1 (by rfl) ⟨77932853, by rfl⟩ : syracuseStep 103910471 = 155865707) B155865707
theorem B5999791 : Blo 1578487 5999791 := bstep (se 1 (by rfl) ⟨4499843, by rfl⟩ : syracuseStep 5999791 = 8999687) B8999687
theorem B4869533 : Blo 1578487 4869533 := bstep (se 3 (by rfl) ⟨913037, by rfl⟩ : syracuseStep 4869533 = 1826075) B1826075
theorem B6745787 : Blo 1578487 6745787 := bstep (se 1 (by rfl) ⟨5059340, by rfl⟩ : syracuseStep 6745787 = 10118681) B10118681
theorem B6000551 : Blo 1578487 6000551 := bstep (se 1 (by rfl) ⟨4500413, by rfl⟩ : syracuseStep 6000551 = 9000827) B9000827
theorem B18231277 : Blo 1578487 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B3371321 : Blo 1578487 3371321 := bstep (se 2 (by rfl) ⟨1264245, by rfl⟩ : syracuseStep 3371321 = 2528491) B2528491
theorem B28832111 : Blo 1578487 28832111 := bstep (se 1 (by rfl) ⟨21624083, by rfl⟩ : syracuseStep 28832111 = 43248167) B43248167
theorem B3551849 : Blo 1578487 3551849 := bstep (se 2 (by rfl) ⟨1331943, by rfl⟩ : syracuseStep 3551849 = 2663887) B2663887
theorem B11989619 : Blo 1578487 11989619 := bstep (se 1 (by rfl) ⟨8992214, by rfl⟩ : syracuseStep 11989619 = 17984429) B17984429
theorem B5329583 : Blo 1578487 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B5329961 : Blo 1578487 5329961 := bstep (se 2 (by rfl) ⟨1998735, by rfl⟩ : syracuseStep 5329961 = 3997471) B3997471
theorem B9122939 : Blo 1578487 9122939 := bstep (se 1 (by rfl) ⟨6842204, by rfl⟩ : syracuseStep 9122939 = 13684409) B13684409
theorem B27366599 : Blo 1578487 27366599 := bstep (se 1 (by rfl) ⟨20524949, by rfl⟩ : syracuseStep 27366599 = 41049899) B41049899
theorem B6075739 : Blo 1578487 6075739 := bstep (se 1 (by rfl) ⟨4556804, by rfl⟩ : syracuseStep 6075739 = 9113609) B9113609
theorem B5690735 : Blo 1578487 5690735 := bstep (se 1 (by rfl) ⟨4268051, by rfl⟩ : syracuseStep 5690735 = 8536103) B8536103
theorem B1578527 : Blo 1578487 1578527 := bstep (se 1 (by rfl) ⟨1183895, by rfl⟩ : syracuseStep 1578527 = 2367791) B2367791
theorem B1578687 : Blo 1578487 1578687 := bstep (se 1 (by rfl) ⟨1184015, by rfl⟩ : syracuseStep 1578687 = 2368031) B2368031
theorem B1578727 : Blo 1578487 1578727 := bstep (se 1 (by rfl) ⟨1184045, by rfl⟩ : syracuseStep 1578727 = 2368091) B2368091
theorem B6076217 : Blo 1578487 6076217 := bstep (se 2 (by rfl) ⟨2278581, by rfl⟩ : syracuseStep 6076217 = 4557163) B4557163
theorem B1579071 : Blo 1578487 1579071 := bstep (se 1 (by rfl) ⟨1184303, by rfl⟩ : syracuseStep 1579071 = 2368607) B2368607
theorem B1579111 : Blo 1578487 1579111 := bstep (se 1 (by rfl) ⟨1184333, by rfl⟩ : syracuseStep 1579111 = 2368667) B2368667
theorem B5404927 : Blo 1578487 5404927 := bstep (se 1 (by rfl) ⟨4053695, by rfl⟩ : syracuseStep 5404927 = 8107391) B8107391
theorem B1579419 : Blo 1578487 1579419 := bstep (se 1 (by rfl) ⟨1184564, by rfl⟩ : syracuseStep 1579419 = 2369129) B2369129
theorem B1579503 : Blo 1578487 1579503 := bstep (se 1 (by rfl) ⟨1184627, by rfl⟩ : syracuseStep 1579503 = 2369255) B2369255
theorem B10959391 : Blo 1578487 10959391 := bstep (se 1 (by rfl) ⟨8219543, by rfl⟩ : syracuseStep 10959391 = 16439087) B16439087
theorem B43219493 : Blo 1578487 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B1579567 : Blo 1578487 1579567 := bstep (se 1 (by rfl) ⟨1184675, by rfl⟩ : syracuseStep 1579567 = 2369351) B2369351
theorem B3553847 : Blo 1578487 3553847 := bstep (se 1 (by rfl) ⟨2665385, by rfl⟩ : syracuseStep 3553847 = 5330771) B5330771
theorem B10402451 : Blo 1578487 10402451 := bstep (se 1 (by rfl) ⟨7801838, by rfl⟩ : syracuseStep 10402451 = 15603677) B15603677
theorem B3373807 : Blo 1578487 3373807 := bstep (se 1 (by rfl) ⟨2530355, by rfl⟩ : syracuseStep 3373807 = 5060711) B5060711
theorem B10951463 : Blo 1578487 10951463 := bstep (se 1 (by rfl) ⟨8213597, by rfl⟩ : syracuseStep 10951463 = 16427195) B16427195
theorem B1579839 : Blo 1578487 1579839 := bstep (se 1 (by rfl) ⟨1184879, by rfl⟩ : syracuseStep 1579839 = 2369759) B2369759
theorem B1579879 : Blo 1578487 1579879 := bstep (se 1 (by rfl) ⟨1184909, by rfl⟩ : syracuseStep 1579879 = 2369819) B2369819
theorem B1579967 : Blo 1578487 1579967 := bstep (se 1 (by rfl) ⟨1184975, by rfl⟩ : syracuseStep 1579967 = 2369951) B2369951
theorem B1776703 : Blo 1578487 1776703 := bstep (se 1 (by rfl) ⟨1332527, by rfl⟩ : syracuseStep 1776703 = 2665055) B2665055
theorem B1580095 : Blo 1578487 1580095 := bstep (se 1 (by rfl) ⟨1185071, by rfl⟩ : syracuseStep 1580095 = 2370143) B2370143
theorem B1580315 : Blo 1578487 1580315 := bstep (se 1 (by rfl) ⟨1185236, by rfl⟩ : syracuseStep 1580315 = 2370473) B2370473
theorem B1580335 : Blo 1578487 1580335 := bstep (se 1 (by rfl) ⟨1185251, by rfl⟩ : syracuseStep 1580335 = 2370503) B2370503
theorem B1580415 : Blo 1578487 1580415 := bstep (se 1 (by rfl) ⟨1185311, by rfl⟩ : syracuseStep 1580415 = 2370623) B2370623
theorem B5332499 : Blo 1578487 5332499 := bstep (se 1 (by rfl) ⟨3999374, by rfl⟩ : syracuseStep 5332499 = 7998749) B7998749
theorem B57646997 : Blo 1578487 57646997 := bstep (se 6 (by rfl) ⟨1351101, by rfl⟩ : syracuseStep 57646997 = 2702203) B2702203
theorem B1777567 : Blo 1578487 1777567 := bstep (se 1 (by rfl) ⟨1333175, by rfl⟩ : syracuseStep 1777567 = 2666351) B2666351
theorem B11993021 : Blo 1578487 11993021 := bstep (se 3 (by rfl) ⟨2248691, by rfl⟩ : syracuseStep 11993021 = 4497383) B4497383
theorem B30769345 : Blo 1578487 30769345 := bstep (se 2 (by rfl) ⟨11538504, by rfl⟩ : syracuseStep 30769345 = 23077009) B23077009
theorem B68297093 : Blo 1578487 68297093 := bstep (se 4 (by rfl) ⟨6402852, by rfl⟩ : syracuseStep 68297093 = 12805705) B12805705
theorem B2367899 : Blo 1578487 2367899 := bstep (se 1 (by rfl) ⟨1775924, by rfl⟩ : syracuseStep 2367899 = 3551849) B3551849
theorem B30343805 : Blo 1578487 30343805 := bstep (se 3 (by rfl) ⟨5689463, by rfl⟩ : syracuseStep 30343805 = 11378927) B11378927
theorem B2999015 : Blo 1578487 2999015 := bstep (se 1 (by rfl) ⟨2249261, by rfl⟩ : syracuseStep 2999015 = 4498523) B4498523
theorem B18244399 : Blo 1578487 18244399 := bstep (se 1 (by rfl) ⟨13683299, by rfl⟩ : syracuseStep 18244399 = 27366599) B27366599
theorem B3998555 : Blo 1578487 3998555 := bstep (se 1 (by rfl) ⟨2998916, by rfl⟩ : syracuseStep 3998555 = 5997833) B5997833
theorem B3793823 : Blo 1578487 3793823 := bstep (se 1 (by rfl) ⟨2845367, by rfl⟩ : syracuseStep 3793823 = 5690735) B5690735
theorem B4498409 : Blo 1578487 4498409 := bstep (se 2 (by rfl) ⟨1686903, by rfl⟩ : syracuseStep 4498409 = 3373807) B3373807
theorem B14402623 : Blo 1578487 14402623 := bstep (se 1 (by rfl) ⟨10801967, by rfl⟩ : syracuseStep 14402623 = 21603935) B21603935
theorem B2368937 : Blo 1578487 2368937 := bstep (se 2 (by rfl) ⟨888351, by rfl⟩ : syracuseStep 2368937 = 1776703) B1776703
theorem B13501991 : Blo 1578487 13501991 := bstep (se 1 (by rfl) ⟨10126493, by rfl⟩ : syracuseStep 13501991 = 20252987) B20252987
theorem B3999415 : Blo 1578487 3999415 := bstep (se 1 (by rfl) ⟨2999561, by rfl⟩ : syracuseStep 3999415 = 5999123) B5999123
theorem B28812995 : Blo 1578487 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B2369231 : Blo 1578487 2369231 := bstep (se 1 (by rfl) ⟨1776923, by rfl⟩ : syracuseStep 2369231 = 3553847) B3553847
theorem B69273647 : Blo 1578487 69273647 := bstep (se 1 (by rfl) ⟨51955235, by rfl⟩ : syracuseStep 69273647 = 103910471) B103910471
theorem B45541541 : Blo 1578487 45541541 := bstep (se 4 (by rfl) ⟨4269519, by rfl⟩ : syracuseStep 45541541 = 8539039) B8539039
theorem B3246355 : Blo 1578487 3246355 := bstep (se 1 (by rfl) ⟨2434766, by rfl⟩ : syracuseStep 3246355 = 4869533) B4869533
theorem B2370089 : Blo 1578487 2370089 := bstep (se 2 (by rfl) ⟨888783, by rfl⟩ : syracuseStep 2370089 = 1777567) B1777567
theorem B38431331 : Blo 1578487 38431331 := bstep (se 1 (by rfl) ⟨28823498, by rfl⟩ : syracuseStep 38431331 = 57646997) B57646997
theorem B4000367 : Blo 1578487 4000367 := bstep (se 1 (by rfl) ⟨3000275, by rfl⟩ : syracuseStep 4000367 = 6000551) B6000551
theorem B24308369 : Blo 1578487 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B19221407 : Blo 1578487 19221407 := bstep (se 1 (by rfl) ⟨14416055, by rfl⟩ : syracuseStep 19221407 = 28832111) B28832111
theorem B21605363 : Blo 1578487 21605363 := bstep (se 1 (by rfl) ⟨16204022, by rfl⟩ : syracuseStep 21605363 = 32408045) B32408045
theorem B3247145 : Blo 1578487 3247145 := bstep (se 2 (by rfl) ⟨1217679, by rfl⟩ : syracuseStep 3247145 = 2435359) B2435359
theorem B8219999 : Blo 1578487 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B6081959 : Blo 1578487 6081959 := bstep (se 1 (by rfl) ⟨4561469, by rfl⟩ : syracuseStep 6081959 = 9122939) B9122939
theorem B2665919 : Blo 1578487 2665919 := bstep (se 1 (by rfl) ⟨1999439, by rfl⟩ : syracuseStep 2665919 = 3998879) B3998879
theorem B8990189 : Blo 1578487 8990189 := bstep (se 3 (by rfl) ⟨1685660, by rfl⟩ : syracuseStep 8990189 = 3371321) B3371321
theorem B7204523 : Blo 1578487 7204523 := bstep (se 1 (by rfl) ⟨5403392, by rfl⟩ : syracuseStep 7204523 = 10806785) B10806785
theorem B4050811 : Blo 1578487 4050811 := bstep (se 1 (by rfl) ⟨3038108, by rfl⟩ : syracuseStep 4050811 = 6076217) B6076217
theorem B7999721 : Blo 1578487 7999721 := bstep (se 2 (by rfl) ⟨2999895, by rfl⟩ : syracuseStep 7999721 = 5999791) B5999791
theorem B6934967 : Blo 1578487 6934967 := bstep (se 1 (by rfl) ⟨5201225, by rfl⟩ : syracuseStep 6934967 = 10402451) B10402451
theorem B3551723 : Blo 1578487 3551723 := bstep (se 1 (by rfl) ⟨2663792, by rfl⟩ : syracuseStep 3551723 = 5327585) B5327585
theorem B2250281 : Blo 1578487 2250281 := bstep (se 2 (by rfl) ⟨843855, by rfl⟩ : syracuseStep 2250281 = 1687711) B1687711
theorem B7206569 : Blo 1578487 7206569 := bstep (se 2 (by rfl) ⟨2702463, by rfl⟩ : syracuseStep 7206569 = 5404927) B5404927
theorem B1578703 : Blo 1578487 1578703 := bstep (se 1 (by rfl) ⟨1184027, by rfl⟩ : syracuseStep 1578703 = 2368055) B2368055
theorem B7591643 : Blo 1578487 7591643 := bstep (se 1 (by rfl) ⟨5693732, by rfl⟩ : syracuseStep 7591643 = 11387465) B11387465
theorem B7993079 : Blo 1578487 7993079 := bstep (se 1 (by rfl) ⟨5994809, by rfl⟩ : syracuseStep 7993079 = 11989619) B11989619
theorem B3553055 : Blo 1578487 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B1578863 : Blo 1578487 1578863 := bstep (se 1 (by rfl) ⟨1184147, by rfl⟩ : syracuseStep 1578863 = 2368295) B2368295
theorem B1578919 : Blo 1578487 1578919 := bstep (se 1 (by rfl) ⟨1184189, by rfl⟩ : syracuseStep 1578919 = 2368379) B2368379
theorem B1578943 : Blo 1578487 1578943 := bstep (se 1 (by rfl) ⟨1184207, by rfl⟩ : syracuseStep 1578943 = 2368415) B2368415
theorem B1579003 : Blo 1578487 1579003 := bstep (se 1 (by rfl) ⟨1184252, by rfl⟩ : syracuseStep 1579003 = 2368505) B2368505
theorem B3553307 : Blo 1578487 3553307 := bstep (se 1 (by rfl) ⟨2664980, by rfl⟩ : syracuseStep 3553307 = 5329961) B5329961
theorem B14612521 : Blo 1578487 14612521 := bstep (se 2 (by rfl) ⟨5479695, by rfl⟩ : syracuseStep 14612521 = 10959391) B10959391
theorem B60741737 : Blo 1578487 60741737 := bstep (se 2 (by rfl) ⟨22778151, by rfl⟩ : syracuseStep 60741737 = 45556303) B45556303
theorem B9001145 : Blo 1578487 9001145 := bstep (se 2 (by rfl) ⟨3375429, by rfl⟩ : syracuseStep 9001145 = 6750859) B6750859
theorem B1579231 : Blo 1578487 1579231 := bstep (se 1 (by rfl) ⟨1184423, by rfl⟩ : syracuseStep 1579231 = 2368847) B2368847
theorem B1579263 : Blo 1578487 1579263 := bstep (se 1 (by rfl) ⟨1184447, by rfl⟩ : syracuseStep 1579263 = 2368895) B2368895
theorem B8993105 : Blo 1578487 8993105 := bstep (se 2 (by rfl) ⟨3372414, by rfl⟩ : syracuseStep 8993105 = 6744829) B6744829
theorem B1579391 : Blo 1578487 1579391 := bstep (se 1 (by rfl) ⟨1184543, by rfl⟩ : syracuseStep 1579391 = 2369087) B2369087
theorem B1579631 : Blo 1578487 1579631 := bstep (se 1 (by rfl) ⟨1184723, by rfl⟩ : syracuseStep 1579631 = 2369447) B2369447
theorem B1579711 : Blo 1578487 1579711 := bstep (se 1 (by rfl) ⟨1184783, by rfl⟩ : syracuseStep 1579711 = 2369567) B2369567
theorem B5331689 : Blo 1578487 5331689 := bstep (se 2 (by rfl) ⟨1999383, by rfl⟩ : syracuseStep 5331689 = 3998767) B3998767
theorem B1776487 : Blo 1578487 1776487 := bstep (se 1 (by rfl) ⟨1332365, by rfl⟩ : syracuseStep 1776487 = 2664731) B2664731
theorem B8100985 : Blo 1578487 8100985 := bstep (se 2 (by rfl) ⟨3037869, by rfl⟩ : syracuseStep 8100985 = 6075739) B6075739
theorem B1580283 : Blo 1578487 1580283 := bstep (se 1 (by rfl) ⟨1185212, by rfl⟩ : syracuseStep 1580283 = 2370425) B2370425
theorem B67525889 : Blo 1578487 67525889 := bstep (se 2 (by rfl) ⟨25322208, by rfl⟩ : syracuseStep 67525889 = 50644417) B50644417
theorem B29203901 : Blo 1578487 29203901 := bstep (se 3 (by rfl) ⟨5475731, by rfl⟩ : syracuseStep 29203901 = 10951463) B10951463
theorem B3554999 : Blo 1578487 3554999 := bstep (se 1 (by rfl) ⟨2666249, by rfl⟩ : syracuseStep 3554999 = 5332499) B5332499
theorem B4497191 : Blo 1578487 4497191 := bstep (se 1 (by rfl) ⟨3372893, by rfl⟩ : syracuseStep 4497191 = 6745787) B6745787
theorem B7995347 : Blo 1578487 7995347 := bstep (se 1 (by rfl) ⟨5996510, by rfl⟩ : syracuseStep 7995347 = 11993021) B11993021
theorem B5333147 : Blo 1578487 5333147 := bstep (se 1 (by rfl) ⟨3999860, by rfl⟩ : syracuseStep 5333147 = 7999721) B7999721
theorem B41025793 : Blo 1578487 41025793 := bstep (se 2 (by rfl) ⟨15384672, by rfl⟩ : syracuseStep 41025793 = 30769345) B30769345
theorem B45531395 : Blo 1578487 45531395 := bstep (se 1 (by rfl) ⟨34148546, by rfl⟩ : syracuseStep 45531395 = 68297093) B68297093
theorem B2367815 : Blo 1578487 2367815 := bstep (se 1 (by rfl) ⟨1775861, by rfl⟩ : syracuseStep 2367815 = 3551723) B3551723
theorem B1999343 : Blo 1578487 1999343 := bstep (se 1 (by rfl) ⟨1499507, by rfl⟩ : syracuseStep 1999343 = 2999015) B2999015
theorem B2998939 : Blo 1578487 2998939 := bstep (se 1 (by rfl) ⟨2249204, by rfl⟩ : syracuseStep 2998939 = 4498409) B4498409
theorem B180069037 : Blo 1578487 180069037 := bstep (se 3 (by rfl) ⟨33762944, by rfl⟩ : syracuseStep 180069037 = 67525889) B67525889
theorem B2368649 : Blo 1578487 2368649 := bstep (se 2 (by rfl) ⟨888243, by rfl⟩ : syracuseStep 2368649 = 1776487) B1776487
theorem B2368703 : Blo 1578487 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B2368871 : Blo 1578487 2368871 := bstep (se 1 (by rfl) ⟨1776653, by rfl⟩ : syracuseStep 2368871 = 3553307) B3553307
theorem B40494491 : Blo 1578487 40494491 := bstep (se 1 (by rfl) ⟨30370868, by rfl⟩ : syracuseStep 40494491 = 60741737) B60741737
theorem B19203497 : Blo 1578487 19203497 := bstep (se 2 (by rfl) ⟨7201311, by rfl⟩ : syracuseStep 19203497 = 14402623) B14402623
theorem B30361027 : Blo 1578487 30361027 := bstep (se 1 (by rfl) ⟨22770770, by rfl⟩ : syracuseStep 30361027 = 45541541) B45541541
theorem B16205579 : Blo 1578487 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B19212061 : Blo 1578487 19212061 := bstep (se 3 (by rfl) ⟨3602261, by rfl⟩ : syracuseStep 19212061 = 7204523) B7204523
theorem B12814271 : Blo 1578487 12814271 := bstep (se 1 (by rfl) ⟨9610703, by rfl⟩ : syracuseStep 12814271 = 19221407) B19221407
theorem B14403575 : Blo 1578487 14403575 := bstep (se 1 (by rfl) ⟨10802681, by rfl⟩ : syracuseStep 14403575 = 21605363) B21605363
theorem B2164763 : Blo 1578487 2164763 := bstep (se 1 (by rfl) ⟨1623572, by rfl⟩ : syracuseStep 2164763 = 3247145) B3247145
theorem B2369999 : Blo 1578487 2369999 := bstep (se 1 (by rfl) ⟨1777499, by rfl⟩ : syracuseStep 2369999 = 3554999) B3554999
theorem B5401081 : Blo 1578487 5401081 := bstep (se 2 (by rfl) ⟨2025405, by rfl⟩ : syracuseStep 5401081 = 4050811) B4050811
theorem B19483361 : Blo 1578487 19483361 := bstep (se 2 (by rfl) ⟨7306260, by rfl⟩ : syracuseStep 19483361 = 14612521) B14612521
theorem B4623311 : Blo 1578487 4623311 := bstep (se 1 (by rfl) ⟨3467483, by rfl⟩ : syracuseStep 4623311 = 6934967) B6934967
theorem B4328473 : Blo 1578487 4328473 := bstep (se 2 (by rfl) ⟨1623177, by rfl⟩ : syracuseStep 4328473 = 3246355) B3246355
theorem B20229203 : Blo 1578487 20229203 := bstep (se 1 (by rfl) ⟨15171902, by rfl⟩ : syracuseStep 20229203 = 30343805) B30343805
theorem B2665703 : Blo 1578487 2665703 := bstep (se 1 (by rfl) ⟨1999277, by rfl⟩ : syracuseStep 2665703 = 3998555) B3998555
theorem B24325865 : Blo 1578487 24325865 := bstep (se 2 (by rfl) ⟨9122199, by rfl⟩ : syracuseStep 24325865 = 18244399) B18244399
theorem B4804379 : Blo 1578487 4804379 := bstep (se 1 (by rfl) ⟨3603284, by rfl⟩ : syracuseStep 4804379 = 7206569) B7206569
theorem B5328719 : Blo 1578487 5328719 := bstep (se 1 (by rfl) ⟨3996539, by rfl⟩ : syracuseStep 5328719 = 7993079) B7993079
theorem B46182431 : Blo 1578487 46182431 := bstep (se 1 (by rfl) ⟨34636823, by rfl⟩ : syracuseStep 46182431 = 69273647) B69273647
theorem B6000749 : Blo 1578487 6000749 := bstep (se 3 (by rfl) ⟨1125140, by rfl⟩ : syracuseStep 6000749 = 2250281) B2250281
theorem B6000763 : Blo 1578487 6000763 := bstep (se 1 (by rfl) ⟨4500572, by rfl⟩ : syracuseStep 6000763 = 9001145) B9001145
theorem B10801313 : Blo 1578487 10801313 := bstep (se 2 (by rfl) ⟨4050492, by rfl⟩ : syracuseStep 10801313 = 8100985) B8100985
theorem B25620887 : Blo 1578487 25620887 := bstep (se 1 (by rfl) ⟨19215665, by rfl⟩ : syracuseStep 25620887 = 38431331) B38431331
theorem B2666911 : Blo 1578487 2666911 := bstep (se 1 (by rfl) ⟨2000183, by rfl⟩ : syracuseStep 2666911 = 4000367) B4000367
theorem B19469267 : Blo 1578487 19469267 := bstep (se 1 (by rfl) ⟨14601950, by rfl⟩ : syracuseStep 19469267 = 29203901) B29203901
theorem B5993459 : Blo 1578487 5993459 := bstep (se 1 (by rfl) ⟨4495094, by rfl⟩ : syracuseStep 5993459 = 8990189) B8990189
theorem B5330231 : Blo 1578487 5330231 := bstep (se 1 (by rfl) ⟨3997673, by rfl⟩ : syracuseStep 5330231 = 7995347) B7995347
theorem B1578599 : Blo 1578487 1578599 := bstep (se 1 (by rfl) ⟨1183949, by rfl⟩ : syracuseStep 1578599 = 2367899) B2367899
theorem B2529215 : Blo 1578487 2529215 := bstep (se 1 (by rfl) ⟨1896911, by rfl⟩ : syracuseStep 2529215 = 3793823) B3793823
theorem B21919997 : Blo 1578487 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B1579291 : Blo 1578487 1579291 := bstep (se 1 (by rfl) ⟨1184468, by rfl⟩ : syracuseStep 1579291 = 2368937) B2368937
theorem B9001327 : Blo 1578487 9001327 := bstep (se 1 (by rfl) ⟨6750995, by rfl⟩ : syracuseStep 9001327 = 13501991) B13501991
theorem B19208663 : Blo 1578487 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B1579487 : Blo 1578487 1579487 := bstep (se 1 (by rfl) ⟨1184615, by rfl⟩ : syracuseStep 1579487 = 2369231) B2369231
theorem B5061095 : Blo 1578487 5061095 := bstep (se 1 (by rfl) ⟨3795821, by rfl⟩ : syracuseStep 5061095 = 7591643) B7591643
theorem B5995403 : Blo 1578487 5995403 := bstep (se 1 (by rfl) ⟨4496552, by rfl⟩ : syracuseStep 5995403 = 8993105) B8993105
theorem B1580059 : Blo 1578487 1580059 := bstep (se 1 (by rfl) ⟨1185044, by rfl⟩ : syracuseStep 1580059 = 2370089) B2370089
theorem B3554459 : Blo 1578487 3554459 := bstep (se 1 (by rfl) ⟨2665844, by rfl⟩ : syracuseStep 3554459 = 5331689) B5331689
theorem B5332553 : Blo 1578487 5332553 := bstep (se 2 (by rfl) ⟨1999707, by rfl⟩ : syracuseStep 5332553 = 3999415) B3999415
theorem B4054639 : Blo 1578487 4054639 := bstep (se 1 (by rfl) ⟨3040979, by rfl⟩ : syracuseStep 4054639 = 6081959) B6081959
theorem B1777279 : Blo 1578487 1777279 := bstep (se 1 (by rfl) ⟨1332959, by rfl⟩ : syracuseStep 1777279 = 2665919) B2665919
theorem B2998127 : Blo 1578487 2998127 := bstep (se 1 (by rfl) ⟨2248595, by rfl⟩ : syracuseStep 2998127 = 4497191) B4497191
theorem B3555431 : Blo 1578487 3555431 := bstep (se 1 (by rfl) ⟨2666573, by rfl⟩ : syracuseStep 3555431 = 5333147) B5333147
theorem B7200875 : Blo 1578487 7200875 := bstep (se 1 (by rfl) ⟨5400656, by rfl⟩ : syracuseStep 7200875 = 10801313) B10801313
theorem B17080591 : Blo 1578487 17080591 := bstep (se 1 (by rfl) ⟨12810443, by rfl⟩ : syracuseStep 17080591 = 25620887) B25620887
theorem B12001769 : Blo 1578487 12001769 := bstep (se 2 (by rfl) ⟨4500663, by rfl⟩ : syracuseStep 12001769 = 9001327) B9001327
theorem B3555881 : Blo 1578487 3555881 := bstep (se 2 (by rfl) ⟨1333455, by rfl⟩ : syracuseStep 3555881 = 2666911) B2666911
theorem B7201441 : Blo 1578487 7201441 := bstep (se 2 (by rfl) ⟨2700540, by rfl⟩ : syracuseStep 7201441 = 5401081) B5401081
theorem B3998585 : Blo 1578487 3998585 := bstep (se 2 (by rfl) ⟨1499469, by rfl⟩ : syracuseStep 3998585 = 2998939) B2998939
theorem B9602383 : Blo 1578487 9602383 := bstep (se 1 (by rfl) ⟨7201787, by rfl⟩ : syracuseStep 9602383 = 14403575) B14403575
theorem B12805775 : Blo 1578487 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B3082207 : Blo 1578487 3082207 := bstep (se 1 (by rfl) ⟨2311655, by rfl⟩ : syracuseStep 3082207 = 4623311) B4623311
theorem B13486135 : Blo 1578487 13486135 := bstep (se 1 (by rfl) ⟨10114601, by rfl⟩ : syracuseStep 13486135 = 20229203) B20229203
theorem B2369639 : Blo 1578487 2369639 := bstep (se 1 (by rfl) ⟨1777229, by rfl⟩ : syracuseStep 2369639 = 3554459) B3554459
theorem B2369705 : Blo 1578487 2369705 := bstep (se 2 (by rfl) ⟨888639, by rfl⟩ : syracuseStep 2369705 = 1777279) B1777279
theorem B4000499 : Blo 1578487 4000499 := bstep (se 1 (by rfl) ⟨3000374, by rfl⟩ : syracuseStep 4000499 = 6000749) B6000749
theorem B123153149 : Blo 1578487 123153149 := bstep (se 3 (by rfl) ⟨23091215, by rfl⟩ : syracuseStep 123153149 = 46182431) B46182431
theorem B30354263 : Blo 1578487 30354263 := bstep (se 1 (by rfl) ⟨22765697, by rfl⟩ : syracuseStep 30354263 = 45531395) B45531395
theorem B54701057 : Blo 1578487 54701057 := bstep (se 2 (by rfl) ⟨20512896, by rfl⟩ : syracuseStep 54701057 = 41025793) B41025793
theorem B12979511 : Blo 1578487 12979511 := bstep (se 1 (by rfl) ⟨9734633, by rfl⟩ : syracuseStep 12979511 = 19469267) B19469267
theorem B58453325 : Blo 1578487 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B960368197 : Blo 1578487 960368197 := bstep (se 4 (by rfl) ⟨90034518, by rfl⟩ : syracuseStep 960368197 = 180069037) B180069037
theorem B26996327 : Blo 1578487 26996327 := bstep (se 1 (by rfl) ⟨20247245, by rfl⟩ : syracuseStep 26996327 = 40494491) B40494491
theorem B5771297 : Blo 1578487 5771297 := bstep (se 2 (by rfl) ⟨2164236, by rfl⟩ : syracuseStep 5771297 = 4328473) B4328473
theorem B12988907 : Blo 1578487 12988907 := bstep (se 1 (by rfl) ⟨9741680, by rfl⟩ : syracuseStep 12988907 = 19483361) B19483361
theorem B40481369 : Blo 1578487 40481369 := bstep (se 2 (by rfl) ⟨15180513, by rfl⟩ : syracuseStep 40481369 = 30361027) B30361027
theorem B16217243 : Blo 1578487 16217243 := bstep (se 1 (by rfl) ⟨12162932, by rfl⟩ : syracuseStep 16217243 = 24325865) B24325865
theorem B3552479 : Blo 1578487 3552479 := bstep (se 1 (by rfl) ⟨2664359, by rfl⟩ : syracuseStep 3552479 = 5328719) B5328719
theorem B5772701 : Blo 1578487 5772701 := bstep (se 3 (by rfl) ⟨1082381, by rfl⟩ : syracuseStep 5772701 = 2164763) B2164763
theorem B8001017 : Blo 1578487 8001017 := bstep (se 2 (by rfl) ⟨3000381, by rfl⟩ : syracuseStep 8001017 = 6000763) B6000763
theorem B1578543 : Blo 1578487 1578543 := bstep (se 1 (by rfl) ⟨1183907, by rfl⟩ : syracuseStep 1578543 = 2367815) B2367815
theorem B3995639 : Blo 1578487 3995639 := bstep (se 1 (by rfl) ⟨2996729, by rfl⟩ : syracuseStep 3995639 = 5993459) B5993459
theorem B1579099 : Blo 1578487 1579099 := bstep (se 1 (by rfl) ⟨1184324, by rfl⟩ : syracuseStep 1579099 = 2368649) B2368649
theorem B1579135 : Blo 1578487 1579135 := bstep (se 1 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 1579135 = 2368703) B2368703
theorem B3553487 : Blo 1578487 3553487 := bstep (se 1 (by rfl) ⟨2665115, by rfl⟩ : syracuseStep 3553487 = 5330231) B5330231
theorem B1579247 : Blo 1578487 1579247 := bstep (se 1 (by rfl) ⟨1184435, by rfl⟩ : syracuseStep 1579247 = 2368871) B2368871
theorem B12802331 : Blo 1578487 12802331 := bstep (se 1 (by rfl) ⟨9601748, by rfl⟩ : syracuseStep 12802331 = 19203497) B19203497
theorem B10803719 : Blo 1578487 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B5331581 : Blo 1578487 5331581 := bstep (se 3 (by rfl) ⟨999671, by rfl⟩ : syracuseStep 5331581 = 1999343) B1999343
theorem B1686143 : Blo 1578487 1686143 := bstep (se 1 (by rfl) ⟨1264607, by rfl⟩ : syracuseStep 1686143 = 2529215) B2529215
theorem B8542847 : Blo 1578487 8542847 := bstep (se 1 (by rfl) ⟨6407135, by rfl⟩ : syracuseStep 8542847 = 12814271) B12814271
theorem B1579999 : Blo 1578487 1579999 := bstep (se 1 (by rfl) ⟨1184999, by rfl⟩ : syracuseStep 1579999 = 2369999) B2369999
theorem B3374063 : Blo 1578487 3374063 := bstep (se 1 (by rfl) ⟨2530547, by rfl⟩ : syracuseStep 3374063 = 5061095) B5061095
theorem B3996935 : Blo 1578487 3996935 := bstep (se 1 (by rfl) ⟨2997701, by rfl⟩ : syracuseStep 3996935 = 5995403) B5995403
theorem B5406185 : Blo 1578487 5406185 := bstep (se 2 (by rfl) ⟨2027319, by rfl⟩ : syracuseStep 5406185 = 4054639) B4054639
theorem B1777135 : Blo 1578487 1777135 := bstep (se 1 (by rfl) ⟨1332851, by rfl⟩ : syracuseStep 1777135 = 2665703) B2665703
theorem B25616081 : Blo 1578487 25616081 := bstep (se 2 (by rfl) ⟨9606030, by rfl⟩ : syracuseStep 25616081 = 19212061) B19212061
theorem B3555035 : Blo 1578487 3555035 := bstep (se 1 (by rfl) ⟨2666276, by rfl⟩ : syracuseStep 3555035 = 5332553) B5332553
theorem B3202919 : Blo 1578487 3202919 := bstep (se 1 (by rfl) ⟨2402189, by rfl⟩ : syracuseStep 3202919 = 4804379) B4804379
theorem B1998751 : Blo 1578487 1998751 := bstep (se 1 (by rfl) ⟨1499063, by rfl⟩ : syracuseStep 1998751 = 2998127) B2998127
theorem B4800583 : Blo 1578487 4800583 := bstep (se 1 (by rfl) ⟨3600437, by rfl⟩ : syracuseStep 4800583 = 7200875) B7200875
theorem B17981513 : Blo 1578487 17981513 := bstep (se 2 (by rfl) ⟨6743067, by rfl⟩ : syracuseStep 17981513 = 13486135) B13486135
theorem B8659271 : Blo 1578487 8659271 := bstep (se 1 (by rfl) ⟨6494453, by rfl⟩ : syracuseStep 8659271 = 12988907) B12988907
theorem B22774121 : Blo 1578487 22774121 := bstep (se 2 (by rfl) ⟨8540295, by rfl⟩ : syracuseStep 22774121 = 17080591) B17080591
theorem B2368319 : Blo 1578487 2368319 := bstep (se 1 (by rfl) ⟨1776239, by rfl⟩ : syracuseStep 2368319 = 3552479) B3552479
theorem B9601921 : Blo 1578487 9601921 := bstep (se 2 (by rfl) ⟨3600720, by rfl⟩ : syracuseStep 9601921 = 7201441) B7201441
theorem B5334011 : Blo 1578487 5334011 := bstep (se 1 (by rfl) ⟨4000508, by rfl⟩ : syracuseStep 5334011 = 8001017) B8001017
theorem B8537183 : Blo 1578487 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B2663759 : Blo 1578487 2663759 := bstep (se 1 (by rfl) ⟨1997819, by rfl⟩ : syracuseStep 2663759 = 3995639) B3995639
theorem B2368991 : Blo 1578487 2368991 := bstep (se 1 (by rfl) ⟨1776743, by rfl⟩ : syracuseStep 2368991 = 3553487) B3553487
theorem B5695231 : Blo 1578487 5695231 := bstep (se 1 (by rfl) ⟨4271423, by rfl⟩ : syracuseStep 5695231 = 8542847) B8542847
theorem B82102099 : Blo 1578487 82102099 := bstep (se 1 (by rfl) ⟨61576574, by rfl⟩ : syracuseStep 82102099 = 123153149) B123153149
theorem B20236175 : Blo 1578487 20236175 := bstep (se 1 (by rfl) ⟨15177131, by rfl⟩ : syracuseStep 20236175 = 30354263) B30354263
theorem B2369513 : Blo 1578487 2369513 := bstep (se 2 (by rfl) ⟨888567, by rfl⟩ : syracuseStep 2369513 = 1777135) B1777135
theorem B2664623 : Blo 1578487 2664623 := bstep (se 1 (by rfl) ⟨1998467, by rfl⟩ : syracuseStep 2664623 = 3996935) B3996935
theorem B8653007 : Blo 1578487 8653007 := bstep (se 1 (by rfl) ⟨6489755, by rfl⟩ : syracuseStep 8653007 = 12979511) B12979511
theorem B2370023 : Blo 1578487 2370023 := bstep (se 1 (by rfl) ⟨1777517, by rfl⟩ : syracuseStep 2370023 = 3555035) B3555035
theorem B2665001 : Blo 1578487 2665001 := bstep (se 2 (by rfl) ⟨999375, by rfl⟩ : syracuseStep 2665001 = 1998751) B1998751
theorem B2370287 : Blo 1578487 2370287 := bstep (se 1 (by rfl) ⟨1777715, by rfl⟩ : syracuseStep 2370287 = 3555431) B3555431
theorem B2370587 : Blo 1578487 2370587 := bstep (se 1 (by rfl) ⟨1777940, by rfl⟩ : syracuseStep 2370587 = 3555881) B3555881
theorem B26987579 : Blo 1578487 26987579 := bstep (se 1 (by rfl) ⟨20240684, by rfl⟩ : syracuseStep 26987579 = 40481369) B40481369
theorem B2665723 : Blo 1578487 2665723 := bstep (se 1 (by rfl) ⟨1999292, by rfl⟩ : syracuseStep 2665723 = 3998585) B3998585
theorem B34139549 : Blo 1578487 34139549 := bstep (se 3 (by rfl) ⟨6401165, by rfl⟩ : syracuseStep 34139549 = 12802331) B12802331
theorem B2666999 : Blo 1578487 2666999 := bstep (se 1 (by rfl) ⟨2000249, by rfl⟩ : syracuseStep 2666999 = 4000499) B4000499
theorem B2249375 : Blo 1578487 2249375 := bstep (se 1 (by rfl) ⟨1687031, by rfl⟩ : syracuseStep 2249375 = 3374063) B3374063
theorem B36467371 : Blo 1578487 36467371 := bstep (se 1 (by rfl) ⟨27350528, by rfl⟩ : syracuseStep 36467371 = 54701057) B54701057
theorem B17077387 : Blo 1578487 17077387 := bstep (se 1 (by rfl) ⟨12808040, by rfl⟩ : syracuseStep 17077387 = 25616081) B25616081
theorem B2135279 : Blo 1578487 2135279 := bstep (se 1 (by rfl) ⟨1601459, by rfl⟩ : syracuseStep 2135279 = 3202919) B3202919
theorem B4109609 : Blo 1578487 4109609 := bstep (se 2 (by rfl) ⟨1541103, by rfl⟩ : syracuseStep 4109609 = 3082207) B3082207
theorem B15390125 : Blo 1578487 15390125 := bstep (se 3 (by rfl) ⟨2885648, by rfl⟩ : syracuseStep 15390125 = 5771297) B5771297
theorem B8001179 : Blo 1578487 8001179 := bstep (se 1 (by rfl) ⟨6000884, by rfl⟩ : syracuseStep 8001179 = 12001769) B12001769
theorem B10811495 : Blo 1578487 10811495 := bstep (se 1 (by rfl) ⟨8108621, by rfl⟩ : syracuseStep 10811495 = 16217243) B16217243
theorem B3848467 : Blo 1578487 3848467 := bstep (se 1 (by rfl) ⟨2886350, by rfl⟩ : syracuseStep 3848467 = 5772701) B5772701
theorem B28809917 : Blo 1578487 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B1579759 : Blo 1578487 1579759 := bstep (se 1 (by rfl) ⟨1184819, by rfl⟩ : syracuseStep 1579759 = 2369639) B2369639
theorem B1579803 : Blo 1578487 1579803 := bstep (se 1 (by rfl) ⟨1184852, by rfl⟩ : syracuseStep 1579803 = 2369705) B2369705
theorem B4496381 : Blo 1578487 4496381 := bstep (se 3 (by rfl) ⟨843071, by rfl⟩ : syracuseStep 4496381 = 1686143) B1686143
theorem B3554387 : Blo 1578487 3554387 := bstep (se 1 (by rfl) ⟨2665790, by rfl⟩ : syracuseStep 3554387 = 5331581) B5331581
theorem B12803177 : Blo 1578487 12803177 := bstep (se 2 (by rfl) ⟨4801191, by rfl⟩ : syracuseStep 12803177 = 9602383) B9602383
theorem B1280490929 : Blo 1578487 1280490929 := bstep (se 2 (by rfl) ⟨480184098, by rfl⟩ : syracuseStep 1280490929 = 960368197) B960368197
theorem B38968883 : Blo 1578487 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B3604123 : Blo 1578487 3604123 := bstep (se 1 (by rfl) ⟨2703092, by rfl⟩ : syracuseStep 3604123 = 5406185) B5406185
theorem B17997551 : Blo 1578487 17997551 := bstep (se 1 (by rfl) ⟨13498163, by rfl⟩ : syracuseStep 17997551 = 26996327) B26996327
theorem B1777999 : Blo 1578487 1777999 := bstep (se 1 (by rfl) ⟨1333499, by rfl⟩ : syracuseStep 1777999 = 2666999) B2666999
theorem B5694077 : Blo 1578487 5694077 := bstep (se 3 (by rfl) ⟨1067639, by rfl⟩ : syracuseStep 5694077 = 2135279) B2135279
theorem B3556007 : Blo 1578487 3556007 := bstep (se 1 (by rfl) ⟨2667005, by rfl⟩ : syracuseStep 3556007 = 5334011) B5334011
theorem B5334119 : Blo 1578487 5334119 := bstep (se 1 (by rfl) ⟨4000589, by rfl⟩ : syracuseStep 5334119 = 8001179) B8001179
theorem B5768671 : Blo 1578487 5768671 := bstep (se 1 (by rfl) ⟨4326503, by rfl⟩ : syracuseStep 5768671 = 8653007) B8653007
theorem B5998333 : Blo 1578487 5998333 := bstep (se 3 (by rfl) ⟨1124687, by rfl⟩ : syracuseStep 5998333 = 2249375) B2249375
theorem B51210245 : Blo 1578487 51210245 := bstep (se 4 (by rfl) ⟨4800960, by rfl⟩ : syracuseStep 51210245 = 9601921) B9601921
theorem B17991719 : Blo 1578487 17991719 := bstep (se 1 (by rfl) ⟨13493789, by rfl⟩ : syracuseStep 17991719 = 26987579) B26987579
theorem B2369591 : Blo 1578487 2369591 := bstep (se 1 (by rfl) ⟨1777193, by rfl⟩ : syracuseStep 2369591 = 3554387) B3554387
theorem B22759699 : Blo 1578487 22759699 := bstep (se 1 (by rfl) ⟨17069774, by rfl⟩ : syracuseStep 22759699 = 34139549) B34139549
theorem B25979255 : Blo 1578487 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B11987675 : Blo 1578487 11987675 := bstep (se 1 (by rfl) ⟨8990756, by rfl⟩ : syracuseStep 11987675 = 17981513) B17981513
theorem B6400777 : Blo 1578487 6400777 := bstep (se 2 (by rfl) ⟨2400291, by rfl⟩ : syracuseStep 6400777 = 4800583) B4800583
theorem B15182747 : Blo 1578487 15182747 := bstep (se 1 (by rfl) ⟨11387060, by rfl⟩ : syracuseStep 15182747 = 22774121) B22774121
theorem B28830653 : Blo 1578487 28830653 := bstep (se 3 (by rfl) ⟨5405747, by rfl⟩ : syracuseStep 28830653 = 10811495) B10811495
theorem B5131289 : Blo 1578487 5131289 := bstep (se 2 (by rfl) ⟨1924233, by rfl⟩ : syracuseStep 5131289 = 3848467) B3848467
theorem B2739739 : Blo 1578487 2739739 := bstep (se 1 (by rfl) ⟨2054804, by rfl⟩ : syracuseStep 2739739 = 4109609) B4109609
theorem B48623161 : Blo 1578487 48623161 := bstep (se 2 (by rfl) ⟨18233685, by rfl⟩ : syracuseStep 48623161 = 36467371) B36467371
theorem B10260083 : Blo 1578487 10260083 := bstep (se 1 (by rfl) ⟨7695062, by rfl⟩ : syracuseStep 10260083 = 15390125) B15390125
theorem B22769849 : Blo 1578487 22769849 := bstep (se 2 (by rfl) ⟨8538693, by rfl⟩ : syracuseStep 22769849 = 17077387) B17077387
theorem B19206611 : Blo 1578487 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B4805497 : Blo 1578487 4805497 := bstep (se 2 (by rfl) ⟨1802061, by rfl⟩ : syracuseStep 4805497 = 3604123) B3604123
theorem B853660619 : Blo 1578487 853660619 := bstep (se 1 (by rfl) ⟨640245464, by rfl⟩ : syracuseStep 853660619 = 1280490929) B1280490929
theorem B11998367 : Blo 1578487 11998367 := bstep (se 1 (by rfl) ⟨8998775, by rfl⟩ : syracuseStep 11998367 = 17997551) B17997551
theorem B1578879 : Blo 1578487 1578879 := bstep (se 1 (by rfl) ⟨1184159, by rfl⟩ : syracuseStep 1578879 = 2368319) B2368319
theorem B5691455 : Blo 1578487 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B23091389 : Blo 1578487 23091389 := bstep (se 3 (by rfl) ⟨4329635, by rfl⟩ : syracuseStep 23091389 = 8659271) B8659271
theorem B1775839 : Blo 1578487 1775839 := bstep (se 1 (by rfl) ⟨1331879, by rfl⟩ : syracuseStep 1775839 = 2663759) B2663759
theorem B1579327 : Blo 1578487 1579327 := bstep (se 1 (by rfl) ⟨1184495, by rfl⟩ : syracuseStep 1579327 = 2368991) B2368991
theorem B13490783 : Blo 1578487 13490783 := bstep (se 1 (by rfl) ⟨10118087, by rfl⟩ : syracuseStep 13490783 = 20236175) B20236175
theorem B1579675 : Blo 1578487 1579675 := bstep (se 1 (by rfl) ⟨1184756, by rfl⟩ : syracuseStep 1579675 = 2369513) B2369513
theorem B1776415 : Blo 1578487 1776415 := bstep (se 1 (by rfl) ⟨1332311, by rfl⟩ : syracuseStep 1776415 = 2664623) B2664623
theorem B1580015 : Blo 1578487 1580015 := bstep (se 1 (by rfl) ⟨1185011, by rfl⟩ : syracuseStep 1580015 = 2370023) B2370023
theorem B3554297 : Blo 1578487 3554297 := bstep (se 2 (by rfl) ⟨1332861, by rfl⟩ : syracuseStep 3554297 = 2665723) B2665723
theorem B1776667 : Blo 1578487 1776667 := bstep (se 1 (by rfl) ⟨1332500, by rfl⟩ : syracuseStep 1776667 = 2665001) B2665001
theorem B1580191 : Blo 1578487 1580191 := bstep (se 1 (by rfl) ⟨1185143, by rfl⟩ : syracuseStep 1580191 = 2370287) B2370287
theorem B2997587 : Blo 1578487 2997587 := bstep (se 1 (by rfl) ⟨2248190, by rfl⟩ : syracuseStep 2997587 = 4496381) B4496381
theorem B1580391 : Blo 1578487 1580391 := bstep (se 1 (by rfl) ⟨1185293, by rfl⟩ : syracuseStep 1580391 = 2370587) B2370587
theorem B8535451 : Blo 1578487 8535451 := bstep (se 1 (by rfl) ⟨6401588, by rfl⟩ : syracuseStep 8535451 = 12803177) B12803177
theorem B7593641 : Blo 1578487 7593641 := bstep (se 2 (by rfl) ⟨2847615, by rfl⟩ : syracuseStep 7593641 = 5695231) B5695231
theorem B109469465 : Blo 1578487 109469465 := bstep (se 2 (by rfl) ⟨41051049, by rfl⟩ : syracuseStep 109469465 = 82102099) B82102099
theorem B15179899 : Blo 1578487 15179899 := bstep (se 1 (by rfl) ⟨11384924, by rfl⟩ : syracuseStep 15179899 = 22769849) B22769849
theorem B2367785 : Blo 1578487 2367785 := bstep (se 2 (by rfl) ⟨887919, by rfl⟩ : syracuseStep 2367785 = 1775839) B1775839
theorem B12804407 : Blo 1578487 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B569107079 : Blo 1578487 569107079 := bstep (se 1 (by rfl) ⟨426830309, by rfl⟩ : syracuseStep 569107079 = 853660619) B853660619
theorem B3556079 : Blo 1578487 3556079 := bstep (se 1 (by rfl) ⟨2667059, by rfl⟩ : syracuseStep 3556079 = 5334119) B5334119
theorem B2368553 : Blo 1578487 2368553 := bstep (se 2 (by rfl) ⟨888207, by rfl⟩ : syracuseStep 2368553 = 1776415) B1776415
theorem B11994479 : Blo 1578487 11994479 := bstep (se 1 (by rfl) ⟨8995859, by rfl⟩ : syracuseStep 11994479 = 17991719) B17991719
theorem B2368889 : Blo 1578487 2368889 := bstep (se 2 (by rfl) ⟨888333, by rfl⟩ : syracuseStep 2368889 = 1776667) B1776667
theorem B3794303 : Blo 1578487 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B15394259 : Blo 1578487 15394259 := bstep (se 1 (by rfl) ⟨11545694, by rfl⟩ : syracuseStep 15394259 = 23091389) B23091389
theorem B17319503 : Blo 1578487 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B11380601 : Blo 1578487 11380601 := bstep (se 2 (by rfl) ⟨4267725, by rfl⟩ : syracuseStep 11380601 = 8535451) B8535451
theorem B19220435 : Blo 1578487 19220435 := bstep (se 1 (by rfl) ⟨14415326, by rfl⟩ : syracuseStep 19220435 = 28830653) B28830653
theorem B2369531 : Blo 1578487 2369531 := bstep (se 1 (by rfl) ⟨1777148, by rfl⟩ : syracuseStep 2369531 = 3554297) B3554297
theorem B7997777 : Blo 1578487 7997777 := bstep (se 2 (by rfl) ⟨2999166, by rfl⟩ : syracuseStep 7997777 = 5998333) B5998333
theorem B30346265 : Blo 1578487 30346265 := bstep (se 2 (by rfl) ⟨11379849, by rfl⟩ : syracuseStep 30346265 = 22759699) B22759699
theorem B2370665 : Blo 1578487 2370665 := bstep (se 2 (by rfl) ⟨888999, by rfl⟩ : syracuseStep 2370665 = 1777999) B1777999
theorem B2370671 : Blo 1578487 2370671 := bstep (se 1 (by rfl) ⟨1778003, by rfl⟩ : syracuseStep 2370671 = 3556007) B3556007
theorem B7998911 : Blo 1578487 7998911 := bstep (se 1 (by rfl) ⟨5999183, by rfl⟩ : syracuseStep 7998911 = 11998367) B11998367
theorem B34140163 : Blo 1578487 34140163 := bstep (se 1 (by rfl) ⟨25605122, by rfl⟩ : syracuseStep 34140163 = 51210245) B51210245
theorem B15184205 : Blo 1578487 15184205 := bstep (se 3 (by rfl) ⟨2847038, by rfl⟩ : syracuseStep 15184205 = 5694077) B5694077
theorem B7991783 : Blo 1578487 7991783 := bstep (se 1 (by rfl) ⟨5993837, by rfl⟩ : syracuseStep 7991783 = 11987675) B11987675
theorem B10121831 : Blo 1578487 10121831 := bstep (se 1 (by rfl) ⟨7591373, by rfl⟩ : syracuseStep 10121831 = 15182747) B15182747
theorem B25629317 : Blo 1578487 25629317 := bstep (se 4 (by rfl) ⟨2402748, by rfl⟩ : syracuseStep 25629317 = 4805497) B4805497
theorem B3420859 : Blo 1578487 3420859 := bstep (se 1 (by rfl) ⟨2565644, by rfl⟩ : syracuseStep 3420859 = 5131289) B5131289
theorem B72979643 : Blo 1578487 72979643 := bstep (se 1 (by rfl) ⟨54734732, by rfl⟩ : syracuseStep 72979643 = 109469465) B109469465
theorem B7993565 : Blo 1578487 7993565 := bstep (se 3 (by rfl) ⟨1498793, by rfl⟩ : syracuseStep 7993565 = 2997587) B2997587
theorem B8534369 : Blo 1578487 8534369 := bstep (se 2 (by rfl) ⟨3200388, by rfl⟩ : syracuseStep 8534369 = 6400777) B6400777
theorem B1579727 : Blo 1578487 1579727 := bstep (se 1 (by rfl) ⟨1184795, by rfl⟩ : syracuseStep 1579727 = 2369591) B2369591
theorem B8993855 : Blo 1578487 8993855 := bstep (se 1 (by rfl) ⟨6745391, by rfl⟩ : syracuseStep 8993855 = 13490783) B13490783
theorem B7691561 : Blo 1578487 7691561 := bstep (se 2 (by rfl) ⟨2884335, by rfl⟩ : syracuseStep 7691561 = 5768671) B5768671
theorem B3652985 : Blo 1578487 3652985 := bstep (se 2 (by rfl) ⟨1369869, by rfl⟩ : syracuseStep 3652985 = 2739739) B2739739
theorem B64830881 : Blo 1578487 64830881 := bstep (se 2 (by rfl) ⟨24311580, by rfl⟩ : syracuseStep 64830881 = 48623161) B48623161
theorem B6840055 : Blo 1578487 6840055 := bstep (se 1 (by rfl) ⟨5130041, by rfl⟩ : syracuseStep 6840055 = 10260083) B10260083
theorem B5062427 : Blo 1578487 5062427 := bstep (se 1 (by rfl) ⟨3796820, by rfl⟩ : syracuseStep 5062427 = 7593641) B7593641
theorem B8536271 : Blo 1578487 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B379404719 : Blo 1578487 379404719 := bstep (se 1 (by rfl) ⟨284553539, by rfl⟩ : syracuseStep 379404719 = 569107079) B569107079
theorem B48653095 : Blo 1578487 48653095 := bstep (se 1 (by rfl) ⟨36489821, by rfl⟩ : syracuseStep 48653095 = 72979643) B72979643
theorem B7996319 : Blo 1578487 7996319 := bstep (se 1 (by rfl) ⟨5997239, by rfl⟩ : syracuseStep 7996319 = 11994479) B11994479
theorem B22758317 : Blo 1578487 22758317 := bstep (se 3 (by rfl) ⟨4267184, by rfl⟩ : syracuseStep 22758317 = 8534369) B8534369
theorem B10118141 : Blo 1578487 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B41051357 : Blo 1578487 41051357 := bstep (se 3 (by rfl) ⟨7697129, by rfl⟩ : syracuseStep 41051357 = 15394259) B15394259
theorem B12813623 : Blo 1578487 12813623 := bstep (se 1 (by rfl) ⟨9610217, by rfl⟩ : syracuseStep 12813623 = 19220435) B19220435
theorem B2435323 : Blo 1578487 2435323 := bstep (se 1 (by rfl) ⟨1826492, by rfl⟩ : syracuseStep 2435323 = 3652985) B3652985
theorem B9120073 : Blo 1578487 9120073 := bstep (se 2 (by rfl) ⟨3420027, by rfl⟩ : syracuseStep 9120073 = 6840055) B6840055
theorem B5327855 : Blo 1578487 5327855 := bstep (se 1 (by rfl) ⟨3995891, by rfl⟩ : syracuseStep 5327855 = 7991783) B7991783
theorem B2370719 : Blo 1578487 2370719 := bstep (se 1 (by rfl) ⟨1778039, by rfl⟩ : syracuseStep 2370719 = 3556079) B3556079
theorem B11546335 : Blo 1578487 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B5329043 : Blo 1578487 5329043 := bstep (se 1 (by rfl) ⟨3996782, by rfl⟩ : syracuseStep 5329043 = 7993565) B7993565
theorem B20230843 : Blo 1578487 20230843 := bstep (se 1 (by rfl) ⟨15173132, by rfl⟩ : syracuseStep 20230843 = 30346265) B30346265
theorem B30348269 : Blo 1578487 30348269 := bstep (se 3 (by rfl) ⟨5690300, by rfl⟩ : syracuseStep 30348269 = 11380601) B11380601
theorem B45520217 : Blo 1578487 45520217 := bstep (se 2 (by rfl) ⟨17070081, by rfl⟩ : syracuseStep 45520217 = 34140163) B34140163
theorem B20239865 : Blo 1578487 20239865 := bstep (se 2 (by rfl) ⟨7589949, by rfl⟩ : syracuseStep 20239865 = 15179899) B15179899
theorem B1578523 : Blo 1578487 1578523 := bstep (se 1 (by rfl) ⟨1183892, by rfl⟩ : syracuseStep 1578523 = 2367785) B2367785
theorem B10122803 : Blo 1578487 10122803 := bstep (se 1 (by rfl) ⟨7592102, by rfl⟩ : syracuseStep 10122803 = 15184205) B15184205
theorem B6747887 : Blo 1578487 6747887 := bstep (se 1 (by rfl) ⟨5060915, by rfl⟩ : syracuseStep 6747887 = 10121831) B10121831
theorem B17086211 : Blo 1578487 17086211 := bstep (se 1 (by rfl) ⟨12814658, by rfl⟩ : syracuseStep 17086211 = 25629317) B25629317
theorem B1579035 : Blo 1578487 1579035 := bstep (se 1 (by rfl) ⟨1184276, by rfl⟩ : syracuseStep 1579035 = 2368553) B2368553
theorem B4561145 : Blo 1578487 4561145 := bstep (se 2 (by rfl) ⟨1710429, by rfl⟩ : syracuseStep 4561145 = 3420859) B3420859
theorem B1579259 : Blo 1578487 1579259 := bstep (se 1 (by rfl) ⟨1184444, by rfl⟩ : syracuseStep 1579259 = 2368889) B2368889
theorem B1579687 : Blo 1578487 1579687 := bstep (se 1 (by rfl) ⟨1184765, by rfl⟩ : syracuseStep 1579687 = 2369531) B2369531
theorem B5331851 : Blo 1578487 5331851 := bstep (se 1 (by rfl) ⟨3998888, by rfl⟩ : syracuseStep 5331851 = 7997777) B7997777
theorem B5995903 : Blo 1578487 5995903 := bstep (se 1 (by rfl) ⟨4496927, by rfl⟩ : syracuseStep 5995903 = 8993855) B8993855
theorem B1580443 : Blo 1578487 1580443 := bstep (se 1 (by rfl) ⟨1185332, by rfl⟩ : syracuseStep 1580443 = 2370665) B2370665
theorem B1580447 : Blo 1578487 1580447 := bstep (se 1 (by rfl) ⟨1185335, by rfl⟩ : syracuseStep 1580447 = 2370671) B2370671
theorem B5127707 : Blo 1578487 5127707 := bstep (se 1 (by rfl) ⟨3845780, by rfl⟩ : syracuseStep 5127707 = 7691561) B7691561
theorem B43220587 : Blo 1578487 43220587 := bstep (se 1 (by rfl) ⟨32415440, by rfl⟩ : syracuseStep 43220587 = 64830881) B64830881
theorem B5332607 : Blo 1578487 5332607 := bstep (se 1 (by rfl) ⟨3999455, by rfl⟩ : syracuseStep 5332607 = 7998911) B7998911
theorem B3374951 : Blo 1578487 3374951 := bstep (se 1 (by rfl) ⟨2531213, by rfl⟩ : syracuseStep 3374951 = 5062427) B5062427
theorem B252936479 : Blo 1578487 252936479 := bstep (se 1 (by rfl) ⟨189702359, by rfl⟩ : syracuseStep 252936479 = 379404719) B379404719
theorem B15172211 : Blo 1578487 15172211 := bstep (se 1 (by rfl) ⟨11379158, by rfl⟩ : syracuseStep 15172211 = 22758317) B22758317
theorem B13493243 : Blo 1578487 13493243 := bstep (se 1 (by rfl) ⟨10119932, by rfl⟩ : syracuseStep 13493243 = 20239865) B20239865
theorem B4498591 : Blo 1578487 4498591 := bstep (se 1 (by rfl) ⟨3373943, by rfl⟩ : syracuseStep 4498591 = 6747887) B6747887
theorem B3040763 : Blo 1578487 3040763 := bstep (se 1 (by rfl) ⟨2280572, by rfl⟩ : syracuseStep 3040763 = 4561145) B4561145
theorem B15395113 : Blo 1578487 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B3418471 : Blo 1578487 3418471 := bstep (se 1 (by rfl) ⟨2563853, by rfl⟩ : syracuseStep 3418471 = 5127707) B5127707
theorem B3247097 : Blo 1578487 3247097 := bstep (se 2 (by rfl) ⟨1217661, by rfl⟩ : syracuseStep 3247097 = 2435323) B2435323
theorem B12160097 : Blo 1578487 12160097 := bstep (se 2 (by rfl) ⟨4560036, by rfl⟩ : syracuseStep 12160097 = 9120073) B9120073
theorem B6745427 : Blo 1578487 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B30346811 : Blo 1578487 30346811 := bstep (se 1 (by rfl) ⟨22760108, by rfl⟩ : syracuseStep 30346811 = 45520217) B45520217
theorem B11390807 : Blo 1578487 11390807 := bstep (se 1 (by rfl) ⟨8543105, by rfl⟩ : syracuseStep 11390807 = 17086211) B17086211
theorem B3551903 : Blo 1578487 3551903 := bstep (se 1 (by rfl) ⟨2663927, by rfl⟩ : syracuseStep 3551903 = 5327855) B5327855
theorem B57627449 : Blo 1578487 57627449 := bstep (se 2 (by rfl) ⟨21610293, by rfl⟩ : syracuseStep 57627449 = 43220587) B43220587
theorem B8999869 : Blo 1578487 8999869 := bstep (se 3 (by rfl) ⟨1687475, by rfl⟩ : syracuseStep 8999869 = 3374951) B3374951
theorem B3552695 : Blo 1578487 3552695 := bstep (se 1 (by rfl) ⟨2664521, by rfl⟩ : syracuseStep 3552695 = 5329043) B5329043
theorem B5330879 : Blo 1578487 5330879 := bstep (se 1 (by rfl) ⟨3998159, by rfl⟩ : syracuseStep 5330879 = 7996319) B7996319
theorem B20232179 : Blo 1578487 20232179 := bstep (se 1 (by rfl) ⟨15174134, by rfl⟩ : syracuseStep 20232179 = 30348269) B30348269
theorem B27367571 : Blo 1578487 27367571 := bstep (se 1 (by rfl) ⟨20525678, by rfl⟩ : syracuseStep 27367571 = 41051357) B41051357
theorem B8542415 : Blo 1578487 8542415 := bstep (se 1 (by rfl) ⟨6406811, by rfl⟩ : syracuseStep 8542415 = 12813623) B12813623
theorem B26974457 : Blo 1578487 26974457 := bstep (se 2 (by rfl) ⟨10115421, by rfl⟩ : syracuseStep 26974457 = 20230843) B20230843
theorem B6748535 : Blo 1578487 6748535 := bstep (se 1 (by rfl) ⟨5061401, by rfl⟩ : syracuseStep 6748535 = 10122803) B10122803
theorem B64870793 : Blo 1578487 64870793 := bstep (se 2 (by rfl) ⟨24326547, by rfl⟩ : syracuseStep 64870793 = 48653095) B48653095
theorem B7994537 : Blo 1578487 7994537 := bstep (se 2 (by rfl) ⟨2997951, by rfl⟩ : syracuseStep 7994537 = 5995903) B5995903
theorem B3554567 : Blo 1578487 3554567 := bstep (se 1 (by rfl) ⟨2665925, by rfl⟩ : syracuseStep 3554567 = 5331851) B5331851
theorem B1580479 : Blo 1578487 1580479 := bstep (se 1 (by rfl) ⟨1185359, by rfl⟩ : syracuseStep 1580479 = 2370719) B2370719
theorem B91053557 : Blo 1578487 91053557 := bstep (se 5 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 91053557 = 8536271) B8536271
theorem B3555071 : Blo 1578487 3555071 := bstep (se 1 (by rfl) ⟨2666303, by rfl⟩ : syracuseStep 3555071 = 5332607) B5332607
theorem B168624319 : Blo 1578487 168624319 := bstep (se 1 (by rfl) ⟨126468239, by rfl⟩ : syracuseStep 168624319 = 252936479) B252936479
theorem B2367935 : Blo 1578487 2367935 := bstep (se 1 (by rfl) ⟨1775951, by rfl⟩ : syracuseStep 2367935 = 3551903) B3551903
theorem B8995495 : Blo 1578487 8995495 := bstep (se 1 (by rfl) ⟨6746621, by rfl⟩ : syracuseStep 8995495 = 13493243) B13493243
theorem B2368463 : Blo 1578487 2368463 := bstep (se 1 (by rfl) ⟨1776347, by rfl⟩ : syracuseStep 2368463 = 3552695) B3552695
theorem B5694943 : Blo 1578487 5694943 := bstep (se 1 (by rfl) ⟨4271207, by rfl⟩ : syracuseStep 5694943 = 8542415) B8542415
theorem B17982971 : Blo 1578487 17982971 := bstep (se 1 (by rfl) ⟨13487228, by rfl⟩ : syracuseStep 17982971 = 26974457) B26974457
theorem B5998121 : Blo 1578487 5998121 := bstep (se 2 (by rfl) ⟨2249295, by rfl⟩ : syracuseStep 5998121 = 4498591) B4498591
theorem B43247195 : Blo 1578487 43247195 := bstep (se 1 (by rfl) ⟨32435396, by rfl⟩ : syracuseStep 43247195 = 64870793) B64870793
theorem B2369711 : Blo 1578487 2369711 := bstep (se 1 (by rfl) ⟨1777283, by rfl⟩ : syracuseStep 2369711 = 3554567) B3554567
theorem B2370047 : Blo 1578487 2370047 := bstep (se 1 (by rfl) ⟨1777535, by rfl⟩ : syracuseStep 2370047 = 3555071) B3555071
theorem B32434805 : Blo 1578487 32434805 := bstep (se 5 (by rfl) ⟨1520381, by rfl⟩ : syracuseStep 32434805 = 3040763) B3040763
theorem B4557961 : Blo 1578487 4557961 := bstep (se 2 (by rfl) ⟨1709235, by rfl⟩ : syracuseStep 4557961 = 3418471) B3418471
theorem B13488119 : Blo 1578487 13488119 := bstep (se 1 (by rfl) ⟨10116089, by rfl⟩ : syracuseStep 13488119 = 20232179) B20232179
theorem B8106731 : Blo 1578487 8106731 := bstep (se 1 (by rfl) ⟨6080048, by rfl⟩ : syracuseStep 8106731 = 12160097) B12160097
theorem B5329691 : Blo 1578487 5329691 := bstep (se 1 (by rfl) ⟨3997268, by rfl⟩ : syracuseStep 5329691 = 7994537) B7994537
theorem B20231207 : Blo 1578487 20231207 := bstep (se 1 (by rfl) ⟨15173405, by rfl⟩ : syracuseStep 20231207 = 30346811) B30346811
theorem B72980189 : Blo 1578487 72980189 := bstep (se 3 (by rfl) ⟨13683785, by rfl⟩ : syracuseStep 72980189 = 27367571) B27367571
theorem B20526817 : Blo 1578487 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B10114807 : Blo 1578487 10114807 := bstep (se 1 (by rfl) ⟨7586105, by rfl⟩ : syracuseStep 10114807 = 15172211) B15172211
theorem B38418299 : Blo 1578487 38418299 := bstep (se 1 (by rfl) ⟨28813724, by rfl⟩ : syracuseStep 38418299 = 57627449) B57627449
theorem B17996093 : Blo 1578487 17996093 := bstep (se 3 (by rfl) ⟨3374267, by rfl⟩ : syracuseStep 17996093 = 6748535) B6748535
theorem B11999825 : Blo 1578487 11999825 := bstep (se 2 (by rfl) ⟨4499934, by rfl⟩ : syracuseStep 11999825 = 8999869) B8999869
theorem B3553919 : Blo 1578487 3553919 := bstep (se 1 (by rfl) ⟨2665439, by rfl⟩ : syracuseStep 3553919 = 5330879) B5330879
theorem B4496951 : Blo 1578487 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B30375485 : Blo 1578487 30375485 := bstep (se 3 (by rfl) ⟨5695403, by rfl⟩ : syracuseStep 30375485 = 11390807) B11390807
theorem B60702371 : Blo 1578487 60702371 := bstep (se 1 (by rfl) ⟨45526778, by rfl⟩ : syracuseStep 60702371 = 91053557) B91053557
theorem B34635701 : Blo 1578487 34635701 := bstep (se 5 (by rfl) ⟨1623548, by rfl⟩ : syracuseStep 34635701 = 3247097) B3247097
theorem B11993993 : Blo 1578487 11993993 := bstep (se 2 (by rfl) ⟨4497747, by rfl⟩ : syracuseStep 11993993 = 8995495) B8995495
theorem B3998747 : Blo 1578487 3998747 := bstep (se 1 (by rfl) ⟨2999060, by rfl⟩ : syracuseStep 3998747 = 5998121) B5998121
theorem B48653459 : Blo 1578487 48653459 := bstep (se 1 (by rfl) ⟨36490094, by rfl⟩ : syracuseStep 48653459 = 72980189) B72980189
theorem B2369279 : Blo 1578487 2369279 := bstep (se 1 (by rfl) ⟨1776959, by rfl⟩ : syracuseStep 2369279 = 3553919) B3553919
theorem B13486409 : Blo 1578487 13486409 := bstep (se 2 (by rfl) ⟨5057403, by rfl⟩ : syracuseStep 13486409 = 10114807) B10114807
theorem B224832425 : Blo 1578487 224832425 := bstep (se 2 (by rfl) ⟨84312159, by rfl⟩ : syracuseStep 224832425 = 168624319) B168624319
theorem B13487471 : Blo 1578487 13487471 := bstep (se 1 (by rfl) ⟨10115603, by rfl⟩ : syracuseStep 13487471 = 20231207) B20231207
theorem B11988647 : Blo 1578487 11988647 := bstep (se 1 (by rfl) ⟨8991485, by rfl⟩ : syracuseStep 11988647 = 17982971) B17982971
theorem B28831463 : Blo 1578487 28831463 := bstep (se 1 (by rfl) ⟨21623597, by rfl⟩ : syracuseStep 28831463 = 43247195) B43247195
theorem B25612199 : Blo 1578487 25612199 := bstep (se 1 (by rfl) ⟨19209149, by rfl⟩ : syracuseStep 25612199 = 38418299) B38418299
theorem B11997395 : Blo 1578487 11997395 := bstep (se 1 (by rfl) ⟨8998046, by rfl⟩ : syracuseStep 11997395 = 17996093) B17996093
theorem B7999883 : Blo 1578487 7999883 := bstep (se 1 (by rfl) ⟨5999912, by rfl⟩ : syracuseStep 7999883 = 11999825) B11999825
theorem B21623203 : Blo 1578487 21623203 := bstep (se 1 (by rfl) ⟨16217402, by rfl⟩ : syracuseStep 21623203 = 32434805) B32434805
theorem B23090467 : Blo 1578487 23090467 := bstep (se 1 (by rfl) ⟨17317850, by rfl⟩ : syracuseStep 23090467 = 34635701) B34635701
theorem B8992079 : Blo 1578487 8992079 := bstep (se 1 (by rfl) ⟨6744059, by rfl⟩ : syracuseStep 8992079 = 13488119) B13488119
theorem B1578623 : Blo 1578487 1578623 := bstep (se 1 (by rfl) ⟨1183967, by rfl⟩ : syracuseStep 1578623 = 2367935) B2367935
theorem B5404487 : Blo 1578487 5404487 := bstep (se 1 (by rfl) ⟨4053365, by rfl⟩ : syracuseStep 5404487 = 8106731) B8106731
theorem B3553127 : Blo 1578487 3553127 := bstep (se 1 (by rfl) ⟨2664845, by rfl⟩ : syracuseStep 3553127 = 5329691) B5329691
theorem B1578975 : Blo 1578487 1578975 := bstep (se 1 (by rfl) ⟨1184231, by rfl⟩ : syracuseStep 1578975 = 2368463) B2368463
theorem B1579807 : Blo 1578487 1579807 := bstep (se 1 (by rfl) ⟨1184855, by rfl⟩ : syracuseStep 1579807 = 2369711) B2369711
theorem B6077281 : Blo 1578487 6077281 := bstep (se 2 (by rfl) ⟨2278980, by rfl⟩ : syracuseStep 6077281 = 4557961) B4557961
theorem B1580031 : Blo 1578487 1580031 := bstep (se 1 (by rfl) ⟨1185023, by rfl⟩ : syracuseStep 1580031 = 2370047) B2370047
theorem B7593257 : Blo 1578487 7593257 := bstep (se 2 (by rfl) ⟨2847471, by rfl⟩ : syracuseStep 7593257 = 5694943) B5694943
theorem B27369089 : Blo 1578487 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B2997967 : Blo 1578487 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B20250323 : Blo 1578487 20250323 := bstep (se 1 (by rfl) ⟨15187742, by rfl⟩ : syracuseStep 20250323 = 30375485) B30375485
theorem B40468247 : Blo 1578487 40468247 := bstep (se 1 (by rfl) ⟨30351185, by rfl⟩ : syracuseStep 40468247 = 60702371) B60702371
theorem B5333255 : Blo 1578487 5333255 := bstep (se 1 (by rfl) ⟨3999941, by rfl⟩ : syracuseStep 5333255 = 7999883) B7999883
theorem B7995995 : Blo 1578487 7995995 := bstep (se 1 (by rfl) ⟨5996996, by rfl⟩ : syracuseStep 7995995 = 11993993) B11993993
theorem B57647861 : Blo 1578487 57647861 := bstep (se 5 (by rfl) ⟨2702243, by rfl⟩ : syracuseStep 57647861 = 5404487) B5404487
theorem B8103041 : Blo 1578487 8103041 := bstep (se 2 (by rfl) ⟨3038640, by rfl⟩ : syracuseStep 8103041 = 6077281) B6077281
theorem B2368751 : Blo 1578487 2368751 := bstep (se 1 (by rfl) ⟨1776563, by rfl⟩ : syracuseStep 2368751 = 3553127) B3553127
theorem B30787289 : Blo 1578487 30787289 := bstep (se 2 (by rfl) ⟨11545233, by rfl⟩ : syracuseStep 30787289 = 23090467) B23090467
theorem B18246059 : Blo 1578487 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B19220975 : Blo 1578487 19220975 := bstep (se 1 (by rfl) ⟨14415731, by rfl⟩ : syracuseStep 19220975 = 28831463) B28831463
theorem B26978831 : Blo 1578487 26978831 := bstep (se 1 (by rfl) ⟨20234123, by rfl⟩ : syracuseStep 26978831 = 40468247) B40468247
theorem B17074799 : Blo 1578487 17074799 := bstep (se 1 (by rfl) ⟨12806099, by rfl⟩ : syracuseStep 17074799 = 25612199) B25612199
theorem B7998263 : Blo 1578487 7998263 := bstep (se 1 (by rfl) ⟨5998697, by rfl⟩ : syracuseStep 7998263 = 11997395) B11997395
theorem B28830937 : Blo 1578487 28830937 := bstep (se 2 (by rfl) ⟨10811601, by rfl⟩ : syracuseStep 28830937 = 21623203) B21623203
theorem B2665831 : Blo 1578487 2665831 := bstep (se 1 (by rfl) ⟨1999373, by rfl⟩ : syracuseStep 2665831 = 3998747) B3998747
theorem B32435639 : Blo 1578487 32435639 := bstep (se 1 (by rfl) ⟨24326729, by rfl⟩ : syracuseStep 32435639 = 48653459) B48653459
theorem B8990939 : Blo 1578487 8990939 := bstep (se 1 (by rfl) ⟨6743204, by rfl⟩ : syracuseStep 8990939 = 13486409) B13486409
theorem B8991647 : Blo 1578487 8991647 := bstep (se 1 (by rfl) ⟨6743735, by rfl⟩ : syracuseStep 8991647 = 13487471) B13487471
theorem B599553133 : Blo 1578487 599553133 := bstep (se 3 (by rfl) ⟨112416212, by rfl⟩ : syracuseStep 599553133 = 224832425) B224832425
theorem B7992431 : Blo 1578487 7992431 := bstep (se 1 (by rfl) ⟨5994323, by rfl⟩ : syracuseStep 7992431 = 11988647) B11988647
theorem B5994719 : Blo 1578487 5994719 := bstep (se 1 (by rfl) ⟨4496039, by rfl⟩ : syracuseStep 5994719 = 8992079) B8992079
theorem B1579519 : Blo 1578487 1579519 := bstep (se 1 (by rfl) ⟨1184639, by rfl⟩ : syracuseStep 1579519 = 2369279) B2369279
theorem B5062171 : Blo 1578487 5062171 := bstep (se 1 (by rfl) ⟨3796628, by rfl⟩ : syracuseStep 5062171 = 7593257) B7593257
theorem B3997289 : Blo 1578487 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B13500215 : Blo 1578487 13500215 := bstep (se 1 (by rfl) ⟨10125161, by rfl⟩ : syracuseStep 13500215 = 20250323) B20250323
theorem B3555503 : Blo 1578487 3555503 := bstep (se 1 (by rfl) ⟨2666627, by rfl⟩ : syracuseStep 3555503 = 5333255) B5333255
theorem B3197616709 : Blo 1578487 3197616709 := bstep (se 4 (by rfl) ⟨299776566, by rfl⟩ : syracuseStep 3197616709 = 599553133) B599553133
theorem B12813983 : Blo 1578487 12813983 := bstep (se 1 (by rfl) ⟨9610487, by rfl⟩ : syracuseStep 12813983 = 19220975) B19220975
theorem B2664859 : Blo 1578487 2664859 := bstep (se 1 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 2664859 = 3997289) B3997289
theorem B38431907 : Blo 1578487 38431907 := bstep (se 1 (by rfl) ⟨28823930, by rfl⟩ : syracuseStep 38431907 = 57647861) B57647861
theorem B5328287 : Blo 1578487 5328287 := bstep (se 1 (by rfl) ⟨3996215, by rfl⟩ : syracuseStep 5328287 = 7992431) B7992431
theorem B5402027 : Blo 1578487 5402027 := bstep (se 1 (by rfl) ⟨4051520, by rfl⟩ : syracuseStep 5402027 = 8103041) B8103041
theorem B20524859 : Blo 1578487 20524859 := bstep (se 1 (by rfl) ⟨15393644, by rfl⟩ : syracuseStep 20524859 = 30787289) B30787289
theorem B38441249 : Blo 1578487 38441249 := bstep (se 2 (by rfl) ⟨14415468, by rfl⟩ : syracuseStep 38441249 = 28830937) B28830937
theorem B17985887 : Blo 1578487 17985887 := bstep (se 1 (by rfl) ⟨13489415, by rfl⟩ : syracuseStep 17985887 = 26978831) B26978831
theorem B11383199 : Blo 1578487 11383199 := bstep (se 1 (by rfl) ⟨8537399, by rfl⟩ : syracuseStep 11383199 = 17074799) B17074799
theorem B21623759 : Blo 1578487 21623759 := bstep (se 1 (by rfl) ⟨16217819, by rfl⟩ : syracuseStep 21623759 = 32435639) B32435639
theorem B9000143 : Blo 1578487 9000143 := bstep (se 1 (by rfl) ⟨6750107, by rfl⟩ : syracuseStep 9000143 = 13500215) B13500215
theorem B5993959 : Blo 1578487 5993959 := bstep (se 1 (by rfl) ⟨4495469, by rfl⟩ : syracuseStep 5993959 = 8990939) B8990939
theorem B5330663 : Blo 1578487 5330663 := bstep (se 1 (by rfl) ⟨3997997, by rfl⟩ : syracuseStep 5330663 = 7995995) B7995995
theorem B5994431 : Blo 1578487 5994431 := bstep (se 1 (by rfl) ⟨4495823, by rfl⟩ : syracuseStep 5994431 = 8991647) B8991647
theorem B1579167 : Blo 1578487 1579167 := bstep (se 1 (by rfl) ⟨1184375, by rfl⟩ : syracuseStep 1579167 = 2368751) B2368751
theorem B3996479 : Blo 1578487 3996479 := bstep (se 1 (by rfl) ⟨2997359, by rfl⟩ : syracuseStep 3996479 = 5994719) B5994719
theorem B12164039 : Blo 1578487 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B3554441 : Blo 1578487 3554441 := bstep (se 2 (by rfl) ⟨1332915, by rfl⟩ : syracuseStep 3554441 = 2665831) B2665831
theorem B5332175 : Blo 1578487 5332175 := bstep (se 1 (by rfl) ⟨3999131, by rfl⟩ : syracuseStep 5332175 = 7998263) B7998263
theorem B6749561 : Blo 1578487 6749561 := bstep (se 2 (by rfl) ⟨2531085, by rfl⟩ : syracuseStep 6749561 = 5062171) B5062171
theorem B2664319 : Blo 1578487 2664319 := bstep (se 1 (by rfl) ⟨1998239, by rfl⟩ : syracuseStep 2664319 = 3996479) B3996479
theorem B2369627 : Blo 1578487 2369627 := bstep (se 1 (by rfl) ⟨1777220, by rfl⟩ : syracuseStep 2369627 = 3554441) B3554441
theorem B4499707 : Blo 1578487 4499707 := bstep (se 1 (by rfl) ⟨3374780, by rfl⟩ : syracuseStep 4499707 = 6749561) B6749561
theorem B13683239 : Blo 1578487 13683239 := bstep (se 1 (by rfl) ⟨10262429, by rfl⟩ : syracuseStep 13683239 = 20524859) B20524859
theorem B2370335 : Blo 1578487 2370335 := bstep (se 1 (by rfl) ⟨1777751, by rfl⟩ : syracuseStep 2370335 = 3555503) B3555503
theorem B25627499 : Blo 1578487 25627499 := bstep (se 1 (by rfl) ⟨19220624, by rfl⟩ : syracuseStep 25627499 = 38441249) B38441249
theorem B7588799 : Blo 1578487 7588799 := bstep (se 1 (by rfl) ⟨5691599, by rfl⟩ : syracuseStep 7588799 = 11383199) B11383199
theorem B4263488945 : Blo 1578487 4263488945 := bstep (se 2 (by rfl) ⟨1598808354, by rfl⟩ : syracuseStep 4263488945 = 3197616709) B3197616709
theorem B6000095 : Blo 1578487 6000095 := bstep (se 1 (by rfl) ⟨4500071, by rfl⟩ : syracuseStep 6000095 = 9000143) B9000143
theorem B7991945 : Blo 1578487 7991945 := bstep (se 2 (by rfl) ⟨2996979, by rfl⟩ : syracuseStep 7991945 = 5993959) B5993959
theorem B25621271 : Blo 1578487 25621271 := bstep (se 1 (by rfl) ⟨19215953, by rfl⟩ : syracuseStep 25621271 = 38431907) B38431907
theorem B3552191 : Blo 1578487 3552191 := bstep (se 1 (by rfl) ⟨2664143, by rfl⟩ : syracuseStep 3552191 = 5328287) B5328287
theorem B3601351 : Blo 1578487 3601351 := bstep (se 1 (by rfl) ⟨2701013, by rfl⟩ : syracuseStep 3601351 = 5402027) B5402027
theorem B11990591 : Blo 1578487 11990591 := bstep (se 1 (by rfl) ⟨8992943, by rfl⟩ : syracuseStep 11990591 = 17985887) B17985887
theorem B3553145 : Blo 1578487 3553145 := bstep (se 2 (by rfl) ⟨1332429, by rfl⟩ : syracuseStep 3553145 = 2664859) B2664859
theorem B14415839 : Blo 1578487 14415839 := bstep (se 1 (by rfl) ⟨10811879, by rfl⟩ : syracuseStep 14415839 = 21623759) B21623759
theorem B8542655 : Blo 1578487 8542655 := bstep (se 1 (by rfl) ⟨6406991, by rfl⟩ : syracuseStep 8542655 = 12813983) B12813983
theorem B3553775 : Blo 1578487 3553775 := bstep (se 1 (by rfl) ⟨2665331, by rfl⟩ : syracuseStep 3553775 = 5330663) B5330663
theorem B3996287 : Blo 1578487 3996287 := bstep (se 1 (by rfl) ⟨2997215, by rfl⟩ : syracuseStep 3996287 = 5994431) B5994431
theorem B8109359 : Blo 1578487 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B3554783 : Blo 1578487 3554783 := bstep (se 1 (by rfl) ⟨2666087, by rfl⟩ : syracuseStep 3554783 = 5332175) B5332175
theorem B17080847 : Blo 1578487 17080847 := bstep (se 1 (by rfl) ⟨12810635, by rfl⟩ : syracuseStep 17080847 = 25621271) B25621271
theorem B2368127 : Blo 1578487 2368127 := bstep (se 1 (by rfl) ⟨1776095, by rfl⟩ : syracuseStep 2368127 = 3552191) B3552191
theorem B2368763 : Blo 1578487 2368763 := bstep (se 1 (by rfl) ⟨1776572, by rfl⟩ : syracuseStep 2368763 = 3553145) B3553145
theorem B9610559 : Blo 1578487 9610559 := bstep (se 1 (by rfl) ⟨7207919, by rfl⟩ : syracuseStep 9610559 = 14415839) B14415839
theorem B5695103 : Blo 1578487 5695103 := bstep (se 1 (by rfl) ⟨4271327, by rfl⟩ : syracuseStep 5695103 = 8542655) B8542655
theorem B2369183 : Blo 1578487 2369183 := bstep (se 1 (by rfl) ⟨1776887, by rfl⟩ : syracuseStep 2369183 = 3553775) B3553775
theorem B2664191 : Blo 1578487 2664191 := bstep (se 1 (by rfl) ⟨1998143, by rfl⟩ : syracuseStep 2664191 = 3996287) B3996287
theorem B2369855 : Blo 1578487 2369855 := bstep (se 1 (by rfl) ⟨1777391, by rfl⟩ : syracuseStep 2369855 = 3554783) B3554783
theorem B4000063 : Blo 1578487 4000063 := bstep (se 1 (by rfl) ⟨3000047, by rfl⟩ : syracuseStep 4000063 = 6000095) B6000095
theorem B5999609 : Blo 1578487 5999609 := bstep (se 2 (by rfl) ⟨2249853, by rfl⟩ : syracuseStep 5999609 = 4499707) B4499707
theorem B5327963 : Blo 1578487 5327963 := bstep (se 1 (by rfl) ⟨3995972, by rfl⟩ : syracuseStep 5327963 = 7991945) B7991945
theorem B9122159 : Blo 1578487 9122159 := bstep (se 1 (by rfl) ⟨6841619, by rfl⟩ : syracuseStep 9122159 = 13683239) B13683239
theorem B17084999 : Blo 1578487 17084999 := bstep (se 1 (by rfl) ⟨12813749, by rfl⟩ : syracuseStep 17084999 = 25627499) B25627499
theorem B5059199 : Blo 1578487 5059199 := bstep (se 1 (by rfl) ⟨3794399, by rfl⟩ : syracuseStep 5059199 = 7588799) B7588799
theorem B2842325963 : Blo 1578487 2842325963 := bstep (se 1 (by rfl) ⟨2131744472, by rfl⟩ : syracuseStep 2842325963 = 4263488945) B4263488945
theorem B19207205 : Blo 1578487 19207205 := bstep (se 4 (by rfl) ⟨1800675, by rfl⟩ : syracuseStep 19207205 = 3601351) B3601351
theorem B3552425 : Blo 1578487 3552425 := bstep (se 2 (by rfl) ⟨1332159, by rfl⟩ : syracuseStep 3552425 = 2664319) B2664319
theorem B7993727 : Blo 1578487 7993727 := bstep (se 1 (by rfl) ⟨5995295, by rfl⟩ : syracuseStep 7993727 = 11990591) B11990591
theorem B1579751 : Blo 1578487 1579751 := bstep (se 1 (by rfl) ⟨1184813, by rfl⟩ : syracuseStep 1579751 = 2369627) B2369627
theorem B1580223 : Blo 1578487 1580223 := bstep (se 1 (by rfl) ⟨1185167, by rfl⟩ : syracuseStep 1580223 = 2370335) B2370335
theorem B5406239 : Blo 1578487 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B11387231 : Blo 1578487 11387231 := bstep (se 1 (by rfl) ⟨8540423, by rfl⟩ : syracuseStep 11387231 = 17080847) B17080847
theorem B5333417 : Blo 1578487 5333417 := bstep (se 2 (by rfl) ⟨2000031, by rfl⟩ : syracuseStep 5333417 = 4000063) B4000063
theorem B1894883975 : Blo 1578487 1894883975 := bstep (se 1 (by rfl) ⟨1421162981, by rfl⟩ : syracuseStep 1894883975 = 2842325963) B2842325963
theorem B12804803 : Blo 1578487 12804803 := bstep (se 1 (by rfl) ⟨9603602, by rfl⟩ : syracuseStep 12804803 = 19207205) B19207205
theorem B2368283 : Blo 1578487 2368283 := bstep (se 1 (by rfl) ⟨1776212, by rfl⟩ : syracuseStep 2368283 = 3552425) B3552425
theorem B6407039 : Blo 1578487 6407039 := bstep (se 1 (by rfl) ⟨4805279, by rfl⟩ : syracuseStep 6407039 = 9610559) B9610559
theorem B3999739 : Blo 1578487 3999739 := bstep (se 1 (by rfl) ⟨2999804, by rfl⟩ : syracuseStep 3999739 = 5999609) B5999609
theorem B6081439 : Blo 1578487 6081439 := bstep (se 1 (by rfl) ⟨4561079, by rfl⟩ : syracuseStep 6081439 = 9122159) B9122159
theorem B11389999 : Blo 1578487 11389999 := bstep (se 1 (by rfl) ⟨8542499, by rfl⟩ : syracuseStep 11389999 = 17084999) B17084999
theorem B3796735 : Blo 1578487 3796735 := bstep (se 1 (by rfl) ⟨2847551, by rfl⟩ : syracuseStep 3796735 = 5695103) B5695103
theorem B5329151 : Blo 1578487 5329151 := bstep (se 1 (by rfl) ⟨3996863, by rfl⟩ : syracuseStep 5329151 = 7993727) B7993727
theorem B3551975 : Blo 1578487 3551975 := bstep (se 1 (by rfl) ⟨2663981, by rfl⟩ : syracuseStep 3551975 = 5327963) B5327963
theorem B1578751 : Blo 1578487 1578751 := bstep (se 1 (by rfl) ⟨1184063, by rfl⟩ : syracuseStep 1578751 = 2368127) B2368127
theorem B3372799 : Blo 1578487 3372799 := bstep (se 1 (by rfl) ⟨2529599, by rfl⟩ : syracuseStep 3372799 = 5059199) B5059199
theorem B1579175 : Blo 1578487 1579175 := bstep (se 1 (by rfl) ⟨1184381, by rfl⟩ : syracuseStep 1579175 = 2368763) B2368763
theorem B1579455 : Blo 1578487 1579455 := bstep (se 1 (by rfl) ⟨1184591, by rfl⟩ : syracuseStep 1579455 = 2369183) B2369183
theorem B1776127 : Blo 1578487 1776127 := bstep (se 1 (by rfl) ⟨1332095, by rfl⟩ : syracuseStep 1776127 = 2664191) B2664191
theorem B1579903 : Blo 1578487 1579903 := bstep (se 1 (by rfl) ⟨1184927, by rfl⟩ : syracuseStep 1579903 = 2369855) B2369855
theorem B3604159 : Blo 1578487 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B3555611 : Blo 1578487 3555611 := bstep (se 1 (by rfl) ⟨2666708, by rfl⟩ : syracuseStep 3555611 = 5333417) B5333417
theorem B1263255983 : Blo 1578487 1263255983 := bstep (se 1 (by rfl) ⟨947441987, by rfl⟩ : syracuseStep 1263255983 = 1894883975) B1894883975
theorem B8536535 : Blo 1578487 8536535 := bstep (se 1 (by rfl) ⟨6402401, by rfl⟩ : syracuseStep 8536535 = 12804803) B12804803
theorem B2367983 : Blo 1578487 2367983 := bstep (se 1 (by rfl) ⟨1775987, by rfl⟩ : syracuseStep 2367983 = 3551975) B3551975
theorem B2368169 : Blo 1578487 2368169 := bstep (se 2 (by rfl) ⟨888063, by rfl⟩ : syracuseStep 2368169 = 1776127) B1776127
theorem B5332985 : Blo 1578487 5332985 := bstep (se 2 (by rfl) ⟨1999869, by rfl⟩ : syracuseStep 5332985 = 3999739) B3999739
theorem B19222181 : Blo 1578487 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B17085437 : Blo 1578487 17085437 := bstep (se 3 (by rfl) ⟨3203519, by rfl⟩ : syracuseStep 17085437 = 6407039) B6407039
theorem B3552767 : Blo 1578487 3552767 := bstep (se 1 (by rfl) ⟨2664575, by rfl⟩ : syracuseStep 3552767 = 5329151) B5329151
theorem B7591487 : Blo 1578487 7591487 := bstep (se 1 (by rfl) ⟨5693615, by rfl⟩ : syracuseStep 7591487 = 11387231) B11387231
theorem B1578855 : Blo 1578487 1578855 := bstep (se 1 (by rfl) ⟨1184141, by rfl⟩ : syracuseStep 1578855 = 2368283) B2368283
theorem B8108585 : Blo 1578487 8108585 := bstep (se 2 (by rfl) ⟨3040719, by rfl⟩ : syracuseStep 8108585 = 6081439) B6081439
theorem B15186665 : Blo 1578487 15186665 := bstep (se 2 (by rfl) ⟨5694999, by rfl⟩ : syracuseStep 15186665 = 11389999) B11389999
theorem B4497065 : Blo 1578487 4497065 := bstep (se 2 (by rfl) ⟨1686399, by rfl⟩ : syracuseStep 4497065 = 3372799) B3372799
theorem B5062313 : Blo 1578487 5062313 := bstep (se 2 (by rfl) ⟨1898367, by rfl⟩ : syracuseStep 5062313 = 3796735) B3796735
theorem B842170655 : Blo 1578487 842170655 := bstep (se 1 (by rfl) ⟨631627991, by rfl⟩ : syracuseStep 842170655 = 1263255983) B1263255983
theorem B2368511 : Blo 1578487 2368511 := bstep (se 1 (by rfl) ⟨1776383, by rfl⟩ : syracuseStep 2368511 = 3552767) B3552767
theorem B20243965 : Blo 1578487 20243965 := bstep (se 3 (by rfl) ⟨3795743, by rfl⟩ : syracuseStep 20243965 = 7591487) B7591487
theorem B12814787 : Blo 1578487 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B2370407 : Blo 1578487 2370407 := bstep (se 1 (by rfl) ⟨1777805, by rfl⟩ : syracuseStep 2370407 = 3555611) B3555611
theorem B11390291 : Blo 1578487 11390291 := bstep (se 1 (by rfl) ⟨8542718, by rfl⟩ : syracuseStep 11390291 = 17085437) B17085437
theorem B5691023 : Blo 1578487 5691023 := bstep (se 1 (by rfl) ⟨4268267, by rfl⟩ : syracuseStep 5691023 = 8536535) B8536535
theorem B1578655 : Blo 1578487 1578655 := bstep (se 1 (by rfl) ⟨1183991, by rfl⟩ : syracuseStep 1578655 = 2367983) B2367983
theorem B1578779 : Blo 1578487 1578779 := bstep (se 1 (by rfl) ⟨1184084, by rfl⟩ : syracuseStep 1578779 = 2368169) B2368169
theorem B5405723 : Blo 1578487 5405723 := bstep (se 1 (by rfl) ⟨4054292, by rfl⟩ : syracuseStep 5405723 = 8108585) B8108585
theorem B10124443 : Blo 1578487 10124443 := bstep (se 1 (by rfl) ⟨7593332, by rfl⟩ : syracuseStep 10124443 = 15186665) B15186665
theorem B2998043 : Blo 1578487 2998043 := bstep (se 1 (by rfl) ⟨2248532, by rfl⟩ : syracuseStep 2998043 = 4497065) B4497065
theorem B3374875 : Blo 1578487 3374875 := bstep (se 1 (by rfl) ⟨2531156, by rfl⟩ : syracuseStep 3374875 = 5062313) B5062313
theorem B3555323 : Blo 1578487 3555323 := bstep (se 1 (by rfl) ⟨2666492, by rfl⟩ : syracuseStep 3555323 = 5332985) B5332985
theorem B2245788413 : Blo 1578487 2245788413 := bstep (se 3 (by rfl) ⟨421085327, by rfl⟩ : syracuseStep 2245788413 = 842170655) B842170655
theorem B3794015 : Blo 1578487 3794015 := bstep (se 1 (by rfl) ⟨2845511, by rfl⟩ : syracuseStep 3794015 = 5691023) B5691023
theorem B4499833 : Blo 1578487 4499833 := bstep (se 2 (by rfl) ⟨1687437, by rfl⟩ : syracuseStep 4499833 = 3374875) B3374875
theorem B2370215 : Blo 1578487 2370215 := bstep (se 1 (by rfl) ⟨1777661, by rfl⟩ : syracuseStep 2370215 = 3555323) B3555323
theorem B34172765 : Blo 1578487 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B1579007 : Blo 1578487 1579007 := bstep (se 1 (by rfl) ⟨1184255, by rfl⟩ : syracuseStep 1579007 = 2368511) B2368511
theorem B13499257 : Blo 1578487 13499257 := bstep (se 2 (by rfl) ⟨5062221, by rfl⟩ : syracuseStep 13499257 = 10124443) B10124443
theorem B1580271 : Blo 1578487 1580271 := bstep (se 1 (by rfl) ⟨1185203, by rfl⟩ : syracuseStep 1580271 = 2370407) B2370407
theorem B26991953 : Blo 1578487 26991953 := bstep (se 2 (by rfl) ⟨10121982, by rfl⟩ : syracuseStep 26991953 = 20243965) B20243965
theorem B3603815 : Blo 1578487 3603815 := bstep (se 1 (by rfl) ⟨2702861, by rfl⟩ : syracuseStep 3603815 = 5405723) B5405723
theorem B7593527 : Blo 1578487 7593527 := bstep (se 1 (by rfl) ⟨5695145, by rfl⟩ : syracuseStep 7593527 = 11390291) B11390291
theorem B1998695 : Blo 1578487 1998695 := bstep (se 1 (by rfl) ⟨1499021, by rfl⟩ : syracuseStep 1998695 = 2998043) B2998043
theorem B17999009 : Blo 1578487 17999009 := bstep (se 2 (by rfl) ⟨6749628, by rfl⟩ : syracuseStep 17999009 = 13499257) B13499257
theorem B2402543 : Blo 1578487 2402543 := bstep (se 1 (by rfl) ⟨1801907, by rfl⟩ : syracuseStep 2402543 = 3603815) B3603815
theorem B5999777 : Blo 1578487 5999777 := bstep (se 2 (by rfl) ⟨2249916, by rfl⟩ : syracuseStep 5999777 = 4499833) B4499833
theorem B17994635 : Blo 1578487 17994635 := bstep (se 1 (by rfl) ⟨13495976, by rfl⟩ : syracuseStep 17994635 = 26991953) B26991953
theorem B5329853 : Blo 1578487 5329853 := bstep (se 3 (by rfl) ⟨999347, by rfl⟩ : syracuseStep 5329853 = 1998695) B1998695
theorem B1497192275 : Blo 1578487 1497192275 := bstep (se 1 (by rfl) ⟨1122894206, by rfl⟩ : syracuseStep 1497192275 = 2245788413) B2245788413
theorem B2529343 : Blo 1578487 2529343 := bstep (se 1 (by rfl) ⟨1897007, by rfl⟩ : syracuseStep 2529343 = 3794015) B3794015
theorem B1580143 : Blo 1578487 1580143 := bstep (se 1 (by rfl) ⟨1185107, by rfl⟩ : syracuseStep 1580143 = 2370215) B2370215
theorem B5062351 : Blo 1578487 5062351 := bstep (se 1 (by rfl) ⟨3796763, by rfl⟩ : syracuseStep 5062351 = 7593527) B7593527
theorem B22781843 : Blo 1578487 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B3999851 : Blo 1578487 3999851 := bstep (se 1 (by rfl) ⟨2999888, by rfl⟩ : syracuseStep 3999851 = 5999777) B5999777
theorem B11996423 : Blo 1578487 11996423 := bstep (se 1 (by rfl) ⟨8997317, by rfl⟩ : syracuseStep 11996423 = 17994635) B17994635
theorem B1601695 : Blo 1578487 1601695 := bstep (se 1 (by rfl) ⟨1201271, by rfl⟩ : syracuseStep 1601695 = 2402543) B2402543
theorem B3372457 : Blo 1578487 3372457 := bstep (se 2 (by rfl) ⟨1264671, by rfl⟩ : syracuseStep 3372457 = 2529343) B2529343
theorem B3553235 : Blo 1578487 3553235 := bstep (se 1 (by rfl) ⟨2664926, by rfl⟩ : syracuseStep 3553235 = 5329853) B5329853
theorem B11999339 : Blo 1578487 11999339 := bstep (se 1 (by rfl) ⟨8999504, by rfl⟩ : syracuseStep 11999339 = 17999009) B17999009
theorem B998128183 : Blo 1578487 998128183 := bstep (se 1 (by rfl) ⟨748596137, by rfl⟩ : syracuseStep 998128183 = 1497192275) B1497192275
theorem B6749801 : Blo 1578487 6749801 := bstep (se 2 (by rfl) ⟨2531175, by rfl⟩ : syracuseStep 6749801 = 5062351) B5062351
theorem B15187895 : Blo 1578487 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B2368823 : Blo 1578487 2368823 := bstep (se 1 (by rfl) ⟨1776617, by rfl⟩ : syracuseStep 2368823 = 3553235) B3553235
theorem B7997615 : Blo 1578487 7997615 := bstep (se 1 (by rfl) ⟨5998211, by rfl⟩ : syracuseStep 7997615 = 11996423) B11996423
theorem B4499867 : Blo 1578487 4499867 := bstep (se 1 (by rfl) ⟨3374900, by rfl⟩ : syracuseStep 4499867 = 6749801) B6749801
theorem B7999559 : Blo 1578487 7999559 := bstep (se 1 (by rfl) ⟨5999669, by rfl⟩ : syracuseStep 7999559 = 11999339) B11999339
theorem B2666567 : Blo 1578487 2666567 := bstep (se 1 (by rfl) ⟨1999925, by rfl⟩ : syracuseStep 2666567 = 3999851) B3999851
theorem B2135593 : Blo 1578487 2135593 := bstep (se 2 (by rfl) ⟨800847, by rfl⟩ : syracuseStep 2135593 = 1601695) B1601695
theorem B1330837577 : Blo 1578487 1330837577 := bstep (se 2 (by rfl) ⟨499064091, by rfl⟩ : syracuseStep 1330837577 = 998128183) B998128183
theorem B4496609 : Blo 1578487 4496609 := bstep (se 2 (by rfl) ⟨1686228, by rfl⟩ : syracuseStep 4496609 = 3372457) B3372457
theorem B10125263 : Blo 1578487 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B5333039 : Blo 1578487 5333039 := bstep (se 1 (by rfl) ⟨3999779, by rfl⟩ : syracuseStep 5333039 = 7999559) B7999559
theorem B1777711 : Blo 1578487 1777711 := bstep (se 1 (by rfl) ⟨1333283, by rfl⟩ : syracuseStep 1777711 = 2666567) B2666567
theorem B2999911 : Blo 1578487 2999911 := bstep (se 1 (by rfl) ⟨2249933, by rfl⟩ : syracuseStep 2999911 = 4499867) B4499867
theorem B2847457 : Blo 1578487 2847457 := bstep (se 2 (by rfl) ⟨1067796, by rfl⟩ : syracuseStep 2847457 = 2135593) B2135593
theorem B1579215 : Blo 1578487 1579215 := bstep (se 1 (by rfl) ⟨1184411, by rfl⟩ : syracuseStep 1579215 = 2368823) B2368823
theorem B887225051 : Blo 1578487 887225051 := bstep (se 1 (by rfl) ⟨665418788, by rfl⟩ : syracuseStep 887225051 = 1330837577) B1330837577
theorem B5331743 : Blo 1578487 5331743 := bstep (se 1 (by rfl) ⟨3998807, by rfl⟩ : syracuseStep 5331743 = 7997615) B7997615
theorem B2997739 : Blo 1578487 2997739 := bstep (se 1 (by rfl) ⟨2248304, by rfl⟩ : syracuseStep 2997739 = 4496609) B4496609
theorem B27000701 : Blo 1578487 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B3555359 : Blo 1578487 3555359 := bstep (se 1 (by rfl) ⟨2666519, by rfl⟩ : syracuseStep 3555359 = 5333039) B5333039
theorem B3999881 : Blo 1578487 3999881 := bstep (se 2 (by rfl) ⟨1499955, by rfl⟩ : syracuseStep 3999881 = 2999911) B2999911
theorem B18000467 : Blo 1578487 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B2370281 : Blo 1578487 2370281 := bstep (se 2 (by rfl) ⟨888855, by rfl⟩ : syracuseStep 2370281 = 1777711) B1777711
theorem B591483367 : Blo 1578487 591483367 := bstep (se 1 (by rfl) ⟨443612525, by rfl⟩ : syracuseStep 591483367 = 887225051) B887225051
theorem B15186437 : Blo 1578487 15186437 := bstep (se 4 (by rfl) ⟨1423728, by rfl⟩ : syracuseStep 15186437 = 2847457) B2847457
theorem B3554495 : Blo 1578487 3554495 := bstep (se 1 (by rfl) ⟨2665871, by rfl⟩ : syracuseStep 3554495 = 5331743) B5331743
theorem B3996985 : Blo 1578487 3996985 := bstep (se 2 (by rfl) ⟨1498869, by rfl⟩ : syracuseStep 3996985 = 2997739) B2997739
theorem B2369663 : Blo 1578487 2369663 := bstep (se 1 (by rfl) ⟨1777247, by rfl⟩ : syracuseStep 2369663 = 3554495) B3554495
theorem B3154577957 : Blo 1578487 3154577957 := bstep (se 4 (by rfl) ⟨295741683, by rfl⟩ : syracuseStep 3154577957 = 591483367) B591483367
theorem B2370239 : Blo 1578487 2370239 := bstep (se 1 (by rfl) ⟨1777679, by rfl⟩ : syracuseStep 2370239 = 3555359) B3555359
theorem B2666587 : Blo 1578487 2666587 := bstep (se 1 (by rfl) ⟨1999940, by rfl⟩ : syracuseStep 2666587 = 3999881) B3999881
theorem B5329313 : Blo 1578487 5329313 := bstep (se 2 (by rfl) ⟨1998492, by rfl⟩ : syracuseStep 5329313 = 3996985) B3996985
theorem B10124291 : Blo 1578487 10124291 := bstep (se 1 (by rfl) ⟨7593218, by rfl⟩ : syracuseStep 10124291 = 15186437) B15186437
theorem B12000311 : Blo 1578487 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B1580187 : Blo 1578487 1580187 := bstep (se 1 (by rfl) ⟨1185140, by rfl⟩ : syracuseStep 1580187 = 2370281) B2370281
theorem B3555449 : Blo 1578487 3555449 := bstep (se 2 (by rfl) ⟨1333293, by rfl⟩ : syracuseStep 3555449 = 2666587) B2666587
theorem B2103051971 : Blo 1578487 2103051971 := bstep (se 1 (by rfl) ⟨1577288978, by rfl⟩ : syracuseStep 2103051971 = 3154577957) B3154577957
theorem B8000207 : Blo 1578487 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B3552875 : Blo 1578487 3552875 := bstep (se 1 (by rfl) ⟨2664656, by rfl⟩ : syracuseStep 3552875 = 5329313) B5329313
theorem B1579775 : Blo 1578487 1579775 := bstep (se 1 (by rfl) ⟨1184831, by rfl⟩ : syracuseStep 1579775 = 2369663) B2369663
theorem B1580159 : Blo 1578487 1580159 := bstep (se 1 (by rfl) ⟨1185119, by rfl⟩ : syracuseStep 1580159 = 2370239) B2370239
theorem B6749527 : Blo 1578487 6749527 := bstep (se 1 (by rfl) ⟨5062145, by rfl⟩ : syracuseStep 6749527 = 10124291) B10124291
theorem B5333471 : Blo 1578487 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B2368583 : Blo 1578487 2368583 := bstep (se 1 (by rfl) ⟨1776437, by rfl⟩ : syracuseStep 2368583 = 3552875) B3552875
theorem B5608138589 : Blo 1578487 5608138589 := bstep (se 3 (by rfl) ⟨1051525985, by rfl⟩ : syracuseStep 5608138589 = 2103051971) B2103051971
theorem B2370299 : Blo 1578487 2370299 := bstep (se 1 (by rfl) ⟨1777724, by rfl⟩ : syracuseStep 2370299 = 3555449) B3555449
theorem B8999369 : Blo 1578487 8999369 := bstep (se 2 (by rfl) ⟨3374763, by rfl⟩ : syracuseStep 8999369 = 6749527) B6749527
theorem B3555647 : Blo 1578487 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B5999579 : Blo 1578487 5999579 := bstep (se 1 (by rfl) ⟨4499684, by rfl⟩ : syracuseStep 5999579 = 8999369) B8999369
theorem B3738759059 : Blo 1578487 3738759059 := bstep (se 1 (by rfl) ⟨2804069294, by rfl⟩ : syracuseStep 3738759059 = 5608138589) B5608138589
theorem B1579055 : Blo 1578487 1579055 := bstep (se 1 (by rfl) ⟨1184291, by rfl⟩ : syracuseStep 1579055 = 2368583) B2368583
theorem B1580199 : Blo 1578487 1580199 := bstep (se 1 (by rfl) ⟨1185149, by rfl⟩ : syracuseStep 1580199 = 2370299) B2370299
theorem B3999719 : Blo 1578487 3999719 := bstep (se 1 (by rfl) ⟨2999789, by rfl⟩ : syracuseStep 3999719 = 5999579) B5999579
theorem B2370431 : Blo 1578487 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B2492506039 : Blo 1578487 2492506039 := bstep (se 1 (by rfl) ⟨1869379529, by rfl⟩ : syracuseStep 2492506039 = 3738759059) B3738759059
theorem B3323341385 : Blo 1578487 3323341385 := bstep (se 2 (by rfl) ⟨1246253019, by rfl⟩ : syracuseStep 3323341385 = 2492506039) B2492506039
theorem B2666479 : Blo 1578487 2666479 := bstep (se 1 (by rfl) ⟨1999859, by rfl⟩ : syracuseStep 2666479 = 3999719) B3999719
theorem B1580287 : Blo 1578487 1580287 := bstep (se 1 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 1580287 = 2370431) B2370431
theorem B2215560923 : Blo 1578487 2215560923 := bstep (se 1 (by rfl) ⟨1661670692, by rfl⟩ : syracuseStep 2215560923 = 3323341385) B3323341385
theorem B3555305 : Blo 1578487 3555305 := bstep (se 2 (by rfl) ⟨1333239, by rfl⟩ : syracuseStep 3555305 = 2666479) B2666479
theorem B2370203 : Blo 1578487 2370203 := bstep (se 1 (by rfl) ⟨1777652, by rfl⟩ : syracuseStep 2370203 = 3555305) B3555305
theorem B1477040615 : Blo 1578487 1477040615 := bstep (se 1 (by rfl) ⟨1107780461, by rfl⟩ : syracuseStep 1477040615 = 2215560923) B2215560923
theorem B984693743 : Blo 1578487 984693743 := bstep (se 1 (by rfl) ⟨738520307, by rfl⟩ : syracuseStep 984693743 = 1477040615) B1477040615
theorem B1580135 : Blo 1578487 1580135 := bstep (se 1 (by rfl) ⟨1185101, by rfl⟩ : syracuseStep 1580135 = 2370203) B2370203
theorem B656462495 : Blo 1578487 656462495 := bstep (se 1 (by rfl) ⟨492346871, by rfl⟩ : syracuseStep 656462495 = 984693743) B984693743
theorem B437641663 : Blo 1578487 437641663 := bstep (se 1 (by rfl) ⟨328231247, by rfl⟩ : syracuseStep 437641663 = 656462495) B656462495
theorem B583522217 : Blo 1578487 583522217 := bstep (se 2 (by rfl) ⟨218820831, by rfl⟩ : syracuseStep 583522217 = 437641663) B437641663
theorem B389014811 : Blo 1578487 389014811 := bstep (se 1 (by rfl) ⟨291761108, by rfl⟩ : syracuseStep 389014811 = 583522217) B583522217
theorem B259343207 : Blo 1578487 259343207 := bstep (se 1 (by rfl) ⟨194507405, by rfl⟩ : syracuseStep 259343207 = 389014811) B389014811
theorem B172895471 : Blo 1578487 172895471 := bstep (se 1 (by rfl) ⟨129671603, by rfl⟩ : syracuseStep 172895471 = 259343207) B259343207
theorem B115263647 : Blo 1578487 115263647 := bstep (se 1 (by rfl) ⟨86447735, by rfl⟩ : syracuseStep 115263647 = 172895471) B172895471
theorem B76842431 : Blo 1578487 76842431 := bstep (se 1 (by rfl) ⟨57631823, by rfl⟩ : syracuseStep 76842431 = 115263647) B115263647
theorem B51228287 : Blo 1578487 51228287 := bstep (se 1 (by rfl) ⟨38421215, by rfl⟩ : syracuseStep 51228287 = 76842431) B76842431
theorem B34152191 : Blo 1578487 34152191 := bstep (se 1 (by rfl) ⟨25614143, by rfl⟩ : syracuseStep 34152191 = 51228287) B51228287
theorem B22768127 : Blo 1578487 22768127 := bstep (se 1 (by rfl) ⟨17076095, by rfl⟩ : syracuseStep 22768127 = 34152191) B34152191
theorem B15178751 : Blo 1578487 15178751 := bstep (se 1 (by rfl) ⟨11384063, by rfl⟩ : syracuseStep 15178751 = 22768127) B22768127
theorem B10119167 : Blo 1578487 10119167 := bstep (se 1 (by rfl) ⟨7589375, by rfl⟩ : syracuseStep 10119167 = 15178751) B15178751
theorem B6746111 : Blo 1578487 6746111 := bstep (se 1 (by rfl) ⟨5059583, by rfl⟩ : syracuseStep 6746111 = 10119167) B10119167
theorem B4497407 : Blo 1578487 4497407 := bstep (se 1 (by rfl) ⟨3373055, by rfl⟩ : syracuseStep 4497407 = 6746111) B6746111
theorem B2998271 : Blo 1578487 2998271 := bstep (se 1 (by rfl) ⟨2248703, by rfl⟩ : syracuseStep 2998271 = 4497407) B4497407
theorem B1998847 : Blo 1578487 1998847 := bstep (se 1 (by rfl) ⟨1499135, by rfl⟩ : syracuseStep 1998847 = 2998271) B2998271
theorem B2665129 : Blo 1578487 2665129 := bstep (se 2 (by rfl) ⟨999423, by rfl⟩ : syracuseStep 2665129 = 1998847) B1998847
theorem B3553505 : Blo 1578487 3553505 := bstep (se 2 (by rfl) ⟨1332564, by rfl⟩ : syracuseStep 3553505 = 2665129) B2665129
theorem B2369003 : Blo 1578487 2369003 := bstep (se 1 (by rfl) ⟨1776752, by rfl⟩ : syracuseStep 2369003 = 3553505) B3553505
theorem B1579335 : Blo 1578487 1579335 := bstep (se 1 (by rfl) ⟨1184501, by rfl⟩ : syracuseStep 1579335 = 2369003) B2369003

theorem C0 (j : ℕ) (h1 : 394621 ≤ j) (h2 : j ≤ 395121) : Blo 1578487 (4 * j + 3) := by
  interval_cases j
  · exact B1578487
  · exact B1578491
  · exact B1578495
  · exact B1578499
  · exact B1578503
  · exact B1578507
  · exact B1578511
  · exact B1578515
  · exact B1578519
  · exact B1578523
  · exact B1578527
  · exact B1578531
  · exact B1578535
  · exact B1578539
  · exact B1578543
  · exact B1578547
  · exact B1578551
  · exact B1578555
  · exact B1578559
  · exact B1578563
  · exact B1578567
  · exact B1578571
  · exact B1578575
  · exact B1578579
  · exact B1578583
  · exact B1578587
  · exact B1578591
  · exact B1578595
  · exact B1578599
  · exact B1578603
  · exact B1578607
  · exact B1578611
  · exact B1578615
  · exact B1578619
  · exact B1578623
  · exact B1578627
  · exact B1578631
  · exact B1578635
  · exact B1578639
  · exact B1578643
  · exact B1578647
  · exact B1578651
  · exact B1578655
  · exact B1578659
  · exact B1578663
  · exact B1578667
  · exact B1578671
  · exact B1578675
  · exact B1578679
  · exact B1578683
  · exact B1578687
  · exact B1578691
  · exact B1578695
  · exact B1578699
  · exact B1578703
  · exact B1578707
  · exact B1578711
  · exact B1578715
  · exact B1578719
  · exact B1578723
  · exact B1578727
  · exact B1578731
  · exact B1578735
  · exact B1578739
  · exact B1578743
  · exact B1578747
  · exact B1578751
  · exact B1578755
  · exact B1578759
  · exact B1578763
  · exact B1578767
  · exact B1578771
  · exact B1578775
  · exact B1578779
  · exact B1578783
  · exact B1578787
  · exact B1578791
  · exact B1578795
  · exact B1578799
  · exact B1578803
  · exact B1578807
  · exact B1578811
  · exact B1578815
  · exact B1578819
  · exact B1578823
  · exact B1578827
  · exact B1578831
  · exact B1578835
  · exact B1578839
  · exact B1578843
  · exact B1578847
  · exact B1578851
  · exact B1578855
  · exact B1578859
  · exact B1578863
  · exact B1578867
  · exact B1578871
  · exact B1578875
  · exact B1578879
  · exact B1578883
  · exact B1578887
  · exact B1578891
  · exact B1578895
  · exact B1578899
  · exact B1578903
  · exact B1578907
  · exact B1578911
  · exact B1578915
  · exact B1578919
  · exact B1578923
  · exact B1578927
  · exact B1578931
  · exact B1578935
  · exact B1578939
  · exact B1578943
  · exact B1578947
  · exact B1578951
  · exact B1578955
  · exact B1578959
  · exact B1578963
  · exact B1578967
  · exact B1578971
  · exact B1578975
  · exact B1578979
  · exact B1578983
  · exact B1578987
  · exact B1578991
  · exact B1578995
  · exact B1578999
  · exact B1579003
  · exact B1579007
  · exact B1579011
  · exact B1579015
  · exact B1579019
  · exact B1579023
  · exact B1579027
  · exact B1579031
  · exact B1579035
  · exact B1579039
  · exact B1579043
  · exact B1579047
  · exact B1579051
  · exact B1579055
  · exact B1579059
  · exact B1579063
  · exact B1579067
  · exact B1579071
  · exact B1579075
  · exact B1579079
  · exact B1579083
  · exact B1579087
  · exact B1579091
  · exact B1579095
  · exact B1579099
  · exact B1579103
  · exact B1579107
  · exact B1579111
  · exact B1579115
  · exact B1579119
  · exact B1579123
  · exact B1579127
  · exact B1579131
  · exact B1579135
  · exact B1579139
  · exact B1579143
  · exact B1579147
  · exact B1579151
  · exact B1579155
  · exact B1579159
  · exact B1579163
  · exact B1579167
  · exact B1579171
  · exact B1579175
  · exact B1579179
  · exact B1579183
  · exact B1579187
  · exact B1579191
  · exact B1579195
  · exact B1579199
  · exact B1579203
  · exact B1579207
  · exact B1579211
  · exact B1579215
  · exact B1579219
  · exact B1579223
  · exact B1579227
  · exact B1579231
  · exact B1579235
  · exact B1579239
  · exact B1579243
  · exact B1579247
  · exact B1579251
  · exact B1579255
  · exact B1579259
  · exact B1579263
  · exact B1579267
  · exact B1579271
  · exact B1579275
  · exact B1579279
  · exact B1579283
  · exact B1579287
  · exact B1579291
  · exact B1579295
  · exact B1579299
  · exact B1579303
  · exact B1579307
  · exact B1579311
  · exact B1579315
  · exact B1579319
  · exact B1579323
  · exact B1579327
  · exact B1579331
  · exact B1579335
  · exact B1579339
  · exact B1579343
  · exact B1579347
  · exact B1579351
  · exact B1579355
  · exact B1579359
  · exact B1579363
  · exact B1579367
  · exact B1579371
  · exact B1579375
  · exact B1579379
  · exact B1579383
  · exact B1579387
  · exact B1579391
  · exact B1579395
  · exact B1579399
  · exact B1579403
  · exact B1579407
  · exact B1579411
  · exact B1579415
  · exact B1579419
  · exact B1579423
  · exact B1579427
  · exact B1579431
  · exact B1579435
  · exact B1579439
  · exact B1579443
  · exact B1579447
  · exact B1579451
  · exact B1579455
  · exact B1579459
  · exact B1579463
  · exact B1579467
  · exact B1579471
  · exact B1579475
  · exact B1579479
  · exact B1579483
  · exact B1579487
  · exact B1579491
  · exact B1579495
  · exact B1579499
  · exact B1579503
  · exact B1579507
  · exact B1579511
  · exact B1579515
  · exact B1579519
  · exact B1579523
  · exact B1579527
  · exact B1579531
  · exact B1579535
  · exact B1579539
  · exact B1579543
  · exact B1579547
  · exact B1579551
  · exact B1579555
  · exact B1579559
  · exact B1579563
  · exact B1579567
  · exact B1579571
  · exact B1579575
  · exact B1579579
  · exact B1579583
  · exact B1579587
  · exact B1579591
  · exact B1579595
  · exact B1579599
  · exact B1579603
  · exact B1579607
  · exact B1579611
  · exact B1579615
  · exact B1579619
  · exact B1579623
  · exact B1579627
  · exact B1579631
  · exact B1579635
  · exact B1579639
  · exact B1579643
  · exact B1579647
  · exact B1579651
  · exact B1579655
  · exact B1579659
  · exact B1579663
  · exact B1579667
  · exact B1579671
  · exact B1579675
  · exact B1579679
  · exact B1579683
  · exact B1579687
  · exact B1579691
  · exact B1579695
  · exact B1579699
  · exact B1579703
  · exact B1579707
  · exact B1579711
  · exact B1579715
  · exact B1579719
  · exact B1579723
  · exact B1579727
  · exact B1579731
  · exact B1579735
  · exact B1579739
  · exact B1579743
  · exact B1579747
  · exact B1579751
  · exact B1579755
  · exact B1579759
  · exact B1579763
  · exact B1579767
  · exact B1579771
  · exact B1579775
  · exact B1579779
  · exact B1579783
  · exact B1579787
  · exact B1579791
  · exact B1579795
  · exact B1579799
  · exact B1579803
  · exact B1579807
  · exact B1579811
  · exact B1579815
  · exact B1579819
  · exact B1579823
  · exact B1579827
  · exact B1579831
  · exact B1579835
  · exact B1579839
  · exact B1579843
  · exact B1579847
  · exact B1579851
  · exact B1579855
  · exact B1579859
  · exact B1579863
  · exact B1579867
  · exact B1579871
  · exact B1579875
  · exact B1579879
  · exact B1579883
  · exact B1579887
  · exact B1579891
  · exact B1579895
  · exact B1579899
  · exact B1579903
  · exact B1579907
  · exact B1579911
  · exact B1579915
  · exact B1579919
  · exact B1579923
  · exact B1579927
  · exact B1579931
  · exact B1579935
  · exact B1579939
  · exact B1579943
  · exact B1579947
  · exact B1579951
  · exact B1579955
  · exact B1579959
  · exact B1579963
  · exact B1579967
  · exact B1579971
  · exact B1579975
  · exact B1579979
  · exact B1579983
  · exact B1579987
  · exact B1579991
  · exact B1579995
  · exact B1579999
  · exact B1580003
  · exact B1580007
  · exact B1580011
  · exact B1580015
  · exact B1580019
  · exact B1580023
  · exact B1580027
  · exact B1580031
  · exact B1580035
  · exact B1580039
  · exact B1580043
  · exact B1580047
  · exact B1580051
  · exact B1580055
  · exact B1580059
  · exact B1580063
  · exact B1580067
  · exact B1580071
  · exact B1580075
  · exact B1580079
  · exact B1580083
  · exact B1580087
  · exact B1580091
  · exact B1580095
  · exact B1580099
  · exact B1580103
  · exact B1580107
  · exact B1580111
  · exact B1580115
  · exact B1580119
  · exact B1580123
  · exact B1580127
  · exact B1580131
  · exact B1580135
  · exact B1580139
  · exact B1580143
  · exact B1580147
  · exact B1580151
  · exact B1580155
  · exact B1580159
  · exact B1580163
  · exact B1580167
  · exact B1580171
  · exact B1580175
  · exact B1580179
  · exact B1580183
  · exact B1580187
  · exact B1580191
  · exact B1580195
  · exact B1580199
  · exact B1580203
  · exact B1580207
  · exact B1580211
  · exact B1580215
  · exact B1580219
  · exact B1580223
  · exact B1580227
  · exact B1580231
  · exact B1580235
  · exact B1580239
  · exact B1580243
  · exact B1580247
  · exact B1580251
  · exact B1580255
  · exact B1580259
  · exact B1580263
  · exact B1580267
  · exact B1580271
  · exact B1580275
  · exact B1580279
  · exact B1580283
  · exact B1580287
  · exact B1580291
  · exact B1580295
  · exact B1580299
  · exact B1580303
  · exact B1580307
  · exact B1580311
  · exact B1580315
  · exact B1580319
  · exact B1580323
  · exact B1580327
  · exact B1580331
  · exact B1580335
  · exact B1580339
  · exact B1580343
  · exact B1580347
  · exact B1580351
  · exact B1580355
  · exact B1580359
  · exact B1580363
  · exact B1580367
  · exact B1580371
  · exact B1580375
  · exact B1580379
  · exact B1580383
  · exact B1580387
  · exact B1580391
  · exact B1580395
  · exact B1580399
  · exact B1580403
  · exact B1580407
  · exact B1580411
  · exact B1580415
  · exact B1580419
  · exact B1580423
  · exact B1580427
  · exact B1580431
  · exact B1580435
  · exact B1580439
  · exact B1580443
  · exact B1580447
  · exact B1580451
  · exact B1580455
  · exact B1580459
  · exact B1580463
  · exact B1580467
  · exact B1580471
  · exact B1580475
  · exact B1580479
  · exact B1580483
  · exact B1580487

theorem solution (m : ℕ) (hlo : 1578487 ≤ m) (hhi : m ≤ 1580487) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 394621 ≤ j := by omega
    have hj2 : j ≤ 395121 := by omega
    have hb : Blo 1578487 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
