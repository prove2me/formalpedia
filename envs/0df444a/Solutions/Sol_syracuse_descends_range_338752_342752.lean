-- Prove2me | solution 1 for syracuse_descends_range_338752_342752
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:33.480583+00:00
-- url     : https://prove2.me/submissions/576827c1-3475-491b-b902-cf68890f08b2

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


theorem B819229 : Blo 338752 819229 := bbase (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) (by norm_num)
theorem B983125 : Blo 338752 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B1147013 : Blo 338752 1147013 := bbase (se 4 (by rfl) ⟨107532, by rfl⟩ : syracuseStep 1147013 = 215065) (by norm_num)
theorem B688493 : Blo 338752 688493 := bbase (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) (by norm_num)
theorem B1147445 : Blo 338752 1147445 := bbase (se 5 (by rfl) ⟨53786, by rfl⟩ : syracuseStep 1147445 = 107573) (by norm_num)
theorem B459389 : Blo 338752 459389 := bbase (se 3 (by rfl) ⟨86135, by rfl⟩ : syracuseStep 459389 = 172271) (by norm_num)
theorem B819845 : Blo 338752 819845 := bbase (se 4 (by rfl) ⟨76860, by rfl⟩ : syracuseStep 819845 = 153721) (by norm_num)
theorem B3277493 : Blo 338752 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B459541 : Blo 338752 459541 := bbase (se 6 (by rfl) ⟨10770, by rfl⟩ : syracuseStep 459541 = 21541) (by norm_num)
theorem B820037 : Blo 338752 820037 := bbase (se 4 (by rfl) ⟨76878, by rfl⟩ : syracuseStep 820037 = 153757) (by norm_num)
theorem B983909 : Blo 338752 983909 := bbase (se 4 (by rfl) ⟨92241, by rfl⟩ : syracuseStep 983909 = 184483) (by norm_num)
theorem B2327413 : Blo 338752 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B1147877 : Blo 338752 1147877 := bbase (se 4 (by rfl) ⟨107613, by rfl⟩ : syracuseStep 1147877 = 215227) (by norm_num)
theorem B525685 : Blo 338752 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B820613 : Blo 338752 820613 := bbase (se 4 (by rfl) ⟨76932, by rfl⟩ : syracuseStep 820613 = 153865) (by norm_num)
theorem B1148309 : Blo 338752 1148309 := bbase (se 6 (by rfl) ⟨26913, by rfl⟩ : syracuseStep 1148309 = 53827) (by norm_num)
theorem B361945 : Blo 338752 361945 := bbase (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) (by norm_num)
theorem B362017 : Blo 338752 362017 := bbase (se 2 (by rfl) ⟨135756, by rfl⟩ : syracuseStep 362017 = 271513) (by norm_num)
theorem B820997 : Blo 338752 820997 := bbase (se 4 (by rfl) ⟨76968, by rfl⟩ : syracuseStep 820997 = 153937) (by norm_num)
theorem B1148741 : Blo 338752 1148741 := bbase (se 4 (by rfl) ⟨107694, by rfl⟩ : syracuseStep 1148741 = 215389) (by norm_num)
theorem B362389 : Blo 338752 362389 := bbase (se 6 (by rfl) ⟨8493, by rfl⟩ : syracuseStep 362389 = 16987) (by norm_num)
theorem B1640341 : Blo 338752 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B395489 : Blo 338752 395489 := bbase (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) (by norm_num)
theorem B1149173 : Blo 338752 1149173 := bbase (se 5 (by rfl) ⟨53867, by rfl⟩ : syracuseStep 1149173 = 107735) (by norm_num)
theorem B362765 : Blo 338752 362765 := bbase (se 3 (by rfl) ⟨68018, by rfl⟩ : syracuseStep 362765 = 136037) (by norm_num)
theorem B362837 : Blo 338752 362837 := bbase (se 10 (by rfl) ⟨531, by rfl⟩ : syracuseStep 362837 = 1063) (by norm_num)
theorem B3705173 : Blo 338752 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B363025 : Blo 338752 363025 := bbase (se 2 (by rfl) ⟨136134, by rfl⟩ : syracuseStep 363025 = 272269) (by norm_num)
theorem B1149605 : Blo 338752 1149605 := bbase (se 4 (by rfl) ⟨107775, by rfl⟩ : syracuseStep 1149605 = 215551) (by norm_num)
theorem B363209 : Blo 338752 363209 := bbase (se 2 (by rfl) ⟨136203, by rfl⟩ : syracuseStep 363209 = 272407) (by norm_num)
theorem B428753 : Blo 338752 428753 := bbase (se 2 (by rfl) ⟨160782, by rfl⟩ : syracuseStep 428753 = 321565) (by norm_num)
theorem B428809 : Blo 338752 428809 := bbase (se 2 (by rfl) ⟨160803, by rfl⟩ : syracuseStep 428809 = 321607) (by norm_num)
theorem B428905 : Blo 338752 428905 := bbase (se 2 (by rfl) ⟨160839, by rfl⟩ : syracuseStep 428905 = 321679) (by norm_num)
theorem B723829 : Blo 338752 723829 := bbase (se 5 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 723829 = 67859) (by norm_num)
theorem B429077 : Blo 338752 429077 := bbase (se 6 (by rfl) ⟨10056, by rfl⟩ : syracuseStep 429077 = 20113) (by norm_num)
theorem B429133 : Blo 338752 429133 := bbase (se 3 (by rfl) ⟨80462, by rfl⟩ : syracuseStep 429133 = 160925) (by norm_num)
theorem B1150037 : Blo 338752 1150037 := bbase (se 8 (by rfl) ⟨6738, by rfl⟩ : syracuseStep 1150037 = 13477) (by norm_num)
theorem B2919509 : Blo 338752 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B429229 : Blo 338752 429229 := bbase (se 3 (by rfl) ⟨80480, by rfl⟩ : syracuseStep 429229 = 160961) (by norm_num)
theorem B691517 : Blo 338752 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B429401 : Blo 338752 429401 := bbase (se 2 (by rfl) ⟨161025, by rfl⟩ : syracuseStep 429401 = 322051) (by norm_num)
theorem B429457 : Blo 338752 429457 := bbase (se 2 (by rfl) ⟨161046, by rfl⟩ : syracuseStep 429457 = 322093) (by norm_num)
theorem B363961 : Blo 338752 363961 := bbase (se 2 (by rfl) ⟨136485, by rfl⟩ : syracuseStep 363961 = 272971) (by norm_num)
theorem B822757 : Blo 338752 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B429553 : Blo 338752 429553 := bbase (se 2 (by rfl) ⟨161082, by rfl⟩ : syracuseStep 429553 = 322165) (by norm_num)
theorem B364033 : Blo 338752 364033 := bbase (se 2 (by rfl) ⟨136512, by rfl⟩ : syracuseStep 364033 = 273025) (by norm_num)
theorem B1150469 : Blo 338752 1150469 := bbase (se 4 (by rfl) ⟨107856, by rfl⟩ : syracuseStep 1150469 = 215713) (by norm_num)
theorem B527885 : Blo 338752 527885 := bbase (se 3 (by rfl) ⟨98978, by rfl⟩ : syracuseStep 527885 = 197957) (by norm_num)
theorem B1183301 : Blo 338752 1183301 := bbase (se 4 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 1183301 = 221869) (by norm_num)
theorem B429725 : Blo 338752 429725 := bbase (se 3 (by rfl) ⟨80573, by rfl⟩ : syracuseStep 429725 = 161147) (by norm_num)
theorem B364213 : Blo 338752 364213 := bbase (se 5 (by rfl) ⟨17072, by rfl⟩ : syracuseStep 364213 = 34145) (by norm_num)
theorem B429781 : Blo 338752 429781 := bbase (se 7 (by rfl) ⟨5036, by rfl⟩ : syracuseStep 429781 = 10073) (by norm_num)
theorem B724717 : Blo 338752 724717 := bbase (se 3 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 724717 = 271769) (by norm_num)
theorem B429877 : Blo 338752 429877 := bbase (se 5 (by rfl) ⟨20150, by rfl⟩ : syracuseStep 429877 = 40301) (by norm_num)
theorem B1740613 : Blo 338752 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B1576853 : Blo 338752 1576853 := bbase (se 6 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 1576853 = 73915) (by norm_num)
theorem B1150901 : Blo 338752 1150901 := bbase (se 5 (by rfl) ⟨53948, by rfl⟩ : syracuseStep 1150901 = 107897) (by norm_num)
theorem B430049 : Blo 338752 430049 := bbase (se 2 (by rfl) ⟨161268, by rfl⟩ : syracuseStep 430049 = 322537) (by norm_num)
theorem B430105 : Blo 338752 430105 := bbase (se 2 (by rfl) ⟨161289, by rfl⟩ : syracuseStep 430105 = 322579) (by norm_num)
theorem B364657 : Blo 338752 364657 := bbase (se 2 (by rfl) ⟨136746, by rfl⟩ : syracuseStep 364657 = 273493) (by norm_num)
theorem B430201 : Blo 338752 430201 := bbase (se 2 (by rfl) ⟨161325, by rfl⟩ : syracuseStep 430201 = 322651) (by norm_num)
theorem B725213 : Blo 338752 725213 := bbase (se 3 (by rfl) ⟨135977, by rfl⟩ : syracuseStep 725213 = 271955) (by norm_num)
theorem B364781 : Blo 338752 364781 := bbase (se 3 (by rfl) ⟨68396, by rfl⟩ : syracuseStep 364781 = 136793) (by norm_num)
theorem B1970453 : Blo 338752 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B430373 : Blo 338752 430373 := bbase (se 4 (by rfl) ⟨40347, by rfl⟩ : syracuseStep 430373 = 80695) (by norm_num)
theorem B430429 : Blo 338752 430429 := bbase (se 3 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 430429 = 161411) (by norm_num)
theorem B1151333 : Blo 338752 1151333 := bbase (se 4 (by rfl) ⟨107937, by rfl⟩ : syracuseStep 1151333 = 215875) (by norm_num)
theorem B1315237 : Blo 338752 1315237 := bbase (se 4 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 1315237 = 246607) (by norm_num)
theorem B430525 : Blo 338752 430525 := bbase (se 3 (by rfl) ⟨80723, by rfl⟩ : syracuseStep 430525 = 161447) (by norm_num)
theorem B365033 : Blo 338752 365033 := bbase (se 2 (by rfl) ⟨136887, by rfl⟩ : syracuseStep 365033 = 273775) (by norm_num)
theorem B430697 : Blo 338752 430697 := bbase (se 2 (by rfl) ⟨161511, by rfl⟩ : syracuseStep 430697 = 323023) (by norm_num)
theorem B430753 : Blo 338752 430753 := bbase (se 2 (by rfl) ⟨161532, by rfl⟩ : syracuseStep 430753 = 323065) (by norm_num)
theorem B430849 : Blo 338752 430849 := bbase (se 2 (by rfl) ⟨161568, by rfl⟩ : syracuseStep 430849 = 323137) (by norm_num)
theorem B1151765 : Blo 338752 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B398233 : Blo 338752 398233 := bbase (se 2 (by rfl) ⟨149337, by rfl⟩ : syracuseStep 398233 = 298675) (by norm_num)
theorem B365477 : Blo 338752 365477 := bbase (se 4 (by rfl) ⟨34263, by rfl⟩ : syracuseStep 365477 = 68527) (by norm_num)
theorem B431021 : Blo 338752 431021 := bbase (se 3 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 431021 = 161633) (by norm_num)
theorem B431077 : Blo 338752 431077 := bbase (se 4 (by rfl) ⟨40413, by rfl⟩ : syracuseStep 431077 = 80827) (by norm_num)
theorem B2593781 : Blo 338752 2593781 := bbase (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) (by norm_num)
theorem B726077 : Blo 338752 726077 := bbase (se 3 (by rfl) ⟨136139, by rfl⟩ : syracuseStep 726077 = 272279) (by norm_num)
theorem B431173 : Blo 338752 431173 := bbase (se 4 (by rfl) ⟨40422, by rfl⟩ : syracuseStep 431173 = 80845) (by norm_num)
theorem B1381445 : Blo 338752 1381445 := bbase (se 4 (by rfl) ⟨129510, by rfl⟩ : syracuseStep 1381445 = 259021) (by norm_num)
theorem B365725 : Blo 338752 365725 := bbase (se 3 (by rfl) ⟨68573, by rfl⟩ : syracuseStep 365725 = 137147) (by norm_num)
theorem B1152197 : Blo 338752 1152197 := bbase (se 4 (by rfl) ⟨108018, by rfl⟩ : syracuseStep 1152197 = 216037) (by norm_num)
theorem B726221 : Blo 338752 726221 := bbase (se 3 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 726221 = 272333) (by norm_num)
theorem B431345 : Blo 338752 431345 := bbase (se 2 (by rfl) ⟨161754, by rfl⟩ : syracuseStep 431345 = 323509) (by norm_num)
theorem B431401 : Blo 338752 431401 := bbase (se 2 (by rfl) ⟨161775, by rfl⟩ : syracuseStep 431401 = 323551) (by norm_num)
theorem B1086821 : Blo 338752 1086821 := bbase (se 4 (by rfl) ⟨101889, by rfl⟩ : syracuseStep 1086821 = 203779) (by norm_num)
theorem B431497 : Blo 338752 431497 := bbase (se 2 (by rfl) ⟨161811, by rfl⟩ : syracuseStep 431497 = 323623) (by norm_num)
theorem B431669 : Blo 338752 431669 := bbase (se 5 (by rfl) ⟨20234, by rfl⟩ : syracuseStep 431669 = 40469) (by norm_num)
theorem B693821 : Blo 338752 693821 := bbase (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) (by norm_num)
theorem B431725 : Blo 338752 431725 := bbase (se 3 (by rfl) ⟨80948, by rfl⟩ : syracuseStep 431725 = 161897) (by norm_num)
theorem B1152629 : Blo 338752 1152629 := bbase (se 5 (by rfl) ⟨54029, by rfl⟩ : syracuseStep 1152629 = 108059) (by norm_num)
theorem B857749 : Blo 338752 857749 := bbase (se 6 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 857749 = 40207) (by norm_num)
theorem B431821 : Blo 338752 431821 := bbase (se 3 (by rfl) ⟨80966, by rfl⟩ : syracuseStep 431821 = 161933) (by norm_num)
theorem B857861 : Blo 338752 857861 := bbase (se 4 (by rfl) ⟨80424, by rfl⟩ : syracuseStep 857861 = 160849) (by norm_num)
theorem B431993 : Blo 338752 431993 := bbase (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) (by norm_num)
theorem B432049 : Blo 338752 432049 := bbase (se 2 (by rfl) ⟨162018, by rfl⟩ : syracuseStep 432049 = 324037) (by norm_num)
theorem B726965 : Blo 338752 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B858053 : Blo 338752 858053 := bbase (se 4 (by rfl) ⟨80442, by rfl⟩ : syracuseStep 858053 = 160885) (by norm_num)
theorem B13277141 : Blo 338752 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B1644533 : Blo 338752 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B432145 : Blo 338752 432145 := bbase (se 2 (by rfl) ⟨162054, by rfl⟩ : syracuseStep 432145 = 324109) (by norm_num)
theorem B1153061 : Blo 338752 1153061 := bbase (se 4 (by rfl) ⟨108099, by rfl⟩ : syracuseStep 1153061 = 216199) (by norm_num)
theorem B1087589 : Blo 338752 1087589 := bbase (se 4 (by rfl) ⟨101961, by rfl⟩ : syracuseStep 1087589 = 203923) (by norm_num)
theorem B432317 : Blo 338752 432317 := bbase (se 3 (by rfl) ⟨81059, by rfl⟩ : syracuseStep 432317 = 162119) (by norm_num)
theorem B432373 : Blo 338752 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B1939733 : Blo 338752 1939733 := bbase (se 6 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 1939733 = 90925) (by norm_num)
theorem B858397 : Blo 338752 858397 := bbase (se 3 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 858397 = 321899) (by norm_num)
theorem B432469 : Blo 338752 432469 := bbase (se 10 (by rfl) ⟨633, by rfl⟩ : syracuseStep 432469 = 1267) (by norm_num)
theorem B858509 : Blo 338752 858509 := bbase (se 3 (by rfl) ⟨160970, by rfl⟩ : syracuseStep 858509 = 321941) (by norm_num)
theorem B1153493 : Blo 338752 1153493 := bbase (se 7 (by rfl) ⟨13517, by rfl⟩ : syracuseStep 1153493 = 27035) (by norm_num)
theorem B432641 : Blo 338752 432641 := bbase (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) (by norm_num)
theorem B1546789 : Blo 338752 1546789 := bbase (se 4 (by rfl) ⟨145011, by rfl⟩ : syracuseStep 1546789 = 290023) (by norm_num)
theorem B432697 : Blo 338752 432697 := bbase (se 2 (by rfl) ⟨162261, by rfl⟩ : syracuseStep 432697 = 324523) (by norm_num)
theorem B858701 : Blo 338752 858701 := bbase (se 3 (by rfl) ⟨161006, by rfl⟩ : syracuseStep 858701 = 322013) (by norm_num)
theorem B1088101 : Blo 338752 1088101 := bbase (se 4 (by rfl) ⟨102009, by rfl⟩ : syracuseStep 1088101 = 204019) (by norm_num)
theorem B432793 : Blo 338752 432793 := bbase (se 2 (by rfl) ⟨162297, by rfl⟩ : syracuseStep 432793 = 324595) (by norm_num)
theorem B727717 : Blo 338752 727717 := bbase (se 4 (by rfl) ⟨68223, by rfl⟩ : syracuseStep 727717 = 136447) (by norm_num)
theorem B3480245 : Blo 338752 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B727861 : Blo 338752 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B432965 : Blo 338752 432965 := bbase (se 4 (by rfl) ⟨40590, by rfl⟩ : syracuseStep 432965 = 81181) (by norm_num)
theorem B433021 : Blo 338752 433021 := bbase (se 3 (by rfl) ⟨81191, by rfl⟩ : syracuseStep 433021 = 162383) (by norm_num)
theorem B1153925 : Blo 338752 1153925 := bbase (se 4 (by rfl) ⟨108180, by rfl⟩ : syracuseStep 1153925 = 216361) (by norm_num)
theorem B859045 : Blo 338752 859045 := bbase (se 4 (by rfl) ⟨80535, by rfl⟩ : syracuseStep 859045 = 161071) (by norm_num)
theorem B433117 : Blo 338752 433117 := bbase (se 3 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 433117 = 162419) (by norm_num)
theorem B859157 : Blo 338752 859157 := bbase (se 6 (by rfl) ⟨20136, by rfl⟩ : syracuseStep 859157 = 40273) (by norm_num)
theorem B433289 : Blo 338752 433289 := bbase (se 2 (by rfl) ⟨162483, by rfl⟩ : syracuseStep 433289 = 324967) (by norm_num)
theorem B728237 : Blo 338752 728237 := bbase (se 3 (by rfl) ⟨136544, by rfl⟩ : syracuseStep 728237 = 273089) (by norm_num)
theorem B433345 : Blo 338752 433345 := bbase (se 2 (by rfl) ⟨162504, by rfl⟩ : syracuseStep 433345 = 325009) (by norm_num)
theorem B859349 : Blo 338752 859349 := bbase (se 7 (by rfl) ⟨10070, by rfl⟩ : syracuseStep 859349 = 20141) (by norm_num)
theorem B433441 : Blo 338752 433441 := bbase (se 2 (by rfl) ⟨162540, by rfl⟩ : syracuseStep 433441 = 325081) (by norm_num)
theorem B1154357 : Blo 338752 1154357 := bbase (se 5 (by rfl) ⟨54110, by rfl⟩ : syracuseStep 1154357 = 108221) (by norm_num)
theorem B433613 : Blo 338752 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B2334197 : Blo 338752 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B433669 : Blo 338752 433669 := bbase (se 4 (by rfl) ⟨40656, by rfl⟩ : syracuseStep 433669 = 81313) (by norm_num)
theorem B3317269 : Blo 338752 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B728605 : Blo 338752 728605 := bbase (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) (by norm_num)
theorem B859693 : Blo 338752 859693 := bbase (se 3 (by rfl) ⟨161192, by rfl⟩ : syracuseStep 859693 = 322385) (by norm_num)
theorem B433765 : Blo 338752 433765 := bbase (se 4 (by rfl) ⟨40665, by rfl⟩ : syracuseStep 433765 = 81331) (by norm_num)
theorem B368269 : Blo 338752 368269 := bbase (se 3 (by rfl) ⟨69050, by rfl⟩ : syracuseStep 368269 = 138101) (by norm_num)
theorem B859805 : Blo 338752 859805 := bbase (se 3 (by rfl) ⟨161213, by rfl⟩ : syracuseStep 859805 = 322427) (by norm_num)
theorem B1154789 : Blo 338752 1154789 := bbase (se 4 (by rfl) ⟨108261, by rfl⟩ : syracuseStep 1154789 = 216523) (by norm_num)
theorem B2072309 : Blo 338752 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B859997 : Blo 338752 859997 := bbase (se 3 (by rfl) ⟨161249, by rfl⟩ : syracuseStep 859997 = 322499) (by norm_num)
theorem B1449845 : Blo 338752 1449845 := bbase (se 5 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 1449845 = 135923) (by norm_num)
theorem B368533 : Blo 338752 368533 := bbase (se 6 (by rfl) ⟨8637, by rfl⟩ : syracuseStep 368533 = 17275) (by norm_num)
theorem B2957269 : Blo 338752 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B7610453 : Blo 338752 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1155221 : Blo 338752 1155221 := bbase (se 6 (by rfl) ⟨27075, by rfl⟩ : syracuseStep 1155221 = 54151) (by norm_num)
theorem B860341 : Blo 338752 860341 := bbase (se 5 (by rfl) ⟨40328, by rfl⟩ : syracuseStep 860341 = 80657) (by norm_num)
theorem B860453 : Blo 338752 860453 := bbase (se 4 (by rfl) ⟨80667, by rfl⟩ : syracuseStep 860453 = 161335) (by norm_num)
theorem B1089845 : Blo 338752 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B762245 : Blo 338752 762245 := bbase (se 4 (by rfl) ⟨71460, by rfl⟩ : syracuseStep 762245 = 142921) (by norm_num)
theorem B1286549 : Blo 338752 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B762317 : Blo 338752 762317 := bbase (se 3 (by rfl) ⟨142934, by rfl⟩ : syracuseStep 762317 = 285869) (by norm_num)
theorem B860645 : Blo 338752 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B434665 : Blo 338752 434665 := bbase (se 2 (by rfl) ⟨162999, by rfl⟩ : syracuseStep 434665 = 325999) (by norm_num)
theorem B1090037 : Blo 338752 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B762389 : Blo 338752 762389 := bbase (se 6 (by rfl) ⟨17868, by rfl⟩ : syracuseStep 762389 = 35737) (by norm_num)
theorem B1155653 : Blo 338752 1155653 := bbase (se 4 (by rfl) ⟨108342, by rfl⟩ : syracuseStep 1155653 = 216685) (by norm_num)
theorem B762461 : Blo 338752 762461 := bbase (se 3 (by rfl) ⟨142961, by rfl⟩ : syracuseStep 762461 = 285923) (by norm_num)
theorem B762533 : Blo 338752 762533 := bbase (se 4 (by rfl) ⟨71487, by rfl⟩ : syracuseStep 762533 = 142975) (by norm_num)
theorem B1286837 : Blo 338752 1286837 := bbase (se 5 (by rfl) ⟨60320, by rfl⟩ : syracuseStep 1286837 = 120641) (by norm_num)
theorem B2761397 : Blo 338752 2761397 := bbase (se 5 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 2761397 = 258881) (by norm_num)
theorem B762605 : Blo 338752 762605 := bbase (se 3 (by rfl) ⟨142988, by rfl⟩ : syracuseStep 762605 = 285977) (by norm_num)
theorem B762677 : Blo 338752 762677 := bbase (se 5 (by rfl) ⟨35750, by rfl⟩ : syracuseStep 762677 = 71501) (by norm_num)
theorem B860989 : Blo 338752 860989 := bbase (se 3 (by rfl) ⟨161435, by rfl⟩ : syracuseStep 860989 = 322871) (by norm_num)
theorem B762749 : Blo 338752 762749 := bbase (se 3 (by rfl) ⟨143015, by rfl⟩ : syracuseStep 762749 = 286031) (by norm_num)
theorem B664453 : Blo 338752 664453 := bbase (se 4 (by rfl) ⟨62292, by rfl⟩ : syracuseStep 664453 = 124585) (by norm_num)
theorem B861101 : Blo 338752 861101 := bbase (se 3 (by rfl) ⟨161456, by rfl⟩ : syracuseStep 861101 = 322913) (by norm_num)
theorem B762821 : Blo 338752 762821 := bbase (se 4 (by rfl) ⟨71514, by rfl⟩ : syracuseStep 762821 = 143029) (by norm_num)
theorem B1156085 : Blo 338752 1156085 := bbase (se 5 (by rfl) ⟨54191, by rfl⟩ : syracuseStep 1156085 = 108383) (by norm_num)
theorem B730109 : Blo 338752 730109 := bbase (se 3 (by rfl) ⟨136895, by rfl⟩ : syracuseStep 730109 = 273791) (by norm_num)
theorem B762893 : Blo 338752 762893 := bbase (se 3 (by rfl) ⟨143042, by rfl⟩ : syracuseStep 762893 = 286085) (by norm_num)
theorem B762965 : Blo 338752 762965 := bbase (se 8 (by rfl) ⟨4470, by rfl⟩ : syracuseStep 762965 = 8941) (by norm_num)
theorem B861293 : Blo 338752 861293 := bbase (se 3 (by rfl) ⟨161492, by rfl⟩ : syracuseStep 861293 = 322985) (by norm_num)
theorem B730253 : Blo 338752 730253 := bbase (se 3 (by rfl) ⟨136922, by rfl⟩ : syracuseStep 730253 = 273845) (by norm_num)
theorem B763037 : Blo 338752 763037 := bbase (se 3 (by rfl) ⟨143069, by rfl⟩ : syracuseStep 763037 = 286139) (by norm_num)
theorem B763109 : Blo 338752 763109 := bbase (se 4 (by rfl) ⟨71541, by rfl⟩ : syracuseStep 763109 = 143083) (by norm_num)
theorem B763181 : Blo 338752 763181 := bbase (se 3 (by rfl) ⟨143096, by rfl⟩ : syracuseStep 763181 = 286193) (by norm_num)
theorem B763253 : Blo 338752 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B1156517 : Blo 338752 1156517 := bbase (se 4 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 1156517 = 216847) (by norm_num)
theorem B763325 : Blo 338752 763325 := bbase (se 3 (by rfl) ⟨143123, by rfl⟩ : syracuseStep 763325 = 286247) (by norm_num)
theorem B861637 : Blo 338752 861637 := bbase (se 4 (by rfl) ⟨80778, by rfl⟩ : syracuseStep 861637 = 161557) (by norm_num)
theorem B730613 : Blo 338752 730613 := bbase (se 5 (by rfl) ⟨34247, by rfl⟩ : syracuseStep 730613 = 68495) (by norm_num)
theorem B763397 : Blo 338752 763397 := bbase (se 4 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 763397 = 143137) (by norm_num)
theorem B861749 : Blo 338752 861749 := bbase (se 5 (by rfl) ⟨40394, by rfl⟩ : syracuseStep 861749 = 80789) (by norm_num)
theorem B763469 : Blo 338752 763469 := bbase (se 3 (by rfl) ⟨143150, by rfl⟩ : syracuseStep 763469 = 286301) (by norm_num)
theorem B1451621 : Blo 338752 1451621 := bbase (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) (by norm_num)
theorem B763541 : Blo 338752 763541 := bbase (se 6 (by rfl) ⟨17895, by rfl⟩ : syracuseStep 763541 = 35791) (by norm_num)
theorem B763613 : Blo 338752 763613 := bbase (se 3 (by rfl) ⟨143177, by rfl⟩ : syracuseStep 763613 = 286355) (by norm_num)
theorem B861941 : Blo 338752 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B763685 : Blo 338752 763685 := bbase (se 4 (by rfl) ⟨71595, by rfl⟩ : syracuseStep 763685 = 143191) (by norm_num)
theorem B1288021 : Blo 338752 1288021 := bbase (se 9 (by rfl) ⟨3773, by rfl⟩ : syracuseStep 1288021 = 7547) (by norm_num)
theorem B763757 : Blo 338752 763757 := bbase (se 3 (by rfl) ⟨143204, by rfl⟩ : syracuseStep 763757 = 286409) (by norm_num)
theorem B763829 : Blo 338752 763829 := bbase (se 5 (by rfl) ⟨35804, by rfl⟩ : syracuseStep 763829 = 71609) (by norm_num)
theorem B3876821 : Blo 338752 3876821 := bbase (se 7 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 3876821 = 90863) (by norm_num)
theorem B763901 : Blo 338752 763901 := bbase (se 3 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 763901 = 286463) (by norm_num)
theorem B763973 : Blo 338752 763973 := bbase (se 4 (by rfl) ⟨71622, by rfl⟩ : syracuseStep 763973 = 143245) (by norm_num)
theorem B862285 : Blo 338752 862285 := bbase (se 3 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 862285 = 323357) (by norm_num)
theorem B829549 : Blo 338752 829549 := bbase (se 3 (by rfl) ⟨155540, by rfl⟩ : syracuseStep 829549 = 311081) (by norm_num)
theorem B1288325 : Blo 338752 1288325 := bbase (se 4 (by rfl) ⟨120780, by rfl⟩ : syracuseStep 1288325 = 241561) (by norm_num)
theorem B764045 : Blo 338752 764045 := bbase (se 3 (by rfl) ⟨143258, by rfl⟩ : syracuseStep 764045 = 286517) (by norm_num)
theorem B469165 : Blo 338752 469165 := bbase (se 3 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 469165 = 175937) (by norm_num)
theorem B3582133 : Blo 338752 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B862397 : Blo 338752 862397 := bbase (se 3 (by rfl) ⟨161699, by rfl⟩ : syracuseStep 862397 = 323399) (by norm_num)
theorem B764117 : Blo 338752 764117 := bbase (se 7 (by rfl) ⟨8954, by rfl⟩ : syracuseStep 764117 = 17909) (by norm_num)
theorem B764189 : Blo 338752 764189 := bbase (se 3 (by rfl) ⟨143285, by rfl⟩ : syracuseStep 764189 = 286571) (by norm_num)
theorem B764261 : Blo 338752 764261 := bbase (se 4 (by rfl) ⟨71649, by rfl⟩ : syracuseStep 764261 = 143299) (by norm_num)
theorem B731501 : Blo 338752 731501 := bbase (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) (by norm_num)
theorem B862589 : Blo 338752 862589 := bbase (se 3 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 862589 = 323471) (by norm_num)
theorem B764333 : Blo 338752 764333 := bbase (se 3 (by rfl) ⟨143312, by rfl⟩ : syracuseStep 764333 = 286625) (by norm_num)
theorem B764405 : Blo 338752 764405 := bbase (se 5 (by rfl) ⟨35831, by rfl⟩ : syracuseStep 764405 = 71663) (by norm_num)
theorem B764477 : Blo 338752 764477 := bbase (se 3 (by rfl) ⟨143339, by rfl⟩ : syracuseStep 764477 = 286679) (by norm_num)
theorem B1452613 : Blo 338752 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B731749 : Blo 338752 731749 := bbase (se 4 (by rfl) ⟨68601, by rfl⟩ : syracuseStep 731749 = 137203) (by norm_num)
theorem B764549 : Blo 338752 764549 := bbase (se 4 (by rfl) ⟨71676, by rfl⟩ : syracuseStep 764549 = 143353) (by norm_num)
theorem B1223365 : Blo 338752 1223365 := bbase (se 4 (by rfl) ⟨114690, by rfl⟩ : syracuseStep 1223365 = 229381) (by norm_num)
theorem B764621 : Blo 338752 764621 := bbase (se 3 (by rfl) ⟨143366, by rfl⟩ : syracuseStep 764621 = 286733) (by norm_num)
theorem B862933 : Blo 338752 862933 := bbase (se 7 (by rfl) ⟨10112, by rfl⟩ : syracuseStep 862933 = 20225) (by norm_num)
theorem B764693 : Blo 338752 764693 := bbase (se 6 (by rfl) ⟨17922, by rfl⟩ : syracuseStep 764693 = 35845) (by norm_num)
theorem B863045 : Blo 338752 863045 := bbase (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) (by norm_num)
theorem B764765 : Blo 338752 764765 := bbase (se 3 (by rfl) ⟨143393, by rfl⟩ : syracuseStep 764765 = 286787) (by norm_num)
theorem B1223525 : Blo 338752 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B1715093 : Blo 338752 1715093 := bbase (se 6 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 1715093 = 80395) (by norm_num)
theorem B764837 : Blo 338752 764837 := bbase (se 4 (by rfl) ⟨71703, by rfl⟩ : syracuseStep 764837 = 143407) (by norm_num)
theorem B2927573 : Blo 338752 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B764909 : Blo 338752 764909 := bbase (se 3 (by rfl) ⟨143420, by rfl⟩ : syracuseStep 764909 = 286841) (by norm_num)
theorem B863237 : Blo 338752 863237 := bbase (se 4 (by rfl) ⟨80928, by rfl⟩ : syracuseStep 863237 = 161857) (by norm_num)
theorem B764981 : Blo 338752 764981 := bbase (se 5 (by rfl) ⟨35858, by rfl⟩ : syracuseStep 764981 = 71717) (by norm_num)
theorem B765053 : Blo 338752 765053 := bbase (se 3 (by rfl) ⟨143447, by rfl⟩ : syracuseStep 765053 = 286895) (by norm_num)
theorem B765125 : Blo 338752 765125 := bbase (se 4 (by rfl) ⟨71730, by rfl⟩ : syracuseStep 765125 = 143461) (by norm_num)
theorem B765197 : Blo 338752 765197 := bbase (se 3 (by rfl) ⟨143474, by rfl⟩ : syracuseStep 765197 = 286949) (by norm_num)
theorem B765269 : Blo 338752 765269 := bbase (se 11 (by rfl) ⟨560, by rfl⟩ : syracuseStep 765269 = 1121) (by norm_num)
theorem B863581 : Blo 338752 863581 := bbase (se 3 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 863581 = 323843) (by norm_num)
theorem B437621 : Blo 338752 437621 := bbase (se 5 (by rfl) ⟨20513, by rfl⟩ : syracuseStep 437621 = 41027) (by norm_num)
theorem B2174357 : Blo 338752 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B765341 : Blo 338752 765341 := bbase (se 3 (by rfl) ⟨143501, by rfl⟩ : syracuseStep 765341 = 287003) (by norm_num)
theorem B863693 : Blo 338752 863693 := bbase (se 3 (by rfl) ⟨161942, by rfl⟩ : syracuseStep 863693 = 323885) (by norm_num)
theorem B765413 : Blo 338752 765413 := bbase (se 4 (by rfl) ⟨71757, by rfl⟩ : syracuseStep 765413 = 143515) (by norm_num)
theorem B765485 : Blo 338752 765485 := bbase (se 3 (by rfl) ⟨143528, by rfl⟩ : syracuseStep 765485 = 287057) (by norm_num)
theorem B765557 : Blo 338752 765557 := bbase (se 5 (by rfl) ⟨35885, by rfl⟩ : syracuseStep 765557 = 71771) (by norm_num)
theorem B863885 : Blo 338752 863885 := bbase (se 3 (by rfl) ⟨161978, by rfl⟩ : syracuseStep 863885 = 323957) (by norm_num)
theorem B765629 : Blo 338752 765629 := bbase (se 3 (by rfl) ⟨143555, by rfl⟩ : syracuseStep 765629 = 287111) (by norm_num)
theorem B765701 : Blo 338752 765701 := bbase (se 4 (by rfl) ⟨71784, by rfl⟩ : syracuseStep 765701 = 143569) (by norm_num)
theorem B438053 : Blo 338752 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B765773 : Blo 338752 765773 := bbase (se 3 (by rfl) ⟨143582, by rfl⟩ : syracuseStep 765773 = 287165) (by norm_num)
theorem B765845 : Blo 338752 765845 := bbase (se 6 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 765845 = 35899) (by norm_num)
theorem B765917 : Blo 338752 765917 := bbase (se 3 (by rfl) ⟨143609, by rfl⟩ : syracuseStep 765917 = 287219) (by norm_num)
theorem B864229 : Blo 338752 864229 := bbase (se 4 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 864229 = 162043) (by norm_num)
theorem B1093637 : Blo 338752 1093637 := bbase (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) (by norm_num)
theorem B765989 : Blo 338752 765989 := bbase (se 4 (by rfl) ⟨71811, by rfl⟩ : syracuseStep 765989 = 143623) (by norm_num)
theorem B864341 : Blo 338752 864341 := bbase (se 8 (by rfl) ⟨5064, by rfl⟩ : syracuseStep 864341 = 10129) (by norm_num)
theorem B766061 : Blo 338752 766061 := bbase (se 3 (by rfl) ⟨143636, by rfl⟩ : syracuseStep 766061 = 287273) (by norm_num)
theorem B1388677 : Blo 338752 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B1716389 : Blo 338752 1716389 := bbase (se 4 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 1716389 = 321823) (by norm_num)
theorem B766133 : Blo 338752 766133 := bbase (se 5 (by rfl) ⟨35912, by rfl⟩ : syracuseStep 766133 = 71825) (by norm_num)
theorem B1290437 : Blo 338752 1290437 := bbase (se 4 (by rfl) ⟨120978, by rfl⟩ : syracuseStep 1290437 = 241957) (by norm_num)
theorem B1323221 : Blo 338752 1323221 := bbase (se 7 (by rfl) ⟨15506, by rfl⟩ : syracuseStep 1323221 = 31013) (by norm_num)
theorem B766205 : Blo 338752 766205 := bbase (se 3 (by rfl) ⟨143663, by rfl⟩ : syracuseStep 766205 = 287327) (by norm_num)
theorem B864533 : Blo 338752 864533 := bbase (se 6 (by rfl) ⟨20262, by rfl⟩ : syracuseStep 864533 = 40525) (by norm_num)
theorem B766277 : Blo 338752 766277 := bbase (se 4 (by rfl) ⟨71838, by rfl⟩ : syracuseStep 766277 = 143677) (by norm_num)
theorem B766349 : Blo 338752 766349 := bbase (se 3 (by rfl) ⟨143690, by rfl⟩ : syracuseStep 766349 = 287381) (by norm_num)
theorem B766421 : Blo 338752 766421 := bbase (se 7 (by rfl) ⟨8981, by rfl⟩ : syracuseStep 766421 = 17963) (by norm_num)
theorem B1290725 : Blo 338752 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B766493 : Blo 338752 766493 := bbase (se 3 (by rfl) ⟨143717, by rfl⟩ : syracuseStep 766493 = 287435) (by norm_num)
theorem B2601557 : Blo 338752 2601557 := bbase (se 8 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 2601557 = 30487) (by norm_num)
theorem B766565 : Blo 338752 766565 := bbase (se 4 (by rfl) ⟨71865, by rfl⟩ : syracuseStep 766565 = 143731) (by norm_num)
theorem B438889 : Blo 338752 438889 := bbase (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) (by norm_num)
theorem B864877 : Blo 338752 864877 := bbase (se 3 (by rfl) ⟨162164, by rfl⟩ : syracuseStep 864877 = 324329) (by norm_num)
theorem B766637 : Blo 338752 766637 := bbase (se 3 (by rfl) ⟨143744, by rfl⟩ : syracuseStep 766637 = 287489) (by norm_num)
theorem B3683029 : Blo 338752 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B864989 : Blo 338752 864989 := bbase (se 3 (by rfl) ⟨162185, by rfl⟩ : syracuseStep 864989 = 324371) (by norm_num)
theorem B766709 : Blo 338752 766709 := bbase (se 5 (by rfl) ⟨35939, by rfl⟩ : syracuseStep 766709 = 71879) (by norm_num)
theorem B766781 : Blo 338752 766781 := bbase (se 3 (by rfl) ⟨143771, by rfl⟩ : syracuseStep 766781 = 287543) (by norm_num)
theorem B6566741 : Blo 338752 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B766853 : Blo 338752 766853 := bbase (se 4 (by rfl) ⟨71892, by rfl⟩ : syracuseStep 766853 = 143785) (by norm_num)
theorem B865181 : Blo 338752 865181 := bbase (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) (by norm_num)
theorem B766925 : Blo 338752 766925 := bbase (se 3 (by rfl) ⟨143798, by rfl⟩ : syracuseStep 766925 = 287597) (by norm_num)
theorem B766997 : Blo 338752 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B767069 : Blo 338752 767069 := bbase (se 3 (by rfl) ⟨143825, by rfl⟩ : syracuseStep 767069 = 287651) (by norm_num)
theorem B767141 : Blo 338752 767141 := bbase (se 4 (by rfl) ⟨71919, by rfl⟩ : syracuseStep 767141 = 143839) (by norm_num)
theorem B767213 : Blo 338752 767213 := bbase (se 3 (by rfl) ⟨143852, by rfl⟩ : syracuseStep 767213 = 287705) (by norm_num)
theorem B865525 : Blo 338752 865525 := bbase (se 5 (by rfl) ⟨40571, by rfl⟩ : syracuseStep 865525 = 81143) (by norm_num)
theorem B767285 : Blo 338752 767285 := bbase (se 5 (by rfl) ⟨35966, by rfl⟩ : syracuseStep 767285 = 71933) (by norm_num)
theorem B865637 : Blo 338752 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B767357 : Blo 338752 767357 := bbase (se 3 (by rfl) ⟨143879, by rfl⟩ : syracuseStep 767357 = 287759) (by norm_num)
theorem B1717685 : Blo 338752 1717685 := bbase (se 5 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 1717685 = 161033) (by norm_num)
theorem B767429 : Blo 338752 767429 := bbase (se 4 (by rfl) ⟨71946, by rfl⟩ : syracuseStep 767429 = 143893) (by norm_num)
theorem B767501 : Blo 338752 767501 := bbase (se 3 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 767501 = 287813) (by norm_num)
theorem B1553941 : Blo 338752 1553941 := bbase (se 6 (by rfl) ⟨36420, by rfl⟩ : syracuseStep 1553941 = 72841) (by norm_num)
theorem B865829 : Blo 338752 865829 := bbase (se 4 (by rfl) ⟨81171, by rfl⟩ : syracuseStep 865829 = 162343) (by norm_num)
theorem B767573 : Blo 338752 767573 := bbase (se 8 (by rfl) ⟨4497, by rfl⟩ : syracuseStep 767573 = 8995) (by norm_num)
theorem B1291909 : Blo 338752 1291909 := bbase (se 4 (by rfl) ⟨121116, by rfl⟩ : syracuseStep 1291909 = 242233) (by norm_num)
theorem B767645 : Blo 338752 767645 := bbase (se 3 (by rfl) ⟨143933, by rfl⟩ : syracuseStep 767645 = 287867) (by norm_num)
theorem B767717 : Blo 338752 767717 := bbase (se 4 (by rfl) ⟨71973, by rfl⟩ : syracuseStep 767717 = 143947) (by norm_num)
theorem B767789 : Blo 338752 767789 := bbase (se 3 (by rfl) ⟨143960, by rfl⟩ : syracuseStep 767789 = 287921) (by norm_num)
theorem B767861 : Blo 338752 767861 := bbase (se 5 (by rfl) ⟨35993, by rfl⟩ : syracuseStep 767861 = 71987) (by norm_num)
theorem B866173 : Blo 338752 866173 := bbase (se 3 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 866173 = 324815) (by norm_num)
theorem B1292213 : Blo 338752 1292213 := bbase (se 5 (by rfl) ⟨60572, by rfl⟩ : syracuseStep 1292213 = 121145) (by norm_num)
theorem B767933 : Blo 338752 767933 := bbase (se 3 (by rfl) ⟨143987, by rfl⟩ : syracuseStep 767933 = 287975) (by norm_num)
theorem B866285 : Blo 338752 866285 := bbase (se 3 (by rfl) ⟨162428, by rfl⟩ : syracuseStep 866285 = 324857) (by norm_num)
theorem B768005 : Blo 338752 768005 := bbase (se 4 (by rfl) ⟨72000, by rfl⟩ : syracuseStep 768005 = 144001) (by norm_num)
theorem B768077 : Blo 338752 768077 := bbase (se 3 (by rfl) ⟨144014, by rfl⟩ : syracuseStep 768077 = 288029) (by norm_num)
theorem B1554565 : Blo 338752 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B768149 : Blo 338752 768149 := bbase (se 6 (by rfl) ⟨18003, by rfl⟩ : syracuseStep 768149 = 36007) (by norm_num)
theorem B1947797 : Blo 338752 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B866477 : Blo 338752 866477 := bbase (se 3 (by rfl) ⟨162464, by rfl⟩ : syracuseStep 866477 = 324929) (by norm_num)
theorem B735437 : Blo 338752 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B1095893 : Blo 338752 1095893 := bbase (se 7 (by rfl) ⟨12842, by rfl⟩ : syracuseStep 1095893 = 25685) (by norm_num)
theorem B768221 : Blo 338752 768221 := bbase (se 3 (by rfl) ⟨144041, by rfl⟩ : syracuseStep 768221 = 288083) (by norm_num)
theorem B768293 : Blo 338752 768293 := bbase (se 4 (by rfl) ⟨72027, by rfl⟩ : syracuseStep 768293 = 144055) (by norm_num)
theorem B1096021 : Blo 338752 1096021 := bbase (se 10 (by rfl) ⟨1605, by rfl⟩ : syracuseStep 1096021 = 3211) (by norm_num)
theorem B768365 : Blo 338752 768365 := bbase (se 3 (by rfl) ⟨144068, by rfl⟩ : syracuseStep 768365 = 288137) (by norm_num)
theorem B571765 : Blo 338752 571765 := bbase (se 5 (by rfl) ⟨26801, by rfl⟩ : syracuseStep 571765 = 53603) (by norm_num)
theorem B768437 : Blo 338752 768437 := bbase (se 5 (by rfl) ⟨36020, by rfl⟩ : syracuseStep 768437 = 72041) (by norm_num)
theorem B571853 : Blo 338752 571853 := bbase (se 3 (by rfl) ⟨107222, by rfl⟩ : syracuseStep 571853 = 214445) (by norm_num)
theorem B768509 : Blo 338752 768509 := bbase (se 3 (by rfl) ⟨144095, by rfl⟩ : syracuseStep 768509 = 288191) (by norm_num)
theorem B1161733 : Blo 338752 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B866821 : Blo 338752 866821 := bbase (se 4 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 866821 = 162529) (by norm_num)
theorem B768581 : Blo 338752 768581 := bbase (se 4 (by rfl) ⟨72054, by rfl⟩ : syracuseStep 768581 = 144109) (by norm_num)
theorem B571981 : Blo 338752 571981 := bbase (se 3 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 571981 = 214493) (by norm_num)
theorem B866933 : Blo 338752 866933 := bbase (se 5 (by rfl) ⟨40637, by rfl⟩ : syracuseStep 866933 = 81275) (by norm_num)
theorem B768653 : Blo 338752 768653 := bbase (se 3 (by rfl) ⟨144122, by rfl⟩ : syracuseStep 768653 = 288245) (by norm_num)
theorem B572069 : Blo 338752 572069 := bbase (se 4 (by rfl) ⟨53631, by rfl⟩ : syracuseStep 572069 = 107263) (by norm_num)
theorem B1555109 : Blo 338752 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1718981 : Blo 338752 1718981 := bbase (se 4 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 1718981 = 322309) (by norm_num)
theorem B965333 : Blo 338752 965333 := bbase (se 7 (by rfl) ⟨11312, by rfl⟩ : syracuseStep 965333 = 22625) (by norm_num)
theorem B768725 : Blo 338752 768725 := bbase (se 7 (by rfl) ⟨9008, by rfl⟩ : syracuseStep 768725 = 18017) (by norm_num)
theorem B768797 : Blo 338752 768797 := bbase (se 3 (by rfl) ⟨144149, by rfl⟩ : syracuseStep 768797 = 288299) (by norm_num)
theorem B572197 : Blo 338752 572197 := bbase (se 4 (by rfl) ⟨53643, by rfl⟩ : syracuseStep 572197 = 107287) (by norm_num)
theorem B867125 : Blo 338752 867125 := bbase (se 5 (by rfl) ⟨40646, by rfl⟩ : syracuseStep 867125 = 81293) (by norm_num)
theorem B768869 : Blo 338752 768869 := bbase (se 4 (by rfl) ⟨72081, by rfl⟩ : syracuseStep 768869 = 144163) (by norm_num)
theorem B572285 : Blo 338752 572285 := bbase (se 3 (by rfl) ⟨107303, by rfl⟩ : syracuseStep 572285 = 214607) (by norm_num)
theorem B408461 : Blo 338752 408461 := bbase (se 3 (by rfl) ⟨76586, by rfl⟩ : syracuseStep 408461 = 153173) (by norm_num)
theorem B768941 : Blo 338752 768941 := bbase (se 3 (by rfl) ⟨144176, by rfl⟩ : syracuseStep 768941 = 288353) (by norm_num)
theorem B769013 : Blo 338752 769013 := bbase (se 5 (by rfl) ⟨36047, by rfl⟩ : syracuseStep 769013 = 72095) (by norm_num)
theorem B1850357 : Blo 338752 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B572413 : Blo 338752 572413 := bbase (se 3 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 572413 = 214655) (by norm_num)
theorem B769085 : Blo 338752 769085 := bbase (se 3 (by rfl) ⟨144203, by rfl⟩ : syracuseStep 769085 = 288407) (by norm_num)
theorem B572501 : Blo 338752 572501 := bbase (se 8 (by rfl) ⟨3354, by rfl⟩ : syracuseStep 572501 = 6709) (by norm_num)
theorem B408673 : Blo 338752 408673 := bbase (se 2 (by rfl) ⟨153252, by rfl⟩ : syracuseStep 408673 = 306505) (by norm_num)
theorem B769157 : Blo 338752 769157 := bbase (se 4 (by rfl) ⟨72108, by rfl⟩ : syracuseStep 769157 = 144217) (by norm_num)
theorem B867469 : Blo 338752 867469 := bbase (se 3 (by rfl) ⟨162650, by rfl⟩ : syracuseStep 867469 = 325301) (by norm_num)
theorem B769229 : Blo 338752 769229 := bbase (se 3 (by rfl) ⟨144230, by rfl⟩ : syracuseStep 769229 = 288461) (by norm_num)
theorem B572629 : Blo 338752 572629 := bbase (se 7 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 572629 = 13421) (by norm_num)
theorem B1752293 : Blo 338752 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B408817 : Blo 338752 408817 := bbase (se 2 (by rfl) ⟨153306, by rfl⟩ : syracuseStep 408817 = 306613) (by norm_num)
theorem B867581 : Blo 338752 867581 := bbase (se 3 (by rfl) ⟨162671, by rfl⟩ : syracuseStep 867581 = 325343) (by norm_num)
theorem B769301 : Blo 338752 769301 := bbase (se 6 (by rfl) ⟨18030, by rfl⟩ : syracuseStep 769301 = 36061) (by norm_num)
theorem B572717 : Blo 338752 572717 := bbase (se 3 (by rfl) ⟨107384, by rfl⟩ : syracuseStep 572717 = 214769) (by norm_num)
theorem B1948981 : Blo 338752 1948981 := bbase (se 5 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 1948981 = 182717) (by norm_num)
theorem B769373 : Blo 338752 769373 := bbase (se 3 (by rfl) ⟨144257, by rfl⟩ : syracuseStep 769373 = 288515) (by norm_num)
theorem B769445 : Blo 338752 769445 := bbase (se 4 (by rfl) ⟨72135, by rfl⟩ : syracuseStep 769445 = 144271) (by norm_num)
theorem B572845 : Blo 338752 572845 := bbase (se 3 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 572845 = 214817) (by norm_num)
theorem B736685 : Blo 338752 736685 := bbase (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) (by norm_num)
theorem B1457621 : Blo 338752 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B769517 : Blo 338752 769517 := bbase (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) (by norm_num)
theorem B572933 : Blo 338752 572933 := bbase (se 4 (by rfl) ⟨53712, by rfl⟩ : syracuseStep 572933 = 107425) (by norm_num)
theorem B769589 : Blo 338752 769589 := bbase (se 5 (by rfl) ⟨36074, by rfl⟩ : syracuseStep 769589 = 72149) (by norm_num)
theorem B769661 : Blo 338752 769661 := bbase (se 3 (by rfl) ⟨144311, by rfl⟩ : syracuseStep 769661 = 288623) (by norm_num)
theorem B573061 : Blo 338752 573061 := bbase (se 4 (by rfl) ⟨53724, by rfl⟩ : syracuseStep 573061 = 107449) (by norm_num)
theorem B769733 : Blo 338752 769733 := bbase (se 4 (by rfl) ⟨72162, by rfl⟩ : syracuseStep 769733 = 144325) (by norm_num)
theorem B573149 : Blo 338752 573149 := bbase (se 3 (by rfl) ⟨107465, by rfl⟩ : syracuseStep 573149 = 214931) (by norm_num)
theorem B1457909 : Blo 338752 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B769805 : Blo 338752 769805 := bbase (se 3 (by rfl) ⟨144338, by rfl⟩ : syracuseStep 769805 = 288677) (by norm_num)
theorem B769877 : Blo 338752 769877 := bbase (se 9 (by rfl) ⟨2255, by rfl⟩ : syracuseStep 769877 = 4511) (by norm_num)
theorem B573277 : Blo 338752 573277 := bbase (se 3 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 573277 = 214979) (by norm_num)
theorem B769949 : Blo 338752 769949 := bbase (se 3 (by rfl) ⟨144365, by rfl⟩ : syracuseStep 769949 = 288731) (by norm_num)
theorem B573365 : Blo 338752 573365 := bbase (se 5 (by rfl) ⟨26876, by rfl⟩ : syracuseStep 573365 = 53753) (by norm_num)
theorem B1720277 : Blo 338752 1720277 := bbase (se 7 (by rfl) ⟨20159, by rfl⟩ : syracuseStep 1720277 = 40319) (by norm_num)
theorem B770021 : Blo 338752 770021 := bbase (se 4 (by rfl) ⟨72189, by rfl⟩ : syracuseStep 770021 = 144379) (by norm_num)
theorem B1294325 : Blo 338752 1294325 := bbase (se 5 (by rfl) ⟨60671, by rfl⟩ : syracuseStep 1294325 = 121343) (by norm_num)
theorem B770093 : Blo 338752 770093 := bbase (se 3 (by rfl) ⟨144392, by rfl⟩ : syracuseStep 770093 = 288785) (by norm_num)
theorem B573493 : Blo 338752 573493 := bbase (se 5 (by rfl) ⟨26882, by rfl⟩ : syracuseStep 573493 = 53765) (by norm_num)
theorem B770165 : Blo 338752 770165 := bbase (se 5 (by rfl) ⟨36101, by rfl⟩ : syracuseStep 770165 = 72203) (by norm_num)
theorem B573581 : Blo 338752 573581 := bbase (se 3 (by rfl) ⟨107546, by rfl⟩ : syracuseStep 573581 = 215093) (by norm_num)
theorem B770237 : Blo 338752 770237 := bbase (se 3 (by rfl) ⟨144419, by rfl⟩ : syracuseStep 770237 = 288839) (by norm_num)
theorem B508133 : Blo 338752 508133 := bbase (se 4 (by rfl) ⟨47637, by rfl⟩ : syracuseStep 508133 = 95275) (by norm_num)
theorem B508157 : Blo 338752 508157 := bbase (se 3 (by rfl) ⟨95279, by rfl⟩ : syracuseStep 508157 = 190559) (by norm_num)
theorem B966917 : Blo 338752 966917 := bbase (se 4 (by rfl) ⟨90648, by rfl⟩ : syracuseStep 966917 = 181297) (by norm_num)
theorem B770309 : Blo 338752 770309 := bbase (se 4 (by rfl) ⟨72216, by rfl⟩ : syracuseStep 770309 = 144433) (by norm_num)
theorem B573709 : Blo 338752 573709 := bbase (se 3 (by rfl) ⟨107570, by rfl⟩ : syracuseStep 573709 = 215141) (by norm_num)
theorem B508181 : Blo 338752 508181 := bbase (se 6 (by rfl) ⟨11910, by rfl⟩ : syracuseStep 508181 = 23821) (by norm_num)
theorem B1294613 : Blo 338752 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B508205 : Blo 338752 508205 := bbase (se 3 (by rfl) ⟨95288, by rfl⟩ : syracuseStep 508205 = 190577) (by norm_num)
theorem B508229 : Blo 338752 508229 := bbase (se 4 (by rfl) ⟨47646, by rfl⟩ : syracuseStep 508229 = 95293) (by norm_num)
theorem B770381 : Blo 338752 770381 := bbase (se 3 (by rfl) ⟨144446, by rfl⟩ : syracuseStep 770381 = 288893) (by norm_num)
theorem B508253 : Blo 338752 508253 := bbase (se 3 (by rfl) ⟨95297, by rfl⟩ : syracuseStep 508253 = 190595) (by norm_num)
theorem B573797 : Blo 338752 573797 := bbase (se 4 (by rfl) ⟨53793, by rfl⟩ : syracuseStep 573797 = 107587) (by norm_num)
theorem B508277 : Blo 338752 508277 := bbase (se 5 (by rfl) ⟨23825, by rfl⟩ : syracuseStep 508277 = 47651) (by norm_num)
theorem B508301 : Blo 338752 508301 := bbase (se 3 (by rfl) ⟨95306, by rfl⟩ : syracuseStep 508301 = 190613) (by norm_num)
theorem B770453 : Blo 338752 770453 := bbase (se 6 (by rfl) ⟨18057, by rfl⟩ : syracuseStep 770453 = 36115) (by norm_num)
theorem B508325 : Blo 338752 508325 := bbase (se 4 (by rfl) ⟨47655, by rfl⟩ : syracuseStep 508325 = 95311) (by norm_num)
theorem B508349 : Blo 338752 508349 := bbase (se 3 (by rfl) ⟨95315, by rfl⟩ : syracuseStep 508349 = 190631) (by norm_num)
theorem B508373 : Blo 338752 508373 := bbase (se 7 (by rfl) ⟨5957, by rfl⟩ : syracuseStep 508373 = 11915) (by norm_num)
theorem B770525 : Blo 338752 770525 := bbase (se 3 (by rfl) ⟨144473, by rfl⟩ : syracuseStep 770525 = 288947) (by norm_num)
theorem B573925 : Blo 338752 573925 := bbase (se 4 (by rfl) ⟨53805, by rfl⟩ : syracuseStep 573925 = 107611) (by norm_num)
theorem B1458661 : Blo 338752 1458661 := bbase (se 4 (by rfl) ⟨136749, by rfl⟩ : syracuseStep 1458661 = 273499) (by norm_num)
theorem B508397 : Blo 338752 508397 := bbase (se 3 (by rfl) ⟨95324, by rfl⟩ : syracuseStep 508397 = 190649) (by norm_num)
theorem B508421 : Blo 338752 508421 := bbase (se 4 (by rfl) ⟨47664, by rfl⟩ : syracuseStep 508421 = 95329) (by norm_num)
theorem B508445 : Blo 338752 508445 := bbase (se 3 (by rfl) ⟨95333, by rfl⟩ : syracuseStep 508445 = 190667) (by norm_num)
theorem B770597 : Blo 338752 770597 := bbase (se 4 (by rfl) ⟨72243, by rfl⟩ : syracuseStep 770597 = 144487) (by norm_num)
theorem B508469 : Blo 338752 508469 := bbase (se 5 (by rfl) ⟨23834, by rfl⟩ : syracuseStep 508469 = 47669) (by norm_num)
theorem B574013 : Blo 338752 574013 := bbase (se 3 (by rfl) ⟨107627, by rfl⟩ : syracuseStep 574013 = 215255) (by norm_num)
theorem B508493 : Blo 338752 508493 := bbase (se 3 (by rfl) ⟨95342, by rfl⟩ : syracuseStep 508493 = 190685) (by norm_num)
theorem B508517 : Blo 338752 508517 := bbase (se 4 (by rfl) ⟨47673, by rfl⟩ : syracuseStep 508517 = 95347) (by norm_num)
theorem B770669 : Blo 338752 770669 := bbase (se 3 (by rfl) ⟨144500, by rfl⟩ : syracuseStep 770669 = 289001) (by norm_num)
theorem B508541 : Blo 338752 508541 := bbase (se 3 (by rfl) ⟨95351, by rfl⟩ : syracuseStep 508541 = 190703) (by norm_num)
theorem B508565 : Blo 338752 508565 := bbase (se 6 (by rfl) ⟨11919, by rfl⟩ : syracuseStep 508565 = 23839) (by norm_num)
theorem B508589 : Blo 338752 508589 := bbase (se 3 (by rfl) ⟨95360, by rfl⟩ : syracuseStep 508589 = 190721) (by norm_num)
theorem B770741 : Blo 338752 770741 := bbase (se 5 (by rfl) ⟨36128, by rfl⟩ : syracuseStep 770741 = 72257) (by norm_num)
theorem B574141 : Blo 338752 574141 := bbase (se 3 (by rfl) ⟨107651, by rfl⟩ : syracuseStep 574141 = 215303) (by norm_num)
theorem B508613 : Blo 338752 508613 := bbase (se 4 (by rfl) ⟨47682, by rfl⟩ : syracuseStep 508613 = 95365) (by norm_num)
theorem B508637 : Blo 338752 508637 := bbase (se 3 (by rfl) ⟨95369, by rfl⟩ : syracuseStep 508637 = 190739) (by norm_num)
theorem B508661 : Blo 338752 508661 := bbase (se 5 (by rfl) ⟨23843, by rfl⟩ : syracuseStep 508661 = 47687) (by norm_num)
theorem B770813 : Blo 338752 770813 := bbase (se 3 (by rfl) ⟨144527, by rfl⟩ : syracuseStep 770813 = 289055) (by norm_num)
theorem B508685 : Blo 338752 508685 := bbase (se 3 (by rfl) ⟨95378, by rfl⟩ : syracuseStep 508685 = 190757) (by norm_num)
theorem B574229 : Blo 338752 574229 := bbase (se 6 (by rfl) ⟨13458, by rfl⟩ : syracuseStep 574229 = 26917) (by norm_num)
theorem B410393 : Blo 338752 410393 := bbase (se 2 (by rfl) ⟨153897, by rfl⟩ : syracuseStep 410393 = 307795) (by norm_num)
theorem B508709 : Blo 338752 508709 := bbase (se 4 (by rfl) ⟨47691, by rfl⟩ : syracuseStep 508709 = 95383) (by norm_num)
theorem B508733 : Blo 338752 508733 := bbase (se 3 (by rfl) ⟨95387, by rfl⟩ : syracuseStep 508733 = 190775) (by norm_num)
theorem B770885 : Blo 338752 770885 := bbase (se 4 (by rfl) ⟨72270, by rfl⟩ : syracuseStep 770885 = 144541) (by norm_num)
theorem B508757 : Blo 338752 508757 := bbase (se 9 (by rfl) ⟨1490, by rfl⟩ : syracuseStep 508757 = 2981) (by norm_num)
theorem B508781 : Blo 338752 508781 := bbase (se 3 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 508781 = 190793) (by norm_num)
theorem B508805 : Blo 338752 508805 := bbase (se 4 (by rfl) ⟨47700, by rfl⟩ : syracuseStep 508805 = 95401) (by norm_num)
theorem B770957 : Blo 338752 770957 := bbase (se 3 (by rfl) ⟨144554, by rfl⟩ : syracuseStep 770957 = 289109) (by norm_num)
theorem B574357 : Blo 338752 574357 := bbase (se 6 (by rfl) ⟨13461, by rfl⟩ : syracuseStep 574357 = 26923) (by norm_num)
theorem B508829 : Blo 338752 508829 := bbase (se 3 (by rfl) ⟨95405, by rfl⟩ : syracuseStep 508829 = 190811) (by norm_num)
theorem B967589 : Blo 338752 967589 := bbase (se 4 (by rfl) ⟨90711, by rfl⟩ : syracuseStep 967589 = 181423) (by norm_num)
theorem B508853 : Blo 338752 508853 := bbase (se 5 (by rfl) ⟨23852, by rfl⟩ : syracuseStep 508853 = 47705) (by norm_num)
theorem B508877 : Blo 338752 508877 := bbase (se 3 (by rfl) ⟨95414, by rfl⟩ : syracuseStep 508877 = 190829) (by norm_num)
theorem B771029 : Blo 338752 771029 := bbase (se 7 (by rfl) ⟨9035, by rfl⟩ : syracuseStep 771029 = 18071) (by norm_num)
theorem B508901 : Blo 338752 508901 := bbase (se 4 (by rfl) ⟨47709, by rfl⟩ : syracuseStep 508901 = 95419) (by norm_num)
theorem B345061 : Blo 338752 345061 := bbase (se 4 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 345061 = 64699) (by norm_num)
theorem B574445 : Blo 338752 574445 := bbase (se 3 (by rfl) ⟨107708, by rfl⟩ : syracuseStep 574445 = 215417) (by norm_num)
theorem B508925 : Blo 338752 508925 := bbase (se 3 (by rfl) ⟨95423, by rfl⟩ : syracuseStep 508925 = 190847) (by norm_num)
theorem B508949 : Blo 338752 508949 := bbase (se 6 (by rfl) ⟨11928, by rfl⟩ : syracuseStep 508949 = 23857) (by norm_num)
theorem B771101 : Blo 338752 771101 := bbase (se 3 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 771101 = 289163) (by norm_num)
theorem B508973 : Blo 338752 508973 := bbase (se 3 (by rfl) ⟨95432, by rfl⟩ : syracuseStep 508973 = 190865) (by norm_num)
theorem B508997 : Blo 338752 508997 := bbase (se 4 (by rfl) ⟨47718, by rfl⟩ : syracuseStep 508997 = 95437) (by norm_num)
theorem B509021 : Blo 338752 509021 := bbase (se 3 (by rfl) ⟨95441, by rfl⟩ : syracuseStep 509021 = 190883) (by norm_num)
theorem B771173 : Blo 338752 771173 := bbase (se 4 (by rfl) ⟨72297, by rfl⟩ : syracuseStep 771173 = 144595) (by norm_num)
theorem B410729 : Blo 338752 410729 := bbase (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) (by norm_num)
theorem B574573 : Blo 338752 574573 := bbase (se 3 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 574573 = 215465) (by norm_num)
theorem B509045 : Blo 338752 509045 := bbase (se 5 (by rfl) ⟨23861, by rfl⟩ : syracuseStep 509045 = 47723) (by norm_num)
theorem B509069 : Blo 338752 509069 := bbase (se 3 (by rfl) ⟨95450, by rfl⟩ : syracuseStep 509069 = 190901) (by norm_num)
theorem B509093 : Blo 338752 509093 := bbase (se 4 (by rfl) ⟨47727, by rfl⟩ : syracuseStep 509093 = 95455) (by norm_num)
theorem B509117 : Blo 338752 509117 := bbase (se 3 (by rfl) ⟨95459, by rfl⟩ : syracuseStep 509117 = 190919) (by norm_num)
theorem B574661 : Blo 338752 574661 := bbase (se 4 (by rfl) ⟨53874, by rfl⟩ : syracuseStep 574661 = 107749) (by norm_num)
theorem B1459397 : Blo 338752 1459397 := bbase (se 4 (by rfl) ⟨136818, by rfl⟩ : syracuseStep 1459397 = 273637) (by norm_num)
theorem B509141 : Blo 338752 509141 := bbase (se 7 (by rfl) ⟨5966, by rfl⟩ : syracuseStep 509141 = 11933) (by norm_num)
theorem B410845 : Blo 338752 410845 := bbase (se 3 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 410845 = 154067) (by norm_num)
theorem B1721573 : Blo 338752 1721573 := bbase (se 4 (by rfl) ⟨161397, by rfl⟩ : syracuseStep 1721573 = 322795) (by norm_num)
theorem B509165 : Blo 338752 509165 := bbase (se 3 (by rfl) ⟨95468, by rfl⟩ : syracuseStep 509165 = 190937) (by norm_num)
theorem B1950965 : Blo 338752 1950965 := bbase (se 5 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 1950965 = 182903) (by norm_num)
theorem B509189 : Blo 338752 509189 := bbase (se 4 (by rfl) ⟨47736, by rfl⟩ : syracuseStep 509189 = 95473) (by norm_num)
theorem B509213 : Blo 338752 509213 := bbase (se 3 (by rfl) ⟨95477, by rfl⟩ : syracuseStep 509213 = 190955) (by norm_num)
theorem B410917 : Blo 338752 410917 := bbase (se 4 (by rfl) ⟨38523, by rfl⟩ : syracuseStep 410917 = 77047) (by norm_num)
theorem B509237 : Blo 338752 509237 := bbase (se 5 (by rfl) ⟨23870, by rfl⟩ : syracuseStep 509237 = 47741) (by norm_num)
theorem B410941 : Blo 338752 410941 := bbase (se 3 (by rfl) ⟨77051, by rfl⟩ : syracuseStep 410941 = 154103) (by norm_num)
theorem B574789 : Blo 338752 574789 := bbase (se 4 (by rfl) ⟨53886, by rfl⟩ : syracuseStep 574789 = 107773) (by norm_num)
theorem B509261 : Blo 338752 509261 := bbase (se 3 (by rfl) ⟨95486, by rfl⟩ : syracuseStep 509261 = 190973) (by norm_num)
theorem B968021 : Blo 338752 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B509285 : Blo 338752 509285 := bbase (se 4 (by rfl) ⟨47745, by rfl⟩ : syracuseStep 509285 = 95491) (by norm_num)
theorem B509309 : Blo 338752 509309 := bbase (se 3 (by rfl) ⟨95495, by rfl⟩ : syracuseStep 509309 = 190991) (by norm_num)
theorem B509333 : Blo 338752 509333 := bbase (se 6 (by rfl) ⟨11937, by rfl⟩ : syracuseStep 509333 = 23875) (by norm_num)
theorem B574877 : Blo 338752 574877 := bbase (se 3 (by rfl) ⟨107789, by rfl⟩ : syracuseStep 574877 = 215579) (by norm_num)
theorem B509357 : Blo 338752 509357 := bbase (se 3 (by rfl) ⟨95504, by rfl⟩ : syracuseStep 509357 = 191009) (by norm_num)
theorem B1295797 : Blo 338752 1295797 := bbase (se 5 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 1295797 = 121481) (by norm_num)
theorem B509381 : Blo 338752 509381 := bbase (se 4 (by rfl) ⟨47754, by rfl⟩ : syracuseStep 509381 = 95509) (by norm_num)
theorem B411085 : Blo 338752 411085 := bbase (se 3 (by rfl) ⟨77078, by rfl⟩ : syracuseStep 411085 = 154157) (by norm_num)
theorem B509405 : Blo 338752 509405 := bbase (se 3 (by rfl) ⟨95513, by rfl⟩ : syracuseStep 509405 = 191027) (by norm_num)
theorem B509429 : Blo 338752 509429 := bbase (se 5 (by rfl) ⟨23879, by rfl⟩ : syracuseStep 509429 = 47759) (by norm_num)
theorem B509453 : Blo 338752 509453 := bbase (se 3 (by rfl) ⟨95522, by rfl⟩ : syracuseStep 509453 = 191045) (by norm_num)
theorem B575005 : Blo 338752 575005 := bbase (se 3 (by rfl) ⟨107813, by rfl⟩ : syracuseStep 575005 = 215627) (by norm_num)
theorem B509477 : Blo 338752 509477 := bbase (se 4 (by rfl) ⟨47763, by rfl⟩ : syracuseStep 509477 = 95527) (by norm_num)
theorem B509501 : Blo 338752 509501 := bbase (se 3 (by rfl) ⟨95531, by rfl⟩ : syracuseStep 509501 = 191063) (by norm_num)
theorem B345677 : Blo 338752 345677 := bbase (se 3 (by rfl) ⟨64814, by rfl⟩ : syracuseStep 345677 = 129629) (by norm_num)
theorem B509525 : Blo 338752 509525 := bbase (se 8 (by rfl) ⟨2985, by rfl⟩ : syracuseStep 509525 = 5971) (by norm_num)
theorem B509549 : Blo 338752 509549 := bbase (se 3 (by rfl) ⟨95540, by rfl⟩ : syracuseStep 509549 = 191081) (by norm_num)
theorem B575093 : Blo 338752 575093 := bbase (se 5 (by rfl) ⟨26957, by rfl⟩ : syracuseStep 575093 = 53915) (by norm_num)
theorem B509573 : Blo 338752 509573 := bbase (se 4 (by rfl) ⟨47772, by rfl⟩ : syracuseStep 509573 = 95545) (by norm_num)
theorem B509597 : Blo 338752 509597 := bbase (se 3 (by rfl) ⟨95549, by rfl⟩ : syracuseStep 509597 = 191099) (by norm_num)
theorem B509621 : Blo 338752 509621 := bbase (se 5 (by rfl) ⟨23888, by rfl⟩ : syracuseStep 509621 = 47777) (by norm_num)
theorem B509645 : Blo 338752 509645 := bbase (se 3 (by rfl) ⟨95558, by rfl⟩ : syracuseStep 509645 = 191117) (by norm_num)
theorem B509669 : Blo 338752 509669 := bbase (se 4 (by rfl) ⟨47781, by rfl⟩ : syracuseStep 509669 = 95563) (by norm_num)
theorem B1296101 : Blo 338752 1296101 := bbase (se 4 (by rfl) ⟨121509, by rfl⟩ : syracuseStep 1296101 = 243019) (by norm_num)
theorem B575221 : Blo 338752 575221 := bbase (se 5 (by rfl) ⟨26963, by rfl⟩ : syracuseStep 575221 = 53927) (by norm_num)
theorem B509693 : Blo 338752 509693 := bbase (se 3 (by rfl) ⟨95567, by rfl⟩ : syracuseStep 509693 = 191135) (by norm_num)
theorem B509717 : Blo 338752 509717 := bbase (se 6 (by rfl) ⟨11946, by rfl⟩ : syracuseStep 509717 = 23893) (by norm_num)
theorem B509741 : Blo 338752 509741 := bbase (se 3 (by rfl) ⟨95576, by rfl⟩ : syracuseStep 509741 = 191153) (by norm_num)
theorem B509765 : Blo 338752 509765 := bbase (se 4 (by rfl) ⟨47790, by rfl⟩ : syracuseStep 509765 = 95581) (by norm_num)
theorem B575309 : Blo 338752 575309 := bbase (se 3 (by rfl) ⟨107870, by rfl⟩ : syracuseStep 575309 = 215741) (by norm_num)
theorem B509789 : Blo 338752 509789 := bbase (se 3 (by rfl) ⟨95585, by rfl⟩ : syracuseStep 509789 = 191171) (by norm_num)
theorem B509813 : Blo 338752 509813 := bbase (se 5 (by rfl) ⟨23897, by rfl⟩ : syracuseStep 509813 = 47795) (by norm_num)
theorem B509837 : Blo 338752 509837 := bbase (se 3 (by rfl) ⟨95594, by rfl⟩ : syracuseStep 509837 = 191189) (by norm_num)
theorem B542629 : Blo 338752 542629 := bbase (se 4 (by rfl) ⟨50871, by rfl⟩ : syracuseStep 542629 = 101743) (by norm_num)
theorem B509861 : Blo 338752 509861 := bbase (se 4 (by rfl) ⟨47799, by rfl⟩ : syracuseStep 509861 = 95599) (by norm_num)
theorem B509885 : Blo 338752 509885 := bbase (se 3 (by rfl) ⟨95603, by rfl⟩ : syracuseStep 509885 = 191207) (by norm_num)
theorem B575437 : Blo 338752 575437 := bbase (se 3 (by rfl) ⟨107894, by rfl⟩ : syracuseStep 575437 = 215789) (by norm_num)
theorem B509909 : Blo 338752 509909 := bbase (se 7 (by rfl) ⟨5975, by rfl⟩ : syracuseStep 509909 = 11951) (by norm_num)
theorem B542693 : Blo 338752 542693 := bbase (se 4 (by rfl) ⟨50877, by rfl⟩ : syracuseStep 542693 = 101755) (by norm_num)
theorem B509933 : Blo 338752 509933 := bbase (se 3 (by rfl) ⟨95612, by rfl⟩ : syracuseStep 509933 = 191225) (by norm_num)
theorem B870389 : Blo 338752 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B509957 : Blo 338752 509957 := bbase (se 4 (by rfl) ⟨47808, by rfl⟩ : syracuseStep 509957 = 95617) (by norm_num)
theorem B509981 : Blo 338752 509981 := bbase (se 3 (by rfl) ⟨95621, by rfl⟩ : syracuseStep 509981 = 191243) (by norm_num)
theorem B575525 : Blo 338752 575525 := bbase (se 4 (by rfl) ⟨53955, by rfl⟩ : syracuseStep 575525 = 107911) (by norm_num)
theorem B510005 : Blo 338752 510005 := bbase (se 5 (by rfl) ⟨23906, by rfl⟩ : syracuseStep 510005 = 47813) (by norm_num)
theorem B968773 : Blo 338752 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B510029 : Blo 338752 510029 := bbase (se 3 (by rfl) ⟨95630, by rfl⟩ : syracuseStep 510029 = 191261) (by norm_num)
theorem B510053 : Blo 338752 510053 := bbase (se 4 (by rfl) ⟨47817, by rfl⟩ : syracuseStep 510053 = 95635) (by norm_num)
theorem B510077 : Blo 338752 510077 := bbase (se 3 (by rfl) ⟨95639, by rfl⟩ : syracuseStep 510077 = 191279) (by norm_num)
theorem B510101 : Blo 338752 510101 := bbase (se 6 (by rfl) ⟨11955, by rfl⟩ : syracuseStep 510101 = 23911) (by norm_num)
theorem B575653 : Blo 338752 575653 := bbase (se 4 (by rfl) ⟨53967, by rfl⟩ : syracuseStep 575653 = 107935) (by norm_num)
theorem B510125 : Blo 338752 510125 := bbase (se 3 (by rfl) ⟨95648, by rfl⟩ : syracuseStep 510125 = 191297) (by norm_num)
theorem B510149 : Blo 338752 510149 := bbase (se 4 (by rfl) ⟨47826, by rfl⟩ : syracuseStep 510149 = 95653) (by norm_num)
theorem B510173 : Blo 338752 510173 := bbase (se 3 (by rfl) ⟨95657, by rfl⟩ : syracuseStep 510173 = 191315) (by norm_num)
theorem B510197 : Blo 338752 510197 := bbase (se 5 (by rfl) ⟨23915, by rfl⟩ : syracuseStep 510197 = 47831) (by norm_num)
theorem B575741 : Blo 338752 575741 := bbase (se 3 (by rfl) ⟨107951, by rfl⟩ : syracuseStep 575741 = 215903) (by norm_num)
theorem B510221 : Blo 338752 510221 := bbase (se 3 (by rfl) ⟨95666, by rfl⟩ : syracuseStep 510221 = 191333) (by norm_num)
theorem B510245 : Blo 338752 510245 := bbase (se 4 (by rfl) ⟨47835, by rfl⟩ : syracuseStep 510245 = 95671) (by norm_num)
theorem B510269 : Blo 338752 510269 := bbase (se 3 (by rfl) ⟨95675, by rfl⟩ : syracuseStep 510269 = 191351) (by norm_num)
theorem B510293 : Blo 338752 510293 := bbase (se 10 (by rfl) ⟨747, by rfl⟩ : syracuseStep 510293 = 1495) (by norm_num)
theorem B510317 : Blo 338752 510317 := bbase (se 3 (by rfl) ⟨95684, by rfl⟩ : syracuseStep 510317 = 191369) (by norm_num)
theorem B575869 : Blo 338752 575869 := bbase (se 3 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 575869 = 215951) (by norm_num)
theorem B510341 : Blo 338752 510341 := bbase (se 4 (by rfl) ⟨47844, by rfl⟩ : syracuseStep 510341 = 95689) (by norm_num)
theorem B510365 : Blo 338752 510365 := bbase (se 3 (by rfl) ⟨95693, by rfl⟩ : syracuseStep 510365 = 191387) (by norm_num)
theorem B346537 : Blo 338752 346537 := bbase (se 2 (by rfl) ⟨129951, by rfl⟩ : syracuseStep 346537 = 259903) (by norm_num)
theorem B510389 : Blo 338752 510389 := bbase (se 5 (by rfl) ⟨23924, by rfl⟩ : syracuseStep 510389 = 47849) (by norm_num)
theorem B510413 : Blo 338752 510413 := bbase (se 3 (by rfl) ⟨95702, by rfl⟩ : syracuseStep 510413 = 191405) (by norm_num)
theorem B575957 : Blo 338752 575957 := bbase (se 7 (by rfl) ⟨6749, by rfl⟩ : syracuseStep 575957 = 13499) (by norm_num)
theorem B510437 : Blo 338752 510437 := bbase (se 4 (by rfl) ⟨47853, by rfl⟩ : syracuseStep 510437 = 95707) (by norm_num)
theorem B1722869 : Blo 338752 1722869 := bbase (se 5 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 1722869 = 161519) (by norm_num)
theorem B510461 : Blo 338752 510461 := bbase (se 3 (by rfl) ⟨95711, by rfl⟩ : syracuseStep 510461 = 191423) (by norm_num)
theorem B510485 : Blo 338752 510485 := bbase (se 6 (by rfl) ⟨11964, by rfl⟩ : syracuseStep 510485 = 23929) (by norm_num)
theorem B510509 : Blo 338752 510509 := bbase (se 3 (by rfl) ⟨95720, by rfl⟩ : syracuseStep 510509 = 191441) (by norm_num)
theorem B510533 : Blo 338752 510533 := bbase (se 4 (by rfl) ⟨47862, by rfl⟩ : syracuseStep 510533 = 95725) (by norm_num)
theorem B576085 : Blo 338752 576085 := bbase (se 8 (by rfl) ⟨3375, by rfl⟩ : syracuseStep 576085 = 6751) (by norm_num)
theorem B510557 : Blo 338752 510557 := bbase (se 3 (by rfl) ⟨95729, by rfl⟩ : syracuseStep 510557 = 191459) (by norm_num)
theorem B510581 : Blo 338752 510581 := bbase (se 5 (by rfl) ⟨23933, by rfl⟩ : syracuseStep 510581 = 47867) (by norm_num)
theorem B510605 : Blo 338752 510605 := bbase (se 3 (by rfl) ⟨95738, by rfl⟩ : syracuseStep 510605 = 191477) (by norm_num)
theorem B510629 : Blo 338752 510629 := bbase (se 4 (by rfl) ⟨47871, by rfl⟩ : syracuseStep 510629 = 95743) (by norm_num)
theorem B576173 : Blo 338752 576173 := bbase (se 3 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 576173 = 216065) (by norm_num)
theorem B510653 : Blo 338752 510653 := bbase (se 3 (by rfl) ⟨95747, by rfl⟩ : syracuseStep 510653 = 191495) (by norm_num)
theorem B510677 : Blo 338752 510677 := bbase (se 7 (by rfl) ⟨5984, by rfl⟩ : syracuseStep 510677 = 11969) (by norm_num)
theorem B9358037 : Blo 338752 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B510701 : Blo 338752 510701 := bbase (se 3 (by rfl) ⟨95756, by rfl⟩ : syracuseStep 510701 = 191513) (by norm_num)
theorem B510725 : Blo 338752 510725 := bbase (se 4 (by rfl) ⟨47880, by rfl⟩ : syracuseStep 510725 = 95761) (by norm_num)
theorem B510749 : Blo 338752 510749 := bbase (se 3 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 510749 = 191531) (by norm_num)
theorem B576301 : Blo 338752 576301 := bbase (se 3 (by rfl) ⟨108056, by rfl⟩ : syracuseStep 576301 = 216113) (by norm_num)
theorem B510773 : Blo 338752 510773 := bbase (se 5 (by rfl) ⟨23942, by rfl⟩ : syracuseStep 510773 = 47885) (by norm_num)
theorem B510797 : Blo 338752 510797 := bbase (se 3 (by rfl) ⟨95774, by rfl⟩ : syracuseStep 510797 = 191549) (by norm_num)
theorem B510821 : Blo 338752 510821 := bbase (se 4 (by rfl) ⟨47889, by rfl⟩ : syracuseStep 510821 = 95779) (by norm_num)
theorem B510845 : Blo 338752 510845 := bbase (se 3 (by rfl) ⟨95783, by rfl⟩ : syracuseStep 510845 = 191567) (by norm_num)
theorem B576389 : Blo 338752 576389 := bbase (se 4 (by rfl) ⟨54036, by rfl⟩ : syracuseStep 576389 = 108073) (by norm_num)
theorem B510869 : Blo 338752 510869 := bbase (se 6 (by rfl) ⟨11973, by rfl⟩ : syracuseStep 510869 = 23947) (by norm_num)
theorem B773029 : Blo 338752 773029 := bbase (se 4 (by rfl) ⟨72471, by rfl⟩ : syracuseStep 773029 = 144943) (by norm_num)
theorem B510893 : Blo 338752 510893 := bbase (se 3 (by rfl) ⟨95792, by rfl⟩ : syracuseStep 510893 = 191585) (by norm_num)
theorem B510917 : Blo 338752 510917 := bbase (se 4 (by rfl) ⟨47898, by rfl⟩ : syracuseStep 510917 = 95797) (by norm_num)
theorem B510941 : Blo 338752 510941 := bbase (se 3 (by rfl) ⟨95801, by rfl⟩ : syracuseStep 510941 = 191603) (by norm_num)
theorem B510965 : Blo 338752 510965 := bbase (se 5 (by rfl) ⟨23951, by rfl⟩ : syracuseStep 510965 = 47903) (by norm_num)
theorem B576517 : Blo 338752 576517 := bbase (se 4 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 576517 = 108097) (by norm_num)
theorem B510989 : Blo 338752 510989 := bbase (se 3 (by rfl) ⟨95810, by rfl⟩ : syracuseStep 510989 = 191621) (by norm_num)
theorem B511013 : Blo 338752 511013 := bbase (se 4 (by rfl) ⟨47907, by rfl⟩ : syracuseStep 511013 = 95815) (by norm_num)
theorem B511037 : Blo 338752 511037 := bbase (se 3 (by rfl) ⟨95819, by rfl⟩ : syracuseStep 511037 = 191639) (by norm_num)
theorem B511061 : Blo 338752 511061 := bbase (se 8 (by rfl) ⟨2994, by rfl⟩ : syracuseStep 511061 = 5989) (by norm_num)
theorem B576605 : Blo 338752 576605 := bbase (se 3 (by rfl) ⟨108113, by rfl⟩ : syracuseStep 576605 = 216227) (by norm_num)
theorem B511085 : Blo 338752 511085 := bbase (se 3 (by rfl) ⟨95828, by rfl⟩ : syracuseStep 511085 = 191657) (by norm_num)
theorem B511109 : Blo 338752 511109 := bbase (se 4 (by rfl) ⟨47916, by rfl⟩ : syracuseStep 511109 = 95833) (by norm_num)
theorem B511133 : Blo 338752 511133 := bbase (se 3 (by rfl) ⟨95837, by rfl⟩ : syracuseStep 511133 = 191675) (by norm_num)
theorem B511157 : Blo 338752 511157 := bbase (se 5 (by rfl) ⟨23960, by rfl⟩ : syracuseStep 511157 = 47921) (by norm_num)
theorem B511181 : Blo 338752 511181 := bbase (se 3 (by rfl) ⟨95846, by rfl⟩ : syracuseStep 511181 = 191693) (by norm_num)
theorem B576733 : Blo 338752 576733 := bbase (se 3 (by rfl) ⟨108137, by rfl⟩ : syracuseStep 576733 = 216275) (by norm_num)
theorem B511205 : Blo 338752 511205 := bbase (se 4 (by rfl) ⟨47925, by rfl⟩ : syracuseStep 511205 = 95851) (by norm_num)
theorem B1232101 : Blo 338752 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B511229 : Blo 338752 511229 := bbase (se 3 (by rfl) ⟨95855, by rfl⟩ : syracuseStep 511229 = 191711) (by norm_num)
theorem B544013 : Blo 338752 544013 := bbase (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) (by norm_num)
theorem B511253 : Blo 338752 511253 := bbase (se 6 (by rfl) ⟨11982, by rfl⟩ : syracuseStep 511253 = 23965) (by norm_num)
theorem B347413 : Blo 338752 347413 := bbase (se 6 (by rfl) ⟨8142, by rfl⟩ : syracuseStep 347413 = 16285) (by norm_num)
theorem B511277 : Blo 338752 511277 := bbase (se 3 (by rfl) ⟨95864, by rfl⟩ : syracuseStep 511277 = 191729) (by norm_num)
theorem B576821 : Blo 338752 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B511301 : Blo 338752 511301 := bbase (se 4 (by rfl) ⟨47934, by rfl⟩ : syracuseStep 511301 = 95869) (by norm_num)
theorem B511325 : Blo 338752 511325 := bbase (se 3 (by rfl) ⟨95873, by rfl⟩ : syracuseStep 511325 = 191747) (by norm_num)
theorem B511349 : Blo 338752 511349 := bbase (se 5 (by rfl) ⟨23969, by rfl⟩ : syracuseStep 511349 = 47939) (by norm_num)
theorem B511373 : Blo 338752 511373 := bbase (se 3 (by rfl) ⟨95882, by rfl⟩ : syracuseStep 511373 = 191765) (by norm_num)
theorem B511397 : Blo 338752 511397 := bbase (se 4 (by rfl) ⟨47943, by rfl⟩ : syracuseStep 511397 = 95887) (by norm_num)
theorem B576949 : Blo 338752 576949 := bbase (se 5 (by rfl) ⟨27044, by rfl⟩ : syracuseStep 576949 = 54089) (by norm_num)
theorem B511421 : Blo 338752 511421 := bbase (se 3 (by rfl) ⟨95891, by rfl⟩ : syracuseStep 511421 = 191783) (by norm_num)
theorem B544205 : Blo 338752 544205 := bbase (se 3 (by rfl) ⟨102038, by rfl⟩ : syracuseStep 544205 = 204077) (by norm_num)
theorem B511445 : Blo 338752 511445 := bbase (se 7 (by rfl) ⟨5993, by rfl⟩ : syracuseStep 511445 = 11987) (by norm_num)
theorem B511469 : Blo 338752 511469 := bbase (se 3 (by rfl) ⟨95900, by rfl⟩ : syracuseStep 511469 = 191801) (by norm_num)
theorem B511493 : Blo 338752 511493 := bbase (se 4 (by rfl) ⟨47952, by rfl⟩ : syracuseStep 511493 = 95905) (by norm_num)
theorem B577037 : Blo 338752 577037 := bbase (se 3 (by rfl) ⟨108194, by rfl⟩ : syracuseStep 577037 = 216389) (by norm_num)
theorem B511517 : Blo 338752 511517 := bbase (se 3 (by rfl) ⟨95909, by rfl⟩ : syracuseStep 511517 = 191819) (by norm_num)
theorem B511541 : Blo 338752 511541 := bbase (se 5 (by rfl) ⟨23978, by rfl⟩ : syracuseStep 511541 = 47957) (by norm_num)
theorem B544333 : Blo 338752 544333 := bbase (se 3 (by rfl) ⟨102062, by rfl⟩ : syracuseStep 544333 = 204125) (by norm_num)
theorem B511565 : Blo 338752 511565 := bbase (se 3 (by rfl) ⟨95918, by rfl⟩ : syracuseStep 511565 = 191837) (by norm_num)
theorem B511589 : Blo 338752 511589 := bbase (se 4 (by rfl) ⟨47961, by rfl⟩ : syracuseStep 511589 = 95923) (by norm_num)
theorem B511613 : Blo 338752 511613 := bbase (se 3 (by rfl) ⟨95927, by rfl⟩ : syracuseStep 511613 = 191855) (by norm_num)
theorem B577165 : Blo 338752 577165 := bbase (se 3 (by rfl) ⟨108218, by rfl⟩ : syracuseStep 577165 = 216437) (by norm_num)
theorem B511637 : Blo 338752 511637 := bbase (se 6 (by rfl) ⟨11991, by rfl⟩ : syracuseStep 511637 = 23983) (by norm_num)
theorem B511661 : Blo 338752 511661 := bbase (se 3 (by rfl) ⟨95936, by rfl⟩ : syracuseStep 511661 = 191873) (by norm_num)
theorem B511685 : Blo 338752 511685 := bbase (se 4 (by rfl) ⟨47970, by rfl⟩ : syracuseStep 511685 = 95941) (by norm_num)
theorem B511709 : Blo 338752 511709 := bbase (se 3 (by rfl) ⟨95945, by rfl⟩ : syracuseStep 511709 = 191891) (by norm_num)
theorem B577253 : Blo 338752 577253 := bbase (se 4 (by rfl) ⟨54117, by rfl⟩ : syracuseStep 577253 = 108235) (by norm_num)
theorem B511733 : Blo 338752 511733 := bbase (se 5 (by rfl) ⟨23987, by rfl⟩ : syracuseStep 511733 = 47975) (by norm_num)
theorem B1724165 : Blo 338752 1724165 := bbase (se 4 (by rfl) ⟨161640, by rfl⟩ : syracuseStep 1724165 = 323281) (by norm_num)
theorem B511757 : Blo 338752 511757 := bbase (se 3 (by rfl) ⟨95954, by rfl⟩ : syracuseStep 511757 = 191909) (by norm_num)
theorem B511781 : Blo 338752 511781 := bbase (se 4 (by rfl) ⟨47979, by rfl⟩ : syracuseStep 511781 = 95959) (by norm_num)
theorem B1298213 : Blo 338752 1298213 := bbase (se 4 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 1298213 = 243415) (by norm_num)
theorem B511805 : Blo 338752 511805 := bbase (se 3 (by rfl) ⟨95963, by rfl⟩ : syracuseStep 511805 = 191927) (by norm_num)
theorem B511829 : Blo 338752 511829 := bbase (se 9 (by rfl) ⟨1499, by rfl⟩ : syracuseStep 511829 = 2999) (by norm_num)
theorem B577381 : Blo 338752 577381 := bbase (se 4 (by rfl) ⟨54129, by rfl⟩ : syracuseStep 577381 = 108259) (by norm_num)
theorem B511853 : Blo 338752 511853 := bbase (se 3 (by rfl) ⟨95972, by rfl⟩ : syracuseStep 511853 = 191945) (by norm_num)
theorem B380785 : Blo 338752 380785 := bbase (se 2 (by rfl) ⟨142794, by rfl⟩ : syracuseStep 380785 = 285589) (by norm_num)
theorem B511877 : Blo 338752 511877 := bbase (se 4 (by rfl) ⟨47988, by rfl⟩ : syracuseStep 511877 = 95977) (by norm_num)
theorem B511901 : Blo 338752 511901 := bbase (se 3 (by rfl) ⟨95981, by rfl⟩ : syracuseStep 511901 = 191963) (by norm_num)
theorem B511925 : Blo 338752 511925 := bbase (se 5 (by rfl) ⟨23996, by rfl⟩ : syracuseStep 511925 = 47993) (by norm_num)
theorem B577469 : Blo 338752 577469 := bbase (se 3 (by rfl) ⟨108275, by rfl⟩ : syracuseStep 577469 = 216551) (by norm_num)
theorem B511949 : Blo 338752 511949 := bbase (se 3 (by rfl) ⟨95990, by rfl⟩ : syracuseStep 511949 = 191981) (by norm_num)
theorem B511973 : Blo 338752 511973 := bbase (se 4 (by rfl) ⟨47997, by rfl⟩ : syracuseStep 511973 = 95995) (by norm_num)
theorem B511997 : Blo 338752 511997 := bbase (se 3 (by rfl) ⟨95999, by rfl⟩ : syracuseStep 511997 = 191999) (by norm_num)
theorem B512021 : Blo 338752 512021 := bbase (se 6 (by rfl) ⟨12000, by rfl⟩ : syracuseStep 512021 = 24001) (by norm_num)
theorem B512045 : Blo 338752 512045 := bbase (se 3 (by rfl) ⟨96008, by rfl⟩ : syracuseStep 512045 = 192017) (by norm_num)
theorem B577597 : Blo 338752 577597 := bbase (se 3 (by rfl) ⟨108299, by rfl⟩ : syracuseStep 577597 = 216599) (by norm_num)
theorem B512069 : Blo 338752 512069 := bbase (se 4 (by rfl) ⟨48006, by rfl⟩ : syracuseStep 512069 = 96013) (by norm_num)
theorem B1298501 : Blo 338752 1298501 := bbase (se 4 (by rfl) ⟨121734, by rfl⟩ : syracuseStep 1298501 = 243469) (by norm_num)
theorem B872525 : Blo 338752 872525 := bbase (se 3 (by rfl) ⟨163598, by rfl⟩ : syracuseStep 872525 = 327197) (by norm_num)
theorem B512093 : Blo 338752 512093 := bbase (se 3 (by rfl) ⟨96017, by rfl⟩ : syracuseStep 512093 = 192035) (by norm_num)
theorem B413797 : Blo 338752 413797 := bbase (se 4 (by rfl) ⟨38793, by rfl⟩ : syracuseStep 413797 = 77587) (by norm_num)
theorem B512117 : Blo 338752 512117 := bbase (se 5 (by rfl) ⟨24005, by rfl⟩ : syracuseStep 512117 = 48011) (by norm_num)
theorem B512141 : Blo 338752 512141 := bbase (se 3 (by rfl) ⟨96026, by rfl⟩ : syracuseStep 512141 = 192053) (by norm_num)
theorem B2445461 : Blo 338752 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B577685 : Blo 338752 577685 := bbase (se 6 (by rfl) ⟨13539, by rfl⟩ : syracuseStep 577685 = 27079) (by norm_num)
theorem B512165 : Blo 338752 512165 := bbase (se 4 (by rfl) ⟨48015, by rfl⟩ : syracuseStep 512165 = 96031) (by norm_num)
theorem B381109 : Blo 338752 381109 := bbase (se 5 (by rfl) ⟨17864, by rfl⟩ : syracuseStep 381109 = 35729) (by norm_num)
theorem B512189 : Blo 338752 512189 := bbase (se 3 (by rfl) ⟨96035, by rfl⟩ : syracuseStep 512189 = 192071) (by norm_num)
theorem B544973 : Blo 338752 544973 := bbase (se 3 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 544973 = 204365) (by norm_num)
theorem B512213 : Blo 338752 512213 := bbase (se 7 (by rfl) ⟨6002, by rfl⟩ : syracuseStep 512213 = 12005) (by norm_num)
theorem B381145 : Blo 338752 381145 := bbase (se 2 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 381145 = 285859) (by norm_num)
theorem B512237 : Blo 338752 512237 := bbase (se 3 (by rfl) ⟨96044, by rfl⟩ : syracuseStep 512237 = 192089) (by norm_num)
theorem B381181 : Blo 338752 381181 := bbase (se 3 (by rfl) ⟨71471, by rfl⟩ : syracuseStep 381181 = 142943) (by norm_num)
theorem B512261 : Blo 338752 512261 := bbase (se 4 (by rfl) ⟨48024, by rfl⟩ : syracuseStep 512261 = 96049) (by norm_num)
theorem B577813 : Blo 338752 577813 := bbase (se 6 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 577813 = 27085) (by norm_num)
theorem B512285 : Blo 338752 512285 := bbase (se 3 (by rfl) ⟨96053, by rfl⟩ : syracuseStep 512285 = 192107) (by norm_num)
theorem B381217 : Blo 338752 381217 := bbase (se 2 (by rfl) ⟨142956, by rfl⟩ : syracuseStep 381217 = 285913) (by norm_num)
theorem B643373 : Blo 338752 643373 := bbase (se 3 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 643373 = 241265) (by norm_num)
theorem B512309 : Blo 338752 512309 := bbase (se 5 (by rfl) ⟨24014, by rfl⟩ : syracuseStep 512309 = 48029) (by norm_num)
theorem B381253 : Blo 338752 381253 := bbase (se 4 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 381253 = 71485) (by norm_num)
theorem B512333 : Blo 338752 512333 := bbase (se 3 (by rfl) ⟨96062, by rfl⟩ : syracuseStep 512333 = 192125) (by norm_num)
theorem B512357 : Blo 338752 512357 := bbase (se 4 (by rfl) ⟨48033, by rfl⟩ : syracuseStep 512357 = 96067) (by norm_num)
theorem B381289 : Blo 338752 381289 := bbase (se 2 (by rfl) ⟨142983, by rfl⟩ : syracuseStep 381289 = 285967) (by norm_num)
theorem B577901 : Blo 338752 577901 := bbase (se 3 (by rfl) ⟨108356, by rfl⟩ : syracuseStep 577901 = 216713) (by norm_num)
theorem B512381 : Blo 338752 512381 := bbase (se 3 (by rfl) ⟨96071, by rfl⟩ : syracuseStep 512381 = 192143) (by norm_num)
theorem B414085 : Blo 338752 414085 := bbase (se 4 (by rfl) ⟨38820, by rfl⟩ : syracuseStep 414085 = 77641) (by norm_num)
theorem B381325 : Blo 338752 381325 := bbase (se 3 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 381325 = 142997) (by norm_num)
theorem B512405 : Blo 338752 512405 := bbase (se 6 (by rfl) ⟨12009, by rfl⟩ : syracuseStep 512405 = 24019) (by norm_num)
theorem B1462693 : Blo 338752 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B512429 : Blo 338752 512429 := bbase (se 3 (by rfl) ⟨96080, by rfl⟩ : syracuseStep 512429 = 192161) (by norm_num)
theorem B381361 : Blo 338752 381361 := bbase (se 2 (by rfl) ⟨143010, by rfl⟩ : syracuseStep 381361 = 286021) (by norm_num)
theorem B512453 : Blo 338752 512453 := bbase (se 4 (by rfl) ⟨48042, by rfl⟩ : syracuseStep 512453 = 96085) (by norm_num)
theorem B381397 : Blo 338752 381397 := bbase (se 7 (by rfl) ⟨4469, by rfl⟩ : syracuseStep 381397 = 8939) (by norm_num)
theorem B512477 : Blo 338752 512477 := bbase (se 3 (by rfl) ⟨96089, by rfl⟩ : syracuseStep 512477 = 192179) (by norm_num)
theorem B578029 : Blo 338752 578029 := bbase (se 3 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 578029 = 216761) (by norm_num)
theorem B512501 : Blo 338752 512501 := bbase (se 5 (by rfl) ⟨24023, by rfl⟩ : syracuseStep 512501 = 48047) (by norm_num)
theorem B381433 : Blo 338752 381433 := bbase (se 2 (by rfl) ⟨143037, by rfl⟩ : syracuseStep 381433 = 286075) (by norm_num)
theorem B512525 : Blo 338752 512525 := bbase (se 3 (by rfl) ⟨96098, by rfl⟩ : syracuseStep 512525 = 192197) (by norm_num)
theorem B381469 : Blo 338752 381469 := bbase (se 3 (by rfl) ⟨71525, by rfl⟩ : syracuseStep 381469 = 143051) (by norm_num)
theorem B512549 : Blo 338752 512549 := bbase (se 4 (by rfl) ⟨48051, by rfl⟩ : syracuseStep 512549 = 96103) (by norm_num)
theorem B512573 : Blo 338752 512573 := bbase (se 3 (by rfl) ⟨96107, by rfl⟩ : syracuseStep 512573 = 192215) (by norm_num)
theorem B381505 : Blo 338752 381505 := bbase (se 2 (by rfl) ⟨143064, by rfl⟩ : syracuseStep 381505 = 286129) (by norm_num)
theorem B578117 : Blo 338752 578117 := bbase (se 4 (by rfl) ⟨54198, by rfl⟩ : syracuseStep 578117 = 108397) (by norm_num)
theorem B512597 : Blo 338752 512597 := bbase (se 8 (by rfl) ⟨3003, by rfl⟩ : syracuseStep 512597 = 6007) (by norm_num)
theorem B381541 : Blo 338752 381541 := bbase (se 4 (by rfl) ⟨35769, by rfl⟩ : syracuseStep 381541 = 71539) (by norm_num)
theorem B512621 : Blo 338752 512621 := bbase (se 3 (by rfl) ⟨96116, by rfl⟩ : syracuseStep 512621 = 192233) (by norm_num)
theorem B512645 : Blo 338752 512645 := bbase (se 4 (by rfl) ⟨48060, by rfl⟩ : syracuseStep 512645 = 96121) (by norm_num)
theorem B381577 : Blo 338752 381577 := bbase (se 2 (by rfl) ⟨143091, by rfl⟩ : syracuseStep 381577 = 286183) (by norm_num)
theorem B545429 : Blo 338752 545429 := bbase (se 6 (by rfl) ⟨12783, by rfl⟩ : syracuseStep 545429 = 25567) (by norm_num)
theorem B512669 : Blo 338752 512669 := bbase (se 3 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 512669 = 192251) (by norm_num)
theorem B381613 : Blo 338752 381613 := bbase (se 3 (by rfl) ⟨71552, by rfl⟩ : syracuseStep 381613 = 143105) (by norm_num)
theorem B512693 : Blo 338752 512693 := bbase (se 5 (by rfl) ⟨24032, by rfl⟩ : syracuseStep 512693 = 48065) (by norm_num)
theorem B578245 : Blo 338752 578245 := bbase (se 4 (by rfl) ⟨54210, by rfl⟩ : syracuseStep 578245 = 108421) (by norm_num)
theorem B512717 : Blo 338752 512717 := bbase (se 3 (by rfl) ⟨96134, by rfl⟩ : syracuseStep 512717 = 192269) (by norm_num)
theorem B381649 : Blo 338752 381649 := bbase (se 2 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 381649 = 286237) (by norm_num)
theorem B512741 : Blo 338752 512741 := bbase (se 4 (by rfl) ⟨48069, by rfl⟩ : syracuseStep 512741 = 96139) (by norm_num)
theorem B381685 : Blo 338752 381685 := bbase (se 5 (by rfl) ⟨17891, by rfl⟩ : syracuseStep 381685 = 35783) (by norm_num)
theorem B512765 : Blo 338752 512765 := bbase (se 3 (by rfl) ⟨96143, by rfl⟩ : syracuseStep 512765 = 192287) (by norm_num)
theorem B512789 : Blo 338752 512789 := bbase (se 6 (by rfl) ⟨12018, by rfl⟩ : syracuseStep 512789 = 24037) (by norm_num)
theorem B381721 : Blo 338752 381721 := bbase (se 2 (by rfl) ⟨143145, by rfl⟩ : syracuseStep 381721 = 286291) (by norm_num)
theorem B578333 : Blo 338752 578333 := bbase (se 3 (by rfl) ⟨108437, by rfl⟩ : syracuseStep 578333 = 216875) (by norm_num)
theorem B512813 : Blo 338752 512813 := bbase (se 3 (by rfl) ⟨96152, by rfl⟩ : syracuseStep 512813 = 192305) (by norm_num)
theorem B381757 : Blo 338752 381757 := bbase (se 3 (by rfl) ⟨71579, by rfl⟩ : syracuseStep 381757 = 143159) (by norm_num)
theorem B512837 : Blo 338752 512837 := bbase (se 4 (by rfl) ⟨48078, by rfl⟩ : syracuseStep 512837 = 96157) (by norm_num)
theorem B611165 : Blo 338752 611165 := bbase (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) (by norm_num)
theorem B512861 : Blo 338752 512861 := bbase (se 3 (by rfl) ⟨96161, by rfl⟩ : syracuseStep 512861 = 192323) (by norm_num)
theorem B381793 : Blo 338752 381793 := bbase (se 2 (by rfl) ⟨143172, by rfl⟩ : syracuseStep 381793 = 286345) (by norm_num)
theorem B971621 : Blo 338752 971621 := bbase (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) (by norm_num)
theorem B545653 : Blo 338752 545653 := bbase (se 5 (by rfl) ⟨25577, by rfl⟩ : syracuseStep 545653 = 51155) (by norm_num)
theorem B512885 : Blo 338752 512885 := bbase (se 5 (by rfl) ⟨24041, by rfl⟩ : syracuseStep 512885 = 48083) (by norm_num)
theorem B381829 : Blo 338752 381829 := bbase (se 4 (by rfl) ⟨35796, by rfl⟩ : syracuseStep 381829 = 71593) (by norm_num)
theorem B512909 : Blo 338752 512909 := bbase (se 3 (by rfl) ⟨96170, by rfl⟩ : syracuseStep 512909 = 192341) (by norm_num)
theorem B512933 : Blo 338752 512933 := bbase (se 4 (by rfl) ⟨48087, by rfl⟩ : syracuseStep 512933 = 96175) (by norm_num)
theorem B381865 : Blo 338752 381865 := bbase (se 2 (by rfl) ⟨143199, by rfl⟩ : syracuseStep 381865 = 286399) (by norm_num)
theorem B545717 : Blo 338752 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B512957 : Blo 338752 512957 := bbase (se 3 (by rfl) ⟨96179, by rfl⟩ : syracuseStep 512957 = 192359) (by norm_num)
theorem B381901 : Blo 338752 381901 := bbase (se 3 (by rfl) ⟨71606, by rfl⟩ : syracuseStep 381901 = 143213) (by norm_num)
theorem B512981 : Blo 338752 512981 := bbase (se 7 (by rfl) ⟨6011, by rfl⟩ : syracuseStep 512981 = 12023) (by norm_num)
theorem B513005 : Blo 338752 513005 := bbase (se 3 (by rfl) ⟨96188, by rfl⟩ : syracuseStep 513005 = 192377) (by norm_num)
theorem B381937 : Blo 338752 381937 := bbase (se 2 (by rfl) ⟨143226, by rfl⟩ : syracuseStep 381937 = 286453) (by norm_num)
theorem B513029 : Blo 338752 513029 := bbase (se 4 (by rfl) ⟨48096, by rfl⟩ : syracuseStep 513029 = 96193) (by norm_num)
theorem B414733 : Blo 338752 414733 := bbase (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) (by norm_num)
theorem B381973 : Blo 338752 381973 := bbase (se 6 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 381973 = 17905) (by norm_num)
theorem B1725461 : Blo 338752 1725461 := bbase (se 6 (by rfl) ⟨40440, by rfl⟩ : syracuseStep 1725461 = 80881) (by norm_num)
theorem B644125 : Blo 338752 644125 := bbase (se 3 (by rfl) ⟨120773, by rfl⟩ : syracuseStep 644125 = 241547) (by norm_num)
theorem B513053 : Blo 338752 513053 := bbase (se 3 (by rfl) ⟨96197, by rfl⟩ : syracuseStep 513053 = 192395) (by norm_num)
theorem B611381 : Blo 338752 611381 := bbase (se 5 (by rfl) ⟨28658, by rfl⟩ : syracuseStep 611381 = 57317) (by norm_num)
theorem B545845 : Blo 338752 545845 := bbase (se 5 (by rfl) ⟨25586, by rfl⟩ : syracuseStep 545845 = 51173) (by norm_num)
theorem B513077 : Blo 338752 513077 := bbase (se 5 (by rfl) ⟨24050, by rfl⟩ : syracuseStep 513077 = 48101) (by norm_num)
theorem B382009 : Blo 338752 382009 := bbase (se 2 (by rfl) ⟨143253, by rfl⟩ : syracuseStep 382009 = 286507) (by norm_num)
theorem B513101 : Blo 338752 513101 := bbase (se 3 (by rfl) ⟨96206, by rfl⟩ : syracuseStep 513101 = 192413) (by norm_num)
theorem B1168469 : Blo 338752 1168469 := bbase (se 8 (by rfl) ⟨6846, by rfl⟩ : syracuseStep 1168469 = 13693) (by norm_num)
theorem B382045 : Blo 338752 382045 := bbase (se 3 (by rfl) ⟨71633, by rfl⟩ : syracuseStep 382045 = 143267) (by norm_num)
theorem B513125 : Blo 338752 513125 := bbase (se 4 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 513125 = 96211) (by norm_num)
theorem B349309 : Blo 338752 349309 := bbase (se 3 (by rfl) ⟨65495, by rfl⟩ : syracuseStep 349309 = 130991) (by norm_num)
theorem B513149 : Blo 338752 513149 := bbase (se 3 (by rfl) ⟨96215, by rfl⟩ : syracuseStep 513149 = 192431) (by norm_num)
theorem B382081 : Blo 338752 382081 := bbase (se 2 (by rfl) ⟨143280, by rfl⟩ : syracuseStep 382081 = 286561) (by norm_num)
theorem B513173 : Blo 338752 513173 := bbase (se 6 (by rfl) ⟨12027, by rfl⟩ : syracuseStep 513173 = 24055) (by norm_num)
theorem B382117 : Blo 338752 382117 := bbase (se 4 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 382117 = 71647) (by norm_num)
theorem B644269 : Blo 338752 644269 := bbase (se 3 (by rfl) ⟨120800, by rfl⟩ : syracuseStep 644269 = 241601) (by norm_num)
theorem B513197 : Blo 338752 513197 := bbase (se 3 (by rfl) ⟨96224, by rfl⟩ : syracuseStep 513197 = 192449) (by norm_num)
theorem B513221 : Blo 338752 513221 := bbase (se 4 (by rfl) ⟨48114, by rfl⟩ : syracuseStep 513221 = 96229) (by norm_num)
theorem B382153 : Blo 338752 382153 := bbase (se 2 (by rfl) ⟨143307, by rfl⟩ : syracuseStep 382153 = 286615) (by norm_num)
theorem B513245 : Blo 338752 513245 := bbase (se 3 (by rfl) ⟨96233, by rfl⟩ : syracuseStep 513245 = 192467) (by norm_num)
theorem B1299685 : Blo 338752 1299685 := bbase (se 4 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 1299685 = 243691) (by norm_num)
theorem B382189 : Blo 338752 382189 := bbase (se 3 (by rfl) ⟨71660, by rfl⟩ : syracuseStep 382189 = 143321) (by norm_num)
theorem B513269 : Blo 338752 513269 := bbase (se 5 (by rfl) ⟨24059, by rfl⟩ : syracuseStep 513269 = 48119) (by norm_num)
theorem B513293 : Blo 338752 513293 := bbase (se 3 (by rfl) ⟨96242, by rfl⟩ : syracuseStep 513293 = 192485) (by norm_num)
theorem B382225 : Blo 338752 382225 := bbase (se 2 (by rfl) ⟨143334, by rfl⟩ : syracuseStep 382225 = 286669) (by norm_num)
theorem B513317 : Blo 338752 513317 := bbase (se 4 (by rfl) ⟨48123, by rfl⟩ : syracuseStep 513317 = 96247) (by norm_num)
theorem B382261 : Blo 338752 382261 := bbase (se 5 (by rfl) ⟨17918, by rfl⟩ : syracuseStep 382261 = 35837) (by norm_num)
theorem B513341 : Blo 338752 513341 := bbase (se 3 (by rfl) ⟨96251, by rfl⟩ : syracuseStep 513341 = 192503) (by norm_num)
theorem B644429 : Blo 338752 644429 := bbase (se 3 (by rfl) ⟨120830, by rfl⟩ : syracuseStep 644429 = 241661) (by norm_num)
theorem B2905429 : Blo 338752 2905429 := bbase (se 16 (by rfl) ⟨66, by rfl⟩ : syracuseStep 2905429 = 133) (by norm_num)
theorem B513365 : Blo 338752 513365 := bbase (se 15 (by rfl) ⟨23, by rfl⟩ : syracuseStep 513365 = 47) (by norm_num)
theorem B382297 : Blo 338752 382297 := bbase (se 2 (by rfl) ⟨143361, by rfl⟩ : syracuseStep 382297 = 286723) (by norm_num)
theorem B513389 : Blo 338752 513389 := bbase (se 3 (by rfl) ⟨96260, by rfl⟩ : syracuseStep 513389 = 192521) (by norm_num)
theorem B382333 : Blo 338752 382333 := bbase (se 3 (by rfl) ⟨71687, by rfl⟩ : syracuseStep 382333 = 143375) (by norm_num)
theorem B513413 : Blo 338752 513413 := bbase (se 4 (by rfl) ⟨48132, by rfl⟩ : syracuseStep 513413 = 96265) (by norm_num)
theorem B513437 : Blo 338752 513437 := bbase (se 3 (by rfl) ⟨96269, by rfl⟩ : syracuseStep 513437 = 192539) (by norm_num)
theorem B382369 : Blo 338752 382369 := bbase (se 2 (by rfl) ⟨143388, by rfl⟩ : syracuseStep 382369 = 286777) (by norm_num)
theorem B513461 : Blo 338752 513461 := bbase (se 5 (by rfl) ⟨24068, by rfl⟩ : syracuseStep 513461 = 48137) (by norm_num)
theorem B382405 : Blo 338752 382405 := bbase (se 4 (by rfl) ⟨35850, by rfl⟩ : syracuseStep 382405 = 71701) (by norm_num)
theorem B513485 : Blo 338752 513485 := bbase (se 3 (by rfl) ⟨96278, by rfl⟩ : syracuseStep 513485 = 192557) (by norm_num)
theorem B644573 : Blo 338752 644573 := bbase (se 3 (by rfl) ⟨120857, by rfl⟩ : syracuseStep 644573 = 241715) (by norm_num)
theorem B513509 : Blo 338752 513509 := bbase (se 4 (by rfl) ⟨48141, by rfl⟩ : syracuseStep 513509 = 96283) (by norm_num)
theorem B382441 : Blo 338752 382441 := bbase (se 2 (by rfl) ⟨143415, by rfl⟩ : syracuseStep 382441 = 286831) (by norm_num)
theorem B513533 : Blo 338752 513533 := bbase (se 3 (by rfl) ⟨96287, by rfl⟩ : syracuseStep 513533 = 192575) (by norm_num)
theorem B382477 : Blo 338752 382477 := bbase (se 3 (by rfl) ⟨71714, by rfl⟩ : syracuseStep 382477 = 143429) (by norm_num)
theorem B513557 : Blo 338752 513557 := bbase (se 6 (by rfl) ⟨12036, by rfl⟩ : syracuseStep 513557 = 24073) (by norm_num)
theorem B1299989 : Blo 338752 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B513581 : Blo 338752 513581 := bbase (se 3 (by rfl) ⟨96296, by rfl⟩ : syracuseStep 513581 = 192593) (by norm_num)
theorem B382513 : Blo 338752 382513 := bbase (se 2 (by rfl) ⟨143442, by rfl⟩ : syracuseStep 382513 = 286885) (by norm_num)
theorem B513605 : Blo 338752 513605 := bbase (se 4 (by rfl) ⟨48150, by rfl⟩ : syracuseStep 513605 = 96301) (by norm_num)
theorem B382549 : Blo 338752 382549 := bbase (se 8 (by rfl) ⟨2241, by rfl⟩ : syracuseStep 382549 = 4483) (by norm_num)
theorem B513629 : Blo 338752 513629 := bbase (se 3 (by rfl) ⟨96305, by rfl⟩ : syracuseStep 513629 = 192611) (by norm_num)
theorem B513653 : Blo 338752 513653 := bbase (se 5 (by rfl) ⟨24077, by rfl⟩ : syracuseStep 513653 = 48155) (by norm_num)
theorem B382585 : Blo 338752 382585 := bbase (se 2 (by rfl) ⟨143469, by rfl⟩ : syracuseStep 382585 = 286939) (by norm_num)
theorem B513677 : Blo 338752 513677 := bbase (se 3 (by rfl) ⟨96314, by rfl⟩ : syracuseStep 513677 = 192629) (by norm_num)
theorem B382621 : Blo 338752 382621 := bbase (se 3 (by rfl) ⟨71741, by rfl⟩ : syracuseStep 382621 = 143483) (by norm_num)
theorem B513701 : Blo 338752 513701 := bbase (se 4 (by rfl) ⟨48159, by rfl⟩ : syracuseStep 513701 = 96319) (by norm_num)
theorem B513725 : Blo 338752 513725 := bbase (se 3 (by rfl) ⟨96323, by rfl⟩ : syracuseStep 513725 = 192647) (by norm_num)
theorem B382657 : Blo 338752 382657 := bbase (se 2 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 382657 = 286993) (by norm_num)
theorem B513749 : Blo 338752 513749 := bbase (se 7 (by rfl) ⟨6020, by rfl⟩ : syracuseStep 513749 = 12041) (by norm_num)
theorem B382693 : Blo 338752 382693 := bbase (se 4 (by rfl) ⟨35877, by rfl⟩ : syracuseStep 382693 = 71755) (by norm_num)
theorem B513773 : Blo 338752 513773 := bbase (se 3 (by rfl) ⟨96332, by rfl⟩ : syracuseStep 513773 = 192665) (by norm_num)
theorem B415477 : Blo 338752 415477 := bbase (se 5 (by rfl) ⟨19475, by rfl⟩ : syracuseStep 415477 = 38951) (by norm_num)
theorem B644861 : Blo 338752 644861 := bbase (se 3 (by rfl) ⟨120911, by rfl⟩ : syracuseStep 644861 = 241823) (by norm_num)
theorem B513797 : Blo 338752 513797 := bbase (se 4 (by rfl) ⟨48168, by rfl⟩ : syracuseStep 513797 = 96337) (by norm_num)
theorem B382729 : Blo 338752 382729 := bbase (se 2 (by rfl) ⟨143523, by rfl⟩ : syracuseStep 382729 = 287047) (by norm_num)
theorem B513821 : Blo 338752 513821 := bbase (se 3 (by rfl) ⟨96341, by rfl⟩ : syracuseStep 513821 = 192683) (by norm_num)
theorem B382765 : Blo 338752 382765 := bbase (se 3 (by rfl) ⟨71768, by rfl⟩ : syracuseStep 382765 = 143537) (by norm_num)
theorem B2578229 : Blo 338752 2578229 := bbase (se 5 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 2578229 = 241709) (by norm_num)
theorem B513845 : Blo 338752 513845 := bbase (se 5 (by rfl) ⟨24086, by rfl⟩ : syracuseStep 513845 = 48173) (by norm_num)
theorem B513869 : Blo 338752 513869 := bbase (se 3 (by rfl) ⟨96350, by rfl⟩ : syracuseStep 513869 = 192701) (by norm_num)
theorem B382801 : Blo 338752 382801 := bbase (se 2 (by rfl) ⟨143550, by rfl⟩ : syracuseStep 382801 = 287101) (by norm_num)
theorem B513893 : Blo 338752 513893 := bbase (se 4 (by rfl) ⟨48177, by rfl⟩ : syracuseStep 513893 = 96355) (by norm_num)
theorem B382837 : Blo 338752 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B513917 : Blo 338752 513917 := bbase (se 3 (by rfl) ⟨96359, by rfl⟩ : syracuseStep 513917 = 192719) (by norm_num)
theorem B645013 : Blo 338752 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B513941 : Blo 338752 513941 := bbase (se 6 (by rfl) ⟨12045, by rfl⟩ : syracuseStep 513941 = 24091) (by norm_num)
theorem B382873 : Blo 338752 382873 := bbase (se 2 (by rfl) ⟨143577, by rfl⟩ : syracuseStep 382873 = 287155) (by norm_num)
theorem B513965 : Blo 338752 513965 := bbase (se 3 (by rfl) ⟨96368, by rfl⟩ : syracuseStep 513965 = 192737) (by norm_num)
theorem B382909 : Blo 338752 382909 := bbase (se 3 (by rfl) ⟨71795, by rfl⟩ : syracuseStep 382909 = 143591) (by norm_num)
theorem B513989 : Blo 338752 513989 := bbase (se 4 (by rfl) ⟨48186, by rfl⟩ : syracuseStep 513989 = 96373) (by norm_num)
theorem B514013 : Blo 338752 514013 := bbase (se 3 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 514013 = 192755) (by norm_num)
theorem B382945 : Blo 338752 382945 := bbase (se 2 (by rfl) ⟨143604, by rfl⟩ : syracuseStep 382945 = 287209) (by norm_num)
theorem B514037 : Blo 338752 514037 := bbase (se 5 (by rfl) ⟨24095, by rfl⟩ : syracuseStep 514037 = 48191) (by norm_num)
theorem B382981 : Blo 338752 382981 := bbase (se 4 (by rfl) ⟨35904, by rfl⟩ : syracuseStep 382981 = 71809) (by norm_num)
theorem B972805 : Blo 338752 972805 := bbase (se 4 (by rfl) ⟨91200, by rfl⟩ : syracuseStep 972805 = 182401) (by norm_num)
theorem B514061 : Blo 338752 514061 := bbase (se 3 (by rfl) ⟨96386, by rfl⟩ : syracuseStep 514061 = 192773) (by norm_num)
theorem B514085 : Blo 338752 514085 := bbase (se 4 (by rfl) ⟨48195, by rfl⟩ : syracuseStep 514085 = 96391) (by norm_num)
theorem B383017 : Blo 338752 383017 := bbase (se 2 (by rfl) ⟨143631, by rfl⟩ : syracuseStep 383017 = 287263) (by norm_num)
theorem B514109 : Blo 338752 514109 := bbase (se 3 (by rfl) ⟨96395, by rfl⟩ : syracuseStep 514109 = 192791) (by norm_num)
theorem B383053 : Blo 338752 383053 := bbase (se 3 (by rfl) ⟨71822, by rfl⟩ : syracuseStep 383053 = 143645) (by norm_num)
theorem B612461 : Blo 338752 612461 := bbase (se 3 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 612461 = 229673) (by norm_num)
theorem B383089 : Blo 338752 383089 := bbase (se 2 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 383089 = 287317) (by norm_num)
theorem B383125 : Blo 338752 383125 := bbase (se 6 (by rfl) ⟨8979, by rfl⟩ : syracuseStep 383125 = 17959) (by norm_num)
theorem B972965 : Blo 338752 972965 := bbase (se 4 (by rfl) ⟨91215, by rfl⟩ : syracuseStep 972965 = 182431) (by norm_num)
theorem B383161 : Blo 338752 383161 := bbase (se 2 (by rfl) ⟨143685, by rfl⟩ : syracuseStep 383161 = 287371) (by norm_num)
theorem B645317 : Blo 338752 645317 := bbase (se 4 (by rfl) ⟨60498, by rfl⟩ : syracuseStep 645317 = 120997) (by norm_num)
theorem B383197 : Blo 338752 383197 := bbase (se 3 (by rfl) ⟨71849, by rfl⟩ : syracuseStep 383197 = 143699) (by norm_num)
theorem B547069 : Blo 338752 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B383233 : Blo 338752 383233 := bbase (se 2 (by rfl) ⟨143712, by rfl⟩ : syracuseStep 383233 = 287425) (by norm_num)
theorem B1562885 : Blo 338752 1562885 := bbase (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) (by norm_num)
theorem B776461 : Blo 338752 776461 := bbase (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) (by norm_num)
theorem B383269 : Blo 338752 383269 := bbase (se 4 (by rfl) ⟨35931, by rfl⟩ : syracuseStep 383269 = 71863) (by norm_num)
theorem B1726757 : Blo 338752 1726757 := bbase (se 4 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 1726757 = 323767) (by norm_num)
theorem B383305 : Blo 338752 383305 := bbase (se 2 (by rfl) ⟨143739, by rfl⟩ : syracuseStep 383305 = 287479) (by norm_num)
theorem B612685 : Blo 338752 612685 := bbase (se 3 (by rfl) ⟨114878, by rfl⟩ : syracuseStep 612685 = 229757) (by norm_num)
theorem B383341 : Blo 338752 383341 := bbase (se 3 (by rfl) ⟨71876, by rfl⟩ : syracuseStep 383341 = 143753) (by norm_num)
theorem B579965 : Blo 338752 579965 := bbase (se 3 (by rfl) ⟨108743, by rfl⟩ : syracuseStep 579965 = 217487) (by norm_num)
theorem B383377 : Blo 338752 383377 := bbase (se 2 (by rfl) ⟨143766, by rfl⟩ : syracuseStep 383377 = 287533) (by norm_num)
theorem B973205 : Blo 338752 973205 := bbase (se 6 (by rfl) ⟨22809, by rfl⟩ : syracuseStep 973205 = 45619) (by norm_num)
theorem B383393 : Blo 338752 383393 := bbase (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) (by norm_num)
theorem B383413 : Blo 338752 383413 := bbase (se 5 (by rfl) ⟨17972, by rfl⟩ : syracuseStep 383413 = 35945) (by norm_num)
theorem B2775509 : Blo 338752 2775509 := bbase (se 7 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 2775509 = 65051) (by norm_num)
theorem B383449 : Blo 338752 383449 := bbase (se 2 (by rfl) ⟨143793, by rfl⟩ : syracuseStep 383449 = 287587) (by norm_num)
theorem B383485 : Blo 338752 383485 := bbase (se 3 (by rfl) ⟨71903, by rfl⟩ : syracuseStep 383485 = 143807) (by norm_num)
theorem B1628693 : Blo 338752 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B383521 : Blo 338752 383521 := bbase (se 2 (by rfl) ⟨143820, by rfl⟩ : syracuseStep 383521 = 287641) (by norm_num)
theorem B383557 : Blo 338752 383557 := bbase (se 4 (by rfl) ⟨35958, by rfl⟩ : syracuseStep 383557 = 71917) (by norm_num)
theorem B973397 : Blo 338752 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B350821 : Blo 338752 350821 := bbase (se 4 (by rfl) ⟨32889, by rfl⟩ : syracuseStep 350821 = 65779) (by norm_num)
theorem B383593 : Blo 338752 383593 := bbase (se 2 (by rfl) ⟨143847, by rfl⟩ : syracuseStep 383593 = 287695) (by norm_num)
theorem B383629 : Blo 338752 383629 := bbase (se 3 (by rfl) ⟨71930, by rfl⟩ : syracuseStep 383629 = 143861) (by norm_num)
theorem B7002773 : Blo 338752 7002773 := bbase (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) (by norm_num)
theorem B383665 : Blo 338752 383665 := bbase (se 2 (by rfl) ⟨143874, by rfl⟩ : syracuseStep 383665 = 287749) (by norm_num)
theorem B383701 : Blo 338752 383701 := bbase (se 7 (by rfl) ⟨4496, by rfl⟩ : syracuseStep 383701 = 8993) (by norm_num)
theorem B383737 : Blo 338752 383737 := bbase (se 2 (by rfl) ⟨143901, by rfl⟩ : syracuseStep 383737 = 287803) (by norm_num)
theorem B383773 : Blo 338752 383773 := bbase (se 3 (by rfl) ⟨71957, by rfl⟩ : syracuseStep 383773 = 143915) (by norm_num)
theorem B383809 : Blo 338752 383809 := bbase (se 2 (by rfl) ⟨143928, by rfl⟩ : syracuseStep 383809 = 287857) (by norm_num)
theorem B383845 : Blo 338752 383845 := bbase (se 4 (by rfl) ⟨35985, by rfl⟩ : syracuseStep 383845 = 71971) (by norm_num)
theorem B383881 : Blo 338752 383881 := bbase (se 2 (by rfl) ⟨143955, by rfl⟩ : syracuseStep 383881 = 287911) (by norm_num)
theorem B547741 : Blo 338752 547741 := bbase (se 3 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 547741 = 205403) (by norm_num)
theorem B383917 : Blo 338752 383917 := bbase (se 3 (by rfl) ⟨71984, by rfl⟩ : syracuseStep 383917 = 143969) (by norm_num)
theorem B646069 : Blo 338752 646069 := bbase (se 5 (by rfl) ⟨30284, by rfl⟩ : syracuseStep 646069 = 60569) (by norm_num)
theorem B383953 : Blo 338752 383953 := bbase (se 2 (by rfl) ⟨143982, by rfl⟩ : syracuseStep 383953 = 287965) (by norm_num)
theorem B383989 : Blo 338752 383989 := bbase (se 5 (by rfl) ⟨17999, by rfl⟩ : syracuseStep 383989 = 35999) (by norm_num)
theorem B384025 : Blo 338752 384025 := bbase (se 2 (by rfl) ⟨144009, by rfl⟩ : syracuseStep 384025 = 288019) (by norm_num)
theorem B1956917 : Blo 338752 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B482365 : Blo 338752 482365 := bbase (se 3 (by rfl) ⟨90443, by rfl⟩ : syracuseStep 482365 = 180887) (by norm_num)
theorem B384061 : Blo 338752 384061 := bbase (se 3 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 384061 = 144023) (by norm_num)
theorem B646213 : Blo 338752 646213 := bbase (se 4 (by rfl) ⟨60582, by rfl⟩ : syracuseStep 646213 = 121165) (by norm_num)
theorem B384097 : Blo 338752 384097 := bbase (se 2 (by rfl) ⟨144036, by rfl⟩ : syracuseStep 384097 = 288073) (by norm_num)
theorem B384133 : Blo 338752 384133 := bbase (se 4 (by rfl) ⟨36012, by rfl⟩ : syracuseStep 384133 = 72025) (by norm_num)
theorem B384169 : Blo 338752 384169 := bbase (se 2 (by rfl) ⟨144063, by rfl⟩ : syracuseStep 384169 = 288127) (by norm_num)
theorem B384205 : Blo 338752 384205 := bbase (se 3 (by rfl) ⟨72038, by rfl⟩ : syracuseStep 384205 = 144077) (by norm_num)
theorem B6544597 : Blo 338752 6544597 := bbase (se 7 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 6544597 = 153389) (by norm_num)
theorem B2186453 : Blo 338752 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B646373 : Blo 338752 646373 := bbase (se 4 (by rfl) ⟨60597, by rfl⟩ : syracuseStep 646373 = 121195) (by norm_num)
theorem B384241 : Blo 338752 384241 := bbase (se 2 (by rfl) ⟨144090, by rfl⟩ : syracuseStep 384241 = 288181) (by norm_num)
theorem B2907413 : Blo 338752 2907413 := bbase (se 6 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 2907413 = 136285) (by norm_num)
theorem B384277 : Blo 338752 384277 := bbase (se 6 (by rfl) ⟨9006, by rfl⟩ : syracuseStep 384277 = 18013) (by norm_num)
theorem B384313 : Blo 338752 384313 := bbase (se 2 (by rfl) ⟨144117, by rfl⟩ : syracuseStep 384313 = 288235) (by norm_num)
theorem B351577 : Blo 338752 351577 := bbase (se 2 (by rfl) ⟨131841, by rfl⟩ : syracuseStep 351577 = 263683) (by norm_num)
theorem B384349 : Blo 338752 384349 := bbase (se 3 (by rfl) ⟨72065, by rfl⟩ : syracuseStep 384349 = 144131) (by norm_num)
theorem B646517 : Blo 338752 646517 := bbase (se 5 (by rfl) ⟨30305, by rfl⟩ : syracuseStep 646517 = 60611) (by norm_num)
theorem B384385 : Blo 338752 384385 := bbase (se 2 (by rfl) ⟨144144, by rfl⟩ : syracuseStep 384385 = 288289) (by norm_num)
theorem B482701 : Blo 338752 482701 := bbase (se 3 (by rfl) ⟨90506, by rfl⟩ : syracuseStep 482701 = 181013) (by norm_num)
theorem B384421 : Blo 338752 384421 := bbase (se 4 (by rfl) ⟨36039, by rfl⟩ : syracuseStep 384421 = 72079) (by norm_num)
theorem B384457 : Blo 338752 384457 := bbase (se 2 (by rfl) ⟨144171, by rfl⟩ : syracuseStep 384457 = 288343) (by norm_num)
theorem B875981 : Blo 338752 875981 := bbase (se 3 (by rfl) ⟨164246, by rfl⟩ : syracuseStep 875981 = 328493) (by norm_num)
theorem B777701 : Blo 338752 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B384493 : Blo 338752 384493 := bbase (se 3 (by rfl) ⟨72092, by rfl⟩ : syracuseStep 384493 = 144185) (by norm_num)
theorem B384529 : Blo 338752 384529 := bbase (se 2 (by rfl) ⟨144198, by rfl⟩ : syracuseStep 384529 = 288397) (by norm_num)
theorem B1728053 : Blo 338752 1728053 := bbase (se 5 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 1728053 = 162005) (by norm_num)
theorem B384565 : Blo 338752 384565 := bbase (se 5 (by rfl) ⟨18026, by rfl⟩ : syracuseStep 384565 = 36053) (by norm_num)
theorem B974389 : Blo 338752 974389 := bbase (se 5 (by rfl) ⟨45674, by rfl⟩ : syracuseStep 974389 = 91349) (by norm_num)
theorem B384601 : Blo 338752 384601 := bbase (se 2 (by rfl) ⟨144225, by rfl⟩ : syracuseStep 384601 = 288451) (by norm_num)
theorem B482917 : Blo 338752 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B384637 : Blo 338752 384637 := bbase (se 3 (by rfl) ⟨72119, by rfl⟩ : syracuseStep 384637 = 144239) (by norm_num)
theorem B646805 : Blo 338752 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B384673 : Blo 338752 384673 := bbase (se 2 (by rfl) ⟨144252, by rfl⟩ : syracuseStep 384673 = 288505) (by norm_num)
theorem B614069 : Blo 338752 614069 := bbase (se 5 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 614069 = 57569) (by norm_num)
theorem B384709 : Blo 338752 384709 := bbase (se 4 (by rfl) ⟨36066, by rfl⟩ : syracuseStep 384709 = 72133) (by norm_num)
theorem B384745 : Blo 338752 384745 := bbase (se 2 (by rfl) ⟨144279, by rfl⟩ : syracuseStep 384745 = 288559) (by norm_num)
theorem B384781 : Blo 338752 384781 := bbase (se 3 (by rfl) ⟨72146, by rfl⟩ : syracuseStep 384781 = 144293) (by norm_num)
theorem B646957 : Blo 338752 646957 := bbase (se 3 (by rfl) ⟨121304, by rfl⟩ : syracuseStep 646957 = 242609) (by norm_num)
theorem B384817 : Blo 338752 384817 := bbase (se 2 (by rfl) ⟨144306, by rfl⟩ : syracuseStep 384817 = 288613) (by norm_num)
theorem B384853 : Blo 338752 384853 := bbase (se 9 (by rfl) ⟨1127, by rfl⟩ : syracuseStep 384853 = 2255) (by norm_num)
theorem B384889 : Blo 338752 384889 := bbase (se 2 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 384889 = 288667) (by norm_num)
theorem B548741 : Blo 338752 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B384925 : Blo 338752 384925 := bbase (se 3 (by rfl) ⟨72173, by rfl⟩ : syracuseStep 384925 = 144347) (by norm_num)
theorem B384961 : Blo 338752 384961 := bbase (se 2 (by rfl) ⟨144360, by rfl⟩ : syracuseStep 384961 = 288721) (by norm_num)
theorem B483293 : Blo 338752 483293 := bbase (se 3 (by rfl) ⟨90617, by rfl⟩ : syracuseStep 483293 = 181235) (by norm_num)
theorem B384997 : Blo 338752 384997 := bbase (se 4 (by rfl) ⟨36093, by rfl⟩ : syracuseStep 384997 = 72187) (by norm_num)
theorem B385033 : Blo 338752 385033 := bbase (se 2 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 385033 = 288775) (by norm_num)
theorem B385069 : Blo 338752 385069 := bbase (se 3 (by rfl) ⟨72200, by rfl⟩ : syracuseStep 385069 = 144401) (by norm_num)
theorem B385105 : Blo 338752 385105 := bbase (se 2 (by rfl) ⟨144414, by rfl⟩ : syracuseStep 385105 = 288829) (by norm_num)
theorem B647261 : Blo 338752 647261 := bbase (se 3 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 647261 = 242723) (by norm_num)
theorem B876637 : Blo 338752 876637 := bbase (se 3 (by rfl) ⟨164369, by rfl⟩ : syracuseStep 876637 = 328739) (by norm_num)
theorem B778349 : Blo 338752 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B385141 : Blo 338752 385141 := bbase (se 5 (by rfl) ⟨18053, by rfl⟩ : syracuseStep 385141 = 36107) (by norm_num)
theorem B385177 : Blo 338752 385177 := bbase (se 2 (by rfl) ⟨144441, by rfl⟩ : syracuseStep 385177 = 288883) (by norm_num)
theorem B581813 : Blo 338752 581813 := bbase (se 5 (by rfl) ⟨27272, by rfl⟩ : syracuseStep 581813 = 54545) (by norm_num)
theorem B385213 : Blo 338752 385213 := bbase (se 3 (by rfl) ⟨72227, by rfl⟩ : syracuseStep 385213 = 144455) (by norm_num)
theorem B385249 : Blo 338752 385249 := bbase (se 2 (by rfl) ⟨144468, by rfl⟩ : syracuseStep 385249 = 288937) (by norm_num)
theorem B385285 : Blo 338752 385285 := bbase (se 4 (by rfl) ⟨36120, by rfl⟩ : syracuseStep 385285 = 72241) (by norm_num)
theorem B385321 : Blo 338752 385321 := bbase (se 2 (by rfl) ⟨144495, by rfl⟩ : syracuseStep 385321 = 288991) (by norm_num)
theorem B385357 : Blo 338752 385357 := bbase (se 3 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 385357 = 144509) (by norm_num)
theorem B385393 : Blo 338752 385393 := bbase (se 2 (by rfl) ⟨144522, by rfl⟩ : syracuseStep 385393 = 289045) (by norm_num)
theorem B385429 : Blo 338752 385429 := bbase (se 6 (by rfl) ⟨9033, by rfl⟩ : syracuseStep 385429 = 18067) (by norm_num)
theorem B385465 : Blo 338752 385465 := bbase (se 2 (by rfl) ⟨144549, by rfl⟩ : syracuseStep 385465 = 289099) (by norm_num)
theorem B385501 : Blo 338752 385501 := bbase (se 3 (by rfl) ⟨72281, by rfl⟩ : syracuseStep 385501 = 144563) (by norm_num)
theorem B385537 : Blo 338752 385537 := bbase (se 2 (by rfl) ⟨144576, by rfl⟩ : syracuseStep 385537 = 289153) (by norm_num)
theorem B385573 : Blo 338752 385573 := bbase (se 4 (by rfl) ⟨36147, by rfl⟩ : syracuseStep 385573 = 72295) (by norm_num)
theorem B975493 : Blo 338752 975493 := bbase (se 4 (by rfl) ⟨91452, by rfl⟩ : syracuseStep 975493 = 182905) (by norm_num)
theorem B1467173 : Blo 338752 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B1729349 : Blo 338752 1729349 := bbase (se 4 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 1729349 = 324253) (by norm_num)
theorem B648013 : Blo 338752 648013 := bbase (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) (by norm_num)
theorem B648157 : Blo 338752 648157 := bbase (se 3 (by rfl) ⟨121529, by rfl⟩ : syracuseStep 648157 = 243059) (by norm_num)
theorem B648317 : Blo 338752 648317 := bbase (se 3 (by rfl) ⟨121559, by rfl⟩ : syracuseStep 648317 = 243119) (by norm_num)
theorem B779453 : Blo 338752 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B1631461 : Blo 338752 1631461 := bbase (se 4 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 1631461 = 305899) (by norm_num)
theorem B648461 : Blo 338752 648461 := bbase (se 3 (by rfl) ⟨121586, by rfl⟩ : syracuseStep 648461 = 243173) (by norm_num)
theorem B484717 : Blo 338752 484717 := bbase (se 3 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 484717 = 181769) (by norm_num)
theorem B648749 : Blo 338752 648749 := bbase (se 3 (by rfl) ⟨121640, by rfl⟩ : syracuseStep 648749 = 243281) (by norm_num)
theorem B648901 : Blo 338752 648901 := bbase (se 4 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 648901 = 121669) (by norm_num)
theorem B485309 : Blo 338752 485309 := bbase (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) (by norm_num)
theorem B649205 : Blo 338752 649205 := bbase (se 5 (by rfl) ⟨30431, by rfl⟩ : syracuseStep 649205 = 60863) (by norm_num)
theorem B780293 : Blo 338752 780293 := bbase (se 4 (by rfl) ⟨73152, by rfl⟩ : syracuseStep 780293 = 146305) (by norm_num)
theorem B485389 : Blo 338752 485389 := bbase (se 3 (by rfl) ⟨91010, by rfl⟩ : syracuseStep 485389 = 182021) (by norm_num)
theorem B1304597 : Blo 338752 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B1730645 : Blo 338752 1730645 := bbase (se 8 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 1730645 = 20281) (by norm_num)
theorem B419941 : Blo 338752 419941 := bbase (se 4 (by rfl) ⟨39369, by rfl⟩ : syracuseStep 419941 = 78739) (by norm_num)
theorem B2189429 : Blo 338752 2189429 := bbase (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) (by norm_num)
theorem B485509 : Blo 338752 485509 := bbase (se 4 (by rfl) ⟨45516, by rfl⟩ : syracuseStep 485509 = 91033) (by norm_num)
theorem B485605 : Blo 338752 485605 := bbase (se 4 (by rfl) ⟨45525, by rfl⟩ : syracuseStep 485605 = 91051) (by norm_num)
theorem B387337 : Blo 338752 387337 := bbase (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) (by norm_num)
theorem B616837 : Blo 338752 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B1304981 : Blo 338752 1304981 := bbase (se 6 (by rfl) ⟨30585, by rfl⟩ : syracuseStep 1304981 = 61171) (by norm_num)
theorem B616901 : Blo 338752 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B486101 : Blo 338752 486101 := bbase (se 7 (by rfl) ⟨5696, by rfl⟩ : syracuseStep 486101 = 11393) (by norm_num)
theorem B649957 : Blo 338752 649957 := bbase (se 4 (by rfl) ⟨60933, by rfl⟩ : syracuseStep 649957 = 121867) (by norm_num)
theorem B879349 : Blo 338752 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B650101 : Blo 338752 650101 := bbase (se 5 (by rfl) ⟨30473, by rfl⟩ : syracuseStep 650101 = 60947) (by norm_num)
theorem B2747317 : Blo 338752 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B9989077 : Blo 338752 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B650261 : Blo 338752 650261 := bbase (se 6 (by rfl) ⟨15240, by rfl⟩ : syracuseStep 650261 = 30481) (by norm_num)
theorem B388157 : Blo 338752 388157 := bbase (se 3 (by rfl) ⟨72779, by rfl⟩ : syracuseStep 388157 = 145559) (by norm_num)
theorem B650405 : Blo 338752 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B486653 : Blo 338752 486653 := bbase (se 3 (by rfl) ⟨91247, by rfl⟩ : syracuseStep 486653 = 182495) (by norm_num)
theorem B781589 : Blo 338752 781589 := bbase (se 6 (by rfl) ⟨18318, by rfl⟩ : syracuseStep 781589 = 36637) (by norm_num)
theorem B1469765 : Blo 338752 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B781669 : Blo 338752 781669 := bbase (se 4 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 781669 = 146563) (by norm_num)
theorem B1731941 : Blo 338752 1731941 := bbase (se 4 (by rfl) ⟨162369, by rfl⟩ : syracuseStep 1731941 = 324739) (by norm_num)
theorem B650693 : Blo 338752 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B814789 : Blo 338752 814789 := bbase (se 4 (by rfl) ⟨76386, by rfl⟩ : syracuseStep 814789 = 152773) (by norm_num)
theorem B388969 : Blo 338752 388969 := bbase (se 2 (by rfl) ⟨145863, by rfl⟩ : syracuseStep 388969 = 291727) (by norm_num)
theorem B1699717 : Blo 338752 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B3502037 : Blo 338752 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B487405 : Blo 338752 487405 := bbase (se 3 (by rfl) ⟨91388, by rfl⟩ : syracuseStep 487405 = 182777) (by norm_num)
theorem B815501 : Blo 338752 815501 := bbase (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) (by norm_num)
theorem B1667557 : Blo 338752 1667557 := bbase (se 4 (by rfl) ⟨156333, by rfl⟩ : syracuseStep 1667557 = 312667) (by norm_num)
theorem B1470997 : Blo 338752 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B1110629 : Blo 338752 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B1929845 : Blo 338752 1929845 := bbase (se 5 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 1929845 = 180923) (by norm_num)
theorem B1733237 : Blo 338752 1733237 := bbase (se 5 (by rfl) ⟨81245, by rfl⟩ : syracuseStep 1733237 = 162491) (by norm_num)
theorem B1143557 : Blo 338752 1143557 := bbase (se 4 (by rfl) ⟨107208, by rfl⟩ : syracuseStep 1143557 = 214417) (by norm_num)
theorem B815885 : Blo 338752 815885 := bbase (se 3 (by rfl) ⟨152978, by rfl⟩ : syracuseStep 815885 = 305957) (by norm_num)
theorem B520997 : Blo 338752 520997 := bbase (se 4 (by rfl) ⟨48843, by rfl⟩ : syracuseStep 520997 = 97687) (by norm_num)
theorem B2749301 : Blo 338752 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B4125653 : Blo 338752 4125653 := bbase (se 7 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 4125653 = 96695) (by norm_num)
theorem B816173 : Blo 338752 816173 := bbase (se 3 (by rfl) ⟨153032, by rfl⟩ : syracuseStep 816173 = 306065) (by norm_num)
theorem B652445 : Blo 338752 652445 := bbase (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) (by norm_num)
theorem B1143989 : Blo 338752 1143989 := bbase (se 5 (by rfl) ⟨53624, by rfl⟩ : syracuseStep 1143989 = 107249) (by norm_num)
theorem B2225333 : Blo 338752 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B390457 : Blo 338752 390457 := bbase (se 2 (by rfl) ⟨146421, by rfl⟩ : syracuseStep 390457 = 292843) (by norm_num)
theorem B2586005 : Blo 338752 2586005 := bbase (se 6 (by rfl) ⟨60609, by rfl⟩ : syracuseStep 2586005 = 121219) (by norm_num)
theorem B1144421 : Blo 338752 1144421 := bbase (se 4 (by rfl) ⟨107289, by rfl⟩ : syracuseStep 1144421 = 214579) (by norm_num)
theorem B1636037 : Blo 338752 1636037 := bbase (se 4 (by rfl) ⟨153378, by rfl⟩ : syracuseStep 1636037 = 306757) (by norm_num)
theorem B6190805 : Blo 338752 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B1734533 : Blo 338752 1734533 := bbase (se 4 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 1734533 = 325225) (by norm_num)
theorem B489461 : Blo 338752 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B1144853 : Blo 338752 1144853 := bbase (se 6 (by rfl) ⟨26832, by rfl⟩ : syracuseStep 1144853 = 53665) (by norm_num)
theorem B555373 : Blo 338752 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B1964405 : Blo 338752 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B1145285 : Blo 338752 1145285 := bbase (se 4 (by rfl) ⟨107370, by rfl⟩ : syracuseStep 1145285 = 214741) (by norm_num)
theorem B555709 : Blo 338752 555709 := bbase (se 3 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 555709 = 208391) (by norm_num)
theorem B1833749 : Blo 338752 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B1178389 : Blo 338752 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B1145717 : Blo 338752 1145717 := bbase (se 5 (by rfl) ⟨53705, by rfl⟩ : syracuseStep 1145717 = 107411) (by norm_num)
theorem B7076821 : Blo 338752 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B2456821 : Blo 338752 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B458005 : Blo 338752 458005 := bbase (se 6 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 458005 = 21469) (by norm_num)
theorem B1146149 : Blo 338752 1146149 := bbase (se 4 (by rfl) ⟨107451, by rfl⟩ : syracuseStep 1146149 = 214903) (by norm_num)
theorem B2752181 : Blo 338752 2752181 := bbase (se 5 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 2752181 = 258017) (by norm_num)
theorem B1146581 : Blo 338752 1146581 := bbase (se 7 (by rfl) ⟨13436, by rfl⟩ : syracuseStep 1146581 = 26873) (by norm_num)
theorem B1310833 : Blo 338752 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B1147121 : Blo 338752 1147121 := bstep (se 2 (by rfl) ⟨430170, by rfl⟩ : syracuseStep 1147121 = 860341) B860341
theorem B458995 : Blo 338752 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B655939 : Blo 338752 655939 := bstep (se 1 (by rfl) ⟨491954, by rfl⟩ : syracuseStep 655939 = 983909) B983909
theorem B1933901 : Blo 338752 1933901 := bstep (se 3 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 1933901 = 725213) B725213
theorem B1147661 : Blo 338752 1147661 := bstep (se 3 (by rfl) ⟨215186, by rfl⟩ : syracuseStep 1147661 = 430373) B430373
theorem B1147715 : Blo 338752 1147715 := bstep (se 1 (by rfl) ⟨860786, by rfl⟩ : syracuseStep 1147715 = 1721573) B1721573
theorem B19104709 : Blo 338752 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1147985 : Blo 338752 1147985 := bstep (se 2 (by rfl) ⟨430494, by rfl⟩ : syracuseStep 1147985 = 860989) B860989
theorem B885937 : Blo 338752 885937 := bstep (se 2 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 885937 = 664453) B664453
theorem B2589893 : Blo 338752 2589893 := bstep (se 4 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 2589893 = 485605) B485605
theorem B460081 : Blo 338752 460081 := bstep (se 2 (by rfl) ⟨172530, by rfl⟩ : syracuseStep 460081 = 345061) B345061
theorem B361795 : Blo 338752 361795 := bstep (se 1 (by rfl) ⟨271346, by rfl⟩ : syracuseStep 361795 = 542693) B542693
theorem B1148525 : Blo 338752 1148525 := bstep (se 3 (by rfl) ⟨215348, by rfl⟩ : syracuseStep 1148525 = 430697) B430697
theorem B1148579 : Blo 338752 1148579 := bstep (se 1 (by rfl) ⟨861434, by rfl⟩ : syracuseStep 1148579 = 1722869) B1722869
theorem B1148849 : Blo 338752 1148849 := bstep (se 2 (by rfl) ⟨430818, by rfl⟩ : syracuseStep 1148849 = 861637) B861637
theorem B362675 : Blo 338752 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B362803 : Blo 338752 362803 := bstep (se 1 (by rfl) ⟨272102, by rfl⟩ : syracuseStep 362803 = 544205) B544205
theorem B788867 : Blo 338752 788867 := bstep (se 1 (by rfl) ⟨591650, by rfl⟩ : syracuseStep 788867 = 1183301) B1183301
theorem B1149389 : Blo 338752 1149389 := bstep (se 3 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 1149389 = 431021) B431021
theorem B1149443 : Blo 338752 1149443 := bstep (se 1 (by rfl) ⟨862082, by rfl⟩ : syracuseStep 1149443 = 1724165) B1724165
theorem B723505 : Blo 338752 723505 := bstep (se 2 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 723505 = 542629) B542629
theorem B1051235 : Blo 338752 1051235 := bstep (se 1 (by rfl) ⟨788426, by rfl⟩ : syracuseStep 1051235 = 1576853) B1576853
theorem B1936133 : Blo 338752 1936133 := bstep (se 4 (by rfl) ⟨181512, by rfl⟩ : syracuseStep 1936133 = 363025) B363025
theorem B1149713 : Blo 338752 1149713 := bstep (se 2 (by rfl) ⟨431142, by rfl⟩ : syracuseStep 1149713 = 862285) B862285
theorem B559921 : Blo 338752 559921 := bstep (se 2 (by rfl) ⟨209970, by rfl⟩ : syracuseStep 559921 = 419941) B419941
theorem B428915 : Blo 338752 428915 := bstep (se 1 (by rfl) ⟨321686, by rfl⟩ : syracuseStep 428915 = 643373) B643373
theorem B625553 : Blo 338752 625553 := bstep (se 2 (by rfl) ⟨234582, by rfl⟩ : syracuseStep 625553 = 469165) B469165
theorem B363619 : Blo 338752 363619 := bstep (se 1 (by rfl) ⟨272714, by rfl⟩ : syracuseStep 363619 = 545429) B545429
theorem B5934221 : Blo 338752 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B822449 : Blo 338752 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B1871045 : Blo 338752 1871045 := bstep (se 4 (by rfl) ⟨175410, by rfl⟩ : syracuseStep 1871045 = 350821) B350821
theorem B1150253 : Blo 338752 1150253 := bstep (se 3 (by rfl) ⟨215672, by rfl⟩ : syracuseStep 1150253 = 431345) B431345
theorem B1150307 : Blo 338752 1150307 := bstep (se 1 (by rfl) ⟨862730, by rfl⟩ : syracuseStep 1150307 = 1725461) B1725461
theorem B920963 : Blo 338752 920963 := bstep (se 1 (by rfl) ⟨690722, by rfl⟩ : syracuseStep 920963 = 1381445) B1381445
theorem B1936817 : Blo 338752 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B429619 : Blo 338752 429619 := bstep (se 1 (by rfl) ⟨322214, by rfl⟩ : syracuseStep 429619 = 644429) B644429
theorem B724547 : Blo 338752 724547 := bstep (se 1 (by rfl) ⟨543410, by rfl⟩ : syracuseStep 724547 = 1086821) B1086821
theorem B1150577 : Blo 338752 1150577 := bstep (se 2 (by rfl) ⟨431466, by rfl⟩ : syracuseStep 1150577 = 862933) B862933
theorem B429715 : Blo 338752 429715 := bstep (se 1 (by rfl) ⟨322286, by rfl⟩ : syracuseStep 429715 = 644573) B644573
theorem B462547 : Blo 338752 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B8851427 : Blo 338752 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B725059 : Blo 338752 725059 := bstep (se 1 (by rfl) ⟨543794, by rfl⟩ : syracuseStep 725059 = 1087589) B1087589
theorem B430211 : Blo 338752 430211 := bstep (se 1 (by rfl) ⟨322658, by rfl⟩ : syracuseStep 430211 = 645317) B645317
theorem B1151117 : Blo 338752 1151117 := bstep (se 3 (by rfl) ⟨215834, by rfl⟩ : syracuseStep 1151117 = 431669) B431669
theorem B1151171 : Blo 338752 1151171 := bstep (se 1 (by rfl) ⟨863378, by rfl⟩ : syracuseStep 1151171 = 1726757) B1726757
theorem B3870989 : Blo 338752 3870989 := bstep (se 3 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 3870989 = 1451621) B1451621
theorem B1085795 : Blo 338752 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B463217 : Blo 338752 463217 := bstep (se 2 (by rfl) ⟨173706, by rfl⟩ : syracuseStep 463217 = 347413) B347413
theorem B1151441 : Blo 338752 1151441 := bstep (se 2 (by rfl) ⟨431790, by rfl⟩ : syracuseStep 1151441 = 863581) B863581
theorem B725777 : Blo 338752 725777 := bstep (se 2 (by rfl) ⟨272166, by rfl⟩ : syracuseStep 725777 = 544333) B544333
theorem B430915 : Blo 338752 430915 := bstep (se 1 (by rfl) ⟨323186, by rfl⟩ : syracuseStep 430915 = 646373) B646373
theorem B2921285 : Blo 338752 2921285 := bstep (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) B547741
theorem B1938275 : Blo 338752 1938275 := bstep (se 1 (by rfl) ⟨1453706, by rfl⟩ : syracuseStep 1938275 = 2907413) B2907413
theorem B431011 : Blo 338752 431011 := bstep (se 1 (by rfl) ⟨323258, by rfl⟩ : syracuseStep 431011 = 646517) B646517
theorem B1086385 : Blo 338752 1086385 := bstep (se 2 (by rfl) ⟨407394, by rfl⟩ : syracuseStep 1086385 = 814789) B814789
theorem B1151981 : Blo 338752 1151981 := bstep (se 3 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 1151981 = 431993) B431993
theorem B1152035 : Blo 338752 1152035 := bstep (se 1 (by rfl) ⟨864026, by rfl⟩ : syracuseStep 1152035 = 1728053) B1728053
theorem B2266289 : Blo 338752 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B1152305 : Blo 338752 1152305 := bstep (se 2 (by rfl) ⟨432114, by rfl⟩ : syracuseStep 1152305 = 864229) B864229
theorem B3478925 : Blo 338752 3478925 := bstep (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) B1304597
theorem B431507 : Blo 338752 431507 := bstep (se 1 (by rfl) ⟨323630, by rfl⟩ : syracuseStep 431507 = 647261) B647261
theorem B726563 : Blo 338752 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B857699 : Blo 338752 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B857891 : Blo 338752 857891 := bstep (se 1 (by rfl) ⟨643418, by rfl⟩ : syracuseStep 857891 = 1286837) B1286837
theorem B1840931 : Blo 338752 1840931 := bstep (se 1 (by rfl) ⟨1380698, by rfl⟩ : syracuseStep 1840931 = 2761397) B2761397
theorem B1152845 : Blo 338752 1152845 := bstep (se 3 (by rfl) ⟨216158, by rfl⟩ : syracuseStep 1152845 = 432317) B432317
theorem B1152899 : Blo 338752 1152899 := bstep (se 1 (by rfl) ⟨864674, by rfl⟩ : syracuseStep 1152899 = 1729349) B1729349
theorem B1054637 : Blo 338752 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B432211 : Blo 338752 432211 := bstep (se 1 (by rfl) ⟨324158, by rfl⟩ : syracuseStep 432211 = 648317) B648317
theorem B1153169 : Blo 338752 1153169 := bstep (se 2 (by rfl) ⟨432438, by rfl⟩ : syracuseStep 1153169 = 864877) B864877
theorem B432307 : Blo 338752 432307 := bstep (se 1 (by rfl) ⟨324230, by rfl⟩ : syracuseStep 432307 = 648461) B648461
theorem B1546573 : Blo 338752 1546573 := bstep (se 3 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 1546573 = 579965) B579965
theorem B1022381 : Blo 338752 1022381 := bstep (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) B383393
theorem B727537 : Blo 338752 727537 := bstep (se 2 (by rfl) ⟨272826, by rfl⟩ : syracuseStep 727537 = 545653) B545653
theorem B1645069 : Blo 338752 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B530977 : Blo 338752 530977 := bstep (se 2 (by rfl) ⟨199116, by rfl⟩ : syracuseStep 530977 = 398233) B398233
theorem B432803 : Blo 338752 432803 := bstep (se 1 (by rfl) ⟨324602, by rfl⟩ : syracuseStep 432803 = 649205) B649205
theorem B1153709 : Blo 338752 1153709 := bstep (se 3 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 1153709 = 432641) B432641
theorem B858833 : Blo 338752 858833 := bstep (se 2 (by rfl) ⟨322062, by rfl⟩ : syracuseStep 858833 = 644125) B644125
theorem B1153763 : Blo 338752 1153763 := bstep (se 1 (by rfl) ⟨865322, by rfl⟩ : syracuseStep 1153763 = 1730645) B1730645
theorem B727793 : Blo 338752 727793 := bstep (se 2 (by rfl) ⟨272922, by rfl⟩ : syracuseStep 727793 = 545845) B545845
theorem B858883 : Blo 338752 858883 := bstep (se 1 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 858883 = 1288325) B1288325
theorem B465745 : Blo 338752 465745 := bstep (se 2 (by rfl) ⟨174654, by rfl⟩ : syracuseStep 465745 = 349309) B349309
theorem B2595725 : Blo 338752 2595725 := bstep (se 3 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 2595725 = 973397) B973397
theorem B859025 : Blo 338752 859025 := bstep (se 2 (by rfl) ⟨322134, by rfl⟩ : syracuseStep 859025 = 644269) B644269
theorem B1154033 : Blo 338752 1154033 := bstep (se 2 (by rfl) ⟨432762, by rfl⟩ : syracuseStep 1154033 = 865525) B865525
theorem B3873905 : Blo 338752 3873905 := bstep (se 2 (by rfl) ⟨1452714, by rfl⟩ : syracuseStep 3873905 = 2905429) B2905429
theorem B1875077 : Blo 338752 1875077 := bstep (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) B351577
theorem B4168901 : Blo 338752 4168901 := bstep (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) B781669
theorem B433507 : Blo 338752 433507 := bstep (se 1 (by rfl) ⟨325130, by rfl⟩ : syracuseStep 433507 = 650261) B650261
theorem B2071921 : Blo 338752 2071921 := bstep (se 2 (by rfl) ⟨776970, by rfl⟩ : syracuseStep 2071921 = 1553941) B1553941
theorem B433603 : Blo 338752 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B1154573 : Blo 338752 1154573 := bstep (se 3 (by rfl) ⟨216482, by rfl⟩ : syracuseStep 1154573 = 432965) B432965
theorem B1154627 : Blo 338752 1154627 := bstep (se 1 (by rfl) ⟨865970, by rfl⟩ : syracuseStep 1154627 = 1731941) B1731941
theorem B1449571 : Blo 338752 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B1089229 : Blo 338752 1089229 := bstep (se 3 (by rfl) ⟨204230, by rfl⟩ : syracuseStep 1089229 = 408461) B408461
theorem B1154897 : Blo 338752 1154897 := bstep (se 2 (by rfl) ⟨433086, by rfl⟩ : syracuseStep 1154897 = 866173) B866173
theorem B860017 : Blo 338752 860017 := bstep (se 2 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 860017 = 645013) B645013
theorem B2334691 : Blo 338752 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B729091 : Blo 338752 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B1941509 : Blo 338752 1941509 := bstep (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) B364033
theorem B860291 : Blo 338752 860291 := bstep (se 1 (by rfl) ⟨645218, by rfl⟩ : syracuseStep 860291 = 1290437) B1290437
theorem B5218445 : Blo 338752 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B2072753 : Blo 338752 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B860483 : Blo 338752 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B729425 : Blo 338752 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B1155437 : Blo 338752 1155437 := bstep (se 3 (by rfl) ⟨216644, by rfl⟩ : syracuseStep 1155437 = 433289) B433289
theorem B1286563 : Blo 338752 1286563 := bstep (se 1 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 1286563 = 1929845) B1929845
theorem B1155491 : Blo 338752 1155491 := bstep (se 1 (by rfl) ⟨866618, by rfl⟩ : syracuseStep 1155491 = 1733237) B1733237
theorem B1941965 : Blo 338752 1941965 := bstep (se 3 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 1941965 = 728237) B728237
theorem B762353 : Blo 338752 762353 := bstep (se 2 (by rfl) ⟨285882, by rfl⟩ : syracuseStep 762353 = 571765) B571765
theorem B762371 : Blo 338752 762371 := bstep (se 1 (by rfl) ⟨571778, by rfl⟩ : syracuseStep 762371 = 1143557) B1143557
theorem B1548977 : Blo 338752 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B1155761 : Blo 338752 1155761 := bstep (se 2 (by rfl) ⟨433410, by rfl⟩ : syracuseStep 1155761 = 866821) B866821
theorem B762641 : Blo 338752 762641 := bstep (se 2 (by rfl) ⟨285990, by rfl⟩ : syracuseStep 762641 = 571981) B571981
theorem B434963 : Blo 338752 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B762659 : Blo 338752 762659 := bstep (se 1 (by rfl) ⟨571994, by rfl⟩ : syracuseStep 762659 = 1143989) B1143989
theorem B1450801 : Blo 338752 1450801 := bstep (se 2 (by rfl) ⟨544050, by rfl⟩ : syracuseStep 1450801 = 1088101) B1088101
theorem B1844045 : Blo 338752 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B762929 : Blo 338752 762929 := bstep (se 2 (by rfl) ⟨286098, by rfl⟩ : syracuseStep 762929 = 572197) B572197
theorem B762947 : Blo 338752 762947 := bstep (se 1 (by rfl) ⟨572210, by rfl⟩ : syracuseStep 762947 = 1144421) B1144421
theorem B1090691 : Blo 338752 1090691 := bstep (se 1 (by rfl) ⟨818018, by rfl⟩ : syracuseStep 1090691 = 1636037) B1636037
theorem B2335949 : Blo 338752 2335949 := bstep (se 3 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 2335949 = 875981) B875981
theorem B1156301 : Blo 338752 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B861425 : Blo 338752 861425 := bstep (se 2 (by rfl) ⟨323034, by rfl⟩ : syracuseStep 861425 = 646069) B646069
theorem B1156355 : Blo 338752 1156355 := bstep (se 1 (by rfl) ⟨867266, by rfl⟩ : syracuseStep 1156355 = 1734533) B1734533
theorem B861475 : Blo 338752 861475 := bstep (se 1 (by rfl) ⟨646106, by rfl⟩ : syracuseStep 861475 = 1292213) B1292213
theorem B763217 : Blo 338752 763217 := bstep (se 2 (by rfl) ⟨286206, by rfl⟩ : syracuseStep 763217 = 572413) B572413
theorem B763235 : Blo 338752 763235 := bstep (se 1 (by rfl) ⟨572426, by rfl⟩ : syracuseStep 763235 = 1144853) B1144853
theorem B861617 : Blo 338752 861617 := bstep (se 2 (by rfl) ⟨323106, by rfl⟩ : syracuseStep 861617 = 646213) B646213
theorem B730595 : Blo 338752 730595 := bstep (se 1 (by rfl) ⟨547946, by rfl⟩ : syracuseStep 730595 = 1095893) B1095893
theorem B1156625 : Blo 338752 1156625 := bstep (se 2 (by rfl) ⟨433734, by rfl⟩ : syracuseStep 1156625 = 867469) B867469
theorem B763505 : Blo 338752 763505 := bstep (se 2 (by rfl) ⟨286314, by rfl⟩ : syracuseStep 763505 = 572629) B572629
theorem B8726129 : Blo 338752 8726129 := bstep (se 2 (by rfl) ⟨3272298, by rfl⟩ : syracuseStep 8726129 = 6544597) B6544597
theorem B763523 : Blo 338752 763523 := bstep (se 1 (by rfl) ⟨572642, by rfl⟩ : syracuseStep 763523 = 1145285) B1145285
theorem B2598641 : Blo 338752 2598641 := bstep (se 2 (by rfl) ⟨974490, by rfl⟩ : syracuseStep 2598641 = 1948981) B1948981
theorem B1222499 : Blo 338752 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B2074501 : Blo 338752 2074501 := bstep (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) B388969
theorem B763793 : Blo 338752 763793 := bstep (se 2 (by rfl) ⟨286422, by rfl⟩ : syracuseStep 763793 = 572845) B572845
theorem B763811 : Blo 338752 763811 := bstep (se 1 (by rfl) ⟨572858, by rfl⟩ : syracuseStep 763811 = 1145717) B1145717
theorem B764081 : Blo 338752 764081 := bstep (se 2 (by rfl) ⟨286530, by rfl⟩ : syracuseStep 764081 = 573061) B573061
theorem B764099 : Blo 338752 764099 := bstep (se 1 (by rfl) ⟨573074, by rfl⟩ : syracuseStep 764099 = 1146149) B1146149
theorem B862609 : Blo 338752 862609 := bstep (se 2 (by rfl) ⟨323478, by rfl⟩ : syracuseStep 862609 = 646957) B646957
theorem B764369 : Blo 338752 764369 := bstep (se 2 (by rfl) ⟨286638, by rfl⟩ : syracuseStep 764369 = 573277) B573277
theorem B764387 : Blo 338752 764387 := bstep (se 1 (by rfl) ⟨573290, by rfl⟩ : syracuseStep 764387 = 1146581) B1146581
theorem B1288781 : Blo 338752 1288781 := bstep (se 3 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 1288781 = 483293) B483293
theorem B3943025 : Blo 338752 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B862883 : Blo 338752 862883 := bstep (se 1 (by rfl) ⟨647162, by rfl⟩ : syracuseStep 862883 = 1294325) B1294325
theorem B1092305 : Blo 338752 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B764657 : Blo 338752 764657 := bstep (se 2 (by rfl) ⟨286746, by rfl⟩ : syracuseStep 764657 = 573493) B573493
theorem B764675 : Blo 338752 764675 := bstep (se 1 (by rfl) ⟨573506, by rfl⟩ : syracuseStep 764675 = 1147013) B1147013
theorem B338755 : Blo 338752 338755 := bstep (se 1 (by rfl) ⟨254066, by rfl⟩ : syracuseStep 338755 = 508133) B508133
theorem B338771 : Blo 338752 338771 := bstep (se 1 (by rfl) ⟨254078, by rfl⟩ : syracuseStep 338771 = 508157) B508157
theorem B338787 : Blo 338752 338787 := bstep (se 1 (by rfl) ⟨254090, by rfl⟩ : syracuseStep 338787 = 508181) B508181
theorem B863075 : Blo 338752 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B338803 : Blo 338752 338803 := bstep (se 1 (by rfl) ⟨254102, by rfl⟩ : syracuseStep 338803 = 508205) B508205
theorem B338819 : Blo 338752 338819 := bstep (se 1 (by rfl) ⟨254114, by rfl⟩ : syracuseStep 338819 = 508229) B508229
theorem B338835 : Blo 338752 338835 := bstep (se 1 (by rfl) ⟨254126, by rfl⟩ : syracuseStep 338835 = 508253) B508253
theorem B338851 : Blo 338752 338851 := bstep (se 1 (by rfl) ⟨254138, by rfl⟩ : syracuseStep 338851 = 508277) B508277
theorem B338867 : Blo 338752 338867 := bstep (se 1 (by rfl) ⟨254150, by rfl⟩ : syracuseStep 338867 = 508301) B508301
theorem B338883 : Blo 338752 338883 := bstep (se 1 (by rfl) ⟨254162, by rfl⟩ : syracuseStep 338883 = 508325) B508325
theorem B2075597 : Blo 338752 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B338899 : Blo 338752 338899 := bstep (se 1 (by rfl) ⟨254174, by rfl⟩ : syracuseStep 338899 = 508349) B508349
theorem B338915 : Blo 338752 338915 := bstep (se 1 (by rfl) ⟨254186, by rfl⟩ : syracuseStep 338915 = 508373) B508373
theorem B338931 : Blo 338752 338931 := bstep (se 1 (by rfl) ⟨254198, by rfl⟩ : syracuseStep 338931 = 508397) B508397
theorem B338947 : Blo 338752 338947 := bstep (se 1 (by rfl) ⟨254210, by rfl⟩ : syracuseStep 338947 = 508421) B508421
theorem B764945 : Blo 338752 764945 := bstep (se 2 (by rfl) ⟨286854, by rfl⟩ : syracuseStep 764945 = 573709) B573709
theorem B338963 : Blo 338752 338963 := bstep (se 1 (by rfl) ⟨254222, by rfl⟩ : syracuseStep 338963 = 508445) B508445
theorem B338979 : Blo 338752 338979 := bstep (se 1 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 338979 = 508469) B508469
theorem B764963 : Blo 338752 764963 := bstep (se 1 (by rfl) ⟨573722, by rfl⟩ : syracuseStep 764963 = 1147445) B1147445
theorem B338995 : Blo 338752 338995 := bstep (se 1 (by rfl) ⟨254246, by rfl⟩ : syracuseStep 338995 = 508493) B508493
theorem B339011 : Blo 338752 339011 := bstep (se 1 (by rfl) ⟨254258, by rfl⟩ : syracuseStep 339011 = 508517) B508517
theorem B339027 : Blo 338752 339027 := bstep (se 1 (by rfl) ⟨254270, by rfl⟩ : syracuseStep 339027 = 508541) B508541
theorem B339043 : Blo 338752 339043 := bstep (se 1 (by rfl) ⟨254282, by rfl⟩ : syracuseStep 339043 = 508565) B508565
theorem B339059 : Blo 338752 339059 := bstep (se 1 (by rfl) ⟨254294, by rfl⟩ : syracuseStep 339059 = 508589) B508589
theorem B339075 : Blo 338752 339075 := bstep (se 1 (by rfl) ⟨254306, by rfl⟩ : syracuseStep 339075 = 508613) B508613
theorem B339091 : Blo 338752 339091 := bstep (se 1 (by rfl) ⟨254318, by rfl⟩ : syracuseStep 339091 = 508637) B508637
theorem B339107 : Blo 338752 339107 := bstep (se 1 (by rfl) ⟨254330, by rfl⟩ : syracuseStep 339107 = 508661) B508661
theorem B339123 : Blo 338752 339123 := bstep (se 1 (by rfl) ⟨254342, by rfl⟩ : syracuseStep 339123 = 508685) B508685
theorem B339139 : Blo 338752 339139 := bstep (se 1 (by rfl) ⟨254354, by rfl⟩ : syracuseStep 339139 = 508709) B508709
theorem B339155 : Blo 338752 339155 := bstep (se 1 (by rfl) ⟨254366, by rfl⟩ : syracuseStep 339155 = 508733) B508733
theorem B339171 : Blo 338752 339171 := bstep (se 1 (by rfl) ⟨254378, by rfl⟩ : syracuseStep 339171 = 508757) B508757
theorem B339187 : Blo 338752 339187 := bstep (se 1 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 339187 = 508781) B508781
theorem B339203 : Blo 338752 339203 := bstep (se 1 (by rfl) ⟨254402, by rfl⟩ : syracuseStep 339203 = 508805) B508805
theorem B339219 : Blo 338752 339219 := bstep (se 1 (by rfl) ⟨254414, by rfl⟩ : syracuseStep 339219 = 508829) B508829
theorem B339235 : Blo 338752 339235 := bstep (se 1 (by rfl) ⟨254426, by rfl⟩ : syracuseStep 339235 = 508853) B508853
theorem B765233 : Blo 338752 765233 := bstep (se 2 (by rfl) ⟨286962, by rfl⟩ : syracuseStep 765233 = 573925) B573925
theorem B1944881 : Blo 338752 1944881 := bstep (se 2 (by rfl) ⟨729330, by rfl⟩ : syracuseStep 1944881 = 1458661) B1458661
theorem B339251 : Blo 338752 339251 := bstep (se 1 (by rfl) ⟨254438, by rfl⟩ : syracuseStep 339251 = 508877) B508877
theorem B4140341 : Blo 338752 4140341 := bstep (se 5 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 4140341 = 388157) B388157
theorem B339267 : Blo 338752 339267 := bstep (se 1 (by rfl) ⟨254450, by rfl⟩ : syracuseStep 339267 = 508901) B508901
theorem B765251 : Blo 338752 765251 := bstep (se 1 (by rfl) ⟨573938, by rfl⟩ : syracuseStep 765251 = 1147877) B1147877
theorem B339283 : Blo 338752 339283 := bstep (se 1 (by rfl) ⟨254462, by rfl⟩ : syracuseStep 339283 = 508925) B508925
theorem B339299 : Blo 338752 339299 := bstep (se 1 (by rfl) ⟨254474, by rfl⟩ : syracuseStep 339299 = 508949) B508949
theorem B339315 : Blo 338752 339315 := bstep (se 1 (by rfl) ⟨254486, by rfl⟩ : syracuseStep 339315 = 508973) B508973
theorem B339331 : Blo 338752 339331 := bstep (se 1 (by rfl) ⟨254498, by rfl⟩ : syracuseStep 339331 = 508997) B508997
theorem B5254541 : Blo 338752 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B339347 : Blo 338752 339347 := bstep (se 1 (by rfl) ⟨254510, by rfl⟩ : syracuseStep 339347 = 509021) B509021
theorem B339363 : Blo 338752 339363 := bstep (se 1 (by rfl) ⟨254522, by rfl⟩ : syracuseStep 339363 = 509045) B509045
theorem B339379 : Blo 338752 339379 := bstep (se 1 (by rfl) ⟨254534, by rfl⟩ : syracuseStep 339379 = 509069) B509069
theorem B339395 : Blo 338752 339395 := bstep (se 1 (by rfl) ⟨254546, by rfl⟩ : syracuseStep 339395 = 509093) B509093
theorem B339411 : Blo 338752 339411 := bstep (se 1 (by rfl) ⟨254558, by rfl⟩ : syracuseStep 339411 = 509117) B509117
theorem B339427 : Blo 338752 339427 := bstep (se 1 (by rfl) ⟨254570, by rfl⟩ : syracuseStep 339427 = 509141) B509141
theorem B339443 : Blo 338752 339443 := bstep (se 1 (by rfl) ⟨254582, by rfl⟩ : syracuseStep 339443 = 509165) B509165
theorem B339459 : Blo 338752 339459 := bstep (se 1 (by rfl) ⟨254594, by rfl⟩ : syracuseStep 339459 = 509189) B509189
theorem B339475 : Blo 338752 339475 := bstep (se 1 (by rfl) ⟨254606, by rfl⟩ : syracuseStep 339475 = 509213) B509213
theorem B339491 : Blo 338752 339491 := bstep (se 1 (by rfl) ⟨254618, by rfl⟩ : syracuseStep 339491 = 509237) B509237
theorem B339507 : Blo 338752 339507 := bstep (se 1 (by rfl) ⟨254630, by rfl⟩ : syracuseStep 339507 = 509261) B509261
theorem B339523 : Blo 338752 339523 := bstep (se 1 (by rfl) ⟨254642, by rfl⟩ : syracuseStep 339523 = 509285) B509285
theorem B765521 : Blo 338752 765521 := bstep (se 2 (by rfl) ⟨287070, by rfl⟩ : syracuseStep 765521 = 574141) B574141
theorem B339539 : Blo 338752 339539 := bstep (se 1 (by rfl) ⟨254654, by rfl⟩ : syracuseStep 339539 = 509309) B509309
theorem B339555 : Blo 338752 339555 := bstep (se 1 (by rfl) ⟨254666, by rfl⟩ : syracuseStep 339555 = 509333) B509333
theorem B765539 : Blo 338752 765539 := bstep (se 1 (by rfl) ⟨574154, by rfl⟩ : syracuseStep 765539 = 1148309) B1148309
theorem B339571 : Blo 338752 339571 := bstep (se 1 (by rfl) ⟨254678, by rfl⟩ : syracuseStep 339571 = 509357) B509357
theorem B339587 : Blo 338752 339587 := bstep (se 1 (by rfl) ⟨254690, by rfl⟩ : syracuseStep 339587 = 509381) B509381
theorem B339603 : Blo 338752 339603 := bstep (se 1 (by rfl) ⟨254702, by rfl⟩ : syracuseStep 339603 = 509405) B509405
theorem B339619 : Blo 338752 339619 := bstep (se 1 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 339619 = 509429) B509429
theorem B339635 : Blo 338752 339635 := bstep (se 1 (by rfl) ⟨254726, by rfl⟩ : syracuseStep 339635 = 509453) B509453
theorem B339651 : Blo 338752 339651 := bstep (se 1 (by rfl) ⟨254738, by rfl⟩ : syracuseStep 339651 = 509477) B509477
theorem B339667 : Blo 338752 339667 := bstep (se 1 (by rfl) ⟨254750, by rfl⟩ : syracuseStep 339667 = 509501) B509501
theorem B339683 : Blo 338752 339683 := bstep (se 1 (by rfl) ⟨254762, by rfl⟩ : syracuseStep 339683 = 509525) B509525
theorem B339699 : Blo 338752 339699 := bstep (se 1 (by rfl) ⟨254774, by rfl⟩ : syracuseStep 339699 = 509549) B509549
theorem B339715 : Blo 338752 339715 := bstep (se 1 (by rfl) ⟨254786, by rfl⟩ : syracuseStep 339715 = 509573) B509573
theorem B864017 : Blo 338752 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B339731 : Blo 338752 339731 := bstep (se 1 (by rfl) ⟨254798, by rfl⟩ : syracuseStep 339731 = 509597) B509597
theorem B339747 : Blo 338752 339747 := bstep (se 1 (by rfl) ⟨254810, by rfl⟩ : syracuseStep 339747 = 509621) B509621
theorem B339763 : Blo 338752 339763 := bstep (se 1 (by rfl) ⟨254822, by rfl⟩ : syracuseStep 339763 = 509645) B509645
theorem B339779 : Blo 338752 339779 := bstep (se 1 (by rfl) ⟨254834, by rfl⟩ : syracuseStep 339779 = 509669) B509669
theorem B864067 : Blo 338752 864067 := bstep (se 1 (by rfl) ⟨648050, by rfl⟩ : syracuseStep 864067 = 1296101) B1296101
theorem B339795 : Blo 338752 339795 := bstep (se 1 (by rfl) ⟨254846, by rfl⟩ : syracuseStep 339795 = 509693) B509693
theorem B339811 : Blo 338752 339811 := bstep (se 1 (by rfl) ⟨254858, by rfl⟩ : syracuseStep 339811 = 509717) B509717
theorem B765809 : Blo 338752 765809 := bstep (se 2 (by rfl) ⟨287178, by rfl⟩ : syracuseStep 765809 = 574357) B574357
theorem B339827 : Blo 338752 339827 := bstep (se 1 (by rfl) ⟨254870, by rfl⟩ : syracuseStep 339827 = 509741) B509741
theorem B339843 : Blo 338752 339843 := bstep (se 1 (by rfl) ⟨254882, by rfl⟩ : syracuseStep 339843 = 509765) B509765
theorem B765827 : Blo 338752 765827 := bstep (se 1 (by rfl) ⟨574370, by rfl⟩ : syracuseStep 765827 = 1148741) B1148741
theorem B339859 : Blo 338752 339859 := bstep (se 1 (by rfl) ⟨254894, by rfl⟩ : syracuseStep 339859 = 509789) B509789
theorem B339875 : Blo 338752 339875 := bstep (se 1 (by rfl) ⟨254906, by rfl⟩ : syracuseStep 339875 = 509813) B509813
theorem B339891 : Blo 338752 339891 := bstep (se 1 (by rfl) ⟨254918, by rfl⟩ : syracuseStep 339891 = 509837) B509837
theorem B339907 : Blo 338752 339907 := bstep (se 1 (by rfl) ⟨254930, by rfl⟩ : syracuseStep 339907 = 509861) B509861
theorem B864209 : Blo 338752 864209 := bstep (se 2 (by rfl) ⟨324078, by rfl⟩ : syracuseStep 864209 = 648157) B648157
theorem B339923 : Blo 338752 339923 := bstep (se 1 (by rfl) ⟨254942, by rfl⟩ : syracuseStep 339923 = 509885) B509885
theorem B339939 : Blo 338752 339939 := bstep (se 1 (by rfl) ⟨254954, by rfl⟩ : syracuseStep 339939 = 509909) B509909
theorem B339955 : Blo 338752 339955 := bstep (se 1 (by rfl) ⟨254966, by rfl⟩ : syracuseStep 339955 = 509933) B509933
theorem B339971 : Blo 338752 339971 := bstep (se 1 (by rfl) ⟨254978, by rfl⟩ : syracuseStep 339971 = 509957) B509957
theorem B339987 : Blo 338752 339987 := bstep (se 1 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 339987 = 509981) B509981
theorem B340003 : Blo 338752 340003 := bstep (se 1 (by rfl) ⟨255002, by rfl⟩ : syracuseStep 340003 = 510005) B510005
theorem B340019 : Blo 338752 340019 := bstep (se 1 (by rfl) ⟨255014, by rfl⟩ : syracuseStep 340019 = 510029) B510029
theorem B340035 : Blo 338752 340035 := bstep (se 1 (by rfl) ⟨255026, by rfl⟩ : syracuseStep 340035 = 510053) B510053
theorem B340051 : Blo 338752 340051 := bstep (se 1 (by rfl) ⟨255038, by rfl⟩ : syracuseStep 340051 = 510077) B510077
theorem B340067 : Blo 338752 340067 := bstep (se 1 (by rfl) ⟨255050, by rfl⟩ : syracuseStep 340067 = 510101) B510101
theorem B340083 : Blo 338752 340083 := bstep (se 1 (by rfl) ⟨255062, by rfl⟩ : syracuseStep 340083 = 510125) B510125
theorem B340099 : Blo 338752 340099 := bstep (se 1 (by rfl) ⟨255074, by rfl⟩ : syracuseStep 340099 = 510149) B510149
theorem B766097 : Blo 338752 766097 := bstep (se 2 (by rfl) ⟨287286, by rfl⟩ : syracuseStep 766097 = 574573) B574573
theorem B340115 : Blo 338752 340115 := bstep (se 1 (by rfl) ⟨255086, by rfl⟩ : syracuseStep 340115 = 510173) B510173
theorem B340131 : Blo 338752 340131 := bstep (se 1 (by rfl) ⟨255098, by rfl⟩ : syracuseStep 340131 = 510197) B510197
theorem B766115 : Blo 338752 766115 := bstep (se 1 (by rfl) ⟨574586, by rfl⟩ : syracuseStep 766115 = 1149173) B1149173
theorem B340147 : Blo 338752 340147 := bstep (se 1 (by rfl) ⟨255110, by rfl⟩ : syracuseStep 340147 = 510221) B510221
theorem B340163 : Blo 338752 340163 := bstep (se 1 (by rfl) ⟨255122, by rfl⟩ : syracuseStep 340163 = 510245) B510245
theorem B340179 : Blo 338752 340179 := bstep (se 1 (by rfl) ⟨255134, by rfl⟩ : syracuseStep 340179 = 510269) B510269
theorem B340195 : Blo 338752 340195 := bstep (se 1 (by rfl) ⟨255146, by rfl⟩ : syracuseStep 340195 = 510293) B510293
theorem B2470115 : Blo 338752 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B340211 : Blo 338752 340211 := bstep (se 1 (by rfl) ⟨255158, by rfl⟩ : syracuseStep 340211 = 510317) B510317
theorem B340227 : Blo 338752 340227 := bstep (se 1 (by rfl) ⟨255170, by rfl⟩ : syracuseStep 340227 = 510341) B510341
theorem B2961677 : Blo 338752 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B340243 : Blo 338752 340243 := bstep (se 1 (by rfl) ⟨255182, by rfl⟩ : syracuseStep 340243 = 510365) B510365
theorem B340259 : Blo 338752 340259 := bstep (se 1 (by rfl) ⟨255194, by rfl⟩ : syracuseStep 340259 = 510389) B510389
theorem B2175281 : Blo 338752 2175281 := bstep (se 2 (by rfl) ⟨815730, by rfl⟩ : syracuseStep 2175281 = 1631461) B1631461
theorem B340275 : Blo 338752 340275 := bstep (se 1 (by rfl) ⟨255206, by rfl⟩ : syracuseStep 340275 = 510413) B510413
theorem B340291 : Blo 338752 340291 := bstep (se 1 (by rfl) ⟨255218, by rfl⟩ : syracuseStep 340291 = 510437) B510437
theorem B1225037 : Blo 338752 1225037 := bstep (se 3 (by rfl) ⟨229694, by rfl⟩ : syracuseStep 1225037 = 459389) B459389
theorem B340307 : Blo 338752 340307 := bstep (se 1 (by rfl) ⟨255230, by rfl⟩ : syracuseStep 340307 = 510461) B510461
theorem B340323 : Blo 338752 340323 := bstep (se 1 (by rfl) ⟨255242, by rfl⟩ : syracuseStep 340323 = 510485) B510485
theorem B340339 : Blo 338752 340339 := bstep (se 1 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 340339 = 510509) B510509
theorem B340355 : Blo 338752 340355 := bstep (se 1 (by rfl) ⟨255266, by rfl⟩ : syracuseStep 340355 = 510533) B510533
theorem B340371 : Blo 338752 340371 := bstep (se 1 (by rfl) ⟨255278, by rfl⟩ : syracuseStep 340371 = 510557) B510557
theorem B340387 : Blo 338752 340387 := bstep (se 1 (by rfl) ⟨255290, by rfl⟩ : syracuseStep 340387 = 510581) B510581
theorem B766385 : Blo 338752 766385 := bstep (se 2 (by rfl) ⟨287394, by rfl⟩ : syracuseStep 766385 = 574789) B574789
theorem B340403 : Blo 338752 340403 := bstep (se 1 (by rfl) ⟨255302, by rfl⟩ : syracuseStep 340403 = 510605) B510605
theorem B340419 : Blo 338752 340419 := bstep (se 1 (by rfl) ⟨255314, by rfl⟩ : syracuseStep 340419 = 510629) B510629
theorem B766403 : Blo 338752 766403 := bstep (se 1 (by rfl) ⟨574802, by rfl⟩ : syracuseStep 766403 = 1149605) B1149605
theorem B340435 : Blo 338752 340435 := bstep (se 1 (by rfl) ⟨255326, by rfl⟩ : syracuseStep 340435 = 510653) B510653
theorem B340451 : Blo 338752 340451 := bstep (se 1 (by rfl) ⟨255338, by rfl⟩ : syracuseStep 340451 = 510677) B510677
theorem B6238691 : Blo 338752 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B700913 : Blo 338752 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B340467 : Blo 338752 340467 := bstep (se 1 (by rfl) ⟨255350, by rfl⟩ : syracuseStep 340467 = 510701) B510701
theorem B340483 : Blo 338752 340483 := bstep (se 1 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 340483 = 510725) B510725
theorem B340499 : Blo 338752 340499 := bstep (se 1 (by rfl) ⟨255374, by rfl⟩ : syracuseStep 340499 = 510749) B510749
theorem B340515 : Blo 338752 340515 := bstep (se 1 (by rfl) ⟨255386, by rfl⟩ : syracuseStep 340515 = 510773) B510773
theorem B340531 : Blo 338752 340531 := bstep (se 1 (by rfl) ⟨255398, by rfl⟩ : syracuseStep 340531 = 510797) B510797
theorem B340547 : Blo 338752 340547 := bstep (se 1 (by rfl) ⟨255410, by rfl⟩ : syracuseStep 340547 = 510821) B510821
theorem B340563 : Blo 338752 340563 := bstep (se 1 (by rfl) ⟨255422, by rfl⟩ : syracuseStep 340563 = 510845) B510845
theorem B340579 : Blo 338752 340579 := bstep (se 1 (by rfl) ⟨255434, by rfl⟩ : syracuseStep 340579 = 510869) B510869
theorem B340595 : Blo 338752 340595 := bstep (se 1 (by rfl) ⟨255446, by rfl⟩ : syracuseStep 340595 = 510893) B510893
theorem B340611 : Blo 338752 340611 := bstep (se 1 (by rfl) ⟨255458, by rfl⟩ : syracuseStep 340611 = 510917) B510917
theorem B340627 : Blo 338752 340627 := bstep (se 1 (by rfl) ⟨255470, by rfl⟩ : syracuseStep 340627 = 510941) B510941
theorem B340643 : Blo 338752 340643 := bstep (se 1 (by rfl) ⟨255482, by rfl⟩ : syracuseStep 340643 = 510965) B510965
theorem B340659 : Blo 338752 340659 := bstep (se 1 (by rfl) ⟨255494, by rfl⟩ : syracuseStep 340659 = 510989) B510989
theorem B340675 : Blo 338752 340675 := bstep (se 1 (by rfl) ⟨255506, by rfl⟩ : syracuseStep 340675 = 511013) B511013
theorem B766673 : Blo 338752 766673 := bstep (se 2 (by rfl) ⟨287502, by rfl⟩ : syracuseStep 766673 = 575005) B575005
theorem B340691 : Blo 338752 340691 := bstep (se 1 (by rfl) ⟨255518, by rfl⟩ : syracuseStep 340691 = 511037) B511037
theorem B340707 : Blo 338752 340707 := bstep (se 1 (by rfl) ⟨255530, by rfl⟩ : syracuseStep 340707 = 511061) B511061
theorem B766691 : Blo 338752 766691 := bstep (se 1 (by rfl) ⟨575018, by rfl⟩ : syracuseStep 766691 = 1150037) B1150037
theorem B1946339 : Blo 338752 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B1094381 : Blo 338752 1094381 := bstep (se 3 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 1094381 = 410393) B410393
theorem B340723 : Blo 338752 340723 := bstep (se 1 (by rfl) ⟨255542, by rfl⟩ : syracuseStep 340723 = 511085) B511085
theorem B340739 : Blo 338752 340739 := bstep (se 1 (by rfl) ⟨255554, by rfl⟩ : syracuseStep 340739 = 511109) B511109
theorem B3912461 : Blo 338752 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B1389325 : Blo 338752 1389325 := bstep (se 3 (by rfl) ⟨260498, by rfl⟩ : syracuseStep 1389325 = 520997) B520997
theorem B340755 : Blo 338752 340755 := bstep (se 1 (by rfl) ⟨255566, by rfl⟩ : syracuseStep 340755 = 511133) B511133
theorem B340771 : Blo 338752 340771 := bstep (se 1 (by rfl) ⟨255578, by rfl⟩ : syracuseStep 340771 = 511157) B511157
theorem B340787 : Blo 338752 340787 := bstep (se 1 (by rfl) ⟨255590, by rfl⟩ : syracuseStep 340787 = 511181) B511181
theorem B5813045 : Blo 338752 5813045 := bstep (se 5 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 5813045 = 544973) B544973
theorem B340803 : Blo 338752 340803 := bstep (se 1 (by rfl) ⟨255602, by rfl⟩ : syracuseStep 340803 = 511205) B511205
theorem B340819 : Blo 338752 340819 := bstep (se 1 (by rfl) ⟨255614, by rfl⟩ : syracuseStep 340819 = 511229) B511229
theorem B340835 : Blo 338752 340835 := bstep (se 1 (by rfl) ⟨255626, by rfl⟩ : syracuseStep 340835 = 511253) B511253
theorem B340851 : Blo 338752 340851 := bstep (se 1 (by rfl) ⟨255638, by rfl⟩ : syracuseStep 340851 = 511277) B511277
theorem B340867 : Blo 338752 340867 := bstep (se 1 (by rfl) ⟨255650, by rfl⟩ : syracuseStep 340867 = 511301) B511301
theorem B1848197 : Blo 338752 1848197 := bstep (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) B346537
theorem B340883 : Blo 338752 340883 := bstep (se 1 (by rfl) ⟨255662, by rfl⟩ : syracuseStep 340883 = 511325) B511325
theorem B340899 : Blo 338752 340899 := bstep (se 1 (by rfl) ⟨255674, by rfl⟩ : syracuseStep 340899 = 511349) B511349
theorem B865201 : Blo 338752 865201 := bstep (se 2 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 865201 = 648901) B648901
theorem B340915 : Blo 338752 340915 := bstep (se 1 (by rfl) ⟨255686, by rfl⟩ : syracuseStep 340915 = 511373) B511373
theorem B340931 : Blo 338752 340931 := bstep (se 1 (by rfl) ⟨255698, by rfl⟩ : syracuseStep 340931 = 511397) B511397
theorem B340947 : Blo 338752 340947 := bstep (se 1 (by rfl) ⟨255710, by rfl⟩ : syracuseStep 340947 = 511421) B511421
theorem B340963 : Blo 338752 340963 := bstep (se 1 (by rfl) ⟨255722, by rfl⟩ : syracuseStep 340963 = 511445) B511445
theorem B766961 : Blo 338752 766961 := bstep (se 2 (by rfl) ⟨287610, by rfl⟩ : syracuseStep 766961 = 575221) B575221
theorem B340979 : Blo 338752 340979 := bstep (se 1 (by rfl) ⟨255734, by rfl⟩ : syracuseStep 340979 = 511469) B511469
theorem B766979 : Blo 338752 766979 := bstep (se 1 (by rfl) ⟨575234, by rfl⟩ : syracuseStep 766979 = 1150469) B1150469
theorem B340995 : Blo 338752 340995 := bstep (se 1 (by rfl) ⟨255746, by rfl⟩ : syracuseStep 340995 = 511493) B511493
theorem B341011 : Blo 338752 341011 := bstep (se 1 (by rfl) ⟨255758, by rfl⟩ : syracuseStep 341011 = 511517) B511517
theorem B341027 : Blo 338752 341027 := bstep (se 1 (by rfl) ⟨255770, by rfl⟩ : syracuseStep 341027 = 511541) B511541
theorem B341043 : Blo 338752 341043 := bstep (se 1 (by rfl) ⟨255782, by rfl⟩ : syracuseStep 341043 = 511565) B511565
theorem B341059 : Blo 338752 341059 := bstep (se 1 (by rfl) ⟨255794, by rfl⟩ : syracuseStep 341059 = 511589) B511589
theorem B341075 : Blo 338752 341075 := bstep (se 1 (by rfl) ⟨255806, by rfl⟩ : syracuseStep 341075 = 511613) B511613
theorem B341091 : Blo 338752 341091 := bstep (se 1 (by rfl) ⟨255818, by rfl⟩ : syracuseStep 341091 = 511637) B511637
theorem B1717361 : Blo 338752 1717361 := bstep (se 2 (by rfl) ⟨644010, by rfl⟩ : syracuseStep 1717361 = 1288021) B1288021
theorem B341107 : Blo 338752 341107 := bstep (se 1 (by rfl) ⟨255830, by rfl⟩ : syracuseStep 341107 = 511661) B511661
theorem B341123 : Blo 338752 341123 := bstep (se 1 (by rfl) ⟨255842, by rfl⟩ : syracuseStep 341123 = 511685) B511685
theorem B1455245 : Blo 338752 1455245 := bstep (se 3 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 1455245 = 545717) B545717
theorem B341139 : Blo 338752 341139 := bstep (se 1 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 341139 = 511709) B511709
theorem B341155 : Blo 338752 341155 := bstep (se 1 (by rfl) ⟨255866, by rfl⟩ : syracuseStep 341155 = 511733) B511733
theorem B341171 : Blo 338752 341171 := bstep (se 1 (by rfl) ⟨255878, by rfl⟩ : syracuseStep 341171 = 511757) B511757
theorem B341187 : Blo 338752 341187 := bstep (se 1 (by rfl) ⟨255890, by rfl⟩ : syracuseStep 341187 = 511781) B511781
theorem B865475 : Blo 338752 865475 := bstep (se 1 (by rfl) ⟨649106, by rfl⟩ : syracuseStep 865475 = 1298213) B1298213
theorem B341203 : Blo 338752 341203 := bstep (se 1 (by rfl) ⟨255902, by rfl⟩ : syracuseStep 341203 = 511805) B511805
theorem B341219 : Blo 338752 341219 := bstep (se 1 (by rfl) ⟨255914, by rfl⟩ : syracuseStep 341219 = 511829) B511829
theorem B341235 : Blo 338752 341235 := bstep (se 1 (by rfl) ⟨255926, by rfl⟩ : syracuseStep 341235 = 511853) B511853
theorem B341251 : Blo 338752 341251 := bstep (se 1 (by rfl) ⟨255938, by rfl⟩ : syracuseStep 341251 = 511877) B511877
theorem B767249 : Blo 338752 767249 := bstep (se 2 (by rfl) ⟨287718, by rfl⟩ : syracuseStep 767249 = 575437) B575437
theorem B341267 : Blo 338752 341267 := bstep (se 1 (by rfl) ⟨255950, by rfl⟩ : syracuseStep 341267 = 511901) B511901
theorem B767267 : Blo 338752 767267 := bstep (se 1 (by rfl) ⟨575450, by rfl⟩ : syracuseStep 767267 = 1150901) B1150901
theorem B341283 : Blo 338752 341283 := bstep (se 1 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 341283 = 511925) B511925
theorem B341299 : Blo 338752 341299 := bstep (se 1 (by rfl) ⟨255974, by rfl⟩ : syracuseStep 341299 = 511949) B511949
theorem B341315 : Blo 338752 341315 := bstep (se 1 (by rfl) ⟨255986, by rfl⟩ : syracuseStep 341315 = 511973) B511973
theorem B341331 : Blo 338752 341331 := bstep (se 1 (by rfl) ⟨255998, by rfl⟩ : syracuseStep 341331 = 511997) B511997
theorem B341347 : Blo 338752 341347 := bstep (se 1 (by rfl) ⟨256010, by rfl⟩ : syracuseStep 341347 = 512021) B512021
theorem B341363 : Blo 338752 341363 := bstep (se 1 (by rfl) ⟨256022, by rfl⟩ : syracuseStep 341363 = 512045) B512045
theorem B341379 : Blo 338752 341379 := bstep (se 1 (by rfl) ⟨256034, by rfl⟩ : syracuseStep 341379 = 512069) B512069
theorem B865667 : Blo 338752 865667 := bstep (se 1 (by rfl) ⟨649250, by rfl⟩ : syracuseStep 865667 = 1298501) B1298501
theorem B341395 : Blo 338752 341395 := bstep (se 1 (by rfl) ⟨256046, by rfl⟩ : syracuseStep 341395 = 512093) B512093
theorem B341411 : Blo 338752 341411 := bstep (se 1 (by rfl) ⟨256058, by rfl⟩ : syracuseStep 341411 = 512117) B512117
theorem B1291697 : Blo 338752 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B341427 : Blo 338752 341427 := bstep (se 1 (by rfl) ⟨256070, by rfl⟩ : syracuseStep 341427 = 512141) B512141
theorem B341443 : Blo 338752 341443 := bstep (se 1 (by rfl) ⟨256082, by rfl⟩ : syracuseStep 341443 = 512165) B512165
theorem B341459 : Blo 338752 341459 := bstep (se 1 (by rfl) ⟨256094, by rfl⟩ : syracuseStep 341459 = 512189) B512189
theorem B341475 : Blo 338752 341475 := bstep (se 1 (by rfl) ⟨256106, by rfl⟩ : syracuseStep 341475 = 512213) B512213
theorem B341491 : Blo 338752 341491 := bstep (se 1 (by rfl) ⟨256118, by rfl⟩ : syracuseStep 341491 = 512237) B512237
theorem B341507 : Blo 338752 341507 := bstep (se 1 (by rfl) ⟨256130, by rfl⟩ : syracuseStep 341507 = 512261) B512261
theorem B341523 : Blo 338752 341523 := bstep (se 1 (by rfl) ⟨256142, by rfl⟩ : syracuseStep 341523 = 512285) B512285
theorem B341539 : Blo 338752 341539 := bstep (se 1 (by rfl) ⟨256154, by rfl⟩ : syracuseStep 341539 = 512309) B512309
theorem B767537 : Blo 338752 767537 := bstep (se 2 (by rfl) ⟨287826, by rfl⟩ : syracuseStep 767537 = 575653) B575653
theorem B341555 : Blo 338752 341555 := bstep (se 1 (by rfl) ⟨256166, by rfl⟩ : syracuseStep 341555 = 512333) B512333
theorem B767555 : Blo 338752 767555 := bstep (se 1 (by rfl) ⟨575666, by rfl⟩ : syracuseStep 767555 = 1151333) B1151333
theorem B341571 : Blo 338752 341571 := bstep (se 1 (by rfl) ⟨256178, by rfl⟩ : syracuseStep 341571 = 512357) B512357
theorem B341587 : Blo 338752 341587 := bstep (se 1 (by rfl) ⟨256190, by rfl⟩ : syracuseStep 341587 = 512381) B512381
theorem B341603 : Blo 338752 341603 := bstep (se 1 (by rfl) ⟨256202, by rfl⟩ : syracuseStep 341603 = 512405) B512405
theorem B1095277 : Blo 338752 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B341619 : Blo 338752 341619 := bstep (se 1 (by rfl) ⟨256214, by rfl⟩ : syracuseStep 341619 = 512429) B512429
theorem B341635 : Blo 338752 341635 := bstep (se 1 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 341635 = 512453) B512453
theorem B341651 : Blo 338752 341651 := bstep (se 1 (by rfl) ⟨256238, by rfl⟩ : syracuseStep 341651 = 512477) B512477
theorem B341667 : Blo 338752 341667 := bstep (se 1 (by rfl) ⟨256250, by rfl⟩ : syracuseStep 341667 = 512501) B512501
theorem B341683 : Blo 338752 341683 := bstep (se 1 (by rfl) ⟨256262, by rfl⟩ : syracuseStep 341683 = 512525) B512525
theorem B341699 : Blo 338752 341699 := bstep (se 1 (by rfl) ⟨256274, by rfl⟩ : syracuseStep 341699 = 512549) B512549
theorem B1947341 : Blo 338752 1947341 := bstep (se 3 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 1947341 = 730253) B730253
theorem B341715 : Blo 338752 341715 := bstep (se 1 (by rfl) ⟨256286, by rfl⟩ : syracuseStep 341715 = 512573) B512573
theorem B341731 : Blo 338752 341731 := bstep (se 1 (by rfl) ⟨256298, by rfl⟩ : syracuseStep 341731 = 512597) B512597
theorem B341747 : Blo 338752 341747 := bstep (se 1 (by rfl) ⟨256310, by rfl⟩ : syracuseStep 341747 = 512621) B512621
theorem B341763 : Blo 338752 341763 := bstep (se 1 (by rfl) ⟨256322, by rfl⟩ : syracuseStep 341763 = 512645) B512645
theorem B341779 : Blo 338752 341779 := bstep (se 1 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 341779 = 512669) B512669
theorem B341795 : Blo 338752 341795 := bstep (se 1 (by rfl) ⟨256346, by rfl⟩ : syracuseStep 341795 = 512693) B512693
theorem B341811 : Blo 338752 341811 := bstep (se 1 (by rfl) ⟨256358, by rfl⟩ : syracuseStep 341811 = 512717) B512717
theorem B341827 : Blo 338752 341827 := bstep (se 1 (by rfl) ⟨256370, by rfl⟩ : syracuseStep 341827 = 512741) B512741
theorem B767825 : Blo 338752 767825 := bstep (se 2 (by rfl) ⟨287934, by rfl⟩ : syracuseStep 767825 = 575869) B575869
theorem B341843 : Blo 338752 341843 := bstep (se 1 (by rfl) ⟨256382, by rfl⟩ : syracuseStep 341843 = 512765) B512765
theorem B767843 : Blo 338752 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B341859 : Blo 338752 341859 := bstep (se 1 (by rfl) ⟨256394, by rfl⟩ : syracuseStep 341859 = 512789) B512789
theorem B341875 : Blo 338752 341875 := bstep (se 1 (by rfl) ⟨256406, by rfl⟩ : syracuseStep 341875 = 512813) B512813
theorem B341891 : Blo 338752 341891 := bstep (se 1 (by rfl) ⟨256418, by rfl⟩ : syracuseStep 341891 = 512837) B512837
theorem B407443 : Blo 338752 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B341907 : Blo 338752 341907 := bstep (se 1 (by rfl) ⟨256430, by rfl⟩ : syracuseStep 341907 = 512861) B512861
theorem B341923 : Blo 338752 341923 := bstep (se 1 (by rfl) ⟨256442, by rfl⟩ : syracuseStep 341923 = 512885) B512885
theorem B341939 : Blo 338752 341939 := bstep (se 1 (by rfl) ⟨256454, by rfl⟩ : syracuseStep 341939 = 512909) B512909
theorem B341955 : Blo 338752 341955 := bstep (se 1 (by rfl) ⟨256466, by rfl⟩ : syracuseStep 341955 = 512933) B512933
theorem B341971 : Blo 338752 341971 := bstep (se 1 (by rfl) ⟨256478, by rfl⟩ : syracuseStep 341971 = 512957) B512957
theorem B341987 : Blo 338752 341987 := bstep (se 1 (by rfl) ⟨256490, by rfl⟩ : syracuseStep 341987 = 512981) B512981
theorem B342003 : Blo 338752 342003 := bstep (se 1 (by rfl) ⟨256502, by rfl⟩ : syracuseStep 342003 = 513005) B513005
theorem B342019 : Blo 338752 342019 := bstep (se 1 (by rfl) ⟨256514, by rfl⟩ : syracuseStep 342019 = 513029) B513029
theorem B342035 : Blo 338752 342035 := bstep (se 1 (by rfl) ⟨256526, by rfl⟩ : syracuseStep 342035 = 513053) B513053
theorem B407587 : Blo 338752 407587 := bstep (se 1 (by rfl) ⟨305690, by rfl⟩ : syracuseStep 407587 = 611381) B611381
theorem B342051 : Blo 338752 342051 := bstep (se 1 (by rfl) ⟨256538, by rfl⟩ : syracuseStep 342051 = 513077) B513077
theorem B342067 : Blo 338752 342067 := bstep (se 1 (by rfl) ⟨256550, by rfl⟩ : syracuseStep 342067 = 513101) B513101
theorem B342083 : Blo 338752 342083 := bstep (se 1 (by rfl) ⟨256562, by rfl⟩ : syracuseStep 342083 = 513125) B513125
theorem B342099 : Blo 338752 342099 := bstep (se 1 (by rfl) ⟨256574, by rfl⟩ : syracuseStep 342099 = 513149) B513149
theorem B342115 : Blo 338752 342115 := bstep (se 1 (by rfl) ⟨256586, by rfl⟩ : syracuseStep 342115 = 513173) B513173
theorem B768113 : Blo 338752 768113 := bstep (se 2 (by rfl) ⟨288042, by rfl⟩ : syracuseStep 768113 = 576085) B576085
theorem B342131 : Blo 338752 342131 := bstep (se 1 (by rfl) ⟨256598, by rfl⟩ : syracuseStep 342131 = 513197) B513197
theorem B768131 : Blo 338752 768131 := bstep (se 1 (by rfl) ⟨576098, by rfl⟩ : syracuseStep 768131 = 1152197) B1152197
theorem B342147 : Blo 338752 342147 := bstep (se 1 (by rfl) ⟨256610, by rfl⟩ : syracuseStep 342147 = 513221) B513221
theorem B342163 : Blo 338752 342163 := bstep (se 1 (by rfl) ⟨256622, by rfl⟩ : syracuseStep 342163 = 513245) B513245
theorem B342179 : Blo 338752 342179 := bstep (se 1 (by rfl) ⟨256634, by rfl⟩ : syracuseStep 342179 = 513269) B513269
theorem B342195 : Blo 338752 342195 := bstep (se 1 (by rfl) ⟨256646, by rfl⟩ : syracuseStep 342195 = 513293) B513293
theorem B342211 : Blo 338752 342211 := bstep (se 1 (by rfl) ⟨256658, by rfl⟩ : syracuseStep 342211 = 513317) B513317
theorem B342227 : Blo 338752 342227 := bstep (se 1 (by rfl) ⟨256670, by rfl⟩ : syracuseStep 342227 = 513341) B513341
theorem B342243 : Blo 338752 342243 := bstep (se 1 (by rfl) ⟨256682, by rfl⟩ : syracuseStep 342243 = 513365) B513365
theorem B342259 : Blo 338752 342259 := bstep (se 1 (by rfl) ⟨256694, by rfl⟩ : syracuseStep 342259 = 513389) B513389
theorem B342275 : Blo 338752 342275 := bstep (se 1 (by rfl) ⟨256706, by rfl⟩ : syracuseStep 342275 = 513413) B513413
theorem B342291 : Blo 338752 342291 := bstep (se 1 (by rfl) ⟨256718, by rfl⟩ : syracuseStep 342291 = 513437) B513437
theorem B342307 : Blo 338752 342307 := bstep (se 1 (by rfl) ⟨256730, by rfl⟩ : syracuseStep 342307 = 513461) B513461
theorem B866609 : Blo 338752 866609 := bstep (se 2 (by rfl) ⟨324978, by rfl⟩ : syracuseStep 866609 = 649957) B649957
theorem B342323 : Blo 338752 342323 := bstep (se 1 (by rfl) ⟨256742, by rfl⟩ : syracuseStep 342323 = 513485) B513485
theorem B342339 : Blo 338752 342339 := bstep (se 1 (by rfl) ⟨256754, by rfl⟩ : syracuseStep 342339 = 513509) B513509
theorem B342355 : Blo 338752 342355 := bstep (se 1 (by rfl) ⟨256766, by rfl⟩ : syracuseStep 342355 = 513533) B513533
theorem B571745 : Blo 338752 571745 := bstep (se 2 (by rfl) ⟨214404, by rfl⟩ : syracuseStep 571745 = 428809) B428809
theorem B342371 : Blo 338752 342371 := bstep (se 1 (by rfl) ⟨256778, by rfl⟩ : syracuseStep 342371 = 513557) B513557
theorem B866659 : Blo 338752 866659 := bstep (se 1 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 866659 = 1299989) B1299989
theorem B342387 : Blo 338752 342387 := bstep (se 1 (by rfl) ⟨256790, by rfl⟩ : syracuseStep 342387 = 513581) B513581
theorem B342403 : Blo 338752 342403 := bstep (se 1 (by rfl) ⟨256802, by rfl⟩ : syracuseStep 342403 = 513605) B513605
theorem B768401 : Blo 338752 768401 := bstep (se 2 (by rfl) ⟨288150, by rfl⟩ : syracuseStep 768401 = 576301) B576301
theorem B342419 : Blo 338752 342419 := bstep (se 1 (by rfl) ⟨256814, by rfl⟩ : syracuseStep 342419 = 513629) B513629
theorem B768419 : Blo 338752 768419 := bstep (se 1 (by rfl) ⟨576314, by rfl⟩ : syracuseStep 768419 = 1152629) B1152629
theorem B342435 : Blo 338752 342435 := bstep (se 1 (by rfl) ⟨256826, by rfl⟩ : syracuseStep 342435 = 513653) B513653
theorem B342451 : Blo 338752 342451 := bstep (se 1 (by rfl) ⟨256838, by rfl⟩ : syracuseStep 342451 = 513677) B513677
theorem B342467 : Blo 338752 342467 := bstep (se 1 (by rfl) ⟨256850, by rfl⟩ : syracuseStep 342467 = 513701) B513701
theorem B342483 : Blo 338752 342483 := bstep (se 1 (by rfl) ⟨256862, by rfl⟩ : syracuseStep 342483 = 513725) B513725
theorem B571873 : Blo 338752 571873 := bstep (se 2 (by rfl) ⟨214452, by rfl⟩ : syracuseStep 571873 = 428905) B428905
theorem B342499 : Blo 338752 342499 := bstep (se 1 (by rfl) ⟨256874, by rfl⟩ : syracuseStep 342499 = 513749) B513749
theorem B965105 : Blo 338752 965105 := bstep (se 2 (by rfl) ⟨361914, by rfl⟩ : syracuseStep 965105 = 723829) B723829
theorem B866801 : Blo 338752 866801 := bstep (se 2 (by rfl) ⟨325050, by rfl⟩ : syracuseStep 866801 = 650101) B650101
theorem B342515 : Blo 338752 342515 := bstep (se 1 (by rfl) ⟨256886, by rfl⟩ : syracuseStep 342515 = 513773) B513773
theorem B571907 : Blo 338752 571907 := bstep (se 1 (by rfl) ⟨428930, by rfl⟩ : syracuseStep 571907 = 857861) B857861
theorem B342531 : Blo 338752 342531 := bstep (se 1 (by rfl) ⟨256898, by rfl⟩ : syracuseStep 342531 = 513797) B513797
theorem B342547 : Blo 338752 342547 := bstep (se 1 (by rfl) ⟨256910, by rfl⟩ : syracuseStep 342547 = 513821) B513821
theorem B1718819 : Blo 338752 1718819 := bstep (se 1 (by rfl) ⟨1289114, by rfl⟩ : syracuseStep 1718819 = 2578229) B2578229
theorem B342563 : Blo 338752 342563 := bstep (se 1 (by rfl) ⟨256922, by rfl⟩ : syracuseStep 342563 = 513845) B513845
theorem B1030705 : Blo 338752 1030705 := bstep (se 2 (by rfl) ⟨386514, by rfl⟩ : syracuseStep 1030705 = 773029) B773029
theorem B342579 : Blo 338752 342579 := bstep (se 1 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 342579 = 513869) B513869
theorem B342595 : Blo 338752 342595 := bstep (se 1 (by rfl) ⟨256946, by rfl⟩ : syracuseStep 342595 = 513893) B513893
theorem B342611 : Blo 338752 342611 := bstep (se 1 (by rfl) ⟨256958, by rfl⟩ : syracuseStep 342611 = 513917) B513917
theorem B342627 : Blo 338752 342627 := bstep (se 1 (by rfl) ⟨256970, by rfl⟩ : syracuseStep 342627 = 513941) B513941
theorem B13318769 : Blo 338752 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B342643 : Blo 338752 342643 := bstep (se 1 (by rfl) ⟨256982, by rfl⟩ : syracuseStep 342643 = 513965) B513965
theorem B572035 : Blo 338752 572035 := bstep (se 1 (by rfl) ⟨429026, by rfl⟩ : syracuseStep 572035 = 858053) B858053
theorem B342659 : Blo 338752 342659 := bstep (se 1 (by rfl) ⟨256994, by rfl⟩ : syracuseStep 342659 = 513989) B513989
theorem B342675 : Blo 338752 342675 := bstep (se 1 (by rfl) ⟨257006, by rfl⟩ : syracuseStep 342675 = 514013) B514013
theorem B1096355 : Blo 338752 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B342691 : Blo 338752 342691 := bstep (se 1 (by rfl) ⟨257018, by rfl⟩ : syracuseStep 342691 = 514037) B514037
theorem B768689 : Blo 338752 768689 := bstep (se 2 (by rfl) ⟨288258, by rfl⟩ : syracuseStep 768689 = 576517) B576517
theorem B342707 : Blo 338752 342707 := bstep (se 1 (by rfl) ⟨257030, by rfl⟩ : syracuseStep 342707 = 514061) B514061
theorem B768707 : Blo 338752 768707 := bstep (se 1 (by rfl) ⟨576530, by rfl⟩ : syracuseStep 768707 = 1153061) B1153061
theorem B342723 : Blo 338752 342723 := bstep (se 1 (by rfl) ⟨257042, by rfl⟩ : syracuseStep 342723 = 514085) B514085
theorem B342739 : Blo 338752 342739 := bstep (se 1 (by rfl) ⟨257054, by rfl⟩ : syracuseStep 342739 = 514109) B514109
theorem B572177 : Blo 338752 572177 := bstep (se 2 (by rfl) ⟨214566, by rfl⟩ : syracuseStep 572177 = 429133) B429133
theorem B1293155 : Blo 338752 1293155 := bstep (se 1 (by rfl) ⟨969866, by rfl⟩ : syracuseStep 1293155 = 1939733) B1939733
theorem B572305 : Blo 338752 572305 := bstep (se 2 (by rfl) ⟨214614, by rfl⟩ : syracuseStep 572305 = 429229) B429229
theorem B572339 : Blo 338752 572339 := bstep (se 1 (by rfl) ⟨429254, by rfl⟩ : syracuseStep 572339 = 858509) B858509
theorem B768977 : Blo 338752 768977 := bstep (se 2 (by rfl) ⟨288366, by rfl⟩ : syracuseStep 768977 = 576733) B576733
theorem B768995 : Blo 338752 768995 := bstep (se 1 (by rfl) ⟨576746, by rfl⟩ : syracuseStep 768995 = 1153493) B1153493
theorem B1850339 : Blo 338752 1850339 := bstep (se 1 (by rfl) ⟨1387754, by rfl⟩ : syracuseStep 1850339 = 2775509) B2775509
theorem B572467 : Blo 338752 572467 := bstep (se 1 (by rfl) ⟨429350, by rfl⟩ : syracuseStep 572467 = 858701) B858701
theorem B4668515 : Blo 338752 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B572609 : Blo 338752 572609 := bstep (se 2 (by rfl) ⟨214728, by rfl⟩ : syracuseStep 572609 = 429457) B429457
theorem B769265 : Blo 338752 769265 := bstep (se 2 (by rfl) ⟨288474, by rfl⟩ : syracuseStep 769265 = 576949) B576949
theorem B769283 : Blo 338752 769283 := bstep (se 1 (by rfl) ⟨576962, by rfl⟩ : syracuseStep 769283 = 1153925) B1153925
theorem B1097009 : Blo 338752 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B572737 : Blo 338752 572737 := bstep (se 2 (by rfl) ⟨214776, by rfl⟩ : syracuseStep 572737 = 429553) B429553
theorem B1719629 : Blo 338752 1719629 := bstep (se 3 (by rfl) ⟨322430, by rfl⟩ : syracuseStep 1719629 = 644861) B644861
theorem B572771 : Blo 338752 572771 := bstep (se 1 (by rfl) ⟨429578, by rfl⟩ : syracuseStep 572771 = 859157) B859157
theorem B572899 : Blo 338752 572899 := bstep (se 1 (by rfl) ⟨429674, by rfl⟩ : syracuseStep 572899 = 859349) B859349
theorem B769553 : Blo 338752 769553 := bstep (se 2 (by rfl) ⟨288582, by rfl⟩ : syracuseStep 769553 = 577165) B577165
theorem B769571 : Blo 338752 769571 := bstep (se 1 (by rfl) ⟨577178, by rfl⟩ : syracuseStep 769571 = 1154357) B1154357
theorem B573041 : Blo 338752 573041 := bstep (se 2 (by rfl) ⟨214890, by rfl⟩ : syracuseStep 573041 = 429781) B429781
theorem B1556131 : Blo 338752 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B573169 : Blo 338752 573169 := bstep (se 2 (by rfl) ⟨214938, by rfl⟩ : syracuseStep 573169 = 429877) B429877
theorem B573203 : Blo 338752 573203 := bstep (se 1 (by rfl) ⟨429902, by rfl⟩ : syracuseStep 573203 = 859805) B859805
theorem B409379 : Blo 338752 409379 := bstep (se 1 (by rfl) ⟨307034, by rfl⟩ : syracuseStep 409379 = 614069) B614069
theorem B769841 : Blo 338752 769841 := bstep (se 2 (by rfl) ⟨288690, by rfl⟩ : syracuseStep 769841 = 577381) B577381
theorem B507713 : Blo 338752 507713 := bstep (se 2 (by rfl) ⟨190392, by rfl⟩ : syracuseStep 507713 = 380785) B380785
theorem B769859 : Blo 338752 769859 := bstep (se 1 (by rfl) ⟨577394, by rfl⟩ : syracuseStep 769859 = 1154789) B1154789
theorem B1294157 : Blo 338752 1294157 := bstep (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) B485309
theorem B573331 : Blo 338752 573331 := bstep (se 1 (by rfl) ⟨429998, by rfl⟩ : syracuseStep 573331 = 859997) B859997
theorem B966563 : Blo 338752 966563 := bstep (se 1 (by rfl) ⟨724922, by rfl⟩ : syracuseStep 966563 = 1449845) B1449845
theorem B573473 : Blo 338752 573473 := bstep (se 2 (by rfl) ⟨215052, by rfl⟩ : syracuseStep 573473 = 430105) B430105
theorem B770129 : Blo 338752 770129 := bstep (se 2 (by rfl) ⟨288798, by rfl⟩ : syracuseStep 770129 = 577597) B577597
theorem B770147 : Blo 338752 770147 := bstep (se 1 (by rfl) ⟨577610, by rfl⟩ : syracuseStep 770147 = 1155221) B1155221
theorem B573601 : Blo 338752 573601 := bstep (se 2 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 573601 = 430201) B430201
theorem B1851569 : Blo 338752 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B573635 : Blo 338752 573635 := bstep (se 1 (by rfl) ⟨430226, by rfl⟩ : syracuseStep 573635 = 860453) B860453
theorem B508145 : Blo 338752 508145 := bstep (se 2 (by rfl) ⟨190554, by rfl⟩ : syracuseStep 508145 = 381109) B381109
theorem B508163 : Blo 338752 508163 := bstep (se 1 (by rfl) ⟨381122, by rfl⟩ : syracuseStep 508163 = 762245) B762245
theorem B508193 : Blo 338752 508193 := bstep (se 2 (by rfl) ⟨190572, by rfl⟩ : syracuseStep 508193 = 381145) B381145
theorem B508211 : Blo 338752 508211 := bstep (se 1 (by rfl) ⟨381158, by rfl⟩ : syracuseStep 508211 = 762317) B762317
theorem B573763 : Blo 338752 573763 := bstep (se 1 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 573763 = 860645) B860645
theorem B508241 : Blo 338752 508241 := bstep (se 2 (by rfl) ⟨190590, by rfl⟩ : syracuseStep 508241 = 381181) B381181
theorem B508259 : Blo 338752 508259 := bstep (se 1 (by rfl) ⟨381194, by rfl⟩ : syracuseStep 508259 = 762389) B762389
theorem B770417 : Blo 338752 770417 := bstep (se 2 (by rfl) ⟨288906, by rfl⟩ : syracuseStep 770417 = 577813) B577813
theorem B508289 : Blo 338752 508289 := bstep (se 2 (by rfl) ⟨190608, by rfl⟩ : syracuseStep 508289 = 381217) B381217
theorem B770435 : Blo 338752 770435 := bstep (se 1 (by rfl) ⟨577826, by rfl⟩ : syracuseStep 770435 = 1155653) B1155653
theorem B508307 : Blo 338752 508307 := bstep (se 1 (by rfl) ⟨381230, by rfl⟩ : syracuseStep 508307 = 762461) B762461
theorem B508337 : Blo 338752 508337 := bstep (se 2 (by rfl) ⟨190626, by rfl⟩ : syracuseStep 508337 = 381253) B381253
theorem B508355 : Blo 338752 508355 := bstep (se 1 (by rfl) ⟨381266, by rfl⟩ : syracuseStep 508355 = 762533) B762533
theorem B573905 : Blo 338752 573905 := bstep (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) B430429
theorem B508385 : Blo 338752 508385 := bstep (se 2 (by rfl) ⟨190644, by rfl⟩ : syracuseStep 508385 = 381289) B381289
theorem B508403 : Blo 338752 508403 := bstep (se 1 (by rfl) ⟨381302, by rfl⟩ : syracuseStep 508403 = 762605) B762605
theorem B508433 : Blo 338752 508433 := bstep (se 2 (by rfl) ⟨190662, by rfl⟩ : syracuseStep 508433 = 381325) B381325
theorem B508451 : Blo 338752 508451 := bstep (se 1 (by rfl) ⟨381338, by rfl⟩ : syracuseStep 508451 = 762677) B762677
theorem B1753649 : Blo 338752 1753649 := bstep (se 2 (by rfl) ⟨657618, by rfl⟩ : syracuseStep 1753649 = 1315237) B1315237
theorem B1950257 : Blo 338752 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B508481 : Blo 338752 508481 := bstep (se 2 (by rfl) ⟨190680, by rfl⟩ : syracuseStep 508481 = 381361) B381361
theorem B574033 : Blo 338752 574033 := bstep (se 2 (by rfl) ⟨215262, by rfl⟩ : syracuseStep 574033 = 430525) B430525
theorem B508499 : Blo 338752 508499 := bstep (se 1 (by rfl) ⟨381374, by rfl⟩ : syracuseStep 508499 = 762749) B762749
theorem B508529 : Blo 338752 508529 := bstep (se 2 (by rfl) ⟨190698, by rfl⟩ : syracuseStep 508529 = 381397) B381397
theorem B574067 : Blo 338752 574067 := bstep (se 1 (by rfl) ⟨430550, by rfl⟩ : syracuseStep 574067 = 861101) B861101
theorem B508547 : Blo 338752 508547 := bstep (se 1 (by rfl) ⟨381410, by rfl⟩ : syracuseStep 508547 = 762821) B762821
theorem B770705 : Blo 338752 770705 := bstep (se 2 (by rfl) ⟨289014, by rfl⟩ : syracuseStep 770705 = 578029) B578029
theorem B508577 : Blo 338752 508577 := bstep (se 2 (by rfl) ⟨190716, by rfl⟩ : syracuseStep 508577 = 381433) B381433
theorem B770723 : Blo 338752 770723 := bstep (se 1 (by rfl) ⟨578042, by rfl⟩ : syracuseStep 770723 = 1156085) B1156085
theorem B508595 : Blo 338752 508595 := bstep (se 1 (by rfl) ⟨381446, by rfl⟩ : syracuseStep 508595 = 762893) B762893
theorem B967373 : Blo 338752 967373 := bstep (se 3 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 967373 = 362765) B362765
theorem B508625 : Blo 338752 508625 := bstep (se 2 (by rfl) ⟨190734, by rfl⟩ : syracuseStep 508625 = 381469) B381469
theorem B508643 : Blo 338752 508643 := bstep (se 1 (by rfl) ⟨381482, by rfl⟩ : syracuseStep 508643 = 762965) B762965
theorem B574195 : Blo 338752 574195 := bstep (se 1 (by rfl) ⟨430646, by rfl⟩ : syracuseStep 574195 = 861293) B861293
theorem B508673 : Blo 338752 508673 := bstep (se 2 (by rfl) ⟨190752, by rfl⟩ : syracuseStep 508673 = 381505) B381505
theorem B508691 : Blo 338752 508691 := bstep (se 1 (by rfl) ⟨381518, by rfl⟩ : syracuseStep 508691 = 763037) B763037
theorem B508721 : Blo 338752 508721 := bstep (se 2 (by rfl) ⟨190770, by rfl⟩ : syracuseStep 508721 = 381541) B381541
theorem B3687221 : Blo 338752 3687221 := bstep (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) B345677
theorem B508739 : Blo 338752 508739 := bstep (se 1 (by rfl) ⟨381554, by rfl⟩ : syracuseStep 508739 = 763109) B763109
theorem B508769 : Blo 338752 508769 := bstep (se 2 (by rfl) ⟨190788, by rfl⟩ : syracuseStep 508769 = 381577) B381577
theorem B508787 : Blo 338752 508787 := bstep (se 1 (by rfl) ⟨381590, by rfl⟩ : syracuseStep 508787 = 763181) B763181
theorem B574337 : Blo 338752 574337 := bstep (se 2 (by rfl) ⟨215376, by rfl⟩ : syracuseStep 574337 = 430753) B430753
theorem B967565 : Blo 338752 967565 := bstep (se 3 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 967565 = 362837) B362837
theorem B508817 : Blo 338752 508817 := bstep (se 2 (by rfl) ⟨190806, by rfl⟩ : syracuseStep 508817 = 381613) B381613
theorem B508835 : Blo 338752 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B770993 : Blo 338752 770993 := bstep (se 2 (by rfl) ⟨289122, by rfl⟩ : syracuseStep 770993 = 578245) B578245
theorem B508865 : Blo 338752 508865 := bstep (se 2 (by rfl) ⟨190824, by rfl⟩ : syracuseStep 508865 = 381649) B381649
theorem B771011 : Blo 338752 771011 := bstep (se 1 (by rfl) ⟨578258, by rfl⟩ : syracuseStep 771011 = 1156517) B1156517
theorem B508883 : Blo 338752 508883 := bstep (se 1 (by rfl) ⟨381662, by rfl⟩ : syracuseStep 508883 = 763325) B763325
theorem B508913 : Blo 338752 508913 := bstep (se 2 (by rfl) ⟨190842, by rfl⟩ : syracuseStep 508913 = 381685) B381685
theorem B574465 : Blo 338752 574465 := bstep (se 2 (by rfl) ⟨215424, by rfl⟩ : syracuseStep 574465 = 430849) B430849
theorem B508931 : Blo 338752 508931 := bstep (se 1 (by rfl) ⟨381698, by rfl⟩ : syracuseStep 508931 = 763397) B763397
theorem B508961 : Blo 338752 508961 := bstep (se 2 (by rfl) ⟨190860, by rfl⟩ : syracuseStep 508961 = 381721) B381721
theorem B574499 : Blo 338752 574499 := bstep (se 1 (by rfl) ⟨430874, by rfl⟩ : syracuseStep 574499 = 861749) B861749
theorem B508979 : Blo 338752 508979 := bstep (se 1 (by rfl) ⟨381734, by rfl⟩ : syracuseStep 508979 = 763469) B763469
theorem B509009 : Blo 338752 509009 := bstep (se 2 (by rfl) ⟨190878, by rfl⟩ : syracuseStep 509009 = 381757) B381757
theorem B509027 : Blo 338752 509027 := bstep (se 1 (by rfl) ⟨381770, by rfl⟩ : syracuseStep 509027 = 763541) B763541
theorem B509057 : Blo 338752 509057 := bstep (se 2 (by rfl) ⟨190896, by rfl⟩ : syracuseStep 509057 = 381793) B381793
theorem B509075 : Blo 338752 509075 := bstep (se 1 (by rfl) ⟨381806, by rfl⟩ : syracuseStep 509075 = 763613) B763613
theorem B574627 : Blo 338752 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B509105 : Blo 338752 509105 := bstep (se 2 (by rfl) ⟨190914, by rfl⟩ : syracuseStep 509105 = 381829) B381829
theorem B509123 : Blo 338752 509123 := bstep (se 1 (by rfl) ⟨381842, by rfl⟩ : syracuseStep 509123 = 763685) B763685
theorem B6571205 : Blo 338752 6571205 := bstep (se 4 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 6571205 = 1232101) B1232101
theorem B509153 : Blo 338752 509153 := bstep (se 2 (by rfl) ⟨190932, by rfl⟩ : syracuseStep 509153 = 381865) B381865
theorem B509171 : Blo 338752 509171 := bstep (se 1 (by rfl) ⟨381878, by rfl⟩ : syracuseStep 509171 = 763757) B763757
theorem B2180357 : Blo 338752 2180357 := bstep (se 4 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 2180357 = 408817) B408817
theorem B509201 : Blo 338752 509201 := bstep (se 2 (by rfl) ⟨190950, by rfl⟩ : syracuseStep 509201 = 381901) B381901
theorem B509219 : Blo 338752 509219 := bstep (se 1 (by rfl) ⟨381914, by rfl⟩ : syracuseStep 509219 = 763829) B763829
theorem B574769 : Blo 338752 574769 := bstep (se 2 (by rfl) ⟨215538, by rfl⟩ : syracuseStep 574769 = 431077) B431077
theorem B509249 : Blo 338752 509249 := bstep (se 2 (by rfl) ⟨190968, by rfl⟩ : syracuseStep 509249 = 381937) B381937
theorem B509267 : Blo 338752 509267 := bstep (se 1 (by rfl) ⟨381950, by rfl⟩ : syracuseStep 509267 = 763901) B763901
theorem B509297 : Blo 338752 509297 := bstep (se 2 (by rfl) ⟨190986, by rfl⟩ : syracuseStep 509297 = 381973) B381973
theorem B509315 : Blo 338752 509315 := bstep (se 1 (by rfl) ⟨381986, by rfl⟩ : syracuseStep 509315 = 763973) B763973
theorem B509345 : Blo 338752 509345 := bstep (se 2 (by rfl) ⟨191004, by rfl⟩ : syracuseStep 509345 = 382009) B382009
theorem B1459619 : Blo 338752 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B574897 : Blo 338752 574897 := bstep (se 2 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 574897 = 431173) B431173
theorem B509363 : Blo 338752 509363 := bstep (se 1 (by rfl) ⟨382022, by rfl⟩ : syracuseStep 509363 = 764045) B764045
theorem B509393 : Blo 338752 509393 := bstep (se 2 (by rfl) ⟨191022, by rfl⟩ : syracuseStep 509393 = 382045) B382045
theorem B574931 : Blo 338752 574931 := bstep (se 1 (by rfl) ⟨431198, by rfl⟩ : syracuseStep 574931 = 862397) B862397
theorem B509411 : Blo 338752 509411 := bstep (se 1 (by rfl) ⟨382058, by rfl⟩ : syracuseStep 509411 = 764117) B764117
theorem B509441 : Blo 338752 509441 := bstep (se 2 (by rfl) ⟨191040, by rfl⟩ : syracuseStep 509441 = 382081) B382081
theorem B509459 : Blo 338752 509459 := bstep (se 1 (by rfl) ⟨382094, by rfl⟩ : syracuseStep 509459 = 764189) B764189
theorem B509489 : Blo 338752 509489 := bstep (se 2 (by rfl) ⟨191058, by rfl⟩ : syracuseStep 509489 = 382117) B382117
theorem B509507 : Blo 338752 509507 := bstep (se 1 (by rfl) ⟨382130, by rfl⟩ : syracuseStep 509507 = 764261) B764261
theorem B575059 : Blo 338752 575059 := bstep (se 1 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 575059 = 862589) B862589
theorem B509537 : Blo 338752 509537 := bstep (se 2 (by rfl) ⟨191076, by rfl⟩ : syracuseStep 509537 = 382153) B382153
theorem B869987 : Blo 338752 869987 := bstep (se 1 (by rfl) ⟨652490, by rfl⟩ : syracuseStep 869987 = 1304981) B1304981
theorem B509555 : Blo 338752 509555 := bstep (se 1 (by rfl) ⟨382166, by rfl⟩ : syracuseStep 509555 = 764333) B764333
theorem B509585 : Blo 338752 509585 := bstep (se 2 (by rfl) ⟨191094, by rfl⟩ : syracuseStep 509585 = 382189) B382189
theorem B509603 : Blo 338752 509603 := bstep (se 1 (by rfl) ⟨382202, by rfl⟩ : syracuseStep 509603 = 764405) B764405
theorem B509633 : Blo 338752 509633 := bstep (se 2 (by rfl) ⟨191112, by rfl⟩ : syracuseStep 509633 = 382225) B382225
theorem B509651 : Blo 338752 509651 := bstep (se 1 (by rfl) ⟨382238, by rfl⟩ : syracuseStep 509651 = 764477) B764477
theorem B575201 : Blo 338752 575201 := bstep (se 2 (by rfl) ⟨215700, by rfl⟩ : syracuseStep 575201 = 431401) B431401
theorem B509681 : Blo 338752 509681 := bstep (se 2 (by rfl) ⟨191130, by rfl⟩ : syracuseStep 509681 = 382261) B382261
theorem B509699 : Blo 338752 509699 := bstep (se 1 (by rfl) ⟨382274, by rfl⟩ : syracuseStep 509699 = 764549) B764549
theorem B509729 : Blo 338752 509729 := bstep (se 2 (by rfl) ⟨191148, by rfl⟩ : syracuseStep 509729 = 382297) B382297
theorem B509747 : Blo 338752 509747 := bstep (se 1 (by rfl) ⟨382310, by rfl⟩ : syracuseStep 509747 = 764621) B764621
theorem B509777 : Blo 338752 509777 := bstep (se 2 (by rfl) ⟨191166, by rfl⟩ : syracuseStep 509777 = 382333) B382333
theorem B575329 : Blo 338752 575329 := bstep (se 2 (by rfl) ⟨215748, by rfl⟩ : syracuseStep 575329 = 431497) B431497
theorem B509795 : Blo 338752 509795 := bstep (se 1 (by rfl) ⟨382346, by rfl⟩ : syracuseStep 509795 = 764693) B764693
theorem B968557 : Blo 338752 968557 := bstep (se 3 (by rfl) ⟨181604, by rfl⟩ : syracuseStep 968557 = 363209) B363209
theorem B509825 : Blo 338752 509825 := bstep (se 2 (by rfl) ⟨191184, by rfl⟩ : syracuseStep 509825 = 382369) B382369
theorem B575363 : Blo 338752 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B1296269 : Blo 338752 1296269 := bstep (se 3 (by rfl) ⟨243050, by rfl⟩ : syracuseStep 1296269 = 486101) B486101
theorem B509843 : Blo 338752 509843 := bstep (se 1 (by rfl) ⟨382382, by rfl⟩ : syracuseStep 509843 = 764765) B764765
theorem B509873 : Blo 338752 509873 := bstep (se 2 (by rfl) ⟨191202, by rfl⟩ : syracuseStep 509873 = 382405) B382405
theorem B509891 : Blo 338752 509891 := bstep (se 1 (by rfl) ⟨382418, by rfl⟩ : syracuseStep 509891 = 764837) B764837
theorem B509921 : Blo 338752 509921 := bstep (se 2 (by rfl) ⟨191220, by rfl⟩ : syracuseStep 509921 = 382441) B382441
theorem B1951715 : Blo 338752 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B509939 : Blo 338752 509939 := bstep (se 1 (by rfl) ⟨382454, by rfl⟩ : syracuseStep 509939 = 764909) B764909
theorem B575491 : Blo 338752 575491 := bstep (se 1 (by rfl) ⟨431618, by rfl⟩ : syracuseStep 575491 = 863237) B863237
theorem B509969 : Blo 338752 509969 := bstep (se 2 (by rfl) ⟨191238, by rfl⟩ : syracuseStep 509969 = 382477) B382477
theorem B509987 : Blo 338752 509987 := bstep (se 1 (by rfl) ⟨382490, by rfl⟩ : syracuseStep 509987 = 764981) B764981
theorem B510017 : Blo 338752 510017 := bstep (se 2 (by rfl) ⟨191256, by rfl⟩ : syracuseStep 510017 = 382513) B382513
theorem B510035 : Blo 338752 510035 := bstep (se 1 (by rfl) ⟨382526, by rfl⟩ : syracuseStep 510035 = 765053) B765053
theorem B510065 : Blo 338752 510065 := bstep (se 2 (by rfl) ⟨191274, by rfl⟩ : syracuseStep 510065 = 382549) B382549
theorem B510083 : Blo 338752 510083 := bstep (se 1 (by rfl) ⟨382562, by rfl⟩ : syracuseStep 510083 = 765125) B765125
theorem B575633 : Blo 338752 575633 := bstep (se 2 (by rfl) ⟨215862, by rfl⟩ : syracuseStep 575633 = 431725) B431725
theorem B510113 : Blo 338752 510113 := bstep (se 2 (by rfl) ⟨191292, by rfl⟩ : syracuseStep 510113 = 382585) B382585
theorem B1722545 : Blo 338752 1722545 := bstep (se 2 (by rfl) ⟨645954, by rfl⟩ : syracuseStep 1722545 = 1291909) B1291909
theorem B510131 : Blo 338752 510131 := bstep (se 1 (by rfl) ⟨382598, by rfl⟩ : syracuseStep 510131 = 765197) B765197
theorem B510161 : Blo 338752 510161 := bstep (se 2 (by rfl) ⟨191310, by rfl⟩ : syracuseStep 510161 = 382621) B382621
theorem B510179 : Blo 338752 510179 := bstep (se 1 (by rfl) ⟨382634, by rfl⟩ : syracuseStep 510179 = 765269) B765269
theorem B510209 : Blo 338752 510209 := bstep (se 2 (by rfl) ⟨191328, by rfl⟩ : syracuseStep 510209 = 382657) B382657
theorem B575761 : Blo 338752 575761 := bstep (se 2 (by rfl) ⟨215910, by rfl⟩ : syracuseStep 575761 = 431821) B431821
theorem B510227 : Blo 338752 510227 := bstep (se 1 (by rfl) ⟨382670, by rfl⟩ : syracuseStep 510227 = 765341) B765341
theorem B510257 : Blo 338752 510257 := bstep (se 2 (by rfl) ⟨191346, by rfl⟩ : syracuseStep 510257 = 382693) B382693
theorem B575795 : Blo 338752 575795 := bstep (se 1 (by rfl) ⟨431846, by rfl⟩ : syracuseStep 575795 = 863693) B863693
theorem B510275 : Blo 338752 510275 := bstep (se 1 (by rfl) ⟨382706, by rfl⟩ : syracuseStep 510275 = 765413) B765413
theorem B510305 : Blo 338752 510305 := bstep (se 2 (by rfl) ⟨191364, by rfl⟩ : syracuseStep 510305 = 382729) B382729
theorem B510323 : Blo 338752 510323 := bstep (se 1 (by rfl) ⟨382742, by rfl⟩ : syracuseStep 510323 = 765485) B765485
theorem B510353 : Blo 338752 510353 := bstep (se 2 (by rfl) ⟨191382, by rfl⟩ : syracuseStep 510353 = 382765) B382765
theorem B510371 : Blo 338752 510371 := bstep (se 1 (by rfl) ⟨382778, by rfl⟩ : syracuseStep 510371 = 765557) B765557
theorem B575923 : Blo 338752 575923 := bstep (se 1 (by rfl) ⟨431942, by rfl⟩ : syracuseStep 575923 = 863885) B863885
theorem B510401 : Blo 338752 510401 := bstep (se 2 (by rfl) ⟨191400, by rfl⟩ : syracuseStep 510401 = 382801) B382801
theorem B510419 : Blo 338752 510419 := bstep (se 1 (by rfl) ⟨382814, by rfl⟩ : syracuseStep 510419 = 765629) B765629
theorem B510449 : Blo 338752 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B510467 : Blo 338752 510467 := bstep (se 1 (by rfl) ⟨382850, by rfl⟩ : syracuseStep 510467 = 765701) B765701
theorem B510497 : Blo 338752 510497 := bstep (se 2 (by rfl) ⟨191436, by rfl⟩ : syracuseStep 510497 = 382873) B382873
theorem B510515 : Blo 338752 510515 := bstep (se 1 (by rfl) ⟨382886, by rfl⟩ : syracuseStep 510515 = 765773) B765773
theorem B576065 : Blo 338752 576065 := bstep (se 2 (by rfl) ⟨216024, by rfl⟩ : syracuseStep 576065 = 432049) B432049
theorem B510545 : Blo 338752 510545 := bstep (se 2 (by rfl) ⟨191454, by rfl⟩ : syracuseStep 510545 = 382909) B382909
theorem B510563 : Blo 338752 510563 := bstep (se 1 (by rfl) ⟨382922, by rfl⟩ : syracuseStep 510563 = 765845) B765845
theorem B510593 : Blo 338752 510593 := bstep (se 2 (by rfl) ⟨191472, by rfl⟩ : syracuseStep 510593 = 382945) B382945
theorem B510611 : Blo 338752 510611 := bstep (se 1 (by rfl) ⟨382958, by rfl⟩ : syracuseStep 510611 = 765917) B765917
theorem B510641 : Blo 338752 510641 := bstep (se 2 (by rfl) ⟨191490, by rfl⟩ : syracuseStep 510641 = 382981) B382981
theorem B1297073 : Blo 338752 1297073 := bstep (se 2 (by rfl) ⟨486402, by rfl⟩ : syracuseStep 1297073 = 972805) B972805
theorem B576193 : Blo 338752 576193 := bstep (se 2 (by rfl) ⟨216072, by rfl⟩ : syracuseStep 576193 = 432145) B432145
theorem B510659 : Blo 338752 510659 := bstep (se 1 (by rfl) ⟨382994, by rfl⟩ : syracuseStep 510659 = 765989) B765989
theorem B510689 : Blo 338752 510689 := bstep (se 2 (by rfl) ⟨191508, by rfl⟩ : syracuseStep 510689 = 383017) B383017
theorem B576227 : Blo 338752 576227 := bstep (se 1 (by rfl) ⟨432170, by rfl⟩ : syracuseStep 576227 = 864341) B864341
theorem B510707 : Blo 338752 510707 := bstep (se 1 (by rfl) ⟨383030, by rfl⟩ : syracuseStep 510707 = 766061) B766061
theorem B510737 : Blo 338752 510737 := bstep (se 2 (by rfl) ⟨191526, by rfl⟩ : syracuseStep 510737 = 383053) B383053
theorem B510755 : Blo 338752 510755 := bstep (se 1 (by rfl) ⟨383066, by rfl⟩ : syracuseStep 510755 = 766133) B766133
theorem B510785 : Blo 338752 510785 := bstep (se 2 (by rfl) ⟨191544, by rfl⟩ : syracuseStep 510785 = 383089) B383089
theorem B510803 : Blo 338752 510803 := bstep (se 1 (by rfl) ⟨383102, by rfl⟩ : syracuseStep 510803 = 766205) B766205
theorem B576355 : Blo 338752 576355 := bstep (se 1 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 576355 = 864533) B864533
theorem B510833 : Blo 338752 510833 := bstep (se 2 (by rfl) ⟨191562, by rfl⟩ : syracuseStep 510833 = 383125) B383125
theorem B510851 : Blo 338752 510851 := bstep (se 1 (by rfl) ⟨383138, by rfl⟩ : syracuseStep 510851 = 766277) B766277
theorem B510881 : Blo 338752 510881 := bstep (se 2 (by rfl) ⟨191580, by rfl⟩ : syracuseStep 510881 = 383161) B383161
theorem B543667 : Blo 338752 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B510899 : Blo 338752 510899 := bstep (se 1 (by rfl) ⟨383174, by rfl⟩ : syracuseStep 510899 = 766349) B766349
theorem B510929 : Blo 338752 510929 := bstep (se 2 (by rfl) ⟨191598, by rfl⟩ : syracuseStep 510929 = 383197) B383197
theorem B510947 : Blo 338752 510947 := bstep (se 1 (by rfl) ⟨383210, by rfl⟩ : syracuseStep 510947 = 766421) B766421
theorem B576497 : Blo 338752 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B510977 : Blo 338752 510977 := bstep (se 2 (by rfl) ⟨191616, by rfl⟩ : syracuseStep 510977 = 383233) B383233
theorem B1035281 : Blo 338752 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B510995 : Blo 338752 510995 := bstep (se 1 (by rfl) ⟨383246, by rfl⟩ : syracuseStep 510995 = 766493) B766493
theorem B511025 : Blo 338752 511025 := bstep (se 2 (by rfl) ⟨191634, by rfl⟩ : syracuseStep 511025 = 383269) B383269
theorem B511043 : Blo 338752 511043 := bstep (se 1 (by rfl) ⟨383282, by rfl⟩ : syracuseStep 511043 = 766565) B766565
theorem B511073 : Blo 338752 511073 := bstep (se 2 (by rfl) ⟨191652, by rfl⟩ : syracuseStep 511073 = 383305) B383305
theorem B576625 : Blo 338752 576625 := bstep (se 2 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 576625 = 432469) B432469
theorem B1461361 : Blo 338752 1461361 := bstep (se 2 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 1461361 = 1096021) B1096021
theorem B511091 : Blo 338752 511091 := bstep (se 1 (by rfl) ⟨383318, by rfl⟩ : syracuseStep 511091 = 766637) B766637
theorem B511121 : Blo 338752 511121 := bstep (se 2 (by rfl) ⟨191670, by rfl⟩ : syracuseStep 511121 = 383341) B383341
theorem B740497 : Blo 338752 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B576659 : Blo 338752 576659 := bstep (se 1 (by rfl) ⟨432494, by rfl⟩ : syracuseStep 576659 = 864989) B864989
theorem B511139 : Blo 338752 511139 := bstep (se 1 (by rfl) ⟨383354, by rfl⟩ : syracuseStep 511139 = 766709) B766709
theorem B543923 : Blo 338752 543923 := bstep (se 1 (by rfl) ⟨407942, by rfl⟩ : syracuseStep 543923 = 815885) B815885
theorem B511169 : Blo 338752 511169 := bstep (se 2 (by rfl) ⟨191688, by rfl⟩ : syracuseStep 511169 = 383377) B383377
theorem B511187 : Blo 338752 511187 := bstep (se 1 (by rfl) ⟨383390, by rfl⟩ : syracuseStep 511187 = 766781) B766781
theorem B4377827 : Blo 338752 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B511217 : Blo 338752 511217 := bstep (se 2 (by rfl) ⟨191706, by rfl⟩ : syracuseStep 511217 = 383413) B383413
theorem B511235 : Blo 338752 511235 := bstep (se 1 (by rfl) ⟨383426, by rfl⟩ : syracuseStep 511235 = 766853) B766853
theorem B576787 : Blo 338752 576787 := bstep (se 1 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 576787 = 865181) B865181
theorem B511265 : Blo 338752 511265 := bstep (se 2 (by rfl) ⟨191724, by rfl⟩ : syracuseStep 511265 = 383449) B383449
theorem B511283 : Blo 338752 511283 := bstep (se 1 (by rfl) ⟨383462, by rfl⟩ : syracuseStep 511283 = 766925) B766925
theorem B1297741 : Blo 338752 1297741 := bstep (se 3 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 1297741 = 486653) B486653
theorem B511313 : Blo 338752 511313 := bstep (se 2 (by rfl) ⟨191742, by rfl⟩ : syracuseStep 511313 = 383485) B383485
theorem B511331 : Blo 338752 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B544115 : Blo 338752 544115 := bstep (se 1 (by rfl) ⟨408086, by rfl⟩ : syracuseStep 544115 = 816173) B816173
theorem B511361 : Blo 338752 511361 := bstep (se 2 (by rfl) ⟨191760, by rfl⟩ : syracuseStep 511361 = 383521) B383521
theorem B511379 : Blo 338752 511379 := bstep (se 1 (by rfl) ⟨383534, by rfl⟩ : syracuseStep 511379 = 767069) B767069
theorem B576929 : Blo 338752 576929 := bstep (se 2 (by rfl) ⟨216348, by rfl⟩ : syracuseStep 576929 = 432697) B432697
theorem B511409 : Blo 338752 511409 := bstep (se 2 (by rfl) ⟨191778, by rfl⟩ : syracuseStep 511409 = 383557) B383557
theorem B511427 : Blo 338752 511427 := bstep (se 1 (by rfl) ⟨383570, by rfl⟩ : syracuseStep 511427 = 767141) B767141
theorem B511457 : Blo 338752 511457 := bstep (se 2 (by rfl) ⟨191796, by rfl⟩ : syracuseStep 511457 = 383593) B383593
theorem B511475 : Blo 338752 511475 := bstep (se 1 (by rfl) ⟨383606, by rfl⟩ : syracuseStep 511475 = 767213) B767213
theorem B3919373 : Blo 338752 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B511505 : Blo 338752 511505 := bstep (se 2 (by rfl) ⟨191814, by rfl⟩ : syracuseStep 511505 = 383629) B383629
theorem B577057 : Blo 338752 577057 := bstep (se 2 (by rfl) ⟨216396, by rfl⟩ : syracuseStep 577057 = 432793) B432793
theorem B511523 : Blo 338752 511523 := bstep (se 1 (by rfl) ⟨383642, by rfl⟩ : syracuseStep 511523 = 767285) B767285
theorem B970289 : Blo 338752 970289 := bstep (se 2 (by rfl) ⟨363858, by rfl⟩ : syracuseStep 970289 = 727717) B727717
theorem B511553 : Blo 338752 511553 := bstep (se 2 (by rfl) ⟨191832, by rfl⟩ : syracuseStep 511553 = 383665) B383665
theorem B577091 : Blo 338752 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B740945 : Blo 338752 740945 := bstep (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) B555709
theorem B511571 : Blo 338752 511571 := bstep (se 1 (by rfl) ⟨383678, by rfl⟩ : syracuseStep 511571 = 767357) B767357
theorem B1724003 : Blo 338752 1724003 := bstep (se 1 (by rfl) ⟨1293002, by rfl⟩ : syracuseStep 1724003 = 2586005) B2586005
theorem B511601 : Blo 338752 511601 := bstep (se 2 (by rfl) ⟨191850, by rfl⟩ : syracuseStep 511601 = 383701) B383701
theorem B511619 : Blo 338752 511619 := bstep (se 1 (by rfl) ⟨383714, by rfl⟩ : syracuseStep 511619 = 767429) B767429
theorem B1166989 : Blo 338752 1166989 := bstep (se 3 (by rfl) ⟨218810, by rfl⟩ : syracuseStep 1166989 = 437621) B437621
theorem B511649 : Blo 338752 511649 := bstep (se 2 (by rfl) ⟨191868, by rfl⟩ : syracuseStep 511649 = 383737) B383737
theorem B511667 : Blo 338752 511667 := bstep (se 1 (by rfl) ⟨383750, by rfl⟩ : syracuseStep 511667 = 767501) B767501
theorem B577219 : Blo 338752 577219 := bstep (se 1 (by rfl) ⟨432914, by rfl⟩ : syracuseStep 577219 = 865829) B865829
theorem B511697 : Blo 338752 511697 := bstep (se 2 (by rfl) ⟨191886, by rfl⟩ : syracuseStep 511697 = 383773) B383773
theorem B511715 : Blo 338752 511715 := bstep (se 1 (by rfl) ⟨383786, by rfl⟩ : syracuseStep 511715 = 767573) B767573
theorem B970481 : Blo 338752 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B511745 : Blo 338752 511745 := bstep (se 2 (by rfl) ⟨191904, by rfl⟩ : syracuseStep 511745 = 383809) B383809
theorem B511763 : Blo 338752 511763 := bstep (se 1 (by rfl) ⟨383822, by rfl⟩ : syracuseStep 511763 = 767645) B767645
theorem B511793 : Blo 338752 511793 := bstep (se 2 (by rfl) ⟨191922, by rfl⟩ : syracuseStep 511793 = 383845) B383845
theorem B511811 : Blo 338752 511811 := bstep (se 1 (by rfl) ⟨383858, by rfl⟩ : syracuseStep 511811 = 767717) B767717
theorem B577361 : Blo 338752 577361 := bstep (se 2 (by rfl) ⟨216510, by rfl⟩ : syracuseStep 577361 = 433021) B433021
theorem B511841 : Blo 338752 511841 := bstep (se 2 (by rfl) ⟨191940, by rfl⟩ : syracuseStep 511841 = 383881) B383881
theorem B511859 : Blo 338752 511859 := bstep (se 1 (by rfl) ⟨383894, by rfl⟩ : syracuseStep 511859 = 767789) B767789
theorem B511889 : Blo 338752 511889 := bstep (se 2 (by rfl) ⟨191958, by rfl⟩ : syracuseStep 511889 = 383917) B383917
theorem B511907 : Blo 338752 511907 := bstep (se 1 (by rfl) ⟨383930, by rfl⟩ : syracuseStep 511907 = 767861) B767861
theorem B511937 : Blo 338752 511937 := bstep (se 2 (by rfl) ⟨191976, by rfl⟩ : syracuseStep 511937 = 383953) B383953
theorem B577489 : Blo 338752 577489 := bstep (se 2 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 577489 = 433117) B433117
theorem B511955 : Blo 338752 511955 := bstep (se 1 (by rfl) ⟨383966, by rfl⟩ : syracuseStep 511955 = 767933) B767933
theorem B511985 : Blo 338752 511985 := bstep (se 2 (by rfl) ⟨191994, by rfl⟩ : syracuseStep 511985 = 383989) B383989
theorem B577523 : Blo 338752 577523 := bstep (se 1 (by rfl) ⟨433142, by rfl⟩ : syracuseStep 577523 = 866285) B866285
theorem B512003 : Blo 338752 512003 := bstep (se 1 (by rfl) ⟨384002, by rfl⟩ : syracuseStep 512003 = 768005) B768005
theorem B512033 : Blo 338752 512033 := bstep (se 2 (by rfl) ⟨192012, by rfl⟩ : syracuseStep 512033 = 384025) B384025
theorem B512051 : Blo 338752 512051 := bstep (se 1 (by rfl) ⟨384038, by rfl⟩ : syracuseStep 512051 = 768077) B768077
theorem B643153 : Blo 338752 643153 := bstep (se 2 (by rfl) ⟨241182, by rfl⟩ : syracuseStep 643153 = 482365) B482365
theorem B512081 : Blo 338752 512081 := bstep (se 2 (by rfl) ⟨192030, by rfl⟩ : syracuseStep 512081 = 384061) B384061
theorem B512099 : Blo 338752 512099 := bstep (se 1 (by rfl) ⟨384074, by rfl⟩ : syracuseStep 512099 = 768149) B768149
theorem B1298531 : Blo 338752 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B577651 : Blo 338752 577651 := bstep (se 1 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 577651 = 866477) B866477
theorem B544897 : Blo 338752 544897 := bstep (se 2 (by rfl) ⟨204336, by rfl⟩ : syracuseStep 544897 = 408673) B408673
theorem B512129 : Blo 338752 512129 := bstep (se 2 (by rfl) ⟨192048, by rfl⟩ : syracuseStep 512129 = 384097) B384097
theorem B512147 : Blo 338752 512147 := bstep (se 1 (by rfl) ⟨384110, by rfl⟩ : syracuseStep 512147 = 768221) B768221
theorem B512177 : Blo 338752 512177 := bstep (se 2 (by rfl) ⟨192066, by rfl⟩ : syracuseStep 512177 = 384133) B384133
theorem B512195 : Blo 338752 512195 := bstep (se 1 (by rfl) ⟨384146, by rfl⟩ : syracuseStep 512195 = 768293) B768293
theorem B512225 : Blo 338752 512225 := bstep (se 2 (by rfl) ⟨192084, by rfl⟩ : syracuseStep 512225 = 384169) B384169
theorem B512243 : Blo 338752 512243 := bstep (se 1 (by rfl) ⟨384182, by rfl⟩ : syracuseStep 512243 = 768365) B768365
theorem B577793 : Blo 338752 577793 := bstep (se 2 (by rfl) ⟨216672, by rfl⟩ : syracuseStep 577793 = 433345) B433345
theorem B512273 : Blo 338752 512273 := bstep (se 2 (by rfl) ⟨192102, by rfl⟩ : syracuseStep 512273 = 384205) B384205
theorem B512291 : Blo 338752 512291 := bstep (se 1 (by rfl) ⟨384218, by rfl⟩ : syracuseStep 512291 = 768437) B768437
theorem B381235 : Blo 338752 381235 := bstep (se 1 (by rfl) ⟨285926, by rfl⟩ : syracuseStep 381235 = 571853) B571853
theorem B512321 : Blo 338752 512321 := bstep (se 2 (by rfl) ⟨192120, by rfl⟩ : syracuseStep 512321 = 384241) B384241
theorem B512339 : Blo 338752 512339 := bstep (se 1 (by rfl) ⟨384254, by rfl⟩ : syracuseStep 512339 = 768509) B768509
theorem B610673 : Blo 338752 610673 := bstep (se 2 (by rfl) ⟨229002, by rfl⟩ : syracuseStep 610673 = 458005) B458005
theorem B512369 : Blo 338752 512369 := bstep (se 2 (by rfl) ⟨192138, by rfl⟩ : syracuseStep 512369 = 384277) B384277
theorem B577921 : Blo 338752 577921 := bstep (se 2 (by rfl) ⟨216720, by rfl⟩ : syracuseStep 577921 = 433441) B433441
theorem B512387 : Blo 338752 512387 := bstep (se 1 (by rfl) ⟨384290, by rfl⟩ : syracuseStep 512387 = 768581) B768581
theorem B1724813 : Blo 338752 1724813 := bstep (se 3 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 1724813 = 646805) B646805
theorem B512417 : Blo 338752 512417 := bstep (se 2 (by rfl) ⟨192156, by rfl⟩ : syracuseStep 512417 = 384313) B384313
theorem B577955 : Blo 338752 577955 := bstep (se 1 (by rfl) ⟨433466, by rfl⟩ : syracuseStep 577955 = 866933) B866933
theorem B512435 : Blo 338752 512435 := bstep (se 1 (by rfl) ⟨384326, by rfl⟩ : syracuseStep 512435 = 768653) B768653
theorem B381379 : Blo 338752 381379 := bstep (se 1 (by rfl) ⟨286034, by rfl⟩ : syracuseStep 381379 = 572069) B572069
theorem B1036739 : Blo 338752 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B512465 : Blo 338752 512465 := bstep (se 2 (by rfl) ⟨192174, by rfl⟩ : syracuseStep 512465 = 384349) B384349
theorem B643555 : Blo 338752 643555 := bstep (se 1 (by rfl) ⟨482666, by rfl⟩ : syracuseStep 643555 = 965333) B965333
theorem B512483 : Blo 338752 512483 := bstep (se 1 (by rfl) ⟨384362, by rfl⟩ : syracuseStep 512483 = 768725) B768725
theorem B512513 : Blo 338752 512513 := bstep (se 2 (by rfl) ⟨192192, by rfl⟩ : syracuseStep 512513 = 384385) B384385
theorem B643601 : Blo 338752 643601 := bstep (se 2 (by rfl) ⟨241350, by rfl⟩ : syracuseStep 643601 = 482701) B482701
theorem B512531 : Blo 338752 512531 := bstep (se 1 (by rfl) ⟨384398, by rfl⟩ : syracuseStep 512531 = 768797) B768797
theorem B578083 : Blo 338752 578083 := bstep (se 1 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 578083 = 867125) B867125
theorem B512561 : Blo 338752 512561 := bstep (se 2 (by rfl) ⟨192210, by rfl⟩ : syracuseStep 512561 = 384421) B384421
theorem B512579 : Blo 338752 512579 := bstep (se 1 (by rfl) ⟨384434, by rfl⟩ : syracuseStep 512579 = 768869) B768869
theorem B381523 : Blo 338752 381523 := bstep (se 1 (by rfl) ⟨286142, by rfl⟩ : syracuseStep 381523 = 572285) B572285
theorem B512609 : Blo 338752 512609 := bstep (se 2 (by rfl) ⟨192228, by rfl⟩ : syracuseStep 512609 = 384457) B384457
theorem B512627 : Blo 338752 512627 := bstep (se 1 (by rfl) ⟨384470, by rfl⟩ : syracuseStep 512627 = 768941) B768941
theorem B5526157 : Blo 338752 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B512657 : Blo 338752 512657 := bstep (se 2 (by rfl) ⟨192246, by rfl⟩ : syracuseStep 512657 = 384493) B384493
theorem B512675 : Blo 338752 512675 := bstep (se 1 (by rfl) ⟨384506, by rfl⟩ : syracuseStep 512675 = 769013) B769013
theorem B1233571 : Blo 338752 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B578225 : Blo 338752 578225 := bstep (se 2 (by rfl) ⟨216834, by rfl⟩ : syracuseStep 578225 = 433669) B433669
theorem B512705 : Blo 338752 512705 := bstep (se 2 (by rfl) ⟨192264, by rfl⟩ : syracuseStep 512705 = 384529) B384529
theorem B971473 : Blo 338752 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B512723 : Blo 338752 512723 := bstep (se 1 (by rfl) ⟨384542, by rfl⟩ : syracuseStep 512723 = 769085) B769085
theorem B381667 : Blo 338752 381667 := bstep (se 1 (by rfl) ⟨286250, by rfl⟩ : syracuseStep 381667 = 572501) B572501
theorem B512753 : Blo 338752 512753 := bstep (se 2 (by rfl) ⟨192282, by rfl⟩ : syracuseStep 512753 = 384565) B384565
theorem B1299185 : Blo 338752 1299185 := bstep (se 2 (by rfl) ⟨487194, by rfl⟩ : syracuseStep 1299185 = 974389) B974389
theorem B512771 : Blo 338752 512771 := bstep (se 1 (by rfl) ⟨384578, by rfl⟩ : syracuseStep 512771 = 769157) B769157
theorem B1168141 : Blo 338752 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B512801 : Blo 338752 512801 := bstep (se 2 (by rfl) ⟨192300, by rfl⟩ : syracuseStep 512801 = 384601) B384601
theorem B643889 : Blo 338752 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B578353 : Blo 338752 578353 := bstep (se 2 (by rfl) ⟨216882, by rfl⟩ : syracuseStep 578353 = 433765) B433765
theorem B512819 : Blo 338752 512819 := bstep (se 1 (by rfl) ⟨384614, by rfl⟩ : syracuseStep 512819 = 769229) B769229
theorem B1168195 : Blo 338752 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B512849 : Blo 338752 512849 := bstep (se 2 (by rfl) ⟨192318, by rfl⟩ : syracuseStep 512849 = 384637) B384637
theorem B578387 : Blo 338752 578387 := bstep (se 1 (by rfl) ⟨433790, by rfl⟩ : syracuseStep 578387 = 867581) B867581
theorem B512867 : Blo 338752 512867 := bstep (se 1 (by rfl) ⟨384650, by rfl⟩ : syracuseStep 512867 = 769301) B769301
theorem B381811 : Blo 338752 381811 := bstep (se 1 (by rfl) ⟨286358, by rfl⟩ : syracuseStep 381811 = 572717) B572717
theorem B512897 : Blo 338752 512897 := bstep (se 2 (by rfl) ⟨192336, by rfl⟩ : syracuseStep 512897 = 384673) B384673
theorem B512915 : Blo 338752 512915 := bstep (se 1 (by rfl) ⟨384686, by rfl⟩ : syracuseStep 512915 = 769373) B769373
theorem B512945 : Blo 338752 512945 := bstep (se 2 (by rfl) ⟨192354, by rfl⟩ : syracuseStep 512945 = 384709) B384709
theorem B512963 : Blo 338752 512963 := bstep (se 1 (by rfl) ⟨384722, by rfl⟩ : syracuseStep 512963 = 769445) B769445
theorem B512993 : Blo 338752 512993 := bstep (se 2 (by rfl) ⟨192372, by rfl⟩ : syracuseStep 512993 = 384745) B384745
theorem B971747 : Blo 338752 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B513011 : Blo 338752 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B381955 : Blo 338752 381955 := bstep (se 1 (by rfl) ⟨286466, by rfl⟩ : syracuseStep 381955 = 572933) B572933
theorem B1463309 : Blo 338752 1463309 := bstep (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) B548741
theorem B513041 : Blo 338752 513041 := bstep (se 2 (by rfl) ⟨192390, by rfl⟩ : syracuseStep 513041 = 384781) B384781
theorem B513059 : Blo 338752 513059 := bstep (se 1 (by rfl) ⟨384794, by rfl⟩ : syracuseStep 513059 = 769589) B769589
theorem B513089 : Blo 338752 513089 := bstep (se 2 (by rfl) ⟨192408, by rfl⟩ : syracuseStep 513089 = 384817) B384817
theorem B513107 : Blo 338752 513107 := bstep (se 1 (by rfl) ⟨384830, by rfl⟩ : syracuseStep 513107 = 769661) B769661
theorem B513137 : Blo 338752 513137 := bstep (se 2 (by rfl) ⟨192426, by rfl⟩ : syracuseStep 513137 = 384853) B384853
theorem B513155 : Blo 338752 513155 := bstep (se 1 (by rfl) ⟨384866, by rfl⟩ : syracuseStep 513155 = 769733) B769733
theorem B382099 : Blo 338752 382099 := bstep (se 1 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 382099 = 573149) B573149
theorem B513185 : Blo 338752 513185 := bstep (se 2 (by rfl) ⟨192444, by rfl⟩ : syracuseStep 513185 = 384889) B384889
theorem B971939 : Blo 338752 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B513203 : Blo 338752 513203 := bstep (se 1 (by rfl) ⟨384902, by rfl⟩ : syracuseStep 513203 = 769805) B769805
theorem B513233 : Blo 338752 513233 := bstep (se 2 (by rfl) ⟨192462, by rfl⟩ : syracuseStep 513233 = 384925) B384925
theorem B513251 : Blo 338752 513251 := bstep (se 1 (by rfl) ⟨384938, by rfl⟩ : syracuseStep 513251 = 769877) B769877
theorem B513281 : Blo 338752 513281 := bstep (se 2 (by rfl) ⟨192480, by rfl⟩ : syracuseStep 513281 = 384961) B384961
theorem B513299 : Blo 338752 513299 := bstep (se 1 (by rfl) ⟨384974, by rfl⟩ : syracuseStep 513299 = 769949) B769949
theorem B382243 : Blo 338752 382243 := bstep (se 1 (by rfl) ⟨286682, by rfl⟩ : syracuseStep 382243 = 573365) B573365
theorem B513329 : Blo 338752 513329 := bstep (se 2 (by rfl) ⟨192498, by rfl⟩ : syracuseStep 513329 = 384997) B384997
theorem B513347 : Blo 338752 513347 := bstep (se 1 (by rfl) ⟨385010, by rfl⟩ : syracuseStep 513347 = 770021) B770021
theorem B513377 : Blo 338752 513377 := bstep (se 2 (by rfl) ⟨192516, by rfl⟩ : syracuseStep 513377 = 385033) B385033
theorem B513395 : Blo 338752 513395 := bstep (se 1 (by rfl) ⟨385046, by rfl⟩ : syracuseStep 513395 = 770093) B770093
theorem B513425 : Blo 338752 513425 := bstep (se 2 (by rfl) ⟨192534, by rfl⟩ : syracuseStep 513425 = 385069) B385069
theorem B513443 : Blo 338752 513443 := bstep (se 1 (by rfl) ⟨385082, by rfl⟩ : syracuseStep 513443 = 770165) B770165
theorem B382387 : Blo 338752 382387 := bstep (se 1 (by rfl) ⟨286790, by rfl⟩ : syracuseStep 382387 = 573581) B573581
theorem B513473 : Blo 338752 513473 := bstep (se 2 (by rfl) ⟨192552, by rfl⟩ : syracuseStep 513473 = 385105) B385105
theorem B1168849 : Blo 338752 1168849 := bstep (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) B876637
theorem B513491 : Blo 338752 513491 := bstep (se 1 (by rfl) ⟨385118, by rfl⟩ : syracuseStep 513491 = 770237) B770237
theorem B513521 : Blo 338752 513521 := bstep (se 2 (by rfl) ⟨192570, by rfl⟩ : syracuseStep 513521 = 385141) B385141
theorem B644611 : Blo 338752 644611 := bstep (se 1 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 644611 = 966917) B966917
theorem B513539 : Blo 338752 513539 := bstep (se 1 (by rfl) ⟨385154, by rfl⟩ : syracuseStep 513539 = 770309) B770309
theorem B513569 : Blo 338752 513569 := bstep (se 2 (by rfl) ⟨192588, by rfl⟩ : syracuseStep 513569 = 385177) B385177
theorem B513587 : Blo 338752 513587 := bstep (se 1 (by rfl) ⟨385190, by rfl⟩ : syracuseStep 513587 = 770381) B770381
theorem B382531 : Blo 338752 382531 := bstep (se 1 (by rfl) ⟨286898, by rfl⟩ : syracuseStep 382531 = 573797) B573797
theorem B513617 : Blo 338752 513617 := bstep (se 2 (by rfl) ⟨192606, by rfl⟩ : syracuseStep 513617 = 385213) B385213
theorem B513635 : Blo 338752 513635 := bstep (se 1 (by rfl) ⟨385226, by rfl⟩ : syracuseStep 513635 = 770453) B770453
theorem B513665 : Blo 338752 513665 := bstep (se 2 (by rfl) ⟨192624, by rfl⟩ : syracuseStep 513665 = 385249) B385249
theorem B513683 : Blo 338752 513683 := bstep (se 1 (by rfl) ⟨385262, by rfl⟩ : syracuseStep 513683 = 770525) B770525
theorem B513713 : Blo 338752 513713 := bstep (se 2 (by rfl) ⟨192642, by rfl⟩ : syracuseStep 513713 = 385285) B385285
theorem B513731 : Blo 338752 513731 := bstep (se 1 (by rfl) ⟨385298, by rfl⟩ : syracuseStep 513731 = 770597) B770597
theorem B382675 : Blo 338752 382675 := bstep (se 1 (by rfl) ⟨287006, by rfl⟩ : syracuseStep 382675 = 574013) B574013
theorem B513761 : Blo 338752 513761 := bstep (se 2 (by rfl) ⟨192660, by rfl⟩ : syracuseStep 513761 = 385321) B385321
theorem B513779 : Blo 338752 513779 := bstep (se 1 (by rfl) ⟨385334, by rfl⟩ : syracuseStep 513779 = 770669) B770669
theorem B546563 : Blo 338752 546563 := bstep (se 1 (by rfl) ⟨409922, by rfl⟩ : syracuseStep 546563 = 819845) B819845
theorem B513809 : Blo 338752 513809 := bstep (se 2 (by rfl) ⟨192678, by rfl⟩ : syracuseStep 513809 = 385357) B385357
theorem B2184995 : Blo 338752 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B513827 : Blo 338752 513827 := bstep (se 1 (by rfl) ⟨385370, by rfl⟩ : syracuseStep 513827 = 770741) B770741
theorem B513857 : Blo 338752 513857 := bstep (se 2 (by rfl) ⟨192696, by rfl⟩ : syracuseStep 513857 = 385393) B385393
theorem B513875 : Blo 338752 513875 := bstep (se 1 (by rfl) ⟨385406, by rfl⟩ : syracuseStep 513875 = 770813) B770813
theorem B382819 : Blo 338752 382819 := bstep (se 1 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 382819 = 574229) B574229
theorem B513905 : Blo 338752 513905 := bstep (se 2 (by rfl) ⟨192714, by rfl⟩ : syracuseStep 513905 = 385429) B385429
theorem B546691 : Blo 338752 546691 := bstep (se 1 (by rfl) ⟨410018, by rfl⟩ : syracuseStep 546691 = 820037) B820037
theorem B513923 : Blo 338752 513923 := bstep (se 1 (by rfl) ⟨385442, by rfl⟩ : syracuseStep 513923 = 770885) B770885
theorem B513953 : Blo 338752 513953 := bstep (se 2 (by rfl) ⟨192732, by rfl⟩ : syracuseStep 513953 = 385465) B385465
theorem B513971 : Blo 338752 513971 := bstep (se 1 (by rfl) ⟨385478, by rfl⟩ : syracuseStep 513971 = 770957) B770957
theorem B645059 : Blo 338752 645059 := bstep (se 1 (by rfl) ⟨483794, by rfl⟩ : syracuseStep 645059 = 967589) B967589
theorem B972749 : Blo 338752 972749 := bstep (se 3 (by rfl) ⟨182390, by rfl⟩ : syracuseStep 972749 = 364781) B364781
theorem B514001 : Blo 338752 514001 := bstep (se 2 (by rfl) ⟨192750, by rfl⟩ : syracuseStep 514001 = 385501) B385501
theorem B514019 : Blo 338752 514019 := bstep (se 1 (by rfl) ⟨385514, by rfl⟩ : syracuseStep 514019 = 771029) B771029
theorem B382963 : Blo 338752 382963 := bstep (se 1 (by rfl) ⟨287222, by rfl⟩ : syracuseStep 382963 = 574445) B574445
theorem B514049 : Blo 338752 514049 := bstep (se 2 (by rfl) ⟨192768, by rfl⟩ : syracuseStep 514049 = 385537) B385537
theorem B514067 : Blo 338752 514067 := bstep (se 1 (by rfl) ⟨385550, by rfl⟩ : syracuseStep 514067 = 771101) B771101
theorem B514097 : Blo 338752 514097 := bstep (se 2 (by rfl) ⟨192786, by rfl⟩ : syracuseStep 514097 = 385573) B385573
theorem B514115 : Blo 338752 514115 := bstep (se 1 (by rfl) ⟨385586, by rfl⟩ : syracuseStep 514115 = 771173) B771173
theorem B383107 : Blo 338752 383107 := bstep (se 1 (by rfl) ⟨287330, by rfl⟩ : syracuseStep 383107 = 574661) B574661
theorem B972931 : Blo 338752 972931 := bstep (se 1 (by rfl) ⟨729698, by rfl⟩ : syracuseStep 972931 = 1459397) B1459397
theorem B1300643 : Blo 338752 1300643 := bstep (se 1 (by rfl) ⟨975482, by rfl⟩ : syracuseStep 1300643 = 1950965) B1950965
theorem B1300657 : Blo 338752 1300657 := bstep (se 2 (by rfl) ⟨487746, by rfl⟩ : syracuseStep 1300657 = 975493) B975493
theorem B645347 : Blo 338752 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B547075 : Blo 338752 547075 := bstep (se 1 (by rfl) ⟨410306, by rfl⟩ : syracuseStep 547075 = 820613) B820613
theorem B383251 : Blo 338752 383251 := bstep (se 1 (by rfl) ⟨287438, by rfl⟩ : syracuseStep 383251 = 574877) B574877
theorem B612721 : Blo 338752 612721 := bstep (se 2 (by rfl) ⟨229770, by rfl⟩ : syracuseStep 612721 = 459541) B459541
theorem B383395 : Blo 338752 383395 := bstep (se 1 (by rfl) ⟨287546, by rfl⟩ : syracuseStep 383395 = 575093) B575093
theorem B3103217 : Blo 338752 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B547331 : Blo 338752 547331 := bstep (se 1 (by rfl) ⟨410498, by rfl⟩ : syracuseStep 547331 = 820997) B820997
theorem B383539 : Blo 338752 383539 := bstep (se 1 (by rfl) ⟨287654, by rfl⟩ : syracuseStep 383539 = 575309) B575309
theorem B973421 : Blo 338752 973421 := bstep (se 3 (by rfl) ⟨182516, by rfl⟩ : syracuseStep 973421 = 365033) B365033
theorem B2906765 : Blo 338752 2906765 := bstep (se 3 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 2906765 = 1090037) B1090037
theorem B580259 : Blo 338752 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B383683 : Blo 338752 383683 := bstep (se 1 (by rfl) ⟨287762, by rfl⟩ : syracuseStep 383683 = 575525) B575525
theorem B383827 : Blo 338752 383827 := bstep (se 1 (by rfl) ⟨287870, by rfl⟩ : syracuseStep 383827 = 575741) B575741
theorem B547793 : Blo 338752 547793 := bstep (se 2 (by rfl) ⟨205422, by rfl⟩ : syracuseStep 547793 = 410845) B410845
theorem B383971 : Blo 338752 383971 := bstep (se 1 (by rfl) ⟨287978, by rfl⟩ : syracuseStep 383971 = 575957) B575957
theorem B547889 : Blo 338752 547889 := bstep (se 2 (by rfl) ⟨205458, by rfl⟩ : syracuseStep 547889 = 410917) B410917
theorem B547921 : Blo 338752 547921 := bstep (se 2 (by rfl) ⟨205470, by rfl⟩ : syracuseStep 547921 = 410941) B410941
theorem B384115 : Blo 338752 384115 := bstep (se 1 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 384115 = 576173) B576173
theorem B646289 : Blo 338752 646289 := bstep (se 2 (by rfl) ⟨242358, by rfl⟩ : syracuseStep 646289 = 484717) B484717
theorem B1727729 : Blo 338752 1727729 := bstep (se 2 (by rfl) ⟨647898, by rfl⟩ : syracuseStep 1727729 = 1295797) B1295797
theorem B384259 : Blo 338752 384259 := bstep (se 1 (by rfl) ⟨288194, by rfl⟩ : syracuseStep 384259 = 576389) B576389
theorem B482593 : Blo 338752 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B482689 : Blo 338752 482689 := bstep (se 2 (by rfl) ⟨181008, by rfl⟩ : syracuseStep 482689 = 362017) B362017
theorem B384403 : Blo 338752 384403 := bstep (se 1 (by rfl) ⟨288302, by rfl⟩ : syracuseStep 384403 = 576605) B576605
theorem B384547 : Blo 338752 384547 := bstep (se 1 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 384547 = 576821) B576821
theorem B14114357 : Blo 338752 14114357 := bstep (se 5 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 14114357 = 1323221) B1323221
theorem B384691 : Blo 338752 384691 := bstep (se 1 (by rfl) ⟨288518, by rfl⟩ : syracuseStep 384691 = 577037) B577037
theorem B351923 : Blo 338752 351923 := bstep (se 1 (by rfl) ⟨263942, by rfl⟩ : syracuseStep 351923 = 527885) B527885
theorem B974605 : Blo 338752 974605 := bstep (se 3 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 974605 = 365477) B365477
theorem B384835 : Blo 338752 384835 := bstep (se 1 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 384835 = 577253) B577253
theorem B483185 : Blo 338752 483185 := bstep (se 2 (by rfl) ⟨181194, by rfl⟩ : syracuseStep 483185 = 362389) B362389
theorem B2187121 : Blo 338752 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B2318213 : Blo 338752 2318213 := bstep (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) B434665
theorem B384979 : Blo 338752 384979 := bstep (se 1 (by rfl) ⟨288734, by rfl⟩ : syracuseStep 384979 = 577469) B577469
theorem B647185 : Blo 338752 647185 := bstep (se 2 (by rfl) ⟨242694, by rfl⟩ : syracuseStep 647185 = 485389) B485389
theorem B581683 : Blo 338752 581683 := bstep (se 1 (by rfl) ⟨436262, by rfl⟩ : syracuseStep 581683 = 872525) B872525
theorem B1630307 : Blo 338752 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B385123 : Blo 338752 385123 := bstep (se 1 (by rfl) ⟨288842, by rfl⟩ : syracuseStep 385123 = 577685) B577685
theorem B1106065 : Blo 338752 1106065 := bstep (se 2 (by rfl) ⟨414774, by rfl⟩ : syracuseStep 1106065 = 829549) B829549
theorem B647345 : Blo 338752 647345 := bstep (se 2 (by rfl) ⟨242754, by rfl⟩ : syracuseStep 647345 = 485509) B485509
theorem B385267 : Blo 338752 385267 := bstep (se 1 (by rfl) ⟨288950, by rfl⟩ : syracuseStep 385267 = 577901) B577901
theorem B516449 : Blo 338752 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B385411 : Blo 338752 385411 := bstep (se 1 (by rfl) ⟨289058, by rfl⟩ : syracuseStep 385411 = 578117) B578117
theorem B385555 : Blo 338752 385555 := bstep (se 1 (by rfl) ⟨289166, by rfl⟩ : syracuseStep 385555 = 578333) B578333
theorem B647747 : Blo 338752 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B1729187 : Blo 338752 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B484051 : Blo 338752 484051 := bstep (se 1 (by rfl) ⟨363038, by rfl⟩ : syracuseStep 484051 = 726077) B726077
theorem B778979 : Blo 338752 778979 := bstep (se 1 (by rfl) ⟨584234, by rfl⟩ : syracuseStep 778979 = 1168469) B1168469
theorem B975665 : Blo 338752 975665 := bstep (se 2 (by rfl) ⟨365874, by rfl⟩ : syracuseStep 975665 = 731749) B731749
theorem B484147 : Blo 338752 484147 := bstep (se 1 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 484147 = 726221) B726221
theorem B1631153 : Blo 338752 1631153 := bstep (se 2 (by rfl) ⟨611682, by rfl⟩ : syracuseStep 1631153 = 1223365) B1223365
theorem B1172465 : Blo 338752 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B3663089 : Blo 338752 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B484643 : Blo 338752 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B648643 : Blo 338752 648643 := bstep (se 1 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 648643 = 972965) B972965
theorem B1729997 : Blo 338752 1729997 := bstep (se 3 (by rfl) ⟨324374, by rfl⟩ : syracuseStep 1729997 = 648749) B648749
theorem B1041923 : Blo 338752 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B648803 : Blo 338752 648803 := bstep (se 1 (by rfl) ⟨486602, by rfl⟩ : syracuseStep 648803 = 973205) B973205
theorem B2320163 : Blo 338752 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B485281 : Blo 338752 485281 := bstep (se 2 (by rfl) ⟨181980, by rfl⟩ : syracuseStep 485281 = 363961) B363961
theorem B485617 : Blo 338752 485617 := bstep (se 2 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 485617 = 364213) B364213
theorem B518467 : Blo 338752 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B2320817 : Blo 338752 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B1305229 : Blo 338752 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B649873 : Blo 338752 649873 := bstep (se 2 (by rfl) ⟨243702, by rfl⟩ : syracuseStep 649873 = 487405) B487405
theorem B5073635 : Blo 338752 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B387875 : Blo 338752 387875 := bstep (se 1 (by rfl) ⟨290906, by rfl⟩ : syracuseStep 387875 = 581813) B581813
theorem B551729 : Blo 338752 551729 := bstep (se 2 (by rfl) ⟨206898, by rfl⟩ : syracuseStep 551729 = 413797) B413797
theorem B486209 : Blo 338752 486209 := bstep (se 2 (by rfl) ⟨182328, by rfl⟩ : syracuseStep 486209 = 364657) B364657
theorem B1633229 : Blo 338752 1633229 := bstep (se 3 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 1633229 = 612461) B612461
theorem B552113 : Blo 338752 552113 := bstep (se 2 (by rfl) ⟨207042, by rfl⟩ : syracuseStep 552113 = 414085) B414085
theorem B1961165 : Blo 338752 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B2223409 : Blo 338752 2223409 := bstep (se 2 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 2223409 = 1667557) B1667557
theorem B486739 : Blo 338752 486739 := bstep (se 1 (by rfl) ⟨365054, by rfl⟩ : syracuseStep 486739 = 730109) B730109
theorem B1961329 : Blo 338752 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B519635 : Blo 338752 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B585185 : Blo 338752 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B4910705 : Blo 338752 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B487075 : Blo 338752 487075 := bstep (se 1 (by rfl) ⟨365306, by rfl⟩ : syracuseStep 487075 = 730613) B730613
theorem B2584547 : Blo 338752 2584547 := bstep (se 1 (by rfl) ⟨1938410, by rfl⟩ : syracuseStep 2584547 = 3876821) B3876821
theorem B520195 : Blo 338752 520195 := bstep (se 1 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 520195 = 780293) B780293
theorem B552977 : Blo 338752 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B487633 : Blo 338752 487633 := bstep (se 2 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 487633 = 365725) B365725
theorem B487667 : Blo 338752 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B1732913 : Blo 338752 1732913 := bstep (se 2 (by rfl) ⟨649842, by rfl⟩ : syracuseStep 1732913 = 1299685) B1299685
theorem B520609 : Blo 338752 520609 := bstep (se 2 (by rfl) ⟨195228, by rfl⟩ : syracuseStep 520609 = 390457) B390457
theorem B1143341 : Blo 338752 1143341 := bstep (se 3 (by rfl) ⟨214376, by rfl⟩ : syracuseStep 1143341 = 428753) B428753
theorem B815683 : Blo 338752 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B1143395 : Blo 338752 1143395 := bstep (se 1 (by rfl) ⟨857546, by rfl⟩ : syracuseStep 1143395 = 1715093) B1715093
theorem B521059 : Blo 338752 521059 := bstep (se 1 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 521059 = 781589) B781589
theorem B1143665 : Blo 338752 1143665 := bstep (se 2 (by rfl) ⟨428874, by rfl⟩ : syracuseStep 1143665 = 857749) B857749
theorem B553969 : Blo 338752 553969 := bstep (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) B415477
theorem B2192453 : Blo 338752 2192453 := bstep (se 4 (by rfl) ⟨205542, by rfl⟩ : syracuseStep 2192453 = 411085) B411085
theorem B1144205 : Blo 338752 1144205 := bstep (se 3 (by rfl) ⟨214538, by rfl⟩ : syracuseStep 1144205 = 429077) B429077
theorem B1144259 : Blo 338752 1144259 := bstep (se 1 (by rfl) ⟨858194, by rfl⟩ : syracuseStep 1144259 = 1716389) B1716389
theorem B1144529 : Blo 338752 1144529 := bstep (se 2 (by rfl) ⟨429198, by rfl⟩ : syracuseStep 1144529 = 858397) B858397
theorem B1734371 : Blo 338752 1734371 := bstep (se 1 (by rfl) ⟨1300778, by rfl⟩ : syracuseStep 1734371 = 2601557) B2601557
theorem B816913 : Blo 338752 816913 := bstep (se 2 (by rfl) ⟨306342, by rfl⟩ : syracuseStep 816913 = 612685) B612685
theorem B5830541 : Blo 338752 5830541 := bstep (se 3 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 5830541 = 2186453) B2186453
theorem B1832867 : Blo 338752 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B2750435 : Blo 338752 2750435 := bstep (se 1 (by rfl) ⟨2062826, by rfl⟩ : syracuseStep 2750435 = 4125653) B4125653
theorem B2062385 : Blo 338752 2062385 := bstep (se 2 (by rfl) ⟨773394, by rfl⟩ : syracuseStep 2062385 = 1546789) B1546789
theorem B1964101 : Blo 338752 1964101 := bstep (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) B368269
theorem B1145069 : Blo 338752 1145069 := bstep (se 3 (by rfl) ⟨214700, by rfl⟩ : syracuseStep 1145069 = 429401) B429401
theorem B1145123 : Blo 338752 1145123 := bstep (se 1 (by rfl) ⟨858842, by rfl⟩ : syracuseStep 1145123 = 1717685) B1717685
theorem B1571185 : Blo 338752 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B4127203 : Blo 338752 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B1735181 : Blo 338752 1735181 := bstep (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) B650693
theorem B1145393 : Blo 338752 1145393 := bstep (se 2 (by rfl) ⟨429522, by rfl⟩ : syracuseStep 1145393 = 859045) B859045
theorem B3865157 : Blo 338752 3865157 := bstep (se 4 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 3865157 = 724717) B724717
theorem B9435761 : Blo 338752 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B1309603 : Blo 338752 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B3275761 : Blo 338752 3275761 := bstep (se 2 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 3275761 = 2456821) B2456821
theorem B1145933 : Blo 338752 1145933 := bstep (se 3 (by rfl) ⟨214862, by rfl⟩ : syracuseStep 1145933 = 429725) B429725
theorem B1145987 : Blo 338752 1145987 := bstep (se 1 (by rfl) ⟨859490, by rfl⟩ : syracuseStep 1145987 = 1718981) B1718981
theorem B4423025 : Blo 338752 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B1146257 : Blo 338752 1146257 := bstep (se 2 (by rfl) ⟨429846, by rfl⟩ : syracuseStep 1146257 = 859693) B859693
theorem B491123 : Blo 338752 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B1834787 : Blo 338752 1834787 := bstep (se 1 (by rfl) ⟨1376090, by rfl⟩ : syracuseStep 1834787 = 2752181) B2752181
theorem B491377 : Blo 338752 491377 := bstep (se 2 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 491377 = 368533) B368533
theorem B1146797 : Blo 338752 1146797 := bstep (se 3 (by rfl) ⟨215024, by rfl⟩ : syracuseStep 1146797 = 430049) B430049
theorem B1146851 : Blo 338752 1146851 := bstep (se 1 (by rfl) ⟨860138, by rfl⟩ : syracuseStep 1146851 = 1720277) B1720277
theorem B1147229 : Blo 338752 1147229 := bstep (se 3 (by rfl) ⟨215105, by rfl⟩ : syracuseStep 1147229 = 430211) B430211
theorem B2458147 : Blo 338752 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B5899013 : Blo 338752 5899013 := bstep (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) B1106065
theorem B1934401 : Blo 338752 1934401 := bstep (se 2 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 1934401 = 1450801) B1450801
theorem B1148363 : Blo 338752 1148363 := bstep (se 1 (by rfl) ⟨861272, by rfl⟩ : syracuseStep 1148363 = 1722545) B1722545
theorem B1181249 : Blo 338752 1181249 := bstep (se 2 (by rfl) ⟨442968, by rfl⟩ : syracuseStep 1181249 = 885937) B885937
theorem B525911 : Blo 338752 525911 := bstep (se 1 (by rfl) ⟨394433, by rfl⟩ : syracuseStep 525911 = 788867) B788867
theorem B1148633 : Blo 338752 1148633 := bstep (se 2 (by rfl) ⟨430737, by rfl⟩ : syracuseStep 1148633 = 861475) B861475
theorem B4130605 : Blo 338752 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B690187 : Blo 338752 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B362615 : Blo 338752 362615 := bstep (se 1 (by rfl) ⟨271961, by rfl⟩ : syracuseStep 362615 = 543923) B543923
theorem B1247363 : Blo 338752 1247363 := bstep (se 1 (by rfl) ⟨935522, by rfl⟩ : syracuseStep 1247363 = 1871045) B1871045
theorem B2918551 : Blo 338752 2918551 := bstep (se 1 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 2918551 = 4377827) B4377827
theorem B1149335 : Blo 338752 1149335 := bstep (se 1 (by rfl) ⟨862001, by rfl⟩ : syracuseStep 1149335 = 1724003) B1724003
theorem B5900951 : Blo 338752 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B723863 : Blo 338752 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B1149875 : Blo 338752 1149875 := bstep (se 1 (by rfl) ⟨862406, by rfl⟩ : syracuseStep 1149875 = 1724813) B1724813
theorem B429067 : Blo 338752 429067 := bstep (se 1 (by rfl) ⟨321800, by rfl⟩ : syracuseStep 429067 = 643601) B643601
theorem B691289 : Blo 338752 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B2591837 : Blo 338752 2591837 := bstep (se 3 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 2591837 = 971939) B971939
theorem B1150145 : Blo 338752 1150145 := bstep (se 2 (by rfl) ⟨431304, by rfl⟩ : syracuseStep 1150145 = 862609) B862609
theorem B1510859 : Blo 338752 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B1740305 : Blo 338752 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B1150685 : Blo 338752 1150685 := bstep (se 3 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 1150685 = 431507) B431507
theorem B364375 : Blo 338752 364375 := bstep (se 1 (by rfl) ⟨273281, by rfl⟩ : syracuseStep 364375 = 546563) B546563
theorem B724889 : Blo 338752 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B430039 : Blo 338752 430039 := bstep (se 1 (by rfl) ⟨322529, by rfl⟩ : syracuseStep 430039 = 645059) B645059
theorem B987329 : Blo 338752 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B2068811 : Blo 338752 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B1937843 : Blo 338752 1937843 := bstep (se 1 (by rfl) ⟨1453382, by rfl⟩ : syracuseStep 1937843 = 2906765) B2906765
theorem B365195 : Blo 338752 365195 := bstep (se 1 (by rfl) ⟨273896, by rfl⟩ : syracuseStep 365195 = 547793) B547793
theorem B1250051 : Blo 338752 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B430859 : Blo 338752 430859 := bstep (se 1 (by rfl) ⟨323144, by rfl⟩ : syracuseStep 430859 = 646289) B646289
theorem B1151819 : Blo 338752 1151819 := bstep (se 1 (by rfl) ⟨863864, by rfl⟩ : syracuseStep 1151819 = 1727729) B1727729
theorem B9409571 : Blo 338752 9409571 := bstep (se 1 (by rfl) ⟨7057178, by rfl⟩ : syracuseStep 9409571 = 14114357) B14114357
theorem B1152089 : Blo 338752 1152089 := bstep (se 2 (by rfl) ⟨432033, by rfl⟩ : syracuseStep 1152089 = 864067) B864067
theorem B1545475 : Blo 338752 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B2954501 : Blo 338752 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B693593 : Blo 338752 693593 := bstep (se 2 (by rfl) ⟨260097, by rfl⟩ : syracuseStep 693593 = 520195) B520195
theorem B1086871 : Blo 338752 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B3478963 : Blo 338752 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B857537 : Blo 338752 857537 := bstep (se 2 (by rfl) ⟨321576, by rfl⟩ : syracuseStep 857537 = 643153) B643153
theorem B1381835 : Blo 338752 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B431563 : Blo 338752 431563 := bstep (se 1 (by rfl) ⟨323672, by rfl⟩ : syracuseStep 431563 = 647345) B647345
theorem B726529 : Blo 338752 726529 := bstep (se 2 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 726529 = 544897) B544897
theorem B431831 : Blo 338752 431831 := bstep (se 1 (by rfl) ⟨323873, by rfl⟩ : syracuseStep 431831 = 647747) B647747
theorem B1152791 : Blo 338752 1152791 := bstep (se 1 (by rfl) ⟨864593, by rfl⟩ : syracuseStep 1152791 = 1729187) B1729187
theorem B1939301 : Blo 338752 1939301 := bstep (se 4 (by rfl) ⟨181809, by rfl⟩ : syracuseStep 1939301 = 363619) B363619
theorem B694145 : Blo 338752 694145 := bstep (se 2 (by rfl) ⟨260304, by rfl⟩ : syracuseStep 694145 = 520609) B520609
theorem B1087435 : Blo 338752 1087435 := bstep (se 1 (by rfl) ⟨815576, by rfl⟩ : syracuseStep 1087435 = 1631153) B1631153
theorem B858073 : Blo 338752 858073 := bstep (se 2 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 858073 = 643555) B643555
theorem B727127 : Blo 338752 727127 := bstep (se 1 (by rfl) ⟨545345, by rfl⟩ : syracuseStep 727127 = 1090691) B1090691
theorem B1087577 : Blo 338752 1087577 := bstep (se 2 (by rfl) ⟨407841, by rfl⟩ : syracuseStep 1087577 = 815683) B815683
theorem B1644761 : Blo 338752 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B1153331 : Blo 338752 1153331 := bstep (se 1 (by rfl) ⟨864998, by rfl⟩ : syracuseStep 1153331 = 1729997) B1729997
theorem B432535 : Blo 338752 432535 := bstep (se 1 (by rfl) ⟨324401, by rfl⟩ : syracuseStep 432535 = 648803) B648803
theorem B694745 : Blo 338752 694745 := bstep (se 2 (by rfl) ⟨260529, by rfl⟩ : syracuseStep 694745 = 521059) B521059
theorem B1546775 : Blo 338752 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B1448513 : Blo 338752 1448513 := bstep (se 2 (by rfl) ⟨543192, by rfl⟩ : syracuseStep 1448513 = 1086385) B1086385
theorem B1153601 : Blo 338752 1153601 := bstep (se 2 (by rfl) ⟨432600, by rfl⟩ : syracuseStep 1153601 = 865201) B865201
theorem B859187 : Blo 338752 859187 := bstep (se 1 (by rfl) ⟨644390, by rfl⟩ : syracuseStep 859187 = 1288781) B1288781
theorem B2628683 : Blo 338752 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B1154141 : Blo 338752 1154141 := bstep (se 3 (by rfl) ⟨216401, by rfl⟩ : syracuseStep 1154141 = 432803) B432803
theorem B728203 : Blo 338752 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B1088819 : Blo 338752 1088819 := bstep (se 1 (by rfl) ⟨816614, by rfl⟩ : syracuseStep 1088819 = 1633229) B1633229
theorem B1383731 : Blo 338752 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B859481 : Blo 338752 859481 := bstep (se 2 (by rfl) ⟨322305, by rfl⟩ : syracuseStep 859481 = 644611) B644611
theorem B368075 : Blo 338752 368075 := bstep (se 1 (by rfl) ⟨276056, by rfl⟩ : syracuseStep 368075 = 552113) B552113
theorem B2760227 : Blo 338752 2760227 := bstep (se 1 (by rfl) ⟨2070170, by rfl⟩ : syracuseStep 2760227 = 4140341) B4140341
theorem B1089217 : Blo 338752 1089217 := bstep (se 2 (by rfl) ⟨408456, by rfl⟩ : syracuseStep 1089217 = 816913) B816913
theorem B6233861 : Blo 338752 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B728921 : Blo 338752 728921 := bstep (se 2 (by rfl) ⟨273345, by rfl⟩ : syracuseStep 728921 = 546691) B546691
theorem B368651 : Blo 338752 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B1646743 : Blo 338752 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B1974451 : Blo 338752 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B1450187 : Blo 338752 1450187 := bstep (se 1 (by rfl) ⟨1087640, by rfl⟩ : syracuseStep 1450187 = 2175281) B2175281
theorem B1155275 : Blo 338752 1155275 := bstep (se 1 (by rfl) ⟨866456, by rfl⟩ : syracuseStep 1155275 = 1732913) B1732913
theorem B467275 : Blo 338752 467275 := bstep (se 1 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 467275 = 700913) B700913
theorem B729433 : Blo 338752 729433 := bstep (se 2 (by rfl) ⟨273537, by rfl⟩ : syracuseStep 729433 = 547075) B547075
theorem B762227 : Blo 338752 762227 := bstep (se 1 (by rfl) ⟨571670, by rfl⟩ : syracuseStep 762227 = 1143341) B1143341
theorem B4366709 : Blo 338752 4366709 := bstep (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) B409379
theorem B762263 : Blo 338752 762263 := bstep (se 1 (by rfl) ⟨571697, by rfl⟩ : syracuseStep 762263 = 1143395) B1143395
theorem B1155545 : Blo 338752 1155545 := bstep (se 2 (by rfl) ⟨433329, by rfl⟩ : syracuseStep 1155545 = 866659) B866659
theorem B729587 : Blo 338752 729587 := bstep (se 1 (by rfl) ⟨547190, by rfl⟩ : syracuseStep 729587 = 1094381) B1094381
theorem B3875363 : Blo 338752 3875363 := bstep (se 1 (by rfl) ⟨2906522, by rfl⟩ : syracuseStep 3875363 = 5813045) B5813045
theorem B762443 : Blo 338752 762443 := bstep (se 1 (by rfl) ⟨571832, by rfl⟩ : syracuseStep 762443 = 1143665) B1143665
theorem B762497 : Blo 338752 762497 := bstep (se 2 (by rfl) ⟨285936, by rfl⟩ : syracuseStep 762497 = 571873) B571873
theorem B5415605 : Blo 338752 5415605 := bstep (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) B507713
theorem B762713 : Blo 338752 762713 := bstep (se 2 (by rfl) ⟨286017, by rfl⟩ : syracuseStep 762713 = 572035) B572035
theorem B762803 : Blo 338752 762803 := bstep (se 1 (by rfl) ⟨572102, by rfl⟩ : syracuseStep 762803 = 1144205) B1144205
theorem B861131 : Blo 338752 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B762839 : Blo 338752 762839 := bstep (se 1 (by rfl) ⟨572129, by rfl⟩ : syracuseStep 762839 = 1144259) B1144259
theorem B1450973 : Blo 338752 1450973 := bstep (se 3 (by rfl) ⟨272057, by rfl⟩ : syracuseStep 1450973 = 544115) B544115
theorem B763019 : Blo 338752 763019 := bstep (se 1 (by rfl) ⟨572264, by rfl⟩ : syracuseStep 763019 = 1144529) B1144529
theorem B1156247 : Blo 338752 1156247 := bstep (se 1 (by rfl) ⟨867185, by rfl⟩ : syracuseStep 1156247 = 1734371) B1734371
theorem B763073 : Blo 338752 763073 := bstep (se 2 (by rfl) ⟨286152, by rfl⟩ : syracuseStep 763073 = 572305) B572305
theorem B1746137 : Blo 338752 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B1221911 : Blo 338752 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B4367681 : Blo 338752 4367681 := bstep (se 2 (by rfl) ⟨1637880, by rfl⟩ : syracuseStep 4367681 = 3275761) B3275761
theorem B763289 : Blo 338752 763289 := bstep (se 2 (by rfl) ⟨286233, by rfl⟩ : syracuseStep 763289 = 572467) B572467
theorem B730561 : Blo 338752 730561 := bstep (se 2 (by rfl) ⟨273960, by rfl⟩ : syracuseStep 730561 = 547921) B547921
theorem B763379 : Blo 338752 763379 := bstep (se 1 (by rfl) ⟨572534, by rfl⟩ : syracuseStep 763379 = 1145069) B1145069
theorem B763415 : Blo 338752 763415 := bstep (se 1 (by rfl) ⟨572561, by rfl⟩ : syracuseStep 763415 = 1145123) B1145123
theorem B1975853 : Blo 338752 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B1156787 : Blo 338752 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B763595 : Blo 338752 763595 := bstep (se 1 (by rfl) ⟨572696, by rfl⟩ : syracuseStep 763595 = 1145393) B1145393
theorem B763649 : Blo 338752 763649 := bstep (se 2 (by rfl) ⟨286368, by rfl⟩ : syracuseStep 763649 = 572737) B572737
theorem B730903 : Blo 338752 730903 := bstep (se 1 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 730903 = 1096355) B1096355
theorem B2762561 : Blo 338752 2762561 := bstep (se 2 (by rfl) ⟨1035960, by rfl⟩ : syracuseStep 2762561 = 2071921) B2071921
theorem B862103 : Blo 338752 862103 := bstep (se 1 (by rfl) ⟨646577, by rfl⟩ : syracuseStep 862103 = 1293155) B1293155
theorem B763865 : Blo 338752 763865 := bstep (se 2 (by rfl) ⟨286449, by rfl⟩ : syracuseStep 763865 = 572899) B572899
theorem B763955 : Blo 338752 763955 := bstep (se 1 (by rfl) ⟨572966, by rfl⟩ : syracuseStep 763955 = 1145933) B1145933
theorem B763991 : Blo 338752 763991 := bstep (se 1 (by rfl) ⟨572993, by rfl⟩ : syracuseStep 763991 = 1145987) B1145987
theorem B731339 : Blo 338752 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B2074841 : Blo 338752 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B764171 : Blo 338752 764171 := bstep (se 1 (by rfl) ⟨573128, by rfl⟩ : syracuseStep 764171 = 1146257) B1146257
theorem B1452305 : Blo 338752 1452305 := bstep (se 2 (by rfl) ⟨544614, by rfl⟩ : syracuseStep 1452305 = 1089229) B1089229
theorem B1288493 : Blo 338752 1288493 := bstep (se 3 (by rfl) ⟨241592, by rfl⟩ : syracuseStep 1288493 = 483185) B483185
theorem B764225 : Blo 338752 764225 := bstep (se 2 (by rfl) ⟨286584, by rfl⟩ : syracuseStep 764225 = 573169) B573169
theorem B1223191 : Blo 338752 1223191 := bstep (se 1 (by rfl) ⟨917393, by rfl⟩ : syracuseStep 1223191 = 1834787) B1834787
theorem B764441 : Blo 338752 764441 := bstep (se 2 (by rfl) ⟨286665, by rfl⟩ : syracuseStep 764441 = 573331) B573331
theorem B862771 : Blo 338752 862771 := bstep (se 1 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 862771 = 1294157) B1294157
theorem B764531 : Blo 338752 764531 := bstep (se 1 (by rfl) ⟨573398, by rfl⟩ : syracuseStep 764531 = 1146797) B1146797
theorem B764567 : Blo 338752 764567 := bstep (se 1 (by rfl) ⟨573425, by rfl⟩ : syracuseStep 764567 = 1146851) B1146851
theorem B862913 : Blo 338752 862913 := bstep (se 2 (by rfl) ⟨323592, by rfl⟩ : syracuseStep 862913 = 647185) B647185
theorem B338763 : Blo 338752 338763 := bstep (se 1 (by rfl) ⟨254072, by rfl⟩ : syracuseStep 338763 = 508145) B508145
theorem B764747 : Blo 338752 764747 := bstep (se 1 (by rfl) ⟨573560, by rfl⟩ : syracuseStep 764747 = 1147121) B1147121
theorem B338775 : Blo 338752 338775 := bstep (se 1 (by rfl) ⟨254081, by rfl⟩ : syracuseStep 338775 = 508163) B508163
theorem B338795 : Blo 338752 338795 := bstep (se 1 (by rfl) ⟨254096, by rfl⟩ : syracuseStep 338795 = 508193) B508193
theorem B338807 : Blo 338752 338807 := bstep (se 1 (by rfl) ⟨254105, by rfl⟩ : syracuseStep 338807 = 508211) B508211
theorem B764801 : Blo 338752 764801 := bstep (se 2 (by rfl) ⟨286800, by rfl⟩ : syracuseStep 764801 = 573601) B573601
theorem B338827 : Blo 338752 338827 := bstep (se 1 (by rfl) ⟨254120, by rfl⟩ : syracuseStep 338827 = 508241) B508241
theorem B338839 : Blo 338752 338839 := bstep (se 1 (by rfl) ⟨254129, by rfl⟩ : syracuseStep 338839 = 508259) B508259
theorem B338859 : Blo 338752 338859 := bstep (se 1 (by rfl) ⟨254144, by rfl⟩ : syracuseStep 338859 = 508289) B508289
theorem B338871 : Blo 338752 338871 := bstep (se 1 (by rfl) ⟨254153, by rfl⟩ : syracuseStep 338871 = 508307) B508307
theorem B338891 : Blo 338752 338891 := bstep (se 1 (by rfl) ⟨254168, by rfl⟩ : syracuseStep 338891 = 508337) B508337
theorem B338903 : Blo 338752 338903 := bstep (se 1 (by rfl) ⟨254177, by rfl⟩ : syracuseStep 338903 = 508355) B508355
theorem B338923 : Blo 338752 338923 := bstep (se 1 (by rfl) ⟨254192, by rfl⟩ : syracuseStep 338923 = 508385) B508385
theorem B338935 : Blo 338752 338935 := bstep (se 1 (by rfl) ⟨254201, by rfl⟩ : syracuseStep 338935 = 508403) B508403
theorem B338955 : Blo 338752 338955 := bstep (se 1 (by rfl) ⟨254216, by rfl⟩ : syracuseStep 338955 = 508433) B508433
theorem B338967 : Blo 338752 338967 := bstep (se 1 (by rfl) ⟨254225, by rfl⟩ : syracuseStep 338967 = 508451) B508451
theorem B338987 : Blo 338752 338987 := bstep (se 1 (by rfl) ⟨254240, by rfl⟩ : syracuseStep 338987 = 508481) B508481
theorem B1289267 : Blo 338752 1289267 := bstep (se 1 (by rfl) ⟨966950, by rfl⟩ : syracuseStep 1289267 = 1933901) B1933901
theorem B338999 : Blo 338752 338999 := bstep (se 1 (by rfl) ⟨254249, by rfl⟩ : syracuseStep 338999 = 508499) B508499
theorem B339019 : Blo 338752 339019 := bstep (se 1 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 339019 = 508529) B508529
theorem B339031 : Blo 338752 339031 := bstep (se 1 (by rfl) ⟨254273, by rfl⟩ : syracuseStep 339031 = 508547) B508547
theorem B765017 : Blo 338752 765017 := bstep (se 2 (by rfl) ⟨286881, by rfl⟩ : syracuseStep 765017 = 573763) B573763
theorem B339051 : Blo 338752 339051 := bstep (se 1 (by rfl) ⟨254288, by rfl⟩ : syracuseStep 339051 = 508577) B508577
theorem B339063 : Blo 338752 339063 := bstep (se 1 (by rfl) ⟨254297, by rfl⟩ : syracuseStep 339063 = 508595) B508595
theorem B339083 : Blo 338752 339083 := bstep (se 1 (by rfl) ⟨254312, by rfl⟩ : syracuseStep 339083 = 508625) B508625
theorem B339095 : Blo 338752 339095 := bstep (se 1 (by rfl) ⟨254321, by rfl⟩ : syracuseStep 339095 = 508643) B508643
theorem B339115 : Blo 338752 339115 := bstep (se 1 (by rfl) ⟨254336, by rfl⟩ : syracuseStep 339115 = 508673) B508673
theorem B765107 : Blo 338752 765107 := bstep (se 1 (by rfl) ⟨573830, by rfl⟩ : syracuseStep 765107 = 1147661) B1147661
theorem B339127 : Blo 338752 339127 := bstep (se 1 (by rfl) ⟨254345, by rfl⟩ : syracuseStep 339127 = 508691) B508691
theorem B339147 : Blo 338752 339147 := bstep (se 1 (by rfl) ⟨254360, by rfl⟩ : syracuseStep 339147 = 508721) B508721
theorem B339159 : Blo 338752 339159 := bstep (se 1 (by rfl) ⟨254369, by rfl⟩ : syracuseStep 339159 = 508739) B508739
theorem B765143 : Blo 338752 765143 := bstep (se 1 (by rfl) ⟨573857, by rfl⟩ : syracuseStep 765143 = 1147715) B1147715
theorem B1715417 : Blo 338752 1715417 := bstep (se 2 (by rfl) ⟨643281, by rfl⟩ : syracuseStep 1715417 = 1286563) B1286563
theorem B339179 : Blo 338752 339179 := bstep (se 1 (by rfl) ⟨254384, by rfl⟩ : syracuseStep 339179 = 508769) B508769
theorem B339191 : Blo 338752 339191 := bstep (se 1 (by rfl) ⟨254393, by rfl⟩ : syracuseStep 339191 = 508787) B508787
theorem B6991109 : Blo 338752 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B339211 : Blo 338752 339211 := bstep (se 1 (by rfl) ⟨254408, by rfl⟩ : syracuseStep 339211 = 508817) B508817
theorem B339223 : Blo 338752 339223 := bstep (se 1 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 339223 = 508835) B508835
theorem B339243 : Blo 338752 339243 := bstep (se 1 (by rfl) ⟨254432, by rfl⟩ : syracuseStep 339243 = 508865) B508865
theorem B339255 : Blo 338752 339255 := bstep (se 1 (by rfl) ⟨254441, by rfl⟩ : syracuseStep 339255 = 508883) B508883
theorem B339275 : Blo 338752 339275 := bstep (se 1 (by rfl) ⟨254456, by rfl⟩ : syracuseStep 339275 = 508913) B508913
theorem B339287 : Blo 338752 339287 := bstep (se 1 (by rfl) ⟨254465, by rfl⟩ : syracuseStep 339287 = 508931) B508931
theorem B339307 : Blo 338752 339307 := bstep (se 1 (by rfl) ⟨254480, by rfl⟩ : syracuseStep 339307 = 508961) B508961
theorem B339319 : Blo 338752 339319 := bstep (se 1 (by rfl) ⟨254489, by rfl⟩ : syracuseStep 339319 = 508979) B508979
theorem B339339 : Blo 338752 339339 := bstep (se 1 (by rfl) ⟨254504, by rfl⟩ : syracuseStep 339339 = 509009) B509009
theorem B765323 : Blo 338752 765323 := bstep (se 1 (by rfl) ⟨573992, by rfl⟩ : syracuseStep 765323 = 1147985) B1147985
theorem B339351 : Blo 338752 339351 := bstep (se 1 (by rfl) ⟨254513, by rfl⟩ : syracuseStep 339351 = 509027) B509027
theorem B339371 : Blo 338752 339371 := bstep (se 1 (by rfl) ⟨254528, by rfl⟩ : syracuseStep 339371 = 509057) B509057
theorem B339383 : Blo 338752 339383 := bstep (se 1 (by rfl) ⟨254537, by rfl⟩ : syracuseStep 339383 = 509075) B509075
theorem B765377 : Blo 338752 765377 := bstep (se 2 (by rfl) ⟨287016, by rfl⟩ : syracuseStep 765377 = 574033) B574033
theorem B339403 : Blo 338752 339403 := bstep (se 1 (by rfl) ⟨254552, by rfl⟩ : syracuseStep 339403 = 509105) B509105
theorem B339415 : Blo 338752 339415 := bstep (se 1 (by rfl) ⟨254561, by rfl⟩ : syracuseStep 339415 = 509123) B509123
theorem B339435 : Blo 338752 339435 := bstep (se 1 (by rfl) ⟨254576, by rfl⟩ : syracuseStep 339435 = 509153) B509153
theorem B339447 : Blo 338752 339447 := bstep (se 1 (by rfl) ⟨254585, by rfl⟩ : syracuseStep 339447 = 509171) B509171
theorem B1453571 : Blo 338752 1453571 := bstep (se 1 (by rfl) ⟨1090178, by rfl⟩ : syracuseStep 1453571 = 2180357) B2180357
theorem B339467 : Blo 338752 339467 := bstep (se 1 (by rfl) ⟨254600, by rfl⟩ : syracuseStep 339467 = 509201) B509201
theorem B339479 : Blo 338752 339479 := bstep (se 1 (by rfl) ⟨254609, by rfl⟩ : syracuseStep 339479 = 509219) B509219
theorem B339499 : Blo 338752 339499 := bstep (se 1 (by rfl) ⟨254624, by rfl⟩ : syracuseStep 339499 = 509249) B509249
theorem B1945133 : Blo 338752 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B339511 : Blo 338752 339511 := bstep (se 1 (by rfl) ⟨254633, by rfl⟩ : syracuseStep 339511 = 509267) B509267
theorem B339531 : Blo 338752 339531 := bstep (se 1 (by rfl) ⟨254648, by rfl⟩ : syracuseStep 339531 = 509297) B509297
theorem B339543 : Blo 338752 339543 := bstep (se 1 (by rfl) ⟨254657, by rfl⟩ : syracuseStep 339543 = 509315) B509315
theorem B339563 : Blo 338752 339563 := bstep (se 1 (by rfl) ⟨254672, by rfl⟩ : syracuseStep 339563 = 509345) B509345
theorem B339575 : Blo 338752 339575 := bstep (se 1 (by rfl) ⟨254681, by rfl⟩ : syracuseStep 339575 = 509363) B509363
theorem B339595 : Blo 338752 339595 := bstep (se 1 (by rfl) ⟨254696, by rfl⟩ : syracuseStep 339595 = 509393) B509393
theorem B339607 : Blo 338752 339607 := bstep (se 1 (by rfl) ⟨254705, by rfl⟩ : syracuseStep 339607 = 509411) B509411
theorem B765593 : Blo 338752 765593 := bstep (se 2 (by rfl) ⟨287097, by rfl⟩ : syracuseStep 765593 = 574195) B574195
theorem B339627 : Blo 338752 339627 := bstep (se 1 (by rfl) ⟨254720, by rfl⟩ : syracuseStep 339627 = 509441) B509441
theorem B339639 : Blo 338752 339639 := bstep (se 1 (by rfl) ⟨254729, by rfl⟩ : syracuseStep 339639 = 509459) B509459
theorem B339659 : Blo 338752 339659 := bstep (se 1 (by rfl) ⟨254744, by rfl⟩ : syracuseStep 339659 = 509489) B509489
theorem B339671 : Blo 338752 339671 := bstep (se 1 (by rfl) ⟨254753, by rfl⟩ : syracuseStep 339671 = 509507) B509507
theorem B339691 : Blo 338752 339691 := bstep (se 1 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 339691 = 509537) B509537
theorem B765683 : Blo 338752 765683 := bstep (se 1 (by rfl) ⟨574262, by rfl⟩ : syracuseStep 765683 = 1148525) B1148525
theorem B339703 : Blo 338752 339703 := bstep (se 1 (by rfl) ⟨254777, by rfl⟩ : syracuseStep 339703 = 509555) B509555
theorem B339723 : Blo 338752 339723 := bstep (se 1 (by rfl) ⟨254792, by rfl⟩ : syracuseStep 339723 = 509585) B509585
theorem B339735 : Blo 338752 339735 := bstep (se 1 (by rfl) ⟨254801, by rfl⟩ : syracuseStep 339735 = 509603) B509603
theorem B765719 : Blo 338752 765719 := bstep (se 1 (by rfl) ⟨574289, by rfl⟩ : syracuseStep 765719 = 1148579) B1148579
theorem B339755 : Blo 338752 339755 := bstep (se 1 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 339755 = 509633) B509633
theorem B339767 : Blo 338752 339767 := bstep (se 1 (by rfl) ⟨254825, by rfl⟩ : syracuseStep 339767 = 509651) B509651
theorem B339787 : Blo 338752 339787 := bstep (se 1 (by rfl) ⟨254840, by rfl⟩ : syracuseStep 339787 = 509681) B509681
theorem B339799 : Blo 338752 339799 := bstep (se 1 (by rfl) ⟨254849, by rfl⟩ : syracuseStep 339799 = 509699) B509699
theorem B2764637 : Blo 338752 2764637 := bstep (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) B1036739
theorem B339819 : Blo 338752 339819 := bstep (se 1 (by rfl) ⟨254864, by rfl⟩ : syracuseStep 339819 = 509729) B509729
theorem B339831 : Blo 338752 339831 := bstep (se 1 (by rfl) ⟨254873, by rfl⟩ : syracuseStep 339831 = 509747) B509747
theorem B339851 : Blo 338752 339851 := bstep (se 1 (by rfl) ⟨254888, by rfl⟩ : syracuseStep 339851 = 509777) B509777
theorem B339863 : Blo 338752 339863 := bstep (se 1 (by rfl) ⟨254897, by rfl⟩ : syracuseStep 339863 = 509795) B509795
theorem B339883 : Blo 338752 339883 := bstep (se 1 (by rfl) ⟨254912, by rfl⟩ : syracuseStep 339883 = 509825) B509825
theorem B25472945 : Blo 338752 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B864179 : Blo 338752 864179 := bstep (se 1 (by rfl) ⟨648134, by rfl⟩ : syracuseStep 864179 = 1296269) B1296269
theorem B339895 : Blo 338752 339895 := bstep (se 1 (by rfl) ⟨254921, by rfl⟩ : syracuseStep 339895 = 509843) B509843
theorem B339915 : Blo 338752 339915 := bstep (se 1 (by rfl) ⟨254936, by rfl⟩ : syracuseStep 339915 = 509873) B509873
theorem B765899 : Blo 338752 765899 := bstep (se 1 (by rfl) ⟨574424, by rfl⟩ : syracuseStep 765899 = 1148849) B1148849
theorem B339927 : Blo 338752 339927 := bstep (se 1 (by rfl) ⟨254945, by rfl⟩ : syracuseStep 339927 = 509891) B509891
theorem B339947 : Blo 338752 339947 := bstep (se 1 (by rfl) ⟨254960, by rfl⟩ : syracuseStep 339947 = 509921) B509921
theorem B339959 : Blo 338752 339959 := bstep (se 1 (by rfl) ⟨254969, by rfl⟩ : syracuseStep 339959 = 509939) B509939
theorem B765953 : Blo 338752 765953 := bstep (se 2 (by rfl) ⟨287232, by rfl⟩ : syracuseStep 765953 = 574465) B574465
theorem B339979 : Blo 338752 339979 := bstep (se 1 (by rfl) ⟨254984, by rfl⟩ : syracuseStep 339979 = 509969) B509969
theorem B339991 : Blo 338752 339991 := bstep (se 1 (by rfl) ⟨254993, by rfl⟩ : syracuseStep 339991 = 509987) B509987
theorem B340011 : Blo 338752 340011 := bstep (se 1 (by rfl) ⟨255008, by rfl⟩ : syracuseStep 340011 = 510017) B510017
theorem B340023 : Blo 338752 340023 := bstep (se 1 (by rfl) ⟨255017, by rfl⟩ : syracuseStep 340023 = 510035) B510035
theorem B340043 : Blo 338752 340043 := bstep (se 1 (by rfl) ⟨255032, by rfl⟩ : syracuseStep 340043 = 510065) B510065
theorem B340055 : Blo 338752 340055 := bstep (se 1 (by rfl) ⟨255041, by rfl⟩ : syracuseStep 340055 = 510083) B510083
theorem B340075 : Blo 338752 340075 := bstep (se 1 (by rfl) ⟨255056, by rfl⟩ : syracuseStep 340075 = 510113) B510113
theorem B340087 : Blo 338752 340087 := bstep (se 1 (by rfl) ⟨255065, by rfl⟩ : syracuseStep 340087 = 510131) B510131
theorem B340107 : Blo 338752 340107 := bstep (se 1 (by rfl) ⟨255080, by rfl⟩ : syracuseStep 340107 = 510161) B510161
theorem B340119 : Blo 338752 340119 := bstep (se 1 (by rfl) ⟨255089, by rfl⟩ : syracuseStep 340119 = 510179) B510179
theorem B340139 : Blo 338752 340139 := bstep (se 1 (by rfl) ⟨255104, by rfl⟩ : syracuseStep 340139 = 510209) B510209
theorem B340151 : Blo 338752 340151 := bstep (se 1 (by rfl) ⟨255113, by rfl⟩ : syracuseStep 340151 = 510227) B510227
theorem B340171 : Blo 338752 340171 := bstep (se 1 (by rfl) ⟨255128, by rfl⟩ : syracuseStep 340171 = 510257) B510257
theorem B340183 : Blo 338752 340183 := bstep (se 1 (by rfl) ⟨255137, by rfl⟩ : syracuseStep 340183 = 510275) B510275
theorem B766169 : Blo 338752 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B340203 : Blo 338752 340203 := bstep (se 1 (by rfl) ⟨255152, by rfl⟩ : syracuseStep 340203 = 510305) B510305
theorem B340215 : Blo 338752 340215 := bstep (se 1 (by rfl) ⟨255161, by rfl⟩ : syracuseStep 340215 = 510323) B510323
theorem B340235 : Blo 338752 340235 := bstep (se 1 (by rfl) ⟨255176, by rfl⟩ : syracuseStep 340235 = 510353) B510353
theorem B340247 : Blo 338752 340247 := bstep (se 1 (by rfl) ⟨255185, by rfl⟩ : syracuseStep 340247 = 510371) B510371
theorem B340267 : Blo 338752 340267 := bstep (se 1 (by rfl) ⟨255200, by rfl⟩ : syracuseStep 340267 = 510401) B510401
theorem B766259 : Blo 338752 766259 := bstep (se 1 (by rfl) ⟨574694, by rfl⟩ : syracuseStep 766259 = 1149389) B1149389
theorem B340279 : Blo 338752 340279 := bstep (se 1 (by rfl) ⟨255209, by rfl⟩ : syracuseStep 340279 = 510419) B510419
theorem B340299 : Blo 338752 340299 := bstep (se 1 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 340299 = 510449) B510449
theorem B340311 : Blo 338752 340311 := bstep (se 1 (by rfl) ⟨255233, by rfl⟩ : syracuseStep 340311 = 510467) B510467
theorem B766295 : Blo 338752 766295 := bstep (se 1 (by rfl) ⟨574721, by rfl⟩ : syracuseStep 766295 = 1149443) B1149443
theorem B340331 : Blo 338752 340331 := bstep (se 1 (by rfl) ⟨255248, by rfl⟩ : syracuseStep 340331 = 510497) B510497
theorem B340343 : Blo 338752 340343 := bstep (se 1 (by rfl) ⟨255257, by rfl⟩ : syracuseStep 340343 = 510515) B510515
theorem B340363 : Blo 338752 340363 := bstep (se 1 (by rfl) ⟨255272, by rfl⟩ : syracuseStep 340363 = 510545) B510545
theorem B340375 : Blo 338752 340375 := bstep (se 1 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 340375 = 510563) B510563
theorem B700823 : Blo 338752 700823 := bstep (se 1 (by rfl) ⟨525617, by rfl⟩ : syracuseStep 700823 = 1051235) B1051235
theorem B340395 : Blo 338752 340395 := bstep (se 1 (by rfl) ⟨255296, by rfl⟩ : syracuseStep 340395 = 510593) B510593
theorem B340407 : Blo 338752 340407 := bstep (se 1 (by rfl) ⟨255305, by rfl⟩ : syracuseStep 340407 = 510611) B510611
theorem B340427 : Blo 338752 340427 := bstep (se 1 (by rfl) ⟨255320, by rfl⟩ : syracuseStep 340427 = 510641) B510641
theorem B864715 : Blo 338752 864715 := bstep (se 1 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 864715 = 1297073) B1297073
theorem B340439 : Blo 338752 340439 := bstep (se 1 (by rfl) ⟨255329, by rfl⟩ : syracuseStep 340439 = 510659) B510659
theorem B340459 : Blo 338752 340459 := bstep (se 1 (by rfl) ⟨255344, by rfl⟩ : syracuseStep 340459 = 510689) B510689
theorem B340471 : Blo 338752 340471 := bstep (se 1 (by rfl) ⟨255353, by rfl⟩ : syracuseStep 340471 = 510707) B510707
theorem B1290755 : Blo 338752 1290755 := bstep (se 1 (by rfl) ⟨968066, by rfl⟩ : syracuseStep 1290755 = 1936133) B1936133
theorem B340491 : Blo 338752 340491 := bstep (se 1 (by rfl) ⟨255368, by rfl⟩ : syracuseStep 340491 = 510737) B510737
theorem B766475 : Blo 338752 766475 := bstep (se 1 (by rfl) ⟨574856, by rfl⟩ : syracuseStep 766475 = 1149713) B1149713
theorem B340503 : Blo 338752 340503 := bstep (se 1 (by rfl) ⟨255377, by rfl⟩ : syracuseStep 340503 = 510755) B510755
theorem B340523 : Blo 338752 340523 := bstep (se 1 (by rfl) ⟨255392, by rfl⟩ : syracuseStep 340523 = 510785) B510785
theorem B340535 : Blo 338752 340535 := bstep (se 1 (by rfl) ⟨255401, by rfl⟩ : syracuseStep 340535 = 510803) B510803
theorem B766529 : Blo 338752 766529 := bstep (se 2 (by rfl) ⟨287448, by rfl⟩ : syracuseStep 766529 = 574897) B574897
theorem B340555 : Blo 338752 340555 := bstep (se 1 (by rfl) ⟨255416, by rfl⟩ : syracuseStep 340555 = 510833) B510833
theorem B340567 : Blo 338752 340567 := bstep (se 1 (by rfl) ⟨255425, by rfl⟩ : syracuseStep 340567 = 510851) B510851
theorem B864857 : Blo 338752 864857 := bstep (se 2 (by rfl) ⟨324321, by rfl⟩ : syracuseStep 864857 = 648643) B648643
theorem B340587 : Blo 338752 340587 := bstep (se 1 (by rfl) ⟨255440, by rfl⟩ : syracuseStep 340587 = 510881) B510881
theorem B340599 : Blo 338752 340599 := bstep (se 1 (by rfl) ⟨255449, by rfl⟩ : syracuseStep 340599 = 510899) B510899
theorem B340619 : Blo 338752 340619 := bstep (se 1 (by rfl) ⟨255464, by rfl⟩ : syracuseStep 340619 = 510929) B510929
theorem B340631 : Blo 338752 340631 := bstep (se 1 (by rfl) ⟨255473, by rfl⟩ : syracuseStep 340631 = 510947) B510947
theorem B340651 : Blo 338752 340651 := bstep (se 1 (by rfl) ⟨255488, by rfl⟩ : syracuseStep 340651 = 510977) B510977
theorem B340663 : Blo 338752 340663 := bstep (se 1 (by rfl) ⟨255497, by rfl⟩ : syracuseStep 340663 = 510995) B510995
theorem B340683 : Blo 338752 340683 := bstep (se 1 (by rfl) ⟨255512, by rfl⟩ : syracuseStep 340683 = 511025) B511025
theorem B340695 : Blo 338752 340695 := bstep (se 1 (by rfl) ⟨255521, by rfl⟩ : syracuseStep 340695 = 511043) B511043
theorem B1159901 : Blo 338752 1159901 := bstep (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) B434963
theorem B340715 : Blo 338752 340715 := bstep (se 1 (by rfl) ⟨255536, by rfl⟩ : syracuseStep 340715 = 511073) B511073
theorem B340727 : Blo 338752 340727 := bstep (se 1 (by rfl) ⟨255545, by rfl⟩ : syracuseStep 340727 = 511091) B511091
theorem B340747 : Blo 338752 340747 := bstep (se 1 (by rfl) ⟨255560, by rfl⟩ : syracuseStep 340747 = 511121) B511121
theorem B340759 : Blo 338752 340759 := bstep (se 1 (by rfl) ⟨255569, by rfl⟩ : syracuseStep 340759 = 511139) B511139
theorem B766745 : Blo 338752 766745 := bstep (se 2 (by rfl) ⟨287529, by rfl⟩ : syracuseStep 766745 = 575059) B575059
theorem B340779 : Blo 338752 340779 := bstep (se 1 (by rfl) ⟨255584, by rfl⟩ : syracuseStep 340779 = 511169) B511169
theorem B1717037 : Blo 338752 1717037 := bstep (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) B643889
theorem B340791 : Blo 338752 340791 := bstep (se 1 (by rfl) ⟨255593, by rfl⟩ : syracuseStep 340791 = 511187) B511187
theorem B340811 : Blo 338752 340811 := bstep (se 1 (by rfl) ⟨255608, by rfl⟩ : syracuseStep 340811 = 511217) B511217
theorem B340823 : Blo 338752 340823 := bstep (se 1 (by rfl) ⟨255617, by rfl⟩ : syracuseStep 340823 = 511235) B511235
theorem B340843 : Blo 338752 340843 := bstep (se 1 (by rfl) ⟨255632, by rfl⟩ : syracuseStep 340843 = 511265) B511265
theorem B766835 : Blo 338752 766835 := bstep (se 1 (by rfl) ⟨575126, by rfl⟩ : syracuseStep 766835 = 1150253) B1150253
theorem B340855 : Blo 338752 340855 := bstep (se 1 (by rfl) ⟨255641, by rfl⟩ : syracuseStep 340855 = 511283) B511283
theorem B340875 : Blo 338752 340875 := bstep (se 1 (by rfl) ⟨255656, by rfl⟩ : syracuseStep 340875 = 511313) B511313
theorem B766871 : Blo 338752 766871 := bstep (se 1 (by rfl) ⟨575153, by rfl⟩ : syracuseStep 766871 = 1150307) B1150307
theorem B340887 : Blo 338752 340887 := bstep (se 1 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 340887 = 511331) B511331
theorem B340907 : Blo 338752 340907 := bstep (se 1 (by rfl) ⟨255680, by rfl⟩ : syracuseStep 340907 = 511361) B511361
theorem B340919 : Blo 338752 340919 := bstep (se 1 (by rfl) ⟨255689, by rfl⟩ : syracuseStep 340919 = 511379) B511379
theorem B1291211 : Blo 338752 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B340939 : Blo 338752 340939 := bstep (se 1 (by rfl) ⟨255704, by rfl⟩ : syracuseStep 340939 = 511409) B511409
theorem B340951 : Blo 338752 340951 := bstep (se 1 (by rfl) ⟨255713, by rfl⟩ : syracuseStep 340951 = 511427) B511427
theorem B340971 : Blo 338752 340971 := bstep (se 1 (by rfl) ⟨255728, by rfl⟩ : syracuseStep 340971 = 511457) B511457
theorem B340983 : Blo 338752 340983 := bstep (se 1 (by rfl) ⟨255737, by rfl⟩ : syracuseStep 340983 = 511475) B511475
theorem B341003 : Blo 338752 341003 := bstep (se 1 (by rfl) ⟨255752, by rfl⟩ : syracuseStep 341003 = 511505) B511505
theorem B341015 : Blo 338752 341015 := bstep (se 1 (by rfl) ⟨255761, by rfl⟩ : syracuseStep 341015 = 511523) B511523
theorem B341035 : Blo 338752 341035 := bstep (se 1 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 341035 = 511553) B511553
theorem B341047 : Blo 338752 341047 := bstep (se 1 (by rfl) ⟨255785, by rfl⟩ : syracuseStep 341047 = 511571) B511571
theorem B767051 : Blo 338752 767051 := bstep (se 1 (by rfl) ⟨575288, by rfl⟩ : syracuseStep 767051 = 1150577) B1150577
theorem B341067 : Blo 338752 341067 := bstep (se 1 (by rfl) ⟨255800, by rfl⟩ : syracuseStep 341067 = 511601) B511601
theorem B341079 : Blo 338752 341079 := bstep (se 1 (by rfl) ⟨255809, by rfl⟩ : syracuseStep 341079 = 511619) B511619
theorem B341099 : Blo 338752 341099 := bstep (se 1 (by rfl) ⟨255824, by rfl⟩ : syracuseStep 341099 = 511649) B511649
theorem B341111 : Blo 338752 341111 := bstep (se 1 (by rfl) ⟨255833, by rfl⟩ : syracuseStep 341111 = 511667) B511667
theorem B767105 : Blo 338752 767105 := bstep (se 2 (by rfl) ⟨287664, by rfl⟩ : syracuseStep 767105 = 575329) B575329
theorem B341131 : Blo 338752 341131 := bstep (se 1 (by rfl) ⟨255848, by rfl⟩ : syracuseStep 341131 = 511697) B511697
theorem B1291409 : Blo 338752 1291409 := bstep (se 2 (by rfl) ⟨484278, by rfl⟩ : syracuseStep 1291409 = 968557) B968557
theorem B341143 : Blo 338752 341143 := bstep (se 1 (by rfl) ⟨255857, by rfl⟩ : syracuseStep 341143 = 511715) B511715
theorem B341163 : Blo 338752 341163 := bstep (se 1 (by rfl) ⟨255872, by rfl⟩ : syracuseStep 341163 = 511745) B511745
theorem B2766001 : Blo 338752 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B341175 : Blo 338752 341175 := bstep (se 1 (by rfl) ⟨255881, by rfl⟩ : syracuseStep 341175 = 511763) B511763
theorem B341195 : Blo 338752 341195 := bstep (se 1 (by rfl) ⟨255896, by rfl⟩ : syracuseStep 341195 = 511793) B511793
theorem B341207 : Blo 338752 341207 := bstep (se 1 (by rfl) ⟨255905, by rfl⟩ : syracuseStep 341207 = 511811) B511811
theorem B341227 : Blo 338752 341227 := bstep (se 1 (by rfl) ⟨255920, by rfl⟩ : syracuseStep 341227 = 511841) B511841
theorem B341239 : Blo 338752 341239 := bstep (se 1 (by rfl) ⟨255929, by rfl⟩ : syracuseStep 341239 = 511859) B511859
theorem B341259 : Blo 338752 341259 := bstep (se 1 (by rfl) ⟨255944, by rfl⟩ : syracuseStep 341259 = 511889) B511889
theorem B341271 : Blo 338752 341271 := bstep (se 1 (by rfl) ⟨255953, by rfl⟩ : syracuseStep 341271 = 511907) B511907
theorem B341291 : Blo 338752 341291 := bstep (se 1 (by rfl) ⟨255968, by rfl⟩ : syracuseStep 341291 = 511937) B511937
theorem B341303 : Blo 338752 341303 := bstep (se 1 (by rfl) ⟨255977, by rfl⟩ : syracuseStep 341303 = 511955) B511955
theorem B341323 : Blo 338752 341323 := bstep (se 1 (by rfl) ⟨255992, by rfl⟩ : syracuseStep 341323 = 511985) B511985
theorem B341335 : Blo 338752 341335 := bstep (se 1 (by rfl) ⟨256001, by rfl⟩ : syracuseStep 341335 = 512003) B512003
theorem B767321 : Blo 338752 767321 := bstep (se 2 (by rfl) ⟨287745, by rfl⟩ : syracuseStep 767321 = 575491) B575491
theorem B341355 : Blo 338752 341355 := bstep (se 1 (by rfl) ⟨256016, by rfl⟩ : syracuseStep 341355 = 512033) B512033
theorem B341367 : Blo 338752 341367 := bstep (se 1 (by rfl) ⟨256025, by rfl⟩ : syracuseStep 341367 = 512051) B512051
theorem B341387 : Blo 338752 341387 := bstep (se 1 (by rfl) ⟨256040, by rfl⟩ : syracuseStep 341387 = 512081) B512081
theorem B341399 : Blo 338752 341399 := bstep (se 1 (by rfl) ⟨256049, by rfl⟩ : syracuseStep 341399 = 512099) B512099
theorem B865687 : Blo 338752 865687 := bstep (se 1 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 865687 = 1298531) B1298531
theorem B341419 : Blo 338752 341419 := bstep (se 1 (by rfl) ⟨256064, by rfl⟩ : syracuseStep 341419 = 512129) B512129
theorem B767411 : Blo 338752 767411 := bstep (se 1 (by rfl) ⟨575558, by rfl⟩ : syracuseStep 767411 = 1151117) B1151117
theorem B341431 : Blo 338752 341431 := bstep (se 1 (by rfl) ⟨256073, by rfl⟩ : syracuseStep 341431 = 512147) B512147
theorem B341451 : Blo 338752 341451 := bstep (se 1 (by rfl) ⟨256088, by rfl⟩ : syracuseStep 341451 = 512177) B512177
theorem B767447 : Blo 338752 767447 := bstep (se 1 (by rfl) ⟨575585, by rfl⟩ : syracuseStep 767447 = 1151171) B1151171
theorem B341463 : Blo 338752 341463 := bstep (se 1 (by rfl) ⟨256097, by rfl⟩ : syracuseStep 341463 = 512195) B512195
theorem B341483 : Blo 338752 341483 := bstep (se 1 (by rfl) ⟨256112, by rfl⟩ : syracuseStep 341483 = 512225) B512225
theorem B341495 : Blo 338752 341495 := bstep (se 1 (by rfl) ⟨256121, by rfl⟩ : syracuseStep 341495 = 512243) B512243
theorem B341515 : Blo 338752 341515 := bstep (se 1 (by rfl) ⟨256136, by rfl⟩ : syracuseStep 341515 = 512273) B512273
theorem B341527 : Blo 338752 341527 := bstep (se 1 (by rfl) ⟨256145, by rfl⟩ : syracuseStep 341527 = 512291) B512291
theorem B341547 : Blo 338752 341547 := bstep (se 1 (by rfl) ⟨256160, by rfl⟩ : syracuseStep 341547 = 512321) B512321
theorem B341559 : Blo 338752 341559 := bstep (se 1 (by rfl) ⟨256169, by rfl⟩ : syracuseStep 341559 = 512339) B512339
theorem B341579 : Blo 338752 341579 := bstep (se 1 (by rfl) ⟨256184, by rfl⟩ : syracuseStep 341579 = 512369) B512369
theorem B341591 : Blo 338752 341591 := bstep (se 1 (by rfl) ⟨256193, by rfl⟩ : syracuseStep 341591 = 512387) B512387
theorem B341611 : Blo 338752 341611 := bstep (se 1 (by rfl) ⟨256208, by rfl⟩ : syracuseStep 341611 = 512417) B512417
theorem B341623 : Blo 338752 341623 := bstep (se 1 (by rfl) ⟨256217, by rfl⟩ : syracuseStep 341623 = 512435) B512435
theorem B767627 : Blo 338752 767627 := bstep (se 1 (by rfl) ⟨575720, by rfl⟩ : syracuseStep 767627 = 1151441) B1151441
theorem B341643 : Blo 338752 341643 := bstep (se 1 (by rfl) ⟨256232, by rfl⟩ : syracuseStep 341643 = 512465) B512465
theorem B341655 : Blo 338752 341655 := bstep (se 1 (by rfl) ⟨256241, by rfl⟩ : syracuseStep 341655 = 512483) B512483
theorem B341675 : Blo 338752 341675 := bstep (se 1 (by rfl) ⟨256256, by rfl⟩ : syracuseStep 341675 = 512513) B512513
theorem B341687 : Blo 338752 341687 := bstep (se 1 (by rfl) ⟨256265, by rfl⟩ : syracuseStep 341687 = 512531) B512531
theorem B767681 : Blo 338752 767681 := bstep (se 2 (by rfl) ⟨287880, by rfl⟩ : syracuseStep 767681 = 575761) B575761
theorem B341707 : Blo 338752 341707 := bstep (se 1 (by rfl) ⟨256280, by rfl⟩ : syracuseStep 341707 = 512561) B512561
theorem B341719 : Blo 338752 341719 := bstep (se 1 (by rfl) ⟨256289, by rfl⟩ : syracuseStep 341719 = 512579) B512579
theorem B341739 : Blo 338752 341739 := bstep (se 1 (by rfl) ⟨256304, by rfl⟩ : syracuseStep 341739 = 512609) B512609
theorem B341751 : Blo 338752 341751 := bstep (se 1 (by rfl) ⟨256313, by rfl⟩ : syracuseStep 341751 = 512627) B512627
theorem B341771 : Blo 338752 341771 := bstep (se 1 (by rfl) ⟨256328, by rfl⟩ : syracuseStep 341771 = 512657) B512657
theorem B341783 : Blo 338752 341783 := bstep (se 1 (by rfl) ⟨256337, by rfl⟩ : syracuseStep 341783 = 512675) B512675
theorem B341803 : Blo 338752 341803 := bstep (se 1 (by rfl) ⟨256352, by rfl⟩ : syracuseStep 341803 = 512705) B512705
theorem B341815 : Blo 338752 341815 := bstep (se 1 (by rfl) ⟨256361, by rfl⟩ : syracuseStep 341815 = 512723) B512723
theorem B341835 : Blo 338752 341835 := bstep (se 1 (by rfl) ⟨256376, by rfl⟩ : syracuseStep 341835 = 512753) B512753
theorem B866123 : Blo 338752 866123 := bstep (se 1 (by rfl) ⟨649592, by rfl⟩ : syracuseStep 866123 = 1299185) B1299185
theorem B341847 : Blo 338752 341847 := bstep (se 1 (by rfl) ⟨256385, by rfl⟩ : syracuseStep 341847 = 512771) B512771
theorem B341867 : Blo 338752 341867 := bstep (se 1 (by rfl) ⟨256400, by rfl⟩ : syracuseStep 341867 = 512801) B512801
theorem B341879 : Blo 338752 341879 := bstep (se 1 (by rfl) ⟨256409, by rfl⟩ : syracuseStep 341879 = 512819) B512819
theorem B1947523 : Blo 338752 1947523 := bstep (se 1 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 1947523 = 2921285) B2921285
theorem B341899 : Blo 338752 341899 := bstep (se 1 (by rfl) ⟨256424, by rfl⟩ : syracuseStep 341899 = 512849) B512849
theorem B1292183 : Blo 338752 1292183 := bstep (se 1 (by rfl) ⟨969137, by rfl⟩ : syracuseStep 1292183 = 1938275) B1938275
theorem B341911 : Blo 338752 341911 := bstep (se 1 (by rfl) ⟨256433, by rfl⟩ : syracuseStep 341911 = 512867) B512867
theorem B767897 : Blo 338752 767897 := bstep (se 2 (by rfl) ⟨287961, by rfl⟩ : syracuseStep 767897 = 575923) B575923
theorem B341931 : Blo 338752 341931 := bstep (se 1 (by rfl) ⟨256448, by rfl⟩ : syracuseStep 341931 = 512897) B512897
theorem B341943 : Blo 338752 341943 := bstep (se 1 (by rfl) ⟨256457, by rfl⟩ : syracuseStep 341943 = 512915) B512915
theorem B341963 : Blo 338752 341963 := bstep (se 1 (by rfl) ⟨256472, by rfl⟩ : syracuseStep 341963 = 512945) B512945
theorem B341975 : Blo 338752 341975 := bstep (se 1 (by rfl) ⟨256481, by rfl⟩ : syracuseStep 341975 = 512963) B512963
theorem B341995 : Blo 338752 341995 := bstep (se 1 (by rfl) ⟨256496, by rfl⟩ : syracuseStep 341995 = 512993) B512993
theorem B767987 : Blo 338752 767987 := bstep (se 1 (by rfl) ⟨575990, by rfl⟩ : syracuseStep 767987 = 1151981) B1151981
theorem B342007 : Blo 338752 342007 := bstep (se 1 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 342007 = 513011) B513011
theorem B342027 : Blo 338752 342027 := bstep (se 1 (by rfl) ⟨256520, by rfl⟩ : syracuseStep 342027 = 513041) B513041
theorem B768023 : Blo 338752 768023 := bstep (se 1 (by rfl) ⟨576017, by rfl⟩ : syracuseStep 768023 = 1152035) B1152035
theorem B342039 : Blo 338752 342039 := bstep (se 1 (by rfl) ⟨256529, by rfl⟩ : syracuseStep 342039 = 513059) B513059
theorem B342059 : Blo 338752 342059 := bstep (se 1 (by rfl) ⟨256544, by rfl⟩ : syracuseStep 342059 = 513089) B513089
theorem B342071 : Blo 338752 342071 := bstep (se 1 (by rfl) ⟨256553, by rfl⟩ : syracuseStep 342071 = 513107) B513107
theorem B964673 : Blo 338752 964673 := bstep (se 2 (by rfl) ⟨361752, by rfl⟩ : syracuseStep 964673 = 723505) B723505
theorem B342091 : Blo 338752 342091 := bstep (se 1 (by rfl) ⟨256568, by rfl⟩ : syracuseStep 342091 = 513137) B513137
theorem B342103 : Blo 338752 342103 := bstep (se 1 (by rfl) ⟨256577, by rfl⟩ : syracuseStep 342103 = 513155) B513155
theorem B1292381 : Blo 338752 1292381 := bstep (se 3 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 1292381 = 484643) B484643
theorem B342123 : Blo 338752 342123 := bstep (se 1 (by rfl) ⟨256592, by rfl⟩ : syracuseStep 342123 = 513185) B513185
theorem B342135 : Blo 338752 342135 := bstep (se 1 (by rfl) ⟨256601, by rfl⟩ : syracuseStep 342135 = 513203) B513203
theorem B342155 : Blo 338752 342155 := bstep (se 1 (by rfl) ⟨256616, by rfl⟩ : syracuseStep 342155 = 513233) B513233
theorem B342167 : Blo 338752 342167 := bstep (se 1 (by rfl) ⟨256625, by rfl⟩ : syracuseStep 342167 = 513251) B513251
theorem B342187 : Blo 338752 342187 := bstep (se 1 (by rfl) ⟨256640, by rfl⟩ : syracuseStep 342187 = 513281) B513281
theorem B342199 : Blo 338752 342199 := bstep (se 1 (by rfl) ⟨256649, by rfl⟩ : syracuseStep 342199 = 513299) B513299
theorem B866497 : Blo 338752 866497 := bstep (se 2 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 866497 = 649873) B649873
theorem B768203 : Blo 338752 768203 := bstep (se 1 (by rfl) ⟨576152, by rfl⟩ : syracuseStep 768203 = 1152305) B1152305
theorem B342219 : Blo 338752 342219 := bstep (se 1 (by rfl) ⟨256664, by rfl⟩ : syracuseStep 342219 = 513329) B513329
theorem B342231 : Blo 338752 342231 := bstep (se 1 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 342231 = 513347) B513347
theorem B342251 : Blo 338752 342251 := bstep (se 1 (by rfl) ⟨256688, by rfl⟩ : syracuseStep 342251 = 513377) B513377
theorem B342263 : Blo 338752 342263 := bstep (se 1 (by rfl) ⟨256697, by rfl⟩ : syracuseStep 342263 = 513395) B513395
theorem B768257 : Blo 338752 768257 := bstep (se 2 (by rfl) ⟨288096, by rfl⟩ : syracuseStep 768257 = 576193) B576193
theorem B342283 : Blo 338752 342283 := bstep (se 1 (by rfl) ⟨256712, by rfl⟩ : syracuseStep 342283 = 513425) B513425
theorem B342295 : Blo 338752 342295 := bstep (se 1 (by rfl) ⟨256721, by rfl⟩ : syracuseStep 342295 = 513443) B513443
theorem B342315 : Blo 338752 342315 := bstep (se 1 (by rfl) ⟨256736, by rfl⟩ : syracuseStep 342315 = 513473) B513473
theorem B342327 : Blo 338752 342327 := bstep (se 1 (by rfl) ⟨256745, by rfl⟩ : syracuseStep 342327 = 513491) B513491
theorem B342347 : Blo 338752 342347 := bstep (se 1 (by rfl) ⟨256760, by rfl⟩ : syracuseStep 342347 = 513521) B513521
theorem B342359 : Blo 338752 342359 := bstep (se 1 (by rfl) ⟨256769, by rfl⟩ : syracuseStep 342359 = 513539) B513539
theorem B342379 : Blo 338752 342379 := bstep (se 1 (by rfl) ⟨256784, by rfl⟩ : syracuseStep 342379 = 513569) B513569
theorem B342391 : Blo 338752 342391 := bstep (se 1 (by rfl) ⟨256793, by rfl⟩ : syracuseStep 342391 = 513587) B513587
theorem B342411 : Blo 338752 342411 := bstep (se 1 (by rfl) ⟨256808, by rfl⟩ : syracuseStep 342411 = 513617) B513617
theorem B571799 : Blo 338752 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B342423 : Blo 338752 342423 := bstep (se 1 (by rfl) ⟨256817, by rfl⟩ : syracuseStep 342423 = 513635) B513635
theorem B342443 : Blo 338752 342443 := bstep (se 1 (by rfl) ⟨256832, by rfl⟩ : syracuseStep 342443 = 513665) B513665
theorem B342455 : Blo 338752 342455 := bstep (se 1 (by rfl) ⟨256841, by rfl⟩ : syracuseStep 342455 = 513683) B513683
theorem B342475 : Blo 338752 342475 := bstep (se 1 (by rfl) ⟨256856, by rfl⟩ : syracuseStep 342475 = 513713) B513713
theorem B342487 : Blo 338752 342487 := bstep (se 1 (by rfl) ⟨256865, by rfl⟩ : syracuseStep 342487 = 513731) B513731
theorem B768473 : Blo 338752 768473 := bstep (se 2 (by rfl) ⟨288177, by rfl⟩ : syracuseStep 768473 = 576355) B576355
theorem B342507 : Blo 338752 342507 := bstep (se 1 (by rfl) ⟨256880, by rfl⟩ : syracuseStep 342507 = 513761) B513761
theorem B342519 : Blo 338752 342519 := bstep (se 1 (by rfl) ⟨256889, by rfl⟩ : syracuseStep 342519 = 513779) B513779
theorem B342539 : Blo 338752 342539 := bstep (se 1 (by rfl) ⟨256904, by rfl⟩ : syracuseStep 342539 = 513809) B513809
theorem B571927 : Blo 338752 571927 := bstep (se 1 (by rfl) ⟨428945, by rfl⟩ : syracuseStep 571927 = 857891) B857891
theorem B1227287 : Blo 338752 1227287 := bstep (se 1 (by rfl) ⟨920465, by rfl⟩ : syracuseStep 1227287 = 1840931) B1840931
theorem B1456663 : Blo 338752 1456663 := bstep (se 1 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 1456663 = 2184995) B2184995
theorem B342551 : Blo 338752 342551 := bstep (se 1 (by rfl) ⟨256913, by rfl⟩ : syracuseStep 342551 = 513827) B513827
theorem B342571 : Blo 338752 342571 := bstep (se 1 (by rfl) ⟨256928, by rfl⟩ : syracuseStep 342571 = 513857) B513857
theorem B768563 : Blo 338752 768563 := bstep (se 1 (by rfl) ⟨576422, by rfl⟩ : syracuseStep 768563 = 1152845) B1152845
theorem B342583 : Blo 338752 342583 := bstep (se 1 (by rfl) ⟨256937, by rfl⟩ : syracuseStep 342583 = 513875) B513875
theorem B342603 : Blo 338752 342603 := bstep (se 1 (by rfl) ⟨256952, by rfl⟩ : syracuseStep 342603 = 513905) B513905
theorem B768599 : Blo 338752 768599 := bstep (se 1 (by rfl) ⟨576449, by rfl⟩ : syracuseStep 768599 = 1152899) B1152899
theorem B342615 : Blo 338752 342615 := bstep (se 1 (by rfl) ⟨256961, by rfl⟩ : syracuseStep 342615 = 513923) B513923
theorem B342635 : Blo 338752 342635 := bstep (se 1 (by rfl) ⟨256976, by rfl⟩ : syracuseStep 342635 = 513953) B513953
theorem B703091 : Blo 338752 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B342647 : Blo 338752 342647 := bstep (se 1 (by rfl) ⟨256985, by rfl⟩ : syracuseStep 342647 = 513971) B513971
theorem B342667 : Blo 338752 342667 := bstep (se 1 (by rfl) ⟨257000, by rfl⟩ : syracuseStep 342667 = 514001) B514001
theorem B342679 : Blo 338752 342679 := bstep (se 1 (by rfl) ⟨257009, by rfl⟩ : syracuseStep 342679 = 514019) B514019
theorem B342699 : Blo 338752 342699 := bstep (se 1 (by rfl) ⟨257024, by rfl⟩ : syracuseStep 342699 = 514049) B514049
theorem B342711 : Blo 338752 342711 := bstep (se 1 (by rfl) ⟨257033, by rfl⟩ : syracuseStep 342711 = 514067) B514067
theorem B342731 : Blo 338752 342731 := bstep (se 1 (by rfl) ⟨257048, by rfl⟩ : syracuseStep 342731 = 514097) B514097
theorem B342743 : Blo 338752 342743 := bstep (se 1 (by rfl) ⟨257057, by rfl⟩ : syracuseStep 342743 = 514115) B514115
theorem B768779 : Blo 338752 768779 := bstep (se 1 (by rfl) ⟨576584, by rfl⟩ : syracuseStep 768779 = 1153169) B1153169
theorem B867095 : Blo 338752 867095 := bstep (se 1 (by rfl) ⟨650321, by rfl⟩ : syracuseStep 867095 = 1300643) B1300643
theorem B768833 : Blo 338752 768833 := bstep (se 2 (by rfl) ⟨288312, by rfl⟩ : syracuseStep 768833 = 576625) B576625
theorem B1948481 : Blo 338752 1948481 := bstep (se 2 (by rfl) ⟨730680, by rfl⟩ : syracuseStep 1948481 = 1461361) B1461361
theorem B769049 : Blo 338752 769049 := bstep (se 2 (by rfl) ⟨288393, by rfl⟩ : syracuseStep 769049 = 576787) B576787
theorem B2964545 : Blo 338752 2964545 := bstep (se 2 (by rfl) ⟨1111704, by rfl⟩ : syracuseStep 2964545 = 2223409) B2223409
theorem B769139 : Blo 338752 769139 := bstep (se 1 (by rfl) ⟨576854, by rfl⟩ : syracuseStep 769139 = 1153709) B1153709
theorem B572555 : Blo 338752 572555 := bstep (se 1 (by rfl) ⟨429416, by rfl⟩ : syracuseStep 572555 = 858833) B858833
theorem B769175 : Blo 338752 769175 := bstep (se 1 (by rfl) ⟨576881, by rfl⟩ : syracuseStep 769175 = 1153763) B1153763
theorem B572683 : Blo 338752 572683 := bstep (se 1 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 572683 = 859025) B859025
theorem B769355 : Blo 338752 769355 := bstep (se 1 (by rfl) ⟨577016, by rfl⟩ : syracuseStep 769355 = 1154033) B1154033
theorem B769409 : Blo 338752 769409 := bstep (se 2 (by rfl) ⟨288528, by rfl⟩ : syracuseStep 769409 = 577057) B577057
theorem B572825 : Blo 338752 572825 := bstep (se 2 (by rfl) ⟨214809, by rfl⟩ : syracuseStep 572825 = 429619) B429619
theorem B1555985 : Blo 338752 1555985 := bstep (se 2 (by rfl) ⟨583494, by rfl⟩ : syracuseStep 1555985 = 1166989) B1166989
theorem B572953 : Blo 338752 572953 := bstep (se 2 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 572953 = 429715) B429715
theorem B769625 : Blo 338752 769625 := bstep (se 2 (by rfl) ⟨288609, by rfl⟩ : syracuseStep 769625 = 577219) B577219
theorem B3259997 : Blo 338752 3259997 := bstep (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) B1222499
theorem B769715 : Blo 338752 769715 := bstep (se 1 (by rfl) ⟨577286, by rfl⟩ : syracuseStep 769715 = 1154573) B1154573
theorem B769751 : Blo 338752 769751 := bstep (se 1 (by rfl) ⟨577313, by rfl⟩ : syracuseStep 769751 = 1154627) B1154627
theorem B769931 : Blo 338752 769931 := bstep (se 1 (by rfl) ⟨577448, by rfl⟩ : syracuseStep 769931 = 1154897) B1154897
theorem B769985 : Blo 338752 769985 := bstep (se 2 (by rfl) ⟨288744, by rfl⟩ : syracuseStep 769985 = 577489) B577489
theorem B1294339 : Blo 338752 1294339 := bstep (se 1 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 1294339 = 1941509) B1941509
theorem B573527 : Blo 338752 573527 := bstep (se 1 (by rfl) ⟨430145, by rfl⟩ : syracuseStep 573527 = 860291) B860291
theorem B966745 : Blo 338752 966745 := bstep (se 2 (by rfl) ⟨362529, by rfl⟩ : syracuseStep 966745 = 725059) B725059
theorem B770201 : Blo 338752 770201 := bstep (se 2 (by rfl) ⟨288825, by rfl⟩ : syracuseStep 770201 = 577651) B577651
theorem B573655 : Blo 338752 573655 := bstep (se 1 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 573655 = 860483) B860483
theorem B344299 : Blo 338752 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B770291 : Blo 338752 770291 := bstep (se 1 (by rfl) ⟨577718, by rfl⟩ : syracuseStep 770291 = 1155437) B1155437
theorem B770327 : Blo 338752 770327 := bstep (se 1 (by rfl) ⟨577745, by rfl⟩ : syracuseStep 770327 = 1155491) B1155491
theorem B1294643 : Blo 338752 1294643 := bstep (se 1 (by rfl) ⟨970982, by rfl⟩ : syracuseStep 1294643 = 1941965) B1941965
theorem B508235 : Blo 338752 508235 := bstep (se 1 (by rfl) ⟨381176, by rfl⟩ : syracuseStep 508235 = 762353) B762353
theorem B508247 : Blo 338752 508247 := bstep (se 1 (by rfl) ⟨381185, by rfl⟩ : syracuseStep 508247 = 762371) B762371
theorem B508313 : Blo 338752 508313 := bstep (se 2 (by rfl) ⟨190617, by rfl⟩ : syracuseStep 508313 = 381235) B381235
theorem B770507 : Blo 338752 770507 := bstep (se 1 (by rfl) ⟨577880, by rfl⟩ : syracuseStep 770507 = 1155761) B1155761
theorem B967133 : Blo 338752 967133 := bstep (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) B362675
theorem B770561 : Blo 338752 770561 := bstep (se 2 (by rfl) ⟨288960, by rfl⟩ : syracuseStep 770561 = 577921) B577921
theorem B508427 : Blo 338752 508427 := bstep (se 1 (by rfl) ⟨381320, by rfl⟩ : syracuseStep 508427 = 762641) B762641
theorem B508439 : Blo 338752 508439 := bstep (se 1 (by rfl) ⟨381329, by rfl⟩ : syracuseStep 508439 = 762659) B762659
theorem B1229363 : Blo 338752 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B508505 : Blo 338752 508505 := bstep (se 2 (by rfl) ⟨190689, by rfl⟩ : syracuseStep 508505 = 381379) B381379
theorem B1720925 : Blo 338752 1720925 := bstep (se 3 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 1720925 = 645347) B645347
theorem B508619 : Blo 338752 508619 := bstep (se 1 (by rfl) ⟨381464, by rfl⟩ : syracuseStep 508619 = 762929) B762929
theorem B508631 : Blo 338752 508631 := bstep (se 1 (by rfl) ⟨381473, by rfl⟩ : syracuseStep 508631 = 762947) B762947
theorem B770777 : Blo 338752 770777 := bstep (se 2 (by rfl) ⟨289041, by rfl⟩ : syracuseStep 770777 = 578083) B578083
theorem B508697 : Blo 338752 508697 := bstep (se 2 (by rfl) ⟨190761, by rfl⟩ : syracuseStep 508697 = 381523) B381523
theorem B1557299 : Blo 338752 1557299 := bstep (se 1 (by rfl) ⟨1167974, by rfl⟩ : syracuseStep 1557299 = 2335949) B2335949
theorem B770867 : Blo 338752 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B2442059 : Blo 338752 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B574283 : Blo 338752 574283 := bstep (se 1 (by rfl) ⟨430712, by rfl⟩ : syracuseStep 574283 = 861425) B861425
theorem B770903 : Blo 338752 770903 := bstep (se 1 (by rfl) ⟨578177, by rfl⟩ : syracuseStep 770903 = 1156355) B1156355
theorem B508811 : Blo 338752 508811 := bstep (se 1 (by rfl) ⟨381608, by rfl⟩ : syracuseStep 508811 = 763217) B763217
theorem B508823 : Blo 338752 508823 := bstep (se 1 (by rfl) ⟨381617, by rfl⟩ : syracuseStep 508823 = 763235) B763235
theorem B1295297 : Blo 338752 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B574411 : Blo 338752 574411 := bstep (se 1 (by rfl) ⟨430808, by rfl⟩ : syracuseStep 574411 = 861617) B861617
theorem B508889 : Blo 338752 508889 := bstep (se 2 (by rfl) ⟨190833, by rfl⟩ : syracuseStep 508889 = 381667) B381667
theorem B771083 : Blo 338752 771083 := bstep (se 1 (by rfl) ⟨578312, by rfl⟩ : syracuseStep 771083 = 1156625) B1156625
theorem B1557521 : Blo 338752 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B1852433 : Blo 338752 1852433 := bstep (se 2 (by rfl) ⟨694662, by rfl⟩ : syracuseStep 1852433 = 1389325) B1389325
theorem B771137 : Blo 338752 771137 := bstep (se 2 (by rfl) ⟨289176, by rfl⟩ : syracuseStep 771137 = 578353) B578353
theorem B509003 : Blo 338752 509003 := bstep (se 1 (by rfl) ⟨381752, by rfl⟩ : syracuseStep 509003 = 763505) B763505
theorem B5817419 : Blo 338752 5817419 := bstep (se 1 (by rfl) ⟨4363064, by rfl⟩ : syracuseStep 5817419 = 8726129) B8726129
theorem B509015 : Blo 338752 509015 := bstep (se 1 (by rfl) ⟨381761, by rfl⟩ : syracuseStep 509015 = 763523) B763523
theorem B574553 : Blo 338752 574553 := bstep (se 2 (by rfl) ⟨215457, by rfl⟩ : syracuseStep 574553 = 430915) B430915
theorem B1557593 : Blo 338752 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B509081 : Blo 338752 509081 := bstep (se 2 (by rfl) ⟨190905, by rfl⟩ : syracuseStep 509081 = 381811) B381811
theorem B574681 : Blo 338752 574681 := bstep (se 2 (by rfl) ⟨215505, by rfl⟩ : syracuseStep 574681 = 431011) B431011
theorem B509195 : Blo 338752 509195 := bstep (se 1 (by rfl) ⟨381896, by rfl⟩ : syracuseStep 509195 = 763793) B763793
theorem B509207 : Blo 338752 509207 := bstep (se 1 (by rfl) ⟨381905, by rfl⟩ : syracuseStep 509207 = 763811) B763811
theorem B509273 : Blo 338752 509273 := bstep (se 2 (by rfl) ⟨190977, by rfl⟩ : syracuseStep 509273 = 381955) B381955
theorem B1459549 : Blo 338752 1459549 := bstep (se 3 (by rfl) ⟨273665, by rfl⟩ : syracuseStep 1459549 = 547331) B547331
theorem B509387 : Blo 338752 509387 := bstep (se 1 (by rfl) ⟨382040, by rfl⟩ : syracuseStep 509387 = 764081) B764081
theorem B509399 : Blo 338752 509399 := bstep (se 1 (by rfl) ⟨382049, by rfl⟩ : syracuseStep 509399 = 764099) B764099
theorem B509465 : Blo 338752 509465 := bstep (se 2 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 509465 = 382099) B382099
theorem B509579 : Blo 338752 509579 := bstep (se 1 (by rfl) ⟨382184, by rfl⟩ : syracuseStep 509579 = 764369) B764369
theorem B509591 : Blo 338752 509591 := bstep (se 1 (by rfl) ⟨382193, by rfl⟩ : syracuseStep 509591 = 764387) B764387
theorem B509657 : Blo 338752 509657 := bstep (se 2 (by rfl) ⟨191121, by rfl⟩ : syracuseStep 509657 = 382243) B382243
theorem B575255 : Blo 338752 575255 := bstep (se 1 (by rfl) ⟨431441, by rfl⟩ : syracuseStep 575255 = 862883) B862883
theorem B509771 : Blo 338752 509771 := bstep (se 1 (by rfl) ⟨382328, by rfl⟩ : syracuseStep 509771 = 764657) B764657
theorem B509783 : Blo 338752 509783 := bstep (se 1 (by rfl) ⟨382337, by rfl⟩ : syracuseStep 509783 = 764675) B764675
theorem B575383 : Blo 338752 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B509849 : Blo 338752 509849 := bstep (se 2 (by rfl) ⟨191193, by rfl⟩ : syracuseStep 509849 = 382387) B382387
theorem B2574341 : Blo 338752 2574341 := bstep (se 4 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 2574341 = 482689) B482689
theorem B509963 : Blo 338752 509963 := bstep (se 1 (by rfl) ⟨382472, by rfl⟩ : syracuseStep 509963 = 764945) B764945
theorem B509975 : Blo 338752 509975 := bstep (se 1 (by rfl) ⟨382481, by rfl⟩ : syracuseStep 509975 = 764963) B764963
theorem B510041 : Blo 338752 510041 := bstep (se 2 (by rfl) ⟨191265, by rfl⟩ : syracuseStep 510041 = 382531) B382531
theorem B1034333 : Blo 338752 1034333 := bstep (se 3 (by rfl) ⟨193937, by rfl⟩ : syracuseStep 1034333 = 387875) B387875
theorem B1460369 : Blo 338752 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B1296557 : Blo 338752 1296557 := bstep (se 3 (by rfl) ⟨243104, by rfl⟩ : syracuseStep 1296557 = 486209) B486209
theorem B510155 : Blo 338752 510155 := bstep (se 1 (by rfl) ⟨382616, by rfl⟩ : syracuseStep 510155 = 765233) B765233
theorem B1296587 : Blo 338752 1296587 := bstep (se 1 (by rfl) ⟨972440, by rfl⟩ : syracuseStep 1296587 = 1944881) B1944881
theorem B510167 : Blo 338752 510167 := bstep (se 1 (by rfl) ⟨382625, by rfl⟩ : syracuseStep 510167 = 765251) B765251
theorem B510233 : Blo 338752 510233 := bstep (se 2 (by rfl) ⟨191337, by rfl⟩ : syracuseStep 510233 = 382675) B382675
theorem B346423 : Blo 338752 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B510347 : Blo 338752 510347 := bstep (se 1 (by rfl) ⟨382760, by rfl⟩ : syracuseStep 510347 = 765521) B765521
theorem B510359 : Blo 338752 510359 := bstep (se 1 (by rfl) ⟨382769, by rfl⟩ : syracuseStep 510359 = 765539) B765539
theorem B510425 : Blo 338752 510425 := bstep (se 2 (by rfl) ⟨191409, by rfl⟩ : syracuseStep 510425 = 382819) B382819
theorem B576011 : Blo 338752 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B543257 : Blo 338752 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B510539 : Blo 338752 510539 := bstep (se 1 (by rfl) ⟨382904, by rfl⟩ : syracuseStep 510539 = 765809) B765809
theorem B510551 : Blo 338752 510551 := bstep (se 1 (by rfl) ⟨382913, by rfl⟩ : syracuseStep 510551 = 765827) B765827
theorem B576139 : Blo 338752 576139 := bstep (se 1 (by rfl) ⟨432104, by rfl⟩ : syracuseStep 576139 = 864209) B864209
theorem B1723031 : Blo 338752 1723031 := bstep (se 1 (by rfl) ⟨1292273, by rfl⟩ : syracuseStep 1723031 = 2584547) B2584547
theorem B510617 : Blo 338752 510617 := bstep (se 2 (by rfl) ⟨191481, by rfl⟩ : syracuseStep 510617 = 382963) B382963
theorem B543449 : Blo 338752 543449 := bstep (se 2 (by rfl) ⟨203793, by rfl⟩ : syracuseStep 543449 = 407587) B407587
theorem B510731 : Blo 338752 510731 := bstep (se 1 (by rfl) ⟨383048, by rfl⟩ : syracuseStep 510731 = 766097) B766097
theorem B510743 : Blo 338752 510743 := bstep (se 1 (by rfl) ⟨383057, by rfl⟩ : syracuseStep 510743 = 766115) B766115
theorem B576281 : Blo 338752 576281 := bstep (se 2 (by rfl) ⟨216105, by rfl⟩ : syracuseStep 576281 = 432211) B432211
theorem B1461037 : Blo 338752 1461037 := bstep (se 3 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 1461037 = 547889) B547889
theorem B510809 : Blo 338752 510809 := bstep (se 2 (by rfl) ⟨191553, by rfl⟩ : syracuseStep 510809 = 383107) B383107
theorem B1297241 : Blo 338752 1297241 := bstep (se 2 (by rfl) ⟨486465, by rfl⟩ : syracuseStep 1297241 = 972931) B972931
theorem B576409 : Blo 338752 576409 := bstep (se 2 (by rfl) ⟨216153, by rfl⟩ : syracuseStep 576409 = 432307) B432307
theorem B510923 : Blo 338752 510923 := bstep (se 1 (by rfl) ⟨383192, by rfl⟩ : syracuseStep 510923 = 766385) B766385
theorem B510935 : Blo 338752 510935 := bstep (se 1 (by rfl) ⟨383201, by rfl⟩ : syracuseStep 510935 = 766403) B766403
theorem B511001 : Blo 338752 511001 := bstep (se 2 (by rfl) ⟨191625, by rfl⟩ : syracuseStep 511001 = 383251) B383251
theorem B511115 : Blo 338752 511115 := bstep (se 1 (by rfl) ⟨383336, by rfl⟩ : syracuseStep 511115 = 766673) B766673
theorem B511127 : Blo 338752 511127 := bstep (se 1 (by rfl) ⟨383345, by rfl⟩ : syracuseStep 511127 = 766691) B766691
theorem B1297559 : Blo 338752 1297559 := bstep (se 1 (by rfl) ⟨973169, by rfl⟩ : syracuseStep 1297559 = 1946339) B1946339
theorem B2608307 : Blo 338752 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B511193 : Blo 338752 511193 := bstep (se 2 (by rfl) ⟨191697, by rfl⟩ : syracuseStep 511193 = 383395) B383395
theorem B1232131 : Blo 338752 1232131 := bstep (se 1 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 1232131 = 1848197) B1848197
theorem B970049 : Blo 338752 970049 := bstep (se 2 (by rfl) ⟨363768, by rfl⟩ : syracuseStep 970049 = 727537) B727537
theorem B511307 : Blo 338752 511307 := bstep (se 1 (by rfl) ⟨383480, by rfl⟩ : syracuseStep 511307 = 766961) B766961
theorem B511319 : Blo 338752 511319 := bstep (se 1 (by rfl) ⟨383489, by rfl⟩ : syracuseStep 511319 = 766979) B766979
theorem B707969 : Blo 338752 707969 := bstep (se 2 (by rfl) ⟨265488, by rfl⟩ : syracuseStep 707969 = 530977) B530977
theorem B1461635 : Blo 338752 1461635 := bstep (se 1 (by rfl) ⟨1096226, by rfl⟩ : syracuseStep 1461635 = 2192453) B2192453
theorem B511385 : Blo 338752 511385 := bstep (se 2 (by rfl) ⟨191769, by rfl⟩ : syracuseStep 511385 = 383539) B383539
theorem B970163 : Blo 338752 970163 := bstep (se 1 (by rfl) ⟨727622, by rfl⟩ : syracuseStep 970163 = 1455245) B1455245
theorem B576983 : Blo 338752 576983 := bstep (se 1 (by rfl) ⟨432737, by rfl⟩ : syracuseStep 576983 = 865475) B865475
theorem B511499 : Blo 338752 511499 := bstep (se 1 (by rfl) ⟨383624, by rfl⟩ : syracuseStep 511499 = 767249) B767249
theorem B511511 : Blo 338752 511511 := bstep (se 1 (by rfl) ⟨383633, by rfl⟩ : syracuseStep 511511 = 767267) B767267
theorem B577111 : Blo 338752 577111 := bstep (se 1 (by rfl) ⟨432833, by rfl⟩ : syracuseStep 577111 = 865667) B865667
theorem B511577 : Blo 338752 511577 := bstep (se 2 (by rfl) ⟨191841, by rfl⟩ : syracuseStep 511577 = 383683) B383683
theorem B511691 : Blo 338752 511691 := bstep (se 1 (by rfl) ⟨383768, by rfl⟩ : syracuseStep 511691 = 767537) B767537
theorem B511703 : Blo 338752 511703 := bstep (se 1 (by rfl) ⟨383777, by rfl⟩ : syracuseStep 511703 = 767555) B767555
theorem B511769 : Blo 338752 511769 := bstep (se 2 (by rfl) ⟨191913, by rfl⟩ : syracuseStep 511769 = 383827) B383827
theorem B1298227 : Blo 338752 1298227 := bstep (se 1 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 1298227 = 1947341) B1947341
theorem B511883 : Blo 338752 511883 := bstep (se 1 (by rfl) ⟨383912, by rfl⟩ : syracuseStep 511883 = 767825) B767825
theorem B511895 : Blo 338752 511895 := bstep (se 1 (by rfl) ⟨383921, by rfl⟩ : syracuseStep 511895 = 767843) B767843
theorem B1560493 : Blo 338752 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B3887027 : Blo 338752 3887027 := bstep (se 1 (by rfl) ⟨2915270, by rfl⟩ : syracuseStep 3887027 = 5830541) B5830541
theorem B511961 : Blo 338752 511961 := bstep (se 2 (by rfl) ⟨191985, by rfl⟩ : syracuseStep 511961 = 383971) B383971
theorem B512075 : Blo 338752 512075 := bstep (se 1 (by rfl) ⟨384056, by rfl⟩ : syracuseStep 512075 = 768113) B768113
theorem B512087 : Blo 338752 512087 := bstep (se 1 (by rfl) ⟨384065, by rfl⟩ : syracuseStep 512087 = 768131) B768131
theorem B512153 : Blo 338752 512153 := bstep (se 2 (by rfl) ⟨192057, by rfl⟩ : syracuseStep 512153 = 384115) B384115
theorem B577739 : Blo 338752 577739 := bstep (se 1 (by rfl) ⟨433304, by rfl⟩ : syracuseStep 577739 = 866609) B866609
theorem B381163 : Blo 338752 381163 := bstep (se 1 (by rfl) ⟨285872, by rfl⟩ : syracuseStep 381163 = 571745) B571745
theorem B512267 : Blo 338752 512267 := bstep (se 1 (by rfl) ⟨384200, by rfl⟩ : syracuseStep 512267 = 768401) B768401
theorem B512279 : Blo 338752 512279 := bstep (se 1 (by rfl) ⟨384209, by rfl⟩ : syracuseStep 512279 = 768419) B768419
theorem B643403 : Blo 338752 643403 := bstep (se 1 (by rfl) ⟨482552, by rfl⟩ : syracuseStep 643403 = 965105) B965105
theorem B577867 : Blo 338752 577867 := bstep (se 1 (by rfl) ⟨433400, by rfl⟩ : syracuseStep 577867 = 866801) B866801
theorem B381271 : Blo 338752 381271 := bstep (se 1 (by rfl) ⟨285953, by rfl⟩ : syracuseStep 381271 = 571907) B571907
theorem B512345 : Blo 338752 512345 := bstep (se 2 (by rfl) ⟨192129, by rfl⟩ : syracuseStep 512345 = 384259) B384259
theorem B643457 : Blo 338752 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B2576771 : Blo 338752 2576771 := bstep (se 1 (by rfl) ⟨1932578, by rfl⟩ : syracuseStep 2576771 = 3865157) B3865157
theorem B512459 : Blo 338752 512459 := bstep (se 1 (by rfl) ⟨384344, by rfl⟩ : syracuseStep 512459 = 768689) B768689
theorem B512471 : Blo 338752 512471 := bstep (se 1 (by rfl) ⟨384353, by rfl⟩ : syracuseStep 512471 = 768707) B768707
theorem B578009 : Blo 338752 578009 := bstep (se 2 (by rfl) ⟨216753, by rfl⟩ : syracuseStep 578009 = 433507) B433507
theorem B938461 : Blo 338752 938461 := bstep (se 3 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 938461 = 351923) B351923
theorem B381451 : Blo 338752 381451 := bstep (se 1 (by rfl) ⟨286088, by rfl⟩ : syracuseStep 381451 = 572177) B572177
theorem B512537 : Blo 338752 512537 := bstep (se 2 (by rfl) ⟨192201, by rfl⟩ : syracuseStep 512537 = 384403) B384403
theorem B578137 : Blo 338752 578137 := bstep (se 2 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 578137 = 433603) B433603
theorem B381559 : Blo 338752 381559 := bstep (se 1 (by rfl) ⟨286169, by rfl⟩ : syracuseStep 381559 = 572339) B572339
theorem B512651 : Blo 338752 512651 := bstep (se 1 (by rfl) ⟨384488, by rfl⟩ : syracuseStep 512651 = 768977) B768977
theorem B512663 : Blo 338752 512663 := bstep (se 1 (by rfl) ⟨384497, by rfl⟩ : syracuseStep 512663 = 768995) B768995
theorem B1233559 : Blo 338752 1233559 := bstep (se 1 (by rfl) ⟨925169, by rfl⟩ : syracuseStep 1233559 = 1850339) B1850339
theorem B512729 : Blo 338752 512729 := bstep (se 2 (by rfl) ⟨192273, by rfl⟩ : syracuseStep 512729 = 384547) B384547
theorem B381739 : Blo 338752 381739 := bstep (se 1 (by rfl) ⟨286304, by rfl⟩ : syracuseStep 381739 = 572609) B572609
theorem B512843 : Blo 338752 512843 := bstep (se 1 (by rfl) ⟨384632, by rfl⟩ : syracuseStep 512843 = 769265) B769265
theorem B512855 : Blo 338752 512855 := bstep (se 1 (by rfl) ⟨384641, by rfl⟩ : syracuseStep 512855 = 769283) B769283
theorem B381847 : Blo 338752 381847 := bstep (se 1 (by rfl) ⟨286385, by rfl⟩ : syracuseStep 381847 = 572771) B572771
theorem B512921 : Blo 338752 512921 := bstep (se 2 (by rfl) ⟨192345, by rfl⟩ : syracuseStep 512921 = 384691) B384691
theorem B513035 : Blo 338752 513035 := bstep (se 1 (by rfl) ⟨384776, by rfl⟩ : syracuseStep 513035 = 769553) B769553
theorem B1299473 : Blo 338752 1299473 := bstep (se 2 (by rfl) ⟨487302, by rfl⟩ : syracuseStep 1299473 = 974605) B974605
theorem B513047 : Blo 338752 513047 := bstep (se 1 (by rfl) ⟨384785, by rfl⟩ : syracuseStep 513047 = 769571) B769571
theorem B382027 : Blo 338752 382027 := bstep (se 1 (by rfl) ⟨286520, by rfl⟩ : syracuseStep 382027 = 573041) B573041
theorem B513113 : Blo 338752 513113 := bstep (se 2 (by rfl) ⟨192417, by rfl⟩ : syracuseStep 513113 = 384835) B384835
theorem B382135 : Blo 338752 382135 := bstep (se 1 (by rfl) ⟨286601, by rfl⟩ : syracuseStep 382135 = 573203) B573203
theorem B513227 : Blo 338752 513227 := bstep (se 1 (by rfl) ⟨384920, by rfl⟩ : syracuseStep 513227 = 769841) B769841
theorem B513239 : Blo 338752 513239 := bstep (se 1 (by rfl) ⟨384929, by rfl⟩ : syracuseStep 513239 = 769859) B769859
theorem B644375 : Blo 338752 644375 := bstep (se 1 (by rfl) ⟨483281, by rfl⟩ : syracuseStep 644375 = 966563) B966563
theorem B513305 : Blo 338752 513305 := bstep (se 2 (by rfl) ⟨192489, by rfl⟩ : syracuseStep 513305 = 384979) B384979
theorem B3888485 : Blo 338752 3888485 := bstep (se 4 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 3888485 = 729091) B729091
theorem B382315 : Blo 338752 382315 := bstep (se 1 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 382315 = 573473) B573473
theorem B513419 : Blo 338752 513419 := bstep (se 1 (by rfl) ⟨385064, by rfl⟩ : syracuseStep 513419 = 770129) B770129
theorem B513431 : Blo 338752 513431 := bstep (se 1 (by rfl) ⟨385073, by rfl⟩ : syracuseStep 513431 = 770147) B770147
theorem B775577 : Blo 338752 775577 := bstep (se 2 (by rfl) ⟨290841, by rfl⟩ : syracuseStep 775577 = 581683) B581683
theorem B1234379 : Blo 338752 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B382423 : Blo 338752 382423 := bstep (se 1 (by rfl) ⟨286817, by rfl⟩ : syracuseStep 382423 = 573635) B573635
theorem B513497 : Blo 338752 513497 := bstep (se 2 (by rfl) ⟨192561, by rfl⟩ : syracuseStep 513497 = 385123) B385123
theorem B513611 : Blo 338752 513611 := bstep (se 1 (by rfl) ⟨385208, by rfl⟩ : syracuseStep 513611 = 770417) B770417
theorem B513623 : Blo 338752 513623 := bstep (se 1 (by rfl) ⟨385217, by rfl⟩ : syracuseStep 513623 = 770435) B770435
theorem B382603 : Blo 338752 382603 := bstep (se 1 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 382603 = 573905) B573905
theorem B611993 : Blo 338752 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B513689 : Blo 338752 513689 := bstep (se 2 (by rfl) ⟨192633, by rfl⟩ : syracuseStep 513689 = 385267) B385267
theorem B1169099 : Blo 338752 1169099 := bstep (se 1 (by rfl) ⟨876824, by rfl⟩ : syracuseStep 1169099 = 1753649) B1753649
theorem B1300171 : Blo 338752 1300171 := bstep (se 1 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 1300171 = 1950257) B1950257
theorem B382711 : Blo 338752 382711 := bstep (se 1 (by rfl) ⟨287033, by rfl⟩ : syracuseStep 382711 = 574067) B574067
theorem B513803 : Blo 338752 513803 := bstep (se 1 (by rfl) ⟨385352, by rfl⟩ : syracuseStep 513803 = 770705) B770705
theorem B513815 : Blo 338752 513815 := bstep (se 1 (by rfl) ⟨385361, by rfl⟩ : syracuseStep 513815 = 770723) B770723
theorem B644915 : Blo 338752 644915 := bstep (se 1 (by rfl) ⟨483686, by rfl⟩ : syracuseStep 644915 = 967373) B967373
theorem B513881 : Blo 338752 513881 := bstep (se 2 (by rfl) ⟨192705, by rfl⟩ : syracuseStep 513881 = 385411) B385411
theorem B382891 : Blo 338752 382891 := bstep (se 1 (by rfl) ⟨287168, by rfl⟩ : syracuseStep 382891 = 574337) B574337
theorem B513995 : Blo 338752 513995 := bstep (se 1 (by rfl) ⟨385496, by rfl⟩ : syracuseStep 513995 = 770993) B770993
theorem B514007 : Blo 338752 514007 := bstep (se 1 (by rfl) ⟨385505, by rfl⟩ : syracuseStep 514007 = 771011) B771011
theorem B1300445 : Blo 338752 1300445 := bstep (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) B487667
theorem B382999 : Blo 338752 382999 := bstep (se 1 (by rfl) ⟨287249, by rfl⟩ : syracuseStep 382999 = 574499) B574499
theorem B514073 : Blo 338752 514073 := bstep (se 2 (by rfl) ⟨192777, by rfl⟩ : syracuseStep 514073 = 385555) B385555
theorem B874585 : Blo 338752 874585 := bstep (se 2 (by rfl) ⟨327969, by rfl⟩ : syracuseStep 874585 = 655939) B655939
theorem B1726595 : Blo 338752 1726595 := bstep (se 1 (by rfl) ⟨1294946, by rfl⟩ : syracuseStep 1726595 = 2589893) B2589893
theorem B4380803 : Blo 338752 4380803 := bstep (se 1 (by rfl) ⟨3285602, by rfl⟩ : syracuseStep 4380803 = 6571205) B6571205
theorem B383179 : Blo 338752 383179 := bstep (se 1 (by rfl) ⟨287384, by rfl⟩ : syracuseStep 383179 = 574769) B574769
theorem B973079 : Blo 338752 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B645401 : Blo 338752 645401 := bstep (se 2 (by rfl) ⟨242025, by rfl⟩ : syracuseStep 645401 = 484051) B484051
theorem B1628461 : Blo 338752 1628461 := bstep (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) B610673
theorem B1235245 : Blo 338752 1235245 := bstep (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) B463217
theorem B383287 : Blo 338752 383287 := bstep (se 1 (by rfl) ⟨287465, by rfl⟩ : syracuseStep 383287 = 574931) B574931
theorem B579991 : Blo 338752 579991 := bstep (se 1 (by rfl) ⟨434993, by rfl⟩ : syracuseStep 579991 = 869987) B869987
theorem B383467 : Blo 338752 383467 := bstep (se 1 (by rfl) ⟨287600, by rfl⟩ : syracuseStep 383467 = 575201) B575201
theorem B383575 : Blo 338752 383575 := bstep (se 1 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 383575 = 575363) B575363
theorem B1301143 : Blo 338752 1301143 := bstep (se 1 (by rfl) ⟨975857, by rfl⟩ : syracuseStep 1301143 = 1951715) B1951715
theorem B383755 : Blo 338752 383755 := bstep (se 1 (by rfl) ⟨287816, by rfl⟩ : syracuseStep 383755 = 575633) B575633
theorem B383863 : Blo 338752 383863 := bstep (se 1 (by rfl) ⟨287897, by rfl⟩ : syracuseStep 383863 = 575795) B575795
theorem B384043 : Blo 338752 384043 := bstep (se 1 (by rfl) ⟨288032, by rfl⟩ : syracuseStep 384043 = 576065) B576065
theorem B613441 : Blo 338752 613441 := bstep (se 2 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 613441 = 460081) B460081
theorem B482393 : Blo 338752 482393 := bstep (se 2 (by rfl) ⟨180897, by rfl⟩ : syracuseStep 482393 = 361795) B361795
theorem B384151 : Blo 338752 384151 := bstep (se 1 (by rfl) ⟨288113, by rfl⟩ : syracuseStep 384151 = 576227) B576227
theorem B417035 : Blo 338752 417035 := bstep (se 1 (by rfl) ⟨312776, by rfl⟩ : syracuseStep 417035 = 625553) B625553
theorem B384331 : Blo 338752 384331 := bstep (se 1 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 384331 = 576497) B576497
theorem B3956147 : Blo 338752 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B384439 : Blo 338752 384439 := bstep (se 1 (by rfl) ⟨288329, by rfl⟩ : syracuseStep 384439 = 576659) B576659
theorem B548299 : Blo 338752 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B613975 : Blo 338752 613975 := bstep (se 1 (by rfl) ⟨460481, by rfl⟩ : syracuseStep 613975 = 920963) B920963
theorem B384619 : Blo 338752 384619 := bstep (se 1 (by rfl) ⟨288464, by rfl⟩ : syracuseStep 384619 = 576929) B576929
theorem B2612915 : Blo 338752 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B646859 : Blo 338752 646859 := bstep (se 1 (by rfl) ⟨485144, by rfl⟩ : syracuseStep 646859 = 970289) B970289
theorem B2580173 : Blo 338752 2580173 := bstep (se 3 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 2580173 = 967565) B967565
theorem B483031 : Blo 338752 483031 := bstep (se 1 (by rfl) ⟨362273, by rfl⟩ : syracuseStep 483031 = 724547) B724547
theorem B384727 : Blo 338752 384727 := bstep (se 1 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 384727 = 577091) B577091
theorem B647041 : Blo 338752 647041 := bstep (se 2 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 647041 = 485281) B485281
theorem B384907 : Blo 338752 384907 := bstep (se 1 (by rfl) ⟨288680, by rfl⟩ : syracuseStep 384907 = 577361) B577361
theorem B385015 : Blo 338752 385015 := bstep (se 1 (by rfl) ⟨288761, by rfl⟩ : syracuseStep 385015 = 577523) B577523
theorem B385195 : Blo 338752 385195 := bstep (se 1 (by rfl) ⟨288896, by rfl⟩ : syracuseStep 385195 = 577793) B577793
theorem B2580659 : Blo 338752 2580659 := bstep (se 1 (by rfl) ⟨1935494, by rfl⟩ : syracuseStep 2580659 = 3870989) B3870989
theorem B5497093 : Blo 338752 5497093 := bstep (se 4 (by rfl) ⟨515352, by rfl⟩ : syracuseStep 5497093 = 1030705) B1030705
theorem B385303 : Blo 338752 385303 := bstep (se 1 (by rfl) ⟨288977, by rfl⟩ : syracuseStep 385303 = 577955) B577955
theorem B647489 : Blo 338752 647489 := bstep (se 2 (by rfl) ⟨242808, by rfl⟩ : syracuseStep 647489 = 485617) B485617
theorem B483737 : Blo 338752 483737 := bstep (se 2 (by rfl) ⟨181401, by rfl⟩ : syracuseStep 483737 = 362803) B362803
theorem B385483 : Blo 338752 385483 := bstep (se 1 (by rfl) ⟨289112, by rfl⟩ : syracuseStep 385483 = 578225) B578225
theorem B483851 : Blo 338752 483851 := bstep (se 1 (by rfl) ⟨362888, by rfl⟩ : syracuseStep 483851 = 725777) B725777
theorem B385591 : Blo 338752 385591 := bstep (se 1 (by rfl) ⟨289193, by rfl⟩ : syracuseStep 385591 = 578387) B578387
theorem B647831 : Blo 338752 647831 := bstep (se 1 (by rfl) ⟨485873, by rfl⟩ : syracuseStep 647831 = 971747) B971747
theorem B975539 : Blo 338752 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B2319283 : Blo 338752 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B484375 : Blo 338752 484375 := bstep (se 1 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 484375 = 726563) B726563
theorem B746561 : Blo 338752 746561 := bstep (se 2 (by rfl) ⟨279960, by rfl⟩ : syracuseStep 746561 = 559921) B559921
theorem B648499 : Blo 338752 648499 := bstep (se 1 (by rfl) ⟨486374, by rfl⟩ : syracuseStep 648499 = 972749) B972749
theorem B2778461 : Blo 338752 2778461 := bstep (se 3 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 2778461 = 1041923) B1041923
theorem B2582117 : Blo 338752 2582117 := bstep (se 4 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 2582117 = 484147) B484147
theorem B681587 : Blo 338752 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B648947 : Blo 338752 648947 := bstep (se 1 (by rfl) ⟨486710, by rfl⟩ : syracuseStep 648947 = 973421) B973421
theorem B1730321 : Blo 338752 1730321 := bstep (se 2 (by rfl) ⟨648870, by rfl⟩ : syracuseStep 1730321 = 1297741) B1297741
theorem B386839 : Blo 338752 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B648985 : Blo 338752 648985 := bstep (se 2 (by rfl) ⟨243369, by rfl⟩ : syracuseStep 648985 = 486739) B486739
theorem B2615105 : Blo 338752 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B485195 : Blo 338752 485195 := bstep (se 1 (by rfl) ⟨363896, by rfl⟩ : syracuseStep 485195 = 727793) B727793
theorem B1730483 : Blo 338752 1730483 := bstep (se 1 (by rfl) ⟨1297862, by rfl⟩ : syracuseStep 1730483 = 2595725) B2595725
theorem B2582603 : Blo 338752 2582603 := bstep (se 1 (by rfl) ⟨1936952, by rfl⟩ : syracuseStep 2582603 = 3873905) B3873905
theorem B2779267 : Blo 338752 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B649433 : Blo 338752 649433 := bstep (se 2 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 649433 = 487075) B487075
theorem B616729 : Blo 338752 616729 := bstep (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) B462547
theorem B650177 : Blo 338752 650177 := bstep (se 2 (by rfl) ⟨243816, by rfl⟩ : syracuseStep 650177 = 487633) B487633
theorem B519319 : Blo 338752 519319 := bstep (se 1 (by rfl) ⟨389489, by rfl⟩ : syracuseStep 519319 = 778979) B778979
theorem B650443 : Blo 338752 650443 := bstep (se 1 (by rfl) ⟨487832, by rfl⟩ : syracuseStep 650443 = 975665) B975665
theorem B781643 : Blo 338752 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B7368209 : Blo 338752 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B487063 : Blo 338752 487063 := bstep (se 1 (by rfl) ⟨365297, by rfl⟩ : syracuseStep 487063 = 730595) B730595
theorem B6188845 : Blo 338752 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B1732427 : Blo 338752 1732427 := bstep (se 1 (by rfl) ⟨1299320, by rfl⟩ : syracuseStep 1732427 = 2598641) B2598641
theorem B13529693 : Blo 338752 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B1471277 : Blo 338752 1471277 := bstep (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) B551729
theorem B1307443 : Blo 338752 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B3503027 : Blo 338752 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B1143773 : Blo 338752 1143773 := bstep (se 3 (by rfl) ⟨214457, by rfl⟩ : syracuseStep 1143773 = 428915) B428915
theorem B3273803 : Blo 338752 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B2618801 : Blo 338752 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B816691 : Blo 338752 816691 := bstep (se 1 (by rfl) ⟨612518, by rfl⟩ : syracuseStep 816691 = 1225037) B1225037
theorem B1734209 : Blo 338752 1734209 := bstep (se 2 (by rfl) ⟨650328, by rfl⟩ : syracuseStep 1734209 = 1300657) B1300657
theorem B4159127 : Blo 338752 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B2062097 : Blo 338752 2062097 := bstep (se 2 (by rfl) ⟨773286, by rfl⟩ : syracuseStep 2062097 = 1546573) B1546573
theorem B2094913 : Blo 338752 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B816961 : Blo 338752 816961 := bstep (se 2 (by rfl) ⟨306360, by rfl⟩ : syracuseStep 816961 = 612721) B612721
theorem B5502937 : Blo 338752 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B2193425 : Blo 338752 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B1144907 : Blo 338752 1144907 := bstep (se 1 (by rfl) ⟨858680, by rfl⟩ : syracuseStep 1144907 = 1717361) B1717361
theorem B11794733 : Blo 338752 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B1145177 : Blo 338752 1145177 := bstep (se 2 (by rfl) ⟨429441, by rfl⟩ : syracuseStep 1145177 = 858883) B858883
theorem B620993 : Blo 338752 620993 := bstep (se 2 (by rfl) ⟨232872, by rfl⟩ : syracuseStep 620993 = 465745) B465745
theorem B1833623 : Blo 338752 1833623 := bstep (se 1 (by rfl) ⟨1375217, by rfl⟩ : syracuseStep 1833623 = 2750435) B2750435
theorem B1374923 : Blo 338752 1374923 := bstep (se 1 (by rfl) ⟨1031192, by rfl⟩ : syracuseStep 1374923 = 2062385) B2062385
theorem B1309661 : Blo 338752 1309661 := bstep (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) B491123
theorem B1145879 : Blo 338752 1145879 := bstep (se 1 (by rfl) ⟨859409, by rfl⟩ : syracuseStep 1145879 = 1718819) B1718819
theorem B6290507 : Blo 338752 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B8879179 : Blo 338752 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B2587949 : Blo 338752 2587949 := bstep (se 3 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 2587949 = 970481) B970481
theorem B3112343 : Blo 338752 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B1932761 : Blo 338752 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1146419 : Blo 338752 1146419 := bstep (se 1 (by rfl) ⟨859814, by rfl⟩ : syracuseStep 1146419 = 1719629) B1719629
theorem B1146689 : Blo 338752 1146689 := bstep (se 2 (by rfl) ⟨430008, by rfl⟩ : syracuseStep 1146689 = 860017) B860017
theorem B655169 : Blo 338752 655169 := bstep (se 2 (by rfl) ⟨245688, by rfl⟩ : syracuseStep 655169 = 491377) B491377
theorem B2916161 : Blo 338752 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B3112921 : Blo 338752 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B983069 : Blo 338752 983069 := bstep (se 3 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 983069 = 368651) B368651
theorem B2195657 : Blo 338752 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B459065 : Blo 338752 459065 := bstep (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) B344299
theorem B819575 : Blo 338752 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B1147283 : Blo 338752 1147283 := bstep (se 1 (by rfl) ⟨860462, by rfl⟩ : syracuseStep 1147283 = 1720925) B1720925
theorem B623033 : Blo 338752 623033 := bstep (se 2 (by rfl) ⟨233637, by rfl⟩ : syracuseStep 623033 = 467275) B467275
theorem B3932675 : Blo 338752 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B3277529 : Blo 338752 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B787499 : Blo 338752 787499 := bstep (se 1 (by rfl) ⟨590624, by rfl⟩ : syracuseStep 787499 = 1181249) B1181249
theorem B689555 : Blo 338752 689555 := bstep (se 1 (by rfl) ⟨517166, by rfl⟩ : syracuseStep 689555 = 1034333) B1034333
theorem B36079181 : Blo 338752 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B362171 : Blo 338752 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B1148687 : Blo 338752 1148687 := bstep (se 1 (by rfl) ⟨861515, by rfl⟩ : syracuseStep 1148687 = 1723031) B1723031
theorem B1148957 : Blo 338752 1148957 := bstep (se 3 (by rfl) ⟨215429, by rfl⟩ : syracuseStep 1148957 = 430859) B430859
theorem B460859 : Blo 338752 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B1738871 : Blo 338752 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B2591351 : Blo 338752 2591351 := bstep (se 1 (by rfl) ⟨1943513, by rfl⟩ : syracuseStep 2591351 = 3887027) B3887027
theorem B920249 : Blo 338752 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B6523685 : Blo 338752 6523685 := bstep (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) B1223191
theorem B658219 : Blo 338752 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B3705689 : Blo 338752 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B1379207 : Blo 338752 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B428971 : Blo 338752 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B822305 : Blo 338752 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B461897 : Blo 338752 461897 := bstep (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) B346423
theorem B4656365 : Blo 338752 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B1150361 : Blo 338752 1150361 := bstep (se 2 (by rfl) ⟨431385, by rfl⟩ : syracuseStep 1150361 = 862771) B862771
theorem B1969667 : Blo 338752 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B462395 : Blo 338752 462395 := bstep (se 1 (by rfl) ⟨346796, by rfl⟩ : syracuseStep 462395 = 693593) B693593
theorem B2592323 : Blo 338752 2592323 := bstep (se 1 (by rfl) ⟨1944242, by rfl⟩ : syracuseStep 2592323 = 3888485) B3888485
theorem B921223 : Blo 338752 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B429943 : Blo 338752 429943 := bstep (se 1 (by rfl) ⟨322457, by rfl⟩ : syracuseStep 429943 = 644915) B644915
theorem B462763 : Blo 338752 462763 := bstep (se 1 (by rfl) ⟨347072, by rfl⟩ : syracuseStep 462763 = 694145) B694145
theorem B725051 : Blo 338752 725051 := bstep (se 1 (by rfl) ⟨543788, by rfl⟩ : syracuseStep 725051 = 1087577) B1087577
theorem B1151063 : Blo 338752 1151063 := bstep (se 1 (by rfl) ⟨863297, by rfl⟩ : syracuseStep 1151063 = 1726595) B1726595
theorem B2920535 : Blo 338752 2920535 := bstep (se 1 (by rfl) ⟨2190401, by rfl⟩ : syracuseStep 2920535 = 4380803) B4380803
theorem B430267 : Blo 338752 430267 := bstep (se 1 (by rfl) ⟨322700, by rfl⟩ : syracuseStep 430267 = 645401) B645401
theorem B692425 : Blo 338752 692425 := bstep (se 2 (by rfl) ⟨259659, by rfl⟩ : syracuseStep 692425 = 519319) B519319
theorem B463163 : Blo 338752 463163 := bstep (se 1 (by rfl) ⟨347372, by rfl⟩ : syracuseStep 463163 = 694745) B694745
theorem B1642841 : Blo 338752 1642841 := bstep (se 2 (by rfl) ⟨616065, by rfl⟩ : syracuseStep 1642841 = 1232131) B1232131
theorem B1151549 : Blo 338752 1151549 := bstep (se 3 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 1151549 = 431831) B431831
theorem B725879 : Blo 338752 725879 := bstep (se 1 (by rfl) ⟨544409, by rfl⟩ : syracuseStep 725879 = 1088819) B1088819
theorem B922487 : Blo 338752 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B1840151 : Blo 338752 1840151 := bstep (se 1 (by rfl) ⟨1380113, by rfl⟩ : syracuseStep 1840151 = 2760227) B2760227
theorem B1741943 : Blo 338752 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B431239 : Blo 338752 431239 := bstep (se 1 (by rfl) ⟨323429, by rfl⟩ : syracuseStep 431239 = 646859) B646859
theorem B431659 : Blo 338752 431659 := bstep (se 1 (by rfl) ⟨323744, by rfl⟩ : syracuseStep 431659 = 647489) B647489
theorem B431887 : Blo 338752 431887 := bstep (se 1 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 431887 = 647831) B647831
theorem B3610403 : Blo 338752 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B1152953 : Blo 338752 1152953 := bstep (se 2 (by rfl) ⟨432357, by rfl⟩ : syracuseStep 1152953 = 864715) B864715
theorem B1251281 : Blo 338752 1251281 := bstep (se 2 (by rfl) ⟨469230, by rfl⟩ : syracuseStep 1251281 = 938461) B938461
theorem B497707 : Blo 338752 497707 := bstep (se 1 (by rfl) ⟨373280, by rfl⟩ : syracuseStep 497707 = 746561) B746561
theorem B1644745 : Blo 338752 1644745 := bstep (se 2 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 1644745 = 1233559) B1233559
theorem B1317235 : Blo 338752 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1743257 : Blo 338752 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B432631 : Blo 338752 432631 := bstep (se 1 (by rfl) ⟨324473, by rfl⟩ : syracuseStep 432631 = 648947) B648947
theorem B1153547 : Blo 338752 1153547 := bstep (se 1 (by rfl) ⟨865160, by rfl⟩ : syracuseStep 1153547 = 1730321) B1730321
theorem B1841707 : Blo 338752 1841707 := bstep (se 1 (by rfl) ⟨1381280, by rfl⟩ : syracuseStep 1841707 = 2762561) B2762561
theorem B1153655 : Blo 338752 1153655 := bstep (se 1 (by rfl) ⟨865241, by rfl⟩ : syracuseStep 1153655 = 1730483) B1730483
theorem B1383227 : Blo 338752 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B432955 : Blo 338752 432955 := bstep (se 1 (by rfl) ⟨324716, by rfl⟩ : syracuseStep 432955 = 649433) B649433
theorem B858995 : Blo 338752 858995 := bstep (se 1 (by rfl) ⟨644246, by rfl⟩ : syracuseStep 858995 = 1288493) B1288493
theorem B1874909 : Blo 338752 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B15735869 : Blo 338752 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B1449161 : Blo 338752 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B1154249 : Blo 338752 1154249 := bstep (se 2 (by rfl) ⟨432843, by rfl⟩ : syracuseStep 1154249 = 865687) B865687
theorem B1449197 : Blo 338752 1449197 := bstep (se 3 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 1449197 = 543449) B543449
theorem B433451 : Blo 338752 433451 := bstep (se 1 (by rfl) ⟨325088, by rfl⟩ : syracuseStep 433451 = 650177) B650177
theorem B859511 : Blo 338752 859511 := bstep (se 1 (by rfl) ⟨644633, by rfl⟩ : syracuseStep 859511 = 1289267) B1289267
theorem B1088921 : Blo 338752 1088921 := bstep (se 2 (by rfl) ⟨408345, by rfl⟩ : syracuseStep 1088921 = 816691) B816691
theorem B4660739 : Blo 338752 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B2924261 : Blo 338752 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B2793217 : Blo 338752 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1089281 : Blo 338752 1089281 := bstep (se 2 (by rfl) ⟨408480, by rfl⟩ : syracuseStep 1089281 = 816961) B816961
theorem B2596697 : Blo 338752 2596697 := bstep (se 2 (by rfl) ⟨973761, by rfl⟩ : syracuseStep 2596697 = 1947523) B1947523
theorem B1154951 : Blo 338752 1154951 := bstep (se 1 (by rfl) ⟨866213, by rfl⟩ : syracuseStep 1154951 = 1732427) B1732427
theorem B1843091 : Blo 338752 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B1449913 : Blo 338752 1449913 := bstep (se 2 (by rfl) ⟨543717, by rfl⟩ : syracuseStep 1449913 = 1087435) B1087435
theorem B1286381 : Blo 338752 1286381 := bstep (se 3 (by rfl) ⟨241196, by rfl⟩ : syracuseStep 1286381 = 482393) B482393
theorem B1155329 : Blo 338752 1155329 := bstep (se 2 (by rfl) ⟨433248, by rfl⟩ : syracuseStep 1155329 = 866497) B866497
theorem B467215 : Blo 338752 467215 := bstep (se 1 (by rfl) ⟨350411, by rfl⟩ : syracuseStep 467215 = 700823) B700823
theorem B860503 : Blo 338752 860503 := bstep (se 1 (by rfl) ⟨645377, by rfl⟩ : syracuseStep 860503 = 1290755) B1290755
theorem B2171281 : Blo 338752 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B1646993 : Blo 338752 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B2335351 : Blo 338752 2335351 := bstep (se 1 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 2335351 = 3503027) B3503027
theorem B860807 : Blo 338752 860807 := bstep (se 1 (by rfl) ⟨645605, by rfl⟩ : syracuseStep 860807 = 1291211) B1291211
theorem B762515 : Blo 338752 762515 := bstep (se 1 (by rfl) ⟨571886, by rfl⟩ : syracuseStep 762515 = 1143773) B1143773
theorem B762569 : Blo 338752 762569 := bstep (se 2 (by rfl) ⟨285963, by rfl⟩ : syracuseStep 762569 = 571927) B571927
theorem B1942217 : Blo 338752 1942217 := bstep (se 2 (by rfl) ⟨728331, by rfl⟩ : syracuseStep 1942217 = 1456663) B1456663
theorem B860939 : Blo 338752 860939 := bstep (se 1 (by rfl) ⟨645704, by rfl⟩ : syracuseStep 860939 = 1291409) B1291409
theorem B2597669 : Blo 338752 2597669 := bstep (se 4 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 2597669 = 487063) B487063
theorem B1745867 : Blo 338752 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B1156139 : Blo 338752 1156139 := bstep (se 1 (by rfl) ⟨867104, by rfl⟩ : syracuseStep 1156139 = 1734209) B1734209
theorem B861455 : Blo 338752 861455 := bstep (se 1 (by rfl) ⟨646091, by rfl⟩ : syracuseStep 861455 = 1292183) B1292183
theorem B763271 : Blo 338752 763271 := bstep (se 1 (by rfl) ⟨572453, by rfl⟩ : syracuseStep 763271 = 1144907) B1144907
theorem B861587 : Blo 338752 861587 := bstep (se 1 (by rfl) ⟨646190, by rfl⟩ : syracuseStep 861587 = 1292381) B1292381
theorem B11838905 : Blo 338752 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B763451 : Blo 338752 763451 := bstep (se 1 (by rfl) ⟨572588, by rfl⟩ : syracuseStep 763451 = 1145177) B1145177
theorem B22029893 : Blo 338752 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B763577 : Blo 338752 763577 := bstep (se 2 (by rfl) ⟨286341, by rfl⟩ : syracuseStep 763577 = 572683) B572683
theorem B1222415 : Blo 338752 1222415 := bstep (se 1 (by rfl) ⟨916811, by rfl⟩ : syracuseStep 1222415 = 1833623) B1833623
theorem B16623629 : Blo 338752 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B763919 : Blo 338752 763919 := bstep (se 1 (by rfl) ⟨572939, by rfl⟩ : syracuseStep 763919 = 1145879) B1145879
theorem B763937 : Blo 338752 763937 := bstep (se 2 (by rfl) ⟨286476, by rfl⟩ : syracuseStep 763937 = 572953) B572953
theorem B1976363 : Blo 338752 1976363 := bstep (se 1 (by rfl) ⟨1482272, by rfl⟩ : syracuseStep 1976363 = 2964545) B2964545
theorem B1747117 : Blo 338752 1747117 := bstep (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) B655169
theorem B1452289 : Blo 338752 1452289 := bstep (se 2 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 1452289 = 1089217) B1089217
theorem B2074895 : Blo 338752 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B1288507 : Blo 338752 1288507 := bstep (se 1 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 1288507 = 1932761) B1932761
theorem B764279 : Blo 338752 764279 := bstep (se 1 (by rfl) ⟨573209, by rfl⟩ : syracuseStep 764279 = 1146419) B1146419
theorem B2173331 : Blo 338752 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B862721 : Blo 338752 862721 := bstep (se 2 (by rfl) ⟨323520, by rfl⟩ : syracuseStep 862721 = 647041) B647041
theorem B764459 : Blo 338752 764459 := bstep (se 1 (by rfl) ⟨573344, by rfl⟩ : syracuseStep 764459 = 1146689) B1146689
theorem B1944107 : Blo 338752 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B1288993 : Blo 338752 1288993 := bstep (se 2 (by rfl) ⟨483372, by rfl⟩ : syracuseStep 1288993 = 966745) B966745
theorem B863095 : Blo 338752 863095 := bstep (se 1 (by rfl) ⟨647321, by rfl⟩ : syracuseStep 863095 = 1294643) B1294643
theorem B338823 : Blo 338752 338823 := bstep (se 1 (by rfl) ⟨254117, by rfl⟩ : syracuseStep 338823 = 508235) B508235
theorem B338831 : Blo 338752 338831 := bstep (se 1 (by rfl) ⟨254123, by rfl⟩ : syracuseStep 338831 = 508247) B508247
theorem B764819 : Blo 338752 764819 := bstep (se 1 (by rfl) ⟨573614, by rfl⟩ : syracuseStep 764819 = 1147229) B1147229
theorem B2632601 : Blo 338752 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B338875 : Blo 338752 338875 := bstep (se 1 (by rfl) ⟨254156, by rfl⟩ : syracuseStep 338875 = 508313) B508313
theorem B764873 : Blo 338752 764873 := bstep (se 2 (by rfl) ⟨286827, by rfl⟩ : syracuseStep 764873 = 573655) B573655
theorem B338951 : Blo 338752 338951 := bstep (se 1 (by rfl) ⟨254213, by rfl⟩ : syracuseStep 338951 = 508427) B508427
theorem B338959 : Blo 338752 338959 := bstep (se 1 (by rfl) ⟨254219, by rfl⟩ : syracuseStep 338959 = 508439) B508439
theorem B339003 : Blo 338752 339003 := bstep (se 1 (by rfl) ⟨254252, by rfl⟩ : syracuseStep 339003 = 508505) B508505
theorem B339079 : Blo 338752 339079 := bstep (se 1 (by rfl) ⟨254309, by rfl⟩ : syracuseStep 339079 = 508619) B508619
theorem B339087 : Blo 338752 339087 := bstep (se 1 (by rfl) ⟨254315, by rfl⟩ : syracuseStep 339087 = 508631) B508631
theorem B339131 : Blo 338752 339131 := bstep (se 1 (by rfl) ⟨254348, by rfl⟩ : syracuseStep 339131 = 508697) B508697
theorem B339207 : Blo 338752 339207 := bstep (se 1 (by rfl) ⟨254405, by rfl⟩ : syracuseStep 339207 = 508811) B508811
theorem B339215 : Blo 338752 339215 := bstep (se 1 (by rfl) ⟨254411, by rfl⟩ : syracuseStep 339215 = 508823) B508823
theorem B863531 : Blo 338752 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B339259 : Blo 338752 339259 := bstep (se 1 (by rfl) ⟨254444, by rfl⟩ : syracuseStep 339259 = 508889) B508889
theorem B339335 : Blo 338752 339335 := bstep (se 1 (by rfl) ⟨254501, by rfl⟩ : syracuseStep 339335 = 509003) B509003
theorem B3878279 : Blo 338752 3878279 := bstep (se 1 (by rfl) ⟨2908709, by rfl⟩ : syracuseStep 3878279 = 5817419) B5817419
theorem B339343 : Blo 338752 339343 := bstep (se 1 (by rfl) ⟨254507, by rfl⟩ : syracuseStep 339343 = 509015) B509015
theorem B339387 : Blo 338752 339387 := bstep (se 1 (by rfl) ⟨254540, by rfl⟩ : syracuseStep 339387 = 509081) B509081
theorem B339463 : Blo 338752 339463 := bstep (se 1 (by rfl) ⟨254597, by rfl⟩ : syracuseStep 339463 = 509195) B509195
theorem B339471 : Blo 338752 339471 := bstep (se 1 (by rfl) ⟨254603, by rfl⟩ : syracuseStep 339471 = 509207) B509207
theorem B1715741 : Blo 338752 1715741 := bstep (se 3 (by rfl) ⟨321701, by rfl⟩ : syracuseStep 1715741 = 643403) B643403
theorem B339515 : Blo 338752 339515 := bstep (se 1 (by rfl) ⟨254636, by rfl⟩ : syracuseStep 339515 = 509273) B509273
theorem B339591 : Blo 338752 339591 := bstep (se 1 (by rfl) ⟨254693, by rfl⟩ : syracuseStep 339591 = 509387) B509387
theorem B765575 : Blo 338752 765575 := bstep (se 1 (by rfl) ⟨574181, by rfl⟩ : syracuseStep 765575 = 1148363) B1148363
theorem B339599 : Blo 338752 339599 := bstep (se 1 (by rfl) ⟨254699, by rfl⟩ : syracuseStep 339599 = 509399) B509399
theorem B339643 : Blo 338752 339643 := bstep (se 1 (by rfl) ⟨254732, by rfl⟩ : syracuseStep 339643 = 509465) B509465
theorem B1289965 : Blo 338752 1289965 := bstep (se 3 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 1289965 = 483737) B483737
theorem B339719 : Blo 338752 339719 := bstep (se 1 (by rfl) ⟨254789, by rfl⟩ : syracuseStep 339719 = 509579) B509579
theorem B339727 : Blo 338752 339727 := bstep (se 1 (by rfl) ⟨254795, by rfl⟩ : syracuseStep 339727 = 509591) B509591
theorem B339771 : Blo 338752 339771 := bstep (se 1 (by rfl) ⟨254828, by rfl⟩ : syracuseStep 339771 = 509657) B509657
theorem B765755 : Blo 338752 765755 := bstep (se 1 (by rfl) ⟨574316, by rfl⟩ : syracuseStep 765755 = 1148633) B1148633
theorem B339847 : Blo 338752 339847 := bstep (se 1 (by rfl) ⟨254885, by rfl⟩ : syracuseStep 339847 = 509771) B509771
theorem B339855 : Blo 338752 339855 := bstep (se 1 (by rfl) ⟨254891, by rfl⟩ : syracuseStep 339855 = 509783) B509783
theorem B3092377 : Blo 338752 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B765881 : Blo 338752 765881 := bstep (se 2 (by rfl) ⟨287205, by rfl⟩ : syracuseStep 765881 = 574411) B574411
theorem B339899 : Blo 338752 339899 := bstep (se 1 (by rfl) ⟨254924, by rfl⟩ : syracuseStep 339899 = 509849) B509849
theorem B1945565 : Blo 338752 1945565 := bstep (se 3 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 1945565 = 729587) B729587
theorem B1716227 : Blo 338752 1716227 := bstep (se 1 (by rfl) ⟨1287170, by rfl⟩ : syracuseStep 1716227 = 2574341) B2574341
theorem B339975 : Blo 338752 339975 := bstep (se 1 (by rfl) ⟨254981, by rfl⟩ : syracuseStep 339975 = 509963) B509963
theorem B339983 : Blo 338752 339983 := bstep (se 1 (by rfl) ⟨254987, by rfl⟩ : syracuseStep 339983 = 509975) B509975
theorem B1290269 : Blo 338752 1290269 := bstep (se 3 (by rfl) ⟨241925, by rfl⟩ : syracuseStep 1290269 = 483851) B483851
theorem B340027 : Blo 338752 340027 := bstep (se 1 (by rfl) ⟨255020, by rfl⟩ : syracuseStep 340027 = 510041) B510041
theorem B831575 : Blo 338752 831575 := bstep (se 1 (by rfl) ⟨623681, by rfl⟩ : syracuseStep 831575 = 1247363) B1247363
theorem B864371 : Blo 338752 864371 := bstep (se 1 (by rfl) ⟨648278, by rfl⟩ : syracuseStep 864371 = 1296557) B1296557
theorem B340103 : Blo 338752 340103 := bstep (se 1 (by rfl) ⟨255077, by rfl⟩ : syracuseStep 340103 = 510155) B510155
theorem B864391 : Blo 338752 864391 := bstep (se 1 (by rfl) ⟨648293, by rfl⟩ : syracuseStep 864391 = 1296587) B1296587
theorem B340111 : Blo 338752 340111 := bstep (se 1 (by rfl) ⟨255083, by rfl⟩ : syracuseStep 340111 = 510167) B510167
theorem B340155 : Blo 338752 340155 := bstep (se 1 (by rfl) ⟨255116, by rfl⟩ : syracuseStep 340155 = 510233) B510233
theorem B340231 : Blo 338752 340231 := bstep (se 1 (by rfl) ⟨255173, by rfl⟩ : syracuseStep 340231 = 510347) B510347
theorem B340239 : Blo 338752 340239 := bstep (se 1 (by rfl) ⟨255179, by rfl⟩ : syracuseStep 340239 = 510359) B510359
theorem B766223 : Blo 338752 766223 := bstep (se 1 (by rfl) ⟨574667, by rfl⟩ : syracuseStep 766223 = 1149335) B1149335
theorem B766241 : Blo 338752 766241 := bstep (se 2 (by rfl) ⟨287340, by rfl⟩ : syracuseStep 766241 = 574681) B574681
theorem B340283 : Blo 338752 340283 := bstep (se 1 (by rfl) ⟨255212, by rfl⟩ : syracuseStep 340283 = 510425) B510425
theorem B340359 : Blo 338752 340359 := bstep (se 1 (by rfl) ⟨255269, by rfl⟩ : syracuseStep 340359 = 510539) B510539
theorem B340367 : Blo 338752 340367 := bstep (se 1 (by rfl) ⟨255275, by rfl⟩ : syracuseStep 340367 = 510551) B510551
theorem B864665 : Blo 338752 864665 := bstep (se 2 (by rfl) ⟨324249, by rfl⟩ : syracuseStep 864665 = 648499) B648499
theorem B340411 : Blo 338752 340411 := bstep (se 1 (by rfl) ⟨255308, by rfl⟩ : syracuseStep 340411 = 510617) B510617
theorem B1946065 : Blo 338752 1946065 := bstep (se 2 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 1946065 = 1459549) B1459549
theorem B340487 : Blo 338752 340487 := bstep (se 1 (by rfl) ⟨255365, by rfl⟩ : syracuseStep 340487 = 510731) B510731
theorem B340495 : Blo 338752 340495 := bstep (se 1 (by rfl) ⟨255371, by rfl⟩ : syracuseStep 340495 = 510743) B510743
theorem B340539 : Blo 338752 340539 := bstep (se 1 (by rfl) ⟨255404, by rfl⟩ : syracuseStep 340539 = 510809) B510809
theorem B864827 : Blo 338752 864827 := bstep (se 1 (by rfl) ⟨648620, by rfl⟩ : syracuseStep 864827 = 1297241) B1297241
theorem B766583 : Blo 338752 766583 := bstep (se 1 (by rfl) ⟨574937, by rfl⟩ : syracuseStep 766583 = 1149875) B1149875
theorem B340615 : Blo 338752 340615 := bstep (se 1 (by rfl) ⟨255461, by rfl⟩ : syracuseStep 340615 = 510923) B510923
theorem B340623 : Blo 338752 340623 := bstep (se 1 (by rfl) ⟨255467, by rfl⟩ : syracuseStep 340623 = 510935) B510935
theorem B340667 : Blo 338752 340667 := bstep (se 1 (by rfl) ⟨255500, by rfl⟩ : syracuseStep 340667 = 511001) B511001
theorem B340743 : Blo 338752 340743 := bstep (se 1 (by rfl) ⟨255557, by rfl⟩ : syracuseStep 340743 = 511115) B511115
theorem B340751 : Blo 338752 340751 := bstep (se 1 (by rfl) ⟨255563, by rfl⟩ : syracuseStep 340751 = 511127) B511127
theorem B865039 : Blo 338752 865039 := bstep (se 1 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 865039 = 1297559) B1297559
theorem B766763 : Blo 338752 766763 := bstep (se 1 (by rfl) ⟨575072, by rfl⟩ : syracuseStep 766763 = 1150145) B1150145
theorem B340795 : Blo 338752 340795 := bstep (se 1 (by rfl) ⟨255596, by rfl⟩ : syracuseStep 340795 = 511193) B511193
theorem B340871 : Blo 338752 340871 := bstep (se 1 (by rfl) ⟨255653, by rfl⟩ : syracuseStep 340871 = 511307) B511307
theorem B340879 : Blo 338752 340879 := bstep (se 1 (by rfl) ⟨255659, by rfl⟩ : syracuseStep 340879 = 511319) B511319
theorem B471979 : Blo 338752 471979 := bstep (se 1 (by rfl) ⟨353984, by rfl⟩ : syracuseStep 471979 = 707969) B707969
theorem B340923 : Blo 338752 340923 := bstep (se 1 (by rfl) ⟨255692, by rfl⟩ : syracuseStep 340923 = 511385) B511385
theorem B340999 : Blo 338752 340999 := bstep (se 1 (by rfl) ⟨255749, by rfl⟩ : syracuseStep 340999 = 511499) B511499
theorem B341007 : Blo 338752 341007 := bstep (se 1 (by rfl) ⟨255755, by rfl⟩ : syracuseStep 341007 = 511511) B511511
theorem B865313 : Blo 338752 865313 := bstep (se 2 (by rfl) ⟨324492, by rfl⟩ : syracuseStep 865313 = 648985) B648985
theorem B341051 : Blo 338752 341051 := bstep (se 1 (by rfl) ⟨255788, by rfl⟩ : syracuseStep 341051 = 511577) B511577
theorem B341127 : Blo 338752 341127 := bstep (se 1 (by rfl) ⟨255845, by rfl⟩ : syracuseStep 341127 = 511691) B511691
theorem B341135 : Blo 338752 341135 := bstep (se 1 (by rfl) ⟨255851, by rfl⟩ : syracuseStep 341135 = 511703) B511703
theorem B767123 : Blo 338752 767123 := bstep (se 1 (by rfl) ⟨575342, by rfl⟩ : syracuseStep 767123 = 1150685) B1150685
theorem B341179 : Blo 338752 341179 := bstep (se 1 (by rfl) ⟨255884, by rfl⟩ : syracuseStep 341179 = 511769) B511769
theorem B767177 : Blo 338752 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B341255 : Blo 338752 341255 := bstep (se 1 (by rfl) ⟨255941, by rfl⟩ : syracuseStep 341255 = 511883) B511883
theorem B341263 : Blo 338752 341263 := bstep (se 1 (by rfl) ⟨255947, by rfl⟩ : syracuseStep 341263 = 511895) B511895
theorem B341307 : Blo 338752 341307 := bstep (se 1 (by rfl) ⟨255980, by rfl⟩ : syracuseStep 341307 = 511961) B511961
theorem B341383 : Blo 338752 341383 := bstep (se 1 (by rfl) ⟨256037, by rfl⟩ : syracuseStep 341383 = 512075) B512075
theorem B341391 : Blo 338752 341391 := bstep (se 1 (by rfl) ⟨256043, by rfl⟩ : syracuseStep 341391 = 512087) B512087
theorem B341435 : Blo 338752 341435 := bstep (se 1 (by rfl) ⟨256076, by rfl⟩ : syracuseStep 341435 = 512153) B512153
theorem B341511 : Blo 338752 341511 := bstep (se 1 (by rfl) ⟨256133, by rfl⟩ : syracuseStep 341511 = 512267) B512267
theorem B341519 : Blo 338752 341519 := bstep (se 1 (by rfl) ⟨256139, by rfl⟩ : syracuseStep 341519 = 512279) B512279
theorem B341563 : Blo 338752 341563 := bstep (se 1 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 341563 = 512345) B512345
theorem B1717847 : Blo 338752 1717847 := bstep (se 1 (by rfl) ⟨1288385, by rfl⟩ : syracuseStep 1717847 = 2576771) B2576771
theorem B1291895 : Blo 338752 1291895 := bstep (se 1 (by rfl) ⟨968921, by rfl⟩ : syracuseStep 1291895 = 1937843) B1937843
theorem B341639 : Blo 338752 341639 := bstep (se 1 (by rfl) ⟨256229, by rfl⟩ : syracuseStep 341639 = 512459) B512459
theorem B341647 : Blo 338752 341647 := bstep (se 1 (by rfl) ⟨256235, by rfl⟩ : syracuseStep 341647 = 512471) B512471
theorem B341691 : Blo 338752 341691 := bstep (se 1 (by rfl) ⟨256268, by rfl⟩ : syracuseStep 341691 = 512537) B512537
theorem B341767 : Blo 338752 341767 := bstep (se 1 (by rfl) ⟨256325, by rfl⟩ : syracuseStep 341767 = 512651) B512651
theorem B341775 : Blo 338752 341775 := bstep (se 1 (by rfl) ⟨256331, by rfl⟩ : syracuseStep 341775 = 512663) B512663
theorem B341819 : Blo 338752 341819 := bstep (se 1 (by rfl) ⟨256364, by rfl⟩ : syracuseStep 341819 = 512729) B512729
theorem B767879 : Blo 338752 767879 := bstep (se 1 (by rfl) ⟨575909, by rfl⟩ : syracuseStep 767879 = 1151819) B1151819
theorem B341895 : Blo 338752 341895 := bstep (se 1 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 341895 = 512843) B512843
theorem B341903 : Blo 338752 341903 := bstep (se 1 (by rfl) ⟨256427, by rfl⟩ : syracuseStep 341903 = 512855) B512855
theorem B341947 : Blo 338752 341947 := bstep (se 1 (by rfl) ⟨256460, by rfl⟩ : syracuseStep 341947 = 512921) B512921
theorem B342023 : Blo 338752 342023 := bstep (se 1 (by rfl) ⟨256517, by rfl⟩ : syracuseStep 342023 = 513035) B513035
theorem B866315 : Blo 338752 866315 := bstep (se 1 (by rfl) ⟨649736, by rfl⟩ : syracuseStep 866315 = 1299473) B1299473
theorem B342031 : Blo 338752 342031 := bstep (se 1 (by rfl) ⟨256523, by rfl⟩ : syracuseStep 342031 = 513047) B513047
theorem B6273047 : Blo 338752 6273047 := bstep (se 1 (by rfl) ⟨4704785, by rfl⟩ : syracuseStep 6273047 = 9409571) B9409571
theorem B768059 : Blo 338752 768059 := bstep (se 1 (by rfl) ⟨576044, by rfl⟩ : syracuseStep 768059 = 1152089) B1152089
theorem B342075 : Blo 338752 342075 := bstep (se 1 (by rfl) ⟨256556, by rfl⟩ : syracuseStep 342075 = 513113) B513113
theorem B1718333 : Blo 338752 1718333 := bstep (se 3 (by rfl) ⟨322187, by rfl⟩ : syracuseStep 1718333 = 644375) B644375
theorem B342151 : Blo 338752 342151 := bstep (se 1 (by rfl) ⟨256613, by rfl⟩ : syracuseStep 342151 = 513227) B513227
theorem B342159 : Blo 338752 342159 := bstep (se 1 (by rfl) ⟨256619, by rfl⟩ : syracuseStep 342159 = 513239) B513239
theorem B768185 : Blo 338752 768185 := bstep (se 2 (by rfl) ⟨288069, by rfl⟩ : syracuseStep 768185 = 576139) B576139
theorem B342203 : Blo 338752 342203 := bstep (se 1 (by rfl) ⟨256652, by rfl⟩ : syracuseStep 342203 = 513305) B513305
theorem B342279 : Blo 338752 342279 := bstep (se 1 (by rfl) ⟨256709, by rfl⟩ : syracuseStep 342279 = 513419) B513419
theorem B342287 : Blo 338752 342287 := bstep (se 1 (by rfl) ⟨256715, by rfl⟩ : syracuseStep 342287 = 513431) B513431
theorem B571691 : Blo 338752 571691 := bstep (se 1 (by rfl) ⟨428768, by rfl⟩ : syracuseStep 571691 = 857537) B857537
theorem B342331 : Blo 338752 342331 := bstep (se 1 (by rfl) ⟨256748, by rfl⟩ : syracuseStep 342331 = 513497) B513497
theorem B342407 : Blo 338752 342407 := bstep (se 1 (by rfl) ⟨256805, by rfl⟩ : syracuseStep 342407 = 513611) B513611
theorem B342415 : Blo 338752 342415 := bstep (se 1 (by rfl) ⟨256811, by rfl⟩ : syracuseStep 342415 = 513623) B513623
theorem B1948049 : Blo 338752 1948049 := bstep (se 2 (by rfl) ⟨730518, by rfl⟩ : syracuseStep 1948049 = 1461037) B1461037
theorem B342459 : Blo 338752 342459 := bstep (se 1 (by rfl) ⟨256844, by rfl⟩ : syracuseStep 342459 = 513689) B513689
theorem B342535 : Blo 338752 342535 := bstep (se 1 (by rfl) ⟨256901, by rfl⟩ : syracuseStep 342535 = 513803) B513803
theorem B768527 : Blo 338752 768527 := bstep (se 1 (by rfl) ⟨576395, by rfl⟩ : syracuseStep 768527 = 1152791) B1152791
theorem B342543 : Blo 338752 342543 := bstep (se 1 (by rfl) ⟨256907, by rfl⟩ : syracuseStep 342543 = 513815) B513815
theorem B3291677 : Blo 338752 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B768545 : Blo 338752 768545 := bstep (se 2 (by rfl) ⟨288204, by rfl⟩ : syracuseStep 768545 = 576409) B576409
theorem B342587 : Blo 338752 342587 := bstep (se 1 (by rfl) ⟨256940, by rfl⟩ : syracuseStep 342587 = 513881) B513881
theorem B1292867 : Blo 338752 1292867 := bstep (se 1 (by rfl) ⟨969650, by rfl⟩ : syracuseStep 1292867 = 1939301) B1939301
theorem B342663 : Blo 338752 342663 := bstep (se 1 (by rfl) ⟨256997, by rfl⟩ : syracuseStep 342663 = 513995) B513995
theorem B342671 : Blo 338752 342671 := bstep (se 1 (by rfl) ⟨257003, by rfl⟩ : syracuseStep 342671 = 514007) B514007
theorem B866963 : Blo 338752 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B572089 : Blo 338752 572089 := bstep (se 2 (by rfl) ⟨214533, by rfl⟩ : syracuseStep 572089 = 429067) B429067
theorem B342715 : Blo 338752 342715 := bstep (se 1 (by rfl) ⟨257036, by rfl⟩ : syracuseStep 342715 = 514073) B514073
theorem B1096507 : Blo 338752 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B768887 : Blo 338752 768887 := bstep (se 1 (by rfl) ⟨576665, by rfl⟩ : syracuseStep 768887 = 1153331) B1153331
theorem B867257 : Blo 338752 867257 := bstep (se 2 (by rfl) ⟨325221, by rfl⟩ : syracuseStep 867257 = 650443) B650443
theorem B1031183 : Blo 338752 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B965675 : Blo 338752 965675 := bstep (se 1 (by rfl) ⟨724256, by rfl⟩ : syracuseStep 965675 = 1448513) B1448513
theorem B769067 : Blo 338752 769067 := bstep (se 1 (by rfl) ⟨576800, by rfl⟩ : syracuseStep 769067 = 1153601) B1153601
theorem B572791 : Blo 338752 572791 := bstep (se 1 (by rfl) ⟨429593, by rfl⟩ : syracuseStep 572791 = 859187) B859187
theorem B1752455 : Blo 338752 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B769427 : Blo 338752 769427 := bstep (se 1 (by rfl) ⟨577070, by rfl⟩ : syracuseStep 769427 = 1154141) B1154141
theorem B769481 : Blo 338752 769481 := bstep (se 2 (by rfl) ⟨288555, by rfl⟩ : syracuseStep 769481 = 577111) B577111
theorem B1293853 : Blo 338752 1293853 := bstep (se 3 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 1293853 = 485195) B485195
theorem B572987 : Blo 338752 572987 := bstep (se 1 (by rfl) ⟨429740, by rfl⟩ : syracuseStep 572987 = 859481) B859481
theorem B2637431 : Blo 338752 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B1720115 : Blo 338752 1720115 := bstep (se 1 (by rfl) ⟨1290086, by rfl⟩ : syracuseStep 1720115 = 2580173) B2580173
theorem B2080657 : Blo 338752 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B573385 : Blo 338752 573385 := bstep (se 2 (by rfl) ⟨215019, by rfl⟩ : syracuseStep 573385 = 430039) B430039
theorem B1720439 : Blo 338752 1720439 := bstep (se 1 (by rfl) ⟨1290329, by rfl⟩ : syracuseStep 1720439 = 2580659) B2580659
theorem B966791 : Blo 338752 966791 := bstep (se 1 (by rfl) ⟨725093, by rfl⟩ : syracuseStep 966791 = 1450187) B1450187
theorem B770183 : Blo 338752 770183 := bstep (se 1 (by rfl) ⟨577637, by rfl⟩ : syracuseStep 770183 = 1155275) B1155275
theorem B508151 : Blo 338752 508151 := bstep (se 1 (by rfl) ⟨381113, by rfl⟩ : syracuseStep 508151 = 762227) B762227
theorem B508175 : Blo 338752 508175 := bstep (se 1 (by rfl) ⟨381131, by rfl⟩ : syracuseStep 508175 = 762263) B762263
theorem B508217 : Blo 338752 508217 := bstep (se 2 (by rfl) ⟨190581, by rfl⟩ : syracuseStep 508217 = 381163) B381163
theorem B770363 : Blo 338752 770363 := bstep (se 1 (by rfl) ⟨577772, by rfl⟩ : syracuseStep 770363 = 1155545) B1155545
theorem B966973 : Blo 338752 966973 := bstep (se 3 (by rfl) ⟨181307, by rfl⟩ : syracuseStep 966973 = 362615) B362615
theorem B508295 : Blo 338752 508295 := bstep (se 1 (by rfl) ⟨381221, by rfl⟩ : syracuseStep 508295 = 762443) B762443
theorem B508331 : Blo 338752 508331 := bstep (se 1 (by rfl) ⟨381248, by rfl⟩ : syracuseStep 508331 = 762497) B762497
theorem B770489 : Blo 338752 770489 := bstep (se 2 (by rfl) ⟨288933, by rfl⟩ : syracuseStep 770489 = 577867) B577867
theorem B508361 : Blo 338752 508361 := bstep (se 2 (by rfl) ⟨190635, by rfl⟩ : syracuseStep 508361 = 381271) B381271
theorem B508475 : Blo 338752 508475 := bstep (se 1 (by rfl) ⟨381356, by rfl⟩ : syracuseStep 508475 = 762713) B762713
theorem B508535 : Blo 338752 508535 := bstep (se 1 (by rfl) ⟨381401, by rfl⟩ : syracuseStep 508535 = 762803) B762803
theorem B574087 : Blo 338752 574087 := bstep (se 1 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 574087 = 861131) B861131
theorem B508559 : Blo 338752 508559 := bstep (se 1 (by rfl) ⟨381419, by rfl⟩ : syracuseStep 508559 = 762839) B762839
theorem B967315 : Blo 338752 967315 := bstep (se 1 (by rfl) ⟨725486, by rfl⟩ : syracuseStep 967315 = 1450973) B1450973
theorem B508601 : Blo 338752 508601 := bstep (se 2 (by rfl) ⟨190725, by rfl⟩ : syracuseStep 508601 = 381451) B381451
theorem B508679 : Blo 338752 508679 := bstep (se 1 (by rfl) ⟨381509, by rfl⟩ : syracuseStep 508679 = 763019) B763019
theorem B770831 : Blo 338752 770831 := bstep (se 1 (by rfl) ⟨578123, by rfl⟩ : syracuseStep 770831 = 1156247) B1156247
theorem B770849 : Blo 338752 770849 := bstep (se 2 (by rfl) ⟨289068, by rfl⟩ : syracuseStep 770849 = 578137) B578137
theorem B508715 : Blo 338752 508715 := bstep (se 1 (by rfl) ⟨381536, by rfl⟩ : syracuseStep 508715 = 763073) B763073
theorem B508745 : Blo 338752 508745 := bstep (se 2 (by rfl) ⟨190779, by rfl⟩ : syracuseStep 508745 = 381559) B381559
theorem B1852307 : Blo 338752 1852307 := bstep (se 1 (by rfl) ⟨1389230, by rfl⟩ : syracuseStep 1852307 = 2778461) B2778461
theorem B508859 : Blo 338752 508859 := bstep (se 1 (by rfl) ⟨381644, by rfl⟩ : syracuseStep 508859 = 763289) B763289
theorem B508919 : Blo 338752 508919 := bstep (se 1 (by rfl) ⟨381689, by rfl⟩ : syracuseStep 508919 = 763379) B763379
theorem B508943 : Blo 338752 508943 := bstep (se 1 (by rfl) ⟨381707, by rfl⟩ : syracuseStep 508943 = 763415) B763415
theorem B508985 : Blo 338752 508985 := bstep (se 2 (by rfl) ⟨190869, by rfl⟩ : syracuseStep 508985 = 381739) B381739
theorem B1721411 : Blo 338752 1721411 := bstep (se 1 (by rfl) ⟨1291058, by rfl⟩ : syracuseStep 1721411 = 2582117) B2582117
theorem B771191 : Blo 338752 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B509063 : Blo 338752 509063 := bstep (se 1 (by rfl) ⟨381797, by rfl⟩ : syracuseStep 509063 = 763595) B763595
theorem B509099 : Blo 338752 509099 := bstep (se 1 (by rfl) ⟨381824, by rfl⟩ : syracuseStep 509099 = 763649) B763649
theorem B509129 : Blo 338752 509129 := bstep (se 2 (by rfl) ⟨190923, by rfl⟩ : syracuseStep 509129 = 381847) B381847
theorem B574735 : Blo 338752 574735 := bstep (se 1 (by rfl) ⟨431051, by rfl⟩ : syracuseStep 574735 = 862103) B862103
theorem B509243 : Blo 338752 509243 := bstep (se 1 (by rfl) ⟨381932, by rfl⟩ : syracuseStep 509243 = 763865) B763865
theorem B509303 : Blo 338752 509303 := bstep (se 1 (by rfl) ⟨381977, by rfl⟩ : syracuseStep 509303 = 763955) B763955
theorem B1721735 : Blo 338752 1721735 := bstep (se 1 (by rfl) ⟨1291301, by rfl⟩ : syracuseStep 1721735 = 2582603) B2582603
theorem B509327 : Blo 338752 509327 := bstep (se 1 (by rfl) ⟨381995, by rfl⟩ : syracuseStep 509327 = 763991) B763991
theorem B509369 : Blo 338752 509369 := bstep (se 2 (by rfl) ⟨191013, by rfl⟩ : syracuseStep 509369 = 382027) B382027
theorem B509447 : Blo 338752 509447 := bstep (se 1 (by rfl) ⟨382085, by rfl⟩ : syracuseStep 509447 = 764171) B764171
theorem B968203 : Blo 338752 968203 := bstep (se 1 (by rfl) ⟨726152, by rfl⟩ : syracuseStep 968203 = 1452305) B1452305
theorem B509483 : Blo 338752 509483 := bstep (se 1 (by rfl) ⟨382112, by rfl⟩ : syracuseStep 509483 = 764225) B764225
theorem B3688001 : Blo 338752 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B509513 : Blo 338752 509513 := bstep (se 2 (by rfl) ⟨191067, by rfl⟩ : syracuseStep 509513 = 382135) B382135
theorem B509627 : Blo 338752 509627 := bstep (se 1 (by rfl) ⟨382220, by rfl⟩ : syracuseStep 509627 = 764441) B764441
theorem B509687 : Blo 338752 509687 := bstep (se 1 (by rfl) ⟨382265, by rfl⟩ : syracuseStep 509687 = 764531) B764531
theorem B509711 : Blo 338752 509711 := bstep (se 1 (by rfl) ⟨382283, by rfl⟩ : syracuseStep 509711 = 764567) B764567
theorem B575275 : Blo 338752 575275 := bstep (se 1 (by rfl) ⟨431456, by rfl⟩ : syracuseStep 575275 = 862913) B862913
theorem B509753 : Blo 338752 509753 := bstep (se 2 (by rfl) ⟨191157, by rfl⟩ : syracuseStep 509753 = 382315) B382315
theorem B509831 : Blo 338752 509831 := bstep (se 1 (by rfl) ⟨382373, by rfl⟩ : syracuseStep 509831 = 764747) B764747
theorem B4638617 : Blo 338752 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B509867 : Blo 338752 509867 := bstep (se 1 (by rfl) ⟨382400, by rfl⟩ : syracuseStep 509867 = 764801) B764801
theorem B575417 : Blo 338752 575417 := bstep (se 2 (by rfl) ⟨215781, by rfl⟩ : syracuseStep 575417 = 431563) B431563
theorem B509897 : Blo 338752 509897 := bstep (se 2 (by rfl) ⟨191211, by rfl⟩ : syracuseStep 509897 = 382423) B382423
theorem B968705 : Blo 338752 968705 := bstep (se 2 (by rfl) ⟨363264, by rfl⟩ : syracuseStep 968705 = 726529) B726529
theorem B510011 : Blo 338752 510011 := bstep (se 1 (by rfl) ⟨382508, by rfl⟩ : syracuseStep 510011 = 765017) B765017
theorem B510071 : Blo 338752 510071 := bstep (se 1 (by rfl) ⟨382553, by rfl⟩ : syracuseStep 510071 = 765107) B765107
theorem B510095 : Blo 338752 510095 := bstep (se 1 (by rfl) ⟨382571, by rfl⟩ : syracuseStep 510095 = 765143) B765143
theorem B510137 : Blo 338752 510137 := bstep (se 2 (by rfl) ⟨191301, by rfl⟩ : syracuseStep 510137 = 382603) B382603
theorem B510215 : Blo 338752 510215 := bstep (se 1 (by rfl) ⟨382661, by rfl⟩ : syracuseStep 510215 = 765323) B765323
theorem B510251 : Blo 338752 510251 := bstep (se 1 (by rfl) ⟨382688, by rfl⟩ : syracuseStep 510251 = 765377) B765377
theorem B510281 : Blo 338752 510281 := bstep (se 2 (by rfl) ⟨191355, by rfl⟩ : syracuseStep 510281 = 382711) B382711
theorem B969047 : Blo 338752 969047 := bstep (se 1 (by rfl) ⟨726785, by rfl⟩ : syracuseStep 969047 = 1453571) B1453571
theorem B1296755 : Blo 338752 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B510395 : Blo 338752 510395 := bstep (se 1 (by rfl) ⟨382796, by rfl⟩ : syracuseStep 510395 = 765593) B765593
theorem B510455 : Blo 338752 510455 := bstep (se 1 (by rfl) ⟨382841, by rfl⟩ : syracuseStep 510455 = 765683) B765683
theorem B510479 : Blo 338752 510479 := bstep (se 1 (by rfl) ⟨382859, by rfl⟩ : syracuseStep 510479 = 765719) B765719
theorem B510521 : Blo 338752 510521 := bstep (se 2 (by rfl) ⟨191445, by rfl⟩ : syracuseStep 510521 = 382891) B382891
theorem B576119 : Blo 338752 576119 := bstep (se 1 (by rfl) ⟨432089, by rfl⟩ : syracuseStep 576119 = 864179) B864179
theorem B510599 : Blo 338752 510599 := bstep (se 1 (by rfl) ⟨382949, by rfl⟩ : syracuseStep 510599 = 765899) B765899
theorem B510635 : Blo 338752 510635 := bstep (se 1 (by rfl) ⟨382976, by rfl⟩ : syracuseStep 510635 = 765953) B765953
theorem B510665 : Blo 338752 510665 := bstep (se 2 (by rfl) ⟨191499, by rfl⟩ : syracuseStep 510665 = 382999) B382999
theorem B1166113 : Blo 338752 1166113 := bstep (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) B874585
theorem B510779 : Blo 338752 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B510839 : Blo 338752 510839 := bstep (se 1 (by rfl) ⟨383129, by rfl⟩ : syracuseStep 510839 = 766259) B766259
theorem B510863 : Blo 338752 510863 := bstep (se 1 (by rfl) ⟨383147, by rfl⟩ : syracuseStep 510863 = 766295) B766295
theorem B510905 : Blo 338752 510905 := bstep (se 2 (by rfl) ⟨191589, by rfl⟩ : syracuseStep 510905 = 383179) B383179
theorem B510983 : Blo 338752 510983 := bstep (se 1 (by rfl) ⟨383237, by rfl⟩ : syracuseStep 510983 = 766475) B766475
theorem B511019 : Blo 338752 511019 := bstep (se 1 (by rfl) ⟨383264, by rfl⟩ : syracuseStep 511019 = 766529) B766529
theorem B576571 : Blo 338752 576571 := bstep (se 1 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 576571 = 864857) B864857
theorem B511049 : Blo 338752 511049 := bstep (se 2 (by rfl) ⟨191643, by rfl⟩ : syracuseStep 511049 = 383287) B383287
theorem B773267 : Blo 338752 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B511163 : Blo 338752 511163 := bstep (se 1 (by rfl) ⟨383372, by rfl⟩ : syracuseStep 511163 = 766745) B766745
theorem B773321 : Blo 338752 773321 := bstep (se 2 (by rfl) ⟨289995, by rfl⟩ : syracuseStep 773321 = 579991) B579991
theorem B576713 : Blo 338752 576713 := bstep (se 2 (by rfl) ⟨216267, by rfl⟩ : syracuseStep 576713 = 432535) B432535
theorem B511223 : Blo 338752 511223 := bstep (se 1 (by rfl) ⟨383417, by rfl⟩ : syracuseStep 511223 = 766835) B766835
theorem B511247 : Blo 338752 511247 := bstep (se 1 (by rfl) ⟨383435, by rfl⟩ : syracuseStep 511247 = 766871) B766871
theorem B511289 : Blo 338752 511289 := bstep (se 2 (by rfl) ⟨191733, by rfl⟩ : syracuseStep 511289 = 383467) B383467
theorem B2182535 : Blo 338752 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B511367 : Blo 338752 511367 := bstep (se 1 (by rfl) ⟨383525, by rfl⟩ : syracuseStep 511367 = 767051) B767051
theorem B511403 : Blo 338752 511403 := bstep (se 1 (by rfl) ⟨383552, by rfl⟩ : syracuseStep 511403 = 767105) B767105
theorem B511433 : Blo 338752 511433 := bstep (se 2 (by rfl) ⟨191787, by rfl⟩ : syracuseStep 511433 = 383575) B383575
theorem B511547 : Blo 338752 511547 := bstep (se 1 (by rfl) ⟨383660, by rfl⟩ : syracuseStep 511547 = 767321) B767321
theorem B511607 : Blo 338752 511607 := bstep (se 1 (by rfl) ⟨383705, by rfl⟩ : syracuseStep 511607 = 767411) B767411
theorem B511631 : Blo 338752 511631 := bstep (se 1 (by rfl) ⟨383723, by rfl⟩ : syracuseStep 511631 = 767447) B767447
theorem B511673 : Blo 338752 511673 := bstep (se 2 (by rfl) ⟨191877, by rfl⟩ : syracuseStep 511673 = 383755) B383755
theorem B511751 : Blo 338752 511751 := bstep (se 1 (by rfl) ⟨383813, by rfl⟩ : syracuseStep 511751 = 767627) B767627
theorem B2772751 : Blo 338752 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B511787 : Blo 338752 511787 := bstep (se 1 (by rfl) ⟨383840, by rfl⟩ : syracuseStep 511787 = 767681) B767681
theorem B511817 : Blo 338752 511817 := bstep (se 2 (by rfl) ⟨191931, by rfl⟩ : syracuseStep 511817 = 383863) B383863
theorem B577415 : Blo 338752 577415 := bstep (se 1 (by rfl) ⟨433061, by rfl⟩ : syracuseStep 577415 = 866123) B866123
theorem B511931 : Blo 338752 511931 := bstep (se 1 (by rfl) ⟨383948, by rfl⟩ : syracuseStep 511931 = 767897) B767897
theorem B511991 : Blo 338752 511991 := bstep (se 1 (by rfl) ⟨383993, by rfl⟩ : syracuseStep 511991 = 767987) B767987
theorem B1462283 : Blo 338752 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B512015 : Blo 338752 512015 := bstep (se 1 (by rfl) ⟨384011, by rfl⟩ : syracuseStep 512015 = 768023) B768023
theorem B643115 : Blo 338752 643115 := bstep (se 1 (by rfl) ⟨482336, by rfl⟩ : syracuseStep 643115 = 964673) B964673
theorem B4640813 : Blo 338752 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B512057 : Blo 338752 512057 := bstep (se 2 (by rfl) ⟨192021, by rfl⟩ : syracuseStep 512057 = 384043) B384043
theorem B512135 : Blo 338752 512135 := bstep (se 1 (by rfl) ⟨384101, by rfl⟩ : syracuseStep 512135 = 768203) B768203
theorem B512171 : Blo 338752 512171 := bstep (se 1 (by rfl) ⟨384128, by rfl⟩ : syracuseStep 512171 = 768257) B768257
theorem B970937 : Blo 338752 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B512201 : Blo 338752 512201 := bstep (se 2 (by rfl) ⟨192075, by rfl⟩ : syracuseStep 512201 = 384151) B384151
theorem B381199 : Blo 338752 381199 := bstep (se 1 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 381199 = 571799) B571799
theorem B413995 : Blo 338752 413995 := bstep (se 1 (by rfl) ⟨310496, by rfl⟩ : syracuseStep 413995 = 620993) B620993
theorem B512315 : Blo 338752 512315 := bstep (se 1 (by rfl) ⟨384236, by rfl⟩ : syracuseStep 512315 = 768473) B768473
theorem B512375 : Blo 338752 512375 := bstep (se 1 (by rfl) ⟨384281, by rfl⟩ : syracuseStep 512375 = 768563) B768563
theorem B512399 : Blo 338752 512399 := bstep (se 1 (by rfl) ⟨384299, by rfl⟩ : syracuseStep 512399 = 768599) B768599
theorem B512441 : Blo 338752 512441 := bstep (se 2 (by rfl) ⟨192165, by rfl⟩ : syracuseStep 512441 = 384331) B384331
theorem B512519 : Blo 338752 512519 := bstep (se 1 (by rfl) ⟨384389, by rfl⟩ : syracuseStep 512519 = 768779) B768779
theorem B578063 : Blo 338752 578063 := bstep (se 1 (by rfl) ⟨433547, by rfl⟩ : syracuseStep 578063 = 867095) B867095
theorem B512555 : Blo 338752 512555 := bstep (se 1 (by rfl) ⟨384416, by rfl⟩ : syracuseStep 512555 = 768833) B768833
theorem B1298987 : Blo 338752 1298987 := bstep (se 1 (by rfl) ⟨974240, by rfl⟩ : syracuseStep 1298987 = 1948481) B1948481
theorem B512585 : Blo 338752 512585 := bstep (se 2 (by rfl) ⟨192219, by rfl⟩ : syracuseStep 512585 = 384439) B384439
theorem B873107 : Blo 338752 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B512699 : Blo 338752 512699 := bstep (se 1 (by rfl) ⟨384524, by rfl⟩ : syracuseStep 512699 = 769049) B769049
theorem B512759 : Blo 338752 512759 := bstep (se 1 (by rfl) ⟨384569, by rfl⟩ : syracuseStep 512759 = 769139) B769139
theorem B381703 : Blo 338752 381703 := bstep (se 1 (by rfl) ⟨286277, by rfl⟩ : syracuseStep 381703 = 572555) B572555
theorem B512783 : Blo 338752 512783 := bstep (se 1 (by rfl) ⟨384587, by rfl⟩ : syracuseStep 512783 = 769175) B769175
theorem B512825 : Blo 338752 512825 := bstep (se 2 (by rfl) ⟨192309, by rfl⟩ : syracuseStep 512825 = 384619) B384619
theorem B1725299 : Blo 338752 1725299 := bstep (se 1 (by rfl) ⟨1293974, by rfl⟩ : syracuseStep 1725299 = 2587949) B2587949
theorem B512903 : Blo 338752 512903 := bstep (se 1 (by rfl) ⟨384677, by rfl⟩ : syracuseStep 512903 = 769355) B769355
theorem B512939 : Blo 338752 512939 := bstep (se 1 (by rfl) ⟨384704, by rfl⟩ : syracuseStep 512939 = 769409) B769409
theorem B381883 : Blo 338752 381883 := bstep (se 1 (by rfl) ⟨286412, by rfl⟩ : syracuseStep 381883 = 572825) B572825
theorem B644041 : Blo 338752 644041 := bstep (se 2 (by rfl) ⟨241515, by rfl⟩ : syracuseStep 644041 = 483031) B483031
theorem B512969 : Blo 338752 512969 := bstep (se 2 (by rfl) ⟨192363, by rfl⟩ : syracuseStep 512969 = 384727) B384727
theorem B1037323 : Blo 338752 1037323 := bstep (se 1 (by rfl) ⟨777992, by rfl⟩ : syracuseStep 1037323 = 1555985) B1555985
theorem B513083 : Blo 338752 513083 := bstep (se 1 (by rfl) ⟨384812, by rfl⟩ : syracuseStep 513083 = 769625) B769625
theorem B513143 : Blo 338752 513143 := bstep (se 1 (by rfl) ⟨384857, by rfl⟩ : syracuseStep 513143 = 769715) B769715
theorem B513167 : Blo 338752 513167 := bstep (se 1 (by rfl) ⟨384875, by rfl⟩ : syracuseStep 513167 = 769751) B769751
theorem B513209 : Blo 338752 513209 := bstep (se 2 (by rfl) ⟨192453, by rfl⟩ : syracuseStep 513209 = 384907) B384907
theorem B513287 : Blo 338752 513287 := bstep (se 1 (by rfl) ⟨384965, by rfl⟩ : syracuseStep 513287 = 769931) B769931
theorem B4150561 : Blo 338752 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B513323 : Blo 338752 513323 := bstep (se 1 (by rfl) ⟨384992, by rfl⟩ : syracuseStep 513323 = 769985) B769985
theorem B513353 : Blo 338752 513353 := bstep (se 2 (by rfl) ⟨192507, by rfl⟩ : syracuseStep 513353 = 385015) B385015
theorem B1725785 : Blo 338752 1725785 := bstep (se 2 (by rfl) ⟨647169, by rfl⟩ : syracuseStep 1725785 = 1294339) B1294339
theorem B382351 : Blo 338752 382351 := bstep (se 1 (by rfl) ⟨286763, by rfl⟩ : syracuseStep 382351 = 573527) B573527
theorem B513467 : Blo 338752 513467 := bstep (se 1 (by rfl) ⟨385100, by rfl⟩ : syracuseStep 513467 = 770201) B770201
theorem B513527 : Blo 338752 513527 := bstep (se 1 (by rfl) ⟨385145, by rfl⟩ : syracuseStep 513527 = 770291) B770291
theorem B513551 : Blo 338752 513551 := bstep (se 1 (by rfl) ⟨385163, by rfl⟩ : syracuseStep 513551 = 770327) B770327
theorem B513593 : Blo 338752 513593 := bstep (se 2 (by rfl) ⟨192597, by rfl⟩ : syracuseStep 513593 = 385195) B385195
theorem B513671 : Blo 338752 513671 := bstep (se 1 (by rfl) ⟨385253, by rfl⟩ : syracuseStep 513671 = 770507) B770507
theorem B644755 : Blo 338752 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B513707 : Blo 338752 513707 := bstep (se 1 (by rfl) ⟨385280, by rfl⟩ : syracuseStep 513707 = 770561) B770561
theorem B7329457 : Blo 338752 7329457 := bstep (se 2 (by rfl) ⟨2748546, by rfl⟩ : syracuseStep 7329457 = 5497093) B5497093
theorem B513737 : Blo 338752 513737 := bstep (se 2 (by rfl) ⟨192651, by rfl⟩ : syracuseStep 513737 = 385303) B385303
theorem B972577 : Blo 338752 972577 := bstep (se 2 (by rfl) ⟨364716, by rfl⟩ : syracuseStep 972577 = 729433) B729433
theorem B513851 : Blo 338752 513851 := bstep (se 1 (by rfl) ⟨385388, by rfl⟩ : syracuseStep 513851 = 770777) B770777
theorem B1038199 : Blo 338752 1038199 := bstep (se 1 (by rfl) ⟨778649, by rfl⟩ : syracuseStep 1038199 = 1557299) B1557299
theorem B513911 : Blo 338752 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B1628039 : Blo 338752 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B382855 : Blo 338752 382855 := bstep (se 1 (by rfl) ⟨287141, by rfl⟩ : syracuseStep 382855 = 574283) B574283
theorem B513935 : Blo 338752 513935 := bstep (se 1 (by rfl) ⟨385451, by rfl⟩ : syracuseStep 513935 = 770903) B770903
theorem B513977 : Blo 338752 513977 := bstep (se 2 (by rfl) ⟨192741, by rfl⟩ : syracuseStep 513977 = 385483) B385483
theorem B514055 : Blo 338752 514055 := bstep (se 1 (by rfl) ⟨385541, by rfl⟩ : syracuseStep 514055 = 771083) B771083
theorem B1038347 : Blo 338752 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B1234955 : Blo 338752 1234955 := bstep (se 1 (by rfl) ⟨926216, by rfl⟩ : syracuseStep 1234955 = 1852433) B1852433
theorem B514091 : Blo 338752 514091 := bstep (se 1 (by rfl) ⟨385568, by rfl⟩ : syracuseStep 514091 = 771137) B771137
theorem B383035 : Blo 338752 383035 := bstep (se 1 (by rfl) ⟨287276, by rfl⟩ : syracuseStep 383035 = 574553) B574553
theorem B1038395 : Blo 338752 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B514121 : Blo 338752 514121 := bstep (se 2 (by rfl) ⟨192795, by rfl⟩ : syracuseStep 514121 = 385591) B385591
theorem B383503 : Blo 338752 383503 := bstep (se 1 (by rfl) ⟨287627, by rfl⟩ : syracuseStep 383503 = 575255) B575255
theorem B645833 : Blo 338752 645833 := bstep (se 2 (by rfl) ⟨242187, by rfl⟩ : syracuseStep 645833 = 484375) B484375
theorem B2579201 : Blo 338752 2579201 := bstep (se 2 (by rfl) ⟨967200, by rfl⟩ : syracuseStep 2579201 = 1934401) B1934401
theorem B384007 : Blo 338752 384007 := bstep (se 1 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 384007 = 576011) B576011
theorem B973853 : Blo 338752 973853 := bstep (se 3 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 973853 = 365195) B365195
theorem B384187 : Blo 338752 384187 := bstep (se 1 (by rfl) ⟨288140, by rfl⟩ : syracuseStep 384187 = 576281) B576281
theorem B974081 : Blo 338752 974081 := bstep (se 2 (by rfl) ⟨365280, by rfl⟩ : syracuseStep 974081 = 730561) B730561
theorem B3333469 : Blo 338752 3333469 := bstep (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) B1250051
theorem B1727891 : Blo 338752 1727891 := bstep (se 1 (by rfl) ⟨1295918, by rfl⟩ : syracuseStep 1727891 = 2591837) B2591837
theorem B646699 : Blo 338752 646699 := bstep (se 1 (by rfl) ⟨485024, by rfl⟩ : syracuseStep 646699 = 970049) B970049
theorem B974423 : Blo 338752 974423 := bstep (se 1 (by rfl) ⟨730817, by rfl⟩ : syracuseStep 974423 = 1461635) B1461635
theorem B646775 : Blo 338752 646775 := bstep (se 1 (by rfl) ⟨485081, by rfl⟩ : syracuseStep 646775 = 970163) B970163
theorem B1007239 : Blo 338752 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B384655 : Blo 338752 384655 := bstep (se 1 (by rfl) ⟨288491, by rfl⟩ : syracuseStep 384655 = 576983) B576983
theorem B974537 : Blo 338752 974537 := bstep (se 2 (by rfl) ⟨365451, by rfl⟩ : syracuseStep 974537 = 730903) B730903
theorem B483259 : Blo 338752 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B385159 : Blo 338752 385159 := bstep (se 1 (by rfl) ⟨288869, by rfl⟩ : syracuseStep 385159 = 577739) B577739
theorem B3891401 : Blo 338752 3891401 := bstep (se 2 (by rfl) ⟨1459275, by rfl⟩ : syracuseStep 3891401 = 2918551) B2918551
theorem B385339 : Blo 338752 385339 := bstep (se 1 (by rfl) ⟨289004, by rfl⟩ : syracuseStep 385339 = 578009) B578009
theorem B517051 : Blo 338752 517051 := bstep (se 1 (by rfl) ⟨387788, by rfl⟩ : syracuseStep 517051 = 775577) B775577
theorem B779399 : Blo 338752 779399 := bstep (se 1 (by rfl) ⟨584549, by rfl⟩ : syracuseStep 779399 = 1169099) B1169099
theorem B484751 : Blo 338752 484751 := bstep (se 1 (by rfl) ⟨363563, by rfl⟩ : syracuseStep 484751 = 727127) B727127
theorem B648719 : Blo 338752 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B1402429 : Blo 338752 1402429 := bstep (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) B525911
theorem B1631981 : Blo 338752 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B6973613 : Blo 338752 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B8251793 : Blo 338752 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B1730969 : Blo 338752 1730969 := bstep (se 2 (by rfl) ⟨649113, by rfl⟩ : syracuseStep 1730969 = 1298227) B1298227
theorem B485833 : Blo 338752 485833 := bstep (se 2 (by rfl) ⟨182187, by rfl⟩ : syracuseStep 485833 = 364375) B364375
theorem B485947 : Blo 338752 485947 := bstep (se 1 (by rfl) ⟨364460, by rfl⟩ : syracuseStep 485947 = 728921) B728921
theorem B2911139 : Blo 338752 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B2583575 : Blo 338752 2583575 := bstep (se 1 (by rfl) ⟨1937681, by rfl⟩ : syracuseStep 2583575 = 3875363) B3875363
theorem B3894317 : Blo 338752 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B650359 : Blo 338752 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B814607 : Blo 338752 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B2911787 : Blo 338752 2911787 := bstep (se 1 (by rfl) ⟨2183840, by rfl⟩ : syracuseStep 2911787 = 4367681) B4367681
theorem B454391 : Blo 338752 454391 := bstep (se 1 (by rfl) ⟨340793, by rfl⟩ : syracuseStep 454391 = 681587) B681587
theorem B487559 : Blo 338752 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B2060633 : Blo 338752 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B1143611 : Blo 338752 1143611 := bstep (se 1 (by rfl) ⟨857708, by rfl⟩ : syracuseStep 1143611 = 1715417) B1715417
theorem B521095 : Blo 338752 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B1733561 : Blo 338752 1733561 := bstep (se 2 (by rfl) ⟨650085, by rfl⟩ : syracuseStep 1733561 = 1300171) B1300171
theorem B4912139 : Blo 338752 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B1930301 : Blo 338752 1930301 := bstep (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) B723863
theorem B1144097 : Blo 338752 1144097 := bstep (se 2 (by rfl) ⟨429036, by rfl⟩ : syracuseStep 1144097 = 858073) B858073
theorem B7337249 : Blo 338752 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B16774685 : Blo 338752 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B1144691 : Blo 338752 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B980851 : Blo 338752 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B1112093 : Blo 338752 1112093 := bstep (se 3 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 1112093 = 417035) B417035
theorem B1734857 : Blo 338752 1734857 := bstep (se 2 (by rfl) ⟨650571, by rfl⟩ : syracuseStep 1734857 = 1301143) B1301143
theorem B1374731 : Blo 338752 1374731 := bstep (se 1 (by rfl) ⟨1031048, by rfl⟩ : syracuseStep 1374731 = 2062097) B2062097
theorem B981533 : Blo 338752 981533 := bstep (se 3 (by rfl) ⟨184037, by rfl⟩ : syracuseStep 981533 = 368075) B368075
theorem B817921 : Blo 338752 817921 := bstep (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) B613441
theorem B2063141 : Blo 338752 2063141 := bstep (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) B386839
theorem B7863155 : Blo 338752 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B818191 : Blo 338752 818191 := bstep (se 1 (by rfl) ⟨613643, by rfl⟩ : syracuseStep 818191 = 1227287) B1227287
theorem B916615 : Blo 338752 916615 := bstep (se 1 (by rfl) ⟨687461, by rfl⟩ : syracuseStep 916615 = 1374923) B1374923
theorem B818633 : Blo 338752 818633 := bstep (se 2 (by rfl) ⟨306987, by rfl⟩ : syracuseStep 818633 = 613975) B613975
theorem B67927853 : Blo 338752 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B655379 : Blo 338752 655379 := bstep (se 1 (by rfl) ⟨491534, by rfl⟩ : syracuseStep 655379 = 983069) B983069
theorem B1146959 : Blo 338752 1146959 := bstep (se 1 (by rfl) ⟨860219, by rfl⟩ : syracuseStep 1146959 = 1720439) B1720439
theorem B1933469 : Blo 338752 1933469 := bstep (se 3 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 1933469 = 725051) B725051
theorem B2621783 : Blo 338752 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B1147337 : Blo 338752 1147337 := bstep (se 2 (by rfl) ⟨430251, by rfl⟩ : syracuseStep 1147337 = 860503) B860503
theorem B4915829 : Blo 338752 4915829 := bstep (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) B460859
theorem B524999 : Blo 338752 524999 := bstep (se 1 (by rfl) ⟨393749, by rfl⟩ : syracuseStep 524999 = 787499) B787499
theorem B1147607 : Blo 338752 1147607 := bstep (se 1 (by rfl) ⟨860705, by rfl⟩ : syracuseStep 1147607 = 1721411) B1721411
theorem B3113801 : Blo 338752 3113801 := bstep (se 2 (by rfl) ⟨1167675, by rfl⟩ : syracuseStep 3113801 = 2335351) B2335351
theorem B10617749 : Blo 338752 10617749 := bstep (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) B497707
theorem B1147823 : Blo 338752 1147823 := bstep (se 1 (by rfl) ⟨860867, by rfl⟩ : syracuseStep 1147823 = 1721735) B1721735
theorem B459703 : Blo 338752 459703 := bstep (se 1 (by rfl) ⟨344777, by rfl⟩ : syracuseStep 459703 = 689555) B689555
theorem B2458667 : Blo 338752 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B24052787 : Blo 338752 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B689401 : Blo 338752 689401 := bstep (se 2 (by rfl) ⟨258525, by rfl⟩ : syracuseStep 689401 = 517051) B517051
theorem B2491813 : Blo 338752 2491813 := bstep (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) B467215
theorem B919471 : Blo 338752 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B1869905 : Blo 338752 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B1935677 : Blo 338752 1935677 := bstep (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) B725879
theorem B2459965 : Blo 338752 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B1313111 : Blo 338752 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B4655645 : Blo 338752 4655645 := bstep (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) B1745867
theorem B428743 : Blo 338752 428743 := bstep (se 1 (by rfl) ⟨321557, by rfl⟩ : syracuseStep 428743 = 643115) B643115
theorem B2329489 : Blo 338752 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B1936385 : Blo 338752 1936385 := bstep (se 2 (by rfl) ⟨726144, by rfl⟩ : syracuseStep 1936385 = 1452289) B1452289
theorem B1150199 : Blo 338752 1150199 := bstep (se 1 (by rfl) ⟨862649, by rfl⟩ : syracuseStep 1150199 = 1725299) B1725299
theorem B1150523 : Blo 338752 1150523 := bstep (se 1 (by rfl) ⟨862892, by rfl⟩ : syracuseStep 1150523 = 1725785) B1725785
theorem B1150793 : Blo 338752 1150793 := bstep (se 2 (by rfl) ⟨431547, by rfl⟩ : syracuseStep 1150793 = 863095) B863095
theorem B4362245 : Blo 338752 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B692231 : Blo 338752 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B823303 : Blo 338752 823303 := bstep (se 1 (by rfl) ⟨617477, by rfl⟩ : syracuseStep 823303 = 1234955) B1234955
theorem B692263 : Blo 338752 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B922151 : Blo 338752 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1249939 : Blo 338752 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B10490579 : Blo 338752 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B1151927 : Blo 338752 1151927 := bstep (se 1 (by rfl) ⟨863945, by rfl⟩ : syracuseStep 1151927 = 1727891) B1727891
theorem B431183 : Blo 338752 431183 := bstep (se 1 (by rfl) ⟨323387, by rfl⟩ : syracuseStep 431183 = 646775) B646775
theorem B726187 : Blo 338752 726187 := bstep (se 1 (by rfl) ⟨544640, by rfl⟩ : syracuseStep 726187 = 1089281) B1089281
theorem B2594267 : Blo 338752 2594267 := bstep (se 1 (by rfl) ⟨1945700, by rfl⟩ : syracuseStep 2594267 = 3891401) B3891401
theorem B857587 : Blo 338752 857587 := bstep (se 1 (by rfl) ⟨643190, by rfl⟩ : syracuseStep 857587 = 1286381) B1286381
theorem B1152521 : Blo 338752 1152521 := bstep (se 2 (by rfl) ⟨432195, by rfl⟩ : syracuseStep 1152521 = 864391) B864391
theorem B923233 : Blo 338752 923233 := bstep (se 2 (by rfl) ⟨346212, by rfl⟩ : syracuseStep 923233 = 692425) B692425
theorem B2594753 : Blo 338752 2594753 := bstep (se 2 (by rfl) ⟨973032, by rfl⟩ : syracuseStep 2594753 = 1946065) B1946065
theorem B4888613 : Blo 338752 4888613 := bstep (se 4 (by rfl) ⟨458307, by rfl⟩ : syracuseStep 4888613 = 916615) B916615
theorem B432479 : Blo 338752 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B1153385 : Blo 338752 1153385 := bstep (se 2 (by rfl) ⟨432519, by rfl⟩ : syracuseStep 1153385 = 865039) B865039
theorem B14686595 : Blo 338752 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B1087987 : Blo 338752 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B694793 : Blo 338752 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B629305 : Blo 338752 629305 := bstep (se 2 (by rfl) ⟨235989, by rfl⟩ : syracuseStep 629305 = 471979) B471979
theorem B858721 : Blo 338752 858721 := bstep (se 2 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 858721 = 644041) B644041
theorem B11082419 : Blo 338752 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B1383097 : Blo 338752 1383097 := bstep (se 2 (by rfl) ⟨518661, by rfl⟩ : syracuseStep 1383097 = 1037323) B1037323
theorem B1317575 : Blo 338752 1317575 := bstep (se 1 (by rfl) ⟨988181, by rfl⟩ : syracuseStep 1317575 = 1976363) B1976363
theorem B1383263 : Blo 338752 1383263 := bstep (se 1 (by rfl) ⟨1037447, by rfl⟩ : syracuseStep 1383263 = 2074895) B2074895
theorem B1153979 : Blo 338752 1153979 := bstep (se 1 (by rfl) ⟨865484, by rfl⟩ : syracuseStep 1153979 = 1730969) B1730969
theorem B1940759 : Blo 338752 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B2596211 : Blo 338752 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B859673 : Blo 338752 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B9772609 : Blo 338752 9772609 := bstep (se 2 (by rfl) ⟨3664728, by rfl⟩ : syracuseStep 9772609 = 7329457) B7329457
theorem B1941191 : Blo 338752 1941191 := bstep (se 1 (by rfl) ⟨1455893, by rfl⟩ : syracuseStep 1941191 = 2911787) B2911787
theorem B7020269 : Blo 338752 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B1384265 : Blo 338752 1384265 := bstep (se 2 (by rfl) ⟨519099, by rfl⟩ : syracuseStep 1384265 = 1038199) B1038199
theorem B860179 : Blo 338752 860179 := bstep (se 1 (by rfl) ⟨645134, by rfl⟩ : syracuseStep 860179 = 1290269) B1290269
theorem B762407 : Blo 338752 762407 := bstep (se 1 (by rfl) ⟨571805, by rfl⟩ : syracuseStep 762407 = 1143611) B1143611
theorem B1155707 : Blo 338752 1155707 := bstep (se 1 (by rfl) ⟨866780, by rfl⟩ : syracuseStep 1155707 = 1733561) B1733561
theorem B1286867 : Blo 338752 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B1155869 : Blo 338752 1155869 := bstep (se 3 (by rfl) ⟨216725, by rfl⟩ : syracuseStep 1155869 = 433451) B433451
theorem B762731 : Blo 338752 762731 := bstep (se 1 (by rfl) ⟨572048, by rfl⟩ : syracuseStep 762731 = 1144097) B1144097
theorem B4891499 : Blo 338752 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B762785 : Blo 338752 762785 := bstep (se 2 (by rfl) ⟨286044, by rfl⟩ : syracuseStep 762785 = 572089) B572089
theorem B11183123 : Blo 338752 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B861263 : Blo 338752 861263 := bstep (se 1 (by rfl) ⟨645947, by rfl⟩ : syracuseStep 861263 = 1291895) B1291895
theorem B763127 : Blo 338752 763127 := bstep (se 1 (by rfl) ⟨572345, by rfl⟩ : syracuseStep 763127 = 1144691) B1144691
theorem B1090921 : Blo 338752 1090921 := bstep (se 2 (by rfl) ⟨409095, by rfl⟩ : syracuseStep 1090921 = 818191) B818191
theorem B1156571 : Blo 338752 1156571 := bstep (se 1 (by rfl) ⟨867428, by rfl⟩ : syracuseStep 1156571 = 1734857) B1734857
theorem B861911 : Blo 338752 861911 := bstep (se 1 (by rfl) ⟨646433, by rfl⟩ : syracuseStep 861911 = 1292867) B1292867
theorem B763721 : Blo 338752 763721 := bstep (se 2 (by rfl) ⟨286395, by rfl⟩ : syracuseStep 763721 = 572791) B572791
theorem B862265 : Blo 338752 862265 := bstep (se 2 (by rfl) ⟨323349, by rfl⟩ : syracuseStep 862265 = 646699) B646699
theorem B764513 : Blo 338752 764513 := bstep (se 2 (by rfl) ⟨286692, by rfl⟩ : syracuseStep 764513 = 573385) B573385
theorem B338767 : Blo 338752 338767 := bstep (se 1 (by rfl) ⟨254075, by rfl⟩ : syracuseStep 338767 = 508151) B508151
theorem B338783 : Blo 338752 338783 := bstep (se 1 (by rfl) ⟨254087, by rfl⟩ : syracuseStep 338783 = 508175) B508175
theorem B338811 : Blo 338752 338811 := bstep (se 1 (by rfl) ⟨254108, by rfl⟩ : syracuseStep 338811 = 508217) B508217
theorem B338863 : Blo 338752 338863 := bstep (se 1 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 338863 = 508295) B508295
theorem B764855 : Blo 338752 764855 := bstep (se 1 (by rfl) ⟨573641, by rfl⟩ : syracuseStep 764855 = 1147283) B1147283
theorem B338887 : Blo 338752 338887 := bstep (se 1 (by rfl) ⟨254165, by rfl⟩ : syracuseStep 338887 = 508331) B508331
theorem B338907 : Blo 338752 338907 := bstep (se 1 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 338907 = 508361) B508361
theorem B338983 : Blo 338752 338983 := bstep (se 1 (by rfl) ⟨254237, by rfl⟩ : syracuseStep 338983 = 508475) B508475
theorem B339023 : Blo 338752 339023 := bstep (se 1 (by rfl) ⟨254267, by rfl⟩ : syracuseStep 339023 = 508535) B508535
theorem B1289297 : Blo 338752 1289297 := bstep (se 2 (by rfl) ⟨483486, by rfl⟩ : syracuseStep 1289297 = 966973) B966973
theorem B339039 : Blo 338752 339039 := bstep (se 1 (by rfl) ⟨254279, by rfl⟩ : syracuseStep 339039 = 508559) B508559
theorem B339067 : Blo 338752 339067 := bstep (se 1 (by rfl) ⟨254300, by rfl⟩ : syracuseStep 339067 = 508601) B508601
theorem B339119 : Blo 338752 339119 := bstep (se 1 (by rfl) ⟨254339, by rfl⟩ : syracuseStep 339119 = 508679) B508679
theorem B2895041 : Blo 338752 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B339143 : Blo 338752 339143 := bstep (se 1 (by rfl) ⟨254357, by rfl⟩ : syracuseStep 339143 = 508715) B508715
theorem B339163 : Blo 338752 339163 := bstep (se 1 (by rfl) ⟨254372, by rfl⟩ : syracuseStep 339163 = 508745) B508745
theorem B339239 : Blo 338752 339239 := bstep (se 1 (by rfl) ⟨254429, by rfl⟩ : syracuseStep 339239 = 508859) B508859
theorem B339279 : Blo 338752 339279 := bstep (se 1 (by rfl) ⟨254459, by rfl⟩ : syracuseStep 339279 = 508919) B508919
theorem B339295 : Blo 338752 339295 := bstep (se 1 (by rfl) ⟨254471, by rfl⟩ : syracuseStep 339295 = 508943) B508943
theorem B339323 : Blo 338752 339323 := bstep (se 1 (by rfl) ⟨254492, by rfl⟩ : syracuseStep 339323 = 508985) B508985
theorem B339375 : Blo 338752 339375 := bstep (se 1 (by rfl) ⟨254531, by rfl⟩ : syracuseStep 339375 = 509063) B509063
theorem B4926901 : Blo 338752 4926901 := bstep (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) B461897
theorem B339399 : Blo 338752 339399 := bstep (se 1 (by rfl) ⟨254549, by rfl⟩ : syracuseStep 339399 = 509099) B509099
theorem B339419 : Blo 338752 339419 := bstep (se 1 (by rfl) ⟨254564, by rfl⟩ : syracuseStep 339419 = 509129) B509129
theorem B1224173 : Blo 338752 1224173 := bstep (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) B459065
theorem B765449 : Blo 338752 765449 := bstep (se 2 (by rfl) ⟨287043, by rfl⟩ : syracuseStep 765449 = 574087) B574087
theorem B1289753 : Blo 338752 1289753 := bstep (se 2 (by rfl) ⟨483657, by rfl⟩ : syracuseStep 1289753 = 967315) B967315
theorem B339495 : Blo 338752 339495 := bstep (se 1 (by rfl) ⟨254621, by rfl⟩ : syracuseStep 339495 = 509243) B509243
theorem B339535 : Blo 338752 339535 := bstep (se 1 (by rfl) ⟨254651, by rfl⟩ : syracuseStep 339535 = 509303) B509303
theorem B339551 : Blo 338752 339551 := bstep (se 1 (by rfl) ⟨254663, by rfl⟩ : syracuseStep 339551 = 509327) B509327
theorem B339579 : Blo 338752 339579 := bstep (se 1 (by rfl) ⟨254684, by rfl⟩ : syracuseStep 339579 = 509369) B509369
theorem B339631 : Blo 338752 339631 := bstep (se 1 (by rfl) ⟨254723, by rfl⟩ : syracuseStep 339631 = 509447) B509447
theorem B339655 : Blo 338752 339655 := bstep (se 1 (by rfl) ⟨254741, by rfl⟩ : syracuseStep 339655 = 509483) B509483
theorem B339675 : Blo 338752 339675 := bstep (se 1 (by rfl) ⟨254756, by rfl⟩ : syracuseStep 339675 = 509513) B509513
theorem B339751 : Blo 338752 339751 := bstep (se 1 (by rfl) ⟨254813, by rfl⟩ : syracuseStep 339751 = 509627) B509627
theorem B339791 : Blo 338752 339791 := bstep (se 1 (by rfl) ⟨254843, by rfl⟩ : syracuseStep 339791 = 509687) B509687
theorem B339807 : Blo 338752 339807 := bstep (se 1 (by rfl) ⟨254855, by rfl⟩ : syracuseStep 339807 = 509711) B509711
theorem B765791 : Blo 338752 765791 := bstep (se 1 (by rfl) ⟨574343, by rfl⟩ : syracuseStep 765791 = 1148687) B1148687
theorem B339835 : Blo 338752 339835 := bstep (se 1 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 339835 = 509753) B509753
theorem B339887 : Blo 338752 339887 := bstep (se 1 (by rfl) ⟨254915, by rfl⟩ : syracuseStep 339887 = 509831) B509831
theorem B3092411 : Blo 338752 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B339911 : Blo 338752 339911 := bstep (se 1 (by rfl) ⟨254933, by rfl⟩ : syracuseStep 339911 = 509867) B509867
theorem B339931 : Blo 338752 339931 := bstep (se 1 (by rfl) ⟨254948, by rfl⟩ : syracuseStep 339931 = 509897) B509897
theorem B765971 : Blo 338752 765971 := bstep (se 1 (by rfl) ⟨574478, by rfl⟩ : syracuseStep 765971 = 1148957) B1148957
theorem B340007 : Blo 338752 340007 := bstep (se 1 (by rfl) ⟨255005, by rfl⟩ : syracuseStep 340007 = 510011) B510011
theorem B1159247 : Blo 338752 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B340047 : Blo 338752 340047 := bstep (se 1 (by rfl) ⟨255035, by rfl⟩ : syracuseStep 340047 = 510071) B510071
theorem B340063 : Blo 338752 340063 := bstep (se 1 (by rfl) ⟨255047, by rfl⟩ : syracuseStep 340063 = 510095) B510095
theorem B340091 : Blo 338752 340091 := bstep (se 1 (by rfl) ⟨255068, by rfl⟩ : syracuseStep 340091 = 510137) B510137
theorem B340143 : Blo 338752 340143 := bstep (se 1 (by rfl) ⟨255107, by rfl⟩ : syracuseStep 340143 = 510215) B510215
theorem B340167 : Blo 338752 340167 := bstep (se 1 (by rfl) ⟨255125, by rfl⟩ : syracuseStep 340167 = 510251) B510251
theorem B340187 : Blo 338752 340187 := bstep (se 1 (by rfl) ⟨255140, by rfl⟩ : syracuseStep 340187 = 510281) B510281
theorem B864503 : Blo 338752 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B340263 : Blo 338752 340263 := bstep (se 1 (by rfl) ⟨255197, by rfl⟩ : syracuseStep 340263 = 510395) B510395
theorem B340303 : Blo 338752 340303 := bstep (se 1 (by rfl) ⟨255227, by rfl⟩ : syracuseStep 340303 = 510455) B510455
theorem B340319 : Blo 338752 340319 := bstep (se 1 (by rfl) ⟨255239, by rfl⟩ : syracuseStep 340319 = 510479) B510479
theorem B766313 : Blo 338752 766313 := bstep (se 2 (by rfl) ⟨287367, by rfl⟩ : syracuseStep 766313 = 574735) B574735
theorem B340347 : Blo 338752 340347 := bstep (se 1 (by rfl) ⟨255260, by rfl⟩ : syracuseStep 340347 = 510521) B510521
theorem B340399 : Blo 338752 340399 := bstep (se 1 (by rfl) ⟨255299, by rfl⟩ : syracuseStep 340399 = 510599) B510599
theorem B340423 : Blo 338752 340423 := bstep (se 1 (by rfl) ⟨255317, by rfl⟩ : syracuseStep 340423 = 510635) B510635
theorem B340443 : Blo 338752 340443 := bstep (se 1 (by rfl) ⟨255332, by rfl⟩ : syracuseStep 340443 = 510665) B510665
theorem B340519 : Blo 338752 340519 := bstep (se 1 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 340519 = 510779) B510779
theorem B2470459 : Blo 338752 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B340559 : Blo 338752 340559 := bstep (se 1 (by rfl) ⟨255419, by rfl⟩ : syracuseStep 340559 = 510839) B510839
theorem B340575 : Blo 338752 340575 := bstep (se 1 (by rfl) ⟨255431, by rfl⟩ : syracuseStep 340575 = 510863) B510863
theorem B340603 : Blo 338752 340603 := bstep (se 1 (by rfl) ⟨255452, by rfl⟩ : syracuseStep 340603 = 510905) B510905
theorem B340655 : Blo 338752 340655 := bstep (se 1 (by rfl) ⟨255491, by rfl⟩ : syracuseStep 340655 = 510983) B510983
theorem B1290937 : Blo 338752 1290937 := bstep (se 2 (by rfl) ⟨484101, by rfl⟩ : syracuseStep 1290937 = 968203) B968203
theorem B340679 : Blo 338752 340679 := bstep (se 1 (by rfl) ⟨255509, by rfl⟩ : syracuseStep 340679 = 511019) B511019
theorem B340699 : Blo 338752 340699 := bstep (se 1 (by rfl) ⟨255524, by rfl⟩ : syracuseStep 340699 = 511049) B511049
theorem B340775 : Blo 338752 340775 := bstep (se 1 (by rfl) ⟨255581, by rfl⟩ : syracuseStep 340775 = 511163) B511163
theorem B340815 : Blo 338752 340815 := bstep (se 1 (by rfl) ⟨255611, by rfl⟩ : syracuseStep 340815 = 511223) B511223
theorem B340831 : Blo 338752 340831 := bstep (se 1 (by rfl) ⟨255623, by rfl⟩ : syracuseStep 340831 = 511247) B511247
theorem B340859 : Blo 338752 340859 := bstep (se 1 (by rfl) ⟨255644, by rfl⟩ : syracuseStep 340859 = 511289) B511289
theorem B1455023 : Blo 338752 1455023 := bstep (se 1 (by rfl) ⟨1091267, by rfl⟩ : syracuseStep 1455023 = 2182535) B2182535
theorem B340911 : Blo 338752 340911 := bstep (se 1 (by rfl) ⟨255683, by rfl⟩ : syracuseStep 340911 = 511367) B511367
theorem B766907 : Blo 338752 766907 := bstep (se 1 (by rfl) ⟨575180, by rfl⟩ : syracuseStep 766907 = 1150361) B1150361
theorem B340935 : Blo 338752 340935 := bstep (se 1 (by rfl) ⟨255701, by rfl⟩ : syracuseStep 340935 = 511403) B511403
theorem B340955 : Blo 338752 340955 := bstep (se 1 (by rfl) ⟨255716, by rfl⟩ : syracuseStep 340955 = 511433) B511433
theorem B341031 : Blo 338752 341031 := bstep (se 1 (by rfl) ⟨255773, by rfl⟩ : syracuseStep 341031 = 511547) B511547
theorem B767033 : Blo 338752 767033 := bstep (se 2 (by rfl) ⟨287637, by rfl⟩ : syracuseStep 767033 = 575275) B575275
theorem B341071 : Blo 338752 341071 := bstep (se 1 (by rfl) ⟨255803, by rfl⟩ : syracuseStep 341071 = 511607) B511607
theorem B341087 : Blo 338752 341087 := bstep (se 1 (by rfl) ⟨255815, by rfl⟩ : syracuseStep 341087 = 511631) B511631
theorem B341115 : Blo 338752 341115 := bstep (se 1 (by rfl) ⟨255836, by rfl⟩ : syracuseStep 341115 = 511673) B511673
theorem B341167 : Blo 338752 341167 := bstep (se 1 (by rfl) ⟨255875, by rfl⟩ : syracuseStep 341167 = 511751) B511751
theorem B341191 : Blo 338752 341191 := bstep (se 1 (by rfl) ⟨255893, by rfl⟩ : syracuseStep 341191 = 511787) B511787
theorem B341211 : Blo 338752 341211 := bstep (se 1 (by rfl) ⟨255908, by rfl⟩ : syracuseStep 341211 = 511817) B511817
theorem B341287 : Blo 338752 341287 := bstep (se 1 (by rfl) ⟨255965, by rfl⟩ : syracuseStep 341287 = 511931) B511931
theorem B341327 : Blo 338752 341327 := bstep (se 1 (by rfl) ⟨255995, by rfl⟩ : syracuseStep 341327 = 511991) B511991
theorem B341343 : Blo 338752 341343 := bstep (se 1 (by rfl) ⟨256007, by rfl⟩ : syracuseStep 341343 = 512015) B512015
theorem B3093875 : Blo 338752 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B341371 : Blo 338752 341371 := bstep (se 1 (by rfl) ⟨256028, by rfl⟩ : syracuseStep 341371 = 512057) B512057
theorem B767375 : Blo 338752 767375 := bstep (se 1 (by rfl) ⟨575531, by rfl⟩ : syracuseStep 767375 = 1151063) B1151063
theorem B1947023 : Blo 338752 1947023 := bstep (se 1 (by rfl) ⟨1460267, by rfl⟩ : syracuseStep 1947023 = 2920535) B2920535
theorem B341423 : Blo 338752 341423 := bstep (se 1 (by rfl) ⟨256067, by rfl⟩ : syracuseStep 341423 = 512135) B512135
theorem B341447 : Blo 338752 341447 := bstep (se 1 (by rfl) ⟨256085, by rfl⟩ : syracuseStep 341447 = 512171) B512171
theorem B341467 : Blo 338752 341467 := bstep (se 1 (by rfl) ⟨256100, by rfl⟩ : syracuseStep 341467 = 512201) B512201
theorem B341543 : Blo 338752 341543 := bstep (se 1 (by rfl) ⟨256157, by rfl⟩ : syracuseStep 341543 = 512315) B512315
theorem B1095227 : Blo 338752 1095227 := bstep (se 1 (by rfl) ⟨821420, by rfl⟩ : syracuseStep 1095227 = 1642841) B1642841
theorem B341583 : Blo 338752 341583 := bstep (se 1 (by rfl) ⟨256187, by rfl⟩ : syracuseStep 341583 = 512375) B512375
theorem B341599 : Blo 338752 341599 := bstep (se 1 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 341599 = 512399) B512399
theorem B341627 : Blo 338752 341627 := bstep (se 1 (by rfl) ⟨256220, by rfl⟩ : syracuseStep 341627 = 512441) B512441
theorem B341679 : Blo 338752 341679 := bstep (se 1 (by rfl) ⟨256259, by rfl⟩ : syracuseStep 341679 = 512519) B512519
theorem B341703 : Blo 338752 341703 := bstep (se 1 (by rfl) ⟨256277, by rfl⟩ : syracuseStep 341703 = 512555) B512555
theorem B865991 : Blo 338752 865991 := bstep (se 1 (by rfl) ⟨649493, by rfl⟩ : syracuseStep 865991 = 1298987) B1298987
theorem B767699 : Blo 338752 767699 := bstep (se 1 (by rfl) ⟨575774, by rfl⟩ : syracuseStep 767699 = 1151549) B1151549
theorem B341723 : Blo 338752 341723 := bstep (se 1 (by rfl) ⟨256292, by rfl⟩ : syracuseStep 341723 = 512585) B512585
theorem B1718009 : Blo 338752 1718009 := bstep (se 2 (by rfl) ⟨644253, by rfl⟩ : syracuseStep 1718009 = 1288507) B1288507
theorem B341799 : Blo 338752 341799 := bstep (se 1 (by rfl) ⟨256349, by rfl⟩ : syracuseStep 341799 = 512699) B512699
theorem B341839 : Blo 338752 341839 := bstep (se 1 (by rfl) ⟨256379, by rfl⟩ : syracuseStep 341839 = 512759) B512759
theorem B341855 : Blo 338752 341855 := bstep (se 1 (by rfl) ⟨256391, by rfl⟩ : syracuseStep 341855 = 512783) B512783
theorem B341883 : Blo 338752 341883 := bstep (se 1 (by rfl) ⟨256412, by rfl⟩ : syracuseStep 341883 = 512825) B512825
theorem B341935 : Blo 338752 341935 := bstep (se 1 (by rfl) ⟨256451, by rfl⟩ : syracuseStep 341935 = 512903) B512903
theorem B341959 : Blo 338752 341959 := bstep (se 1 (by rfl) ⟨256469, by rfl⟩ : syracuseStep 341959 = 512939) B512939
theorem B341979 : Blo 338752 341979 := bstep (se 1 (by rfl) ⟨256484, by rfl⟩ : syracuseStep 341979 = 512969) B512969
theorem B1226767 : Blo 338752 1226767 := bstep (se 1 (by rfl) ⟨920075, by rfl⟩ : syracuseStep 1226767 = 1840151) B1840151
theorem B342055 : Blo 338752 342055 := bstep (se 1 (by rfl) ⟨256541, by rfl⟩ : syracuseStep 342055 = 513083) B513083
theorem B342095 : Blo 338752 342095 := bstep (se 1 (by rfl) ⟨256571, by rfl⟩ : syracuseStep 342095 = 513143) B513143
theorem B342111 : Blo 338752 342111 := bstep (se 1 (by rfl) ⟨256583, by rfl⟩ : syracuseStep 342111 = 513167) B513167
theorem B342139 : Blo 338752 342139 := bstep (se 1 (by rfl) ⟨256604, by rfl⟩ : syracuseStep 342139 = 513209) B513209
theorem B342191 : Blo 338752 342191 := bstep (se 1 (by rfl) ⟨256643, by rfl⟩ : syracuseStep 342191 = 513287) B513287
theorem B342215 : Blo 338752 342215 := bstep (se 1 (by rfl) ⟨256661, by rfl⟩ : syracuseStep 342215 = 513323) B513323
theorem B342235 : Blo 338752 342235 := bstep (se 1 (by rfl) ⟨256676, by rfl⟩ : syracuseStep 342235 = 513353) B513353
theorem B342311 : Blo 338752 342311 := bstep (se 1 (by rfl) ⟨256733, by rfl⟩ : syracuseStep 342311 = 513467) B513467
theorem B342351 : Blo 338752 342351 := bstep (se 1 (by rfl) ⟨256763, by rfl⟩ : syracuseStep 342351 = 513527) B513527
theorem B342367 : Blo 338752 342367 := bstep (se 1 (by rfl) ⟨256775, by rfl⟩ : syracuseStep 342367 = 513551) B513551
theorem B342395 : Blo 338752 342395 := bstep (se 1 (by rfl) ⟨256796, by rfl⟩ : syracuseStep 342395 = 513593) B513593
theorem B1292669 : Blo 338752 1292669 := bstep (se 3 (by rfl) ⟨242375, by rfl⟩ : syracuseStep 1292669 = 484751) B484751
theorem B1718657 : Blo 338752 1718657 := bstep (se 2 (by rfl) ⟨644496, by rfl⟩ : syracuseStep 1718657 = 1288993) B1288993
theorem B1554817 : Blo 338752 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B342447 : Blo 338752 342447 := bstep (se 1 (by rfl) ⟨256835, by rfl⟩ : syracuseStep 342447 = 513671) B513671
theorem B342471 : Blo 338752 342471 := bstep (se 1 (by rfl) ⟨256853, by rfl⟩ : syracuseStep 342471 = 513707) B513707
theorem B342491 : Blo 338752 342491 := bstep (se 1 (by rfl) ⟨256868, by rfl⟩ : syracuseStep 342491 = 513737) B513737
theorem B2406935 : Blo 338752 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B342567 : Blo 338752 342567 := bstep (se 1 (by rfl) ⟨256925, by rfl⟩ : syracuseStep 342567 = 513851) B513851
theorem B571961 : Blo 338752 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B342607 : Blo 338752 342607 := bstep (se 1 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 342607 = 513911) B513911
theorem B342623 : Blo 338752 342623 := bstep (se 1 (by rfl) ⟨256967, by rfl⟩ : syracuseStep 342623 = 513935) B513935
theorem B768635 : Blo 338752 768635 := bstep (se 1 (by rfl) ⟨576476, by rfl⟩ : syracuseStep 768635 = 1152953) B1152953
theorem B342651 : Blo 338752 342651 := bstep (se 1 (by rfl) ⟨256988, by rfl⟩ : syracuseStep 342651 = 513977) B513977
theorem B834187 : Blo 338752 834187 := bstep (se 1 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 834187 = 1251281) B1251281
theorem B342703 : Blo 338752 342703 := bstep (se 1 (by rfl) ⟨257027, by rfl⟩ : syracuseStep 342703 = 514055) B514055
theorem B342727 : Blo 338752 342727 := bstep (se 1 (by rfl) ⟨257045, by rfl⟩ : syracuseStep 342727 = 514091) B514091
theorem B342747 : Blo 338752 342747 := bstep (se 1 (by rfl) ⟨257060, by rfl⟩ : syracuseStep 342747 = 514121) B514121
theorem B768761 : Blo 338752 768761 := bstep (se 2 (by rfl) ⟨288285, by rfl⟩ : syracuseStep 768761 = 576571) B576571
theorem B867145 : Blo 338752 867145 := bstep (se 2 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 867145 = 650359) B650359
theorem B1162171 : Blo 338752 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B5848037 : Blo 338752 5848037 := bstep (se 4 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 5848037 = 1096507) B1096507
theorem B769031 : Blo 338752 769031 := bstep (se 1 (by rfl) ⟨576773, by rfl⟩ : syracuseStep 769031 = 1153547) B1153547
theorem B769103 : Blo 338752 769103 := bstep (se 1 (by rfl) ⟨576827, by rfl⟩ : syracuseStep 769103 = 1153655) B1153655
theorem B965789 : Blo 338752 965789 := bstep (se 3 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 965789 = 362171) B362171
theorem B1719467 : Blo 338752 1719467 := bstep (se 1 (by rfl) ⟨1289600, by rfl⟩ : syracuseStep 1719467 = 2579201) B2579201
theorem B572663 : Blo 338752 572663 := bstep (se 1 (by rfl) ⟨429497, by rfl⟩ : syracuseStep 572663 = 858995) B858995
theorem B966107 : Blo 338752 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B769499 : Blo 338752 769499 := bstep (se 1 (by rfl) ⟨577124, by rfl⟩ : syracuseStep 769499 = 1154249) B1154249
theorem B966131 : Blo 338752 966131 := bstep (se 1 (by rfl) ⟨724598, by rfl⟩ : syracuseStep 966131 = 1449197) B1449197
theorem B1228297 : Blo 338752 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B573007 : Blo 338752 573007 := bstep (se 1 (by rfl) ⟨429755, by rfl⟩ : syracuseStep 573007 = 859511) B859511
theorem B1719953 : Blo 338752 1719953 := bstep (se 2 (by rfl) ⟨644982, by rfl⟩ : syracuseStep 1719953 = 1289965) B1289965
theorem B4341437 : Blo 338752 4341437 := bstep (se 3 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 4341437 = 1628039) B1628039
theorem B1949507 : Blo 338752 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B573257 : Blo 338752 573257 := bstep (se 2 (by rfl) ⟨214971, by rfl⟩ : syracuseStep 573257 = 429943) B429943
theorem B769967 : Blo 338752 769967 := bstep (se 1 (by rfl) ⟨577475, by rfl⟩ : syracuseStep 769967 = 1154951) B1154951
theorem B1228727 : Blo 338752 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B770219 : Blo 338752 770219 := bstep (se 1 (by rfl) ⟨577664, by rfl⟩ : syracuseStep 770219 = 1155329) B1155329
theorem B573689 : Blo 338752 573689 := bstep (se 2 (by rfl) ⟨215133, by rfl⟩ : syracuseStep 573689 = 430267) B430267
theorem B1097995 : Blo 338752 1097995 := bstep (se 1 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 1097995 = 1646993) B1646993
theorem B508265 : Blo 338752 508265 := bstep (se 2 (by rfl) ⟨190599, by rfl⟩ : syracuseStep 508265 = 381199) B381199
theorem B573871 : Blo 338752 573871 := bstep (se 1 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 573871 = 860807) B860807
theorem B508343 : Blo 338752 508343 := bstep (se 1 (by rfl) ⟨381257, by rfl⟩ : syracuseStep 508343 = 762515) B762515
theorem B508379 : Blo 338752 508379 := bstep (se 1 (by rfl) ⟨381284, by rfl⟩ : syracuseStep 508379 = 762569) B762569
theorem B1294811 : Blo 338752 1294811 := bstep (se 1 (by rfl) ⟨971108, by rfl⟩ : syracuseStep 1294811 = 1942217) B1942217
theorem B573959 : Blo 338752 573959 := bstep (se 1 (by rfl) ⟨430469, by rfl⟩ : syracuseStep 573959 = 860939) B860939
theorem B770759 : Blo 338752 770759 := bstep (se 1 (by rfl) ⟨578069, by rfl⟩ : syracuseStep 770759 = 1156139) B1156139
theorem B574303 : Blo 338752 574303 := bstep (se 1 (by rfl) ⟨430727, by rfl⟩ : syracuseStep 574303 = 861455) B861455
theorem B508847 : Blo 338752 508847 := bstep (se 1 (by rfl) ⟨381635, by rfl⟩ : syracuseStep 508847 = 763271) B763271
theorem B574391 : Blo 338752 574391 := bstep (se 1 (by rfl) ⟨430793, by rfl⟩ : syracuseStep 574391 = 861587) B861587
theorem B508937 : Blo 338752 508937 := bstep (se 2 (by rfl) ⟨190851, by rfl⟩ : syracuseStep 508937 = 381703) B381703
theorem B508967 : Blo 338752 508967 := bstep (se 1 (by rfl) ⟨381725, by rfl⟩ : syracuseStep 508967 = 763451) B763451
theorem B509051 : Blo 338752 509051 := bstep (se 1 (by rfl) ⟨381788, by rfl⟩ : syracuseStep 509051 = 763577) B763577
theorem B509177 : Blo 338752 509177 := bstep (se 2 (by rfl) ⟨190941, by rfl⟩ : syracuseStep 509177 = 381883) B381883
theorem B509279 : Blo 338752 509279 := bstep (se 1 (by rfl) ⟨381959, by rfl⟩ : syracuseStep 509279 = 763919) B763919
theorem B509291 : Blo 338752 509291 := bstep (se 1 (by rfl) ⟨381968, by rfl⟩ : syracuseStep 509291 = 763937) B763937
theorem B574985 : Blo 338752 574985 := bstep (se 2 (by rfl) ⟨215619, by rfl⟩ : syracuseStep 574985 = 431239) B431239
theorem B509519 : Blo 338752 509519 := bstep (se 1 (by rfl) ⟨382139, by rfl⟩ : syracuseStep 509519 = 764279) B764279
theorem B575147 : Blo 338752 575147 := bstep (se 1 (by rfl) ⟨431360, by rfl⟩ : syracuseStep 575147 = 862721) B862721
theorem B509639 : Blo 338752 509639 := bstep (se 1 (by rfl) ⟨382229, by rfl⟩ : syracuseStep 509639 = 764459) B764459
theorem B1296071 : Blo 338752 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B509801 : Blo 338752 509801 := bstep (se 2 (by rfl) ⟨191175, by rfl⟩ : syracuseStep 509801 = 382351) B382351
theorem B1722221 : Blo 338752 1722221 := bstep (se 3 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 1722221 = 645833) B645833
theorem B509879 : Blo 338752 509879 := bstep (se 1 (by rfl) ⟨382409, by rfl⟩ : syracuseStep 509879 = 764819) B764819
theorem B509915 : Blo 338752 509915 := bstep (se 1 (by rfl) ⟨382436, by rfl⟩ : syracuseStep 509915 = 764873) B764873
theorem B1722383 : Blo 338752 1722383 := bstep (se 1 (by rfl) ⟨1291787, by rfl⟩ : syracuseStep 1722383 = 2583575) B2583575
theorem B575545 : Blo 338752 575545 := bstep (se 2 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 575545 = 431659) B431659
theorem B575687 : Blo 338752 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B543071 : Blo 338752 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B575849 : Blo 338752 575849 := bstep (se 2 (by rfl) ⟨215943, by rfl⟩ : syracuseStep 575849 = 431887) B431887
theorem B1296769 : Blo 338752 1296769 := bstep (se 2 (by rfl) ⟨486288, by rfl⟩ : syracuseStep 1296769 = 972577) B972577
theorem B510383 : Blo 338752 510383 := bstep (se 1 (by rfl) ⟨382787, by rfl⟩ : syracuseStep 510383 = 765575) B765575
theorem B510473 : Blo 338752 510473 := bstep (se 2 (by rfl) ⟨191427, by rfl⟩ : syracuseStep 510473 = 382855) B382855
theorem B510503 : Blo 338752 510503 := bstep (se 1 (by rfl) ⟨382877, by rfl⟩ : syracuseStep 510503 = 765755) B765755
theorem B510587 : Blo 338752 510587 := bstep (se 1 (by rfl) ⟨382940, by rfl⟩ : syracuseStep 510587 = 765881) B765881
theorem B1297043 : Blo 338752 1297043 := bstep (se 1 (by rfl) ⟨972782, by rfl⟩ : syracuseStep 1297043 = 1945565) B1945565
theorem B576247 : Blo 338752 576247 := bstep (se 1 (by rfl) ⟨432185, by rfl⟩ : syracuseStep 576247 = 864371) B864371
theorem B510713 : Blo 338752 510713 := bstep (se 2 (by rfl) ⟨191517, by rfl⟩ : syracuseStep 510713 = 383035) B383035
theorem B510815 : Blo 338752 510815 := bstep (se 1 (by rfl) ⟨383111, by rfl⟩ : syracuseStep 510815 = 766223) B766223
theorem B510827 : Blo 338752 510827 := bstep (se 1 (by rfl) ⟨383120, by rfl⟩ : syracuseStep 510827 = 766241) B766241
theorem B576443 : Blo 338752 576443 := bstep (se 1 (by rfl) ⟨432332, by rfl⟩ : syracuseStep 576443 = 864665) B864665
theorem B576551 : Blo 338752 576551 := bstep (se 1 (by rfl) ⟨432413, by rfl⟩ : syracuseStep 576551 = 864827) B864827
theorem B511055 : Blo 338752 511055 := bstep (se 1 (by rfl) ⟨383291, by rfl⟩ : syracuseStep 511055 = 766583) B766583
theorem B1756313 : Blo 338752 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B511175 : Blo 338752 511175 := bstep (se 1 (by rfl) ⟨383381, by rfl⟩ : syracuseStep 511175 = 766763) B766763
theorem B576841 : Blo 338752 576841 := bstep (se 2 (by rfl) ⟨216315, by rfl⟩ : syracuseStep 576841 = 432631) B432631
theorem B511337 : Blo 338752 511337 := bstep (se 2 (by rfl) ⟨191751, by rfl⟩ : syracuseStep 511337 = 383503) B383503
theorem B576875 : Blo 338752 576875 := bstep (se 1 (by rfl) ⟨432656, by rfl⟩ : syracuseStep 576875 = 865313) B865313
theorem B511415 : Blo 338752 511415 := bstep (se 1 (by rfl) ⟨383561, by rfl⟩ : syracuseStep 511415 = 767123) B767123
theorem B511451 : Blo 338752 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B2903789 : Blo 338752 2903789 := bstep (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) B1088921
theorem B577273 : Blo 338752 577273 := bstep (se 2 (by rfl) ⟨216477, by rfl⟩ : syracuseStep 577273 = 432955) B432955
theorem B2183021 : Blo 338752 2183021 := bstep (se 3 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 2183021 = 818633) B818633
theorem B511919 : Blo 338752 511919 := bstep (se 1 (by rfl) ⟨383939, by rfl⟩ : syracuseStep 511919 = 767879) B767879
theorem B577543 : Blo 338752 577543 := bstep (se 1 (by rfl) ⟨433157, by rfl⟩ : syracuseStep 577543 = 866315) B866315
theorem B512009 : Blo 338752 512009 := bstep (se 2 (by rfl) ⟨192003, by rfl⟩ : syracuseStep 512009 = 384007) B384007
theorem B4182031 : Blo 338752 4182031 := bstep (se 1 (by rfl) ⟨3136523, by rfl⟩ : syracuseStep 4182031 = 6273047) B6273047
theorem B741395 : Blo 338752 741395 := bstep (se 1 (by rfl) ⟨556046, by rfl⟩ : syracuseStep 741395 = 1112093) B1112093
theorem B512039 : Blo 338752 512039 := bstep (se 1 (by rfl) ⟨384029, by rfl⟩ : syracuseStep 512039 = 768059) B768059
theorem B512123 : Blo 338752 512123 := bstep (se 1 (by rfl) ⟨384092, by rfl⟩ : syracuseStep 512123 = 768185) B768185
theorem B1233053 : Blo 338752 1233053 := bstep (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) B462395
theorem B381127 : Blo 338752 381127 := bstep (se 1 (by rfl) ⟨285845, by rfl⟩ : syracuseStep 381127 = 571691) B571691
theorem B512249 : Blo 338752 512249 := bstep (se 2 (by rfl) ⟨192093, by rfl⟩ : syracuseStep 512249 = 384187) B384187
theorem B1298699 : Blo 338752 1298699 := bstep (se 1 (by rfl) ⟨974024, by rfl⟩ : syracuseStep 1298699 = 1948049) B1948049
theorem B512351 : Blo 338752 512351 := bstep (se 1 (by rfl) ⟨384263, by rfl⟩ : syracuseStep 512351 = 768527) B768527
theorem B512363 : Blo 338752 512363 := bstep (se 1 (by rfl) ⟨384272, by rfl⟩ : syracuseStep 512363 = 768545) B768545
theorem B577975 : Blo 338752 577975 := bstep (se 1 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 577975 = 866963) B866963
theorem B4444625 : Blo 338752 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B512591 : Blo 338752 512591 := bstep (se 1 (by rfl) ⟨384443, by rfl⟩ : syracuseStep 512591 = 768887) B768887
theorem B578171 : Blo 338752 578171 := bstep (se 1 (by rfl) ⟨433628, by rfl⟩ : syracuseStep 578171 = 867257) B867257
theorem B643783 : Blo 338752 643783 := bstep (se 1 (by rfl) ⟨482837, by rfl⟩ : syracuseStep 643783 = 965675) B965675
theorem B512711 : Blo 338752 512711 := bstep (se 1 (by rfl) ⟨384533, by rfl⟩ : syracuseStep 512711 = 769067) B769067
theorem B1725137 : Blo 338752 1725137 := bstep (se 2 (by rfl) ⟨646926, by rfl⟩ : syracuseStep 1725137 = 1293853) B1293853
theorem B11096837 : Blo 338752 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B512873 : Blo 338752 512873 := bstep (se 2 (by rfl) ⟨192327, by rfl⟩ : syracuseStep 512873 = 384655) B384655
theorem B1168303 : Blo 338752 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B512951 : Blo 338752 512951 := bstep (se 1 (by rfl) ⟨384713, by rfl⟩ : syracuseStep 512951 = 769427) B769427
theorem B512987 : Blo 338752 512987 := bstep (se 1 (by rfl) ⟨384740, by rfl⟩ : syracuseStep 512987 = 769481) B769481
theorem B3724289 : Blo 338752 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B381991 : Blo 338752 381991 := bstep (se 1 (by rfl) ⟨286493, by rfl⟩ : syracuseStep 381991 = 572987) B572987
theorem B1758287 : Blo 338752 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B644345 : Blo 338752 644345 := bstep (se 2 (by rfl) ⟨241629, by rfl⟩ : syracuseStep 644345 = 483259) B483259
theorem B644527 : Blo 338752 644527 := bstep (se 1 (by rfl) ⟨483395, by rfl⟩ : syracuseStep 644527 = 966791) B966791
theorem B513455 : Blo 338752 513455 := bstep (se 1 (by rfl) ⟨385091, by rfl⟩ : syracuseStep 513455 = 770183) B770183
theorem B1463771 : Blo 338752 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B513545 : Blo 338752 513545 := bstep (se 2 (by rfl) ⟨192579, by rfl⟩ : syracuseStep 513545 = 385159) B385159
theorem B513575 : Blo 338752 513575 := bstep (se 1 (by rfl) ⟨385181, by rfl⟩ : syracuseStep 513575 = 770363) B770363
theorem B546383 : Blo 338752 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B415355 : Blo 338752 415355 := bstep (se 1 (by rfl) ⟨311516, by rfl⟩ : syracuseStep 415355 = 623033) B623033
theorem B513659 : Blo 338752 513659 := bstep (se 1 (by rfl) ⟨385244, by rfl⟩ : syracuseStep 513659 = 770489) B770489
theorem B1300157 : Blo 338752 1300157 := bstep (se 3 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 1300157 = 487559) B487559
theorem B513785 : Blo 338752 513785 := bstep (se 2 (by rfl) ⟨192669, by rfl⟩ : syracuseStep 513785 = 385339) B385339
theorem B2185019 : Blo 338752 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B513887 : Blo 338752 513887 := bstep (se 1 (by rfl) ⟨385415, by rfl⟩ : syracuseStep 513887 = 770831) B770831
theorem B513899 : Blo 338752 513899 := bstep (se 1 (by rfl) ⟨385424, by rfl⟩ : syracuseStep 513899 = 770849) B770849
theorem B1234871 : Blo 338752 1234871 := bstep (se 1 (by rfl) ⟨926153, by rfl⟩ : syracuseStep 1234871 = 1852307) B1852307
theorem B514127 : Blo 338752 514127 := bstep (se 1 (by rfl) ⟨385595, by rfl⟩ : syracuseStep 514127 = 771191) B771191
theorem B1235101 : Blo 338752 1235101 := bstep (se 3 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 1235101 = 463163) B463163
theorem B383611 : Blo 338752 383611 := bstep (se 1 (by rfl) ⟨287708, by rfl⟩ : syracuseStep 383611 = 575417) B575417
theorem B645803 : Blo 338752 645803 := bstep (se 1 (by rfl) ⟨484352, by rfl⟩ : syracuseStep 645803 = 968705) B968705
theorem B646031 : Blo 338752 646031 := bstep (se 1 (by rfl) ⟨484523, by rfl⟩ : syracuseStep 646031 = 969047) B969047
theorem B1727567 : Blo 338752 1727567 := bstep (se 1 (by rfl) ⟨1295675, by rfl⟩ : syracuseStep 1727567 = 2591351) B2591351
theorem B384079 : Blo 338752 384079 := bstep (se 1 (by rfl) ⟨288059, by rfl⟩ : syracuseStep 384079 = 576119) B576119
theorem B613499 : Blo 338752 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B4349123 : Blo 338752 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B548203 : Blo 338752 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B384475 : Blo 338752 384475 := bstep (se 1 (by rfl) ⟨288356, by rfl⟩ : syracuseStep 384475 = 576713) B576713
theorem B3104243 : Blo 338752 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B1728215 : Blo 338752 1728215 := bstep (se 1 (by rfl) ⟨1296161, by rfl⟩ : syracuseStep 1728215 = 2592323) B2592323
theorem B384943 : Blo 338752 384943 := bstep (se 1 (by rfl) ⟨288707, by rfl⟩ : syracuseStep 384943 = 577415) B577415
theorem B974855 : Blo 338752 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B647291 : Blo 338752 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B4645181 : Blo 338752 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B385375 : Blo 338752 385375 := bstep (se 1 (by rfl) ⟨289031, by rfl⟩ : syracuseStep 385375 = 578063) B578063
theorem B582071 : Blo 338752 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B647777 : Blo 338752 647777 := bstep (se 2 (by rfl) ⟨242916, by rfl⟩ : syracuseStep 647777 = 485833) B485833
theorem B647929 : Blo 338752 647929 := bstep (se 2 (by rfl) ⟨242973, by rfl⟩ : syracuseStep 647929 = 485947) B485947
theorem B877625 : Blo 338752 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B649235 : Blo 338752 649235 := bstep (se 1 (by rfl) ⟨486926, by rfl⟩ : syracuseStep 649235 = 973853) B973853
theorem B649387 : Blo 338752 649387 := bstep (se 1 (by rfl) ⟨487040, by rfl⟩ : syracuseStep 649387 = 974081) B974081
theorem B3107159 : Blo 338752 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B3697001 : Blo 338752 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B649615 : Blo 338752 649615 := bstep (se 1 (by rfl) ⟨487211, by rfl⟩ : syracuseStep 649615 = 974423) B974423
theorem B649691 : Blo 338752 649691 := bstep (se 1 (by rfl) ⟨487268, by rfl⟩ : syracuseStep 649691 = 974537) B974537
theorem B4123169 : Blo 338752 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B617017 : Blo 338752 617017 := bstep (se 2 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 617017 = 462763) B462763
theorem B1731131 : Blo 338752 1731131 := bstep (se 1 (by rfl) ⟨1298348, by rfl⟩ : syracuseStep 1731131 = 2596697) B2596697
theorem B551993 : Blo 338752 551993 := bstep (se 2 (by rfl) ⟨206997, by rfl⟩ : syracuseStep 551993 = 413995) B413995
theorem B1731779 : Blo 338752 1731779 := bstep (se 1 (by rfl) ⟨1298834, by rfl⟩ : syracuseStep 1731779 = 2597669) B2597669
theorem B519599 : Blo 338752 519599 := bstep (se 1 (by rfl) ⟨389699, by rfl⟩ : syracuseStep 519599 = 779399) B779399
theorem B7892603 : Blo 338752 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B5795549 : Blo 338752 5795549 := bstep (se 3 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 5795549 = 2173331) B2173331
theorem B814943 : Blo 338752 814943 := bstep (se 1 (by rfl) ⟨611207, by rfl⟩ : syracuseStep 814943 = 1222415) B1222415
theorem B4649075 : Blo 338752 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B5501195 : Blo 338752 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B5534081 : Blo 338752 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B2585519 : Blo 338752 2585519 := bstep (se 1 (by rfl) ⟨1939139, by rfl⟩ : syracuseStep 2585519 = 3878279) B3878279
theorem B1143827 : Blo 338752 1143827 := bstep (se 1 (by rfl) ⟨857870, by rfl⟩ : syracuseStep 1143827 = 1715741) B1715741
theorem B1307801 : Blo 338752 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B4846837 : Blo 338752 4846837 := bstep (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) B454391
theorem B1144151 : Blo 338752 1144151 := bstep (se 1 (by rfl) ⟨858113, by rfl⟩ : syracuseStep 1144151 = 1716227) B1716227
theorem B554383 : Blo 338752 554383 := bstep (se 1 (by rfl) ⟨415787, by rfl⟩ : syracuseStep 554383 = 831575) B831575
theorem B1373755 : Blo 338752 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B2192993 : Blo 338752 2192993 := bstep (se 2 (by rfl) ⟨822372, by rfl⟩ : syracuseStep 2192993 = 1644745) B1644745
theorem B2062045 : Blo 338752 2062045 := bstep (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) B773267
theorem B2062189 : Blo 338752 2062189 := bstep (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) B773321
theorem B3274759 : Blo 338752 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B2455609 : Blo 338752 2455609 := bstep (se 2 (by rfl) ⟨920853, by rfl⟩ : syracuseStep 2455609 = 1841707) B1841707
theorem B1145231 : Blo 338752 1145231 := bstep (se 1 (by rfl) ⟨858923, by rfl⟩ : syracuseStep 1145231 = 1717847) B1717847
theorem B1145555 : Blo 338752 1145555 := bstep (se 1 (by rfl) ⟨859166, by rfl⟩ : syracuseStep 1145555 = 1718333) B1718333
theorem B916487 : Blo 338752 916487 := bstep (se 1 (by rfl) ⟨687365, by rfl⟩ : syracuseStep 916487 = 1374731) B1374731
theorem B654355 : Blo 338752 654355 := bstep (se 1 (by rfl) ⟨490766, by rfl⟩ : syracuseStep 654355 = 981533) B981533
theorem B2194451 : Blo 338752 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B1375427 : Blo 338752 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B5242103 : Blo 338752 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B687455 : Blo 338752 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B181140941 : Blo 338752 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1342985 : Blo 338752 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B1146743 : Blo 338752 1146743 := bstep (se 1 (by rfl) ⟨860057, by rfl⟩ : syracuseStep 1146743 = 1720115) B1720115
theorem B1933217 : Blo 338752 1933217 := bstep (se 2 (by rfl) ⟨724956, by rfl⟩ : syracuseStep 1933217 = 1449913) B1449913
theorem B1146905 : Blo 338752 1146905 := bstep (se 2 (by rfl) ⟨430089, by rfl⟩ : syracuseStep 1146905 = 860179) B860179
theorem B4390949 : Blo 338752 4390949 := bstep (se 4 (by rfl) ⟨411651, by rfl⟩ : syracuseStep 4390949 = 823303) B823303
theorem B7078499 : Blo 338752 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B1639111 : Blo 338752 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B1148147 : Blo 338752 1148147 := bstep (se 1 (by rfl) ⟨861110, by rfl⟩ : syracuseStep 1148147 = 1722221) B1722221
theorem B1148255 : Blo 338752 1148255 := bstep (se 1 (by rfl) ⟨861191, by rfl⟩ : syracuseStep 1148255 = 1722383) B1722383
theorem B1246603 : Blo 338752 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B2459069 : Blo 338752 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B13108877 : Blo 338752 13108877 := bstep (se 3 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 13108877 = 4915829) B4915829
theorem B919201 : Blo 338752 919201 := bstep (se 2 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 919201 = 689401) B689401
theorem B1935859 : Blo 338752 1935859 := bstep (se 1 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 1935859 = 2903789) B2903789
theorem B494263 : Blo 338752 494263 := bstep (se 1 (by rfl) ⟨370697, by rfl⟩ : syracuseStep 494263 = 741395) B741395
theorem B822035 : Blo 338752 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B1149821 : Blo 338752 1149821 := bstep (se 3 (by rfl) ⟨215591, by rfl⟩ : syracuseStep 1149821 = 431183) B431183
theorem B3279953 : Blo 338752 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B1150091 : Blo 338752 1150091 := bstep (se 1 (by rfl) ⟨862568, by rfl⟩ : syracuseStep 1150091 = 1725137) B1725137
theorem B822689 : Blo 338752 822689 := bstep (se 2 (by rfl) ⟨308508, by rfl⟩ : syracuseStep 822689 = 617017) B617017
theorem B429563 : Blo 338752 429563 := bstep (se 1 (by rfl) ⟨322172, by rfl⟩ : syracuseStep 429563 = 644345) B644345
theorem B823247 : Blo 338752 823247 := bstep (se 1 (by rfl) ⟨617435, by rfl⟩ : syracuseStep 823247 = 1234871) B1234871
theorem B463195 : Blo 338752 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B430535 : Blo 338752 430535 := bstep (se 1 (by rfl) ⟨322901, by rfl⟩ : syracuseStep 430535 = 645803) B645803
theorem B922175 : Blo 338752 922175 := bstep (se 1 (by rfl) ⟨691631, by rfl⟩ : syracuseStep 922175 = 1383263) B1383263
theorem B430687 : Blo 338752 430687 := bstep (se 1 (by rfl) ⟨323015, by rfl⟩ : syracuseStep 430687 = 646031) B646031
theorem B1151711 : Blo 338752 1151711 := bstep (se 1 (by rfl) ⟨863783, by rfl⟩ : syracuseStep 1151711 = 1727567) B1727567
theorem B2069495 : Blo 338752 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B1152143 : Blo 338752 1152143 := bstep (se 1 (by rfl) ⟨864107, by rfl⟩ : syracuseStep 1152143 = 1728215) B1728215
theorem B922843 : Blo 338752 922843 := bstep (se 1 (by rfl) ⟨692132, by rfl⟩ : syracuseStep 922843 = 1384265) B1384265
theorem B923017 : Blo 338752 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B857911 : Blo 338752 857911 := bstep (se 1 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 857911 = 1286867) B1286867
theorem B1448189 : Blo 338752 1448189 := bstep (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) B543071
theorem B1153277 : Blo 338752 1153277 := bstep (se 3 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 1153277 = 432479) B432479
theorem B858377 : Blo 338752 858377 := bstep (se 2 (by rfl) ⟨321891, by rfl⟩ : syracuseStep 858377 = 643783) B643783
theorem B2071439 : Blo 338752 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B2464667 : Blo 338752 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B433127 : Blo 338752 433127 := bstep (se 1 (by rfl) ⟨324845, by rfl⟩ : syracuseStep 433127 = 649691) B649691
theorem B6462449 : Blo 338752 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B1154087 : Blo 338752 1154087 := bstep (se 1 (by rfl) ⟨865565, by rfl⟩ : syracuseStep 1154087 = 1731131) B1731131
theorem B859369 : Blo 338752 859369 := bstep (se 2 (by rfl) ⟨322263, by rfl⟩ : syracuseStep 859369 = 644527) B644527
theorem B859531 : Blo 338752 859531 := bstep (se 1 (by rfl) ⟨644648, by rfl⟩ : syracuseStep 859531 = 1289297) B1289297
theorem B2956709 : Blo 338752 2956709 := bstep (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) B554383
theorem B1154519 : Blo 338752 1154519 := bstep (se 1 (by rfl) ⟨865889, by rfl⟩ : syracuseStep 1154519 = 1731779) B1731779
theorem B859835 : Blo 338752 859835 := bstep (se 1 (by rfl) ⟨644876, by rfl⟩ : syracuseStep 859835 = 1289753) B1289753
theorem B4366345 : Blo 338752 4366345 := bstep (se 2 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 4366345 = 3274759) B3274759
theorem B1646801 : Blo 338752 1646801 := bstep (se 2 (by rfl) ⟨617550, by rfl⟩ : syracuseStep 1646801 = 1235101) B1235101
theorem B2073089 : Blo 338752 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B1450649 : Blo 338752 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B762551 : Blo 338752 762551 := bstep (se 1 (by rfl) ⟨571913, by rfl⟩ : syracuseStep 762551 = 1143827) B1143827
theorem B762767 : Blo 338752 762767 := bstep (se 1 (by rfl) ⟨572075, by rfl⟩ : syracuseStep 762767 = 1144151) B1144151
theorem B1844129 : Blo 338752 1844129 := bstep (se 2 (by rfl) ⟨691548, by rfl⟩ : syracuseStep 1844129 = 1383097) B1383097
theorem B730151 : Blo 338752 730151 := bstep (se 1 (by rfl) ⟨547613, by rfl⟩ : syracuseStep 730151 = 1095227) B1095227
theorem B1156193 : Blo 338752 1156193 := bstep (se 2 (by rfl) ⟨433572, by rfl⟩ : syracuseStep 1156193 = 867145) B867145
theorem B1549561 : Blo 338752 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B3581293 : Blo 338752 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B861779 : Blo 338752 861779 := bstep (se 1 (by rfl) ⟨646334, by rfl⟩ : syracuseStep 861779 = 1292669) B1292669
theorem B763487 : Blo 338752 763487 := bstep (se 1 (by rfl) ⟨572615, by rfl⟩ : syracuseStep 763487 = 1145231) B1145231
theorem B763703 : Blo 338752 763703 := bstep (se 1 (by rfl) ⟨572777, by rfl⟩ : syracuseStep 763703 = 1145555) B1145555
theorem B730937 : Blo 338752 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B764009 : Blo 338752 764009 := bstep (se 2 (by rfl) ⟨286503, by rfl⟩ : syracuseStep 764009 = 573007) B573007
theorem B120760627 : Blo 338752 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B2894291 : Blo 338752 2894291 := bstep (se 1 (by rfl) ⟨2170718, by rfl⟩ : syracuseStep 2894291 = 4341437) B4341437
theorem B764495 : Blo 338752 764495 := bstep (se 1 (by rfl) ⟨573371, by rfl⟩ : syracuseStep 764495 = 1146743) B1146743
theorem B1288811 : Blo 338752 1288811 := bstep (se 1 (by rfl) ⟨966608, by rfl⟩ : syracuseStep 1288811 = 1933217) B1933217
theorem B436919 : Blo 338752 436919 := bstep (se 1 (by rfl) ⟨327689, by rfl⟩ : syracuseStep 436919 = 655379) B655379
theorem B1845949 : Blo 338752 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B2599613 : Blo 338752 2599613 := bstep (se 3 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 2599613 = 974855) B974855
theorem B764639 : Blo 338752 764639 := bstep (se 1 (by rfl) ⟨573479, by rfl⟩ : syracuseStep 764639 = 1146959) B1146959
theorem B1288979 : Blo 338752 1288979 := bstep (se 1 (by rfl) ⟨966734, by rfl⟩ : syracuseStep 1288979 = 1933469) B1933469
theorem B1747855 : Blo 338752 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B338843 : Blo 338752 338843 := bstep (se 1 (by rfl) ⟨254132, by rfl⟩ : syracuseStep 338843 = 508265) B508265
theorem B338895 : Blo 338752 338895 := bstep (se 1 (by rfl) ⟨254171, by rfl⟩ : syracuseStep 338895 = 508343) B508343
theorem B764891 : Blo 338752 764891 := bstep (se 1 (by rfl) ⟨573668, by rfl⟩ : syracuseStep 764891 = 1147337) B1147337
theorem B338919 : Blo 338752 338919 := bstep (se 1 (by rfl) ⟨254189, by rfl⟩ : syracuseStep 338919 = 508379) B508379
theorem B863207 : Blo 338752 863207 := bstep (se 1 (by rfl) ⟨647405, by rfl⟩ : syracuseStep 863207 = 1294811) B1294811
theorem B765071 : Blo 338752 765071 := bstep (se 1 (by rfl) ⟨573803, by rfl⟩ : syracuseStep 765071 = 1147607) B1147607
theorem B2075867 : Blo 338752 2075867 := bstep (se 1 (by rfl) ⟨1556900, by rfl⟩ : syracuseStep 2075867 = 3113801) B3113801
theorem B765161 : Blo 338752 765161 := bstep (se 2 (by rfl) ⟨286935, by rfl⟩ : syracuseStep 765161 = 573871) B573871
theorem B339231 : Blo 338752 339231 := bstep (se 1 (by rfl) ⟨254423, by rfl⟩ : syracuseStep 339231 = 508847) B508847
theorem B765215 : Blo 338752 765215 := bstep (se 1 (by rfl) ⟨573911, by rfl⟩ : syracuseStep 765215 = 1147823) B1147823
theorem B339291 : Blo 338752 339291 := bstep (se 1 (by rfl) ⟨254468, by rfl⟩ : syracuseStep 339291 = 508937) B508937
theorem B339311 : Blo 338752 339311 := bstep (se 1 (by rfl) ⟨254483, by rfl⟩ : syracuseStep 339311 = 508967) B508967
theorem B16035191 : Blo 338752 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B339367 : Blo 338752 339367 := bstep (se 1 (by rfl) ⟨254525, by rfl⟩ : syracuseStep 339367 = 509051) B509051
theorem B339451 : Blo 338752 339451 := bstep (se 1 (by rfl) ⟨254588, by rfl⟩ : syracuseStep 339451 = 509177) B509177
theorem B339519 : Blo 338752 339519 := bstep (se 1 (by rfl) ⟨254639, by rfl⟩ : syracuseStep 339519 = 509279) B509279
theorem B339527 : Blo 338752 339527 := bstep (se 1 (by rfl) ⟨254645, by rfl⟩ : syracuseStep 339527 = 509291) B509291
theorem B863905 : Blo 338752 863905 := bstep (se 2 (by rfl) ⟨323964, by rfl⟩ : syracuseStep 863905 = 647929) B647929
theorem B339679 : Blo 338752 339679 := bstep (se 1 (by rfl) ⟨254759, by rfl⟩ : syracuseStep 339679 = 509519) B509519
theorem B765737 : Blo 338752 765737 := bstep (se 2 (by rfl) ⟨287151, by rfl⟩ : syracuseStep 765737 = 574303) B574303
theorem B339759 : Blo 338752 339759 := bstep (se 1 (by rfl) ⟨254819, by rfl⟩ : syracuseStep 339759 = 509639) B509639
theorem B864047 : Blo 338752 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B339867 : Blo 338752 339867 := bstep (se 1 (by rfl) ⟨254900, by rfl⟩ : syracuseStep 339867 = 509801) B509801
theorem B339919 : Blo 338752 339919 := bstep (se 1 (by rfl) ⟨254939, by rfl⟩ : syracuseStep 339919 = 509879) B509879
theorem B339943 : Blo 338752 339943 := bstep (se 1 (by rfl) ⟨254957, by rfl⟩ : syracuseStep 339943 = 509915) B509915
theorem B1290451 : Blo 338752 1290451 := bstep (se 1 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 1290451 = 1935677) B1935677
theorem B340255 : Blo 338752 340255 := bstep (se 1 (by rfl) ⟨255191, by rfl⟩ : syracuseStep 340255 = 510383) B510383
theorem B340315 : Blo 338752 340315 := bstep (se 1 (by rfl) ⟨255236, by rfl⟩ : syracuseStep 340315 = 510473) B510473
theorem B340335 : Blo 338752 340335 := bstep (se 1 (by rfl) ⟨255251, by rfl⟩ : syracuseStep 340335 = 510503) B510503
theorem B340391 : Blo 338752 340391 := bstep (se 1 (by rfl) ⟨255293, by rfl⟩ : syracuseStep 340391 = 510587) B510587
theorem B864695 : Blo 338752 864695 := bstep (se 1 (by rfl) ⟨648521, by rfl⟩ : syracuseStep 864695 = 1297043) B1297043
theorem B1454561 : Blo 338752 1454561 := bstep (se 2 (by rfl) ⟨545460, by rfl⟩ : syracuseStep 1454561 = 1090921) B1090921
theorem B340475 : Blo 338752 340475 := bstep (se 1 (by rfl) ⟨255356, by rfl⟩ : syracuseStep 340475 = 510713) B510713
theorem B340543 : Blo 338752 340543 := bstep (se 1 (by rfl) ⟨255407, by rfl⟩ : syracuseStep 340543 = 510815) B510815
theorem B340551 : Blo 338752 340551 := bstep (se 1 (by rfl) ⟨255413, by rfl⟩ : syracuseStep 340551 = 510827) B510827
theorem B1290923 : Blo 338752 1290923 := bstep (se 1 (by rfl) ⟨968192, by rfl⟩ : syracuseStep 1290923 = 1936385) B1936385
theorem B340703 : Blo 338752 340703 := bstep (se 1 (by rfl) ⟨255527, by rfl⟩ : syracuseStep 340703 = 511055) B511055
theorem B340783 : Blo 338752 340783 := bstep (se 1 (by rfl) ⟨255587, by rfl⟩ : syracuseStep 340783 = 511175) B511175
theorem B766799 : Blo 338752 766799 := bstep (se 1 (by rfl) ⟨575099, by rfl⟩ : syracuseStep 766799 = 1150199) B1150199
theorem B340891 : Blo 338752 340891 := bstep (se 1 (by rfl) ⟨255668, by rfl⟩ : syracuseStep 340891 = 511337) B511337
theorem B340943 : Blo 338752 340943 := bstep (se 1 (by rfl) ⟨255707, by rfl⟩ : syracuseStep 340943 = 511415) B511415
theorem B340967 : Blo 338752 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B767015 : Blo 338752 767015 := bstep (se 1 (by rfl) ⟨575261, by rfl⟩ : syracuseStep 767015 = 1150523) B1150523
theorem B767195 : Blo 338752 767195 := bstep (se 1 (by rfl) ⟨575396, by rfl⟩ : syracuseStep 767195 = 1150793) B1150793
theorem B1225961 : Blo 338752 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B1455347 : Blo 338752 1455347 := bstep (se 1 (by rfl) ⟨1091510, by rfl⟩ : syracuseStep 1455347 = 2183021) B2183021
theorem B341279 : Blo 338752 341279 := bstep (se 1 (by rfl) ⟨255959, by rfl⟩ : syracuseStep 341279 = 511919) B511919
theorem B341339 : Blo 338752 341339 := bstep (se 1 (by rfl) ⟨256004, by rfl⟩ : syracuseStep 341339 = 512009) B512009
theorem B341359 : Blo 338752 341359 := bstep (se 1 (by rfl) ⟨256019, by rfl⟩ : syracuseStep 341359 = 512039) B512039
theorem B767393 : Blo 338752 767393 := bstep (se 2 (by rfl) ⟨287772, by rfl⟩ : syracuseStep 767393 = 575545) B575545
theorem B341415 : Blo 338752 341415 := bstep (se 1 (by rfl) ⟨256061, by rfl⟩ : syracuseStep 341415 = 512123) B512123
theorem B341499 : Blo 338752 341499 := bstep (se 1 (by rfl) ⟨256124, by rfl⟩ : syracuseStep 341499 = 512249) B512249
theorem B865799 : Blo 338752 865799 := bstep (se 1 (by rfl) ⟨649349, by rfl⟩ : syracuseStep 865799 = 1298699) B1298699
theorem B865849 : Blo 338752 865849 := bstep (se 2 (by rfl) ⟨324693, by rfl⟩ : syracuseStep 865849 = 649387) B649387
theorem B341567 : Blo 338752 341567 := bstep (se 1 (by rfl) ⟨256175, by rfl⟩ : syracuseStep 341567 = 512351) B512351
theorem B341575 : Blo 338752 341575 := bstep (se 1 (by rfl) ⟨256181, by rfl⟩ : syracuseStep 341575 = 512363) B512363
theorem B3356293 : Blo 338752 3356293 := bstep (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) B629305
theorem B2963083 : Blo 338752 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B341727 : Blo 338752 341727 := bstep (se 1 (by rfl) ⟨256295, by rfl⟩ : syracuseStep 341727 = 512591) B512591
theorem B341807 : Blo 338752 341807 := bstep (se 1 (by rfl) ⟨256355, by rfl⟩ : syracuseStep 341807 = 512711) B512711
theorem B6993719 : Blo 338752 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B866153 : Blo 338752 866153 := bstep (se 2 (by rfl) ⟨324807, by rfl⟩ : syracuseStep 866153 = 649615) B649615
theorem B341915 : Blo 338752 341915 := bstep (se 1 (by rfl) ⟨256436, by rfl⟩ : syracuseStep 341915 = 512873) B512873
theorem B767951 : Blo 338752 767951 := bstep (se 1 (by rfl) ⟨575963, by rfl⟩ : syracuseStep 767951 = 1151927) B1151927
theorem B341967 : Blo 338752 341967 := bstep (se 1 (by rfl) ⟨256475, by rfl⟩ : syracuseStep 341967 = 512951) B512951
theorem B341991 : Blo 338752 341991 := bstep (se 1 (by rfl) ⟨256493, by rfl⟩ : syracuseStep 341991 = 512987) B512987
theorem B571657 : Blo 338752 571657 := bstep (se 2 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 571657 = 428743) B428743
theorem B342303 : Blo 338752 342303 := bstep (se 1 (by rfl) ⟨256727, by rfl⟩ : syracuseStep 342303 = 513455) B513455
theorem B768329 : Blo 338752 768329 := bstep (se 2 (by rfl) ⟨288123, by rfl⟩ : syracuseStep 768329 = 576247) B576247
theorem B768347 : Blo 338752 768347 := bstep (se 1 (by rfl) ⟨576260, by rfl⟩ : syracuseStep 768347 = 1152521) B1152521
theorem B342363 : Blo 338752 342363 := bstep (se 1 (by rfl) ⟨256772, by rfl⟩ : syracuseStep 342363 = 513545) B513545
theorem B342383 : Blo 338752 342383 := bstep (se 1 (by rfl) ⟨256787, by rfl⟩ : syracuseStep 342383 = 513575) B513575
theorem B342439 : Blo 338752 342439 := bstep (se 1 (by rfl) ⟨256829, by rfl⟩ : syracuseStep 342439 = 513659) B513659
theorem B866771 : Blo 338752 866771 := bstep (se 1 (by rfl) ⟨650078, by rfl⟩ : syracuseStep 866771 = 1300157) B1300157
theorem B342523 : Blo 338752 342523 := bstep (se 1 (by rfl) ⟨256892, by rfl⟩ : syracuseStep 342523 = 513785) B513785
theorem B1456679 : Blo 338752 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B342591 : Blo 338752 342591 := bstep (se 1 (by rfl) ⟨256943, by rfl⟩ : syracuseStep 342591 = 513887) B513887
theorem B342599 : Blo 338752 342599 := bstep (se 1 (by rfl) ⟨256949, by rfl⟩ : syracuseStep 342599 = 513899) B513899
theorem B3259075 : Blo 338752 3259075 := bstep (se 1 (by rfl) ⟨2444306, by rfl⟩ : syracuseStep 3259075 = 4888613) B4888613
theorem B342751 : Blo 338752 342751 := bstep (se 1 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 342751 = 514127) B514127
theorem B1457021 : Blo 338752 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B768923 : Blo 338752 768923 := bstep (se 1 (by rfl) ⟨576692, by rfl⟩ : syracuseStep 768923 = 1153385) B1153385
theorem B769121 : Blo 338752 769121 := bstep (se 2 (by rfl) ⟨288420, by rfl⟩ : syracuseStep 769121 = 576841) B576841
theorem B7388279 : Blo 338752 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B6569201 : Blo 338752 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B6208757 : Blo 338752 6208757 := bstep (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) B582071
theorem B769319 : Blo 338752 769319 := bstep (se 1 (by rfl) ⟨576989, by rfl⟩ : syracuseStep 769319 = 1153979) B1153979
theorem B2899415 : Blo 338752 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B1293839 : Blo 338752 1293839 := bstep (se 1 (by rfl) ⟨970379, by rfl⟩ : syracuseStep 1293839 = 1940759) B1940759
theorem B769697 : Blo 338752 769697 := bstep (se 2 (by rfl) ⟨288636, by rfl⟩ : syracuseStep 769697 = 577273) B577273
theorem B573115 : Blo 338752 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B1294127 : Blo 338752 1294127 := bstep (se 1 (by rfl) ⟨970595, by rfl⟩ : syracuseStep 1294127 = 1941191) B1941191
theorem B770057 : Blo 338752 770057 := bstep (se 2 (by rfl) ⟨288771, by rfl⟩ : syracuseStep 770057 = 577543) B577543
theorem B3096787 : Blo 338752 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B508169 : Blo 338752 508169 := bstep (se 2 (by rfl) ⟨190563, by rfl⟩ : syracuseStep 508169 = 381127) B381127
theorem B508271 : Blo 338752 508271 := bstep (se 1 (by rfl) ⟨381203, by rfl⟩ : syracuseStep 508271 = 762407) B762407
theorem B770471 : Blo 338752 770471 := bstep (se 1 (by rfl) ⟨577853, by rfl⟩ : syracuseStep 770471 = 1155707) B1155707
theorem B770579 : Blo 338752 770579 := bstep (se 1 (by rfl) ⟨577934, by rfl⟩ : syracuseStep 770579 = 1155869) B1155869
theorem B508487 : Blo 338752 508487 := bstep (se 1 (by rfl) ⟨381365, by rfl⟩ : syracuseStep 508487 = 762731) B762731
theorem B3260999 : Blo 338752 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B770633 : Blo 338752 770633 := bstep (se 2 (by rfl) ⟨288987, by rfl⟩ : syracuseStep 770633 = 577975) B577975
theorem B508523 : Blo 338752 508523 := bstep (se 1 (by rfl) ⟨381392, by rfl⟩ : syracuseStep 508523 = 762785) B762785
theorem B7455415 : Blo 338752 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B574175 : Blo 338752 574175 := bstep (se 1 (by rfl) ⟨430631, by rfl⟩ : syracuseStep 574175 = 861263) B861263
theorem B3293945 : Blo 338752 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B508751 : Blo 338752 508751 := bstep (se 1 (by rfl) ⟨381563, by rfl⟩ : syracuseStep 508751 = 763127) B763127
theorem B1721249 : Blo 338752 1721249 := bstep (se 2 (by rfl) ⟨645468, by rfl⟩ : syracuseStep 1721249 = 1290937) B1290937
theorem B771047 : Blo 338752 771047 := bstep (se 1 (by rfl) ⟨578285, by rfl⟩ : syracuseStep 771047 = 1156571) B1156571
theorem B574607 : Blo 338752 574607 := bstep (se 1 (by rfl) ⟨430955, by rfl⟩ : syracuseStep 574607 = 861911) B861911
theorem B509147 : Blo 338752 509147 := bstep (se 1 (by rfl) ⟨381860, by rfl⟩ : syracuseStep 509147 = 763721) B763721
theorem B1557737 : Blo 338752 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B574843 : Blo 338752 574843 := bstep (se 1 (by rfl) ⟨431132, by rfl⟩ : syracuseStep 574843 = 862265) B862265
theorem B509321 : Blo 338752 509321 := bstep (se 2 (by rfl) ⟨190995, by rfl⟩ : syracuseStep 509321 = 381991) B381991
theorem B968249 : Blo 338752 968249 := bstep (se 2 (by rfl) ⟨363093, by rfl⟩ : syracuseStep 968249 = 726187) B726187
theorem B509675 : Blo 338752 509675 := bstep (se 1 (by rfl) ⟨382256, by rfl⟩ : syracuseStep 509675 = 764513) B764513
theorem B509903 : Blo 338752 509903 := bstep (se 1 (by rfl) ⟨382427, by rfl⟩ : syracuseStep 509903 = 764855) B764855
theorem B1230977 : Blo 338752 1230977 := bstep (se 2 (by rfl) ⟨461616, by rfl⟩ : syracuseStep 1230977 = 923233) B923233
theorem B13289669 : Blo 338752 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B346399 : Blo 338752 346399 := bstep (se 1 (by rfl) ⟨259799, by rfl⟩ : syracuseStep 346399 = 519599) B519599
theorem B510299 : Blo 338752 510299 := bstep (se 1 (by rfl) ⟨382724, by rfl⟩ : syracuseStep 510299 = 765449) B765449
theorem B5261735 : Blo 338752 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B543295 : Blo 338752 543295 := bstep (se 1 (by rfl) ⟨407471, by rfl⟩ : syracuseStep 543295 = 814943) B814943
theorem B510527 : Blo 338752 510527 := bstep (se 1 (by rfl) ⟨382895, by rfl⟩ : syracuseStep 510527 = 765791) B765791
theorem B510647 : Blo 338752 510647 := bstep (se 1 (by rfl) ⟨382985, by rfl⟩ : syracuseStep 510647 = 765971) B765971
theorem B772831 : Blo 338752 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B3099383 : Blo 338752 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B576335 : Blo 338752 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B510875 : Blo 338752 510875 := bstep (se 1 (by rfl) ⟨383156, by rfl⟩ : syracuseStep 510875 = 766313) B766313
theorem B3689387 : Blo 338752 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B1723679 : Blo 338752 1723679 := bstep (se 1 (by rfl) ⟨1292759, by rfl⟩ : syracuseStep 1723679 = 2585519) B2585519
theorem B970015 : Blo 338752 970015 := bstep (se 1 (by rfl) ⟨727511, by rfl⟩ : syracuseStep 970015 = 1455023) B1455023
theorem B511271 : Blo 338752 511271 := bstep (se 1 (by rfl) ⟨383453, by rfl⟩ : syracuseStep 511271 = 766907) B766907
theorem B511355 : Blo 338752 511355 := bstep (se 1 (by rfl) ⟨383516, by rfl⟩ : syracuseStep 511355 = 767033) B767033
theorem B871867 : Blo 338752 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B511481 : Blo 338752 511481 := bstep (se 2 (by rfl) ⟨191805, by rfl⟩ : syracuseStep 511481 = 383611) B383611
theorem B511583 : Blo 338752 511583 := bstep (se 1 (by rfl) ⟨383687, by rfl⟩ : syracuseStep 511583 = 767375) B767375
theorem B1298015 : Blo 338752 1298015 := bstep (se 1 (by rfl) ⟨973511, by rfl⟩ : syracuseStep 1298015 = 1947023) B1947023
theorem B1461995 : Blo 338752 1461995 := bstep (se 1 (by rfl) ⟨1096496, by rfl⟩ : syracuseStep 1461995 = 2192993) B2192993
theorem B577327 : Blo 338752 577327 := bstep (se 1 (by rfl) ⟨432995, by rfl⟩ : syracuseStep 577327 = 865991) B865991
theorem B511799 : Blo 338752 511799 := bstep (se 1 (by rfl) ⟨383849, by rfl⟩ : syracuseStep 511799 = 767699) B767699
theorem B2576285 : Blo 338752 2576285 := bstep (se 3 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 2576285 = 966107) B966107
theorem B3264461 : Blo 338752 3264461 := bstep (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) B1224173
theorem B872473 : Blo 338752 872473 := bstep (se 2 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 872473 = 654355) B654355
theorem B512105 : Blo 338752 512105 := bstep (se 2 (by rfl) ⟨192039, by rfl⟩ : syracuseStep 512105 = 384079) B384079
theorem B381307 : Blo 338752 381307 := bstep (se 1 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 381307 = 571961) B571961
theorem B512423 : Blo 338752 512423 := bstep (se 1 (by rfl) ⟨384317, by rfl⟩ : syracuseStep 512423 = 768635) B768635
theorem B512507 : Blo 338752 512507 := bstep (se 1 (by rfl) ⟨384380, by rfl⟩ : syracuseStep 512507 = 768761) B768761
theorem B10998341 : Blo 338752 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B512633 : Blo 338752 512633 := bstep (se 2 (by rfl) ⟨192237, by rfl⟩ : syracuseStep 512633 = 384475) B384475
theorem B610991 : Blo 338752 610991 := bstep (se 1 (by rfl) ⟨458243, by rfl⟩ : syracuseStep 610991 = 916487) B916487
theorem B512687 : Blo 338752 512687 := bstep (se 1 (by rfl) ⟨384515, by rfl⟩ : syracuseStep 512687 = 769031) B769031
theorem B1462967 : Blo 338752 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B512735 : Blo 338752 512735 := bstep (se 1 (by rfl) ⟨384551, by rfl⟩ : syracuseStep 512735 = 769103) B769103
theorem B13030145 : Blo 338752 13030145 := bstep (se 2 (by rfl) ⟨4886304, by rfl⟩ : syracuseStep 13030145 = 9772609) B9772609
theorem B643859 : Blo 338752 643859 := bstep (se 1 (by rfl) ⟨482894, by rfl⟩ : syracuseStep 643859 = 965789) B965789
theorem B381775 : Blo 338752 381775 := bstep (se 1 (by rfl) ⟨286331, by rfl⟩ : syracuseStep 381775 = 572663) B572663
theorem B3494735 : Blo 338752 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B512999 : Blo 338752 512999 := bstep (se 1 (by rfl) ⟨384749, by rfl⟩ : syracuseStep 512999 = 769499) B769499
theorem B644087 : Blo 338752 644087 := bstep (se 1 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 644087 = 966131) B966131
theorem B1299671 : Blo 338752 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B382171 : Blo 338752 382171 := bstep (se 1 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 382171 = 573257) B573257
theorem B513257 : Blo 338752 513257 := bstep (se 2 (by rfl) ⟨192471, by rfl⟩ : syracuseStep 513257 = 384943) B384943
theorem B513311 : Blo 338752 513311 := bstep (se 1 (by rfl) ⟨384983, by rfl⟩ : syracuseStep 513311 = 769967) B769967
theorem B22304165 : Blo 338752 22304165 := bstep (se 4 (by rfl) ⟨2091015, by rfl⟩ : syracuseStep 22304165 = 4182031) B4182031
theorem B513479 : Blo 338752 513479 := bstep (se 1 (by rfl) ⟨385109, by rfl⟩ : syracuseStep 513479 = 770219) B770219
theorem B382459 : Blo 338752 382459 := bstep (se 1 (by rfl) ⟨286844, by rfl⟩ : syracuseStep 382459 = 573689) B573689
theorem B1726109 : Blo 338752 1726109 := bstep (se 3 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 1726109 = 647291) B647291
theorem B382639 : Blo 338752 382639 := bstep (se 1 (by rfl) ⟨286979, by rfl⟩ : syracuseStep 382639 = 573959) B573959
theorem B1463993 : Blo 338752 1463993 := bstep (se 2 (by rfl) ⟨548997, by rfl⟩ : syracuseStep 1463993 = 1097995) B1097995
theorem B513833 : Blo 338752 513833 := bstep (se 2 (by rfl) ⟨192687, by rfl⟩ : syracuseStep 513833 = 385375) B385375
theorem B513839 : Blo 338752 513839 := bstep (se 1 (by rfl) ⟨385379, by rfl⟩ : syracuseStep 513839 = 770759) B770759
theorem B382927 : Blo 338752 382927 := bstep (se 1 (by rfl) ⟨287195, by rfl⟩ : syracuseStep 382927 = 574391) B574391
theorem B383323 : Blo 338752 383323 := bstep (se 1 (by rfl) ⟨287492, by rfl⟩ : syracuseStep 383323 = 574985) B574985
theorem B383431 : Blo 338752 383431 := bstep (se 1 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 383431 = 575147) B575147
theorem B612937 : Blo 338752 612937 := bstep (se 2 (by rfl) ⟨229851, by rfl⟩ : syracuseStep 612937 = 459703) B459703
theorem B383791 : Blo 338752 383791 := bstep (se 1 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 383791 = 575687) B575687
theorem B383899 : Blo 338752 383899 := bstep (se 1 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 383899 = 575849) B575849
theorem B1727405 : Blo 338752 1727405 := bstep (se 3 (by rfl) ⟨323888, by rfl⟩ : syracuseStep 1727405 = 647777) B647777
theorem B3103763 : Blo 338752 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B1399997 : Blo 338752 1399997 := bstep (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) B524999
theorem B384295 : Blo 338752 384295 := bstep (se 1 (by rfl) ⟨288221, by rfl⟩ : syracuseStep 384295 = 576443) B576443
theorem B384367 : Blo 338752 384367 := bstep (se 1 (by rfl) ⟨288275, by rfl⟩ : syracuseStep 384367 = 576551) B576551
theorem B1170875 : Blo 338752 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B384583 : Blo 338752 384583 := bstep (se 1 (by rfl) ⟨288437, by rfl⟩ : syracuseStep 384583 = 576875) B576875
theorem B2908163 : Blo 338752 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B385447 : Blo 338752 385447 := bstep (se 1 (by rfl) ⟨289085, by rfl⟩ : syracuseStep 385447 = 578171) B578171
theorem B1729025 : Blo 338752 1729025 := bstep (se 2 (by rfl) ⟨648384, by rfl⟩ : syracuseStep 1729025 = 1296769) B1296769
theorem B7397891 : Blo 338752 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B2482859 : Blo 338752 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B1172191 : Blo 338752 1172191 := bstep (se 1 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 1172191 = 1758287) B1758287
theorem B1729511 : Blo 338752 1729511 := bstep (se 1 (by rfl) ⟨1297133, by rfl⟩ : syracuseStep 1729511 = 2594267) B2594267
theorem B975847 : Blo 338752 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B3105985 : Blo 338752 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B1729835 : Blo 338752 1729835 := bstep (se 1 (by rfl) ⟨1297376, by rfl⟩ : syracuseStep 1729835 = 2594753) B2594753
theorem B9791063 : Blo 338752 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B1107613 : Blo 338752 1107613 := bstep (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) B415355
theorem B878383 : Blo 338752 878383 := bstep (se 1 (by rfl) ⟨658787, by rfl⟩ : syracuseStep 878383 = 1317575) B1317575
theorem B1730807 : Blo 338752 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B4680179 : Blo 338752 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B1731293 : Blo 338752 1731293 := bstep (se 3 (by rfl) ⟨324617, by rfl⟩ : syracuseStep 1731293 = 649235) B649235
theorem B585083 : Blo 338752 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B1666585 : Blo 338752 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B3501629 : Blo 338752 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B2748779 : Blo 338752 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B1143449 : Blo 338752 1143449 := bstep (se 2 (by rfl) ⟨428793, by rfl⟩ : syracuseStep 1143449 = 857587) B857587
theorem B1831673 : Blo 338752 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B1930027 : Blo 338752 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B2749393 : Blo 338752 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B3863699 : Blo 338752 3863699 := bstep (se 1 (by rfl) ⟨2897774, by rfl⟩ : syracuseStep 3863699 = 5795549) B5795549
theorem B2061607 : Blo 338752 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B1635689 : Blo 338752 1635689 := bstep (se 2 (by rfl) ⟨613383, by rfl⟩ : syracuseStep 1635689 = 1226767) B1226767
theorem B3274145 : Blo 338752 3274145 := bstep (se 2 (by rfl) ⟨1227804, by rfl⟩ : syracuseStep 3274145 = 2455609) B2455609
theorem B1471981 : Blo 338752 1471981 := bstep (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) B551993
theorem B3667463 : Blo 338752 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B1635997 : Blo 338752 1635997 := bstep (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) B613499
theorem B3667805 : Blo 338752 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B1144961 : Blo 338752 1144961 := bstep (se 2 (by rfl) ⟨429360, by rfl⟩ : syracuseStep 1144961 = 858721) B858721
theorem B1112249 : Blo 338752 1112249 := bstep (se 2 (by rfl) ⟨417093, by rfl⟩ : syracuseStep 1112249 = 834187) B834187
theorem B2062583 : Blo 338752 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B1145339 : Blo 338752 1145339 := bstep (se 1 (by rfl) ⟨859004, by rfl⟩ : syracuseStep 1145339 = 1718009) B1718009
theorem B1145771 : Blo 338752 1145771 := bstep (se 1 (by rfl) ⟨859328, by rfl⟩ : syracuseStep 1145771 = 1718657) B1718657
theorem B1604623 : Blo 338752 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B3898691 : Blo 338752 3898691 := bstep (se 1 (by rfl) ⟨2924018, by rfl⟩ : syracuseStep 3898691 = 5848037) B5848037
theorem B1637729 : Blo 338752 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B1146311 : Blo 338752 1146311 := bstep (se 1 (by rfl) ⟨859733, by rfl⟩ : syracuseStep 1146311 = 1719467) B1719467
theorem B458303 : Blo 338752 458303 := bstep (se 1 (by rfl) ⟨343727, by rfl⟩ : syracuseStep 458303 = 687455) B687455
theorem B1146635 : Blo 338752 1146635 := bstep (se 1 (by rfl) ⟨859976, by rfl⟩ : syracuseStep 1146635 = 1719953) B1719953
theorem B3276605 : Blo 338752 3276605 := bstep (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) B1228727
theorem B4129049 : Blo 338752 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B4718999 : Blo 338752 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B2195963 : Blo 338752 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B1147499 : Blo 338752 1147499 := bstep (se 1 (by rfl) ⟨860624, by rfl⟩ : syracuseStep 1147499 = 1721249) B1721249
theorem B1639379 : Blo 338752 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B1148093 : Blo 338752 1148093 := bstep (se 3 (by rfl) ⟨215267, by rfl⟩ : syracuseStep 1148093 = 430535) B430535
theorem B3507823 : Blo 338752 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B2066081 : Blo 338752 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B6620957 : Blo 338752 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B2066255 : Blo 338752 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B2459591 : Blo 338752 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B4884461 : Blo 338752 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B1149119 : Blo 338752 1149119 := bstep (se 1 (by rfl) ⟨861839, by rfl⟩ : syracuseStep 1149119 = 1723679) B1723679
theorem B8686763 : Blo 338752 8686763 := bstep (se 1 (by rfl) ⟨6515072, by rfl⟩ : syracuseStep 8686763 = 13030145) B13030145
theorem B429239 : Blo 338752 429239 := bstep (se 1 (by rfl) ⟨321929, by rfl⟩ : syracuseStep 429239 = 643859) B643859
theorem B2329823 : Blo 338752 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B429391 : Blo 338752 429391 := bstep (se 1 (by rfl) ⟨322043, by rfl⟩ : syracuseStep 429391 = 644087) B644087
theorem B1379663 : Blo 338752 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B724393 : Blo 338752 724393 := bstep (se 2 (by rfl) ⟨271647, by rfl⟩ : syracuseStep 724393 = 543295) B543295
theorem B659017 : Blo 338752 659017 := bstep (se 2 (by rfl) ⟨247131, by rfl⟩ : syracuseStep 659017 = 494263) B494263
theorem B2461265 : Blo 338752 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B59477773 : Blo 338752 59477773 := bstep (se 3 (by rfl) ⟨11152082, by rfl⟩ : syracuseStep 59477773 = 22304165) B22304165
theorem B1150739 : Blo 338752 1150739 := bstep (se 1 (by rfl) ⟨863054, by rfl⟩ : syracuseStep 1150739 = 1726109) B1726109
theorem B2330473 : Blo 338752 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B1380959 : Blo 338752 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B1643111 : Blo 338752 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B1151603 : Blo 338752 1151603 := bstep (se 1 (by rfl) ⟨863702, by rfl⟩ : syracuseStep 1151603 = 1727405) B1727405
theorem B1151873 : Blo 338752 1151873 := bstep (se 2 (by rfl) ⟨431952, by rfl⟩ : syracuseStep 1151873 = 863905) B863905
theorem B1938775 : Blo 338752 1938775 := bstep (se 1 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 1938775 = 2908163) B2908163
theorem B1382059 : Blo 338752 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B1152683 : Blo 338752 1152683 := bstep (se 1 (by rfl) ⟨864512, by rfl⟩ : syracuseStep 1152683 = 1729025) B1729025
theorem B3282605 : Blo 338752 3282605 := bstep (se 3 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 3282605 = 1230977) B1230977
theorem B1153007 : Blo 338752 1153007 := bstep (se 1 (by rfl) ⟨864755, by rfl⟩ : syracuseStep 1153007 = 1729511) B1729511
theorem B1153223 : Blo 338752 1153223 := bstep (se 1 (by rfl) ⟨864917, by rfl⟩ : syracuseStep 1153223 = 1729835) B1729835
theorem B6527375 : Blo 338752 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B4921829 : Blo 338752 4921829 := bstep (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) B922843
theorem B1153871 : Blo 338752 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B3120119 : Blo 338752 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B859207 : Blo 338752 859207 := bstep (se 1 (by rfl) ⟨644405, by rfl⟩ : syracuseStep 859207 = 1288811) B1288811
theorem B1154195 : Blo 338752 1154195 := bstep (se 1 (by rfl) ⟨865646, by rfl⟩ : syracuseStep 1154195 = 1731293) B1731293
theorem B859319 : Blo 338752 859319 := bstep (se 1 (by rfl) ⟨644489, by rfl⟩ : syracuseStep 859319 = 1288979) B1288979
theorem B1154465 : Blo 338752 1154465 := bstep (se 2 (by rfl) ⟨432924, by rfl⟩ : syracuseStep 1154465 = 865849) B865849
theorem B1383911 : Blo 338752 1383911 := bstep (se 1 (by rfl) ⟨1037933, by rfl⟩ : syracuseStep 1383911 = 2075867) B2075867
theorem B10690127 : Blo 338752 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B2334419 : Blo 338752 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B1155005 : Blo 338752 1155005 := bstep (se 3 (by rfl) ⟨216563, by rfl⟩ : syracuseStep 1155005 = 433127) B433127
theorem B762209 : Blo 338752 762209 := bstep (se 2 (by rfl) ⟨285828, by rfl⟩ : syracuseStep 762209 = 571657) B571657
theorem B762299 : Blo 338752 762299 := bstep (se 1 (by rfl) ⟨571724, by rfl⟩ : syracuseStep 762299 = 1143449) B1143449
theorem B860615 : Blo 338752 860615 := bstep (se 1 (by rfl) ⟨645461, by rfl⟩ : syracuseStep 860615 = 1290923) B1290923
theorem B5907269 : Blo 338752 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B1090459 : Blo 338752 1090459 := bstep (se 1 (by rfl) ⟨817844, by rfl⟩ : syracuseStep 1090459 = 1635689) B1635689
theorem B3122333 : Blo 338752 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B4662479 : Blo 338752 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B2139497 : Blo 338752 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B763307 : Blo 338752 763307 := bstep (se 1 (by rfl) ⟨572480, by rfl⟩ : syracuseStep 763307 = 1144961) B1144961
theorem B1222141 : Blo 338752 1222141 := bstep (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) B458303
theorem B763559 : Blo 338752 763559 := bstep (se 1 (by rfl) ⟨572669, by rfl⟩ : syracuseStep 763559 = 1145339) B1145339
theorem B763847 : Blo 338752 763847 := bstep (se 1 (by rfl) ⟨572885, by rfl⟩ : syracuseStep 763847 = 1145771) B1145771
theorem B4925519 : Blo 338752 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B4139171 : Blo 338752 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B2599127 : Blo 338752 2599127 := bstep (se 1 (by rfl) ⟨1949345, by rfl⟩ : syracuseStep 2599127 = 3898691) B3898691
theorem B1091819 : Blo 338752 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B764153 : Blo 338752 764153 := bstep (se 2 (by rfl) ⟨286557, by rfl⟩ : syracuseStep 764153 = 573115) B573115
theorem B764207 : Blo 338752 764207 := bstep (se 1 (by rfl) ⟨573155, by rfl⟩ : syracuseStep 764207 = 1146311) B1146311
theorem B862559 : Blo 338752 862559 := bstep (se 1 (by rfl) ⟨646919, by rfl⟩ : syracuseStep 862559 = 1293839) B1293839
theorem B764423 : Blo 338752 764423 := bstep (se 1 (by rfl) ⟨573317, by rfl⟩ : syracuseStep 764423 = 1146635) B1146635
theorem B862751 : Blo 338752 862751 := bstep (se 1 (by rfl) ⟨647063, by rfl⟩ : syracuseStep 862751 = 1294127) B1294127
theorem B764603 : Blo 338752 764603 := bstep (se 1 (by rfl) ⟨573452, by rfl⟩ : syracuseStep 764603 = 1146905) B1146905
theorem B2927299 : Blo 338752 2927299 := bstep (se 1 (by rfl) ⟨2195474, by rfl⟩ : syracuseStep 2927299 = 4390949) B4390949
theorem B338779 : Blo 338752 338779 := bstep (se 1 (by rfl) ⟨254084, by rfl⟩ : syracuseStep 338779 = 508169) B508169
theorem B338847 : Blo 338752 338847 := bstep (se 1 (by rfl) ⟨254135, by rfl⟩ : syracuseStep 338847 = 508271) B508271
theorem B338991 : Blo 338752 338991 := bstep (se 1 (by rfl) ⟨254243, by rfl⟩ : syracuseStep 338991 = 508487) B508487
theorem B2173999 : Blo 338752 2173999 := bstep (se 1 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 2173999 = 3260999) B3260999
theorem B339015 : Blo 338752 339015 := bstep (se 1 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 339015 = 508523) B508523
theorem B339167 : Blo 338752 339167 := bstep (se 1 (by rfl) ⟨254375, by rfl⟩ : syracuseStep 339167 = 508751) B508751
theorem B339431 : Blo 338752 339431 := bstep (se 1 (by rfl) ⟨254573, by rfl⟩ : syracuseStep 339431 = 509147) B509147
theorem B765431 : Blo 338752 765431 := bstep (se 1 (by rfl) ⟨574073, by rfl⟩ : syracuseStep 765431 = 1148147) B1148147
theorem B765503 : Blo 338752 765503 := bstep (se 1 (by rfl) ⟨574127, by rfl⟩ : syracuseStep 765503 = 1148255) B1148255
theorem B9940553 : Blo 338752 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B339547 : Blo 338752 339547 := bstep (se 1 (by rfl) ⟨254660, by rfl⟩ : syracuseStep 339547 = 509321) B509321
theorem B339783 : Blo 338752 339783 := bstep (se 1 (by rfl) ⟨254837, by rfl⟩ : syracuseStep 339783 = 509675) B509675
theorem B339935 : Blo 338752 339935 := bstep (se 1 (by rfl) ⟨254951, by rfl⟩ : syracuseStep 339935 = 509903) B509903
theorem B8859779 : Blo 338752 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B1847461 : Blo 338752 1847461 := bstep (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) B346399
theorem B340199 : Blo 338752 340199 := bstep (se 1 (by rfl) ⟨255149, by rfl⟩ : syracuseStep 340199 = 510299) B510299
theorem B4141313 : Blo 338752 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B340351 : Blo 338752 340351 := bstep (se 1 (by rfl) ⟨255263, by rfl⟩ : syracuseStep 340351 = 510527) B510527
theorem B340431 : Blo 338752 340431 := bstep (se 1 (by rfl) ⟨255323, by rfl⟩ : syracuseStep 340431 = 510647) B510647
theorem B766457 : Blo 338752 766457 := bstep (se 2 (by rfl) ⟨287421, by rfl⟩ : syracuseStep 766457 = 574843) B574843
theorem B766547 : Blo 338752 766547 := bstep (se 1 (by rfl) ⟨574910, by rfl⟩ : syracuseStep 766547 = 1149821) B1149821
theorem B340583 : Blo 338752 340583 := bstep (se 1 (by rfl) ⟨255437, by rfl⟩ : syracuseStep 340583 = 510875) B510875
theorem B766727 : Blo 338752 766727 := bstep (se 1 (by rfl) ⟨575045, by rfl⟩ : syracuseStep 766727 = 1150091) B1150091
theorem B340847 : Blo 338752 340847 := bstep (se 1 (by rfl) ⟨255635, by rfl⟩ : syracuseStep 340847 = 511271) B511271
theorem B1225601 : Blo 338752 1225601 := bstep (se 2 (by rfl) ⟨459600, by rfl⟩ : syracuseStep 1225601 = 919201) B919201
theorem B340903 : Blo 338752 340903 := bstep (se 1 (by rfl) ⟨255677, by rfl⟩ : syracuseStep 340903 = 511355) B511355
theorem B340987 : Blo 338752 340987 := bstep (se 1 (by rfl) ⟨255740, by rfl⟩ : syracuseStep 340987 = 511481) B511481
theorem B341055 : Blo 338752 341055 := bstep (se 1 (by rfl) ⟨255791, by rfl⟩ : syracuseStep 341055 = 511583) B511583
theorem B865343 : Blo 338752 865343 := bstep (se 1 (by rfl) ⟨649007, by rfl⟩ : syracuseStep 865343 = 1298015) B1298015
theorem B341199 : Blo 338752 341199 := bstep (se 1 (by rfl) ⟨255899, by rfl⟩ : syracuseStep 341199 = 511799) B511799
theorem B1717523 : Blo 338752 1717523 := bstep (se 1 (by rfl) ⟨1288142, by rfl⟩ : syracuseStep 1717523 = 2576285) B2576285
theorem B2176307 : Blo 338752 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B341403 : Blo 338752 341403 := bstep (se 1 (by rfl) ⟨256052, by rfl⟩ : syracuseStep 341403 = 512105) B512105
theorem B341615 : Blo 338752 341615 := bstep (se 1 (by rfl) ⟨256211, by rfl⟩ : syracuseStep 341615 = 512423) B512423
theorem B341671 : Blo 338752 341671 := bstep (se 1 (by rfl) ⟨256253, by rfl⟩ : syracuseStep 341671 = 512507) B512507
theorem B341755 : Blo 338752 341755 := bstep (se 1 (by rfl) ⟨256316, by rfl⟩ : syracuseStep 341755 = 512633) B512633
theorem B407327 : Blo 338752 407327 := bstep (se 1 (by rfl) ⟨305495, by rfl⟩ : syracuseStep 407327 = 610991) B610991
theorem B341791 : Blo 338752 341791 := bstep (se 1 (by rfl) ⟨256343, by rfl⟩ : syracuseStep 341791 = 512687) B512687
theorem B767807 : Blo 338752 767807 := bstep (se 1 (by rfl) ⟨575855, by rfl⟩ : syracuseStep 767807 = 1151711) B1151711
theorem B341823 : Blo 338752 341823 := bstep (se 1 (by rfl) ⟨256367, by rfl⟩ : syracuseStep 341823 = 512735) B512735
theorem B341999 : Blo 338752 341999 := bstep (se 1 (by rfl) ⟨256499, by rfl⟩ : syracuseStep 341999 = 512999) B512999
theorem B768095 : Blo 338752 768095 := bstep (se 1 (by rfl) ⟨576071, by rfl⟩ : syracuseStep 768095 = 1152143) B1152143
theorem B866447 : Blo 338752 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B342171 : Blo 338752 342171 := bstep (se 1 (by rfl) ⟨256628, by rfl⟩ : syracuseStep 342171 = 513257) B513257
theorem B342207 : Blo 338752 342207 := bstep (se 1 (by rfl) ⟨256655, by rfl⟩ : syracuseStep 342207 = 513311) B513311
theorem B342319 : Blo 338752 342319 := bstep (se 1 (by rfl) ⟨256739, by rfl⟩ : syracuseStep 342319 = 513479) B513479
theorem B342555 : Blo 338752 342555 := bstep (se 1 (by rfl) ⟨256916, by rfl⟩ : syracuseStep 342555 = 513833) B513833
theorem B342559 : Blo 338752 342559 := bstep (se 1 (by rfl) ⟨256919, by rfl⟩ : syracuseStep 342559 = 513839) B513839
theorem B965459 : Blo 338752 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B768851 : Blo 338752 768851 := bstep (se 1 (by rfl) ⟨576638, by rfl⟩ : syracuseStep 768851 = 1153277) B1153277
theorem B572251 : Blo 338752 572251 := bstep (se 1 (by rfl) ⟨429188, by rfl⟩ : syracuseStep 572251 = 858377) B858377
theorem B1293353 : Blo 338752 1293353 := bstep (se 2 (by rfl) ⟨485007, by rfl⟩ : syracuseStep 1293353 = 970015) B970015
theorem B4308299 : Blo 338752 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B769391 : Blo 338752 769391 := bstep (se 1 (by rfl) ⟨577043, by rfl⟩ : syracuseStep 769391 = 1154087) B1154087
theorem B933331 : Blo 338752 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B769679 : Blo 338752 769679 := bstep (se 1 (by rfl) ⟨577259, by rfl⟩ : syracuseStep 769679 = 1154519) B1154519
theorem B769769 : Blo 338752 769769 := bstep (se 2 (by rfl) ⟨288663, by rfl⟩ : syracuseStep 769769 = 577327) B577327
theorem B573223 : Blo 338752 573223 := bstep (se 1 (by rfl) ⟨429917, by rfl⟩ : syracuseStep 573223 = 859835) B859835
theorem B1163297 : Blo 338752 1163297 := bstep (se 2 (by rfl) ⟨436236, by rfl⟩ : syracuseStep 1163297 = 872473) B872473
theorem B1097867 : Blo 338752 1097867 := bstep (se 1 (by rfl) ⟨823400, by rfl⟩ : syracuseStep 1097867 = 1646801) B1646801
theorem B1720601 : Blo 338752 1720601 := bstep (se 2 (by rfl) ⟨645225, by rfl⟩ : syracuseStep 1720601 = 1290451) B1290451
theorem B4931927 : Blo 338752 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B967099 : Blo 338752 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B508367 : Blo 338752 508367 := bstep (se 1 (by rfl) ⟨381275, by rfl⟩ : syracuseStep 508367 = 762551) B762551
theorem B2965997 : Blo 338752 2965997 := bstep (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) B1112249
theorem B508409 : Blo 338752 508409 := bstep (se 2 (by rfl) ⟨190653, by rfl⟩ : syracuseStep 508409 = 381307) B381307
theorem B508511 : Blo 338752 508511 := bstep (se 1 (by rfl) ⟨381383, by rfl⟩ : syracuseStep 508511 = 762767) B762767
theorem B1229419 : Blo 338752 1229419 := bstep (se 1 (by rfl) ⟨922064, by rfl⟩ : syracuseStep 1229419 = 1844129) B1844129
theorem B770795 : Blo 338752 770795 := bstep (se 1 (by rfl) ⟨578096, by rfl⟩ : syracuseStep 770795 = 1156193) B1156193
theorem B574249 : Blo 338752 574249 := bstep (se 2 (by rfl) ⟨215343, by rfl⟩ : syracuseStep 574249 = 430687) B430687
theorem B574519 : Blo 338752 574519 := bstep (se 1 (by rfl) ⟨430889, by rfl⟩ : syracuseStep 574519 = 861779) B861779
theorem B2573369 : Blo 338752 2573369 := bstep (se 2 (by rfl) ⟨965013, by rfl⟩ : syracuseStep 2573369 = 1930027) B1930027
theorem B508991 : Blo 338752 508991 := bstep (se 1 (by rfl) ⟨381743, by rfl⟩ : syracuseStep 508991 = 763487) B763487
theorem B509033 : Blo 338752 509033 := bstep (se 2 (by rfl) ⟨190887, by rfl⟩ : syracuseStep 509033 = 381775) B381775
theorem B509135 : Blo 338752 509135 := bstep (se 1 (by rfl) ⟨381851, by rfl⟩ : syracuseStep 509135 = 763703) B763703
theorem B509339 : Blo 338752 509339 := bstep (se 1 (by rfl) ⟨382004, by rfl⟩ : syracuseStep 509339 = 764009) B764009
theorem B509561 : Blo 338752 509561 := bstep (se 2 (by rfl) ⟨191085, by rfl⟩ : syracuseStep 509561 = 382171) B382171
theorem B509663 : Blo 338752 509663 := bstep (se 1 (by rfl) ⟨382247, by rfl⟩ : syracuseStep 509663 = 764495) B764495
theorem B1165117 : Blo 338752 1165117 := bstep (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) B436919
theorem B509759 : Blo 338752 509759 := bstep (se 1 (by rfl) ⟨382319, by rfl⟩ : syracuseStep 509759 = 764639) B764639
theorem B1230689 : Blo 338752 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B509927 : Blo 338752 509927 := bstep (se 1 (by rfl) ⟨382445, by rfl⟩ : syracuseStep 509927 = 764891) B764891
theorem B575471 : Blo 338752 575471 := bstep (se 1 (by rfl) ⟨431603, by rfl⟩ : syracuseStep 575471 = 863207) B863207
theorem B509945 : Blo 338752 509945 := bstep (se 2 (by rfl) ⟨191229, by rfl⟩ : syracuseStep 509945 = 382459) B382459
theorem B510047 : Blo 338752 510047 := bstep (se 1 (by rfl) ⟨382535, by rfl⟩ : syracuseStep 510047 = 765071) B765071
theorem B510107 : Blo 338752 510107 := bstep (se 1 (by rfl) ⟨382580, by rfl⟩ : syracuseStep 510107 = 765161) B765161
theorem B4475057 : Blo 338752 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B3950777 : Blo 338752 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B510143 : Blo 338752 510143 := bstep (se 1 (by rfl) ⟨382607, by rfl⟩ : syracuseStep 510143 = 765215) B765215
theorem B2181329 : Blo 338752 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B510185 : Blo 338752 510185 := bstep (se 2 (by rfl) ⟨191319, by rfl⟩ : syracuseStep 510185 = 382639) B382639
theorem B510491 : Blo 338752 510491 := bstep (se 1 (by rfl) ⟨382868, by rfl⟩ : syracuseStep 510491 = 765737) B765737
theorem B576031 : Blo 338752 576031 := bstep (se 1 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 576031 = 864047) B864047
theorem B510569 : Blo 338752 510569 := bstep (se 2 (by rfl) ⟨191463, by rfl⟩ : syracuseStep 510569 = 382927) B382927
theorem B8276701 : Blo 338752 8276701 := bstep (se 3 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 8276701 = 3103763) B3103763
theorem B576463 : Blo 338752 576463 := bstep (se 1 (by rfl) ⟨432347, by rfl⟩ : syracuseStep 576463 = 864695) B864695
theorem B969707 : Blo 338752 969707 := bstep (se 1 (by rfl) ⟨727280, by rfl⟩ : syracuseStep 969707 = 1454561) B1454561
theorem B511097 : Blo 338752 511097 := bstep (se 2 (by rfl) ⟨191661, by rfl⟩ : syracuseStep 511097 = 383323) B383323
theorem B511199 : Blo 338752 511199 := bstep (se 1 (by rfl) ⟨383399, by rfl⟩ : syracuseStep 511199 = 766799) B766799
theorem B511241 : Blo 338752 511241 := bstep (se 2 (by rfl) ⟨191715, by rfl⟩ : syracuseStep 511241 = 383431) B383431
theorem B511343 : Blo 338752 511343 := bstep (se 1 (by rfl) ⟨383507, by rfl⟩ : syracuseStep 511343 = 767015) B767015
theorem B2575799 : Blo 338752 2575799 := bstep (se 1 (by rfl) ⟨1931849, by rfl⟩ : syracuseStep 2575799 = 3863699) B3863699
theorem B511463 : Blo 338752 511463 := bstep (se 1 (by rfl) ⟨383597, by rfl⟩ : syracuseStep 511463 = 767195) B767195
theorem B970231 : Blo 338752 970231 := bstep (se 1 (by rfl) ⟨727673, by rfl⟩ : syracuseStep 970231 = 1455347) B1455347
theorem B4345433 : Blo 338752 4345433 := bstep (se 2 (by rfl) ⟨1629537, by rfl⟩ : syracuseStep 4345433 = 3259075) B3259075
theorem B2182763 : Blo 338752 2182763 := bstep (se 1 (by rfl) ⟨1637072, by rfl⟩ : syracuseStep 2182763 = 3274145) B3274145
theorem B511595 : Blo 338752 511595 := bstep (se 1 (by rfl) ⟨383696, by rfl⟩ : syracuseStep 511595 = 767393) B767393
theorem B1560221 : Blo 338752 1560221 := bstep (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) B585083
theorem B2444975 : Blo 338752 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B577199 : Blo 338752 577199 := bstep (se 1 (by rfl) ⟨432899, by rfl⟩ : syracuseStep 577199 = 865799) B865799
theorem B511721 : Blo 338752 511721 := bstep (se 2 (by rfl) ⟨191895, by rfl⟩ : syracuseStep 511721 = 383791) B383791
theorem B7884557 : Blo 338752 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B511865 : Blo 338752 511865 := bstep (se 2 (by rfl) ⟨191949, by rfl⟩ : syracuseStep 511865 = 383899) B383899
theorem B2445203 : Blo 338752 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B577435 : Blo 338752 577435 := bstep (se 1 (by rfl) ⟨433076, by rfl⟩ : syracuseStep 577435 = 866153) B866153
theorem B511967 : Blo 338752 511967 := bstep (se 1 (by rfl) ⟨383975, by rfl⟩ : syracuseStep 511967 = 767951) B767951
theorem B512219 : Blo 338752 512219 := bstep (se 1 (by rfl) ⟨384164, by rfl⟩ : syracuseStep 512219 = 768329) B768329
theorem B512231 : Blo 338752 512231 := bstep (se 1 (by rfl) ⟨384173, by rfl⟩ : syracuseStep 512231 = 768347) B768347
theorem B577847 : Blo 338752 577847 := bstep (se 1 (by rfl) ⟨433385, by rfl⟩ : syracuseStep 577847 = 866771) B866771
theorem B971119 : Blo 338752 971119 := bstep (se 1 (by rfl) ⟨728339, by rfl⟩ : syracuseStep 971119 = 1456679) B1456679
theorem B512393 : Blo 338752 512393 := bstep (se 2 (by rfl) ⟨192147, by rfl⟩ : syracuseStep 512393 = 384295) B384295
theorem B512489 : Blo 338752 512489 := bstep (se 2 (by rfl) ⟨192183, by rfl⟩ : syracuseStep 512489 = 384367) B384367
theorem B971347 : Blo 338752 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B512615 : Blo 338752 512615 := bstep (se 1 (by rfl) ⟨384461, by rfl⟩ : syracuseStep 512615 = 768923) B768923
theorem B512747 : Blo 338752 512747 := bstep (se 1 (by rfl) ⟨384560, by rfl⟩ : syracuseStep 512747 = 769121) B769121
theorem B512777 : Blo 338752 512777 := bstep (se 2 (by rfl) ⟨192291, by rfl⟩ : syracuseStep 512777 = 384583) B384583
theorem B4379467 : Blo 338752 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B512879 : Blo 338752 512879 := bstep (se 1 (by rfl) ⟨384659, by rfl⟩ : syracuseStep 512879 = 769319) B769319
theorem B513131 : Blo 338752 513131 := bstep (se 1 (by rfl) ⟨384848, by rfl⟩ : syracuseStep 513131 = 769697) B769697
theorem B2184403 : Blo 338752 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B513371 : Blo 338752 513371 := bstep (se 1 (by rfl) ⟨385028, by rfl⟩ : syracuseStep 513371 = 770057) B770057
theorem B5821793 : Blo 338752 5821793 := bstep (se 2 (by rfl) ⟨2183172, by rfl⟩ : syracuseStep 5821793 = 4366345) B4366345
theorem B513647 : Blo 338752 513647 := bstep (se 1 (by rfl) ⟨385235, by rfl⟩ : syracuseStep 513647 = 770471) B770471
theorem B513719 : Blo 338752 513719 := bstep (se 1 (by rfl) ⟨385289, by rfl⟩ : syracuseStep 513719 = 770579) B770579
theorem B513755 : Blo 338752 513755 := bstep (se 1 (by rfl) ⟨385316, by rfl⟩ : syracuseStep 513755 = 770633) B770633
theorem B382783 : Blo 338752 382783 := bstep (se 1 (by rfl) ⟨287087, by rfl⟩ : syracuseStep 382783 = 574175) B574175
theorem B513929 : Blo 338752 513929 := bstep (se 2 (by rfl) ⟨192723, by rfl⟩ : syracuseStep 513929 = 385447) B385447
theorem B514031 : Blo 338752 514031 := bstep (se 1 (by rfl) ⟨385523, by rfl⟩ : syracuseStep 514031 = 771047) B771047
theorem B383071 : Blo 338752 383071 := bstep (se 1 (by rfl) ⟨287303, by rfl⟩ : syracuseStep 383071 = 574607) B574607
theorem B1038491 : Blo 338752 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B2185481 : Blo 338752 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B1562921 : Blo 338752 1562921 := bstep (se 2 (by rfl) ⟨586095, by rfl⟩ : syracuseStep 1562921 = 1172191) B1172191
theorem B645499 : Blo 338752 645499 := bstep (se 1 (by rfl) ⟨484124, by rfl⟩ : syracuseStep 645499 = 968249) B968249
theorem B8739251 : Blo 338752 8739251 := bstep (se 1 (by rfl) ⟨6554438, by rfl⟩ : syracuseStep 8739251 = 13108877) B13108877
theorem B1301129 : Blo 338752 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B4775057 : Blo 338752 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B1662137 : Blo 338752 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B384223 : Blo 338752 384223 := bstep (se 1 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 384223 = 576335) B576335
theorem B2186635 : Blo 338752 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B548459 : Blo 338752 548459 := bstep (se 1 (by rfl) ⟨411344, by rfl⟩ : syracuseStep 548459 = 822689) B822689
theorem B974663 : Blo 338752 974663 := bstep (se 1 (by rfl) ⟨730997, by rfl⟩ : syracuseStep 974663 = 1461995) B1461995
theorem B548831 : Blo 338752 548831 := bstep (se 1 (by rfl) ⟨411623, by rfl⟩ : syracuseStep 548831 = 823247) B823247
theorem B614783 : Blo 338752 614783 := bstep (se 1 (by rfl) ⟨461087, by rfl⟩ : syracuseStep 614783 = 922175) B922175
theorem B7332227 : Blo 338752 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B3268997 : Blo 338752 3268997 := bstep (se 4 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 3268997 = 612937) B612937
theorem B161014169 : Blo 338752 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B975311 : Blo 338752 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B2581145 : Blo 338752 2581145 := bstep (se 2 (by rfl) ⟨967929, by rfl⟩ : syracuseStep 2581145 = 1935859) B1935859
theorem B975995 : Blo 338752 975995 := bstep (se 1 (by rfl) ⟨731996, by rfl⟩ : syracuseStep 975995 = 1463993) B1463993
theorem B4121765 : Blo 338752 4121765 := bstep (se 4 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 4121765 = 772831) B772831
theorem B2222113 : Blo 338752 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B617593 : Blo 338752 617593 := bstep (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) B463195
theorem B486767 : Blo 338752 486767 := bstep (se 1 (by rfl) ⟨365075, by rfl⟩ : syracuseStep 486767 = 730151) B730151
theorem B487291 : Blo 338752 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B3665857 : Blo 338752 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B1929527 : Blo 338752 1929527 := bstep (se 1 (by rfl) ⟨1447145, by rfl⟩ : syracuseStep 1929527 = 2894291) B2894291
theorem B2748809 : Blo 338752 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B1733075 : Blo 338752 1733075 := bstep (se 1 (by rfl) ⟨1299806, by rfl⟩ : syracuseStep 1733075 = 2599613) B2599613
theorem B1962641 : Blo 338752 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B2192093 : Blo 338752 2192093 := bstep (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) B822035
theorem B4649957 : Blo 338752 4649957 := bstep (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) B871867
theorem B1143881 : Blo 338752 1143881 := bstep (se 2 (by rfl) ⟨428955, by rfl⟩ : syracuseStep 1143881 = 857911) B857911
theorem B1832519 : Blo 338752 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B817307 : Blo 338752 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B1145501 : Blo 338752 1145501 := bstep (se 3 (by rfl) ⟨214781, by rfl⟩ : syracuseStep 1145501 = 429563) B429563
theorem B1375055 : Blo 338752 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B4684709 : Blo 338752 4684709 := bstep (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) B878383
theorem B1145825 : Blo 338752 1145825 := bstep (se 2 (by rfl) ⟨429684, by rfl⟩ : syracuseStep 1145825 = 859369) B859369
theorem B1146041 : Blo 338752 1146041 := bstep (se 2 (by rfl) ⟨429765, by rfl⟩ : syracuseStep 1146041 = 859531) B859531
theorem B1932943 : Blo 338752 1932943 := bstep (se 1 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 1932943 = 2899415) B2899415
theorem B2752699 : Blo 338752 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B1147067 : Blo 338752 1147067 := bstep (se 1 (by rfl) ⟨860300, by rfl⟩ : syracuseStep 1147067 = 1720601) B1720601
theorem B1639225 : Blo 338752 1639225 := bstep (se 2 (by rfl) ⟨614709, by rfl⟩ : syracuseStep 1639225 = 1229419) B1229419
theorem B12583997 : Blo 338752 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B1377503 : Blo 338752 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B820459 : Blo 338752 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B1639727 : Blo 338752 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B919775 : Blo 338752 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B1640843 : Blo 338752 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B920639 : Blo 338752 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B3903065 : Blo 338752 3903065 := bstep (se 2 (by rfl) ⟨1463649, by rfl⟩ : syracuseStep 3903065 = 2927299) B2927299
theorem B692327 : Blo 338752 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B823457 : Blo 338752 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B3281219 : Blo 338752 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B5509549 : Blo 338752 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B1086205 : Blo 338752 1086205 := bstep (se 3 (by rfl) ⟨203663, by rfl⟩ : syracuseStep 1086205 = 407327) B407327
theorem B3183371 : Blo 338752 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B922607 : Blo 338752 922607 := bstep (se 1 (by rfl) ⟨691955, by rfl⟩ : syracuseStep 922607 = 1383911) B1383911
theorem B79303697 : Blo 338752 79303697 := bstep (se 2 (by rfl) ⟨29738886, by rfl⟩ : syracuseStep 79303697 = 59477773) B59477773
theorem B365639 : Blo 338752 365639 := bstep (se 1 (by rfl) ⟨274229, by rfl⟩ : syracuseStep 365639 = 548459) B548459
theorem B4887809 : Blo 338752 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B365887 : Blo 338752 365887 := bstep (se 1 (by rfl) ⟨274415, by rfl⟩ : syracuseStep 365887 = 548831) B548831
theorem B2463281 : Blo 338752 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B4888151 : Blo 338752 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B3938179 : Blo 338752 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B5839289 : Blo 338752 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B3283679 : Blo 338752 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B2759447 : Blo 338752 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B727879 : Blo 338752 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B1842745 : Blo 338752 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B6627035 : Blo 338752 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B5906519 : Blo 338752 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B2760875 : Blo 338752 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B1286351 : Blo 338752 1286351 := bstep (se 1 (by rfl) ⟨964763, by rfl⟩ : syracuseStep 1286351 = 1929527) B1929527
theorem B1155383 : Blo 338752 1155383 := bstep (se 1 (by rfl) ⟨866537, by rfl⟩ : syracuseStep 1155383 = 1733075) B1733075
theorem B3514757 : Blo 338752 3514757 := bstep (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) B659017
theorem B860665 : Blo 338752 860665 := bstep (se 2 (by rfl) ⟨322749, by rfl⟩ : syracuseStep 860665 = 645499) B645499
theorem B762587 : Blo 338752 762587 := bstep (se 1 (by rfl) ⟨571940, by rfl⟩ : syracuseStep 762587 = 1143881) B1143881
theorem B1450871 : Blo 338752 1450871 := bstep (se 1 (by rfl) ⟨1088153, by rfl⟩ : syracuseStep 1450871 = 2176307) B2176307
theorem B1221679 : Blo 338752 1221679 := bstep (se 1 (by rfl) ⟨916259, by rfl⟩ : syracuseStep 1221679 = 1832519) B1832519
theorem B763001 : Blo 338752 763001 := bstep (se 2 (by rfl) ⟨286125, by rfl⟩ : syracuseStep 763001 = 572251) B572251
theorem B763667 : Blo 338752 763667 := bstep (se 1 (by rfl) ⟨572750, by rfl⟩ : syracuseStep 763667 = 1145501) B1145501
theorem B3123139 : Blo 338752 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B763883 : Blo 338752 763883 := bstep (se 1 (by rfl) ⟨572912, by rfl⟩ : syracuseStep 763883 = 1145825) B1145825
theorem B862235 : Blo 338752 862235 := bstep (se 1 (by rfl) ⟨646676, by rfl⟩ : syracuseStep 862235 = 1293353) B1293353
theorem B764027 : Blo 338752 764027 := bstep (se 1 (by rfl) ⟨573020, by rfl⟩ : syracuseStep 764027 = 1146041) B1146041
theorem B764297 : Blo 338752 764297 := bstep (se 2 (by rfl) ⟨286611, by rfl⟩ : syracuseStep 764297 = 573223) B573223
theorem B731911 : Blo 338752 731911 := bstep (se 1 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 731911 = 1097867) B1097867
theorem B3287951 : Blo 338752 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B338911 : Blo 338752 338911 := bstep (se 1 (by rfl) ⟨254183, by rfl⟩ : syracuseStep 338911 = 508367) B508367
theorem B1977331 : Blo 338752 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B338939 : Blo 338752 338939 := bstep (se 1 (by rfl) ⟨254204, by rfl⟩ : syracuseStep 338939 = 508409) B508409
theorem B339007 : Blo 338752 339007 := bstep (se 1 (by rfl) ⟨254255, by rfl⟩ : syracuseStep 339007 = 508511) B508511
theorem B764999 : Blo 338752 764999 := bstep (se 1 (by rfl) ⟨573749, by rfl⟩ : syracuseStep 764999 = 1147499) B1147499
theorem B1289465 : Blo 338752 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B1715579 : Blo 338752 1715579 := bstep (se 1 (by rfl) ⟨1286684, by rfl⟩ : syracuseStep 1715579 = 2573369) B2573369
theorem B339327 : Blo 338752 339327 := bstep (se 1 (by rfl) ⟨254495, by rfl⟩ : syracuseStep 339327 = 508991) B508991
theorem B339355 : Blo 338752 339355 := bstep (se 1 (by rfl) ⟨254516, by rfl⟩ : syracuseStep 339355 = 509033) B509033
theorem B765395 : Blo 338752 765395 := bstep (se 1 (by rfl) ⟨574046, by rfl⟩ : syracuseStep 765395 = 1148093) B1148093
theorem B339423 : Blo 338752 339423 := bstep (se 1 (by rfl) ⟨254567, by rfl⟩ : syracuseStep 339423 = 509135) B509135
theorem B339559 : Blo 338752 339559 := bstep (se 1 (by rfl) ⟨254669, by rfl⟩ : syracuseStep 339559 = 509339) B509339
theorem B765665 : Blo 338752 765665 := bstep (se 2 (by rfl) ⟨287124, by rfl⟩ : syracuseStep 765665 = 574249) B574249
theorem B339707 : Blo 338752 339707 := bstep (se 1 (by rfl) ⟨254780, by rfl⟩ : syracuseStep 339707 = 509561) B509561
theorem B339775 : Blo 338752 339775 := bstep (se 1 (by rfl) ⟨254831, by rfl⟩ : syracuseStep 339775 = 509663) B509663
theorem B1453945 : Blo 338752 1453945 := bstep (se 2 (by rfl) ⟨545229, by rfl⟩ : syracuseStep 1453945 = 1090459) B1090459
theorem B339839 : Blo 338752 339839 := bstep (se 1 (by rfl) ⟨254879, by rfl⟩ : syracuseStep 339839 = 509759) B509759
theorem B339951 : Blo 338752 339951 := bstep (se 1 (by rfl) ⟨254963, by rfl⟩ : syracuseStep 339951 = 509927) B509927
theorem B3256307 : Blo 338752 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B339963 : Blo 338752 339963 := bstep (se 1 (by rfl) ⟨254972, by rfl⟩ : syracuseStep 339963 = 509945) B509945
theorem B340031 : Blo 338752 340031 := bstep (se 1 (by rfl) ⟨255023, by rfl⟩ : syracuseStep 340031 = 510047) B510047
theorem B766025 : Blo 338752 766025 := bstep (se 2 (by rfl) ⟨287259, by rfl⟩ : syracuseStep 766025 = 574519) B574519
theorem B340071 : Blo 338752 340071 := bstep (se 1 (by rfl) ⟨255053, by rfl⟩ : syracuseStep 340071 = 510107) B510107
theorem B2633851 : Blo 338752 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B340095 : Blo 338752 340095 := bstep (se 1 (by rfl) ⟨255071, by rfl⟩ : syracuseStep 340095 = 510143) B510143
theorem B766079 : Blo 338752 766079 := bstep (se 1 (by rfl) ⟨574559, by rfl⟩ : syracuseStep 766079 = 1149119) B1149119
theorem B1454219 : Blo 338752 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B340123 : Blo 338752 340123 := bstep (se 1 (by rfl) ⟨255092, by rfl⟩ : syracuseStep 340123 = 510185) B510185
theorem B340327 : Blo 338752 340327 := bstep (se 1 (by rfl) ⟨255245, by rfl⟩ : syracuseStep 340327 = 510491) B510491
theorem B340379 : Blo 338752 340379 := bstep (se 1 (by rfl) ⟨255284, by rfl⟩ : syracuseStep 340379 = 510569) B510569
theorem B340731 : Blo 338752 340731 := bstep (se 1 (by rfl) ⟨255548, by rfl⟩ : syracuseStep 340731 = 511097) B511097
theorem B1553215 : Blo 338752 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B340799 : Blo 338752 340799 := bstep (se 1 (by rfl) ⟨255599, by rfl⟩ : syracuseStep 340799 = 511199) B511199
theorem B340827 : Blo 338752 340827 := bstep (se 1 (by rfl) ⟨255620, by rfl⟩ : syracuseStep 340827 = 511241) B511241
theorem B340895 : Blo 338752 340895 := bstep (se 1 (by rfl) ⟨255671, by rfl⟩ : syracuseStep 340895 = 511343) B511343
theorem B1717199 : Blo 338752 1717199 := bstep (se 1 (by rfl) ⟨1287899, by rfl⟩ : syracuseStep 1717199 = 2575799) B2575799
theorem B340975 : Blo 338752 340975 := bstep (se 1 (by rfl) ⟨255731, by rfl⟩ : syracuseStep 340975 = 511463) B511463
theorem B2896955 : Blo 338752 2896955 := bstep (se 1 (by rfl) ⟨2172716, by rfl⟩ : syracuseStep 2896955 = 4345433) B4345433
theorem B1455175 : Blo 338752 1455175 := bstep (se 1 (by rfl) ⟨1091381, by rfl⟩ : syracuseStep 1455175 = 2182763) B2182763
theorem B341063 : Blo 338752 341063 := bstep (se 1 (by rfl) ⟨255797, by rfl⟩ : syracuseStep 341063 = 511595) B511595
theorem B1553489 : Blo 338752 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B341147 : Blo 338752 341147 := bstep (se 1 (by rfl) ⟨255860, by rfl⟩ : syracuseStep 341147 = 511721) B511721
theorem B5256371 : Blo 338752 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B767159 : Blo 338752 767159 := bstep (se 1 (by rfl) ⟨575369, by rfl⟩ : syracuseStep 767159 = 1150739) B1150739
theorem B4371677 : Blo 338752 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B341243 : Blo 338752 341243 := bstep (se 1 (by rfl) ⟨255932, by rfl⟩ : syracuseStep 341243 = 511865) B511865
theorem B341311 : Blo 338752 341311 := bstep (se 1 (by rfl) ⟨255983, by rfl⟩ : syracuseStep 341311 = 511967) B511967
theorem B2962817 : Blo 338752 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B341479 : Blo 338752 341479 := bstep (se 1 (by rfl) ⟨256109, by rfl⟩ : syracuseStep 341479 = 512219) B512219
theorem B341487 : Blo 338752 341487 := bstep (se 1 (by rfl) ⟨256115, by rfl⟩ : syracuseStep 341487 = 512231) B512231
theorem B341595 : Blo 338752 341595 := bstep (se 1 (by rfl) ⟨256196, by rfl⟩ : syracuseStep 341595 = 512393) B512393
theorem B341659 : Blo 338752 341659 := bstep (se 1 (by rfl) ⟨256244, by rfl⟩ : syracuseStep 341659 = 512489) B512489
theorem B341743 : Blo 338752 341743 := bstep (se 1 (by rfl) ⟨256307, by rfl⟩ : syracuseStep 341743 = 512615) B512615
theorem B1095407 : Blo 338752 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B767735 : Blo 338752 767735 := bstep (se 1 (by rfl) ⟨575801, by rfl⟩ : syracuseStep 767735 = 1151603) B1151603
theorem B341831 : Blo 338752 341831 := bstep (se 1 (by rfl) ⟨256373, by rfl⟩ : syracuseStep 341831 = 512747) B512747
theorem B341851 : Blo 338752 341851 := bstep (se 1 (by rfl) ⟨256388, by rfl⟩ : syracuseStep 341851 = 512777) B512777
theorem B12433277 : Blo 338752 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B341919 : Blo 338752 341919 := bstep (se 1 (by rfl) ⟨256439, by rfl⟩ : syracuseStep 341919 = 512879) B512879
theorem B767915 : Blo 338752 767915 := bstep (se 1 (by rfl) ⟨575936, by rfl⟩ : syracuseStep 767915 = 1151873) B1151873
theorem B768041 : Blo 338752 768041 := bstep (se 2 (by rfl) ⟨288015, by rfl⟩ : syracuseStep 768041 = 576031) B576031
theorem B342087 : Blo 338752 342087 := bstep (se 1 (by rfl) ⟨256565, by rfl⟩ : syracuseStep 342087 = 513131) B513131
theorem B342247 : Blo 338752 342247 := bstep (se 1 (by rfl) ⟨256685, by rfl⟩ : syracuseStep 342247 = 513371) B513371
theorem B3881195 : Blo 338752 3881195 := bstep (se 1 (by rfl) ⟨2910896, by rfl⟩ : syracuseStep 3881195 = 5821793) B5821793
theorem B342431 : Blo 338752 342431 := bstep (se 1 (by rfl) ⟨256823, by rfl⟩ : syracuseStep 342431 = 513647) B513647
theorem B768455 : Blo 338752 768455 := bstep (se 1 (by rfl) ⟨576341, by rfl⟩ : syracuseStep 768455 = 1152683) B1152683
theorem B342479 : Blo 338752 342479 := bstep (se 1 (by rfl) ⟨256859, by rfl⟩ : syracuseStep 342479 = 513719) B513719
theorem B342503 : Blo 338752 342503 := bstep (se 1 (by rfl) ⟨256877, by rfl⟩ : syracuseStep 342503 = 513755) B513755
theorem B342619 : Blo 338752 342619 := bstep (se 1 (by rfl) ⟨256964, by rfl⟩ : syracuseStep 342619 = 513929) B513929
theorem B768617 : Blo 338752 768617 := bstep (se 2 (by rfl) ⟨288231, by rfl⟩ : syracuseStep 768617 = 576463) B576463
theorem B768671 : Blo 338752 768671 := bstep (se 1 (by rfl) ⟨576503, by rfl⟩ : syracuseStep 768671 = 1153007) B1153007
theorem B342687 : Blo 338752 342687 := bstep (se 1 (by rfl) ⟨257015, by rfl⟩ : syracuseStep 342687 = 514031) B514031
theorem B2898665 : Blo 338752 2898665 := bstep (se 2 (by rfl) ⟨1086999, by rfl⟩ : syracuseStep 2898665 = 2173999) B2173999
theorem B768815 : Blo 338752 768815 := bstep (se 1 (by rfl) ⟨576611, by rfl⟩ : syracuseStep 768815 = 1153223) B1153223
theorem B1456987 : Blo 338752 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B867419 : Blo 338752 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B572521 : Blo 338752 572521 := bstep (se 2 (by rfl) ⟨214695, by rfl⟩ : syracuseStep 572521 = 429391) B429391
theorem B769247 : Blo 338752 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B965857 : Blo 338752 965857 := bstep (se 2 (by rfl) ⟨362196, by rfl⟩ : syracuseStep 965857 = 724393) B724393
theorem B1293641 : Blo 338752 1293641 := bstep (se 2 (by rfl) ⟨485115, by rfl⟩ : syracuseStep 1293641 = 970231) B970231
theorem B2080079 : Blo 338752 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B769463 : Blo 338752 769463 := bstep (se 1 (by rfl) ⟨577097, by rfl⟩ : syracuseStep 769463 = 1154195) B1154195
theorem B572879 : Blo 338752 572879 := bstep (se 1 (by rfl) ⟨429659, by rfl⟩ : syracuseStep 572879 = 859319) B859319
theorem B769643 : Blo 338752 769643 := bstep (se 1 (by rfl) ⟨577232, by rfl⟩ : syracuseStep 769643 = 1154465) B1154465
theorem B7126751 : Blo 338752 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B1556279 : Blo 338752 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B769913 : Blo 338752 769913 := bstep (se 2 (by rfl) ⟨288717, by rfl⟩ : syracuseStep 769913 = 577435) B577435
theorem B770003 : Blo 338752 770003 := bstep (se 1 (by rfl) ⟨577502, by rfl⟩ : syracuseStep 770003 = 1155005) B1155005
theorem B508139 : Blo 338752 508139 := bstep (se 1 (by rfl) ⟨381104, by rfl⟩ : syracuseStep 508139 = 762209) B762209
theorem B409855 : Blo 338752 409855 := bstep (se 1 (by rfl) ⟨307391, by rfl⟩ : syracuseStep 409855 = 614783) B614783
theorem B2179331 : Blo 338752 2179331 := bstep (se 1 (by rfl) ⟨1634498, by rfl⟩ : syracuseStep 2179331 = 3268997) B3268997
theorem B508199 : Blo 338752 508199 := bstep (se 1 (by rfl) ⟨381149, by rfl⟩ : syracuseStep 508199 = 762299) B762299
theorem B573743 : Blo 338752 573743 := bstep (se 1 (by rfl) ⟨430307, by rfl⟩ : syracuseStep 573743 = 860615) B860615
theorem B1720763 : Blo 338752 1720763 := bstep (se 1 (by rfl) ⟨1290572, by rfl⟩ : syracuseStep 1720763 = 2581145) B2581145
theorem B1294825 : Blo 338752 1294825 := bstep (se 2 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 1294825 = 971119) B971119
theorem B2081555 : Blo 338752 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B1295129 : Blo 338752 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B1426331 : Blo 338752 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B508871 : Blo 338752 508871 := bstep (se 1 (by rfl) ⟨381653, by rfl⟩ : syracuseStep 508871 = 763307) B763307
theorem B509039 : Blo 338752 509039 := bstep (se 1 (by rfl) ⟨381779, by rfl⟩ : syracuseStep 509039 = 763559) B763559
theorem B509231 : Blo 338752 509231 := bstep (se 1 (by rfl) ⟨381923, by rfl⟩ : syracuseStep 509231 = 763847) B763847
theorem B509435 : Blo 338752 509435 := bstep (se 1 (by rfl) ⟨382076, by rfl⟩ : syracuseStep 509435 = 764153) B764153
theorem B509471 : Blo 338752 509471 := bstep (se 1 (by rfl) ⟨382103, by rfl⟩ : syracuseStep 509471 = 764207) B764207
theorem B575039 : Blo 338752 575039 := bstep (se 1 (by rfl) ⟨431279, by rfl⟩ : syracuseStep 575039 = 862559) B862559
theorem B509615 : Blo 338752 509615 := bstep (se 1 (by rfl) ⟨382211, by rfl⟩ : syracuseStep 509615 = 764423) B764423
theorem B575167 : Blo 338752 575167 := bstep (se 1 (by rfl) ⟨431375, by rfl⟩ : syracuseStep 575167 = 862751) B862751
theorem B509735 : Blo 338752 509735 := bstep (se 1 (by rfl) ⟨382301, by rfl⟩ : syracuseStep 509735 = 764603) B764603
theorem B510287 : Blo 338752 510287 := bstep (se 1 (by rfl) ⟨382715, by rfl⟩ : syracuseStep 510287 = 765431) B765431
theorem B510335 : Blo 338752 510335 := bstep (se 1 (by rfl) ⟨382751, by rfl⟩ : syracuseStep 510335 = 765503) B765503
theorem B510377 : Blo 338752 510377 := bstep (se 2 (by rfl) ⟨191391, by rfl⟩ : syracuseStep 510377 = 382783) B382783
theorem B510761 : Blo 338752 510761 := bstep (se 2 (by rfl) ⟨191535, by rfl⟩ : syracuseStep 510761 = 383071) B383071
theorem B510971 : Blo 338752 510971 := bstep (se 1 (by rfl) ⟨383228, by rfl⟩ : syracuseStep 510971 = 766457) B766457
theorem B511031 : Blo 338752 511031 := bstep (se 1 (by rfl) ⟨383273, by rfl⟩ : syracuseStep 511031 = 766547) B766547
theorem B1461395 : Blo 338752 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B511151 : Blo 338752 511151 := bstep (se 1 (by rfl) ⟨383363, by rfl⟩ : syracuseStep 511151 = 766727) B766727
theorem B3099971 : Blo 338752 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B576895 : Blo 338752 576895 := bstep (se 1 (by rfl) ⟨432671, by rfl⟩ : syracuseStep 576895 = 865343) B865343
theorem B1298045 : Blo 338752 1298045 := bstep (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) B486767
theorem B511871 : Blo 338752 511871 := bstep (se 1 (by rfl) ⟨383903, by rfl⟩ : syracuseStep 511871 = 767807) B767807
theorem B512063 : Blo 338752 512063 := bstep (se 1 (by rfl) ⟨384047, by rfl⟩ : syracuseStep 512063 = 768095) B768095
theorem B577631 : Blo 338752 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B544871 : Blo 338752 544871 := bstep (se 1 (by rfl) ⟨408653, by rfl⟩ : syracuseStep 544871 = 817307) B817307
theorem B512297 : Blo 338752 512297 := bstep (se 2 (by rfl) ⟨192111, by rfl⟩ : syracuseStep 512297 = 384223) B384223
theorem B643639 : Blo 338752 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B512567 : Blo 338752 512567 := bstep (se 1 (by rfl) ⟨384425, by rfl⟩ : syracuseStep 512567 = 768851) B768851
theorem B2577257 : Blo 338752 2577257 := bstep (se 2 (by rfl) ⟨966471, by rfl⟩ : syracuseStep 2577257 = 1932943) B1932943
theorem B2872199 : Blo 338752 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B512927 : Blo 338752 512927 := bstep (se 1 (by rfl) ⟨384695, by rfl⟩ : syracuseStep 512927 = 769391) B769391
theorem B513119 : Blo 338752 513119 := bstep (se 1 (by rfl) ⟨384839, by rfl⟩ : syracuseStep 513119 = 769679) B769679
theorem B513179 : Blo 338752 513179 := bstep (se 1 (by rfl) ⟨384884, by rfl⟩ : syracuseStep 513179 = 769769) B769769
theorem B775531 : Blo 338752 775531 := bstep (se 1 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 775531 = 1163297) B1163297
theorem B1463975 : Blo 338752 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B513863 : Blo 338752 513863 := bstep (se 1 (by rfl) ⟨385397, by rfl⟩ : syracuseStep 513863 = 770795) B770795
theorem B4413971 : Blo 338752 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B383647 : Blo 338752 383647 := bstep (se 1 (by rfl) ⟨287735, by rfl⟩ : syracuseStep 383647 = 575471) B575471
theorem B5233709 : Blo 338752 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B47733941 : Blo 338752 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B646471 : Blo 338752 646471 := bstep (se 1 (by rfl) ⟨484853, by rfl⟩ : syracuseStep 646471 = 969707) B969707
theorem B1629521 : Blo 338752 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B5791175 : Blo 338752 5791175 := bstep (se 1 (by rfl) ⟨4343381, by rfl⟩ : syracuseStep 5791175 = 8686763) B8686763
theorem B4677097 : Blo 338752 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B1040147 : Blo 338752 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B1629983 : Blo 338752 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B384799 : Blo 338752 384799 := bstep (se 1 (by rfl) ⟨288599, by rfl⟩ : syracuseStep 384799 = 577199) B577199
theorem B1630135 : Blo 338752 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B385231 : Blo 338752 385231 := bstep (se 1 (by rfl) ⟨288923, by rfl⟩ : syracuseStep 385231 = 577847) B577847
theorem B11035601 : Blo 338752 11035601 := bstep (se 2 (by rfl) ⟨4138350, by rfl⟩ : syracuseStep 11035601 = 8276701) B8276701
theorem B2188403 : Blo 338752 2188403 := bstep (se 1 (by rfl) ⟨1641302, by rfl⟩ : syracuseStep 2188403 = 3282605) B3282605
theorem B1041947 : Blo 338752 1041947 := bstep (se 1 (by rfl) ⟨781460, by rfl⟩ : syracuseStep 1041947 = 1562921) B1562921
theorem B4351583 : Blo 338752 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B5826167 : Blo 338752 5826167 := bstep (se 1 (by rfl) ⟨4369625, by rfl⟩ : syracuseStep 5826167 = 8739251) B8739251
theorem B1108091 : Blo 338752 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B3107297 : Blo 338752 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B649721 : Blo 338752 649721 := bstep (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) B487291
theorem B649775 : Blo 338752 649775 := bstep (se 1 (by rfl) ⟨487331, by rfl⟩ : syracuseStep 649775 = 974663) B974663
theorem B107342779 : Blo 338752 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B650207 : Blo 338752 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B650663 : Blo 338752 650663 := bstep (se 1 (by rfl) ⟨487997, by rfl⟩ : syracuseStep 650663 = 975995) B975995
theorem B2747843 : Blo 338752 2747843 := bstep (se 1 (by rfl) ⟨2060882, by rfl⟩ : syracuseStep 2747843 = 4121765) B4121765
theorem B1732751 : Blo 338752 1732751 := bstep (se 1 (by rfl) ⟨1299563, by rfl⟩ : syracuseStep 1732751 = 2599127) B2599127
theorem B2912537 : Blo 338752 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B2585033 : Blo 338752 2585033 := bstep (se 2 (by rfl) ⟨969387, by rfl⟩ : syracuseStep 2585033 = 1938775) B1938775
theorem B1832539 : Blo 338752 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B1144637 : Blo 338752 1144637 := bstep (se 3 (by rfl) ⟨214619, by rfl⟩ : syracuseStep 1144637 = 429239) B429239
theorem B817067 : Blo 338752 817067 := bstep (se 1 (by rfl) ⟨612800, by rfl⟩ : syracuseStep 817067 = 1225601) B1225601
theorem B1145015 : Blo 338752 1145015 := bstep (se 1 (by rfl) ⟨858761, by rfl⟩ : syracuseStep 1145015 = 1717523) B1717523
theorem B1145609 : Blo 338752 1145609 := bstep (se 2 (by rfl) ⟨429603, by rfl⟩ : syracuseStep 1145609 = 859207) B859207
theorem B2915513 : Blo 338752 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B916703 : Blo 338752 916703 := bstep (se 1 (by rfl) ⟨687527, by rfl⟩ : syracuseStep 916703 = 1375055) B1375055
theorem B1244441 : Blo 338752 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B3670265 : Blo 338752 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B1147175 : Blo 338752 1147175 := bstep (se 1 (by rfl) ⟨860381, by rfl⟩ : syracuseStep 1147175 = 1720763) B1720763
theorem B2195885 : Blo 338752 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B950887 : Blo 338752 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B1147553 : Blo 338752 1147553 := bstep (se 2 (by rfl) ⟨430332, by rfl⟩ : syracuseStep 1147553 = 860665) B860665
theorem B8389331 : Blo 338752 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B3900149 : Blo 338752 3900149 := bstep (se 5 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 3900149 = 365639) B365639
theorem B918335 : Blo 338752 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B9372685 : Blo 338752 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B2066647 : Blo 338752 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B4164185 : Blo 338752 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B363247 : Blo 338752 363247 := bstep (se 1 (by rfl) ⟨272435, by rfl⟩ : syracuseStep 363247 = 544871) B544871
theorem B1642187 : Blo 338752 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B31822627 : Blo 338752 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B1086347 : Blo 338752 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B1938593 : Blo 338752 1938593 := bstep (se 2 (by rfl) ⟨726972, by rfl⟩ : syracuseStep 1938593 = 1453945) B1453945
theorem B693431 : Blo 338752 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B1086655 : Blo 338752 1086655 := bstep (se 1 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 1086655 = 1629983) B1629983
theorem B3937679 : Blo 338752 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B1840583 : Blo 338752 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B857567 : Blo 338752 857567 := bstep (se 1 (by rfl) ⟨643175, by rfl⟩ : syracuseStep 857567 = 1286351) B1286351
theorem B3511801 : Blo 338752 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B2954909 : Blo 338752 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B7346065 : Blo 338752 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B858185 : Blo 338752 858185 := bstep (se 2 (by rfl) ⟨321819, by rfl⟩ : syracuseStep 858185 = 643639) B643639
theorem B1448273 : Blo 338752 1448273 := bstep (se 2 (by rfl) ⟨543102, by rfl⟩ : syracuseStep 1448273 = 1086205) B1086205
theorem B694631 : Blo 338752 694631 := bstep (se 1 (by rfl) ⟨520973, by rfl⟩ : syracuseStep 694631 = 1041947) B1041947
theorem B2070953 : Blo 338752 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B1940233 : Blo 338752 1940233 := bstep (se 2 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 1940233 = 1455175) B1455175
theorem B2071531 : Blo 338752 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B433183 : Blo 338752 433183 := bstep (se 1 (by rfl) ⟨324887, by rfl⟩ : syracuseStep 433183 = 649775) B649775
theorem B859643 : Blo 338752 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B433775 : Blo 338752 433775 := bstep (se 1 (by rfl) ⟨325331, by rfl⟩ : syracuseStep 433775 = 650663) B650663
theorem B5250905 : Blo 338752 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B2170871 : Blo 338752 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B1155167 : Blo 338752 1155167 := bstep (se 1 (by rfl) ⟨866375, by rfl⟩ : syracuseStep 1155167 = 1732751) B1732751
theorem B1941691 : Blo 338752 1941691 := bstep (se 1 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 1941691 = 2912537) B2912537
theorem B3318509 : Blo 338752 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B1975211 : Blo 338752 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B1942649 : Blo 338752 1942649 := bstep (se 2 (by rfl) ⟨728493, by rfl⟩ : syracuseStep 1942649 = 1456987) B1456987
theorem B730271 : Blo 338752 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B763091 : Blo 338752 763091 := bstep (se 1 (by rfl) ⟨572318, by rfl⟩ : syracuseStep 763091 = 1144637) B1144637
theorem B763343 : Blo 338752 763343 := bstep (se 1 (by rfl) ⟨572507, by rfl⟩ : syracuseStep 763343 = 1145015) B1145015
theorem B763361 : Blo 338752 763361 := bstep (se 2 (by rfl) ⟨286260, by rfl⟩ : syracuseStep 763361 = 572521) B572521
theorem B1287809 : Blo 338752 1287809 := bstep (se 2 (by rfl) ⟨482928, by rfl⟩ : syracuseStep 1287809 = 965857) B965857
theorem B861961 : Blo 338752 861961 := bstep (se 2 (by rfl) ⟨323235, by rfl⟩ : syracuseStep 861961 = 646471) B646471
theorem B763739 : Blo 338752 763739 := bstep (se 1 (by rfl) ⟨572804, by rfl⟩ : syracuseStep 763739 = 1145609) B1145609
theorem B6236129 : Blo 338752 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B1943675 : Blo 338752 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B862427 : Blo 338752 862427 := bstep (se 1 (by rfl) ⟨646820, by rfl⟩ : syracuseStep 862427 = 1293641) B1293641
theorem B1386719 : Blo 338752 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B2173513 : Blo 338752 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B764711 : Blo 338752 764711 := bstep (se 1 (by rfl) ⟨573533, by rfl⟩ : syracuseStep 764711 = 1147067) B1147067
theorem B338759 : Blo 338752 338759 := bstep (se 1 (by rfl) ⟨254069, by rfl⟩ : syracuseStep 338759 = 508139) B508139
theorem B1452887 : Blo 338752 1452887 := bstep (se 1 (by rfl) ⟨1089665, by rfl⟩ : syracuseStep 1452887 = 2179331) B2179331
theorem B338799 : Blo 338752 338799 := bstep (se 1 (by rfl) ⟨254099, by rfl⟩ : syracuseStep 338799 = 508199) B508199
theorem B1846205 : Blo 338752 1846205 := bstep (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) B692327
theorem B1387703 : Blo 338752 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B863419 : Blo 338752 863419 := bstep (se 1 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 863419 = 1295129) B1295129
theorem B339247 : Blo 338752 339247 := bstep (se 1 (by rfl) ⟨254435, by rfl⟩ : syracuseStep 339247 = 508871) B508871
theorem B339359 : Blo 338752 339359 := bstep (se 1 (by rfl) ⟨254519, by rfl⟩ : syracuseStep 339359 = 509039) B509039
theorem B339487 : Blo 338752 339487 := bstep (se 1 (by rfl) ⟨254615, by rfl⟩ : syracuseStep 339487 = 509231) B509231
theorem B1093151 : Blo 338752 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B339623 : Blo 338752 339623 := bstep (se 1 (by rfl) ⟨254717, by rfl⟩ : syracuseStep 339623 = 509435) B509435
theorem B339647 : Blo 338752 339647 := bstep (se 1 (by rfl) ⟨254735, by rfl⟩ : syracuseStep 339647 = 509471) B509471
theorem B339743 : Blo 338752 339743 := bstep (se 1 (by rfl) ⟨254807, by rfl⟩ : syracuseStep 339743 = 509615) B509615
theorem B339823 : Blo 338752 339823 := bstep (se 1 (by rfl) ⟨254867, by rfl⟩ : syracuseStep 339823 = 509735) B509735
theorem B340191 : Blo 338752 340191 := bstep (se 1 (by rfl) ⟨255143, by rfl⟩ : syracuseStep 340191 = 510287) B510287
theorem B340223 : Blo 338752 340223 := bstep (se 1 (by rfl) ⟨255167, by rfl⟩ : syracuseStep 340223 = 510335) B510335
theorem B1093895 : Blo 338752 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B340251 : Blo 338752 340251 := bstep (se 1 (by rfl) ⟨255188, by rfl⟩ : syracuseStep 340251 = 510377) B510377
theorem B1093945 : Blo 338752 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B340507 : Blo 338752 340507 := bstep (se 1 (by rfl) ⟨255380, by rfl⟩ : syracuseStep 340507 = 510761) B510761
theorem B340647 : Blo 338752 340647 := bstep (se 1 (by rfl) ⟨255485, by rfl⟩ : syracuseStep 340647 = 510971) B510971
theorem B340687 : Blo 338752 340687 := bstep (se 1 (by rfl) ⟨255515, by rfl⟩ : syracuseStep 340687 = 511031) B511031
theorem B340767 : Blo 338752 340767 := bstep (se 1 (by rfl) ⟨255575, by rfl⟩ : syracuseStep 340767 = 511151) B511151
theorem B766889 : Blo 338752 766889 := bstep (se 2 (by rfl) ⟨287583, by rfl⟩ : syracuseStep 766889 = 575167) B575167
theorem B2602043 : Blo 338752 2602043 := bstep (se 1 (by rfl) ⟨1951532, by rfl⟩ : syracuseStep 2602043 = 3903065) B3903065
theorem B865363 : Blo 338752 865363 := bstep (se 1 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 865363 = 1298045) B1298045
theorem B341247 : Blo 338752 341247 := bstep (se 1 (by rfl) ⟨255935, by rfl⟩ : syracuseStep 341247 = 511871) B511871
theorem B341375 : Blo 338752 341375 := bstep (se 1 (by rfl) ⟨256031, by rfl⟩ : syracuseStep 341375 = 512063) B512063
theorem B341531 : Blo 338752 341531 := bstep (se 1 (by rfl) ⟨256148, by rfl⟩ : syracuseStep 341531 = 512297) B512297
theorem B341711 : Blo 338752 341711 := bstep (se 1 (by rfl) ⟨256283, by rfl⟩ : syracuseStep 341711 = 512567) B512567
theorem B1718171 : Blo 338752 1718171 := bstep (se 1 (by rfl) ⟨1288628, by rfl⟩ : syracuseStep 1718171 = 2577257) B2577257
theorem B1914799 : Blo 338752 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B341951 : Blo 338752 341951 := bstep (se 1 (by rfl) ⟨256463, by rfl⟩ : syracuseStep 341951 = 512927) B512927
theorem B52869131 : Blo 338752 52869131 := bstep (se 1 (by rfl) ⟨39651848, by rfl⟩ : syracuseStep 52869131 = 79303697) B79303697
theorem B342079 : Blo 338752 342079 := bstep (se 1 (by rfl) ⟨256559, by rfl⟩ : syracuseStep 342079 = 513119) B513119
theorem B342119 : Blo 338752 342119 := bstep (se 1 (by rfl) ⟨256589, by rfl⟩ : syracuseStep 342119 = 513179) B513179
theorem B3258539 : Blo 338752 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B3258767 : Blo 338752 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B342575 : Blo 338752 342575 := bstep (se 1 (by rfl) ⟨256931, by rfl⟩ : syracuseStep 342575 = 513863) B513863
theorem B2636441 : Blo 338752 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B769193 : Blo 338752 769193 := bstep (se 2 (by rfl) ⟨288447, by rfl⟩ : syracuseStep 769193 = 576895) B576895
theorem B3489139 : Blo 338752 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B2178845 : Blo 338752 2178845 := bstep (se 3 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 2178845 = 817067) B817067
theorem B770255 : Blo 338752 770255 := bstep (se 1 (by rfl) ⟨577691, by rfl⟩ : syracuseStep 770255 = 1155383) B1155383
theorem B508391 : Blo 338752 508391 := bstep (se 1 (by rfl) ⟨381293, by rfl⟩ : syracuseStep 508391 = 762587) B762587
theorem B967247 : Blo 338752 967247 := bstep (se 1 (by rfl) ⟨725435, by rfl⟩ : syracuseStep 967247 = 1450871) B1450871
theorem B7357067 : Blo 338752 7357067 := bstep (se 1 (by rfl) ⟨5517800, by rfl⟩ : syracuseStep 7357067 = 11035601) B11035601
theorem B1458935 : Blo 338752 1458935 := bstep (se 1 (by rfl) ⟨1094201, by rfl⟩ : syracuseStep 1458935 = 2188403) B2188403
theorem B508667 : Blo 338752 508667 := bstep (se 1 (by rfl) ⟨381500, by rfl⟩ : syracuseStep 508667 = 763001) B763001
theorem B2901055 : Blo 338752 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B3884111 : Blo 338752 3884111 := bstep (se 1 (by rfl) ⟨2913083, by rfl⟩ : syracuseStep 3884111 = 5826167) B5826167
theorem B509111 : Blo 338752 509111 := bstep (se 1 (by rfl) ⟨381833, by rfl⟩ : syracuseStep 509111 = 763667) B763667
theorem B509255 : Blo 338752 509255 := bstep (se 1 (by rfl) ⟨381941, by rfl⟩ : syracuseStep 509255 = 763883) B763883
theorem B574823 : Blo 338752 574823 := bstep (se 1 (by rfl) ⟨431117, by rfl⟩ : syracuseStep 574823 = 862235) B862235
theorem B509351 : Blo 338752 509351 := bstep (se 1 (by rfl) ⟨382013, by rfl⟩ : syracuseStep 509351 = 764027) B764027
theorem B509531 : Blo 338752 509531 := bstep (se 1 (by rfl) ⟨382148, by rfl⟩ : syracuseStep 509531 = 764297) B764297
theorem B1951397 : Blo 338752 1951397 := bstep (se 4 (by rfl) ⟨182943, by rfl⟩ : syracuseStep 1951397 = 365887) B365887
theorem B1034041 : Blo 338752 1034041 := bstep (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) B775531
theorem B509999 : Blo 338752 509999 := bstep (se 1 (by rfl) ⟨382499, by rfl⟩ : syracuseStep 509999 = 764999) B764999
theorem B7358525 : Blo 338752 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B2443385 : Blo 338752 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B510263 : Blo 338752 510263 := bstep (se 1 (by rfl) ⟨382697, by rfl⟩ : syracuseStep 510263 = 765395) B765395
theorem B510443 : Blo 338752 510443 := bstep (se 1 (by rfl) ⟨382832, by rfl⟩ : syracuseStep 510443 = 765665) B765665
theorem B510683 : Blo 338752 510683 := bstep (se 1 (by rfl) ⟨383012, by rfl⟩ : syracuseStep 510683 = 766025) B766025
theorem B510719 : Blo 338752 510719 := bstep (se 1 (by rfl) ⟨383039, by rfl⟩ : syracuseStep 510719 = 766079) B766079
theorem B969479 : Blo 338752 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B1723355 : Blo 338752 1723355 := bstep (se 1 (by rfl) ⟨1292516, by rfl⟩ : syracuseStep 1723355 = 2585033) B2585033
theorem B1035659 : Blo 338752 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B511439 : Blo 338752 511439 := bstep (se 1 (by rfl) ⟨383579, by rfl⟩ : syracuseStep 511439 = 767159) B767159
theorem B511529 : Blo 338752 511529 := bstep (se 2 (by rfl) ⟨191823, by rfl⟩ : syracuseStep 511529 = 383647) B383647
theorem B970505 : Blo 338752 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B511823 : Blo 338752 511823 := bstep (se 1 (by rfl) ⟨383867, by rfl⟩ : syracuseStep 511823 = 767735) B767735
theorem B511943 : Blo 338752 511943 := bstep (se 1 (by rfl) ⟨383957, by rfl⟩ : syracuseStep 511943 = 767915) B767915
theorem B512027 : Blo 338752 512027 := bstep (se 1 (by rfl) ⟨384020, by rfl⟩ : syracuseStep 512027 = 768041) B768041
theorem B512303 : Blo 338752 512303 := bstep (se 1 (by rfl) ⟨384227, by rfl⟩ : syracuseStep 512303 = 768455) B768455
theorem B512411 : Blo 338752 512411 := bstep (se 1 (by rfl) ⟨384308, by rfl⟩ : syracuseStep 512411 = 768617) B768617
theorem B512447 : Blo 338752 512447 := bstep (se 1 (by rfl) ⟨384335, by rfl⟩ : syracuseStep 512447 = 768671) B768671
theorem B512543 : Blo 338752 512543 := bstep (se 1 (by rfl) ⟨384407, by rfl⟩ : syracuseStep 512543 = 768815) B768815
theorem B578279 : Blo 338752 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B611135 : Blo 338752 611135 := bstep (se 1 (by rfl) ⟨458351, by rfl⟩ : syracuseStep 611135 = 916703) B916703
theorem B512831 : Blo 338752 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B512975 : Blo 338752 512975 := bstep (se 1 (by rfl) ⟨384731, by rfl⟩ : syracuseStep 512975 = 769463) B769463
theorem B381919 : Blo 338752 381919 := bstep (se 1 (by rfl) ⟨286439, by rfl⟩ : syracuseStep 381919 = 572879) B572879
theorem B513065 : Blo 338752 513065 := bstep (se 2 (by rfl) ⟨192399, by rfl⟩ : syracuseStep 513065 = 384799) B384799
theorem B513095 : Blo 338752 513095 := bstep (se 1 (by rfl) ⟨384821, by rfl⟩ : syracuseStep 513095 = 769643) B769643
theorem B1037519 : Blo 338752 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B513275 : Blo 338752 513275 := bstep (se 1 (by rfl) ⟨384956, by rfl⟩ : syracuseStep 513275 = 769913) B769913
theorem B513335 : Blo 338752 513335 := bstep (se 1 (by rfl) ⟨385001, by rfl⟩ : syracuseStep 513335 = 770003) B770003
theorem B382495 : Blo 338752 382495 := bstep (se 1 (by rfl) ⟨286871, by rfl⟩ : syracuseStep 382495 = 573743) B573743
theorem B513641 : Blo 338752 513641 := bstep (se 2 (by rfl) ⟨192615, by rfl⟩ : syracuseStep 513641 = 385231) B385231
theorem B546473 : Blo 338752 546473 := bstep (se 2 (by rfl) ⟨204927, by rfl⟩ : syracuseStep 546473 = 409855) B409855
theorem B1726433 : Blo 338752 1726433 := bstep (se 2 (by rfl) ⟨647412, by rfl⟩ : syracuseStep 1726433 = 1294825) B1294825
theorem B383359 : Blo 338752 383359 := bstep (se 1 (by rfl) ⟨287519, by rfl⟩ : syracuseStep 383359 = 575039) B575039
theorem B2185633 : Blo 338752 2185633 := bstep (se 2 (by rfl) ⟨819612, by rfl⟩ : syracuseStep 2185633 = 1639225) B1639225
theorem B1628905 : Blo 338752 1628905 := bstep (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) B1221679
theorem B613183 : Blo 338752 613183 := bstep (se 1 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 613183 = 919775) B919775
theorem B613759 : Blo 338752 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B974263 : Blo 338752 974263 := bstep (se 1 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 974263 = 1461395) B1461395
theorem B385087 : Blo 338752 385087 := bstep (se 1 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 385087 = 577631) B577631
theorem B2187479 : Blo 338752 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B14016989 : Blo 338752 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B2122247 : Blo 338752 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B615071 : Blo 338752 615071 := bstep (se 1 (by rfl) ⟨461303, by rfl⟩ : syracuseStep 615071 = 922607) B922607
theorem B975881 : Blo 338752 975881 := bstep (se 2 (by rfl) ⟨365955, by rfl⟩ : syracuseStep 975881 = 731911) B731911
theorem B975983 : Blo 338752 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B143123705 : Blo 338752 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B3892859 : Blo 338752 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B2942647 : Blo 338752 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B2189119 : Blo 338752 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B3860783 : Blo 338752 3860783 := bstep (se 1 (by rfl) ⟨2895587, by rfl⟩ : syracuseStep 3860783 = 5791175) B5791175
theorem B4418023 : Blo 338752 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B1732589 : Blo 338752 1732589 := bstep (se 3 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 1732589 = 649721) B649721
theorem B2191967 : Blo 338752 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B1143719 : Blo 338752 1143719 := bstep (se 1 (by rfl) ⟨857789, by rfl⟩ : syracuseStep 1143719 = 1715579) B1715579
theorem B1831895 : Blo 338752 1831895 := bstep (se 1 (by rfl) ⟨1373921, by rfl⟩ : syracuseStep 1831895 = 2747843) B2747843
theorem B1733885 : Blo 338752 1733885 := bstep (se 3 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 1733885 = 650207) B650207
theorem B1144799 : Blo 338752 1144799 := bstep (se 1 (by rfl) ⟨858599, by rfl⟩ : syracuseStep 1144799 = 1717199) B1717199
theorem B1931303 : Blo 338752 1931303 := bstep (se 1 (by rfl) ⟨1448477, by rfl⟩ : syracuseStep 1931303 = 2896955) B2896955
theorem B2914451 : Blo 338752 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B8288851 : Blo 338752 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B2587463 : Blo 338752 2587463 := bstep (se 1 (by rfl) ⟨1940597, by rfl⟩ : syracuseStep 2587463 = 3881195) B3881195
theorem B1932443 : Blo 338752 1932443 := bstep (se 1 (by rfl) ⟨1449332, by rfl⟩ : syracuseStep 1932443 = 2898665) B2898665
theorem B19004669 : Blo 338752 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B2456993 : Blo 338752 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B2588921 : Blo 338752 2588921 := bstep (se 2 (by rfl) ⟨970845, by rfl⟩ : syracuseStep 2588921 = 1941691) B1941691
theorem B2589407 : Blo 338752 2589407 := bstep (se 1 (by rfl) ⟨1942055, by rfl⟩ : syracuseStep 2589407 = 3884111) B3884111
theorem B3868073 : Blo 338752 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B1640189 : Blo 338752 1640189 := bstep (se 3 (by rfl) ⟨307535, by rfl⟩ : syracuseStep 1640189 = 615071) B615071
theorem B1148903 : Blo 338752 1148903 := bstep (se 1 (by rfl) ⟨861677, by rfl⟩ : syracuseStep 1148903 = 1723355) B1723355
theorem B690439 : Blo 338752 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B1149281 : Blo 338752 1149281 := bstep (se 2 (by rfl) ⟨430980, by rfl⟩ : syracuseStep 1149281 = 861961) B861961
theorem B1378721 : Blo 338752 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B2918825 : Blo 338752 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B2755529 : Blo 338752 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B724231 : Blo 338752 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B462287 : Blo 338752 462287 := bstep (se 1 (by rfl) ⟨346715, by rfl⟩ : syracuseStep 462287 = 693431) B693431
theorem B691679 : Blo 338752 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B2625119 : Blo 338752 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B1969939 : Blo 338752 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B1937317 : Blo 338752 1937317 := bstep (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) B363247
theorem B1150955 : Blo 338752 1150955 := bstep (se 1 (by rfl) ⟨863216, by rfl⟩ : syracuseStep 1150955 = 1726433) B1726433
theorem B463087 : Blo 338752 463087 := bstep (se 1 (by rfl) ⟨347315, by rfl⟩ : syracuseStep 463087 = 694631) B694631
theorem B1151225 : Blo 338752 1151225 := bstep (se 2 (by rfl) ⟨431709, by rfl⟩ : syracuseStep 1151225 = 863419) B863419
theorem B1380635 : Blo 338752 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B1447247 : Blo 338752 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B9344659 : Blo 338752 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B1414831 : Blo 338752 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B1316807 : Blo 338752 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B2595239 : Blo 338752 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B858539 : Blo 338752 858539 := bstep (se 1 (by rfl) ⟨643904, by rfl⟩ : syracuseStep 858539 = 1287809) B1287809
theorem B1153817 : Blo 338752 1153817 := bstep (se 2 (by rfl) ⟨432681, by rfl⟩ : syracuseStep 1153817 = 865363) B865363
theorem B924479 : Blo 338752 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B1448873 : Blo 338752 1448873 := bstep (se 2 (by rfl) ⟨543327, by rfl⟩ : syracuseStep 1448873 = 1086655) B1086655
theorem B728767 : Blo 338752 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B1155059 : Blo 338752 1155059 := bstep (se 1 (by rfl) ⟨866294, by rfl⟩ : syracuseStep 1155059 = 1732589) B1732589
theorem B729263 : Blo 338752 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B762479 : Blo 338752 762479 := bstep (se 1 (by rfl) ⟨571859, by rfl⟩ : syracuseStep 762479 = 1143719) B1143719
theorem B1221263 : Blo 338752 1221263 := bstep (se 1 (by rfl) ⟨915947, by rfl⟩ : syracuseStep 1221263 = 1831895) B1831895
theorem B11051801 : Blo 338752 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B1155923 : Blo 338752 1155923 := bstep (se 1 (by rfl) ⟨866942, by rfl⟩ : syracuseStep 1155923 = 1733885) B1733885
theorem B2171873 : Blo 338752 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B2762041 : Blo 338752 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B763199 : Blo 338752 763199 := bstep (se 1 (by rfl) ⟨572399, by rfl⟩ : syracuseStep 763199 = 1144799) B1144799
theorem B1287535 : Blo 338752 1287535 := bstep (se 1 (by rfl) ⟨965651, by rfl⟩ : syracuseStep 1287535 = 1931303) B1931303
theorem B1942967 : Blo 338752 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B2172359 : Blo 338752 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B2172511 : Blo 338752 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B1156733 : Blo 338752 1156733 := bstep (se 3 (by rfl) ⟨216887, by rfl⟩ : syracuseStep 1156733 = 433775) B433775
theorem B1288295 : Blo 338752 1288295 := bstep (se 1 (by rfl) ⟨966221, by rfl⟩ : syracuseStep 1288295 = 1932443) B1932443
theorem B1452563 : Blo 338752 1452563 := bstep (se 1 (by rfl) ⟨1089422, by rfl⟩ : syracuseStep 1452563 = 2178845) B2178845
theorem B764783 : Blo 338752 764783 := bstep (se 1 (by rfl) ⟨573587, by rfl⟩ : syracuseStep 764783 = 1147175) B1147175
theorem B338927 : Blo 338752 338927 := bstep (se 1 (by rfl) ⟨254195, by rfl⟩ : syracuseStep 338927 = 508391) B508391
theorem B765035 : Blo 338752 765035 := bstep (se 1 (by rfl) ⟨573776, by rfl⟩ : syracuseStep 765035 = 1147553) B1147553
theorem B2600099 : Blo 338752 2600099 := bstep (se 1 (by rfl) ⟨1950074, by rfl⟩ : syracuseStep 2600099 = 3900149) B3900149
theorem B339111 : Blo 338752 339111 := bstep (se 1 (by rfl) ⟨254333, by rfl⟩ : syracuseStep 339111 = 508667) B508667
theorem B339407 : Blo 338752 339407 := bstep (se 1 (by rfl) ⟨254555, by rfl⟩ : syracuseStep 339407 = 509111) B509111
theorem B339503 : Blo 338752 339503 := bstep (se 1 (by rfl) ⟨254627, by rfl⟩ : syracuseStep 339503 = 509255) B509255
theorem B339567 : Blo 338752 339567 := bstep (se 1 (by rfl) ⟨254675, by rfl⟩ : syracuseStep 339567 = 509351) B509351
theorem B339687 : Blo 338752 339687 := bstep (se 1 (by rfl) ⟨254765, by rfl⟩ : syracuseStep 339687 = 509531) B509531
theorem B12496913 : Blo 338752 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B339999 : Blo 338752 339999 := bstep (se 1 (by rfl) ⟨254999, by rfl⟩ : syracuseStep 339999 = 509999) B509999
theorem B340175 : Blo 338752 340175 := bstep (se 1 (by rfl) ⟨255131, by rfl⟩ : syracuseStep 340175 = 510263) B510263
theorem B340295 : Blo 338752 340295 := bstep (se 1 (by rfl) ⟨255221, by rfl⟩ : syracuseStep 340295 = 510443) B510443
theorem B340455 : Blo 338752 340455 := bstep (se 1 (by rfl) ⟨255341, by rfl⟩ : syracuseStep 340455 = 510683) B510683
theorem B340479 : Blo 338752 340479 := bstep (se 1 (by rfl) ⟨255359, by rfl⟩ : syracuseStep 340479 = 510719) B510719
theorem B340959 : Blo 338752 340959 := bstep (se 1 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 340959 = 511439) B511439
theorem B341019 : Blo 338752 341019 := bstep (se 1 (by rfl) ⟨255764, by rfl⟩ : syracuseStep 341019 = 511529) B511529
theorem B1094791 : Blo 338752 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B341215 : Blo 338752 341215 := bstep (se 1 (by rfl) ⟨255911, by rfl⟩ : syracuseStep 341215 = 511823) B511823
theorem B341295 : Blo 338752 341295 := bstep (se 1 (by rfl) ⟨255971, by rfl⟩ : syracuseStep 341295 = 511943) B511943
theorem B341351 : Blo 338752 341351 := bstep (se 1 (by rfl) ⟨256013, by rfl⟩ : syracuseStep 341351 = 512027) B512027
theorem B341535 : Blo 338752 341535 := bstep (se 1 (by rfl) ⟨256151, by rfl⟩ : syracuseStep 341535 = 512303) B512303
theorem B341607 : Blo 338752 341607 := bstep (se 1 (by rfl) ⟨256205, by rfl⟩ : syracuseStep 341607 = 512411) B512411
theorem B2602621 : Blo 338752 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B341631 : Blo 338752 341631 := bstep (se 1 (by rfl) ⟨256223, by rfl⟩ : syracuseStep 341631 = 512447) B512447
theorem B341695 : Blo 338752 341695 := bstep (se 1 (by rfl) ⟨256271, by rfl⟩ : syracuseStep 341695 = 512543) B512543
theorem B407423 : Blo 338752 407423 := bstep (se 1 (by rfl) ⟨305567, by rfl⟩ : syracuseStep 407423 = 611135) B611135
theorem B341887 : Blo 338752 341887 := bstep (se 1 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 341887 = 512831) B512831
theorem B341983 : Blo 338752 341983 := bstep (se 1 (by rfl) ⟨256487, by rfl⟩ : syracuseStep 341983 = 512975) B512975
theorem B342043 : Blo 338752 342043 := bstep (se 1 (by rfl) ⟨256532, by rfl⟩ : syracuseStep 342043 = 513065) B513065
theorem B342063 : Blo 338752 342063 := bstep (se 1 (by rfl) ⟨256547, by rfl⟩ : syracuseStep 342063 = 513095) B513095
theorem B2898017 : Blo 338752 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B1292395 : Blo 338752 1292395 := bstep (se 1 (by rfl) ⟨969296, by rfl⟩ : syracuseStep 1292395 = 1938593) B1938593
theorem B342183 : Blo 338752 342183 := bstep (se 1 (by rfl) ⟨256637, by rfl⟩ : syracuseStep 342183 = 513275) B513275
theorem B342223 : Blo 338752 342223 := bstep (se 1 (by rfl) ⟨256667, by rfl⟩ : syracuseStep 342223 = 513335) B513335
theorem B571711 : Blo 338752 571711 := bstep (se 1 (by rfl) ⟨428783, by rfl⟩ : syracuseStep 571711 = 857567) B857567
theorem B342427 : Blo 338752 342427 := bstep (se 1 (by rfl) ⟨256820, by rfl⟩ : syracuseStep 342427 = 513641) B513641
theorem B572123 : Blo 338752 572123 := bstep (se 1 (by rfl) ⟨429092, by rfl⟩ : syracuseStep 572123 = 858185) B858185
theorem B965515 : Blo 338752 965515 := bstep (se 1 (by rfl) ⟨724136, by rfl⟩ : syracuseStep 965515 = 1448273) B1448273
theorem B1457261 : Blo 338752 1457261 := bstep (se 3 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 1457261 = 546473) B546473
theorem B573095 : Blo 338752 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B770111 : Blo 338752 770111 := bstep (se 1 (by rfl) ⟨577583, by rfl⟩ : syracuseStep 770111 = 1155167) B1155167
theorem B1458319 : Blo 338752 1458319 := bstep (se 1 (by rfl) ⟨1093739, by rfl⟩ : syracuseStep 1458319 = 2187479) B2187479
theorem B1458593 : Blo 338752 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B2212339 : Blo 338752 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B1295099 : Blo 338752 1295099 := bstep (se 1 (by rfl) ⟨971324, by rfl⟩ : syracuseStep 1295099 = 1942649) B1942649
theorem B508727 : Blo 338752 508727 := bstep (se 1 (by rfl) ⟨381545, by rfl⟩ : syracuseStep 508727 = 763091) B763091
theorem B508895 : Blo 338752 508895 := bstep (se 1 (by rfl) ⟨381671, by rfl⟩ : syracuseStep 508895 = 763343) B763343
theorem B508907 : Blo 338752 508907 := bstep (se 1 (by rfl) ⟨381680, by rfl⟩ : syracuseStep 508907 = 763361) B763361
theorem B509159 : Blo 338752 509159 := bstep (se 1 (by rfl) ⟨381869, by rfl⟩ : syracuseStep 509159 = 763739) B763739
theorem B509225 : Blo 338752 509225 := bstep (se 2 (by rfl) ⟨190959, by rfl⟩ : syracuseStep 509225 = 381919) B381919
theorem B1295783 : Blo 338752 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B574951 : Blo 338752 574951 := bstep (se 1 (by rfl) ⟨431213, by rfl⟩ : syracuseStep 574951 = 862427) B862427
theorem B2573855 : Blo 338752 2573855 := bstep (se 1 (by rfl) ⟨1930391, by rfl⟩ : syracuseStep 2573855 = 3860783) B3860783
theorem B509807 : Blo 338752 509807 := bstep (se 1 (by rfl) ⟨382355, by rfl⟩ : syracuseStep 509807 = 764711) B764711
theorem B968591 : Blo 338752 968591 := bstep (se 1 (by rfl) ⟨726443, by rfl⟩ : syracuseStep 968591 = 1452887) B1452887
theorem B1230803 : Blo 338752 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B509993 : Blo 338752 509993 := bstep (se 2 (by rfl) ⟨191247, by rfl⟩ : syracuseStep 509993 = 382495) B382495
theorem B18729605 : Blo 338752 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B1461311 : Blo 338752 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B511145 : Blo 338752 511145 := bstep (se 2 (by rfl) ⟨191679, by rfl⟩ : syracuseStep 511145 = 383359) B383359
theorem B511259 : Blo 338752 511259 := bstep (se 1 (by rfl) ⟨383444, by rfl⟩ : syracuseStep 511259 = 766889) B766889
theorem B35246087 : Blo 338752 35246087 := bstep (se 1 (by rfl) ⟨26434565, by rfl⟩ : syracuseStep 35246087 = 52869131) B52869131
theorem B577577 : Blo 338752 577577 := bstep (se 2 (by rfl) ⟨216591, by rfl⟩ : syracuseStep 577577 = 433183) B433183
theorem B1757627 : Blo 338752 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B1724975 : Blo 338752 1724975 := bstep (se 1 (by rfl) ⟨1293731, by rfl⟩ : syracuseStep 1724975 = 2587463) B2587463
theorem B1299017 : Blo 338752 1299017 := bstep (se 2 (by rfl) ⟨487131, by rfl⟩ : syracuseStep 1299017 = 974263) B974263
theorem B512795 : Blo 338752 512795 := bstep (se 1 (by rfl) ⟨384596, by rfl⟩ : syracuseStep 512795 = 769193) B769193
theorem B12669779 : Blo 338752 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B513449 : Blo 338752 513449 := bstep (se 2 (by rfl) ⟨192543, by rfl⟩ : syracuseStep 513449 = 385087) B385087
theorem B513503 : Blo 338752 513503 := bstep (se 1 (by rfl) ⟨385127, by rfl⟩ : syracuseStep 513503 = 770255) B770255
theorem B2446843 : Blo 338752 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B1463923 : Blo 338752 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B644831 : Blo 338752 644831 := bstep (se 1 (by rfl) ⟨483623, by rfl⟩ : syracuseStep 644831 = 967247) B967247
theorem B4904711 : Blo 338752 4904711 := bstep (se 1 (by rfl) ⟨3678533, by rfl⟩ : syracuseStep 4904711 = 7357067) B7357067
theorem B5592887 : Blo 338752 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B972623 : Blo 338752 972623 := bstep (se 1 (by rfl) ⟨729467, by rfl⟩ : syracuseStep 972623 = 1458935) B1458935
theorem B1267849 : Blo 338752 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B383215 : Blo 338752 383215 := bstep (se 1 (by rfl) ⟨287411, by rfl⟩ : syracuseStep 383215 = 574823) B574823
theorem B1300931 : Blo 338752 1300931 := bstep (se 1 (by rfl) ⟨975698, by rfl⟩ : syracuseStep 1300931 = 1951397) B1951397
theorem B4905683 : Blo 338752 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B1628923 : Blo 338752 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B2776123 : Blo 338752 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B646319 : Blo 338752 646319 := bstep (se 1 (by rfl) ⟨484739, by rfl⟩ : syracuseStep 646319 = 969479) B969479
theorem B2448893 : Blo 338752 2448893 := bstep (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) B918335
theorem B647003 : Blo 338752 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B385519 : Blo 338752 385519 := bstep (se 1 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 385519 = 578279) B578279
theorem B5890697 : Blo 338752 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B4908221 : Blo 338752 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B3500603 : Blo 338752 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B650587 : Blo 338752 650587 := bstep (se 1 (by rfl) ⟨487940, by rfl⟩ : syracuseStep 650587 = 975881) B975881
theorem B486847 : Blo 338752 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B95415803 : Blo 338752 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B42430169 : Blo 338752 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B4157419 : Blo 338752 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B9794753 : Blo 338752 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B2553065 : Blo 338752 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B3700541 : Blo 338752 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B2914177 : Blo 338752 2914177 := bstep (se 2 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 2914177 = 2185633) B2185633
theorem B1734695 : Blo 338752 1734695 := bstep (se 1 (by rfl) ⟨1301021, by rfl⟩ : syracuseStep 1734695 = 2602043) B2602043
theorem B15694117 : Blo 338752 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B2586977 : Blo 338752 2586977 := bstep (se 2 (by rfl) ⟨970116, by rfl⟩ : syracuseStep 2586977 = 1940233) B1940233
theorem B817577 : Blo 338752 817577 := bstep (se 2 (by rfl) ⟨306591, by rfl⟩ : syracuseStep 817577 = 613183) B613183
theorem B1145447 : Blo 338752 1145447 := bstep (se 1 (by rfl) ⟨859085, by rfl⟩ : syracuseStep 1145447 = 1718171) B1718171
theorem B4652185 : Blo 338752 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B818345 : Blo 338752 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B1637995 : Blo 338752 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B2949785 : Blo 338752 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B820535 : Blo 338752 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B12486403 : Blo 338752 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B1837019 : Blo 338752 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B23497391 : Blo 338752 23497391 := bstep (se 1 (by rfl) ⟨17623043, by rfl⟩ : syracuseStep 23497391 = 35246087) B35246087
theorem B920423 : Blo 338752 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B920585 : Blo 338752 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B1149983 : Blo 338752 1149983 := bstep (se 1 (by rfl) ⟨862487, by rfl⟩ : syracuseStep 1149983 = 1724975) B1724975
theorem B429887 : Blo 338752 429887 := bstep (se 1 (by rfl) ⟨322415, by rfl⟩ : syracuseStep 429887 = 644831) B644831
theorem B1086461 : Blo 338752 1086461 := bstep (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) B407423
theorem B431335 : Blo 338752 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B5543225 : Blo 338752 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B1447915 : Blo 338752 1447915 := bstep (se 1 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 1447915 = 2171873) B2171873
theorem B1448239 : Blo 338752 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B3676589 : Blo 338752 3676589 := bstep (se 3 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 3676589 = 1378721) B1378721
theorem B858863 : Blo 338752 858863 := bstep (se 1 (by rfl) ⟨644147, by rfl⟩ : syracuseStep 858863 = 1288295) B1288295
theorem B2333735 : Blo 338752 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B12459545 : Blo 338752 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B63610535 : Blo 338752 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B28286779 : Blo 338752 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B8331275 : Blo 338752 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B762281 : Blo 338752 762281 := bstep (se 2 (by rfl) ⟨285855, by rfl⟩ : syracuseStep 762281 = 571711) B571711
theorem B6529835 : Blo 338752 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B2171897 : Blo 338752 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B1287353 : Blo 338752 1287353 := bstep (se 2 (by rfl) ⟨482757, by rfl⟩ : syracuseStep 1287353 = 965515) B965515
theorem B2467027 : Blo 338752 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B1844477 : Blo 338752 1844477 := bstep (se 3 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 1844477 = 691679) B691679
theorem B6530381 : Blo 338752 6530381 := bstep (se 3 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 6530381 = 2448893) B2448893
theorem B1156463 : Blo 338752 1156463 := bstep (se 1 (by rfl) ⟨867347, by rfl⟩ : syracuseStep 1156463 = 1734695) B1734695
theorem B6202913 : Blo 338752 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B763631 : Blo 338752 763631 := bstep (se 1 (by rfl) ⟨572723, by rfl⟩ : syracuseStep 763631 = 1145447) B1145447
theorem B1944425 : Blo 338752 1944425 := bstep (se 2 (by rfl) ⟨729159, by rfl⟩ : syracuseStep 1944425 = 1458319) B1458319
theorem B863399 : Blo 338752 863399 := bstep (se 1 (by rfl) ⟨647549, by rfl⟩ : syracuseStep 863399 = 1295099) B1295099
theorem B339151 : Blo 338752 339151 := bstep (se 1 (by rfl) ⟨254363, by rfl⟩ : syracuseStep 339151 = 508727) B508727
theorem B339263 : Blo 338752 339263 := bstep (se 1 (by rfl) ⟨254447, by rfl⟩ : syracuseStep 339263 = 508895) B508895
theorem B339271 : Blo 338752 339271 := bstep (se 1 (by rfl) ⟨254453, by rfl⟩ : syracuseStep 339271 = 508907) B508907
theorem B6761861 : Blo 338752 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B339439 : Blo 338752 339439 := bstep (se 1 (by rfl) ⟨254579, by rfl⟩ : syracuseStep 339439 = 509159) B509159
theorem B339483 : Blo 338752 339483 := bstep (se 1 (by rfl) ⟨254612, by rfl⟩ : syracuseStep 339483 = 509225) B509225
theorem B863855 : Blo 338752 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B1715903 : Blo 338752 1715903 := bstep (se 1 (by rfl) ⟨1286927, by rfl⟩ : syracuseStep 1715903 = 2573855) B2573855
theorem B1093459 : Blo 338752 1093459 := bstep (se 1 (by rfl) ⟨820094, by rfl⟩ : syracuseStep 1093459 = 1640189) B1640189
theorem B339871 : Blo 338752 339871 := bstep (se 1 (by rfl) ⟨254903, by rfl⟩ : syracuseStep 339871 = 509807) B509807
theorem B2469797 : Blo 338752 2469797 := bstep (se 4 (by rfl) ⟨231543, by rfl⟩ : syracuseStep 2469797 = 463087) B463087
theorem B765935 : Blo 338752 765935 := bstep (se 1 (by rfl) ⟨574451, by rfl⟩ : syracuseStep 765935 = 1148903) B1148903
theorem B339995 : Blo 338752 339995 := bstep (se 1 (by rfl) ⟨254996, by rfl⟩ : syracuseStep 339995 = 509993) B509993
theorem B83701957 : Blo 338752 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B766187 : Blo 338752 766187 := bstep (se 1 (by rfl) ⟨574640, by rfl⟩ : syracuseStep 766187 = 1149281) B1149281
theorem B1945883 : Blo 338752 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B3682721 : Blo 338752 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B1716713 : Blo 338752 1716713 := bstep (se 2 (by rfl) ⟨643767, by rfl⟩ : syracuseStep 1716713 = 1287535) B1287535
theorem B766601 : Blo 338752 766601 := bstep (se 2 (by rfl) ⟨287475, by rfl⟩ : syracuseStep 766601 = 574951) B574951
theorem B340763 : Blo 338752 340763 := bstep (se 1 (by rfl) ⟨255572, by rfl⟩ : syracuseStep 340763 = 511145) B511145
theorem B2896681 : Blo 338752 2896681 := bstep (se 2 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 2896681 = 2172511) B2172511
theorem B340839 : Blo 338752 340839 := bstep (se 1 (by rfl) ⟨255629, by rfl⟩ : syracuseStep 340839 = 511259) B511259
theorem B1750079 : Blo 338752 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B767303 : Blo 338752 767303 := bstep (se 1 (by rfl) ⟨575477, by rfl⟩ : syracuseStep 767303 = 1150955) B1150955
theorem B767483 : Blo 338752 767483 := bstep (se 1 (by rfl) ⟨575612, by rfl⟩ : syracuseStep 767483 = 1151225) B1151225
theorem B866011 : Blo 338752 866011 := bstep (se 1 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 866011 = 1299017) B1299017
theorem B341863 : Blo 338752 341863 := bstep (se 1 (by rfl) ⟨256397, by rfl⟩ : syracuseStep 341863 = 512795) B512795
theorem B342299 : Blo 338752 342299 := bstep (se 1 (by rfl) ⟨256724, by rfl⟩ : syracuseStep 342299 = 513449) B513449
theorem B342335 : Blo 338752 342335 := bstep (se 1 (by rfl) ⟨256751, by rfl⟩ : syracuseStep 342335 = 513503) B513503
theorem B572359 : Blo 338752 572359 := bstep (se 1 (by rfl) ⟨429269, by rfl⟩ : syracuseStep 572359 = 858539) B858539
theorem B867287 : Blo 338752 867287 := bstep (se 1 (by rfl) ⟨650465, by rfl⟩ : syracuseStep 867287 = 1300931) B1300931
theorem B965641 : Blo 338752 965641 := bstep (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) B724231
theorem B867449 : Blo 338752 867449 := bstep (se 2 (by rfl) ⟨325293, by rfl⟩ : syracuseStep 867449 = 650587) B650587
theorem B769211 : Blo 338752 769211 := bstep (se 1 (by rfl) ⟨576908, by rfl⟩ : syracuseStep 769211 = 1153817) B1153817
theorem B965915 : Blo 338752 965915 := bstep (se 1 (by rfl) ⟨724436, by rfl⟩ : syracuseStep 965915 = 1448873) B1448873
theorem B770039 : Blo 338752 770039 := bstep (se 1 (by rfl) ⟨577529, by rfl⟩ : syracuseStep 770039 = 1155059) B1155059
theorem B508319 : Blo 338752 508319 := bstep (se 1 (by rfl) ⟨381239, by rfl⟩ : syracuseStep 508319 = 762479) B762479
theorem B770615 : Blo 338752 770615 := bstep (se 1 (by rfl) ⟨577961, by rfl⟩ : syracuseStep 770615 = 1155923) B1155923
theorem B508799 : Blo 338752 508799 := bstep (se 1 (by rfl) ⟨381599, by rfl⟩ : syracuseStep 508799 = 763199) B763199
theorem B1295311 : Blo 338752 1295311 := bstep (se 1 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 1295311 = 1942967) B1942967
theorem B771155 : Blo 338752 771155 := bstep (se 1 (by rfl) ⟨578366, by rfl⟩ : syracuseStep 771155 = 1156733) B1156733
theorem B1459721 : Blo 338752 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B968375 : Blo 338752 968375 := bstep (se 1 (by rfl) ⟨726281, by rfl⟩ : syracuseStep 968375 = 1452563) B1452563
theorem B509855 : Blo 338752 509855 := bstep (se 1 (by rfl) ⟨382391, by rfl⟩ : syracuseStep 509855 = 764783) B764783
theorem B3262457 : Blo 338752 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B510023 : Blo 338752 510023 := bstep (se 1 (by rfl) ⟨382517, by rfl⟩ : syracuseStep 510023 = 765035) B765035
theorem B1951897 : Blo 338752 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B1886441 : Blo 338752 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B3885569 : Blo 338752 3885569 := bstep (se 2 (by rfl) ⟨1457088, by rfl⟩ : syracuseStep 3885569 = 2914177) B2914177
theorem B1723193 : Blo 338752 1723193 := bstep (se 2 (by rfl) ⟨646197, by rfl⟩ : syracuseStep 1723193 = 1292395) B1292395
theorem B510953 : Blo 338752 510953 := bstep (se 2 (by rfl) ⟨191607, by rfl⟩ : syracuseStep 510953 = 383215) B383215
theorem B1723517 : Blo 338752 1723517 := bstep (se 3 (by rfl) ⟨323159, by rfl⟩ : syracuseStep 1723517 = 646319) B646319
theorem B1232765 : Blo 338752 1232765 := bstep (se 3 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 1232765 = 462287) B462287
theorem B10506341 : Blo 338752 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B1724651 : Blo 338752 1724651 := bstep (se 1 (by rfl) ⟨1293488, by rfl⟩ : syracuseStep 1724651 = 2586977) B2586977
theorem B545051 : Blo 338752 545051 := bstep (se 1 (by rfl) ⟨408788, by rfl⟩ : syracuseStep 545051 = 817577) B817577
theorem B381415 : Blo 338752 381415 := bstep (se 1 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 381415 = 572123) B572123
theorem B971507 : Blo 338752 971507 := bstep (se 1 (by rfl) ⟨728630, by rfl⟩ : syracuseStep 971507 = 1457261) B1457261
theorem B545563 : Blo 338752 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B2183993 : Blo 338752 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B971689 : Blo 338752 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B382063 : Blo 338752 382063 := bstep (se 1 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 382063 = 573095) B573095
theorem B513407 : Blo 338752 513407 := bstep (se 1 (by rfl) ⟨385055, by rfl⟩ : syracuseStep 513407 = 770111) B770111
theorem B1725947 : Blo 338752 1725947 := bstep (se 1 (by rfl) ⟨1294460, by rfl⟩ : syracuseStep 1725947 = 2588921) B2588921
theorem B972395 : Blo 338752 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B1726271 : Blo 338752 1726271 := bstep (se 1 (by rfl) ⟨1294703, by rfl⟩ : syracuseStep 1726271 = 2589407) B2589407
theorem B514025 : Blo 338752 514025 := bstep (se 2 (by rfl) ⟨192759, by rfl⟩ : syracuseStep 514025 = 385519) B385519
theorem B2578715 : Blo 338752 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B645727 : Blo 338752 645727 := bstep (se 1 (by rfl) ⟨484295, by rfl⟩ : syracuseStep 645727 = 968591) B968591
theorem B974207 : Blo 338752 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B385051 : Blo 338752 385051 := bstep (se 1 (by rfl) ⟨288788, by rfl⟩ : syracuseStep 385051 = 577577) B577577
theorem B1171751 : Blo 338752 1171751 := bstep (se 1 (by rfl) ⟨878813, by rfl⟩ : syracuseStep 1171751 = 1757627) B1757627
theorem B8446519 : Blo 338752 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B3859325 : Blo 338752 3859325 := bstep (se 3 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 3859325 = 1447247) B1447247
theorem B3269807 : Blo 338752 3269807 := bstep (se 1 (by rfl) ⟨2452355, by rfl⟩ : syracuseStep 3269807 = 4904711) B4904711
theorem B3728591 : Blo 338752 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B648415 : Blo 338752 648415 := bstep (se 1 (by rfl) ⟨486311, by rfl⟩ : syracuseStep 648415 = 972623) B972623
theorem B877871 : Blo 338752 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B1730159 : Blo 338752 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B3270455 : Blo 338752 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B616319 : Blo 338752 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B649129 : Blo 338752 649129 := bstep (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) B486847
theorem B2583089 : Blo 338752 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B486175 : Blo 338752 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B3927131 : Blo 338752 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B814175 : Blo 338752 814175 := bstep (se 1 (by rfl) ⟨610631, by rfl⟩ : syracuseStep 814175 = 1221263) B1221263
theorem B7367867 : Blo 338752 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B3272147 : Blo 338752 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B1733399 : Blo 338752 1733399 := bstep (se 1 (by rfl) ⟨1300049, by rfl⟩ : syracuseStep 1733399 = 2600099) B2600099
theorem B3470161 : Blo 338752 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B1702043 : Blo 338752 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B1932011 : Blo 338752 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B3701497 : Blo 338752 3701497 := bstep (se 2 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 3701497 = 2776123) B2776123
theorem B1966523 : Blo 338752 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B2590379 : Blo 338752 2590379 := bstep (se 1 (by rfl) ⟨1942784, by rfl⟩ : syracuseStep 2590379 = 3885569) B3885569
theorem B15664927 : Blo 338752 15664927 := bstep (se 1 (by rfl) ⟨11748695, by rfl⟩ : syracuseStep 15664927 = 23497391) B23497391
theorem B1148795 : Blo 338752 1148795 := bstep (se 1 (by rfl) ⟨861596, by rfl⟩ : syracuseStep 1148795 = 1723193) B1723193
theorem B1149011 : Blo 338752 1149011 := bstep (se 1 (by rfl) ⟨861758, by rfl⟩ : syracuseStep 1149011 = 1723517) B1723517
theorem B16648537 : Blo 338752 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B20122037 : Blo 338752 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B821843 : Blo 338752 821843 := bstep (se 1 (by rfl) ⟨616382, by rfl⟩ : syracuseStep 821843 = 1232765) B1232765
theorem B1149767 : Blo 338752 1149767 := bstep (se 1 (by rfl) ⟨862325, by rfl⟩ : syracuseStep 1149767 = 1724651) B1724651
theorem B363367 : Blo 338752 363367 := bstep (se 1 (by rfl) ⟨272525, by rfl⟩ : syracuseStep 363367 = 545051) B545051
theorem B8752373 : Blo 338752 8752373 := bstep (se 5 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 8752373 = 820535) B820535
theorem B724307 : Blo 338752 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B1150631 : Blo 338752 1150631 := bstep (se 1 (by rfl) ⟨862973, by rfl⟩ : syracuseStep 1150631 = 1725947) B1725947
theorem B1150847 : Blo 338752 1150847 := bstep (se 1 (by rfl) ⟨863135, by rfl⟩ : syracuseStep 1150847 = 1726271) B1726271
theorem B42407023 : Blo 338752 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B1447931 : Blo 338752 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B858235 : Blo 338752 858235 := bstep (se 1 (by rfl) ⟨643676, by rfl⟩ : syracuseStep 858235 = 1287353) B1287353
theorem B727417 : Blo 338752 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B1153439 : Blo 338752 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B4626881 : Blo 338752 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B1154681 : Blo 338752 1154681 := bstep (se 2 (by rfl) ⟨433005, by rfl⟩ : syracuseStep 1154681 = 866011) B866011
theorem B1646531 : Blo 338752 1646531 := bstep (se 1 (by rfl) ⟨1234898, by rfl⟩ : syracuseStep 1646531 = 2469797) B2469797
theorem B1155599 : Blo 338752 1155599 := bstep (se 1 (by rfl) ⟨866699, by rfl⟩ : syracuseStep 1155599 = 1733399) B1733399
theorem B860969 : Blo 338752 860969 := bstep (se 2 (by rfl) ⟨322863, by rfl⟩ : syracuseStep 860969 = 645727) B645727
theorem B763145 : Blo 338752 763145 := bstep (se 2 (by rfl) ⟨286179, by rfl⟩ : syracuseStep 763145 = 572359) B572359
theorem B1287521 : Blo 338752 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B1288007 : Blo 338752 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B338879 : Blo 338752 338879 := bstep (se 1 (by rfl) ⟨254159, by rfl⟩ : syracuseStep 338879 = 508319) B508319
theorem B339199 : Blo 338752 339199 := bstep (se 1 (by rfl) ⟨254399, by rfl⟩ : syracuseStep 339199 = 508799) B508799
theorem B3124669 : Blo 338752 3124669 := bstep (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) B1171751
theorem B339903 : Blo 338752 339903 := bstep (se 1 (by rfl) ⟨254927, by rfl⟩ : syracuseStep 339903 = 509855) B509855
theorem B1224679 : Blo 338752 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B340015 : Blo 338752 340015 := bstep (se 1 (by rfl) ⟨255011, by rfl⟩ : syracuseStep 340015 = 510023) B510023
theorem B3289369 : Blo 338752 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B864553 : Blo 338752 864553 := bstep (se 2 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 864553 = 648415) B648415
theorem B340635 : Blo 338752 340635 := bstep (se 1 (by rfl) ⟨255476, by rfl⟩ : syracuseStep 340635 = 510953) B510953
theorem B766655 : Blo 338752 766655 := bstep (se 1 (by rfl) ⟨574991, by rfl⟩ : syracuseStep 766655 = 1149983) B1149983
theorem B865505 : Blo 338752 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B2602529 : Blo 338752 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B1455995 : Blo 338752 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B342271 : Blo 338752 342271 := bstep (se 1 (by rfl) ⟨256703, by rfl⟩ : syracuseStep 342271 = 513407) B513407
theorem B342683 : Blo 338752 342683 := bstep (se 1 (by rfl) ⟨257012, by rfl⟩ : syracuseStep 342683 = 514025) B514025
theorem B1719143 : Blo 338752 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B572575 : Blo 338752 572575 := bstep (se 1 (by rfl) ⟨429431, by rfl⟩ : syracuseStep 572575 = 858863) B858863
theorem B1555823 : Blo 338752 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B8306363 : Blo 338752 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B1457945 : Blo 338752 1457945 := bstep (se 2 (by rfl) ⟨546729, by rfl⟩ : syracuseStep 1457945 = 1093459) B1093459
theorem B8699885 : Blo 338752 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B5554183 : Blo 338752 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B508187 : Blo 338752 508187 := bstep (se 1 (by rfl) ⟨381140, by rfl⟩ : syracuseStep 508187 = 762281) B762281
theorem B2572883 : Blo 338752 2572883 := bstep (se 1 (by rfl) ⟨1929662, by rfl⟩ : syracuseStep 2572883 = 3859325) B3859325
theorem B508553 : Blo 338752 508553 := bstep (se 2 (by rfl) ⟨190707, by rfl⟩ : syracuseStep 508553 = 381415) B381415
theorem B2179871 : Blo 338752 2179871 := bstep (se 1 (by rfl) ⟨1634903, by rfl⟩ : syracuseStep 2179871 = 3269807) B3269807
theorem B1229651 : Blo 338752 1229651 := bstep (se 1 (by rfl) ⟨922238, by rfl⟩ : syracuseStep 1229651 = 1844477) B1844477
theorem B770975 : Blo 338752 770975 := bstep (se 1 (by rfl) ⟨578231, by rfl⟩ : syracuseStep 770975 = 1156463) B1156463
theorem B509087 : Blo 338752 509087 := bstep (se 1 (by rfl) ⟨381815, by rfl⟩ : syracuseStep 509087 = 763631) B763631
theorem B2180303 : Blo 338752 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B1295585 : Blo 338752 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B410879 : Blo 338752 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B509417 : Blo 338752 509417 := bstep (se 2 (by rfl) ⟨191031, by rfl⟩ : syracuseStep 509417 = 382063) B382063
theorem B575113 : Blo 338752 575113 := bstep (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) B431335
theorem B1722059 : Blo 338752 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B1296283 : Blo 338752 1296283 := bstep (se 1 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 1296283 = 1944425) B1944425
theorem B542783 : Blo 338752 542783 := bstep (se 1 (by rfl) ⟨407087, by rfl⟩ : syracuseStep 542783 = 814175) B814175
theorem B575599 : Blo 338752 575599 := bstep (se 1 (by rfl) ⟨431699, by rfl⟩ : syracuseStep 575599 = 863399) B863399
theorem B4507907 : Blo 338752 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B2181431 : Blo 338752 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B575903 : Blo 338752 575903 := bstep (se 1 (by rfl) ⟨431927, by rfl⟩ : syracuseStep 575903 = 863855) B863855
theorem B510623 : Blo 338752 510623 := bstep (se 1 (by rfl) ⟨382967, by rfl⟩ : syracuseStep 510623 = 765935) B765935
theorem B510791 : Blo 338752 510791 := bstep (se 1 (by rfl) ⟨383093, by rfl⟩ : syracuseStep 510791 = 766187) B766187
theorem B1297255 : Blo 338752 1297255 := bstep (se 1 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 1297255 = 1945883) B1945883
theorem B511067 : Blo 338752 511067 := bstep (se 1 (by rfl) ⟨383300, by rfl⟩ : syracuseStep 511067 = 766601) B766601
theorem B1166719 : Blo 338752 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B511535 : Blo 338752 511535 := bstep (se 1 (by rfl) ⟨383651, by rfl⟩ : syracuseStep 511535 = 767303) B767303
theorem B4935329 : Blo 338752 4935329 := bstep (se 2 (by rfl) ⟨1850748, by rfl⟩ : syracuseStep 4935329 = 3701497) B3701497
theorem B511655 : Blo 338752 511655 := bstep (se 1 (by rfl) ⟨383741, by rfl⟩ : syracuseStep 511655 = 767483) B767483
theorem B1134695 : Blo 338752 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B578191 : Blo 338752 578191 := bstep (se 1 (by rfl) ⟨433643, by rfl⟩ : syracuseStep 578191 = 867287) B867287
theorem B578299 : Blo 338752 578299 := bstep (se 1 (by rfl) ⟨433724, by rfl⟩ : syracuseStep 578299 = 867449) B867449
theorem B512807 : Blo 338752 512807 := bstep (se 1 (by rfl) ⟨384605, by rfl⟩ : syracuseStep 512807 = 769211) B769211
theorem B643943 : Blo 338752 643943 := bstep (se 1 (by rfl) ⟨482957, by rfl⟩ : syracuseStep 643943 = 965915) B965915
theorem B513359 : Blo 338752 513359 := bstep (se 1 (by rfl) ⟨385019, by rfl⟩ : syracuseStep 513359 = 770039) B770039
theorem B513401 : Blo 338752 513401 := bstep (se 2 (by rfl) ⟨192525, by rfl⟩ : syracuseStep 513401 = 385051) B385051
theorem B513743 : Blo 338752 513743 := bstep (se 1 (by rfl) ⟨385307, by rfl⟩ : syracuseStep 513743 = 770615) B770615
theorem B514103 : Blo 338752 514103 := bstep (se 1 (by rfl) ⟨385577, by rfl⟩ : syracuseStep 514103 = 771155) B771155
theorem B11262025 : Blo 338752 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B973147 : Blo 338752 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B645583 : Blo 338752 645583 := bstep (se 1 (by rfl) ⟨484187, by rfl⟩ : syracuseStep 645583 = 968375) B968375
theorem B1727081 : Blo 338752 1727081 := bstep (se 2 (by rfl) ⟨647655, by rfl⟩ : syracuseStep 1727081 = 1295311) B1295311
theorem B613615 : Blo 338752 613615 := bstep (se 1 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 613615 = 920423) B920423
theorem B7004227 : Blo 338752 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B647671 : Blo 338752 647671 := bstep (se 1 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 647671 = 971507) B971507
theorem B3695483 : Blo 338752 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B648233 : Blo 338752 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B648263 : Blo 338752 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B16541101 : Blo 338752 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B2451059 : Blo 338752 2451059 := bstep (se 1 (by rfl) ⟨1838294, by rfl⟩ : syracuseStep 2451059 = 3676589) B3676589
theorem B649471 : Blo 338752 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B111602609 : Blo 338752 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B4353223 : Blo 338752 4353223 := bstep (se 1 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 4353223 = 6529835) B6529835
theorem B2485727 : Blo 338752 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B585247 : Blo 338752 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B4353587 : Blo 338752 4353587 := bstep (se 1 (by rfl) ⟨3265190, by rfl⟩ : syracuseStep 4353587 = 6530381) B6530381
theorem B3862241 : Blo 338752 3862241 := bstep (se 2 (by rfl) ⟨1448340, by rfl⟩ : syracuseStep 3862241 = 2896681) B2896681
theorem B2618087 : Blo 338752 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B4911911 : Blo 338752 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B1143935 : Blo 338752 1143935 := bstep (se 1 (by rfl) ⟨857951, by rfl⟩ : syracuseStep 1143935 = 1715903) B1715903
theorem B1930553 : Blo 338752 1930553 := bstep (se 2 (by rfl) ⟨723957, by rfl⟩ : syracuseStep 1930553 = 1447915) B1447915
theorem B2454893 : Blo 338752 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B2455147 : Blo 338752 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B1144475 : Blo 338752 1144475 := bstep (se 1 (by rfl) ⟨858356, by rfl⟩ : syracuseStep 1144475 = 1716713) B1716713
theorem B1930985 : Blo 338752 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B1146365 : Blo 338752 1146365 := bstep (se 3 (by rfl) ⟨214943, by rfl⟩ : syracuseStep 1146365 = 429887) B429887
theorem B37715705 : Blo 338752 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B7405577 : Blo 338752 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B9338969 : Blo 338752 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B819767 : Blo 338752 819767 := bstep (se 1 (by rfl) ⟨614825, by rfl⟩ : syracuseStep 819767 = 1229651) B1229651
theorem B1148039 : Blo 338752 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B5244061 : Blo 338752 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B361855 : Blo 338752 361855 := bstep (se 1 (by rfl) ⟨271391, by rfl⟩ : syracuseStep 361855 = 542783) B542783
theorem B22054801 : Blo 338752 22054801 := bstep (se 2 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 22054801 = 16541101) B16541101
theorem B6981565 : Blo 338752 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B5834915 : Blo 338752 5834915 := bstep (se 1 (by rfl) ⟨4376186, by rfl⟩ : syracuseStep 5834915 = 8752373) B8752373
theorem B756463 : Blo 338752 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B429295 : Blo 338752 429295 := bstep (se 1 (by rfl) ⟨321971, by rfl⟩ : syracuseStep 429295 = 643943) B643943
theorem B5804297 : Blo 338752 5804297 := bstep (se 2 (by rfl) ⟨2176611, by rfl⟩ : syracuseStep 5804297 = 4353223) B4353223
theorem B3084587 : Blo 338752 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B1151387 : Blo 338752 1151387 := bstep (se 1 (by rfl) ⟨863540, by rfl⟩ : syracuseStep 1151387 = 1727081) B1727081
theorem B4166225 : Blo 338752 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B1152737 : Blo 338752 1152737 := bstep (se 2 (by rfl) ⟨432276, by rfl⟩ : syracuseStep 1152737 = 864553) B864553
theorem B432155 : Blo 338752 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B858347 : Blo 338752 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B858671 : Blo 338752 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B15016033 : Blo 338752 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B860777 : Blo 338752 860777 := bstep (se 2 (by rfl) ⟨322791, by rfl⟩ : syracuseStep 860777 = 645583) B645583
theorem B762623 : Blo 338752 762623 := bstep (se 1 (by rfl) ⟨571967, by rfl⟩ : syracuseStep 762623 = 1143935) B1143935
theorem B1287035 : Blo 338752 1287035 := bstep (se 1 (by rfl) ⟨965276, by rfl⟩ : syracuseStep 1287035 = 1930553) B1930553
theorem B762983 : Blo 338752 762983 := bstep (se 1 (by rfl) ⟨572237, by rfl⟩ : syracuseStep 762983 = 1144475) B1144475
theorem B1287323 : Blo 338752 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B763433 : Blo 338752 763433 := bstep (se 2 (by rfl) ⟨286287, by rfl⟩ : syracuseStep 763433 = 572575) B572575
theorem B764243 : Blo 338752 764243 := bstep (se 1 (by rfl) ⟨573182, by rfl⟩ : syracuseStep 764243 = 1146365) B1146365
theorem B25143803 : Blo 338752 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B338791 : Blo 338752 338791 := bstep (se 1 (by rfl) ⟨254093, by rfl⟩ : syracuseStep 338791 = 508187) B508187
theorem B1715255 : Blo 338752 1715255 := bstep (se 1 (by rfl) ⟨1286441, by rfl⟩ : syracuseStep 1715255 = 2572883) B2572883
theorem B339035 : Blo 338752 339035 := bstep (se 1 (by rfl) ⟨254276, by rfl⟩ : syracuseStep 339035 = 508553) B508553
theorem B1453247 : Blo 338752 1453247 := bstep (se 1 (by rfl) ⟨1089935, by rfl⟩ : syracuseStep 1453247 = 2179871) B2179871
theorem B863561 : Blo 338752 863561 := bstep (se 2 (by rfl) ⟨323835, by rfl⟩ : syracuseStep 863561 = 647671) B647671
theorem B339391 : Blo 338752 339391 := bstep (se 1 (by rfl) ⟨254543, by rfl⟩ : syracuseStep 339391 = 509087) B509087
theorem B1453535 : Blo 338752 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B863723 : Blo 338752 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B339611 : Blo 338752 339611 := bstep (se 1 (by rfl) ⟨254708, by rfl⟩ : syracuseStep 339611 = 509417) B509417
theorem B765863 : Blo 338752 765863 := bstep (se 1 (by rfl) ⟨574397, by rfl⟩ : syracuseStep 765863 = 1148795) B1148795
theorem B766007 : Blo 338752 766007 := bstep (se 1 (by rfl) ⟨574505, by rfl⟩ : syracuseStep 766007 = 1149011) B1149011
theorem B1454287 : Blo 338752 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B13414691 : Blo 338752 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B340415 : Blo 338752 340415 := bstep (se 1 (by rfl) ⟨255311, by rfl⟩ : syracuseStep 340415 = 510623) B510623
theorem B340527 : Blo 338752 340527 := bstep (se 1 (by rfl) ⟨255395, by rfl⟩ : syracuseStep 340527 = 510791) B510791
theorem B766511 : Blo 338752 766511 := bstep (se 1 (by rfl) ⟨574883, by rfl⟩ : syracuseStep 766511 = 1149767) B1149767
theorem B340711 : Blo 338752 340711 := bstep (se 1 (by rfl) ⟨255533, by rfl⟩ : syracuseStep 340711 = 511067) B511067
theorem B766817 : Blo 338752 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B341023 : Blo 338752 341023 := bstep (se 1 (by rfl) ⟨255767, by rfl⟩ : syracuseStep 341023 = 511535) B511535
theorem B20886569 : Blo 338752 20886569 := bstep (se 2 (by rfl) ⟨7832463, by rfl⟩ : syracuseStep 20886569 = 15664927) B15664927
theorem B3290219 : Blo 338752 3290219 := bstep (se 1 (by rfl) ⟨2467664, by rfl⟩ : syracuseStep 3290219 = 4935329) B4935329
theorem B767087 : Blo 338752 767087 := bstep (se 1 (by rfl) ⟨575315, by rfl⟩ : syracuseStep 767087 = 1150631) B1150631
theorem B341103 : Blo 338752 341103 := bstep (se 1 (by rfl) ⟨255827, by rfl⟩ : syracuseStep 341103 = 511655) B511655
theorem B767231 : Blo 338752 767231 := bstep (se 1 (by rfl) ⟨575423, by rfl⟩ : syracuseStep 767231 = 1150847) B1150847
theorem B767465 : Blo 338752 767465 := bstep (se 2 (by rfl) ⟨287799, by rfl⟩ : syracuseStep 767465 = 575599) B575599
theorem B865961 : Blo 338752 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B22198049 : Blo 338752 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B341871 : Blo 338752 341871 := bstep (se 1 (by rfl) ⟨256403, by rfl⟩ : syracuseStep 341871 = 512807) B512807
theorem B1095677 : Blo 338752 1095677 := bstep (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) B410879
theorem B342239 : Blo 338752 342239 := bstep (se 1 (by rfl) ⟨256679, by rfl⟩ : syracuseStep 342239 = 513359) B513359
theorem B342267 : Blo 338752 342267 := bstep (se 1 (by rfl) ⟨256700, by rfl⟩ : syracuseStep 342267 = 513401) B513401
theorem B342495 : Blo 338752 342495 := bstep (se 1 (by rfl) ⟨256871, by rfl⟩ : syracuseStep 342495 = 513743) B513743
theorem B965287 : Blo 338752 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B342735 : Blo 338752 342735 := bstep (se 1 (by rfl) ⟨257051, by rfl⟩ : syracuseStep 342735 = 514103) B514103
theorem B768959 : Blo 338752 768959 := bstep (se 1 (by rfl) ⟨576719, by rfl⟩ : syracuseStep 768959 = 1153439) B1153439
theorem B1555625 : Blo 338752 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B3882653 : Blo 338752 3882653 := bstep (se 3 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 3882653 = 1455995) B1455995
theorem B769787 : Blo 338752 769787 := bstep (se 1 (by rfl) ⟨577340, by rfl⟩ : syracuseStep 769787 = 1154681) B1154681
theorem B1097687 : Blo 338752 1097687 := bstep (se 1 (by rfl) ⟨823265, by rfl⟩ : syracuseStep 1097687 = 1646531) B1646531
theorem B770399 : Blo 338752 770399 := bstep (se 1 (by rfl) ⟨577799, by rfl⟩ : syracuseStep 770399 = 1155599) B1155599
theorem B573979 : Blo 338752 573979 := bstep (se 1 (by rfl) ⟨430484, by rfl⟩ : syracuseStep 573979 = 860969) B860969
theorem B508763 : Blo 338752 508763 := bstep (se 1 (by rfl) ⟨381572, by rfl⟩ : syracuseStep 508763 = 763145) B763145
theorem B770921 : Blo 338752 770921 := bstep (se 2 (by rfl) ⟨289095, by rfl⟩ : syracuseStep 770921 = 578191) B578191
theorem B771065 : Blo 338752 771065 := bstep (se 2 (by rfl) ⟨289149, by rfl⟩ : syracuseStep 771065 = 578299) B578299
theorem B56542697 : Blo 338752 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B74401739 : Blo 338752 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B1657151 : Blo 338752 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B2902391 : Blo 338752 2902391 := bstep (se 1 (by rfl) ⟨2176793, by rfl⟩ : syracuseStep 2902391 = 4353587) B4353587
theorem B2574827 : Blo 338752 2574827 := bstep (se 1 (by rfl) ⟨1931120, by rfl⟩ : syracuseStep 2574827 = 3862241) B3862241
theorem B1297529 : Blo 338752 1297529 := bstep (se 2 (by rfl) ⟨486573, by rfl⟩ : syracuseStep 1297529 = 973147) B973147
theorem B511103 : Blo 338752 511103 := bstep (se 1 (by rfl) ⟨383327, by rfl⟩ : syracuseStep 511103 = 766655) B766655
theorem B969889 : Blo 338752 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B577003 : Blo 338752 577003 := bstep (se 1 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 577003 = 865505) B865505
theorem B1037215 : Blo 338752 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B971963 : Blo 338752 971963 := bstep (se 1 (by rfl) ⟨728972, by rfl⟩ : syracuseStep 971963 = 1457945) B1457945
theorem B513983 : Blo 338752 513983 := bstep (se 1 (by rfl) ⟨385487, by rfl⟩ : syracuseStep 513983 = 770975) B770975
theorem B1726919 : Blo 338752 1726919 := bstep (se 1 (by rfl) ⟨1295189, by rfl⟩ : syracuseStep 1726919 = 2590379) B2590379
theorem B383935 : Blo 338752 383935 := bstep (se 1 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 383935 = 575903) B575903
theorem B547895 : Blo 338752 547895 := bstep (se 1 (by rfl) ⟨410921, by rfl⟩ : syracuseStep 547895 = 821843) B821843
theorem B9854621 : Blo 338752 9854621 := bstep (se 3 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 9854621 = 3695483) B3695483
theorem B1728377 : Blo 338752 1728377 := bstep (se 2 (by rfl) ⟨648141, by rfl⟩ : syracuseStep 1728377 = 1296283) B1296283
theorem B1728701 : Blo 338752 1728701 := bstep (se 3 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 1728701 = 648263) B648263
theorem B484489 : Blo 338752 484489 := bstep (se 2 (by rfl) ⟨181683, by rfl⟩ : syracuseStep 484489 = 363367) B363367
theorem B1729673 : Blo 338752 1729673 := bstep (se 2 (by rfl) ⟨648627, by rfl⟩ : syracuseStep 1729673 = 1297255) B1297255
theorem B780329 : Blo 338752 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B1632905 : Blo 338752 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B4385825 : Blo 338752 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B12021085 : Blo 338752 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B1634039 : Blo 338752 1634039 := bstep (se 1 (by rfl) ⟨1225529, by rfl⟩ : syracuseStep 1634039 = 2451059) B2451059
theorem B3273529 : Blo 338752 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B1144313 : Blo 338752 1144313 := bstep (se 2 (by rfl) ⟨429117, by rfl⟩ : syracuseStep 1144313 = 858235) B858235
theorem B3274607 : Blo 338752 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B1931485 : Blo 338752 1931485 := bstep (se 3 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 1931485 = 724307) B724307
theorem B1636595 : Blo 338752 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B1735019 : Blo 338752 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B818153 : Blo 338752 818153 := bstep (se 2 (by rfl) ⟨306807, by rfl⟩ : syracuseStep 818153 = 613615) B613615
theorem B1146095 : Blo 338752 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B5537575 : Blo 338752 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B5799923 : Blo 338752 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B6225979 : Blo 338752 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B20021377 : Blo 338752 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B1934927 : Blo 338752 1934927 := bstep (se 1 (by rfl) ⟨1451195, by rfl⟩ : syracuseStep 1934927 = 2902391) B2902391
theorem B9308753 : Blo 338752 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B3869531 : Blo 338752 3869531 := bstep (se 1 (by rfl) ⟨2902148, by rfl⟩ : syracuseStep 3869531 = 5804297) B5804297
theorem B1151279 : Blo 338752 1151279 := bstep (se 1 (by rfl) ⟨863459, by rfl⟩ : syracuseStep 1151279 = 1726919) B1726919
theorem B16028113 : Blo 338752 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B1152251 : Blo 338752 1152251 := bstep (se 1 (by rfl) ⟨864188, by rfl⟩ : syracuseStep 1152251 = 1728377) B1728377
theorem B1152413 : Blo 338752 1152413 := bstep (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) B432155
theorem B1152467 : Blo 338752 1152467 := bstep (se 1 (by rfl) ⟨864350, by rfl⟩ : syracuseStep 1152467 = 1728701) B1728701
theorem B1939049 : Blo 338752 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B858023 : Blo 338752 858023 := bstep (se 1 (by rfl) ⟨643517, by rfl⟩ : syracuseStep 858023 = 1287035) B1287035
theorem B1153115 : Blo 338752 1153115 := bstep (se 1 (by rfl) ⟨864836, by rfl⟩ : syracuseStep 1153115 = 1729673) B1729673
theorem B858215 : Blo 338752 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B4364705 : Blo 338752 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B1088603 : Blo 338752 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B2923883 : Blo 338752 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B1089359 : Blo 338752 1089359 := bstep (se 1 (by rfl) ⟨817019, by rfl⟩ : syracuseStep 1089359 = 1634039) B1634039
theorem B1287049 : Blo 338752 1287049 := bstep (se 2 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 1287049 = 965287) B965287
theorem B762875 : Blo 338752 762875 := bstep (se 1 (by rfl) ⟨572156, by rfl⟩ : syracuseStep 762875 = 1144313) B1144313
theorem B730451 : Blo 338752 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B1091063 : Blo 338752 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B1156679 : Blo 338752 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B764063 : Blo 338752 764063 := bstep (se 1 (by rfl) ⟨573047, by rfl⟩ : syracuseStep 764063 = 1146095) B1146095
theorem B7383433 : Blo 338752 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B731791 : Blo 338752 731791 := bstep (se 1 (by rfl) ⟨548843, by rfl⟩ : syracuseStep 731791 = 1097687) B1097687
theorem B339175 : Blo 338752 339175 := bstep (se 1 (by rfl) ⟨254381, by rfl⟩ : syracuseStep 339175 = 508763) B508763
theorem B765305 : Blo 338752 765305 := bstep (se 2 (by rfl) ⟨286989, by rfl⟩ : syracuseStep 765305 = 573979) B573979
theorem B765359 : Blo 338752 765359 := bstep (se 1 (by rfl) ⟨574019, by rfl⟩ : syracuseStep 765359 = 1148039) B1148039
theorem B37695131 : Blo 338752 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B6992081 : Blo 338752 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B1716551 : Blo 338752 1716551 := bstep (se 1 (by rfl) ⟨1287413, by rfl⟩ : syracuseStep 1716551 = 2574827) B2574827
theorem B865019 : Blo 338752 865019 := bstep (se 1 (by rfl) ⟨648764, by rfl⟩ : syracuseStep 865019 = 1297529) B1297529
theorem B340735 : Blo 338752 340735 := bstep (se 1 (by rfl) ⟨255551, by rfl⟩ : syracuseStep 340735 = 511103) B511103
theorem B29406401 : Blo 338752 29406401 := bstep (se 2 (by rfl) ⟨11027400, by rfl⟩ : syracuseStep 29406401 = 22054801) B22054801
theorem B767591 : Blo 338752 767591 := bstep (se 1 (by rfl) ⟨575693, by rfl⟩ : syracuseStep 767591 = 1151387) B1151387
theorem B768491 : Blo 338752 768491 := bstep (se 1 (by rfl) ⟨576368, by rfl⟩ : syracuseStep 768491 = 1152737) B1152737
theorem B342655 : Blo 338752 342655 := bstep (se 1 (by rfl) ⟨256991, by rfl⟩ : syracuseStep 342655 = 513983) B513983
theorem B572231 : Blo 338752 572231 := bstep (se 1 (by rfl) ⟨429173, by rfl⟩ : syracuseStep 572231 = 858347) B858347
theorem B1293185 : Blo 338752 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B572393 : Blo 338752 572393 := bstep (se 2 (by rfl) ⟨214647, by rfl⟩ : syracuseStep 572393 = 429295) B429295
theorem B572447 : Blo 338752 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B769337 : Blo 338752 769337 := bstep (se 2 (by rfl) ⟨288501, by rfl⟩ : syracuseStep 769337 = 577003) B577003
theorem B6569747 : Blo 338752 6569747 := bstep (se 1 (by rfl) ⟨4927310, by rfl⟩ : syracuseStep 6569747 = 9854621) B9854621
theorem B573851 : Blo 338752 573851 := bstep (se 1 (by rfl) ⟨430388, by rfl⟩ : syracuseStep 573851 = 860777) B860777
theorem B508415 : Blo 338752 508415 := bstep (se 1 (by rfl) ⟨381311, by rfl⟩ : syracuseStep 508415 = 762623) B762623
theorem B508655 : Blo 338752 508655 := bstep (se 1 (by rfl) ⟨381491, by rfl⟩ : syracuseStep 508655 = 762983) B762983
theorem B508955 : Blo 338752 508955 := bstep (se 1 (by rfl) ⟨381716, by rfl⟩ : syracuseStep 508955 = 763433) B763433
theorem B509495 : Blo 338752 509495 := bstep (se 1 (by rfl) ⟨382121, by rfl⟩ : syracuseStep 509495 = 764243) B764243
theorem B16762535 : Blo 338752 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B968831 : Blo 338752 968831 := bstep (se 1 (by rfl) ⟨726623, by rfl⟩ : syracuseStep 968831 = 1453247) B1453247
theorem B575707 : Blo 338752 575707 := bstep (se 1 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 575707 = 863561) B863561
theorem B969023 : Blo 338752 969023 := bstep (se 1 (by rfl) ⟨726767, by rfl⟩ : syracuseStep 969023 = 1453535) B1453535
theorem B575815 : Blo 338752 575815 := bstep (se 1 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 575815 = 863723) B863723
theorem B510575 : Blo 338752 510575 := bstep (se 1 (by rfl) ⟨382931, by rfl⟩ : syracuseStep 510575 = 765863) B765863
theorem B510671 : Blo 338752 510671 := bstep (se 1 (by rfl) ⟨383003, by rfl⟩ : syracuseStep 510671 = 766007) B766007
theorem B1461053 : Blo 338752 1461053 := bstep (se 3 (by rfl) ⟨273947, by rfl⟩ : syracuseStep 1461053 = 547895) B547895
theorem B2575313 : Blo 338752 2575313 := bstep (se 2 (by rfl) ⟨965742, by rfl⟩ : syracuseStep 2575313 = 1931485) B1931485
theorem B511007 : Blo 338752 511007 := bstep (se 1 (by rfl) ⟨383255, by rfl⟩ : syracuseStep 511007 = 766511) B766511
theorem B511211 : Blo 338752 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B511391 : Blo 338752 511391 := bstep (se 1 (by rfl) ⟨383543, by rfl⟩ : syracuseStep 511391 = 767087) B767087
theorem B511487 : Blo 338752 511487 := bstep (se 1 (by rfl) ⟨383615, by rfl⟩ : syracuseStep 511487 = 767231) B767231
theorem B511643 : Blo 338752 511643 := bstep (se 1 (by rfl) ⟨383732, by rfl⟩ : syracuseStep 511643 = 767465) B767465
theorem B577307 : Blo 338752 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B14798699 : Blo 338752 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B2183071 : Blo 338752 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B511913 : Blo 338752 511913 := bstep (se 2 (by rfl) ⟨191967, by rfl⟩ : syracuseStep 511913 = 383935) B383935
theorem B512639 : Blo 338752 512639 := bstep (se 1 (by rfl) ⟨384479, by rfl⟩ : syracuseStep 512639 = 768959) B768959
theorem B545435 : Blo 338752 545435 := bstep (se 1 (by rfl) ⟨409076, by rfl⟩ : syracuseStep 545435 = 818153) B818153
theorem B1037083 : Blo 338752 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B513191 : Blo 338752 513191 := bstep (se 1 (by rfl) ⟨384893, by rfl⟩ : syracuseStep 513191 = 769787) B769787
theorem B4937051 : Blo 338752 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B513599 : Blo 338752 513599 := bstep (se 1 (by rfl) ⟨385199, by rfl⟩ : syracuseStep 513599 = 770399) B770399
theorem B546511 : Blo 338752 546511 := bstep (se 1 (by rfl) ⟨409883, by rfl⟩ : syracuseStep 546511 = 819767) B819767
theorem B513947 : Blo 338752 513947 := bstep (se 1 (by rfl) ⟨385460, by rfl⟩ : syracuseStep 513947 = 770921) B770921
theorem B514043 : Blo 338752 514043 := bstep (se 1 (by rfl) ⟨385532, by rfl⟩ : syracuseStep 514043 = 771065) B771065
theorem B35772509 : Blo 338752 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B49601159 : Blo 338752 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B3889943 : Blo 338752 3889943 := bstep (se 1 (by rfl) ⟨2917457, by rfl⟩ : syracuseStep 3889943 = 5834915) B5834915
theorem B645985 : Blo 338752 645985 := bstep (se 2 (by rfl) ⟨242244, by rfl⟩ : syracuseStep 645985 = 484489) B484489
theorem B1104767 : Blo 338752 1104767 := bstep (se 1 (by rfl) ⟨828575, by rfl⟩ : syracuseStep 1104767 = 1657151) B1657151
theorem B482473 : Blo 338752 482473 := bstep (se 2 (by rfl) ⟨180927, by rfl⟩ : syracuseStep 482473 = 361855) B361855
theorem B2056391 : Blo 338752 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B2777483 : Blo 338752 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B647975 : Blo 338752 647975 := bstep (se 1 (by rfl) ⟨485981, by rfl⟩ : syracuseStep 647975 = 971963) B971963
theorem B1008617 : Blo 338752 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B5531813 : Blo 338752 5531813 := bstep (se 4 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 5531813 = 1037215) B1037215
theorem B520219 : Blo 338752 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B1143503 : Blo 338752 1143503 := bstep (se 1 (by rfl) ⟨857627, by rfl⟩ : syracuseStep 1143503 = 1715255) B1715255
theorem B13924379 : Blo 338752 13924379 := bstep (se 1 (by rfl) ⟨10443284, by rfl⟩ : syracuseStep 13924379 = 20886569) B20886569
theorem B2193479 : Blo 338752 2193479 := bstep (se 1 (by rfl) ⟨1645109, by rfl⟩ : syracuseStep 2193479 = 3290219) B3290219
theorem B2588435 : Blo 338752 2588435 := bstep (se 1 (by rfl) ⟨1941326, by rfl⟩ : syracuseStep 2588435 = 3882653) B3882653
theorem B3866615 : Blo 338752 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B11175023 : Blo 338752 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B9865799 : Blo 338752 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B2689645 : Blo 338752 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B363623 : Blo 338752 363623 := bstep (se 1 (by rfl) ⟨272717, by rfl⟩ : syracuseStep 363623 = 545435) B545435
theorem B33067439 : Blo 338752 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B2593295 : Blo 338752 2593295 := bstep (se 1 (by rfl) ⟨1944971, by rfl⟩ : syracuseStep 2593295 = 3889943) B3889943
theorem B725735 : Blo 338752 725735 := bstep (se 1 (by rfl) ⟨544301, by rfl⟩ : syracuseStep 725735 = 1088603) B1088603
theorem B726239 : Blo 338752 726239 := bstep (se 1 (by rfl) ⟨544679, by rfl⟩ : syracuseStep 726239 = 1089359) B1089359
theorem B693625 : Blo 338752 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B431983 : Blo 338752 431983 := bstep (se 1 (by rfl) ⟨323987, by rfl⟩ : syracuseStep 431983 = 647975) B647975
theorem B21370817 : Blo 338752 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B727375 : Blo 338752 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B1382777 : Blo 338752 1382777 := bstep (se 2 (by rfl) ⟨518541, by rfl⟩ : syracuseStep 1382777 = 1037083) B1037083
theorem B728681 : Blo 338752 728681 := bstep (se 2 (by rfl) ⟨273255, by rfl⟩ : syracuseStep 728681 = 546511) B546511
theorem B4661387 : Blo 338752 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B762335 : Blo 338752 762335 := bstep (se 1 (by rfl) ⟨571751, by rfl⟩ : syracuseStep 762335 = 1143503) B1143503
theorem B19604267 : Blo 338752 19604267 := bstep (se 1 (by rfl) ⟨14703200, by rfl⟩ : syracuseStep 19604267 = 29406401) B29406401
theorem B861313 : Blo 338752 861313 := bstep (se 2 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 861313 = 645985) B645985
theorem B9282919 : Blo 338752 9282919 := bstep (se 1 (by rfl) ⟨6962189, by rfl⟩ : syracuseStep 9282919 = 13924379) B13924379
theorem B862123 : Blo 338752 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B8301305 : Blo 338752 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B338943 : Blo 338752 338943 := bstep (se 1 (by rfl) ⟨254207, by rfl⟩ : syracuseStep 338943 = 508415) B508415
theorem B339103 : Blo 338752 339103 := bstep (se 1 (by rfl) ⟨254327, by rfl⟩ : syracuseStep 339103 = 508655) B508655
theorem B339303 : Blo 338752 339303 := bstep (se 1 (by rfl) ⟨254477, by rfl⟩ : syracuseStep 339303 = 508955) B508955
theorem B339663 : Blo 338752 339663 := bstep (se 1 (by rfl) ⟨254747, by rfl⟩ : syracuseStep 339663 = 509495) B509495
theorem B1289951 : Blo 338752 1289951 := bstep (se 1 (by rfl) ⟨967463, by rfl⟩ : syracuseStep 1289951 = 1934927) B1934927
theorem B1716065 : Blo 338752 1716065 := bstep (se 2 (by rfl) ⟨643524, by rfl⟩ : syracuseStep 1716065 = 1287049) B1287049
theorem B6205835 : Blo 338752 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B340383 : Blo 338752 340383 := bstep (se 1 (by rfl) ⟨255287, by rfl⟩ : syracuseStep 340383 = 510575) B510575
theorem B340447 : Blo 338752 340447 := bstep (se 1 (by rfl) ⟨255335, by rfl⟩ : syracuseStep 340447 = 510671) B510671
theorem B1716875 : Blo 338752 1716875 := bstep (se 1 (by rfl) ⟨1287656, by rfl⟩ : syracuseStep 1716875 = 2575313) B2575313
theorem B340671 : Blo 338752 340671 := bstep (se 1 (by rfl) ⟨255503, by rfl⟩ : syracuseStep 340671 = 511007) B511007
theorem B340807 : Blo 338752 340807 := bstep (se 1 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 340807 = 511211) B511211
theorem B340927 : Blo 338752 340927 := bstep (se 1 (by rfl) ⟨255695, by rfl⟩ : syracuseStep 340927 = 511391) B511391
theorem B340991 : Blo 338752 340991 := bstep (se 1 (by rfl) ⟨255743, by rfl⟩ : syracuseStep 340991 = 511487) B511487
theorem B341095 : Blo 338752 341095 := bstep (se 1 (by rfl) ⟨255821, by rfl⟩ : syracuseStep 341095 = 511643) B511643
theorem B341275 : Blo 338752 341275 := bstep (se 1 (by rfl) ⟨255956, by rfl⟩ : syracuseStep 341275 = 511913) B511913
theorem B767519 : Blo 338752 767519 := bstep (se 1 (by rfl) ⟨575639, by rfl⟩ : syracuseStep 767519 = 1151279) B1151279
theorem B767609 : Blo 338752 767609 := bstep (se 2 (by rfl) ⟨287853, by rfl⟩ : syracuseStep 767609 = 575707) B575707
theorem B341759 : Blo 338752 341759 := bstep (se 1 (by rfl) ⟨256319, by rfl⟩ : syracuseStep 341759 = 512639) B512639
theorem B767753 : Blo 338752 767753 := bstep (se 2 (by rfl) ⟨287907, by rfl⟩ : syracuseStep 767753 = 575815) B575815
theorem B9844577 : Blo 338752 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B342127 : Blo 338752 342127 := bstep (se 1 (by rfl) ⟨256595, by rfl⟩ : syracuseStep 342127 = 513191) B513191
theorem B768167 : Blo 338752 768167 := bstep (se 1 (by rfl) ⟨576125, by rfl⟩ : syracuseStep 768167 = 1152251) B1152251
theorem B3291367 : Blo 338752 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B768275 : Blo 338752 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B768311 : Blo 338752 768311 := bstep (se 1 (by rfl) ⟨576233, by rfl⟩ : syracuseStep 768311 = 1152467) B1152467
theorem B342399 : Blo 338752 342399 := bstep (se 1 (by rfl) ⟨256799, by rfl⟩ : syracuseStep 342399 = 513599) B513599
theorem B1292699 : Blo 338752 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B342631 : Blo 338752 342631 := bstep (se 1 (by rfl) ⟨256973, by rfl⟩ : syracuseStep 342631 = 513947) B513947
theorem B572015 : Blo 338752 572015 := bstep (se 1 (by rfl) ⟨429011, by rfl⟩ : syracuseStep 572015 = 858023) B858023
theorem B342695 : Blo 338752 342695 := bstep (se 1 (by rfl) ⟨257021, by rfl⟩ : syracuseStep 342695 = 514043) B514043
theorem B768743 : Blo 338752 768743 := bstep (se 1 (by rfl) ⟨576557, by rfl⟩ : syracuseStep 768743 = 1153115) B1153115
theorem B572143 : Blo 338752 572143 := bstep (se 1 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 572143 = 858215) B858215
theorem B736511 : Blo 338752 736511 := bstep (se 1 (by rfl) ⟨552383, by rfl⟩ : syracuseStep 736511 = 1104767) B1104767
theorem B1949255 : Blo 338752 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B1851655 : Blo 338752 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B508583 : Blo 338752 508583 := bstep (se 1 (by rfl) ⟨381437, by rfl⟩ : syracuseStep 508583 = 762875) B762875
theorem B771119 : Blo 338752 771119 := bstep (se 1 (by rfl) ⟨578339, by rfl⟩ : syracuseStep 771119 = 1156679) B1156679
theorem B509375 : Blo 338752 509375 := bstep (se 1 (by rfl) ⟨382031, by rfl⟩ : syracuseStep 509375 = 764063) B764063
theorem B3687875 : Blo 338752 3687875 := bstep (se 1 (by rfl) ⟨2765906, by rfl⟩ : syracuseStep 3687875 = 5531813) B5531813
theorem B510203 : Blo 338752 510203 := bstep (se 1 (by rfl) ⟨382652, by rfl⟩ : syracuseStep 510203 = 765305) B765305
theorem B510239 : Blo 338752 510239 := bstep (se 1 (by rfl) ⟨382679, by rfl⟩ : syracuseStep 510239 = 765359) B765359
theorem B576679 : Blo 338752 576679 := bstep (se 1 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 576679 = 865019) B865019
theorem B511727 : Blo 338752 511727 := bstep (se 1 (by rfl) ⟨383795, by rfl⟩ : syracuseStep 511727 = 767591) B767591
theorem B1462319 : Blo 338752 1462319 := bstep (se 1 (by rfl) ⟨1096739, by rfl⟩ : syracuseStep 1462319 = 2193479) B2193479
theorem B643297 : Blo 338752 643297 := bstep (se 2 (by rfl) ⟨241236, by rfl⟩ : syracuseStep 643297 = 482473) B482473
theorem B512327 : Blo 338752 512327 := bstep (se 1 (by rfl) ⟨384245, by rfl⟩ : syracuseStep 512327 = 768491) B768491
theorem B381487 : Blo 338752 381487 := bstep (se 1 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 381487 = 572231) B572231
theorem B381595 : Blo 338752 381595 := bstep (se 1 (by rfl) ⟨286196, by rfl⟩ : syracuseStep 381595 = 572393) B572393
theorem B381631 : Blo 338752 381631 := bstep (se 1 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 381631 = 572447) B572447
theorem B512891 : Blo 338752 512891 := bstep (se 1 (by rfl) ⟨384668, by rfl⟩ : syracuseStep 512891 = 769337) B769337
theorem B1725623 : Blo 338752 1725623 := bstep (se 1 (by rfl) ⟨1294217, by rfl⟩ : syracuseStep 1725623 = 2588435) B2588435
theorem B4379831 : Blo 338752 4379831 := bstep (se 1 (by rfl) ⟨3284873, by rfl⟩ : syracuseStep 4379831 = 6569747) B6569747
theorem B2577743 : Blo 338752 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B26695169 : Blo 338752 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B382567 : Blo 338752 382567 := bstep (se 1 (by rfl) ⟨286925, by rfl⟩ : syracuseStep 382567 = 573851) B573851
theorem B645887 : Blo 338752 645887 := bstep (se 1 (by rfl) ⟨484415, by rfl⟩ : syracuseStep 645887 = 968831) B968831
theorem B974035 : Blo 338752 974035 := bstep (se 1 (by rfl) ⟨730526, by rfl⟩ : syracuseStep 974035 = 1461053) B1461053
theorem B2579687 : Blo 338752 2579687 := bstep (se 1 (by rfl) ⟨1934765, by rfl⟩ : syracuseStep 2579687 = 3869531) B3869531
theorem B384871 : Blo 338752 384871 := bstep (se 1 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 384871 = 577307) B577307
theorem B975721 : Blo 338752 975721 := bstep (se 2 (by rfl) ⟨365895, by rfl⟩ : syracuseStep 975721 = 731791) B731791
theorem B23848339 : Blo 338752 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B2909803 : Blo 338752 2909803 := bstep (se 1 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 2909803 = 4364705) B4364705
theorem B2910761 : Blo 338752 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B1370927 : Blo 338752 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B2584061 : Blo 338752 2584061 := bstep (se 3 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 2584061 = 969023) B969023
theorem B486967 : Blo 338752 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B25130087 : Blo 338752 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B1144367 : Blo 338752 1144367 := bstep (se 1 (by rfl) ⟨858275, by rfl⟩ : syracuseStep 1144367 = 1716551) B1716551
theorem B2458583 : Blo 338752 2458583 := bstep (se 1 (by rfl) ⟨1843937, by rfl⟩ : syracuseStep 2458583 = 3687875) B3687875
theorem B16548893 : Blo 338752 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B1148417 : Blo 338752 1148417 := bstep (se 2 (by rfl) ⟨430656, by rfl⟩ : syracuseStep 1148417 = 861313) B861313
theorem B1149497 : Blo 338752 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B1150415 : Blo 338752 1150415 := bstep (se 1 (by rfl) ⟨862811, by rfl⟩ : syracuseStep 1150415 = 1725623) B1725623
theorem B2919887 : Blo 338752 2919887 := bstep (se 1 (by rfl) ⟨2189915, by rfl⟩ : syracuseStep 2919887 = 4379831) B4379831
theorem B17796779 : Blo 338752 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B921851 : Blo 338752 921851 := bstep (se 1 (by rfl) ⟨691388, by rfl⟩ : syracuseStep 921851 = 1382777) B1382777
theorem B430591 : Blo 338752 430591 := bstep (se 1 (by rfl) ⟨322943, by rfl⟩ : syracuseStep 430591 = 645887) B645887
theorem B56988845 : Blo 338752 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B857729 : Blo 338752 857729 := bstep (se 2 (by rfl) ⟨321648, by rfl⟩ : syracuseStep 857729 = 643297) B643297
theorem B1940507 : Blo 338752 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B924833 : Blo 338752 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B859967 : Blo 338752 859967 := bstep (se 1 (by rfl) ⟨644975, by rfl⟩ : syracuseStep 859967 = 1289951) B1289951
theorem B16753391 : Blo 338752 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B762857 : Blo 338752 762857 := bstep (se 2 (by rfl) ⟨286071, by rfl⟩ : syracuseStep 762857 = 572143) B572143
theorem B762911 : Blo 338752 762911 := bstep (se 1 (by rfl) ⟨572183, by rfl⟩ : syracuseStep 762911 = 1144367) B1144367
theorem B6563051 : Blo 338752 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B861799 : Blo 338752 861799 := bstep (se 1 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 861799 = 1292699) B1292699
theorem B1943149 : Blo 338752 1943149 := bstep (se 3 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 1943149 = 728681) B728681
theorem B2468873 : Blo 338752 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B339055 : Blo 338752 339055 := bstep (se 1 (by rfl) ⟨254291, by rfl⟩ : syracuseStep 339055 = 508583) B508583
theorem B7450015 : Blo 338752 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B339583 : Blo 338752 339583 := bstep (se 1 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 339583 = 509375) B509375
theorem B340135 : Blo 338752 340135 := bstep (se 1 (by rfl) ⟨255101, by rfl⟩ : syracuseStep 340135 = 510203) B510203
theorem B340159 : Blo 338752 340159 := bstep (se 1 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 340159 = 510239) B510239
theorem B31797785 : Blo 338752 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B3879737 : Blo 338752 3879737 := bstep (se 2 (by rfl) ⟨1454901, by rfl⟩ : syracuseStep 3879737 = 2909803) B2909803
theorem B341151 : Blo 338752 341151 := bstep (se 1 (by rfl) ⟨255863, by rfl⟩ : syracuseStep 341151 = 511727) B511727
theorem B341551 : Blo 338752 341551 := bstep (se 1 (by rfl) ⟨256163, by rfl⟩ : syracuseStep 341551 = 512327) B512327
theorem B341927 : Blo 338752 341927 := bstep (se 1 (by rfl) ⟨256445, by rfl⟩ : syracuseStep 341927 = 512891) B512891
theorem B3586193 : Blo 338752 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1718495 : Blo 338752 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B768905 : Blo 338752 768905 := bstep (se 2 (by rfl) ⟨288339, by rfl⟩ : syracuseStep 768905 = 576679) B576679
theorem B1719791 : Blo 338752 1719791 := bstep (se 1 (by rfl) ⟨1289843, by rfl⟩ : syracuseStep 1719791 = 2579687) B2579687
theorem B508223 : Blo 338752 508223 := bstep (se 1 (by rfl) ⟨381167, by rfl⟩ : syracuseStep 508223 = 762335) B762335
theorem B508649 : Blo 338752 508649 := bstep (se 2 (by rfl) ⟨190743, by rfl⟩ : syracuseStep 508649 = 381487) B381487
theorem B508793 : Blo 338752 508793 := bstep (se 2 (by rfl) ⟨190797, by rfl⟩ : syracuseStep 508793 = 381595) B381595
theorem B508841 : Blo 338752 508841 := bstep (se 2 (by rfl) ⟨190815, by rfl⟩ : syracuseStep 508841 = 381631) B381631
theorem B22136813 : Blo 338752 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B510089 : Blo 338752 510089 := bstep (se 2 (by rfl) ⟨191283, by rfl⟩ : syracuseStep 510089 = 382567) B382567
theorem B1722707 : Blo 338752 1722707 := bstep (se 1 (by rfl) ⟨1292030, by rfl⟩ : syracuseStep 1722707 = 2584061) B2584061
theorem B575977 : Blo 338752 575977 := bstep (se 2 (by rfl) ⟨215991, by rfl⟩ : syracuseStep 575977 = 431983) B431983
theorem B969661 : Blo 338752 969661 := bstep (se 3 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 969661 = 363623) B363623
theorem B969833 : Blo 338752 969833 := bstep (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) B727375
theorem B511679 : Blo 338752 511679 := bstep (se 1 (by rfl) ⟨383759, by rfl⟩ : syracuseStep 511679 = 767519) B767519
theorem B511739 : Blo 338752 511739 := bstep (se 1 (by rfl) ⟨383804, by rfl⟩ : syracuseStep 511739 = 767609) B767609
theorem B511835 : Blo 338752 511835 := bstep (se 1 (by rfl) ⟨383876, by rfl⟩ : syracuseStep 511835 = 767753) B767753
theorem B512111 : Blo 338752 512111 := bstep (se 1 (by rfl) ⟨384083, by rfl⟩ : syracuseStep 512111 = 768167) B768167
theorem B512183 : Blo 338752 512183 := bstep (se 1 (by rfl) ⟨384137, by rfl⟩ : syracuseStep 512183 = 768275) B768275
theorem B512207 : Blo 338752 512207 := bstep (se 1 (by rfl) ⟨384155, by rfl⟩ : syracuseStep 512207 = 768311) B768311
theorem B1298713 : Blo 338752 1298713 := bstep (se 2 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 1298713 = 974035) B974035
theorem B381343 : Blo 338752 381343 := bstep (se 1 (by rfl) ⟨286007, by rfl⟩ : syracuseStep 381343 = 572015) B572015
theorem B512495 : Blo 338752 512495 := bstep (se 1 (by rfl) ⟨384371, by rfl⟩ : syracuseStep 512495 = 768743) B768743
theorem B1299503 : Blo 338752 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B513161 : Blo 338752 513161 := bstep (se 2 (by rfl) ⟨192435, by rfl⟩ : syracuseStep 513161 = 384871) B384871
theorem B514079 : Blo 338752 514079 := bstep (se 1 (by rfl) ⟨385559, by rfl⟩ : syracuseStep 514079 = 771119) B771119
theorem B1300961 : Blo 338752 1300961 := bstep (se 2 (by rfl) ⟨487860, by rfl⟩ : syracuseStep 1300961 = 975721) B975721
theorem B6577199 : Blo 338752 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B12377225 : Blo 338752 12377225 := bstep (se 2 (by rfl) ⟨4641459, by rfl⟩ : syracuseStep 12377225 = 9282919) B9282919
theorem B974879 : Blo 338752 974879 := bstep (se 1 (by rfl) ⟨731159, by rfl⟩ : syracuseStep 974879 = 1462319) B1462319
theorem B22044959 : Blo 338752 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B1728863 : Blo 338752 1728863 := bstep (se 1 (by rfl) ⟨1296647, by rfl⟩ : syracuseStep 1728863 = 2593295) B2593295
theorem B483823 : Blo 338752 483823 := bstep (se 1 (by rfl) ⟨362867, by rfl⟩ : syracuseStep 483823 = 725735) B725735
theorem B484159 : Blo 338752 484159 := bstep (se 1 (by rfl) ⟨363119, by rfl⟩ : syracuseStep 484159 = 726239) B726239
theorem B649289 : Blo 338752 649289 := bstep (se 2 (by rfl) ⟨243483, by rfl⟩ : syracuseStep 649289 = 486967) B486967
theorem B3107591 : Blo 338752 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B13069511 : Blo 338752 13069511 := bstep (se 1 (by rfl) ⟨9802133, by rfl⟩ : syracuseStep 13069511 = 19604267) B19604267
theorem B913951 : Blo 338752 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B1144043 : Blo 338752 1144043 := bstep (se 1 (by rfl) ⟨858032, by rfl⟩ : syracuseStep 1144043 = 1716065) B1716065
theorem B4388489 : Blo 338752 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B1144583 : Blo 338752 1144583 := bstep (se 1 (by rfl) ⟨858437, by rfl⟩ : syracuseStep 1144583 = 1716875) B1716875
theorem B1964029 : Blo 338752 1964029 := bstep (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) B736511
theorem B1639055 : Blo 338752 1639055 := bstep (se 1 (by rfl) ⟨1229291, by rfl⟩ : syracuseStep 1639055 = 2458583) B2458583
theorem B1148471 : Blo 338752 1148471 := bstep (se 1 (by rfl) ⟨861353, by rfl⟩ : syracuseStep 1148471 = 1722707) B1722707
theorem B1149065 : Blo 338752 1149065 := bstep (se 2 (by rfl) ⟨430899, by rfl⟩ : syracuseStep 1149065 = 861799) B861799
theorem B2590865 : Blo 338752 2590865 := bstep (se 2 (by rfl) ⟨971574, by rfl⟩ : syracuseStep 2590865 = 1943149) B1943149
theorem B11864519 : Blo 338752 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B9933353 : Blo 338752 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B1152575 : Blo 338752 1152575 := bstep (se 1 (by rfl) ⟨864431, by rfl⟩ : syracuseStep 1152575 = 1728863) B1728863
theorem B1218601 : Blo 338752 1218601 := bstep (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) B913951
theorem B432859 : Blo 338752 432859 := bstep (se 1 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 432859 = 649289) B649289
theorem B2071727 : Blo 338752 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B1645915 : Blo 338752 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B762695 : Blo 338752 762695 := bstep (se 1 (by rfl) ⟨572021, by rfl⟩ : syracuseStep 762695 = 1144043) B1144043
theorem B2925659 : Blo 338752 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B763055 : Blo 338752 763055 := bstep (se 1 (by rfl) ⟨572291, by rfl⟩ : syracuseStep 763055 = 1144583) B1144583
theorem B338815 : Blo 338752 338815 := bstep (se 1 (by rfl) ⟨254111, by rfl⟩ : syracuseStep 338815 = 508223) B508223
theorem B339099 : Blo 338752 339099 := bstep (se 1 (by rfl) ⟨254324, by rfl⟩ : syracuseStep 339099 = 508649) B508649
theorem B339195 : Blo 338752 339195 := bstep (se 1 (by rfl) ⟨254396, by rfl⟩ : syracuseStep 339195 = 508793) B508793
theorem B339227 : Blo 338752 339227 := bstep (se 1 (by rfl) ⟨254420, by rfl⟩ : syracuseStep 339227 = 508841) B508841
theorem B765611 : Blo 338752 765611 := bstep (se 1 (by rfl) ⟨574208, by rfl⟩ : syracuseStep 765611 = 1148417) B1148417
theorem B14757875 : Blo 338752 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B340059 : Blo 338752 340059 := bstep (se 1 (by rfl) ⟨255044, by rfl⟩ : syracuseStep 340059 = 510089) B510089
theorem B766331 : Blo 338752 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B766943 : Blo 338752 766943 := bstep (se 1 (by rfl) ⟨575207, by rfl⟩ : syracuseStep 766943 = 1150415) B1150415
theorem B1946591 : Blo 338752 1946591 := bstep (se 1 (by rfl) ⟨1459943, by rfl⟩ : syracuseStep 1946591 = 2919887) B2919887
theorem B341119 : Blo 338752 341119 := bstep (se 1 (by rfl) ⟨255839, by rfl⟩ : syracuseStep 341119 = 511679) B511679
theorem B341159 : Blo 338752 341159 := bstep (se 1 (by rfl) ⟨255869, by rfl⟩ : syracuseStep 341159 = 511739) B511739
theorem B341223 : Blo 338752 341223 := bstep (se 1 (by rfl) ⟨255917, by rfl⟩ : syracuseStep 341223 = 511835) B511835
theorem B341407 : Blo 338752 341407 := bstep (se 1 (by rfl) ⟨256055, by rfl⟩ : syracuseStep 341407 = 512111) B512111
theorem B341455 : Blo 338752 341455 := bstep (se 1 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 341455 = 512183) B512183
theorem B341471 : Blo 338752 341471 := bstep (se 1 (by rfl) ⟨256103, by rfl⟩ : syracuseStep 341471 = 512207) B512207
theorem B341663 : Blo 338752 341663 := bstep (se 1 (by rfl) ⟨256247, by rfl⟩ : syracuseStep 341663 = 512495) B512495
theorem B767969 : Blo 338752 767969 := bstep (se 2 (by rfl) ⟨287988, by rfl⟩ : syracuseStep 767969 = 575977) B575977
theorem B866335 : Blo 338752 866335 := bstep (se 1 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 866335 = 1299503) B1299503
theorem B342107 : Blo 338752 342107 := bstep (se 1 (by rfl) ⟨256580, by rfl⟩ : syracuseStep 342107 = 513161) B513161
theorem B37992563 : Blo 338752 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B571819 : Blo 338752 571819 := bstep (se 1 (by rfl) ⟨428864, by rfl⟩ : syracuseStep 571819 = 857729) B857729
theorem B1292881 : Blo 338752 1292881 := bstep (se 2 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 1292881 = 969661) B969661
theorem B342719 : Blo 338752 342719 := bstep (se 1 (by rfl) ⟨257039, by rfl⟩ : syracuseStep 342719 = 514079) B514079
theorem B867307 : Blo 338752 867307 := bstep (se 1 (by rfl) ⟨650480, by rfl⟩ : syracuseStep 867307 = 1300961) B1300961
theorem B1293671 : Blo 338752 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B573311 : Blo 338752 573311 := bstep (se 1 (by rfl) ⟨429983, by rfl⟩ : syracuseStep 573311 = 859967) B859967
theorem B14696639 : Blo 338752 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B508457 : Blo 338752 508457 := bstep (se 2 (by rfl) ⟨190671, by rfl⟩ : syracuseStep 508457 = 381343) B381343
theorem B508571 : Blo 338752 508571 := bstep (se 1 (by rfl) ⟨381428, by rfl⟩ : syracuseStep 508571 = 762857) B762857
theorem B574121 : Blo 338752 574121 := bstep (se 2 (by rfl) ⟨215295, by rfl⟩ : syracuseStep 574121 = 430591) B430591
theorem B508607 : Blo 338752 508607 := bstep (se 1 (by rfl) ⟨381455, by rfl⟩ : syracuseStep 508607 = 762911) B762911
theorem B4375367 : Blo 338752 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B512603 : Blo 338752 512603 := bstep (se 1 (by rfl) ⟨384452, by rfl⟩ : syracuseStep 512603 = 768905) B768905
theorem B645097 : Blo 338752 645097 := bstep (se 2 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 645097 = 483823) B483823
theorem B11032595 : Blo 338752 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B645545 : Blo 338752 645545 := bstep (se 2 (by rfl) ⟨242079, by rfl⟩ : syracuseStep 645545 = 484159) B484159
theorem B646555 : Blo 338752 646555 := bstep (se 1 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 646555 = 969833) B969833
theorem B614567 : Blo 338752 614567 := bstep (se 1 (by rfl) ⟨460925, by rfl⟩ : syracuseStep 614567 = 921851) B921851
theorem B4384799 : Blo 338752 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B8251483 : Blo 338752 8251483 := bstep (se 1 (by rfl) ⟨6188612, by rfl⟩ : syracuseStep 8251483 = 12377225) B12377225
theorem B616555 : Blo 338752 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B649919 : Blo 338752 649919 := bstep (se 1 (by rfl) ⟨487439, by rfl⟩ : syracuseStep 649919 = 974879) B974879
theorem B1731617 : Blo 338752 1731617 := bstep (se 2 (by rfl) ⟨649356, by rfl⟩ : syracuseStep 1731617 = 1298713) B1298713
theorem B11168927 : Blo 338752 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B8713007 : Blo 338752 8713007 := bstep (se 1 (by rfl) ⟨6534755, by rfl⟩ : syracuseStep 8713007 = 13069511) B13069511
theorem B2618705 : Blo 338752 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B21198523 : Blo 338752 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B2586491 : Blo 338752 2586491 := bstep (se 1 (by rfl) ⟨1939868, by rfl⟩ : syracuseStep 2586491 = 3879737) B3879737
theorem B2390795 : Blo 338752 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B1145663 : Blo 338752 1145663 := bstep (se 1 (by rfl) ⟨859247, by rfl⟩ : syracuseStep 1145663 = 1718495) B1718495
theorem B1146527 : Blo 338752 1146527 := bstep (se 1 (by rfl) ⟨859895, by rfl⟩ : syracuseStep 1146527 = 1719791) B1719791
theorem B9797759 : Blo 338752 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B2916911 : Blo 338752 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B822073 : Blo 338752 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B6622235 : Blo 338752 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B430363 : Blo 338752 430363 := bstep (se 1 (by rfl) ⟨322772, by rfl⟩ : syracuseStep 430363 = 645545) B645545
theorem B1381151 : Blo 338752 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B2923199 : Blo 338752 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B433279 : Blo 338752 433279 := bstep (se 1 (by rfl) ⟨324959, by rfl⟩ : syracuseStep 433279 = 649919) B649919
theorem B1154411 : Blo 338752 1154411 := bstep (se 1 (by rfl) ⟨865808, by rfl⟩ : syracuseStep 1154411 = 1731617) B1731617
theorem B7445951 : Blo 338752 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B860129 : Blo 338752 860129 := bstep (se 2 (by rfl) ⟨322548, by rfl⟩ : syracuseStep 860129 = 645097) B645097
theorem B9838583 : Blo 338752 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B1155113 : Blo 338752 1155113 := bstep (se 2 (by rfl) ⟨433167, by rfl⟩ : syracuseStep 1155113 = 866335) B866335
theorem B5808671 : Blo 338752 5808671 := bstep (se 1 (by rfl) ⟨4356503, by rfl⟩ : syracuseStep 5808671 = 8713007) B8713007
theorem B762425 : Blo 338752 762425 := bstep (se 2 (by rfl) ⟨285909, by rfl⟩ : syracuseStep 762425 = 571819) B571819
theorem B1745803 : Blo 338752 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B1156409 : Blo 338752 1156409 := bstep (se 2 (by rfl) ⟨433653, by rfl⟩ : syracuseStep 1156409 = 867307) B867307
theorem B862073 : Blo 338752 862073 := bstep (se 2 (by rfl) ⟨323277, by rfl⟩ : syracuseStep 862073 = 646555) B646555
theorem B763775 : Blo 338752 763775 := bstep (se 1 (by rfl) ⟨572831, by rfl⟩ : syracuseStep 763775 = 1145663) B1145663
theorem B862447 : Blo 338752 862447 := bstep (se 1 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 862447 = 1293671) B1293671
theorem B764351 : Blo 338752 764351 := bstep (se 1 (by rfl) ⟨573263, by rfl⟩ : syracuseStep 764351 = 1146527) B1146527
theorem B338971 : Blo 338752 338971 := bstep (se 1 (by rfl) ⟨254228, by rfl⟩ : syracuseStep 338971 = 508457) B508457
theorem B1092703 : Blo 338752 1092703 := bstep (se 1 (by rfl) ⟨819527, by rfl⟩ : syracuseStep 1092703 = 1639055) B1639055
theorem B339047 : Blo 338752 339047 := bstep (se 1 (by rfl) ⟨254285, by rfl⟩ : syracuseStep 339047 = 508571) B508571
theorem B339071 : Blo 338752 339071 := bstep (se 1 (by rfl) ⟨254303, by rfl⟩ : syracuseStep 339071 = 508607) B508607
theorem B765647 : Blo 338752 765647 := bstep (se 1 (by rfl) ⟨574235, by rfl⟩ : syracuseStep 765647 = 1148471) B1148471
theorem B766043 : Blo 338752 766043 := bstep (se 1 (by rfl) ⟨574532, by rfl⟩ : syracuseStep 766043 = 1149065) B1149065
theorem B7909679 : Blo 338752 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B341735 : Blo 338752 341735 := bstep (se 1 (by rfl) ⟨256301, by rfl⟩ : syracuseStep 341735 = 512603) B512603
theorem B768383 : Blo 338752 768383 := bstep (se 1 (by rfl) ⟨576287, by rfl⟩ : syracuseStep 768383 = 1152575) B1152575
theorem B7355063 : Blo 338752 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B409711 : Blo 338752 409711 := bstep (se 1 (by rfl) ⟨307283, by rfl⟩ : syracuseStep 409711 = 614567) B614567
theorem B508463 : Blo 338752 508463 := bstep (se 1 (by rfl) ⟨381347, by rfl⟩ : syracuseStep 508463 = 762695) B762695
theorem B1950439 : Blo 338752 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B508703 : Blo 338752 508703 := bstep (se 1 (by rfl) ⟨381527, by rfl⟩ : syracuseStep 508703 = 763055) B763055
theorem B28264697 : Blo 338752 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B510407 : Blo 338752 510407 := bstep (se 1 (by rfl) ⟨382805, by rfl⟩ : syracuseStep 510407 = 765611) B765611
theorem B1624801 : Blo 338752 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B510887 : Blo 338752 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B1297727 : Blo 338752 1297727 := bstep (se 1 (by rfl) ⟨973295, by rfl⟩ : syracuseStep 1297727 = 1946591) B1946591
theorem B511295 : Blo 338752 511295 := bstep (se 1 (by rfl) ⟨383471, by rfl⟩ : syracuseStep 511295 = 766943) B766943
theorem B1723841 : Blo 338752 1723841 := bstep (se 2 (by rfl) ⟨646440, by rfl⟩ : syracuseStep 1723841 = 1292881) B1292881
theorem B577145 : Blo 338752 577145 := bstep (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) B432859
theorem B1724327 : Blo 338752 1724327 := bstep (se 1 (by rfl) ⟨1293245, by rfl⟩ : syracuseStep 1724327 = 2586491) B2586491
theorem B511979 : Blo 338752 511979 := bstep (se 1 (by rfl) ⟨383984, by rfl⟩ : syracuseStep 511979 = 767969) B767969
theorem B1593863 : Blo 338752 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B382207 : Blo 338752 382207 := bstep (se 1 (by rfl) ⟨286655, by rfl⟩ : syracuseStep 382207 = 573311) B573311
theorem B382747 : Blo 338752 382747 := bstep (se 1 (by rfl) ⟨287060, by rfl⟩ : syracuseStep 382747 = 574121) B574121
theorem B1727243 : Blo 338752 1727243 := bstep (se 1 (by rfl) ⟨1295432, by rfl⟩ : syracuseStep 1727243 = 2590865) B2590865
theorem B11001977 : Blo 338752 11001977 := bstep (se 2 (by rfl) ⟨4125741, by rfl⟩ : syracuseStep 11001977 = 8251483) B8251483
theorem B25328375 : Blo 338752 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B2194553 : Blo 338752 2194553 := bstep (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) B1645915
theorem B18843131 : Blo 338752 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B1149227 : Blo 338752 1149227 := bstep (se 1 (by rfl) ⟨861920, by rfl⟩ : syracuseStep 1149227 = 1723841) B1723841
theorem B1149551 : Blo 338752 1149551 := bstep (se 1 (by rfl) ⟨862163, by rfl⟩ : syracuseStep 1149551 = 1724327) B1724327
theorem B1149929 : Blo 338752 1149929 := bstep (se 2 (by rfl) ⟨431223, by rfl⟩ : syracuseStep 1149929 = 862447) B862447
theorem B2166401 : Blo 338752 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B1151495 : Blo 338752 1151495 := bstep (se 1 (by rfl) ⟨863621, by rfl⟩ : syracuseStep 1151495 = 1727243) B1727243
theorem B9310949 : Blo 338752 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B6559055 : Blo 338752 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B3872447 : Blo 338752 3872447 := bstep (se 1 (by rfl) ⟨2904335, by rfl⟩ : syracuseStep 3872447 = 5808671) B5808671
theorem B16885583 : Blo 338752 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B6531839 : Blo 338752 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B338975 : Blo 338752 338975 := bstep (se 1 (by rfl) ⟨254231, by rfl⟩ : syracuseStep 338975 = 508463) B508463
theorem B1944607 : Blo 338752 1944607 := bstep (se 1 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 1944607 = 2916911) B2916911
theorem B339135 : Blo 338752 339135 := bstep (se 1 (by rfl) ⟨254351, by rfl⟩ : syracuseStep 339135 = 508703) B508703
theorem B2600585 : Blo 338752 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B340271 : Blo 338752 340271 := bstep (se 1 (by rfl) ⟨255203, by rfl⟩ : syracuseStep 340271 = 510407) B510407
theorem B340591 : Blo 338752 340591 := bstep (se 1 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 340591 = 510887) B510887
theorem B3683069 : Blo 338752 3683069 := bstep (se 3 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 3683069 = 1381151) B1381151
theorem B340863 : Blo 338752 340863 := bstep (se 1 (by rfl) ⟨255647, by rfl⟩ : syracuseStep 340863 = 511295) B511295
theorem B865151 : Blo 338752 865151 := bstep (se 1 (by rfl) ⟨648863, by rfl⟩ : syracuseStep 865151 = 1297727) B1297727
theorem B341319 : Blo 338752 341319 := bstep (se 1 (by rfl) ⟨255989, by rfl⟩ : syracuseStep 341319 = 511979) B511979
theorem B1062575 : Blo 338752 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B1096097 : Blo 338752 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B1456937 : Blo 338752 1456937 := bstep (se 2 (by rfl) ⟨546351, by rfl⟩ : syracuseStep 1456937 = 1092703) B1092703
theorem B1948799 : Blo 338752 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B769607 : Blo 338752 769607 := bstep (se 1 (by rfl) ⟨577205, by rfl⟩ : syracuseStep 769607 = 1154411) B1154411
theorem B4963967 : Blo 338752 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B573419 : Blo 338752 573419 := bstep (se 1 (by rfl) ⟨430064, by rfl⟩ : syracuseStep 573419 = 860129) B860129
theorem B770075 : Blo 338752 770075 := bstep (se 1 (by rfl) ⟨577556, by rfl⟩ : syracuseStep 770075 = 1155113) B1155113
theorem B573817 : Blo 338752 573817 := bstep (se 2 (by rfl) ⟨215181, by rfl⟩ : syracuseStep 573817 = 430363) B430363
theorem B508283 : Blo 338752 508283 := bstep (se 1 (by rfl) ⟨381212, by rfl⟩ : syracuseStep 508283 = 762425) B762425
theorem B770939 : Blo 338752 770939 := bstep (se 1 (by rfl) ⟨578204, by rfl⟩ : syracuseStep 770939 = 1156409) B1156409
theorem B574715 : Blo 338752 574715 := bstep (se 1 (by rfl) ⟨431036, by rfl⟩ : syracuseStep 574715 = 862073) B862073
theorem B509183 : Blo 338752 509183 := bstep (se 1 (by rfl) ⟨381887, by rfl⟩ : syracuseStep 509183 = 763775) B763775
theorem B509567 : Blo 338752 509567 := bstep (se 1 (by rfl) ⟨382175, by rfl⟩ : syracuseStep 509567 = 764351) B764351
theorem B509609 : Blo 338752 509609 := bstep (se 2 (by rfl) ⟨191103, by rfl⟩ : syracuseStep 509609 = 382207) B382207
theorem B510329 : Blo 338752 510329 := bstep (se 2 (by rfl) ⟨191373, by rfl⟩ : syracuseStep 510329 = 382747) B382747
theorem B510431 : Blo 338752 510431 := bstep (se 1 (by rfl) ⟨382823, by rfl⟩ : syracuseStep 510431 = 765647) B765647
theorem B510695 : Blo 338752 510695 := bstep (se 1 (by rfl) ⟨383021, by rfl⟩ : syracuseStep 510695 = 766043) B766043
theorem B577705 : Blo 338752 577705 := bstep (se 2 (by rfl) ⟨216639, by rfl⟩ : syracuseStep 577705 = 433279) B433279
theorem B512255 : Blo 338752 512255 := bstep (se 1 (by rfl) ⟨384191, by rfl⟩ : syracuseStep 512255 = 768383) B768383
theorem B4903375 : Blo 338752 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B1463035 : Blo 338752 1463035 := bstep (se 1 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 1463035 = 2194553) B2194553
theorem B546281 : Blo 338752 546281 := bstep (se 2 (by rfl) ⟨204855, by rfl⟩ : syracuseStep 546281 = 409711) B409711
theorem B4414823 : Blo 338752 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B384763 : Blo 338752 384763 := bstep (se 1 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 384763 = 577145) B577145
theorem B7334651 : Blo 338752 7334651 := bstep (se 1 (by rfl) ⟨5500988, by rfl⟩ : syracuseStep 7334651 = 11001977) B11001977
theorem B5273119 : Blo 338752 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B1444267 : Blo 338752 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B364187 : Blo 338752 364187 := bstep (se 1 (by rfl) ⟨273140, by rfl⟩ : syracuseStep 364187 = 546281) B546281
theorem B2592809 : Blo 338752 2592809 := bstep (se 2 (by rfl) ⟨972303, by rfl⟩ : syracuseStep 2592809 = 1944607) B1944607
theorem B2922925 : Blo 338752 2922925 := bstep (se 3 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 2922925 = 1096097) B1096097
theorem B4889767 : Blo 338752 4889767 := bstep (se 1 (by rfl) ⟨3667325, by rfl⟩ : syracuseStep 4889767 = 7334651) B7334651
theorem B28123301 : Blo 338752 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B338855 : Blo 338752 338855 := bstep (se 1 (by rfl) ⟨254141, by rfl⟩ : syracuseStep 338855 = 508283) B508283
theorem B765089 : Blo 338752 765089 := bstep (se 2 (by rfl) ⟨286908, by rfl⟩ : syracuseStep 765089 = 573817) B573817
theorem B339455 : Blo 338752 339455 := bstep (se 1 (by rfl) ⟨254591, by rfl⟩ : syracuseStep 339455 = 509183) B509183
theorem B12562087 : Blo 338752 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B339711 : Blo 338752 339711 := bstep (se 1 (by rfl) ⟨254783, by rfl⟩ : syracuseStep 339711 = 509567) B509567
theorem B339739 : Blo 338752 339739 := bstep (se 1 (by rfl) ⟨254804, by rfl⟩ : syracuseStep 339739 = 509609) B509609
theorem B766151 : Blo 338752 766151 := bstep (se 1 (by rfl) ⟨574613, by rfl⟩ : syracuseStep 766151 = 1149227) B1149227
theorem B340219 : Blo 338752 340219 := bstep (se 1 (by rfl) ⟨255164, by rfl⟩ : syracuseStep 340219 = 510329) B510329
theorem B340287 : Blo 338752 340287 := bstep (se 1 (by rfl) ⟨255215, by rfl⟩ : syracuseStep 340287 = 510431) B510431
theorem B766367 : Blo 338752 766367 := bstep (se 1 (by rfl) ⟨574775, by rfl⟩ : syracuseStep 766367 = 1149551) B1149551
theorem B340463 : Blo 338752 340463 := bstep (se 1 (by rfl) ⟨255347, by rfl⟩ : syracuseStep 340463 = 510695) B510695
theorem B766619 : Blo 338752 766619 := bstep (se 1 (by rfl) ⟨574964, by rfl⟩ : syracuseStep 766619 = 1149929) B1149929
theorem B341503 : Blo 338752 341503 := bstep (se 1 (by rfl) ⟨256127, by rfl⟩ : syracuseStep 341503 = 512255) B512255
theorem B767663 : Blo 338752 767663 := bstep (se 1 (by rfl) ⟨575747, by rfl⟩ : syracuseStep 767663 = 1151495) B1151495
theorem B6207299 : Blo 338752 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B4372703 : Blo 338752 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B770273 : Blo 338752 770273 := bstep (se 2 (by rfl) ⟨288852, by rfl⟩ : syracuseStep 770273 = 577705) B577705
theorem B6537833 : Blo 338752 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B1950713 : Blo 338752 1950713 := bstep (se 2 (by rfl) ⟨731517, by rfl⟩ : syracuseStep 1950713 = 1463035) B1463035
theorem B11257055 : Blo 338752 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B576767 : Blo 338752 576767 := bstep (se 1 (by rfl) ⟨432575, by rfl⟩ : syracuseStep 576767 = 865151) B865151
theorem B708383 : Blo 338752 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B971291 : Blo 338752 971291 := bstep (se 1 (by rfl) ⟨728468, by rfl⟩ : syracuseStep 971291 = 1456937) B1456937
theorem B1299199 : Blo 338752 1299199 := bstep (se 1 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 1299199 = 1948799) B1948799
theorem B513017 : Blo 338752 513017 := bstep (se 2 (by rfl) ⟨192381, by rfl⟩ : syracuseStep 513017 = 384763) B384763
theorem B513071 : Blo 338752 513071 := bstep (se 1 (by rfl) ⟨384803, by rfl⟩ : syracuseStep 513071 = 769607) B769607
theorem B382279 : Blo 338752 382279 := bstep (se 1 (by rfl) ⟨286709, by rfl⟩ : syracuseStep 382279 = 573419) B573419
theorem B513383 : Blo 338752 513383 := bstep (se 1 (by rfl) ⟨385037, by rfl⟩ : syracuseStep 513383 = 770075) B770075
theorem B513959 : Blo 338752 513959 := bstep (se 1 (by rfl) ⟨385469, by rfl⟩ : syracuseStep 513959 = 770939) B770939
theorem B383143 : Blo 338752 383143 := bstep (se 1 (by rfl) ⟨287357, by rfl⟩ : syracuseStep 383143 = 574715) B574715
theorem B2581631 : Blo 338752 2581631 := bstep (se 1 (by rfl) ⟨1936223, by rfl⟩ : syracuseStep 2581631 = 3872447) B3872447
theorem B2943215 : Blo 338752 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B4354559 : Blo 338752 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B1733723 : Blo 338752 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B2455379 : Blo 338752 2455379 := bstep (se 1 (by rfl) ⟨1841534, by rfl⟩ : syracuseStep 2455379 = 3683069) B3683069
theorem B3309311 : Blo 338752 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B4358555 : Blo 338752 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B7504703 : Blo 338752 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B16749449 : Blo 338752 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B18748867 : Blo 338752 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B1155815 : Blo 338752 1155815 := bstep (se 1 (by rfl) ⟨866861, by rfl⟩ : syracuseStep 1155815 = 1733723) B1733723
theorem B4138199 : Blo 338752 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B2206207 : Blo 338752 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B472255 : Blo 338752 472255 := bstep (se 1 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 472255 = 708383) B708383
theorem B342011 : Blo 338752 342011 := bstep (se 1 (by rfl) ⟨256508, by rfl⟩ : syracuseStep 342011 = 513017) B513017
theorem B342047 : Blo 338752 342047 := bstep (se 1 (by rfl) ⟨256535, by rfl⟩ : syracuseStep 342047 = 513071) B513071
theorem B342255 : Blo 338752 342255 := bstep (se 1 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 342255 = 513383) B513383
theorem B342639 : Blo 338752 342639 := bstep (se 1 (by rfl) ⟨256979, by rfl⟩ : syracuseStep 342639 = 513959) B513959
theorem B1721087 : Blo 338752 1721087 := bstep (se 1 (by rfl) ⟨1290815, by rfl⟩ : syracuseStep 1721087 = 2581631) B2581631
theorem B509705 : Blo 338752 509705 := bstep (se 2 (by rfl) ⟨191139, by rfl⟩ : syracuseStep 509705 = 382279) B382279
theorem B510059 : Blo 338752 510059 := bstep (se 1 (by rfl) ⟨382544, by rfl⟩ : syracuseStep 510059 = 765089) B765089
theorem B510767 : Blo 338752 510767 := bstep (se 1 (by rfl) ⟨383075, by rfl⟩ : syracuseStep 510767 = 766151) B766151
theorem B510857 : Blo 338752 510857 := bstep (se 2 (by rfl) ⟨191571, by rfl⟩ : syracuseStep 510857 = 383143) B383143
theorem B510911 : Blo 338752 510911 := bstep (se 1 (by rfl) ⟨383183, by rfl⟩ : syracuseStep 510911 = 766367) B766367
theorem B2903039 : Blo 338752 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B511079 : Blo 338752 511079 := bstep (se 1 (by rfl) ⟨383309, by rfl⟩ : syracuseStep 511079 = 766619) B766619
theorem B511775 : Blo 338752 511775 := bstep (se 1 (by rfl) ⟨383831, by rfl⟩ : syracuseStep 511775 = 767663) B767663
theorem B971165 : Blo 338752 971165 := bstep (se 3 (by rfl) ⟨182093, by rfl⟩ : syracuseStep 971165 = 364187) B364187
theorem B513515 : Blo 338752 513515 := bstep (se 1 (by rfl) ⟨385136, by rfl⟩ : syracuseStep 513515 = 770273) B770273
theorem B1300475 : Blo 338752 1300475 := bstep (se 1 (by rfl) ⟨975356, by rfl⟩ : syracuseStep 1300475 = 1950713) B1950713
theorem B384511 : Blo 338752 384511 := bstep (se 1 (by rfl) ⟨288383, by rfl⟩ : syracuseStep 384511 = 576767) B576767
theorem B1728539 : Blo 338752 1728539 := bstep (se 1 (by rfl) ⟨1296404, by rfl⟩ : syracuseStep 1728539 = 2592809) B2592809
theorem B647527 : Blo 338752 647527 := bstep (se 1 (by rfl) ⟨485645, by rfl⟩ : syracuseStep 647527 = 971291) B971291
theorem B1925689 : Blo 338752 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B1732265 : Blo 338752 1732265 := bstep (se 2 (by rfl) ⟨649599, by rfl⟩ : syracuseStep 1732265 = 1299199) B1299199
theorem B1962143 : Blo 338752 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B3897233 : Blo 338752 3897233 := bstep (se 2 (by rfl) ⟨1461462, by rfl⟩ : syracuseStep 3897233 = 2922925) B2922925
theorem B1636919 : Blo 338752 1636919 := bstep (se 1 (by rfl) ⟨1227689, by rfl⟩ : syracuseStep 1636919 = 2455379) B2455379
theorem B2915135 : Blo 338752 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B6519689 : Blo 338752 6519689 := bstep (se 2 (by rfl) ⟨2444883, by rfl⟩ : syracuseStep 6519689 = 4889767) B4889767
theorem B1147391 : Blo 338752 1147391 := bstep (se 1 (by rfl) ⟨860543, by rfl⟩ : syracuseStep 1147391 = 1721087) B1721087
theorem B1935359 : Blo 338752 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B11766437 : Blo 338752 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B1152359 : Blo 338752 1152359 := bstep (se 1 (by rfl) ⟨864269, by rfl⟩ : syracuseStep 1152359 = 1728539) B1728539
theorem B2758799 : Blo 338752 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B1154843 : Blo 338752 1154843 := bstep (se 1 (by rfl) ⟨866132, by rfl⟩ : syracuseStep 1154843 = 1732265) B1732265
theorem B2598155 : Blo 338752 2598155 := bstep (se 1 (by rfl) ⟨1948616, by rfl⟩ : syracuseStep 2598155 = 3897233) B3897233
theorem B1091279 : Blo 338752 1091279 := bstep (se 1 (by rfl) ⟨818459, by rfl⟩ : syracuseStep 1091279 = 1636919) B1636919
theorem B1943423 : Blo 338752 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B863369 : Blo 338752 863369 := bstep (se 2 (by rfl) ⟨323763, by rfl⟩ : syracuseStep 863369 = 647527) B647527
theorem B2567585 : Blo 338752 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B339803 : Blo 338752 339803 := bstep (se 1 (by rfl) ⟨254852, by rfl⟩ : syracuseStep 339803 = 509705) B509705
theorem B340039 : Blo 338752 340039 := bstep (se 1 (by rfl) ⟨255029, by rfl⟩ : syracuseStep 340039 = 510059) B510059
theorem B340511 : Blo 338752 340511 := bstep (se 1 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 340511 = 510767) B510767
theorem B340571 : Blo 338752 340571 := bstep (se 1 (by rfl) ⟨255428, by rfl⟩ : syracuseStep 340571 = 510857) B510857
theorem B340607 : Blo 338752 340607 := bstep (se 1 (by rfl) ⟨255455, by rfl⟩ : syracuseStep 340607 = 510911) B510911
theorem B340719 : Blo 338752 340719 := bstep (se 1 (by rfl) ⟨255539, by rfl⟩ : syracuseStep 340719 = 511079) B511079
theorem B341183 : Blo 338752 341183 := bstep (se 1 (by rfl) ⟨255887, by rfl⟩ : syracuseStep 341183 = 511775) B511775
theorem B342343 : Blo 338752 342343 := bstep (se 1 (by rfl) ⟨256757, by rfl⟩ : syracuseStep 342343 = 513515) B513515
theorem B10074773 : Blo 338752 10074773 := bstep (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) B472255
theorem B866983 : Blo 338752 866983 := bstep (se 1 (by rfl) ⟨650237, by rfl⟩ : syracuseStep 866983 = 1300475) B1300475
theorem B770543 : Blo 338752 770543 := bstep (se 1 (by rfl) ⟨577907, by rfl⟩ : syracuseStep 770543 = 1155815) B1155815
theorem B4346459 : Blo 338752 4346459 := bstep (se 1 (by rfl) ⟨3259844, by rfl⟩ : syracuseStep 4346459 = 6519689) B6519689
theorem B512681 : Blo 338752 512681 := bstep (se 2 (by rfl) ⟨192255, by rfl⟩ : syracuseStep 512681 = 384511) B384511
theorem B2905703 : Blo 338752 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B5003135 : Blo 338752 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B647443 : Blo 338752 647443 := bstep (se 1 (by rfl) ⟨485582, by rfl⟩ : syracuseStep 647443 = 971165) B971165
theorem B11166299 : Blo 338752 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B24998489 : Blo 338752 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B1308095 : Blo 338752 1308095 := bstep (se 1 (by rfl) ⟨981071, by rfl⟩ : syracuseStep 1308095 = 1962143) B1962143
theorem B1937135 : Blo 338752 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B1839199 : Blo 338752 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B7444199 : Blo 338752 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B1155977 : Blo 338752 1155977 := bstep (se 2 (by rfl) ⟨433491, by rfl⟩ : syracuseStep 1155977 = 866983) B866983
theorem B764927 : Blo 338752 764927 := bstep (se 1 (by rfl) ⟨573695, by rfl⟩ : syracuseStep 764927 = 1147391) B1147391
theorem B863257 : Blo 338752 863257 := bstep (se 2 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 863257 = 647443) B647443
theorem B1290239 : Blo 338752 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B7844291 : Blo 338752 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B2897639 : Blo 338752 2897639 := bstep (se 1 (by rfl) ⟨2173229, by rfl⟩ : syracuseStep 2897639 = 4346459) B4346459
theorem B341787 : Blo 338752 341787 := bstep (se 1 (by rfl) ⟨256340, by rfl⟩ : syracuseStep 341787 = 512681) B512681
theorem B768239 : Blo 338752 768239 := bstep (se 1 (by rfl) ⟨576179, by rfl⟩ : syracuseStep 768239 = 1152359) B1152359
theorem B769895 : Blo 338752 769895 := bstep (se 1 (by rfl) ⟨577421, by rfl⟩ : syracuseStep 769895 = 1154843) B1154843
theorem B1295615 : Blo 338752 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B575579 : Blo 338752 575579 := bstep (se 1 (by rfl) ⟨431684, by rfl⟩ : syracuseStep 575579 = 863369) B863369
theorem B16665659 : Blo 338752 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B872063 : Blo 338752 872063 := bstep (se 1 (by rfl) ⟨654047, by rfl⟩ : syracuseStep 872063 = 1308095) B1308095
theorem B513695 : Blo 338752 513695 := bstep (se 1 (by rfl) ⟨385271, by rfl⟩ : syracuseStep 513695 = 770543) B770543
theorem B3335423 : Blo 338752 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B2910077 : Blo 338752 2910077 := bstep (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) B1091279
theorem B1732103 : Blo 338752 1732103 := bstep (se 1 (by rfl) ⟨1299077, by rfl⟩ : syracuseStep 1732103 = 2598155) B2598155
theorem B6846893 : Blo 338752 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B6716515 : Blo 338752 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B11110439 : Blo 338752 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B1151009 : Blo 338752 1151009 := bstep (se 2 (by rfl) ⟨431628, by rfl⟩ : syracuseStep 1151009 = 863257) B863257
theorem B1940051 : Blo 338752 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B1154735 : Blo 338752 1154735 := bstep (se 1 (by rfl) ⟨866051, by rfl⟩ : syracuseStep 1154735 = 1732103) B1732103
theorem B860159 : Blo 338752 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B8955353 : Blo 338752 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B4564595 : Blo 338752 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B863743 : Blo 338752 863743 := bstep (se 1 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 863743 = 1295615) B1295615
theorem B1291423 : Blo 338752 1291423 := bstep (se 1 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 1291423 = 1937135) B1937135
theorem B8894461 : Blo 338752 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B342463 : Blo 338752 342463 := bstep (se 1 (by rfl) ⟨256847, by rfl⟩ : syracuseStep 342463 = 513695) B513695
theorem B4962799 : Blo 338752 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B770651 : Blo 338752 770651 := bstep (se 1 (by rfl) ⟨577988, by rfl⟩ : syracuseStep 770651 = 1155977) B1155977
theorem B509951 : Blo 338752 509951 := bstep (se 1 (by rfl) ⟨382463, by rfl⟩ : syracuseStep 509951 = 764927) B764927
theorem B5229527 : Blo 338752 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B512159 : Blo 338752 512159 := bstep (se 1 (by rfl) ⟨384119, by rfl⟩ : syracuseStep 512159 = 768239) B768239
theorem B513263 : Blo 338752 513263 := bstep (se 1 (by rfl) ⟨384947, by rfl⟩ : syracuseStep 513263 = 769895) B769895
theorem B383719 : Blo 338752 383719 := bstep (se 1 (by rfl) ⟨287789, by rfl⟩ : syracuseStep 383719 = 575579) B575579
theorem B581375 : Blo 338752 581375 := bstep (se 1 (by rfl) ⟨436031, by rfl⟩ : syracuseStep 581375 = 872063) B872063
theorem B2452265 : Blo 338752 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B1931759 : Blo 338752 1931759 := bstep (se 1 (by rfl) ⟨1448819, by rfl⟩ : syracuseStep 1931759 = 2897639) B2897639
theorem B7406959 : Blo 338752 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B1151657 : Blo 338752 1151657 := bstep (se 2 (by rfl) ⟨431871, by rfl⟩ : syracuseStep 1151657 = 863743) B863743
theorem B5970235 : Blo 338752 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B1287839 : Blo 338752 1287839 := bstep (se 1 (by rfl) ⟨965879, by rfl⟩ : syracuseStep 1287839 = 1931759) B1931759
theorem B1550333 : Blo 338752 1550333 := bstep (se 3 (by rfl) ⟨290687, by rfl⟩ : syracuseStep 1550333 = 581375) B581375
theorem B339967 : Blo 338752 339967 := bstep (se 1 (by rfl) ⟨254975, by rfl⟩ : syracuseStep 339967 = 509951) B509951
theorem B767339 : Blo 338752 767339 := bstep (se 1 (by rfl) ⟨575504, by rfl⟩ : syracuseStep 767339 = 1151009) B1151009
theorem B341439 : Blo 338752 341439 := bstep (se 1 (by rfl) ⟨256079, by rfl⟩ : syracuseStep 341439 = 512159) B512159
theorem B342175 : Blo 338752 342175 := bstep (se 1 (by rfl) ⟨256631, by rfl⟩ : syracuseStep 342175 = 513263) B513263
theorem B1293367 : Blo 338752 1293367 := bstep (se 1 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 1293367 = 1940051) B1940051
theorem B769823 : Blo 338752 769823 := bstep (se 1 (by rfl) ⟨577367, by rfl⟩ : syracuseStep 769823 = 1154735) B1154735
theorem B573439 : Blo 338752 573439 := bstep (se 1 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 573439 = 860159) B860159
theorem B1721897 : Blo 338752 1721897 := bstep (se 2 (by rfl) ⟨645711, by rfl⟩ : syracuseStep 1721897 = 1291423) B1291423
theorem B13945405 : Blo 338752 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B511625 : Blo 338752 511625 := bstep (se 2 (by rfl) ⟨191859, by rfl⟩ : syracuseStep 511625 = 383719) B383719
theorem B513767 : Blo 338752 513767 := bstep (se 1 (by rfl) ⟨385325, by rfl⟩ : syracuseStep 513767 = 770651) B770651
theorem B3043063 : Blo 338752 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B1634843 : Blo 338752 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B11859281 : Blo 338752 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B6617065 : Blo 338752 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B1147931 : Blo 338752 1147931 := bstep (se 1 (by rfl) ⟨860948, by rfl⟩ : syracuseStep 1147931 = 1721897) B1721897
theorem B4359581 : Blo 338752 4359581 := bstep (se 3 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 4359581 = 1634843) B1634843
theorem B858559 : Blo 338752 858559 := bstep (se 1 (by rfl) ⟨643919, by rfl⟩ : syracuseStep 858559 = 1287839) B1287839
theorem B8822753 : Blo 338752 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B7906187 : Blo 338752 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B764585 : Blo 338752 764585 := bstep (se 2 (by rfl) ⟨286719, by rfl⟩ : syracuseStep 764585 = 573439) B573439
theorem B9875945 : Blo 338752 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B341083 : Blo 338752 341083 := bstep (se 1 (by rfl) ⟨255812, by rfl⟩ : syracuseStep 341083 = 511625) B511625
theorem B767771 : Blo 338752 767771 := bstep (se 1 (by rfl) ⟨575828, by rfl⟩ : syracuseStep 767771 = 1151657) B1151657
theorem B18593873 : Blo 338752 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B342511 : Blo 338752 342511 := bstep (se 1 (by rfl) ⟨256883, by rfl⟩ : syracuseStep 342511 = 513767) B513767
theorem B1033555 : Blo 338752 1033555 := bstep (se 1 (by rfl) ⟨775166, by rfl⟩ : syracuseStep 1033555 = 1550333) B1550333
theorem B511559 : Blo 338752 511559 := bstep (se 1 (by rfl) ⟨383669, by rfl⟩ : syracuseStep 511559 = 767339) B767339
theorem B1724489 : Blo 338752 1724489 := bstep (se 2 (by rfl) ⟨646683, by rfl⟩ : syracuseStep 1724489 = 1293367) B1293367
theorem B513215 : Blo 338752 513215 := bstep (se 1 (by rfl) ⟨384911, by rfl⟩ : syracuseStep 513215 = 769823) B769823
theorem B4057417 : Blo 338752 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B7960313 : Blo 338752 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B1378073 : Blo 338752 1378073 := bstep (se 2 (by rfl) ⟨516777, by rfl⟩ : syracuseStep 1378073 = 1033555) B1033555
theorem B1149659 : Blo 338752 1149659 := bstep (se 1 (by rfl) ⟨862244, by rfl⟩ : syracuseStep 1149659 = 1724489) B1724489
theorem B12395915 : Blo 338752 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B765287 : Blo 338752 765287 := bstep (se 1 (by rfl) ⟨573965, by rfl⟩ : syracuseStep 765287 = 1147931) B1147931
theorem B21639557 : Blo 338752 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B341039 : Blo 338752 341039 := bstep (se 1 (by rfl) ⟨255779, by rfl⟩ : syracuseStep 341039 = 511559) B511559
theorem B342143 : Blo 338752 342143 := bstep (se 1 (by rfl) ⟨256607, by rfl⟩ : syracuseStep 342143 = 513215) B513215
theorem B5881835 : Blo 338752 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B509723 : Blo 338752 509723 := bstep (se 1 (by rfl) ⟨382292, by rfl⟩ : syracuseStep 509723 = 764585) B764585
theorem B511847 : Blo 338752 511847 := bstep (se 1 (by rfl) ⟨383885, by rfl⟩ : syracuseStep 511847 = 767771) B767771
theorem B2906387 : Blo 338752 2906387 := bstep (se 1 (by rfl) ⟨2179790, by rfl⟩ : syracuseStep 2906387 = 4359581) B4359581
theorem B21227501 : Blo 338752 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B5270791 : Blo 338752 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B6583963 : Blo 338752 6583963 := bstep (se 1 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 6583963 = 9875945) B9875945
theorem B1144745 : Blo 338752 1144745 := bstep (se 2 (by rfl) ⟨429279, by rfl⟩ : syracuseStep 1144745 = 858559) B858559
theorem B918715 : Blo 338752 918715 := bstep (se 1 (by rfl) ⟨689036, by rfl⟩ : syracuseStep 918715 = 1378073) B1378073
theorem B1937591 : Blo 338752 1937591 := bstep (se 1 (by rfl) ⟨1453193, by rfl⟩ : syracuseStep 1937591 = 2906387) B2906387
theorem B8263943 : Blo 338752 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B14426371 : Blo 338752 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B763163 : Blo 338752 763163 := bstep (se 1 (by rfl) ⟨572372, by rfl⟩ : syracuseStep 763163 = 1144745) B1144745
theorem B339815 : Blo 338752 339815 := bstep (se 1 (by rfl) ⟨254861, by rfl⟩ : syracuseStep 339815 = 509723) B509723
theorem B766439 : Blo 338752 766439 := bstep (se 1 (by rfl) ⟨574829, by rfl⟩ : syracuseStep 766439 = 1149659) B1149659
theorem B341231 : Blo 338752 341231 := bstep (se 1 (by rfl) ⟨255923, by rfl⟩ : syracuseStep 341231 = 511847) B511847
theorem B7027721 : Blo 338752 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B510191 : Blo 338752 510191 := bstep (se 1 (by rfl) ⟨382643, by rfl⟩ : syracuseStep 510191 = 765287) B765287
theorem B3921223 : Blo 338752 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B14151667 : Blo 338752 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B8778617 : Blo 338752 8778617 := bstep (se 2 (by rfl) ⟨3291981, by rfl⟩ : syracuseStep 8778617 = 6583963) B6583963
theorem B19235161 : Blo 338752 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B5509295 : Blo 338752 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B340127 : Blo 338752 340127 := bstep (se 1 (by rfl) ⟨255095, by rfl⟩ : syracuseStep 340127 = 510191) B510191
theorem B1224953 : Blo 338752 1224953 := bstep (se 2 (by rfl) ⟨459357, by rfl⟩ : syracuseStep 1224953 = 918715) B918715
theorem B1291727 : Blo 338752 1291727 := bstep (se 1 (by rfl) ⟨968795, by rfl⟩ : syracuseStep 1291727 = 1937591) B1937591
theorem B508775 : Blo 338752 508775 := bstep (se 1 (by rfl) ⟨381581, by rfl⟩ : syracuseStep 508775 = 763163) B763163
theorem B5228297 : Blo 338752 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B510959 : Blo 338752 510959 := bstep (se 1 (by rfl) ⟨383219, by rfl⟩ : syracuseStep 510959 = 766439) B766439
theorem B5852411 : Blo 338752 5852411 := bstep (se 1 (by rfl) ⟨4389308, by rfl⟩ : syracuseStep 5852411 = 8778617) B8778617
theorem B18868889 : Blo 338752 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B4685147 : Blo 338752 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B3901607 : Blo 338752 3901607 := bstep (se 1 (by rfl) ⟨2926205, by rfl⟩ : syracuseStep 3901607 = 5852411) B5852411
theorem B3672863 : Blo 338752 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B861151 : Blo 338752 861151 := bstep (se 1 (by rfl) ⟨645863, by rfl⟩ : syracuseStep 861151 = 1291727) B1291727
theorem B3123431 : Blo 338752 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B339183 : Blo 338752 339183 := bstep (se 1 (by rfl) ⟨254387, by rfl⟩ : syracuseStep 339183 = 508775) B508775
theorem B3485531 : Blo 338752 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B340639 : Blo 338752 340639 := bstep (se 1 (by rfl) ⟨255479, by rfl⟩ : syracuseStep 340639 = 510959) B510959
theorem B25646881 : Blo 338752 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B12579259 : Blo 338752 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B816635 : Blo 338752 816635 := bstep (se 1 (by rfl) ⟨612476, by rfl⟩ : syracuseStep 816635 = 1224953) B1224953
theorem B1148201 : Blo 338752 1148201 := bstep (se 2 (by rfl) ⟨430575, by rfl⟩ : syracuseStep 1148201 = 861151) B861151
theorem B2601071 : Blo 338752 2601071 := bstep (se 1 (by rfl) ⟨1950803, by rfl⟩ : syracuseStep 2601071 = 3901607) B3901607
theorem B2082287 : Blo 338752 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B34195841 : Blo 338752 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B544423 : Blo 338752 544423 := bstep (se 1 (by rfl) ⟨408317, by rfl⟩ : syracuseStep 544423 = 816635) B816635
theorem B9294749 : Blo 338752 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B2448575 : Blo 338752 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B16772345 : Blo 338752 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B6196499 : Blo 338752 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B725897 : Blo 338752 725897 := bstep (se 2 (by rfl) ⟨272211, by rfl⟩ : syracuseStep 725897 = 544423) B544423
theorem B11181563 : Blo 338752 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B765467 : Blo 338752 765467 := bstep (se 1 (by rfl) ⟨574100, by rfl⟩ : syracuseStep 765467 = 1148201) B1148201
theorem B1388191 : Blo 338752 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B22797227 : Blo 338752 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B1632383 : Blo 338752 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B1734047 : Blo 338752 1734047 := bstep (se 1 (by rfl) ⟨1300535, by rfl⟩ : syracuseStep 1734047 = 2601071) B2601071
theorem B4130999 : Blo 338752 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B1088255 : Blo 338752 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B1156031 : Blo 338752 1156031 := bstep (se 1 (by rfl) ⟨867023, by rfl⟩ : syracuseStep 1156031 = 1734047) B1734047
theorem B1850921 : Blo 338752 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B7454375 : Blo 338752 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B510311 : Blo 338752 510311 := bstep (se 1 (by rfl) ⟨382733, by rfl⟩ : syracuseStep 510311 = 765467) B765467
theorem B483931 : Blo 338752 483931 := bstep (se 1 (by rfl) ⟨362948, by rfl⟩ : syracuseStep 483931 = 725897) B725897
theorem B15198151 : Blo 338752 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B2753999 : Blo 338752 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B340207 : Blo 338752 340207 := bstep (se 1 (by rfl) ⟨255155, by rfl⟩ : syracuseStep 340207 = 510311) B510311
theorem B20264201 : Blo 338752 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B770687 : Blo 338752 770687 := bstep (se 1 (by rfl) ⟨578015, by rfl⟩ : syracuseStep 770687 = 1156031) B1156031
theorem B2902013 : Blo 338752 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B1233947 : Blo 338752 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B4969583 : Blo 338752 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B645241 : Blo 338752 645241 := bstep (se 2 (by rfl) ⟨241965, by rfl⟩ : syracuseStep 645241 = 483931) B483931
theorem B1835999 : Blo 338752 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B1934675 : Blo 338752 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B822631 : Blo 338752 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B3313055 : Blo 338752 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B860321 : Blo 338752 860321 := bstep (se 2 (by rfl) ⟨322620, by rfl⟩ : syracuseStep 860321 = 645241) B645241
theorem B13509467 : Blo 338752 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B513791 : Blo 338752 513791 := bstep (se 1 (by rfl) ⟨385343, by rfl⟩ : syracuseStep 513791 = 770687) B770687
theorem B1223999 : Blo 338752 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B1289783 : Blo 338752 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B2208703 : Blo 338752 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B342527 : Blo 338752 342527 := bstep (se 1 (by rfl) ⟨256895, by rfl⟩ : syracuseStep 342527 = 513791) B513791
theorem B1096841 : Blo 338752 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B573547 : Blo 338752 573547 := bstep (se 1 (by rfl) ⟨430160, by rfl⟩ : syracuseStep 573547 = 860321) B860321
theorem B9006311 : Blo 338752 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B6004207 : Blo 338752 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B859855 : Blo 338752 859855 := bstep (se 1 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 859855 = 1289783) B1289783
theorem B2924909 : Blo 338752 2924909 := bstep (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) B1096841
theorem B764729 : Blo 338752 764729 := bstep (se 2 (by rfl) ⟨286773, by rfl⟩ : syracuseStep 764729 = 573547) B573547
theorem B2944937 : Blo 338752 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B815999 : Blo 338752 815999 := bstep (se 1 (by rfl) ⟨611999, by rfl⟩ : syracuseStep 815999 = 1223999) B1223999
theorem B8005609 : Blo 338752 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B2175997 : Blo 338752 2175997 := bstep (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) B815999
theorem B1949939 : Blo 338752 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B509819 : Blo 338752 509819 := bstep (se 1 (by rfl) ⟨382364, by rfl⟩ : syracuseStep 509819 = 764729) B764729
theorem B1963291 : Blo 338752 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B1146473 : Blo 338752 1146473 := bstep (se 2 (by rfl) ⟨429927, by rfl⟩ : syracuseStep 1146473 = 859855) B859855
theorem B764315 : Blo 338752 764315 := bstep (se 1 (by rfl) ⟨573236, by rfl⟩ : syracuseStep 764315 = 1146473) B1146473
theorem B339879 : Blo 338752 339879 := bstep (se 1 (by rfl) ⟨254909, by rfl⟩ : syracuseStep 339879 = 509819) B509819
theorem B2901329 : Blo 338752 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B1299959 : Blo 338752 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B10674145 : Blo 338752 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B2617721 : Blo 338752 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B1934219 : Blo 338752 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B1745147 : Blo 338752 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B14232193 : Blo 338752 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B866639 : Blo 338752 866639 := bstep (se 1 (by rfl) ⟨649979, by rfl⟩ : syracuseStep 866639 = 1299959) B1299959
theorem B509543 : Blo 338752 509543 := bstep (se 1 (by rfl) ⟨382157, by rfl⟩ : syracuseStep 509543 = 764315) B764315
theorem B1289479 : Blo 338752 1289479 := bstep (se 1 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 1289479 = 1934219) B1934219
theorem B339695 : Blo 338752 339695 := bstep (se 1 (by rfl) ⟨254771, by rfl⟩ : syracuseStep 339695 = 509543) B509543
theorem B75905029 : Blo 338752 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B1163431 : Blo 338752 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B577759 : Blo 338752 577759 := bstep (se 1 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 577759 = 866639) B866639
theorem B1551241 : Blo 338752 1551241 := bstep (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) B1163431
theorem B1719305 : Blo 338752 1719305 := bstep (se 2 (by rfl) ⟨644739, by rfl⟩ : syracuseStep 1719305 = 1289479) B1289479
theorem B770345 : Blo 338752 770345 := bstep (se 2 (by rfl) ⟨288879, by rfl⟩ : syracuseStep 770345 = 577759) B577759
theorem B101206705 : Blo 338752 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B134942273 : Blo 338752 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B8273285 : Blo 338752 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B513563 : Blo 338752 513563 := bstep (se 1 (by rfl) ⟨385172, by rfl⟩ : syracuseStep 513563 = 770345) B770345
theorem B1146203 : Blo 338752 1146203 := bstep (se 1 (by rfl) ⟨859652, by rfl⟩ : syracuseStep 1146203 = 1719305) B1719305
theorem B764135 : Blo 338752 764135 := bstep (se 1 (by rfl) ⟨573101, by rfl⟩ : syracuseStep 764135 = 1146203) B1146203
theorem B5515523 : Blo 338752 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B89961515 : Blo 338752 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B342375 : Blo 338752 342375 := bstep (se 1 (by rfl) ⟨256781, by rfl⟩ : syracuseStep 342375 = 513563) B513563
theorem B3677015 : Blo 338752 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B59974343 : Blo 338752 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B509423 : Blo 338752 509423 := bstep (se 1 (by rfl) ⟨382067, by rfl⟩ : syracuseStep 509423 = 764135) B764135
theorem B39982895 : Blo 338752 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B339615 : Blo 338752 339615 := bstep (se 1 (by rfl) ⟨254711, by rfl⟩ : syracuseStep 339615 = 509423) B509423
theorem B2451343 : Blo 338752 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B26655263 : Blo 338752 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B3268457 : Blo 338752 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B17770175 : Blo 338752 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B2178971 : Blo 338752 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B1452647 : Blo 338752 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B11846783 : Blo 338752 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B31591421 : Blo 338752 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B968431 : Blo 338752 968431 := bstep (se 1 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 968431 = 1452647) B1452647
theorem B1291241 : Blo 338752 1291241 := bstep (se 2 (by rfl) ⟨484215, by rfl⟩ : syracuseStep 1291241 = 968431) B968431
theorem B21060947 : Blo 338752 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B860827 : Blo 338752 860827 := bstep (se 1 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 860827 = 1291241) B1291241
theorem B14040631 : Blo 338752 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B1147769 : Blo 338752 1147769 := bstep (se 2 (by rfl) ⟨430413, by rfl⟩ : syracuseStep 1147769 = 860827) B860827
theorem B18720841 : Blo 338752 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B765179 : Blo 338752 765179 := bstep (se 1 (by rfl) ⟨573884, by rfl⟩ : syracuseStep 765179 = 1147769) B1147769
theorem B24961121 : Blo 338752 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B510119 : Blo 338752 510119 := bstep (se 1 (by rfl) ⟨382589, by rfl⟩ : syracuseStep 510119 = 765179) B765179
theorem B16640747 : Blo 338752 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B340079 : Blo 338752 340079 := bstep (se 1 (by rfl) ⟨255059, by rfl⟩ : syracuseStep 340079 = 510119) B510119
theorem B11093831 : Blo 338752 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B7395887 : Blo 338752 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B19722365 : Blo 338752 19722365 := bstep (se 3 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 19722365 = 7395887) B7395887
theorem B13148243 : Blo 338752 13148243 := bstep (se 1 (by rfl) ⟨9861182, by rfl⟩ : syracuseStep 13148243 = 19722365) B19722365
theorem B8765495 : Blo 338752 8765495 := bstep (se 1 (by rfl) ⟨6574121, by rfl⟩ : syracuseStep 8765495 = 13148243) B13148243
theorem B5843663 : Blo 338752 5843663 := bstep (se 1 (by rfl) ⟨4382747, by rfl⟩ : syracuseStep 5843663 = 8765495) B8765495
theorem B3895775 : Blo 338752 3895775 := bstep (se 1 (by rfl) ⟨2921831, by rfl⟩ : syracuseStep 3895775 = 5843663) B5843663
theorem B2597183 : Blo 338752 2597183 := bstep (se 1 (by rfl) ⟨1947887, by rfl⟩ : syracuseStep 2597183 = 3895775) B3895775
theorem B1731455 : Blo 338752 1731455 := bstep (se 1 (by rfl) ⟨1298591, by rfl⟩ : syracuseStep 1731455 = 2597183) B2597183
theorem B1154303 : Blo 338752 1154303 := bstep (se 1 (by rfl) ⟨865727, by rfl⟩ : syracuseStep 1154303 = 1731455) B1731455
theorem B769535 : Blo 338752 769535 := bstep (se 1 (by rfl) ⟨577151, by rfl⟩ : syracuseStep 769535 = 1154303) B1154303
theorem B513023 : Blo 338752 513023 := bstep (se 1 (by rfl) ⟨384767, by rfl⟩ : syracuseStep 513023 = 769535) B769535
theorem B342015 : Blo 338752 342015 := bstep (se 1 (by rfl) ⟨256511, by rfl⟩ : syracuseStep 342015 = 513023) B513023

theorem C0 (j : ℕ) (h1 : 84688 ≤ j) (h2 : j ≤ 85387) : Blo 338752 (4 * j + 3) := by
  interval_cases j
  · exact B338755
  · exact B338759
  · exact B338763
  · exact B338767
  · exact B338771
  · exact B338775
  · exact B338779
  · exact B338783
  · exact B338787
  · exact B338791
  · exact B338795
  · exact B338799
  · exact B338803
  · exact B338807
  · exact B338811
  · exact B338815
  · exact B338819
  · exact B338823
  · exact B338827
  · exact B338831
  · exact B338835
  · exact B338839
  · exact B338843
  · exact B338847
  · exact B338851
  · exact B338855
  · exact B338859
  · exact B338863
  · exact B338867
  · exact B338871
  · exact B338875
  · exact B338879
  · exact B338883
  · exact B338887
  · exact B338891
  · exact B338895
  · exact B338899
  · exact B338903
  · exact B338907
  · exact B338911
  · exact B338915
  · exact B338919
  · exact B338923
  · exact B338927
  · exact B338931
  · exact B338935
  · exact B338939
  · exact B338943
  · exact B338947
  · exact B338951
  · exact B338955
  · exact B338959
  · exact B338963
  · exact B338967
  · exact B338971
  · exact B338975
  · exact B338979
  · exact B338983
  · exact B338987
  · exact B338991
  · exact B338995
  · exact B338999
  · exact B339003
  · exact B339007
  · exact B339011
  · exact B339015
  · exact B339019
  · exact B339023
  · exact B339027
  · exact B339031
  · exact B339035
  · exact B339039
  · exact B339043
  · exact B339047
  · exact B339051
  · exact B339055
  · exact B339059
  · exact B339063
  · exact B339067
  · exact B339071
  · exact B339075
  · exact B339079
  · exact B339083
  · exact B339087
  · exact B339091
  · exact B339095
  · exact B339099
  · exact B339103
  · exact B339107
  · exact B339111
  · exact B339115
  · exact B339119
  · exact B339123
  · exact B339127
  · exact B339131
  · exact B339135
  · exact B339139
  · exact B339143
  · exact B339147
  · exact B339151
  · exact B339155
  · exact B339159
  · exact B339163
  · exact B339167
  · exact B339171
  · exact B339175
  · exact B339179
  · exact B339183
  · exact B339187
  · exact B339191
  · exact B339195
  · exact B339199
  · exact B339203
  · exact B339207
  · exact B339211
  · exact B339215
  · exact B339219
  · exact B339223
  · exact B339227
  · exact B339231
  · exact B339235
  · exact B339239
  · exact B339243
  · exact B339247
  · exact B339251
  · exact B339255
  · exact B339259
  · exact B339263
  · exact B339267
  · exact B339271
  · exact B339275
  · exact B339279
  · exact B339283
  · exact B339287
  · exact B339291
  · exact B339295
  · exact B339299
  · exact B339303
  · exact B339307
  · exact B339311
  · exact B339315
  · exact B339319
  · exact B339323
  · exact B339327
  · exact B339331
  · exact B339335
  · exact B339339
  · exact B339343
  · exact B339347
  · exact B339351
  · exact B339355
  · exact B339359
  · exact B339363
  · exact B339367
  · exact B339371
  · exact B339375
  · exact B339379
  · exact B339383
  · exact B339387
  · exact B339391
  · exact B339395
  · exact B339399
  · exact B339403
  · exact B339407
  · exact B339411
  · exact B339415
  · exact B339419
  · exact B339423
  · exact B339427
  · exact B339431
  · exact B339435
  · exact B339439
  · exact B339443
  · exact B339447
  · exact B339451
  · exact B339455
  · exact B339459
  · exact B339463
  · exact B339467
  · exact B339471
  · exact B339475
  · exact B339479
  · exact B339483
  · exact B339487
  · exact B339491
  · exact B339495
  · exact B339499
  · exact B339503
  · exact B339507
  · exact B339511
  · exact B339515
  · exact B339519
  · exact B339523
  · exact B339527
  · exact B339531
  · exact B339535
  · exact B339539
  · exact B339543
  · exact B339547
  · exact B339551
  · exact B339555
  · exact B339559
  · exact B339563
  · exact B339567
  · exact B339571
  · exact B339575
  · exact B339579
  · exact B339583
  · exact B339587
  · exact B339591
  · exact B339595
  · exact B339599
  · exact B339603
  · exact B339607
  · exact B339611
  · exact B339615
  · exact B339619
  · exact B339623
  · exact B339627
  · exact B339631
  · exact B339635
  · exact B339639
  · exact B339643
  · exact B339647
  · exact B339651
  · exact B339655
  · exact B339659
  · exact B339663
  · exact B339667
  · exact B339671
  · exact B339675
  · exact B339679
  · exact B339683
  · exact B339687
  · exact B339691
  · exact B339695
  · exact B339699
  · exact B339703
  · exact B339707
  · exact B339711
  · exact B339715
  · exact B339719
  · exact B339723
  · exact B339727
  · exact B339731
  · exact B339735
  · exact B339739
  · exact B339743
  · exact B339747
  · exact B339751
  · exact B339755
  · exact B339759
  · exact B339763
  · exact B339767
  · exact B339771
  · exact B339775
  · exact B339779
  · exact B339783
  · exact B339787
  · exact B339791
  · exact B339795
  · exact B339799
  · exact B339803
  · exact B339807
  · exact B339811
  · exact B339815
  · exact B339819
  · exact B339823
  · exact B339827
  · exact B339831
  · exact B339835
  · exact B339839
  · exact B339843
  · exact B339847
  · exact B339851
  · exact B339855
  · exact B339859
  · exact B339863
  · exact B339867
  · exact B339871
  · exact B339875
  · exact B339879
  · exact B339883
  · exact B339887
  · exact B339891
  · exact B339895
  · exact B339899
  · exact B339903
  · exact B339907
  · exact B339911
  · exact B339915
  · exact B339919
  · exact B339923
  · exact B339927
  · exact B339931
  · exact B339935
  · exact B339939
  · exact B339943
  · exact B339947
  · exact B339951
  · exact B339955
  · exact B339959
  · exact B339963
  · exact B339967
  · exact B339971
  · exact B339975
  · exact B339979
  · exact B339983
  · exact B339987
  · exact B339991
  · exact B339995
  · exact B339999
  · exact B340003
  · exact B340007
  · exact B340011
  · exact B340015
  · exact B340019
  · exact B340023
  · exact B340027
  · exact B340031
  · exact B340035
  · exact B340039
  · exact B340043
  · exact B340047
  · exact B340051
  · exact B340055
  · exact B340059
  · exact B340063
  · exact B340067
  · exact B340071
  · exact B340075
  · exact B340079
  · exact B340083
  · exact B340087
  · exact B340091
  · exact B340095
  · exact B340099
  · exact B340103
  · exact B340107
  · exact B340111
  · exact B340115
  · exact B340119
  · exact B340123
  · exact B340127
  · exact B340131
  · exact B340135
  · exact B340139
  · exact B340143
  · exact B340147
  · exact B340151
  · exact B340155
  · exact B340159
  · exact B340163
  · exact B340167
  · exact B340171
  · exact B340175
  · exact B340179
  · exact B340183
  · exact B340187
  · exact B340191
  · exact B340195
  · exact B340199
  · exact B340203
  · exact B340207
  · exact B340211
  · exact B340215
  · exact B340219
  · exact B340223
  · exact B340227
  · exact B340231
  · exact B340235
  · exact B340239
  · exact B340243
  · exact B340247
  · exact B340251
  · exact B340255
  · exact B340259
  · exact B340263
  · exact B340267
  · exact B340271
  · exact B340275
  · exact B340279
  · exact B340283
  · exact B340287
  · exact B340291
  · exact B340295
  · exact B340299
  · exact B340303
  · exact B340307
  · exact B340311
  · exact B340315
  · exact B340319
  · exact B340323
  · exact B340327
  · exact B340331
  · exact B340335
  · exact B340339
  · exact B340343
  · exact B340347
  · exact B340351
  · exact B340355
  · exact B340359
  · exact B340363
  · exact B340367
  · exact B340371
  · exact B340375
  · exact B340379
  · exact B340383
  · exact B340387
  · exact B340391
  · exact B340395
  · exact B340399
  · exact B340403
  · exact B340407
  · exact B340411
  · exact B340415
  · exact B340419
  · exact B340423
  · exact B340427
  · exact B340431
  · exact B340435
  · exact B340439
  · exact B340443
  · exact B340447
  · exact B340451
  · exact B340455
  · exact B340459
  · exact B340463
  · exact B340467
  · exact B340471
  · exact B340475
  · exact B340479
  · exact B340483
  · exact B340487
  · exact B340491
  · exact B340495
  · exact B340499
  · exact B340503
  · exact B340507
  · exact B340511
  · exact B340515
  · exact B340519
  · exact B340523
  · exact B340527
  · exact B340531
  · exact B340535
  · exact B340539
  · exact B340543
  · exact B340547
  · exact B340551
  · exact B340555
  · exact B340559
  · exact B340563
  · exact B340567
  · exact B340571
  · exact B340575
  · exact B340579
  · exact B340583
  · exact B340587
  · exact B340591
  · exact B340595
  · exact B340599
  · exact B340603
  · exact B340607
  · exact B340611
  · exact B340615
  · exact B340619
  · exact B340623
  · exact B340627
  · exact B340631
  · exact B340635
  · exact B340639
  · exact B340643
  · exact B340647
  · exact B340651
  · exact B340655
  · exact B340659
  · exact B340663
  · exact B340667
  · exact B340671
  · exact B340675
  · exact B340679
  · exact B340683
  · exact B340687
  · exact B340691
  · exact B340695
  · exact B340699
  · exact B340703
  · exact B340707
  · exact B340711
  · exact B340715
  · exact B340719
  · exact B340723
  · exact B340727
  · exact B340731
  · exact B340735
  · exact B340739
  · exact B340743
  · exact B340747
  · exact B340751
  · exact B340755
  · exact B340759
  · exact B340763
  · exact B340767
  · exact B340771
  · exact B340775
  · exact B340779
  · exact B340783
  · exact B340787
  · exact B340791
  · exact B340795
  · exact B340799
  · exact B340803
  · exact B340807
  · exact B340811
  · exact B340815
  · exact B340819
  · exact B340823
  · exact B340827
  · exact B340831
  · exact B340835
  · exact B340839
  · exact B340843
  · exact B340847
  · exact B340851
  · exact B340855
  · exact B340859
  · exact B340863
  · exact B340867
  · exact B340871
  · exact B340875
  · exact B340879
  · exact B340883
  · exact B340887
  · exact B340891
  · exact B340895
  · exact B340899
  · exact B340903
  · exact B340907
  · exact B340911
  · exact B340915
  · exact B340919
  · exact B340923
  · exact B340927
  · exact B340931
  · exact B340935
  · exact B340939
  · exact B340943
  · exact B340947
  · exact B340951
  · exact B340955
  · exact B340959
  · exact B340963
  · exact B340967
  · exact B340971
  · exact B340975
  · exact B340979
  · exact B340983
  · exact B340987
  · exact B340991
  · exact B340995
  · exact B340999
  · exact B341003
  · exact B341007
  · exact B341011
  · exact B341015
  · exact B341019
  · exact B341023
  · exact B341027
  · exact B341031
  · exact B341035
  · exact B341039
  · exact B341043
  · exact B341047
  · exact B341051
  · exact B341055
  · exact B341059
  · exact B341063
  · exact B341067
  · exact B341071
  · exact B341075
  · exact B341079
  · exact B341083
  · exact B341087
  · exact B341091
  · exact B341095
  · exact B341099
  · exact B341103
  · exact B341107
  · exact B341111
  · exact B341115
  · exact B341119
  · exact B341123
  · exact B341127
  · exact B341131
  · exact B341135
  · exact B341139
  · exact B341143
  · exact B341147
  · exact B341151
  · exact B341155
  · exact B341159
  · exact B341163
  · exact B341167
  · exact B341171
  · exact B341175
  · exact B341179
  · exact B341183
  · exact B341187
  · exact B341191
  · exact B341195
  · exact B341199
  · exact B341203
  · exact B341207
  · exact B341211
  · exact B341215
  · exact B341219
  · exact B341223
  · exact B341227
  · exact B341231
  · exact B341235
  · exact B341239
  · exact B341243
  · exact B341247
  · exact B341251
  · exact B341255
  · exact B341259
  · exact B341263
  · exact B341267
  · exact B341271
  · exact B341275
  · exact B341279
  · exact B341283
  · exact B341287
  · exact B341291
  · exact B341295
  · exact B341299
  · exact B341303
  · exact B341307
  · exact B341311
  · exact B341315
  · exact B341319
  · exact B341323
  · exact B341327
  · exact B341331
  · exact B341335
  · exact B341339
  · exact B341343
  · exact B341347
  · exact B341351
  · exact B341355
  · exact B341359
  · exact B341363
  · exact B341367
  · exact B341371
  · exact B341375
  · exact B341379
  · exact B341383
  · exact B341387
  · exact B341391
  · exact B341395
  · exact B341399
  · exact B341403
  · exact B341407
  · exact B341411
  · exact B341415
  · exact B341419
  · exact B341423
  · exact B341427
  · exact B341431
  · exact B341435
  · exact B341439
  · exact B341443
  · exact B341447
  · exact B341451
  · exact B341455
  · exact B341459
  · exact B341463
  · exact B341467
  · exact B341471
  · exact B341475
  · exact B341479
  · exact B341483
  · exact B341487
  · exact B341491
  · exact B341495
  · exact B341499
  · exact B341503
  · exact B341507
  · exact B341511
  · exact B341515
  · exact B341519
  · exact B341523
  · exact B341527
  · exact B341531
  · exact B341535
  · exact B341539
  · exact B341543
  · exact B341547
  · exact B341551

theorem C1 (j : ℕ) (h1 : 85388 ≤ j) (h2 : j ≤ 85687) : Blo 338752 (4 * j + 3) := by
  interval_cases j
  · exact B341555
  · exact B341559
  · exact B341563
  · exact B341567
  · exact B341571
  · exact B341575
  · exact B341579
  · exact B341583
  · exact B341587
  · exact B341591
  · exact B341595
  · exact B341599
  · exact B341603
  · exact B341607
  · exact B341611
  · exact B341615
  · exact B341619
  · exact B341623
  · exact B341627
  · exact B341631
  · exact B341635
  · exact B341639
  · exact B341643
  · exact B341647
  · exact B341651
  · exact B341655
  · exact B341659
  · exact B341663
  · exact B341667
  · exact B341671
  · exact B341675
  · exact B341679
  · exact B341683
  · exact B341687
  · exact B341691
  · exact B341695
  · exact B341699
  · exact B341703
  · exact B341707
  · exact B341711
  · exact B341715
  · exact B341719
  · exact B341723
  · exact B341727
  · exact B341731
  · exact B341735
  · exact B341739
  · exact B341743
  · exact B341747
  · exact B341751
  · exact B341755
  · exact B341759
  · exact B341763
  · exact B341767
  · exact B341771
  · exact B341775
  · exact B341779
  · exact B341783
  · exact B341787
  · exact B341791
  · exact B341795
  · exact B341799
  · exact B341803
  · exact B341807
  · exact B341811
  · exact B341815
  · exact B341819
  · exact B341823
  · exact B341827
  · exact B341831
  · exact B341835
  · exact B341839
  · exact B341843
  · exact B341847
  · exact B341851
  · exact B341855
  · exact B341859
  · exact B341863
  · exact B341867
  · exact B341871
  · exact B341875
  · exact B341879
  · exact B341883
  · exact B341887
  · exact B341891
  · exact B341895
  · exact B341899
  · exact B341903
  · exact B341907
  · exact B341911
  · exact B341915
  · exact B341919
  · exact B341923
  · exact B341927
  · exact B341931
  · exact B341935
  · exact B341939
  · exact B341943
  · exact B341947
  · exact B341951
  · exact B341955
  · exact B341959
  · exact B341963
  · exact B341967
  · exact B341971
  · exact B341975
  · exact B341979
  · exact B341983
  · exact B341987
  · exact B341991
  · exact B341995
  · exact B341999
  · exact B342003
  · exact B342007
  · exact B342011
  · exact B342015
  · exact B342019
  · exact B342023
  · exact B342027
  · exact B342031
  · exact B342035
  · exact B342039
  · exact B342043
  · exact B342047
  · exact B342051
  · exact B342055
  · exact B342059
  · exact B342063
  · exact B342067
  · exact B342071
  · exact B342075
  · exact B342079
  · exact B342083
  · exact B342087
  · exact B342091
  · exact B342095
  · exact B342099
  · exact B342103
  · exact B342107
  · exact B342111
  · exact B342115
  · exact B342119
  · exact B342123
  · exact B342127
  · exact B342131
  · exact B342135
  · exact B342139
  · exact B342143
  · exact B342147
  · exact B342151
  · exact B342155
  · exact B342159
  · exact B342163
  · exact B342167
  · exact B342171
  · exact B342175
  · exact B342179
  · exact B342183
  · exact B342187
  · exact B342191
  · exact B342195
  · exact B342199
  · exact B342203
  · exact B342207
  · exact B342211
  · exact B342215
  · exact B342219
  · exact B342223
  · exact B342227
  · exact B342231
  · exact B342235
  · exact B342239
  · exact B342243
  · exact B342247
  · exact B342251
  · exact B342255
  · exact B342259
  · exact B342263
  · exact B342267
  · exact B342271
  · exact B342275
  · exact B342279
  · exact B342283
  · exact B342287
  · exact B342291
  · exact B342295
  · exact B342299
  · exact B342303
  · exact B342307
  · exact B342311
  · exact B342315
  · exact B342319
  · exact B342323
  · exact B342327
  · exact B342331
  · exact B342335
  · exact B342339
  · exact B342343
  · exact B342347
  · exact B342351
  · exact B342355
  · exact B342359
  · exact B342363
  · exact B342367
  · exact B342371
  · exact B342375
  · exact B342379
  · exact B342383
  · exact B342387
  · exact B342391
  · exact B342395
  · exact B342399
  · exact B342403
  · exact B342407
  · exact B342411
  · exact B342415
  · exact B342419
  · exact B342423
  · exact B342427
  · exact B342431
  · exact B342435
  · exact B342439
  · exact B342443
  · exact B342447
  · exact B342451
  · exact B342455
  · exact B342459
  · exact B342463
  · exact B342467
  · exact B342471
  · exact B342475
  · exact B342479
  · exact B342483
  · exact B342487
  · exact B342491
  · exact B342495
  · exact B342499
  · exact B342503
  · exact B342507
  · exact B342511
  · exact B342515
  · exact B342519
  · exact B342523
  · exact B342527
  · exact B342531
  · exact B342535
  · exact B342539
  · exact B342543
  · exact B342547
  · exact B342551
  · exact B342555
  · exact B342559
  · exact B342563
  · exact B342567
  · exact B342571
  · exact B342575
  · exact B342579
  · exact B342583
  · exact B342587
  · exact B342591
  · exact B342595
  · exact B342599
  · exact B342603
  · exact B342607
  · exact B342611
  · exact B342615
  · exact B342619
  · exact B342623
  · exact B342627
  · exact B342631
  · exact B342635
  · exact B342639
  · exact B342643
  · exact B342647
  · exact B342651
  · exact B342655
  · exact B342659
  · exact B342663
  · exact B342667
  · exact B342671
  · exact B342675
  · exact B342679
  · exact B342683
  · exact B342687
  · exact B342691
  · exact B342695
  · exact B342699
  · exact B342703
  · exact B342707
  · exact B342711
  · exact B342715
  · exact B342719
  · exact B342723
  · exact B342727
  · exact B342731
  · exact B342735
  · exact B342739
  · exact B342743
  · exact B342747
  · exact B342751

theorem solution (m : ℕ) (hlo : 338752 ≤ m) (hhi : m ≤ 342752) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 84688 ≤ j := by omega
    have hj2 : j ≤ 85687 := by omega
    have hb : Blo 338752 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 85388 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
