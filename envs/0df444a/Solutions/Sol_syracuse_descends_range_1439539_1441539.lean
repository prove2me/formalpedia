-- Prove2me | solution 1 for syracuse_descends_range_1439539_1441539
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:42:39.945015+00:00
-- url     : https://prove2.me/submissions/1a096e90-da17-4036-9a9a-4631e79b0ece

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


theorem B3645445 : Blo 1439539 3645445 := bbase (se 4 (by rfl) ⟨341760, by rfl⟩ : syracuseStep 3645445 = 683521) (by norm_num)
theorem B3285029 : Blo 1439539 3285029 := bbase (se 4 (by rfl) ⟨307971, by rfl⟩ : syracuseStep 3285029 = 615943) (by norm_num)
theorem B2736173 : Blo 1439539 2736173 := bbase (se 3 (by rfl) ⟨513032, by rfl⟩ : syracuseStep 2736173 = 1026065) (by norm_num)
theorem B3645557 : Blo 1439539 3645557 := bbase (se 5 (by rfl) ⟨170885, by rfl⟩ : syracuseStep 3645557 = 341771) (by norm_num)
theorem B6922421 : Blo 1439539 6922421 := bbase (se 5 (by rfl) ⟨324488, by rfl⟩ : syracuseStep 6922421 = 648977) (by norm_num)
theorem B2736317 : Blo 1439539 2736317 := bbase (se 3 (by rfl) ⟨513059, by rfl⟩ : syracuseStep 2736317 = 1026119) (by norm_num)
theorem B4382981 : Blo 1439539 4382981 := bbase (se 4 (by rfl) ⟨410904, by rfl⟩ : syracuseStep 4382981 = 821809) (by norm_num)
theorem B4612373 : Blo 1439539 4612373 := bbase (se 6 (by rfl) ⟨108102, by rfl⟩ : syracuseStep 4612373 = 216205) (by norm_num)
theorem B3506485 : Blo 1439539 3506485 := bbase (se 5 (by rfl) ⟨164366, by rfl⟩ : syracuseStep 3506485 = 328733) (by norm_num)
theorem B7012661 : Blo 1439539 7012661 := bbase (se 5 (by rfl) ⟨328718, by rfl⟩ : syracuseStep 7012661 = 657437) (by norm_num)
theorem B3645749 : Blo 1439539 3645749 := bbase (se 5 (by rfl) ⟨170894, by rfl⟩ : syracuseStep 3645749 = 341789) (by norm_num)
theorem B4104533 : Blo 1439539 4104533 := bbase (se 10 (by rfl) ⟨6012, by rfl⟩ : syracuseStep 4104533 = 12025) (by norm_num)
theorem B3285373 : Blo 1439539 3285373 := bbase (se 3 (by rfl) ⟨616007, by rfl⟩ : syracuseStep 3285373 = 1232015) (by norm_num)
theorem B2597285 : Blo 1439539 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B2736605 : Blo 1439539 2736605 := bbase (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) (by norm_num)
theorem B3646093 : Blo 1439539 3646093 := bbase (se 3 (by rfl) ⟨683642, by rfl⟩ : syracuseStep 3646093 = 1367285) (by norm_num)
theorem B8200885 : Blo 1439539 8200885 := bbase (se 5 (by rfl) ⟨384416, by rfl⟩ : syracuseStep 8200885 = 768833) (by norm_num)
theorem B10945205 : Blo 1439539 10945205 := bbase (se 5 (by rfl) ⟨513056, by rfl⟩ : syracuseStep 10945205 = 1026113) (by norm_num)
theorem B2630333 : Blo 1439539 2630333 := bbase (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) (by norm_num)
theorem B44360405 : Blo 1439539 44360405 := bbase (se 7 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 44360405 = 1039697) (by norm_num)
theorem B3646205 : Blo 1439539 3646205 := bbase (se 3 (by rfl) ⟨683663, by rfl⟩ : syracuseStep 3646205 = 1367327) (by norm_num)
theorem B3556165 : Blo 1439539 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B4858757 : Blo 1439539 4858757 := bbase (se 4 (by rfl) ⟨455508, by rfl⟩ : syracuseStep 4858757 = 911017) (by norm_num)
theorem B7291781 : Blo 1439539 7291781 := bbase (se 4 (by rfl) ⟨683604, by rfl⟩ : syracuseStep 7291781 = 1367209) (by norm_num)
theorem B3646397 : Blo 1439539 3646397 := bbase (se 3 (by rfl) ⟨683699, by rfl⟩ : syracuseStep 3646397 = 1367399) (by norm_num)
theorem B12305429 : Blo 1439539 12305429 := bbase (se 6 (by rfl) ⟨288408, by rfl⟩ : syracuseStep 12305429 = 576817) (by norm_num)
theorem B10937429 : Blo 1439539 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B1729721 : Blo 1439539 1729721 := bbase (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) (by norm_num)
theorem B1729769 : Blo 1439539 1729769 := bbase (se 2 (by rfl) ⟨648663, by rfl⟩ : syracuseStep 1729769 = 1297327) (by norm_num)
theorem B3646741 : Blo 1439539 3646741 := bbase (se 6 (by rfl) ⟨85470, by rfl⟩ : syracuseStep 3646741 = 170941) (by norm_num)
theorem B6325541 : Blo 1439539 6325541 := bbase (se 4 (by rfl) ⟨593019, by rfl⟩ : syracuseStep 6325541 = 1186039) (by norm_num)
theorem B4859189 : Blo 1439539 4859189 := bbase (se 5 (by rfl) ⟨227774, by rfl⟩ : syracuseStep 4859189 = 455549) (by norm_num)
theorem B1459517 : Blo 1439539 1459517 := bbase (se 3 (by rfl) ⟨273659, by rfl⟩ : syracuseStep 1459517 = 547319) (by norm_num)
theorem B3646853 : Blo 1439539 3646853 := bbase (se 4 (by rfl) ⟨341892, by rfl⟩ : syracuseStep 3646853 = 683785) (by norm_num)
theorem B6235541 : Blo 1439539 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B1459777 : Blo 1439539 1459777 := bbase (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) (by norm_num)
theorem B3647045 : Blo 1439539 3647045 := bbase (se 4 (by rfl) ⟨341910, by rfl⟩ : syracuseStep 3647045 = 683821) (by norm_num)
theorem B5195333 : Blo 1439539 5195333 := bbase (se 4 (by rfl) ⟨487062, by rfl⟩ : syracuseStep 5195333 = 974125) (by norm_num)
theorem B2958925 : Blo 1439539 2958925 := bbase (se 3 (by rfl) ⟨554798, by rfl⟩ : syracuseStep 2958925 = 1109597) (by norm_num)
theorem B9225845 : Blo 1439539 9225845 := bbase (se 5 (by rfl) ⟨432461, by rfl⟩ : syracuseStep 9225845 = 864923) (by norm_num)
theorem B4859621 : Blo 1439539 4859621 := bbase (se 4 (by rfl) ⟨455589, by rfl⟩ : syracuseStep 4859621 = 911179) (by norm_num)
theorem B3892997 : Blo 1439539 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B1730317 : Blo 1439539 1730317 := bbase (se 3 (by rfl) ⟨324434, by rfl⟩ : syracuseStep 1730317 = 648869) (by norm_num)
theorem B14042933 : Blo 1439539 14042933 := bbase (se 5 (by rfl) ⟨658262, by rfl⟩ : syracuseStep 14042933 = 1316525) (by norm_num)
theorem B1460101 : Blo 1439539 1460101 := bbase (se 4 (by rfl) ⟨136884, by rfl⟩ : syracuseStep 1460101 = 273769) (by norm_num)
theorem B3647389 : Blo 1439539 3647389 := bbase (se 3 (by rfl) ⟨683885, by rfl⟩ : syracuseStep 3647389 = 1367771) (by norm_num)
theorem B3647501 : Blo 1439539 3647501 := bbase (se 3 (by rfl) ⟨683906, by rfl⟩ : syracuseStep 3647501 = 1367813) (by norm_num)
theorem B5466149 : Blo 1439539 5466149 := bbase (se 4 (by rfl) ⟨512451, by rfl⟩ : syracuseStep 5466149 = 1024903) (by norm_num)
theorem B11683925 : Blo 1439539 11683925 := bbase (se 8 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 11683925 = 136921) (by norm_num)
theorem B4860053 : Blo 1439539 4860053 := bbase (se 6 (by rfl) ⟨113907, by rfl⟩ : syracuseStep 4860053 = 227815) (by norm_num)
theorem B7293077 : Blo 1439539 7293077 := bbase (se 6 (by rfl) ⟨170931, by rfl⟩ : syracuseStep 7293077 = 341863) (by norm_num)
theorem B2959517 : Blo 1439539 2959517 := bbase (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) (by norm_num)
theorem B3893429 : Blo 1439539 3893429 := bbase (se 5 (by rfl) ⟨182504, by rfl⟩ : syracuseStep 3893429 = 365009) (by norm_num)
theorem B2918597 : Blo 1439539 2918597 := bbase (se 4 (by rfl) ⟨273618, by rfl⟩ : syracuseStep 2918597 = 547237) (by norm_num)
theorem B3647693 : Blo 1439539 3647693 := bbase (se 3 (by rfl) ⟨683942, by rfl⟩ : syracuseStep 3647693 = 1367885) (by norm_num)
theorem B1730797 : Blo 1439539 1730797 := bbase (se 3 (by rfl) ⟨324524, by rfl⟩ : syracuseStep 1730797 = 649049) (by norm_num)
theorem B11094293 : Blo 1439539 11094293 := bbase (se 6 (by rfl) ⟨260022, by rfl⟩ : syracuseStep 11094293 = 520045) (by norm_num)
theorem B3459365 : Blo 1439539 3459365 := bbase (se 4 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 3459365 = 648631) (by norm_num)
theorem B2189629 : Blo 1439539 2189629 := bbase (se 3 (by rfl) ⟨410555, by rfl⟩ : syracuseStep 2189629 = 821111) (by norm_num)
theorem B5466437 : Blo 1439539 5466437 := bbase (se 4 (by rfl) ⟨512478, by rfl⟩ : syracuseStep 5466437 = 1024957) (by norm_num)
theorem B2050381 : Blo 1439539 2050381 := bbase (se 3 (by rfl) ⟨384446, by rfl⟩ : syracuseStep 2050381 = 768893) (by norm_num)
theorem B6154613 : Blo 1439539 6154613 := bbase (se 5 (by rfl) ⟨288497, by rfl⟩ : syracuseStep 6154613 = 576995) (by norm_num)
theorem B11684245 : Blo 1439539 11684245 := bbase (se 6 (by rfl) ⟨273849, by rfl⟩ : syracuseStep 11684245 = 547699) (by norm_num)
theorem B3459557 : Blo 1439539 3459557 := bbase (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) (by norm_num)
theorem B3074573 : Blo 1439539 3074573 := bbase (se 3 (by rfl) ⟨576482, by rfl⟩ : syracuseStep 3074573 = 1152965) (by norm_num)
theorem B3648037 : Blo 1439539 3648037 := bbase (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) (by norm_num)
theorem B4860485 : Blo 1439539 4860485 := bbase (se 4 (by rfl) ⟨455670, by rfl⟩ : syracuseStep 4860485 = 911341) (by norm_num)
theorem B8202869 : Blo 1439539 8202869 := bbase (se 5 (by rfl) ⟨384509, by rfl⟩ : syracuseStep 8202869 = 769019) (by norm_num)
theorem B3648149 : Blo 1439539 3648149 := bbase (se 6 (by rfl) ⟨85503, by rfl⟩ : syracuseStep 3648149 = 171007) (by norm_num)
theorem B3074717 : Blo 1439539 3074717 := bbase (se 3 (by rfl) ⟨576509, by rfl⟩ : syracuseStep 3074717 = 1153019) (by norm_num)
theorem B1539221 : Blo 1439539 1539221 := bbase (se 6 (by rfl) ⟨36075, by rfl⟩ : syracuseStep 1539221 = 72151) (by norm_num)
theorem B7785173 : Blo 1439539 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B2919197 : Blo 1439539 2919197 := bbase (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) (by norm_num)
theorem B3648341 : Blo 1439539 3648341 := bbase (se 9 (by rfl) ⟨10688, by rfl⟩ : syracuseStep 3648341 = 21377) (by norm_num)
theorem B4860917 : Blo 1439539 4860917 := bbase (se 5 (by rfl) ⟨227855, by rfl⟩ : syracuseStep 4860917 = 455711) (by norm_num)
theorem B3075077 : Blo 1439539 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B3238973 : Blo 1439539 3238973 := bbase (se 3 (by rfl) ⟨607307, by rfl⟩ : syracuseStep 3238973 = 1214615) (by norm_num)
theorem B1731677 : Blo 1439539 1731677 := bbase (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) (by norm_num)
theorem B2051173 : Blo 1439539 2051173 := bbase (se 4 (by rfl) ⟨192297, by rfl⟩ : syracuseStep 2051173 = 384595) (by norm_num)
theorem B3239045 : Blo 1439539 3239045 := bbase (se 4 (by rfl) ⟨303660, by rfl⟩ : syracuseStep 3239045 = 607321) (by norm_num)
theorem B3648685 : Blo 1439539 3648685 := bbase (se 3 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 3648685 = 1368257) (by norm_num)
theorem B3239117 : Blo 1439539 3239117 := bbase (se 3 (by rfl) ⟨607334, by rfl⟩ : syracuseStep 3239117 = 1214669) (by norm_num)
theorem B1731793 : Blo 1439539 1731793 := bbase (se 2 (by rfl) ⟨649422, by rfl⟩ : syracuseStep 1731793 = 1298845) (by norm_num)
theorem B1821953 : Blo 1439539 1821953 := bbase (se 2 (by rfl) ⟨683232, by rfl⟩ : syracuseStep 1821953 = 1366465) (by norm_num)
theorem B4099349 : Blo 1439539 4099349 := bbase (se 6 (by rfl) ⟨96078, by rfl⟩ : syracuseStep 4099349 = 192157) (by norm_num)
theorem B3239189 : Blo 1439539 3239189 := bbase (se 6 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 3239189 = 151837) (by norm_num)
theorem B3648797 : Blo 1439539 3648797 := bbase (se 3 (by rfl) ⟨684149, by rfl⟩ : syracuseStep 3648797 = 1368299) (by norm_num)
theorem B1822009 : Blo 1439539 1822009 := bbase (se 2 (by rfl) ⟨683253, by rfl⟩ : syracuseStep 1822009 = 1366507) (by norm_num)
theorem B3239261 : Blo 1439539 3239261 := bbase (se 3 (by rfl) ⟨607361, by rfl⟩ : syracuseStep 3239261 = 1214723) (by norm_num)
theorem B6155621 : Blo 1439539 6155621 := bbase (se 4 (by rfl) ⟨577089, by rfl⟩ : syracuseStep 6155621 = 1154179) (by norm_num)
theorem B1822105 : Blo 1439539 1822105 := bbase (se 2 (by rfl) ⟨683289, by rfl⟩ : syracuseStep 1822105 = 1366579) (by norm_num)
theorem B3239333 : Blo 1439539 3239333 := bbase (se 4 (by rfl) ⟨303687, by rfl⟩ : syracuseStep 3239333 = 607375) (by norm_num)
theorem B4861349 : Blo 1439539 4861349 := bbase (se 4 (by rfl) ⟨455751, by rfl⟩ : syracuseStep 4861349 = 911503) (by norm_num)
theorem B7294373 : Blo 1439539 7294373 := bbase (se 4 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 7294373 = 1367695) (by norm_num)
theorem B2051509 : Blo 1439539 2051509 := bbase (se 5 (by rfl) ⟨96164, by rfl⟩ : syracuseStep 2051509 = 192329) (by norm_num)
theorem B5467621 : Blo 1439539 5467621 := bbase (se 4 (by rfl) ⟨512589, by rfl⟩ : syracuseStep 5467621 = 1025179) (by norm_num)
theorem B3239405 : Blo 1439539 3239405 := bbase (se 3 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 3239405 = 1214777) (by norm_num)
theorem B3239477 : Blo 1439539 3239477 := bbase (se 5 (by rfl) ⟨151850, by rfl⟩ : syracuseStep 3239477 = 303701) (by norm_num)
theorem B1822277 : Blo 1439539 1822277 := bbase (se 4 (by rfl) ⟨170838, by rfl⟩ : syracuseStep 1822277 = 341677) (by norm_num)
theorem B3329605 : Blo 1439539 3329605 := bbase (se 4 (by rfl) ⟨312150, by rfl⟩ : syracuseStep 3329605 = 624301) (by norm_num)
theorem B3239549 : Blo 1439539 3239549 := bbase (se 3 (by rfl) ⟨607415, by rfl⟩ : syracuseStep 3239549 = 1214831) (by norm_num)
theorem B1822333 : Blo 1439539 1822333 := bbase (se 3 (by rfl) ⟨341687, by rfl⟩ : syracuseStep 1822333 = 683375) (by norm_num)
theorem B2051725 : Blo 1439539 2051725 := bbase (se 3 (by rfl) ⟨384698, by rfl⟩ : syracuseStep 2051725 = 769397) (by norm_num)
theorem B3239621 : Blo 1439539 3239621 := bbase (se 4 (by rfl) ⟨303714, by rfl⟩ : syracuseStep 3239621 = 607429) (by norm_num)
theorem B1822429 : Blo 1439539 1822429 := bbase (se 3 (by rfl) ⟨341705, by rfl⟩ : syracuseStep 1822429 = 683411) (by norm_num)
theorem B3239693 : Blo 1439539 3239693 := bbase (se 3 (by rfl) ⟨607442, by rfl⟩ : syracuseStep 3239693 = 1214885) (by norm_num)
theorem B5467925 : Blo 1439539 5467925 := bbase (se 6 (by rfl) ⟨128154, by rfl⟩ : syracuseStep 5467925 = 256309) (by norm_num)
theorem B2772773 : Blo 1439539 2772773 := bbase (se 4 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 2772773 = 519895) (by norm_num)
theorem B3239765 : Blo 1439539 3239765 := bbase (se 9 (by rfl) ⟨9491, by rfl⟩ : syracuseStep 3239765 = 18983) (by norm_num)
theorem B4861781 : Blo 1439539 4861781 := bbase (se 9 (by rfl) ⟨14243, by rfl⟩ : syracuseStep 4861781 = 28487) (by norm_num)
theorem B3075965 : Blo 1439539 3075965 := bbase (se 3 (by rfl) ⟨576743, by rfl⟩ : syracuseStep 3075965 = 1153487) (by norm_num)
theorem B1822601 : Blo 1439539 1822601 := bbase (se 2 (by rfl) ⟨683475, by rfl⟩ : syracuseStep 1822601 = 1366951) (by norm_num)
theorem B3239837 : Blo 1439539 3239837 := bbase (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) (by norm_num)
theorem B1822657 : Blo 1439539 1822657 := bbase (se 2 (by rfl) ⟨683496, by rfl⟩ : syracuseStep 1822657 = 1366993) (by norm_num)
theorem B3239909 : Blo 1439539 3239909 := bbase (se 4 (by rfl) ⟨303741, by rfl⟩ : syracuseStep 3239909 = 607483) (by norm_num)
theorem B4616165 : Blo 1439539 4616165 := bbase (se 4 (by rfl) ⟨432765, by rfl⟩ : syracuseStep 4616165 = 865531) (by norm_num)
theorem B3461125 : Blo 1439539 3461125 := bbase (se 4 (by rfl) ⟨324480, by rfl⟩ : syracuseStep 3461125 = 648961) (by norm_num)
theorem B2052101 : Blo 1439539 2052101 := bbase (se 4 (by rfl) ⟨192384, by rfl⟩ : syracuseStep 2052101 = 384769) (by norm_num)
theorem B1822753 : Blo 1439539 1822753 := bbase (se 2 (by rfl) ⟨683532, by rfl⟩ : syracuseStep 1822753 = 1367065) (by norm_num)
theorem B3239981 : Blo 1439539 3239981 := bbase (se 3 (by rfl) ⟨607496, by rfl⟩ : syracuseStep 3239981 = 1214993) (by norm_num)
theorem B1847345 : Blo 1439539 1847345 := bbase (se 2 (by rfl) ⟨692754, by rfl⟩ : syracuseStep 1847345 = 1385509) (by norm_num)
theorem B1642573 : Blo 1439539 1642573 := bbase (se 3 (by rfl) ⟨307982, by rfl⟩ : syracuseStep 1642573 = 615965) (by norm_num)
theorem B2306141 : Blo 1439539 2306141 := bbase (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) (by norm_num)
theorem B3240053 : Blo 1439539 3240053 := bbase (se 5 (by rfl) ⟨151877, by rfl⟩ : syracuseStep 3240053 = 303755) (by norm_num)
theorem B3076213 : Blo 1439539 3076213 := bbase (se 5 (by rfl) ⟨144197, by rfl⟩ : syracuseStep 3076213 = 288395) (by norm_num)
theorem B2306237 : Blo 1439539 2306237 := bbase (se 3 (by rfl) ⟨432419, by rfl⟩ : syracuseStep 2306237 = 864839) (by norm_num)
theorem B3240125 : Blo 1439539 3240125 := bbase (se 3 (by rfl) ⟨607523, by rfl⟩ : syracuseStep 3240125 = 1215047) (by norm_num)
theorem B1822925 : Blo 1439539 1822925 := bbase (se 3 (by rfl) ⟨341798, by rfl⟩ : syracuseStep 1822925 = 683597) (by norm_num)
theorem B2306269 : Blo 1439539 2306269 := bbase (se 3 (by rfl) ⟨432425, by rfl⟩ : syracuseStep 2306269 = 864851) (by norm_num)
theorem B4100341 : Blo 1439539 4100341 := bbase (se 5 (by rfl) ⟨192203, by rfl⟩ : syracuseStep 4100341 = 384407) (by norm_num)
theorem B3240197 : Blo 1439539 3240197 := bbase (se 4 (by rfl) ⟨303768, by rfl⟩ : syracuseStep 3240197 = 607537) (by norm_num)
theorem B1822981 : Blo 1439539 1822981 := bbase (se 4 (by rfl) ⟨170904, by rfl⟩ : syracuseStep 1822981 = 341809) (by norm_num)
theorem B4862213 : Blo 1439539 4862213 := bbase (se 4 (by rfl) ⟨455832, by rfl⟩ : syracuseStep 4862213 = 911665) (by norm_num)
theorem B2429237 : Blo 1439539 2429237 := bbase (se 5 (by rfl) ⟨113870, by rfl⟩ : syracuseStep 2429237 = 227741) (by norm_num)
theorem B5189957 : Blo 1439539 5189957 := bbase (se 4 (by rfl) ⟨486558, by rfl⟩ : syracuseStep 5189957 = 973117) (by norm_num)
theorem B3240269 : Blo 1439539 3240269 := bbase (se 3 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 3240269 = 1215101) (by norm_num)
theorem B1823077 : Blo 1439539 1823077 := bbase (se 4 (by rfl) ⟨170913, by rfl⟩ : syracuseStep 1823077 = 341827) (by norm_num)
theorem B6926725 : Blo 1439539 6926725 := bbase (se 4 (by rfl) ⟨649380, by rfl⟩ : syracuseStep 6926725 = 1298761) (by norm_num)
theorem B3240341 : Blo 1439539 3240341 := bbase (se 6 (by rfl) ⟨75945, by rfl⟩ : syracuseStep 3240341 = 151891) (by norm_num)
theorem B2429365 : Blo 1439539 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B5190085 : Blo 1439539 5190085 := bbase (se 4 (by rfl) ⟨486570, by rfl⟩ : syracuseStep 5190085 = 973141) (by norm_num)
theorem B2773453 : Blo 1439539 2773453 := bbase (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) (by norm_num)
theorem B1642961 : Blo 1439539 1642961 := bbase (se 2 (by rfl) ⟨616110, by rfl⟩ : syracuseStep 1642961 = 1232221) (by norm_num)
theorem B3240413 : Blo 1439539 3240413 := bbase (se 3 (by rfl) ⟨607577, by rfl⟩ : syracuseStep 3240413 = 1215155) (by norm_num)
theorem B2429453 : Blo 1439539 2429453 := bbase (se 3 (by rfl) ⟨455522, by rfl⟩ : syracuseStep 2429453 = 911045) (by norm_num)
theorem B1823249 : Blo 1439539 1823249 := bbase (se 2 (by rfl) ⟨683718, by rfl⟩ : syracuseStep 1823249 = 1367437) (by norm_num)
theorem B3240485 : Blo 1439539 3240485 := bbase (se 4 (by rfl) ⟨303795, by rfl⟩ : syracuseStep 3240485 = 607591) (by norm_num)
theorem B3242717 : Blo 1439539 3242717 := bbase (se 3 (by rfl) ⟨608009, by rfl⟩ : syracuseStep 3242717 = 1216019) (by norm_num)
theorem B1823305 : Blo 1439539 1823305 := bbase (se 2 (by rfl) ⟨683739, by rfl⟩ : syracuseStep 1823305 = 1367479) (by norm_num)
theorem B3240557 : Blo 1439539 3240557 := bbase (se 3 (by rfl) ⟨607604, by rfl⟩ : syracuseStep 3240557 = 1215209) (by norm_num)
theorem B3076717 : Blo 1439539 3076717 := bbase (se 3 (by rfl) ⟨576884, by rfl⟩ : syracuseStep 3076717 = 1153769) (by norm_num)
theorem B3461741 : Blo 1439539 3461741 := bbase (se 3 (by rfl) ⟨649076, by rfl⟩ : syracuseStep 3461741 = 1298153) (by norm_num)
theorem B11686517 : Blo 1439539 11686517 := bbase (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) (by norm_num)
theorem B2429581 : Blo 1439539 2429581 := bbase (se 3 (by rfl) ⟨455546, by rfl⟩ : syracuseStep 2429581 = 911093) (by norm_num)
theorem B1643161 : Blo 1439539 1643161 := bbase (se 2 (by rfl) ⟨616185, by rfl⟩ : syracuseStep 1643161 = 1232371) (by norm_num)
theorem B1823401 : Blo 1439539 1823401 := bbase (se 2 (by rfl) ⟨683775, by rfl⟩ : syracuseStep 1823401 = 1367551) (by norm_num)
theorem B3240629 : Blo 1439539 3240629 := bbase (se 5 (by rfl) ⟨151904, by rfl⟩ : syracuseStep 3240629 = 303809) (by norm_num)
theorem B4862645 : Blo 1439539 4862645 := bbase (se 5 (by rfl) ⟨227936, by rfl⟩ : syracuseStep 4862645 = 455873) (by norm_num)
theorem B7295669 : Blo 1439539 7295669 := bbase (se 5 (by rfl) ⟨341984, by rfl⟩ : syracuseStep 7295669 = 683969) (by norm_num)
theorem B2159309 : Blo 1439539 2159309 := bbase (se 3 (by rfl) ⟨404870, by rfl⟩ : syracuseStep 2159309 = 809741) (by norm_num)
theorem B2159333 : Blo 1439539 2159333 := bbase (se 4 (by rfl) ⟨202437, by rfl⟩ : syracuseStep 2159333 = 404875) (by norm_num)
theorem B2429669 : Blo 1439539 2429669 := bbase (se 4 (by rfl) ⟨227781, by rfl⟩ : syracuseStep 2429669 = 455563) (by norm_num)
theorem B2159357 : Blo 1439539 2159357 := bbase (se 3 (by rfl) ⟨404879, by rfl⟩ : syracuseStep 2159357 = 809759) (by norm_num)
theorem B3240701 : Blo 1439539 3240701 := bbase (se 3 (by rfl) ⟨607631, by rfl⟩ : syracuseStep 3240701 = 1215263) (by norm_num)
theorem B2159381 : Blo 1439539 2159381 := bbase (se 6 (by rfl) ⟨50610, by rfl⟩ : syracuseStep 2159381 = 101221) (by norm_num)
theorem B8205077 : Blo 1439539 8205077 := bbase (se 6 (by rfl) ⟨192306, by rfl⟩ : syracuseStep 8205077 = 384613) (by norm_num)
theorem B2159405 : Blo 1439539 2159405 := bbase (se 3 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 2159405 = 809777) (by norm_num)
theorem B2159429 : Blo 1439539 2159429 := bbase (se 4 (by rfl) ⟨202446, by rfl⟩ : syracuseStep 2159429 = 404893) (by norm_num)
theorem B3240773 : Blo 1439539 3240773 := bbase (se 4 (by rfl) ⟨303822, by rfl⟩ : syracuseStep 3240773 = 607645) (by norm_num)
theorem B1823573 : Blo 1439539 1823573 := bbase (se 9 (by rfl) ⟨5342, by rfl⟩ : syracuseStep 1823573 = 10685) (by norm_num)
theorem B2159453 : Blo 1439539 2159453 := bbase (se 3 (by rfl) ⟨404897, by rfl⟩ : syracuseStep 2159453 = 809795) (by norm_num)
theorem B2429797 : Blo 1439539 2429797 := bbase (se 4 (by rfl) ⟨227793, by rfl⟩ : syracuseStep 2429797 = 455587) (by norm_num)
theorem B2159477 : Blo 1439539 2159477 := bbase (se 5 (by rfl) ⟨101225, by rfl⟩ : syracuseStep 2159477 = 202451) (by norm_num)
theorem B2159501 : Blo 1439539 2159501 := bbase (se 3 (by rfl) ⟨404906, by rfl⟩ : syracuseStep 2159501 = 809813) (by norm_num)
theorem B3240845 : Blo 1439539 3240845 := bbase (se 3 (by rfl) ⟨607658, by rfl⟩ : syracuseStep 3240845 = 1215317) (by norm_num)
theorem B1823629 : Blo 1439539 1823629 := bbase (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) (by norm_num)
theorem B8426389 : Blo 1439539 8426389 := bbase (se 6 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 8426389 = 394987) (by norm_num)
theorem B2159525 : Blo 1439539 2159525 := bbase (se 4 (by rfl) ⟨202455, by rfl⟩ : syracuseStep 2159525 = 404911) (by norm_num)
theorem B2159549 : Blo 1439539 2159549 := bbase (se 3 (by rfl) ⟨404915, by rfl⟩ : syracuseStep 2159549 = 809831) (by norm_num)
theorem B2429885 : Blo 1439539 2429885 := bbase (se 3 (by rfl) ⟨455603, by rfl⟩ : syracuseStep 2429885 = 911207) (by norm_num)
theorem B2159573 : Blo 1439539 2159573 := bbase (se 7 (by rfl) ⟨25307, by rfl⟩ : syracuseStep 2159573 = 50615) (by norm_num)
theorem B3240917 : Blo 1439539 3240917 := bbase (se 7 (by rfl) ⟨37979, by rfl⟩ : syracuseStep 3240917 = 75959) (by norm_num)
theorem B2159597 : Blo 1439539 2159597 := bbase (se 3 (by rfl) ⟨404924, by rfl⟩ : syracuseStep 2159597 = 809849) (by norm_num)
theorem B1823725 : Blo 1439539 1823725 := bbase (se 3 (by rfl) ⟨341948, by rfl⟩ : syracuseStep 1823725 = 683897) (by norm_num)
theorem B2159621 : Blo 1439539 2159621 := bbase (se 4 (by rfl) ⟨202464, by rfl⟩ : syracuseStep 2159621 = 404929) (by norm_num)
theorem B2159645 : Blo 1439539 2159645 := bbase (se 3 (by rfl) ⟨404933, by rfl⟩ : syracuseStep 2159645 = 809867) (by norm_num)
theorem B3240989 : Blo 1439539 3240989 := bbase (se 3 (by rfl) ⟨607685, by rfl⟩ : syracuseStep 3240989 = 1215371) (by norm_num)
theorem B4617253 : Blo 1439539 4617253 := bbase (se 4 (by rfl) ⟨432867, by rfl⟩ : syracuseStep 4617253 = 865735) (by norm_num)
theorem B2159669 : Blo 1439539 2159669 := bbase (se 5 (by rfl) ⟨101234, by rfl⟩ : syracuseStep 2159669 = 202469) (by norm_num)
theorem B2430013 : Blo 1439539 2430013 := bbase (se 3 (by rfl) ⟨455627, by rfl⟩ : syracuseStep 2430013 = 911255) (by norm_num)
theorem B2159693 : Blo 1439539 2159693 := bbase (se 3 (by rfl) ⟨404942, by rfl⟩ : syracuseStep 2159693 = 809885) (by norm_num)
theorem B7287893 : Blo 1439539 7287893 := bbase (se 8 (by rfl) ⟨42702, by rfl⟩ : syracuseStep 7287893 = 85405) (by norm_num)
theorem B6157397 : Blo 1439539 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B2159717 : Blo 1439539 2159717 := bbase (se 4 (by rfl) ⟨202473, by rfl⟩ : syracuseStep 2159717 = 404947) (by norm_num)
theorem B3241061 : Blo 1439539 3241061 := bbase (se 4 (by rfl) ⟨303849, by rfl⟩ : syracuseStep 3241061 = 607699) (by norm_num)
theorem B4863077 : Blo 1439539 4863077 := bbase (se 4 (by rfl) ⟨455913, by rfl⟩ : syracuseStep 4863077 = 911827) (by norm_num)
theorem B2733173 : Blo 1439539 2733173 := bbase (se 5 (by rfl) ⟨128117, by rfl⟩ : syracuseStep 2733173 = 256235) (by norm_num)
theorem B2159741 : Blo 1439539 2159741 := bbase (se 3 (by rfl) ⟨404951, by rfl⟩ : syracuseStep 2159741 = 809903) (by norm_num)
theorem B2159765 : Blo 1439539 2159765 := bbase (se 6 (by rfl) ⟨50619, by rfl⟩ : syracuseStep 2159765 = 101239) (by norm_num)
theorem B2430101 : Blo 1439539 2430101 := bbase (se 6 (by rfl) ⟨56955, by rfl⟩ : syracuseStep 2430101 = 113911) (by norm_num)
theorem B1873049 : Blo 1439539 1873049 := bbase (se 2 (by rfl) ⟨702393, by rfl⟩ : syracuseStep 1873049 = 1404787) (by norm_num)
theorem B1823897 : Blo 1439539 1823897 := bbase (se 2 (by rfl) ⟨683961, by rfl⟩ : syracuseStep 1823897 = 1367923) (by norm_num)
theorem B2159789 : Blo 1439539 2159789 := bbase (se 3 (by rfl) ⟨404960, by rfl⟩ : syracuseStep 2159789 = 809921) (by norm_num)
theorem B3241133 : Blo 1439539 3241133 := bbase (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) (by norm_num)
theorem B2159813 : Blo 1439539 2159813 := bbase (se 4 (by rfl) ⟨202482, by rfl⟩ : syracuseStep 2159813 = 404965) (by norm_num)
theorem B17528021 : Blo 1439539 17528021 := bbase (se 7 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 17528021 = 410813) (by norm_num)
theorem B1823953 : Blo 1439539 1823953 := bbase (se 2 (by rfl) ⟨683982, by rfl⟩ : syracuseStep 1823953 = 1367965) (by norm_num)
theorem B16643285 : Blo 1439539 16643285 := bbase (se 7 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 16643285 = 390077) (by norm_num)
theorem B2159837 : Blo 1439539 2159837 := bbase (se 3 (by rfl) ⟨404969, by rfl⟩ : syracuseStep 2159837 = 809939) (by norm_num)
theorem B1537265 : Blo 1439539 1537265 := bbase (se 2 (by rfl) ⟨576474, by rfl⟩ : syracuseStep 1537265 = 1152949) (by norm_num)
theorem B2159861 : Blo 1439539 2159861 := bbase (se 5 (by rfl) ⟨101243, by rfl⟩ : syracuseStep 2159861 = 202487) (by norm_num)
theorem B3241205 : Blo 1439539 3241205 := bbase (se 5 (by rfl) ⟨151931, by rfl⟩ : syracuseStep 3241205 = 303863) (by norm_num)
theorem B2159885 : Blo 1439539 2159885 := bbase (se 3 (by rfl) ⟨404978, by rfl⟩ : syracuseStep 2159885 = 809957) (by norm_num)
theorem B2430229 : Blo 1439539 2430229 := bbase (se 6 (by rfl) ⟨56958, by rfl⟩ : syracuseStep 2430229 = 113917) (by norm_num)
theorem B2159909 : Blo 1439539 2159909 := bbase (se 4 (by rfl) ⟨202491, by rfl⟩ : syracuseStep 2159909 = 404983) (by norm_num)
theorem B7615781 : Blo 1439539 7615781 := bbase (se 4 (by rfl) ⟨713979, by rfl⟩ : syracuseStep 7615781 = 1427959) (by norm_num)
theorem B1824049 : Blo 1439539 1824049 := bbase (se 2 (by rfl) ⟨684018, by rfl⟩ : syracuseStep 1824049 = 1368037) (by norm_num)
theorem B2159933 : Blo 1439539 2159933 := bbase (se 3 (by rfl) ⟨404987, by rfl⟩ : syracuseStep 2159933 = 809975) (by norm_num)
theorem B3241277 : Blo 1439539 3241277 := bbase (se 3 (by rfl) ⟨607739, by rfl⟩ : syracuseStep 3241277 = 1215479) (by norm_num)
theorem B4101445 : Blo 1439539 4101445 := bbase (se 4 (by rfl) ⟨384510, by rfl⟩ : syracuseStep 4101445 = 769021) (by norm_num)
theorem B2159957 : Blo 1439539 2159957 := bbase (se 13 (by rfl) ⟨395, by rfl⟩ : syracuseStep 2159957 = 791) (by norm_num)
theorem B2159981 : Blo 1439539 2159981 := bbase (se 3 (by rfl) ⟨404996, by rfl⟩ : syracuseStep 2159981 = 809993) (by norm_num)
theorem B2430317 : Blo 1439539 2430317 := bbase (se 3 (by rfl) ⟨455684, by rfl⟩ : syracuseStep 2430317 = 911369) (by norm_num)
theorem B3462517 : Blo 1439539 3462517 := bbase (se 5 (by rfl) ⟨162305, by rfl⟩ : syracuseStep 3462517 = 324611) (by norm_num)
theorem B2160005 : Blo 1439539 2160005 := bbase (se 4 (by rfl) ⟨202500, by rfl⟩ : syracuseStep 2160005 = 405001) (by norm_num)
theorem B3241349 : Blo 1439539 3241349 := bbase (se 4 (by rfl) ⟨303876, by rfl⟩ : syracuseStep 3241349 = 607753) (by norm_num)
theorem B17528213 : Blo 1439539 17528213 := bbase (se 6 (by rfl) ⟨410817, by rfl⟩ : syracuseStep 17528213 = 821635) (by norm_num)
theorem B2160029 : Blo 1439539 2160029 := bbase (se 3 (by rfl) ⟨405005, by rfl⟩ : syracuseStep 2160029 = 810011) (by norm_num)
theorem B2463149 : Blo 1439539 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B2160053 : Blo 1439539 2160053 := bbase (se 5 (by rfl) ⟨101252, by rfl⟩ : syracuseStep 2160053 = 202505) (by norm_num)
theorem B1480117 : Blo 1439539 1480117 := bbase (se 5 (by rfl) ⟨69380, by rfl⟩ : syracuseStep 1480117 = 138761) (by norm_num)
theorem B2160077 : Blo 1439539 2160077 := bbase (se 3 (by rfl) ⟨405014, by rfl⟩ : syracuseStep 2160077 = 810029) (by norm_num)
theorem B3241421 : Blo 1439539 3241421 := bbase (se 3 (by rfl) ⟨607766, by rfl⟩ : syracuseStep 3241421 = 1215533) (by norm_num)
theorem B1824221 : Blo 1439539 1824221 := bbase (se 3 (by rfl) ⟨342041, by rfl⟩ : syracuseStep 1824221 = 684083) (by norm_num)
theorem B2160101 : Blo 1439539 2160101 := bbase (se 4 (by rfl) ⟨202509, by rfl⟩ : syracuseStep 2160101 = 405019) (by norm_num)
theorem B3077605 : Blo 1439539 3077605 := bbase (se 4 (by rfl) ⟨288525, by rfl⟩ : syracuseStep 3077605 = 577051) (by norm_num)
theorem B2430445 : Blo 1439539 2430445 := bbase (se 3 (by rfl) ⟨455708, by rfl⟩ : syracuseStep 2430445 = 911417) (by norm_num)
theorem B2160125 : Blo 1439539 2160125 := bbase (se 3 (by rfl) ⟨405023, by rfl⟩ : syracuseStep 2160125 = 810047) (by norm_num)
theorem B1873405 : Blo 1439539 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B2160149 : Blo 1439539 2160149 := bbase (se 6 (by rfl) ⟨50628, by rfl⟩ : syracuseStep 2160149 = 101257) (by norm_num)
theorem B3241493 : Blo 1439539 3241493 := bbase (se 6 (by rfl) ⟨75972, by rfl⟩ : syracuseStep 3241493 = 151945) (by norm_num)
theorem B4863509 : Blo 1439539 4863509 := bbase (se 6 (by rfl) ⟨113988, by rfl⟩ : syracuseStep 4863509 = 227977) (by norm_num)
theorem B1824277 : Blo 1439539 1824277 := bbase (se 6 (by rfl) ⟨42756, by rfl⟩ : syracuseStep 1824277 = 85513) (by norm_num)
theorem B2160173 : Blo 1439539 2160173 := bbase (se 3 (by rfl) ⟨405032, by rfl⟩ : syracuseStep 2160173 = 810065) (by norm_num)
theorem B1619509 : Blo 1439539 1619509 := bbase (se 5 (by rfl) ⟨75914, by rfl⟩ : syracuseStep 1619509 = 151829) (by norm_num)
theorem B2160197 : Blo 1439539 2160197 := bbase (se 4 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 2160197 = 405037) (by norm_num)
theorem B2430533 : Blo 1439539 2430533 := bbase (se 4 (by rfl) ⟨227862, by rfl⟩ : syracuseStep 2430533 = 455725) (by norm_num)
theorem B1619545 : Blo 1439539 1619545 := bbase (se 2 (by rfl) ⟨607329, by rfl⟩ : syracuseStep 1619545 = 1214659) (by norm_num)
theorem B2160221 : Blo 1439539 2160221 := bbase (se 3 (by rfl) ⟨405041, by rfl⟩ : syracuseStep 2160221 = 810083) (by norm_num)
theorem B3241565 : Blo 1439539 3241565 := bbase (se 3 (by rfl) ⟨607793, by rfl⟩ : syracuseStep 3241565 = 1215587) (by norm_num)
theorem B2160245 : Blo 1439539 2160245 := bbase (se 5 (by rfl) ⟨101261, by rfl⟩ : syracuseStep 2160245 = 202523) (by norm_num)
theorem B1824373 : Blo 1439539 1824373 := bbase (se 5 (by rfl) ⟨85517, by rfl⟩ : syracuseStep 1824373 = 171035) (by norm_num)
theorem B1619581 : Blo 1439539 1619581 := bbase (se 3 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 1619581 = 607343) (by norm_num)
theorem B2160269 : Blo 1439539 2160269 := bbase (se 3 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 2160269 = 810101) (by norm_num)
theorem B1947277 : Blo 1439539 1947277 := bbase (se 3 (by rfl) ⟨365114, by rfl⟩ : syracuseStep 1947277 = 730229) (by norm_num)
theorem B5060245 : Blo 1439539 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B1619617 : Blo 1439539 1619617 := bbase (se 2 (by rfl) ⟨607356, by rfl⟩ : syracuseStep 1619617 = 1214713) (by norm_num)
theorem B2160293 : Blo 1439539 2160293 := bbase (se 4 (by rfl) ⟨202527, by rfl⟩ : syracuseStep 2160293 = 405055) (by norm_num)
theorem B3241637 : Blo 1439539 3241637 := bbase (se 4 (by rfl) ⟨303903, by rfl⟩ : syracuseStep 3241637 = 607807) (by norm_num)
theorem B1537709 : Blo 1439539 1537709 := bbase (se 3 (by rfl) ⟨288320, by rfl⟩ : syracuseStep 1537709 = 576641) (by norm_num)
theorem B3118765 : Blo 1439539 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B2160317 : Blo 1439539 2160317 := bbase (se 3 (by rfl) ⟨405059, by rfl⟩ : syracuseStep 2160317 = 810119) (by norm_num)
theorem B1619653 : Blo 1439539 1619653 := bbase (se 4 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 1619653 = 303685) (by norm_num)
theorem B2430661 : Blo 1439539 2430661 := bbase (se 4 (by rfl) ⟨227874, by rfl⟩ : syracuseStep 2430661 = 455749) (by norm_num)
theorem B2307781 : Blo 1439539 2307781 := bbase (se 4 (by rfl) ⟨216354, by rfl⟩ : syracuseStep 2307781 = 432709) (by norm_num)
theorem B2160341 : Blo 1439539 2160341 := bbase (se 7 (by rfl) ⟨25316, by rfl⟩ : syracuseStep 2160341 = 50633) (by norm_num)
theorem B1619689 : Blo 1439539 1619689 := bbase (se 2 (by rfl) ⟨607383, by rfl⟩ : syracuseStep 1619689 = 1214767) (by norm_num)
theorem B2160365 : Blo 1439539 2160365 := bbase (se 3 (by rfl) ⟨405068, by rfl⟩ : syracuseStep 2160365 = 810137) (by norm_num)
theorem B3241709 : Blo 1439539 3241709 := bbase (se 3 (by rfl) ⟨607820, by rfl⟩ : syracuseStep 3241709 = 1215641) (by norm_num)
theorem B2160389 : Blo 1439539 2160389 := bbase (se 4 (by rfl) ⟨202536, by rfl⟩ : syracuseStep 2160389 = 405073) (by norm_num)
theorem B1619725 : Blo 1439539 1619725 := bbase (se 3 (by rfl) ⟨303698, by rfl⟩ : syracuseStep 1619725 = 607397) (by norm_num)
theorem B2160413 : Blo 1439539 2160413 := bbase (se 3 (by rfl) ⟨405077, by rfl⟩ : syracuseStep 2160413 = 810155) (by norm_num)
theorem B2430749 : Blo 1439539 2430749 := bbase (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) (by norm_num)
theorem B1619761 : Blo 1439539 1619761 := bbase (se 2 (by rfl) ⟨607410, by rfl⟩ : syracuseStep 1619761 = 1214821) (by norm_num)
theorem B2160437 : Blo 1439539 2160437 := bbase (se 5 (by rfl) ⟨101270, by rfl⟩ : syracuseStep 2160437 = 202541) (by norm_num)
theorem B3241781 : Blo 1439539 3241781 := bbase (se 5 (by rfl) ⟨151958, by rfl⟩ : syracuseStep 3241781 = 303917) (by norm_num)
theorem B1947461 : Blo 1439539 1947461 := bbase (se 4 (by rfl) ⟨182574, by rfl⟩ : syracuseStep 1947461 = 365149) (by norm_num)
theorem B2160461 : Blo 1439539 2160461 := bbase (se 3 (by rfl) ⟨405086, by rfl⟩ : syracuseStep 2160461 = 810173) (by norm_num)
theorem B1619797 : Blo 1439539 1619797 := bbase (se 9 (by rfl) ⟨4745, by rfl⟩ : syracuseStep 1619797 = 9491) (by norm_num)
theorem B5470037 : Blo 1439539 5470037 := bbase (se 9 (by rfl) ⟨16025, by rfl⟩ : syracuseStep 5470037 = 32051) (by norm_num)
theorem B13850453 : Blo 1439539 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B2733925 : Blo 1439539 2733925 := bbase (se 4 (by rfl) ⟨256305, by rfl⟩ : syracuseStep 2733925 = 512611) (by norm_num)
theorem B2160485 : Blo 1439539 2160485 := bbase (se 4 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 2160485 = 405091) (by norm_num)
theorem B1947493 : Blo 1439539 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B1619833 : Blo 1439539 1619833 := bbase (se 2 (by rfl) ⟨607437, by rfl⟩ : syracuseStep 1619833 = 1214875) (by norm_num)
theorem B2160509 : Blo 1439539 2160509 := bbase (se 3 (by rfl) ⟨405095, by rfl⟩ : syracuseStep 2160509 = 810191) (by norm_num)
theorem B3241853 : Blo 1439539 3241853 := bbase (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) (by norm_num)
theorem B2160533 : Blo 1439539 2160533 := bbase (se 6 (by rfl) ⟨50637, by rfl⟩ : syracuseStep 2160533 = 101275) (by norm_num)
theorem B1619869 : Blo 1439539 1619869 := bbase (se 3 (by rfl) ⟨303725, by rfl⟩ : syracuseStep 1619869 = 607451) (by norm_num)
theorem B2430877 : Blo 1439539 2430877 := bbase (se 3 (by rfl) ⟨455789, by rfl⟩ : syracuseStep 2430877 = 911579) (by norm_num)
theorem B1537957 : Blo 1439539 1537957 := bbase (se 4 (by rfl) ⟨144183, by rfl⟩ : syracuseStep 1537957 = 288367) (by norm_num)
theorem B2160557 : Blo 1439539 2160557 := bbase (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) (by norm_num)
theorem B1619905 : Blo 1439539 1619905 := bbase (se 2 (by rfl) ⟨607464, by rfl⟩ : syracuseStep 1619905 = 1214929) (by norm_num)
theorem B2160581 : Blo 1439539 2160581 := bbase (se 4 (by rfl) ⟨202554, by rfl⟩ : syracuseStep 2160581 = 405109) (by norm_num)
theorem B3241925 : Blo 1439539 3241925 := bbase (se 4 (by rfl) ⟨303930, by rfl⟩ : syracuseStep 3241925 = 607861) (by norm_num)
theorem B4863941 : Blo 1439539 4863941 := bbase (se 4 (by rfl) ⟨455994, by rfl⟩ : syracuseStep 4863941 = 911989) (by norm_num)
theorem B7296965 : Blo 1439539 7296965 := bbase (se 4 (by rfl) ⟨684090, by rfl⟩ : syracuseStep 7296965 = 1368181) (by norm_num)
theorem B3078101 : Blo 1439539 3078101 := bbase (se 7 (by rfl) ⟨36071, by rfl⟩ : syracuseStep 3078101 = 72143) (by norm_num)
theorem B2160605 : Blo 1439539 2160605 := bbase (se 3 (by rfl) ⟨405113, by rfl⟩ : syracuseStep 2160605 = 810227) (by norm_num)
theorem B1619941 : Blo 1439539 1619941 := bbase (se 4 (by rfl) ⟨151869, by rfl⟩ : syracuseStep 1619941 = 303739) (by norm_num)
theorem B2734069 : Blo 1439539 2734069 := bbase (se 5 (by rfl) ⟨128159, by rfl⟩ : syracuseStep 2734069 = 256319) (by norm_num)
theorem B2160629 : Blo 1439539 2160629 := bbase (se 5 (by rfl) ⟨101279, by rfl⟩ : syracuseStep 2160629 = 202559) (by norm_num)
theorem B2430965 : Blo 1439539 2430965 := bbase (se 5 (by rfl) ⟨113951, by rfl⟩ : syracuseStep 2430965 = 227903) (by norm_num)
theorem B1619977 : Blo 1439539 1619977 := bbase (se 2 (by rfl) ⟨607491, by rfl⟩ : syracuseStep 1619977 = 1214983) (by norm_num)
theorem B2160653 : Blo 1439539 2160653 := bbase (se 3 (by rfl) ⟨405122, by rfl⟩ : syracuseStep 2160653 = 810245) (by norm_num)
theorem B3241997 : Blo 1439539 3241997 := bbase (se 3 (by rfl) ⟨607874, by rfl⟩ : syracuseStep 3241997 = 1215749) (by norm_num)
theorem B2160677 : Blo 1439539 2160677 := bbase (se 4 (by rfl) ⟨202563, by rfl⟩ : syracuseStep 2160677 = 405127) (by norm_num)
theorem B1620013 : Blo 1439539 1620013 := bbase (se 3 (by rfl) ⟨303752, by rfl⟩ : syracuseStep 1620013 = 607505) (by norm_num)
theorem B2160701 : Blo 1439539 2160701 := bbase (se 3 (by rfl) ⟨405131, by rfl⟩ : syracuseStep 2160701 = 810263) (by norm_num)
theorem B3463229 : Blo 1439539 3463229 := bbase (se 3 (by rfl) ⟨649355, by rfl⟩ : syracuseStep 3463229 = 1298711) (by norm_num)
theorem B1620049 : Blo 1439539 1620049 := bbase (se 2 (by rfl) ⟨607518, by rfl⟩ : syracuseStep 1620049 = 1215037) (by norm_num)
theorem B2160725 : Blo 1439539 2160725 := bbase (se 8 (by rfl) ⟨12660, by rfl⟩ : syracuseStep 2160725 = 25321) (by norm_num)
theorem B3242069 : Blo 1439539 3242069 := bbase (se 8 (by rfl) ⟨18996, by rfl⟩ : syracuseStep 3242069 = 37993) (by norm_num)
theorem B71071829 : Blo 1439539 71071829 := bbase (se 8 (by rfl) ⟨416436, by rfl⟩ : syracuseStep 71071829 = 832873) (by norm_num)
theorem B2160749 : Blo 1439539 2160749 := bbase (se 3 (by rfl) ⟨405140, by rfl⟩ : syracuseStep 2160749 = 810281) (by norm_num)
theorem B1620085 : Blo 1439539 1620085 := bbase (se 5 (by rfl) ⟨75941, by rfl⟩ : syracuseStep 1620085 = 151883) (by norm_num)
theorem B2431093 : Blo 1439539 2431093 := bbase (se 5 (by rfl) ⟨113957, by rfl⟩ : syracuseStep 2431093 = 227915) (by norm_num)
theorem B5470325 : Blo 1439539 5470325 := bbase (se 5 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 5470325 = 512843) (by norm_num)
theorem B2160773 : Blo 1439539 2160773 := bbase (se 4 (by rfl) ⟨202572, by rfl⟩ : syracuseStep 2160773 = 405145) (by norm_num)
theorem B2734229 : Blo 1439539 2734229 := bbase (se 6 (by rfl) ⟨64083, by rfl⟩ : syracuseStep 2734229 = 128167) (by norm_num)
theorem B1620121 : Blo 1439539 1620121 := bbase (se 2 (by rfl) ⟨607545, by rfl⟩ : syracuseStep 1620121 = 1215091) (by norm_num)
theorem B2160797 : Blo 1439539 2160797 := bbase (se 3 (by rfl) ⟨405149, by rfl⟩ : syracuseStep 2160797 = 810299) (by norm_num)
theorem B3242141 : Blo 1439539 3242141 := bbase (se 3 (by rfl) ⟨607901, by rfl⟩ : syracuseStep 3242141 = 1215803) (by norm_num)
theorem B2160821 : Blo 1439539 2160821 := bbase (se 5 (by rfl) ⟨101288, by rfl⟩ : syracuseStep 2160821 = 202577) (by norm_num)
theorem B1620157 : Blo 1439539 1620157 := bbase (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) (by norm_num)
theorem B2160845 : Blo 1439539 2160845 := bbase (se 3 (by rfl) ⟨405158, by rfl⟩ : syracuseStep 2160845 = 810317) (by norm_num)
theorem B2431181 : Blo 1439539 2431181 := bbase (se 3 (by rfl) ⟨455846, by rfl⟩ : syracuseStep 2431181 = 911693) (by norm_num)
theorem B1620193 : Blo 1439539 1620193 := bbase (se 2 (by rfl) ⟨607572, by rfl⟩ : syracuseStep 1620193 = 1215145) (by norm_num)
theorem B2160869 : Blo 1439539 2160869 := bbase (se 4 (by rfl) ⟨202581, by rfl⟩ : syracuseStep 2160869 = 405163) (by norm_num)
theorem B3242213 : Blo 1439539 3242213 := bbase (se 4 (by rfl) ⟨303957, by rfl⟩ : syracuseStep 3242213 = 607915) (by norm_num)
theorem B2160893 : Blo 1439539 2160893 := bbase (se 3 (by rfl) ⟨405167, by rfl⟩ : syracuseStep 2160893 = 810335) (by norm_num)
theorem B1620229 : Blo 1439539 1620229 := bbase (se 4 (by rfl) ⟨151896, by rfl⟩ : syracuseStep 1620229 = 303793) (by norm_num)
theorem B2160917 : Blo 1439539 2160917 := bbase (se 6 (by rfl) ⟨50646, by rfl⟩ : syracuseStep 2160917 = 101293) (by norm_num)
theorem B2734373 : Blo 1439539 2734373 := bbase (se 4 (by rfl) ⟨256347, by rfl⟩ : syracuseStep 2734373 = 512695) (by norm_num)
theorem B1620265 : Blo 1439539 1620265 := bbase (se 2 (by rfl) ⟨607599, by rfl⟩ : syracuseStep 1620265 = 1215199) (by norm_num)
theorem B2160941 : Blo 1439539 2160941 := bbase (se 3 (by rfl) ⟨405176, by rfl⟩ : syracuseStep 2160941 = 810353) (by norm_num)
theorem B3242285 : Blo 1439539 3242285 := bbase (se 3 (by rfl) ⟨607928, by rfl⟩ : syracuseStep 3242285 = 1215857) (by norm_num)
theorem B13146421 : Blo 1439539 13146421 := bbase (se 5 (by rfl) ⟨616238, by rfl⟩ : syracuseStep 13146421 = 1232477) (by norm_num)
theorem B2160965 : Blo 1439539 2160965 := bbase (se 4 (by rfl) ⟨202590, by rfl⟩ : syracuseStep 2160965 = 405181) (by norm_num)
theorem B1620301 : Blo 1439539 1620301 := bbase (se 3 (by rfl) ⟨303806, by rfl⟩ : syracuseStep 1620301 = 607613) (by norm_num)
theorem B2431309 : Blo 1439539 2431309 := bbase (se 3 (by rfl) ⟨455870, by rfl⟩ : syracuseStep 2431309 = 911741) (by norm_num)
theorem B2160989 : Blo 1439539 2160989 := bbase (se 3 (by rfl) ⟨405185, by rfl⟩ : syracuseStep 2160989 = 810371) (by norm_num)
theorem B1538401 : Blo 1439539 1538401 := bbase (se 2 (by rfl) ⟨576900, by rfl⟩ : syracuseStep 1538401 = 1153801) (by norm_num)
theorem B7289189 : Blo 1439539 7289189 := bbase (se 4 (by rfl) ⟨683361, by rfl⟩ : syracuseStep 7289189 = 1366723) (by norm_num)
theorem B1620337 : Blo 1439539 1620337 := bbase (se 2 (by rfl) ⟨607626, by rfl⟩ : syracuseStep 1620337 = 1215253) (by norm_num)
theorem B2161013 : Blo 1439539 2161013 := bbase (se 5 (by rfl) ⟨101297, by rfl⟩ : syracuseStep 2161013 = 202595) (by norm_num)
theorem B3242357 : Blo 1439539 3242357 := bbase (se 5 (by rfl) ⟨151985, by rfl⟩ : syracuseStep 3242357 = 303971) (by norm_num)
theorem B4864373 : Blo 1439539 4864373 := bbase (se 5 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 4864373 = 456035) (by norm_num)
theorem B2161037 : Blo 1439539 2161037 := bbase (se 3 (by rfl) ⟨405194, by rfl⟩ : syracuseStep 2161037 = 810389) (by norm_num)
theorem B2308493 : Blo 1439539 2308493 := bbase (se 3 (by rfl) ⟨432842, by rfl⟩ : syracuseStep 2308493 = 865685) (by norm_num)
theorem B1620373 : Blo 1439539 1620373 := bbase (se 6 (by rfl) ⟨37977, by rfl⟩ : syracuseStep 1620373 = 75955) (by norm_num)
theorem B1538461 : Blo 1439539 1538461 := bbase (se 3 (by rfl) ⟨288461, by rfl⟩ : syracuseStep 1538461 = 576923) (by norm_num)
theorem B2161061 : Blo 1439539 2161061 := bbase (se 4 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 2161061 = 405199) (by norm_num)
theorem B2431397 : Blo 1439539 2431397 := bbase (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) (by norm_num)
theorem B1620409 : Blo 1439539 1620409 := bbase (se 2 (by rfl) ⟨607653, by rfl⟩ : syracuseStep 1620409 = 1215307) (by norm_num)
theorem B2161085 : Blo 1439539 2161085 := bbase (se 3 (by rfl) ⟨405203, by rfl⟩ : syracuseStep 2161085 = 810407) (by norm_num)
theorem B3242429 : Blo 1439539 3242429 := bbase (se 3 (by rfl) ⟨607955, by rfl⟩ : syracuseStep 3242429 = 1215911) (by norm_num)
theorem B2161109 : Blo 1439539 2161109 := bbase (se 7 (by rfl) ⟨25325, by rfl⟩ : syracuseStep 2161109 = 50651) (by norm_num)
theorem B1620445 : Blo 1439539 1620445 := bbase (se 3 (by rfl) ⟨303833, by rfl⟩ : syracuseStep 1620445 = 607667) (by norm_num)
theorem B2161133 : Blo 1439539 2161133 := bbase (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) (by norm_num)
theorem B1620481 : Blo 1439539 1620481 := bbase (se 2 (by rfl) ⟨607680, by rfl⟩ : syracuseStep 1620481 = 1215361) (by norm_num)
theorem B2161157 : Blo 1439539 2161157 := bbase (se 4 (by rfl) ⟨202608, by rfl⟩ : syracuseStep 2161157 = 405217) (by norm_num)
theorem B3242501 : Blo 1439539 3242501 := bbase (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) (by norm_num)
theorem B2161181 : Blo 1439539 2161181 := bbase (se 3 (by rfl) ⟨405221, by rfl⟩ : syracuseStep 2161181 = 810443) (by norm_num)
theorem B1620517 : Blo 1439539 1620517 := bbase (se 4 (by rfl) ⟨151923, by rfl⟩ : syracuseStep 1620517 = 303847) (by norm_num)
theorem B2431525 : Blo 1439539 2431525 := bbase (se 4 (by rfl) ⟨227955, by rfl⟩ : syracuseStep 2431525 = 455911) (by norm_num)
theorem B2161205 : Blo 1439539 2161205 := bbase (se 5 (by rfl) ⟨101306, by rfl⟩ : syracuseStep 2161205 = 202613) (by norm_num)
theorem B2734661 : Blo 1439539 2734661 := bbase (se 4 (by rfl) ⟨256374, by rfl⟩ : syracuseStep 2734661 = 512749) (by norm_num)
theorem B1620553 : Blo 1439539 1620553 := bbase (se 2 (by rfl) ⟨607707, by rfl⟩ : syracuseStep 1620553 = 1215415) (by norm_num)
theorem B2161229 : Blo 1439539 2161229 := bbase (se 3 (by rfl) ⟨405230, by rfl⟩ : syracuseStep 2161229 = 810461) (by norm_num)
theorem B3242573 : Blo 1439539 3242573 := bbase (se 3 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 3242573 = 1215965) (by norm_num)
theorem B2161253 : Blo 1439539 2161253 := bbase (se 4 (by rfl) ⟨202617, by rfl⟩ : syracuseStep 2161253 = 405235) (by norm_num)
theorem B1620589 : Blo 1439539 1620589 := bbase (se 3 (by rfl) ⟨303860, by rfl⟩ : syracuseStep 1620589 = 607721) (by norm_num)
theorem B2161277 : Blo 1439539 2161277 := bbase (se 3 (by rfl) ⟨405239, by rfl⟩ : syracuseStep 2161277 = 810479) (by norm_num)
theorem B2431613 : Blo 1439539 2431613 := bbase (se 3 (by rfl) ⟨455927, by rfl⟩ : syracuseStep 2431613 = 911855) (by norm_num)
theorem B1620625 : Blo 1439539 1620625 := bbase (se 2 (by rfl) ⟨607734, by rfl⟩ : syracuseStep 1620625 = 1215469) (by norm_num)
theorem B2161301 : Blo 1439539 2161301 := bbase (se 6 (by rfl) ⟨50655, by rfl⟩ : syracuseStep 2161301 = 101311) (by norm_num)
theorem B3242645 : Blo 1439539 3242645 := bbase (se 6 (by rfl) ⟨75999, by rfl⟩ : syracuseStep 3242645 = 151999) (by norm_num)
theorem B2161325 : Blo 1439539 2161325 := bbase (se 3 (by rfl) ⟨405248, by rfl⟩ : syracuseStep 2161325 = 810497) (by norm_num)
theorem B1620661 : Blo 1439539 1620661 := bbase (se 5 (by rfl) ⟨75968, by rfl⟩ : syracuseStep 1620661 = 151937) (by norm_num)
theorem B2161349 : Blo 1439539 2161349 := bbase (se 4 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 2161349 = 405253) (by norm_num)
theorem B1620697 : Blo 1439539 1620697 := bbase (se 2 (by rfl) ⟨607761, by rfl⟩ : syracuseStep 1620697 = 1215523) (by norm_num)
theorem B1538777 : Blo 1439539 1538777 := bbase (se 2 (by rfl) ⟨577041, by rfl⟩ : syracuseStep 1538777 = 1154083) (by norm_num)
theorem B2734813 : Blo 1439539 2734813 := bbase (se 3 (by rfl) ⟨512777, by rfl⟩ : syracuseStep 2734813 = 1025555) (by norm_num)
theorem B2161373 : Blo 1439539 2161373 := bbase (se 3 (by rfl) ⟨405257, by rfl⟩ : syracuseStep 2161373 = 810515) (by norm_num)
theorem B3644149 : Blo 1439539 3644149 := bbase (se 5 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 3644149 = 341639) (by norm_num)
theorem B2161397 : Blo 1439539 2161397 := bbase (se 5 (by rfl) ⟨101315, by rfl⟩ : syracuseStep 2161397 = 202631) (by norm_num)
theorem B1620733 : Blo 1439539 1620733 := bbase (se 3 (by rfl) ⟨303887, by rfl⟩ : syracuseStep 1620733 = 607775) (by norm_num)
theorem B2431741 : Blo 1439539 2431741 := bbase (se 3 (by rfl) ⟨455951, by rfl⟩ : syracuseStep 2431741 = 911903) (by norm_num)
theorem B2161421 : Blo 1439539 2161421 := bbase (se 3 (by rfl) ⟨405266, by rfl⟩ : syracuseStep 2161421 = 810533) (by norm_num)
theorem B1620769 : Blo 1439539 1620769 := bbase (se 2 (by rfl) ⟨607788, by rfl⟩ : syracuseStep 1620769 = 1215577) (by norm_num)
theorem B4102949 : Blo 1439539 4102949 := bbase (se 4 (by rfl) ⟨384651, by rfl⟩ : syracuseStep 4102949 = 769303) (by norm_num)
theorem B2161445 : Blo 1439539 2161445 := bbase (se 4 (by rfl) ⟨202635, by rfl⟩ : syracuseStep 2161445 = 405271) (by norm_num)
theorem B3242789 : Blo 1439539 3242789 := bbase (se 4 (by rfl) ⟨304011, by rfl⟩ : syracuseStep 3242789 = 608023) (by norm_num)
theorem B4864805 : Blo 1439539 4864805 := bbase (se 4 (by rfl) ⟨456075, by rfl⟩ : syracuseStep 4864805 = 912151) (by norm_num)
theorem B2161469 : Blo 1439539 2161469 := bbase (se 3 (by rfl) ⟨405275, by rfl⟩ : syracuseStep 2161469 = 810551) (by norm_num)
theorem B1620805 : Blo 1439539 1620805 := bbase (se 4 (by rfl) ⟨151950, by rfl⟩ : syracuseStep 1620805 = 303901) (by norm_num)
theorem B27671381 : Blo 1439539 27671381 := bbase (se 9 (by rfl) ⟨81068, by rfl⟩ : syracuseStep 27671381 = 162137) (by norm_num)
theorem B1973077 : Blo 1439539 1973077 := bbase (se 9 (by rfl) ⟨5780, by rfl⟩ : syracuseStep 1973077 = 11561) (by norm_num)
theorem B2161493 : Blo 1439539 2161493 := bbase (se 9 (by rfl) ⟨6332, by rfl⟩ : syracuseStep 2161493 = 12665) (by norm_num)
theorem B2431829 : Blo 1439539 2431829 := bbase (se 9 (by rfl) ⟨7124, by rfl⟩ : syracuseStep 2431829 = 14249) (by norm_num)
theorem B3644261 : Blo 1439539 3644261 := bbase (se 4 (by rfl) ⟨341649, by rfl⟩ : syracuseStep 3644261 = 683299) (by norm_num)
theorem B1620841 : Blo 1439539 1620841 := bbase (se 2 (by rfl) ⟨607815, by rfl⟩ : syracuseStep 1620841 = 1215631) (by norm_num)
theorem B2161517 : Blo 1439539 2161517 := bbase (se 3 (by rfl) ⟨405284, by rfl⟩ : syracuseStep 2161517 = 810569) (by norm_num)
theorem B3242861 : Blo 1439539 3242861 := bbase (se 3 (by rfl) ⟨608036, by rfl⟩ : syracuseStep 3242861 = 1216073) (by norm_num)
theorem B2161541 : Blo 1439539 2161541 := bbase (se 4 (by rfl) ⟨202644, by rfl⟩ : syracuseStep 2161541 = 405289) (by norm_num)
theorem B1620877 : Blo 1439539 1620877 := bbase (se 3 (by rfl) ⟨303914, by rfl⟩ : syracuseStep 1620877 = 607829) (by norm_num)
theorem B2464661 : Blo 1439539 2464661 := bbase (se 6 (by rfl) ⟨57765, by rfl⟩ : syracuseStep 2464661 = 115531) (by norm_num)
theorem B2161565 : Blo 1439539 2161565 := bbase (se 3 (by rfl) ⟨405293, by rfl⟩ : syracuseStep 2161565 = 810587) (by norm_num)
theorem B4930469 : Blo 1439539 4930469 := bbase (se 4 (by rfl) ⟨462231, by rfl⟩ : syracuseStep 4930469 = 924463) (by norm_num)
theorem B1620913 : Blo 1439539 1620913 := bbase (se 2 (by rfl) ⟨607842, by rfl⟩ : syracuseStep 1620913 = 1215685) (by norm_num)
theorem B2161589 : Blo 1439539 2161589 := bbase (se 5 (by rfl) ⟨101324, by rfl⟩ : syracuseStep 2161589 = 202649) (by norm_num)
theorem B3242933 : Blo 1439539 3242933 := bbase (se 5 (by rfl) ⟨152012, by rfl⟩ : syracuseStep 3242933 = 304025) (by norm_num)
theorem B2161613 : Blo 1439539 2161613 := bbase (se 3 (by rfl) ⟨405302, by rfl⟩ : syracuseStep 2161613 = 810605) (by norm_num)
theorem B1620949 : Blo 1439539 1620949 := bbase (se 7 (by rfl) ⟨18995, by rfl⟩ : syracuseStep 1620949 = 37991) (by norm_num)
theorem B2431957 : Blo 1439539 2431957 := bbase (se 7 (by rfl) ⟨28499, by rfl⟩ : syracuseStep 2431957 = 56999) (by norm_num)
theorem B2161637 : Blo 1439539 2161637 := bbase (se 4 (by rfl) ⟨202653, by rfl⟩ : syracuseStep 2161637 = 405307) (by norm_num)
theorem B2595821 : Blo 1439539 2595821 := bbase (se 3 (by rfl) ⟨486716, by rfl⟩ : syracuseStep 2595821 = 973433) (by norm_num)
theorem B1620985 : Blo 1439539 1620985 := bbase (se 2 (by rfl) ⟨607869, by rfl⟩ : syracuseStep 1620985 = 1215739) (by norm_num)
theorem B2161661 : Blo 1439539 2161661 := bbase (se 3 (by rfl) ⟨405311, by rfl⟩ : syracuseStep 2161661 = 810623) (by norm_num)
theorem B3243005 : Blo 1439539 3243005 := bbase (se 3 (by rfl) ⟨608063, by rfl⟩ : syracuseStep 3243005 = 1216127) (by norm_num)
theorem B2735117 : Blo 1439539 2735117 := bbase (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) (by norm_num)
theorem B2161685 : Blo 1439539 2161685 := bbase (se 6 (by rfl) ⟨50664, by rfl⟩ : syracuseStep 2161685 = 101329) (by norm_num)
theorem B1621021 : Blo 1439539 1621021 := bbase (se 3 (by rfl) ⟨303941, by rfl⟩ : syracuseStep 1621021 = 607883) (by norm_num)
theorem B3644453 : Blo 1439539 3644453 := bbase (se 4 (by rfl) ⟨341667, by rfl⟩ : syracuseStep 3644453 = 683335) (by norm_num)
theorem B2161709 : Blo 1439539 2161709 := bbase (se 3 (by rfl) ⟨405320, by rfl⟩ : syracuseStep 2161709 = 810641) (by norm_num)
theorem B2432045 : Blo 1439539 2432045 := bbase (se 3 (by rfl) ⟨456008, by rfl⟩ : syracuseStep 2432045 = 912017) (by norm_num)
theorem B1621057 : Blo 1439539 1621057 := bbase (se 2 (by rfl) ⟨607896, by rfl⟩ : syracuseStep 1621057 = 1215793) (by norm_num)
theorem B2161733 : Blo 1439539 2161733 := bbase (se 4 (by rfl) ⟨202662, by rfl⟩ : syracuseStep 2161733 = 405325) (by norm_num)
theorem B3243077 : Blo 1439539 3243077 := bbase (se 4 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 3243077 = 608077) (by norm_num)
theorem B2161757 : Blo 1439539 2161757 := bbase (se 3 (by rfl) ⟨405329, by rfl⟩ : syracuseStep 2161757 = 810659) (by norm_num)
theorem B1621093 : Blo 1439539 1621093 := bbase (se 4 (by rfl) ⟨151977, by rfl⟩ : syracuseStep 1621093 = 303955) (by norm_num)
theorem B2161781 : Blo 1439539 2161781 := bbase (se 5 (by rfl) ⟨101333, by rfl⟩ : syracuseStep 2161781 = 202667) (by norm_num)
theorem B2464901 : Blo 1439539 2464901 := bbase (se 4 (by rfl) ⟨231084, by rfl⟩ : syracuseStep 2464901 = 462169) (by norm_num)
theorem B1621129 : Blo 1439539 1621129 := bbase (se 2 (by rfl) ⟨607923, by rfl⟩ : syracuseStep 1621129 = 1215847) (by norm_num)
theorem B2161805 : Blo 1439539 2161805 := bbase (se 3 (by rfl) ⟨405338, by rfl⟩ : syracuseStep 2161805 = 810677) (by norm_num)
theorem B3243149 : Blo 1439539 3243149 := bbase (se 3 (by rfl) ⟨608090, by rfl⟩ : syracuseStep 3243149 = 1216181) (by norm_num)
theorem B9231509 : Blo 1439539 9231509 := bbase (se 6 (by rfl) ⟨216363, by rfl⟩ : syracuseStep 9231509 = 432727) (by norm_num)
theorem B2161829 : Blo 1439539 2161829 := bbase (se 4 (by rfl) ⟨202671, by rfl⟩ : syracuseStep 2161829 = 405343) (by norm_num)
theorem B1621165 : Blo 1439539 1621165 := bbase (se 3 (by rfl) ⟨303968, by rfl⟩ : syracuseStep 1621165 = 607937) (by norm_num)
theorem B2432173 : Blo 1439539 2432173 := bbase (se 3 (by rfl) ⟨456032, by rfl⟩ : syracuseStep 2432173 = 912065) (by norm_num)
theorem B2161853 : Blo 1439539 2161853 := bbase (se 3 (by rfl) ⟨405347, by rfl⟩ : syracuseStep 2161853 = 810695) (by norm_num)
theorem B1621201 : Blo 1439539 1621201 := bbase (se 2 (by rfl) ⟨607950, by rfl⟩ : syracuseStep 1621201 = 1215901) (by norm_num)
theorem B2161877 : Blo 1439539 2161877 := bbase (se 7 (by rfl) ⟨25334, by rfl⟩ : syracuseStep 2161877 = 50669) (by norm_num)
theorem B3243221 : Blo 1439539 3243221 := bbase (se 7 (by rfl) ⟨38006, by rfl⟩ : syracuseStep 3243221 = 76013) (by norm_num)
theorem B1539281 : Blo 1439539 1539281 := bbase (se 2 (by rfl) ⟨577230, by rfl⟩ : syracuseStep 1539281 = 1154461) (by norm_num)
theorem B2161901 : Blo 1439539 2161901 := bbase (se 3 (by rfl) ⟨405356, by rfl⟩ : syracuseStep 2161901 = 810713) (by norm_num)
theorem B1621237 : Blo 1439539 1621237 := bbase (se 5 (by rfl) ⟨75995, by rfl⟩ : syracuseStep 1621237 = 151991) (by norm_num)
theorem B2161925 : Blo 1439539 2161925 := bbase (se 4 (by rfl) ⟨202680, by rfl⟩ : syracuseStep 2161925 = 405361) (by norm_num)
theorem B2432261 : Blo 1439539 2432261 := bbase (se 4 (by rfl) ⟨228024, by rfl⟩ : syracuseStep 2432261 = 456049) (by norm_num)
theorem B5471509 : Blo 1439539 5471509 := bbase (se 6 (by rfl) ⟨128238, by rfl⟩ : syracuseStep 5471509 = 256477) (by norm_num)
theorem B1621273 : Blo 1439539 1621273 := bbase (se 2 (by rfl) ⟨607977, by rfl⟩ : syracuseStep 1621273 = 1215955) (by norm_num)
theorem B2161949 : Blo 1439539 2161949 := bbase (se 3 (by rfl) ⟨405365, by rfl⟩ : syracuseStep 2161949 = 810731) (by norm_num)
theorem B3243293 : Blo 1439539 3243293 := bbase (se 3 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 3243293 = 1216235) (by norm_num)
theorem B2161973 : Blo 1439539 2161973 := bbase (se 5 (by rfl) ⟨101342, by rfl⟩ : syracuseStep 2161973 = 202685) (by norm_num)
theorem B1621309 : Blo 1439539 1621309 := bbase (se 3 (by rfl) ⟨303995, by rfl⟩ : syracuseStep 1621309 = 607991) (by norm_num)
theorem B2161997 : Blo 1439539 2161997 := bbase (se 3 (by rfl) ⟨405374, by rfl⟩ : syracuseStep 2161997 = 810749) (by norm_num)
theorem B1621345 : Blo 1439539 1621345 := bbase (se 2 (by rfl) ⟨608004, by rfl⟩ : syracuseStep 1621345 = 1216009) (by norm_num)
theorem B2162021 : Blo 1439539 2162021 := bbase (se 4 (by rfl) ⟨202689, by rfl⟩ : syracuseStep 2162021 = 405379) (by norm_num)
theorem B3243365 : Blo 1439539 3243365 := bbase (se 4 (by rfl) ⟨304065, by rfl⟩ : syracuseStep 3243365 = 608131) (by norm_num)
theorem B3644797 : Blo 1439539 3644797 := bbase (se 3 (by rfl) ⟨683399, by rfl⟩ : syracuseStep 3644797 = 1366799) (by norm_num)
theorem B2162045 : Blo 1439539 2162045 := bbase (se 3 (by rfl) ⟨405383, by rfl⟩ : syracuseStep 2162045 = 810767) (by norm_num)
theorem B1621381 : Blo 1439539 1621381 := bbase (se 4 (by rfl) ⟨152004, by rfl⟩ : syracuseStep 1621381 = 304009) (by norm_num)
theorem B2432389 : Blo 1439539 2432389 := bbase (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) (by norm_num)
theorem B2162069 : Blo 1439539 2162069 := bbase (se 6 (by rfl) ⟨50673, by rfl⟩ : syracuseStep 2162069 = 101347) (by norm_num)
theorem B1621417 : Blo 1439539 1621417 := bbase (se 2 (by rfl) ⟨608031, by rfl⟩ : syracuseStep 1621417 = 1216063) (by norm_num)
theorem B2162093 : Blo 1439539 2162093 := bbase (se 3 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 2162093 = 810785) (by norm_num)
theorem B3243437 : Blo 1439539 3243437 := bbase (se 3 (by rfl) ⟨608144, by rfl⟩ : syracuseStep 3243437 = 1216289) (by norm_num)
theorem B6151621 : Blo 1439539 6151621 := bbase (se 4 (by rfl) ⟨576714, by rfl⟩ : syracuseStep 6151621 = 1153429) (by norm_num)
theorem B2162117 : Blo 1439539 2162117 := bbase (se 4 (by rfl) ⟨202698, by rfl⟩ : syracuseStep 2162117 = 405397) (by norm_num)
theorem B1621453 : Blo 1439539 1621453 := bbase (se 3 (by rfl) ⟨304022, by rfl⟩ : syracuseStep 1621453 = 608045) (by norm_num)
theorem B2162141 : Blo 1439539 2162141 := bbase (se 3 (by rfl) ⟨405401, by rfl⟩ : syracuseStep 2162141 = 810803) (by norm_num)
theorem B2432477 : Blo 1439539 2432477 := bbase (se 3 (by rfl) ⟨456089, by rfl⟩ : syracuseStep 2432477 = 912179) (by norm_num)
theorem B3644909 : Blo 1439539 3644909 := bbase (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) (by norm_num)
theorem B1621489 : Blo 1439539 1621489 := bbase (se 2 (by rfl) ⟨608058, by rfl⟩ : syracuseStep 1621489 = 1216117) (by norm_num)
theorem B10673653 : Blo 1439539 10673653 := bbase (se 5 (by rfl) ⟨500327, by rfl⟩ : syracuseStep 10673653 = 1000655) (by norm_num)
theorem B2162165 : Blo 1439539 2162165 := bbase (se 5 (by rfl) ⟨101351, by rfl⟩ : syracuseStep 2162165 = 202703) (by norm_num)
theorem B2162189 : Blo 1439539 2162189 := bbase (se 3 (by rfl) ⟨405410, by rfl⟩ : syracuseStep 2162189 = 810821) (by norm_num)
theorem B8199701 : Blo 1439539 8199701 := bbase (se 6 (by rfl) ⟨192180, by rfl⟩ : syracuseStep 8199701 = 384361) (by norm_num)
theorem B4562453 : Blo 1439539 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B1621525 : Blo 1439539 1621525 := bbase (se 6 (by rfl) ⟨38004, by rfl⟩ : syracuseStep 1621525 = 76009) (by norm_num)
theorem B2162213 : Blo 1439539 2162213 := bbase (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) (by norm_num)
theorem B1621561 : Blo 1439539 1621561 := bbase (se 2 (by rfl) ⟨608085, by rfl⟩ : syracuseStep 1621561 = 1216171) (by norm_num)
theorem B2162237 : Blo 1439539 2162237 := bbase (se 3 (by rfl) ⟨405419, by rfl⟩ : syracuseStep 2162237 = 810839) (by norm_num)
theorem B5471813 : Blo 1439539 5471813 := bbase (se 4 (by rfl) ⟨512982, by rfl⟩ : syracuseStep 5471813 = 1025965) (by norm_num)
theorem B2162261 : Blo 1439539 2162261 := bbase (se 8 (by rfl) ⟨12669, by rfl⟩ : syracuseStep 2162261 = 25339) (by norm_num)
theorem B1621597 : Blo 1439539 1621597 := bbase (se 3 (by rfl) ⟨304049, by rfl⟩ : syracuseStep 1621597 = 608099) (by norm_num)
theorem B2162285 : Blo 1439539 2162285 := bbase (se 3 (by rfl) ⟨405428, by rfl⟩ : syracuseStep 2162285 = 810857) (by norm_num)
theorem B7290485 : Blo 1439539 7290485 := bbase (se 5 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 7290485 = 683483) (by norm_num)
theorem B6921845 : Blo 1439539 6921845 := bbase (se 5 (by rfl) ⟨324461, by rfl⟩ : syracuseStep 6921845 = 648923) (by norm_num)
theorem B1621633 : Blo 1439539 1621633 := bbase (se 2 (by rfl) ⟨608112, by rfl⟩ : syracuseStep 1621633 = 1216225) (by norm_num)
theorem B2162309 : Blo 1439539 2162309 := bbase (se 4 (by rfl) ⟨202716, by rfl⟩ : syracuseStep 2162309 = 405433) (by norm_num)
theorem B8756885 : Blo 1439539 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B1621669 : Blo 1439539 1621669 := bbase (se 4 (by rfl) ⟨152031, by rfl⟩ : syracuseStep 1621669 = 304063) (by norm_num)
theorem B3645101 : Blo 1439539 3645101 := bbase (se 3 (by rfl) ⟨683456, by rfl⟩ : syracuseStep 3645101 = 1366913) (by norm_num)
theorem B1621705 : Blo 1439539 1621705 := bbase (se 2 (by rfl) ⟨608139, by rfl⟩ : syracuseStep 1621705 = 1216279) (by norm_num)
theorem B2735869 : Blo 1439539 2735869 := bbase (se 3 (by rfl) ⟨512975, by rfl⟩ : syracuseStep 2735869 = 1025951) (by norm_num)
theorem B6922037 : Blo 1439539 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B9362261 : Blo 1439539 9362261 := bbase (se 9 (by rfl) ⟨27428, by rfl⟩ : syracuseStep 9362261 = 54857) (by norm_num)
theorem B4611973 : Blo 1439539 4611973 := bbase (se 4 (by rfl) ⟨432372, by rfl⟩ : syracuseStep 4611973 = 864745) (by norm_num)
theorem B2736013 : Blo 1439539 2736013 := bbase (se 3 (by rfl) ⟨513002, by rfl⟩ : syracuseStep 2736013 = 1026005) (by norm_num)
theorem B5472269 : Blo 1439539 5472269 := bstep (se 3 (by rfl) ⟨1026050, by rfl⟩ : syracuseStep 5472269 = 2052101) B2052101
theorem B2736355 : Blo 1439539 2736355 := bstep (se 1 (by rfl) ⟨2052266, by rfl⟩ : syracuseStep 2736355 = 4104533) B4104533
theorem B4104589 : Blo 1439539 4104589 := bstep (se 3 (by rfl) ⟨769610, by rfl⟩ : syracuseStep 4104589 = 1539221) B1539221
theorem B7791011 : Blo 1439539 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B1753555 : Blo 1439539 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B29573603 : Blo 1439539 29573603 := bstep (se 1 (by rfl) ⟨22180202, by rfl⟩ : syracuseStep 29573603 = 44360405) B44360405
theorem B4612589 : Blo 1439539 4612589 := bstep (se 3 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 4612589 = 1729721) B1729721
theorem B7782925 : Blo 1439539 7782925 := bstep (se 3 (by rfl) ⟨1459298, by rfl⟩ : syracuseStep 7782925 = 2918597) B2918597
theorem B4104749 : Blo 1439539 4104749 := bstep (se 3 (by rfl) ⟨769640, by rfl⟩ : syracuseStep 4104749 = 1539281) B1539281
theorem B4612717 : Blo 1439539 4612717 := bstep (se 3 (by rfl) ⟨864884, by rfl⟩ : syracuseStep 4612717 = 1729769) B1729769
theorem B4858541 : Blo 1439539 4858541 := bstep (se 3 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 4858541 = 1821953) B1821953
theorem B4858595 : Blo 1439539 4858595 := bstep (se 1 (by rfl) ⟨3643946, by rfl⟩ : syracuseStep 4858595 = 7287893) B7287893
theorem B7291619 : Blo 1439539 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B4104931 : Blo 1439539 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B3892045 : Blo 1439539 3892045 := bstep (se 3 (by rfl) ⟨729758, by rfl⟩ : syracuseStep 3892045 = 1459517) B1459517
theorem B3646417 : Blo 1439539 3646417 := bstep (se 2 (by rfl) ⟨1367406, by rfl⟩ : syracuseStep 3646417 = 2734813) B2734813
theorem B4858865 : Blo 1439539 4858865 := bstep (se 2 (by rfl) ⟨1822074, by rfl⟩ : syracuseStep 4858865 = 3644149) B3644149
theorem B3646691 : Blo 1439539 3646691 := bstep (se 1 (by rfl) ⟨2735018, by rfl⟩ : syracuseStep 3646691 = 5470037) B5470037
theorem B9233635 : Blo 1439539 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B9225485 : Blo 1439539 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B12166541 : Blo 1439539 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B3646883 : Blo 1439539 3646883 := bstep (se 1 (by rfl) ⟨2735162, by rfl⟩ : syracuseStep 3646883 = 5470325) B5470325
theorem B4859405 : Blo 1439539 4859405 := bstep (se 3 (by rfl) ⟨911138, by rfl⟩ : syracuseStep 4859405 = 1822277) B1822277
theorem B7292429 : Blo 1439539 7292429 := bstep (se 3 (by rfl) ⟨1367330, by rfl⟩ : syracuseStep 7292429 = 2734661) B2734661
theorem B4859459 : Blo 1439539 4859459 := bstep (se 1 (by rfl) ⟨3644594, by rfl⟩ : syracuseStep 4859459 = 7289189) B7289189
theorem B2049715 : Blo 1439539 2049715 := bstep (se 1 (by rfl) ⟨1537286, by rfl⟩ : syracuseStep 2049715 = 3074573) B3074573
theorem B4859729 : Blo 1439539 4859729 := bstep (se 2 (by rfl) ⟨1822398, by rfl⟩ : syracuseStep 4859729 = 3644797) B3644797
theorem B20760461 : Blo 1439539 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B8202161 : Blo 1439539 8202161 := bstep (se 2 (by rfl) ⟨3075810, by rfl⟩ : syracuseStep 8202161 = 6151621) B6151621
theorem B3286979 : Blo 1439539 3286979 := bstep (se 1 (by rfl) ⟨2465234, by rfl⟩ : syracuseStep 3286979 = 4930469) B4930469
theorem B14231537 : Blo 1439539 14231537 := bstep (se 2 (by rfl) ⟨5336826, by rfl⟩ : syracuseStep 14231537 = 10673653) B10673653
theorem B2050051 : Blo 1439539 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B7784525 : Blo 1439539 7784525 := bstep (se 3 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 7784525 = 2919197) B2919197
theorem B6154339 : Blo 1439539 6154339 := bstep (se 1 (by rfl) ⟨4615754, by rfl⟩ : syracuseStep 6154339 = 9231509) B9231509
theorem B3647825 : Blo 1439539 3647825 := bstep (se 2 (by rfl) ⟨1367934, by rfl⟩ : syracuseStep 3647825 = 2735869) B2735869
theorem B5466467 : Blo 1439539 5466467 := bstep (se 1 (by rfl) ⟨4099850, by rfl⟩ : syracuseStep 5466467 = 8199701) B8199701
theorem B4860269 : Blo 1439539 4860269 := bstep (se 3 (by rfl) ⟨911300, by rfl⟩ : syracuseStep 4860269 = 1822601) B1822601
theorem B3647875 : Blo 1439539 3647875 := bstep (se 1 (by rfl) ⟨2735906, by rfl⟩ : syracuseStep 3647875 = 5471813) B5471813
theorem B4860323 : Blo 1439539 4860323 := bstep (se 1 (by rfl) ⟨3645242, by rfl⟩ : syracuseStep 4860323 = 7290485) B7290485
theorem B4614563 : Blo 1439539 4614563 := bstep (se 1 (by rfl) ⟨3460922, by rfl⟩ : syracuseStep 4614563 = 6921845) B6921845
theorem B3648017 : Blo 1439539 3648017 := bstep (se 2 (by rfl) ⟨1368006, by rfl⟩ : syracuseStep 3648017 = 2736013) B2736013
theorem B4614691 : Blo 1439539 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B2050609 : Blo 1439539 2050609 := bstep (se 2 (by rfl) ⟨768978, by rfl⟩ : syracuseStep 2050609 = 1537957) B1537957
theorem B2050643 : Blo 1439539 2050643 := bstep (se 1 (by rfl) ⟨1537982, by rfl⟩ : syracuseStep 2050643 = 3075965) B3075965
theorem B4860593 : Blo 1439539 4860593 := bstep (se 2 (by rfl) ⟨1822722, by rfl⟩ : syracuseStep 4860593 = 3645445) B3645445
theorem B4614833 : Blo 1439539 4614833 := bstep (se 2 (by rfl) ⟨1730562, by rfl⟩ : syracuseStep 4614833 = 3461125) B3461125
theorem B2190019 : Blo 1439539 2190019 := bstep (se 1 (by rfl) ⟨1642514, by rfl⟩ : syracuseStep 2190019 = 3285029) B3285029
theorem B2190097 : Blo 1439539 2190097 := bstep (se 2 (by rfl) ⟨821286, by rfl⟩ : syracuseStep 2190097 = 1642573) B1642573
theorem B4614947 : Blo 1439539 4614947 := bstep (se 1 (by rfl) ⟨3461210, by rfl⟩ : syracuseStep 4614947 = 6922421) B6922421
theorem B4926253 : Blo 1439539 4926253 := bstep (se 3 (by rfl) ⟨923672, by rfl⟩ : syracuseStep 4926253 = 1847345) B1847345
theorem B3074915 : Blo 1439539 3074915 := bstep (se 1 (by rfl) ⟨2306186, by rfl⟩ : syracuseStep 3074915 = 4612373) B4612373
theorem B3459971 : Blo 1439539 3459971 := bstep (se 1 (by rfl) ⟨2594978, by rfl⟩ : syracuseStep 3459971 = 5189957) B5189957
theorem B3075025 : Blo 1439539 3075025 := bstep (se 2 (by rfl) ⟨1153134, by rfl⟩ : syracuseStep 3075025 = 2306269) B2306269
theorem B5467121 : Blo 1439539 5467121 := bstep (se 2 (by rfl) ⟨2050170, by rfl⟩ : syracuseStep 5467121 = 4100341) B4100341
theorem B7892045 : Blo 1439539 7892045 := bstep (se 3 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 7892045 = 2959517) B2959517
theorem B2919505 : Blo 1439539 2919505 := bstep (se 2 (by rfl) ⟨1094814, by rfl⟩ : syracuseStep 2919505 = 2189629) B2189629
theorem B2051201 : Blo 1439539 2051201 := bstep (se 2 (by rfl) ⟨769200, by rfl⟩ : syracuseStep 2051201 = 1538401) B1538401
theorem B9235633 : Blo 1439539 9235633 := bstep (se 2 (by rfl) ⟨3463362, by rfl⟩ : syracuseStep 9235633 = 6926725) B6926725
theorem B4861133 : Blo 1439539 4861133 := bstep (se 3 (by rfl) ⟨911462, by rfl⟩ : syracuseStep 4861133 = 1822925) B1822925
theorem B2051281 : Blo 1439539 2051281 := bstep (se 2 (by rfl) ⟨769230, by rfl⟩ : syracuseStep 2051281 = 1538461) B1538461
theorem B3239153 : Blo 1439539 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B3239171 : Blo 1439539 3239171 := bstep (se 1 (by rfl) ⟨2429378, by rfl⟩ : syracuseStep 3239171 = 4858757) B4858757
theorem B4861187 : Blo 1439539 4861187 := bstep (se 1 (by rfl) ⟨3645890, by rfl⟩ : syracuseStep 4861187 = 7291781) B7291781
theorem B3697937 : Blo 1439539 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B4099373 : Blo 1439539 4099373 := bstep (se 3 (by rfl) ⟨768632, by rfl⟩ : syracuseStep 4099373 = 1537265) B1537265
theorem B8203619 : Blo 1439539 8203619 := bstep (se 1 (by rfl) ⟨6152714, by rfl⟩ : syracuseStep 8203619 = 12305429) B12305429
theorem B10931597 : Blo 1439539 10931597 := bstep (se 3 (by rfl) ⟨2049674, by rfl⟩ : syracuseStep 10931597 = 4099349) B4099349
theorem B1822115 : Blo 1439539 1822115 := bstep (se 1 (by rfl) ⟨1366586, by rfl⟩ : syracuseStep 1822115 = 2733173) B2733173
theorem B11685347 : Blo 1439539 11685347 := bstep (se 1 (by rfl) ⟨8764010, by rfl⟩ : syracuseStep 11685347 = 17528021) B17528021
theorem B11095523 : Blo 1439539 11095523 := bstep (se 1 (by rfl) ⟨8321642, by rfl⟩ : syracuseStep 11095523 = 16643285) B16643285
theorem B3239441 : Blo 1439539 3239441 := bstep (se 2 (by rfl) ⟨1214790, by rfl⟩ : syracuseStep 3239441 = 2429581) B2429581
theorem B4861457 : Blo 1439539 4861457 := bstep (se 2 (by rfl) ⟨1823046, by rfl⟩ : syracuseStep 4861457 = 3646093) B3646093
theorem B2190881 : Blo 1439539 2190881 := bstep (se 2 (by rfl) ⟨821580, by rfl⟩ : syracuseStep 2190881 = 1643161) B1643161
theorem B3239459 : Blo 1439539 3239459 := bstep (se 1 (by rfl) ⟨2429594, by rfl⟩ : syracuseStep 3239459 = 4859189) B4859189
theorem B4157027 : Blo 1439539 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B11685475 : Blo 1439539 11685475 := bstep (se 1 (by rfl) ⟨8764106, by rfl⟩ : syracuseStep 11685475 = 17528213) B17528213
theorem B6926093 : Blo 1439539 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B3239729 : Blo 1439539 3239729 := bstep (se 2 (by rfl) ⟨1214898, by rfl⟩ : syracuseStep 3239729 = 2429797) B2429797
theorem B3239747 : Blo 1439539 3239747 := bstep (se 1 (by rfl) ⟨2429810, by rfl⟩ : syracuseStep 3239747 = 4859621) B4859621
theorem B11235185 : Blo 1439539 11235185 := bstep (se 2 (by rfl) ⟨4213194, by rfl⟩ : syracuseStep 11235185 = 8426389) B8426389
theorem B2052067 : Blo 1439539 2052067 := bstep (se 1 (by rfl) ⟨1539050, by rfl⟩ : syracuseStep 2052067 = 3078101) B3078101
theorem B4861997 : Blo 1439539 4861997 := bstep (se 3 (by rfl) ⟨911624, by rfl⟩ : syracuseStep 4861997 = 1823249) B1823249
theorem B6156337 : Blo 1439539 6156337 := bstep (se 2 (by rfl) ⟨2308626, by rfl⟩ : syracuseStep 6156337 = 4617253) B4617253
theorem B3240017 : Blo 1439539 3240017 := bstep (se 2 (by rfl) ⟨1215006, by rfl⟩ : syracuseStep 3240017 = 2430013) B2430013
theorem B3240035 : Blo 1439539 3240035 := bstep (se 1 (by rfl) ⟨2430026, by rfl⟩ : syracuseStep 3240035 = 4860053) B4860053
theorem B1822819 : Blo 1439539 1822819 := bstep (se 1 (by rfl) ⟨1367114, by rfl⟩ : syracuseStep 1822819 = 2734229) B2734229
theorem B4862051 : Blo 1439539 4862051 := bstep (se 1 (by rfl) ⟨3646538, by rfl⟩ : syracuseStep 4862051 = 7293077) B7293077
theorem B2306243 : Blo 1439539 2306243 := bstep (se 1 (by rfl) ⟨1729682, by rfl⟩ : syracuseStep 2306243 = 3459365) B3459365
theorem B1822915 : Blo 1439539 1822915 := bstep (se 1 (by rfl) ⟨1367186, by rfl⟩ : syracuseStep 1822915 = 2734373) B2734373
theorem B3240305 : Blo 1439539 3240305 := bstep (se 2 (by rfl) ⟨1215114, by rfl⟩ : syracuseStep 3240305 = 2430229) B2430229
theorem B4862321 : Blo 1439539 4862321 := bstep (se 2 (by rfl) ⟨1823370, by rfl⟩ : syracuseStep 4862321 = 3646741) B3646741
theorem B7295345 : Blo 1439539 7295345 := bstep (se 2 (by rfl) ⟨2735754, by rfl⟩ : syracuseStep 7295345 = 5471509) B5471509
theorem B3240323 : Blo 1439539 3240323 := bstep (se 1 (by rfl) ⟨2430242, by rfl⟩ : syracuseStep 3240323 = 4860485) B4860485
theorem B2429345 : Blo 1439539 2429345 := bstep (se 2 (by rfl) ⟨911004, by rfl⟩ : syracuseStep 2429345 = 1822009) B1822009
theorem B5468579 : Blo 1439539 5468579 := bstep (se 1 (by rfl) ⟨4101434, by rfl⟩ : syracuseStep 5468579 = 8202869) B8202869
theorem B5468593 : Blo 1439539 5468593 := bstep (se 2 (by rfl) ⟨2050722, by rfl⟩ : syracuseStep 5468593 = 4101445) B4101445
theorem B10523077 : Blo 1439539 10523077 := bstep (se 4 (by rfl) ⟨986538, by rfl⟩ : syracuseStep 10523077 = 1973077) B1973077
theorem B4100557 : Blo 1439539 4100557 := bstep (se 3 (by rfl) ⟨768854, by rfl⟩ : syracuseStep 4100557 = 1537709) B1537709
theorem B4616689 : Blo 1439539 4616689 := bstep (se 2 (by rfl) ⟨1731258, by rfl⟩ : syracuseStep 4616689 = 3462517) B3462517
theorem B2429473 : Blo 1439539 2429473 := bstep (se 2 (by rfl) ⟨911052, by rfl⟩ : syracuseStep 2429473 = 1822105) B1822105
theorem B2429507 : Blo 1439539 2429507 := bstep (se 1 (by rfl) ⟨1822130, by rfl⟩ : syracuseStep 2429507 = 3644261) B3644261
theorem B1643107 : Blo 1439539 1643107 := bstep (se 1 (by rfl) ⟨1232330, by rfl⟩ : syracuseStep 1643107 = 2464661) B2464661
theorem B3240593 : Blo 1439539 3240593 := bstep (se 2 (by rfl) ⟨1215222, by rfl⟩ : syracuseStep 3240593 = 2430445) B2430445
theorem B3240611 : Blo 1439539 3240611 := bstep (se 1 (by rfl) ⟨2430458, by rfl⟩ : syracuseStep 3240611 = 4860917) B4860917
theorem B1823411 : Blo 1439539 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B2429635 : Blo 1439539 2429635 := bstep (se 1 (by rfl) ⟨1822226, by rfl⟩ : syracuseStep 2429635 = 3644453) B3644453
theorem B2159315 : Blo 1439539 2159315 := bstep (se 1 (by rfl) ⟨1619486, by rfl⟩ : syracuseStep 2159315 = 3238973) B3238973
theorem B2159345 : Blo 1439539 2159345 := bstep (se 2 (by rfl) ⟨809754, by rfl⟩ : syracuseStep 2159345 = 1619509) B1619509
theorem B1946369 : Blo 1439539 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B2159363 : Blo 1439539 2159363 := bstep (se 1 (by rfl) ⟨1619522, by rfl⟩ : syracuseStep 2159363 = 3239045) B3239045
theorem B1643267 : Blo 1439539 1643267 := bstep (se 1 (by rfl) ⟨1232450, by rfl⟩ : syracuseStep 1643267 = 2464901) B2464901
theorem B3945233 : Blo 1439539 3945233 := bstep (se 2 (by rfl) ⟨1479462, by rfl⟩ : syracuseStep 3945233 = 2958925) B2958925
theorem B2159393 : Blo 1439539 2159393 := bstep (se 2 (by rfl) ⟨809772, by rfl⟩ : syracuseStep 2159393 = 1619545) B1619545
theorem B2159411 : Blo 1439539 2159411 := bstep (se 1 (by rfl) ⟨1619558, by rfl⟩ : syracuseStep 2159411 = 3239117) B3239117
theorem B2159441 : Blo 1439539 2159441 := bstep (se 2 (by rfl) ⟨809790, by rfl⟩ : syracuseStep 2159441 = 1619581) B1619581
theorem B2429777 : Blo 1439539 2429777 := bstep (se 2 (by rfl) ⟨911166, by rfl⟩ : syracuseStep 2429777 = 1822333) B1822333
theorem B2159459 : Blo 1439539 2159459 := bstep (se 1 (by rfl) ⟨1619594, by rfl⟩ : syracuseStep 2159459 = 3239189) B3239189
theorem B6746993 : Blo 1439539 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B2159489 : Blo 1439539 2159489 := bstep (se 2 (by rfl) ⟨809808, by rfl⟩ : syracuseStep 2159489 = 1619617) B1619617
theorem B4862861 : Blo 1439539 4862861 := bstep (se 3 (by rfl) ⟨911786, by rfl⟩ : syracuseStep 4862861 = 1823573) B1823573
theorem B4158353 : Blo 1439539 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B24966029 : Blo 1439539 24966029 := bstep (se 3 (by rfl) ⟨4681130, by rfl⟩ : syracuseStep 24966029 = 9362261) B9362261
theorem B2159507 : Blo 1439539 2159507 := bstep (se 1 (by rfl) ⟨1619630, by rfl⟩ : syracuseStep 2159507 = 3239261) B3239261
theorem B2159537 : Blo 1439539 2159537 := bstep (se 2 (by rfl) ⟨809826, by rfl⟩ : syracuseStep 2159537 = 1619653) B1619653
theorem B3240881 : Blo 1439539 3240881 := bstep (se 2 (by rfl) ⟨1215330, by rfl⟩ : syracuseStep 3240881 = 2430661) B2430661
theorem B3077041 : Blo 1439539 3077041 := bstep (se 2 (by rfl) ⟨1153890, by rfl⟩ : syracuseStep 3077041 = 2307781) B2307781
theorem B2159555 : Blo 1439539 2159555 := bstep (se 1 (by rfl) ⟨1619666, by rfl⟩ : syracuseStep 2159555 = 3239333) B3239333
theorem B3240899 : Blo 1439539 3240899 := bstep (se 1 (by rfl) ⟨2430674, by rfl⟩ : syracuseStep 3240899 = 4861349) B4861349
theorem B4862915 : Blo 1439539 4862915 := bstep (se 1 (by rfl) ⟨3647186, by rfl⟩ : syracuseStep 4862915 = 7294373) B7294373
theorem B2429905 : Blo 1439539 2429905 := bstep (se 2 (by rfl) ⟨911214, by rfl⟩ : syracuseStep 2429905 = 1822429) B1822429
theorem B2159585 : Blo 1439539 2159585 := bstep (se 2 (by rfl) ⟨809844, by rfl⟩ : syracuseStep 2159585 = 1619689) B1619689
theorem B2159603 : Blo 1439539 2159603 := bstep (se 1 (by rfl) ⟨1619702, by rfl⟩ : syracuseStep 2159603 = 3239405) B3239405
theorem B2429939 : Blo 1439539 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B2159633 : Blo 1439539 2159633 := bstep (se 2 (by rfl) ⟨809862, by rfl⟩ : syracuseStep 2159633 = 1619725) B1619725
theorem B2307089 : Blo 1439539 2307089 := bstep (se 2 (by rfl) ⟨865158, by rfl⟩ : syracuseStep 2307089 = 1730317) B1730317
theorem B2159651 : Blo 1439539 2159651 := bstep (se 1 (by rfl) ⟨1619738, by rfl⟩ : syracuseStep 2159651 = 3239477) B3239477
theorem B2159681 : Blo 1439539 2159681 := bstep (se 2 (by rfl) ⟨809880, by rfl⟩ : syracuseStep 2159681 = 1619761) B1619761
theorem B2159699 : Blo 1439539 2159699 := bstep (se 1 (by rfl) ⟨1619774, by rfl⟩ : syracuseStep 2159699 = 3239549) B3239549
theorem B5837923 : Blo 1439539 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B2159729 : Blo 1439539 2159729 := bstep (se 2 (by rfl) ⟨809898, by rfl⟩ : syracuseStep 2159729 = 1619797) B1619797
theorem B2430067 : Blo 1439539 2430067 := bstep (se 1 (by rfl) ⟨1822550, by rfl⟩ : syracuseStep 2430067 = 3645101) B3645101
theorem B2159747 : Blo 1439539 2159747 := bstep (se 1 (by rfl) ⟨1619810, by rfl⟩ : syracuseStep 2159747 = 3239621) B3239621
theorem B2159777 : Blo 1439539 2159777 := bstep (se 2 (by rfl) ⟨809916, by rfl⟩ : syracuseStep 2159777 = 1619833) B1619833
theorem B6149297 : Blo 1439539 6149297 := bstep (se 2 (by rfl) ⟨2305986, by rfl⟩ : syracuseStep 6149297 = 4611973) B4611973
theorem B1946801 : Blo 1439539 1946801 := bstep (se 2 (by rfl) ⟨730050, by rfl⟩ : syracuseStep 1946801 = 1460101) B1460101
theorem B2159795 : Blo 1439539 2159795 := bstep (se 1 (by rfl) ⟨1619846, by rfl⟩ : syracuseStep 2159795 = 3239693) B3239693
theorem B1848515 : Blo 1439539 1848515 := bstep (se 1 (by rfl) ⟨1386386, by rfl⟩ : syracuseStep 1848515 = 2772773) B2772773
theorem B2159825 : Blo 1439539 2159825 := bstep (se 2 (by rfl) ⟨809934, by rfl⟩ : syracuseStep 2159825 = 1619869) B1619869
theorem B3241169 : Blo 1439539 3241169 := bstep (se 2 (by rfl) ⟨1215438, by rfl⟩ : syracuseStep 3241169 = 2430877) B2430877
theorem B4863185 : Blo 1439539 4863185 := bstep (se 2 (by rfl) ⟨1823694, by rfl⟩ : syracuseStep 4863185 = 3647389) B3647389
theorem B2159843 : Blo 1439539 2159843 := bstep (se 1 (by rfl) ⟨1619882, by rfl⟩ : syracuseStep 2159843 = 3239765) B3239765
theorem B3241187 : Blo 1439539 3241187 := bstep (se 1 (by rfl) ⟨2430890, by rfl⟩ : syracuseStep 3241187 = 4861781) B4861781
theorem B2159873 : Blo 1439539 2159873 := bstep (se 2 (by rfl) ⟨809952, by rfl⟩ : syracuseStep 2159873 = 1619905) B1619905
theorem B2430209 : Blo 1439539 2430209 := bstep (se 2 (by rfl) ⟨911328, by rfl⟩ : syracuseStep 2430209 = 1822657) B1822657
theorem B2159891 : Blo 1439539 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B2159921 : Blo 1439539 2159921 := bstep (se 2 (by rfl) ⟨809970, by rfl⟩ : syracuseStep 2159921 = 1619941) B1619941
theorem B2159939 : Blo 1439539 2159939 := bstep (se 1 (by rfl) ⟨1619954, by rfl⟩ : syracuseStep 2159939 = 3239909) B3239909
theorem B3077443 : Blo 1439539 3077443 := bstep (se 1 (by rfl) ⟨2308082, by rfl⟩ : syracuseStep 3077443 = 4616165) B4616165
theorem B2159969 : Blo 1439539 2159969 := bstep (se 2 (by rfl) ⟨809988, by rfl⟩ : syracuseStep 2159969 = 1619977) B1619977
theorem B2159987 : Blo 1439539 2159987 := bstep (se 1 (by rfl) ⟨1619990, by rfl⟩ : syracuseStep 2159987 = 3239981) B3239981
theorem B1824115 : Blo 1439539 1824115 := bstep (se 1 (by rfl) ⟨1368086, by rfl⟩ : syracuseStep 1824115 = 2736173) B2736173
theorem B2430337 : Blo 1439539 2430337 := bstep (se 2 (by rfl) ⟨911376, by rfl⟩ : syracuseStep 2430337 = 1822753) B1822753
theorem B2160017 : Blo 1439539 2160017 := bstep (se 2 (by rfl) ⟨810006, by rfl⟩ : syracuseStep 2160017 = 1620013) B1620013
theorem B1537427 : Blo 1439539 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B2160035 : Blo 1439539 2160035 := bstep (se 1 (by rfl) ⟨1620026, by rfl⟩ : syracuseStep 2160035 = 3240053) B3240053
theorem B2430371 : Blo 1439539 2430371 := bstep (se 1 (by rfl) ⟨1822778, by rfl⟩ : syracuseStep 2430371 = 3645557) B3645557
theorem B2160065 : Blo 1439539 2160065 := bstep (se 2 (by rfl) ⟨810024, by rfl⟩ : syracuseStep 2160065 = 1620049) B1620049
theorem B2160083 : Blo 1439539 2160083 := bstep (se 1 (by rfl) ⟨1620062, by rfl⟩ : syracuseStep 2160083 = 3240125) B3240125
theorem B1824211 : Blo 1439539 1824211 := bstep (se 1 (by rfl) ⟨1368158, by rfl⟩ : syracuseStep 1824211 = 2736317) B2736317
theorem B2160113 : Blo 1439539 2160113 := bstep (se 2 (by rfl) ⟨810042, by rfl⟩ : syracuseStep 2160113 = 1620085) B1620085
theorem B4101617 : Blo 1439539 4101617 := bstep (se 2 (by rfl) ⟨1538106, by rfl⟩ : syracuseStep 4101617 = 3076213) B3076213
theorem B3241457 : Blo 1439539 3241457 := bstep (se 2 (by rfl) ⟨1215546, by rfl⟩ : syracuseStep 3241457 = 2431093) B2431093
theorem B2160131 : Blo 1439539 2160131 := bstep (se 1 (by rfl) ⟨1620098, by rfl⟩ : syracuseStep 2160131 = 3240197) B3240197
theorem B3241475 : Blo 1439539 3241475 := bstep (se 1 (by rfl) ⟨2431106, by rfl⟩ : syracuseStep 3241475 = 4862213) B4862213
theorem B2921987 : Blo 1439539 2921987 := bstep (se 1 (by rfl) ⟨2191490, by rfl⟩ : syracuseStep 2921987 = 4382981) B4382981
theorem B2160161 : Blo 1439539 2160161 := bstep (se 2 (by rfl) ⟨810060, by rfl⟩ : syracuseStep 2160161 = 1620121) B1620121
theorem B1619491 : Blo 1439539 1619491 := bstep (se 1 (by rfl) ⟨1214618, by rfl⟩ : syracuseStep 1619491 = 2429237) B2429237
theorem B2430499 : Blo 1439539 2430499 := bstep (se 1 (by rfl) ⟨1822874, by rfl⟩ : syracuseStep 2430499 = 3645749) B3645749
theorem B2160179 : Blo 1439539 2160179 := bstep (se 1 (by rfl) ⟨1620134, by rfl⟩ : syracuseStep 2160179 = 3240269) B3240269
theorem B4617805 : Blo 1439539 4617805 := bstep (se 3 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 4617805 = 1731677) B1731677
theorem B2160209 : Blo 1439539 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B2160227 : Blo 1439539 2160227 := bstep (se 1 (by rfl) ⟨1620170, by rfl⟩ : syracuseStep 2160227 = 3240341) B3240341
theorem B2160257 : Blo 1439539 2160257 := bstep (se 2 (by rfl) ⟨810096, by rfl⟩ : syracuseStep 2160257 = 1620193) B1620193
theorem B2160275 : Blo 1439539 2160275 := bstep (se 1 (by rfl) ⟨1620206, by rfl⟩ : syracuseStep 2160275 = 3240413) B3240413
theorem B2160305 : Blo 1439539 2160305 := bstep (se 2 (by rfl) ⟨810114, by rfl⟩ : syracuseStep 2160305 = 1620229) B1620229
theorem B2430641 : Blo 1439539 2430641 := bstep (se 2 (by rfl) ⟨911490, by rfl⟩ : syracuseStep 2430641 = 1822981) B1822981
theorem B1619635 : Blo 1439539 1619635 := bstep (se 1 (by rfl) ⟨1214726, by rfl⟩ : syracuseStep 1619635 = 2429453) B2429453
theorem B2160323 : Blo 1439539 2160323 := bstep (se 1 (by rfl) ⟨1620242, by rfl⟩ : syracuseStep 2160323 = 3240485) B3240485
theorem B17757893 : Blo 1439539 17757893 := bstep (se 4 (by rfl) ⟨1664802, by rfl⟩ : syracuseStep 17757893 = 3329605) B3329605
theorem B2160353 : Blo 1439539 2160353 := bstep (se 2 (by rfl) ⟨810132, by rfl⟩ : syracuseStep 2160353 = 1620265) B1620265
theorem B4994797 : Blo 1439539 4994797 := bstep (se 3 (by rfl) ⟨936524, by rfl⟩ : syracuseStep 4994797 = 1873049) B1873049
theorem B4863725 : Blo 1439539 4863725 := bstep (se 3 (by rfl) ⟨911948, by rfl⟩ : syracuseStep 4863725 = 1823897) B1823897
theorem B4675313 : Blo 1439539 4675313 := bstep (se 2 (by rfl) ⟨1753242, by rfl⟩ : syracuseStep 4675313 = 3506485) B3506485
theorem B17528561 : Blo 1439539 17528561 := bstep (se 2 (by rfl) ⟨6573210, by rfl⟩ : syracuseStep 17528561 = 13146421) B13146421
theorem B2160371 : Blo 1439539 2160371 := bstep (se 1 (by rfl) ⟨1620278, by rfl⟩ : syracuseStep 2160371 = 3240557) B3240557
theorem B2307827 : Blo 1439539 2307827 := bstep (se 1 (by rfl) ⟨1730870, by rfl⟩ : syracuseStep 2307827 = 3461741) B3461741
theorem B2733841 : Blo 1439539 2733841 := bstep (se 2 (by rfl) ⟨1025190, by rfl⟩ : syracuseStep 2733841 = 2050381) B2050381
theorem B2160401 : Blo 1439539 2160401 := bstep (se 2 (by rfl) ⟨810150, by rfl⟩ : syracuseStep 2160401 = 1620301) B1620301
theorem B3241745 : Blo 1439539 3241745 := bstep (se 2 (by rfl) ⟨1215654, by rfl⟩ : syracuseStep 3241745 = 2431309) B2431309
theorem B2160419 : Blo 1439539 2160419 := bstep (se 1 (by rfl) ⟨1620314, by rfl⟩ : syracuseStep 2160419 = 3240629) B3240629
theorem B3241763 : Blo 1439539 3241763 := bstep (se 1 (by rfl) ⟨2431322, by rfl⟩ : syracuseStep 3241763 = 4862645) B4862645
theorem B4863779 : Blo 1439539 4863779 := bstep (se 1 (by rfl) ⟨3647834, by rfl⟩ : syracuseStep 4863779 = 7295669) B7295669
theorem B7296803 : Blo 1439539 7296803 := bstep (se 1 (by rfl) ⟨5472602, by rfl⟩ : syracuseStep 7296803 = 10945205) B10945205
theorem B2430769 : Blo 1439539 2430769 := bstep (se 2 (by rfl) ⟨911538, by rfl⟩ : syracuseStep 2430769 = 1823077) B1823077
theorem B1439539 : Blo 1439539 1439539 := bstep (se 1 (by rfl) ⟨1079654, by rfl⟩ : syracuseStep 1439539 = 2159309) B2159309
theorem B2160449 : Blo 1439539 2160449 := bstep (se 2 (by rfl) ⟨810168, by rfl⟩ : syracuseStep 2160449 = 1620337) B1620337
theorem B1439555 : Blo 1439539 1439555 := bstep (se 1 (by rfl) ⟨1079666, by rfl⟩ : syracuseStep 1439555 = 2159333) B2159333
theorem B1619779 : Blo 1439539 1619779 := bstep (se 1 (by rfl) ⟨1214834, by rfl⟩ : syracuseStep 1619779 = 2429669) B2429669
theorem B6149965 : Blo 1439539 6149965 := bstep (se 3 (by rfl) ⟨1153118, by rfl⟩ : syracuseStep 6149965 = 2306237) B2306237
theorem B4380497 : Blo 1439539 4380497 := bstep (se 2 (by rfl) ⟨1642686, by rfl⟩ : syracuseStep 4380497 = 3285373) B3285373
theorem B1439571 : Blo 1439539 1439571 := bstep (se 1 (by rfl) ⟨1079678, by rfl⟩ : syracuseStep 1439571 = 2159357) B2159357
theorem B2160467 : Blo 1439539 2160467 := bstep (se 1 (by rfl) ⟨1620350, by rfl⟩ : syracuseStep 2160467 = 3240701) B3240701
theorem B2430803 : Blo 1439539 2430803 := bstep (se 1 (by rfl) ⟨1823102, by rfl⟩ : syracuseStep 2430803 = 3646205) B3646205
theorem B1439587 : Blo 1439539 1439587 := bstep (se 1 (by rfl) ⟨1079690, by rfl⟩ : syracuseStep 1439587 = 2159381) B2159381
theorem B5470051 : Blo 1439539 5470051 := bstep (se 1 (by rfl) ⟨4102538, by rfl⟩ : syracuseStep 5470051 = 8205077) B8205077
theorem B2160497 : Blo 1439539 2160497 := bstep (se 2 (by rfl) ⟨810186, by rfl⟩ : syracuseStep 2160497 = 1620373) B1620373
theorem B15578993 : Blo 1439539 15578993 := bstep (se 2 (by rfl) ⟨5842122, by rfl⟩ : syracuseStep 15578993 = 11684245) B11684245
theorem B1439603 : Blo 1439539 1439603 := bstep (se 1 (by rfl) ⟨1079702, by rfl⟩ : syracuseStep 1439603 = 2159405) B2159405
theorem B1439619 : Blo 1439539 1439619 := bstep (se 1 (by rfl) ⟨1079714, by rfl⟩ : syracuseStep 1439619 = 2159429) B2159429
theorem B2160515 : Blo 1439539 2160515 := bstep (se 1 (by rfl) ⟨1620386, by rfl⟩ : syracuseStep 2160515 = 3240773) B3240773
theorem B1439635 : Blo 1439539 1439635 := bstep (se 1 (by rfl) ⟨1079726, by rfl⟩ : syracuseStep 1439635 = 2159453) B2159453
theorem B2160545 : Blo 1439539 2160545 := bstep (se 2 (by rfl) ⟨810204, by rfl⟩ : syracuseStep 2160545 = 1620409) B1620409
theorem B1439651 : Blo 1439539 1439651 := bstep (se 1 (by rfl) ⟨1079738, by rfl⟩ : syracuseStep 1439651 = 2159477) B2159477
theorem B6920113 : Blo 1439539 6920113 := bstep (se 2 (by rfl) ⟨2595042, by rfl⟩ : syracuseStep 6920113 = 5190085) B5190085
theorem B1439667 : Blo 1439539 1439667 := bstep (se 1 (by rfl) ⟨1079750, by rfl⟩ : syracuseStep 1439667 = 2159501) B2159501
theorem B2160563 : Blo 1439539 2160563 := bstep (se 1 (by rfl) ⟨1620422, by rfl⟩ : syracuseStep 2160563 = 3240845) B3240845
theorem B1439683 : Blo 1439539 1439683 := bstep (se 1 (by rfl) ⟨1079762, by rfl⟩ : syracuseStep 1439683 = 2159525) B2159525
theorem B2160593 : Blo 1439539 2160593 := bstep (se 2 (by rfl) ⟨810222, by rfl⟩ : syracuseStep 2160593 = 1620445) B1620445
theorem B1439699 : Blo 1439539 1439699 := bstep (se 1 (by rfl) ⟨1079774, by rfl⟩ : syracuseStep 1439699 = 2159549) B2159549
theorem B1619923 : Blo 1439539 1619923 := bstep (se 1 (by rfl) ⟨1214942, by rfl⟩ : syracuseStep 1619923 = 2429885) B2429885
theorem B2430931 : Blo 1439539 2430931 := bstep (se 1 (by rfl) ⟨1823198, by rfl⟩ : syracuseStep 2430931 = 3646397) B3646397
theorem B1439715 : Blo 1439539 1439715 := bstep (se 1 (by rfl) ⟨1079786, by rfl⟩ : syracuseStep 1439715 = 2159573) B2159573
theorem B2160611 : Blo 1439539 2160611 := bstep (se 1 (by rfl) ⟨1620458, by rfl⟩ : syracuseStep 2160611 = 3240917) B3240917
theorem B1439731 : Blo 1439539 1439731 := bstep (se 1 (by rfl) ⟨1079798, by rfl⟩ : syracuseStep 1439731 = 2159597) B2159597
theorem B2160641 : Blo 1439539 2160641 := bstep (se 2 (by rfl) ⟨810240, by rfl⟩ : syracuseStep 2160641 = 1620481) B1620481
theorem B1439747 : Blo 1439539 1439747 := bstep (se 1 (by rfl) ⟨1079810, by rfl⟩ : syracuseStep 1439747 = 2159621) B2159621
theorem B1439763 : Blo 1439539 1439763 := bstep (se 1 (by rfl) ⟨1079822, by rfl⟩ : syracuseStep 1439763 = 2159645) B2159645
theorem B2160659 : Blo 1439539 2160659 := bstep (se 1 (by rfl) ⟨1620494, by rfl⟩ : syracuseStep 2160659 = 3240989) B3240989
theorem B1439779 : Blo 1439539 1439779 := bstep (se 1 (by rfl) ⟨1079834, by rfl⟩ : syracuseStep 1439779 = 2159669) B2159669
theorem B2160689 : Blo 1439539 2160689 := bstep (se 2 (by rfl) ⟨810258, by rfl⟩ : syracuseStep 2160689 = 1620517) B1620517
theorem B3242033 : Blo 1439539 3242033 := bstep (se 2 (by rfl) ⟨1215762, by rfl⟩ : syracuseStep 3242033 = 2431525) B2431525
theorem B1439795 : Blo 1439539 1439795 := bstep (se 1 (by rfl) ⟨1079846, by rfl⟩ : syracuseStep 1439795 = 2159693) B2159693
theorem B4864049 : Blo 1439539 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B1439811 : Blo 1439539 1439811 := bstep (se 1 (by rfl) ⟨1079858, by rfl⟩ : syracuseStep 1439811 = 2159717) B2159717
theorem B2160707 : Blo 1439539 2160707 := bstep (se 1 (by rfl) ⟨1620530, by rfl⟩ : syracuseStep 2160707 = 3241061) B3241061
theorem B3242051 : Blo 1439539 3242051 := bstep (se 1 (by rfl) ⟨2431538, by rfl⟩ : syracuseStep 3242051 = 4863077) B4863077
theorem B1439827 : Blo 1439539 1439827 := bstep (se 1 (by rfl) ⟨1079870, by rfl⟩ : syracuseStep 1439827 = 2159741) B2159741
theorem B2160737 : Blo 1439539 2160737 := bstep (se 2 (by rfl) ⟨810276, by rfl⟩ : syracuseStep 2160737 = 1620553) B1620553
theorem B1439843 : Blo 1439539 1439843 := bstep (se 1 (by rfl) ⟨1079882, by rfl⟩ : syracuseStep 1439843 = 2159765) B2159765
theorem B1620067 : Blo 1439539 1620067 := bstep (se 1 (by rfl) ⟨1215050, by rfl⟩ : syracuseStep 1620067 = 2430101) B2430101
theorem B2431073 : Blo 1439539 2431073 := bstep (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) B1823305
theorem B1439859 : Blo 1439539 1439859 := bstep (se 1 (by rfl) ⟨1079894, by rfl⟩ : syracuseStep 1439859 = 2159789) B2159789
theorem B2160755 : Blo 1439539 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B1439875 : Blo 1439539 1439875 := bstep (se 1 (by rfl) ⟨1079906, by rfl⟩ : syracuseStep 1439875 = 2159813) B2159813
theorem B18700429 : Blo 1439539 18700429 := bstep (se 3 (by rfl) ⟨3506330, by rfl⟩ : syracuseStep 18700429 = 7012661) B7012661
theorem B2160785 : Blo 1439539 2160785 := bstep (se 2 (by rfl) ⟨810294, by rfl⟩ : syracuseStep 2160785 = 1620589) B1620589
theorem B1439891 : Blo 1439539 1439891 := bstep (se 1 (by rfl) ⟨1079918, by rfl⟩ : syracuseStep 1439891 = 2159837) B2159837
theorem B4102289 : Blo 1439539 4102289 := bstep (se 2 (by rfl) ⟨1538358, by rfl⟩ : syracuseStep 4102289 = 3076717) B3076717
theorem B1439907 : Blo 1439539 1439907 := bstep (se 1 (by rfl) ⟨1079930, by rfl⟩ : syracuseStep 1439907 = 2159861) B2159861
theorem B2160803 : Blo 1439539 2160803 := bstep (se 1 (by rfl) ⟨1620602, by rfl⟩ : syracuseStep 2160803 = 3241205) B3241205
theorem B1439923 : Blo 1439539 1439923 := bstep (se 1 (by rfl) ⟨1079942, by rfl⟩ : syracuseStep 1439923 = 2159885) B2159885
theorem B2160833 : Blo 1439539 2160833 := bstep (se 2 (by rfl) ⟨810312, by rfl⟩ : syracuseStep 2160833 = 1620625) B1620625
theorem B1439939 : Blo 1439539 1439939 := bstep (se 1 (by rfl) ⟨1079954, by rfl⟩ : syracuseStep 1439939 = 2159909) B2159909
theorem B4217027 : Blo 1439539 4217027 := bstep (se 1 (by rfl) ⟨3162770, by rfl⟩ : syracuseStep 4217027 = 6325541) B6325541
theorem B5077187 : Blo 1439539 5077187 := bstep (se 1 (by rfl) ⟨3807890, by rfl⟩ : syracuseStep 5077187 = 7615781) B7615781
theorem B1439955 : Blo 1439539 1439955 := bstep (se 1 (by rfl) ⟨1079966, by rfl⟩ : syracuseStep 1439955 = 2159933) B2159933
theorem B2160851 : Blo 1439539 2160851 := bstep (se 1 (by rfl) ⟨1620638, by rfl⟩ : syracuseStep 2160851 = 3241277) B3241277
theorem B1439971 : Blo 1439539 1439971 := bstep (se 1 (by rfl) ⟨1079978, by rfl⟩ : syracuseStep 1439971 = 2159957) B2159957
theorem B2431201 : Blo 1439539 2431201 := bstep (se 2 (by rfl) ⟨911700, by rfl⟩ : syracuseStep 2431201 = 1823401) B1823401
theorem B10934513 : Blo 1439539 10934513 := bstep (se 2 (by rfl) ⟨4100442, by rfl⟩ : syracuseStep 10934513 = 8200885) B8200885
theorem B2160881 : Blo 1439539 2160881 := bstep (se 2 (by rfl) ⟨810330, by rfl⟩ : syracuseStep 2160881 = 1620661) B1620661
theorem B1439987 : Blo 1439539 1439987 := bstep (se 1 (by rfl) ⟨1079990, by rfl⟩ : syracuseStep 1439987 = 2159981) B2159981
theorem B1620211 : Blo 1439539 1620211 := bstep (se 1 (by rfl) ⟨1215158, by rfl⟩ : syracuseStep 1620211 = 2430317) B2430317
theorem B1440003 : Blo 1439539 1440003 := bstep (se 1 (by rfl) ⟨1080002, by rfl⟩ : syracuseStep 1440003 = 2160005) B2160005
theorem B2160899 : Blo 1439539 2160899 := bstep (se 1 (by rfl) ⟨1620674, by rfl⟩ : syracuseStep 2160899 = 3241349) B3241349
theorem B2431235 : Blo 1439539 2431235 := bstep (se 1 (by rfl) ⟨1823426, by rfl⟩ : syracuseStep 2431235 = 3646853) B3646853
theorem B1440019 : Blo 1439539 1440019 := bstep (se 1 (by rfl) ⟨1080014, by rfl⟩ : syracuseStep 1440019 = 2160029) B2160029
theorem B2160929 : Blo 1439539 2160929 := bstep (se 2 (by rfl) ⟨810348, by rfl⟩ : syracuseStep 2160929 = 1620697) B1620697
theorem B1440035 : Blo 1439539 1440035 := bstep (se 1 (by rfl) ⟨1080026, by rfl⟩ : syracuseStep 1440035 = 2160053) B2160053
theorem B1440051 : Blo 1439539 1440051 := bstep (se 1 (by rfl) ⟨1080038, by rfl⟩ : syracuseStep 1440051 = 2160077) B2160077
theorem B2160947 : Blo 1439539 2160947 := bstep (se 1 (by rfl) ⟨1620710, by rfl⟩ : syracuseStep 2160947 = 3241421) B3241421
theorem B1440067 : Blo 1439539 1440067 := bstep (se 1 (by rfl) ⟨1080050, by rfl⟩ : syracuseStep 1440067 = 2160101) B2160101
theorem B2160977 : Blo 1439539 2160977 := bstep (se 2 (by rfl) ⟨810366, by rfl⟩ : syracuseStep 2160977 = 1620733) B1620733
theorem B3242321 : Blo 1439539 3242321 := bstep (se 2 (by rfl) ⟨1215870, by rfl⟩ : syracuseStep 3242321 = 2431741) B2431741
theorem B1440083 : Blo 1439539 1440083 := bstep (se 1 (by rfl) ⟨1080062, by rfl⟩ : syracuseStep 1440083 = 2160125) B2160125
theorem B1440099 : Blo 1439539 1440099 := bstep (se 1 (by rfl) ⟨1080074, by rfl⟩ : syracuseStep 1440099 = 2160149) B2160149
theorem B2160995 : Blo 1439539 2160995 := bstep (se 1 (by rfl) ⟨1620746, by rfl⟩ : syracuseStep 2160995 = 3241493) B3241493
theorem B3242339 : Blo 1439539 3242339 := bstep (se 1 (by rfl) ⟨2431754, by rfl⟩ : syracuseStep 3242339 = 4863509) B4863509
theorem B1440115 : Blo 1439539 1440115 := bstep (se 1 (by rfl) ⟨1080086, by rfl⟩ : syracuseStep 1440115 = 2160173) B2160173
theorem B2161025 : Blo 1439539 2161025 := bstep (se 2 (by rfl) ⟨810384, by rfl⟩ : syracuseStep 2161025 = 1620769) B1620769
theorem B1440131 : Blo 1439539 1440131 := bstep (se 1 (by rfl) ⟨1080098, by rfl⟩ : syracuseStep 1440131 = 2160197) B2160197
theorem B1620355 : Blo 1439539 1620355 := bstep (se 1 (by rfl) ⟨1215266, by rfl⟩ : syracuseStep 1620355 = 2430533) B2430533
theorem B2431363 : Blo 1439539 2431363 := bstep (se 1 (by rfl) ⟨1823522, by rfl⟩ : syracuseStep 2431363 = 3647045) B3647045
theorem B3463555 : Blo 1439539 3463555 := bstep (se 1 (by rfl) ⟨2597666, by rfl⟩ : syracuseStep 3463555 = 5195333) B5195333
theorem B1440147 : Blo 1439539 1440147 := bstep (se 1 (by rfl) ⟨1080110, by rfl⟩ : syracuseStep 1440147 = 2160221) B2160221
theorem B2161043 : Blo 1439539 2161043 := bstep (se 1 (by rfl) ⟨1620782, by rfl⟩ : syracuseStep 2161043 = 3241565) B3241565
theorem B6150563 : Blo 1439539 6150563 := bstep (se 1 (by rfl) ⟨4612922, by rfl⟩ : syracuseStep 6150563 = 9225845) B9225845
theorem B1440163 : Blo 1439539 1440163 := bstep (se 1 (by rfl) ⟨1080122, by rfl⟩ : syracuseStep 1440163 = 2160245) B2160245
theorem B4741553 : Blo 1439539 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B2161073 : Blo 1439539 2161073 := bstep (se 2 (by rfl) ⟨810402, by rfl⟩ : syracuseStep 2161073 = 1620805) B1620805
theorem B1440179 : Blo 1439539 1440179 := bstep (se 1 (by rfl) ⟨1080134, by rfl⟩ : syracuseStep 1440179 = 2160269) B2160269
theorem B1440195 : Blo 1439539 1440195 := bstep (se 1 (by rfl) ⟨1080146, by rfl⟩ : syracuseStep 1440195 = 2160293) B2160293
theorem B2161091 : Blo 1439539 2161091 := bstep (se 1 (by rfl) ⟨1620818, by rfl⟩ : syracuseStep 2161091 = 3241637) B3241637
theorem B6568397 : Blo 1439539 6568397 := bstep (se 3 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 6568397 = 2463149) B2463149
theorem B1440211 : Blo 1439539 1440211 := bstep (se 1 (by rfl) ⟨1080158, by rfl⟩ : syracuseStep 1440211 = 2160317) B2160317
theorem B2161121 : Blo 1439539 2161121 := bstep (se 2 (by rfl) ⟨810420, by rfl⟩ : syracuseStep 2161121 = 1620841) B1620841
theorem B1440227 : Blo 1439539 1440227 := bstep (se 1 (by rfl) ⟨1080170, by rfl⟩ : syracuseStep 1440227 = 2160341) B2160341
theorem B1440243 : Blo 1439539 1440243 := bstep (se 1 (by rfl) ⟨1080182, by rfl⟩ : syracuseStep 1440243 = 2160365) B2160365
theorem B2161139 : Blo 1439539 2161139 := bstep (se 1 (by rfl) ⟨1620854, by rfl⟩ : syracuseStep 2161139 = 3241709) B3241709
theorem B2595331 : Blo 1439539 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B1440259 : Blo 1439539 1440259 := bstep (se 1 (by rfl) ⟨1080194, by rfl⟩ : syracuseStep 1440259 = 2160389) B2160389
theorem B2161169 : Blo 1439539 2161169 := bstep (se 2 (by rfl) ⟨810438, by rfl⟩ : syracuseStep 2161169 = 1620877) B1620877
theorem B2431505 : Blo 1439539 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B1440275 : Blo 1439539 1440275 := bstep (se 1 (by rfl) ⟨1080206, by rfl⟩ : syracuseStep 1440275 = 2160413) B2160413
theorem B1620499 : Blo 1439539 1620499 := bstep (se 1 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 1620499 = 2430749) B2430749
theorem B1440291 : Blo 1439539 1440291 := bstep (se 1 (by rfl) ⟨1080218, by rfl⟩ : syracuseStep 1440291 = 2160437) B2160437
theorem B2161187 : Blo 1439539 2161187 := bstep (se 1 (by rfl) ⟨1620890, by rfl⟩ : syracuseStep 2161187 = 3241781) B3241781
theorem B9361955 : Blo 1439539 9361955 := bstep (se 1 (by rfl) ⟨7021466, by rfl⟩ : syracuseStep 9361955 = 14042933) B14042933
theorem B4381229 : Blo 1439539 4381229 := bstep (se 3 (by rfl) ⟨821480, by rfl⟩ : syracuseStep 4381229 = 1642961) B1642961
theorem B1440307 : Blo 1439539 1440307 := bstep (se 1 (by rfl) ⟨1080230, by rfl⟩ : syracuseStep 1440307 = 2160461) B2160461
theorem B2161217 : Blo 1439539 2161217 := bstep (se 2 (by rfl) ⟨810456, by rfl⟩ : syracuseStep 2161217 = 1620913) B1620913
theorem B1440323 : Blo 1439539 1440323 := bstep (se 1 (by rfl) ⟨1080242, by rfl⟩ : syracuseStep 1440323 = 2160485) B2160485
theorem B9230917 : Blo 1439539 9230917 := bstep (se 4 (by rfl) ⟨865398, by rfl⟩ : syracuseStep 9230917 = 1730797) B1730797
theorem B4864589 : Blo 1439539 4864589 := bstep (se 3 (by rfl) ⟨912110, by rfl⟩ : syracuseStep 4864589 = 1824221) B1824221
theorem B7297613 : Blo 1439539 7297613 := bstep (se 3 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 7297613 = 2736605) B2736605
theorem B1440339 : Blo 1439539 1440339 := bstep (se 1 (by rfl) ⟨1080254, by rfl⟩ : syracuseStep 1440339 = 2160509) B2160509
theorem B2161235 : Blo 1439539 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B1440355 : Blo 1439539 1440355 := bstep (se 1 (by rfl) ⟨1080266, by rfl⟩ : syracuseStep 1440355 = 2160533) B2160533
theorem B2161265 : Blo 1439539 2161265 := bstep (se 2 (by rfl) ⟨810474, by rfl⟩ : syracuseStep 2161265 = 1620949) B1620949
theorem B3242609 : Blo 1439539 3242609 := bstep (se 2 (by rfl) ⟨1215978, by rfl⟩ : syracuseStep 3242609 = 2431957) B2431957
theorem B1440371 : Blo 1439539 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B1440387 : Blo 1439539 1440387 := bstep (se 1 (by rfl) ⟨1080290, by rfl⟩ : syracuseStep 1440387 = 2160581) B2160581
theorem B2161283 : Blo 1439539 2161283 := bstep (se 1 (by rfl) ⟨1620962, by rfl⟩ : syracuseStep 2161283 = 3241925) B3241925
theorem B3242627 : Blo 1439539 3242627 := bstep (se 1 (by rfl) ⟨2431970, by rfl⟩ : syracuseStep 3242627 = 4863941) B4863941
theorem B4864643 : Blo 1439539 4864643 := bstep (se 1 (by rfl) ⟨3648482, by rfl⟩ : syracuseStep 4864643 = 7296965) B7296965
theorem B2431633 : Blo 1439539 2431633 := bstep (se 2 (by rfl) ⟨911862, by rfl⟩ : syracuseStep 2431633 = 1823725) B1823725
theorem B1440403 : Blo 1439539 1440403 := bstep (se 1 (by rfl) ⟨1080302, by rfl⟩ : syracuseStep 1440403 = 2160605) B2160605
theorem B2161313 : Blo 1439539 2161313 := bstep (se 2 (by rfl) ⟨810492, by rfl⟩ : syracuseStep 2161313 = 1620985) B1620985
theorem B1440419 : Blo 1439539 1440419 := bstep (se 1 (by rfl) ⟨1080314, by rfl⟩ : syracuseStep 1440419 = 2160629) B2160629
theorem B1620643 : Blo 1439539 1620643 := bstep (se 1 (by rfl) ⟨1215482, by rfl⟩ : syracuseStep 1620643 = 2430965) B2430965
theorem B1440435 : Blo 1439539 1440435 := bstep (se 1 (by rfl) ⟨1080326, by rfl⟩ : syracuseStep 1440435 = 2160653) B2160653
theorem B2161331 : Blo 1439539 2161331 := bstep (se 1 (by rfl) ⟨1620998, by rfl⟩ : syracuseStep 2161331 = 3241997) B3241997
theorem B2431667 : Blo 1439539 2431667 := bstep (se 1 (by rfl) ⟨1823750, by rfl⟩ : syracuseStep 2431667 = 3647501) B3647501
theorem B3644099 : Blo 1439539 3644099 := bstep (se 1 (by rfl) ⟨2733074, by rfl⟩ : syracuseStep 3644099 = 5466149) B5466149
theorem B1440451 : Blo 1439539 1440451 := bstep (se 1 (by rfl) ⟨1080338, by rfl⟩ : syracuseStep 1440451 = 2160677) B2160677
theorem B2161361 : Blo 1439539 2161361 := bstep (se 2 (by rfl) ⟨810510, by rfl⟩ : syracuseStep 2161361 = 1621021) B1621021
theorem B1440467 : Blo 1439539 1440467 := bstep (se 1 (by rfl) ⟨1080350, by rfl⟩ : syracuseStep 1440467 = 2160701) B2160701
theorem B2308819 : Blo 1439539 2308819 := bstep (se 1 (by rfl) ⟨1731614, by rfl⟩ : syracuseStep 2308819 = 3463229) B3463229
theorem B1440483 : Blo 1439539 1440483 := bstep (se 1 (by rfl) ⟨1080362, by rfl⟩ : syracuseStep 1440483 = 2160725) B2160725
theorem B7789283 : Blo 1439539 7789283 := bstep (se 1 (by rfl) ⟨5841962, by rfl⟩ : syracuseStep 7789283 = 11683925) B11683925
theorem B2161379 : Blo 1439539 2161379 := bstep (se 1 (by rfl) ⟨1621034, by rfl⟩ : syracuseStep 2161379 = 3242069) B3242069
theorem B47381219 : Blo 1439539 47381219 := bstep (se 1 (by rfl) ⟨35535914, by rfl⟩ : syracuseStep 47381219 = 71071829) B71071829
theorem B1440499 : Blo 1439539 1440499 := bstep (se 1 (by rfl) ⟨1080374, by rfl⟩ : syracuseStep 1440499 = 2160749) B2160749
theorem B2161409 : Blo 1439539 2161409 := bstep (se 2 (by rfl) ⟨810528, by rfl⟩ : syracuseStep 2161409 = 1621057) B1621057
theorem B1440515 : Blo 1439539 1440515 := bstep (se 1 (by rfl) ⟨1080386, by rfl⟩ : syracuseStep 1440515 = 2160773) B2160773
theorem B1440531 : Blo 1439539 1440531 := bstep (se 1 (by rfl) ⟨1080398, by rfl⟩ : syracuseStep 1440531 = 2160797) B2160797
theorem B2161427 : Blo 1439539 2161427 := bstep (se 1 (by rfl) ⟨1621070, by rfl⟩ : syracuseStep 2161427 = 3242141) B3242141
theorem B2595619 : Blo 1439539 2595619 := bstep (se 1 (by rfl) ⟨1946714, by rfl⟩ : syracuseStep 2595619 = 3893429) B3893429
theorem B1440547 : Blo 1439539 1440547 := bstep (se 1 (by rfl) ⟨1080410, by rfl⟩ : syracuseStep 1440547 = 2160821) B2160821
theorem B2734897 : Blo 1439539 2734897 := bstep (se 2 (by rfl) ⟨1025586, by rfl⟩ : syracuseStep 2734897 = 2051173) B2051173
theorem B2161457 : Blo 1439539 2161457 := bstep (se 2 (by rfl) ⟨810546, by rfl⟩ : syracuseStep 2161457 = 1621093) B1621093
theorem B1440563 : Blo 1439539 1440563 := bstep (se 1 (by rfl) ⟨1080422, by rfl⟩ : syracuseStep 1440563 = 2160845) B2160845
theorem B1620787 : Blo 1439539 1620787 := bstep (se 1 (by rfl) ⟨1215590, by rfl⟩ : syracuseStep 1620787 = 2431181) B2431181
theorem B2431795 : Blo 1439539 2431795 := bstep (se 1 (by rfl) ⟨1823846, by rfl⟩ : syracuseStep 2431795 = 3647693) B3647693
theorem B1440579 : Blo 1439539 1440579 := bstep (se 1 (by rfl) ⟨1080434, by rfl⟩ : syracuseStep 1440579 = 2160869) B2160869
theorem B2161475 : Blo 1439539 2161475 := bstep (se 1 (by rfl) ⟨1621106, by rfl⟩ : syracuseStep 2161475 = 3242213) B3242213
theorem B1440595 : Blo 1439539 1440595 := bstep (se 1 (by rfl) ⟨1080446, by rfl⟩ : syracuseStep 1440595 = 2160893) B2160893
theorem B2161505 : Blo 1439539 2161505 := bstep (se 2 (by rfl) ⟨810564, by rfl⟩ : syracuseStep 2161505 = 1621129) B1621129
theorem B1440611 : Blo 1439539 1440611 := bstep (se 1 (by rfl) ⟨1080458, by rfl⟩ : syracuseStep 1440611 = 2160917) B2160917
theorem B7396195 : Blo 1439539 7396195 := bstep (se 1 (by rfl) ⟨5547146, by rfl⟩ : syracuseStep 7396195 = 11094293) B11094293
theorem B1440627 : Blo 1439539 1440627 := bstep (se 1 (by rfl) ⟨1080470, by rfl⟩ : syracuseStep 1440627 = 2160941) B2160941
theorem B2161523 : Blo 1439539 2161523 := bstep (se 1 (by rfl) ⟨1621142, by rfl⟩ : syracuseStep 2161523 = 3242285) B3242285
theorem B3644291 : Blo 1439539 3644291 := bstep (se 1 (by rfl) ⟨2733218, by rfl⟩ : syracuseStep 3644291 = 5466437) B5466437
theorem B1440643 : Blo 1439539 1440643 := bstep (se 1 (by rfl) ⟨1080482, by rfl⟩ : syracuseStep 1440643 = 2160965) B2160965
theorem B2161553 : Blo 1439539 2161553 := bstep (se 2 (by rfl) ⟨810582, by rfl⟩ : syracuseStep 2161553 = 1621165) B1621165
theorem B3242897 : Blo 1439539 3242897 := bstep (se 2 (by rfl) ⟨1216086, by rfl⟩ : syracuseStep 3242897 = 2432173) B2432173
theorem B1440659 : Blo 1439539 1440659 := bstep (se 1 (by rfl) ⟨1080494, by rfl⟩ : syracuseStep 1440659 = 2160989) B2160989
theorem B4864913 : Blo 1439539 4864913 := bstep (se 2 (by rfl) ⟨1824342, by rfl⟩ : syracuseStep 4864913 = 3648685) B3648685
theorem B1440675 : Blo 1439539 1440675 := bstep (se 1 (by rfl) ⟨1080506, by rfl⟩ : syracuseStep 1440675 = 2161013) B2161013
theorem B4103075 : Blo 1439539 4103075 := bstep (se 1 (by rfl) ⟨3077306, by rfl⟩ : syracuseStep 4103075 = 6154613) B6154613
theorem B2161571 : Blo 1439539 2161571 := bstep (se 1 (by rfl) ⟨1621178, by rfl⟩ : syracuseStep 2161571 = 3242357) B3242357
theorem B3242915 : Blo 1439539 3242915 := bstep (se 1 (by rfl) ⟨2432186, by rfl⟩ : syracuseStep 3242915 = 4864373) B4864373
theorem B1440691 : Blo 1439539 1440691 := bstep (se 1 (by rfl) ⟨1080518, by rfl⟩ : syracuseStep 1440691 = 2161037) B2161037
theorem B1538995 : Blo 1439539 1538995 := bstep (se 1 (by rfl) ⟨1154246, by rfl⟩ : syracuseStep 1538995 = 2308493) B2308493
theorem B2161601 : Blo 1439539 2161601 := bstep (se 2 (by rfl) ⟨810600, by rfl⟩ : syracuseStep 2161601 = 1621201) B1621201
theorem B1440707 : Blo 1439539 1440707 := bstep (se 1 (by rfl) ⟨1080530, by rfl⟩ : syracuseStep 1440707 = 2161061) B2161061
theorem B1620931 : Blo 1439539 1620931 := bstep (se 1 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 1620931 = 2431397) B2431397
theorem B2431937 : Blo 1439539 2431937 := bstep (se 2 (by rfl) ⟨911976, by rfl⟩ : syracuseStep 2431937 = 1823953) B1823953
theorem B2309057 : Blo 1439539 2309057 := bstep (se 2 (by rfl) ⟨865896, by rfl⟩ : syracuseStep 2309057 = 1731793) B1731793
theorem B1440723 : Blo 1439539 1440723 := bstep (se 1 (by rfl) ⟨1080542, by rfl⟩ : syracuseStep 1440723 = 2161085) B2161085
theorem B2161619 : Blo 1439539 2161619 := bstep (se 1 (by rfl) ⟨1621214, by rfl⟩ : syracuseStep 2161619 = 3242429) B3242429
theorem B1440739 : Blo 1439539 1440739 := bstep (se 1 (by rfl) ⟨1080554, by rfl⟩ : syracuseStep 1440739 = 2161109) B2161109
theorem B2161649 : Blo 1439539 2161649 := bstep (se 2 (by rfl) ⟨810618, by rfl⟩ : syracuseStep 2161649 = 1621237) B1621237
theorem B1440755 : Blo 1439539 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B1440771 : Blo 1439539 1440771 := bstep (se 1 (by rfl) ⟨1080578, by rfl⟩ : syracuseStep 1440771 = 2161157) B2161157
theorem B2161667 : Blo 1439539 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B1440787 : Blo 1439539 1440787 := bstep (se 1 (by rfl) ⟨1080590, by rfl⟩ : syracuseStep 1440787 = 2161181) B2161181
theorem B2161697 : Blo 1439539 2161697 := bstep (se 2 (by rfl) ⟨810636, by rfl⟩ : syracuseStep 2161697 = 1621273) B1621273
theorem B1440803 : Blo 1439539 1440803 := bstep (se 1 (by rfl) ⟨1080602, by rfl⟩ : syracuseStep 1440803 = 2161205) B2161205
theorem B1440819 : Blo 1439539 1440819 := bstep (se 1 (by rfl) ⟨1080614, by rfl⟩ : syracuseStep 1440819 = 2161229) B2161229
theorem B2161715 : Blo 1439539 2161715 := bstep (se 1 (by rfl) ⟨1621286, by rfl⟩ : syracuseStep 2161715 = 3242573) B3242573
theorem B1440835 : Blo 1439539 1440835 := bstep (se 1 (by rfl) ⟨1080626, by rfl⟩ : syracuseStep 1440835 = 2161253) B2161253
theorem B2432065 : Blo 1439539 2432065 := bstep (se 2 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 2432065 = 1824049) B1824049
theorem B8199245 : Blo 1439539 8199245 := bstep (se 3 (by rfl) ⟨1537358, by rfl⟩ : syracuseStep 8199245 = 3074717) B3074717
theorem B2161745 : Blo 1439539 2161745 := bstep (se 2 (by rfl) ⟨810654, by rfl⟩ : syracuseStep 2161745 = 1621309) B1621309
theorem B1440851 : Blo 1439539 1440851 := bstep (se 1 (by rfl) ⟨1080638, by rfl⟩ : syracuseStep 1440851 = 2161277) B2161277
theorem B1621075 : Blo 1439539 1621075 := bstep (se 1 (by rfl) ⟨1215806, by rfl⟩ : syracuseStep 1621075 = 2431613) B2431613
theorem B1440867 : Blo 1439539 1440867 := bstep (se 1 (by rfl) ⟨1080650, by rfl⟩ : syracuseStep 1440867 = 2161301) B2161301
theorem B2161763 : Blo 1439539 2161763 := bstep (se 1 (by rfl) ⟨1621322, by rfl⟩ : syracuseStep 2161763 = 3242645) B3242645
theorem B2432099 : Blo 1439539 2432099 := bstep (se 1 (by rfl) ⟨1824074, by rfl⟩ : syracuseStep 2432099 = 3648149) B3648149
theorem B1440883 : Blo 1439539 1440883 := bstep (se 1 (by rfl) ⟨1080662, by rfl⟩ : syracuseStep 1440883 = 2161325) B2161325
theorem B2161793 : Blo 1439539 2161793 := bstep (se 2 (by rfl) ⟨810672, by rfl⟩ : syracuseStep 2161793 = 1621345) B1621345
theorem B1440899 : Blo 1439539 1440899 := bstep (se 1 (by rfl) ⟨1080674, by rfl⟩ : syracuseStep 1440899 = 2161349) B2161349
theorem B1440915 : Blo 1439539 1440915 := bstep (se 1 (by rfl) ⟨1080686, by rfl⟩ : syracuseStep 1440915 = 2161373) B2161373
theorem B2161811 : Blo 1439539 2161811 := bstep (se 1 (by rfl) ⟨1621358, by rfl⟩ : syracuseStep 2161811 = 3242717) B3242717
theorem B1440931 : Blo 1439539 1440931 := bstep (se 1 (by rfl) ⟨1080698, by rfl⟩ : syracuseStep 1440931 = 2161397) B2161397
theorem B2161841 : Blo 1439539 2161841 := bstep (se 2 (by rfl) ⟨810690, by rfl⟩ : syracuseStep 2161841 = 1621381) B1621381
theorem B1440947 : Blo 1439539 1440947 := bstep (se 1 (by rfl) ⟨1080710, by rfl⟩ : syracuseStep 1440947 = 2161421) B2161421
theorem B3243185 : Blo 1439539 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B2735299 : Blo 1439539 2735299 := bstep (se 1 (by rfl) ⟨2051474, by rfl⟩ : syracuseStep 2735299 = 4102949) B4102949
theorem B1440963 : Blo 1439539 1440963 := bstep (se 1 (by rfl) ⟨1080722, by rfl⟩ : syracuseStep 1440963 = 2161445) B2161445
theorem B10386629 : Blo 1439539 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B2161859 : Blo 1439539 2161859 := bstep (se 1 (by rfl) ⟨1621394, by rfl⟩ : syracuseStep 2161859 = 3242789) B3242789
theorem B3243203 : Blo 1439539 3243203 := bstep (se 1 (by rfl) ⟨2432402, by rfl⟩ : syracuseStep 3243203 = 4864805) B4864805
theorem B1440979 : Blo 1439539 1440979 := bstep (se 1 (by rfl) ⟨1080734, by rfl⟩ : syracuseStep 1440979 = 2161469) B2161469
theorem B2161889 : Blo 1439539 2161889 := bstep (se 2 (by rfl) ⟨810708, by rfl⟩ : syracuseStep 2161889 = 1621417) B1621417
theorem B18447587 : Blo 1439539 18447587 := bstep (se 1 (by rfl) ⟨13835690, by rfl⟩ : syracuseStep 18447587 = 27671381) B27671381
theorem B1440995 : Blo 1439539 1440995 := bstep (se 1 (by rfl) ⟨1080746, by rfl⟩ : syracuseStep 1440995 = 2161493) B2161493
theorem B1621219 : Blo 1439539 1621219 := bstep (se 1 (by rfl) ⟨1215914, by rfl⟩ : syracuseStep 1621219 = 2431829) B2431829
theorem B2432227 : Blo 1439539 2432227 := bstep (se 1 (by rfl) ⟨1824170, by rfl⟩ : syracuseStep 2432227 = 3648341) B3648341
theorem B4103405 : Blo 1439539 4103405 := bstep (se 3 (by rfl) ⟨769388, by rfl⟩ : syracuseStep 4103405 = 1538777) B1538777
theorem B1973489 : Blo 1439539 1973489 := bstep (se 2 (by rfl) ⟨740058, by rfl⟩ : syracuseStep 1973489 = 1480117) B1480117
theorem B2735345 : Blo 1439539 2735345 := bstep (se 2 (by rfl) ⟨1025754, by rfl⟩ : syracuseStep 2735345 = 2051509) B2051509
theorem B1441011 : Blo 1439539 1441011 := bstep (se 1 (by rfl) ⟨1080758, by rfl⟩ : syracuseStep 1441011 = 2161517) B2161517
theorem B2161907 : Blo 1439539 2161907 := bstep (se 1 (by rfl) ⟨1621430, by rfl⟩ : syracuseStep 2161907 = 3242861) B3242861
theorem B1441027 : Blo 1439539 1441027 := bstep (se 1 (by rfl) ⟨1080770, by rfl⟩ : syracuseStep 1441027 = 2161541) B2161541
theorem B2161937 : Blo 1439539 2161937 := bstep (se 2 (by rfl) ⟨810726, by rfl⟩ : syracuseStep 2161937 = 1621453) B1621453
theorem B1441043 : Blo 1439539 1441043 := bstep (se 1 (by rfl) ⟨1080782, by rfl⟩ : syracuseStep 1441043 = 2161565) B2161565
theorem B1441059 : Blo 1439539 1441059 := bstep (se 1 (by rfl) ⟨1080794, by rfl⟩ : syracuseStep 1441059 = 2161589) B2161589
theorem B2161955 : Blo 1439539 2161955 := bstep (se 1 (by rfl) ⟨1621466, by rfl⟩ : syracuseStep 2161955 = 3242933) B3242933
theorem B7290161 : Blo 1439539 7290161 := bstep (se 2 (by rfl) ⟨2733810, by rfl⟩ : syracuseStep 7290161 = 5467621) B5467621
theorem B4103473 : Blo 1439539 4103473 := bstep (se 2 (by rfl) ⟨1538802, by rfl⟩ : syracuseStep 4103473 = 3077605) B3077605
theorem B1441075 : Blo 1439539 1441075 := bstep (se 1 (by rfl) ⟨1080806, by rfl⟩ : syracuseStep 1441075 = 2161613) B2161613
theorem B2161985 : Blo 1439539 2161985 := bstep (se 2 (by rfl) ⟨810744, by rfl⟩ : syracuseStep 2161985 = 1621489) B1621489
theorem B1441091 : Blo 1439539 1441091 := bstep (se 1 (by rfl) ⟨1080818, by rfl⟩ : syracuseStep 1441091 = 2161637) B2161637
theorem B2497873 : Blo 1439539 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B1441107 : Blo 1439539 1441107 := bstep (se 1 (by rfl) ⟨1080830, by rfl⟩ : syracuseStep 1441107 = 2161661) B2161661
theorem B2162003 : Blo 1439539 2162003 := bstep (se 1 (by rfl) ⟨1621502, by rfl⟩ : syracuseStep 2162003 = 3243005) B3243005
theorem B1441123 : Blo 1439539 1441123 := bstep (se 1 (by rfl) ⟨1080842, by rfl⟩ : syracuseStep 1441123 = 2161685) B2161685
theorem B2162033 : Blo 1439539 2162033 := bstep (se 2 (by rfl) ⟨810762, by rfl⟩ : syracuseStep 2162033 = 1621525) B1621525
theorem B2432369 : Blo 1439539 2432369 := bstep (se 2 (by rfl) ⟨912138, by rfl⟩ : syracuseStep 2432369 = 1824277) B1824277
theorem B1441139 : Blo 1439539 1441139 := bstep (se 1 (by rfl) ⟨1080854, by rfl⟩ : syracuseStep 1441139 = 2161709) B2161709
theorem B1621363 : Blo 1439539 1621363 := bstep (se 1 (by rfl) ⟨1216022, by rfl⟩ : syracuseStep 1621363 = 2432045) B2432045
theorem B1441155 : Blo 1439539 1441155 := bstep (se 1 (by rfl) ⟨1080866, by rfl⟩ : syracuseStep 1441155 = 2161733) B2161733
theorem B2162051 : Blo 1439539 2162051 := bstep (se 1 (by rfl) ⟨1621538, by rfl⟩ : syracuseStep 2162051 = 3243077) B3243077
theorem B1441171 : Blo 1439539 1441171 := bstep (se 1 (by rfl) ⟨1080878, by rfl⟩ : syracuseStep 1441171 = 2161757) B2161757
theorem B2162081 : Blo 1439539 2162081 := bstep (se 2 (by rfl) ⟨810780, by rfl⟩ : syracuseStep 2162081 = 1621561) B1621561
theorem B1441187 : Blo 1439539 1441187 := bstep (se 1 (by rfl) ⟨1080890, by rfl⟩ : syracuseStep 1441187 = 2161781) B2161781
theorem B1441203 : Blo 1439539 1441203 := bstep (se 1 (by rfl) ⟨1080902, by rfl⟩ : syracuseStep 1441203 = 2161805) B2161805
theorem B2162099 : Blo 1439539 2162099 := bstep (se 1 (by rfl) ⟨1621574, by rfl⟩ : syracuseStep 2162099 = 3243149) B3243149
theorem B1441219 : Blo 1439539 1441219 := bstep (se 1 (by rfl) ⟨1080914, by rfl⟩ : syracuseStep 1441219 = 2161829) B2161829
theorem B2162129 : Blo 1439539 2162129 := bstep (se 2 (by rfl) ⟨810798, by rfl⟩ : syracuseStep 2162129 = 1621597) B1621597
theorem B1441235 : Blo 1439539 1441235 := bstep (se 1 (by rfl) ⟨1080926, by rfl⟩ : syracuseStep 1441235 = 2161853) B2161853
theorem B1441251 : Blo 1439539 1441251 := bstep (se 1 (by rfl) ⟨1080938, by rfl⟩ : syracuseStep 1441251 = 2161877) B2161877
theorem B2162147 : Blo 1439539 2162147 := bstep (se 1 (by rfl) ⟨1621610, by rfl⟩ : syracuseStep 2162147 = 3243221) B3243221
theorem B2432497 : Blo 1439539 2432497 := bstep (se 2 (by rfl) ⟨912186, by rfl⟩ : syracuseStep 2432497 = 1824373) B1824373
theorem B1441267 : Blo 1439539 1441267 := bstep (se 1 (by rfl) ⟨1080950, by rfl⟩ : syracuseStep 1441267 = 2161901) B2161901
theorem B2162177 : Blo 1439539 2162177 := bstep (se 2 (by rfl) ⟨810816, by rfl⟩ : syracuseStep 2162177 = 1621633) B1621633
theorem B1441283 : Blo 1439539 1441283 := bstep (se 1 (by rfl) ⟨1080962, by rfl⟩ : syracuseStep 1441283 = 2161925) B2161925
theorem B1621507 : Blo 1439539 1621507 := bstep (se 1 (by rfl) ⟨1216130, by rfl⟩ : syracuseStep 1621507 = 2432261) B2432261
theorem B5193229 : Blo 1439539 5193229 := bstep (se 3 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 5193229 = 1947461) B1947461
theorem B2596369 : Blo 1439539 2596369 := bstep (se 2 (by rfl) ⟨973638, by rfl⟩ : syracuseStep 2596369 = 1947277) B1947277
theorem B2735633 : Blo 1439539 2735633 := bstep (se 2 (by rfl) ⟨1025862, by rfl⟩ : syracuseStep 2735633 = 2051725) B2051725
theorem B1441299 : Blo 1439539 1441299 := bstep (se 1 (by rfl) ⟨1080974, by rfl⟩ : syracuseStep 1441299 = 2161949) B2161949
theorem B2162195 : Blo 1439539 2162195 := bstep (se 1 (by rfl) ⟨1621646, by rfl⟩ : syracuseStep 2162195 = 3243293) B3243293
theorem B2432531 : Blo 1439539 2432531 := bstep (se 1 (by rfl) ⟨1824398, by rfl⟩ : syracuseStep 2432531 = 3648797) B3648797
theorem B1441315 : Blo 1439539 1441315 := bstep (se 1 (by rfl) ⟨1080986, by rfl⟩ : syracuseStep 1441315 = 2161973) B2161973
theorem B2162225 : Blo 1439539 2162225 := bstep (se 2 (by rfl) ⟨810834, by rfl⟩ : syracuseStep 2162225 = 1621669) B1621669
theorem B1441331 : Blo 1439539 1441331 := bstep (se 1 (by rfl) ⟨1080998, by rfl⟩ : syracuseStep 1441331 = 2161997) B2161997
theorem B4103747 : Blo 1439539 4103747 := bstep (se 1 (by rfl) ⟨3077810, by rfl⟩ : syracuseStep 4103747 = 6155621) B6155621
theorem B1441347 : Blo 1439539 1441347 := bstep (se 1 (by rfl) ⟨1081010, by rfl⟩ : syracuseStep 1441347 = 2162021) B2162021
theorem B2162243 : Blo 1439539 2162243 := bstep (se 1 (by rfl) ⟨1621682, by rfl⟩ : syracuseStep 2162243 = 3243365) B3243365
theorem B1441363 : Blo 1439539 1441363 := bstep (se 1 (by rfl) ⟨1081022, by rfl⟩ : syracuseStep 1441363 = 2162045) B2162045
theorem B2162273 : Blo 1439539 2162273 := bstep (se 2 (by rfl) ⟨810852, by rfl⟩ : syracuseStep 2162273 = 1621705) B1621705
theorem B1441379 : Blo 1439539 1441379 := bstep (se 1 (by rfl) ⟨1081034, by rfl⟩ : syracuseStep 1441379 = 2162069) B2162069
theorem B1441395 : Blo 1439539 1441395 := bstep (se 1 (by rfl) ⟨1081046, by rfl⟩ : syracuseStep 1441395 = 2162093) B2162093
theorem B2162291 : Blo 1439539 2162291 := bstep (se 1 (by rfl) ⟨1621718, by rfl⟩ : syracuseStep 2162291 = 3243437) B3243437
theorem B1441411 : Blo 1439539 1441411 := bstep (se 1 (by rfl) ⟨1081058, by rfl⟩ : syracuseStep 1441411 = 2162117) B2162117
theorem B1441427 : Blo 1439539 1441427 := bstep (se 1 (by rfl) ⟨1081070, by rfl⟩ : syracuseStep 1441427 = 2162141) B2162141
theorem B1621651 : Blo 1439539 1621651 := bstep (se 1 (by rfl) ⟨1216238, by rfl⟩ : syracuseStep 1621651 = 2432477) B2432477
theorem B1441443 : Blo 1439539 1441443 := bstep (se 1 (by rfl) ⟨1081082, by rfl⟩ : syracuseStep 1441443 = 2162165) B2162165
theorem B1441459 : Blo 1439539 1441459 := bstep (se 1 (by rfl) ⟨1081094, by rfl⟩ : syracuseStep 1441459 = 2162189) B2162189
theorem B1441475 : Blo 1439539 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B1441491 : Blo 1439539 1441491 := bstep (se 1 (by rfl) ⟨1081118, by rfl⟩ : syracuseStep 1441491 = 2162237) B2162237
theorem B1441507 : Blo 1439539 1441507 := bstep (se 1 (by rfl) ⟨1081130, by rfl⟩ : syracuseStep 1441507 = 2162261) B2162261
theorem B1441523 : Blo 1439539 1441523 := bstep (se 1 (by rfl) ⟨1081142, by rfl⟩ : syracuseStep 1441523 = 2162285) B2162285
theorem B1441539 : Blo 1439539 1441539 := bstep (se 1 (by rfl) ⟨1081154, by rfl⟩ : syracuseStep 1441539 = 2162309) B2162309
theorem B3645233 : Blo 1439539 3645233 := bstep (se 2 (by rfl) ⟨1366962, by rfl⟩ : syracuseStep 3645233 = 2733925) B2733925
theorem B3645283 : Blo 1439539 3645283 := bstep (se 1 (by rfl) ⟨2733962, by rfl⟩ : syracuseStep 3645283 = 5467925) B5467925
theorem B6922189 : Blo 1439539 6922189 := bstep (se 3 (by rfl) ⟨1297910, by rfl⟩ : syracuseStep 6922189 = 2595821) B2595821
theorem B3645425 : Blo 1439539 3645425 := bstep (se 2 (by rfl) ⟨1367034, by rfl⟩ : syracuseStep 3645425 = 2734069) B2734069
theorem B6152237 : Blo 1439539 6152237 := bstep (se 3 (by rfl) ⟨1153544, by rfl⟩ : syracuseStep 6152237 = 2307089) B2307089
theorem B8208449 : Blo 1439539 8208449 := bstep (se 2 (by rfl) ⟨3078168, by rfl⟩ : syracuseStep 8208449 = 6156337) B6156337
theorem B3645719 : Blo 1439539 3645719 := bstep (se 1 (by rfl) ⟨2734289, by rfl⟩ : syracuseStep 3645719 = 5468579) B5468579
theorem B5194007 : Blo 1439539 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B2736499 : Blo 1439539 2736499 := bstep (se 1 (by rfl) ⟨2052374, by rfl⟩ : syracuseStep 2736499 = 4104749) B4104749
theorem B5472785 : Blo 1439539 5472785 := bstep (se 2 (by rfl) ⟨2052294, by rfl⟩ : syracuseStep 5472785 = 4104589) B4104589
theorem B7291457 : Blo 1439539 7291457 := bstep (se 2 (by rfl) ⟨2734296, by rfl⟩ : syracuseStep 7291457 = 5468593) B5468593
theorem B4497995 : Blo 1439539 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B6152921 : Blo 1439539 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B8111027 : Blo 1439539 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B5473241 : Blo 1439539 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B3646529 : Blo 1439539 3646529 := bstep (se 2 (by rfl) ⟨1367448, by rfl⟩ : syracuseStep 3646529 = 2734897) B2734897
theorem B4858973 : Blo 1439539 4858973 := bstep (se 3 (by rfl) ⟨911057, by rfl⟩ : syracuseStep 4858973 = 1822115) B1822115
theorem B9487691 : Blo 1439539 9487691 := bstep (se 1 (by rfl) ⟨7115768, by rfl⟩ : syracuseStep 9487691 = 14231537) B14231537
theorem B5842349 : Blo 1439539 5842349 := bstep (se 3 (by rfl) ⟨1095440, by rfl⟩ : syracuseStep 5842349 = 2190881) B2190881
theorem B3892673 : Blo 1439539 3892673 := bstep (se 2 (by rfl) ⟨1459752, by rfl⟩ : syracuseStep 3892673 = 2919505) B2919505
theorem B3384791 : Blo 1439539 3384791 := bstep (se 1 (by rfl) ⟨2538593, by rfl⟩ : syracuseStep 3384791 = 5077187) B5077187
theorem B12314177 : Blo 1439539 12314177 := bstep (se 2 (by rfl) ⟨4617816, by rfl⟩ : syracuseStep 12314177 = 9235633) B9235633
theorem B3647065 : Blo 1439539 3647065 := bstep (se 2 (by rfl) ⟨1367649, by rfl⟩ : syracuseStep 3647065 = 2735299) B2735299
theorem B2049943 : Blo 1439539 2049943 := bstep (se 1 (by rfl) ⟨1537457, by rfl⟩ : syracuseStep 2049943 = 3074915) B3074915
theorem B6924305 : Blo 1439539 6924305 := bstep (se 2 (by rfl) ⟨2596614, by rfl⟩ : syracuseStep 6924305 = 5193229) B5193229
theorem B10520621 : Blo 1439539 10520621 := bstep (se 3 (by rfl) ⟨1972616, by rfl⟩ : syracuseStep 10520621 = 3945233) B3945233
theorem B5466163 : Blo 1439539 5466163 := bstep (se 1 (by rfl) ⟨4099622, by rfl⟩ : syracuseStep 5466163 = 8199245) B8199245
theorem B5261363 : Blo 1439539 5261363 := bstep (se 1 (by rfl) ⟨3946022, by rfl⟩ : syracuseStep 5261363 = 7892045) B7892045
theorem B4618073 : Blo 1439539 4618073 := bstep (se 2 (by rfl) ⟨1731777, by rfl⟩ : syracuseStep 4618073 = 3463555) B3463555
theorem B6924419 : Blo 1439539 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B12298391 : Blo 1439539 12298391 := bstep (se 1 (by rfl) ⟨9223793, by rfl⟩ : syracuseStep 12298391 = 18447587) B18447587
theorem B4860107 : Blo 1439539 4860107 := bstep (se 1 (by rfl) ⟨3645080, by rfl⟩ : syracuseStep 4860107 = 7290161) B7290161
theorem B2771351 : Blo 1439539 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B4860377 : Blo 1439539 4860377 := bstep (se 2 (by rfl) ⟨1822641, by rfl⟩ : syracuseStep 4860377 = 3645283) B3645283
theorem B7293401 : Blo 1439539 7293401 := bstep (se 2 (by rfl) ⟨2735025, by rfl⟩ : syracuseStep 7293401 = 5470051) B5470051
theorem B9226817 : Blo 1439539 9226817 := bstep (se 2 (by rfl) ⟨3460056, by rfl⟩ : syracuseStep 9226817 = 6920113) B6920113
theorem B7490123 : Blo 1439539 7490123 := bstep (se 1 (by rfl) ⟨5617592, by rfl⟩ : syracuseStep 7490123 = 11235185) B11235185
theorem B3648179 : Blo 1439539 3648179 := bstep (se 1 (by rfl) ⟨2736134, by rfl⟩ : syracuseStep 3648179 = 5472269) B5472269
theorem B3648473 : Blo 1439539 3648473 := bstep (se 2 (by rfl) ⟨1368177, by rfl⟩ : syracuseStep 3648473 = 2736355) B2736355
theorem B3075059 : Blo 1439539 3075059 := bstep (se 1 (by rfl) ⟨2306294, by rfl⟩ : syracuseStep 3075059 = 4612589) B4612589
theorem B3239027 : Blo 1439539 3239027 := bstep (se 1 (by rfl) ⟨2429270, by rfl⟩ : syracuseStep 3239027 = 4858541) B4858541
theorem B3239063 : Blo 1439539 3239063 := bstep (se 1 (by rfl) ⟨2429297, by rfl⟩ : syracuseStep 3239063 = 4858595) B4858595
theorem B4861079 : Blo 1439539 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B2772235 : Blo 1439539 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B5467409 : Blo 1439539 5467409 := bstep (se 2 (by rfl) ⟨2050278, by rfl⟩ : syracuseStep 5467409 = 4100557) B4100557
theorem B2338073 : Blo 1439539 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B6155585 : Blo 1439539 6155585 := bstep (se 2 (by rfl) ⟨2308344, by rfl⟩ : syracuseStep 6155585 = 4616689) B4616689
theorem B3239243 : Blo 1439539 3239243 := bstep (se 1 (by rfl) ⟨2429432, by rfl⟩ : syracuseStep 3239243 = 4858865) B4858865
theorem B3239297 : Blo 1439539 3239297 := bstep (se 2 (by rfl) ⟨1214736, by rfl⟩ : syracuseStep 3239297 = 2429473) B2429473
theorem B12307889 : Blo 1439539 12307889 := bstep (se 2 (by rfl) ⟨4615458, by rfl⟩ : syracuseStep 12307889 = 9230917) B9230917
theorem B2190809 : Blo 1439539 2190809 := bstep (se 2 (by rfl) ⟨821553, by rfl⟩ : syracuseStep 2190809 = 1643107) B1643107
theorem B3239513 : Blo 1439539 3239513 := bstep (se 2 (by rfl) ⟨1214817, by rfl⟩ : syracuseStep 3239513 = 2429635) B2429635
theorem B2920025 : Blo 1439539 2920025 := bstep (se 2 (by rfl) ⟨1095009, by rfl⟩ : syracuseStep 2920025 = 2190019) B2190019
theorem B3239603 : Blo 1439539 3239603 := bstep (se 1 (by rfl) ⟨2429702, by rfl⟩ : syracuseStep 3239603 = 4859405) B4859405
theorem B4861619 : Blo 1439539 4861619 := bstep (se 1 (by rfl) ⟨3646214, by rfl⟩ : syracuseStep 4861619 = 7292429) B7292429
theorem B3239639 : Blo 1439539 3239639 := bstep (se 1 (by rfl) ⟨2429729, by rfl⟩ : syracuseStep 3239639 = 4859459) B4859459
theorem B3460825 : Blo 1439539 3460825 := bstep (se 2 (by rfl) ⟨1297809, by rfl⟩ : syracuseStep 3460825 = 2595619) B2595619
theorem B4099805 : Blo 1439539 4099805 := bstep (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) B1537427
theorem B5189393 : Blo 1439539 5189393 := bstep (se 2 (by rfl) ⟨1946022, by rfl⟩ : syracuseStep 5189393 = 3892045) B3892045
theorem B3116875 : Blo 1439539 3116875 := bstep (se 1 (by rfl) ⟨2337656, by rfl⟩ : syracuseStep 3116875 = 4675313) B4675313
theorem B11685707 : Blo 1439539 11685707 := bstep (se 1 (by rfl) ⟨8764280, by rfl⟩ : syracuseStep 11685707 = 17528561) B17528561
theorem B3239819 : Blo 1439539 3239819 := bstep (se 1 (by rfl) ⟨2429864, by rfl⟩ : syracuseStep 3239819 = 4859729) B4859729
theorem B2920331 : Blo 1439539 2920331 := bstep (se 1 (by rfl) ⟨2190248, by rfl⟩ : syracuseStep 2920331 = 4380497) B4380497
theorem B2051993 : Blo 1439539 2051993 := bstep (se 2 (by rfl) ⟨769497, by rfl⟩ : syracuseStep 2051993 = 1538995) B1538995
theorem B13840307 : Blo 1439539 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B4100033 : Blo 1439539 4100033 := bstep (se 2 (by rfl) ⟨1537512, by rfl⟩ : syracuseStep 4100033 = 3075025) B3075025
theorem B3239873 : Blo 1439539 3239873 := bstep (se 2 (by rfl) ⟨1214952, by rfl⟩ : syracuseStep 3239873 = 2429905) B2429905
theorem B4861889 : Blo 1439539 4861889 := bstep (se 2 (by rfl) ⟨1823208, by rfl⟩ : syracuseStep 4861889 = 3646417) B3646417
theorem B5468107 : Blo 1439539 5468107 := bstep (se 1 (by rfl) ⟨4101080, by rfl⟩ : syracuseStep 5468107 = 8202161) B8202161
theorem B2191319 : Blo 1439539 2191319 := bstep (se 1 (by rfl) ⟨1643489, by rfl⟩ : syracuseStep 2191319 = 3286979) B3286979
theorem B7295021 : Blo 1439539 7295021 := bstep (se 3 (by rfl) ⟨1367816, by rfl⟩ : syracuseStep 7295021 = 2735633) B2735633
theorem B5189683 : Blo 1439539 5189683 := bstep (se 1 (by rfl) ⟨3892262, by rfl⟩ : syracuseStep 5189683 = 7784525) B7784525
theorem B3240089 : Blo 1439539 3240089 := bstep (se 2 (by rfl) ⟨1215033, by rfl⟩ : syracuseStep 3240089 = 2430067) B2430067
theorem B5468381 : Blo 1439539 5468381 := bstep (se 3 (by rfl) ⟨1025321, by rfl⟩ : syracuseStep 5468381 = 2050643) B2050643
theorem B3240179 : Blo 1439539 3240179 := bstep (se 1 (by rfl) ⟨2430134, by rfl⟩ : syracuseStep 3240179 = 4860269) B4860269
theorem B4100375 : Blo 1439539 4100375 := bstep (se 1 (by rfl) ⟨3075281, by rfl⟩ : syracuseStep 4100375 = 6150563) B6150563
theorem B3240215 : Blo 1439539 3240215 := bstep (se 1 (by rfl) ⟨2430161, by rfl⟩ : syracuseStep 3240215 = 4860323) B4860323
theorem B3076375 : Blo 1439539 3076375 := bstep (se 1 (by rfl) ⟨2307281, by rfl⟩ : syracuseStep 3076375 = 4614563) B4614563
theorem B4378931 : Blo 1439539 4378931 := bstep (se 1 (by rfl) ⟨3284198, by rfl⟩ : syracuseStep 4378931 = 6568397) B6568397
theorem B2920819 : Blo 1439539 2920819 := bstep (se 1 (by rfl) ⟨2190614, by rfl⟩ : syracuseStep 2920819 = 4381229) B4381229
theorem B11245405 : Blo 1439539 11245405 := bstep (se 3 (by rfl) ⟨2108513, by rfl⟩ : syracuseStep 11245405 = 4217027) B4217027
theorem B3330497 : Blo 1439539 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B3240395 : Blo 1439539 3240395 := bstep (se 1 (by rfl) ⟨2430296, by rfl⟩ : syracuseStep 3240395 = 4860593) B4860593
theorem B3076555 : Blo 1439539 3076555 := bstep (se 1 (by rfl) ⟨2307416, by rfl⟩ : syracuseStep 3076555 = 4614833) B4614833
theorem B2429399 : Blo 1439539 2429399 := bstep (se 1 (by rfl) ⟨1822049, by rfl⟩ : syracuseStep 2429399 = 3644099) B3644099
theorem B4862429 : Blo 1439539 4862429 := bstep (se 3 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 4862429 = 1823411) B1823411
theorem B3240449 : Blo 1439539 3240449 := bstep (se 2 (by rfl) ⟨1215168, by rfl⟩ : syracuseStep 3240449 = 2430337) B2430337
theorem B47354381 : Blo 1439539 47354381 := bstep (se 3 (by rfl) ⟨8878946, by rfl⟩ : syracuseStep 47354381 = 17757893) B17757893
theorem B3076631 : Blo 1439539 3076631 := bstep (se 1 (by rfl) ⟨2307473, by rfl⟩ : syracuseStep 3076631 = 4614947) B4614947
theorem B2429527 : Blo 1439539 2429527 := bstep (se 1 (by rfl) ⟨1822145, by rfl⟩ : syracuseStep 2429527 = 3644291) B3644291
theorem B2306647 : Blo 1439539 2306647 := bstep (se 1 (by rfl) ⟨1729985, by rfl⟩ : syracuseStep 2306647 = 3459971) B3459971
theorem B5190317 : Blo 1439539 5190317 := bstep (se 3 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 5190317 = 1946369) B1946369
theorem B3461825 : Blo 1439539 3461825 := bstep (se 2 (by rfl) ⟨1298184, by rfl⟩ : syracuseStep 3461825 = 2596369) B2596369
theorem B2159321 : Blo 1439539 2159321 := bstep (se 2 (by rfl) ⟨809745, by rfl⟩ : syracuseStep 2159321 = 1619491) B1619491
theorem B3240665 : Blo 1439539 3240665 := bstep (se 2 (by rfl) ⟨1215249, by rfl⟩ : syracuseStep 3240665 = 2430499) B2430499
theorem B6157073 : Blo 1439539 6157073 := bstep (se 2 (by rfl) ⟨2308902, by rfl⟩ : syracuseStep 6157073 = 4617805) B4617805
theorem B3240755 : Blo 1439539 3240755 := bstep (se 1 (by rfl) ⟨2430566, by rfl⟩ : syracuseStep 3240755 = 4861133) B4861133
theorem B2159435 : Blo 1439539 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B1823563 : Blo 1439539 1823563 := bstep (se 1 (by rfl) ⟨1367672, by rfl⟩ : syracuseStep 1823563 = 2735345) B2735345
theorem B2159447 : Blo 1439539 2159447 := bstep (se 1 (by rfl) ⟨1619585, by rfl⟩ : syracuseStep 2159447 = 3239171) B3239171
theorem B3240791 : Blo 1439539 3240791 := bstep (se 1 (by rfl) ⟨2430593, by rfl⟩ : syracuseStep 3240791 = 4861187) B4861187
theorem B2732915 : Blo 1439539 2732915 := bstep (se 1 (by rfl) ⟨2049686, by rfl⟩ : syracuseStep 2732915 = 4099373) B4099373
theorem B5469079 : Blo 1439539 5469079 := bstep (se 1 (by rfl) ⟨4101809, by rfl⟩ : syracuseStep 5469079 = 8203619) B8203619
theorem B2732953 : Blo 1439539 2732953 := bstep (se 2 (by rfl) ⟨1024857, by rfl⟩ : syracuseStep 2732953 = 2049715) B2049715
theorem B2159513 : Blo 1439539 2159513 := bstep (se 2 (by rfl) ⟨809817, by rfl⟩ : syracuseStep 2159513 = 1619635) B1619635
theorem B7287731 : Blo 1439539 7287731 := bstep (se 1 (by rfl) ⟨5465798, by rfl⟩ : syracuseStep 7287731 = 10931597) B10931597
theorem B2159627 : Blo 1439539 2159627 := bstep (se 1 (by rfl) ⟨1619720, by rfl⟩ : syracuseStep 2159627 = 3239441) B3239441
theorem B3240971 : Blo 1439539 3240971 := bstep (se 1 (by rfl) ⟨2430728, by rfl⟩ : syracuseStep 3240971 = 4861457) B4861457
theorem B2159639 : Blo 1439539 2159639 := bstep (se 1 (by rfl) ⟨1619729, by rfl⟩ : syracuseStep 2159639 = 3239459) B3239459
theorem B3241025 : Blo 1439539 3241025 := bstep (se 2 (by rfl) ⟨1215384, by rfl⟩ : syracuseStep 3241025 = 2430769) B2430769
theorem B2159705 : Blo 1439539 2159705 := bstep (se 2 (by rfl) ⟨809889, by rfl⟩ : syracuseStep 2159705 = 1619779) B1619779
theorem B4617395 : Blo 1439539 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B21050549 : Blo 1439539 21050549 := bstep (se 5 (by rfl) ⟨986744, by rfl⟩ : syracuseStep 21050549 = 1973489) B1973489
theorem B2159819 : Blo 1439539 2159819 := bstep (se 1 (by rfl) ⟨1619864, by rfl⟩ : syracuseStep 2159819 = 3239729) B3239729
theorem B2430155 : Blo 1439539 2430155 := bstep (se 1 (by rfl) ⟨1822616, by rfl⟩ : syracuseStep 2430155 = 3645233) B3645233
theorem B2159831 : Blo 1439539 2159831 := bstep (se 1 (by rfl) ⟨1619873, by rfl⟩ : syracuseStep 2159831 = 3239747) B3239747
theorem B9229585 : Blo 1439539 9229585 := bstep (se 2 (by rfl) ⟨3461094, by rfl⟩ : syracuseStep 9229585 = 6922189) B6922189
theorem B2159897 : Blo 1439539 2159897 := bstep (se 2 (by rfl) ⟨809961, by rfl⟩ : syracuseStep 2159897 = 1619923) B1619923
theorem B3241241 : Blo 1439539 3241241 := bstep (se 2 (by rfl) ⟨1215465, by rfl⟩ : syracuseStep 3241241 = 2430931) B2430931
theorem B2430283 : Blo 1439539 2430283 := bstep (se 1 (by rfl) ⟨1822712, by rfl⟩ : syracuseStep 2430283 = 3645425) B3645425
theorem B2733401 : Blo 1439539 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B13841765 : Blo 1439539 13841765 := bstep (se 4 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 13841765 = 2595331) B2595331
theorem B3241331 : Blo 1439539 3241331 := bstep (se 1 (by rfl) ⟨2430998, by rfl⟩ : syracuseStep 3241331 = 4861997) B4861997
theorem B2160011 : Blo 1439539 2160011 := bstep (se 1 (by rfl) ⟨1620008, by rfl⟩ : syracuseStep 2160011 = 3240017) B3240017
theorem B2160023 : Blo 1439539 2160023 := bstep (se 1 (by rfl) ⟨1620017, by rfl⟩ : syracuseStep 2160023 = 3240035) B3240035
theorem B3241367 : Blo 1439539 3241367 := bstep (se 1 (by rfl) ⟨2431025, by rfl⟩ : syracuseStep 3241367 = 4862051) B4862051
theorem B2160089 : Blo 1439539 2160089 := bstep (se 2 (by rfl) ⟨810033, by rfl⟩ : syracuseStep 2160089 = 1620067) B1620067
theorem B2430425 : Blo 1439539 2430425 := bstep (se 2 (by rfl) ⟨911409, by rfl⟩ : syracuseStep 2430425 = 1822819) B1822819
theorem B8205785 : Blo 1439539 8205785 := bstep (se 2 (by rfl) ⟨3077169, by rfl⟩ : syracuseStep 8205785 = 6154339) B6154339
theorem B24933905 : Blo 1439539 24933905 := bstep (se 2 (by rfl) ⟨9350214, by rfl⟩ : syracuseStep 24933905 = 18700429) B18700429
theorem B2160203 : Blo 1439539 2160203 := bstep (se 1 (by rfl) ⟨1620152, by rfl⟩ : syracuseStep 2160203 = 3240305) B3240305
theorem B3241547 : Blo 1439539 3241547 := bstep (se 1 (by rfl) ⟨2431160, by rfl⟩ : syracuseStep 3241547 = 4862321) B4862321
theorem B4863563 : Blo 1439539 4863563 := bstep (se 1 (by rfl) ⟨3647672, by rfl⟩ : syracuseStep 4863563 = 7295345) B7295345
theorem B2160215 : Blo 1439539 2160215 := bstep (se 1 (by rfl) ⟨1620161, by rfl⟩ : syracuseStep 2160215 = 3240323) B3240323
theorem B2430553 : Blo 1439539 2430553 := bstep (se 2 (by rfl) ⟨911457, by rfl⟩ : syracuseStep 2430553 = 1822915) B1822915
theorem B1619563 : Blo 1439539 1619563 := bstep (se 1 (by rfl) ⟨1214672, by rfl⟩ : syracuseStep 1619563 = 2429345) B2429345
theorem B3241601 : Blo 1439539 3241601 := bstep (se 2 (by rfl) ⟨1215600, by rfl⟩ : syracuseStep 3241601 = 2431201) B2431201
theorem B19715735 : Blo 1439539 19715735 := bstep (se 1 (by rfl) ⟨14786801, by rfl⟩ : syracuseStep 19715735 = 29573603) B29573603
theorem B2160281 : Blo 1439539 2160281 := bstep (se 2 (by rfl) ⟨810105, by rfl⟩ : syracuseStep 2160281 = 1620211) B1620211
theorem B5469869 : Blo 1439539 5469869 := bstep (se 3 (by rfl) ⟨1025600, by rfl⟩ : syracuseStep 5469869 = 2051201) B2051201
theorem B1619671 : Blo 1439539 1619671 := bstep (se 1 (by rfl) ⟨1214753, by rfl⟩ : syracuseStep 1619671 = 2429507) B2429507
theorem B2160395 : Blo 1439539 2160395 := bstep (se 1 (by rfl) ⟨1620296, by rfl⟩ : syracuseStep 2160395 = 3240593) B3240593
theorem B2160407 : Blo 1439539 2160407 := bstep (se 1 (by rfl) ⟨1620305, by rfl⟩ : syracuseStep 2160407 = 3240611) B3240611
theorem B16398125 : Blo 1439539 16398125 := bstep (se 3 (by rfl) ⟨3074648, by rfl⟩ : syracuseStep 16398125 = 6149297) B6149297
theorem B5191469 : Blo 1439539 5191469 := bstep (se 3 (by rfl) ⟨973400, by rfl⟩ : syracuseStep 5191469 = 1946801) B1946801
theorem B1439543 : Blo 1439539 1439543 := bstep (se 1 (by rfl) ⟨1079657, by rfl⟩ : syracuseStep 1439543 = 2159315) B2159315
theorem B1439563 : Blo 1439539 1439563 := bstep (se 1 (by rfl) ⟨1079672, by rfl⟩ : syracuseStep 1439563 = 2159345) B2159345
theorem B1439575 : Blo 1439539 1439575 := bstep (se 1 (by rfl) ⟨1079681, by rfl⟩ : syracuseStep 1439575 = 2159363) B2159363
theorem B2160473 : Blo 1439539 2160473 := bstep (se 2 (by rfl) ⟨810177, by rfl⟩ : syracuseStep 2160473 = 1620355) B1620355
theorem B3241817 : Blo 1439539 3241817 := bstep (se 2 (by rfl) ⟨1215681, by rfl⟩ : syracuseStep 3241817 = 2431363) B2431363
theorem B6149981 : Blo 1439539 6149981 := bstep (se 3 (by rfl) ⟨1153121, by rfl⟩ : syracuseStep 6149981 = 2306243) B2306243
theorem B4929373 : Blo 1439539 4929373 := bstep (se 3 (by rfl) ⟨924257, by rfl⟩ : syracuseStep 4929373 = 1848515) B1848515
theorem B4863833 : Blo 1439539 4863833 := bstep (se 2 (by rfl) ⟨1823937, by rfl⟩ : syracuseStep 4863833 = 3647875) B3647875
theorem B31135589 : Blo 1439539 31135589 := bstep (se 4 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 31135589 = 5837923) B5837923
theorem B1439595 : Blo 1439539 1439595 := bstep (se 1 (by rfl) ⟨1079696, by rfl⟩ : syracuseStep 1439595 = 2159393) B2159393
theorem B1439607 : Blo 1439539 1439607 := bstep (se 1 (by rfl) ⟨1079705, by rfl⟩ : syracuseStep 1439607 = 2159411) B2159411
theorem B1439627 : Blo 1439539 1439627 := bstep (se 1 (by rfl) ⟨1079720, by rfl⟩ : syracuseStep 1439627 = 2159441) B2159441
theorem B1619851 : Blo 1439539 1619851 := bstep (se 1 (by rfl) ⟨1214888, by rfl⟩ : syracuseStep 1619851 = 2429777) B2429777
theorem B1439639 : Blo 1439539 1439639 := bstep (se 1 (by rfl) ⟨1079729, by rfl⟩ : syracuseStep 1439639 = 2159459) B2159459
theorem B1439659 : Blo 1439539 1439659 := bstep (se 1 (by rfl) ⟨1079744, by rfl⟩ : syracuseStep 1439659 = 2159489) B2159489
theorem B3241907 : Blo 1439539 3241907 := bstep (se 1 (by rfl) ⟨2431430, by rfl⟩ : syracuseStep 3241907 = 4862861) B4862861
theorem B1439671 : Blo 1439539 1439671 := bstep (se 1 (by rfl) ⟨1079753, by rfl⟩ : syracuseStep 1439671 = 2159507) B2159507
theorem B1439691 : Blo 1439539 1439691 := bstep (se 1 (by rfl) ⟨1079768, by rfl⟩ : syracuseStep 1439691 = 2159537) B2159537
theorem B2160587 : Blo 1439539 2160587 := bstep (se 1 (by rfl) ⟨1620440, by rfl⟩ : syracuseStep 2160587 = 3240881) B3240881
theorem B1439703 : Blo 1439539 1439703 := bstep (se 1 (by rfl) ⟨1079777, by rfl⟩ : syracuseStep 1439703 = 2159555) B2159555
theorem B2160599 : Blo 1439539 2160599 := bstep (se 1 (by rfl) ⟨1620449, by rfl⟩ : syracuseStep 2160599 = 3240899) B3240899
theorem B3241943 : Blo 1439539 3241943 := bstep (se 1 (by rfl) ⟨2431457, by rfl⟩ : syracuseStep 3241943 = 4862915) B4862915
theorem B1439723 : Blo 1439539 1439723 := bstep (se 1 (by rfl) ⟨1079792, by rfl⟩ : syracuseStep 1439723 = 2159585) B2159585
theorem B1619959 : Blo 1439539 1619959 := bstep (se 1 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 1619959 = 2429939) B2429939
theorem B1439735 : Blo 1439539 1439735 := bstep (se 1 (by rfl) ⟨1079801, by rfl⟩ : syracuseStep 1439735 = 2159603) B2159603
theorem B1439755 : Blo 1439539 1439755 := bstep (se 1 (by rfl) ⟨1079816, by rfl⟩ : syracuseStep 1439755 = 2159633) B2159633
theorem B10377233 : Blo 1439539 10377233 := bstep (se 2 (by rfl) ⟨3891462, by rfl⟩ : syracuseStep 10377233 = 7782925) B7782925
theorem B1439767 : Blo 1439539 1439767 := bstep (se 1 (by rfl) ⟨1079825, by rfl⟩ : syracuseStep 1439767 = 2159651) B2159651
theorem B2160665 : Blo 1439539 2160665 := bstep (se 2 (by rfl) ⟨810249, by rfl⟩ : syracuseStep 2160665 = 1620499) B1620499
theorem B1439787 : Blo 1439539 1439787 := bstep (se 1 (by rfl) ⟨1079840, by rfl⟩ : syracuseStep 1439787 = 2159681) B2159681
theorem B1439799 : Blo 1439539 1439799 := bstep (se 1 (by rfl) ⟨1079849, by rfl⟩ : syracuseStep 1439799 = 2159699) B2159699
theorem B2734145 : Blo 1439539 2734145 := bstep (se 2 (by rfl) ⟨1025304, by rfl⟩ : syracuseStep 2734145 = 2050609) B2050609
theorem B1439819 : Blo 1439539 1439819 := bstep (se 1 (by rfl) ⟨1079864, by rfl⟩ : syracuseStep 1439819 = 2159729) B2159729
theorem B1439831 : Blo 1439539 1439831 := bstep (se 1 (by rfl) ⟨1079873, by rfl⟩ : syracuseStep 1439831 = 2159747) B2159747
theorem B1439851 : Blo 1439539 1439851 := bstep (se 1 (by rfl) ⟨1079888, by rfl⟩ : syracuseStep 1439851 = 2159777) B2159777
theorem B1439863 : Blo 1439539 1439863 := bstep (se 1 (by rfl) ⟨1079897, by rfl⟩ : syracuseStep 1439863 = 2159795) B2159795
theorem B1439883 : Blo 1439539 1439883 := bstep (se 1 (by rfl) ⟨1079912, by rfl⟩ : syracuseStep 1439883 = 2159825) B2159825
theorem B2160779 : Blo 1439539 2160779 := bstep (se 1 (by rfl) ⟨1620584, by rfl⟩ : syracuseStep 2160779 = 3241169) B3241169
theorem B3242123 : Blo 1439539 3242123 := bstep (se 1 (by rfl) ⟨2431592, by rfl⟩ : syracuseStep 3242123 = 4863185) B4863185
theorem B6150289 : Blo 1439539 6150289 := bstep (se 2 (by rfl) ⟨2306358, by rfl⟩ : syracuseStep 6150289 = 4612717) B4612717
theorem B1439895 : Blo 1439539 1439895 := bstep (se 1 (by rfl) ⟨1079921, by rfl⟩ : syracuseStep 1439895 = 2159843) B2159843
theorem B2160791 : Blo 1439539 2160791 := bstep (se 1 (by rfl) ⟨1620593, by rfl⟩ : syracuseStep 2160791 = 3241187) B3241187
theorem B2431127 : Blo 1439539 2431127 := bstep (se 1 (by rfl) ⟨1823345, by rfl⟩ : syracuseStep 2431127 = 3646691) B3646691
theorem B1439915 : Blo 1439539 1439915 := bstep (se 1 (by rfl) ⟨1079936, by rfl⟩ : syracuseStep 1439915 = 2159873) B2159873
theorem B1620139 : Blo 1439539 1620139 := bstep (se 1 (by rfl) ⟨1215104, by rfl⟩ : syracuseStep 1620139 = 2430209) B2430209
theorem B6150323 : Blo 1439539 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B1439927 : Blo 1439539 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B3242177 : Blo 1439539 3242177 := bstep (se 2 (by rfl) ⟨1215816, by rfl⟩ : syracuseStep 3242177 = 2431633) B2431633
theorem B1439947 : Blo 1439539 1439947 := bstep (se 1 (by rfl) ⟨1079960, by rfl⟩ : syracuseStep 1439947 = 2159921) B2159921
theorem B1439959 : Blo 1439539 1439959 := bstep (se 1 (by rfl) ⟨1079969, by rfl⟩ : syracuseStep 1439959 = 2159939) B2159939
theorem B2160857 : Blo 1439539 2160857 := bstep (se 2 (by rfl) ⟨810321, by rfl⟩ : syracuseStep 2160857 = 1620643) B1620643
theorem B1439979 : Blo 1439539 1439979 := bstep (se 1 (by rfl) ⟨1079984, by rfl⟩ : syracuseStep 1439979 = 2159969) B2159969
theorem B1439991 : Blo 1439539 1439991 := bstep (se 1 (by rfl) ⟨1079993, by rfl⟩ : syracuseStep 1439991 = 2159987) B2159987
theorem B1440011 : Blo 1439539 1440011 := bstep (se 1 (by rfl) ⟨1080008, by rfl⟩ : syracuseStep 1440011 = 2160017) B2160017
theorem B1440023 : Blo 1439539 1440023 := bstep (se 1 (by rfl) ⟨1080017, by rfl⟩ : syracuseStep 1440023 = 2160035) B2160035
theorem B1620247 : Blo 1439539 1620247 := bstep (se 1 (by rfl) ⟨1215185, by rfl⟩ : syracuseStep 1620247 = 2430371) B2430371
theorem B2431255 : Blo 1439539 2431255 := bstep (se 1 (by rfl) ⟨1823441, by rfl⟩ : syracuseStep 2431255 = 3646883) B3646883
theorem B3078425 : Blo 1439539 3078425 := bstep (se 2 (by rfl) ⟨1154409, by rfl⟩ : syracuseStep 3078425 = 2308819) B2308819
theorem B1440043 : Blo 1439539 1440043 := bstep (se 1 (by rfl) ⟨1080032, by rfl⟩ : syracuseStep 1440043 = 2160065) B2160065
theorem B1440055 : Blo 1439539 1440055 := bstep (se 1 (by rfl) ⟨1080041, by rfl⟩ : syracuseStep 1440055 = 2160083) B2160083
theorem B1440075 : Blo 1439539 1440075 := bstep (se 1 (by rfl) ⟨1080056, by rfl⟩ : syracuseStep 1440075 = 2160113) B2160113
theorem B2734411 : Blo 1439539 2734411 := bstep (se 1 (by rfl) ⟨2050808, by rfl⟩ : syracuseStep 2734411 = 4101617) B4101617
theorem B2160971 : Blo 1439539 2160971 := bstep (se 1 (by rfl) ⟨1620728, by rfl⟩ : syracuseStep 2160971 = 3241457) B3241457
theorem B1440087 : Blo 1439539 1440087 := bstep (se 1 (by rfl) ⟨1080065, by rfl⟩ : syracuseStep 1440087 = 2160131) B2160131
theorem B2160983 : Blo 1439539 2160983 := bstep (se 1 (by rfl) ⟨1620737, by rfl⟩ : syracuseStep 2160983 = 3241475) B3241475
theorem B1947991 : Blo 1439539 1947991 := bstep (se 1 (by rfl) ⟨1460993, by rfl⟩ : syracuseStep 1947991 = 2921987) B2921987
theorem B1440107 : Blo 1439539 1440107 := bstep (se 1 (by rfl) ⟨1080080, by rfl⟩ : syracuseStep 1440107 = 2160161) B2160161
theorem B1440119 : Blo 1439539 1440119 := bstep (se 1 (by rfl) ⟨1080089, by rfl⟩ : syracuseStep 1440119 = 2160179) B2160179
theorem B1440139 : Blo 1439539 1440139 := bstep (se 1 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 1440139 = 2160209) B2160209
theorem B6568337 : Blo 1439539 6568337 := bstep (se 2 (by rfl) ⟨2463126, by rfl⟩ : syracuseStep 6568337 = 4926253) B4926253
theorem B1440151 : Blo 1439539 1440151 := bstep (se 1 (by rfl) ⟨1080113, by rfl⟩ : syracuseStep 1440151 = 2160227) B2160227
theorem B2161049 : Blo 1439539 2161049 := bstep (se 2 (by rfl) ⟨810393, by rfl⟩ : syracuseStep 2161049 = 1620787) B1620787
theorem B3242393 : Blo 1439539 3242393 := bstep (se 2 (by rfl) ⟨1215897, by rfl⟩ : syracuseStep 3242393 = 2431795) B2431795
theorem B1440171 : Blo 1439539 1440171 := bstep (se 1 (by rfl) ⟨1080128, by rfl⟩ : syracuseStep 1440171 = 2160257) B2160257
theorem B1440183 : Blo 1439539 1440183 := bstep (se 1 (by rfl) ⟨1080137, by rfl⟩ : syracuseStep 1440183 = 2160275) B2160275
theorem B1440203 : Blo 1439539 1440203 := bstep (se 1 (by rfl) ⟨1080152, by rfl⟩ : syracuseStep 1440203 = 2160305) B2160305
theorem B1620427 : Blo 1439539 1620427 := bstep (se 1 (by rfl) ⟨1215320, by rfl⟩ : syracuseStep 1620427 = 2430641) B2430641
theorem B1440215 : Blo 1439539 1440215 := bstep (se 1 (by rfl) ⟨1080161, by rfl⟩ : syracuseStep 1440215 = 2160323) B2160323
theorem B9861593 : Blo 1439539 9861593 := bstep (se 2 (by rfl) ⟨3698097, by rfl⟩ : syracuseStep 9861593 = 7396195) B7396195
theorem B1440235 : Blo 1439539 1440235 := bstep (se 1 (by rfl) ⟨1080176, by rfl⟩ : syracuseStep 1440235 = 2160353) B2160353
theorem B3242483 : Blo 1439539 3242483 := bstep (se 1 (by rfl) ⟨2431862, by rfl⟩ : syracuseStep 3242483 = 4863725) B4863725
theorem B1440247 : Blo 1439539 1440247 := bstep (se 1 (by rfl) ⟨1080185, by rfl⟩ : syracuseStep 1440247 = 2160371) B2160371
theorem B1538551 : Blo 1439539 1538551 := bstep (se 1 (by rfl) ⟨1153913, by rfl⟩ : syracuseStep 1538551 = 2307827) B2307827
theorem B1440267 : Blo 1439539 1440267 := bstep (se 1 (by rfl) ⟨1080200, by rfl⟩ : syracuseStep 1440267 = 2160401) B2160401
theorem B2161163 : Blo 1439539 2161163 := bstep (se 1 (by rfl) ⟨1620872, by rfl⟩ : syracuseStep 2161163 = 3241745) B3241745
theorem B1440279 : Blo 1439539 1440279 := bstep (se 1 (by rfl) ⟨1080209, by rfl⟩ : syracuseStep 1440279 = 2160419) B2160419
theorem B2161175 : Blo 1439539 2161175 := bstep (se 1 (by rfl) ⟨1620881, by rfl⟩ : syracuseStep 2161175 = 3241763) B3241763
theorem B3242519 : Blo 1439539 3242519 := bstep (se 1 (by rfl) ⟨2431889, by rfl⟩ : syracuseStep 3242519 = 4863779) B4863779
theorem B4864535 : Blo 1439539 4864535 := bstep (se 1 (by rfl) ⟨3648401, by rfl⟩ : syracuseStep 4864535 = 7296803) B7296803
theorem B1440299 : Blo 1439539 1440299 := bstep (se 1 (by rfl) ⟨1080224, by rfl⟩ : syracuseStep 1440299 = 2160449) B2160449
theorem B1440311 : Blo 1439539 1440311 := bstep (se 1 (by rfl) ⟨1080233, by rfl⟩ : syracuseStep 1440311 = 2160467) B2160467
theorem B1620535 : Blo 1439539 1620535 := bstep (se 1 (by rfl) ⟨1215401, by rfl⟩ : syracuseStep 1620535 = 2430803) B2430803
theorem B4102721 : Blo 1439539 4102721 := bstep (se 2 (by rfl) ⟨1538520, by rfl⟩ : syracuseStep 4102721 = 3077041) B3077041
theorem B1440331 : Blo 1439539 1440331 := bstep (se 1 (by rfl) ⟨1080248, by rfl⟩ : syracuseStep 1440331 = 2160497) B2160497
theorem B10385995 : Blo 1439539 10385995 := bstep (se 1 (by rfl) ⟨7789496, by rfl⟩ : syracuseStep 10385995 = 15578993) B15578993
theorem B1440343 : Blo 1439539 1440343 := bstep (se 1 (by rfl) ⟨1080257, by rfl⟩ : syracuseStep 1440343 = 2160515) B2160515
theorem B2161241 : Blo 1439539 2161241 := bstep (se 2 (by rfl) ⟨810465, by rfl⟩ : syracuseStep 2161241 = 1620931) B1620931
theorem B1440363 : Blo 1439539 1440363 := bstep (se 1 (by rfl) ⟨1080272, by rfl⟩ : syracuseStep 1440363 = 2160545) B2160545
theorem B1440375 : Blo 1439539 1440375 := bstep (se 1 (by rfl) ⟨1080281, by rfl⟩ : syracuseStep 1440375 = 2160563) B2160563
theorem B1440395 : Blo 1439539 1440395 := bstep (se 1 (by rfl) ⟨1080296, by rfl⟩ : syracuseStep 1440395 = 2160593) B2160593
theorem B1440407 : Blo 1439539 1440407 := bstep (se 1 (by rfl) ⟨1080305, by rfl⟩ : syracuseStep 1440407 = 2160611) B2160611
theorem B1440427 : Blo 1439539 1440427 := bstep (se 1 (by rfl) ⟨1080320, by rfl⟩ : syracuseStep 1440427 = 2160641) B2160641
theorem B1440439 : Blo 1439539 1440439 := bstep (se 1 (by rfl) ⟨1080329, by rfl⟩ : syracuseStep 1440439 = 2160659) B2160659
theorem B1440459 : Blo 1439539 1440459 := bstep (se 1 (by rfl) ⟨1080344, by rfl⟩ : syracuseStep 1440459 = 2160689) B2160689
theorem B2161355 : Blo 1439539 2161355 := bstep (se 1 (by rfl) ⟨1621016, by rfl⟩ : syracuseStep 2161355 = 3242033) B3242033
theorem B3242699 : Blo 1439539 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B1440471 : Blo 1439539 1440471 := bstep (se 1 (by rfl) ⟨1080353, by rfl⟩ : syracuseStep 1440471 = 2160707) B2160707
theorem B2161367 : Blo 1439539 2161367 := bstep (se 1 (by rfl) ⟨1621025, by rfl⟩ : syracuseStep 2161367 = 3242051) B3242051
theorem B1440491 : Blo 1439539 1440491 := bstep (se 1 (by rfl) ⟨1080368, by rfl⟩ : syracuseStep 1440491 = 2160737) B2160737
theorem B1620715 : Blo 1439539 1620715 := bstep (se 1 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 1620715 = 2431073) B2431073
theorem B1440503 : Blo 1439539 1440503 := bstep (se 1 (by rfl) ⟨1080377, by rfl⟩ : syracuseStep 1440503 = 2160755) B2160755
theorem B3242753 : Blo 1439539 3242753 := bstep (se 2 (by rfl) ⟨1216032, by rfl⟩ : syracuseStep 3242753 = 2432065) B2432065
theorem B11680517 : Blo 1439539 11680517 := bstep (se 4 (by rfl) ⟨1095048, by rfl⟩ : syracuseStep 11680517 = 2190097) B2190097
theorem B1440523 : Blo 1439539 1440523 := bstep (se 1 (by rfl) ⟨1080392, by rfl⟩ : syracuseStep 1440523 = 2160785) B2160785
theorem B2734859 : Blo 1439539 2734859 := bstep (se 1 (by rfl) ⟨2051144, by rfl⟩ : syracuseStep 2734859 = 4102289) B4102289
theorem B1440535 : Blo 1439539 1440535 := bstep (se 1 (by rfl) ⟨1080401, by rfl⟩ : syracuseStep 1440535 = 2160803) B2160803
theorem B2161433 : Blo 1439539 2161433 := bstep (se 2 (by rfl) ⟨810537, by rfl⟩ : syracuseStep 2161433 = 1621075) B1621075
theorem B1440555 : Blo 1439539 1440555 := bstep (se 1 (by rfl) ⟨1080416, by rfl⟩ : syracuseStep 1440555 = 2160833) B2160833
theorem B1440567 : Blo 1439539 1440567 := bstep (se 1 (by rfl) ⟨1080425, by rfl⟩ : syracuseStep 1440567 = 2160851) B2160851
theorem B7289675 : Blo 1439539 7289675 := bstep (se 1 (by rfl) ⟨5467256, by rfl⟩ : syracuseStep 7289675 = 10934513) B10934513
theorem B1440587 : Blo 1439539 1440587 := bstep (se 1 (by rfl) ⟨1080440, by rfl⟩ : syracuseStep 1440587 = 2160881) B2160881
theorem B1440599 : Blo 1439539 1440599 := bstep (se 1 (by rfl) ⟨1080449, by rfl⟩ : syracuseStep 1440599 = 2160899) B2160899
theorem B1620823 : Blo 1439539 1620823 := bstep (se 1 (by rfl) ⟨1215617, by rfl⟩ : syracuseStep 1620823 = 2431235) B2431235
theorem B1440619 : Blo 1439539 1440619 := bstep (se 1 (by rfl) ⟨1080464, by rfl⟩ : syracuseStep 1440619 = 2160929) B2160929
theorem B1440631 : Blo 1439539 1440631 := bstep (se 1 (by rfl) ⟨1080473, by rfl⟩ : syracuseStep 1440631 = 2160947) B2160947
theorem B1440651 : Blo 1439539 1440651 := bstep (se 1 (by rfl) ⟨1080488, by rfl⟩ : syracuseStep 1440651 = 2160977) B2160977
theorem B2161547 : Blo 1439539 2161547 := bstep (se 1 (by rfl) ⟨1621160, by rfl⟩ : syracuseStep 2161547 = 3242321) B3242321
theorem B2431883 : Blo 1439539 2431883 := bstep (se 1 (by rfl) ⟨1823912, by rfl⟩ : syracuseStep 2431883 = 3647825) B3647825
theorem B3644311 : Blo 1439539 3644311 := bstep (se 1 (by rfl) ⟨2733233, by rfl⟩ : syracuseStep 3644311 = 5466467) B5466467
theorem B1440663 : Blo 1439539 1440663 := bstep (se 1 (by rfl) ⟨1080497, by rfl⟩ : syracuseStep 1440663 = 2160995) B2160995
theorem B2161559 : Blo 1439539 2161559 := bstep (se 1 (by rfl) ⟨1621169, by rfl⟩ : syracuseStep 2161559 = 3242339) B3242339
theorem B1440683 : Blo 1439539 1440683 := bstep (se 1 (by rfl) ⟨1080512, by rfl⟩ : syracuseStep 1440683 = 2161025) B2161025
theorem B1440695 : Blo 1439539 1440695 := bstep (se 1 (by rfl) ⟨1080521, by rfl⟩ : syracuseStep 1440695 = 2161043) B2161043
theorem B2735041 : Blo 1439539 2735041 := bstep (se 2 (by rfl) ⟨1025640, by rfl⟩ : syracuseStep 2735041 = 2051281) B2051281
theorem B3161035 : Blo 1439539 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B1440715 : Blo 1439539 1440715 := bstep (se 1 (by rfl) ⟨1080536, by rfl⟩ : syracuseStep 1440715 = 2161073) B2161073
theorem B1440727 : Blo 1439539 1440727 := bstep (se 1 (by rfl) ⟨1080545, by rfl⟩ : syracuseStep 1440727 = 2161091) B2161091
theorem B2161625 : Blo 1439539 2161625 := bstep (se 2 (by rfl) ⟨810609, by rfl⟩ : syracuseStep 2161625 = 1621219) B1621219
theorem B12311513 : Blo 1439539 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B3242969 : Blo 1439539 3242969 := bstep (se 2 (by rfl) ⟨1216113, by rfl⟩ : syracuseStep 3242969 = 2432227) B2432227
theorem B1440747 : Blo 1439539 1440747 := bstep (se 1 (by rfl) ⟨1080560, by rfl⟩ : syracuseStep 1440747 = 2161121) B2161121
theorem B1440759 : Blo 1439539 1440759 := bstep (se 1 (by rfl) ⟨1080569, by rfl⟩ : syracuseStep 1440759 = 2161139) B2161139
theorem B1440779 : Blo 1439539 1440779 := bstep (se 1 (by rfl) ⟨1080584, by rfl⟩ : syracuseStep 1440779 = 2161169) B2161169
theorem B1621003 : Blo 1439539 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B2432011 : Blo 1439539 2432011 := bstep (se 1 (by rfl) ⟨1824008, by rfl⟩ : syracuseStep 2432011 = 3648017) B3648017
theorem B1440791 : Blo 1439539 1440791 := bstep (se 1 (by rfl) ⟨1080593, by rfl⟩ : syracuseStep 1440791 = 2161187) B2161187
theorem B6241303 : Blo 1439539 6241303 := bstep (se 1 (by rfl) ⟨4680977, by rfl⟩ : syracuseStep 6241303 = 9361955) B9361955
theorem B1440811 : Blo 1439539 1440811 := bstep (se 1 (by rfl) ⟨1080608, by rfl⟩ : syracuseStep 1440811 = 2161217) B2161217
theorem B3243059 : Blo 1439539 3243059 := bstep (se 1 (by rfl) ⟨2432294, by rfl⟩ : syracuseStep 3243059 = 4864589) B4864589
theorem B4865075 : Blo 1439539 4865075 := bstep (se 1 (by rfl) ⟨3648806, by rfl⟩ : syracuseStep 4865075 = 7297613) B7297613
theorem B1440823 : Blo 1439539 1440823 := bstep (se 1 (by rfl) ⟨1080617, by rfl⟩ : syracuseStep 1440823 = 2161235) B2161235
theorem B5471297 : Blo 1439539 5471297 := bstep (se 2 (by rfl) ⟨2051736, by rfl⟩ : syracuseStep 5471297 = 4103473) B4103473
theorem B1440843 : Blo 1439539 1440843 := bstep (se 1 (by rfl) ⟨1080632, by rfl⟩ : syracuseStep 1440843 = 2161265) B2161265
theorem B2161739 : Blo 1439539 2161739 := bstep (se 1 (by rfl) ⟨1621304, by rfl⟩ : syracuseStep 2161739 = 3242609) B3242609
theorem B1440855 : Blo 1439539 1440855 := bstep (se 1 (by rfl) ⟨1080641, by rfl⟩ : syracuseStep 1440855 = 2161283) B2161283
theorem B2161751 : Blo 1439539 2161751 := bstep (se 1 (by rfl) ⟨1621313, by rfl⟩ : syracuseStep 2161751 = 3242627) B3242627
theorem B4103257 : Blo 1439539 4103257 := bstep (se 2 (by rfl) ⟨1538721, by rfl⟩ : syracuseStep 4103257 = 3077443) B3077443
theorem B3243095 : Blo 1439539 3243095 := bstep (se 1 (by rfl) ⟨2432321, by rfl⟩ : syracuseStep 3243095 = 4864643) B4864643
theorem B1440875 : Blo 1439539 1440875 := bstep (se 1 (by rfl) ⟨1080656, by rfl⟩ : syracuseStep 1440875 = 2161313) B2161313
theorem B1440887 : Blo 1439539 1440887 := bstep (se 1 (by rfl) ⟨1080665, by rfl⟩ : syracuseStep 1440887 = 2161331) B2161331
theorem B1621111 : Blo 1439539 1621111 := bstep (se 1 (by rfl) ⟨1215833, by rfl⟩ : syracuseStep 1621111 = 2431667) B2431667
theorem B1440907 : Blo 1439539 1440907 := bstep (se 1 (by rfl) ⟨1080680, by rfl⟩ : syracuseStep 1440907 = 2161361) B2161361
theorem B5192855 : Blo 1439539 5192855 := bstep (se 1 (by rfl) ⟨3894641, by rfl⟩ : syracuseStep 5192855 = 7789283) B7789283
theorem B1440919 : Blo 1439539 1440919 := bstep (se 1 (by rfl) ⟨1080689, by rfl⟩ : syracuseStep 1440919 = 2161379) B2161379
theorem B31587479 : Blo 1439539 31587479 := bstep (se 1 (by rfl) ⟨23690609, by rfl⟩ : syracuseStep 31587479 = 47381219) B47381219
theorem B2161817 : Blo 1439539 2161817 := bstep (se 2 (by rfl) ⟨810681, by rfl⟩ : syracuseStep 2161817 = 1621363) B1621363
theorem B2432153 : Blo 1439539 2432153 := bstep (se 2 (by rfl) ⟨912057, by rfl⟩ : syracuseStep 2432153 = 1824115) B1824115
theorem B1440939 : Blo 1439539 1440939 := bstep (se 1 (by rfl) ⟨1080704, by rfl⟩ : syracuseStep 1440939 = 2161409) B2161409
theorem B1440951 : Blo 1439539 1440951 := bstep (se 1 (by rfl) ⟨1080713, by rfl⟩ : syracuseStep 1440951 = 2161427) B2161427
theorem B1440971 : Blo 1439539 1440971 := bstep (se 1 (by rfl) ⟨1080728, by rfl⟩ : syracuseStep 1440971 = 2161457) B2161457
theorem B1440983 : Blo 1439539 1440983 := bstep (se 1 (by rfl) ⟨1080737, by rfl⟩ : syracuseStep 1440983 = 2161475) B2161475
theorem B1441003 : Blo 1439539 1441003 := bstep (se 1 (by rfl) ⟨1080752, by rfl⟩ : syracuseStep 1441003 = 2161505) B2161505
theorem B1441015 : Blo 1439539 1441015 := bstep (se 1 (by rfl) ⟨1080761, by rfl⟩ : syracuseStep 1441015 = 2161523) B2161523
theorem B1441035 : Blo 1439539 1441035 := bstep (se 1 (by rfl) ⟨1080776, by rfl⟩ : syracuseStep 1441035 = 2161553) B2161553
theorem B2161931 : Blo 1439539 2161931 := bstep (se 1 (by rfl) ⟨1621448, by rfl⟩ : syracuseStep 2161931 = 3242897) B3242897
theorem B3243275 : Blo 1439539 3243275 := bstep (se 1 (by rfl) ⟨2432456, by rfl⟩ : syracuseStep 3243275 = 4864913) B4864913
theorem B2735383 : Blo 1439539 2735383 := bstep (se 1 (by rfl) ⟨2051537, by rfl⟩ : syracuseStep 2735383 = 4103075) B4103075
theorem B1441047 : Blo 1439539 1441047 := bstep (se 1 (by rfl) ⟨1080785, by rfl⟩ : syracuseStep 1441047 = 2161571) B2161571
theorem B2161943 : Blo 1439539 2161943 := bstep (se 1 (by rfl) ⟨1621457, by rfl⟩ : syracuseStep 2161943 = 3242915) B3242915
theorem B2432281 : Blo 1439539 2432281 := bstep (se 2 (by rfl) ⟨912105, by rfl⟩ : syracuseStep 2432281 = 1824211) B1824211
theorem B1441067 : Blo 1439539 1441067 := bstep (se 1 (by rfl) ⟨1080800, by rfl⟩ : syracuseStep 1441067 = 2161601) B2161601
theorem B1621291 : Blo 1439539 1621291 := bstep (se 1 (by rfl) ⟨1215968, by rfl⟩ : syracuseStep 1621291 = 2431937) B2431937
theorem B1539371 : Blo 1439539 1539371 := bstep (se 1 (by rfl) ⟨1154528, by rfl⟩ : syracuseStep 1539371 = 2309057) B2309057
theorem B1441079 : Blo 1439539 1441079 := bstep (se 1 (by rfl) ⟨1080809, by rfl⟩ : syracuseStep 1441079 = 2161619) B2161619
theorem B3243329 : Blo 1439539 3243329 := bstep (se 2 (by rfl) ⟨1216248, by rfl⟩ : syracuseStep 3243329 = 2432497) B2432497
theorem B3644747 : Blo 1439539 3644747 := bstep (se 1 (by rfl) ⟨2733560, by rfl⟩ : syracuseStep 3644747 = 5467121) B5467121
theorem B1441099 : Blo 1439539 1441099 := bstep (se 1 (by rfl) ⟨1080824, by rfl⟩ : syracuseStep 1441099 = 2161649) B2161649
theorem B1441111 : Blo 1439539 1441111 := bstep (se 1 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 1441111 = 2161667) B2161667
theorem B2162009 : Blo 1439539 2162009 := bstep (se 2 (by rfl) ⟨810753, by rfl⟩ : syracuseStep 2162009 = 1621507) B1621507
theorem B4382045 : Blo 1439539 4382045 := bstep (se 3 (by rfl) ⟨821633, by rfl⟩ : syracuseStep 4382045 = 1643267) B1643267
theorem B1441131 : Blo 1439539 1441131 := bstep (se 1 (by rfl) ⟨1080848, by rfl⟩ : syracuseStep 1441131 = 2161697) B2161697
theorem B1441143 : Blo 1439539 1441143 := bstep (se 1 (by rfl) ⟨1080857, by rfl⟩ : syracuseStep 1441143 = 2161715) B2161715
theorem B1441163 : Blo 1439539 1441163 := bstep (se 1 (by rfl) ⟨1080872, by rfl⟩ : syracuseStep 1441163 = 2161745) B2161745
theorem B1441175 : Blo 1439539 1441175 := bstep (se 1 (by rfl) ⟨1080881, by rfl⟩ : syracuseStep 1441175 = 2161763) B2161763
theorem B1621399 : Blo 1439539 1621399 := bstep (se 1 (by rfl) ⟨1216049, by rfl⟩ : syracuseStep 1621399 = 2432099) B2432099
theorem B1441195 : Blo 1439539 1441195 := bstep (se 1 (by rfl) ⟨1080896, by rfl⟩ : syracuseStep 1441195 = 2161793) B2161793
theorem B1441207 : Blo 1439539 1441207 := bstep (se 1 (by rfl) ⟨1080905, by rfl⟩ : syracuseStep 1441207 = 2161811) B2161811
theorem B1441227 : Blo 1439539 1441227 := bstep (se 1 (by rfl) ⟨1080920, by rfl⟩ : syracuseStep 1441227 = 2161841) B2161841
theorem B2162123 : Blo 1439539 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B1441239 : Blo 1439539 1441239 := bstep (se 1 (by rfl) ⟨1080929, by rfl⟩ : syracuseStep 1441239 = 2161859) B2161859
theorem B2162135 : Blo 1439539 2162135 := bstep (se 1 (by rfl) ⟨1621601, by rfl⟩ : syracuseStep 2162135 = 3243203) B3243203
theorem B15580633 : Blo 1439539 15580633 := bstep (se 2 (by rfl) ⟨5842737, by rfl⟩ : syracuseStep 15580633 = 11685475) B11685475
theorem B1441259 : Blo 1439539 1441259 := bstep (se 1 (by rfl) ⟨1080944, by rfl⟩ : syracuseStep 1441259 = 2161889) B2161889
theorem B2735603 : Blo 1439539 2735603 := bstep (se 1 (by rfl) ⟨2051702, by rfl⟩ : syracuseStep 2735603 = 4103405) B4103405
theorem B1441271 : Blo 1439539 1441271 := bstep (se 1 (by rfl) ⟨1080953, by rfl⟩ : syracuseStep 1441271 = 2161907) B2161907
theorem B2465291 : Blo 1439539 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B1441291 : Blo 1439539 1441291 := bstep (se 1 (by rfl) ⟨1080968, by rfl⟩ : syracuseStep 1441291 = 2161937) B2161937
theorem B1441303 : Blo 1439539 1441303 := bstep (se 1 (by rfl) ⟨1080977, by rfl⟩ : syracuseStep 1441303 = 2161955) B2161955
theorem B2162201 : Blo 1439539 2162201 := bstep (se 2 (by rfl) ⟨810825, by rfl⟩ : syracuseStep 2162201 = 1621651) B1621651
theorem B1441323 : Blo 1439539 1441323 := bstep (se 1 (by rfl) ⟨1080992, by rfl⟩ : syracuseStep 1441323 = 2161985) B2161985
theorem B1441335 : Blo 1439539 1441335 := bstep (se 1 (by rfl) ⟨1081001, by rfl⟩ : syracuseStep 1441335 = 2162003) B2162003
theorem B1441355 : Blo 1439539 1441355 := bstep (se 1 (by rfl) ⟨1081016, by rfl⟩ : syracuseStep 1441355 = 2162033) B2162033
theorem B1621579 : Blo 1439539 1621579 := bstep (se 1 (by rfl) ⟨1216184, by rfl⟩ : syracuseStep 1621579 = 2432369) B2432369
theorem B1441367 : Blo 1439539 1441367 := bstep (se 1 (by rfl) ⟨1081025, by rfl⟩ : syracuseStep 1441367 = 2162051) B2162051
theorem B1441387 : Blo 1439539 1441387 := bstep (se 1 (by rfl) ⟨1081040, by rfl⟩ : syracuseStep 1441387 = 2162081) B2162081
theorem B1441399 : Blo 1439539 1441399 := bstep (se 1 (by rfl) ⟨1081049, by rfl⟩ : syracuseStep 1441399 = 2162099) B2162099
theorem B1441419 : Blo 1439539 1441419 := bstep (se 1 (by rfl) ⟨1081064, by rfl⟩ : syracuseStep 1441419 = 2162129) B2162129
theorem B6659729 : Blo 1439539 6659729 := bstep (se 2 (by rfl) ⟨2497398, by rfl⟩ : syracuseStep 6659729 = 4994797) B4994797
theorem B7790231 : Blo 1439539 7790231 := bstep (se 1 (by rfl) ⟨5842673, by rfl⟩ : syracuseStep 7790231 = 11685347) B11685347
theorem B1441431 : Blo 1439539 1441431 := bstep (se 1 (by rfl) ⟨1081073, by rfl⟩ : syracuseStep 1441431 = 2162147) B2162147
theorem B7397015 : Blo 1439539 7397015 := bstep (se 1 (by rfl) ⟨5547761, by rfl⟩ : syracuseStep 7397015 = 11095523) B11095523
theorem B1441451 : Blo 1439539 1441451 := bstep (se 1 (by rfl) ⟨1081088, by rfl⟩ : syracuseStep 1441451 = 2162177) B2162177
theorem B1441463 : Blo 1439539 1441463 := bstep (se 1 (by rfl) ⟨1081097, by rfl⟩ : syracuseStep 1441463 = 2162195) B2162195
theorem B1621687 : Blo 1439539 1621687 := bstep (se 1 (by rfl) ⟨1216265, by rfl⟩ : syracuseStep 1621687 = 2432531) B2432531
theorem B3645121 : Blo 1439539 3645121 := bstep (se 2 (by rfl) ⟨1366920, by rfl⟩ : syracuseStep 3645121 = 2733841) B2733841
theorem B56123077 : Blo 1439539 56123077 := bstep (se 4 (by rfl) ⟨5261538, by rfl⟩ : syracuseStep 56123077 = 10523077) B10523077
theorem B1441483 : Blo 1439539 1441483 := bstep (se 1 (by rfl) ⟨1081112, by rfl⟩ : syracuseStep 1441483 = 2162225) B2162225
theorem B66576077 : Blo 1439539 66576077 := bstep (se 3 (by rfl) ⟨12483014, by rfl⟩ : syracuseStep 66576077 = 24966029) B24966029
theorem B2735831 : Blo 1439539 2735831 := bstep (se 1 (by rfl) ⟨2051873, by rfl⟩ : syracuseStep 2735831 = 4103747) B4103747
theorem B1441495 : Blo 1439539 1441495 := bstep (se 1 (by rfl) ⟨1081121, by rfl⟩ : syracuseStep 1441495 = 2162243) B2162243
theorem B1441515 : Blo 1439539 1441515 := bstep (se 1 (by rfl) ⟨1081136, by rfl⟩ : syracuseStep 1441515 = 2162273) B2162273
theorem B1441527 : Blo 1439539 1441527 := bstep (se 1 (by rfl) ⟨1081145, by rfl⟩ : syracuseStep 1441527 = 2162291) B2162291
theorem B8199953 : Blo 1439539 8199953 := bstep (se 2 (by rfl) ⟨3074982, by rfl⟩ : syracuseStep 8199953 = 6149965) B6149965
theorem B2736089 : Blo 1439539 2736089 := bstep (se 2 (by rfl) ⟨1026033, by rfl⟩ : syracuseStep 2736089 = 2052067) B2052067
theorem B5472299 : Blo 1439539 5472299 := bstep (se 1 (by rfl) ⟨4104224, by rfl⟩ : syracuseStep 5472299 = 8208449) B8208449
theorem B3645587 : Blo 1439539 3645587 := bstep (se 1 (by rfl) ⟨2734190, by rfl⟩ : syracuseStep 3645587 = 5468381) B5468381
theorem B8200385 : Blo 1439539 8200385 := bstep (se 2 (by rfl) ⟨3075144, by rfl⟩ : syracuseStep 8200385 = 6150289) B6150289
theorem B2998663 : Blo 1439539 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B3645881 : Blo 1439539 3645881 := bstep (se 2 (by rfl) ⟨1367205, by rfl⟩ : syracuseStep 3645881 = 2734411) B2734411
theorem B2597321 : Blo 1439539 2597321 := bstep (se 2 (by rfl) ⟨973995, by rfl⟩ : syracuseStep 2597321 = 1947991) B1947991
theorem B4104715 : Blo 1439539 4104715 := bstep (se 1 (by rfl) ⟨3078536, by rfl⟩ : syracuseStep 4104715 = 6157073) B6157073
theorem B4858487 : Blo 1439539 4858487 := bstep (se 1 (by rfl) ⟨3643865, by rfl⟩ : syracuseStep 4858487 = 7287731) B7287731
theorem B8209133 : Blo 1439539 8209133 := bstep (se 3 (by rfl) ⟨1539212, by rfl⟩ : syracuseStep 8209133 = 3078425) B3078425
theorem B4104989 : Blo 1439539 4104989 := bstep (se 3 (by rfl) ⟨769685, by rfl⟩ : syracuseStep 4104989 = 1539371) B1539371
theorem B14033699 : Blo 1439539 14033699 := bstep (se 1 (by rfl) ⟨10525274, by rfl⟩ : syracuseStep 14033699 = 21050549) B21050549
theorem B6325127 : Blo 1439539 6325127 := bstep (se 1 (by rfl) ⟨4743845, by rfl⟩ : syracuseStep 6325127 = 9487691) B9487691
theorem B16622603 : Blo 1439539 16622603 := bstep (se 1 (by rfl) ⟨12466952, by rfl⟩ : syracuseStep 16622603 = 24933905) B24933905
theorem B8209451 : Blo 1439539 8209451 := bstep (se 1 (by rfl) ⟨6157088, by rfl⟩ : syracuseStep 8209451 = 12314177) B12314177
theorem B17515565 : Blo 1439539 17515565 := bstep (se 3 (by rfl) ⟨3284168, by rfl⟩ : syracuseStep 17515565 = 6568337) B6568337
theorem B3646579 : Blo 1439539 3646579 := bstep (se 1 (by rfl) ⟨2734934, by rfl⟩ : syracuseStep 3646579 = 5469869) B5469869
theorem B18457733 : Blo 1439539 18457733 := bstep (se 4 (by rfl) ⟨1730412, by rfl⟩ : syracuseStep 18457733 = 3460825) B3460825
theorem B8881325 : Blo 1439539 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B4859081 : Blo 1439539 4859081 := bstep (se 2 (by rfl) ⟨1822155, by rfl⟩ : syracuseStep 4859081 = 3644311) B3644311
theorem B7292105 : Blo 1439539 7292105 := bstep (se 2 (by rfl) ⟨2734539, by rfl⟩ : syracuseStep 7292105 = 5469079) B5469079
theorem B26297581 : Blo 1439539 26297581 := bstep (se 3 (by rfl) ⟨4930796, by rfl⟩ : syracuseStep 26297581 = 9861593) B9861593
theorem B3646721 : Blo 1439539 3646721 := bstep (se 2 (by rfl) ⟨1367520, by rfl⟩ : syracuseStep 3646721 = 2735041) B2735041
theorem B7013747 : Blo 1439539 7013747 := bstep (se 1 (by rfl) ⟨5260310, by rfl⟩ : syracuseStep 7013747 = 10520621) B10520621
theorem B3507575 : Blo 1439539 3507575 := bstep (se 1 (by rfl) ⟨2630681, by rfl⟩ : syracuseStep 3507575 = 5261363) B5261363
theorem B3696313 : Blo 1439539 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B12306113 : Blo 1439539 12306113 := bstep (se 2 (by rfl) ⟨4614792, by rfl⟩ : syracuseStep 12306113 = 9229585) B9229585
theorem B3647177 : Blo 1439539 3647177 := bstep (se 2 (by rfl) ⟨1367691, by rfl⟩ : syracuseStep 3647177 = 2735383) B2735383
theorem B4859783 : Blo 1439539 4859783 := bstep (se 1 (by rfl) ⟨3644837, by rfl⟩ : syracuseStep 4859783 = 7289675) B7289675
theorem B2050039 : Blo 1439539 2050039 := bstep (se 1 (by rfl) ⟨1537529, by rfl⟩ : syracuseStep 2050039 = 3075059) B3075059
theorem B3647531 : Blo 1439539 3647531 := bstep (se 1 (by rfl) ⟨2735648, by rfl⟩ : syracuseStep 3647531 = 5471297) B5471297
theorem B1558715 : Blo 1439539 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B12314861 : Blo 1439539 12314861 := bstep (se 3 (by rfl) ⟨2309036, by rfl⟩ : syracuseStep 12314861 = 4618073) B4618073
theorem B36104437 : Blo 1439539 36104437 := bstep (se 5 (by rfl) ⟨1692395, by rfl⟩ : syracuseStep 36104437 = 3384791) B3384791
theorem B4860161 : Blo 1439539 4860161 := bstep (se 2 (by rfl) ⟨1822560, by rfl⟩ : syracuseStep 4860161 = 3645121) B3645121
theorem B1460539 : Blo 1439539 1460539 := bstep (se 1 (by rfl) ⟨1095404, by rfl⟩ : syracuseStep 1460539 = 2190809) B2190809
theorem B4155833 : Blo 1439539 4155833 := bstep (se 2 (by rfl) ⟨1558437, by rfl⟩ : syracuseStep 4155833 = 3116875) B3116875
theorem B6572497 : Blo 1439539 6572497 := bstep (se 2 (by rfl) ⟨2464686, by rfl⟩ : syracuseStep 6572497 = 4929373) B4929373
theorem B14993873 : Blo 1439539 14993873 := bstep (se 2 (by rfl) ⟨5622702, by rfl⟩ : syracuseStep 14993873 = 11245405) B11245405
theorem B21629405 : Blo 1439539 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B5466635 : Blo 1439539 5466635 := bstep (se 1 (by rfl) ⟨4099976, by rfl⟩ : syracuseStep 5466635 = 8199953) B8199953
theorem B3459595 : Blo 1439539 3459595 := bstep (se 1 (by rfl) ⟨2594696, by rfl⟩ : syracuseStep 3459595 = 5189393) B5189393
theorem B9226871 : Blo 1439539 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B1460879 : Blo 1439539 1460879 := bstep (se 1 (by rfl) ⟨1095659, by rfl⟩ : syracuseStep 1460879 = 2191319) B2191319
theorem B2919287 : Blo 1439539 2919287 := bstep (se 1 (by rfl) ⟨2189465, by rfl⟩ : syracuseStep 2919287 = 4378931) B4378931
theorem B3648523 : Blo 1439539 3648523 := bstep (se 1 (by rfl) ⟨2736392, by rfl⟩ : syracuseStep 3648523 = 5472785) B5472785
theorem B2051087 : Blo 1439539 2051087 := bstep (se 1 (by rfl) ⟨1538315, by rfl⟩ : syracuseStep 2051087 = 3076631) B3076631
theorem B4860971 : Blo 1439539 4860971 := bstep (se 1 (by rfl) ⟨3645728, by rfl⟩ : syracuseStep 4860971 = 7291457) B7291457
theorem B3460211 : Blo 1439539 3460211 := bstep (se 1 (by rfl) ⟨2595158, by rfl⟩ : syracuseStep 3460211 = 5190317) B5190317
theorem B3894425 : Blo 1439539 3894425 := bstep (se 2 (by rfl) ⟨1460409, by rfl⟩ : syracuseStep 3894425 = 2920819) B2920819
theorem B3648665 : Blo 1439539 3648665 := bstep (se 2 (by rfl) ⟨1368249, by rfl⟩ : syracuseStep 3648665 = 2736499) B2736499
theorem B1821943 : Blo 1439539 1821943 := bstep (se 1 (by rfl) ⟨1366457, by rfl⟩ : syracuseStep 1821943 = 2732915) B2732915
theorem B3648827 : Blo 1439539 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B2051401 : Blo 1439539 2051401 := bstep (se 2 (by rfl) ⟨769275, by rfl⟩ : syracuseStep 2051401 = 1538551) B1538551
theorem B3239315 : Blo 1439539 3239315 := bstep (se 1 (by rfl) ⟨2429486, by rfl⟩ : syracuseStep 3239315 = 4858973) B4858973
theorem B13847993 : Blo 1439539 13847993 := bstep (se 2 (by rfl) ⟨5192997, by rfl⟩ : syracuseStep 13847993 = 10385995) B10385995
theorem B3239369 : Blo 1439539 3239369 := bstep (se 2 (by rfl) ⟨1214763, by rfl⟩ : syracuseStep 3239369 = 2429527) B2429527
theorem B1822267 : Blo 1439539 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B9227843 : Blo 1439539 9227843 := bstep (se 1 (by rfl) ⟨6920882, by rfl⟩ : syracuseStep 9227843 = 13841765) B13841765
theorem B3894899 : Blo 1439539 3894899 := bstep (se 1 (by rfl) ⟨2921174, by rfl⟩ : syracuseStep 3894899 = 5842349) B5842349
theorem B10932083 : Blo 1439539 10932083 := bstep (se 1 (by rfl) ⟨8199062, by rfl⟩ : syracuseStep 10932083 = 16398125) B16398125
theorem B3460979 : Blo 1439539 3460979 := bstep (se 1 (by rfl) ⟨2595734, by rfl⟩ : syracuseStep 3460979 = 5191469) B5191469
theorem B4099987 : Blo 1439539 4099987 := bstep (se 1 (by rfl) ⟨3074990, by rfl⟩ : syracuseStep 4099987 = 6149981) B6149981
theorem B6918155 : Blo 1439539 6918155 := bstep (se 1 (by rfl) ⟨5188616, by rfl⟩ : syracuseStep 6918155 = 10377233) B10377233
theorem B4616203 : Blo 1439539 4616203 := bstep (se 1 (by rfl) ⟨3462152, by rfl⟩ : syracuseStep 4616203 = 6924305) B6924305
theorem B1822763 : Blo 1439539 1822763 := bstep (se 1 (by rfl) ⟨1367072, by rfl⟩ : syracuseStep 1822763 = 2734145) B2734145
theorem B4616279 : Blo 1439539 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B4100215 : Blo 1439539 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B3240071 : Blo 1439539 3240071 := bstep (se 1 (by rfl) ⟨2430053, by rfl⟩ : syracuseStep 3240071 = 4860107) B4860107
theorem B1847567 : Blo 1439539 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B3240251 : Blo 1439539 3240251 := bstep (se 1 (by rfl) ⟨2430188, by rfl⟩ : syracuseStep 3240251 = 4860377) B4860377
theorem B4862267 : Blo 1439539 4862267 := bstep (se 1 (by rfl) ⟨3646700, by rfl⟩ : syracuseStep 4862267 = 7293401) B7293401
theorem B4993415 : Blo 1439539 4993415 := bstep (se 1 (by rfl) ⟨3745061, by rfl⟩ : syracuseStep 4993415 = 7490123) B7490123
theorem B3240377 : Blo 1439539 3240377 := bstep (se 2 (by rfl) ⟨1215141, by rfl⟩ : syracuseStep 3240377 = 2430283) B2430283
theorem B7787011 : Blo 1439539 7787011 := bstep (se 1 (by rfl) ⟨5840258, by rfl⟩ : syracuseStep 7787011 = 11680517) B11680517
theorem B1823239 : Blo 1439539 1823239 := bstep (se 1 (by rfl) ⟨1367429, by rfl⟩ : syracuseStep 1823239 = 2734859) B2734859
theorem B2159351 : Blo 1439539 2159351 := bstep (se 1 (by rfl) ⟨1619513, by rfl⟩ : syracuseStep 2159351 = 3239027) B3239027
theorem B2159375 : Blo 1439539 2159375 := bstep (se 1 (by rfl) ⟨1619531, by rfl⟩ : syracuseStep 2159375 = 3239063) B3239063
theorem B3240719 : Blo 1439539 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B3461903 : Blo 1439539 3461903 := bstep (se 1 (by rfl) ⟨2596427, by rfl⟩ : syracuseStep 3461903 = 5192855) B5192855
theorem B21058319 : Blo 1439539 21058319 := bstep (se 1 (by rfl) ⟨15793739, by rfl⟩ : syracuseStep 21058319 = 31587479) B31587479
theorem B3240737 : Blo 1439539 3240737 := bstep (se 2 (by rfl) ⟨1215276, by rfl⟩ : syracuseStep 3240737 = 2430553) B2430553
theorem B4862753 : Blo 1439539 4862753 := bstep (se 2 (by rfl) ⟨1823532, by rfl⟩ : syracuseStep 4862753 = 3647065) B3647065
theorem B2159417 : Blo 1439539 2159417 := bstep (se 2 (by rfl) ⟨809781, by rfl⟩ : syracuseStep 2159417 = 1619563) B1619563
theorem B2159495 : Blo 1439539 2159495 := bstep (se 1 (by rfl) ⟨1619621, by rfl⟩ : syracuseStep 2159495 = 3239243) B3239243
theorem B2429831 : Blo 1439539 2429831 := bstep (se 1 (by rfl) ⟨1822373, by rfl⟩ : syracuseStep 2429831 = 3644747) B3644747
theorem B2921363 : Blo 1439539 2921363 := bstep (se 1 (by rfl) ⟨2191022, by rfl⟩ : syracuseStep 2921363 = 4382045) B4382045
theorem B2159531 : Blo 1439539 2159531 := bstep (se 1 (by rfl) ⟨1619648, by rfl⟩ : syracuseStep 2159531 = 3239297) B3239297
theorem B74830769 : Blo 1439539 74830769 := bstep (se 2 (by rfl) ⟨28061538, by rfl⟩ : syracuseStep 74830769 = 56123077) B56123077
theorem B2159561 : Blo 1439539 2159561 := bstep (se 2 (by rfl) ⟨809835, by rfl⟩ : syracuseStep 2159561 = 1619671) B1619671
theorem B8205259 : Blo 1439539 8205259 := bstep (se 1 (by rfl) ⟨6153944, by rfl⟩ : syracuseStep 8205259 = 12307889) B12307889
theorem B1823735 : Blo 1439539 1823735 := bstep (se 1 (by rfl) ⟨1367801, by rfl⟩ : syracuseStep 1823735 = 2735603) B2735603
theorem B1643527 : Blo 1439539 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B7787549 : Blo 1439539 7787549 := bstep (se 3 (by rfl) ⟨1460165, by rfl⟩ : syracuseStep 7787549 = 2920331) B2920331
theorem B2159675 : Blo 1439539 2159675 := bstep (se 1 (by rfl) ⟨1619756, by rfl⟩ : syracuseStep 2159675 = 3239513) B3239513
theorem B1946683 : Blo 1439539 1946683 := bstep (se 1 (by rfl) ⟨1460012, by rfl⟩ : syracuseStep 1946683 = 2920025) B2920025
theorem B2159735 : Blo 1439539 2159735 := bstep (se 1 (by rfl) ⟨1619801, by rfl⟩ : syracuseStep 2159735 = 3239603) B3239603
theorem B3241079 : Blo 1439539 3241079 := bstep (se 1 (by rfl) ⟨2430809, by rfl⟩ : syracuseStep 3241079 = 4861619) B4861619
theorem B2159759 : Blo 1439539 2159759 := bstep (se 1 (by rfl) ⟨1619819, by rfl⟩ : syracuseStep 2159759 = 3239639) B3239639
theorem B1823887 : Blo 1439539 1823887 := bstep (se 1 (by rfl) ⟨1367915, by rfl⟩ : syracuseStep 1823887 = 2735831) B2735831
theorem B2733203 : Blo 1439539 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B2159801 : Blo 1439539 2159801 := bstep (se 2 (by rfl) ⟨809925, by rfl⟩ : syracuseStep 2159801 = 1619851) B1619851
theorem B2733257 : Blo 1439539 2733257 := bstep (se 2 (by rfl) ⟨1024971, by rfl⟩ : syracuseStep 2733257 = 2049943) B2049943
theorem B2159879 : Blo 1439539 2159879 := bstep (se 1 (by rfl) ⟨1619909, by rfl⟩ : syracuseStep 2159879 = 3239819) B3239819
theorem B19725373 : Blo 1439539 19725373 := bstep (se 3 (by rfl) ⟨3698507, by rfl⟩ : syracuseStep 19725373 = 7397015) B7397015
theorem B2733355 : Blo 1439539 2733355 := bstep (se 1 (by rfl) ⟨2050016, by rfl⟩ : syracuseStep 2733355 = 4100033) B4100033
theorem B2159915 : Blo 1439539 2159915 := bstep (se 1 (by rfl) ⟨1619936, by rfl⟩ : syracuseStep 2159915 = 3239873) B3239873
theorem B3241259 : Blo 1439539 3241259 := bstep (se 1 (by rfl) ⟨2430944, by rfl⟩ : syracuseStep 3241259 = 4861889) B4861889
theorem B1824059 : Blo 1439539 1824059 := bstep (se 1 (by rfl) ⟨1368044, by rfl⟩ : syracuseStep 1824059 = 2736089) B2736089
theorem B2159945 : Blo 1439539 2159945 := bstep (se 2 (by rfl) ⟨809979, by rfl⟩ : syracuseStep 2159945 = 1619959) B1619959
theorem B4101491 : Blo 1439539 4101491 := bstep (se 1 (by rfl) ⟨3076118, by rfl⟩ : syracuseStep 4101491 = 6152237) B6152237
theorem B4863347 : Blo 1439539 4863347 := bstep (se 1 (by rfl) ⟨3647510, by rfl⟩ : syracuseStep 4863347 = 7295021) B7295021
theorem B7288217 : Blo 1439539 7288217 := bstep (se 2 (by rfl) ⟨2733081, by rfl⟩ : syracuseStep 7288217 = 5466163) B5466163
theorem B6919577 : Blo 1439539 6919577 := bstep (se 2 (by rfl) ⟨2594841, by rfl⟩ : syracuseStep 6919577 = 5189683) B5189683
theorem B2160059 : Blo 1439539 2160059 := bstep (se 1 (by rfl) ⟨1620044, by rfl⟩ : syracuseStep 2160059 = 3240089) B3240089
theorem B2160119 : Blo 1439539 2160119 := bstep (se 1 (by rfl) ⟨1620089, by rfl⟩ : syracuseStep 2160119 = 3240179) B3240179
theorem B2733583 : Blo 1439539 2733583 := bstep (se 1 (by rfl) ⟨2050187, by rfl⟩ : syracuseStep 2733583 = 4100375) B4100375
theorem B2160143 : Blo 1439539 2160143 := bstep (se 1 (by rfl) ⟨1620107, by rfl⟩ : syracuseStep 2160143 = 3240215) B3240215
theorem B2430479 : Blo 1439539 2430479 := bstep (se 1 (by rfl) ⟨1822859, by rfl⟩ : syracuseStep 2430479 = 3645719) B3645719
theorem B3462671 : Blo 1439539 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B2160185 : Blo 1439539 2160185 := bstep (se 2 (by rfl) ⟨810069, by rfl⟩ : syracuseStep 2160185 = 1620139) B1620139
theorem B2160263 : Blo 1439539 2160263 := bstep (se 1 (by rfl) ⟨1620197, by rfl⟩ : syracuseStep 2160263 = 3240395) B3240395
theorem B1619599 : Blo 1439539 1619599 := bstep (se 1 (by rfl) ⟨1214699, by rfl⟩ : syracuseStep 1619599 = 2429399) B2429399
theorem B3241619 : Blo 1439539 3241619 := bstep (se 1 (by rfl) ⟨2431214, by rfl⟩ : syracuseStep 3241619 = 4862429) B4862429
theorem B2160299 : Blo 1439539 2160299 := bstep (se 1 (by rfl) ⟨1620224, by rfl⟩ : syracuseStep 2160299 = 3240449) B3240449
theorem B31569587 : Blo 1439539 31569587 := bstep (se 1 (by rfl) ⟨23677190, by rfl⟩ : syracuseStep 31569587 = 47354381) B47354381
theorem B2160329 : Blo 1439539 2160329 := bstep (se 2 (by rfl) ⟨810123, by rfl⟩ : syracuseStep 2160329 = 1620247) B1620247
theorem B4101833 : Blo 1439539 4101833 := bstep (se 2 (by rfl) ⟨1538187, by rfl⟩ : syracuseStep 4101833 = 3076375) B3076375
theorem B3241673 : Blo 1439539 3241673 := bstep (se 2 (by rfl) ⟨1215627, by rfl⟩ : syracuseStep 3241673 = 2431255) B2431255
theorem B12302117 : Blo 1439539 12302117 := bstep (se 4 (by rfl) ⟨1153323, by rfl⟩ : syracuseStep 12302117 = 2306647) B2306647
theorem B1439547 : Blo 1439539 1439547 := bstep (se 1 (by rfl) ⟨1079660, by rfl⟩ : syracuseStep 1439547 = 2159321) B2159321
theorem B2160443 : Blo 1439539 2160443 := bstep (se 1 (by rfl) ⟨1620332, by rfl⟩ : syracuseStep 2160443 = 3240665) B3240665
theorem B4101947 : Blo 1439539 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B2160503 : Blo 1439539 2160503 := bstep (se 1 (by rfl) ⟨1620377, by rfl⟩ : syracuseStep 2160503 = 3240755) B3240755
theorem B1439623 : Blo 1439539 1439623 := bstep (se 1 (by rfl) ⟨1079717, by rfl⟩ : syracuseStep 1439623 = 2159435) B2159435
theorem B1439631 : Blo 1439539 1439631 := bstep (se 1 (by rfl) ⟨1079723, by rfl⟩ : syracuseStep 1439631 = 2159447) B2159447
theorem B2160527 : Blo 1439539 2160527 := bstep (se 1 (by rfl) ⟨1620395, by rfl⟩ : syracuseStep 2160527 = 3240791) B3240791
theorem B2160569 : Blo 1439539 2160569 := bstep (se 2 (by rfl) ⟨810213, by rfl⟩ : syracuseStep 2160569 = 1620427) B1620427
theorem B4102073 : Blo 1439539 4102073 := bstep (se 2 (by rfl) ⟨1538277, by rfl⟩ : syracuseStep 4102073 = 3076555) B3076555
theorem B1439675 : Blo 1439539 1439675 := bstep (se 1 (by rfl) ⟨1079756, by rfl⟩ : syracuseStep 1439675 = 2159513) B2159513
theorem B1439751 : Blo 1439539 1439751 := bstep (se 1 (by rfl) ⟨1079813, by rfl⟩ : syracuseStep 1439751 = 2159627) B2159627
theorem B2160647 : Blo 1439539 2160647 := bstep (se 1 (by rfl) ⟨1620485, by rfl⟩ : syracuseStep 2160647 = 3240971) B3240971
theorem B1439759 : Blo 1439539 1439759 := bstep (se 1 (by rfl) ⟨1079819, by rfl⟩ : syracuseStep 1439759 = 2159639) B2159639
theorem B2160683 : Blo 1439539 2160683 := bstep (se 1 (by rfl) ⟨1620512, by rfl⟩ : syracuseStep 2160683 = 3241025) B3241025
theorem B2431019 : Blo 1439539 2431019 := bstep (se 1 (by rfl) ⟨1823264, by rfl⟩ : syracuseStep 2431019 = 3646529) B3646529
theorem B1439803 : Blo 1439539 1439803 := bstep (se 1 (by rfl) ⟨1079852, by rfl⟩ : syracuseStep 1439803 = 2159705) B2159705
theorem B2160713 : Blo 1439539 2160713 := bstep (se 2 (by rfl) ⟨810267, by rfl⟩ : syracuseStep 2160713 = 1620535) B1620535
theorem B3078263 : Blo 1439539 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B1439879 : Blo 1439539 1439879 := bstep (se 1 (by rfl) ⟨1079909, by rfl⟩ : syracuseStep 1439879 = 2159819) B2159819
theorem B1620103 : Blo 1439539 1620103 := bstep (se 1 (by rfl) ⟨1215077, by rfl⟩ : syracuseStep 1620103 = 2430155) B2430155
theorem B1439887 : Blo 1439539 1439887 := bstep (se 1 (by rfl) ⟨1079915, by rfl⟩ : syracuseStep 1439887 = 2159831) B2159831
theorem B1439931 : Blo 1439539 1439931 := bstep (se 1 (by rfl) ⟨1079948, by rfl⟩ : syracuseStep 1439931 = 2159897) B2159897
theorem B2160827 : Blo 1439539 2160827 := bstep (se 1 (by rfl) ⟨1620620, by rfl⟩ : syracuseStep 2160827 = 3241241) B3241241
theorem B2160887 : Blo 1439539 2160887 := bstep (se 1 (by rfl) ⟨1620665, by rfl⟩ : syracuseStep 2160887 = 3241331) B3241331
theorem B1440007 : Blo 1439539 1440007 := bstep (se 1 (by rfl) ⟨1080005, by rfl⟩ : syracuseStep 1440007 = 2160011) B2160011
theorem B1440015 : Blo 1439539 1440015 := bstep (se 1 (by rfl) ⟨1080011, by rfl⟩ : syracuseStep 1440015 = 2160023) B2160023
theorem B2160911 : Blo 1439539 2160911 := bstep (se 1 (by rfl) ⟨1620683, by rfl⟩ : syracuseStep 2160911 = 3241367) B3241367
theorem B2595115 : Blo 1439539 2595115 := bstep (se 1 (by rfl) ⟨1946336, by rfl⟩ : syracuseStep 2595115 = 3892673) B3892673
theorem B2160953 : Blo 1439539 2160953 := bstep (se 2 (by rfl) ⟨810357, by rfl⟩ : syracuseStep 2160953 = 1620715) B1620715
theorem B1440059 : Blo 1439539 1440059 := bstep (se 1 (by rfl) ⟨1080044, by rfl⟩ : syracuseStep 1440059 = 2160089) B2160089
theorem B1620283 : Blo 1439539 1620283 := bstep (se 1 (by rfl) ⟨1215212, by rfl⟩ : syracuseStep 1620283 = 2430425) B2430425
theorem B5470523 : Blo 1439539 5470523 := bstep (se 1 (by rfl) ⟨4102892, by rfl⟩ : syracuseStep 5470523 = 8205785) B8205785
theorem B1440135 : Blo 1439539 1440135 := bstep (se 1 (by rfl) ⟨1080101, by rfl⟩ : syracuseStep 1440135 = 2160203) B2160203
theorem B2161031 : Blo 1439539 2161031 := bstep (se 1 (by rfl) ⟨1620773, by rfl⟩ : syracuseStep 2161031 = 3241547) B3241547
theorem B3242375 : Blo 1439539 3242375 := bstep (se 1 (by rfl) ⟨2431781, by rfl⟩ : syracuseStep 3242375 = 4863563) B4863563
theorem B1440143 : Blo 1439539 1440143 := bstep (se 1 (by rfl) ⟨1080107, by rfl⟩ : syracuseStep 1440143 = 2160215) B2160215
theorem B2161067 : Blo 1439539 2161067 := bstep (se 1 (by rfl) ⟨1620800, by rfl⟩ : syracuseStep 2161067 = 3241601) B3241601
theorem B2431417 : Blo 1439539 2431417 := bstep (se 2 (by rfl) ⟨911781, by rfl⟩ : syracuseStep 2431417 = 1823563) B1823563
theorem B1440187 : Blo 1439539 1440187 := bstep (se 1 (by rfl) ⟨1080140, by rfl⟩ : syracuseStep 1440187 = 2160281) B2160281
theorem B2161097 : Blo 1439539 2161097 := bstep (se 2 (by rfl) ⟨810411, by rfl⟩ : syracuseStep 2161097 = 1620823) B1620823
theorem B1440263 : Blo 1439539 1440263 := bstep (se 1 (by rfl) ⟨1080197, by rfl⟩ : syracuseStep 1440263 = 2160395) B2160395
theorem B1440271 : Blo 1439539 1440271 := bstep (se 1 (by rfl) ⟨1080203, by rfl⟩ : syracuseStep 1440271 = 2160407) B2160407
theorem B3643937 : Blo 1439539 3643937 := bstep (se 2 (by rfl) ⟨1366476, by rfl⟩ : syracuseStep 3643937 = 2732953) B2732953
theorem B1440315 : Blo 1439539 1440315 := bstep (se 1 (by rfl) ⟨1080236, by rfl⟩ : syracuseStep 1440315 = 2160473) B2160473
theorem B2161211 : Blo 1439539 2161211 := bstep (se 1 (by rfl) ⟨1620908, by rfl⟩ : syracuseStep 2161211 = 3241817) B3241817
theorem B3242555 : Blo 1439539 3242555 := bstep (se 1 (by rfl) ⟨2431916, by rfl⟩ : syracuseStep 3242555 = 4863833) B4863833
theorem B20757059 : Blo 1439539 20757059 := bstep (se 1 (by rfl) ⟨15567794, by rfl⟩ : syracuseStep 20757059 = 31135589) B31135589
theorem B2161271 : Blo 1439539 2161271 := bstep (se 1 (by rfl) ⟨1620953, by rfl⟩ : syracuseStep 2161271 = 3241907) B3241907
theorem B1440391 : Blo 1439539 1440391 := bstep (se 1 (by rfl) ⟨1080293, by rfl⟩ : syracuseStep 1440391 = 2160587) B2160587
theorem B1440399 : Blo 1439539 1440399 := bstep (se 1 (by rfl) ⟨1080299, by rfl⟩ : syracuseStep 1440399 = 2160599) B2160599
theorem B2161295 : Blo 1439539 2161295 := bstep (se 1 (by rfl) ⟨1620971, by rfl⟩ : syracuseStep 2161295 = 3241943) B3241943
theorem B2161337 : Blo 1439539 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B3242681 : Blo 1439539 3242681 := bstep (se 2 (by rfl) ⟨1216005, by rfl⟩ : syracuseStep 3242681 = 2432011) B2432011
theorem B1440443 : Blo 1439539 1440443 := bstep (se 1 (by rfl) ⟨1080332, by rfl⟩ : syracuseStep 1440443 = 2160665) B2160665
theorem B8321737 : Blo 1439539 8321737 := bstep (se 2 (by rfl) ⟨3120651, by rfl⟩ : syracuseStep 8321737 = 6241303) B6241303
theorem B1440519 : Blo 1439539 1440519 := bstep (se 1 (by rfl) ⟨1080389, by rfl⟩ : syracuseStep 1440519 = 2160779) B2160779
theorem B2161415 : Blo 1439539 2161415 := bstep (se 1 (by rfl) ⟨1621061, by rfl⟩ : syracuseStep 2161415 = 3242123) B3242123
theorem B8198927 : Blo 1439539 8198927 := bstep (se 1 (by rfl) ⟨6149195, by rfl⟩ : syracuseStep 8198927 = 12298391) B12298391
theorem B1440527 : Blo 1439539 1440527 := bstep (se 1 (by rfl) ⟨1080395, by rfl⟩ : syracuseStep 1440527 = 2160791) B2160791
theorem B1620751 : Blo 1439539 1620751 := bstep (se 1 (by rfl) ⟨1215563, by rfl⟩ : syracuseStep 1620751 = 2431127) B2431127
theorem B5471009 : Blo 1439539 5471009 := bstep (se 2 (by rfl) ⟨2051628, by rfl⟩ : syracuseStep 5471009 = 4103257) B4103257
theorem B2161451 : Blo 1439539 2161451 := bstep (se 1 (by rfl) ⟨1621088, by rfl⟩ : syracuseStep 2161451 = 3242177) B3242177
theorem B1440571 : Blo 1439539 1440571 := bstep (se 1 (by rfl) ⟨1080428, by rfl⟩ : syracuseStep 1440571 = 2160857) B2160857
theorem B2161481 : Blo 1439539 2161481 := bstep (se 2 (by rfl) ⟨810555, by rfl⟩ : syracuseStep 2161481 = 1621111) B1621111
theorem B1440647 : Blo 1439539 1440647 := bstep (se 1 (by rfl) ⟨1080485, by rfl⟩ : syracuseStep 1440647 = 2160971) B2160971
theorem B1440655 : Blo 1439539 1440655 := bstep (se 1 (by rfl) ⟨1080491, by rfl⟩ : syracuseStep 1440655 = 2160983) B2160983
theorem B1440699 : Blo 1439539 1440699 := bstep (se 1 (by rfl) ⟨1080524, by rfl⟩ : syracuseStep 1440699 = 2161049) B2161049
theorem B2161595 : Blo 1439539 2161595 := bstep (se 1 (by rfl) ⟨1621196, by rfl⟩ : syracuseStep 2161595 = 3242393) B3242393
theorem B2161655 : Blo 1439539 2161655 := bstep (se 1 (by rfl) ⟨1621241, by rfl⟩ : syracuseStep 2161655 = 3242483) B3242483
theorem B1440775 : Blo 1439539 1440775 := bstep (se 1 (by rfl) ⟨1080581, by rfl⟩ : syracuseStep 1440775 = 2161163) B2161163
theorem B1440783 : Blo 1439539 1440783 := bstep (se 1 (by rfl) ⟨1080587, by rfl⟩ : syracuseStep 1440783 = 2161175) B2161175
theorem B2161679 : Blo 1439539 2161679 := bstep (se 1 (by rfl) ⟨1621259, by rfl⟩ : syracuseStep 2161679 = 3242519) B3242519
theorem B3243023 : Blo 1439539 3243023 := bstep (se 1 (by rfl) ⟨2432267, by rfl⟩ : syracuseStep 3243023 = 4864535) B4864535
theorem B3243041 : Blo 1439539 3243041 := bstep (se 2 (by rfl) ⟨1216140, by rfl⟩ : syracuseStep 3243041 = 2432281) B2432281
theorem B6151211 : Blo 1439539 6151211 := bstep (se 1 (by rfl) ⟨4613408, by rfl⟩ : syracuseStep 6151211 = 9226817) B9226817
theorem B2735147 : Blo 1439539 2735147 := bstep (se 1 (by rfl) ⟨2051360, by rfl⟩ : syracuseStep 2735147 = 4102721) B4102721
theorem B1440827 : Blo 1439539 1440827 := bstep (se 1 (by rfl) ⟨1080620, by rfl⟩ : syracuseStep 1440827 = 2161241) B2161241
theorem B52575293 : Blo 1439539 52575293 := bstep (se 3 (by rfl) ⟨9857867, by rfl⟩ : syracuseStep 52575293 = 19715735) B19715735
theorem B2161721 : Blo 1439539 2161721 := bstep (se 2 (by rfl) ⟨810645, by rfl⟩ : syracuseStep 2161721 = 1621291) B1621291
theorem B2432119 : Blo 1439539 2432119 := bstep (se 1 (by rfl) ⟨1824089, by rfl⟩ : syracuseStep 2432119 = 3648179) B3648179
theorem B1440903 : Blo 1439539 1440903 := bstep (se 1 (by rfl) ⟨1080677, by rfl⟩ : syracuseStep 1440903 = 2161355) B2161355
theorem B2161799 : Blo 1439539 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B1440911 : Blo 1439539 1440911 := bstep (se 1 (by rfl) ⟨1080683, by rfl⟩ : syracuseStep 1440911 = 2161367) B2161367
theorem B2161835 : Blo 1439539 2161835 := bstep (se 1 (by rfl) ⟨1621376, by rfl⟩ : syracuseStep 2161835 = 3242753) B3242753
theorem B9231533 : Blo 1439539 9231533 := bstep (se 3 (by rfl) ⟨1730912, by rfl⟩ : syracuseStep 9231533 = 3461825) B3461825
theorem B1440955 : Blo 1439539 1440955 := bstep (se 1 (by rfl) ⟨1080716, by rfl⟩ : syracuseStep 1440955 = 2161433) B2161433
theorem B2161865 : Blo 1439539 2161865 := bstep (se 2 (by rfl) ⟨810699, by rfl⟩ : syracuseStep 2161865 = 1621399) B1621399
theorem B1441031 : Blo 1439539 1441031 := bstep (se 1 (by rfl) ⟨1080773, by rfl⟩ : syracuseStep 1441031 = 2161547) B2161547
theorem B1621255 : Blo 1439539 1621255 := bstep (se 1 (by rfl) ⟨1215941, by rfl⟩ : syracuseStep 1621255 = 2431883) B2431883
theorem B1441039 : Blo 1439539 1441039 := bstep (se 1 (by rfl) ⟨1080779, by rfl⟩ : syracuseStep 1441039 = 2161559) B2161559
theorem B20774177 : Blo 1439539 20774177 := bstep (se 2 (by rfl) ⟨7790316, by rfl⟩ : syracuseStep 20774177 = 15580633) B15580633
theorem B1441083 : Blo 1439539 1441083 := bstep (se 1 (by rfl) ⟨1080812, by rfl⟩ : syracuseStep 1441083 = 2161625) B2161625
theorem B8207675 : Blo 1439539 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B2161979 : Blo 1439539 2161979 := bstep (se 1 (by rfl) ⟨1621484, by rfl⟩ : syracuseStep 2161979 = 3242969) B3242969
theorem B2432315 : Blo 1439539 2432315 := bstep (se 1 (by rfl) ⟨1824236, by rfl⟩ : syracuseStep 2432315 = 3648473) B3648473
theorem B2162039 : Blo 1439539 2162039 := bstep (se 1 (by rfl) ⟨1621529, by rfl⟩ : syracuseStep 2162039 = 3243059) B3243059
theorem B3243383 : Blo 1439539 3243383 := bstep (se 1 (by rfl) ⟨2432537, by rfl⟩ : syracuseStep 3243383 = 4865075) B4865075
theorem B1441159 : Blo 1439539 1441159 := bstep (se 1 (by rfl) ⟨1080869, by rfl⟩ : syracuseStep 1441159 = 2161739) B2161739
theorem B1441167 : Blo 1439539 1441167 := bstep (se 1 (by rfl) ⟨1080875, by rfl⟩ : syracuseStep 1441167 = 2161751) B2161751
theorem B2162063 : Blo 1439539 2162063 := bstep (se 1 (by rfl) ⟨1621547, by rfl⟩ : syracuseStep 2162063 = 3243095) B3243095
theorem B2162105 : Blo 1439539 2162105 := bstep (se 2 (by rfl) ⟨810789, by rfl⟩ : syracuseStep 2162105 = 1621579) B1621579
theorem B1441211 : Blo 1439539 1441211 := bstep (se 1 (by rfl) ⟨1080908, by rfl⟩ : syracuseStep 1441211 = 2161817) B2161817
theorem B1621435 : Blo 1439539 1621435 := bstep (se 1 (by rfl) ⟨1216076, by rfl⟩ : syracuseStep 1621435 = 2432153) B2432153
theorem B1441287 : Blo 1439539 1441287 := bstep (se 1 (by rfl) ⟨1080965, by rfl⟩ : syracuseStep 1441287 = 2161931) B2161931
theorem B2162183 : Blo 1439539 2162183 := bstep (se 1 (by rfl) ⟨1621637, by rfl⟩ : syracuseStep 2162183 = 3243275) B3243275
theorem B3644939 : Blo 1439539 3644939 := bstep (se 1 (by rfl) ⟨2733704, by rfl⟩ : syracuseStep 3644939 = 5467409) B5467409
theorem B1441295 : Blo 1439539 1441295 := bstep (se 1 (by rfl) ⟨1080971, by rfl⟩ : syracuseStep 1441295 = 2161943) B2161943
theorem B4103723 : Blo 1439539 4103723 := bstep (se 1 (by rfl) ⟨3077792, by rfl⟩ : syracuseStep 4103723 = 6155585) B6155585
theorem B2162219 : Blo 1439539 2162219 := bstep (se 1 (by rfl) ⟨1621664, by rfl⟩ : syracuseStep 2162219 = 3243329) B3243329
theorem B1441339 : Blo 1439539 1441339 := bstep (se 1 (by rfl) ⟨1081004, by rfl⟩ : syracuseStep 1441339 = 2162009) B2162009
theorem B2162249 : Blo 1439539 2162249 := bstep (se 2 (by rfl) ⟨810843, by rfl⟩ : syracuseStep 2162249 = 1621687) B1621687
theorem B1441415 : Blo 1439539 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B1441423 : Blo 1439539 1441423 := bstep (se 1 (by rfl) ⟨1081067, by rfl⟩ : syracuseStep 1441423 = 2162135) B2162135
theorem B1441467 : Blo 1439539 1441467 := bstep (se 1 (by rfl) ⟨1081100, by rfl⟩ : syracuseStep 1441467 = 2162201) B2162201
theorem B16858853 : Blo 1439539 16858853 := bstep (se 4 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 16858853 = 3161035) B3161035
theorem B5471981 : Blo 1439539 5471981 := bstep (se 3 (by rfl) ⟨1025996, by rfl⟩ : syracuseStep 5471981 = 2051993) B2051993
theorem B4439819 : Blo 1439539 4439819 := bstep (se 1 (by rfl) ⟨3329864, by rfl⟩ : syracuseStep 4439819 = 6659729) B6659729
theorem B5193487 : Blo 1439539 5193487 := bstep (se 1 (by rfl) ⟨3895115, by rfl⟩ : syracuseStep 5193487 = 7790231) B7790231
theorem B44384051 : Blo 1439539 44384051 := bstep (se 1 (by rfl) ⟨33288038, by rfl⟩ : syracuseStep 44384051 = 66576077) B66576077
theorem B7790471 : Blo 1439539 7790471 := bstep (se 1 (by rfl) ⟨5842853, by rfl⟩ : syracuseStep 7790471 = 11685707) B11685707
theorem B7290809 : Blo 1439539 7290809 := bstep (se 2 (by rfl) ⟨2734053, by rfl⟩ : syracuseStep 7290809 = 5468107) B5468107
theorem B4612103 : Blo 1439539 4612103 := bstep (se 1 (by rfl) ⟨3459077, by rfl⟩ : syracuseStep 4612103 = 6918155) B6918155
theorem B63971477 : Blo 1439539 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B8208701 : Blo 1439539 8208701 := bstep (se 3 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 8208701 = 3078263) B3078263
theorem B5472755 : Blo 1439539 5472755 := bstep (se 1 (by rfl) ⟨4104566, by rfl⟩ : syracuseStep 5472755 = 8209133) B8209133
theorem B2736659 : Blo 1439539 2736659 := bstep (se 1 (by rfl) ⟨2052494, by rfl⟩ : syracuseStep 2736659 = 4104989) B4104989
theorem B9355799 : Blo 1439539 9355799 := bstep (se 1 (by rfl) ⟨7016849, by rfl⟩ : syracuseStep 9355799 = 14033699) B14033699
theorem B4612793 : Blo 1439539 4612793 := bstep (se 2 (by rfl) ⟨1729797, by rfl⟩ : syracuseStep 4612793 = 3459595) B3459595
theorem B5472953 : Blo 1439539 5472953 := bstep (se 2 (by rfl) ⟨2052357, by rfl⟩ : syracuseStep 5472953 = 4104715) B4104715
theorem B5472967 : Blo 1439539 5472967 := bstep (se 1 (by rfl) ⟨4104725, by rfl⟩ : syracuseStep 5472967 = 8209451) B8209451
theorem B12305155 : Blo 1439539 12305155 := bstep (se 1 (by rfl) ⟨9228866, by rfl⟩ : syracuseStep 12305155 = 18457733) B18457733
theorem B4858811 : Blo 1439539 4858811 := bstep (se 1 (by rfl) ⟨3644108, by rfl⟩ : syracuseStep 4858811 = 7288217) B7288217
theorem B4613051 : Blo 1439539 4613051 := bstep (se 1 (by rfl) ⟨3459788, by rfl⟩ : syracuseStep 4613051 = 6919577) B6919577
theorem B21046391 : Blo 1439539 21046391 := bstep (se 1 (by rfl) ⟨15784793, by rfl⟩ : syracuseStep 21046391 = 31569587) B31569587
theorem B8201411 : Blo 1439539 8201411 := bstep (se 1 (by rfl) ⟨6151058, by rfl⟩ : syracuseStep 8201411 = 12302117) B12302117
theorem B37414133 : Blo 1439539 37414133 := bstep (se 5 (by rfl) ⟨1753787, by rfl⟩ : syracuseStep 37414133 = 3507575) B3507575
theorem B27698597 : Blo 1439539 27698597 := bstep (se 4 (by rfl) ⟨2596743, by rfl⟩ : syracuseStep 27698597 = 5193487) B5193487
theorem B8209907 : Blo 1439539 8209907 := bstep (se 1 (by rfl) ⟨6157430, by rfl⟩ : syracuseStep 8209907 = 12314861) B12314861
theorem B15582709 : Blo 1439539 15582709 := bstep (se 5 (by rfl) ⟨730439, by rfl⟩ : syracuseStep 15582709 = 1460879) B1460879
theorem B3647015 : Blo 1439539 3647015 := bstep (se 1 (by rfl) ⟨2735261, by rfl⟩ : syracuseStep 3647015 = 5470523) B5470523
theorem B9995915 : Blo 1439539 9995915 := bstep (se 1 (by rfl) ⟨7496936, by rfl⟩ : syracuseStep 9995915 = 14993873) B14993873
theorem B35063441 : Blo 1439539 35063441 := bstep (se 2 (by rfl) ⟨13148790, by rfl⟩ : syracuseStep 35063441 = 26297581) B26297581
theorem B14419603 : Blo 1439539 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B13838039 : Blo 1439539 13838039 := bstep (se 1 (by rfl) ⟨10378529, by rfl⟩ : syracuseStep 13838039 = 20757059) B20757059
theorem B5465951 : Blo 1439539 5465951 := bstep (se 1 (by rfl) ⟨4099463, by rfl⟩ : syracuseStep 5465951 = 8198927) B8198927
theorem B3647339 : Blo 1439539 3647339 := bstep (se 1 (by rfl) ⟨2735504, by rfl⟩ : syracuseStep 3647339 = 5471009) B5471009
theorem B11839517 : Blo 1439539 11839517 := bstep (se 3 (by rfl) ⟨2219909, by rfl⟩ : syracuseStep 11839517 = 4439819) B4439819
theorem B6154355 : Blo 1439539 6154355 := bstep (se 1 (by rfl) ⟨4615766, by rfl⟩ : syracuseStep 6154355 = 9231533) B9231533
theorem B3647987 : Blo 1439539 3647987 := bstep (se 1 (by rfl) ⟨2735990, by rfl⟩ : syracuseStep 3647987 = 5471981) B5471981
theorem B5466649 : Blo 1439539 5466649 := bstep (se 2 (by rfl) ⟨2049993, by rfl⟩ : syracuseStep 5466649 = 4099987) B4099987
theorem B4860539 : Blo 1439539 4860539 := bstep (se 1 (by rfl) ⟨3645404, by rfl⟩ : syracuseStep 4860539 = 7290809) B7290809
theorem B6154937 : Blo 1439539 6154937 := bstep (se 2 (by rfl) ⟨2308101, by rfl⟩ : syracuseStep 6154937 = 4616203) B4616203
theorem B3648199 : Blo 1439539 3648199 := bstep (se 1 (by rfl) ⟨2736149, by rfl⟩ : syracuseStep 3648199 = 5472299) B5472299
theorem B4860701 : Blo 1439539 4860701 := bstep (se 3 (by rfl) ⟨911381, by rfl⟩ : syracuseStep 4860701 = 1822763) B1822763
theorem B7293725 : Blo 1439539 7293725 := bstep (se 3 (by rfl) ⟨1367573, by rfl⟩ : syracuseStep 7293725 = 2735147) B2735147
theorem B5466923 : Blo 1439539 5466923 := bstep (se 1 (by rfl) ⟨4100192, by rfl⟩ : syracuseStep 5466923 = 8200385) B8200385
theorem B5466953 : Blo 1439539 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B3328943 : Blo 1439539 3328943 := bstep (se 1 (by rfl) ⟨2496707, by rfl⟩ : syracuseStep 3328943 = 4993415) B4993415
theorem B1731547 : Blo 1439539 1731547 := bstep (se 1 (by rfl) ⟨1298660, by rfl⟩ : syracuseStep 1731547 = 2597321) B2597321
theorem B3460153 : Blo 1439539 3460153 := bstep (se 2 (by rfl) ⟨1297557, by rfl⟩ : syracuseStep 3460153 = 2595115) B2595115
theorem B3238991 : Blo 1439539 3238991 := bstep (se 1 (by rfl) ⟨2429243, by rfl⟩ : syracuseStep 3238991 = 4858487) B4858487
theorem B10382681 : Blo 1439539 10382681 := bstep (se 2 (by rfl) ⟨3893505, by rfl⟩ : syracuseStep 10382681 = 7787011) B7787011
theorem B11677043 : Blo 1439539 11677043 := bstep (se 1 (by rfl) ⟨8757782, by rfl⟩ : syracuseStep 11677043 = 17515565) B17515565
theorem B4926845 : Blo 1439539 4926845 := bstep (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) B1847567
theorem B3239387 : Blo 1439539 3239387 := bstep (se 1 (by rfl) ⟨2429540, by rfl⟩ : syracuseStep 3239387 = 4859081) B4859081
theorem B1822171 : Blo 1439539 1822171 := bstep (se 1 (by rfl) ⟨1366628, by rfl⟩ : syracuseStep 1822171 = 2733257) B2733257
theorem B4861403 : Blo 1439539 4861403 := bstep (se 1 (by rfl) ⟨3646052, by rfl⟩ : syracuseStep 4861403 = 7292105) B7292105
theorem B11095649 : Blo 1439539 11095649 := bstep (se 2 (by rfl) ⟨4160868, by rfl⟩ : syracuseStep 11095649 = 8321737) B8321737
theorem B8204075 : Blo 1439539 8204075 := bstep (se 1 (by rfl) ⟨6153056, by rfl⟩ : syracuseStep 8204075 = 12306113) B12306113
theorem B3239855 : Blo 1439539 3239855 := bstep (se 1 (by rfl) ⟨2429891, by rfl⟩ : syracuseStep 3239855 = 4859783) B4859783
theorem B10940345 : Blo 1439539 10940345 := bstep (se 2 (by rfl) ⟨4102629, by rfl⟩ : syracuseStep 10940345 = 8205259) B8205259
theorem B192556997 : Blo 1439539 192556997 := bstep (se 4 (by rfl) ⟨18052218, by rfl⟩ : syracuseStep 192556997 = 36104437) B36104437
theorem B2191369 : Blo 1439539 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B26300497 : Blo 1439539 26300497 := bstep (se 2 (by rfl) ⟨9862686, by rfl⟩ : syracuseStep 26300497 = 19725373) B19725373
theorem B4862105 : Blo 1439539 4862105 := bstep (se 2 (by rfl) ⟨1823289, by rfl⟩ : syracuseStep 4862105 = 3646579) B3646579
theorem B3240107 : Blo 1439539 3240107 := bstep (se 1 (by rfl) ⟨2430080, by rfl⟩ : syracuseStep 3240107 = 4860161) B4860161
theorem B2429257 : Blo 1439539 2429257 := bstep (se 2 (by rfl) ⟨910971, by rfl⟩ : syracuseStep 2429257 = 1821943) B1821943
theorem B2429291 : Blo 1439539 2429291 := bstep (se 1 (by rfl) ⟨1821968, by rfl⟩ : syracuseStep 2429291 = 3643937) B3643937
theorem B1946191 : Blo 1439539 1946191 := bstep (se 1 (by rfl) ⟨1459643, by rfl⟩ : syracuseStep 1946191 = 2919287) B2919287
theorem B16626293 : Blo 1439539 16626293 := bstep (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) B1558715
theorem B4100807 : Blo 1439539 4100807 := bstep (se 1 (by rfl) ⟨3075605, by rfl⟩ : syracuseStep 4100807 = 6151211) B6151211
theorem B3240647 : Blo 1439539 3240647 := bstep (se 1 (by rfl) ⟨2430485, by rfl⟩ : syracuseStep 3240647 = 4860971) B4860971
theorem B35050195 : Blo 1439539 35050195 := bstep (se 1 (by rfl) ⟨26287646, by rfl⟩ : syracuseStep 35050195 = 52575293) B52575293
theorem B2306807 : Blo 1439539 2306807 := bstep (se 1 (by rfl) ⟨1730105, by rfl⟩ : syracuseStep 2306807 = 3460211) B3460211
theorem B2429689 : Blo 1439539 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B2159465 : Blo 1439539 2159465 := bstep (se 2 (by rfl) ⟨809799, by rfl⟩ : syracuseStep 2159465 = 1619599) B1619599
theorem B13849451 : Blo 1439539 13849451 := bstep (se 1 (by rfl) ⟨10387088, by rfl⟩ : syracuseStep 13849451 = 20774177) B20774177
theorem B4928417 : Blo 1439539 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B2159543 : Blo 1439539 2159543 := bstep (se 1 (by rfl) ⟨1619657, by rfl⟩ : syracuseStep 2159543 = 3239315) B3239315
theorem B2159579 : Blo 1439539 2159579 := bstep (se 1 (by rfl) ⟨1619684, by rfl⟩ : syracuseStep 2159579 = 3239369) B3239369
theorem B9229277 : Blo 1439539 9229277 := bstep (se 3 (by rfl) ⟨1730489, by rfl⟩ : syracuseStep 9229277 = 3460979) B3460979
theorem B2429959 : Blo 1439539 2429959 := bstep (se 1 (by rfl) ⟨1822469, by rfl⟩ : syracuseStep 2429959 = 3644939) B3644939
theorem B7288055 : Blo 1439539 7288055 := bstep (se 1 (by rfl) ⟨5466041, by rfl⟩ : syracuseStep 7288055 = 10932083) B10932083
theorem B10933541 : Blo 1439539 10933541 := bstep (se 4 (by rfl) ⟨1025019, by rfl⟩ : syracuseStep 10933541 = 2050039) B2050039
theorem B4863293 : Blo 1439539 4863293 := bstep (se 3 (by rfl) ⟨911867, by rfl⟩ : syracuseStep 4863293 = 1823735) B1823735
theorem B5469565 : Blo 1439539 5469565 := bstep (se 3 (by rfl) ⟨1025543, by rfl⟩ : syracuseStep 5469565 = 2051087) B2051087
theorem B3077519 : Blo 1439539 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B2160047 : Blo 1439539 2160047 := bstep (se 1 (by rfl) ⟨1620035, by rfl⟩ : syracuseStep 2160047 = 3240071) B3240071
theorem B2430391 : Blo 1439539 2430391 := bstep (se 1 (by rfl) ⟨1822793, by rfl⟩ : syracuseStep 2430391 = 3645587) B3645587
theorem B2160137 : Blo 1439539 2160137 := bstep (se 2 (by rfl) ⟨810051, by rfl⟩ : syracuseStep 2160137 = 1620103) B1620103
theorem B2160167 : Blo 1439539 2160167 := bstep (se 1 (by rfl) ⟨1620125, by rfl⟩ : syracuseStep 2160167 = 3240251) B3240251
theorem B3241511 : Blo 1439539 3241511 := bstep (se 1 (by rfl) ⟨2431133, by rfl⟩ : syracuseStep 3241511 = 4862267) B4862267
theorem B2160251 : Blo 1439539 2160251 := bstep (se 1 (by rfl) ⟨1620188, by rfl⟩ : syracuseStep 2160251 = 3240377) B3240377
theorem B2430587 : Blo 1439539 2430587 := bstep (se 1 (by rfl) ⟨1822940, by rfl⟩ : syracuseStep 2430587 = 3645881) B3645881
theorem B7288541 : Blo 1439539 7288541 := bstep (se 3 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 7288541 = 2733203) B2733203
theorem B2160377 : Blo 1439539 2160377 := bstep (se 2 (by rfl) ⟨810141, by rfl⟩ : syracuseStep 2160377 = 1620283) B1620283
theorem B1947385 : Blo 1439539 1947385 := bstep (se 2 (by rfl) ⟨730269, by rfl⟩ : syracuseStep 1947385 = 1460539) B1460539
theorem B1439567 : Blo 1439539 1439567 := bstep (se 1 (by rfl) ⟨1079675, by rfl⟩ : syracuseStep 1439567 = 2159351) B2159351
theorem B1439583 : Blo 1439539 1439583 := bstep (se 1 (by rfl) ⟨1079687, by rfl⟩ : syracuseStep 1439583 = 2159375) B2159375
theorem B2160479 : Blo 1439539 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B2307935 : Blo 1439539 2307935 := bstep (se 1 (by rfl) ⟨1730951, by rfl⟩ : syracuseStep 2307935 = 3461903) B3461903
theorem B2160491 : Blo 1439539 2160491 := bstep (se 1 (by rfl) ⟨1620368, by rfl⟩ : syracuseStep 2160491 = 3240737) B3240737
theorem B3241835 : Blo 1439539 3241835 := bstep (se 1 (by rfl) ⟨2431376, by rfl⟩ : syracuseStep 3241835 = 4862753) B4862753
theorem B1439611 : Blo 1439539 1439611 := bstep (se 1 (by rfl) ⟨1079708, by rfl⟩ : syracuseStep 1439611 = 2159417) B2159417
theorem B3241889 : Blo 1439539 3241889 := bstep (se 2 (by rfl) ⟨1215708, by rfl⟩ : syracuseStep 3241889 = 2431417) B2431417
theorem B1439663 : Blo 1439539 1439663 := bstep (se 1 (by rfl) ⟨1079747, by rfl⟩ : syracuseStep 1439663 = 2159495) B2159495
theorem B1619887 : Blo 1439539 1619887 := bstep (se 1 (by rfl) ⟨1214915, by rfl⟩ : syracuseStep 1619887 = 2429831) B2429831
theorem B4216751 : Blo 1439539 4216751 := bstep (se 1 (by rfl) ⟨3162563, by rfl⟩ : syracuseStep 4216751 = 6325127) B6325127
theorem B1947575 : Blo 1439539 1947575 := bstep (se 1 (by rfl) ⟨1460681, by rfl⟩ : syracuseStep 1947575 = 2921363) B2921363
theorem B8763329 : Blo 1439539 8763329 := bstep (se 2 (by rfl) ⟨3286248, by rfl⟩ : syracuseStep 8763329 = 6572497) B6572497
theorem B1439687 : Blo 1439539 1439687 := bstep (se 1 (by rfl) ⟨1079765, by rfl⟩ : syracuseStep 1439687 = 2159531) B2159531
theorem B49887179 : Blo 1439539 49887179 := bstep (se 1 (by rfl) ⟨37415384, by rfl⟩ : syracuseStep 49887179 = 74830769) B74830769
theorem B1439707 : Blo 1439539 1439707 := bstep (se 1 (by rfl) ⟨1079780, by rfl⟩ : syracuseStep 1439707 = 2159561) B2159561
theorem B11081735 : Blo 1439539 11081735 := bstep (se 1 (by rfl) ⟨8311301, by rfl⟩ : syracuseStep 11081735 = 16622603) B16622603
theorem B2430985 : Blo 1439539 2430985 := bstep (se 2 (by rfl) ⟨911619, by rfl⟩ : syracuseStep 2430985 = 1823239) B1823239
theorem B5191699 : Blo 1439539 5191699 := bstep (se 1 (by rfl) ⟨3893774, by rfl⟩ : syracuseStep 5191699 = 7787549) B7787549
theorem B1439783 : Blo 1439539 1439783 := bstep (se 1 (by rfl) ⟨1079837, by rfl⟩ : syracuseStep 1439783 = 2159675) B2159675
theorem B1439823 : Blo 1439539 1439823 := bstep (se 1 (by rfl) ⟨1079867, by rfl⟩ : syracuseStep 1439823 = 2159735) B2159735
theorem B2160719 : Blo 1439539 2160719 := bstep (se 1 (by rfl) ⟨1620539, by rfl⟩ : syracuseStep 2160719 = 3241079) B3241079
theorem B1439839 : Blo 1439539 1439839 := bstep (se 1 (by rfl) ⟨1079879, by rfl⟩ : syracuseStep 1439839 = 2159759) B2159759
theorem B5920883 : Blo 1439539 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B1439867 : Blo 1439539 1439867 := bstep (se 1 (by rfl) ⟨1079900, by rfl⟩ : syracuseStep 1439867 = 2159801) B2159801
theorem B4864157 : Blo 1439539 4864157 := bstep (se 3 (by rfl) ⟨912029, by rfl⟩ : syracuseStep 4864157 = 1824059) B1824059
theorem B2431147 : Blo 1439539 2431147 := bstep (se 1 (by rfl) ⟨1823360, by rfl⟩ : syracuseStep 2431147 = 3646721) B3646721
theorem B1439919 : Blo 1439539 1439919 := bstep (se 1 (by rfl) ⟨1079939, by rfl⟩ : syracuseStep 1439919 = 2159879) B2159879
theorem B1439943 : Blo 1439539 1439943 := bstep (se 1 (by rfl) ⟨1079957, by rfl⟩ : syracuseStep 1439943 = 2159915) B2159915
theorem B2160839 : Blo 1439539 2160839 := bstep (se 1 (by rfl) ⟨1620629, by rfl⟩ : syracuseStep 2160839 = 3241259) B3241259
theorem B1439963 : Blo 1439539 1439963 := bstep (se 1 (by rfl) ⟨1079972, by rfl⟩ : syracuseStep 1439963 = 2159945) B2159945
theorem B4675831 : Blo 1439539 4675831 := bstep (se 1 (by rfl) ⟨3506873, by rfl⟩ : syracuseStep 4675831 = 7013747) B7013747
theorem B2734327 : Blo 1439539 2734327 := bstep (se 1 (by rfl) ⟨2050745, by rfl⟩ : syracuseStep 2734327 = 4101491) B4101491
theorem B3242231 : Blo 1439539 3242231 := bstep (se 1 (by rfl) ⟨2431673, by rfl⟩ : syracuseStep 3242231 = 4863347) B4863347
theorem B1440039 : Blo 1439539 1440039 := bstep (se 1 (by rfl) ⟨1080029, by rfl⟩ : syracuseStep 1440039 = 2160059) B2160059
theorem B1440079 : Blo 1439539 1440079 := bstep (se 1 (by rfl) ⟨1080059, by rfl⟩ : syracuseStep 1440079 = 2160119) B2160119
theorem B1440095 : Blo 1439539 1440095 := bstep (se 1 (by rfl) ⟨1080071, by rfl⟩ : syracuseStep 1440095 = 2160143) B2160143
theorem B1620319 : Blo 1439539 1620319 := bstep (se 1 (by rfl) ⟨1215239, by rfl⟩ : syracuseStep 1620319 = 2430479) B2430479
theorem B2308447 : Blo 1439539 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B2161001 : Blo 1439539 2161001 := bstep (se 2 (by rfl) ⟨810375, by rfl⟩ : syracuseStep 2161001 = 1620751) B1620751
theorem B1440123 : Blo 1439539 1440123 := bstep (se 1 (by rfl) ⟨1080092, by rfl⟩ : syracuseStep 1440123 = 2160185) B2160185
theorem B1440175 : Blo 1439539 1440175 := bstep (se 1 (by rfl) ⟨1080131, by rfl⟩ : syracuseStep 1440175 = 2160263) B2160263
theorem B2161079 : Blo 1439539 2161079 := bstep (se 1 (by rfl) ⟨1620809, by rfl⟩ : syracuseStep 2161079 = 3241619) B3241619
theorem B1440199 : Blo 1439539 1440199 := bstep (se 1 (by rfl) ⟨1080149, by rfl⟩ : syracuseStep 1440199 = 2160299) B2160299
theorem B1440219 : Blo 1439539 1440219 := bstep (se 1 (by rfl) ⟨1080164, by rfl⟩ : syracuseStep 1440219 = 2160329) B2160329
theorem B2734555 : Blo 1439539 2734555 := bstep (se 1 (by rfl) ⟨2050916, by rfl⟩ : syracuseStep 2734555 = 4101833) B4101833
theorem B2161115 : Blo 1439539 2161115 := bstep (se 1 (by rfl) ⟨1620836, by rfl⟩ : syracuseStep 2161115 = 3241673) B3241673
theorem B2431451 : Blo 1439539 2431451 := bstep (se 1 (by rfl) ⟨1823588, by rfl⟩ : syracuseStep 2431451 = 3647177) B3647177
theorem B11082221 : Blo 1439539 11082221 := bstep (se 3 (by rfl) ⟨2077916, by rfl⟩ : syracuseStep 11082221 = 4155833) B4155833
theorem B1440295 : Blo 1439539 1440295 := bstep (se 1 (by rfl) ⟨1080221, by rfl⟩ : syracuseStep 1440295 = 2160443) B2160443
theorem B2734631 : Blo 1439539 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B1440335 : Blo 1439539 1440335 := bstep (se 1 (by rfl) ⟨1080251, by rfl⟩ : syracuseStep 1440335 = 2160503) B2160503
theorem B1440351 : Blo 1439539 1440351 := bstep (se 1 (by rfl) ⟨1080263, by rfl⟩ : syracuseStep 1440351 = 2160527) B2160527
theorem B1440379 : Blo 1439539 1440379 := bstep (se 1 (by rfl) ⟨1080284, by rfl⟩ : syracuseStep 1440379 = 2160569) B2160569
theorem B2734715 : Blo 1439539 2734715 := bstep (se 1 (by rfl) ⟨2051036, by rfl⟩ : syracuseStep 2734715 = 4102073) B4102073
theorem B1440431 : Blo 1439539 1440431 := bstep (se 1 (by rfl) ⟨1080323, by rfl⟩ : syracuseStep 1440431 = 2160647) B2160647
theorem B4864697 : Blo 1439539 4864697 := bstep (se 2 (by rfl) ⟨1824261, by rfl⟩ : syracuseStep 4864697 = 3648523) B3648523
theorem B1440455 : Blo 1439539 1440455 := bstep (se 1 (by rfl) ⟨1080341, by rfl⟩ : syracuseStep 1440455 = 2160683) B2160683
theorem B1620679 : Blo 1439539 1620679 := bstep (se 1 (by rfl) ⟨1215509, by rfl⟩ : syracuseStep 1620679 = 2431019) B2431019
theorem B2431687 : Blo 1439539 2431687 := bstep (se 1 (by rfl) ⟨1823765, by rfl⟩ : syracuseStep 2431687 = 3647531) B3647531
theorem B1440475 : Blo 1439539 1440475 := bstep (se 1 (by rfl) ⟨1080356, by rfl⟩ : syracuseStep 1440475 = 2160713) B2160713
theorem B2595577 : Blo 1439539 2595577 := bstep (se 2 (by rfl) ⟨973341, by rfl⟩ : syracuseStep 2595577 = 1946683) B1946683
theorem B10943261 : Blo 1439539 10943261 := bstep (se 3 (by rfl) ⟨2051861, by rfl⟩ : syracuseStep 10943261 = 4103723) B4103723
theorem B1440551 : Blo 1439539 1440551 := bstep (se 1 (by rfl) ⟨1080413, by rfl⟩ : syracuseStep 1440551 = 2160827) B2160827
theorem B3242825 : Blo 1439539 3242825 := bstep (se 2 (by rfl) ⟨1216059, by rfl⟩ : syracuseStep 3242825 = 2432119) B2432119
theorem B1440591 : Blo 1439539 1440591 := bstep (se 1 (by rfl) ⟨1080443, by rfl⟩ : syracuseStep 1440591 = 2160887) B2160887
theorem B1440607 : Blo 1439539 1440607 := bstep (se 1 (by rfl) ⟨1080455, by rfl⟩ : syracuseStep 1440607 = 2160911) B2160911
theorem B2431849 : Blo 1439539 2431849 := bstep (se 2 (by rfl) ⟨911943, by rfl⟩ : syracuseStep 2431849 = 1823887) B1823887
theorem B1440635 : Blo 1439539 1440635 := bstep (se 1 (by rfl) ⟨1080476, by rfl⟩ : syracuseStep 1440635 = 2160953) B2160953
theorem B1440687 : Blo 1439539 1440687 := bstep (se 1 (by rfl) ⟨1080515, by rfl⟩ : syracuseStep 1440687 = 2161031) B2161031
theorem B2161583 : Blo 1439539 2161583 := bstep (se 1 (by rfl) ⟨1621187, by rfl⟩ : syracuseStep 2161583 = 3242375) B3242375
theorem B1440711 : Blo 1439539 1440711 := bstep (se 1 (by rfl) ⟨1080533, by rfl⟩ : syracuseStep 1440711 = 2161067) B2161067
theorem B1440731 : Blo 1439539 1440731 := bstep (se 1 (by rfl) ⟨1080548, by rfl⟩ : syracuseStep 1440731 = 2161097) B2161097
theorem B10386397 : Blo 1439539 10386397 := bstep (se 3 (by rfl) ⟨1947449, by rfl⟩ : syracuseStep 10386397 = 3894899) B3894899
theorem B3644423 : Blo 1439539 3644423 := bstep (se 1 (by rfl) ⟨2733317, by rfl⟩ : syracuseStep 3644423 = 5466635) B5466635
theorem B2161673 : Blo 1439539 2161673 := bstep (se 2 (by rfl) ⟨810627, by rfl⟩ : syracuseStep 2161673 = 1621255) B1621255
theorem B1440807 : Blo 1439539 1440807 := bstep (se 1 (by rfl) ⟨1080605, by rfl⟩ : syracuseStep 1440807 = 2161211) B2161211
theorem B2161703 : Blo 1439539 2161703 := bstep (se 1 (by rfl) ⟨1621277, by rfl⟩ : syracuseStep 2161703 = 3242555) B3242555
theorem B3644473 : Blo 1439539 3644473 := bstep (se 2 (by rfl) ⟨1366677, by rfl⟩ : syracuseStep 3644473 = 2733355) B2733355
theorem B6151247 : Blo 1439539 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B1440847 : Blo 1439539 1440847 := bstep (se 1 (by rfl) ⟨1080635, by rfl⟩ : syracuseStep 1440847 = 2161271) B2161271
theorem B1440863 : Blo 1439539 1440863 := bstep (se 1 (by rfl) ⟨1080647, by rfl⟩ : syracuseStep 1440863 = 2161295) B2161295
theorem B2735201 : Blo 1439539 2735201 := bstep (se 2 (by rfl) ⟨1025700, by rfl⟩ : syracuseStep 2735201 = 2051401) B2051401
theorem B1440891 : Blo 1439539 1440891 := bstep (se 1 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 1440891 = 2161337) B2161337
theorem B2161787 : Blo 1439539 2161787 := bstep (se 1 (by rfl) ⟨1621340, by rfl⟩ : syracuseStep 2161787 = 3242681) B3242681
theorem B1440943 : Blo 1439539 1440943 := bstep (se 1 (by rfl) ⟨1080707, by rfl⟩ : syracuseStep 1440943 = 2161415) B2161415
theorem B1440967 : Blo 1439539 1440967 := bstep (se 1 (by rfl) ⟨1080725, by rfl⟩ : syracuseStep 1440967 = 2161451) B2161451
theorem B1440987 : Blo 1439539 1440987 := bstep (se 1 (by rfl) ⟨1080740, by rfl⟩ : syracuseStep 1440987 = 2161481) B2161481
theorem B2161913 : Blo 1439539 2161913 := bstep (se 2 (by rfl) ⟨810717, by rfl⟩ : syracuseStep 2161913 = 1621435) B1621435
theorem B1441063 : Blo 1439539 1441063 := bstep (se 1 (by rfl) ⟨1080797, by rfl⟩ : syracuseStep 1441063 = 2161595) B2161595
theorem B1441103 : Blo 1439539 1441103 := bstep (se 1 (by rfl) ⟨1080827, by rfl⟩ : syracuseStep 1441103 = 2161655) B2161655
theorem B1441119 : Blo 1439539 1441119 := bstep (se 1 (by rfl) ⟨1080839, by rfl⟩ : syracuseStep 1441119 = 2161679) B2161679
theorem B2162015 : Blo 1439539 2162015 := bstep (se 1 (by rfl) ⟨1621511, by rfl⟩ : syracuseStep 2162015 = 3243023) B3243023
theorem B3644777 : Blo 1439539 3644777 := bstep (se 2 (by rfl) ⟨1366791, by rfl⟩ : syracuseStep 3644777 = 2733583) B2733583
theorem B2162027 : Blo 1439539 2162027 := bstep (se 1 (by rfl) ⟨1621520, by rfl⟩ : syracuseStep 2162027 = 3243041) B3243041
theorem B56155517 : Blo 1439539 56155517 := bstep (se 3 (by rfl) ⟨10529159, by rfl⟩ : syracuseStep 56155517 = 21058319) B21058319
theorem B1441147 : Blo 1439539 1441147 := bstep (se 1 (by rfl) ⟨1080860, by rfl⟩ : syracuseStep 1441147 = 2161721) B2161721
theorem B1441199 : Blo 1439539 1441199 := bstep (se 1 (by rfl) ⟨1080899, by rfl⟩ : syracuseStep 1441199 = 2161799) B2161799
theorem B2596283 : Blo 1439539 2596283 := bstep (se 1 (by rfl) ⟨1947212, by rfl⟩ : syracuseStep 2596283 = 3894425) B3894425
theorem B2432443 : Blo 1439539 2432443 := bstep (se 1 (by rfl) ⟨1824332, by rfl⟩ : syracuseStep 2432443 = 3648665) B3648665
theorem B1441223 : Blo 1439539 1441223 := bstep (se 1 (by rfl) ⟨1080917, by rfl⟩ : syracuseStep 1441223 = 2161835) B2161835
theorem B1441243 : Blo 1439539 1441243 := bstep (se 1 (by rfl) ⟨1080932, by rfl⟩ : syracuseStep 1441243 = 2161865) B2161865
theorem B118357469 : Blo 1439539 118357469 := bstep (se 3 (by rfl) ⟨22192025, by rfl⟩ : syracuseStep 118357469 = 44384051) B44384051
theorem B5471783 : Blo 1439539 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B1441319 : Blo 1439539 1441319 := bstep (se 1 (by rfl) ⟨1080989, by rfl⟩ : syracuseStep 1441319 = 2161979) B2161979
theorem B1621543 : Blo 1439539 1621543 := bstep (se 1 (by rfl) ⟨1216157, by rfl⟩ : syracuseStep 1621543 = 2432315) B2432315
theorem B2432551 : Blo 1439539 2432551 := bstep (se 1 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 2432551 = 3648827) B3648827
theorem B1441359 : Blo 1439539 1441359 := bstep (se 1 (by rfl) ⟨1081019, by rfl⟩ : syracuseStep 1441359 = 2162039) B2162039
theorem B2162255 : Blo 1439539 2162255 := bstep (se 1 (by rfl) ⟨1621691, by rfl⟩ : syracuseStep 2162255 = 3243383) B3243383
theorem B1441375 : Blo 1439539 1441375 := bstep (se 1 (by rfl) ⟨1081031, by rfl⟩ : syracuseStep 1441375 = 2162063) B2162063
theorem B9231995 : Blo 1439539 9231995 := bstep (se 1 (by rfl) ⟨6923996, by rfl⟩ : syracuseStep 9231995 = 13847993) B13847993
theorem B1441403 : Blo 1439539 1441403 := bstep (se 1 (by rfl) ⟨1081052, by rfl⟩ : syracuseStep 1441403 = 2162105) B2162105
theorem B1441455 : Blo 1439539 1441455 := bstep (se 1 (by rfl) ⟨1081091, by rfl⟩ : syracuseStep 1441455 = 2162183) B2162183
theorem B1441479 : Blo 1439539 1441479 := bstep (se 1 (by rfl) ⟨1081109, by rfl⟩ : syracuseStep 1441479 = 2162219) B2162219
theorem B6151895 : Blo 1439539 6151895 := bstep (se 1 (by rfl) ⟨4613921, by rfl⟩ : syracuseStep 6151895 = 9227843) B9227843
theorem B1441499 : Blo 1439539 1441499 := bstep (se 1 (by rfl) ⟨1081124, by rfl⟩ : syracuseStep 1441499 = 2162249) B2162249
theorem B11239235 : Blo 1439539 11239235 := bstep (se 1 (by rfl) ⟨8429426, by rfl⟩ : syracuseStep 11239235 = 16858853) B16858853
theorem B5193647 : Blo 1439539 5193647 := bstep (se 1 (by rfl) ⟨3895235, by rfl⟩ : syracuseStep 5193647 = 7790471) B7790471
theorem B6922265 : Blo 1439539 6922265 := bstep (se 2 (by rfl) ⟨2595849, by rfl⟩ : syracuseStep 6922265 = 5191699) B5191699
theorem B42647651 : Blo 1439539 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B5472467 : Blo 1439539 5472467 := bstep (se 1 (by rfl) ⟨4104350, by rfl⟩ : syracuseStep 5472467 = 8208701) B8208701
theorem B3645769 : Blo 1439539 3645769 := bstep (se 2 (by rfl) ⟨1367163, by rfl⟩ : syracuseStep 3645769 = 2734327) B2734327
theorem B11084195 : Blo 1439539 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B9232967 : Blo 1439539 9232967 := bstep (se 1 (by rfl) ⟨6924725, by rfl⟩ : syracuseStep 9232967 = 13849451) B13849451
theorem B3285611 : Blo 1439539 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B3646073 : Blo 1439539 3646073 := bstep (se 2 (by rfl) ⟨1367277, by rfl⟩ : syracuseStep 3646073 = 2734555) B2734555
theorem B6152851 : Blo 1439539 6152851 := bstep (se 1 (by rfl) ⟨4614638, by rfl⟩ : syracuseStep 6152851 = 9229277) B9229277
theorem B4858703 : Blo 1439539 4858703 := bstep (se 1 (by rfl) ⟨3644027, by rfl⟩ : syracuseStep 4858703 = 7288055) B7288055
theorem B18465731 : Blo 1439539 18465731 := bstep (se 1 (by rfl) ⟨13849298, by rfl⟩ : syracuseStep 18465731 = 27698597) B27698597
theorem B5473271 : Blo 1439539 5473271 := bstep (se 1 (by rfl) ⟨4104953, by rfl⟩ : syracuseStep 5473271 = 8209907) B8209907
theorem B9225359 : Blo 1439539 9225359 := bstep (se 1 (by rfl) ⟨6919019, by rfl⟩ : syracuseStep 9225359 = 13838039) B13838039
theorem B4859027 : Blo 1439539 4859027 := bstep (se 1 (by rfl) ⟨3644270, by rfl⟩ : syracuseStep 4859027 = 7288541) B7288541
theorem B2811167 : Blo 1439539 2811167 := bstep (se 1 (by rfl) ⟨2108375, by rfl⟩ : syracuseStep 2811167 = 4216751) B4216751
theorem B5842219 : Blo 1439539 5842219 := bstep (se 1 (by rfl) ⟨4381664, by rfl⟩ : syracuseStep 5842219 = 8763329) B8763329
theorem B4859297 : Blo 1439539 4859297 := bstep (se 2 (by rfl) ⟨1822236, by rfl⟩ : syracuseStep 4859297 = 3644473) B3644473
theorem B4613537 : Blo 1439539 4613537 := bstep (se 2 (by rfl) ⟨1730076, by rfl⟩ : syracuseStep 4613537 = 3460153) B3460153
theorem B7292753 : Blo 1439539 7292753 := bstep (se 2 (by rfl) ⟨2734782, by rfl⟩ : syracuseStep 7292753 = 5469565) B5469565
theorem B20776945 : Blo 1439539 20776945 := bstep (se 2 (by rfl) ⟨7791354, by rfl⟩ : syracuseStep 20776945 = 15582709) B15582709
theorem B7784695 : Blo 1439539 7784695 := bstep (se 1 (by rfl) ⟨5838521, by rfl⟩ : syracuseStep 7784695 = 11677043) B11677043
theorem B1730855 : Blo 1439539 1730855 := bstep (se 1 (by rfl) ⟨1298141, by rfl⟩ : syracuseStep 1730855 = 2596283) B2596283
theorem B3647855 : Blo 1439539 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B6154663 : Blo 1439539 6154663 := bstep (se 1 (by rfl) ⟨4615997, by rfl⟩ : syracuseStep 6154663 = 9231995) B9231995
theorem B9234917 : Blo 1439539 9234917 := bstep (se 4 (by rfl) ⟨865773, by rfl⟩ : syracuseStep 9234917 = 1731547) B1731547
theorem B7293563 : Blo 1439539 7293563 := bstep (se 1 (by rfl) ⟨5470172, by rfl⟩ : syracuseStep 7293563 = 10940345) B10940345
theorem B128371331 : Blo 1439539 128371331 := bstep (se 1 (by rfl) ⟨96278498, by rfl⟩ : syracuseStep 128371331 = 192556997) B192556997
theorem B3074735 : Blo 1439539 3074735 := bstep (se 1 (by rfl) ⟨2306051, by rfl⟩ : syracuseStep 3074735 = 4612103) B4612103
theorem B3648503 : Blo 1439539 3648503 := bstep (se 1 (by rfl) ⟨2736377, by rfl⟩ : syracuseStep 3648503 = 5472755) B5472755
theorem B6237199 : Blo 1439539 6237199 := bstep (se 1 (by rfl) ⟨4677899, by rfl⟩ : syracuseStep 6237199 = 9355799) B9355799
theorem B3239009 : Blo 1439539 3239009 := bstep (se 2 (by rfl) ⟨1214628, by rfl⟩ : syracuseStep 3239009 = 2429257) B2429257
theorem B3648635 : Blo 1439539 3648635 := bstep (se 1 (by rfl) ⟨2736476, by rfl⟩ : syracuseStep 3648635 = 5472953) B5472953
theorem B3239207 : Blo 1439539 3239207 := bstep (se 1 (by rfl) ⟨2429405, by rfl⟩ : syracuseStep 3239207 = 4858811) B4858811
theorem B3075367 : Blo 1439539 3075367 := bstep (se 1 (by rfl) ⟨2306525, by rfl⟩ : syracuseStep 3075367 = 4613051) B4613051
theorem B5467607 : Blo 1439539 5467607 := bstep (se 1 (by rfl) ⟨4100705, by rfl⟩ : syracuseStep 5467607 = 8201411) B8201411
theorem B3239585 : Blo 1439539 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B3460769 : Blo 1439539 3460769 := bstep (se 2 (by rfl) ⟨1297788, by rfl⟩ : syracuseStep 3460769 = 2595577) B2595577
theorem B6663943 : Blo 1439539 6663943 := bstep (se 1 (by rfl) ⟨4997957, by rfl⟩ : syracuseStep 6663943 = 9995915) B9995915
theorem B23375627 : Blo 1439539 23375627 := bstep (se 1 (by rfl) ⟨17531720, by rfl⟩ : syracuseStep 23375627 = 35063441) B35063441
theorem B13848529 : Blo 1439539 13848529 := bstep (se 2 (by rfl) ⟨5193198, by rfl⟩ : syracuseStep 13848529 = 10386397) B10386397
theorem B3239945 : Blo 1439539 3239945 := bstep (se 2 (by rfl) ⟨1214979, by rfl⟩ : syracuseStep 3239945 = 2429959) B2429959
theorem B7893011 : Blo 1439539 7893011 := bstep (se 1 (by rfl) ⟨5919758, by rfl⟩ : syracuseStep 7893011 = 11839517) B11839517
theorem B1823087 : Blo 1439539 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B3240359 : Blo 1439539 3240359 := bstep (se 1 (by rfl) ⟨2430269, by rfl⟩ : syracuseStep 3240359 = 4860539) B4860539
theorem B1823143 : Blo 1439539 1823143 := bstep (se 1 (by rfl) ⟨1367357, by rfl⟩ : syracuseStep 1823143 = 2734715) B2734715
theorem B12300781 : Blo 1439539 12300781 := bstep (se 3 (by rfl) ⟨2306396, by rfl⟩ : syracuseStep 12300781 = 4612793) B4612793
theorem B35508725 : Blo 1439539 35508725 := bstep (se 5 (by rfl) ⟨1664471, by rfl⟩ : syracuseStep 35508725 = 3328943) B3328943
theorem B3240467 : Blo 1439539 3240467 := bstep (se 1 (by rfl) ⟨2430350, by rfl⟩ : syracuseStep 3240467 = 4860701) B4860701
theorem B4862483 : Blo 1439539 4862483 := bstep (se 1 (by rfl) ⟨3646862, by rfl⟩ : syracuseStep 4862483 = 7293725) B7293725
theorem B7295507 : Blo 1439539 7295507 := bstep (se 1 (by rfl) ⟨5471630, by rfl⟩ : syracuseStep 7295507 = 10943261) B10943261
theorem B3240521 : Blo 1439539 3240521 := bstep (se 2 (by rfl) ⟨1215195, by rfl⟩ : syracuseStep 3240521 = 2430391) B2430391
theorem B2429561 : Blo 1439539 2429561 := bstep (se 2 (by rfl) ⟨911085, by rfl⟩ : syracuseStep 2429561 = 1822171) B1822171
theorem B2429615 : Blo 1439539 2429615 := bstep (se 1 (by rfl) ⟨1822211, by rfl⟩ : syracuseStep 2429615 = 3644423) B3644423
theorem B2159327 : Blo 1439539 2159327 := bstep (se 1 (by rfl) ⟨1619495, by rfl⟩ : syracuseStep 2159327 = 3238991) B3238991
theorem B4100831 : Blo 1439539 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B1823467 : Blo 1439539 1823467 := bstep (se 1 (by rfl) ⟨1367600, by rfl⟩ : syracuseStep 1823467 = 2735201) B2735201
theorem B2429851 : Blo 1439539 2429851 := bstep (se 1 (by rfl) ⟨1822388, by rfl⟩ : syracuseStep 2429851 = 3644777) B3644777
theorem B2159591 : Blo 1439539 2159591 := bstep (se 1 (by rfl) ⟨1619693, by rfl⟩ : syracuseStep 2159591 = 3239387) B3239387
theorem B3240935 : Blo 1439539 3240935 := bstep (se 1 (by rfl) ⟨2430701, by rfl⟩ : syracuseStep 3240935 = 4861403) B4861403
theorem B4101263 : Blo 1439539 4101263 := bstep (se 1 (by rfl) ⟨3075947, by rfl⟩ : syracuseStep 4101263 = 6151895) B6151895
theorem B99751061 : Blo 1439539 99751061 := bstep (se 6 (by rfl) ⟨2337915, by rfl⟩ : syracuseStep 99751061 = 4675831) B4675831
theorem B5469383 : Blo 1439539 5469383 := bstep (se 1 (by rfl) ⟨4102037, by rfl⟩ : syracuseStep 5469383 = 8204075) B8204075
theorem B7492823 : Blo 1439539 7492823 := bstep (se 1 (by rfl) ⟨5619617, by rfl⟩ : syracuseStep 7492823 = 11239235) B11239235
theorem B2159849 : Blo 1439539 2159849 := bstep (se 2 (by rfl) ⟨809943, by rfl⟩ : syracuseStep 2159849 = 1619887) B1619887
theorem B2159903 : Blo 1439539 2159903 := bstep (se 1 (by rfl) ⟨1619927, by rfl⟩ : syracuseStep 2159903 = 3239855) B3239855
theorem B3462431 : Blo 1439539 3462431 := bstep (se 1 (by rfl) ⟨2596823, by rfl⟩ : syracuseStep 3462431 = 5193647) B5193647
theorem B3241313 : Blo 1439539 3241313 := bstep (se 2 (by rfl) ⟨1215492, by rfl⟩ : syracuseStep 3241313 = 2430985) B2430985
theorem B2921825 : Blo 1439539 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B3241403 : Blo 1439539 3241403 := bstep (se 1 (by rfl) ⟨2431052, by rfl⟩ : syracuseStep 3241403 = 4862105) B4862105
theorem B35067329 : Blo 1439539 35067329 := bstep (se 2 (by rfl) ⟨13150248, by rfl⟩ : syracuseStep 35067329 = 26300497) B26300497
theorem B2160071 : Blo 1439539 2160071 := bstep (se 1 (by rfl) ⟨1620053, by rfl⟩ : syracuseStep 2160071 = 3240107) B3240107
theorem B3241529 : Blo 1439539 3241529 := bstep (se 2 (by rfl) ⟨1215573, by rfl⟩ : syracuseStep 3241529 = 2431147) B2431147
theorem B1619527 : Blo 1439539 1619527 := bstep (se 1 (by rfl) ⟨1214645, by rfl⟩ : syracuseStep 1619527 = 2429291) B2429291
theorem B1824439 : Blo 1439539 1824439 := bstep (se 1 (by rfl) ⟨1368329, by rfl⟩ : syracuseStep 1824439 = 2736659) B2736659
theorem B2160425 : Blo 1439539 2160425 := bstep (se 2 (by rfl) ⟨810159, by rfl⟩ : syracuseStep 2160425 = 1620319) B1620319
theorem B3077929 : Blo 1439539 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B2160431 : Blo 1439539 2160431 := bstep (se 1 (by rfl) ⟨1620323, by rfl⟩ : syracuseStep 2160431 = 3240647) B3240647
theorem B1537871 : Blo 1439539 1537871 := bstep (se 1 (by rfl) ⟨1153403, by rfl⟩ : syracuseStep 1537871 = 2306807) B2306807
theorem B1439643 : Blo 1439539 1439643 := bstep (se 1 (by rfl) ⟨1079732, by rfl⟩ : syracuseStep 1439643 = 2159465) B2159465
theorem B1439695 : Blo 1439539 1439695 := bstep (se 1 (by rfl) ⟨1079771, by rfl⟩ : syracuseStep 1439695 = 2159543) B2159543
theorem B1439719 : Blo 1439539 1439719 := bstep (se 1 (by rfl) ⟨1079789, by rfl⟩ : syracuseStep 1439719 = 2159579) B2159579
theorem B7288865 : Blo 1439539 7288865 := bstep (se 2 (by rfl) ⟨2733324, by rfl⟩ : syracuseStep 7288865 = 5466649) B5466649
theorem B14030927 : Blo 1439539 14030927 := bstep (se 1 (by rfl) ⟨10523195, by rfl⟩ : syracuseStep 14030927 = 21046391) B21046391
theorem B76904549 : Blo 1439539 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B2594921 : Blo 1439539 2594921 := bstep (se 2 (by rfl) ⟨973095, by rfl⟩ : syracuseStep 2594921 = 1946191) B1946191
theorem B24942755 : Blo 1439539 24942755 := bstep (se 1 (by rfl) ⟨18707066, by rfl⟩ : syracuseStep 24942755 = 37414133) B37414133
theorem B7289027 : Blo 1439539 7289027 := bstep (se 1 (by rfl) ⟨5466770, by rfl⟩ : syracuseStep 7289027 = 10933541) B10933541
theorem B3242195 : Blo 1439539 3242195 := bstep (se 1 (by rfl) ⟨2431646, by rfl⟩ : syracuseStep 3242195 = 4863293) B4863293
theorem B2160905 : Blo 1439539 2160905 := bstep (se 2 (by rfl) ⟨810339, by rfl⟩ : syracuseStep 2160905 = 1620679) B1620679
theorem B3242249 : Blo 1439539 3242249 := bstep (se 2 (by rfl) ⟨1215843, by rfl⟩ : syracuseStep 3242249 = 2431687) B2431687
theorem B4864265 : Blo 1439539 4864265 := bstep (se 2 (by rfl) ⟨1824099, by rfl⟩ : syracuseStep 4864265 = 3648199) B3648199
theorem B7297289 : Blo 1439539 7297289 := bstep (se 2 (by rfl) ⟨2736483, by rfl⟩ : syracuseStep 7297289 = 5472967) B5472967
theorem B46733593 : Blo 1439539 46733593 := bstep (se 2 (by rfl) ⟨17525097, by rfl⟩ : syracuseStep 46733593 = 35050195) B35050195
theorem B1440031 : Blo 1439539 1440031 := bstep (se 1 (by rfl) ⟨1080023, by rfl⟩ : syracuseStep 1440031 = 2160047) B2160047
theorem B16406873 : Blo 1439539 16406873 := bstep (se 2 (by rfl) ⟨6152577, by rfl⟩ : syracuseStep 16406873 = 12305155) B12305155
theorem B1440091 : Blo 1439539 1440091 := bstep (se 1 (by rfl) ⟨1080068, by rfl⟩ : syracuseStep 1440091 = 2160137) B2160137
theorem B1440111 : Blo 1439539 1440111 := bstep (se 1 (by rfl) ⟨1080083, by rfl⟩ : syracuseStep 1440111 = 2160167) B2160167
theorem B2161007 : Blo 1439539 2161007 := bstep (se 1 (by rfl) ⟨1620755, by rfl⟩ : syracuseStep 2161007 = 3241511) B3241511
theorem B2431343 : Blo 1439539 2431343 := bstep (se 1 (by rfl) ⟨1823507, by rfl⟩ : syracuseStep 2431343 = 3647015) B3647015
theorem B8206717 : Blo 1439539 8206717 := bstep (se 3 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 8206717 = 3077519) B3077519
theorem B1440167 : Blo 1439539 1440167 := bstep (se 1 (by rfl) ⟨1080125, by rfl⟩ : syracuseStep 1440167 = 2160251) B2160251
theorem B1620391 : Blo 1439539 1620391 := bstep (se 1 (by rfl) ⟨1215293, by rfl⟩ : syracuseStep 1620391 = 2430587) B2430587
theorem B3242465 : Blo 1439539 3242465 := bstep (se 2 (by rfl) ⟨1215924, by rfl⟩ : syracuseStep 3242465 = 2431849) B2431849
theorem B1440251 : Blo 1439539 1440251 := bstep (se 1 (by rfl) ⟨1080188, by rfl⟩ : syracuseStep 1440251 = 2160377) B2160377
theorem B3643967 : Blo 1439539 3643967 := bstep (se 1 (by rfl) ⟨2732975, by rfl⟩ : syracuseStep 3643967 = 5465951) B5465951
theorem B1440319 : Blo 1439539 1440319 := bstep (se 1 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 1440319 = 2160479) B2160479
theorem B1440327 : Blo 1439539 1440327 := bstep (se 1 (by rfl) ⟨1080245, by rfl⟩ : syracuseStep 1440327 = 2160491) B2160491
theorem B2161223 : Blo 1439539 2161223 := bstep (se 1 (by rfl) ⟨1620917, by rfl⟩ : syracuseStep 2161223 = 3241835) B3241835
theorem B2431559 : Blo 1439539 2431559 := bstep (se 1 (by rfl) ⟨1823669, by rfl⟩ : syracuseStep 2431559 = 3647339) B3647339
theorem B2161259 : Blo 1439539 2161259 := bstep (se 1 (by rfl) ⟨1620944, by rfl⟩ : syracuseStep 2161259 = 3241889) B3241889
theorem B10386053 : Blo 1439539 10386053 := bstep (se 4 (by rfl) ⟨973692, by rfl⟩ : syracuseStep 10386053 = 1947385) B1947385
theorem B33258119 : Blo 1439539 33258119 := bstep (se 1 (by rfl) ⟨24943589, by rfl⟩ : syracuseStep 33258119 = 49887179) B49887179
theorem B7387823 : Blo 1439539 7387823 := bstep (se 1 (by rfl) ⟨5540867, by rfl⟩ : syracuseStep 7387823 = 11081735) B11081735
theorem B1440479 : Blo 1439539 1440479 := bstep (se 1 (by rfl) ⟨1080359, by rfl⟩ : syracuseStep 1440479 = 2160719) B2160719
theorem B3947255 : Blo 1439539 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B4102903 : Blo 1439539 4102903 := bstep (se 1 (by rfl) ⟨3077177, by rfl⟩ : syracuseStep 4102903 = 6154355) B6154355
theorem B3242771 : Blo 1439539 3242771 := bstep (se 1 (by rfl) ⟨2432078, by rfl⟩ : syracuseStep 3242771 = 4864157) B4864157
theorem B1440559 : Blo 1439539 1440559 := bstep (se 1 (by rfl) ⟨1080419, by rfl⟩ : syracuseStep 1440559 = 2160839) B2160839
theorem B2161487 : Blo 1439539 2161487 := bstep (se 1 (by rfl) ⟨1621115, by rfl⟩ : syracuseStep 2161487 = 3242231) B3242231
theorem B1440667 : Blo 1439539 1440667 := bstep (se 1 (by rfl) ⟨1080500, by rfl⟩ : syracuseStep 1440667 = 2161001) B2161001
theorem B1440719 : Blo 1439539 1440719 := bstep (se 1 (by rfl) ⟨1080539, by rfl⟩ : syracuseStep 1440719 = 2161079) B2161079
theorem B1440743 : Blo 1439539 1440743 := bstep (se 1 (by rfl) ⟨1080557, by rfl⟩ : syracuseStep 1440743 = 2161115) B2161115
theorem B1620967 : Blo 1439539 1620967 := bstep (se 1 (by rfl) ⟨1215725, by rfl⟩ : syracuseStep 1620967 = 2431451) B2431451
theorem B7388147 : Blo 1439539 7388147 := bstep (se 1 (by rfl) ⟨5541110, by rfl⟩ : syracuseStep 7388147 = 11082221) B11082221
theorem B2431991 : Blo 1439539 2431991 := bstep (se 1 (by rfl) ⟨1823993, by rfl⟩ : syracuseStep 2431991 = 3647987) B3647987
theorem B4103291 : Blo 1439539 4103291 := bstep (se 1 (by rfl) ⟨3077468, by rfl⟩ : syracuseStep 4103291 = 6154937) B6154937
theorem B3243131 : Blo 1439539 3243131 := bstep (se 1 (by rfl) ⟨2432348, by rfl⟩ : syracuseStep 3243131 = 4864697) B4864697
theorem B10935485 : Blo 1439539 10935485 := bstep (se 3 (by rfl) ⟨2050403, by rfl⟩ : syracuseStep 10935485 = 4100807) B4100807
theorem B3644615 : Blo 1439539 3644615 := bstep (se 1 (by rfl) ⟨2733461, by rfl⟩ : syracuseStep 3644615 = 5466923) B5466923
theorem B3644635 : Blo 1439539 3644635 := bstep (se 1 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 3644635 = 5466953) B5466953
theorem B2161883 : Blo 1439539 2161883 := bstep (se 1 (by rfl) ⟨1621412, by rfl⟩ : syracuseStep 2161883 = 3242825) B3242825
theorem B3243257 : Blo 1439539 3243257 := bstep (se 2 (by rfl) ⟨1216221, by rfl⟩ : syracuseStep 3243257 = 2432443) B2432443
theorem B1441055 : Blo 1439539 1441055 := bstep (se 1 (by rfl) ⟨1080791, by rfl⟩ : syracuseStep 1441055 = 2161583) B2161583
theorem B1441115 : Blo 1439539 1441115 := bstep (se 1 (by rfl) ⟨1080836, by rfl⟩ : syracuseStep 1441115 = 2161673) B2161673
theorem B1441135 : Blo 1439539 1441135 := bstep (se 1 (by rfl) ⟨1080851, by rfl⟩ : syracuseStep 1441135 = 2161703) B2161703
theorem B2162057 : Blo 1439539 2162057 := bstep (se 2 (by rfl) ⟨810771, by rfl⟩ : syracuseStep 2162057 = 1621543) B1621543
theorem B3243401 : Blo 1439539 3243401 := bstep (se 2 (by rfl) ⟨1216275, by rfl⟩ : syracuseStep 3243401 = 2432551) B2432551
theorem B1441191 : Blo 1439539 1441191 := bstep (se 1 (by rfl) ⟨1080893, by rfl⟩ : syracuseStep 1441191 = 2161787) B2161787
theorem B1441275 : Blo 1439539 1441275 := bstep (se 1 (by rfl) ⟨1080956, by rfl⟩ : syracuseStep 1441275 = 2161913) B2161913
theorem B6921787 : Blo 1439539 6921787 := bstep (se 1 (by rfl) ⟨5191340, by rfl⟩ : syracuseStep 6921787 = 10382681) B10382681
theorem B1441343 : Blo 1439539 1441343 := bstep (se 1 (by rfl) ⟨1081007, by rfl⟩ : syracuseStep 1441343 = 2162015) B2162015
theorem B1441351 : Blo 1439539 1441351 := bstep (se 1 (by rfl) ⟨1081013, by rfl⟩ : syracuseStep 1441351 = 2162027) B2162027
theorem B3284563 : Blo 1439539 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B37437011 : Blo 1439539 37437011 := bstep (se 1 (by rfl) ⟨28077758, by rfl⟩ : syracuseStep 37437011 = 56155517) B56155517
theorem B78904979 : Blo 1439539 78904979 := bstep (se 1 (by rfl) ⟨59178734, by rfl⟩ : syracuseStep 78904979 = 118357469) B118357469
theorem B1441503 : Blo 1439539 1441503 := bstep (se 1 (by rfl) ⟨1081127, by rfl⟩ : syracuseStep 1441503 = 2162255) B2162255
theorem B7397099 : Blo 1439539 7397099 := bstep (se 1 (by rfl) ⟨5547824, by rfl⟩ : syracuseStep 7397099 = 11095649) B11095649
theorem B1538623 : Blo 1439539 1538623 := bstep (se 1 (by rfl) ⟨1153967, by rfl⟩ : syracuseStep 1538623 = 2307935) B2307935
theorem B5193533 : Blo 1439539 5193533 := bstep (se 3 (by rfl) ⟨973787, by rfl⟩ : syracuseStep 5193533 = 1947575) B1947575
theorem B7389463 : Blo 1439539 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B10379593 : Blo 1439539 10379593 := bstep (se 2 (by rfl) ⟨3892347, by rfl⟩ : syracuseStep 10379593 = 7784695) B7784695
theorem B266002829 : Blo 1439539 266002829 := bstep (se 3 (by rfl) ⟨49875530, by rfl⟩ : syracuseStep 266002829 = 99751061) B99751061
theorem B16401041 : Blo 1439539 16401041 := bstep (se 2 (by rfl) ⟨6150390, by rfl⟩ : syracuseStep 16401041 = 12300781) B12300781
theorem B9233149 : Blo 1439539 9233149 := bstep (se 3 (by rfl) ⟨1731215, by rfl⟩ : syracuseStep 9233149 = 3462431) B3462431
theorem B3646255 : Blo 1439539 3646255 := bstep (se 1 (by rfl) ⟨2734691, by rfl⟩ : syracuseStep 3646255 = 5469383) B5469383
theorem B8316265 : Blo 1439539 8316265 := bstep (se 2 (by rfl) ⟨3118599, by rfl⟩ : syracuseStep 8316265 = 6237199) B6237199
theorem B4859243 : Blo 1439539 4859243 := bstep (se 1 (by rfl) ⟨3644432, by rfl⟩ : syracuseStep 4859243 = 7288865) B7288865
theorem B4859351 : Blo 1439539 4859351 := bstep (se 1 (by rfl) ⟨3644513, by rfl⟩ : syracuseStep 4859351 = 7289027) B7289027
theorem B10937915 : Blo 1439539 10937915 := bstep (se 1 (by rfl) ⟨8203436, by rfl⟩ : syracuseStep 10937915 = 16406873) B16406873
theorem B4859513 : Blo 1439539 4859513 := bstep (se 2 (by rfl) ⟨1822317, by rfl⟩ : syracuseStep 4859513 = 3644635) B3644635
theorem B88688317 : Blo 1439539 88688317 := bstep (se 3 (by rfl) ⟨16629059, by rfl⟩ : syracuseStep 88688317 = 33258119) B33258119
theorem B6924035 : Blo 1439539 6924035 := bstep (se 1 (by rfl) ⟨5193026, by rfl⟩ : syracuseStep 6924035 = 10386053) B10386053
theorem B2049823 : Blo 1439539 2049823 := bstep (se 1 (by rfl) ⟨1537367, by rfl⟩ : syracuseStep 2049823 = 3074735) B3074735
theorem B4925215 : Blo 1439539 4925215 := bstep (se 1 (by rfl) ⟨3693911, by rfl⟩ : syracuseStep 4925215 = 7387823) B7387823
theorem B2631503 : Blo 1439539 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B4925431 : Blo 1439539 4925431 := bstep (se 1 (by rfl) ⟨3694073, by rfl⟩ : syracuseStep 4925431 = 7388147) B7388147
theorem B52603319 : Blo 1439539 52603319 := bstep (se 1 (by rfl) ⟨39452489, by rfl⟩ : syracuseStep 52603319 = 78904979) B78904979
theorem B15583751 : Blo 1439539 15583751 := bstep (se 1 (by rfl) ⟨11687813, by rfl⟩ : syracuseStep 15583751 = 23375627) B23375627
theorem B21048029 : Blo 1439539 21048029 := bstep (se 3 (by rfl) ⟨3946505, by rfl⟩ : syracuseStep 21048029 = 7893011) B7893011
theorem B18459373 : Blo 1439539 18459373 := bstep (se 3 (by rfl) ⟨3461132, by rfl⟩ : syracuseStep 18459373 = 6922265) B6922265
theorem B3648311 : Blo 1439539 3648311 := bstep (se 1 (by rfl) ⟨2736233, by rfl⟩ : syracuseStep 3648311 = 5472467) B5472467
theorem B62311457 : Blo 1439539 62311457 := bstep (se 2 (by rfl) ⟨23366796, by rfl⟩ : syracuseStep 62311457 = 46733593) B46733593
theorem B2190407 : Blo 1439539 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B4861025 : Blo 1439539 4861025 := bstep (se 2 (by rfl) ⟨1822884, by rfl⟩ : syracuseStep 4861025 = 3645769) B3645769
theorem B3239135 : Blo 1439539 3239135 := bstep (se 1 (by rfl) ⟨2429351, by rfl⟩ : syracuseStep 3239135 = 4858703) B4858703
theorem B3648847 : Blo 1439539 3648847 := bstep (se 1 (by rfl) ⟨2736635, by rfl⟩ : syracuseStep 3648847 = 5473271) B5473271
theorem B2051497 : Blo 1439539 2051497 := bstep (se 2 (by rfl) ⟨769311, by rfl⟩ : syracuseStep 2051497 = 1538623) B1538623
theorem B3239351 : Blo 1439539 3239351 := bstep (se 1 (by rfl) ⟨2429513, by rfl⟩ : syracuseStep 3239351 = 4859027) B4859027
theorem B4615613 : Blo 1439539 4615613 := bstep (se 3 (by rfl) ⟨865427, by rfl⟩ : syracuseStep 4615613 = 1730855) B1730855
theorem B16403957 : Blo 1439539 16403957 := bstep (se 5 (by rfl) ⟨768935, by rfl⟩ : syracuseStep 16403957 = 1537871) B1537871
theorem B8203801 : Blo 1439539 8203801 := bstep (se 2 (by rfl) ⟨3076425, by rfl⟩ : syracuseStep 8203801 = 6152851) B6152851
theorem B3239531 : Blo 1439539 3239531 := bstep (se 1 (by rfl) ⟨2429648, by rfl⟩ : syracuseStep 3239531 = 4859297) B4859297
theorem B4861565 : Blo 1439539 4861565 := bstep (se 3 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 4861565 = 1823087) B1823087
theorem B3239801 : Blo 1439539 3239801 := bstep (se 2 (by rfl) ⟨1214925, by rfl⟩ : syracuseStep 3239801 = 2429851) B2429851
theorem B4861835 : Blo 1439539 4861835 := bstep (se 1 (by rfl) ⟨3646376, by rfl⟩ : syracuseStep 4861835 = 7292753) B7292753
theorem B51269699 : Blo 1439539 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B24621245 : Blo 1439539 24621245 := bstep (se 3 (by rfl) ⟨4616483, by rfl⟩ : syracuseStep 24621245 = 9232967) B9232967
theorem B6156611 : Blo 1439539 6156611 := bstep (se 1 (by rfl) ⟨4617458, by rfl⟩ : syracuseStep 6156611 = 9234917) B9234917
theorem B2429311 : Blo 1439539 2429311 := bstep (se 1 (by rfl) ⟨1821983, by rfl⟩ : syracuseStep 2429311 = 3643967) B3643967
theorem B4100489 : Blo 1439539 4100489 := bstep (se 2 (by rfl) ⟨1537683, by rfl⟩ : syracuseStep 4100489 = 3075367) B3075367
theorem B4862375 : Blo 1439539 4862375 := bstep (se 1 (by rfl) ⟨3646781, by rfl⟩ : syracuseStep 4862375 = 7293563) B7293563
theorem B2159339 : Blo 1439539 2159339 := bstep (se 1 (by rfl) ⟨1619504, by rfl⟩ : syracuseStep 2159339 = 3239009) B3239009
theorem B9229049 : Blo 1439539 9229049 := bstep (se 2 (by rfl) ⟨3460893, by rfl⟩ : syracuseStep 9229049 = 6921787) B6921787
theorem B2159369 : Blo 1439539 2159369 := bstep (se 2 (by rfl) ⟨809763, by rfl⟩ : syracuseStep 2159369 = 1619527) B1619527
theorem B4379417 : Blo 1439539 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B2429743 : Blo 1439539 2429743 := bstep (se 1 (by rfl) ⟨1822307, by rfl⟩ : syracuseStep 2429743 = 3644615) B3644615
theorem B2159471 : Blo 1439539 2159471 := bstep (se 1 (by rfl) ⟨1619603, by rfl⟩ : syracuseStep 2159471 = 3239207) B3239207
theorem B8885257 : Blo 1439539 8885257 := bstep (se 2 (by rfl) ⟨3331971, by rfl⟩ : syracuseStep 8885257 = 6663943) B6663943
theorem B24958007 : Blo 1439539 24958007 := bstep (se 1 (by rfl) ⟨18718505, by rfl⟩ : syracuseStep 24958007 = 37437011) B37437011
theorem B2159723 : Blo 1439539 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B2307179 : Blo 1439539 2307179 := bstep (se 1 (by rfl) ⟨1730384, by rfl⟩ : syracuseStep 2307179 = 3460769) B3460769
theorem B3462355 : Blo 1439539 3462355 := bstep (se 1 (by rfl) ⟨2596766, by rfl⟩ : syracuseStep 3462355 = 5193533) B5193533
theorem B27702593 : Blo 1439539 27702593 := bstep (se 2 (by rfl) ⟨10388472, by rfl⟩ : syracuseStep 27702593 = 20776945) B20776945
theorem B2159963 : Blo 1439539 2159963 := bstep (se 1 (by rfl) ⟨1619972, by rfl⟩ : syracuseStep 2159963 = 3239945) B3239945
theorem B28431767 : Blo 1439539 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B6919789 : Blo 1439539 6919789 := bstep (se 3 (by rfl) ⟨1297460, by rfl⟩ : syracuseStep 6919789 = 2594921) B2594921
theorem B2160239 : Blo 1439539 2160239 := bstep (se 1 (by rfl) ⟨1620179, by rfl⟩ : syracuseStep 2160239 = 3240359) B3240359
theorem B23672483 : Blo 1439539 23672483 := bstep (se 1 (by rfl) ⟨17754362, by rfl⟩ : syracuseStep 23672483 = 35508725) B35508725
theorem B2160311 : Blo 1439539 2160311 := bstep (se 1 (by rfl) ⟨1620233, by rfl⟩ : syracuseStep 2160311 = 3240467) B3240467
theorem B3241655 : Blo 1439539 3241655 := bstep (se 1 (by rfl) ⟨2431241, by rfl⟩ : syracuseStep 3241655 = 4862483) B4862483
theorem B4863671 : Blo 1439539 4863671 := bstep (se 1 (by rfl) ⟨3647753, by rfl⟩ : syracuseStep 4863671 = 7295507) B7295507
theorem B2160347 : Blo 1439539 2160347 := bstep (se 1 (by rfl) ⟨1620260, by rfl⟩ : syracuseStep 2160347 = 3240521) B3240521
theorem B1619707 : Blo 1439539 1619707 := bstep (se 1 (by rfl) ⟨1214780, by rfl⟩ : syracuseStep 1619707 = 2429561) B2429561
theorem B2430715 : Blo 1439539 2430715 := bstep (se 1 (by rfl) ⟨1823036, by rfl⟩ : syracuseStep 2430715 = 3646073) B3646073
theorem B1619743 : Blo 1439539 1619743 := bstep (se 1 (by rfl) ⟨1214807, by rfl⟩ : syracuseStep 1619743 = 2429615) B2429615
theorem B1439551 : Blo 1439539 1439551 := bstep (se 1 (by rfl) ⟨1079663, by rfl⟩ : syracuseStep 1439551 = 2159327) B2159327
theorem B2733887 : Blo 1439539 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B10942289 : Blo 1439539 10942289 := bstep (se 2 (by rfl) ⟨4103358, by rfl⟩ : syracuseStep 10942289 = 8206717) B8206717
theorem B2160521 : Blo 1439539 2160521 := bstep (se 2 (by rfl) ⟨810195, by rfl⟩ : syracuseStep 2160521 = 1620391) B1620391
theorem B2430857 : Blo 1439539 2430857 := bstep (se 2 (by rfl) ⟨911571, by rfl⟩ : syracuseStep 2430857 = 1823143) B1823143
theorem B8206217 : Blo 1439539 8206217 := bstep (se 2 (by rfl) ⟨3077331, by rfl⟩ : syracuseStep 8206217 = 6154663) B6154663
theorem B12310487 : Blo 1439539 12310487 := bstep (se 1 (by rfl) ⟨9232865, by rfl⟩ : syracuseStep 12310487 = 18465731) B18465731
theorem B1439727 : Blo 1439539 1439727 := bstep (se 1 (by rfl) ⟨1079795, by rfl⟩ : syracuseStep 1439727 = 2159591) B2159591
theorem B2160623 : Blo 1439539 2160623 := bstep (se 1 (by rfl) ⟨1620467, by rfl⟩ : syracuseStep 2160623 = 3240935) B3240935
theorem B6150239 : Blo 1439539 6150239 := bstep (se 1 (by rfl) ⟨4612679, by rfl⟩ : syracuseStep 6150239 = 9225359) B9225359
theorem B2734175 : Blo 1439539 2734175 := bstep (se 1 (by rfl) ⟨2050631, by rfl⟩ : syracuseStep 2734175 = 4101263) B4101263
theorem B4995215 : Blo 1439539 4995215 := bstep (se 1 (by rfl) ⟨3746411, by rfl⟩ : syracuseStep 4995215 = 7492823) B7492823
theorem B1439899 : Blo 1439539 1439899 := bstep (se 1 (by rfl) ⟨1079924, by rfl⟩ : syracuseStep 1439899 = 2159849) B2159849
theorem B1439935 : Blo 1439539 1439935 := bstep (se 1 (by rfl) ⟨1079951, by rfl⟩ : syracuseStep 1439935 = 2159903) B2159903
theorem B1874111 : Blo 1439539 1874111 := bstep (se 1 (by rfl) ⟨1405583, by rfl⟩ : syracuseStep 1874111 = 2811167) B2811167
theorem B2160875 : Blo 1439539 2160875 := bstep (se 1 (by rfl) ⟨1620656, by rfl⟩ : syracuseStep 2160875 = 3241313) B3241313
theorem B1947883 : Blo 1439539 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B2160935 : Blo 1439539 2160935 := bstep (se 1 (by rfl) ⟨1620701, by rfl⟩ : syracuseStep 2160935 = 3241403) B3241403
theorem B1440047 : Blo 1439539 1440047 := bstep (se 1 (by rfl) ⟨1080035, by rfl⟩ : syracuseStep 1440047 = 2160071) B2160071
theorem B23378219 : Blo 1439539 23378219 := bstep (se 1 (by rfl) ⟨17533664, by rfl⟩ : syracuseStep 23378219 = 35067329) B35067329
theorem B2431289 : Blo 1439539 2431289 := bstep (se 2 (by rfl) ⟨911733, by rfl⟩ : syracuseStep 2431289 = 1823467) B1823467
theorem B5470537 : Blo 1439539 5470537 := bstep (se 2 (by rfl) ⟨2051451, by rfl⟩ : syracuseStep 5470537 = 4102903) B4102903
theorem B2161019 : Blo 1439539 2161019 := bstep (se 1 (by rfl) ⟨1620764, by rfl⟩ : syracuseStep 2161019 = 3241529) B3241529
theorem B12302765 : Blo 1439539 12302765 := bstep (se 3 (by rfl) ⟨2306768, by rfl⟩ : syracuseStep 12302765 = 4613537) B4613537
theorem B1440283 : Blo 1439539 1440283 := bstep (se 1 (by rfl) ⟨1080212, by rfl⟩ : syracuseStep 1440283 = 2160425) B2160425
theorem B1440287 : Blo 1439539 1440287 := bstep (se 1 (by rfl) ⟨1080215, by rfl⟩ : syracuseStep 1440287 = 2160431) B2160431
theorem B2161289 : Blo 1439539 2161289 := bstep (se 2 (by rfl) ⟨810483, by rfl⟩ : syracuseStep 2161289 = 1620967) B1620967
theorem B9353951 : Blo 1439539 9353951 := bstep (se 1 (by rfl) ⟨7015463, by rfl⟩ : syracuseStep 9353951 = 14030927) B14030927
theorem B16628503 : Blo 1439539 16628503 := bstep (se 1 (by rfl) ⟨12471377, by rfl⟩ : syracuseStep 16628503 = 24942755) B24942755
theorem B2161463 : Blo 1439539 2161463 := bstep (se 1 (by rfl) ⟨1621097, by rfl⟩ : syracuseStep 2161463 = 3242195) B3242195
theorem B1440603 : Blo 1439539 1440603 := bstep (se 1 (by rfl) ⟨1080452, by rfl⟩ : syracuseStep 1440603 = 2160905) B2160905
theorem B2161499 : Blo 1439539 2161499 := bstep (se 1 (by rfl) ⟨1621124, by rfl⟩ : syracuseStep 2161499 = 3242249) B3242249
theorem B3242843 : Blo 1439539 3242843 := bstep (se 1 (by rfl) ⟨2432132, by rfl⟩ : syracuseStep 3242843 = 4864265) B4864265
theorem B4864859 : Blo 1439539 4864859 := bstep (se 1 (by rfl) ⟨3648644, by rfl⟩ : syracuseStep 4864859 = 7297289) B7297289
theorem B16415621 : Blo 1439539 16415621 := bstep (se 4 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 16415621 = 3077929) B3077929
theorem B1440671 : Blo 1439539 1440671 := bstep (se 1 (by rfl) ⟨1080503, by rfl⟩ : syracuseStep 1440671 = 2161007) B2161007
theorem B1620895 : Blo 1439539 1620895 := bstep (se 1 (by rfl) ⟨1215671, by rfl⟩ : syracuseStep 1620895 = 2431343) B2431343
theorem B2431903 : Blo 1439539 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B2161643 : Blo 1439539 2161643 := bstep (se 1 (by rfl) ⟨1621232, by rfl⟩ : syracuseStep 2161643 = 3242465) B3242465
theorem B1440815 : Blo 1439539 1440815 := bstep (se 1 (by rfl) ⟨1080611, by rfl⟩ : syracuseStep 1440815 = 2161223) B2161223
theorem B1621039 : Blo 1439539 1621039 := bstep (se 1 (by rfl) ⟨1215779, by rfl⟩ : syracuseStep 1621039 = 2431559) B2431559
theorem B7789625 : Blo 1439539 7789625 := bstep (se 2 (by rfl) ⟨2921109, by rfl⟩ : syracuseStep 7789625 = 5842219) B5842219
theorem B1440839 : Blo 1439539 1440839 := bstep (se 1 (by rfl) ⟨1080629, by rfl⟩ : syracuseStep 1440839 = 2161259) B2161259
theorem B85580887 : Blo 1439539 85580887 := bstep (se 1 (by rfl) ⟨64185665, by rfl⟩ : syracuseStep 85580887 = 128371331) B128371331
theorem B2161847 : Blo 1439539 2161847 := bstep (se 1 (by rfl) ⟨1621385, by rfl⟩ : syracuseStep 2161847 = 3242771) B3242771
theorem B1440991 : Blo 1439539 1440991 := bstep (se 1 (by rfl) ⟨1080743, by rfl⟩ : syracuseStep 1440991 = 2161487) B2161487
theorem B1621327 : Blo 1439539 1621327 := bstep (se 1 (by rfl) ⟨1215995, by rfl⟩ : syracuseStep 1621327 = 2431991) B2431991
theorem B2432335 : Blo 1439539 2432335 := bstep (se 1 (by rfl) ⟨1824251, by rfl⟩ : syracuseStep 2432335 = 3648503) B3648503
theorem B2735527 : Blo 1439539 2735527 := bstep (se 1 (by rfl) ⟨2051645, by rfl⟩ : syracuseStep 2735527 = 4103291) B4103291
theorem B2162087 : Blo 1439539 2162087 := bstep (se 1 (by rfl) ⟨1621565, by rfl⟩ : syracuseStep 2162087 = 3243131) B3243131
theorem B2432423 : Blo 1439539 2432423 := bstep (se 1 (by rfl) ⟨1824317, by rfl⟩ : syracuseStep 2432423 = 3648635) B3648635
theorem B7290323 : Blo 1439539 7290323 := bstep (se 1 (by rfl) ⟨5467742, by rfl⟩ : syracuseStep 7290323 = 10935485) B10935485
theorem B1441255 : Blo 1439539 1441255 := bstep (se 1 (by rfl) ⟨1080941, by rfl⟩ : syracuseStep 1441255 = 2161883) B2161883
theorem B2162171 : Blo 1439539 2162171 := bstep (se 1 (by rfl) ⟨1621628, by rfl⟩ : syracuseStep 2162171 = 3243257) B3243257
theorem B2432585 : Blo 1439539 2432585 := bstep (se 2 (by rfl) ⟨912219, by rfl⟩ : syracuseStep 2432585 = 1824439) B1824439
theorem B1441371 : Blo 1439539 1441371 := bstep (se 1 (by rfl) ⟨1081028, by rfl⟩ : syracuseStep 1441371 = 2162057) B2162057
theorem B2162267 : Blo 1439539 2162267 := bstep (se 1 (by rfl) ⟨1621700, by rfl⟩ : syracuseStep 2162267 = 3243401) B3243401
theorem B3645071 : Blo 1439539 3645071 := bstep (se 1 (by rfl) ⟨2733803, by rfl⟩ : syracuseStep 3645071 = 5467607) B5467607
theorem B4931399 : Blo 1439539 4931399 := bstep (se 1 (by rfl) ⟨3698549, by rfl⟩ : syracuseStep 4931399 = 7397099) B7397099
theorem B18464705 : Blo 1439539 18464705 := bstep (se 2 (by rfl) ⟨6924264, by rfl⟩ : syracuseStep 18464705 = 13848529) B13848529
theorem B5841085 : Blo 1439539 5841085 := bstep (se 3 (by rfl) ⟨1095203, by rfl⟩ : syracuseStep 5841085 = 2190407) B2190407
theorem B4104407 : Blo 1439539 4104407 := bstep (se 1 (by rfl) ⟨3078305, by rfl⟩ : syracuseStep 4104407 = 6156611) B6156611
theorem B7291133 : Blo 1439539 7291133 := bstep (se 3 (by rfl) ⟨1367087, by rfl⟩ : syracuseStep 7291133 = 2734175) B2734175
theorem B2597177 : Blo 1439539 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B6152699 : Blo 1439539 6152699 := bstep (se 1 (by rfl) ⟨4614524, by rfl⟩ : syracuseStep 6152699 = 9229049) B9229049
theorem B4997629 : Blo 1439539 4997629 := bstep (se 3 (by rfl) ⟨937055, by rfl⟩ : syracuseStep 4997629 = 1874111) B1874111
theorem B16638671 : Blo 1439539 16638671 := bstep (se 1 (by rfl) ⟨12479003, by rfl⟩ : syracuseStep 16638671 = 24958007) B24958007
theorem B7291943 : Blo 1439539 7291943 := bstep (se 1 (by rfl) ⟨5468957, by rfl⟩ : syracuseStep 7291943 = 10937915) B10937915
theorem B75818045 : Blo 1439539 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B1754335 : Blo 1439539 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B114107849 : Blo 1439539 114107849 := bstep (se 2 (by rfl) ⟨42790443, by rfl⟩ : syracuseStep 114107849 = 85580887) B85580887
theorem B8201843 : Blo 1439539 8201843 := bstep (se 1 (by rfl) ⟨6151382, by rfl⟩ : syracuseStep 8201843 = 12302765) B12302765
theorem B10389167 : Blo 1439539 10389167 := bstep (se 1 (by rfl) ⟨7791875, by rfl⟩ : syracuseStep 10389167 = 15583751) B15583751
theorem B6235967 : Blo 1439539 6235967 := bstep (se 1 (by rfl) ⟨4676975, by rfl⟩ : syracuseStep 6235967 = 9353951) B9353951
theorem B3647369 : Blo 1439539 3647369 := bstep (se 2 (by rfl) ⟨1367763, by rfl⟩ : syracuseStep 3647369 = 2735527) B2735527
theorem B10938401 : Blo 1439539 10938401 := bstep (se 2 (by rfl) ⟨4101900, by rfl⟩ : syracuseStep 10938401 = 8203801) B8203801
theorem B9226385 : Blo 1439539 9226385 := bstep (se 2 (by rfl) ⟨3459894, by rfl⟩ : syracuseStep 9226385 = 6919789) B6919789
theorem B13150397 : Blo 1439539 13150397 := bstep (se 3 (by rfl) ⟨2465699, by rfl⟩ : syracuseStep 13150397 = 4931399) B4931399
theorem B4860215 : Blo 1439539 4860215 := bstep (se 1 (by rfl) ⟨3645161, by rfl⟩ : syracuseStep 4860215 = 7290323) B7290323
theorem B136719197 : Blo 1439539 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B177335219 : Blo 1439539 177335219 := bstep (se 1 (by rfl) ⟨133001414, by rfl⟩ : syracuseStep 177335219 = 266002829) B266002829
theorem B13839457 : Blo 1439539 13839457 := bstep (se 2 (by rfl) ⟨5189796, by rfl⟩ : syracuseStep 13839457 = 10379593) B10379593
theorem B7294049 : Blo 1439539 7294049 := bstep (se 2 (by rfl) ⟨2735268, by rfl⟩ : syracuseStep 7294049 = 5470537) B5470537
theorem B3239081 : Blo 1439539 3239081 := bstep (se 2 (by rfl) ⟨1214655, by rfl⟩ : syracuseStep 3239081 = 2429311) B2429311
theorem B2919611 : Blo 1439539 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B18468395 : Blo 1439539 18468395 := bstep (se 1 (by rfl) ⟨13851296, by rfl⟩ : syracuseStep 18468395 = 27702593) B27702593
theorem B3239495 : Blo 1439539 3239495 := bstep (se 1 (by rfl) ⟨2429621, by rfl⟩ : syracuseStep 3239495 = 4859243) B4859243
theorem B3239567 : Blo 1439539 3239567 := bstep (se 1 (by rfl) ⟨2429675, by rfl⟩ : syracuseStep 3239567 = 4859351) B4859351
theorem B24612497 : Blo 1439539 24612497 := bstep (se 2 (by rfl) ⟨9229686, by rfl⟩ : syracuseStep 24612497 = 18459373) B18459373
theorem B22171337 : Blo 1439539 22171337 := bstep (se 2 (by rfl) ⟨8314251, by rfl⟩ : syracuseStep 22171337 = 16628503) B16628503
theorem B3239657 : Blo 1439539 3239657 := bstep (se 2 (by rfl) ⟨1214871, by rfl⟩ : syracuseStep 3239657 = 2429743) B2429743
theorem B4861673 : Blo 1439539 4861673 := bstep (se 2 (by rfl) ⟨1823127, by rfl⟩ : syracuseStep 4861673 = 3646255) B3646255
theorem B3239675 : Blo 1439539 3239675 := bstep (se 1 (by rfl) ⟨2429756, by rfl⟩ : syracuseStep 3239675 = 4859513) B4859513
theorem B15781655 : Blo 1439539 15781655 := bstep (se 1 (by rfl) ⟨11836241, by rfl⟩ : syracuseStep 15781655 = 23672483) B23672483
theorem B4616023 : Blo 1439539 4616023 := bstep (se 1 (by rfl) ⟨3462017, by rfl⟩ : syracuseStep 4616023 = 6924035) B6924035
theorem B1822591 : Blo 1439539 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B7294859 : Blo 1439539 7294859 := bstep (se 1 (by rfl) ⟨5471144, by rfl⟩ : syracuseStep 7294859 = 10942289) B10942289
theorem B4100159 : Blo 1439539 4100159 := bstep (se 1 (by rfl) ⟨3075119, by rfl⟩ : syracuseStep 4100159 = 6150239) B6150239
theorem B3330143 : Blo 1439539 3330143 := bstep (se 1 (by rfl) ⟨2497607, by rfl⟩ : syracuseStep 3330143 = 4995215) B4995215
theorem B15585479 : Blo 1439539 15585479 := bstep (se 1 (by rfl) ⟨11689109, by rfl⟩ : syracuseStep 15585479 = 23378219) B23378219
theorem B4616473 : Blo 1439539 4616473 := bstep (se 2 (by rfl) ⟨1731177, by rfl⟩ : syracuseStep 4616473 = 3462355) B3462355
theorem B11088353 : Blo 1439539 11088353 := bstep (se 2 (by rfl) ⟨4158132, by rfl⟩ : syracuseStep 11088353 = 8316265) B8316265
theorem B3240683 : Blo 1439539 3240683 := bstep (se 1 (by rfl) ⟨2430512, by rfl⟩ : syracuseStep 3240683 = 4861025) B4861025
theorem B2159423 : Blo 1439539 2159423 := bstep (se 1 (by rfl) ⟨1619567, by rfl⟩ : syracuseStep 2159423 = 3239135) B3239135
theorem B10941317 : Blo 1439539 10941317 := bstep (se 4 (by rfl) ⟨1025748, by rfl⟩ : syracuseStep 10941317 = 2051497) B2051497
theorem B2159567 : Blo 1439539 2159567 := bstep (se 1 (by rfl) ⟨1619675, by rfl⟩ : syracuseStep 2159567 = 3239351) B3239351
theorem B3077075 : Blo 1439539 3077075 := bstep (se 1 (by rfl) ⟨2307806, by rfl⟩ : syracuseStep 3077075 = 4615613) B4615613
theorem B2159609 : Blo 1439539 2159609 := bstep (se 2 (by rfl) ⟨809853, by rfl⟩ : syracuseStep 2159609 = 1619707) B1619707
theorem B3240953 : Blo 1439539 3240953 := bstep (se 2 (by rfl) ⟨1215357, by rfl⟩ : syracuseStep 3240953 = 2430715) B2430715
theorem B2733097 : Blo 1439539 2733097 := bstep (se 2 (by rfl) ⟨1024911, by rfl⟩ : syracuseStep 2733097 = 2049823) B2049823
theorem B6566953 : Blo 1439539 6566953 := bstep (se 2 (by rfl) ⟨2462607, by rfl⟩ : syracuseStep 6566953 = 4925215) B4925215
theorem B2159657 : Blo 1439539 2159657 := bstep (se 2 (by rfl) ⟨809871, by rfl⟩ : syracuseStep 2159657 = 1619743) B1619743
theorem B2159687 : Blo 1439539 2159687 := bstep (se 1 (by rfl) ⟨1619765, by rfl⟩ : syracuseStep 2159687 = 3239531) B3239531
theorem B3241043 : Blo 1439539 3241043 := bstep (se 1 (by rfl) ⟨2430782, by rfl⟩ : syracuseStep 3241043 = 4861565) B4861565
theorem B2430047 : Blo 1439539 2430047 := bstep (se 1 (by rfl) ⟨1822535, by rfl⟩ : syracuseStep 2430047 = 3645071) B3645071
theorem B2159867 : Blo 1439539 2159867 := bstep (se 1 (by rfl) ⟨1619900, by rfl⟩ : syracuseStep 2159867 = 3239801) B3239801
theorem B3241223 : Blo 1439539 3241223 := bstep (se 1 (by rfl) ⟨2430917, by rfl⟩ : syracuseStep 3241223 = 4861835) B4861835
theorem B12309803 : Blo 1439539 12309803 := bstep (se 1 (by rfl) ⟨9232352, by rfl⟩ : syracuseStep 12309803 = 18464705) B18464705
theorem B6567241 : Blo 1439539 6567241 := bstep (se 2 (by rfl) ⟨2462715, by rfl⟩ : syracuseStep 6567241 = 4925431) B4925431
theorem B47388037 : Blo 1439539 47388037 := bstep (se 4 (by rfl) ⟨4442628, by rfl⟩ : syracuseStep 47388037 = 8885257) B8885257
theorem B16414163 : Blo 1439539 16414163 := bstep (se 1 (by rfl) ⟨12310622, by rfl⟩ : syracuseStep 16414163 = 24621245) B24621245
theorem B2733659 : Blo 1439539 2733659 := bstep (se 1 (by rfl) ⟨2050244, by rfl⟩ : syracuseStep 2733659 = 4100489) B4100489
theorem B3241583 : Blo 1439539 3241583 := bstep (se 1 (by rfl) ⟨2431187, by rfl⟩ : syracuseStep 3241583 = 4862375) B4862375
theorem B9852617 : Blo 1439539 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B10934027 : Blo 1439539 10934027 := bstep (se 1 (by rfl) ⟨8200520, by rfl⟩ : syracuseStep 10934027 = 16401041) B16401041
theorem B1439559 : Blo 1439539 1439559 := bstep (se 1 (by rfl) ⟨1079669, by rfl⟩ : syracuseStep 1439559 = 2159339) B2159339
theorem B1439579 : Blo 1439539 1439579 := bstep (se 1 (by rfl) ⟨1079684, by rfl⟩ : syracuseStep 1439579 = 2159369) B2159369
theorem B1439647 : Blo 1439539 1439647 := bstep (se 1 (by rfl) ⟨1079735, by rfl⟩ : syracuseStep 1439647 = 2159471) B2159471
theorem B1439815 : Blo 1439539 1439815 := bstep (se 1 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 1439815 = 2159723) B2159723
theorem B1538119 : Blo 1439539 1538119 := bstep (se 1 (by rfl) ⟨1153589, by rfl⟩ : syracuseStep 1538119 = 2307179) B2307179
theorem B1439975 : Blo 1439539 1439975 := bstep (se 1 (by rfl) ⟨1079981, by rfl⟩ : syracuseStep 1439975 = 2159963) B2159963
theorem B12310865 : Blo 1439539 12310865 := bstep (se 2 (by rfl) ⟨4616574, by rfl⟩ : syracuseStep 12310865 = 9233149) B9233149
theorem B1440159 : Blo 1439539 1440159 := bstep (se 1 (by rfl) ⟨1080119, by rfl⟩ : syracuseStep 1440159 = 2160239) B2160239
theorem B1440207 : Blo 1439539 1440207 := bstep (se 1 (by rfl) ⟨1080155, by rfl⟩ : syracuseStep 1440207 = 2160311) B2160311
theorem B2161103 : Blo 1439539 2161103 := bstep (se 1 (by rfl) ⟨1620827, by rfl⟩ : syracuseStep 2161103 = 3241655) B3241655
theorem B3242447 : Blo 1439539 3242447 := bstep (se 1 (by rfl) ⟨2431835, by rfl⟩ : syracuseStep 3242447 = 4863671) B4863671
theorem B1440231 : Blo 1439539 1440231 := bstep (se 1 (by rfl) ⟨1080173, by rfl⟩ : syracuseStep 1440231 = 2160347) B2160347
theorem B2161193 : Blo 1439539 2161193 := bstep (se 2 (by rfl) ⟨810447, by rfl⟩ : syracuseStep 2161193 = 1620895) B1620895
theorem B3242537 : Blo 1439539 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B1440347 : Blo 1439539 1440347 := bstep (se 1 (by rfl) ⟨1080260, by rfl⟩ : syracuseStep 1440347 = 2160521) B2160521
theorem B1620571 : Blo 1439539 1620571 := bstep (se 1 (by rfl) ⟨1215428, by rfl⟩ : syracuseStep 1620571 = 2430857) B2430857
theorem B5470811 : Blo 1439539 5470811 := bstep (se 1 (by rfl) ⟨4103108, by rfl⟩ : syracuseStep 5470811 = 8206217) B8206217
theorem B8206991 : Blo 1439539 8206991 := bstep (se 1 (by rfl) ⟨6155243, by rfl⟩ : syracuseStep 8206991 = 12310487) B12310487
theorem B1440415 : Blo 1439539 1440415 := bstep (se 1 (by rfl) ⟨1080311, by rfl⟩ : syracuseStep 1440415 = 2160623) B2160623
theorem B2161385 : Blo 1439539 2161385 := bstep (se 2 (by rfl) ⟨810519, by rfl⟩ : syracuseStep 2161385 = 1621039) B1621039
theorem B1440583 : Blo 1439539 1440583 := bstep (se 1 (by rfl) ⟨1080437, by rfl⟩ : syracuseStep 1440583 = 2160875) B2160875
theorem B1440623 : Blo 1439539 1440623 := bstep (se 1 (by rfl) ⟨1080467, by rfl⟩ : syracuseStep 1440623 = 2160935) B2160935
theorem B1620859 : Blo 1439539 1620859 := bstep (se 1 (by rfl) ⟨1215644, by rfl⟩ : syracuseStep 1620859 = 2431289) B2431289
theorem B1440679 : Blo 1439539 1440679 := bstep (se 1 (by rfl) ⟨1080509, by rfl⟩ : syracuseStep 1440679 = 2161019) B2161019
theorem B35068879 : Blo 1439539 35068879 := bstep (se 1 (by rfl) ⟨26301659, by rfl⟩ : syracuseStep 35068879 = 52603319) B52603319
theorem B1440859 : Blo 1439539 1440859 := bstep (se 1 (by rfl) ⟨1080644, by rfl⟩ : syracuseStep 1440859 = 2161289) B2161289
theorem B2161769 : Blo 1439539 2161769 := bstep (se 2 (by rfl) ⟨810663, by rfl⟩ : syracuseStep 2161769 = 1621327) B1621327
theorem B3243113 : Blo 1439539 3243113 := bstep (se 2 (by rfl) ⟨1216167, by rfl⟩ : syracuseStep 3243113 = 2432335) B2432335
theorem B4865129 : Blo 1439539 4865129 := bstep (se 2 (by rfl) ⟨1824423, by rfl⟩ : syracuseStep 4865129 = 3648847) B3648847
theorem B14032019 : Blo 1439539 14032019 := bstep (se 1 (by rfl) ⟨10524014, by rfl⟩ : syracuseStep 14032019 = 21048029) B21048029
theorem B1440975 : Blo 1439539 1440975 := bstep (se 1 (by rfl) ⟨1080731, by rfl⟩ : syracuseStep 1440975 = 2161463) B2161463
theorem B2432207 : Blo 1439539 2432207 := bstep (se 1 (by rfl) ⟨1824155, by rfl⟩ : syracuseStep 2432207 = 3648311) B3648311
theorem B1440999 : Blo 1439539 1440999 := bstep (se 1 (by rfl) ⟨1080749, by rfl⟩ : syracuseStep 1440999 = 2161499) B2161499
theorem B2161895 : Blo 1439539 2161895 := bstep (se 1 (by rfl) ⟨1621421, by rfl⟩ : syracuseStep 2161895 = 3242843) B3242843
theorem B3243239 : Blo 1439539 3243239 := bstep (se 1 (by rfl) ⟨2432429, by rfl⟩ : syracuseStep 3243239 = 4864859) B4864859
theorem B10943747 : Blo 1439539 10943747 := bstep (se 1 (by rfl) ⟨8207810, by rfl⟩ : syracuseStep 10943747 = 16415621) B16415621
theorem B1441095 : Blo 1439539 1441095 := bstep (se 1 (by rfl) ⟨1080821, by rfl⟩ : syracuseStep 1441095 = 2161643) B2161643
theorem B41540971 : Blo 1439539 41540971 := bstep (se 1 (by rfl) ⟨31155728, by rfl⟩ : syracuseStep 41540971 = 62311457) B62311457
theorem B5193083 : Blo 1439539 5193083 := bstep (se 1 (by rfl) ⟨3894812, by rfl⟩ : syracuseStep 5193083 = 7789625) B7789625
theorem B1441231 : Blo 1439539 1441231 := bstep (se 1 (by rfl) ⟨1080923, by rfl⟩ : syracuseStep 1441231 = 2161847) B2161847
theorem B118251089 : Blo 1439539 118251089 := bstep (se 2 (by rfl) ⟨44344158, by rfl⟩ : syracuseStep 118251089 = 88688317) B88688317
theorem B1441391 : Blo 1439539 1441391 := bstep (se 1 (by rfl) ⟨1081043, by rfl⟩ : syracuseStep 1441391 = 2162087) B2162087
theorem B1621615 : Blo 1439539 1621615 := bstep (se 1 (by rfl) ⟨1216211, by rfl⟩ : syracuseStep 1621615 = 2432423) B2432423
theorem B10935971 : Blo 1439539 10935971 := bstep (se 1 (by rfl) ⟨8201978, by rfl⟩ : syracuseStep 10935971 = 16403957) B16403957
theorem B1441447 : Blo 1439539 1441447 := bstep (se 1 (by rfl) ⟨1081085, by rfl⟩ : syracuseStep 1441447 = 2162171) B2162171
theorem B1621723 : Blo 1439539 1621723 := bstep (se 1 (by rfl) ⟨1216292, by rfl⟩ : syracuseStep 1621723 = 2432585) B2432585
theorem B1441511 : Blo 1439539 1441511 := bstep (se 1 (by rfl) ⟨1081133, by rfl⟩ : syracuseStep 1441511 = 2162267) B2162267
theorem B2220095 : Blo 1439539 2220095 := bstep (se 1 (by rfl) ⟨1665071, by rfl⟩ : syracuseStep 2220095 = 3330143) B3330143
theorem B2736271 : Blo 1439539 2736271 := bstep (se 1 (by rfl) ⟨2052203, by rfl⟩ : syracuseStep 2736271 = 4104407) B4104407
theorem B11092447 : Blo 1439539 11092447 := bstep (se 1 (by rfl) ⟨8319335, by rfl⟩ : syracuseStep 11092447 = 16638671) B16638671
theorem B76071899 : Blo 1439539 76071899 := bstep (se 1 (by rfl) ⟨57053924, by rfl⟩ : syracuseStep 76071899 = 114107849) B114107849
theorem B7292267 : Blo 1439539 7292267 := bstep (se 1 (by rfl) ⟨5469200, by rfl⟩ : syracuseStep 7292267 = 10938401) B10938401
theorem B3647207 : Blo 1439539 3647207 := bstep (se 1 (by rfl) ⟨2735405, by rfl⟩ : syracuseStep 3647207 = 5470811) B5470811
theorem B55387961 : Blo 1439539 55387961 := bstep (se 2 (by rfl) ⟨20770485, by rfl⟩ : syracuseStep 55387961 = 41540971) B41540971
theorem B91146131 : Blo 1439539 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B78834059 : Blo 1439539 78834059 := bstep (se 1 (by rfl) ⟨59125544, by rfl⟩ : syracuseStep 78834059 = 118251089) B118251089
theorem B6154697 : Blo 1439539 6154697 := bstep (se 2 (by rfl) ⟨2308011, by rfl⟩ : syracuseStep 6154697 = 4616023) B4616023
theorem B14780891 : Blo 1439539 14780891 := bstep (se 1 (by rfl) ⟨11085668, by rfl⟩ : syracuseStep 14780891 = 22171337) B22171337
theorem B10521103 : Blo 1439539 10521103 := bstep (se 1 (by rfl) ⟨7890827, by rfl⟩ : syracuseStep 10521103 = 15781655) B15781655
theorem B10390319 : Blo 1439539 10390319 := bstep (se 1 (by rfl) ⟨7792739, by rfl⟩ : syracuseStep 10390319 = 15585479) B15585479
theorem B202181453 : Blo 1439539 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B4860755 : Blo 1439539 4860755 := bstep (se 1 (by rfl) ⟨3645566, by rfl⟩ : syracuseStep 4860755 = 7291133) B7291133
theorem B1731451 : Blo 1439539 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B7392235 : Blo 1439539 7392235 := bstep (se 1 (by rfl) ⟨5544176, by rfl⟩ : syracuseStep 7392235 = 11088353) B11088353
theorem B6155297 : Blo 1439539 6155297 := bstep (se 2 (by rfl) ⟨2308236, by rfl⟩ : syracuseStep 6155297 = 4616473) B4616473
theorem B8203301 : Blo 1439539 8203301 := bstep (se 4 (by rfl) ⟨769059, by rfl⟩ : syracuseStep 8203301 = 1538119) B1538119
theorem B7785629 : Blo 1439539 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B7294211 : Blo 1439539 7294211 := bstep (se 1 (by rfl) ⟨5470658, by rfl⟩ : syracuseStep 7294211 = 10941317) B10941317
theorem B35067725 : Blo 1439539 35067725 := bstep (se 3 (by rfl) ⟨6575198, by rfl⟩ : syracuseStep 35067725 = 13150397) B13150397
theorem B6663505 : Blo 1439539 6663505 := bstep (se 2 (by rfl) ⟨2498814, by rfl⟩ : syracuseStep 6663505 = 4997629) B4997629
theorem B4861295 : Blo 1439539 4861295 := bstep (se 1 (by rfl) ⟨3645971, by rfl⟩ : syracuseStep 4861295 = 7291943) B7291943
theorem B13848221 : Blo 1439539 13848221 := bstep (se 3 (by rfl) ⟨2596541, by rfl⟩ : syracuseStep 13848221 = 5193083) B5193083
theorem B1822439 : Blo 1439539 1822439 := bstep (se 1 (by rfl) ⟨1366829, by rfl⟩ : syracuseStep 1822439 = 2733659) B2733659
theorem B5467895 : Blo 1439539 5467895 := bstep (se 1 (by rfl) ⟨4100921, by rfl⟩ : syracuseStep 5467895 = 8201843) B8201843
theorem B6926111 : Blo 1439539 6926111 := bstep (se 1 (by rfl) ⟨5194583, by rfl⟩ : syracuseStep 6926111 = 10389167) B10389167
theorem B4157311 : Blo 1439539 4157311 := bstep (se 1 (by rfl) ⟨3117983, by rfl⟩ : syracuseStep 4157311 = 6235967) B6235967
theorem B18452609 : Blo 1439539 18452609 := bstep (se 2 (by rfl) ⟨6919728, by rfl⟩ : syracuseStep 18452609 = 13839457) B13839457
theorem B3240143 : Blo 1439539 3240143 := bstep (se 1 (by rfl) ⟨2430107, by rfl⟩ : syracuseStep 3240143 = 4860215) B4860215
theorem B2339113 : Blo 1439539 2339113 := bstep (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) B1754335
theorem B118223479 : Blo 1439539 118223479 := bstep (se 1 (by rfl) ⟨88667609, by rfl⟩ : syracuseStep 118223479 = 177335219) B177335219
theorem B4862699 : Blo 1439539 4862699 := bstep (se 1 (by rfl) ⟨3647024, by rfl⟩ : syracuseStep 4862699 = 7294049) B7294049
theorem B2159387 : Blo 1439539 2159387 := bstep (se 1 (by rfl) ⟨1619540, by rfl⟩ : syracuseStep 2159387 = 3239081) B3239081
theorem B7295831 : Blo 1439539 7295831 := bstep (se 1 (by rfl) ⟨5471873, by rfl⟩ : syracuseStep 7295831 = 10943747) B10943747
theorem B2159663 : Blo 1439539 2159663 := bstep (se 1 (by rfl) ⟨1619747, by rfl⟩ : syracuseStep 2159663 = 3239495) B3239495
theorem B2159711 : Blo 1439539 2159711 := bstep (se 1 (by rfl) ⟨1619783, by rfl⟩ : syracuseStep 2159711 = 3239567) B3239567
theorem B2159771 : Blo 1439539 2159771 := bstep (se 1 (by rfl) ⟨1619828, by rfl⟩ : syracuseStep 2159771 = 3239657) B3239657
theorem B3241115 : Blo 1439539 3241115 := bstep (se 1 (by rfl) ⟨2430836, by rfl⟩ : syracuseStep 3241115 = 4861673) B4861673
theorem B2159783 : Blo 1439539 2159783 := bstep (se 1 (by rfl) ⟨1619837, by rfl⟩ : syracuseStep 2159783 = 3239675) B3239675
theorem B2430121 : Blo 1439539 2430121 := bstep (se 2 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 2430121 = 1822591) B1822591
theorem B8205533 : Blo 1439539 8205533 := bstep (se 3 (by rfl) ⟨1538537, by rfl⟩ : syracuseStep 8205533 = 3077075) B3077075
theorem B4863239 : Blo 1439539 4863239 := bstep (se 1 (by rfl) ⟨3647429, by rfl⟩ : syracuseStep 4863239 = 7294859) B7294859
theorem B2733439 : Blo 1439539 2733439 := bstep (se 1 (by rfl) ⟨2050079, by rfl⟩ : syracuseStep 2733439 = 4100159) B4100159
theorem B7788113 : Blo 1439539 7788113 := bstep (se 2 (by rfl) ⟨2920542, by rfl⟩ : syracuseStep 7788113 = 5841085) B5841085
theorem B4101799 : Blo 1439539 4101799 := bstep (se 1 (by rfl) ⟨3076349, by rfl⟩ : syracuseStep 4101799 = 6152699) B6152699
theorem B2160455 : Blo 1439539 2160455 := bstep (se 1 (by rfl) ⟨1620341, by rfl⟩ : syracuseStep 2160455 = 3240683) B3240683
theorem B1439615 : Blo 1439539 1439615 := bstep (se 1 (by rfl) ⟨1079711, by rfl⟩ : syracuseStep 1439615 = 2159423) B2159423
theorem B1439711 : Blo 1439539 1439711 := bstep (se 1 (by rfl) ⟨1079783, by rfl⟩ : syracuseStep 1439711 = 2159567) B2159567
theorem B1439739 : Blo 1439539 1439739 := bstep (se 1 (by rfl) ⟨1079804, by rfl⟩ : syracuseStep 1439739 = 2159609) B2159609
theorem B2160635 : Blo 1439539 2160635 := bstep (se 1 (by rfl) ⟨1620476, by rfl⟩ : syracuseStep 2160635 = 3240953) B3240953
theorem B1439771 : Blo 1439539 1439771 := bstep (se 1 (by rfl) ⟨1079828, by rfl⟩ : syracuseStep 1439771 = 2159657) B2159657
theorem B1439791 : Blo 1439539 1439791 := bstep (se 1 (by rfl) ⟨1079843, by rfl⟩ : syracuseStep 1439791 = 2159687) B2159687
theorem B2160695 : Blo 1439539 2160695 := bstep (se 1 (by rfl) ⟨1620521, by rfl⟩ : syracuseStep 2160695 = 3241043) B3241043
theorem B1620031 : Blo 1439539 1620031 := bstep (se 1 (by rfl) ⟨1215023, by rfl⟩ : syracuseStep 1620031 = 2430047) B2430047
theorem B2160761 : Blo 1439539 2160761 := bstep (se 2 (by rfl) ⟨810285, by rfl⟩ : syracuseStep 2160761 = 1620571) B1620571
theorem B1439911 : Blo 1439539 1439911 := bstep (se 1 (by rfl) ⟨1079933, by rfl⟩ : syracuseStep 1439911 = 2159867) B2159867
theorem B2160815 : Blo 1439539 2160815 := bstep (se 1 (by rfl) ⟨1620611, by rfl⟩ : syracuseStep 2160815 = 3241223) B3241223
theorem B8206535 : Blo 1439539 8206535 := bstep (se 1 (by rfl) ⟨6154901, by rfl⟩ : syracuseStep 8206535 = 12309803) B12309803
theorem B10942775 : Blo 1439539 10942775 := bstep (se 1 (by rfl) ⟨8207081, by rfl⟩ : syracuseStep 10942775 = 16414163) B16414163
theorem B2161055 : Blo 1439539 2161055 := bstep (se 1 (by rfl) ⟨1620791, by rfl⟩ : syracuseStep 2161055 = 3241583) B3241583
theorem B6568411 : Blo 1439539 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B2161145 : Blo 1439539 2161145 := bstep (se 2 (by rfl) ⟨810429, by rfl⟩ : syracuseStep 2161145 = 1620859) B1620859
theorem B7289351 : Blo 1439539 7289351 := bstep (se 1 (by rfl) ⟨5467013, by rfl⟩ : syracuseStep 7289351 = 10934027) B10934027
theorem B2431579 : Blo 1439539 2431579 := bstep (se 1 (by rfl) ⟨1823684, by rfl⟩ : syracuseStep 2431579 = 3647369) B3647369
theorem B46758505 : Blo 1439539 46758505 := bstep (se 2 (by rfl) ⟨17534439, by rfl⟩ : syracuseStep 46758505 = 35068879) B35068879
theorem B3644129 : Blo 1439539 3644129 := bstep (se 2 (by rfl) ⟨1366548, by rfl⟩ : syracuseStep 3644129 = 2733097) B2733097
theorem B8755937 : Blo 1439539 8755937 := bstep (se 2 (by rfl) ⟨3283476, by rfl⟩ : syracuseStep 8755937 = 6566953) B6566953
theorem B6150923 : Blo 1439539 6150923 := bstep (se 1 (by rfl) ⟨4613192, by rfl⟩ : syracuseStep 6150923 = 9226385) B9226385
theorem B8207243 : Blo 1439539 8207243 := bstep (se 1 (by rfl) ⟨6155432, by rfl⟩ : syracuseStep 8207243 = 12310865) B12310865
theorem B1440735 : Blo 1439539 1440735 := bstep (se 1 (by rfl) ⟨1080551, by rfl⟩ : syracuseStep 1440735 = 2161103) B2161103
theorem B2161631 : Blo 1439539 2161631 := bstep (se 1 (by rfl) ⟨1621223, by rfl⟩ : syracuseStep 2161631 = 3242447) B3242447
theorem B1440795 : Blo 1439539 1440795 := bstep (se 1 (by rfl) ⟨1080596, by rfl⟩ : syracuseStep 1440795 = 2161193) B2161193
theorem B2161691 : Blo 1439539 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B5471327 : Blo 1439539 5471327 := bstep (se 1 (by rfl) ⟨4103495, by rfl⟩ : syracuseStep 5471327 = 8206991) B8206991
theorem B8756321 : Blo 1439539 8756321 := bstep (se 2 (by rfl) ⟨3283620, by rfl⟩ : syracuseStep 8756321 = 6567241) B6567241
theorem B1440923 : Blo 1439539 1440923 := bstep (se 1 (by rfl) ⟨1080692, by rfl⟩ : syracuseStep 1440923 = 2161385) B2161385
theorem B63184049 : Blo 1439539 63184049 := bstep (se 2 (by rfl) ⟨23694018, by rfl⟩ : syracuseStep 63184049 = 47388037) B47388037
theorem B1441179 : Blo 1439539 1441179 := bstep (se 1 (by rfl) ⟨1080884, by rfl⟩ : syracuseStep 1441179 = 2161769) B2161769
theorem B2162075 : Blo 1439539 2162075 := bstep (se 1 (by rfl) ⟨1621556, by rfl⟩ : syracuseStep 2162075 = 3243113) B3243113
theorem B3243419 : Blo 1439539 3243419 := bstep (se 1 (by rfl) ⟨2432564, by rfl⟩ : syracuseStep 3243419 = 4865129) B4865129
theorem B9354679 : Blo 1439539 9354679 := bstep (se 1 (by rfl) ⟨7016009, by rfl⟩ : syracuseStep 9354679 = 14032019) B14032019
theorem B1621471 : Blo 1439539 1621471 := bstep (se 1 (by rfl) ⟨1216103, by rfl⟩ : syracuseStep 1621471 = 2432207) B2432207
theorem B2162153 : Blo 1439539 2162153 := bstep (se 2 (by rfl) ⟨810807, by rfl⟩ : syracuseStep 2162153 = 1621615) B1621615
theorem B1441263 : Blo 1439539 1441263 := bstep (se 1 (by rfl) ⟨1080947, by rfl⟩ : syracuseStep 1441263 = 2161895) B2161895
theorem B2162159 : Blo 1439539 2162159 := bstep (se 1 (by rfl) ⟨1621619, by rfl⟩ : syracuseStep 2162159 = 3243239) B3243239
theorem B2162297 : Blo 1439539 2162297 := bstep (se 2 (by rfl) ⟨810861, by rfl⟩ : syracuseStep 2162297 = 1621723) B1621723
theorem B12312263 : Blo 1439539 12312263 := bstep (se 1 (by rfl) ⟨9234197, by rfl⟩ : syracuseStep 12312263 = 18468395) B18468395
theorem B16408331 : Blo 1439539 16408331 := bstep (se 1 (by rfl) ⟨12306248, by rfl⟩ : syracuseStep 16408331 = 24612497) B24612497
theorem B7290647 : Blo 1439539 7290647 := bstep (se 1 (by rfl) ⟨5467985, by rfl⟩ : syracuseStep 7290647 = 10935971) B10935971
theorem B8757881 : Blo 1439539 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B157631305 : Blo 1439539 157631305 := bstep (se 2 (by rfl) ⟨59111739, by rfl⟩ : syracuseStep 157631305 = 118223479) B118223479
theorem B9856313 : Blo 1439539 9856313 := bstep (se 2 (by rfl) ⟨3696117, by rfl⟩ : syracuseStep 9856313 = 7392235) B7392235
theorem B4859567 : Blo 1439539 4859567 := bstep (se 1 (by rfl) ⟨3644675, by rfl⟩ : syracuseStep 4859567 = 7289351) B7289351
theorem B4859837 : Blo 1439539 4859837 := bstep (se 3 (by rfl) ⟨911219, by rfl⟩ : syracuseStep 4859837 = 1822439) B1822439
theorem B3647551 : Blo 1439539 3647551 := bstep (se 1 (by rfl) ⟨2735663, by rfl⟩ : syracuseStep 3647551 = 5471327) B5471327
theorem B49891621 : Blo 1439539 49891621 := bstep (se 4 (by rfl) ⟨4677339, by rfl⟩ : syracuseStep 49891621 = 9354679) B9354679
theorem B10938887 : Blo 1439539 10938887 := bstep (se 1 (by rfl) ⟨8204165, by rfl⟩ : syracuseStep 10938887 = 16408331) B16408331
theorem B4860431 : Blo 1439539 4860431 := bstep (se 1 (by rfl) ⟨3645323, by rfl⟩ : syracuseStep 4860431 = 7290647) B7290647
theorem B3648361 : Blo 1439539 3648361 := bstep (se 2 (by rfl) ⟨1368135, by rfl⟩ : syracuseStep 3648361 = 2736271) B2736271
theorem B23350189 : Blo 1439539 23350189 := bstep (se 3 (by rfl) ⟨4378160, by rfl⟩ : syracuseStep 23350189 = 8756321) B8756321
theorem B14028137 : Blo 1439539 14028137 := bstep (se 2 (by rfl) ⟨5260551, by rfl⟩ : syracuseStep 14028137 = 10521103) B10521103
theorem B62344673 : Blo 1439539 62344673 := bstep (se 2 (by rfl) ⟨23379252, by rfl⟩ : syracuseStep 62344673 = 46758505) B46758505
theorem B4861511 : Blo 1439539 4861511 := bstep (se 1 (by rfl) ⟨3646133, by rfl⟩ : syracuseStep 4861511 = 7292267) B7292267
theorem B36925307 : Blo 1439539 36925307 := bstep (se 1 (by rfl) ⟨27693980, by rfl⟩ : syracuseStep 36925307 = 55387961) B55387961
theorem B39415709 : Blo 1439539 39415709 := bstep (se 3 (by rfl) ⟨7390445, by rfl⟩ : syracuseStep 39415709 = 14780891) B14780891
theorem B60764087 : Blo 1439539 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B7295183 : Blo 1439539 7295183 := bstep (se 1 (by rfl) ⟨5471387, by rfl⟩ : syracuseStep 7295183 = 10942775) B10942775
theorem B3240161 : Blo 1439539 3240161 := bstep (se 2 (by rfl) ⟨1215060, by rfl⟩ : syracuseStep 3240161 = 2430121) B2430121
theorem B52556039 : Blo 1439539 52556039 := bstep (se 1 (by rfl) ⟨39417029, by rfl⟩ : syracuseStep 52556039 = 78834059) B78834059
theorem B8884673 : Blo 1439539 8884673 := bstep (se 2 (by rfl) ⟨3331752, by rfl⟩ : syracuseStep 8884673 = 6663505) B6663505
theorem B2429419 : Blo 1439539 2429419 := bstep (se 1 (by rfl) ⟨1822064, by rfl⟩ : syracuseStep 2429419 = 3644129) B3644129
theorem B5837291 : Blo 1439539 5837291 := bstep (se 1 (by rfl) ⟨4377968, by rfl⟩ : syracuseStep 5837291 = 8755937) B8755937
theorem B4100615 : Blo 1439539 4100615 := bstep (se 1 (by rfl) ⟨3075461, by rfl⟩ : syracuseStep 4100615 = 6150923) B6150923
theorem B6926879 : Blo 1439539 6926879 := bstep (se 1 (by rfl) ⟨5195159, by rfl⟩ : syracuseStep 6926879 = 10390319) B10390319
theorem B134787635 : Blo 1439539 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B3240503 : Blo 1439539 3240503 := bstep (se 1 (by rfl) ⟨2430377, by rfl⟩ : syracuseStep 3240503 = 4860755) B4860755
theorem B5468867 : Blo 1439539 5468867 := bstep (se 1 (by rfl) ⟨4101650, by rfl⟩ : syracuseStep 5468867 = 8203301) B8203301
theorem B5190419 : Blo 1439539 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B4862807 : Blo 1439539 4862807 := bstep (se 1 (by rfl) ⟨3647105, by rfl⟩ : syracuseStep 4862807 = 7294211) B7294211
theorem B5469065 : Blo 1439539 5469065 := bstep (se 2 (by rfl) ⟨2050899, by rfl⟩ : syracuseStep 5469065 = 4101799) B4101799
theorem B3240863 : Blo 1439539 3240863 := bstep (se 1 (by rfl) ⟨2430647, by rfl⟩ : syracuseStep 3240863 = 4861295) B4861295
theorem B59159717 : Blo 1439539 59159717 := bstep (se 4 (by rfl) ⟨5546223, by rfl⟩ : syracuseStep 59159717 = 11092447) B11092447
theorem B5543081 : Blo 1439539 5543081 := bstep (se 2 (by rfl) ⟨2078655, by rfl⟩ : syracuseStep 5543081 = 4157311) B4157311
theorem B4617407 : Blo 1439539 4617407 := bstep (se 1 (by rfl) ⟨3463055, by rfl⟩ : syracuseStep 4617407 = 6926111) B6926111
theorem B2160041 : Blo 1439539 2160041 := bstep (se 2 (by rfl) ⟨810015, by rfl⟩ : syracuseStep 2160041 = 1620031) B1620031
theorem B12301739 : Blo 1439539 12301739 := bstep (se 1 (by rfl) ⟨9226304, by rfl⟩ : syracuseStep 12301739 = 18452609) B18452609
theorem B2160095 : Blo 1439539 2160095 := bstep (se 1 (by rfl) ⟨1620071, by rfl⟩ : syracuseStep 2160095 = 3240143) B3240143
theorem B5920253 : Blo 1439539 5920253 := bstep (se 3 (by rfl) ⟨1110047, by rfl⟩ : syracuseStep 5920253 = 2220095) B2220095
theorem B3118817 : Blo 1439539 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B3241799 : Blo 1439539 3241799 := bstep (se 1 (by rfl) ⟨2431349, by rfl⟩ : syracuseStep 3241799 = 4862699) B4862699
theorem B1439591 : Blo 1439539 1439591 := bstep (se 1 (by rfl) ⟨1079693, by rfl⟩ : syracuseStep 1439591 = 2159387) B2159387
theorem B4863887 : Blo 1439539 4863887 := bstep (se 1 (by rfl) ⟨3647915, by rfl⟩ : syracuseStep 4863887 = 7295831) B7295831
theorem B50714599 : Blo 1439539 50714599 := bstep (se 1 (by rfl) ⟨38035949, by rfl⟩ : syracuseStep 50714599 = 76071899) B76071899
theorem B1439775 : Blo 1439539 1439775 := bstep (se 1 (by rfl) ⟨1079831, by rfl⟩ : syracuseStep 1439775 = 2159663) B2159663
theorem B1439807 : Blo 1439539 1439807 := bstep (se 1 (by rfl) ⟨1079855, by rfl⟩ : syracuseStep 1439807 = 2159711) B2159711
theorem B1439847 : Blo 1439539 1439847 := bstep (se 1 (by rfl) ⟨1079885, by rfl⟩ : syracuseStep 1439847 = 2159771) B2159771
theorem B2160743 : Blo 1439539 2160743 := bstep (se 1 (by rfl) ⟨1620557, by rfl⟩ : syracuseStep 2160743 = 3241115) B3241115
theorem B1439855 : Blo 1439539 1439855 := bstep (se 1 (by rfl) ⟨1079891, by rfl⟩ : syracuseStep 1439855 = 2159783) B2159783
theorem B3242105 : Blo 1439539 3242105 := bstep (se 2 (by rfl) ⟨1215789, by rfl⟩ : syracuseStep 3242105 = 2431579) B2431579
theorem B5470355 : Blo 1439539 5470355 := bstep (se 1 (by rfl) ⟨4102766, by rfl⟩ : syracuseStep 5470355 = 8205533) B8205533
theorem B3242159 : Blo 1439539 3242159 := bstep (se 1 (by rfl) ⟨2431619, by rfl⟩ : syracuseStep 3242159 = 4863239) B4863239
theorem B5192075 : Blo 1439539 5192075 := bstep (se 1 (by rfl) ⟨3894056, by rfl⟩ : syracuseStep 5192075 = 7788113) B7788113
theorem B2431471 : Blo 1439539 2431471 := bstep (se 1 (by rfl) ⟨1823603, by rfl⟩ : syracuseStep 2431471 = 3647207) B3647207
theorem B2308601 : Blo 1439539 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B1440303 : Blo 1439539 1440303 := bstep (se 1 (by rfl) ⟨1080227, by rfl⟩ : syracuseStep 1440303 = 2160455) B2160455
theorem B23378483 : Blo 1439539 23378483 := bstep (se 1 (by rfl) ⟨17533862, by rfl⟩ : syracuseStep 23378483 = 35067725) B35067725
theorem B1440423 : Blo 1439539 1440423 := bstep (se 1 (by rfl) ⟨1080317, by rfl⟩ : syracuseStep 1440423 = 2160635) B2160635
theorem B1440463 : Blo 1439539 1440463 := bstep (se 1 (by rfl) ⟨1080347, by rfl⟩ : syracuseStep 1440463 = 2160695) B2160695
theorem B1440507 : Blo 1439539 1440507 := bstep (se 1 (by rfl) ⟨1080380, by rfl⟩ : syracuseStep 1440507 = 2160761) B2160761
theorem B1440543 : Blo 1439539 1440543 := bstep (se 1 (by rfl) ⟨1080407, by rfl⟩ : syracuseStep 1440543 = 2160815) B2160815
theorem B5471023 : Blo 1439539 5471023 := bstep (se 1 (by rfl) ⟨4103267, by rfl⟩ : syracuseStep 5471023 = 8206535) B8206535
theorem B1440703 : Blo 1439539 1440703 := bstep (se 1 (by rfl) ⟨1080527, by rfl⟩ : syracuseStep 1440703 = 2161055) B2161055
theorem B4103131 : Blo 1439539 4103131 := bstep (se 1 (by rfl) ⟨3077348, by rfl⟩ : syracuseStep 4103131 = 6154697) B6154697
theorem B1440763 : Blo 1439539 1440763 := bstep (se 1 (by rfl) ⟨1080572, by rfl⟩ : syracuseStep 1440763 = 2161145) B2161145
theorem B3644585 : Blo 1439539 3644585 := bstep (se 2 (by rfl) ⟨1366719, by rfl⟩ : syracuseStep 3644585 = 2733439) B2733439
theorem B5471495 : Blo 1439539 5471495 := bstep (se 1 (by rfl) ⟨4103621, by rfl⟩ : syracuseStep 5471495 = 8207243) B8207243
theorem B2161961 : Blo 1439539 2161961 := bstep (se 2 (by rfl) ⟨810735, by rfl⟩ : syracuseStep 2161961 = 1621471) B1621471
theorem B1441087 : Blo 1439539 1441087 := bstep (se 1 (by rfl) ⟨1080815, by rfl⟩ : syracuseStep 1441087 = 2161631) B2161631
theorem B1441127 : Blo 1439539 1441127 := bstep (se 1 (by rfl) ⟨1080845, by rfl⟩ : syracuseStep 1441127 = 2161691) B2161691
theorem B4103531 : Blo 1439539 4103531 := bstep (se 1 (by rfl) ⟨3077648, by rfl⟩ : syracuseStep 4103531 = 6155297) B6155297
theorem B42122699 : Blo 1439539 42122699 := bstep (se 1 (by rfl) ⟨31592024, by rfl⟩ : syracuseStep 42122699 = 63184049) B63184049
theorem B1441383 : Blo 1439539 1441383 := bstep (se 1 (by rfl) ⟨1081037, by rfl⟩ : syracuseStep 1441383 = 2162075) B2162075
theorem B2162279 : Blo 1439539 2162279 := bstep (se 1 (by rfl) ⟨1621709, by rfl⟩ : syracuseStep 2162279 = 3243419) B3243419
theorem B1441435 : Blo 1439539 1441435 := bstep (se 1 (by rfl) ⟨1081076, by rfl⟩ : syracuseStep 1441435 = 2162153) B2162153
theorem B1441439 : Blo 1439539 1441439 := bstep (se 1 (by rfl) ⟨1081079, by rfl⟩ : syracuseStep 1441439 = 2162159) B2162159
theorem B1441531 : Blo 1439539 1441531 := bstep (se 1 (by rfl) ⟨1081148, by rfl⟩ : syracuseStep 1441531 = 2162297) B2162297
theorem B9232147 : Blo 1439539 9232147 := bstep (se 1 (by rfl) ⟨6924110, by rfl⟩ : syracuseStep 9232147 = 13848221) B13848221
theorem B8208175 : Blo 1439539 8208175 := bstep (se 1 (by rfl) ⟨6156131, by rfl⟩ : syracuseStep 8208175 = 12312263) B12312263
theorem B3645263 : Blo 1439539 3645263 := bstep (se 1 (by rfl) ⟨2733947, by rfl⟩ : syracuseStep 3645263 = 5467895) B5467895
theorem B35037359 : Blo 1439539 35037359 := bstep (se 1 (by rfl) ⟨26278019, by rfl⟩ : syracuseStep 35037359 = 52556039) B52556039
theorem B5923115 : Blo 1439539 5923115 := bstep (se 1 (by rfl) ⟨4442336, by rfl⟩ : syracuseStep 5923115 = 8884673) B8884673
theorem B3891527 : Blo 1439539 3891527 := bstep (se 1 (by rfl) ⟨2918645, by rfl⟩ : syracuseStep 3891527 = 5837291) B5837291
theorem B89858423 : Blo 1439539 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B3645911 : Blo 1439539 3645911 := bstep (se 1 (by rfl) ⟨2734433, by rfl⟩ : syracuseStep 3645911 = 5468867) B5468867
theorem B3646043 : Blo 1439539 3646043 := bstep (se 1 (by rfl) ⟨2734532, by rfl⟩ : syracuseStep 3646043 = 5469065) B5469065
theorem B3695387 : Blo 1439539 3695387 := bstep (se 1 (by rfl) ⟨2771540, by rfl⟩ : syracuseStep 3695387 = 5543081) B5543081
theorem B6570875 : Blo 1439539 6570875 := bstep (se 1 (by rfl) ⟨4928156, by rfl⟩ : syracuseStep 6570875 = 9856313) B9856313
theorem B8201159 : Blo 1439539 8201159 := bstep (se 1 (by rfl) ⟨6150869, by rfl⟩ : syracuseStep 8201159 = 12301739) B12301739
theorem B210175073 : Blo 1439539 210175073 := bstep (se 2 (by rfl) ⟨78815652, by rfl⟩ : syracuseStep 210175073 = 157631305) B157631305
theorem B3646903 : Blo 1439539 3646903 := bstep (se 1 (by rfl) ⟨2735177, by rfl⟩ : syracuseStep 3646903 = 5470355) B5470355
theorem B7292591 : Blo 1439539 7292591 := bstep (se 1 (by rfl) ⟨5469443, by rfl⟩ : syracuseStep 7292591 = 10938887) B10938887
theorem B3647663 : Blo 1439539 3647663 := bstep (se 1 (by rfl) ⟨2735747, by rfl⟩ : syracuseStep 3647663 = 5471495) B5471495
theorem B67619465 : Blo 1439539 67619465 := bstep (se 2 (by rfl) ⟨25357299, by rfl⟩ : syracuseStep 67619465 = 50714599) B50714599
theorem B66522161 : Blo 1439539 66522161 := bstep (se 2 (by rfl) ⟨24945810, by rfl⟩ : syracuseStep 66522161 = 49891621) B49891621
theorem B3460279 : Blo 1439539 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B3239225 : Blo 1439539 3239225 := bstep (se 2 (by rfl) ⟨1214709, by rfl⟩ : syracuseStep 3239225 = 2429419) B2429419
theorem B39439811 : Blo 1439539 39439811 := bstep (se 1 (by rfl) ⟨29579858, by rfl⟩ : syracuseStep 39439811 = 59159717) B59159717
theorem B7294697 : Blo 1439539 7294697 := bstep (se 2 (by rfl) ⟨2735511, by rfl⟩ : syracuseStep 7294697 = 5471023) B5471023
theorem B3239711 : Blo 1439539 3239711 := bstep (se 1 (by rfl) ⟨2429783, by rfl⟩ : syracuseStep 3239711 = 4859567) B4859567
theorem B31133585 : Blo 1439539 31133585 := bstep (se 2 (by rfl) ⟨11675094, by rfl⟩ : syracuseStep 31133585 = 23350189) B23350189
theorem B3239891 : Blo 1439539 3239891 := bstep (se 1 (by rfl) ⟨2429918, by rfl⟩ : syracuseStep 3239891 = 4859837) B4859837
theorem B6156269 : Blo 1439539 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B3461383 : Blo 1439539 3461383 := bstep (se 1 (by rfl) ⟨2596037, by rfl⟩ : syracuseStep 3461383 = 5192075) B5192075
theorem B3240287 : Blo 1439539 3240287 := bstep (se 1 (by rfl) ⟨2430215, by rfl⟩ : syracuseStep 3240287 = 4860431) B4860431
theorem B15585655 : Blo 1439539 15585655 := bstep (se 1 (by rfl) ⟨11689241, by rfl⟩ : syracuseStep 15585655 = 23378483) B23378483
theorem B2429723 : Blo 1439539 2429723 := bstep (se 1 (by rfl) ⟨1822292, by rfl⟩ : syracuseStep 2429723 = 3644585) B3644585
theorem B9352091 : Blo 1439539 9352091 := bstep (se 1 (by rfl) ⟨7014068, by rfl⟩ : syracuseStep 9352091 = 14028137) B14028137
theorem B41563115 : Blo 1439539 41563115 := bstep (se 1 (by rfl) ⟨31172336, by rfl⟩ : syracuseStep 41563115 = 62344673) B62344673
theorem B12309529 : Blo 1439539 12309529 := bstep (se 2 (by rfl) ⟨4616073, by rfl⟩ : syracuseStep 12309529 = 9232147) B9232147
theorem B3241007 : Blo 1439539 3241007 := bstep (se 1 (by rfl) ⟨2430755, by rfl⟩ : syracuseStep 3241007 = 4861511) B4861511
theorem B2430175 : Blo 1439539 2430175 := bstep (se 1 (by rfl) ⟨1822631, by rfl⟩ : syracuseStep 2430175 = 3645263) B3645263
theorem B26277139 : Blo 1439539 26277139 := bstep (se 1 (by rfl) ⟨19707854, by rfl⟩ : syracuseStep 26277139 = 39415709) B39415709
theorem B4863401 : Blo 1439539 4863401 := bstep (se 2 (by rfl) ⟨1823775, by rfl⟩ : syracuseStep 4863401 = 3647551) B3647551
theorem B4863455 : Blo 1439539 4863455 := bstep (se 1 (by rfl) ⟨3647591, by rfl⟩ : syracuseStep 4863455 = 7295183) B7295183
theorem B2160107 : Blo 1439539 2160107 := bstep (se 1 (by rfl) ⟨1620080, by rfl⟩ : syracuseStep 2160107 = 3240161) B3240161
theorem B2733743 : Blo 1439539 2733743 := bstep (se 1 (by rfl) ⟨2050307, by rfl⟩ : syracuseStep 2733743 = 4100615) B4100615
theorem B4617919 : Blo 1439539 4617919 := bstep (se 1 (by rfl) ⟨3463439, by rfl⟩ : syracuseStep 4617919 = 6926879) B6926879
theorem B2160335 : Blo 1439539 2160335 := bstep (se 1 (by rfl) ⟨1620251, by rfl⟩ : syracuseStep 2160335 = 3240503) B3240503
theorem B5838587 : Blo 1439539 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B3241871 : Blo 1439539 3241871 := bstep (se 1 (by rfl) ⟨2431403, by rfl⟩ : syracuseStep 3241871 = 4862807) B4862807
theorem B2160575 : Blo 1439539 2160575 := bstep (se 1 (by rfl) ⟨1620431, by rfl⟩ : syracuseStep 2160575 = 3240863) B3240863
theorem B3241961 : Blo 1439539 3241961 := bstep (se 2 (by rfl) ⟨1215735, by rfl⟩ : syracuseStep 3241961 = 2431471) B2431471
theorem B3078271 : Blo 1439539 3078271 := bstep (se 1 (by rfl) ⟨2308703, by rfl⟩ : syracuseStep 3078271 = 4617407) B4617407
theorem B1440027 : Blo 1439539 1440027 := bstep (se 1 (by rfl) ⟨1080020, by rfl⟩ : syracuseStep 1440027 = 2160041) B2160041
theorem B1440063 : Blo 1439539 1440063 := bstep (se 1 (by rfl) ⟨1080047, by rfl⟩ : syracuseStep 1440063 = 2160095) B2160095
theorem B3946835 : Blo 1439539 3946835 := bstep (se 1 (by rfl) ⟨2960126, by rfl⟩ : syracuseStep 3946835 = 5920253) B5920253
theorem B4864481 : Blo 1439539 4864481 := bstep (se 2 (by rfl) ⟨1824180, by rfl⟩ : syracuseStep 4864481 = 3648361) B3648361
theorem B2079211 : Blo 1439539 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B2161199 : Blo 1439539 2161199 := bstep (se 1 (by rfl) ⟨1620899, by rfl⟩ : syracuseStep 2161199 = 3241799) B3241799
theorem B3242591 : Blo 1439539 3242591 := bstep (se 1 (by rfl) ⟨2431943, by rfl⟩ : syracuseStep 3242591 = 4863887) B4863887
theorem B5470841 : Blo 1439539 5470841 := bstep (se 2 (by rfl) ⟨2051565, by rfl⟩ : syracuseStep 5470841 = 4103131) B4103131
theorem B1440495 : Blo 1439539 1440495 := bstep (se 1 (by rfl) ⟨1080371, by rfl⟩ : syracuseStep 1440495 = 2160743) B2160743
theorem B2161403 : Blo 1439539 2161403 := bstep (se 1 (by rfl) ⟨1621052, by rfl⟩ : syracuseStep 2161403 = 3242105) B3242105
theorem B2161439 : Blo 1439539 2161439 := bstep (se 1 (by rfl) ⟨1621079, by rfl⟩ : syracuseStep 2161439 = 3242159) B3242159
theorem B1441307 : Blo 1439539 1441307 := bstep (se 1 (by rfl) ⟨1080980, by rfl⟩ : syracuseStep 1441307 = 2161961) B2161961
theorem B2735687 : Blo 1439539 2735687 := bstep (se 1 (by rfl) ⟨2051765, by rfl⟩ : syracuseStep 2735687 = 4103531) B4103531
theorem B28081799 : Blo 1439539 28081799 := bstep (se 1 (by rfl) ⟨21061349, by rfl⟩ : syracuseStep 28081799 = 42122699) B42122699
theorem B10944233 : Blo 1439539 10944233 := bstep (se 2 (by rfl) ⟨4104087, by rfl⟩ : syracuseStep 10944233 = 8208175) B8208175
theorem B1441519 : Blo 1439539 1441519 := bstep (se 1 (by rfl) ⟨1081139, by rfl⟩ : syracuseStep 1441519 = 2162279) B2162279
theorem B24616871 : Blo 1439539 24616871 := bstep (se 1 (by rfl) ⟨18462653, by rfl⟩ : syracuseStep 24616871 = 36925307) B36925307
theorem B40509391 : Blo 1439539 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B4104361 : Blo 1439539 4104361 := bstep (se 2 (by rfl) ⟨1539135, by rfl⟩ : syracuseStep 4104361 = 3078271) B3078271
theorem B3948743 : Blo 1439539 3948743 := bstep (se 1 (by rfl) ⟨2961557, by rfl⟩ : syracuseStep 3948743 = 5923115) B5923115
theorem B6234727 : Blo 1439539 6234727 := bstep (se 1 (by rfl) ⟨4676045, by rfl⟩ : syracuseStep 6234727 = 9352091) B9352091
theorem B140116715 : Blo 1439539 140116715 := bstep (se 1 (by rfl) ⟨105087536, by rfl⟩ : syracuseStep 140116715 = 210175073) B210175073
theorem B3892391 : Blo 1439539 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B2631223 : Blo 1439539 2631223 := bstep (se 1 (by rfl) ⟨1973417, by rfl⟩ : syracuseStep 2631223 = 3946835) B3946835
theorem B4613705 : Blo 1439539 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B3647227 : Blo 1439539 3647227 := bstep (se 1 (by rfl) ⟨2735420, by rfl⟩ : syracuseStep 3647227 = 5470841) B5470841
theorem B18721199 : Blo 1439539 18721199 := bstep (se 1 (by rfl) ⟨14040899, by rfl⟩ : syracuseStep 18721199 = 28081799) B28081799
theorem B54012521 : Blo 1439539 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B16411247 : Blo 1439539 16411247 := bstep (se 1 (by rfl) ⟨12308435, by rfl⟩ : syracuseStep 16411247 = 24616871) B24616871
theorem B23358239 : Blo 1439539 23358239 := bstep (se 1 (by rfl) ⟨17518679, by rfl⟩ : syracuseStep 23358239 = 35037359) B35037359
theorem B5467439 : Blo 1439539 5467439 := bstep (se 1 (by rfl) ⟨4100579, by rfl⟩ : syracuseStep 5467439 = 8201159) B8201159
theorem B2772281 : Blo 1439539 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B27708743 : Blo 1439539 27708743 := bstep (se 1 (by rfl) ⟨20781557, by rfl⟩ : syracuseStep 27708743 = 41563115) B41563115
theorem B1822495 : Blo 1439539 1822495 := bstep (se 1 (by rfl) ⟨1366871, by rfl⟩ : syracuseStep 1822495 = 2733743) B2733743
theorem B4861727 : Blo 1439539 4861727 := bstep (se 1 (by rfl) ⟨3646295, by rfl⟩ : syracuseStep 4861727 = 7292591) B7292591
theorem B16412705 : Blo 1439539 16412705 := bstep (se 2 (by rfl) ⟨6154764, by rfl⟩ : syracuseStep 16412705 = 12309529) B12309529
theorem B18460709 : Blo 1439539 18460709 := bstep (se 4 (by rfl) ⟨1730691, by rfl⟩ : syracuseStep 18460709 = 3461383) B3461383
theorem B3240233 : Blo 1439539 3240233 := bstep (se 2 (by rfl) ⟨1215087, by rfl⟩ : syracuseStep 3240233 = 2430175) B2430175
theorem B4862537 : Blo 1439539 4862537 := bstep (se 2 (by rfl) ⟨1823451, by rfl⟩ : syracuseStep 4862537 = 3646903) B3646903
theorem B44348107 : Blo 1439539 44348107 := bstep (se 1 (by rfl) ⟨33261080, by rfl⟩ : syracuseStep 44348107 = 66522161) B66522161
theorem B2159483 : Blo 1439539 2159483 := bstep (se 1 (by rfl) ⟨1619612, by rfl⟩ : syracuseStep 2159483 = 3239225) B3239225
theorem B6157225 : Blo 1439539 6157225 := bstep (se 2 (by rfl) ⟨2308959, by rfl⟩ : syracuseStep 6157225 = 4617919) B4617919
theorem B26293207 : Blo 1439539 26293207 := bstep (se 1 (by rfl) ⟨19719905, by rfl⟩ : syracuseStep 26293207 = 39439811) B39439811
theorem B83022893 : Blo 1439539 83022893 := bstep (se 3 (by rfl) ⟨15566792, by rfl⟩ : syracuseStep 83022893 = 31133585) B31133585
theorem B1823791 : Blo 1439539 1823791 := bstep (se 1 (by rfl) ⟨1367843, by rfl⟩ : syracuseStep 1823791 = 2735687) B2735687
theorem B4863131 : Blo 1439539 4863131 := bstep (se 1 (by rfl) ⟨3647348, by rfl⟩ : syracuseStep 4863131 = 7294697) B7294697
theorem B7296155 : Blo 1439539 7296155 := bstep (se 1 (by rfl) ⟨5472116, by rfl⟩ : syracuseStep 7296155 = 10944233) B10944233
theorem B2159807 : Blo 1439539 2159807 := bstep (se 1 (by rfl) ⟨1619855, by rfl⟩ : syracuseStep 2159807 = 3239711) B3239711
theorem B2159927 : Blo 1439539 2159927 := bstep (se 1 (by rfl) ⟨1619945, by rfl⟩ : syracuseStep 2159927 = 3239891) B3239891
theorem B2594351 : Blo 1439539 2594351 := bstep (se 1 (by rfl) ⟨1945763, by rfl⟩ : syracuseStep 2594351 = 3891527) B3891527
theorem B2160191 : Blo 1439539 2160191 := bstep (se 1 (by rfl) ⟨1620143, by rfl⟩ : syracuseStep 2160191 = 3240287) B3240287
theorem B2430607 : Blo 1439539 2430607 := bstep (se 1 (by rfl) ⟨1822955, by rfl⟩ : syracuseStep 2430607 = 3645911) B3645911
theorem B2430695 : Blo 1439539 2430695 := bstep (se 1 (by rfl) ⟨1823021, by rfl⟩ : syracuseStep 2430695 = 3646043) B3646043
theorem B20780873 : Blo 1439539 20780873 := bstep (se 2 (by rfl) ⟨7792827, by rfl⟩ : syracuseStep 20780873 = 15585655) B15585655
theorem B1619815 : Blo 1439539 1619815 := bstep (se 1 (by rfl) ⟨1214861, by rfl⟩ : syracuseStep 1619815 = 2429723) B2429723
theorem B4380583 : Blo 1439539 4380583 := bstep (se 1 (by rfl) ⟨3285437, by rfl⟩ : syracuseStep 4380583 = 6570875) B6570875
theorem B2160671 : Blo 1439539 2160671 := bstep (se 1 (by rfl) ⟨1620503, by rfl⟩ : syracuseStep 2160671 = 3241007) B3241007
theorem B3242267 : Blo 1439539 3242267 := bstep (se 1 (by rfl) ⟨2431700, by rfl⟩ : syracuseStep 3242267 = 4863401) B4863401
theorem B239622461 : Blo 1439539 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B3242303 : Blo 1439539 3242303 := bstep (se 1 (by rfl) ⟨2431727, by rfl⟩ : syracuseStep 3242303 = 4863455) B4863455
theorem B1440071 : Blo 1439539 1440071 := bstep (se 1 (by rfl) ⟨1080053, by rfl⟩ : syracuseStep 1440071 = 2160107) B2160107
theorem B1440223 : Blo 1439539 1440223 := bstep (se 1 (by rfl) ⟨1080167, by rfl⟩ : syracuseStep 1440223 = 2160335) B2160335
theorem B2161247 : Blo 1439539 2161247 := bstep (se 1 (by rfl) ⟨1620935, by rfl⟩ : syracuseStep 2161247 = 3241871) B3241871
theorem B1440383 : Blo 1439539 1440383 := bstep (se 1 (by rfl) ⟨1080287, by rfl⟩ : syracuseStep 1440383 = 2160575) B2160575
theorem B2161307 : Blo 1439539 2161307 := bstep (se 1 (by rfl) ⟨1620980, by rfl⟩ : syracuseStep 2161307 = 3241961) B3241961
theorem B2431775 : Blo 1439539 2431775 := bstep (se 1 (by rfl) ⟨1823831, by rfl⟩ : syracuseStep 2431775 = 3647663) B3647663
theorem B3242987 : Blo 1439539 3242987 := bstep (se 1 (by rfl) ⟨2432240, by rfl⟩ : syracuseStep 3242987 = 4864481) B4864481
theorem B35036185 : Blo 1439539 35036185 := bstep (se 2 (by rfl) ⟨13138569, by rfl⟩ : syracuseStep 35036185 = 26277139) B26277139
theorem B1440799 : Blo 1439539 1440799 := bstep (se 1 (by rfl) ⟨1080599, by rfl⟩ : syracuseStep 1440799 = 2161199) B2161199
theorem B2161727 : Blo 1439539 2161727 := bstep (se 1 (by rfl) ⟨1621295, by rfl⟩ : syracuseStep 2161727 = 3242591) B3242591
theorem B45079643 : Blo 1439539 45079643 := bstep (se 1 (by rfl) ⟨33809732, by rfl⟩ : syracuseStep 45079643 = 67619465) B67619465
theorem B1440935 : Blo 1439539 1440935 := bstep (se 1 (by rfl) ⟨1080701, by rfl⟩ : syracuseStep 1440935 = 2161403) B2161403
theorem B1440959 : Blo 1439539 1440959 := bstep (se 1 (by rfl) ⟨1080719, by rfl⟩ : syracuseStep 1440959 = 2161439) B2161439
theorem B9854365 : Blo 1439539 9854365 := bstep (se 3 (by rfl) ⟨1847693, by rfl⟩ : syracuseStep 9854365 = 3695387) B3695387
theorem B4104179 : Blo 1439539 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B5472481 : Blo 1439539 5472481 := bstep (se 2 (by rfl) ⟨2052180, by rfl⟩ : syracuseStep 5472481 = 4104361) B4104361
theorem B14033189 : Blo 1439539 14033189 := bstep (se 4 (by rfl) ⟨1315611, by rfl⟩ : syracuseStep 14033189 = 2631223) B2631223
theorem B59130809 : Blo 1439539 59130809 := bstep (se 2 (by rfl) ⟨22174053, by rfl⟩ : syracuseStep 59130809 = 44348107) B44348107
theorem B1729567 : Blo 1439539 1729567 := bstep (se 1 (by rfl) ⟨1297175, by rfl⟩ : syracuseStep 1729567 = 2594351) B2594351
theorem B13853915 : Blo 1439539 13853915 := bstep (se 1 (by rfl) ⟨10390436, by rfl⟩ : syracuseStep 13853915 = 20780873) B20780873
theorem B8209633 : Blo 1439539 8209633 := bstep (se 2 (by rfl) ⟨3078612, by rfl⟩ : syracuseStep 8209633 = 6157225) B6157225
theorem B12307139 : Blo 1439539 12307139 := bstep (se 1 (by rfl) ⟨9230354, by rfl⟩ : syracuseStep 12307139 = 18460709) B18460709
theorem B2632495 : Blo 1439539 2632495 := bstep (se 1 (by rfl) ⟨1974371, by rfl⟩ : syracuseStep 2632495 = 3948743) B3948743
theorem B120212381 : Blo 1439539 120212381 := bstep (se 3 (by rfl) ⟨22539821, by rfl⟩ : syracuseStep 120212381 = 45079643) B45079643
theorem B55348595 : Blo 1439539 55348595 := bstep (se 1 (by rfl) ⟨41511446, by rfl⟩ : syracuseStep 55348595 = 83022893) B83022893
theorem B3075803 : Blo 1439539 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B35057609 : Blo 1439539 35057609 := bstep (se 2 (by rfl) ⟨13146603, by rfl⟩ : syracuseStep 35057609 = 26293207) B26293207
theorem B46714913 : Blo 1439539 46714913 := bstep (se 2 (by rfl) ⟨17518092, by rfl⟩ : syracuseStep 46714913 = 35036185) B35036185
theorem B159748307 : Blo 1439539 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B12480799 : Blo 1439539 12480799 := bstep (se 1 (by rfl) ⟨9360599, by rfl⟩ : syracuseStep 12480799 = 18721199) B18721199
theorem B36008347 : Blo 1439539 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B10940831 : Blo 1439539 10940831 := bstep (se 1 (by rfl) ⟨8205623, by rfl⟩ : syracuseStep 10940831 = 16411247) B16411247
theorem B3240809 : Blo 1439539 3240809 := bstep (se 2 (by rfl) ⟨1215303, by rfl⟩ : syracuseStep 3240809 = 2430607) B2430607
theorem B1848187 : Blo 1439539 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B4862969 : Blo 1439539 4862969 := bstep (se 2 (by rfl) ⟨1823613, by rfl⟩ : syracuseStep 4862969 = 3647227) B3647227
theorem B2429993 : Blo 1439539 2429993 := bstep (se 2 (by rfl) ⟨911247, by rfl⟩ : syracuseStep 2429993 = 1822495) B1822495
theorem B2159753 : Blo 1439539 2159753 := bstep (se 2 (by rfl) ⟨809907, by rfl⟩ : syracuseStep 2159753 = 1619815) B1619815
theorem B3241151 : Blo 1439539 3241151 := bstep (se 1 (by rfl) ⟨2430863, by rfl⟩ : syracuseStep 3241151 = 4861727) B4861727
theorem B10941803 : Blo 1439539 10941803 := bstep (se 1 (by rfl) ⟨8206352, by rfl⟩ : syracuseStep 10941803 = 16412705) B16412705
theorem B2160155 : Blo 1439539 2160155 := bstep (se 1 (by rfl) ⟨1620116, by rfl⟩ : syracuseStep 2160155 = 3240233) B3240233
theorem B3241691 : Blo 1439539 3241691 := bstep (se 1 (by rfl) ⟨2431268, by rfl⟩ : syracuseStep 3241691 = 4862537) B4862537
theorem B93411143 : Blo 1439539 93411143 := bstep (se 1 (by rfl) ⟨70058357, by rfl⟩ : syracuseStep 93411143 = 140116715) B140116715
theorem B1439655 : Blo 1439539 1439655 := bstep (se 1 (by rfl) ⟨1079741, by rfl⟩ : syracuseStep 1439655 = 2159483) B2159483
theorem B3242087 : Blo 1439539 3242087 := bstep (se 1 (by rfl) ⟨2431565, by rfl⟩ : syracuseStep 3242087 = 4863131) B4863131
theorem B4864103 : Blo 1439539 4864103 := bstep (se 1 (by rfl) ⟨3648077, by rfl⟩ : syracuseStep 4864103 = 7296155) B7296155
theorem B2594927 : Blo 1439539 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B1439871 : Blo 1439539 1439871 := bstep (se 1 (by rfl) ⟨1079903, by rfl⟩ : syracuseStep 1439871 = 2159807) B2159807
theorem B8312969 : Blo 1439539 8312969 := bstep (se 2 (by rfl) ⟨3117363, by rfl⟩ : syracuseStep 8312969 = 6234727) B6234727
theorem B1439951 : Blo 1439539 1439951 := bstep (se 1 (by rfl) ⟨1079963, by rfl⟩ : syracuseStep 1439951 = 2159927) B2159927
theorem B1440127 : Blo 1439539 1440127 := bstep (se 1 (by rfl) ⟨1080095, by rfl⟩ : syracuseStep 1440127 = 2160191) B2160191
theorem B1620463 : Blo 1439539 1620463 := bstep (se 1 (by rfl) ⟨1215347, by rfl⟩ : syracuseStep 1620463 = 2430695) B2430695
theorem B1440447 : Blo 1439539 1440447 := bstep (se 1 (by rfl) ⟨1080335, by rfl⟩ : syracuseStep 1440447 = 2160671) B2160671
theorem B2431721 : Blo 1439539 2431721 := bstep (se 2 (by rfl) ⟨911895, by rfl⟩ : syracuseStep 2431721 = 1823791) B1823791
theorem B2161511 : Blo 1439539 2161511 := bstep (se 1 (by rfl) ⟨1621133, by rfl⟩ : syracuseStep 2161511 = 3242267) B3242267
theorem B2161535 : Blo 1439539 2161535 := bstep (se 1 (by rfl) ⟨1621151, by rfl⟩ : syracuseStep 2161535 = 3242303) B3242303
theorem B1440831 : Blo 1439539 1440831 := bstep (se 1 (by rfl) ⟨1080623, by rfl⟩ : syracuseStep 1440831 = 2161247) B2161247
theorem B1440871 : Blo 1439539 1440871 := bstep (se 1 (by rfl) ⟨1080653, by rfl⟩ : syracuseStep 1440871 = 2161307) B2161307
theorem B15572159 : Blo 1439539 15572159 := bstep (se 1 (by rfl) ⟨11679119, by rfl⟩ : syracuseStep 15572159 = 23358239) B23358239
theorem B1621183 : Blo 1439539 1621183 := bstep (se 1 (by rfl) ⟨1215887, by rfl⟩ : syracuseStep 1621183 = 2431775) B2431775
theorem B13139153 : Blo 1439539 13139153 := bstep (se 2 (by rfl) ⟨4927182, by rfl⟩ : syracuseStep 13139153 = 9854365) B9854365
theorem B2161991 : Blo 1439539 2161991 := bstep (se 1 (by rfl) ⟨1621493, by rfl⟩ : syracuseStep 2161991 = 3242987) B3242987
theorem B1441151 : Blo 1439539 1441151 := bstep (se 1 (by rfl) ⟨1080863, by rfl⟩ : syracuseStep 1441151 = 2161727) B2161727
theorem B3644959 : Blo 1439539 3644959 := bstep (se 1 (by rfl) ⟨2733719, by rfl⟩ : syracuseStep 3644959 = 5467439) B5467439
theorem B18472495 : Blo 1439539 18472495 := bstep (se 1 (by rfl) ⟨13854371, by rfl⟩ : syracuseStep 18472495 = 27708743) B27708743
theorem B5840777 : Blo 1439539 5840777 := bstep (se 2 (by rfl) ⟨2190291, by rfl⟩ : syracuseStep 5840777 = 4380583) B4380583
theorem B2736119 : Blo 1439539 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B9355459 : Blo 1439539 9355459 := bstep (se 1 (by rfl) ⟨7016594, by rfl⟩ : syracuseStep 9355459 = 14033189) B14033189
theorem B39420539 : Blo 1439539 39420539 := bstep (se 1 (by rfl) ⟨29565404, by rfl⟩ : syracuseStep 39420539 = 59130809) B59130809
theorem B10946177 : Blo 1439539 10946177 := bstep (se 2 (by rfl) ⟨4104816, by rfl⟩ : syracuseStep 10946177 = 8209633) B8209633
theorem B4859945 : Blo 1439539 4859945 := bstep (se 2 (by rfl) ⟨1822479, by rfl⟩ : syracuseStep 4859945 = 3644959) B3644959
theorem B10381439 : Blo 1439539 10381439 := bstep (se 1 (by rfl) ⟨7786079, by rfl⟩ : syracuseStep 10381439 = 15572159) B15572159
theorem B8759435 : Blo 1439539 8759435 := bstep (se 1 (by rfl) ⟨6569576, by rfl⟩ : syracuseStep 8759435 = 13139153) B13139153
theorem B36899063 : Blo 1439539 36899063 := bstep (se 1 (by rfl) ⟨27674297, by rfl⟩ : syracuseStep 36899063 = 55348595) B55348595
theorem B2050535 : Blo 1439539 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B3893851 : Blo 1439539 3893851 := bstep (se 1 (by rfl) ⟨2920388, by rfl⟩ : syracuseStep 3893851 = 5840777) B5840777
theorem B106498871 : Blo 1439539 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B7293887 : Blo 1439539 7293887 := bstep (se 1 (by rfl) ⟨5470415, by rfl⟩ : syracuseStep 7293887 = 10940831) B10940831
theorem B16641065 : Blo 1439539 16641065 := bstep (se 2 (by rfl) ⟨6240399, by rfl⟩ : syracuseStep 16641065 = 12480799) B12480799
theorem B9235943 : Blo 1439539 9235943 := bstep (se 1 (by rfl) ⟨6926957, by rfl⟩ : syracuseStep 9235943 = 13853915) B13853915
theorem B7294535 : Blo 1439539 7294535 := bstep (se 1 (by rfl) ⟨5470901, by rfl⟩ : syracuseStep 7294535 = 10941803) B10941803
theorem B3509993 : Blo 1439539 3509993 := bstep (se 2 (by rfl) ⟨1316247, by rfl⟩ : syracuseStep 3509993 = 2632495) B2632495
theorem B2306089 : Blo 1439539 2306089 := bstep (se 2 (by rfl) ⟨864783, by rfl⟩ : syracuseStep 2306089 = 1729567) B1729567
theorem B5541979 : Blo 1439539 5541979 := bstep (se 1 (by rfl) ⟨4156484, by rfl⟩ : syracuseStep 5541979 = 8312969) B8312969
theorem B8204759 : Blo 1439539 8204759 := bstep (se 1 (by rfl) ⟨6153569, by rfl⟩ : syracuseStep 8204759 = 12307139) B12307139
theorem B24629993 : Blo 1439539 24629993 := bstep (se 2 (by rfl) ⟨9236247, by rfl⟩ : syracuseStep 24629993 = 18472495) B18472495
theorem B320566349 : Blo 1439539 320566349 := bstep (se 3 (by rfl) ⟨60106190, by rfl⟩ : syracuseStep 320566349 = 120212381) B120212381
theorem B7296317 : Blo 1439539 7296317 := bstep (se 3 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 7296317 = 2736119) B2736119
theorem B31143275 : Blo 1439539 31143275 := bstep (se 1 (by rfl) ⟨23357456, by rfl⟩ : syracuseStep 31143275 = 46714913) B46714913
theorem B6919805 : Blo 1439539 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B7296641 : Blo 1439539 7296641 := bstep (se 2 (by rfl) ⟨2736240, by rfl⟩ : syracuseStep 7296641 = 5472481) B5472481
theorem B48011129 : Blo 1439539 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B2160539 : Blo 1439539 2160539 := bstep (se 1 (by rfl) ⟨1620404, by rfl⟩ : syracuseStep 2160539 = 3240809) B3240809
theorem B2160617 : Blo 1439539 2160617 := bstep (se 2 (by rfl) ⟨810231, by rfl⟩ : syracuseStep 2160617 = 1620463) B1620463
theorem B3241979 : Blo 1439539 3241979 := bstep (se 1 (by rfl) ⟨2431484, by rfl⟩ : syracuseStep 3241979 = 4862969) B4862969
theorem B1619995 : Blo 1439539 1619995 := bstep (se 1 (by rfl) ⟨1214996, by rfl⟩ : syracuseStep 1619995 = 2429993) B2429993
theorem B1439835 : Blo 1439539 1439835 := bstep (se 1 (by rfl) ⟨1079876, by rfl⟩ : syracuseStep 1439835 = 2159753) B2159753
theorem B2160767 : Blo 1439539 2160767 := bstep (se 1 (by rfl) ⟨1620575, by rfl⟩ : syracuseStep 2160767 = 3241151) B3241151
theorem B1440103 : Blo 1439539 1440103 := bstep (se 1 (by rfl) ⟨1080077, by rfl⟩ : syracuseStep 1440103 = 2160155) B2160155
theorem B2161127 : Blo 1439539 2161127 := bstep (se 1 (by rfl) ⟨1620845, by rfl⟩ : syracuseStep 2161127 = 3241691) B3241691
theorem B2464249 : Blo 1439539 2464249 := bstep (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) B1848187
theorem B62274095 : Blo 1439539 62274095 := bstep (se 1 (by rfl) ⟨46705571, by rfl⟩ : syracuseStep 62274095 = 93411143) B93411143
theorem B2161391 : Blo 1439539 2161391 := bstep (se 1 (by rfl) ⟨1621043, by rfl⟩ : syracuseStep 2161391 = 3242087) B3242087
theorem B3242735 : Blo 1439539 3242735 := bstep (se 1 (by rfl) ⟨2432051, by rfl⟩ : syracuseStep 3242735 = 4864103) B4864103
theorem B2161577 : Blo 1439539 2161577 := bstep (se 2 (by rfl) ⟨810591, by rfl⟩ : syracuseStep 2161577 = 1621183) B1621183
theorem B1621147 : Blo 1439539 1621147 := bstep (se 1 (by rfl) ⟨1215860, by rfl⟩ : syracuseStep 1621147 = 2431721) B2431721
theorem B1441007 : Blo 1439539 1441007 := bstep (se 1 (by rfl) ⟨1080755, by rfl⟩ : syracuseStep 1441007 = 2161511) B2161511
theorem B1441023 : Blo 1439539 1441023 := bstep (se 1 (by rfl) ⟨1080767, by rfl⟩ : syracuseStep 1441023 = 2161535) B2161535
theorem B1441327 : Blo 1439539 1441327 := bstep (se 1 (by rfl) ⟨1080995, by rfl⟩ : syracuseStep 1441327 = 2161991) B2161991
theorem B23371739 : Blo 1439539 23371739 := bstep (se 1 (by rfl) ⟨17528804, by rfl⟩ : syracuseStep 23371739 = 35057609) B35057609
theorem B44376173 : Blo 1439539 44376173 := bstep (se 3 (by rfl) ⟨8320532, by rfl⟩ : syracuseStep 44376173 = 16641065) B16641065
theorem B7389305 : Blo 1439539 7389305 := bstep (se 2 (by rfl) ⟨2770989, by rfl⟩ : syracuseStep 7389305 = 5541979) B5541979
theorem B26280359 : Blo 1439539 26280359 := bstep (se 1 (by rfl) ⟨19710269, by rfl⟩ : syracuseStep 26280359 = 39420539) B39420539
theorem B20767205 : Blo 1439539 20767205 := bstep (se 4 (by rfl) ⟨1946925, by rfl⟩ : syracuseStep 20767205 = 3893851) B3893851
theorem B3285665 : Blo 1439539 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B4613203 : Blo 1439539 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B32007419 : Blo 1439539 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B12299141 : Blo 1439539 12299141 := bstep (se 4 (by rfl) ⟨1153044, by rfl⟩ : syracuseStep 12299141 = 2306089) B2306089
theorem B23358493 : Blo 1439539 23358493 := bstep (se 3 (by rfl) ⟨4379717, by rfl⟩ : syracuseStep 23358493 = 8759435) B8759435
theorem B16419995 : Blo 1439539 16419995 := bstep (se 1 (by rfl) ⟨12314996, by rfl⟩ : syracuseStep 16419995 = 24629993) B24629993
theorem B20762183 : Blo 1439539 20762183 := bstep (se 1 (by rfl) ⟨15571637, by rfl⟩ : syracuseStep 20762183 = 31143275) B31143275
theorem B5468093 : Blo 1439539 5468093 := bstep (se 3 (by rfl) ⟨1025267, by rfl⟩ : syracuseStep 5468093 = 2050535) B2050535
theorem B3239963 : Blo 1439539 3239963 := bstep (se 1 (by rfl) ⟨2429972, by rfl⟩ : syracuseStep 3239963 = 4859945) B4859945
theorem B9359981 : Blo 1439539 9359981 := bstep (se 3 (by rfl) ⟨1754996, by rfl⟩ : syracuseStep 9359981 = 3509993) B3509993
theorem B4862591 : Blo 1439539 4862591 := bstep (se 1 (by rfl) ⟨3646943, by rfl⟩ : syracuseStep 4862591 = 7293887) B7293887
theorem B6157295 : Blo 1439539 6157295 := bstep (se 1 (by rfl) ⟨4617971, by rfl⟩ : syracuseStep 6157295 = 9235943) B9235943
theorem B4863023 : Blo 1439539 4863023 := bstep (se 1 (by rfl) ⟨3647267, by rfl⟩ : syracuseStep 4863023 = 7294535) B7294535
theorem B2159993 : Blo 1439539 2159993 := bstep (se 2 (by rfl) ⟨809997, by rfl⟩ : syracuseStep 2159993 = 1619995) B1619995
theorem B12473945 : Blo 1439539 12473945 := bstep (se 2 (by rfl) ⟨4677729, by rfl⟩ : syracuseStep 12473945 = 9355459) B9355459
theorem B5469839 : Blo 1439539 5469839 := bstep (se 1 (by rfl) ⟨4102379, by rfl⟩ : syracuseStep 5469839 = 8204759) B8204759
theorem B213710899 : Blo 1439539 213710899 := bstep (se 1 (by rfl) ⟨160283174, by rfl⟩ : syracuseStep 213710899 = 320566349) B320566349
theorem B4864211 : Blo 1439539 4864211 := bstep (se 1 (by rfl) ⟨3648158, by rfl⟩ : syracuseStep 4864211 = 7296317) B7296317
theorem B4864427 : Blo 1439539 4864427 := bstep (se 1 (by rfl) ⟨3648320, by rfl⟩ : syracuseStep 4864427 = 7296641) B7296641
theorem B7297451 : Blo 1439539 7297451 := bstep (se 1 (by rfl) ⟨5473088, by rfl⟩ : syracuseStep 7297451 = 10946177) B10946177
theorem B1440359 : Blo 1439539 1440359 := bstep (se 1 (by rfl) ⟨1080269, by rfl⟩ : syracuseStep 1440359 = 2160539) B2160539
theorem B1440411 : Blo 1439539 1440411 := bstep (se 1 (by rfl) ⟨1080308, by rfl⟩ : syracuseStep 1440411 = 2160617) B2160617
theorem B2161319 : Blo 1439539 2161319 := bstep (se 1 (by rfl) ⟨1620989, by rfl⟩ : syracuseStep 2161319 = 3241979) B3241979
theorem B6920959 : Blo 1439539 6920959 := bstep (se 1 (by rfl) ⟨5190719, by rfl⟩ : syracuseStep 6920959 = 10381439) B10381439
theorem B1440511 : Blo 1439539 1440511 := bstep (se 1 (by rfl) ⟨1080383, by rfl⟩ : syracuseStep 1440511 = 2160767) B2160767
theorem B24599375 : Blo 1439539 24599375 := bstep (se 1 (by rfl) ⟨18449531, by rfl⟩ : syracuseStep 24599375 = 36899063) B36899063
theorem B2161529 : Blo 1439539 2161529 := bstep (se 2 (by rfl) ⟨810573, by rfl⟩ : syracuseStep 2161529 = 1621147) B1621147
theorem B1440751 : Blo 1439539 1440751 := bstep (se 1 (by rfl) ⟨1080563, by rfl⟩ : syracuseStep 1440751 = 2161127) B2161127
theorem B41516063 : Blo 1439539 41516063 := bstep (se 1 (by rfl) ⟨31137047, by rfl⟩ : syracuseStep 41516063 = 62274095) B62274095
theorem B1440927 : Blo 1439539 1440927 := bstep (se 1 (by rfl) ⟨1080695, by rfl⟩ : syracuseStep 1440927 = 2161391) B2161391
theorem B2161823 : Blo 1439539 2161823 := bstep (se 1 (by rfl) ⟨1621367, by rfl⟩ : syracuseStep 2161823 = 3242735) B3242735
theorem B70999247 : Blo 1439539 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B1441051 : Blo 1439539 1441051 := bstep (se 1 (by rfl) ⟨1080788, by rfl⟩ : syracuseStep 1441051 = 2161577) B2161577
theorem B15581159 : Blo 1439539 15581159 := bstep (se 1 (by rfl) ⟨11685869, by rfl⟩ : syracuseStep 15581159 = 23371739) B23371739
theorem B13844803 : Blo 1439539 13844803 := bstep (se 1 (by rfl) ⟨10383602, by rfl⟩ : syracuseStep 13844803 = 20767205) B20767205
theorem B4104863 : Blo 1439539 4104863 := bstep (se 1 (by rfl) ⟨3078647, by rfl⟩ : syracuseStep 4104863 = 6157295) B6157295
theorem B8315963 : Blo 1439539 8315963 := bstep (se 1 (by rfl) ⟨6236972, by rfl⟩ : syracuseStep 8315963 = 12473945) B12473945
theorem B3646559 : Blo 1439539 3646559 := bstep (se 1 (by rfl) ⟨2734919, by rfl⟩ : syracuseStep 3646559 = 5469839) B5469839
theorem B10946663 : Blo 1439539 10946663 := bstep (se 1 (by rfl) ⟨8209997, by rfl⟩ : syracuseStep 10946663 = 16419995) B16419995
theorem B29584115 : Blo 1439539 29584115 := bstep (se 1 (by rfl) ⟨22188086, by rfl⟩ : syracuseStep 29584115 = 44376173) B44376173
theorem B4926203 : Blo 1439539 4926203 := bstep (se 1 (by rfl) ⟨3694652, by rfl⟩ : syracuseStep 4926203 = 7389305) B7389305
theorem B24603749 : Blo 1439539 24603749 := bstep (se 4 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 24603749 = 4613203) B4613203
theorem B2190443 : Blo 1439539 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B9227945 : Blo 1439539 9227945 := bstep (se 2 (by rfl) ⟨3460479, by rfl⟩ : syracuseStep 9227945 = 6920959) B6920959
theorem B27677375 : Blo 1439539 27677375 := bstep (se 1 (by rfl) ⟨20758031, by rfl⟩ : syracuseStep 27677375 = 41516063) B41516063
theorem B13841455 : Blo 1439539 13841455 := bstep (se 1 (by rfl) ⟨10381091, by rfl⟩ : syracuseStep 13841455 = 20762183) B20762183
theorem B2159975 : Blo 1439539 2159975 := bstep (se 1 (by rfl) ⟨1619981, by rfl⟩ : syracuseStep 2159975 = 3239963) B3239963
theorem B284947865 : Blo 1439539 284947865 := bstep (se 2 (by rfl) ⟨106855449, by rfl⟩ : syracuseStep 284947865 = 213710899) B213710899
theorem B17520239 : Blo 1439539 17520239 := bstep (se 1 (by rfl) ⟨13140179, by rfl⟩ : syracuseStep 17520239 = 26280359) B26280359
theorem B6239987 : Blo 1439539 6239987 := bstep (se 1 (by rfl) ⟨4679990, by rfl⟩ : syracuseStep 6239987 = 9359981) B9359981
theorem B3241727 : Blo 1439539 3241727 := bstep (se 1 (by rfl) ⟨2431295, by rfl⟩ : syracuseStep 3241727 = 4862591) B4862591
theorem B3242015 : Blo 1439539 3242015 := bstep (se 1 (by rfl) ⟨2431511, by rfl⟩ : syracuseStep 3242015 = 4863023) B4863023
theorem B21338279 : Blo 1439539 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B1439995 : Blo 1439539 1439995 := bstep (se 1 (by rfl) ⟨1079996, by rfl⟩ : syracuseStep 1439995 = 2159993) B2159993
theorem B31144657 : Blo 1439539 31144657 := bstep (se 2 (by rfl) ⟨11679246, by rfl⟩ : syracuseStep 31144657 = 23358493) B23358493
theorem B3242807 : Blo 1439539 3242807 := bstep (se 1 (by rfl) ⟨2432105, by rfl⟩ : syracuseStep 3242807 = 4864211) B4864211
theorem B3242951 : Blo 1439539 3242951 := bstep (se 1 (by rfl) ⟨2432213, by rfl⟩ : syracuseStep 3242951 = 4864427) B4864427
theorem B4864967 : Blo 1439539 4864967 := bstep (se 1 (by rfl) ⟨3648725, by rfl⟩ : syracuseStep 4864967 = 7297451) B7297451
theorem B1440879 : Blo 1439539 1440879 := bstep (se 1 (by rfl) ⟨1080659, by rfl⟩ : syracuseStep 1440879 = 2161319) B2161319
theorem B16399583 : Blo 1439539 16399583 := bstep (se 1 (by rfl) ⟨12299687, by rfl⟩ : syracuseStep 16399583 = 24599375) B24599375
theorem B1441019 : Blo 1439539 1441019 := bstep (se 1 (by rfl) ⟨1080764, by rfl⟩ : syracuseStep 1441019 = 2161529) B2161529
theorem B8199427 : Blo 1439539 8199427 := bstep (se 1 (by rfl) ⟨6149570, by rfl⟩ : syracuseStep 8199427 = 12299141) B12299141
theorem B1441215 : Blo 1439539 1441215 := bstep (se 1 (by rfl) ⟨1080911, by rfl⟩ : syracuseStep 1441215 = 2161823) B2161823
theorem B47332831 : Blo 1439539 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B3645395 : Blo 1439539 3645395 := bstep (se 1 (by rfl) ⟨2734046, by rfl⟩ : syracuseStep 3645395 = 5468093) B5468093
theorem B10387439 : Blo 1439539 10387439 := bstep (se 1 (by rfl) ⟨7790579, by rfl⟩ : syracuseStep 10387439 = 15581159) B15581159
theorem B5841181 : Blo 1439539 5841181 := bstep (se 3 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 5841181 = 2190443) B2190443
theorem B2736575 : Blo 1439539 2736575 := bstep (se 1 (by rfl) ⟨2052431, by rfl⟩ : syracuseStep 2736575 = 4104863) B4104863
theorem B189965243 : Blo 1439539 189965243 := bstep (se 1 (by rfl) ⟨142473932, by rfl⟩ : syracuseStep 189965243 = 284947865) B284947865
theorem B41526209 : Blo 1439539 41526209 := bstep (se 2 (by rfl) ⟨15572328, by rfl⟩ : syracuseStep 41526209 = 31144657) B31144657
theorem B16402499 : Blo 1439539 16402499 := bstep (se 1 (by rfl) ⟨12301874, by rfl⟩ : syracuseStep 16402499 = 24603749) B24603749
theorem B6924959 : Blo 1439539 6924959 := bstep (se 1 (by rfl) ⟨5193719, by rfl⟩ : syracuseStep 6924959 = 10387439) B10387439
theorem B18459737 : Blo 1439539 18459737 := bstep (se 2 (by rfl) ⟨6922401, by rfl⟩ : syracuseStep 18459737 = 13844803) B13844803
theorem B18451583 : Blo 1439539 18451583 := bstep (se 1 (by rfl) ⟨13838687, by rfl⟩ : syracuseStep 18451583 = 27677375) B27677375
theorem B14225519 : Blo 1439539 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B10932569 : Blo 1439539 10932569 := bstep (se 2 (by rfl) ⟨4099713, by rfl⟩ : syracuseStep 10932569 = 8199427) B8199427
theorem B19722743 : Blo 1439539 19722743 := bstep (se 1 (by rfl) ⟨14792057, by rfl⟩ : syracuseStep 19722743 = 29584115) B29584115
theorem B10933055 : Blo 1439539 10933055 := bstep (se 1 (by rfl) ⟨8199791, by rfl⟩ : syracuseStep 10933055 = 16399583) B16399583
theorem B2430263 : Blo 1439539 2430263 := bstep (se 1 (by rfl) ⟨1822697, by rfl⟩ : syracuseStep 2430263 = 3645395) B3645395
theorem B5543975 : Blo 1439539 5543975 := bstep (se 1 (by rfl) ⟨4157981, by rfl⟩ : syracuseStep 5543975 = 8315963) B8315963
theorem B2431039 : Blo 1439539 2431039 := bstep (se 1 (by rfl) ⟨1823279, by rfl⟩ : syracuseStep 2431039 = 3646559) B3646559
theorem B1439983 : Blo 1439539 1439983 := bstep (se 1 (by rfl) ⟨1079987, by rfl⟩ : syracuseStep 1439983 = 2159975) B2159975
theorem B11680159 : Blo 1439539 11680159 := bstep (se 1 (by rfl) ⟨8760119, by rfl⟩ : syracuseStep 11680159 = 17520239) B17520239
theorem B4159991 : Blo 1439539 4159991 := bstep (se 1 (by rfl) ⟨3119993, by rfl⟩ : syracuseStep 4159991 = 6239987) B6239987
theorem B2161151 : Blo 1439539 2161151 := bstep (se 1 (by rfl) ⟨1620863, by rfl⟩ : syracuseStep 2161151 = 3241727) B3241727
theorem B2161343 : Blo 1439539 2161343 := bstep (se 1 (by rfl) ⟨1621007, by rfl⟩ : syracuseStep 2161343 = 3242015) B3242015
theorem B18455273 : Blo 1439539 18455273 := bstep (se 2 (by rfl) ⟨6920727, by rfl⟩ : syracuseStep 18455273 = 13841455) B13841455
theorem B7297775 : Blo 1439539 7297775 := bstep (se 1 (by rfl) ⟨5473331, by rfl⟩ : syracuseStep 7297775 = 10946663) B10946663
theorem B3284135 : Blo 1439539 3284135 := bstep (se 1 (by rfl) ⟨2463101, by rfl⟩ : syracuseStep 3284135 = 4926203) B4926203
theorem B2161871 : Blo 1439539 2161871 := bstep (se 1 (by rfl) ⟨1621403, by rfl⟩ : syracuseStep 2161871 = 3242807) B3242807
theorem B63110441 : Blo 1439539 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B2161967 : Blo 1439539 2161967 := bstep (se 1 (by rfl) ⟨1621475, by rfl⟩ : syracuseStep 2161967 = 3242951) B3242951
theorem B3243311 : Blo 1439539 3243311 := bstep (se 1 (by rfl) ⟨2432483, by rfl⟩ : syracuseStep 3243311 = 4864967) B4864967
theorem B6151963 : Blo 1439539 6151963 := bstep (se 1 (by rfl) ⟨4613972, by rfl⟩ : syracuseStep 6151963 = 9227945) B9227945
theorem B13148495 : Blo 1439539 13148495 := bstep (se 1 (by rfl) ⟨9861371, by rfl⟩ : syracuseStep 13148495 = 19722743) B19722743
theorem B15573545 : Blo 1439539 15573545 := bstep (se 2 (by rfl) ⟨5840079, by rfl⟩ : syracuseStep 15573545 = 11680159) B11680159
theorem B12306491 : Blo 1439539 12306491 := bstep (se 1 (by rfl) ⟨9229868, by rfl⟩ : syracuseStep 12306491 = 18459737) B18459737
theorem B2189423 : Blo 1439539 2189423 := bstep (se 1 (by rfl) ⟨1642067, by rfl⟩ : syracuseStep 2189423 = 3284135) B3284135
theorem B8202617 : Blo 1439539 8202617 := bstep (se 2 (by rfl) ⟨3075981, by rfl⟩ : syracuseStep 8202617 = 6151963) B6151963
theorem B126643495 : Blo 1439539 126643495 := bstep (se 1 (by rfl) ⟨94982621, by rfl⟩ : syracuseStep 126643495 = 189965243) B189965243
theorem B27684139 : Blo 1439539 27684139 := bstep (se 1 (by rfl) ⟨20763104, by rfl⟩ : syracuseStep 27684139 = 41526209) B41526209
theorem B2773327 : Blo 1439539 2773327 := bstep (se 1 (by rfl) ⟨2079995, by rfl⟩ : syracuseStep 2773327 = 4159991) B4159991
theorem B4616639 : Blo 1439539 4616639 := bstep (se 1 (by rfl) ⟨3462479, by rfl⟩ : syracuseStep 4616639 = 6924959) B6924959
theorem B12301055 : Blo 1439539 12301055 := bstep (se 1 (by rfl) ⟨9225791, by rfl⟩ : syracuseStep 12301055 = 18451583) B18451583
theorem B9483679 : Blo 1439539 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B3241385 : Blo 1439539 3241385 := bstep (se 2 (by rfl) ⟨1215519, by rfl⟩ : syracuseStep 3241385 = 2431039) B2431039
theorem B14783933 : Blo 1439539 14783933 := bstep (se 3 (by rfl) ⟨2771987, by rfl⟩ : syracuseStep 14783933 = 5543975) B5543975
theorem B7288379 : Blo 1439539 7288379 := bstep (se 1 (by rfl) ⟨5466284, by rfl⟩ : syracuseStep 7288379 = 10932569) B10932569
theorem B1824383 : Blo 1439539 1824383 := bstep (se 1 (by rfl) ⟨1368287, by rfl⟩ : syracuseStep 1824383 = 2736575) B2736575
theorem B7788241 : Blo 1439539 7788241 := bstep (se 2 (by rfl) ⟨2920590, by rfl⟩ : syracuseStep 7788241 = 5841181) B5841181
theorem B7288703 : Blo 1439539 7288703 := bstep (se 1 (by rfl) ⟨5466527, by rfl⟩ : syracuseStep 7288703 = 10933055) B10933055
theorem B1620175 : Blo 1439539 1620175 := bstep (se 1 (by rfl) ⟨1215131, by rfl⟩ : syracuseStep 1620175 = 2430263) B2430263
theorem B10934999 : Blo 1439539 10934999 := bstep (se 1 (by rfl) ⟨8201249, by rfl⟩ : syracuseStep 10934999 = 16402499) B16402499
theorem B1440767 : Blo 1439539 1440767 := bstep (se 1 (by rfl) ⟨1080575, by rfl⟩ : syracuseStep 1440767 = 2161151) B2161151
theorem B1440895 : Blo 1439539 1440895 := bstep (se 1 (by rfl) ⟨1080671, by rfl⟩ : syracuseStep 1440895 = 2161343) B2161343
theorem B12303515 : Blo 1439539 12303515 := bstep (se 1 (by rfl) ⟨9227636, by rfl⟩ : syracuseStep 12303515 = 18455273) B18455273
theorem B4865183 : Blo 1439539 4865183 := bstep (se 1 (by rfl) ⟨3648887, by rfl⟩ : syracuseStep 4865183 = 7297775) B7297775
theorem B1441247 : Blo 1439539 1441247 := bstep (se 1 (by rfl) ⟨1080935, by rfl⟩ : syracuseStep 1441247 = 2161871) B2161871
theorem B42073627 : Blo 1439539 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B1441311 : Blo 1439539 1441311 := bstep (se 1 (by rfl) ⟨1080983, by rfl⟩ : syracuseStep 1441311 = 2161967) B2161967
theorem B2162207 : Blo 1439539 2162207 := bstep (se 1 (by rfl) ⟨1621655, by rfl⟩ : syracuseStep 2162207 = 3243311) B3243311
theorem B8765663 : Blo 1439539 8765663 := bstep (se 1 (by rfl) ⟨6574247, by rfl⟩ : syracuseStep 8765663 = 13148495) B13148495
theorem B8200703 : Blo 1439539 8200703 := bstep (se 1 (by rfl) ⟨6150527, by rfl⟩ : syracuseStep 8200703 = 12301055) B12301055
theorem B9855955 : Blo 1439539 9855955 := bstep (se 1 (by rfl) ⟨7391966, by rfl⟩ : syracuseStep 9855955 = 14783933) B14783933
theorem B4858919 : Blo 1439539 4858919 := bstep (se 1 (by rfl) ⟨3644189, by rfl⟩ : syracuseStep 4858919 = 7288379) B7288379
theorem B4859135 : Blo 1439539 4859135 := bstep (se 1 (by rfl) ⟨3644351, by rfl⟩ : syracuseStep 4859135 = 7288703) B7288703
theorem B1459615 : Blo 1439539 1459615 := bstep (se 1 (by rfl) ⟨1094711, by rfl⟩ : syracuseStep 1459615 = 2189423) B2189423
theorem B8202343 : Blo 1439539 8202343 := bstep (se 1 (by rfl) ⟨6151757, by rfl⟩ : syracuseStep 8202343 = 12303515) B12303515
theorem B50579621 : Blo 1439539 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B10382363 : Blo 1439539 10382363 := bstep (se 1 (by rfl) ⟨7786772, by rfl⟩ : syracuseStep 10382363 = 15573545) B15573545
theorem B3697769 : Blo 1439539 3697769 := bstep (se 2 (by rfl) ⟨1386663, by rfl⟩ : syracuseStep 3697769 = 2773327) B2773327
theorem B8204327 : Blo 1439539 8204327 := bstep (se 1 (by rfl) ⟨6153245, by rfl⟩ : syracuseStep 8204327 = 12306491) B12306491
theorem B5468411 : Blo 1439539 5468411 := bstep (se 1 (by rfl) ⟨4101308, by rfl⟩ : syracuseStep 5468411 = 8202617) B8202617
theorem B168857993 : Blo 1439539 168857993 := bstep (se 2 (by rfl) ⟨63321747, by rfl⟩ : syracuseStep 168857993 = 126643495) B126643495
theorem B10384321 : Blo 1439539 10384321 := bstep (se 2 (by rfl) ⟨3894120, by rfl⟩ : syracuseStep 10384321 = 7788241) B7788241
theorem B2160233 : Blo 1439539 2160233 := bstep (se 2 (by rfl) ⟨810087, by rfl⟩ : syracuseStep 2160233 = 1620175) B1620175
theorem B3077759 : Blo 1439539 3077759 := bstep (se 1 (by rfl) ⟨2308319, by rfl⟩ : syracuseStep 3077759 = 4616639) B4616639
theorem B2160923 : Blo 1439539 2160923 := bstep (se 1 (by rfl) ⟨1620692, by rfl⟩ : syracuseStep 2160923 = 3241385) B3241385
theorem B4865021 : Blo 1439539 4865021 := bstep (se 3 (by rfl) ⟨912191, by rfl⟩ : syracuseStep 4865021 = 1824383) B1824383
theorem B36912185 : Blo 1439539 36912185 := bstep (se 2 (by rfl) ⟨13842069, by rfl⟩ : syracuseStep 36912185 = 27684139) B27684139
theorem B7289999 : Blo 1439539 7289999 := bstep (se 1 (by rfl) ⟨5467499, by rfl⟩ : syracuseStep 7289999 = 10934999) B10934999
theorem B56098169 : Blo 1439539 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B3243455 : Blo 1439539 3243455 := bstep (se 1 (by rfl) ⟨2432591, by rfl⟩ : syracuseStep 3243455 = 4865183) B4865183
theorem B1441471 : Blo 1439539 1441471 := bstep (se 1 (by rfl) ⟨1081103, by rfl⟩ : syracuseStep 1441471 = 2162207) B2162207
theorem B10936457 : Blo 1439539 10936457 := bstep (se 2 (by rfl) ⟨4101171, by rfl⟩ : syracuseStep 10936457 = 8202343) B8202343
theorem B3645607 : Blo 1439539 3645607 := bstep (se 1 (by rfl) ⟨2734205, by rfl⟩ : syracuseStep 3645607 = 5468411) B5468411
theorem B13845761 : Blo 1439539 13845761 := bstep (se 2 (by rfl) ⟨5192160, by rfl⟩ : syracuseStep 13845761 = 10384321) B10384321
theorem B13141273 : Blo 1439539 13141273 := bstep (se 2 (by rfl) ⟨4927977, by rfl⟩ : syracuseStep 13141273 = 9855955) B9855955
theorem B33719747 : Blo 1439539 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B4859999 : Blo 1439539 4859999 := bstep (se 1 (by rfl) ⟨3644999, by rfl⟩ : syracuseStep 4859999 = 7289999) B7289999
theorem B37398779 : Blo 1439539 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B5467135 : Blo 1439539 5467135 := bstep (se 1 (by rfl) ⟨4100351, by rfl⟩ : syracuseStep 5467135 = 8200703) B8200703
theorem B23375101 : Blo 1439539 23375101 := bstep (se 3 (by rfl) ⟨4382831, by rfl⟩ : syracuseStep 23375101 = 8765663) B8765663
theorem B3239279 : Blo 1439539 3239279 := bstep (se 1 (by rfl) ⟨2429459, by rfl⟩ : syracuseStep 3239279 = 4858919) B4858919
theorem B3239423 : Blo 1439539 3239423 := bstep (se 1 (by rfl) ⟨2429567, by rfl⟩ : syracuseStep 3239423 = 4859135) B4859135
theorem B2051839 : Blo 1439539 2051839 := bstep (se 1 (by rfl) ⟨1538879, by rfl⟩ : syracuseStep 2051839 = 3077759) B3077759
theorem B1946153 : Blo 1439539 1946153 := bstep (se 2 (by rfl) ⟨729807, by rfl⟩ : syracuseStep 1946153 = 1459615) B1459615
theorem B5469551 : Blo 1439539 5469551 := bstep (se 1 (by rfl) ⟨4102163, by rfl⟩ : syracuseStep 5469551 = 8204327) B8204327
theorem B9860717 : Blo 1439539 9860717 := bstep (se 3 (by rfl) ⟨1848884, by rfl⟩ : syracuseStep 9860717 = 3697769) B3697769
theorem B450287981 : Blo 1439539 450287981 := bstep (se 3 (by rfl) ⟨84428996, by rfl⟩ : syracuseStep 450287981 = 168857993) B168857993
theorem B1440155 : Blo 1439539 1440155 := bstep (se 1 (by rfl) ⟨1080116, by rfl⟩ : syracuseStep 1440155 = 2160233) B2160233
theorem B1440615 : Blo 1439539 1440615 := bstep (se 1 (by rfl) ⟨1080461, by rfl⟩ : syracuseStep 1440615 = 2160923) B2160923
theorem B3243347 : Blo 1439539 3243347 := bstep (se 1 (by rfl) ⟨2432510, by rfl⟩ : syracuseStep 3243347 = 4865021) B4865021
theorem B6921575 : Blo 1439539 6921575 := bstep (se 1 (by rfl) ⟨5191181, by rfl⟩ : syracuseStep 6921575 = 10382363) B10382363
theorem B24608123 : Blo 1439539 24608123 := bstep (se 1 (by rfl) ⟨18456092, by rfl⟩ : syracuseStep 24608123 = 36912185) B36912185
theorem B2162303 : Blo 1439539 2162303 := bstep (se 1 (by rfl) ⟨1621727, by rfl⟩ : syracuseStep 2162303 = 3243455) B3243455
theorem B7290971 : Blo 1439539 7290971 := bstep (se 1 (by rfl) ⟨5468228, by rfl⟩ : syracuseStep 7290971 = 10936457) B10936457
theorem B3646367 : Blo 1439539 3646367 := bstep (se 1 (by rfl) ⟨2734775, by rfl⟩ : syracuseStep 3646367 = 5469551) B5469551
theorem B4614383 : Blo 1439539 4614383 := bstep (se 1 (by rfl) ⟨3460787, by rfl⟩ : syracuseStep 4614383 = 6921575) B6921575
theorem B4860809 : Blo 1439539 4860809 := bstep (se 2 (by rfl) ⟨1822803, by rfl⟩ : syracuseStep 4860809 = 3645607) B3645607
theorem B6573811 : Blo 1439539 6573811 := bstep (se 1 (by rfl) ⟨4930358, by rfl⟩ : syracuseStep 6573811 = 9860717) B9860717
theorem B89919325 : Blo 1439539 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B3239999 : Blo 1439539 3239999 := bstep (se 1 (by rfl) ⟨2429999, by rfl⟩ : syracuseStep 3239999 = 4859999) B4859999
theorem B5189741 : Blo 1439539 5189741 := bstep (se 3 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 5189741 = 1946153) B1946153
theorem B24932519 : Blo 1439539 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B300191987 : Blo 1439539 300191987 := bstep (se 1 (by rfl) ⟨225143990, by rfl⟩ : syracuseStep 300191987 = 450287981) B450287981
theorem B31166801 : Blo 1439539 31166801 := bstep (se 2 (by rfl) ⟨11687550, by rfl⟩ : syracuseStep 31166801 = 23375101) B23375101
theorem B2159519 : Blo 1439539 2159519 := bstep (se 1 (by rfl) ⟨1619639, by rfl⟩ : syracuseStep 2159519 = 3239279) B3239279
theorem B16405415 : Blo 1439539 16405415 := bstep (se 1 (by rfl) ⟨12304061, by rfl⟩ : syracuseStep 16405415 = 24608123) B24608123
theorem B2159615 : Blo 1439539 2159615 := bstep (se 1 (by rfl) ⟨1619711, by rfl⟩ : syracuseStep 2159615 = 3239423) B3239423
theorem B9230507 : Blo 1439539 9230507 := bstep (se 1 (by rfl) ⟨6922880, by rfl⟩ : syracuseStep 9230507 = 13845761) B13845761
theorem B7289513 : Blo 1439539 7289513 := bstep (se 2 (by rfl) ⟨2733567, by rfl⟩ : syracuseStep 7289513 = 5467135) B5467135
theorem B17521697 : Blo 1439539 17521697 := bstep (se 2 (by rfl) ⟨6570636, by rfl⟩ : syracuseStep 17521697 = 13141273) B13141273
theorem B2162231 : Blo 1439539 2162231 := bstep (se 1 (by rfl) ⟨1621673, by rfl⟩ : syracuseStep 2162231 = 3243347) B3243347
theorem B2735785 : Blo 1439539 2735785 := bstep (se 2 (by rfl) ⟨1025919, by rfl⟩ : syracuseStep 2735785 = 2051839) B2051839
theorem B1441535 : Blo 1439539 1441535 := bstep (se 1 (by rfl) ⟨1081151, by rfl⟩ : syracuseStep 1441535 = 2162303) B2162303
theorem B16621679 : Blo 1439539 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B10936943 : Blo 1439539 10936943 := bstep (se 1 (by rfl) ⟨8202707, by rfl⟩ : syracuseStep 10936943 = 16405415) B16405415
theorem B6153671 : Blo 1439539 6153671 := bstep (se 1 (by rfl) ⟨4615253, by rfl⟩ : syracuseStep 6153671 = 9230507) B9230507
theorem B4859675 : Blo 1439539 4859675 := bstep (se 1 (by rfl) ⟨3644756, by rfl⟩ : syracuseStep 4859675 = 7289513) B7289513
theorem B479569733 : Blo 1439539 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B3647713 : Blo 1439539 3647713 := bstep (se 2 (by rfl) ⟨1367892, by rfl⟩ : syracuseStep 3647713 = 2735785) B2735785
theorem B4860647 : Blo 1439539 4860647 := bstep (se 1 (by rfl) ⟨3645485, by rfl⟩ : syracuseStep 4860647 = 7290971) B7290971
theorem B3459827 : Blo 1439539 3459827 := bstep (se 1 (by rfl) ⟨2594870, by rfl⟩ : syracuseStep 3459827 = 5189741) B5189741
theorem B20777867 : Blo 1439539 20777867 := bstep (se 1 (by rfl) ⟨15583400, by rfl⟩ : syracuseStep 20777867 = 31166801) B31166801
theorem B3076255 : Blo 1439539 3076255 := bstep (se 1 (by rfl) ⟨2307191, by rfl⟩ : syracuseStep 3076255 = 4614383) B4614383
theorem B3240539 : Blo 1439539 3240539 := bstep (se 1 (by rfl) ⟨2430404, by rfl⟩ : syracuseStep 3240539 = 4860809) B4860809
theorem B2159999 : Blo 1439539 2159999 := bstep (se 1 (by rfl) ⟨1619999, by rfl⟩ : syracuseStep 2159999 = 3239999) B3239999
theorem B46724525 : Blo 1439539 46724525 := bstep (se 3 (by rfl) ⟨8760848, by rfl⟩ : syracuseStep 46724525 = 17521697) B17521697
theorem B200127991 : Blo 1439539 200127991 := bstep (se 1 (by rfl) ⟨150095993, by rfl⟩ : syracuseStep 200127991 = 300191987) B300191987
theorem B1439679 : Blo 1439539 1439679 := bstep (se 1 (by rfl) ⟨1079759, by rfl⟩ : syracuseStep 1439679 = 2159519) B2159519
theorem B2430911 : Blo 1439539 2430911 := bstep (se 1 (by rfl) ⟨1823183, by rfl⟩ : syracuseStep 2430911 = 3646367) B3646367
theorem B1439743 : Blo 1439539 1439743 := bstep (se 1 (by rfl) ⟨1079807, by rfl⟩ : syracuseStep 1439743 = 2159615) B2159615
theorem B8765081 : Blo 1439539 8765081 := bstep (se 2 (by rfl) ⟨3286905, by rfl⟩ : syracuseStep 8765081 = 6573811) B6573811
theorem B1441487 : Blo 1439539 1441487 := bstep (se 1 (by rfl) ⟨1081115, by rfl⟩ : syracuseStep 1441487 = 2162231) B2162231
theorem B7291295 : Blo 1439539 7291295 := bstep (se 1 (by rfl) ⟨5468471, by rfl⟩ : syracuseStep 7291295 = 10936943) B10936943
theorem B16409789 : Blo 1439539 16409789 := bstep (se 3 (by rfl) ⟨3076835, by rfl⟩ : syracuseStep 16409789 = 6153671) B6153671
theorem B5843387 : Blo 1439539 5843387 := bstep (se 1 (by rfl) ⟨4382540, by rfl⟩ : syracuseStep 5843387 = 8765081) B8765081
theorem B31149683 : Blo 1439539 31149683 := bstep (se 1 (by rfl) ⟨23362262, by rfl⟩ : syracuseStep 31149683 = 46724525) B46724525
theorem B3239783 : Blo 1439539 3239783 := bstep (se 1 (by rfl) ⟨2429837, by rfl⟩ : syracuseStep 3239783 = 4859675) B4859675
theorem B319713155 : Blo 1439539 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B3240431 : Blo 1439539 3240431 := bstep (se 1 (by rfl) ⟨2430323, by rfl⟩ : syracuseStep 3240431 = 4860647) B4860647
theorem B2306551 : Blo 1439539 2306551 := bstep (se 1 (by rfl) ⟨1729913, by rfl⟩ : syracuseStep 2306551 = 3459827) B3459827
theorem B11081119 : Blo 1439539 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B4101673 : Blo 1439539 4101673 := bstep (se 2 (by rfl) ⟨1538127, by rfl⟩ : syracuseStep 4101673 = 3076255) B3076255
theorem B4863617 : Blo 1439539 4863617 := bstep (se 2 (by rfl) ⟨1823856, by rfl⟩ : syracuseStep 4863617 = 3647713) B3647713
theorem B2160359 : Blo 1439539 2160359 := bstep (se 1 (by rfl) ⟨1620269, by rfl⟩ : syracuseStep 2160359 = 3240539) B3240539
theorem B1439999 : Blo 1439539 1439999 := bstep (se 1 (by rfl) ⟨1079999, by rfl⟩ : syracuseStep 1439999 = 2159999) B2159999
theorem B1620607 : Blo 1439539 1620607 := bstep (se 1 (by rfl) ⟨1215455, by rfl⟩ : syracuseStep 1620607 = 2430911) B2430911
theorem B13851911 : Blo 1439539 13851911 := bstep (se 1 (by rfl) ⟨10388933, by rfl⟩ : syracuseStep 13851911 = 20777867) B20777867
theorem B266837321 : Blo 1439539 266837321 := bstep (se 2 (by rfl) ⟨100063995, by rfl⟩ : syracuseStep 266837321 = 200127991) B200127991
theorem B36938429 : Blo 1439539 36938429 := bstep (se 3 (by rfl) ⟨6925955, by rfl⟩ : syracuseStep 36938429 = 13851911) B13851911
theorem B711566189 : Blo 1439539 711566189 := bstep (se 3 (by rfl) ⟨133418660, by rfl⟩ : syracuseStep 711566189 = 266837321) B266837321
theorem B15582365 : Blo 1439539 15582365 := bstep (se 3 (by rfl) ⟨2921693, by rfl⟩ : syracuseStep 15582365 = 5843387) B5843387
theorem B213142103 : Blo 1439539 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B4860863 : Blo 1439539 4860863 := bstep (se 1 (by rfl) ⟨3645647, by rfl⟩ : syracuseStep 4860863 = 7291295) B7291295
theorem B3075401 : Blo 1439539 3075401 := bstep (se 2 (by rfl) ⟨1153275, by rfl⟩ : syracuseStep 3075401 = 2306551) B2306551
theorem B10939859 : Blo 1439539 10939859 := bstep (se 1 (by rfl) ⟨8204894, by rfl⟩ : syracuseStep 10939859 = 16409789) B16409789
theorem B14774825 : Blo 1439539 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B5468897 : Blo 1439539 5468897 := bstep (se 2 (by rfl) ⟨2050836, by rfl⟩ : syracuseStep 5468897 = 4101673) B4101673
theorem B2159855 : Blo 1439539 2159855 := bstep (se 1 (by rfl) ⟨1619891, by rfl⟩ : syracuseStep 2159855 = 3239783) B3239783
theorem B2160287 : Blo 1439539 2160287 := bstep (se 1 (by rfl) ⟨1620215, by rfl⟩ : syracuseStep 2160287 = 3240431) B3240431
theorem B2160809 : Blo 1439539 2160809 := bstep (se 2 (by rfl) ⟨810303, by rfl⟩ : syracuseStep 2160809 = 1620607) B1620607
theorem B3242411 : Blo 1439539 3242411 := bstep (se 1 (by rfl) ⟨2431808, by rfl⟩ : syracuseStep 3242411 = 4863617) B4863617
theorem B1440239 : Blo 1439539 1440239 := bstep (se 1 (by rfl) ⟨1080179, by rfl⟩ : syracuseStep 1440239 = 2160359) B2160359
theorem B20766455 : Blo 1439539 20766455 := bstep (se 1 (by rfl) ⟨15574841, by rfl⟩ : syracuseStep 20766455 = 31149683) B31149683
theorem B24625619 : Blo 1439539 24625619 := bstep (se 1 (by rfl) ⟨18469214, by rfl⟩ : syracuseStep 24625619 = 36938429) B36938429
theorem B3645931 : Blo 1439539 3645931 := bstep (se 1 (by rfl) ⟨2734448, by rfl⟩ : syracuseStep 3645931 = 5468897) B5468897
theorem B10388243 : Blo 1439539 10388243 := bstep (se 1 (by rfl) ⟨7791182, by rfl⟩ : syracuseStep 10388243 = 15582365) B15582365
theorem B2050267 : Blo 1439539 2050267 := bstep (se 1 (by rfl) ⟨1537700, by rfl⟩ : syracuseStep 2050267 = 3075401) B3075401
theorem B7293239 : Blo 1439539 7293239 := bstep (se 1 (by rfl) ⟨5469929, by rfl⟩ : syracuseStep 7293239 = 10939859) B10939859
theorem B9849883 : Blo 1439539 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B142094735 : Blo 1439539 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B3240575 : Blo 1439539 3240575 := bstep (se 1 (by rfl) ⟨2430431, by rfl⟩ : syracuseStep 3240575 = 4860863) B4860863
theorem B1439903 : Blo 1439539 1439903 := bstep (se 1 (by rfl) ⟨1079927, by rfl⟩ : syracuseStep 1439903 = 2159855) B2159855
theorem B1440191 : Blo 1439539 1440191 := bstep (se 1 (by rfl) ⟨1080143, by rfl⟩ : syracuseStep 1440191 = 2160287) B2160287
theorem B1440539 : Blo 1439539 1440539 := bstep (se 1 (by rfl) ⟨1080404, by rfl⟩ : syracuseStep 1440539 = 2160809) B2160809
theorem B2161607 : Blo 1439539 2161607 := bstep (se 1 (by rfl) ⟨1621205, by rfl⟩ : syracuseStep 2161607 = 3242411) B3242411
theorem B30360157397 : Blo 1439539 30360157397 := bstep (se 7 (by rfl) ⟨355783094, by rfl⟩ : syracuseStep 30360157397 = 711566189) B711566189
theorem B13844303 : Blo 1439539 13844303 := bstep (se 1 (by rfl) ⟨10383227, by rfl⟩ : syracuseStep 13844303 = 20766455) B20766455
theorem B16417079 : Blo 1439539 16417079 := bstep (se 1 (by rfl) ⟨12312809, by rfl⟩ : syracuseStep 16417079 = 24625619) B24625619
theorem B13133177 : Blo 1439539 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B6925495 : Blo 1439539 6925495 := bstep (se 1 (by rfl) ⟨5194121, by rfl⟩ : syracuseStep 6925495 = 10388243) B10388243
theorem B4861241 : Blo 1439539 4861241 := bstep (se 2 (by rfl) ⟨1822965, by rfl⟩ : syracuseStep 4861241 = 3645931) B3645931
theorem B4862159 : Blo 1439539 4862159 := bstep (se 1 (by rfl) ⟨3646619, by rfl⟩ : syracuseStep 4862159 = 7293239) B7293239
theorem B9229535 : Blo 1439539 9229535 := bstep (se 1 (by rfl) ⟨6922151, by rfl⟩ : syracuseStep 9229535 = 13844303) B13844303
theorem B94729823 : Blo 1439539 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B2733689 : Blo 1439539 2733689 := bstep (se 2 (by rfl) ⟨1025133, by rfl⟩ : syracuseStep 2733689 = 2050267) B2050267
theorem B2160383 : Blo 1439539 2160383 := bstep (se 1 (by rfl) ⟨1620287, by rfl⟩ : syracuseStep 2160383 = 3240575) B3240575
theorem B1441071 : Blo 1439539 1441071 := bstep (se 1 (by rfl) ⟨1080803, by rfl⟩ : syracuseStep 1441071 = 2161607) B2161607
theorem B20240104931 : Blo 1439539 20240104931 := bstep (se 1 (by rfl) ⟨15180078698, by rfl⟩ : syracuseStep 20240104931 = 30360157397) B30360157397
theorem B10944719 : Blo 1439539 10944719 := bstep (se 1 (by rfl) ⟨8208539, by rfl⟩ : syracuseStep 10944719 = 16417079) B16417079
theorem B6153023 : Blo 1439539 6153023 := bstep (se 1 (by rfl) ⟨4614767, by rfl⟩ : syracuseStep 6153023 = 9229535) B9229535
theorem B63153215 : Blo 1439539 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B9233993 : Blo 1439539 9233993 := bstep (se 2 (by rfl) ⟨3462747, by rfl⟩ : syracuseStep 9233993 = 6925495) B6925495
theorem B3240827 : Blo 1439539 3240827 := bstep (se 1 (by rfl) ⟨2430620, by rfl⟩ : syracuseStep 3240827 = 4861241) B4861241
theorem B3241439 : Blo 1439539 3241439 := bstep (se 1 (by rfl) ⟨2431079, by rfl⟩ : syracuseStep 3241439 = 4862159) B4862159
theorem B8755451 : Blo 1439539 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B1440255 : Blo 1439539 1440255 := bstep (se 1 (by rfl) ⟨1080191, by rfl⟩ : syracuseStep 1440255 = 2160383) B2160383
theorem B7289837 : Blo 1439539 7289837 := bstep (se 3 (by rfl) ⟨1366844, by rfl⟩ : syracuseStep 7289837 = 2733689) B2733689
theorem B13493403287 : Blo 1439539 13493403287 := bstep (se 1 (by rfl) ⟨10120052465, by rfl⟩ : syracuseStep 13493403287 = 20240104931) B20240104931
theorem B4859891 : Blo 1439539 4859891 := bstep (se 1 (by rfl) ⟨3644918, by rfl⟩ : syracuseStep 4859891 = 7289837) B7289837
theorem B42102143 : Blo 1439539 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B6155995 : Blo 1439539 6155995 := bstep (se 1 (by rfl) ⟨4616996, by rfl⟩ : syracuseStep 6155995 = 9233993) B9233993
theorem B5836967 : Blo 1439539 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B7296479 : Blo 1439539 7296479 := bstep (se 1 (by rfl) ⟨5472359, by rfl⟩ : syracuseStep 7296479 = 10944719) B10944719
theorem B4102015 : Blo 1439539 4102015 := bstep (se 1 (by rfl) ⟨3076511, by rfl⟩ : syracuseStep 4102015 = 6153023) B6153023
theorem B2160551 : Blo 1439539 2160551 := bstep (se 1 (by rfl) ⟨1620413, by rfl⟩ : syracuseStep 2160551 = 3240827) B3240827
theorem B2160959 : Blo 1439539 2160959 := bstep (se 1 (by rfl) ⟨1620719, by rfl⟩ : syracuseStep 2160959 = 3241439) B3241439
theorem B8995602191 : Blo 1439539 8995602191 := bstep (se 1 (by rfl) ⟨6746701643, by rfl⟩ : syracuseStep 8995602191 = 13493403287) B13493403287
theorem B3891311 : Blo 1439539 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B28068095 : Blo 1439539 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B3239927 : Blo 1439539 3239927 := bstep (se 1 (by rfl) ⟨2429945, by rfl⟩ : syracuseStep 3239927 = 4859891) B4859891
theorem B5469353 : Blo 1439539 5469353 := bstep (se 2 (by rfl) ⟨2051007, by rfl⟩ : syracuseStep 5469353 = 4102015) B4102015
theorem B4864319 : Blo 1439539 4864319 := bstep (se 1 (by rfl) ⟨3648239, by rfl⟩ : syracuseStep 4864319 = 7296479) B7296479
theorem B1440367 : Blo 1439539 1440367 := bstep (se 1 (by rfl) ⟨1080275, by rfl⟩ : syracuseStep 1440367 = 2160551) B2160551
theorem B1440639 : Blo 1439539 1440639 := bstep (se 1 (by rfl) ⟨1080479, by rfl⟩ : syracuseStep 1440639 = 2160959) B2160959
theorem B23988272509 : Blo 1439539 23988272509 := bstep (se 3 (by rfl) ⟨4497801095, by rfl⟩ : syracuseStep 23988272509 = 8995602191) B8995602191
theorem B8207993 : Blo 1439539 8207993 := bstep (se 2 (by rfl) ⟨3077997, by rfl⟩ : syracuseStep 8207993 = 6155995) B6155995
theorem B3646235 : Blo 1439539 3646235 := bstep (se 1 (by rfl) ⟨2734676, by rfl⟩ : syracuseStep 3646235 = 5469353) B5469353
theorem B18712063 : Blo 1439539 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B31984363345 : Blo 1439539 31984363345 := bstep (se 2 (by rfl) ⟨11994136254, by rfl⟩ : syracuseStep 31984363345 = 23988272509) B23988272509
theorem B2159951 : Blo 1439539 2159951 := bstep (se 1 (by rfl) ⟨1619963, by rfl⟩ : syracuseStep 2159951 = 3239927) B3239927
theorem B2594207 : Blo 1439539 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B3242879 : Blo 1439539 3242879 := bstep (se 1 (by rfl) ⟨2432159, by rfl⟩ : syracuseStep 3242879 = 4864319) B4864319
theorem B5471995 : Blo 1439539 5471995 := bstep (se 1 (by rfl) ⟨4103996, by rfl⟩ : syracuseStep 5471995 = 8207993) B8207993
theorem B42645817793 : Blo 1439539 42645817793 := bstep (se 2 (by rfl) ⟨15992181672, by rfl⟩ : syracuseStep 42645817793 = 31984363345) B31984363345
theorem B6917885 : Blo 1439539 6917885 := bstep (se 3 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 6917885 = 2594207) B2594207
theorem B24949417 : Blo 1439539 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B7295993 : Blo 1439539 7295993 := bstep (se 2 (by rfl) ⟨2735997, by rfl⟩ : syracuseStep 7295993 = 5471995) B5471995
theorem B2430823 : Blo 1439539 2430823 := bstep (se 1 (by rfl) ⟨1823117, by rfl⟩ : syracuseStep 2430823 = 3646235) B3646235
theorem B1439967 : Blo 1439539 1439967 := bstep (se 1 (by rfl) ⟨1079975, by rfl⟩ : syracuseStep 1439967 = 2159951) B2159951
theorem B2161919 : Blo 1439539 2161919 := bstep (se 1 (by rfl) ⟨1621439, by rfl⟩ : syracuseStep 2161919 = 3242879) B3242879
theorem B28430545195 : Blo 1439539 28430545195 := bstep (se 1 (by rfl) ⟨21322908896, by rfl⟩ : syracuseStep 28430545195 = 42645817793) B42645817793
theorem B3241097 : Blo 1439539 3241097 := bstep (se 2 (by rfl) ⟨1215411, by rfl⟩ : syracuseStep 3241097 = 2430823) B2430823
theorem B4863995 : Blo 1439539 4863995 := bstep (se 1 (by rfl) ⟨3647996, by rfl⟩ : syracuseStep 4863995 = 7295993) B7295993
theorem B33265889 : Blo 1439539 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B1441279 : Blo 1439539 1441279 := bstep (se 1 (by rfl) ⟨1080959, by rfl⟩ : syracuseStep 1441279 = 2161919) B2161919
theorem B4611923 : Blo 1439539 4611923 := bstep (se 1 (by rfl) ⟨3458942, by rfl⟩ : syracuseStep 4611923 = 6917885) B6917885
theorem B22177259 : Blo 1439539 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B3074615 : Blo 1439539 3074615 := bstep (se 1 (by rfl) ⟨2305961, by rfl⟩ : syracuseStep 3074615 = 4611923) B4611923
theorem B37907393593 : Blo 1439539 37907393593 := bstep (se 2 (by rfl) ⟨14215272597, by rfl⟩ : syracuseStep 37907393593 = 28430545195) B28430545195
theorem B2160731 : Blo 1439539 2160731 := bstep (se 1 (by rfl) ⟨1620548, by rfl⟩ : syracuseStep 2160731 = 3241097) B3241097
theorem B3242663 : Blo 1439539 3242663 := bstep (se 1 (by rfl) ⟨2431997, by rfl⟩ : syracuseStep 3242663 = 4863995) B4863995
theorem B50543191457 : Blo 1439539 50543191457 := bstep (se 2 (by rfl) ⟨18953696796, by rfl⟩ : syracuseStep 50543191457 = 37907393593) B37907393593
theorem B2049743 : Blo 1439539 2049743 := bstep (se 1 (by rfl) ⟨1537307, by rfl⟩ : syracuseStep 2049743 = 3074615) B3074615
theorem B14784839 : Blo 1439539 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B1440487 : Blo 1439539 1440487 := bstep (se 1 (by rfl) ⟨1080365, by rfl⟩ : syracuseStep 1440487 = 2160731) B2160731
theorem B2161775 : Blo 1439539 2161775 := bstep (se 1 (by rfl) ⟨1621331, by rfl⟩ : syracuseStep 2161775 = 3242663) B3242663
theorem B9856559 : Blo 1439539 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B5465981 : Blo 1439539 5465981 := bstep (se 3 (by rfl) ⟨1024871, by rfl⟩ : syracuseStep 5465981 = 2049743) B2049743
theorem B33695460971 : Blo 1439539 33695460971 := bstep (se 1 (by rfl) ⟨25271595728, by rfl⟩ : syracuseStep 33695460971 = 50543191457) B50543191457
theorem B1441183 : Blo 1439539 1441183 := bstep (se 1 (by rfl) ⟨1080887, by rfl⟩ : syracuseStep 1441183 = 2161775) B2161775
theorem B6571039 : Blo 1439539 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B22463640647 : Blo 1439539 22463640647 := bstep (se 1 (by rfl) ⟨16847730485, by rfl⟩ : syracuseStep 22463640647 = 33695460971) B33695460971
theorem B3643987 : Blo 1439539 3643987 := bstep (se 1 (by rfl) ⟨2732990, by rfl⟩ : syracuseStep 3643987 = 5465981) B5465981
theorem B4858649 : Blo 1439539 4858649 := bstep (se 2 (by rfl) ⟨1821993, by rfl⟩ : syracuseStep 4858649 = 3643987) B3643987
theorem B8761385 : Blo 1439539 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B14975760431 : Blo 1439539 14975760431 := bstep (se 1 (by rfl) ⟨11231820323, by rfl⟩ : syracuseStep 14975760431 = 22463640647) B22463640647
theorem B5840923 : Blo 1439539 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B3239099 : Blo 1439539 3239099 := bstep (se 1 (by rfl) ⟨2429324, by rfl⟩ : syracuseStep 3239099 = 4858649) B4858649
theorem B9983840287 : Blo 1439539 9983840287 := bstep (se 1 (by rfl) ⟨7487880215, by rfl⟩ : syracuseStep 9983840287 = 14975760431) B14975760431
theorem B13311787049 : Blo 1439539 13311787049 := bstep (se 2 (by rfl) ⟨4991920143, by rfl⟩ : syracuseStep 13311787049 = 9983840287) B9983840287
theorem B2159399 : Blo 1439539 2159399 := bstep (se 1 (by rfl) ⟨1619549, by rfl⟩ : syracuseStep 2159399 = 3239099) B3239099
theorem B7787897 : Blo 1439539 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B8874524699 : Blo 1439539 8874524699 := bstep (se 1 (by rfl) ⟨6655893524, by rfl⟩ : syracuseStep 8874524699 = 13311787049) B13311787049
theorem B1439599 : Blo 1439539 1439599 := bstep (se 1 (by rfl) ⟨1079699, by rfl⟩ : syracuseStep 1439599 = 2159399) B2159399
theorem B5191931 : Blo 1439539 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B3461287 : Blo 1439539 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B5916349799 : Blo 1439539 5916349799 := bstep (se 1 (by rfl) ⟨4437262349, by rfl⟩ : syracuseStep 5916349799 = 8874524699) B8874524699
theorem B4615049 : Blo 1439539 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B3944233199 : Blo 1439539 3944233199 := bstep (se 1 (by rfl) ⟨2958174899, by rfl⟩ : syracuseStep 3944233199 = 5916349799) B5916349799
theorem B2629488799 : Blo 1439539 2629488799 := bstep (se 1 (by rfl) ⟨1972116599, by rfl⟩ : syracuseStep 2629488799 = 3944233199) B3944233199
theorem B3076699 : Blo 1439539 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B3505985065 : Blo 1439539 3505985065 := bstep (se 2 (by rfl) ⟨1314744399, by rfl⟩ : syracuseStep 3505985065 = 2629488799) B2629488799
theorem B4102265 : Blo 1439539 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B18698587013 : Blo 1439539 18698587013 := bstep (se 4 (by rfl) ⟨1752992532, by rfl⟩ : syracuseStep 18698587013 = 3505985065) B3505985065
theorem B10939373 : Blo 1439539 10939373 := bstep (se 3 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 10939373 = 4102265) B4102265
theorem B7292915 : Blo 1439539 7292915 := bstep (se 1 (by rfl) ⟨5469686, by rfl⟩ : syracuseStep 7292915 = 10939373) B10939373
theorem B12465724675 : Blo 1439539 12465724675 := bstep (se 1 (by rfl) ⟨9349293506, by rfl⟩ : syracuseStep 12465724675 = 18698587013) B18698587013
theorem B4861943 : Blo 1439539 4861943 := bstep (se 1 (by rfl) ⟨3646457, by rfl⟩ : syracuseStep 4861943 = 7292915) B7292915
theorem B16620966233 : Blo 1439539 16620966233 := bstep (se 2 (by rfl) ⟨6232862337, by rfl⟩ : syracuseStep 16620966233 = 12465724675) B12465724675
theorem B3241295 : Blo 1439539 3241295 := bstep (se 1 (by rfl) ⟨2430971, by rfl⟩ : syracuseStep 3241295 = 4861943) B4861943
theorem B11080644155 : Blo 1439539 11080644155 := bstep (se 1 (by rfl) ⟨8310483116, by rfl⟩ : syracuseStep 11080644155 = 16620966233) B16620966233
theorem B7387096103 : Blo 1439539 7387096103 := bstep (se 1 (by rfl) ⟨5540322077, by rfl⟩ : syracuseStep 7387096103 = 11080644155) B11080644155
theorem B2160863 : Blo 1439539 2160863 := bstep (se 1 (by rfl) ⟨1620647, by rfl⟩ : syracuseStep 2160863 = 3241295) B3241295
theorem B4924730735 : Blo 1439539 4924730735 := bstep (se 1 (by rfl) ⟨3693548051, by rfl⟩ : syracuseStep 4924730735 = 7387096103) B7387096103
theorem B1440575 : Blo 1439539 1440575 := bstep (se 1 (by rfl) ⟨1080431, by rfl⟩ : syracuseStep 1440575 = 2160863) B2160863
theorem B3283153823 : Blo 1439539 3283153823 := bstep (se 1 (by rfl) ⟨2462365367, by rfl⟩ : syracuseStep 3283153823 = 4924730735) B4924730735
theorem B2188769215 : Blo 1439539 2188769215 := bstep (se 1 (by rfl) ⟨1641576911, by rfl⟩ : syracuseStep 2188769215 = 3283153823) B3283153823
theorem B2918358953 : Blo 1439539 2918358953 := bstep (se 2 (by rfl) ⟨1094384607, by rfl⟩ : syracuseStep 2918358953 = 2188769215) B2188769215
theorem B1945572635 : Blo 1439539 1945572635 := bstep (se 1 (by rfl) ⟨1459179476, by rfl⟩ : syracuseStep 1945572635 = 2918358953) B2918358953
theorem B1297048423 : Blo 1439539 1297048423 := bstep (se 1 (by rfl) ⟨972786317, by rfl⟩ : syracuseStep 1297048423 = 1945572635) B1945572635
theorem B1729397897 : Blo 1439539 1729397897 := bstep (se 2 (by rfl) ⟨648524211, by rfl⟩ : syracuseStep 1729397897 = 1297048423) B1297048423
theorem B1152931931 : Blo 1439539 1152931931 := bstep (se 1 (by rfl) ⟨864698948, by rfl⟩ : syracuseStep 1152931931 = 1729397897) B1729397897
theorem B768621287 : Blo 1439539 768621287 := bstep (se 1 (by rfl) ⟨576465965, by rfl⟩ : syracuseStep 768621287 = 1152931931) B1152931931
theorem B512414191 : Blo 1439539 512414191 := bstep (se 1 (by rfl) ⟨384310643, by rfl⟩ : syracuseStep 512414191 = 768621287) B768621287
theorem B683218921 : Blo 1439539 683218921 := bstep (se 2 (by rfl) ⟨256207095, by rfl⟩ : syracuseStep 683218921 = 512414191) B512414191
theorem B910958561 : Blo 1439539 910958561 := bstep (se 2 (by rfl) ⟨341609460, by rfl⟩ : syracuseStep 910958561 = 683218921) B683218921
theorem B607305707 : Blo 1439539 607305707 := bstep (se 1 (by rfl) ⟨455479280, by rfl⟩ : syracuseStep 607305707 = 910958561) B910958561
theorem B404870471 : Blo 1439539 404870471 := bstep (se 1 (by rfl) ⟨303652853, by rfl⟩ : syracuseStep 404870471 = 607305707) B607305707
theorem B269913647 : Blo 1439539 269913647 := bstep (se 1 (by rfl) ⟨202435235, by rfl⟩ : syracuseStep 269913647 = 404870471) B404870471
theorem B179942431 : Blo 1439539 179942431 := bstep (se 1 (by rfl) ⟨134956823, by rfl⟩ : syracuseStep 179942431 = 269913647) B269913647
theorem B239923241 : Blo 1439539 239923241 := bstep (se 2 (by rfl) ⟨89971215, by rfl⟩ : syracuseStep 239923241 = 179942431) B179942431
theorem B159948827 : Blo 1439539 159948827 := bstep (se 1 (by rfl) ⟨119961620, by rfl⟩ : syracuseStep 159948827 = 239923241) B239923241
theorem B106632551 : Blo 1439539 106632551 := bstep (se 1 (by rfl) ⟨79974413, by rfl⟩ : syracuseStep 106632551 = 159948827) B159948827
theorem B71088367 : Blo 1439539 71088367 := bstep (se 1 (by rfl) ⟨53316275, by rfl⟩ : syracuseStep 71088367 = 106632551) B106632551
theorem B94784489 : Blo 1439539 94784489 := bstep (se 2 (by rfl) ⟨35544183, by rfl⟩ : syracuseStep 94784489 = 71088367) B71088367
theorem B63189659 : Blo 1439539 63189659 := bstep (se 1 (by rfl) ⟨47392244, by rfl⟩ : syracuseStep 63189659 = 94784489) B94784489
theorem B42126439 : Blo 1439539 42126439 := bstep (se 1 (by rfl) ⟨31594829, by rfl⟩ : syracuseStep 42126439 = 63189659) B63189659
theorem B56168585 : Blo 1439539 56168585 := bstep (se 2 (by rfl) ⟨21063219, by rfl⟩ : syracuseStep 56168585 = 42126439) B42126439
theorem B37445723 : Blo 1439539 37445723 := bstep (se 1 (by rfl) ⟨28084292, by rfl⟩ : syracuseStep 37445723 = 56168585) B56168585
theorem B24963815 : Blo 1439539 24963815 := bstep (se 1 (by rfl) ⟨18722861, by rfl⟩ : syracuseStep 24963815 = 37445723) B37445723
theorem B16642543 : Blo 1439539 16642543 := bstep (se 1 (by rfl) ⟨12481907, by rfl⟩ : syracuseStep 16642543 = 24963815) B24963815
theorem B22190057 : Blo 1439539 22190057 := bstep (se 2 (by rfl) ⟨8321271, by rfl⟩ : syracuseStep 22190057 = 16642543) B16642543
theorem B14793371 : Blo 1439539 14793371 := bstep (se 1 (by rfl) ⟨11095028, by rfl⟩ : syracuseStep 14793371 = 22190057) B22190057
theorem B9862247 : Blo 1439539 9862247 := bstep (se 1 (by rfl) ⟨7396685, by rfl⟩ : syracuseStep 9862247 = 14793371) B14793371
theorem B26299325 : Blo 1439539 26299325 := bstep (se 3 (by rfl) ⟨4931123, by rfl⟩ : syracuseStep 26299325 = 9862247) B9862247
theorem B17532883 : Blo 1439539 17532883 := bstep (se 1 (by rfl) ⟨13149662, by rfl⟩ : syracuseStep 17532883 = 26299325) B26299325
theorem B23377177 : Blo 1439539 23377177 := bstep (se 2 (by rfl) ⟨8766441, by rfl⟩ : syracuseStep 23377177 = 17532883) B17532883
theorem B31169569 : Blo 1439539 31169569 := bstep (se 2 (by rfl) ⟨11688588, by rfl⟩ : syracuseStep 31169569 = 23377177) B23377177
theorem B41559425 : Blo 1439539 41559425 := bstep (se 2 (by rfl) ⟨15584784, by rfl⟩ : syracuseStep 41559425 = 31169569) B31169569
theorem B27706283 : Blo 1439539 27706283 := bstep (se 1 (by rfl) ⟨20779712, by rfl⟩ : syracuseStep 27706283 = 41559425) B41559425
theorem B18470855 : Blo 1439539 18470855 := bstep (se 1 (by rfl) ⟨13853141, by rfl⟩ : syracuseStep 18470855 = 27706283) B27706283
theorem B12313903 : Blo 1439539 12313903 := bstep (se 1 (by rfl) ⟨9235427, by rfl⟩ : syracuseStep 12313903 = 18470855) B18470855
theorem B16418537 : Blo 1439539 16418537 := bstep (se 2 (by rfl) ⟨6156951, by rfl⟩ : syracuseStep 16418537 = 12313903) B12313903
theorem B10945691 : Blo 1439539 10945691 := bstep (se 1 (by rfl) ⟨8209268, by rfl⟩ : syracuseStep 10945691 = 16418537) B16418537
theorem B7297127 : Blo 1439539 7297127 := bstep (se 1 (by rfl) ⟨5472845, by rfl⟩ : syracuseStep 7297127 = 10945691) B10945691
theorem B4864751 : Blo 1439539 4864751 := bstep (se 1 (by rfl) ⟨3648563, by rfl⟩ : syracuseStep 4864751 = 7297127) B7297127
theorem B3243167 : Blo 1439539 3243167 := bstep (se 1 (by rfl) ⟨2432375, by rfl⟩ : syracuseStep 3243167 = 4864751) B4864751
theorem B2162111 : Blo 1439539 2162111 := bstep (se 1 (by rfl) ⟨1621583, by rfl⟩ : syracuseStep 2162111 = 3243167) B3243167
theorem B1441407 : Blo 1439539 1441407 := bstep (se 1 (by rfl) ⟨1081055, by rfl⟩ : syracuseStep 1441407 = 2162111) B2162111

theorem C0 (j : ℕ) (h1 : 359884 ≤ j) (h2 : j ≤ 360384) : Blo 1439539 (4 * j + 3) := by
  interval_cases j
  · exact B1439539
  · exact B1439543
  · exact B1439547
  · exact B1439551
  · exact B1439555
  · exact B1439559
  · exact B1439563
  · exact B1439567
  · exact B1439571
  · exact B1439575
  · exact B1439579
  · exact B1439583
  · exact B1439587
  · exact B1439591
  · exact B1439595
  · exact B1439599
  · exact B1439603
  · exact B1439607
  · exact B1439611
  · exact B1439615
  · exact B1439619
  · exact B1439623
  · exact B1439627
  · exact B1439631
  · exact B1439635
  · exact B1439639
  · exact B1439643
  · exact B1439647
  · exact B1439651
  · exact B1439655
  · exact B1439659
  · exact B1439663
  · exact B1439667
  · exact B1439671
  · exact B1439675
  · exact B1439679
  · exact B1439683
  · exact B1439687
  · exact B1439691
  · exact B1439695
  · exact B1439699
  · exact B1439703
  · exact B1439707
  · exact B1439711
  · exact B1439715
  · exact B1439719
  · exact B1439723
  · exact B1439727
  · exact B1439731
  · exact B1439735
  · exact B1439739
  · exact B1439743
  · exact B1439747
  · exact B1439751
  · exact B1439755
  · exact B1439759
  · exact B1439763
  · exact B1439767
  · exact B1439771
  · exact B1439775
  · exact B1439779
  · exact B1439783
  · exact B1439787
  · exact B1439791
  · exact B1439795
  · exact B1439799
  · exact B1439803
  · exact B1439807
  · exact B1439811
  · exact B1439815
  · exact B1439819
  · exact B1439823
  · exact B1439827
  · exact B1439831
  · exact B1439835
  · exact B1439839
  · exact B1439843
  · exact B1439847
  · exact B1439851
  · exact B1439855
  · exact B1439859
  · exact B1439863
  · exact B1439867
  · exact B1439871
  · exact B1439875
  · exact B1439879
  · exact B1439883
  · exact B1439887
  · exact B1439891
  · exact B1439895
  · exact B1439899
  · exact B1439903
  · exact B1439907
  · exact B1439911
  · exact B1439915
  · exact B1439919
  · exact B1439923
  · exact B1439927
  · exact B1439931
  · exact B1439935
  · exact B1439939
  · exact B1439943
  · exact B1439947
  · exact B1439951
  · exact B1439955
  · exact B1439959
  · exact B1439963
  · exact B1439967
  · exact B1439971
  · exact B1439975
  · exact B1439979
  · exact B1439983
  · exact B1439987
  · exact B1439991
  · exact B1439995
  · exact B1439999
  · exact B1440003
  · exact B1440007
  · exact B1440011
  · exact B1440015
  · exact B1440019
  · exact B1440023
  · exact B1440027
  · exact B1440031
  · exact B1440035
  · exact B1440039
  · exact B1440043
  · exact B1440047
  · exact B1440051
  · exact B1440055
  · exact B1440059
  · exact B1440063
  · exact B1440067
  · exact B1440071
  · exact B1440075
  · exact B1440079
  · exact B1440083
  · exact B1440087
  · exact B1440091
  · exact B1440095
  · exact B1440099
  · exact B1440103
  · exact B1440107
  · exact B1440111
  · exact B1440115
  · exact B1440119
  · exact B1440123
  · exact B1440127
  · exact B1440131
  · exact B1440135
  · exact B1440139
  · exact B1440143
  · exact B1440147
  · exact B1440151
  · exact B1440155
  · exact B1440159
  · exact B1440163
  · exact B1440167
  · exact B1440171
  · exact B1440175
  · exact B1440179
  · exact B1440183
  · exact B1440187
  · exact B1440191
  · exact B1440195
  · exact B1440199
  · exact B1440203
  · exact B1440207
  · exact B1440211
  · exact B1440215
  · exact B1440219
  · exact B1440223
  · exact B1440227
  · exact B1440231
  · exact B1440235
  · exact B1440239
  · exact B1440243
  · exact B1440247
  · exact B1440251
  · exact B1440255
  · exact B1440259
  · exact B1440263
  · exact B1440267
  · exact B1440271
  · exact B1440275
  · exact B1440279
  · exact B1440283
  · exact B1440287
  · exact B1440291
  · exact B1440295
  · exact B1440299
  · exact B1440303
  · exact B1440307
  · exact B1440311
  · exact B1440315
  · exact B1440319
  · exact B1440323
  · exact B1440327
  · exact B1440331
  · exact B1440335
  · exact B1440339
  · exact B1440343
  · exact B1440347
  · exact B1440351
  · exact B1440355
  · exact B1440359
  · exact B1440363
  · exact B1440367
  · exact B1440371
  · exact B1440375
  · exact B1440379
  · exact B1440383
  · exact B1440387
  · exact B1440391
  · exact B1440395
  · exact B1440399
  · exact B1440403
  · exact B1440407
  · exact B1440411
  · exact B1440415
  · exact B1440419
  · exact B1440423
  · exact B1440427
  · exact B1440431
  · exact B1440435
  · exact B1440439
  · exact B1440443
  · exact B1440447
  · exact B1440451
  · exact B1440455
  · exact B1440459
  · exact B1440463
  · exact B1440467
  · exact B1440471
  · exact B1440475
  · exact B1440479
  · exact B1440483
  · exact B1440487
  · exact B1440491
  · exact B1440495
  · exact B1440499
  · exact B1440503
  · exact B1440507
  · exact B1440511
  · exact B1440515
  · exact B1440519
  · exact B1440523
  · exact B1440527
  · exact B1440531
  · exact B1440535
  · exact B1440539
  · exact B1440543
  · exact B1440547
  · exact B1440551
  · exact B1440555
  · exact B1440559
  · exact B1440563
  · exact B1440567
  · exact B1440571
  · exact B1440575
  · exact B1440579
  · exact B1440583
  · exact B1440587
  · exact B1440591
  · exact B1440595
  · exact B1440599
  · exact B1440603
  · exact B1440607
  · exact B1440611
  · exact B1440615
  · exact B1440619
  · exact B1440623
  · exact B1440627
  · exact B1440631
  · exact B1440635
  · exact B1440639
  · exact B1440643
  · exact B1440647
  · exact B1440651
  · exact B1440655
  · exact B1440659
  · exact B1440663
  · exact B1440667
  · exact B1440671
  · exact B1440675
  · exact B1440679
  · exact B1440683
  · exact B1440687
  · exact B1440691
  · exact B1440695
  · exact B1440699
  · exact B1440703
  · exact B1440707
  · exact B1440711
  · exact B1440715
  · exact B1440719
  · exact B1440723
  · exact B1440727
  · exact B1440731
  · exact B1440735
  · exact B1440739
  · exact B1440743
  · exact B1440747
  · exact B1440751
  · exact B1440755
  · exact B1440759
  · exact B1440763
  · exact B1440767
  · exact B1440771
  · exact B1440775
  · exact B1440779
  · exact B1440783
  · exact B1440787
  · exact B1440791
  · exact B1440795
  · exact B1440799
  · exact B1440803
  · exact B1440807
  · exact B1440811
  · exact B1440815
  · exact B1440819
  · exact B1440823
  · exact B1440827
  · exact B1440831
  · exact B1440835
  · exact B1440839
  · exact B1440843
  · exact B1440847
  · exact B1440851
  · exact B1440855
  · exact B1440859
  · exact B1440863
  · exact B1440867
  · exact B1440871
  · exact B1440875
  · exact B1440879
  · exact B1440883
  · exact B1440887
  · exact B1440891
  · exact B1440895
  · exact B1440899
  · exact B1440903
  · exact B1440907
  · exact B1440911
  · exact B1440915
  · exact B1440919
  · exact B1440923
  · exact B1440927
  · exact B1440931
  · exact B1440935
  · exact B1440939
  · exact B1440943
  · exact B1440947
  · exact B1440951
  · exact B1440955
  · exact B1440959
  · exact B1440963
  · exact B1440967
  · exact B1440971
  · exact B1440975
  · exact B1440979
  · exact B1440983
  · exact B1440987
  · exact B1440991
  · exact B1440995
  · exact B1440999
  · exact B1441003
  · exact B1441007
  · exact B1441011
  · exact B1441015
  · exact B1441019
  · exact B1441023
  · exact B1441027
  · exact B1441031
  · exact B1441035
  · exact B1441039
  · exact B1441043
  · exact B1441047
  · exact B1441051
  · exact B1441055
  · exact B1441059
  · exact B1441063
  · exact B1441067
  · exact B1441071
  · exact B1441075
  · exact B1441079
  · exact B1441083
  · exact B1441087
  · exact B1441091
  · exact B1441095
  · exact B1441099
  · exact B1441103
  · exact B1441107
  · exact B1441111
  · exact B1441115
  · exact B1441119
  · exact B1441123
  · exact B1441127
  · exact B1441131
  · exact B1441135
  · exact B1441139
  · exact B1441143
  · exact B1441147
  · exact B1441151
  · exact B1441155
  · exact B1441159
  · exact B1441163
  · exact B1441167
  · exact B1441171
  · exact B1441175
  · exact B1441179
  · exact B1441183
  · exact B1441187
  · exact B1441191
  · exact B1441195
  · exact B1441199
  · exact B1441203
  · exact B1441207
  · exact B1441211
  · exact B1441215
  · exact B1441219
  · exact B1441223
  · exact B1441227
  · exact B1441231
  · exact B1441235
  · exact B1441239
  · exact B1441243
  · exact B1441247
  · exact B1441251
  · exact B1441255
  · exact B1441259
  · exact B1441263
  · exact B1441267
  · exact B1441271
  · exact B1441275
  · exact B1441279
  · exact B1441283
  · exact B1441287
  · exact B1441291
  · exact B1441295
  · exact B1441299
  · exact B1441303
  · exact B1441307
  · exact B1441311
  · exact B1441315
  · exact B1441319
  · exact B1441323
  · exact B1441327
  · exact B1441331
  · exact B1441335
  · exact B1441339
  · exact B1441343
  · exact B1441347
  · exact B1441351
  · exact B1441355
  · exact B1441359
  · exact B1441363
  · exact B1441367
  · exact B1441371
  · exact B1441375
  · exact B1441379
  · exact B1441383
  · exact B1441387
  · exact B1441391
  · exact B1441395
  · exact B1441399
  · exact B1441403
  · exact B1441407
  · exact B1441411
  · exact B1441415
  · exact B1441419
  · exact B1441423
  · exact B1441427
  · exact B1441431
  · exact B1441435
  · exact B1441439
  · exact B1441443
  · exact B1441447
  · exact B1441451
  · exact B1441455
  · exact B1441459
  · exact B1441463
  · exact B1441467
  · exact B1441471
  · exact B1441475
  · exact B1441479
  · exact B1441483
  · exact B1441487
  · exact B1441491
  · exact B1441495
  · exact B1441499
  · exact B1441503
  · exact B1441507
  · exact B1441511
  · exact B1441515
  · exact B1441519
  · exact B1441523
  · exact B1441527
  · exact B1441531
  · exact B1441535
  · exact B1441539

theorem solution (m : ℕ) (hlo : 1439539 ≤ m) (hhi : m ≤ 1441539) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 359884 ≤ j := by omega
    have hj2 : j ≤ 360384 := by omega
    have hb : Blo 1439539 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
