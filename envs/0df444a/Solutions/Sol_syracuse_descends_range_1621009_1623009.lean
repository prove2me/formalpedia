-- Prove2me | solution 1 for syracuse_descends_range_1621009_1623009
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:13:15.736503+00:00
-- url     : https://prove2.me/submissions/29a5640b-27a9-460d-b9ed-adc33b94d947

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


theorem B2433029 : Blo 1621009 2433029 := bbase (se 4 (by rfl) ⟨228096, by rfl⟩ : syracuseStep 2433029 = 456193) (by norm_num)
theorem B2433053 : Blo 1621009 2433053 := bbase (se 3 (by rfl) ⟨456197, by rfl⟩ : syracuseStep 2433053 = 912395) (by norm_num)
theorem B4104229 : Blo 1621009 4104229 := bbase (se 4 (by rfl) ⟨384771, by rfl⟩ : syracuseStep 4104229 = 769543) (by norm_num)
theorem B2736173 : Blo 1621009 2736173 := bbase (se 3 (by rfl) ⟨513032, by rfl⟩ : syracuseStep 2736173 = 1026065) (by norm_num)
theorem B2433077 : Blo 1621009 2433077 := bbase (se 5 (by rfl) ⟨114050, by rfl⟩ : syracuseStep 2433077 = 228101) (by norm_num)
theorem B10395701 : Blo 1621009 10395701 := bbase (se 5 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 10395701 = 974597) (by norm_num)
theorem B3080261 : Blo 1621009 3080261 := bbase (se 4 (by rfl) ⟨288774, by rfl⟩ : syracuseStep 3080261 = 577549) (by norm_num)
theorem B2433101 : Blo 1621009 2433101 := bbase (se 3 (by rfl) ⟨456206, by rfl⟩ : syracuseStep 2433101 = 912413) (by norm_num)
theorem B2433125 : Blo 1621009 2433125 := bbase (se 4 (by rfl) ⟨228105, by rfl⟩ : syracuseStep 2433125 = 456211) (by norm_num)
theorem B3473509 : Blo 1621009 3473509 := bbase (se 4 (by rfl) ⟨325641, by rfl⟩ : syracuseStep 3473509 = 651283) (by norm_num)
theorem B2433149 : Blo 1621009 2433149 := bbase (se 3 (by rfl) ⟨456215, by rfl⟩ : syracuseStep 2433149 = 912431) (by norm_num)
theorem B4104341 : Blo 1621009 4104341 := bbase (se 6 (by rfl) ⟨96195, by rfl⟩ : syracuseStep 4104341 = 192391) (by norm_num)
theorem B9863317 : Blo 1621009 9863317 := bbase (se 6 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 9863317 = 462343) (by norm_num)
theorem B2433173 : Blo 1621009 2433173 := bbase (se 6 (by rfl) ⟨57027, by rfl⟩ : syracuseStep 2433173 = 114055) (by norm_num)
theorem B2736301 : Blo 1621009 2736301 := bbase (se 3 (by rfl) ⟨513056, by rfl⟩ : syracuseStep 2736301 = 1026113) (by norm_num)
theorem B2433197 : Blo 1621009 2433197 := bbase (se 3 (by rfl) ⟨456224, by rfl⟩ : syracuseStep 2433197 = 912449) (by norm_num)
theorem B2433221 : Blo 1621009 2433221 := bbase (se 4 (by rfl) ⟨228114, by rfl⟩ : syracuseStep 2433221 = 456229) (by norm_num)
theorem B6004949 : Blo 1621009 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B21070037 : Blo 1621009 21070037 := bbase (se 7 (by rfl) ⟨246914, by rfl⟩ : syracuseStep 21070037 = 493829) (by norm_num)
theorem B3080405 : Blo 1621009 3080405 := bbase (se 7 (by rfl) ⟨36098, by rfl⟩ : syracuseStep 3080405 = 72197) (by norm_num)
theorem B2433245 : Blo 1621009 2433245 := bbase (se 3 (by rfl) ⟨456233, by rfl⟩ : syracuseStep 2433245 = 912467) (by norm_num)
theorem B2433269 : Blo 1621009 2433269 := bbase (se 5 (by rfl) ⟨114059, by rfl⟩ : syracuseStep 2433269 = 228119) (by norm_num)
theorem B2736389 : Blo 1621009 2736389 := bbase (se 4 (by rfl) ⟨256536, by rfl⟩ : syracuseStep 2736389 = 513073) (by norm_num)
theorem B2433293 : Blo 1621009 2433293 := bbase (se 3 (by rfl) ⟨456242, by rfl⟩ : syracuseStep 2433293 = 912485) (by norm_num)
theorem B2433317 : Blo 1621009 2433317 := bbase (se 4 (by rfl) ⟨228123, by rfl⟩ : syracuseStep 2433317 = 456247) (by norm_num)
theorem B2433341 : Blo 1621009 2433341 := bbase (se 3 (by rfl) ⟨456251, by rfl⟩ : syracuseStep 2433341 = 912503) (by norm_num)
theorem B3465541 : Blo 1621009 3465541 := bbase (se 4 (by rfl) ⟨324894, by rfl⟩ : syracuseStep 3465541 = 649789) (by norm_num)
theorem B4104533 : Blo 1621009 4104533 := bbase (se 10 (by rfl) ⟨6012, by rfl⟩ : syracuseStep 4104533 = 12025) (by norm_num)
theorem B2433365 : Blo 1621009 2433365 := bbase (se 10 (by rfl) ⟨3564, by rfl⟩ : syracuseStep 2433365 = 7129) (by norm_num)
theorem B2433389 : Blo 1621009 2433389 := bbase (se 3 (by rfl) ⟨456260, by rfl⟩ : syracuseStep 2433389 = 912521) (by norm_num)
theorem B5472629 : Blo 1621009 5472629 := bbase (se 5 (by rfl) ⟨256529, by rfl⟩ : syracuseStep 5472629 = 513059) (by norm_num)
theorem B2736517 : Blo 1621009 2736517 := bbase (se 4 (by rfl) ⟨256548, by rfl⟩ : syracuseStep 2736517 = 513097) (by norm_num)
theorem B2433413 : Blo 1621009 2433413 := bbase (se 4 (by rfl) ⟨228132, by rfl⟩ : syracuseStep 2433413 = 456265) (by norm_num)
theorem B2433437 : Blo 1621009 2433437 := bbase (se 3 (by rfl) ⟨456269, by rfl⟩ : syracuseStep 2433437 = 912539) (by norm_num)
theorem B2597285 : Blo 1621009 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B2433461 : Blo 1621009 2433461 := bbase (se 5 (by rfl) ⟨114068, by rfl⟩ : syracuseStep 2433461 = 228137) (by norm_num)
theorem B3465661 : Blo 1621009 3465661 := bbase (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) (by norm_num)
theorem B7799237 : Blo 1621009 7799237 := bbase (se 4 (by rfl) ⟨731178, by rfl⟩ : syracuseStep 7799237 = 1462357) (by norm_num)
theorem B2433485 : Blo 1621009 2433485 := bbase (se 3 (by rfl) ⟨456278, by rfl⟩ : syracuseStep 2433485 = 912557) (by norm_num)
theorem B2736605 : Blo 1621009 2736605 := bbase (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) (by norm_num)
theorem B2433509 : Blo 1621009 2433509 := bbase (se 4 (by rfl) ⟨228141, by rfl⟩ : syracuseStep 2433509 = 456283) (by norm_num)
theorem B3080693 : Blo 1621009 3080693 := bbase (se 5 (by rfl) ⟨144407, by rfl⟩ : syracuseStep 3080693 = 288815) (by norm_num)
theorem B2433533 : Blo 1621009 2433533 := bbase (se 3 (by rfl) ⟨456287, by rfl⟩ : syracuseStep 2433533 = 912575) (by norm_num)
theorem B2433557 : Blo 1621009 2433557 := bbase (se 6 (by rfl) ⟨57036, by rfl⟩ : syracuseStep 2433557 = 114073) (by norm_num)
theorem B2433581 : Blo 1621009 2433581 := bbase (se 3 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 2433581 = 912593) (by norm_num)
theorem B2433605 : Blo 1621009 2433605 := bbase (se 4 (by rfl) ⟨228150, by rfl⟩ : syracuseStep 2433605 = 456301) (by norm_num)
theorem B2310725 : Blo 1621009 2310725 := bbase (se 4 (by rfl) ⟨216630, by rfl⟩ : syracuseStep 2310725 = 433261) (by norm_num)
theorem B10535509 : Blo 1621009 10535509 := bbase (se 8 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 10535509 = 123463) (by norm_num)
theorem B2736733 : Blo 1621009 2736733 := bbase (se 3 (by rfl) ⟨513137, by rfl⟩ : syracuseStep 2736733 = 1026275) (by norm_num)
theorem B2433629 : Blo 1621009 2433629 := bbase (se 3 (by rfl) ⟨456305, by rfl⟩ : syracuseStep 2433629 = 912611) (by norm_num)
theorem B2433653 : Blo 1621009 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B2433677 : Blo 1621009 2433677 := bbase (se 3 (by rfl) ⟨456314, by rfl⟩ : syracuseStep 2433677 = 912629) (by norm_num)
theorem B3080845 : Blo 1621009 3080845 := bbase (se 3 (by rfl) ⟨577658, by rfl⟩ : syracuseStep 3080845 = 1155317) (by norm_num)
theorem B2310805 : Blo 1621009 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B2433701 : Blo 1621009 2433701 := bbase (se 4 (by rfl) ⟨228159, by rfl⟩ : syracuseStep 2433701 = 456319) (by norm_num)
theorem B4104877 : Blo 1621009 4104877 := bbase (se 3 (by rfl) ⟨769664, by rfl⟩ : syracuseStep 4104877 = 1539329) (by norm_num)
theorem B2736821 : Blo 1621009 2736821 := bbase (se 5 (by rfl) ⟨128288, by rfl⟩ : syracuseStep 2736821 = 256577) (by norm_num)
theorem B2433725 : Blo 1621009 2433725 := bbase (se 3 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 2433725 = 912647) (by norm_num)
theorem B3465917 : Blo 1621009 3465917 := bbase (se 3 (by rfl) ⟨649859, by rfl⟩ : syracuseStep 3465917 = 1299719) (by norm_num)
theorem B2433749 : Blo 1621009 2433749 := bbase (se 7 (by rfl) ⟨28520, by rfl⟩ : syracuseStep 2433749 = 57041) (by norm_num)
theorem B2433773 : Blo 1621009 2433773 := bbase (se 3 (by rfl) ⟨456332, by rfl⟩ : syracuseStep 2433773 = 912665) (by norm_num)
theorem B2433797 : Blo 1621009 2433797 := bbase (se 4 (by rfl) ⟨228168, by rfl⟩ : syracuseStep 2433797 = 456337) (by norm_num)
theorem B12321557 : Blo 1621009 12321557 := bbase (se 6 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 12321557 = 577573) (by norm_num)
theorem B4104989 : Blo 1621009 4104989 := bbase (se 3 (by rfl) ⟨769685, by rfl⟩ : syracuseStep 4104989 = 1539371) (by norm_num)
theorem B2433821 : Blo 1621009 2433821 := bbase (se 3 (by rfl) ⟨456341, by rfl⟩ : syracuseStep 2433821 = 912683) (by norm_num)
theorem B5473061 : Blo 1621009 5473061 := bbase (se 4 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 5473061 = 1026199) (by norm_num)
theorem B2736949 : Blo 1621009 2736949 := bbase (se 5 (by rfl) ⟨128294, by rfl⟩ : syracuseStep 2736949 = 256589) (by norm_num)
theorem B2433845 : Blo 1621009 2433845 := bbase (se 5 (by rfl) ⟨114086, by rfl⟩ : syracuseStep 2433845 = 228173) (by norm_num)
theorem B9241397 : Blo 1621009 9241397 := bbase (se 5 (by rfl) ⟨433190, by rfl⟩ : syracuseStep 9241397 = 866381) (by norm_num)
theorem B2433869 : Blo 1621009 2433869 := bbase (se 3 (by rfl) ⟨456350, by rfl⟩ : syracuseStep 2433869 = 912701) (by norm_num)
theorem B2433893 : Blo 1621009 2433893 := bbase (se 4 (by rfl) ⟨228177, by rfl⟩ : syracuseStep 2433893 = 456355) (by norm_num)
theorem B2597741 : Blo 1621009 2597741 := bbase (se 3 (by rfl) ⟨487076, by rfl⟩ : syracuseStep 2597741 = 974153) (by norm_num)
theorem B2433917 : Blo 1621009 2433917 := bbase (se 3 (by rfl) ⟨456359, by rfl⟩ : syracuseStep 2433917 = 912719) (by norm_num)
theorem B2737037 : Blo 1621009 2737037 := bbase (se 3 (by rfl) ⟨513194, by rfl⟩ : syracuseStep 2737037 = 1026389) (by norm_num)
theorem B2433941 : Blo 1621009 2433941 := bbase (se 6 (by rfl) ⟨57045, by rfl⟩ : syracuseStep 2433941 = 114091) (by norm_num)
theorem B2433965 : Blo 1621009 2433965 := bbase (se 3 (by rfl) ⟨456368, by rfl⟩ : syracuseStep 2433965 = 912737) (by norm_num)
theorem B3081149 : Blo 1621009 3081149 := bbase (se 3 (by rfl) ⟨577715, by rfl⟩ : syracuseStep 3081149 = 1155431) (by norm_num)
theorem B8209349 : Blo 1621009 8209349 := bbase (se 4 (by rfl) ⟨769626, by rfl⟩ : syracuseStep 8209349 = 1539253) (by norm_num)
theorem B2433989 : Blo 1621009 2433989 := bbase (se 4 (by rfl) ⟨228186, by rfl⟩ : syracuseStep 2433989 = 456373) (by norm_num)
theorem B4105181 : Blo 1621009 4105181 := bbase (se 3 (by rfl) ⟨769721, by rfl⟩ : syracuseStep 4105181 = 1539443) (by norm_num)
theorem B2434013 : Blo 1621009 2434013 := bbase (se 3 (by rfl) ⟨456377, by rfl⟩ : syracuseStep 2434013 = 912755) (by norm_num)
theorem B2434037 : Blo 1621009 2434037 := bbase (se 5 (by rfl) ⟨114095, by rfl⟩ : syracuseStep 2434037 = 228191) (by norm_num)
theorem B2737165 : Blo 1621009 2737165 := bbase (se 3 (by rfl) ⟨513218, by rfl⟩ : syracuseStep 2737165 = 1026437) (by norm_num)
theorem B2434061 : Blo 1621009 2434061 := bbase (se 3 (by rfl) ⟨456386, by rfl⟩ : syracuseStep 2434061 = 912773) (by norm_num)
theorem B2434085 : Blo 1621009 2434085 := bbase (se 4 (by rfl) ⟨228195, by rfl⟩ : syracuseStep 2434085 = 456391) (by norm_num)
theorem B6931493 : Blo 1621009 6931493 := bbase (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) (by norm_num)
theorem B2434109 : Blo 1621009 2434109 := bbase (se 3 (by rfl) ⟨456395, by rfl⟩ : syracuseStep 2434109 = 912791) (by norm_num)
theorem B2434133 : Blo 1621009 2434133 := bbase (se 8 (by rfl) ⟨14262, by rfl⟩ : syracuseStep 2434133 = 28525) (by norm_num)
theorem B2737253 : Blo 1621009 2737253 := bbase (se 4 (by rfl) ⟨256617, by rfl⟩ : syracuseStep 2737253 = 513235) (by norm_num)
theorem B2434157 : Blo 1621009 2434157 := bbase (se 3 (by rfl) ⟨456404, by rfl⟩ : syracuseStep 2434157 = 912809) (by norm_num)
theorem B2434181 : Blo 1621009 2434181 := bbase (se 4 (by rfl) ⟨228204, by rfl⟩ : syracuseStep 2434181 = 456409) (by norm_num)
theorem B2434205 : Blo 1621009 2434205 := bbase (se 3 (by rfl) ⟨456413, by rfl⟩ : syracuseStep 2434205 = 912827) (by norm_num)
theorem B12313781 : Blo 1621009 12313781 := bbase (se 5 (by rfl) ⟨577208, by rfl⟩ : syracuseStep 12313781 = 1154417) (by norm_num)
theorem B1975477 : Blo 1621009 1975477 := bbase (se 5 (by rfl) ⟨92600, by rfl⟩ : syracuseStep 1975477 = 185201) (by norm_num)
theorem B2466997 : Blo 1621009 2466997 := bbase (se 5 (by rfl) ⟨115640, by rfl⟩ : syracuseStep 2466997 = 231281) (by norm_num)
theorem B2434229 : Blo 1621009 2434229 := bbase (se 5 (by rfl) ⟨114104, by rfl⟩ : syracuseStep 2434229 = 228209) (by norm_num)
theorem B2434253 : Blo 1621009 2434253 := bbase (se 3 (by rfl) ⟨456422, by rfl⟩ : syracuseStep 2434253 = 912845) (by norm_num)
theorem B5473493 : Blo 1621009 5473493 := bbase (se 7 (by rfl) ⟨64142, by rfl⟩ : syracuseStep 5473493 = 128285) (by norm_num)
theorem B2737381 : Blo 1621009 2737381 := bbase (se 4 (by rfl) ⟨256629, by rfl⟩ : syracuseStep 2737381 = 513259) (by norm_num)
theorem B2434277 : Blo 1621009 2434277 := bbase (se 4 (by rfl) ⟨228213, by rfl⟩ : syracuseStep 2434277 = 456427) (by norm_num)
theorem B2434301 : Blo 1621009 2434301 := bbase (se 3 (by rfl) ⟨456431, by rfl⟩ : syracuseStep 2434301 = 912863) (by norm_num)
theorem B2434325 : Blo 1621009 2434325 := bbase (se 6 (by rfl) ⟨57054, by rfl⟩ : syracuseStep 2434325 = 114109) (by norm_num)
theorem B6325541 : Blo 1621009 6325541 := bbase (se 4 (by rfl) ⟨593019, by rfl⟩ : syracuseStep 6325541 = 1186039) (by norm_num)
theorem B2434349 : Blo 1621009 2434349 := bbase (se 3 (by rfl) ⟨456440, by rfl⟩ : syracuseStep 2434349 = 912881) (by norm_num)
theorem B4105525 : Blo 1621009 4105525 := bbase (se 5 (by rfl) ⟨192446, by rfl⟩ : syracuseStep 4105525 = 384893) (by norm_num)
theorem B2737469 : Blo 1621009 2737469 := bbase (se 3 (by rfl) ⟨513275, by rfl⟩ : syracuseStep 2737469 = 1026551) (by norm_num)
theorem B2434373 : Blo 1621009 2434373 := bbase (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) (by norm_num)
theorem B2434397 : Blo 1621009 2434397 := bbase (se 3 (by rfl) ⟨456449, by rfl⟩ : syracuseStep 2434397 = 912899) (by norm_num)
theorem B5842277 : Blo 1621009 5842277 := bbase (se 4 (by rfl) ⟨547713, by rfl⟩ : syracuseStep 5842277 = 1095427) (by norm_num)
theorem B2434421 : Blo 1621009 2434421 := bbase (se 5 (by rfl) ⟨114113, by rfl⟩ : syracuseStep 2434421 = 228227) (by norm_num)
theorem B6849925 : Blo 1621009 6849925 := bbase (se 4 (by rfl) ⟨642180, by rfl⟩ : syracuseStep 6849925 = 1284361) (by norm_num)
theorem B2434445 : Blo 1621009 2434445 := bbase (se 3 (by rfl) ⟨456458, by rfl⟩ : syracuseStep 2434445 = 912917) (by norm_num)
theorem B5195173 : Blo 1621009 5195173 := bbase (se 4 (by rfl) ⟨487047, by rfl⟩ : syracuseStep 5195173 = 974095) (by norm_num)
theorem B4105637 : Blo 1621009 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2434469 : Blo 1621009 2434469 := bbase (se 4 (by rfl) ⟨228231, by rfl⟩ : syracuseStep 2434469 = 456463) (by norm_num)
theorem B14050741 : Blo 1621009 14050741 := bbase (se 5 (by rfl) ⟨658628, by rfl⟩ : syracuseStep 14050741 = 1317257) (by norm_num)
theorem B2737597 : Blo 1621009 2737597 := bbase (se 3 (by rfl) ⟨513299, by rfl⟩ : syracuseStep 2737597 = 1026599) (by norm_num)
theorem B2434493 : Blo 1621009 2434493 := bbase (se 3 (by rfl) ⟨456467, by rfl⟩ : syracuseStep 2434493 = 912935) (by norm_num)
theorem B2737685 : Blo 1621009 2737685 := bbase (se 6 (by rfl) ⟨64164, by rfl⟩ : syracuseStep 2737685 = 128329) (by norm_num)
theorem B4105829 : Blo 1621009 4105829 := bbase (se 4 (by rfl) ⟨384921, by rfl⟩ : syracuseStep 4105829 = 769843) (by norm_num)
theorem B1754741 : Blo 1621009 1754741 := bbase (se 5 (by rfl) ⟨82253, by rfl⟩ : syracuseStep 1754741 = 164507) (by norm_num)
theorem B5473925 : Blo 1621009 5473925 := bbase (se 4 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 5473925 = 1026361) (by norm_num)
theorem B2737813 : Blo 1621009 2737813 := bbase (se 6 (by rfl) ⟨64167, by rfl⟩ : syracuseStep 2737813 = 128335) (by norm_num)
theorem B4679333 : Blo 1621009 4679333 := bbase (se 4 (by rfl) ⟨438687, by rfl⟩ : syracuseStep 4679333 = 877375) (by norm_num)
theorem B6162101 : Blo 1621009 6162101 := bbase (se 5 (by rfl) ⟨288848, by rfl⟩ : syracuseStep 6162101 = 577697) (by norm_num)
theorem B2737901 : Blo 1621009 2737901 := bbase (se 3 (by rfl) ⟨513356, by rfl⟩ : syracuseStep 2737901 = 1026713) (by norm_num)
theorem B3647285 : Blo 1621009 3647285 := bbase (se 5 (by rfl) ⟨170966, by rfl⟩ : syracuseStep 3647285 = 341933) (by norm_num)
theorem B2598733 : Blo 1621009 2598733 := bbase (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) (by norm_num)
theorem B2738029 : Blo 1621009 2738029 := bbase (se 3 (by rfl) ⟨513380, by rfl⟩ : syracuseStep 2738029 = 1026761) (by norm_num)
theorem B3647357 : Blo 1621009 3647357 := bbase (se 3 (by rfl) ⟨683879, by rfl⟩ : syracuseStep 3647357 = 1367759) (by norm_num)
theorem B4106173 : Blo 1621009 4106173 := bbase (se 3 (by rfl) ⟨769907, by rfl⟩ : syracuseStep 4106173 = 1539815) (by norm_num)
theorem B3647429 : Blo 1621009 3647429 := bbase (se 4 (by rfl) ⟨341946, by rfl⟩ : syracuseStep 3647429 = 683893) (by norm_num)
theorem B2738117 : Blo 1621009 2738117 := bbase (se 4 (by rfl) ⟨256698, by rfl⟩ : syracuseStep 2738117 = 513397) (by norm_num)
theorem B3647501 : Blo 1621009 3647501 := bbase (se 3 (by rfl) ⟨683906, by rfl⟩ : syracuseStep 3647501 = 1367813) (by norm_num)
theorem B4106285 : Blo 1621009 4106285 := bbase (se 3 (by rfl) ⟨769928, by rfl⟩ : syracuseStep 4106285 = 1539857) (by norm_num)
theorem B5474357 : Blo 1621009 5474357 := bbase (se 5 (by rfl) ⟨256610, by rfl⟩ : syracuseStep 5474357 = 513221) (by norm_num)
theorem B2738245 : Blo 1621009 2738245 := bbase (se 4 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 2738245 = 513421) (by norm_num)
theorem B3647573 : Blo 1621009 3647573 := bbase (se 8 (by rfl) ⟨21372, by rfl⟩ : syracuseStep 3647573 = 42745) (by norm_num)
theorem B6924437 : Blo 1621009 6924437 := bbase (se 6 (by rfl) ⟨162291, by rfl⟩ : syracuseStep 6924437 = 324583) (by norm_num)
theorem B10389653 : Blo 1621009 10389653 := bbase (se 6 (by rfl) ⟨243507, by rfl⟩ : syracuseStep 10389653 = 487015) (by norm_num)
theorem B31180949 : Blo 1621009 31180949 := bbase (se 6 (by rfl) ⟨730803, by rfl⟩ : syracuseStep 31180949 = 1461607) (by norm_num)
theorem B3647645 : Blo 1621009 3647645 := bbase (se 3 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 3647645 = 1367867) (by norm_num)
theorem B2738333 : Blo 1621009 2738333 := bbase (se 3 (by rfl) ⟨513437, by rfl⟩ : syracuseStep 2738333 = 1026875) (by norm_num)
theorem B8210645 : Blo 1621009 8210645 := bbase (se 7 (by rfl) ⟨96218, by rfl⟩ : syracuseStep 8210645 = 192437) (by norm_num)
theorem B3647717 : Blo 1621009 3647717 := bbase (se 4 (by rfl) ⟨341973, by rfl⟩ : syracuseStep 3647717 = 683947) (by norm_num)
theorem B5196005 : Blo 1621009 5196005 := bbase (se 4 (by rfl) ⟨487125, by rfl⟩ : syracuseStep 5196005 = 974251) (by norm_num)
theorem B4106477 : Blo 1621009 4106477 := bbase (se 3 (by rfl) ⟨769964, by rfl⟩ : syracuseStep 4106477 = 1539929) (by norm_num)
theorem B2500853 : Blo 1621009 2500853 := bbase (se 5 (by rfl) ⟨117227, by rfl⟩ : syracuseStep 2500853 = 234455) (by norm_num)
theorem B14805269 : Blo 1621009 14805269 := bbase (se 6 (by rfl) ⟨346998, by rfl⟩ : syracuseStep 14805269 = 693997) (by norm_num)
theorem B2738461 : Blo 1621009 2738461 := bbase (se 3 (by rfl) ⟨513461, by rfl⟩ : syracuseStep 2738461 = 1026923) (by norm_num)
theorem B3647789 : Blo 1621009 3647789 := bbase (se 3 (by rfl) ⟨683960, by rfl⟩ : syracuseStep 3647789 = 1367921) (by norm_num)
theorem B3647861 : Blo 1621009 3647861 := bbase (se 5 (by rfl) ⟨170993, by rfl⟩ : syracuseStep 3647861 = 341987) (by norm_num)
theorem B2738549 : Blo 1621009 2738549 := bbase (se 5 (by rfl) ⟨128369, by rfl⟩ : syracuseStep 2738549 = 256739) (by norm_num)
theorem B3647933 : Blo 1621009 3647933 := bbase (se 3 (by rfl) ⟨683987, by rfl⟩ : syracuseStep 3647933 = 1367975) (by norm_num)
theorem B2599381 : Blo 1621009 2599381 := bbase (se 7 (by rfl) ⟨30461, by rfl⟩ : syracuseStep 2599381 = 60923) (by norm_num)
theorem B5474789 : Blo 1621009 5474789 := bbase (se 4 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 5474789 = 1026523) (by norm_num)
theorem B2738677 : Blo 1621009 2738677 := bbase (se 5 (by rfl) ⟨128375, by rfl⟩ : syracuseStep 2738677 = 256751) (by norm_num)
theorem B3951101 : Blo 1621009 3951101 := bbase (se 3 (by rfl) ⟨740831, by rfl⟩ : syracuseStep 3951101 = 1481663) (by norm_num)
theorem B3648005 : Blo 1621009 3648005 := bbase (se 4 (by rfl) ⟨342000, by rfl⟩ : syracuseStep 3648005 = 684001) (by norm_num)
theorem B14789141 : Blo 1621009 14789141 := bbase (se 6 (by rfl) ⟨346620, by rfl⟩ : syracuseStep 14789141 = 693241) (by norm_num)
theorem B4106821 : Blo 1621009 4106821 := bbase (se 4 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 4106821 = 770029) (by norm_num)
theorem B3648077 : Blo 1621009 3648077 := bbase (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) (by norm_num)
theorem B2738765 : Blo 1621009 2738765 := bbase (se 3 (by rfl) ⟨513518, by rfl⟩ : syracuseStep 2738765 = 1027037) (by norm_num)
theorem B2632333 : Blo 1621009 2632333 := bbase (se 3 (by rfl) ⟨493562, by rfl⟩ : syracuseStep 2632333 = 987125) (by norm_num)
theorem B3648149 : Blo 1621009 3648149 := bbase (se 6 (by rfl) ⟨85503, by rfl⟩ : syracuseStep 3648149 = 171007) (by norm_num)
theorem B1731233 : Blo 1621009 1731233 := bbase (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) (by norm_num)
theorem B4106933 : Blo 1621009 4106933 := bbase (se 5 (by rfl) ⟨192512, by rfl⟩ : syracuseStep 4106933 = 385025) (by norm_num)
theorem B3648221 : Blo 1621009 3648221 := bbase (se 3 (by rfl) ⟨684041, by rfl⟩ : syracuseStep 3648221 = 1368083) (by norm_num)
theorem B3648293 : Blo 1621009 3648293 := bbase (se 4 (by rfl) ⟨342027, by rfl⟩ : syracuseStep 3648293 = 684055) (by norm_num)
theorem B10529621 : Blo 1621009 10529621 := bbase (se 9 (by rfl) ⟨30848, by rfl⟩ : syracuseStep 10529621 = 61697) (by norm_num)
theorem B3648365 : Blo 1621009 3648365 := bbase (se 3 (by rfl) ⟨684068, by rfl⟩ : syracuseStep 3648365 = 1368137) (by norm_num)
theorem B4107125 : Blo 1621009 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B5475221 : Blo 1621009 5475221 := bbase (se 6 (by rfl) ⟨128325, by rfl⟩ : syracuseStep 5475221 = 256651) (by norm_num)
theorem B3648437 : Blo 1621009 3648437 := bbase (se 5 (by rfl) ⟨171020, by rfl⟩ : syracuseStep 3648437 = 342041) (by norm_num)
theorem B3648509 : Blo 1621009 3648509 := bbase (se 3 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 3648509 = 1368191) (by norm_num)
theorem B5549093 : Blo 1621009 5549093 := bbase (se 4 (by rfl) ⟨520227, by rfl⟩ : syracuseStep 5549093 = 1040455) (by norm_num)
theorem B3648581 : Blo 1621009 3648581 := bbase (se 4 (by rfl) ⟨342054, by rfl⟩ : syracuseStep 3648581 = 684109) (by norm_num)
theorem B1731677 : Blo 1621009 1731677 := bbase (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) (by norm_num)
theorem B4934773 : Blo 1621009 4934773 := bbase (se 5 (by rfl) ⟨231317, by rfl⟩ : syracuseStep 4934773 = 462635) (by norm_num)
theorem B6925445 : Blo 1621009 6925445 := bbase (se 4 (by rfl) ⟨649260, by rfl⟩ : syracuseStep 6925445 = 1298521) (by norm_num)
theorem B3648653 : Blo 1621009 3648653 := bbase (se 3 (by rfl) ⟨684122, by rfl⟩ : syracuseStep 3648653 = 1368245) (by norm_num)
theorem B1731737 : Blo 1621009 1731737 := bbase (se 2 (by rfl) ⟨649401, by rfl⟩ : syracuseStep 1731737 = 1298803) (by norm_num)
theorem B1666217 : Blo 1621009 1666217 := bbase (se 2 (by rfl) ⟨624831, by rfl⟩ : syracuseStep 1666217 = 1249663) (by norm_num)
theorem B4107469 : Blo 1621009 4107469 := bbase (se 3 (by rfl) ⟨770150, by rfl⟩ : syracuseStep 4107469 = 1540301) (by norm_num)
theorem B3648725 : Blo 1621009 3648725 := bbase (se 7 (by rfl) ⟨42758, by rfl⟩ : syracuseStep 3648725 = 85517) (by norm_num)
theorem B1731865 : Blo 1621009 1731865 := bbase (se 2 (by rfl) ⟨649449, by rfl⟩ : syracuseStep 1731865 = 1298899) (by norm_num)
theorem B3648797 : Blo 1621009 3648797 := bbase (se 3 (by rfl) ⟨684149, by rfl⟩ : syracuseStep 3648797 = 1368299) (by norm_num)
theorem B4107581 : Blo 1621009 4107581 := bbase (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) (by norm_num)
theorem B5475653 : Blo 1621009 5475653 := bbase (se 4 (by rfl) ⟨513342, by rfl⟩ : syracuseStep 5475653 = 1026685) (by norm_num)
theorem B52596053 : Blo 1621009 52596053 := bbase (se 11 (by rfl) ⟨38522, by rfl⟩ : syracuseStep 52596053 = 77045) (by norm_num)
theorem B3648869 : Blo 1621009 3648869 := bbase (se 4 (by rfl) ⟨342081, by rfl⟩ : syracuseStep 3648869 = 684163) (by norm_num)
theorem B3648941 : Blo 1621009 3648941 := bbase (se 3 (by rfl) ⟨684176, by rfl⟩ : syracuseStep 3648941 = 1368353) (by norm_num)
theorem B5336549 : Blo 1621009 5336549 := bbase (se 4 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 5336549 = 1000603) (by norm_num)
theorem B8211941 : Blo 1621009 8211941 := bbase (se 4 (by rfl) ⟨769869, by rfl⟩ : syracuseStep 8211941 = 1539739) (by norm_num)
theorem B3649013 : Blo 1621009 3649013 := bbase (se 5 (by rfl) ⟨171047, by rfl⟩ : syracuseStep 3649013 = 342095) (by norm_num)
theorem B4107773 : Blo 1621009 4107773 := bbase (se 3 (by rfl) ⟨770207, by rfl⟩ : syracuseStep 4107773 = 1540415) (by norm_num)
theorem B6155797 : Blo 1621009 6155797 := bbase (se 6 (by rfl) ⟨144276, by rfl⟩ : syracuseStep 6155797 = 288553) (by norm_num)
theorem B3649085 : Blo 1621009 3649085 := bbase (se 3 (by rfl) ⟨684203, by rfl⟩ : syracuseStep 3649085 = 1368407) (by norm_num)
theorem B2051669 : Blo 1621009 2051669 := bbase (se 8 (by rfl) ⟨12021, by rfl⟩ : syracuseStep 2051669 = 24043) (by norm_num)
theorem B3649157 : Blo 1621009 3649157 := bbase (se 4 (by rfl) ⟨342108, by rfl⟩ : syracuseStep 3649157 = 684217) (by norm_num)
theorem B2051725 : Blo 1621009 2051725 := bbase (se 3 (by rfl) ⟨384698, by rfl⟩ : syracuseStep 2051725 = 769397) (by norm_num)
theorem B3649229 : Blo 1621009 3649229 := bbase (se 3 (by rfl) ⟨684230, by rfl⟩ : syracuseStep 3649229 = 1368461) (by norm_num)
theorem B1732309 : Blo 1621009 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B2051821 : Blo 1621009 2051821 := bbase (se 3 (by rfl) ⟨384716, by rfl⟩ : syracuseStep 2051821 = 769433) (by norm_num)
theorem B5476085 : Blo 1621009 5476085 := bbase (se 5 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 5476085 = 513383) (by norm_num)
theorem B3649301 : Blo 1621009 3649301 := bbase (se 6 (by rfl) ⟨85530, by rfl⟩ : syracuseStep 3649301 = 171061) (by norm_num)
theorem B6156101 : Blo 1621009 6156101 := bbase (se 4 (by rfl) ⟨577134, by rfl⟩ : syracuseStep 6156101 = 1154269) (by norm_num)
theorem B1732429 : Blo 1621009 1732429 := bbase (se 3 (by rfl) ⟨324830, by rfl⟩ : syracuseStep 1732429 = 649661) (by norm_num)
theorem B4108117 : Blo 1621009 4108117 := bbase (se 9 (by rfl) ⟨12035, by rfl⟩ : syracuseStep 4108117 = 24071) (by norm_num)
theorem B3649373 : Blo 1621009 3649373 := bbase (se 3 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 3649373 = 1368515) (by norm_num)
theorem B3288941 : Blo 1621009 3288941 := bbase (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) (by norm_num)
theorem B2051993 : Blo 1621009 2051993 := bbase (se 2 (by rfl) ⟨769497, by rfl⟩ : syracuseStep 2051993 = 1538995) (by norm_num)
theorem B3649445 : Blo 1621009 3649445 := bbase (se 4 (by rfl) ⟨342135, by rfl⟩ : syracuseStep 3649445 = 684271) (by norm_num)
theorem B4108229 : Blo 1621009 4108229 := bbase (se 4 (by rfl) ⟨385146, by rfl⟩ : syracuseStep 4108229 = 770293) (by norm_num)
theorem B2052049 : Blo 1621009 2052049 := bbase (se 2 (by rfl) ⟨769518, by rfl⟩ : syracuseStep 2052049 = 1539037) (by norm_num)
theorem B4616165 : Blo 1621009 4616165 := bbase (se 4 (by rfl) ⟨432765, by rfl⟩ : syracuseStep 4616165 = 865531) (by norm_num)
theorem B3649517 : Blo 1621009 3649517 := bbase (se 3 (by rfl) ⟨684284, by rfl⟩ : syracuseStep 3649517 = 1368569) (by norm_num)
theorem B2052145 : Blo 1621009 2052145 := bbase (se 2 (by rfl) ⟨769554, by rfl⟩ : syracuseStep 2052145 = 1539109) (by norm_num)
theorem B3649589 : Blo 1621009 3649589 := bbase (se 5 (by rfl) ⟨171074, by rfl⟩ : syracuseStep 3649589 = 342149) (by norm_num)
theorem B5197877 : Blo 1621009 5197877 := bbase (se 5 (by rfl) ⟨243650, by rfl⟩ : syracuseStep 5197877 = 487301) (by norm_num)
theorem B1732681 : Blo 1621009 1732681 := bbase (se 2 (by rfl) ⟨649755, by rfl⟩ : syracuseStep 1732681 = 1299511) (by norm_num)
theorem B1732685 : Blo 1621009 1732685 := bbase (se 3 (by rfl) ⟨324878, by rfl⟩ : syracuseStep 1732685 = 649757) (by norm_num)
theorem B3895381 : Blo 1621009 3895381 := bbase (se 8 (by rfl) ⟨22824, by rfl⟩ : syracuseStep 3895381 = 45649) (by norm_num)
theorem B3649661 : Blo 1621009 3649661 := bbase (se 3 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 3649661 = 1368623) (by norm_num)
theorem B5476517 : Blo 1621009 5476517 := bbase (se 4 (by rfl) ⟨513423, by rfl⟩ : syracuseStep 5476517 = 1026847) (by norm_num)
theorem B2191541 : Blo 1621009 2191541 := bbase (se 5 (by rfl) ⟨102728, by rfl⟩ : syracuseStep 2191541 = 205457) (by norm_num)
theorem B3649733 : Blo 1621009 3649733 := bbase (se 4 (by rfl) ⟨342162, by rfl⟩ : syracuseStep 3649733 = 684325) (by norm_num)
theorem B2052317 : Blo 1621009 2052317 := bbase (se 3 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 2052317 = 769619) (by norm_num)
theorem B4681957 : Blo 1621009 4681957 := bbase (se 4 (by rfl) ⟨438933, by rfl⟩ : syracuseStep 4681957 = 877867) (by norm_num)
theorem B3649805 : Blo 1621009 3649805 := bbase (se 3 (by rfl) ⟨684338, by rfl⟩ : syracuseStep 3649805 = 1368677) (by norm_num)
theorem B2052373 : Blo 1621009 2052373 := bbase (se 6 (by rfl) ⟨48102, by rfl⟩ : syracuseStep 2052373 = 96205) (by norm_num)
theorem B3649877 : Blo 1621009 3649877 := bbase (se 10 (by rfl) ⟨5346, by rfl⟩ : syracuseStep 3649877 = 10693) (by norm_num)
theorem B3699037 : Blo 1621009 3699037 := bbase (se 3 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 3699037 = 1387139) (by norm_num)
theorem B2052469 : Blo 1621009 2052469 := bbase (se 5 (by rfl) ⟨96209, by rfl⟩ : syracuseStep 2052469 = 192419) (by norm_num)
theorem B27718037 : Blo 1621009 27718037 := bbase (se 6 (by rfl) ⟨649641, by rfl⟩ : syracuseStep 27718037 = 1299283) (by norm_num)
theorem B3649949 : Blo 1621009 3649949 := bbase (se 3 (by rfl) ⟨684365, by rfl⟩ : syracuseStep 3649949 = 1368731) (by norm_num)
theorem B7025093 : Blo 1621009 7025093 := bbase (se 4 (by rfl) ⟨658602, by rfl⟩ : syracuseStep 7025093 = 1317205) (by norm_num)
theorem B2773453 : Blo 1621009 2773453 := bbase (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) (by norm_num)
theorem B3650021 : Blo 1621009 3650021 := bbase (se 4 (by rfl) ⟨342189, by rfl⟩ : syracuseStep 3650021 = 684379) (by norm_num)
theorem B2052641 : Blo 1621009 2052641 := bbase (se 2 (by rfl) ⟨769740, by rfl⟩ : syracuseStep 2052641 = 1539481) (by norm_num)
theorem B3650093 : Blo 1621009 3650093 := bbase (se 3 (by rfl) ⟨684392, by rfl⟩ : syracuseStep 3650093 = 1368785) (by norm_num)
theorem B5476949 : Blo 1621009 5476949 := bbase (se 8 (by rfl) ⟨32091, by rfl⟩ : syracuseStep 5476949 = 64183) (by norm_num)
theorem B2052697 : Blo 1621009 2052697 := bbase (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) (by norm_num)
theorem B11686517 : Blo 1621009 11686517 := bbase (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) (by norm_num)
theorem B5845621 : Blo 1621009 5845621 := bbase (se 5 (by rfl) ⟨274013, by rfl⟩ : syracuseStep 5845621 = 548027) (by norm_num)
theorem B3650165 : Blo 1621009 3650165 := bbase (se 5 (by rfl) ⟨171101, by rfl⟩ : syracuseStep 3650165 = 342203) (by norm_num)
theorem B2052793 : Blo 1621009 2052793 := bbase (se 2 (by rfl) ⟨769797, by rfl⟩ : syracuseStep 2052793 = 1539595) (by norm_num)
theorem B3650237 : Blo 1621009 3650237 := bbase (se 3 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 3650237 = 1368839) (by norm_num)
theorem B8327909 : Blo 1621009 8327909 := bbase (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) (by norm_num)
theorem B2921197 : Blo 1621009 2921197 := bbase (se 3 (by rfl) ⟨547724, by rfl⟩ : syracuseStep 2921197 = 1095449) (by norm_num)
theorem B8213237 : Blo 1621009 8213237 := bbase (se 5 (by rfl) ⟨384995, by rfl⟩ : syracuseStep 8213237 = 769991) (by norm_num)
theorem B3650309 : Blo 1621009 3650309 := bbase (se 4 (by rfl) ⟨342216, by rfl⟩ : syracuseStep 3650309 = 684433) (by norm_num)
theorem B3650381 : Blo 1621009 3650381 := bbase (se 3 (by rfl) ⟨684446, by rfl⟩ : syracuseStep 3650381 = 1368893) (by norm_num)
theorem B2052965 : Blo 1621009 2052965 := bbase (se 4 (by rfl) ⟨192465, by rfl⟩ : syracuseStep 2052965 = 384931) (by norm_num)
theorem B6927221 : Blo 1621009 6927221 := bbase (se 5 (by rfl) ⟨324713, by rfl⟩ : syracuseStep 6927221 = 649427) (by norm_num)
theorem B3289997 : Blo 1621009 3289997 := bbase (se 3 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 3289997 = 1233749) (by norm_num)
theorem B3650453 : Blo 1621009 3650453 := bbase (se 6 (by rfl) ⟨85557, by rfl⟩ : syracuseStep 3650453 = 171115) (by norm_num)
theorem B2053021 : Blo 1621009 2053021 := bbase (se 3 (by rfl) ⟨384941, by rfl⟩ : syracuseStep 2053021 = 769883) (by norm_num)
theorem B2192293 : Blo 1621009 2192293 := bbase (se 4 (by rfl) ⟨205527, by rfl⟩ : syracuseStep 2192293 = 411055) (by norm_num)
theorem B1823665 : Blo 1621009 1823665 := bbase (se 2 (by rfl) ⟨683874, by rfl⟩ : syracuseStep 1823665 = 1367749) (by norm_num)
theorem B1643473 : Blo 1621009 1643473 := bbase (se 2 (by rfl) ⟨616302, by rfl⟩ : syracuseStep 1643473 = 1232605) (by norm_num)
theorem B1823701 : Blo 1621009 1823701 := bbase (se 7 (by rfl) ⟨21371, by rfl⟩ : syracuseStep 1823701 = 42743) (by norm_num)
theorem B3650525 : Blo 1621009 3650525 := bbase (se 3 (by rfl) ⟨684473, by rfl⟩ : syracuseStep 3650525 = 1368947) (by norm_num)
theorem B2888677 : Blo 1621009 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B1823737 : Blo 1621009 1823737 := bbase (se 2 (by rfl) ⟨683901, by rfl⟩ : syracuseStep 1823737 = 1367803) (by norm_num)
theorem B2053117 : Blo 1621009 2053117 := bbase (se 3 (by rfl) ⟨384959, by rfl⟩ : syracuseStep 2053117 = 769919) (by norm_num)
theorem B5477381 : Blo 1621009 5477381 := bbase (se 4 (by rfl) ⟨513504, by rfl⟩ : syracuseStep 5477381 = 1027009) (by norm_num)
theorem B14242837 : Blo 1621009 14242837 := bbase (se 6 (by rfl) ⟨333816, by rfl⟩ : syracuseStep 14242837 = 667633) (by norm_num)
theorem B1823773 : Blo 1621009 1823773 := bbase (se 3 (by rfl) ⟨341957, by rfl⟩ : syracuseStep 1823773 = 683915) (by norm_num)
theorem B7705637 : Blo 1621009 7705637 := bbase (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) (by norm_num)
theorem B3650597 : Blo 1621009 3650597 := bbase (se 4 (by rfl) ⟨342243, by rfl⟩ : syracuseStep 3650597 = 684487) (by norm_num)
theorem B1823809 : Blo 1621009 1823809 := bbase (se 2 (by rfl) ⟨683928, by rfl⟩ : syracuseStep 1823809 = 1367857) (by norm_num)
theorem B1823845 : Blo 1621009 1823845 := bbase (se 4 (by rfl) ⟨170985, by rfl⟩ : syracuseStep 1823845 = 341971) (by norm_num)
theorem B3650669 : Blo 1621009 3650669 := bbase (se 3 (by rfl) ⟨684500, by rfl⟩ : syracuseStep 3650669 = 1369001) (by norm_num)
theorem B1823881 : Blo 1621009 1823881 := bbase (se 2 (by rfl) ⟨683955, by rfl⟩ : syracuseStep 1823881 = 1367911) (by norm_num)
theorem B3699877 : Blo 1621009 3699877 := bbase (se 4 (by rfl) ⟨346863, by rfl⟩ : syracuseStep 3699877 = 693727) (by norm_num)
theorem B2053289 : Blo 1621009 2053289 := bbase (se 2 (by rfl) ⟨769983, by rfl⟩ : syracuseStep 2053289 = 1539967) (by norm_num)
theorem B1823917 : Blo 1621009 1823917 := bbase (se 3 (by rfl) ⟨341984, by rfl⟩ : syracuseStep 1823917 = 683969) (by norm_num)
theorem B3650741 : Blo 1621009 3650741 := bbase (se 5 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 3650741 = 342257) (by norm_num)
theorem B1823953 : Blo 1621009 1823953 := bbase (se 2 (by rfl) ⟨683982, by rfl⟩ : syracuseStep 1823953 = 1367965) (by norm_num)
theorem B2053345 : Blo 1621009 2053345 := bbase (se 2 (by rfl) ⟨770004, by rfl⟩ : syracuseStep 2053345 = 1540009) (by norm_num)
theorem B1823989 : Blo 1621009 1823989 := bbase (se 5 (by rfl) ⟨85499, by rfl⟩ : syracuseStep 1823989 = 170999) (by norm_num)
theorem B3650813 : Blo 1621009 3650813 := bbase (se 3 (by rfl) ⟨684527, by rfl⟩ : syracuseStep 3650813 = 1369055) (by norm_num)
theorem B3896581 : Blo 1621009 3896581 := bbase (se 4 (by rfl) ⟨365304, by rfl⟩ : syracuseStep 3896581 = 730609) (by norm_num)
theorem B1824025 : Blo 1621009 1824025 := bbase (se 2 (by rfl) ⟨684009, by rfl⟩ : syracuseStep 1824025 = 1368019) (by norm_num)
theorem B2921773 : Blo 1621009 2921773 := bbase (se 3 (by rfl) ⟨547832, by rfl⟩ : syracuseStep 2921773 = 1095665) (by norm_num)
theorem B1824061 : Blo 1621009 1824061 := bbase (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) (by norm_num)
theorem B2053441 : Blo 1621009 2053441 := bbase (se 2 (by rfl) ⟨770040, by rfl⟩ : syracuseStep 2053441 = 1540081) (by norm_num)
theorem B3650885 : Blo 1621009 3650885 := bbase (se 4 (by rfl) ⟨342270, by rfl⟩ : syracuseStep 3650885 = 684541) (by norm_num)
theorem B1824097 : Blo 1621009 1824097 := bbase (se 2 (by rfl) ⟨684036, by rfl⟩ : syracuseStep 1824097 = 1368073) (by norm_num)
theorem B3462517 : Blo 1621009 3462517 := bbase (se 5 (by rfl) ⟨162305, by rfl⟩ : syracuseStep 3462517 = 324611) (by norm_num)
theorem B1824133 : Blo 1621009 1824133 := bbase (se 4 (by rfl) ⟨171012, by rfl⟩ : syracuseStep 1824133 = 342025) (by norm_num)
theorem B3650957 : Blo 1621009 3650957 := bbase (se 3 (by rfl) ⟨684554, by rfl⟩ : syracuseStep 3650957 = 1369109) (by norm_num)
theorem B17528213 : Blo 1621009 17528213 := bbase (se 6 (by rfl) ⟨410817, by rfl⟩ : syracuseStep 17528213 = 821635) (by norm_num)
theorem B1824169 : Blo 1621009 1824169 := bbase (se 2 (by rfl) ⟨684063, by rfl⟩ : syracuseStep 1824169 = 1368127) (by norm_num)
theorem B5551541 : Blo 1621009 5551541 := bbase (se 5 (by rfl) ⟨260228, by rfl⟩ : syracuseStep 5551541 = 520457) (by norm_num)
theorem B1824205 : Blo 1621009 1824205 := bbase (se 3 (by rfl) ⟨342038, by rfl⟩ : syracuseStep 1824205 = 684077) (by norm_num)
theorem B3651029 : Blo 1621009 3651029 := bbase (se 7 (by rfl) ⟨42785, by rfl⟩ : syracuseStep 3651029 = 85571) (by norm_num)
theorem B2053613 : Blo 1621009 2053613 := bbase (se 3 (by rfl) ⟨385052, by rfl⟩ : syracuseStep 2053613 = 770105) (by norm_num)
theorem B1824241 : Blo 1621009 1824241 := bbase (se 2 (by rfl) ⟨684090, by rfl⟩ : syracuseStep 1824241 = 1368181) (by norm_num)
theorem B1824277 : Blo 1621009 1824277 := bbase (se 6 (by rfl) ⟨42756, by rfl⟩ : syracuseStep 1824277 = 85513) (by norm_num)
theorem B4617749 : Blo 1621009 4617749 := bbase (se 6 (by rfl) ⟨108228, by rfl⟩ : syracuseStep 4617749 = 216457) (by norm_num)
theorem B3651101 : Blo 1621009 3651101 := bbase (se 3 (by rfl) ⟨684581, by rfl⟩ : syracuseStep 3651101 = 1369163) (by norm_num)
theorem B2053669 : Blo 1621009 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B1824313 : Blo 1621009 1824313 := bbase (se 2 (by rfl) ⟨684117, by rfl⟩ : syracuseStep 1824313 = 1368235) (by norm_num)
theorem B1824349 : Blo 1621009 1824349 := bbase (se 3 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 1824349 = 684131) (by norm_num)
theorem B3651173 : Blo 1621009 3651173 := bbase (se 4 (by rfl) ⟨342297, by rfl⟩ : syracuseStep 3651173 = 684595) (by norm_num)
theorem B1824385 : Blo 1621009 1824385 := bbase (se 2 (by rfl) ⟨684144, by rfl⟩ : syracuseStep 1824385 = 1368289) (by norm_num)
theorem B2053765 : Blo 1621009 2053765 := bbase (se 4 (by rfl) ⟨192540, by rfl⟩ : syracuseStep 2053765 = 385081) (by norm_num)
theorem B1824421 : Blo 1621009 1824421 := bbase (se 4 (by rfl) ⟨171039, by rfl⟩ : syracuseStep 1824421 = 342079) (by norm_num)
theorem B3651245 : Blo 1621009 3651245 := bbase (se 3 (by rfl) ⟨684608, by rfl⟩ : syracuseStep 3651245 = 1369217) (by norm_num)
theorem B1824457 : Blo 1621009 1824457 := bbase (se 2 (by rfl) ⟨684171, by rfl⟩ : syracuseStep 1824457 = 1368343) (by norm_num)
theorem B1824493 : Blo 1621009 1824493 := bbase (se 3 (by rfl) ⟨342092, by rfl⟩ : syracuseStep 1824493 = 684185) (by norm_num)
theorem B3651317 : Blo 1621009 3651317 := bbase (se 5 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 3651317 = 342311) (by norm_num)
theorem B1824529 : Blo 1621009 1824529 := bbase (se 2 (by rfl) ⟨684198, by rfl⟩ : syracuseStep 1824529 = 1368397) (by norm_num)
theorem B1644305 : Blo 1621009 1644305 := bbase (se 2 (by rfl) ⟨616614, by rfl⟩ : syracuseStep 1644305 = 1233229) (by norm_num)
theorem B1947421 : Blo 1621009 1947421 := bbase (se 3 (by rfl) ⟨365141, by rfl⟩ : syracuseStep 1947421 = 730283) (by norm_num)
theorem B2053937 : Blo 1621009 2053937 := bbase (se 2 (by rfl) ⟨770226, by rfl⟩ : syracuseStep 2053937 = 1540453) (by norm_num)
theorem B1824565 : Blo 1621009 1824565 := bbase (se 5 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 1824565 = 171053) (by norm_num)
theorem B3651389 : Blo 1621009 3651389 := bbase (se 3 (by rfl) ⟨684635, by rfl⟩ : syracuseStep 3651389 = 1369271) (by norm_num)
theorem B1824601 : Blo 1621009 1824601 := bbase (se 2 (by rfl) ⟨684225, by rfl⟩ : syracuseStep 1824601 = 1368451) (by norm_num)
theorem B3463013 : Blo 1621009 3463013 := bbase (se 4 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 3463013 = 649315) (by norm_num)
theorem B4446053 : Blo 1621009 4446053 := bbase (se 4 (by rfl) ⟨416817, by rfl⟩ : syracuseStep 4446053 = 833635) (by norm_num)
theorem B2053993 : Blo 1621009 2053993 := bbase (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) (by norm_num)
theorem B3897197 : Blo 1621009 3897197 := bbase (se 3 (by rfl) ⟨730724, by rfl⟩ : syracuseStep 3897197 = 1461449) (by norm_num)
theorem B3078013 : Blo 1621009 3078013 := bbase (se 3 (by rfl) ⟨577127, by rfl⟩ : syracuseStep 3078013 = 1154255) (by norm_num)
theorem B1824637 : Blo 1621009 1824637 := bbase (se 3 (by rfl) ⟨342119, by rfl⟩ : syracuseStep 1824637 = 684239) (by norm_num)
theorem B6158213 : Blo 1621009 6158213 := bbase (se 4 (by rfl) ⟨577332, by rfl⟩ : syracuseStep 6158213 = 1154665) (by norm_num)
theorem B3651461 : Blo 1621009 3651461 := bbase (se 4 (by rfl) ⟨342324, by rfl⟩ : syracuseStep 3651461 = 684649) (by norm_num)
theorem B1824673 : Blo 1621009 1824673 := bbase (se 2 (by rfl) ⟨684252, by rfl⟩ : syracuseStep 1824673 = 1368505) (by norm_num)
theorem B1824709 : Blo 1621009 1824709 := bbase (se 4 (by rfl) ⟨171066, by rfl⟩ : syracuseStep 1824709 = 342133) (by norm_num)
theorem B2054089 : Blo 1621009 2054089 := bbase (se 2 (by rfl) ⟨770283, by rfl⟩ : syracuseStep 2054089 = 1540567) (by norm_num)
theorem B3651533 : Blo 1621009 3651533 := bbase (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) (by norm_num)
theorem B1824745 : Blo 1621009 1824745 := bbase (se 2 (by rfl) ⟨684279, by rfl⟩ : syracuseStep 1824745 = 1368559) (by norm_num)
theorem B8214533 : Blo 1621009 8214533 := bbase (se 4 (by rfl) ⟨770112, by rfl⟩ : syracuseStep 8214533 = 1540225) (by norm_num)
theorem B3078157 : Blo 1621009 3078157 := bbase (se 3 (by rfl) ⟨577154, by rfl⟩ : syracuseStep 3078157 = 1154309) (by norm_num)
theorem B1824781 : Blo 1621009 1824781 := bbase (se 3 (by rfl) ⟨342146, by rfl⟩ : syracuseStep 1824781 = 684293) (by norm_num)
theorem B2308117 : Blo 1621009 2308117 := bbase (se 6 (by rfl) ⟨54096, by rfl⟩ : syracuseStep 2308117 = 108193) (by norm_num)
theorem B3651605 : Blo 1621009 3651605 := bbase (se 6 (by rfl) ⟨85584, by rfl⟩ : syracuseStep 3651605 = 171169) (by norm_num)
theorem B3897389 : Blo 1621009 3897389 := bbase (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) (by norm_num)
theorem B1824817 : Blo 1621009 1824817 := bbase (se 2 (by rfl) ⟨684306, by rfl⟩ : syracuseStep 1824817 = 1368613) (by norm_num)
theorem B2922581 : Blo 1621009 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B1824853 : Blo 1621009 1824853 := bbase (se 8 (by rfl) ⟨10692, by rfl⟩ : syracuseStep 1824853 = 21385) (by norm_num)
theorem B3651677 : Blo 1621009 3651677 := bbase (se 3 (by rfl) ⟨684689, by rfl⟩ : syracuseStep 3651677 = 1369379) (by norm_num)
theorem B1824889 : Blo 1621009 1824889 := bbase (se 2 (by rfl) ⟨684333, by rfl⟩ : syracuseStep 1824889 = 1368667) (by norm_num)
theorem B3897485 : Blo 1621009 3897485 := bbase (se 3 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 3897485 = 1461557) (by norm_num)
theorem B1824925 : Blo 1621009 1824925 := bbase (se 3 (by rfl) ⟨342173, by rfl⟩ : syracuseStep 1824925 = 684347) (by norm_num)
theorem B6158501 : Blo 1621009 6158501 := bbase (se 4 (by rfl) ⟨577359, by rfl⟩ : syracuseStep 6158501 = 1154719) (by norm_num)
theorem B3651749 : Blo 1621009 3651749 := bbase (se 4 (by rfl) ⟨342351, by rfl⟩ : syracuseStep 3651749 = 684703) (by norm_num)
theorem B3078317 : Blo 1621009 3078317 := bbase (se 3 (by rfl) ⟨577184, by rfl⟩ : syracuseStep 3078317 = 1154369) (by norm_num)
theorem B4618421 : Blo 1621009 4618421 := bbase (se 5 (by rfl) ⟨216488, by rfl⟩ : syracuseStep 4618421 = 432977) (by norm_num)
theorem B1824961 : Blo 1621009 1824961 := bbase (se 2 (by rfl) ⟨684360, by rfl⟩ : syracuseStep 1824961 = 1368721) (by norm_num)
theorem B1824997 : Blo 1621009 1824997 := bbase (se 4 (by rfl) ⟨171093, by rfl⟩ : syracuseStep 1824997 = 342187) (by norm_num)
theorem B2308333 : Blo 1621009 2308333 := bbase (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) (by norm_num)
theorem B1825033 : Blo 1621009 1825033 := bbase (se 2 (by rfl) ⟨684387, by rfl⟩ : syracuseStep 1825033 = 1368775) (by norm_num)
theorem B1825069 : Blo 1621009 1825069 := bbase (se 3 (by rfl) ⟨342200, by rfl⟩ : syracuseStep 1825069 = 684401) (by norm_num)
theorem B13146421 : Blo 1621009 13146421 := bbase (se 5 (by rfl) ⟨616238, by rfl⟩ : syracuseStep 13146421 = 1232477) (by norm_num)
theorem B11688245 : Blo 1621009 11688245 := bbase (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) (by norm_num)
theorem B3701045 : Blo 1621009 3701045 := bbase (se 5 (by rfl) ⟨173486, by rfl⟩ : syracuseStep 3701045 = 346973) (by norm_num)
theorem B3078461 : Blo 1621009 3078461 := bbase (se 3 (by rfl) ⟨577211, by rfl⟩ : syracuseStep 3078461 = 1154423) (by norm_num)
theorem B1825105 : Blo 1621009 1825105 := bbase (se 2 (by rfl) ⟨684414, by rfl⟩ : syracuseStep 1825105 = 1368829) (by norm_num)
theorem B1825141 : Blo 1621009 1825141 := bbase (se 5 (by rfl) ⟨85553, by rfl⟩ : syracuseStep 1825141 = 171107) (by norm_num)
theorem B1825177 : Blo 1621009 1825177 := bbase (se 2 (by rfl) ⟨684441, by rfl⟩ : syracuseStep 1825177 = 1368883) (by norm_num)
theorem B1644953 : Blo 1621009 1644953 := bbase (se 2 (by rfl) ⟨616857, by rfl⟩ : syracuseStep 1644953 = 1233715) (by norm_num)
theorem B8206757 : Blo 1621009 8206757 := bbase (se 4 (by rfl) ⟨769383, by rfl⟩ : syracuseStep 8206757 = 1538767) (by norm_num)
theorem B1825213 : Blo 1621009 1825213 := bbase (se 3 (by rfl) ⟨342227, by rfl⟩ : syracuseStep 1825213 = 684455) (by norm_num)
theorem B1825249 : Blo 1621009 1825249 := bbase (se 2 (by rfl) ⟨684468, by rfl⟩ : syracuseStep 1825249 = 1368937) (by norm_num)
theorem B2923013 : Blo 1621009 2923013 := bbase (se 4 (by rfl) ⟨274032, by rfl⟩ : syracuseStep 2923013 = 548065) (by norm_num)
theorem B1825285 : Blo 1621009 1825285 := bbase (se 4 (by rfl) ⟨171120, by rfl⟩ : syracuseStep 1825285 = 342241) (by norm_num)
theorem B2431517 : Blo 1621009 2431517 := bbase (se 3 (by rfl) ⟨455909, by rfl⟩ : syracuseStep 2431517 = 911819) (by norm_num)
theorem B6502949 : Blo 1621009 6502949 := bbase (se 4 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 6502949 = 1219303) (by norm_num)
theorem B1825321 : Blo 1621009 1825321 := bbase (se 2 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 1825321 = 1368991) (by norm_num)
theorem B2431541 : Blo 1621009 2431541 := bbase (se 5 (by rfl) ⟨113978, by rfl⟩ : syracuseStep 2431541 = 227957) (by norm_num)
theorem B2431565 : Blo 1621009 2431565 := bbase (se 3 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 2431565 = 911837) (by norm_num)
theorem B1825357 : Blo 1621009 1825357 := bbase (se 3 (by rfl) ⟨342254, by rfl⟩ : syracuseStep 1825357 = 684509) (by norm_num)
theorem B33290837 : Blo 1621009 33290837 := bbase (se 8 (by rfl) ⟨195063, by rfl⟩ : syracuseStep 33290837 = 390127) (by norm_num)
theorem B3078749 : Blo 1621009 3078749 := bbase (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) (by norm_num)
theorem B2431589 : Blo 1621009 2431589 := bbase (se 4 (by rfl) ⟨227961, by rfl⟩ : syracuseStep 2431589 = 455923) (by norm_num)
theorem B2308709 : Blo 1621009 2308709 := bbase (se 4 (by rfl) ⟨216441, by rfl⟩ : syracuseStep 2308709 = 432883) (by norm_num)
theorem B4618853 : Blo 1621009 4618853 := bbase (se 4 (by rfl) ⟨433017, by rfl⟩ : syracuseStep 4618853 = 866035) (by norm_num)
theorem B1825393 : Blo 1621009 1825393 := bbase (se 2 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 1825393 = 1369045) (by norm_num)
theorem B2431613 : Blo 1621009 2431613 := bbase (se 3 (by rfl) ⟨455927, by rfl⟩ : syracuseStep 2431613 = 911855) (by norm_num)
theorem B2431637 : Blo 1621009 2431637 := bbase (se 6 (by rfl) ⟨56991, by rfl⟩ : syracuseStep 2431637 = 113983) (by norm_num)
theorem B2923157 : Blo 1621009 2923157 := bbase (se 6 (by rfl) ⟨68511, by rfl⟩ : syracuseStep 2923157 = 137023) (by norm_num)
theorem B1825429 : Blo 1621009 1825429 := bbase (se 6 (by rfl) ⟨42783, by rfl⟩ : syracuseStep 1825429 = 85567) (by norm_num)
theorem B2431661 : Blo 1621009 2431661 := bbase (se 3 (by rfl) ⟨455936, by rfl⟩ : syracuseStep 2431661 = 911873) (by norm_num)
theorem B1825465 : Blo 1621009 1825465 := bbase (se 2 (by rfl) ⟨684549, by rfl⟩ : syracuseStep 1825465 = 1369099) (by norm_num)
theorem B2431685 : Blo 1621009 2431685 := bbase (se 4 (by rfl) ⟨227970, by rfl⟩ : syracuseStep 2431685 = 455941) (by norm_num)
theorem B2431709 : Blo 1621009 2431709 := bbase (se 3 (by rfl) ⟨455945, by rfl⟩ : syracuseStep 2431709 = 911891) (by norm_num)
theorem B3463901 : Blo 1621009 3463901 := bbase (se 3 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 3463901 = 1298963) (by norm_num)
theorem B1825501 : Blo 1621009 1825501 := bbase (se 3 (by rfl) ⟨342281, by rfl⟩ : syracuseStep 1825501 = 684563) (by norm_num)
theorem B2431733 : Blo 1621009 2431733 := bbase (se 5 (by rfl) ⟨113987, by rfl⟩ : syracuseStep 2431733 = 227975) (by norm_num)
theorem B3078901 : Blo 1621009 3078901 := bbase (se 5 (by rfl) ⟨144323, by rfl⟩ : syracuseStep 3078901 = 288647) (by norm_num)
theorem B1825537 : Blo 1621009 1825537 := bbase (se 2 (by rfl) ⟨684576, by rfl⟩ : syracuseStep 1825537 = 1369153) (by norm_num)
theorem B1948421 : Blo 1621009 1948421 := bbase (se 4 (by rfl) ⟨182664, by rfl⟩ : syracuseStep 1948421 = 365329) (by norm_num)
theorem B2431757 : Blo 1621009 2431757 := bbase (se 3 (by rfl) ⟨455954, by rfl⟩ : syracuseStep 2431757 = 911909) (by norm_num)
theorem B19725077 : Blo 1621009 19725077 := bbase (se 6 (by rfl) ⟨462306, by rfl⟩ : syracuseStep 19725077 = 924613) (by norm_num)
theorem B2431781 : Blo 1621009 2431781 := bbase (se 4 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 2431781 = 455959) (by norm_num)
theorem B1825573 : Blo 1621009 1825573 := bbase (se 4 (by rfl) ⟨171147, by rfl⟩ : syracuseStep 1825573 = 342295) (by norm_num)
theorem B2431805 : Blo 1621009 2431805 := bbase (se 3 (by rfl) ⟨455963, by rfl⟩ : syracuseStep 2431805 = 911927) (by norm_num)
theorem B7904069 : Blo 1621009 7904069 := bbase (se 4 (by rfl) ⟨741006, by rfl⟩ : syracuseStep 7904069 = 1482013) (by norm_num)
theorem B1825609 : Blo 1621009 1825609 := bbase (se 2 (by rfl) ⟨684603, by rfl⟩ : syracuseStep 1825609 = 1369207) (by norm_num)
theorem B2431829 : Blo 1621009 2431829 := bbase (se 9 (by rfl) ⟨7124, by rfl⟩ : syracuseStep 2431829 = 14249) (by norm_num)
theorem B3464021 : Blo 1621009 3464021 := bbase (se 9 (by rfl) ⟨10148, by rfl⟩ : syracuseStep 3464021 = 20297) (by norm_num)
theorem B4684645 : Blo 1621009 4684645 := bbase (se 4 (by rfl) ⟨439185, by rfl⟩ : syracuseStep 4684645 = 878371) (by norm_num)
theorem B2431853 : Blo 1621009 2431853 := bbase (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) (by norm_num)
theorem B1825645 : Blo 1621009 1825645 := bbase (se 3 (by rfl) ⟨342308, by rfl⟩ : syracuseStep 1825645 = 684617) (by norm_num)
theorem B2923381 : Blo 1621009 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B2431877 : Blo 1621009 2431877 := bbase (se 4 (by rfl) ⟨227988, by rfl⟩ : syracuseStep 2431877 = 455977) (by norm_num)
theorem B1825681 : Blo 1621009 1825681 := bbase (se 2 (by rfl) ⟨684630, by rfl⟩ : syracuseStep 1825681 = 1369261) (by norm_num)
theorem B2431901 : Blo 1621009 2431901 := bbase (se 3 (by rfl) ⟨455981, by rfl⟩ : syracuseStep 2431901 = 911963) (by norm_num)
theorem B2431925 : Blo 1621009 2431925 := bbase (se 5 (by rfl) ⟨113996, by rfl⟩ : syracuseStep 2431925 = 227993) (by norm_num)
theorem B1825717 : Blo 1621009 1825717 := bbase (se 5 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 1825717 = 171161) (by norm_num)
theorem B2431949 : Blo 1621009 2431949 := bbase (se 3 (by rfl) ⟨455990, by rfl⟩ : syracuseStep 2431949 = 911981) (by norm_num)
theorem B1825753 : Blo 1621009 1825753 := bbase (se 2 (by rfl) ⟨684657, by rfl⟩ : syracuseStep 1825753 = 1369315) (by norm_num)
theorem B2431973 : Blo 1621009 2431973 := bbase (se 4 (by rfl) ⟨227997, by rfl⟩ : syracuseStep 2431973 = 455995) (by norm_num)
theorem B2431997 : Blo 1621009 2431997 := bbase (se 3 (by rfl) ⟨455999, by rfl⟩ : syracuseStep 2431997 = 911999) (by norm_num)
theorem B1825789 : Blo 1621009 1825789 := bbase (se 3 (by rfl) ⟨342335, by rfl⟩ : syracuseStep 1825789 = 684671) (by norm_num)
theorem B2432021 : Blo 1621009 2432021 := bbase (se 6 (by rfl) ⟨57000, by rfl⟩ : syracuseStep 2432021 = 114001) (by norm_num)
theorem B18480149 : Blo 1621009 18480149 := bbase (se 6 (by rfl) ⟨433128, by rfl⟩ : syracuseStep 18480149 = 866257) (by norm_num)
theorem B1825825 : Blo 1621009 1825825 := bbase (se 2 (by rfl) ⟨684684, by rfl⟩ : syracuseStep 1825825 = 1369369) (by norm_num)
theorem B3079205 : Blo 1621009 3079205 := bbase (se 4 (by rfl) ⟨288675, by rfl⟩ : syracuseStep 3079205 = 577351) (by norm_num)
theorem B2432045 : Blo 1621009 2432045 := bbase (se 3 (by rfl) ⟨456008, by rfl⟩ : syracuseStep 2432045 = 912017) (by norm_num)
theorem B4103237 : Blo 1621009 4103237 := bbase (se 4 (by rfl) ⟨384678, by rfl⟩ : syracuseStep 4103237 = 769357) (by norm_num)
theorem B2432069 : Blo 1621009 2432069 := bbase (se 4 (by rfl) ⟨228006, by rfl⟩ : syracuseStep 2432069 = 456013) (by norm_num)
theorem B3513413 : Blo 1621009 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B1825861 : Blo 1621009 1825861 := bbase (se 4 (by rfl) ⟨171174, by rfl⟩ : syracuseStep 1825861 = 342349) (by norm_num)
theorem B4217933 : Blo 1621009 4217933 := bbase (se 3 (by rfl) ⟨790862, by rfl⟩ : syracuseStep 4217933 = 1581725) (by norm_num)
theorem B23379029 : Blo 1621009 23379029 := bbase (se 8 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 23379029 = 273973) (by norm_num)
theorem B2432093 : Blo 1621009 2432093 := bbase (se 3 (by rfl) ⟨456017, by rfl⟩ : syracuseStep 2432093 = 912035) (by norm_num)
theorem B5471333 : Blo 1621009 5471333 := bbase (se 4 (by rfl) ⟨512937, by rfl⟩ : syracuseStep 5471333 = 1025875) (by norm_num)
theorem B2432117 : Blo 1621009 2432117 := bbase (se 5 (by rfl) ⟨114005, by rfl⟩ : syracuseStep 2432117 = 228011) (by norm_num)
theorem B2464901 : Blo 1621009 2464901 := bbase (se 4 (by rfl) ⟨231084, by rfl⟩ : syracuseStep 2464901 = 462169) (by norm_num)
theorem B2432141 : Blo 1621009 2432141 := bbase (se 3 (by rfl) ⟨456026, by rfl⟩ : syracuseStep 2432141 = 912053) (by norm_num)
theorem B2432165 : Blo 1621009 2432165 := bbase (se 4 (by rfl) ⟨228015, by rfl⟩ : syracuseStep 2432165 = 456031) (by norm_num)
theorem B2432189 : Blo 1621009 2432189 := bbase (se 3 (by rfl) ⟨456035, by rfl⟩ : syracuseStep 2432189 = 912071) (by norm_num)
theorem B2432213 : Blo 1621009 2432213 := bbase (se 7 (by rfl) ⟨28502, by rfl⟩ : syracuseStep 2432213 = 57005) (by norm_num)
theorem B2923733 : Blo 1621009 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B2432237 : Blo 1621009 2432237 := bbase (se 3 (by rfl) ⟨456044, by rfl⟩ : syracuseStep 2432237 = 912089) (by norm_num)
theorem B2432261 : Blo 1621009 2432261 := bbase (se 4 (by rfl) ⟨228024, by rfl⟩ : syracuseStep 2432261 = 456049) (by norm_num)
theorem B8215829 : Blo 1621009 8215829 := bbase (se 6 (by rfl) ⟨192558, by rfl⟩ : syracuseStep 8215829 = 385117) (by norm_num)
theorem B2432285 : Blo 1621009 2432285 := bbase (se 3 (by rfl) ⟨456053, by rfl⟩ : syracuseStep 2432285 = 912107) (by norm_num)
theorem B2432309 : Blo 1621009 2432309 := bbase (se 5 (by rfl) ⟨114014, by rfl⟩ : syracuseStep 2432309 = 228029) (by norm_num)
theorem B6159685 : Blo 1621009 6159685 := bbase (se 4 (by rfl) ⟨577470, by rfl⟩ : syracuseStep 6159685 = 1154941) (by norm_num)
theorem B2432333 : Blo 1621009 2432333 := bbase (se 3 (by rfl) ⟨456062, by rfl⟩ : syracuseStep 2432333 = 912125) (by norm_num)
theorem B4619605 : Blo 1621009 4619605 := bbase (se 11 (by rfl) ⟨3383, by rfl⟩ : syracuseStep 4619605 = 6767) (by norm_num)
theorem B2080093 : Blo 1621009 2080093 := bbase (se 3 (by rfl) ⟨390017, by rfl⟩ : syracuseStep 2080093 = 780035) (by norm_num)
theorem B2432357 : Blo 1621009 2432357 := bbase (se 4 (by rfl) ⟨228033, by rfl⟩ : syracuseStep 2432357 = 456067) (by norm_num)
theorem B2465149 : Blo 1621009 2465149 := bbase (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) (by norm_num)
theorem B2432381 : Blo 1621009 2432381 := bbase (se 3 (by rfl) ⟨456071, by rfl⟩ : syracuseStep 2432381 = 912143) (by norm_num)
theorem B2432405 : Blo 1621009 2432405 := bbase (se 6 (by rfl) ⟨57009, by rfl⟩ : syracuseStep 2432405 = 114019) (by norm_num)
theorem B4103581 : Blo 1621009 4103581 := bbase (se 3 (by rfl) ⟨769421, by rfl⟩ : syracuseStep 4103581 = 1538843) (by norm_num)
theorem B2735525 : Blo 1621009 2735525 := bbase (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) (by norm_num)
theorem B2432429 : Blo 1621009 2432429 := bbase (se 3 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 2432429 = 912161) (by norm_num)
theorem B11689397 : Blo 1621009 11689397 := bbase (se 5 (by rfl) ⟨547940, by rfl⟩ : syracuseStep 11689397 = 1095881) (by norm_num)
theorem B1949113 : Blo 1621009 1949113 := bbase (se 2 (by rfl) ⟨730917, by rfl⟩ : syracuseStep 1949113 = 1461835) (by norm_num)
theorem B2432453 : Blo 1621009 2432453 := bbase (se 4 (by rfl) ⟨228042, by rfl⟩ : syracuseStep 2432453 = 456085) (by norm_num)
theorem B1949117 : Blo 1621009 1949117 := bbase (se 3 (by rfl) ⟨365459, by rfl⟩ : syracuseStep 1949117 = 730919) (by norm_num)
theorem B3464653 : Blo 1621009 3464653 := bbase (se 3 (by rfl) ⟨649622, by rfl⟩ : syracuseStep 3464653 = 1299245) (by norm_num)
theorem B2432477 : Blo 1621009 2432477 := bbase (se 3 (by rfl) ⟨456089, by rfl⟩ : syracuseStep 2432477 = 912179) (by norm_num)
theorem B2432501 : Blo 1621009 2432501 := bbase (se 5 (by rfl) ⟨114023, by rfl⟩ : syracuseStep 2432501 = 228047) (by norm_num)
theorem B3751429 : Blo 1621009 3751429 := bbase (se 4 (by rfl) ⟨351696, by rfl⟩ : syracuseStep 3751429 = 703393) (by norm_num)
theorem B4103693 : Blo 1621009 4103693 := bbase (se 3 (by rfl) ⟨769442, by rfl⟩ : syracuseStep 4103693 = 1538885) (by norm_num)
theorem B2432525 : Blo 1621009 2432525 := bbase (se 3 (by rfl) ⟨456098, by rfl⟩ : syracuseStep 2432525 = 912197) (by norm_num)
theorem B5471765 : Blo 1621009 5471765 := bbase (se 6 (by rfl) ⟨128244, by rfl⟩ : syracuseStep 5471765 = 256489) (by norm_num)
theorem B2735653 : Blo 1621009 2735653 := bbase (se 4 (by rfl) ⟨256467, by rfl⟩ : syracuseStep 2735653 = 512935) (by norm_num)
theorem B2432549 : Blo 1621009 2432549 := bbase (se 4 (by rfl) ⟨228051, by rfl⟩ : syracuseStep 2432549 = 456103) (by norm_num)
theorem B2432573 : Blo 1621009 2432573 := bbase (se 3 (by rfl) ⟨456107, by rfl⟩ : syracuseStep 2432573 = 912215) (by norm_num)
theorem B2432597 : Blo 1621009 2432597 := bbase (se 8 (by rfl) ⟨14253, by rfl⟩ : syracuseStep 2432597 = 28507) (by norm_num)
theorem B2432621 : Blo 1621009 2432621 := bbase (se 3 (by rfl) ⟨456116, by rfl⟩ : syracuseStep 2432621 = 912233) (by norm_num)
theorem B6159989 : Blo 1621009 6159989 := bbase (se 5 (by rfl) ⟨288749, by rfl⟩ : syracuseStep 6159989 = 577499) (by norm_num)
theorem B2735741 : Blo 1621009 2735741 := bbase (se 3 (by rfl) ⟨512951, by rfl⟩ : syracuseStep 2735741 = 1025903) (by norm_num)
theorem B2432645 : Blo 1621009 2432645 := bbase (se 4 (by rfl) ⟨228060, by rfl⟩ : syracuseStep 2432645 = 456121) (by norm_num)
theorem B2432669 : Blo 1621009 2432669 := bbase (se 3 (by rfl) ⟨456125, by rfl⟩ : syracuseStep 2432669 = 912251) (by norm_num)
theorem B8208053 : Blo 1621009 8208053 := bbase (se 5 (by rfl) ⟨384752, by rfl⟩ : syracuseStep 8208053 = 769505) (by norm_num)
theorem B2432693 : Blo 1621009 2432693 := bbase (se 5 (by rfl) ⟨114032, by rfl⟩ : syracuseStep 2432693 = 228065) (by norm_num)
theorem B4103885 : Blo 1621009 4103885 := bbase (se 3 (by rfl) ⟨769478, by rfl⟩ : syracuseStep 4103885 = 1538957) (by norm_num)
theorem B2432717 : Blo 1621009 2432717 := bbase (se 3 (by rfl) ⟨456134, by rfl⟩ : syracuseStep 2432717 = 912269) (by norm_num)
theorem B2432741 : Blo 1621009 2432741 := bbase (se 4 (by rfl) ⟨228069, by rfl⟩ : syracuseStep 2432741 = 456139) (by norm_num)
theorem B2735869 : Blo 1621009 2735869 := bbase (se 3 (by rfl) ⟨512975, by rfl⟩ : syracuseStep 2735869 = 1025951) (by norm_num)
theorem B2432765 : Blo 1621009 2432765 := bbase (se 3 (by rfl) ⟨456143, by rfl⟩ : syracuseStep 2432765 = 912287) (by norm_num)
theorem B7790357 : Blo 1621009 7790357 := bbase (se 6 (by rfl) ⟨182586, by rfl⟩ : syracuseStep 7790357 = 365173) (by norm_num)
theorem B2432789 : Blo 1621009 2432789 := bbase (se 6 (by rfl) ⟨57018, by rfl⟩ : syracuseStep 2432789 = 114037) (by norm_num)
theorem B3079957 : Blo 1621009 3079957 := bbase (se 6 (by rfl) ⟨72186, by rfl⟩ : syracuseStep 3079957 = 144373) (by norm_num)
theorem B2432813 : Blo 1621009 2432813 := bbase (se 3 (by rfl) ⟨456152, by rfl⟩ : syracuseStep 2432813 = 912305) (by norm_num)
theorem B2432837 : Blo 1621009 2432837 := bbase (se 4 (by rfl) ⟨228078, by rfl⟩ : syracuseStep 2432837 = 456157) (by norm_num)
theorem B2735957 : Blo 1621009 2735957 := bbase (se 9 (by rfl) ⟨8015, by rfl⟩ : syracuseStep 2735957 = 16031) (by norm_num)
theorem B2432861 : Blo 1621009 2432861 := bbase (se 3 (by rfl) ⟨456161, by rfl⟩ : syracuseStep 2432861 = 912323) (by norm_num)
theorem B2432885 : Blo 1621009 2432885 := bbase (se 5 (by rfl) ⟨114041, by rfl⟩ : syracuseStep 2432885 = 228083) (by norm_num)
theorem B2432909 : Blo 1621009 2432909 := bbase (se 3 (by rfl) ⟨456170, by rfl⟩ : syracuseStep 2432909 = 912341) (by norm_num)
theorem B29998997 : Blo 1621009 29998997 := bbase (se 6 (by rfl) ⟨703101, by rfl⟩ : syracuseStep 29998997 = 1406203) (by norm_num)
theorem B2432933 : Blo 1621009 2432933 := bbase (se 4 (by rfl) ⟨228087, by rfl⟩ : syracuseStep 2432933 = 456175) (by norm_num)
theorem B3080101 : Blo 1621009 3080101 := bbase (se 4 (by rfl) ⟨288759, by rfl⟩ : syracuseStep 3080101 = 577519) (by norm_num)
theorem B1949617 : Blo 1621009 1949617 := bbase (se 2 (by rfl) ⟨731106, by rfl⟩ : syracuseStep 1949617 = 1462213) (by norm_num)
theorem B2432957 : Blo 1621009 2432957 := bbase (se 3 (by rfl) ⟨456179, by rfl⟩ : syracuseStep 2432957 = 912359) (by norm_num)
theorem B5472197 : Blo 1621009 5472197 := bbase (se 4 (by rfl) ⟨513018, by rfl⟩ : syracuseStep 5472197 = 1026037) (by norm_num)
theorem B2736085 : Blo 1621009 2736085 := bbase (se 7 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 2736085 = 64127) (by norm_num)
theorem B2432981 : Blo 1621009 2432981 := bbase (se 7 (by rfl) ⟨28511, by rfl⟩ : syracuseStep 2432981 = 57023) (by norm_num)
theorem B2433005 : Blo 1621009 2433005 := bbase (se 3 (by rfl) ⟨456188, by rfl⟩ : syracuseStep 2433005 = 912377) (by norm_num)
theorem B2310133 : Blo 1621009 2310133 := bbase (se 5 (by rfl) ⟨108287, by rfl⟩ : syracuseStep 2310133 = 216575) (by norm_num)
theorem B1622019 : Blo 1621009 1622019 := bstep (se 1 (by rfl) ⟨1216514, by rfl⟩ : syracuseStep 1622019 = 2433029) B2433029
theorem B4104209 : Blo 1621009 4104209 := bstep (se 2 (by rfl) ⟨1539078, by rfl⟩ : syracuseStep 4104209 = 3078157) B3078157
theorem B2433041 : Blo 1621009 2433041 := bstep (se 2 (by rfl) ⟨912390, by rfl⟩ : syracuseStep 2433041 = 1824781) B1824781
theorem B1622035 : Blo 1621009 1622035 := bstep (se 1 (by rfl) ⟨1216526, by rfl⟩ : syracuseStep 1622035 = 2433053) B2433053
theorem B2433059 : Blo 1621009 2433059 := bstep (se 1 (by rfl) ⟨1824794, by rfl⟩ : syracuseStep 2433059 = 3649589) B3649589
theorem B1622051 : Blo 1621009 1622051 := bstep (se 1 (by rfl) ⟨1216538, by rfl⟩ : syracuseStep 1622051 = 2433077) B2433077
theorem B6930467 : Blo 1621009 6930467 := bstep (se 1 (by rfl) ⟨5197850, by rfl⟩ : syracuseStep 6930467 = 10395701) B10395701
theorem B3465251 : Blo 1621009 3465251 := bstep (se 1 (by rfl) ⟨2598938, by rfl⟩ : syracuseStep 3465251 = 5197877) B5197877
theorem B5472305 : Blo 1621009 5472305 := bstep (se 2 (by rfl) ⟨2052114, by rfl⟩ : syracuseStep 5472305 = 4104229) B4104229
theorem B1622067 : Blo 1621009 1622067 := bstep (se 1 (by rfl) ⟨1216550, by rfl⟩ : syracuseStep 1622067 = 2433101) B2433101
theorem B2736193 : Blo 1621009 2736193 := bstep (se 2 (by rfl) ⟨1026072, by rfl⟩ : syracuseStep 2736193 = 2052145) B2052145
theorem B2433089 : Blo 1621009 2433089 := bstep (se 2 (by rfl) ⟨912408, by rfl⟩ : syracuseStep 2433089 = 1824817) B1824817
theorem B1622083 : Blo 1621009 1622083 := bstep (se 1 (by rfl) ⟨1216562, by rfl⟩ : syracuseStep 1622083 = 2433125) B2433125
theorem B2433107 : Blo 1621009 2433107 := bstep (se 1 (by rfl) ⟨1824830, by rfl⟩ : syracuseStep 2433107 = 3649661) B3649661
theorem B1622099 : Blo 1621009 1622099 := bstep (se 1 (by rfl) ⟨1216574, by rfl⟩ : syracuseStep 1622099 = 2433149) B2433149
theorem B2736227 : Blo 1621009 2736227 := bstep (se 1 (by rfl) ⟨2052170, by rfl⟩ : syracuseStep 2736227 = 4104341) B4104341
theorem B1622115 : Blo 1621009 1622115 := bstep (se 1 (by rfl) ⟨1216586, by rfl⟩ : syracuseStep 1622115 = 2433173) B2433173
theorem B5193841 : Blo 1621009 5193841 := bstep (se 2 (by rfl) ⟨1947690, by rfl⟩ : syracuseStep 5193841 = 3895381) B3895381
theorem B2433137 : Blo 1621009 2433137 := bstep (se 2 (by rfl) ⟨912426, by rfl⟩ : syracuseStep 2433137 = 1824853) B1824853
theorem B1622131 : Blo 1621009 1622131 := bstep (se 1 (by rfl) ⟨1216598, by rfl⟩ : syracuseStep 1622131 = 2433197) B2433197
theorem B2433155 : Blo 1621009 2433155 := bstep (se 1 (by rfl) ⟨1824866, by rfl⟩ : syracuseStep 2433155 = 3649733) B3649733
theorem B1622147 : Blo 1621009 1622147 := bstep (se 1 (by rfl) ⟨1216610, by rfl⟩ : syracuseStep 1622147 = 2433221) B2433221
theorem B1622163 : Blo 1621009 1622163 := bstep (se 1 (by rfl) ⟨1216622, by rfl⟩ : syracuseStep 1622163 = 2433245) B2433245
theorem B2433185 : Blo 1621009 2433185 := bstep (se 2 (by rfl) ⟨912444, by rfl⟩ : syracuseStep 2433185 = 1824889) B1824889
theorem B1622179 : Blo 1621009 1622179 := bstep (se 1 (by rfl) ⟨1216634, by rfl⟩ : syracuseStep 1622179 = 2433269) B2433269
theorem B2433203 : Blo 1621009 2433203 := bstep (se 1 (by rfl) ⟨1824902, by rfl⟩ : syracuseStep 2433203 = 3649805) B3649805
theorem B1622195 : Blo 1621009 1622195 := bstep (se 1 (by rfl) ⟨1216646, by rfl⟩ : syracuseStep 1622195 = 2433293) B2433293
theorem B1622211 : Blo 1621009 1622211 := bstep (se 1 (by rfl) ⟨1216658, by rfl⟩ : syracuseStep 1622211 = 2433317) B2433317
theorem B11247821 : Blo 1621009 11247821 := bstep (se 3 (by rfl) ⟨2108966, by rfl⟩ : syracuseStep 11247821 = 4217933) B4217933
theorem B2433233 : Blo 1621009 2433233 := bstep (se 2 (by rfl) ⟨912462, by rfl⟩ : syracuseStep 2433233 = 1824925) B1824925
theorem B4620493 : Blo 1621009 4620493 := bstep (se 3 (by rfl) ⟨866342, by rfl⟩ : syracuseStep 4620493 = 1732685) B1732685
theorem B1622227 : Blo 1621009 1622227 := bstep (se 1 (by rfl) ⟨1216670, by rfl⟩ : syracuseStep 1622227 = 2433341) B2433341
theorem B2736355 : Blo 1621009 2736355 := bstep (se 1 (by rfl) ⟨2052266, by rfl⟩ : syracuseStep 2736355 = 4104533) B4104533
theorem B2433251 : Blo 1621009 2433251 := bstep (se 1 (by rfl) ⟨1824938, by rfl⟩ : syracuseStep 2433251 = 3649877) B3649877
theorem B1622243 : Blo 1621009 1622243 := bstep (se 1 (by rfl) ⟨1216682, by rfl⟩ : syracuseStep 1622243 = 2433365) B2433365
theorem B1622259 : Blo 1621009 1622259 := bstep (se 1 (by rfl) ⟨1216694, by rfl⟩ : syracuseStep 1622259 = 2433389) B2433389
theorem B2433281 : Blo 1621009 2433281 := bstep (se 2 (by rfl) ⟨912480, by rfl⟩ : syracuseStep 2433281 = 1824961) B1824961
theorem B1622275 : Blo 1621009 1622275 := bstep (se 1 (by rfl) ⟨1216706, by rfl⟩ : syracuseStep 1622275 = 2433413) B2433413
theorem B2433299 : Blo 1621009 2433299 := bstep (se 1 (by rfl) ⟨1824974, by rfl⟩ : syracuseStep 2433299 = 3649949) B3649949
theorem B1622291 : Blo 1621009 1622291 := bstep (se 1 (by rfl) ⟨1216718, by rfl⟩ : syracuseStep 1622291 = 2433437) B2433437
theorem B1622307 : Blo 1621009 1622307 := bstep (se 1 (by rfl) ⟨1216730, by rfl⟩ : syracuseStep 1622307 = 2433461) B2433461
theorem B6242609 : Blo 1621009 6242609 := bstep (se 2 (by rfl) ⟨2340978, by rfl⟩ : syracuseStep 6242609 = 4681957) B4681957
theorem B2433329 : Blo 1621009 2433329 := bstep (se 2 (by rfl) ⟨912498, by rfl⟩ : syracuseStep 2433329 = 1824997) B1824997
theorem B1622323 : Blo 1621009 1622323 := bstep (se 1 (by rfl) ⟨1216742, by rfl⟩ : syracuseStep 1622323 = 2433485) B2433485
theorem B2433347 : Blo 1621009 2433347 := bstep (se 1 (by rfl) ⟨1825010, by rfl⟩ : syracuseStep 2433347 = 3650021) B3650021
theorem B1622339 : Blo 1621009 1622339 := bstep (se 1 (by rfl) ⟨1216754, by rfl⟩ : syracuseStep 1622339 = 2433509) B2433509
theorem B1622355 : Blo 1621009 1622355 := bstep (se 1 (by rfl) ⟨1216766, by rfl⟩ : syracuseStep 1622355 = 2433533) B2433533
theorem B2433377 : Blo 1621009 2433377 := bstep (se 2 (by rfl) ⟨912516, by rfl⟩ : syracuseStep 2433377 = 1825033) B1825033
theorem B1622371 : Blo 1621009 1622371 := bstep (se 1 (by rfl) ⟨1216778, by rfl⟩ : syracuseStep 1622371 = 2433557) B2433557
theorem B2736497 : Blo 1621009 2736497 := bstep (se 2 (by rfl) ⟨1026186, by rfl⟩ : syracuseStep 2736497 = 2052373) B2052373
theorem B2433395 : Blo 1621009 2433395 := bstep (se 1 (by rfl) ⟨1825046, by rfl⟩ : syracuseStep 2433395 = 3650093) B3650093
theorem B1622387 : Blo 1621009 1622387 := bstep (se 1 (by rfl) ⟨1216790, by rfl⟩ : syracuseStep 1622387 = 2433581) B2433581
theorem B1622403 : Blo 1621009 1622403 := bstep (se 1 (by rfl) ⟨1216802, by rfl⟩ : syracuseStep 1622403 = 2433605) B2433605
theorem B9240965 : Blo 1621009 9240965 := bstep (se 4 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 9240965 = 1732681) B1732681
theorem B2433425 : Blo 1621009 2433425 := bstep (se 2 (by rfl) ⟨912534, by rfl⟩ : syracuseStep 2433425 = 1825069) B1825069
theorem B1622419 : Blo 1621009 1622419 := bstep (se 1 (by rfl) ⟨1216814, by rfl⟩ : syracuseStep 1622419 = 2433629) B2433629
theorem B7791011 : Blo 1621009 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B2433443 : Blo 1621009 2433443 := bstep (se 1 (by rfl) ⟨1825082, by rfl⟩ : syracuseStep 2433443 = 3650165) B3650165
theorem B1622435 : Blo 1621009 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B4620721 : Blo 1621009 4620721 := bstep (se 2 (by rfl) ⟨1732770, by rfl⟩ : syracuseStep 4620721 = 3465541) B3465541
theorem B1622451 : Blo 1621009 1622451 := bstep (se 1 (by rfl) ⟨1216838, by rfl⟩ : syracuseStep 1622451 = 2433677) B2433677
theorem B2433473 : Blo 1621009 2433473 := bstep (se 2 (by rfl) ⟨912552, by rfl⟩ : syracuseStep 2433473 = 1825105) B1825105
theorem B1622467 : Blo 1621009 1622467 := bstep (se 1 (by rfl) ⟨1216850, by rfl⟩ : syracuseStep 1622467 = 2433701) B2433701
theorem B2433491 : Blo 1621009 2433491 := bstep (se 1 (by rfl) ⟨1825118, by rfl⟩ : syracuseStep 2433491 = 3650237) B3650237
theorem B1622483 : Blo 1621009 1622483 := bstep (se 1 (by rfl) ⟨1216862, by rfl⟩ : syracuseStep 1622483 = 2433725) B2433725
theorem B2310611 : Blo 1621009 2310611 := bstep (se 1 (by rfl) ⟨1732958, by rfl⟩ : syracuseStep 2310611 = 3465917) B3465917
theorem B1622499 : Blo 1621009 1622499 := bstep (se 1 (by rfl) ⟨1216874, by rfl⟩ : syracuseStep 1622499 = 2433749) B2433749
theorem B2736625 : Blo 1621009 2736625 := bstep (se 2 (by rfl) ⟨1026234, by rfl⟩ : syracuseStep 2736625 = 2052469) B2052469
theorem B2433521 : Blo 1621009 2433521 := bstep (se 2 (by rfl) ⟨912570, by rfl⟩ : syracuseStep 2433521 = 1825141) B1825141
theorem B1622515 : Blo 1621009 1622515 := bstep (se 1 (by rfl) ⟨1216886, by rfl⟩ : syracuseStep 1622515 = 2433773) B2433773
theorem B2433539 : Blo 1621009 2433539 := bstep (se 1 (by rfl) ⟨1825154, by rfl⟩ : syracuseStep 2433539 = 3650309) B3650309
theorem B1622531 : Blo 1621009 1622531 := bstep (se 1 (by rfl) ⟨1216898, by rfl⟩ : syracuseStep 1622531 = 2433797) B2433797
theorem B2736659 : Blo 1621009 2736659 := bstep (se 1 (by rfl) ⟨2052494, by rfl⟩ : syracuseStep 2736659 = 4104989) B4104989
theorem B1622547 : Blo 1621009 1622547 := bstep (se 1 (by rfl) ⟨1216910, by rfl⟩ : syracuseStep 1622547 = 2433821) B2433821
theorem B2433569 : Blo 1621009 2433569 := bstep (se 2 (by rfl) ⟨912588, by rfl⟩ : syracuseStep 2433569 = 1825177) B1825177
theorem B1622563 : Blo 1621009 1622563 := bstep (se 1 (by rfl) ⟨1216922, by rfl⟩ : syracuseStep 1622563 = 2433845) B2433845
theorem B6160931 : Blo 1621009 6160931 := bstep (se 1 (by rfl) ⟨4620698, by rfl⟩ : syracuseStep 6160931 = 9241397) B9241397
theorem B2433587 : Blo 1621009 2433587 := bstep (se 1 (by rfl) ⟨1825190, by rfl⟩ : syracuseStep 2433587 = 3650381) B3650381
theorem B1622579 : Blo 1621009 1622579 := bstep (se 1 (by rfl) ⟨1216934, by rfl⟩ : syracuseStep 1622579 = 2433869) B2433869
theorem B1622595 : Blo 1621009 1622595 := bstep (se 1 (by rfl) ⟨1216946, by rfl⟩ : syracuseStep 1622595 = 2433893) B2433893
theorem B5472845 : Blo 1621009 5472845 := bstep (se 3 (by rfl) ⟨1026158, by rfl⟩ : syracuseStep 5472845 = 2052317) B2052317
theorem B2433617 : Blo 1621009 2433617 := bstep (se 2 (by rfl) ⟨912606, by rfl⟩ : syracuseStep 2433617 = 1825213) B1825213
theorem B4620881 : Blo 1621009 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B1622611 : Blo 1621009 1622611 := bstep (se 1 (by rfl) ⟨1216958, by rfl⟩ : syracuseStep 1622611 = 2433917) B2433917
theorem B2433635 : Blo 1621009 2433635 := bstep (se 1 (by rfl) ⟨1825226, by rfl⟩ : syracuseStep 2433635 = 3650453) B3650453
theorem B1622627 : Blo 1621009 1622627 := bstep (se 1 (by rfl) ⟨1216970, by rfl⟩ : syracuseStep 1622627 = 2433941) B2433941
theorem B3465841 : Blo 1621009 3465841 := bstep (se 2 (by rfl) ⟨1299690, by rfl⟩ : syracuseStep 3465841 = 2599381) B2599381
theorem B1622643 : Blo 1621009 1622643 := bstep (se 1 (by rfl) ⟨1216982, by rfl⟩ : syracuseStep 1622643 = 2433965) B2433965
theorem B5472899 : Blo 1621009 5472899 := bstep (se 1 (by rfl) ⟨4104674, by rfl⟩ : syracuseStep 5472899 = 8209349) B8209349
theorem B2433665 : Blo 1621009 2433665 := bstep (se 2 (by rfl) ⟨912624, by rfl⟩ : syracuseStep 2433665 = 1825249) B1825249
theorem B1622659 : Blo 1621009 1622659 := bstep (se 1 (by rfl) ⟨1216994, by rfl⟩ : syracuseStep 1622659 = 2433989) B2433989
theorem B6668941 : Blo 1621009 6668941 := bstep (se 3 (by rfl) ⟨1250426, by rfl⟩ : syracuseStep 6668941 = 2500853) B2500853
theorem B2736787 : Blo 1621009 2736787 := bstep (se 1 (by rfl) ⟨2052590, by rfl⟩ : syracuseStep 2736787 = 4105181) B4105181
theorem B2433683 : Blo 1621009 2433683 := bstep (se 1 (by rfl) ⟨1825262, by rfl⟩ : syracuseStep 2433683 = 3650525) B3650525
theorem B1622675 : Blo 1621009 1622675 := bstep (se 1 (by rfl) ⟨1217006, by rfl⟩ : syracuseStep 1622675 = 2434013) B2434013
theorem B1622691 : Blo 1621009 1622691 := bstep (se 1 (by rfl) ⟨1217018, by rfl⟩ : syracuseStep 1622691 = 2434037) B2434037
theorem B2433713 : Blo 1621009 2433713 := bstep (se 2 (by rfl) ⟨912642, by rfl⟩ : syracuseStep 2433713 = 1825285) B1825285
theorem B1622707 : Blo 1621009 1622707 := bstep (se 1 (by rfl) ⟨1217030, by rfl⟩ : syracuseStep 1622707 = 2434061) B2434061
theorem B5137091 : Blo 1621009 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B2433731 : Blo 1621009 2433731 := bstep (se 1 (by rfl) ⟨1825298, by rfl⟩ : syracuseStep 2433731 = 3650597) B3650597
theorem B1622723 : Blo 1621009 1622723 := bstep (se 1 (by rfl) ⟨1217042, by rfl⟩ : syracuseStep 1622723 = 2434085) B2434085
theorem B4620995 : Blo 1621009 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B1622739 : Blo 1621009 1622739 := bstep (se 1 (by rfl) ⟨1217054, by rfl⟩ : syracuseStep 1622739 = 2434109) B2434109
theorem B2433761 : Blo 1621009 2433761 := bstep (se 2 (by rfl) ⟨912660, by rfl⟩ : syracuseStep 2433761 = 1825321) B1825321
theorem B1622755 : Blo 1621009 1622755 := bstep (se 1 (by rfl) ⟨1217066, by rfl⟩ : syracuseStep 1622755 = 2434133) B2434133
theorem B2433779 : Blo 1621009 2433779 := bstep (se 1 (by rfl) ⟨1825334, by rfl⟩ : syracuseStep 2433779 = 3650669) B3650669
theorem B1622771 : Blo 1621009 1622771 := bstep (se 1 (by rfl) ⟨1217078, by rfl⟩ : syracuseStep 1622771 = 2434157) B2434157
theorem B1622787 : Blo 1621009 1622787 := bstep (se 1 (by rfl) ⟨1217090, by rfl⟩ : syracuseStep 1622787 = 2434181) B2434181
theorem B2433809 : Blo 1621009 2433809 := bstep (se 2 (by rfl) ⟨912678, by rfl⟩ : syracuseStep 2433809 = 1825357) B1825357
theorem B1622803 : Blo 1621009 1622803 := bstep (se 1 (by rfl) ⟨1217102, by rfl⟩ : syracuseStep 1622803 = 2434205) B2434205
theorem B2736929 : Blo 1621009 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B8209187 : Blo 1621009 8209187 := bstep (se 1 (by rfl) ⟨6156890, by rfl⟩ : syracuseStep 8209187 = 12313781) B12313781
theorem B2433827 : Blo 1621009 2433827 := bstep (se 1 (by rfl) ⟨1825370, by rfl⟩ : syracuseStep 2433827 = 3650741) B3650741
theorem B1622819 : Blo 1621009 1622819 := bstep (se 1 (by rfl) ⟨1217114, by rfl⟩ : syracuseStep 1622819 = 2434229) B2434229
theorem B1622835 : Blo 1621009 1622835 := bstep (se 1 (by rfl) ⟨1217126, by rfl⟩ : syracuseStep 1622835 = 2434253) B2434253
theorem B2433857 : Blo 1621009 2433857 := bstep (se 2 (by rfl) ⟨912696, by rfl⟩ : syracuseStep 2433857 = 1825393) B1825393
theorem B1622851 : Blo 1621009 1622851 := bstep (se 1 (by rfl) ⟨1217138, by rfl⟩ : syracuseStep 1622851 = 2434277) B2434277
theorem B2433875 : Blo 1621009 2433875 := bstep (se 1 (by rfl) ⟨1825406, by rfl⟩ : syracuseStep 2433875 = 3650813) B3650813
theorem B1622867 : Blo 1621009 1622867 := bstep (se 1 (by rfl) ⟨1217150, by rfl⟩ : syracuseStep 1622867 = 2434301) B2434301
theorem B1622883 : Blo 1621009 1622883 := bstep (se 1 (by rfl) ⟨1217162, by rfl⟩ : syracuseStep 1622883 = 2434325) B2434325
theorem B2433905 : Blo 1621009 2433905 := bstep (se 2 (by rfl) ⟨912714, by rfl⟩ : syracuseStep 2433905 = 1825429) B1825429
theorem B1622899 : Blo 1621009 1622899 := bstep (se 1 (by rfl) ⟨1217174, by rfl⟩ : syracuseStep 1622899 = 2434349) B2434349
theorem B3081073 : Blo 1621009 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B2433923 : Blo 1621009 2433923 := bstep (se 1 (by rfl) ⟨1825442, by rfl⟩ : syracuseStep 2433923 = 3650885) B3650885
theorem B1622915 : Blo 1621009 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B5473169 : Blo 1621009 5473169 := bstep (se 2 (by rfl) ⟨2052438, by rfl⟩ : syracuseStep 5473169 = 4104877) B4104877
theorem B1622931 : Blo 1621009 1622931 := bstep (se 1 (by rfl) ⟨1217198, by rfl⟩ : syracuseStep 1622931 = 2434397) B2434397
theorem B2737057 : Blo 1621009 2737057 := bstep (se 2 (by rfl) ⟨1026396, by rfl⟩ : syracuseStep 2737057 = 2052793) B2052793
theorem B2433953 : Blo 1621009 2433953 := bstep (se 2 (by rfl) ⟨912732, by rfl⟩ : syracuseStep 2433953 = 1825465) B1825465
theorem B1622947 : Blo 1621009 1622947 := bstep (se 1 (by rfl) ⟨1217210, by rfl⟩ : syracuseStep 1622947 = 2434421) B2434421
theorem B2433971 : Blo 1621009 2433971 := bstep (se 1 (by rfl) ⟨1825478, by rfl⟩ : syracuseStep 2433971 = 3650957) B3650957
theorem B1622963 : Blo 1621009 1622963 := bstep (se 1 (by rfl) ⟨1217222, by rfl⟩ : syracuseStep 1622963 = 2434445) B2434445
theorem B2737091 : Blo 1621009 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B1622979 : Blo 1621009 1622979 := bstep (se 1 (by rfl) ⟨1217234, by rfl⟩ : syracuseStep 1622979 = 2434469) B2434469
theorem B13157317 : Blo 1621009 13157317 := bstep (se 4 (by rfl) ⟨1233498, by rfl⟩ : syracuseStep 13157317 = 2466997) B2466997
theorem B2434001 : Blo 1621009 2434001 := bstep (se 2 (by rfl) ⟨912750, by rfl⟩ : syracuseStep 2434001 = 1825501) B1825501
theorem B1622995 : Blo 1621009 1622995 := bstep (se 1 (by rfl) ⟨1217246, by rfl⟩ : syracuseStep 1622995 = 2434493) B2434493
theorem B2434019 : Blo 1621009 2434019 := bstep (se 1 (by rfl) ⟨1825514, by rfl⟩ : syracuseStep 2434019 = 3651029) B3651029
theorem B4105201 : Blo 1621009 4105201 := bstep (se 2 (by rfl) ⟨1539450, by rfl⟩ : syracuseStep 4105201 = 3078901) B3078901
theorem B2434049 : Blo 1621009 2434049 := bstep (se 2 (by rfl) ⟨912768, by rfl⟩ : syracuseStep 2434049 = 1825537) B1825537
theorem B2434067 : Blo 1621009 2434067 := bstep (se 1 (by rfl) ⟨1825550, by rfl⟩ : syracuseStep 2434067 = 3651101) B3651101
theorem B2434097 : Blo 1621009 2434097 := bstep (se 2 (by rfl) ⟨912786, by rfl⟩ : syracuseStep 2434097 = 1825573) B1825573
theorem B2737219 : Blo 1621009 2737219 := bstep (se 1 (by rfl) ⟨2052914, by rfl⟩ : syracuseStep 2737219 = 4105829) B4105829
theorem B2434115 : Blo 1621009 2434115 := bstep (se 1 (by rfl) ⟨1825586, by rfl⟩ : syracuseStep 2434115 = 3651173) B3651173
theorem B2434145 : Blo 1621009 2434145 := bstep (se 2 (by rfl) ⟨912804, by rfl⟩ : syracuseStep 2434145 = 1825609) B1825609
theorem B2434163 : Blo 1621009 2434163 := bstep (se 1 (by rfl) ⟨1825622, by rfl⟩ : syracuseStep 2434163 = 3651245) B3651245
theorem B2434193 : Blo 1621009 2434193 := bstep (se 2 (by rfl) ⟨912822, by rfl⟩ : syracuseStep 2434193 = 1825645) B1825645
theorem B2434211 : Blo 1621009 2434211 := bstep (se 1 (by rfl) ⟨1825658, by rfl⟩ : syracuseStep 2434211 = 3651317) B3651317
theorem B2434241 : Blo 1621009 2434241 := bstep (se 2 (by rfl) ⟨912840, by rfl⟩ : syracuseStep 2434241 = 1825681) B1825681
theorem B2737361 : Blo 1621009 2737361 := bstep (se 2 (by rfl) ⟨1026510, by rfl⟩ : syracuseStep 2737361 = 2053021) B2053021
theorem B2434259 : Blo 1621009 2434259 := bstep (se 1 (by rfl) ⟨1825694, by rfl⟩ : syracuseStep 2434259 = 3651389) B3651389
theorem B2434289 : Blo 1621009 2434289 := bstep (se 2 (by rfl) ⟨912858, by rfl⟩ : syracuseStep 2434289 = 1825717) B1825717
theorem B2598131 : Blo 1621009 2598131 := bstep (se 1 (by rfl) ⟨1948598, by rfl⟩ : syracuseStep 2598131 = 3897197) B3897197
theorem B4105475 : Blo 1621009 4105475 := bstep (se 1 (by rfl) ⟨3079106, by rfl⟩ : syracuseStep 4105475 = 6158213) B6158213
theorem B2434307 : Blo 1621009 2434307 := bstep (se 1 (by rfl) ⟨1825730, by rfl⟩ : syracuseStep 2434307 = 3651461) B3651461
theorem B2434337 : Blo 1621009 2434337 := bstep (se 2 (by rfl) ⟨912876, by rfl⟩ : syracuseStep 2434337 = 1825753) B1825753
theorem B3851569 : Blo 1621009 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B2434355 : Blo 1621009 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B2737489 : Blo 1621009 2737489 := bstep (se 2 (by rfl) ⟨1026558, by rfl⟩ : syracuseStep 2737489 = 2053117) B2053117
theorem B2434385 : Blo 1621009 2434385 := bstep (se 2 (by rfl) ⟨912894, by rfl⟩ : syracuseStep 2434385 = 1825789) B1825789
theorem B2434403 : Blo 1621009 2434403 := bstep (se 1 (by rfl) ⟨1825802, by rfl⟩ : syracuseStep 2434403 = 3651605) B3651605
theorem B18990449 : Blo 1621009 18990449 := bstep (se 2 (by rfl) ⟨7121418, by rfl⟩ : syracuseStep 18990449 = 14242837) B14242837
theorem B2598259 : Blo 1621009 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B2737523 : Blo 1621009 2737523 := bstep (se 1 (by rfl) ⟨2053142, by rfl⟩ : syracuseStep 2737523 = 4106285) B4106285
theorem B2434433 : Blo 1621009 2434433 := bstep (se 2 (by rfl) ⟨912912, by rfl⟩ : syracuseStep 2434433 = 1825825) B1825825
theorem B2434451 : Blo 1621009 2434451 := bstep (se 1 (by rfl) ⟨1825838, by rfl⟩ : syracuseStep 2434451 = 3651677) B3651677
theorem B5473709 : Blo 1621009 5473709 := bstep (se 3 (by rfl) ⟨1026320, by rfl⟩ : syracuseStep 5473709 = 2052641) B2052641
theorem B2434481 : Blo 1621009 2434481 := bstep (se 2 (by rfl) ⟨912930, by rfl⟩ : syracuseStep 2434481 = 1825861) B1825861
theorem B2598323 : Blo 1621009 2598323 := bstep (se 1 (by rfl) ⟨1948742, by rfl⟩ : syracuseStep 2598323 = 3897485) B3897485
theorem B4105667 : Blo 1621009 4105667 := bstep (se 1 (by rfl) ⟨3079250, by rfl⟩ : syracuseStep 4105667 = 6158501) B6158501
theorem B2434499 : Blo 1621009 2434499 := bstep (se 1 (by rfl) ⟨1825874, by rfl⟩ : syracuseStep 2434499 = 3651749) B3651749
theorem B5473763 : Blo 1621009 5473763 := bstep (se 1 (by rfl) ⟨4105322, by rfl⟩ : syracuseStep 5473763 = 8210645) B8210645
theorem B6579697 : Blo 1621009 6579697 := bstep (se 2 (by rfl) ⟨2467386, by rfl⟩ : syracuseStep 6579697 = 4934773) B4934773
theorem B2737651 : Blo 1621009 2737651 := bstep (se 1 (by rfl) ⟨2053238, by rfl⟩ : syracuseStep 2737651 = 4106477) B4106477
theorem B6161933 : Blo 1621009 6161933 := bstep (se 3 (by rfl) ⟨1155362, by rfl⟩ : syracuseStep 6161933 = 2310725) B2310725
theorem B7792163 : Blo 1621009 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B2467363 : Blo 1621009 2467363 := bstep (se 1 (by rfl) ⟨1850522, by rfl⟩ : syracuseStep 2467363 = 3701045) B3701045
theorem B4933169 : Blo 1621009 4933169 := bstep (se 2 (by rfl) ⟨1849938, by rfl⟩ : syracuseStep 4933169 = 3699877) B3699877
theorem B8209997 : Blo 1621009 8209997 := bstep (se 3 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 8209997 = 3078749) B3078749
theorem B2737793 : Blo 1621009 2737793 := bstep (se 2 (by rfl) ⟨1026672, by rfl⟩ : syracuseStep 2737793 = 2053345) B2053345
theorem B4679309 : Blo 1621009 4679309 := bstep (se 3 (by rfl) ⟨877370, by rfl⟩ : syracuseStep 4679309 = 1754741) B1754741
theorem B5195441 : Blo 1621009 5195441 := bstep (se 2 (by rfl) ⟨1948290, by rfl⟩ : syracuseStep 5195441 = 3896581) B3896581
theorem B4335299 : Blo 1621009 4335299 := bstep (se 1 (by rfl) ⟨3251474, by rfl⟩ : syracuseStep 4335299 = 6502949) B6502949
theorem B22193891 : Blo 1621009 22193891 := bstep (se 1 (by rfl) ⟨16645418, by rfl⟩ : syracuseStep 22193891 = 33290837) B33290837
theorem B5474033 : Blo 1621009 5474033 := bstep (se 2 (by rfl) ⟨2052762, by rfl⟩ : syracuseStep 5474033 = 4105525) B4105525
theorem B2737921 : Blo 1621009 2737921 := bstep (se 2 (by rfl) ⟨1026720, by rfl⟩ : syracuseStep 2737921 = 2053441) B2053441
theorem B2737955 : Blo 1621009 2737955 := bstep (se 1 (by rfl) ⟨2053466, by rfl⟩ : syracuseStep 2737955 = 4106933) B4106933
theorem B19728197 : Blo 1621009 19728197 := bstep (se 4 (by rfl) ⟨1849518, by rfl⟩ : syracuseStep 19728197 = 3699037) B3699037
theorem B3286865 : Blo 1621009 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B5269379 : Blo 1621009 5269379 := bstep (se 1 (by rfl) ⟨3952034, by rfl⟩ : syracuseStep 5269379 = 7904069) B7904069
theorem B2598817 : Blo 1621009 2598817 := bstep (se 2 (by rfl) ⟨974556, by rfl⟩ : syracuseStep 2598817 = 1949113) B1949113
theorem B2738083 : Blo 1621009 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B15591365 : Blo 1621009 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B5195789 : Blo 1621009 5195789 := bstep (se 3 (by rfl) ⟨974210, by rfl⟩ : syracuseStep 5195789 = 1948421) B1948421
theorem B4384813 : Blo 1621009 4384813 := bstep (se 3 (by rfl) ⟨822152, by rfl⟩ : syracuseStep 4384813 = 1644305) B1644305
theorem B3647537 : Blo 1621009 3647537 := bstep (se 2 (by rfl) ⟨1367826, by rfl⟩ : syracuseStep 3647537 = 2735653) B2735653
theorem B2738225 : Blo 1621009 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B3647555 : Blo 1621009 3647555 := bstep (se 1 (by rfl) ⟨2735666, by rfl⟩ : syracuseStep 3647555 = 5471333) B5471333
theorem B2738353 : Blo 1621009 2738353 := bstep (se 2 (by rfl) ⟨1026882, by rfl⟩ : syracuseStep 2738353 = 2053765) B2053765
theorem B2738387 : Blo 1621009 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B35064035 : Blo 1621009 35064035 := bstep (se 1 (by rfl) ⟨26298026, by rfl⟩ : syracuseStep 35064035 = 52596053) B52596053
theorem B5474573 : Blo 1621009 5474573 := bstep (se 3 (by rfl) ⟨1026482, by rfl⟩ : syracuseStep 5474573 = 2052965) B2052965
theorem B7792931 : Blo 1621009 7792931 := bstep (se 1 (by rfl) ⟨5844698, by rfl⟩ : syracuseStep 7792931 = 11689397) B11689397
theorem B3557699 : Blo 1621009 3557699 := bstep (se 1 (by rfl) ⟨2668274, by rfl⟩ : syracuseStep 3557699 = 5336549) B5336549
theorem B5474627 : Blo 1621009 5474627 := bstep (se 1 (by rfl) ⟨4105970, by rfl⟩ : syracuseStep 5474627 = 8211941) B8211941
theorem B3647825 : Blo 1621009 3647825 := bstep (se 2 (by rfl) ⟨1367934, by rfl⟩ : syracuseStep 3647825 = 2735869) B2735869
theorem B2738515 : Blo 1621009 2738515 := bstep (se 1 (by rfl) ⟨2053886, by rfl⟩ : syracuseStep 2738515 = 4107773) B4107773
theorem B3647843 : Blo 1621009 3647843 := bstep (se 1 (by rfl) ⟨2735882, by rfl⟩ : syracuseStep 3647843 = 5471765) B5471765
theorem B4106609 : Blo 1621009 4106609 := bstep (se 2 (by rfl) ⟨1539978, by rfl⟩ : syracuseStep 4106609 = 3079957) B3079957
theorem B4106659 : Blo 1621009 4106659 := bstep (se 1 (by rfl) ⟨3079994, by rfl⟩ : syracuseStep 4106659 = 6159989) B6159989
theorem B2738657 : Blo 1621009 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B4106801 : Blo 1621009 4106801 := bstep (se 2 (by rfl) ⟨1540050, by rfl⟩ : syracuseStep 4106801 = 3080101) B3080101
theorem B2599489 : Blo 1621009 2599489 := bstep (se 2 (by rfl) ⟨974808, by rfl⟩ : syracuseStep 2599489 = 1949617) B1949617
theorem B5474897 : Blo 1621009 5474897 := bstep (se 2 (by rfl) ⟨2053086, by rfl⟩ : syracuseStep 5474897 = 4106173) B4106173
theorem B2738785 : Blo 1621009 2738785 := bstep (se 2 (by rfl) ⟨1027044, by rfl⟩ : syracuseStep 2738785 = 2054089) B2054089
theorem B19999331 : Blo 1621009 19999331 := bstep (se 1 (by rfl) ⟨14999498, by rfl⟩ : syracuseStep 19999331 = 29998997) B29998997
theorem B3648113 : Blo 1621009 3648113 := bstep (se 2 (by rfl) ⟨1368042, by rfl⟩ : syracuseStep 3648113 = 2736085) B2736085
theorem B3648131 : Blo 1621009 3648131 := bstep (se 1 (by rfl) ⟨2736098, by rfl⟩ : syracuseStep 3648131 = 5472197) B5472197
theorem B2738819 : Blo 1621009 2738819 := bstep (se 1 (by rfl) ⟨2054114, by rfl⟩ : syracuseStep 2738819 = 4108229) B4108229
theorem B146131733 : Blo 1621009 146131733 := bstep (se 6 (by rfl) ⟨3424962, by rfl⟩ : syracuseStep 146131733 = 6849925) B6849925
theorem B4631345 : Blo 1621009 4631345 := bstep (se 2 (by rfl) ⟨1736754, by rfl⟩ : syracuseStep 4631345 = 3473509) B3473509
theorem B13151089 : Blo 1621009 13151089 := bstep (se 2 (by rfl) ⟨4931658, by rfl⟩ : syracuseStep 13151089 = 9863317) B9863317
theorem B3648401 : Blo 1621009 3648401 := bstep (se 2 (by rfl) ⟨1368150, by rfl⟩ : syracuseStep 3648401 = 2736301) B2736301
theorem B3648419 : Blo 1621009 3648419 := bstep (se 1 (by rfl) ⟨2736314, by rfl⟩ : syracuseStep 3648419 = 5472629) B5472629
theorem B4443245 : Blo 1621009 4443245 := bstep (se 3 (by rfl) ⟨833108, by rfl⟩ : syracuseStep 4443245 = 1666217) B1666217
theorem B5475437 : Blo 1621009 5475437 := bstep (se 3 (by rfl) ⟨1026644, by rfl⟩ : syracuseStep 5475437 = 2053289) B2053289
theorem B5844109 : Blo 1621009 5844109 := bstep (se 3 (by rfl) ⟨1095770, by rfl⟩ : syracuseStep 5844109 = 2191541) B2191541
theorem B5475491 : Blo 1621009 5475491 := bstep (se 1 (by rfl) ⟨4106618, by rfl⟩ : syracuseStep 5475491 = 8213237) B8213237
theorem B3648689 : Blo 1621009 3648689 := bstep (se 2 (by rfl) ⟨1368258, by rfl⟩ : syracuseStep 3648689 = 2736517) B2736517
theorem B3648707 : Blo 1621009 3648707 := bstep (se 1 (by rfl) ⟨2736530, by rfl⟩ : syracuseStep 3648707 = 5473061) B5473061
theorem B1731827 : Blo 1621009 1731827 := bstep (se 1 (by rfl) ⟨1298870, by rfl⟩ : syracuseStep 1731827 = 2597741) B2597741
theorem B3697937 : Blo 1621009 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B5475761 : Blo 1621009 5475761 := bstep (se 2 (by rfl) ⟨2053410, by rfl⟩ : syracuseStep 5475761 = 4106821) B4106821
theorem B3648977 : Blo 1621009 3648977 := bstep (se 2 (by rfl) ⟨1368366, by rfl⟩ : syracuseStep 3648977 = 2736733) B2736733
theorem B3648995 : Blo 1621009 3648995 := bstep (se 1 (by rfl) ⟨2736746, by rfl⟩ : syracuseStep 3648995 = 5473493) B5473493
theorem B7794161 : Blo 1621009 7794161 := bstep (se 2 (by rfl) ⟨2922810, by rfl⟩ : syracuseStep 7794161 = 5845621) B5845621
theorem B3509777 : Blo 1621009 3509777 := bstep (se 2 (by rfl) ⟨1316166, by rfl⟩ : syracuseStep 3509777 = 2632333) B2632333
theorem B4107793 : Blo 1621009 4107793 := bstep (se 2 (by rfl) ⟨1540422, by rfl⟩ : syracuseStep 4107793 = 3080845) B3080845
theorem B3894851 : Blo 1621009 3894851 := bstep (se 1 (by rfl) ⟨2921138, by rfl⟩ : syracuseStep 3894851 = 5842277) B5842277
theorem B11685475 : Blo 1621009 11685475 := bstep (se 1 (by rfl) ⟨8764106, by rfl⟩ : syracuseStep 11685475 = 17528213) B17528213
theorem B3894929 : Blo 1621009 3894929 := bstep (se 2 (by rfl) ⟨1460598, by rfl⟩ : syracuseStep 3894929 = 2921197) B2921197
theorem B3649265 : Blo 1621009 3649265 := bstep (se 2 (by rfl) ⟨1368474, by rfl⟩ : syracuseStep 3649265 = 2736949) B2736949
theorem B3649283 : Blo 1621009 3649283 := bstep (se 1 (by rfl) ⟨2736962, by rfl⟩ : syracuseStep 3649283 = 5473925) B5473925
theorem B6926093 : Blo 1621009 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B4108067 : Blo 1621009 4108067 := bstep (se 1 (by rfl) ⟨3081050, by rfl⟩ : syracuseStep 4108067 = 6162101) B6162101
theorem B6246193 : Blo 1621009 6246193 := bstep (se 2 (by rfl) ⟨2342322, by rfl⟩ : syracuseStep 6246193 = 4684645) B4684645
theorem B5197645 : Blo 1621009 5197645 := bstep (se 3 (by rfl) ⟨974558, by rfl⟩ : syracuseStep 5197645 = 1949117) B1949117
theorem B5476301 : Blo 1621009 5476301 := bstep (se 3 (by rfl) ⟨1026806, by rfl⟩ : syracuseStep 5476301 = 2053613) B2053613
theorem B5476355 : Blo 1621009 5476355 := bstep (se 1 (by rfl) ⟨4107266, by rfl⟩ : syracuseStep 5476355 = 8214533) B8214533
theorem B7794701 : Blo 1621009 7794701 := bstep (se 3 (by rfl) ⟨1461506, by rfl⟩ : syracuseStep 7794701 = 2923013) B2923013
theorem B3649553 : Blo 1621009 3649553 := bstep (se 2 (by rfl) ⟨1368582, by rfl⟩ : syracuseStep 3649553 = 2737165) B2737165
theorem B3649571 : Blo 1621009 3649571 := bstep (se 1 (by rfl) ⟨2737178, by rfl⟩ : syracuseStep 3649571 = 5474357) B5474357
theorem B4616291 : Blo 1621009 4616291 := bstep (se 1 (by rfl) ⟨3462218, by rfl⟩ : syracuseStep 4616291 = 6924437) B6924437
theorem B6926435 : Blo 1621009 6926435 := bstep (se 1 (by rfl) ⟨5194826, by rfl⟩ : syracuseStep 6926435 = 10389653) B10389653
theorem B20787299 : Blo 1621009 20787299 := bstep (se 1 (by rfl) ⟨15590474, by rfl⟩ : syracuseStep 20787299 = 31180949) B31180949
theorem B2052211 : Blo 1621009 2052211 := bstep (se 1 (by rfl) ⟨1539158, by rfl⟩ : syracuseStep 2052211 = 3078317) B3078317
theorem B2052307 : Blo 1621009 2052307 := bstep (se 1 (by rfl) ⟨1539230, by rfl⟩ : syracuseStep 2052307 = 3078461) B3078461
theorem B2633969 : Blo 1621009 2633969 := bstep (se 2 (by rfl) ⟨987738, by rfl⟩ : syracuseStep 2633969 = 1975477) B1975477
theorem B6156557 : Blo 1621009 6156557 := bstep (se 3 (by rfl) ⟨1154354, by rfl⟩ : syracuseStep 6156557 = 2308709) B2308709
theorem B5476625 : Blo 1621009 5476625 := bstep (se 2 (by rfl) ⟨2053734, by rfl⟩ : syracuseStep 5476625 = 4107469) B4107469
theorem B3649841 : Blo 1621009 3649841 := bstep (se 2 (by rfl) ⟨1368690, by rfl⟩ : syracuseStep 3649841 = 2737381) B2737381
theorem B3649859 : Blo 1621009 3649859 := bstep (se 1 (by rfl) ⟨2737394, by rfl⟩ : syracuseStep 3649859 = 5474789) B5474789
theorem B2634067 : Blo 1621009 2634067 := bstep (se 1 (by rfl) ⟨1975550, by rfl⟩ : syracuseStep 2634067 = 3951101) B3951101
theorem B9859427 : Blo 1621009 9859427 := bstep (se 1 (by rfl) ⟨7394570, by rfl⟩ : syracuseStep 9859427 = 14789141) B14789141
theorem B3895697 : Blo 1621009 3895697 := bstep (se 2 (by rfl) ⟨1460886, by rfl⟩ : syracuseStep 3895697 = 2921773) B2921773
theorem B4616621 : Blo 1621009 4616621 := bstep (se 3 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 4616621 = 1731233) B1731233
theorem B8212913 : Blo 1621009 8212913 := bstep (se 2 (by rfl) ⟨3079842, by rfl⟩ : syracuseStep 8212913 = 6159685) B6159685
theorem B2773457 : Blo 1621009 2773457 := bstep (se 2 (by rfl) ⟨1040046, by rfl⟩ : syracuseStep 2773457 = 2080093) B2080093
theorem B4616689 : Blo 1621009 4616689 := bstep (se 2 (by rfl) ⟨1731258, by rfl⟩ : syracuseStep 4616689 = 3462517) B3462517
theorem B6926897 : Blo 1621009 6926897 := bstep (se 2 (by rfl) ⟨2597586, by rfl⟩ : syracuseStep 6926897 = 5195173) B5195173
theorem B3650129 : Blo 1621009 3650129 := bstep (se 2 (by rfl) ⟨1368798, by rfl⟩ : syracuseStep 3650129 = 2737597) B2737597
theorem B3650147 : Blo 1621009 3650147 := bstep (se 1 (by rfl) ⟨2737610, by rfl⟩ : syracuseStep 3650147 = 5475221) B5475221
theorem B5001905 : Blo 1621009 5001905 := bstep (se 2 (by rfl) ⟨1875714, by rfl⟩ : syracuseStep 5001905 = 3751429) B3751429
theorem B2052803 : Blo 1621009 2052803 := bstep (se 1 (by rfl) ⟨1539602, by rfl⟩ : syracuseStep 2052803 = 3079205) B3079205
theorem B3699395 : Blo 1621009 3699395 := bstep (se 1 (by rfl) ⟨2774546, by rfl⟩ : syracuseStep 3699395 = 5549093) B5549093
theorem B15586019 : Blo 1621009 15586019 := bstep (se 1 (by rfl) ⟨11689514, by rfl⟩ : syracuseStep 15586019 = 23379029) B23379029
theorem B1643267 : Blo 1621009 1643267 := bstep (se 1 (by rfl) ⟨1232450, by rfl⟩ : syracuseStep 1643267 = 2464901) B2464901
theorem B4616963 : Blo 1621009 4616963 := bstep (se 1 (by rfl) ⟨3462722, by rfl⟩ : syracuseStep 4616963 = 6925445) B6925445
theorem B5477165 : Blo 1621009 5477165 := bstep (se 3 (by rfl) ⟨1026968, by rfl⟩ : syracuseStep 5477165 = 2053937) B2053937
theorem B5477219 : Blo 1621009 5477219 := bstep (se 1 (by rfl) ⟨4107914, by rfl⟩ : syracuseStep 5477219 = 8215829) B8215829
theorem B3650417 : Blo 1621009 3650417 := bstep (se 2 (by rfl) ⟨1368906, by rfl⟩ : syracuseStep 3650417 = 2737813) B2737813
theorem B3650435 : Blo 1621009 3650435 := bstep (se 1 (by rfl) ⟨2737826, by rfl⟩ : syracuseStep 3650435 = 5475653) B5475653
theorem B1823683 : Blo 1621009 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B1823827 : Blo 1621009 1823827 := bstep (se 1 (by rfl) ⟨1367870, by rfl⟩ : syracuseStep 1823827 = 2735741) B2735741
theorem B5477489 : Blo 1621009 5477489 := bstep (se 2 (by rfl) ⟨2054058, by rfl⟩ : syracuseStep 5477489 = 4108117) B4108117
theorem B3650705 : Blo 1621009 3650705 := bstep (se 2 (by rfl) ⟨1369014, by rfl⟩ : syracuseStep 3650705 = 2738029) B2738029
theorem B3650723 : Blo 1621009 3650723 := bstep (se 1 (by rfl) ⟨2738042, by rfl⟩ : syracuseStep 3650723 = 5476085) B5476085
theorem B1823971 : Blo 1621009 1823971 := bstep (se 1 (by rfl) ⟨1367978, by rfl⟩ : syracuseStep 1823971 = 2735957) B2735957
theorem B2192627 : Blo 1621009 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B3077443 : Blo 1621009 3077443 := bstep (se 1 (by rfl) ⟨2308082, by rfl⟩ : syracuseStep 3077443 = 4616165) B4616165
theorem B3077489 : Blo 1621009 3077489 := bstep (se 2 (by rfl) ⟨1154058, by rfl⟩ : syracuseStep 3077489 = 2308117) B2308117
theorem B1824115 : Blo 1621009 1824115 := bstep (se 1 (by rfl) ⟨1368086, by rfl⟩ : syracuseStep 1824115 = 2736173) B2736173
theorem B2053507 : Blo 1621009 2053507 := bstep (se 1 (by rfl) ⟨1540130, by rfl⟩ : syracuseStep 2053507 = 3080261) B3080261
theorem B3650993 : Blo 1621009 3650993 := bstep (se 2 (by rfl) ⟨1369122, by rfl⟩ : syracuseStep 3650993 = 2738245) B2738245
theorem B3651011 : Blo 1621009 3651011 := bstep (se 1 (by rfl) ⟨2738258, by rfl⟩ : syracuseStep 3651011 = 5476517) B5476517
theorem B14046691 : Blo 1621009 14046691 := bstep (se 1 (by rfl) ⟨10535018, by rfl⟩ : syracuseStep 14046691 = 21070037) B21070037
theorem B2053603 : Blo 1621009 2053603 := bstep (se 1 (by rfl) ⟨1540202, by rfl⟩ : syracuseStep 2053603 = 3080405) B3080405
theorem B1824259 : Blo 1621009 1824259 := bstep (se 1 (by rfl) ⟨1368194, by rfl⟩ : syracuseStep 1824259 = 2736389) B2736389
theorem B9369101 : Blo 1621009 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B4617805 : Blo 1621009 4617805 := bstep (se 3 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 4617805 = 1731677) B1731677
theorem B18478691 : Blo 1621009 18478691 := bstep (se 1 (by rfl) ⟨13859018, by rfl⟩ : syracuseStep 18478691 = 27718037) B27718037
theorem B4683395 : Blo 1621009 4683395 := bstep (se 1 (by rfl) ⟨3512546, by rfl⟩ : syracuseStep 4683395 = 7025093) B7025093
theorem B5199491 : Blo 1621009 5199491 := bstep (se 1 (by rfl) ⟨3899618, by rfl⟩ : syracuseStep 5199491 = 7799237) B7799237
theorem B3077777 : Blo 1621009 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B1824403 : Blo 1621009 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B3651281 : Blo 1621009 3651281 := bstep (se 2 (by rfl) ⟨1369230, by rfl⟩ : syracuseStep 3651281 = 2738461) B2738461
theorem B3651299 : Blo 1621009 3651299 := bstep (se 1 (by rfl) ⟨2738474, by rfl⟩ : syracuseStep 3651299 = 5476949) B5476949
theorem B4617965 : Blo 1621009 4617965 := bstep (se 3 (by rfl) ⟨865868, by rfl⟩ : syracuseStep 4617965 = 1731737) B1731737
theorem B17528561 : Blo 1621009 17528561 := bstep (se 2 (by rfl) ⟨6573210, by rfl⟩ : syracuseStep 17528561 = 13146421) B13146421
theorem B1824547 : Blo 1621009 1824547 := bstep (se 1 (by rfl) ⟨1368410, by rfl⟩ : syracuseStep 1824547 = 2736821) B2736821
theorem B5551939 : Blo 1621009 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B8214371 : Blo 1621009 8214371 := bstep (se 1 (by rfl) ⟨6160778, by rfl⟩ : syracuseStep 8214371 = 12321557) B12321557
theorem B16013197 : Blo 1621009 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B7796621 : Blo 1621009 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B4618147 : Blo 1621009 4618147 := bstep (se 1 (by rfl) ⟨3463610, by rfl⟩ : syracuseStep 4618147 = 6927221) B6927221
theorem B1824691 : Blo 1621009 1824691 := bstep (se 1 (by rfl) ⟨1368518, by rfl⟩ : syracuseStep 1824691 = 2737037) B2737037
theorem B2193331 : Blo 1621009 2193331 := bstep (se 1 (by rfl) ⟨1644998, by rfl⟩ : syracuseStep 2193331 = 3289997) B3289997
theorem B2054099 : Blo 1621009 2054099 := bstep (se 1 (by rfl) ⟨1540574, by rfl⟩ : syracuseStep 2054099 = 3081149) B3081149
theorem B3651569 : Blo 1621009 3651569 := bstep (se 2 (by rfl) ⟨1369338, by rfl⟩ : syracuseStep 3651569 = 2738677) B2738677
theorem B3651587 : Blo 1621009 3651587 := bstep (se 1 (by rfl) ⟨2738690, by rfl⟩ : syracuseStep 3651587 = 5477381) B5477381
theorem B1824835 : Blo 1621009 1824835 := bstep (se 1 (by rfl) ⟨1368626, by rfl⟩ : syracuseStep 1824835 = 2737253) B2737253
theorem B14047345 : Blo 1621009 14047345 := bstep (se 2 (by rfl) ⟨5267754, by rfl⟩ : syracuseStep 14047345 = 10535509) B10535509
theorem B4217027 : Blo 1621009 4217027 := bstep (se 1 (by rfl) ⟨3162770, by rfl⟩ : syracuseStep 4217027 = 6325541) B6325541
theorem B1824979 : Blo 1621009 1824979 := bstep (se 1 (by rfl) ⟨1368734, by rfl⟩ : syracuseStep 1824979 = 2737469) B2737469
theorem B3701027 : Blo 1621009 3701027 := bstep (se 1 (by rfl) ⟨2775770, by rfl⟩ : syracuseStep 3701027 = 5551541) B5551541
theorem B3078499 : Blo 1621009 3078499 := bstep (se 1 (by rfl) ⟨2308874, by rfl⟩ : syracuseStep 3078499 = 4617749) B4617749
theorem B1825123 : Blo 1621009 1825123 := bstep (se 1 (by rfl) ⟨1368842, by rfl⟩ : syracuseStep 1825123 = 2737685) B2737685
theorem B3119555 : Blo 1621009 3119555 := bstep (se 1 (by rfl) ⟨2339666, by rfl⟩ : syracuseStep 3119555 = 4679333) B4679333
theorem B9238981 : Blo 1621009 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B1825267 : Blo 1621009 1825267 := bstep (se 1 (by rfl) ⟨1368950, by rfl⟩ : syracuseStep 1825267 = 2737901) B2737901
theorem B2431523 : Blo 1621009 2431523 := bstep (se 1 (by rfl) ⟨1823642, by rfl⟩ : syracuseStep 2431523 = 3647285) B3647285
theorem B2923057 : Blo 1621009 2923057 := bstep (se 2 (by rfl) ⟨1096146, by rfl⟩ : syracuseStep 2923057 = 2192293) B2192293
theorem B2431553 : Blo 1621009 2431553 := bstep (se 2 (by rfl) ⟨911832, by rfl⟩ : syracuseStep 2431553 = 1823665) B1823665
theorem B2308675 : Blo 1621009 2308675 := bstep (se 1 (by rfl) ⟨1731506, by rfl⟩ : syracuseStep 2308675 = 3463013) B3463013
theorem B2964035 : Blo 1621009 2964035 := bstep (se 1 (by rfl) ⟨2223026, by rfl⟩ : syracuseStep 2964035 = 4446053) B4446053
theorem B2431571 : Blo 1621009 2431571 := bstep (se 1 (by rfl) ⟨1823678, by rfl⟩ : syracuseStep 2431571 = 3647357) B3647357
theorem B2431601 : Blo 1621009 2431601 := bstep (se 2 (by rfl) ⟨911850, by rfl⟩ : syracuseStep 2431601 = 1823701) B1823701
theorem B2431619 : Blo 1621009 2431619 := bstep (se 1 (by rfl) ⟨1823714, by rfl⟩ : syracuseStep 2431619 = 3647429) B3647429
theorem B1825411 : Blo 1621009 1825411 := bstep (se 1 (by rfl) ⟨1369058, by rfl⟩ : syracuseStep 1825411 = 2738117) B2738117
theorem B8215181 : Blo 1621009 8215181 := bstep (se 3 (by rfl) ⟨1540346, by rfl⟩ : syracuseStep 8215181 = 3080693) B3080693
theorem B2431649 : Blo 1621009 2431649 := bstep (se 2 (by rfl) ⟨911868, by rfl⟩ : syracuseStep 2431649 = 1823737) B1823737
theorem B2431667 : Blo 1621009 2431667 := bstep (se 1 (by rfl) ⟨1823750, by rfl⟩ : syracuseStep 2431667 = 3647501) B3647501
theorem B2431697 : Blo 1621009 2431697 := bstep (se 2 (by rfl) ⟨911886, by rfl⟩ : syracuseStep 2431697 = 1823773) B1823773
theorem B2431715 : Blo 1621009 2431715 := bstep (se 1 (by rfl) ⟨1823786, by rfl⟩ : syracuseStep 2431715 = 3647573) B3647573
theorem B1948387 : Blo 1621009 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B2431745 : Blo 1621009 2431745 := bstep (se 2 (by rfl) ⟨911904, by rfl⟩ : syracuseStep 2431745 = 1823809) B1823809
theorem B2431763 : Blo 1621009 2431763 := bstep (se 1 (by rfl) ⟨1823822, by rfl⟩ : syracuseStep 2431763 = 3647645) B3647645
theorem B1825555 : Blo 1621009 1825555 := bstep (se 1 (by rfl) ⟨1369166, by rfl⟩ : syracuseStep 1825555 = 2738333) B2738333
theorem B3078947 : Blo 1621009 3078947 := bstep (se 1 (by rfl) ⟨2309210, by rfl⟩ : syracuseStep 3078947 = 4618421) B4618421
theorem B2431793 : Blo 1621009 2431793 := bstep (se 2 (by rfl) ⟨911922, by rfl⟩ : syracuseStep 2431793 = 1823845) B1823845
theorem B2431811 : Blo 1621009 2431811 := bstep (se 1 (by rfl) ⟨1823858, by rfl⟩ : syracuseStep 2431811 = 3647717) B3647717
theorem B3464003 : Blo 1621009 3464003 := bstep (se 1 (by rfl) ⟨2598002, by rfl⟩ : syracuseStep 3464003 = 5196005) B5196005
theorem B10386245 : Blo 1621009 10386245 := bstep (se 4 (by rfl) ⟨973710, by rfl⟩ : syracuseStep 10386245 = 1947421) B1947421
theorem B2431841 : Blo 1621009 2431841 := bstep (se 2 (by rfl) ⟨911940, by rfl⟩ : syracuseStep 2431841 = 1823881) B1823881
theorem B9870179 : Blo 1621009 9870179 := bstep (se 1 (by rfl) ⟨7402634, by rfl⟩ : syracuseStep 9870179 = 14805269) B14805269
theorem B2431859 : Blo 1621009 2431859 := bstep (se 1 (by rfl) ⟨1823894, by rfl⟩ : syracuseStep 2431859 = 3647789) B3647789
theorem B5471117 : Blo 1621009 5471117 := bstep (se 3 (by rfl) ⟨1025834, by rfl⟩ : syracuseStep 5471117 = 2051669) B2051669
theorem B2431889 : Blo 1621009 2431889 := bstep (se 2 (by rfl) ⟨911958, by rfl⟩ : syracuseStep 2431889 = 1823917) B1823917
theorem B2431907 : Blo 1621009 2431907 := bstep (se 1 (by rfl) ⟨1823930, by rfl⟩ : syracuseStep 2431907 = 3647861) B3647861
theorem B1825699 : Blo 1621009 1825699 := bstep (se 1 (by rfl) ⟨1369274, by rfl⟩ : syracuseStep 1825699 = 2738549) B2738549
theorem B17546165 : Blo 1621009 17546165 := bstep (se 5 (by rfl) ⟨822476, by rfl⟩ : syracuseStep 17546165 = 1644953) B1644953
theorem B2431937 : Blo 1621009 2431937 := bstep (se 2 (by rfl) ⟨911976, by rfl⟩ : syracuseStep 2431937 = 1823953) B1823953
theorem B5471171 : Blo 1621009 5471171 := bstep (se 1 (by rfl) ⟨4103378, by rfl⟩ : syracuseStep 5471171 = 8206757) B8206757
theorem B2431955 : Blo 1621009 2431955 := bstep (se 1 (by rfl) ⟨1823966, by rfl⟩ : syracuseStep 2431955 = 3647933) B3647933
theorem B2431985 : Blo 1621009 2431985 := bstep (se 2 (by rfl) ⟨911994, by rfl⟩ : syracuseStep 2431985 = 1823989) B1823989
theorem B2432003 : Blo 1621009 2432003 := bstep (se 1 (by rfl) ⟨1824002, by rfl⟩ : syracuseStep 2432003 = 3648005) B3648005
theorem B1621011 : Blo 1621009 1621011 := bstep (se 1 (by rfl) ⟨1215758, by rfl⟩ : syracuseStep 1621011 = 2431517) B2431517
theorem B2432033 : Blo 1621009 2432033 := bstep (se 2 (by rfl) ⟨912012, by rfl⟩ : syracuseStep 2432033 = 1824025) B1824025
theorem B2309153 : Blo 1621009 2309153 := bstep (se 2 (by rfl) ⟨865932, by rfl⟩ : syracuseStep 2309153 = 1731865) B1731865
theorem B1621027 : Blo 1621009 1621027 := bstep (se 1 (by rfl) ⟨1215770, by rfl⟩ : syracuseStep 1621027 = 2431541) B2431541
theorem B1621043 : Blo 1621009 1621043 := bstep (se 1 (by rfl) ⟨1215782, by rfl⟩ : syracuseStep 1621043 = 2431565) B2431565
theorem B2432051 : Blo 1621009 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B1825843 : Blo 1621009 1825843 := bstep (se 1 (by rfl) ⟨1369382, by rfl⟩ : syracuseStep 1825843 = 2738765) B2738765
theorem B1621059 : Blo 1621009 1621059 := bstep (se 1 (by rfl) ⟨1215794, by rfl⟩ : syracuseStep 1621059 = 2431589) B2431589
theorem B3079235 : Blo 1621009 3079235 := bstep (se 1 (by rfl) ⟨2309426, by rfl⟩ : syracuseStep 3079235 = 4618853) B4618853
theorem B13859909 : Blo 1621009 13859909 := bstep (se 4 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 13859909 = 2598733) B2598733
theorem B2432081 : Blo 1621009 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B1621075 : Blo 1621009 1621075 := bstep (se 1 (by rfl) ⟨1215806, by rfl⟩ : syracuseStep 1621075 = 2431613) B2431613
theorem B1621091 : Blo 1621009 1621091 := bstep (se 1 (by rfl) ⟨1215818, by rfl⟩ : syracuseStep 1621091 = 2431637) B2431637
theorem B2432099 : Blo 1621009 2432099 := bstep (se 1 (by rfl) ⟨1824074, by rfl⟩ : syracuseStep 2432099 = 3648149) B3648149
theorem B1948771 : Blo 1621009 1948771 := bstep (se 1 (by rfl) ⟨1461578, by rfl⟩ : syracuseStep 1948771 = 2923157) B2923157
theorem B6159473 : Blo 1621009 6159473 := bstep (se 2 (by rfl) ⟨2309802, by rfl⟩ : syracuseStep 6159473 = 4619605) B4619605
theorem B1621107 : Blo 1621009 1621107 := bstep (se 1 (by rfl) ⟨1215830, by rfl⟩ : syracuseStep 1621107 = 2431661) B2431661
theorem B2432129 : Blo 1621009 2432129 := bstep (se 2 (by rfl) ⟨912048, by rfl⟩ : syracuseStep 2432129 = 1824097) B1824097
theorem B1621123 : Blo 1621009 1621123 := bstep (se 1 (by rfl) ⟨1215842, by rfl⟩ : syracuseStep 1621123 = 2431685) B2431685
theorem B1621139 : Blo 1621009 1621139 := bstep (se 1 (by rfl) ⟨1215854, by rfl⟩ : syracuseStep 1621139 = 2431709) B2431709
theorem B2432147 : Blo 1621009 2432147 := bstep (se 1 (by rfl) ⟨1824110, by rfl⟩ : syracuseStep 2432147 = 3648221) B3648221
theorem B2309267 : Blo 1621009 2309267 := bstep (se 1 (by rfl) ⟨1731950, by rfl⟩ : syracuseStep 2309267 = 3463901) B3463901
theorem B1621155 : Blo 1621009 1621155 := bstep (se 1 (by rfl) ⟨1215866, by rfl⟩ : syracuseStep 1621155 = 2431733) B2431733
theorem B2432177 : Blo 1621009 2432177 := bstep (se 2 (by rfl) ⟨912066, by rfl⟩ : syracuseStep 2432177 = 1824133) B1824133
theorem B1621171 : Blo 1621009 1621171 := bstep (se 1 (by rfl) ⟨1215878, by rfl⟩ : syracuseStep 1621171 = 2431757) B2431757
theorem B1621187 : Blo 1621009 1621187 := bstep (se 1 (by rfl) ⟨1215890, by rfl⟩ : syracuseStep 1621187 = 2431781) B2431781
theorem B2432195 : Blo 1621009 2432195 := bstep (se 1 (by rfl) ⟨1824146, by rfl⟩ : syracuseStep 2432195 = 3648293) B3648293
theorem B5471441 : Blo 1621009 5471441 := bstep (se 2 (by rfl) ⟨2051790, by rfl⟩ : syracuseStep 5471441 = 4103581) B4103581
theorem B1621203 : Blo 1621009 1621203 := bstep (se 1 (by rfl) ⟨1215902, by rfl⟩ : syracuseStep 1621203 = 2431805) B2431805
theorem B2432225 : Blo 1621009 2432225 := bstep (se 2 (by rfl) ⟨912084, by rfl⟩ : syracuseStep 2432225 = 1824169) B1824169
theorem B1621219 : Blo 1621009 1621219 := bstep (se 1 (by rfl) ⟨1215914, by rfl⟩ : syracuseStep 1621219 = 2431829) B2431829
theorem B7019747 : Blo 1621009 7019747 := bstep (se 1 (by rfl) ⟨5264810, by rfl⟩ : syracuseStep 7019747 = 10529621) B10529621
theorem B2309347 : Blo 1621009 2309347 := bstep (se 1 (by rfl) ⟨1732010, by rfl⟩ : syracuseStep 2309347 = 3464021) B3464021
theorem B18734321 : Blo 1621009 18734321 := bstep (se 2 (by rfl) ⟨7025370, by rfl⟩ : syracuseStep 18734321 = 14050741) B14050741
theorem B1621235 : Blo 1621009 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B2432243 : Blo 1621009 2432243 := bstep (se 1 (by rfl) ⟨1824182, by rfl⟩ : syracuseStep 2432243 = 3648365) B3648365
theorem B1621251 : Blo 1621009 1621251 := bstep (se 1 (by rfl) ⟨1215938, by rfl⟩ : syracuseStep 1621251 = 2431877) B2431877
theorem B2432273 : Blo 1621009 2432273 := bstep (se 2 (by rfl) ⟨912102, by rfl⟩ : syracuseStep 2432273 = 1824205) B1824205
theorem B4619537 : Blo 1621009 4619537 := bstep (se 2 (by rfl) ⟨1732326, by rfl⟩ : syracuseStep 4619537 = 3464653) B3464653
theorem B1621267 : Blo 1621009 1621267 := bstep (se 1 (by rfl) ⟨1215950, by rfl⟩ : syracuseStep 1621267 = 2431901) B2431901
theorem B1621283 : Blo 1621009 1621283 := bstep (se 1 (by rfl) ⟨1215962, by rfl⟩ : syracuseStep 1621283 = 2431925) B2431925
theorem B2432291 : Blo 1621009 2432291 := bstep (se 1 (by rfl) ⟨1824218, by rfl⟩ : syracuseStep 2432291 = 3648437) B3648437
theorem B1621299 : Blo 1621009 1621299 := bstep (se 1 (by rfl) ⟨1215974, by rfl⟩ : syracuseStep 1621299 = 2431949) B2431949
theorem B2432321 : Blo 1621009 2432321 := bstep (se 2 (by rfl) ⟨912120, by rfl⟩ : syracuseStep 2432321 = 1824241) B1824241
theorem B1621315 : Blo 1621009 1621315 := bstep (se 1 (by rfl) ⟨1215986, by rfl⟩ : syracuseStep 1621315 = 2431973) B2431973
theorem B1621331 : Blo 1621009 1621331 := bstep (se 1 (by rfl) ⟨1215998, by rfl⟩ : syracuseStep 1621331 = 2431997) B2431997
theorem B2432339 : Blo 1621009 2432339 := bstep (se 1 (by rfl) ⟨1824254, by rfl⟩ : syracuseStep 2432339 = 3648509) B3648509
theorem B1621347 : Blo 1621009 1621347 := bstep (se 1 (by rfl) ⟨1216010, by rfl⟩ : syracuseStep 1621347 = 2432021) B2432021
theorem B12320099 : Blo 1621009 12320099 := bstep (se 1 (by rfl) ⟨9240074, by rfl⟩ : syracuseStep 12320099 = 18480149) B18480149
theorem B8207729 : Blo 1621009 8207729 := bstep (se 2 (by rfl) ⟨3077898, by rfl⟩ : syracuseStep 8207729 = 6155797) B6155797
theorem B2432369 : Blo 1621009 2432369 := bstep (se 2 (by rfl) ⟨912138, by rfl⟩ : syracuseStep 2432369 = 1824277) B1824277
theorem B1621363 : Blo 1621009 1621363 := bstep (se 1 (by rfl) ⟨1216022, by rfl⟩ : syracuseStep 1621363 = 2432045) B2432045
theorem B2735491 : Blo 1621009 2735491 := bstep (se 1 (by rfl) ⟨2051618, by rfl⟩ : syracuseStep 2735491 = 4103237) B4103237
theorem B1621379 : Blo 1621009 1621379 := bstep (se 1 (by rfl) ⟨1216034, by rfl⟩ : syracuseStep 1621379 = 2432069) B2432069
theorem B2432387 : Blo 1621009 2432387 := bstep (se 1 (by rfl) ⟨1824290, by rfl⟩ : syracuseStep 2432387 = 3648581) B3648581
theorem B52600205 : Blo 1621009 52600205 := bstep (se 3 (by rfl) ⟨9862538, by rfl⟩ : syracuseStep 52600205 = 19725077) B19725077
theorem B1621395 : Blo 1621009 1621395 := bstep (se 1 (by rfl) ⟨1216046, by rfl⟩ : syracuseStep 1621395 = 2432093) B2432093
theorem B2432417 : Blo 1621009 2432417 := bstep (se 2 (by rfl) ⟨912156, by rfl⟩ : syracuseStep 2432417 = 1824313) B1824313
theorem B1621411 : Blo 1621009 1621411 := bstep (se 1 (by rfl) ⟨1216058, by rfl⟩ : syracuseStep 1621411 = 2432117) B2432117
theorem B1621427 : Blo 1621009 1621427 := bstep (se 1 (by rfl) ⟨1216070, by rfl⟩ : syracuseStep 1621427 = 2432141) B2432141
theorem B2432435 : Blo 1621009 2432435 := bstep (se 1 (by rfl) ⟨1824326, by rfl⟩ : syracuseStep 2432435 = 3648653) B3648653
theorem B1621443 : Blo 1621009 1621443 := bstep (se 1 (by rfl) ⟨1216082, by rfl⟩ : syracuseStep 1621443 = 2432165) B2432165
theorem B2432465 : Blo 1621009 2432465 := bstep (se 2 (by rfl) ⟨912174, by rfl⟩ : syracuseStep 2432465 = 1824349) B1824349
theorem B1621459 : Blo 1621009 1621459 := bstep (se 1 (by rfl) ⟨1216094, by rfl⟩ : syracuseStep 1621459 = 2432189) B2432189
theorem B1621475 : Blo 1621009 1621475 := bstep (se 1 (by rfl) ⟨1216106, by rfl⟩ : syracuseStep 1621475 = 2432213) B2432213
theorem B2432483 : Blo 1621009 2432483 := bstep (se 1 (by rfl) ⟨1824362, by rfl⟩ : syracuseStep 2432483 = 3648725) B3648725
theorem B1621491 : Blo 1621009 1621491 := bstep (se 1 (by rfl) ⟨1216118, by rfl⟩ : syracuseStep 1621491 = 2432237) B2432237
theorem B2432513 : Blo 1621009 2432513 := bstep (se 2 (by rfl) ⟨912192, by rfl⟩ : syracuseStep 2432513 = 1824385) B1824385
theorem B1621507 : Blo 1621009 1621507 := bstep (se 1 (by rfl) ⟨1216130, by rfl⟩ : syracuseStep 1621507 = 2432261) B2432261
theorem B2735633 : Blo 1621009 2735633 := bstep (se 2 (by rfl) ⟨1025862, by rfl⟩ : syracuseStep 2735633 = 2051725) B2051725
theorem B1621523 : Blo 1621009 1621523 := bstep (se 1 (by rfl) ⟨1216142, by rfl⟩ : syracuseStep 1621523 = 2432285) B2432285
theorem B2432531 : Blo 1621009 2432531 := bstep (se 1 (by rfl) ⟨1824398, by rfl⟩ : syracuseStep 2432531 = 3648797) B3648797
theorem B1621539 : Blo 1621009 1621539 := bstep (se 1 (by rfl) ⟨1216154, by rfl⟩ : syracuseStep 1621539 = 2432309) B2432309
theorem B2432561 : Blo 1621009 2432561 := bstep (se 2 (by rfl) ⟨912210, by rfl⟩ : syracuseStep 2432561 = 1824421) B1824421
theorem B1621555 : Blo 1621009 1621555 := bstep (se 1 (by rfl) ⟨1216166, by rfl⟩ : syracuseStep 1621555 = 2432333) B2432333
theorem B1621571 : Blo 1621009 1621571 := bstep (se 1 (by rfl) ⟨1216178, by rfl⟩ : syracuseStep 1621571 = 2432357) B2432357
theorem B2432579 : Blo 1621009 2432579 := bstep (se 1 (by rfl) ⟨1824434, by rfl⟩ : syracuseStep 2432579 = 3648869) B3648869
theorem B1621587 : Blo 1621009 1621587 := bstep (se 1 (by rfl) ⟨1216190, by rfl⟩ : syracuseStep 1621587 = 2432381) B2432381
theorem B2432609 : Blo 1621009 2432609 := bstep (se 2 (by rfl) ⟨912228, by rfl⟩ : syracuseStep 2432609 = 1824457) B1824457
theorem B1621603 : Blo 1621009 1621603 := bstep (se 1 (by rfl) ⟨1216202, by rfl⟩ : syracuseStep 1621603 = 2432405) B2432405
theorem B1621619 : Blo 1621009 1621619 := bstep (se 1 (by rfl) ⟨1216214, by rfl⟩ : syracuseStep 1621619 = 2432429) B2432429
theorem B2432627 : Blo 1621009 2432627 := bstep (se 1 (by rfl) ⟨1824470, by rfl⟩ : syracuseStep 2432627 = 3648941) B3648941
theorem B1621635 : Blo 1621009 1621635 := bstep (se 1 (by rfl) ⟨1216226, by rfl⟩ : syracuseStep 1621635 = 2432453) B2432453
theorem B2735761 : Blo 1621009 2735761 := bstep (se 2 (by rfl) ⟨1025910, by rfl⟩ : syracuseStep 2735761 = 2051821) B2051821
theorem B2432657 : Blo 1621009 2432657 := bstep (se 2 (by rfl) ⟨912246, by rfl⟩ : syracuseStep 2432657 = 1824493) B1824493
theorem B1621651 : Blo 1621009 1621651 := bstep (se 1 (by rfl) ⟨1216238, by rfl⟩ : syracuseStep 1621651 = 2432477) B2432477
theorem B1621667 : Blo 1621009 1621667 := bstep (se 1 (by rfl) ⟨1216250, by rfl⟩ : syracuseStep 1621667 = 2432501) B2432501
theorem B2432675 : Blo 1621009 2432675 := bstep (se 1 (by rfl) ⟨1824506, by rfl⟩ : syracuseStep 2432675 = 3649013) B3649013
theorem B2735795 : Blo 1621009 2735795 := bstep (se 1 (by rfl) ⟨2051846, by rfl⟩ : syracuseStep 2735795 = 4103693) B4103693
theorem B1621683 : Blo 1621009 1621683 := bstep (se 1 (by rfl) ⟨1216262, by rfl⟩ : syracuseStep 1621683 = 2432525) B2432525
theorem B2432705 : Blo 1621009 2432705 := bstep (se 2 (by rfl) ⟨912264, by rfl⟩ : syracuseStep 2432705 = 1824529) B1824529
theorem B1621699 : Blo 1621009 1621699 := bstep (se 1 (by rfl) ⟨1216274, by rfl⟩ : syracuseStep 1621699 = 2432549) B2432549
theorem B1621715 : Blo 1621009 1621715 := bstep (se 1 (by rfl) ⟨1216286, by rfl⟩ : syracuseStep 1621715 = 2432573) B2432573
theorem B2432723 : Blo 1621009 2432723 := bstep (se 1 (by rfl) ⟨1824542, by rfl⟩ : syracuseStep 2432723 = 3649085) B3649085
theorem B1621731 : Blo 1621009 1621731 := bstep (se 1 (by rfl) ⟨1216298, by rfl⟩ : syracuseStep 1621731 = 2432597) B2432597
theorem B5471981 : Blo 1621009 5471981 := bstep (se 3 (by rfl) ⟨1025996, by rfl⟩ : syracuseStep 5471981 = 2051993) B2051993
theorem B2432753 : Blo 1621009 2432753 := bstep (se 2 (by rfl) ⟨912282, by rfl⟩ : syracuseStep 2432753 = 1824565) B1824565
theorem B1621747 : Blo 1621009 1621747 := bstep (se 1 (by rfl) ⟨1216310, by rfl⟩ : syracuseStep 1621747 = 2432621) B2432621
theorem B1621763 : Blo 1621009 1621763 := bstep (se 1 (by rfl) ⟨1216322, by rfl⟩ : syracuseStep 1621763 = 2432645) B2432645
theorem B8765189 : Blo 1621009 8765189 := bstep (se 4 (by rfl) ⟨821736, by rfl⟩ : syracuseStep 8765189 = 1643473) B1643473
theorem B2432771 : Blo 1621009 2432771 := bstep (se 1 (by rfl) ⟨1824578, by rfl⟩ : syracuseStep 2432771 = 3649157) B3649157
theorem B2309905 : Blo 1621009 2309905 := bstep (se 2 (by rfl) ⟨866214, by rfl⟩ : syracuseStep 2309905 = 1732429) B1732429
theorem B1621779 : Blo 1621009 1621779 := bstep (se 1 (by rfl) ⟨1216334, by rfl⟩ : syracuseStep 1621779 = 2432669) B2432669
theorem B2432801 : Blo 1621009 2432801 := bstep (se 2 (by rfl) ⟨912300, by rfl⟩ : syracuseStep 2432801 = 1824601) B1824601
theorem B5472035 : Blo 1621009 5472035 := bstep (se 1 (by rfl) ⟨4104026, by rfl⟩ : syracuseStep 5472035 = 8208053) B8208053
theorem B1621795 : Blo 1621009 1621795 := bstep (se 1 (by rfl) ⟨1216346, by rfl⟩ : syracuseStep 1621795 = 2432693) B2432693
theorem B2735923 : Blo 1621009 2735923 := bstep (se 1 (by rfl) ⟨2051942, by rfl⟩ : syracuseStep 2735923 = 4103885) B4103885
theorem B1621811 : Blo 1621009 1621811 := bstep (se 1 (by rfl) ⟨1216358, by rfl⟩ : syracuseStep 1621811 = 2432717) B2432717
theorem B2432819 : Blo 1621009 2432819 := bstep (se 1 (by rfl) ⟨1824614, by rfl⟩ : syracuseStep 2432819 = 3649229) B3649229
theorem B1621827 : Blo 1621009 1621827 := bstep (se 1 (by rfl) ⟨1216370, by rfl⟩ : syracuseStep 1621827 = 2432741) B2432741
theorem B4104017 : Blo 1621009 4104017 := bstep (se 2 (by rfl) ⟨1539006, by rfl⟩ : syracuseStep 4104017 = 3078013) B3078013
theorem B2432849 : Blo 1621009 2432849 := bstep (se 2 (by rfl) ⟨912318, by rfl⟩ : syracuseStep 2432849 = 1824637) B1824637
theorem B1621843 : Blo 1621009 1621843 := bstep (se 1 (by rfl) ⟨1216382, by rfl⟩ : syracuseStep 1621843 = 2432765) B2432765
theorem B5193571 : Blo 1621009 5193571 := bstep (se 1 (by rfl) ⟨3895178, by rfl⟩ : syracuseStep 5193571 = 7790357) B7790357
theorem B1621859 : Blo 1621009 1621859 := bstep (se 1 (by rfl) ⟨1216394, by rfl⟩ : syracuseStep 1621859 = 2432789) B2432789
theorem B2432867 : Blo 1621009 2432867 := bstep (se 1 (by rfl) ⟨1824650, by rfl⟩ : syracuseStep 2432867 = 3649301) B3649301
theorem B1621875 : Blo 1621009 1621875 := bstep (se 1 (by rfl) ⟨1216406, by rfl⟩ : syracuseStep 1621875 = 2432813) B2432813
theorem B2432897 : Blo 1621009 2432897 := bstep (se 2 (by rfl) ⟨912336, by rfl⟩ : syracuseStep 2432897 = 1824673) B1824673
theorem B4104067 : Blo 1621009 4104067 := bstep (se 1 (by rfl) ⟨3078050, by rfl⟩ : syracuseStep 4104067 = 6156101) B6156101
theorem B1621891 : Blo 1621009 1621891 := bstep (se 1 (by rfl) ⟨1216418, by rfl⟩ : syracuseStep 1621891 = 2432837) B2432837
theorem B1621907 : Blo 1621009 1621907 := bstep (se 1 (by rfl) ⟨1216430, by rfl⟩ : syracuseStep 1621907 = 2432861) B2432861
theorem B2432915 : Blo 1621009 2432915 := bstep (se 1 (by rfl) ⟨1824686, by rfl⟩ : syracuseStep 2432915 = 3649373) B3649373
theorem B1621923 : Blo 1621009 1621923 := bstep (se 1 (by rfl) ⟨1216442, by rfl⟩ : syracuseStep 1621923 = 2432885) B2432885
theorem B2432945 : Blo 1621009 2432945 := bstep (se 2 (by rfl) ⟨912354, by rfl⟩ : syracuseStep 2432945 = 1824709) B1824709
theorem B1621939 : Blo 1621009 1621939 := bstep (se 1 (by rfl) ⟨1216454, by rfl⟩ : syracuseStep 1621939 = 2432909) B2432909
theorem B2736065 : Blo 1621009 2736065 := bstep (se 2 (by rfl) ⟨1026024, by rfl⟩ : syracuseStep 2736065 = 2052049) B2052049
theorem B1621955 : Blo 1621009 1621955 := bstep (se 1 (by rfl) ⟨1216466, by rfl⟩ : syracuseStep 1621955 = 2432933) B2432933
theorem B2432963 : Blo 1621009 2432963 := bstep (se 1 (by rfl) ⟨1824722, by rfl⟩ : syracuseStep 2432963 = 3649445) B3649445
theorem B1621971 : Blo 1621009 1621971 := bstep (se 1 (by rfl) ⟨1216478, by rfl⟩ : syracuseStep 1621971 = 2432957) B2432957
theorem B2432993 : Blo 1621009 2432993 := bstep (se 2 (by rfl) ⟨912372, by rfl⟩ : syracuseStep 2432993 = 1824745) B1824745
theorem B1621987 : Blo 1621009 1621987 := bstep (se 1 (by rfl) ⟨1216490, by rfl⟩ : syracuseStep 1621987 = 2432981) B2432981
theorem B3080177 : Blo 1621009 3080177 := bstep (se 2 (by rfl) ⟨1155066, by rfl⟩ : syracuseStep 3080177 = 2310133) B2310133
theorem B1622003 : Blo 1621009 1622003 := bstep (se 1 (by rfl) ⟨1216502, by rfl⟩ : syracuseStep 1622003 = 2433005) B2433005
theorem B2433011 : Blo 1621009 2433011 := bstep (se 1 (by rfl) ⟨1824758, by rfl⟩ : syracuseStep 2433011 = 3649517) B3649517
theorem B2736139 : Blo 1621009 2736139 := bstep (se 1 (by rfl) ⟨2052104, by rfl⟩ : syracuseStep 2736139 = 4104209) B4104209
theorem B2433035 : Blo 1621009 2433035 := bstep (se 1 (by rfl) ⟨1824776, by rfl⟩ : syracuseStep 2433035 = 3649553) B3649553
theorem B1622027 : Blo 1621009 1622027 := bstep (se 1 (by rfl) ⟨1216520, by rfl⟩ : syracuseStep 1622027 = 2433041) B2433041
theorem B2433047 : Blo 1621009 2433047 := bstep (se 1 (by rfl) ⟨1824785, by rfl⟩ : syracuseStep 2433047 = 3649571) B3649571
theorem B1622039 : Blo 1621009 1622039 := bstep (se 1 (by rfl) ⟨1216529, by rfl⟩ : syracuseStep 1622039 = 2433059) B2433059
theorem B4620311 : Blo 1621009 4620311 := bstep (se 1 (by rfl) ⟨3465233, by rfl⟩ : syracuseStep 4620311 = 6930467) B6930467
theorem B2310167 : Blo 1621009 2310167 := bstep (se 1 (by rfl) ⟨1732625, by rfl⟩ : syracuseStep 2310167 = 3465251) B3465251
theorem B1622059 : Blo 1621009 1622059 := bstep (se 1 (by rfl) ⟨1216544, by rfl⟩ : syracuseStep 1622059 = 2433089) B2433089
theorem B1622071 : Blo 1621009 1622071 := bstep (se 1 (by rfl) ⟨1216553, by rfl⟩ : syracuseStep 1622071 = 2433107) B2433107
theorem B1622091 : Blo 1621009 1622091 := bstep (se 1 (by rfl) ⟨1216568, by rfl⟩ : syracuseStep 1622091 = 2433137) B2433137
theorem B1622103 : Blo 1621009 1622103 := bstep (se 1 (by rfl) ⟨1216577, by rfl⟩ : syracuseStep 1622103 = 2433155) B2433155
theorem B2433113 : Blo 1621009 2433113 := bstep (se 2 (by rfl) ⟨912417, by rfl⟩ : syracuseStep 2433113 = 1824835) B1824835
theorem B1622123 : Blo 1621009 1622123 := bstep (se 1 (by rfl) ⟨1216592, by rfl⟩ : syracuseStep 1622123 = 2433185) B2433185
theorem B1622135 : Blo 1621009 1622135 := bstep (se 1 (by rfl) ⟨1216601, by rfl⟩ : syracuseStep 1622135 = 2433203) B2433203
theorem B1622155 : Blo 1621009 1622155 := bstep (se 1 (by rfl) ⟨1216616, by rfl⟩ : syracuseStep 1622155 = 2433233) B2433233
theorem B1622167 : Blo 1621009 1622167 := bstep (se 1 (by rfl) ⟨1216625, by rfl⟩ : syracuseStep 1622167 = 2433251) B2433251
theorem B2736281 : Blo 1621009 2736281 := bstep (se 2 (by rfl) ⟨1026105, by rfl⟩ : syracuseStep 2736281 = 2052211) B2052211
theorem B1622187 : Blo 1621009 1622187 := bstep (se 1 (by rfl) ⟨1216640, by rfl⟩ : syracuseStep 1622187 = 2433281) B2433281
theorem B4104371 : Blo 1621009 4104371 := bstep (se 1 (by rfl) ⟨3078278, by rfl⟩ : syracuseStep 4104371 = 6156557) B6156557
theorem B1622199 : Blo 1621009 1622199 := bstep (se 1 (by rfl) ⟨1216649, by rfl⟩ : syracuseStep 1622199 = 2433299) B2433299
theorem B4161739 : Blo 1621009 4161739 := bstep (se 1 (by rfl) ⟨3121304, by rfl⟩ : syracuseStep 4161739 = 6242609) B6242609
theorem B2433227 : Blo 1621009 2433227 := bstep (se 1 (by rfl) ⟨1824920, by rfl⟩ : syracuseStep 2433227 = 3649841) B3649841
theorem B1622219 : Blo 1621009 1622219 := bstep (se 1 (by rfl) ⟨1216664, by rfl⟩ : syracuseStep 1622219 = 2433329) B2433329
theorem B2433239 : Blo 1621009 2433239 := bstep (se 1 (by rfl) ⟨1824929, by rfl⟩ : syracuseStep 2433239 = 3649859) B3649859
theorem B1622231 : Blo 1621009 1622231 := bstep (se 1 (by rfl) ⟨1216673, by rfl⟩ : syracuseStep 1622231 = 2433347) B2433347
theorem B1622251 : Blo 1621009 1622251 := bstep (se 1 (by rfl) ⟨1216688, by rfl⟩ : syracuseStep 1622251 = 2433377) B2433377
theorem B1622263 : Blo 1621009 1622263 := bstep (se 1 (by rfl) ⟨1216697, by rfl⟩ : syracuseStep 1622263 = 2433395) B2433395
theorem B6160643 : Blo 1621009 6160643 := bstep (se 1 (by rfl) ⟨4620482, by rfl⟩ : syracuseStep 6160643 = 9240965) B9240965
theorem B2597131 : Blo 1621009 2597131 := bstep (se 1 (by rfl) ⟨1947848, by rfl⟩ : syracuseStep 2597131 = 3895697) B3895697
theorem B1622283 : Blo 1621009 1622283 := bstep (se 1 (by rfl) ⟨1216712, by rfl⟩ : syracuseStep 1622283 = 2433425) B2433425
theorem B6160657 : Blo 1621009 6160657 := bstep (se 2 (by rfl) ⟨2310246, by rfl⟩ : syracuseStep 6160657 = 4620493) B4620493
theorem B5194007 : Blo 1621009 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B1622295 : Blo 1621009 1622295 := bstep (se 1 (by rfl) ⟨1216721, by rfl⟩ : syracuseStep 1622295 = 2433443) B2433443
theorem B2736409 : Blo 1621009 2736409 := bstep (se 2 (by rfl) ⟨1026153, by rfl⟩ : syracuseStep 2736409 = 2052307) B2052307
theorem B2433305 : Blo 1621009 2433305 := bstep (se 2 (by rfl) ⟨912489, by rfl⟩ : syracuseStep 2433305 = 1824979) B1824979
theorem B1622315 : Blo 1621009 1622315 := bstep (se 1 (by rfl) ⟨1216736, by rfl⟩ : syracuseStep 1622315 = 2433473) B2433473
theorem B1622327 : Blo 1621009 1622327 := bstep (se 1 (by rfl) ⟨1216745, by rfl⟩ : syracuseStep 1622327 = 2433491) B2433491
theorem B1622347 : Blo 1621009 1622347 := bstep (se 1 (by rfl) ⟨1216760, by rfl⟩ : syracuseStep 1622347 = 2433521) B2433521
theorem B1622359 : Blo 1621009 1622359 := bstep (se 1 (by rfl) ⟨1216769, by rfl⟩ : syracuseStep 1622359 = 2433539) B2433539
theorem B1622379 : Blo 1621009 1622379 := bstep (se 1 (by rfl) ⟨1216784, by rfl⟩ : syracuseStep 1622379 = 2433569) B2433569
theorem B1622391 : Blo 1621009 1622391 := bstep (se 1 (by rfl) ⟨1216793, by rfl⟩ : syracuseStep 1622391 = 2433587) B2433587
theorem B2433419 : Blo 1621009 2433419 := bstep (se 1 (by rfl) ⟨1825064, by rfl⟩ : syracuseStep 2433419 = 3650129) B3650129
theorem B1622411 : Blo 1621009 1622411 := bstep (se 1 (by rfl) ⟨1216808, by rfl⟩ : syracuseStep 1622411 = 2433617) B2433617
theorem B3080587 : Blo 1621009 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B2433431 : Blo 1621009 2433431 := bstep (se 1 (by rfl) ⟨1825073, by rfl⟩ : syracuseStep 2433431 = 3650147) B3650147
theorem B1622423 : Blo 1621009 1622423 := bstep (se 1 (by rfl) ⟨1216817, by rfl⟩ : syracuseStep 1622423 = 2433635) B2433635
theorem B1622443 : Blo 1621009 1622443 := bstep (se 1 (by rfl) ⟨1216832, by rfl⟩ : syracuseStep 1622443 = 2433665) B2433665
theorem B1622455 : Blo 1621009 1622455 := bstep (se 1 (by rfl) ⟨1216841, by rfl⟩ : syracuseStep 1622455 = 2433683) B2433683
theorem B1622475 : Blo 1621009 1622475 := bstep (se 1 (by rfl) ⟨1216856, by rfl⟩ : syracuseStep 1622475 = 2433713) B2433713
theorem B3334603 : Blo 1621009 3334603 := bstep (se 1 (by rfl) ⟨2500952, by rfl⟩ : syracuseStep 3334603 = 5001905) B5001905
theorem B3424727 : Blo 1621009 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B2466263 : Blo 1621009 2466263 := bstep (se 1 (by rfl) ⟨1849697, by rfl⟩ : syracuseStep 2466263 = 3699395) B3699395
theorem B4104665 : Blo 1621009 4104665 := bstep (se 2 (by rfl) ⟨1539249, by rfl⟩ : syracuseStep 4104665 = 3078499) B3078499
theorem B2433497 : Blo 1621009 2433497 := bstep (se 2 (by rfl) ⟨912561, by rfl⟩ : syracuseStep 2433497 = 1825123) B1825123
theorem B1622487 : Blo 1621009 1622487 := bstep (se 1 (by rfl) ⟨1216865, by rfl⟩ : syracuseStep 1622487 = 2433731) B2433731
theorem B3080663 : Blo 1621009 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B1622507 : Blo 1621009 1622507 := bstep (se 1 (by rfl) ⟨1216880, by rfl⟩ : syracuseStep 1622507 = 2433761) B2433761
theorem B1622519 : Blo 1621009 1622519 := bstep (se 1 (by rfl) ⟨1216889, by rfl⟩ : syracuseStep 1622519 = 2433779) B2433779
theorem B1622539 : Blo 1621009 1622539 := bstep (se 1 (by rfl) ⟨1216904, by rfl⟩ : syracuseStep 1622539 = 2433809) B2433809
theorem B5472791 : Blo 1621009 5472791 := bstep (se 1 (by rfl) ⟨4104593, by rfl⟩ : syracuseStep 5472791 = 8209187) B8209187
theorem B1622551 : Blo 1621009 1622551 := bstep (se 1 (by rfl) ⟨1216913, by rfl⟩ : syracuseStep 1622551 = 2433827) B2433827
theorem B1622571 : Blo 1621009 1622571 := bstep (se 1 (by rfl) ⟨1216928, by rfl⟩ : syracuseStep 1622571 = 2433857) B2433857
theorem B1622583 : Blo 1621009 1622583 := bstep (se 1 (by rfl) ⟨1216937, by rfl⟩ : syracuseStep 1622583 = 2433875) B2433875
theorem B6160961 : Blo 1621009 6160961 := bstep (se 2 (by rfl) ⟨2310360, by rfl⟩ : syracuseStep 6160961 = 4620721) B4620721
theorem B2433611 : Blo 1621009 2433611 := bstep (se 1 (by rfl) ⟨1825208, by rfl⟩ : syracuseStep 2433611 = 3650417) B3650417
theorem B1622603 : Blo 1621009 1622603 := bstep (se 1 (by rfl) ⟨1216952, by rfl⟩ : syracuseStep 1622603 = 2433905) B2433905
theorem B2433623 : Blo 1621009 2433623 := bstep (se 1 (by rfl) ⟨1825217, by rfl⟩ : syracuseStep 2433623 = 3650435) B3650435
theorem B1622615 : Blo 1621009 1622615 := bstep (se 1 (by rfl) ⟨1216961, by rfl⟩ : syracuseStep 1622615 = 2433923) B2433923
theorem B1622635 : Blo 1621009 1622635 := bstep (se 1 (by rfl) ⟨1216976, by rfl⟩ : syracuseStep 1622635 = 2433953) B2433953
theorem B1622647 : Blo 1621009 1622647 := bstep (se 1 (by rfl) ⟨1216985, by rfl⟩ : syracuseStep 1622647 = 2433971) B2433971
theorem B1622667 : Blo 1621009 1622667 := bstep (se 1 (by rfl) ⟨1217000, by rfl⟩ : syracuseStep 1622667 = 2434001) B2434001
theorem B1622679 : Blo 1621009 1622679 := bstep (se 1 (by rfl) ⟨1217009, by rfl⟩ : syracuseStep 1622679 = 2434019) B2434019
theorem B2433689 : Blo 1621009 2433689 := bstep (se 2 (by rfl) ⟨912633, by rfl⟩ : syracuseStep 2433689 = 1825267) B1825267
theorem B1622699 : Blo 1621009 1622699 := bstep (se 1 (by rfl) ⟨1217024, by rfl⟩ : syracuseStep 1622699 = 2434049) B2434049
theorem B1622711 : Blo 1621009 1622711 := bstep (se 1 (by rfl) ⟨1217033, by rfl⟩ : syracuseStep 1622711 = 2434067) B2434067
theorem B1622731 : Blo 1621009 1622731 := bstep (se 1 (by rfl) ⟨1217048, by rfl⟩ : syracuseStep 1622731 = 2434097) B2434097
theorem B1622743 : Blo 1621009 1622743 := bstep (se 1 (by rfl) ⟨1217057, by rfl⟩ : syracuseStep 1622743 = 2434115) B2434115
theorem B1622763 : Blo 1621009 1622763 := bstep (se 1 (by rfl) ⟨1217072, by rfl⟩ : syracuseStep 1622763 = 2434145) B2434145
theorem B1622775 : Blo 1621009 1622775 := bstep (se 1 (by rfl) ⟨1217081, by rfl⟩ : syracuseStep 1622775 = 2434163) B2434163
theorem B3465985 : Blo 1621009 3465985 := bstep (se 2 (by rfl) ⟨1299744, by rfl⟩ : syracuseStep 3465985 = 2599489) B2599489
theorem B2433803 : Blo 1621009 2433803 := bstep (se 1 (by rfl) ⟨1825352, by rfl⟩ : syracuseStep 2433803 = 3650705) B3650705
theorem B1622795 : Blo 1621009 1622795 := bstep (se 1 (by rfl) ⟨1217096, by rfl⟩ : syracuseStep 1622795 = 2434193) B2434193
theorem B2433815 : Blo 1621009 2433815 := bstep (se 1 (by rfl) ⟨1825361, by rfl⟩ : syracuseStep 2433815 = 3650723) B3650723
theorem B1622807 : Blo 1621009 1622807 := bstep (se 1 (by rfl) ⟨1217105, by rfl⟩ : syracuseStep 1622807 = 2434211) B2434211
theorem B1622827 : Blo 1621009 1622827 := bstep (se 1 (by rfl) ⟨1217120, by rfl⟩ : syracuseStep 1622827 = 2434241) B2434241
theorem B1622839 : Blo 1621009 1622839 := bstep (se 1 (by rfl) ⟨1217129, by rfl⟩ : syracuseStep 1622839 = 2434259) B2434259
theorem B4621121 : Blo 1621009 4621121 := bstep (se 2 (by rfl) ⟨1732920, by rfl⟩ : syracuseStep 4621121 = 3465841) B3465841
theorem B1622859 : Blo 1621009 1622859 := bstep (se 1 (by rfl) ⟨1217144, by rfl⟩ : syracuseStep 1622859 = 2434289) B2434289
theorem B2736983 : Blo 1621009 2736983 := bstep (se 1 (by rfl) ⟨2052737, by rfl⟩ : syracuseStep 2736983 = 4105475) B4105475
theorem B1622871 : Blo 1621009 1622871 := bstep (se 1 (by rfl) ⟨1217153, by rfl⟩ : syracuseStep 1622871 = 2434307) B2434307
theorem B2433881 : Blo 1621009 2433881 := bstep (se 2 (by rfl) ⟨912705, by rfl⟩ : syracuseStep 2433881 = 1825411) B1825411
theorem B1622891 : Blo 1621009 1622891 := bstep (se 1 (by rfl) ⟨1217168, by rfl⟩ : syracuseStep 1622891 = 2434337) B2434337
theorem B1622903 : Blo 1621009 1622903 := bstep (se 1 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 1622903 = 2434355) B2434355
theorem B1622923 : Blo 1621009 1622923 := bstep (se 1 (by rfl) ⟨1217192, by rfl⟩ : syracuseStep 1622923 = 2434385) B2434385
theorem B1622935 : Blo 1621009 1622935 := bstep (se 1 (by rfl) ⟨1217201, by rfl⟩ : syracuseStep 1622935 = 2434403) B2434403
theorem B1622955 : Blo 1621009 1622955 := bstep (se 1 (by rfl) ⟨1217216, by rfl⟩ : syracuseStep 1622955 = 2434433) B2434433
theorem B1622967 : Blo 1621009 1622967 := bstep (se 1 (by rfl) ⟨1217225, by rfl⟩ : syracuseStep 1622967 = 2434451) B2434451
theorem B2433995 : Blo 1621009 2433995 := bstep (se 1 (by rfl) ⟨1825496, by rfl⟩ : syracuseStep 2433995 = 3650993) B3650993
theorem B1622987 : Blo 1621009 1622987 := bstep (se 1 (by rfl) ⟨1217240, by rfl⟩ : syracuseStep 1622987 = 2434481) B2434481
theorem B2737111 : Blo 1621009 2737111 := bstep (se 1 (by rfl) ⟨2052833, by rfl⟩ : syracuseStep 2737111 = 4105667) B4105667
theorem B2434007 : Blo 1621009 2434007 := bstep (se 1 (by rfl) ⟨1825505, by rfl⟩ : syracuseStep 2434007 = 3651011) B3651011
theorem B2597849 : Blo 1621009 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B1622999 : Blo 1621009 1622999 := bstep (se 1 (by rfl) ⟨1217249, by rfl⟩ : syracuseStep 1622999 = 2434499) B2434499
theorem B5194775 : Blo 1621009 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B2434073 : Blo 1621009 2434073 := bstep (se 2 (by rfl) ⟨912777, by rfl⟩ : syracuseStep 2434073 = 1825555) B1825555
theorem B5473331 : Blo 1621009 5473331 := bstep (se 1 (by rfl) ⟨4104998, by rfl⟩ : syracuseStep 5473331 = 8209997) B8209997
theorem B3122263 : Blo 1621009 3122263 := bstep (se 1 (by rfl) ⟨2341697, by rfl⟩ : syracuseStep 3122263 = 4683395) B4683395
theorem B3466327 : Blo 1621009 3466327 := bstep (se 1 (by rfl) ⟨2599745, by rfl⟩ : syracuseStep 3466327 = 5199491) B5199491
theorem B2434187 : Blo 1621009 2434187 := bstep (se 1 (by rfl) ⟨1825640, by rfl⟩ : syracuseStep 2434187 = 3651281) B3651281
theorem B14795927 : Blo 1621009 14795927 := bstep (se 1 (by rfl) ⟨11096945, by rfl⟩ : syracuseStep 14795927 = 22193891) B22193891
theorem B2434199 : Blo 1621009 2434199 := bstep (se 1 (by rfl) ⟨1825649, by rfl⟩ : syracuseStep 2434199 = 3651299) B3651299
theorem B2434265 : Blo 1621009 2434265 := bstep (se 2 (by rfl) ⟨912849, by rfl⟩ : syracuseStep 2434265 = 1825699) B1825699
theorem B6161629 : Blo 1621009 6161629 := bstep (se 3 (by rfl) ⟨1155305, by rfl⟩ : syracuseStep 6161629 = 2310611) B2310611
theorem B5473601 : Blo 1621009 5473601 := bstep (se 2 (by rfl) ⟨2052600, by rfl⟩ : syracuseStep 5473601 = 4105201) B4105201
theorem B2434379 : Blo 1621009 2434379 := bstep (se 1 (by rfl) ⟨1825784, by rfl⟩ : syracuseStep 2434379 = 3651569) B3651569
theorem B2434391 : Blo 1621009 2434391 := bstep (se 1 (by rfl) ⟨1825793, by rfl⟩ : syracuseStep 2434391 = 3651587) B3651587
theorem B2434457 : Blo 1621009 2434457 := bstep (se 2 (by rfl) ⟨912921, by rfl⟩ : syracuseStep 2434457 = 1825843) B1825843
theorem B1622007 : Blo 1621009 1622007 := bstep (se 1 (by rfl) ⟨1216505, by rfl⟩ : syracuseStep 1622007 = 2433011) B2433011
theorem B2598361 : Blo 1621009 2598361 := bstep (se 2 (by rfl) ⟨974385, by rfl⟩ : syracuseStep 2598361 = 1948771) B1948771
theorem B7792145 : Blo 1621009 7792145 := bstep (se 2 (by rfl) ⟨2922054, by rfl⟩ : syracuseStep 7792145 = 5844109) B5844109
theorem B5195287 : Blo 1621009 5195287 := bstep (se 1 (by rfl) ⟨3896465, by rfl⟩ : syracuseStep 5195287 = 7792931) B7792931
theorem B2467351 : Blo 1621009 2467351 := bstep (se 1 (by rfl) ⟨1850513, by rfl⟩ : syracuseStep 2467351 = 3701027) B3701027
theorem B2737739 : Blo 1621009 2737739 := bstep (se 1 (by rfl) ⟨2053304, by rfl⟩ : syracuseStep 2737739 = 4106609) B4106609
theorem B2737867 : Blo 1621009 2737867 := bstep (se 1 (by rfl) ⟨2053400, by rfl⟩ : syracuseStep 2737867 = 4106801) B4106801
theorem B12478157 : Blo 1621009 12478157 := bstep (se 3 (by rfl) ⟨2339654, by rfl⟩ : syracuseStep 12478157 = 4679309) B4679309
theorem B1976023 : Blo 1621009 1976023 := bstep (se 1 (by rfl) ⟨1482017, by rfl⟩ : syracuseStep 1976023 = 2964035) B2964035
theorem B13854509 : Blo 1621009 13854509 := bstep (se 3 (by rfl) ⟨2597720, by rfl⟩ : syracuseStep 13854509 = 5195441) B5195441
theorem B3647321 : Blo 1621009 3647321 := bstep (se 2 (by rfl) ⟨1367745, by rfl⟩ : syracuseStep 3647321 = 2735491) B2735491
theorem B2738009 : Blo 1621009 2738009 := bstep (se 2 (by rfl) ⟨1026753, by rfl⟩ : syracuseStep 2738009 = 2053507) B2053507
theorem B5474141 : Blo 1621009 5474141 := bstep (se 3 (by rfl) ⟨1026401, by rfl⟩ : syracuseStep 5474141 = 2052803) B2052803
theorem B6924163 : Blo 1621009 6924163 := bstep (se 1 (by rfl) ⟨5193122, by rfl⟩ : syracuseStep 6924163 = 10386245) B10386245
theorem B3647411 : Blo 1621009 3647411 := bstep (se 1 (by rfl) ⟨2735558, by rfl⟩ : syracuseStep 3647411 = 5471117) B5471117
theorem B3647447 : Blo 1621009 3647447 := bstep (se 1 (by rfl) ⟨2735585, by rfl⟩ : syracuseStep 3647447 = 5471171) B5471171
theorem B18728921 : Blo 1621009 18728921 := bstep (se 2 (by rfl) ⟨7023345, by rfl⟩ : syracuseStep 18728921 = 14046691) B14046691
theorem B2738137 : Blo 1621009 2738137 := bstep (se 2 (by rfl) ⟨1026801, by rfl⟩ : syracuseStep 2738137 = 2053603) B2053603
theorem B85403717 : Blo 1621009 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B4106315 : Blo 1621009 4106315 := bstep (se 1 (by rfl) ⟨3079736, by rfl⟩ : syracuseStep 4106315 = 6159473) B6159473
theorem B3647627 : Blo 1621009 3647627 := bstep (se 1 (by rfl) ⟨2735720, by rfl⟩ : syracuseStep 3647627 = 5471441) B5471441
theorem B4679831 : Blo 1621009 4679831 := bstep (se 1 (by rfl) ⟨3509873, by rfl⟩ : syracuseStep 4679831 = 7019747) B7019747
theorem B3647681 : Blo 1621009 3647681 := bstep (se 2 (by rfl) ⟨1367880, by rfl⟩ : syracuseStep 3647681 = 2735761) B2735761
theorem B5196107 : Blo 1621009 5196107 := bstep (se 1 (by rfl) ⟨3897080, by rfl⟩ : syracuseStep 5196107 = 7794161) B7794161
theorem B14051677 : Blo 1621009 14051677 := bstep (se 3 (by rfl) ⟨2634689, by rfl⟩ : syracuseStep 14051677 = 5269379) B5269379
theorem B3647897 : Blo 1621009 3647897 := bstep (se 2 (by rfl) ⟨1367961, by rfl⟩ : syracuseStep 3647897 = 2735923) B2735923
theorem B6924761 : Blo 1621009 6924761 := bstep (se 2 (by rfl) ⟨2596785, by rfl⟩ : syracuseStep 6924761 = 5193571) B5193571
theorem B3647987 : Blo 1621009 3647987 := bstep (se 1 (by rfl) ⟨2735990, by rfl⟩ : syracuseStep 3647987 = 5471981) B5471981
theorem B5843459 : Blo 1621009 5843459 := bstep (se 1 (by rfl) ⟨4382594, by rfl⟩ : syracuseStep 5843459 = 8765189) B8765189
theorem B3648023 : Blo 1621009 3648023 := bstep (se 1 (by rfl) ⟨2736017, by rfl⟩ : syracuseStep 3648023 = 5472035) B5472035
theorem B2738711 : Blo 1621009 2738711 := bstep (se 1 (by rfl) ⟨2054033, by rfl⟩ : syracuseStep 2738711 = 4108067) B4108067
theorem B5196467 : Blo 1621009 5196467 := bstep (se 1 (by rfl) ⟨3897350, by rfl⟩ : syracuseStep 5196467 = 7794701) B7794701
theorem B3648203 : Blo 1621009 3648203 := bstep (se 1 (by rfl) ⟨2736152, by rfl⟩ : syracuseStep 3648203 = 5472305) B5472305
theorem B3648257 : Blo 1621009 3648257 := bstep (se 2 (by rfl) ⟨1368096, by rfl⟩ : syracuseStep 3648257 = 2736193) B2736193
theorem B7498547 : Blo 1621009 7498547 := bstep (se 1 (by rfl) ⟨5623910, by rfl⟩ : syracuseStep 7498547 = 11247821) B11247821
theorem B6925121 : Blo 1621009 6925121 := bstep (se 2 (by rfl) ⟨2596920, by rfl⟩ : syracuseStep 6925121 = 5193841) B5193841
theorem B18729793 : Blo 1621009 18729793 := bstep (se 2 (by rfl) ⟨7023672, by rfl⟩ : syracuseStep 18729793 = 14047345) B14047345
theorem B8211293 : Blo 1621009 8211293 := bstep (se 3 (by rfl) ⟨1539617, by rfl⟩ : syracuseStep 8211293 = 3079235) B3079235
theorem B6572951 : Blo 1621009 6572951 := bstep (se 1 (by rfl) ⟨4929713, by rfl⟩ : syracuseStep 6572951 = 9859427) B9859427
theorem B5475275 : Blo 1621009 5475275 := bstep (se 1 (by rfl) ⟨4106456, by rfl⟩ : syracuseStep 5475275 = 8212913) B8212913
theorem B3648473 : Blo 1621009 3648473 := bstep (se 2 (by rfl) ⟨1368177, by rfl⟩ : syracuseStep 3648473 = 2736355) B2736355
theorem B4107287 : Blo 1621009 4107287 := bstep (se 1 (by rfl) ⟨3080465, by rfl⟩ : syracuseStep 4107287 = 6160931) B6160931
theorem B3648563 : Blo 1621009 3648563 := bstep (se 1 (by rfl) ⟨2736422, by rfl⟩ : syracuseStep 3648563 = 5472845) B5472845
theorem B3648599 : Blo 1621009 3648599 := bstep (se 1 (by rfl) ⟨2736449, by rfl⟩ : syracuseStep 3648599 = 5472899) B5472899
theorem B10390679 : Blo 1621009 10390679 := bstep (se 1 (by rfl) ⟨7793009, by rfl⟩ : syracuseStep 10390679 = 15586019) B15586019
theorem B5475545 : Blo 1621009 5475545 := bstep (se 2 (by rfl) ⟨2053329, by rfl⟩ : syracuseStep 5475545 = 4106659) B4106659
theorem B3648779 : Blo 1621009 3648779 := bstep (se 1 (by rfl) ⟨2736584, by rfl⟩ : syracuseStep 3648779 = 5473169) B5473169
theorem B7023917 : Blo 1621009 7023917 := bstep (se 3 (by rfl) ⟨1316984, by rfl⟩ : syracuseStep 7023917 = 2633969) B2633969
theorem B6155585 : Blo 1621009 6155585 := bstep (se 2 (by rfl) ⟨2308344, by rfl⟩ : syracuseStep 6155585 = 4616689) B4616689
theorem B3648833 : Blo 1621009 3648833 := bstep (se 2 (by rfl) ⟨1368312, by rfl⟩ : syracuseStep 3648833 = 2736625) B2736625
theorem B1732087 : Blo 1621009 1732087 := bstep (se 1 (by rfl) ⟨1299065, by rfl⟩ : syracuseStep 1732087 = 2598131) B2598131
theorem B8891921 : Blo 1621009 8891921 := bstep (se 2 (by rfl) ⟨3334470, by rfl⟩ : syracuseStep 8891921 = 6668941) B6668941
theorem B3649049 : Blo 1621009 3649049 := bstep (se 2 (by rfl) ⟨1368393, by rfl⟩ : syracuseStep 3649049 = 2736787) B2736787
theorem B2051659 : Blo 1621009 2051659 := bstep (se 1 (by rfl) ⟨1538744, by rfl⟩ : syracuseStep 2051659 = 3077489) B3077489
theorem B12660299 : Blo 1621009 12660299 := bstep (se 1 (by rfl) ⟨9495224, by rfl⟩ : syracuseStep 12660299 = 18990449) B18990449
theorem B3649139 : Blo 1621009 3649139 := bstep (se 1 (by rfl) ⟨2736854, by rfl⟩ : syracuseStep 3649139 = 5473709) B5473709
theorem B3649175 : Blo 1621009 3649175 := bstep (se 1 (by rfl) ⟨2736881, by rfl⟩ : syracuseStep 3649175 = 5473763) B5473763
theorem B4107955 : Blo 1621009 4107955 := bstep (se 1 (by rfl) ⟨3080966, by rfl⟩ : syracuseStep 4107955 = 6161933) B6161933
theorem B6246067 : Blo 1621009 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B3288779 : Blo 1621009 3288779 := bstep (se 1 (by rfl) ⟨2466584, by rfl⟩ : syracuseStep 3288779 = 4933169) B4933169
theorem B4108097 : Blo 1621009 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B11685707 : Blo 1621009 11685707 := bstep (se 1 (by rfl) ⟨8764280, by rfl⟩ : syracuseStep 11685707 = 17528561) B17528561
theorem B3649355 : Blo 1621009 3649355 := bstep (se 1 (by rfl) ⟨2737016, by rfl⟩ : syracuseStep 3649355 = 5474033) B5474033
theorem B3649409 : Blo 1621009 3649409 := bstep (se 2 (by rfl) ⟨1368528, by rfl⟩ : syracuseStep 3649409 = 2737057) B2737057
theorem B13152131 : Blo 1621009 13152131 := bstep (se 1 (by rfl) ⟨9864098, by rfl⟩ : syracuseStep 13152131 = 19728197) B19728197
theorem B5476247 : Blo 1621009 5476247 := bstep (se 1 (by rfl) ⟨4107185, by rfl⟩ : syracuseStep 5476247 = 8214371) B8214371
theorem B17543089 : Blo 1621009 17543089 := bstep (se 2 (by rfl) ⟨6578658, by rfl⟩ : syracuseStep 17543089 = 13157317) B13157317
theorem B3649625 : Blo 1621009 3649625 := bstep (se 2 (by rfl) ⟨1368609, by rfl⟩ : syracuseStep 3649625 = 2737219) B2737219
theorem B23376023 : Blo 1621009 23376023 := bstep (se 1 (by rfl) ⟨17532017, by rfl⟩ : syracuseStep 23376023 = 35064035) B35064035
theorem B3649715 : Blo 1621009 3649715 := bstep (se 1 (by rfl) ⟨2737286, by rfl⟩ : syracuseStep 3649715 = 5474573) B5474573
theorem B2371799 : Blo 1621009 2371799 := bstep (se 1 (by rfl) ⟨1778849, by rfl⟩ : syracuseStep 2371799 = 3557699) B3557699
theorem B3649751 : Blo 1621009 3649751 := bstep (se 1 (by rfl) ⟨2737313, by rfl⟩ : syracuseStep 3649751 = 5474627) B5474627
theorem B3649931 : Blo 1621009 3649931 := bstep (se 1 (by rfl) ⟨2737448, by rfl⟩ : syracuseStep 3649931 = 5474897) B5474897
theorem B13332887 : Blo 1621009 13332887 := bstep (se 1 (by rfl) ⟨9999665, by rfl⟩ : syracuseStep 13332887 = 19999331) B19999331
theorem B5476787 : Blo 1621009 5476787 := bstep (se 1 (by rfl) ⟨4107590, by rfl⟩ : syracuseStep 5476787 = 8215181) B8215181
theorem B3649985 : Blo 1621009 3649985 := bstep (se 2 (by rfl) ⟨1368744, by rfl⟩ : syracuseStep 3649985 = 2737489) B2737489
theorem B2052631 : Blo 1621009 2052631 := bstep (se 1 (by rfl) ⟨1539473, by rfl⟩ : syracuseStep 2052631 = 3078947) B3078947
theorem B3650201 : Blo 1621009 3650201 := bstep (se 2 (by rfl) ⟨1368825, by rfl⟩ : syracuseStep 3650201 = 2737651) B2737651
theorem B5477057 : Blo 1621009 5477057 := bstep (se 2 (by rfl) ⟨2053896, by rfl⟩ : syracuseStep 5477057 = 4107793) B4107793
theorem B3289817 : Blo 1621009 3289817 := bstep (se 2 (by rfl) ⟨1233681, by rfl⟩ : syracuseStep 3289817 = 2467363) B2467363
theorem B2962163 : Blo 1621009 2962163 := bstep (se 1 (by rfl) ⟨2221622, by rfl⟩ : syracuseStep 2962163 = 4443245) B4443245
theorem B3650291 : Blo 1621009 3650291 := bstep (se 1 (by rfl) ⟨2737718, by rfl⟩ : syracuseStep 3650291 = 5475437) B5475437
theorem B6157073 : Blo 1621009 6157073 := bstep (se 2 (by rfl) ⟨2308902, by rfl⟩ : syracuseStep 6157073 = 4617805) B4617805
theorem B3650327 : Blo 1621009 3650327 := bstep (se 1 (by rfl) ⟨2737745, by rfl⟩ : syracuseStep 3650327 = 5475491) B5475491
theorem B12489547 : Blo 1621009 12489547 := bstep (se 1 (by rfl) ⟨9367160, by rfl⟩ : syracuseStep 12489547 = 18734321) B18734321
theorem B9237341 : Blo 1621009 9237341 := bstep (se 3 (by rfl) ⟨1732001, by rfl⟩ : syracuseStep 9237341 = 3464003) B3464003
theorem B8213399 : Blo 1621009 8213399 := bstep (se 1 (by rfl) ⟨6160049, by rfl⟩ : syracuseStep 8213399 = 12320099) B12320099
theorem B35066803 : Blo 1621009 35066803 := bstep (se 1 (by rfl) ⟨26300102, by rfl⟩ : syracuseStep 35066803 = 52600205) B52600205
theorem B3650507 : Blo 1621009 3650507 := bstep (se 1 (by rfl) ⟨2737880, by rfl⟩ : syracuseStep 3650507 = 5475761) B5475761
theorem B3650561 : Blo 1621009 3650561 := bstep (se 2 (by rfl) ⟨1368960, by rfl⟩ : syracuseStep 3650561 = 2737921) B2737921
theorem B1823755 : Blo 1621009 1823755 := bstep (se 1 (by rfl) ⟨1367816, by rfl⟩ : syracuseStep 1823755 = 2735633) B2735633
theorem B2339851 : Blo 1621009 2339851 := bstep (se 1 (by rfl) ⟨1754888, by rfl⟩ : syracuseStep 2339851 = 3509777) B3509777
theorem B8328257 : Blo 1621009 8328257 := bstep (se 2 (by rfl) ⟨3123096, by rfl⟩ : syracuseStep 8328257 = 6246193) B6246193
theorem B7402585 : Blo 1621009 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B1823863 : Blo 1621009 1823863 := bstep (se 1 (by rfl) ⟨1367897, by rfl⟩ : syracuseStep 1823863 = 2735795) B2735795
theorem B4617395 : Blo 1621009 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B6157529 : Blo 1621009 6157529 := bstep (se 2 (by rfl) ⟨2309073, by rfl⟩ : syracuseStep 6157529 = 4618147) B4618147
theorem B3650777 : Blo 1621009 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B5477597 : Blo 1621009 5477597 := bstep (se 3 (by rfl) ⟨1027049, by rfl⟩ : syracuseStep 5477597 = 2054099) B2054099
theorem B1824043 : Blo 1621009 1824043 := bstep (se 1 (by rfl) ⟨1368032, by rfl⟩ : syracuseStep 1824043 = 2736065) B2736065
theorem B3650867 : Blo 1621009 3650867 := bstep (se 1 (by rfl) ⟨2738150, by rfl⟩ : syracuseStep 3650867 = 5476301) B5476301
theorem B2053451 : Blo 1621009 2053451 := bstep (se 1 (by rfl) ⟨1540088, by rfl⟩ : syracuseStep 2053451 = 3080177) B3080177
theorem B3650903 : Blo 1621009 3650903 := bstep (se 1 (by rfl) ⟨2738177, by rfl⟩ : syracuseStep 3650903 = 5476355) B5476355
theorem B5846417 : Blo 1621009 5846417 := bstep (se 2 (by rfl) ⟨2192406, by rfl⟩ : syracuseStep 5846417 = 4384813) B4384813
theorem B3077527 : Blo 1621009 3077527 := bstep (se 1 (by rfl) ⟨2308145, by rfl⟩ : syracuseStep 3077527 = 4616291) B4616291
theorem B1824151 : Blo 1621009 1824151 := bstep (se 1 (by rfl) ⟨1368113, by rfl⟩ : syracuseStep 1824151 = 2736227) B2736227
theorem B4617623 : Blo 1621009 4617623 := bstep (se 1 (by rfl) ⟨3463217, by rfl⟩ : syracuseStep 4617623 = 6926435) B6926435
theorem B13858199 : Blo 1621009 13858199 := bstep (se 1 (by rfl) ⟨10393649, by rfl⟩ : syracuseStep 13858199 = 20787299) B20787299
theorem B6157741 : Blo 1621009 6157741 := bstep (se 3 (by rfl) ⟨1154576, by rfl⟩ : syracuseStep 6157741 = 2309153) B2309153
theorem B3651083 : Blo 1621009 3651083 := bstep (se 1 (by rfl) ⟨2738312, by rfl⟩ : syracuseStep 3651083 = 5476625) B5476625
theorem B3651137 : Blo 1621009 3651137 := bstep (se 2 (by rfl) ⟨1369176, by rfl⟩ : syracuseStep 3651137 = 2738353) B2738353
theorem B1824331 : Blo 1621009 1824331 := bstep (se 1 (by rfl) ⟨1368248, by rfl⟩ : syracuseStep 1824331 = 2736497) B2736497
theorem B3077747 : Blo 1621009 3077747 := bstep (se 1 (by rfl) ⟨2308310, by rfl⟩ : syracuseStep 3077747 = 4616621) B4616621
theorem B1848971 : Blo 1621009 1848971 := bstep (se 1 (by rfl) ⟨1386728, by rfl⟩ : syracuseStep 1848971 = 2773457) B2773457
theorem B1824439 : Blo 1621009 1824439 := bstep (se 1 (by rfl) ⟨1368329, by rfl⟩ : syracuseStep 1824439 = 2736659) B2736659
theorem B4617931 : Blo 1621009 4617931 := bstep (se 1 (by rfl) ⟨3463448, by rfl⟩ : syracuseStep 4617931 = 6926897) B6926897
theorem B6158045 : Blo 1621009 6158045 := bstep (se 3 (by rfl) ⟨1154633, by rfl⟩ : syracuseStep 6158045 = 2309267) B2309267
theorem B3512089 : Blo 1621009 3512089 := bstep (se 2 (by rfl) ⟨1317033, by rfl⟩ : syracuseStep 3512089 = 2634067) B2634067
theorem B3651353 : Blo 1621009 3651353 := bstep (se 2 (by rfl) ⟨1369257, by rfl⟩ : syracuseStep 3651353 = 2738515) B2738515
theorem B3077975 : Blo 1621009 3077975 := bstep (se 1 (by rfl) ⟨2308481, by rfl⟩ : syracuseStep 3077975 = 4616963) B4616963
theorem B11245405 : Blo 1621009 11245405 := bstep (se 3 (by rfl) ⟨2108513, by rfl⟩ : syracuseStep 11245405 = 4217027) B4217027
theorem B1824619 : Blo 1621009 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B3651443 : Blo 1621009 3651443 := bstep (se 1 (by rfl) ⟨2738582, by rfl⟩ : syracuseStep 3651443 = 5477165) B5477165
theorem B3651479 : Blo 1621009 3651479 := bstep (se 1 (by rfl) ⟨2738609, by rfl⟩ : syracuseStep 3651479 = 5477219) B5477219
theorem B12318641 : Blo 1621009 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B1824727 : Blo 1621009 1824727 := bstep (se 1 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 1824727 = 2737091) B2737091
theorem B4618205 : Blo 1621009 4618205 := bstep (se 3 (by rfl) ⟨865913, by rfl⟩ : syracuseStep 4618205 = 1731827) B1731827
theorem B5847005 : Blo 1621009 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B3897409 : Blo 1621009 3897409 := bstep (se 2 (by rfl) ⟨1461528, by rfl⟩ : syracuseStep 3897409 = 2923057) B2923057
theorem B3651659 : Blo 1621009 3651659 := bstep (se 1 (by rfl) ⟨2738744, by rfl⟩ : syracuseStep 3651659 = 5477489) B5477489
theorem B3078233 : Blo 1621009 3078233 := bstep (se 2 (by rfl) ⟨1154337, by rfl⟩ : syracuseStep 3078233 = 2308675) B2308675
theorem B3651713 : Blo 1621009 3651713 := bstep (se 2 (by rfl) ⟨1369392, by rfl⟩ : syracuseStep 3651713 = 2738785) B2738785
theorem B1824907 : Blo 1621009 1824907 := bstep (se 1 (by rfl) ⟨1368680, by rfl⟩ : syracuseStep 1824907 = 2737361) B2737361
theorem B1825015 : Blo 1621009 1825015 := bstep (se 1 (by rfl) ⟨1368761, by rfl⟩ : syracuseStep 1825015 = 2737523) B2737523
theorem B12319127 : Blo 1621009 12319127 := bstep (se 1 (by rfl) ⟨9239345, by rfl⟩ : syracuseStep 12319127 = 18478691) B18478691
theorem B1825195 : Blo 1621009 1825195 := bstep (se 1 (by rfl) ⟨1368896, by rfl⟩ : syracuseStep 1825195 = 2737793) B2737793
theorem B2890199 : Blo 1621009 2890199 := bstep (se 1 (by rfl) ⟨2167649, by rfl⟩ : syracuseStep 2890199 = 4335299) B4335299
theorem B6928861 : Blo 1621009 6928861 := bstep (se 3 (by rfl) ⟨1299161, by rfl⟩ : syracuseStep 6928861 = 2598323) B2598323
theorem B3078643 : Blo 1621009 3078643 := bstep (se 1 (by rfl) ⟨2308982, by rfl⟩ : syracuseStep 3078643 = 4617965) B4617965
theorem B1825303 : Blo 1621009 1825303 := bstep (se 1 (by rfl) ⟨1368977, by rfl⟩ : syracuseStep 1825303 = 2737955) B2737955
theorem B2431577 : Blo 1621009 2431577 := bstep (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) B1823683
theorem B10394243 : Blo 1621009 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B3463859 : Blo 1621009 3463859 := bstep (se 1 (by rfl) ⟨2597894, by rfl⟩ : syracuseStep 3463859 = 5195789) B5195789
theorem B2431691 : Blo 1621009 2431691 := bstep (se 1 (by rfl) ⟨1823768, by rfl⟩ : syracuseStep 2431691 = 3647537) B3647537
theorem B1825483 : Blo 1621009 1825483 := bstep (se 1 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 1825483 = 2738225) B2738225
theorem B2431703 : Blo 1621009 2431703 := bstep (se 1 (by rfl) ⟨1823777, by rfl⟩ : syracuseStep 2431703 = 3647555) B3647555
theorem B2431769 : Blo 1621009 2431769 := bstep (se 2 (by rfl) ⟨911913, by rfl⟩ : syracuseStep 2431769 = 1823827) B1823827
theorem B1825591 : Blo 1621009 1825591 := bstep (se 1 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 1825591 = 2738387) B2738387
theorem B10386269 : Blo 1621009 10386269 := bstep (se 3 (by rfl) ⟨1947425, by rfl⟩ : syracuseStep 10386269 = 3894851) B3894851
theorem B2431883 : Blo 1621009 2431883 := bstep (se 1 (by rfl) ⟨1823912, by rfl⟩ : syracuseStep 2431883 = 3647825) B3647825
theorem B2431895 : Blo 1621009 2431895 := bstep (se 1 (by rfl) ⟨1823921, by rfl⟩ : syracuseStep 2431895 = 3647843) B3647843
theorem B2079703 : Blo 1621009 2079703 := bstep (se 1 (by rfl) ⟨1559777, by rfl⟩ : syracuseStep 2079703 = 3119555) B3119555
theorem B2431961 : Blo 1621009 2431961 := bstep (se 2 (by rfl) ⟨911985, by rfl⟩ : syracuseStep 2431961 = 1823971) B1823971
theorem B3079129 : Blo 1621009 3079129 := bstep (se 2 (by rfl) ⟨1154673, by rfl⟩ : syracuseStep 3079129 = 2309347) B2309347
theorem B1825771 : Blo 1621009 1825771 := bstep (se 1 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 1825771 = 2738657) B2738657
theorem B1621015 : Blo 1621009 1621015 := bstep (se 1 (by rfl) ⟨1215761, by rfl⟩ : syracuseStep 1621015 = 2431523) B2431523
theorem B1621035 : Blo 1621009 1621035 := bstep (se 1 (by rfl) ⟨1215776, by rfl⟩ : syracuseStep 1621035 = 2431553) B2431553
theorem B8207405 : Blo 1621009 8207405 := bstep (se 3 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 8207405 = 3077777) B3077777
theorem B1621047 : Blo 1621009 1621047 := bstep (se 1 (by rfl) ⟨1215785, by rfl⟩ : syracuseStep 1621047 = 2431571) B2431571
theorem B5135425 : Blo 1621009 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B1621067 : Blo 1621009 1621067 := bstep (se 1 (by rfl) ⟨1215800, by rfl⟩ : syracuseStep 1621067 = 2431601) B2431601
theorem B2432075 : Blo 1621009 2432075 := bstep (se 1 (by rfl) ⟨1824056, by rfl⟩ : syracuseStep 2432075 = 3648113) B3648113
theorem B1621079 : Blo 1621009 1621079 := bstep (se 1 (by rfl) ⟨1215809, by rfl⟩ : syracuseStep 1621079 = 2431619) B2431619
theorem B2432087 : Blo 1621009 2432087 := bstep (se 1 (by rfl) ⟨1824065, by rfl⟩ : syracuseStep 2432087 = 3648131) B3648131
theorem B4103257 : Blo 1621009 4103257 := bstep (se 2 (by rfl) ⟨1538721, by rfl⟩ : syracuseStep 4103257 = 3077443) B3077443
theorem B1825879 : Blo 1621009 1825879 := bstep (se 1 (by rfl) ⟨1369409, by rfl⟩ : syracuseStep 1825879 = 2738819) B2738819
theorem B1621099 : Blo 1621009 1621099 := bstep (se 1 (by rfl) ⟨1215824, by rfl⟩ : syracuseStep 1621099 = 2431649) B2431649
theorem B1621111 : Blo 1621009 1621111 := bstep (se 1 (by rfl) ⟨1215833, by rfl⟩ : syracuseStep 1621111 = 2431667) B2431667
theorem B1621131 : Blo 1621009 1621131 := bstep (se 1 (by rfl) ⟨1215848, by rfl⟩ : syracuseStep 1621131 = 2431697) B2431697
theorem B1621143 : Blo 1621009 1621143 := bstep (se 1 (by rfl) ⟨1215857, by rfl⟩ : syracuseStep 1621143 = 2431715) B2431715
theorem B2432153 : Blo 1621009 2432153 := bstep (se 2 (by rfl) ⟨912057, by rfl⟩ : syracuseStep 2432153 = 1824115) B1824115
theorem B3464345 : Blo 1621009 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B1621163 : Blo 1621009 1621163 := bstep (se 1 (by rfl) ⟨1215872, by rfl⟩ : syracuseStep 1621163 = 2431745) B2431745
theorem B1621175 : Blo 1621009 1621175 := bstep (se 1 (by rfl) ⟨1215881, by rfl⟩ : syracuseStep 1621175 = 2431763) B2431763
theorem B1621195 : Blo 1621009 1621195 := bstep (se 1 (by rfl) ⟨1215896, by rfl⟩ : syracuseStep 1621195 = 2431793) B2431793
theorem B3087563 : Blo 1621009 3087563 := bstep (se 1 (by rfl) ⟨2315672, by rfl⟩ : syracuseStep 3087563 = 4631345) B4631345
theorem B1621207 : Blo 1621009 1621207 := bstep (se 1 (by rfl) ⟨1215905, by rfl⟩ : syracuseStep 1621207 = 2431811) B2431811
theorem B1621227 : Blo 1621009 1621227 := bstep (se 1 (by rfl) ⟨1215920, by rfl⟩ : syracuseStep 1621227 = 2431841) B2431841
theorem B1621239 : Blo 1621009 1621239 := bstep (se 1 (by rfl) ⟨1215929, by rfl⟩ : syracuseStep 1621239 = 2431859) B2431859
theorem B70139141 : Blo 1621009 70139141 := bstep (se 4 (by rfl) ⟨6575544, by rfl⟩ : syracuseStep 70139141 = 13151089) B13151089
theorem B1621259 : Blo 1621009 1621259 := bstep (se 1 (by rfl) ⟨1215944, by rfl⟩ : syracuseStep 1621259 = 2431889) B2431889
theorem B2432267 : Blo 1621009 2432267 := bstep (se 1 (by rfl) ⟨1824200, by rfl⟩ : syracuseStep 2432267 = 3648401) B3648401
theorem B1621271 : Blo 1621009 1621271 := bstep (se 1 (by rfl) ⟨1215953, by rfl⟩ : syracuseStep 1621271 = 2431907) B2431907
theorem B2432279 : Blo 1621009 2432279 := bstep (se 1 (by rfl) ⟨1824209, by rfl⟩ : syracuseStep 2432279 = 3648419) B3648419
theorem B11697443 : Blo 1621009 11697443 := bstep (se 1 (by rfl) ⟨8773082, by rfl⟩ : syracuseStep 11697443 = 17546165) B17546165
theorem B1621291 : Blo 1621009 1621291 := bstep (se 1 (by rfl) ⟨1215968, by rfl⟩ : syracuseStep 1621291 = 2431937) B2431937
theorem B1621303 : Blo 1621009 1621303 := bstep (se 1 (by rfl) ⟨1215977, by rfl⟩ : syracuseStep 1621303 = 2431955) B2431955
theorem B8772929 : Blo 1621009 8772929 := bstep (se 2 (by rfl) ⟨3289848, by rfl⟩ : syracuseStep 8772929 = 6579697) B6579697
theorem B1621323 : Blo 1621009 1621323 := bstep (se 1 (by rfl) ⟨1215992, by rfl⟩ : syracuseStep 1621323 = 2431985) B2431985
theorem B1621335 : Blo 1621009 1621335 := bstep (se 1 (by rfl) ⟨1216001, by rfl⟩ : syracuseStep 1621335 = 2432003) B2432003
theorem B2432345 : Blo 1621009 2432345 := bstep (se 2 (by rfl) ⟨912129, by rfl⟩ : syracuseStep 2432345 = 1824259) B1824259
theorem B4382045 : Blo 1621009 4382045 := bstep (se 3 (by rfl) ⟨821633, by rfl⟩ : syracuseStep 4382045 = 1643267) B1643267
theorem B1621355 : Blo 1621009 1621355 := bstep (se 1 (by rfl) ⟨1216016, by rfl⟩ : syracuseStep 1621355 = 2432033) B2432033
theorem B1621367 : Blo 1621009 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B9239939 : Blo 1621009 9239939 := bstep (se 1 (by rfl) ⟨6929954, by rfl⟩ : syracuseStep 9239939 = 13859909) B13859909
theorem B1621387 : Blo 1621009 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B389684621 : Blo 1621009 389684621 := bstep (se 3 (by rfl) ⟨73065866, by rfl⟩ : syracuseStep 389684621 = 146131733) B146131733
theorem B1621399 : Blo 1621009 1621399 := bstep (se 1 (by rfl) ⟨1216049, by rfl⟩ : syracuseStep 1621399 = 2432099) B2432099
theorem B1621419 : Blo 1621009 1621419 := bstep (se 1 (by rfl) ⟨1216064, by rfl⟩ : syracuseStep 1621419 = 2432129) B2432129
theorem B1621431 : Blo 1621009 1621431 := bstep (se 1 (by rfl) ⟨1216073, by rfl⟩ : syracuseStep 1621431 = 2432147) B2432147
theorem B1621451 : Blo 1621009 1621451 := bstep (se 1 (by rfl) ⟨1216088, by rfl⟩ : syracuseStep 1621451 = 2432177) B2432177
theorem B2432459 : Blo 1621009 2432459 := bstep (se 1 (by rfl) ⟨1824344, by rfl⟩ : syracuseStep 2432459 = 3648689) B3648689
theorem B1621463 : Blo 1621009 1621463 := bstep (se 1 (by rfl) ⟨1216097, by rfl⟩ : syracuseStep 1621463 = 2432195) B2432195
theorem B2432471 : Blo 1621009 2432471 := bstep (se 1 (by rfl) ⟨1824353, by rfl⟩ : syracuseStep 2432471 = 3648707) B3648707
theorem B15580633 : Blo 1621009 15580633 := bstep (se 2 (by rfl) ⟨5842737, by rfl⟩ : syracuseStep 15580633 = 11685475) B11685475
theorem B1621483 : Blo 1621009 1621483 := bstep (se 1 (by rfl) ⟨1216112, by rfl⟩ : syracuseStep 1621483 = 2432225) B2432225
theorem B1621495 : Blo 1621009 1621495 := bstep (se 1 (by rfl) ⟨1216121, by rfl⟩ : syracuseStep 1621495 = 2432243) B2432243
theorem B2465291 : Blo 1621009 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B1621515 : Blo 1621009 1621515 := bstep (se 1 (by rfl) ⟨1216136, by rfl⟩ : syracuseStep 1621515 = 2432273) B2432273
theorem B3079691 : Blo 1621009 3079691 := bstep (se 1 (by rfl) ⟨2309768, by rfl⟩ : syracuseStep 3079691 = 4619537) B4619537
theorem B1621527 : Blo 1621009 1621527 := bstep (se 1 (by rfl) ⟨1216145, by rfl⟩ : syracuseStep 1621527 = 2432291) B2432291
theorem B2432537 : Blo 1621009 2432537 := bstep (se 2 (by rfl) ⟨912201, by rfl⟩ : syracuseStep 2432537 = 1824403) B1824403
theorem B1621547 : Blo 1621009 1621547 := bstep (se 1 (by rfl) ⟨1216160, by rfl⟩ : syracuseStep 1621547 = 2432321) B2432321
theorem B8764973 : Blo 1621009 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B1621559 : Blo 1621009 1621559 := bstep (se 1 (by rfl) ⟨1216169, by rfl⟩ : syracuseStep 1621559 = 2432339) B2432339
theorem B5471819 : Blo 1621009 5471819 := bstep (se 1 (by rfl) ⟨4103864, by rfl⟩ : syracuseStep 5471819 = 8207729) B8207729
theorem B1621579 : Blo 1621009 1621579 := bstep (se 1 (by rfl) ⟨1216184, by rfl⟩ : syracuseStep 1621579 = 2432369) B2432369
theorem B1621591 : Blo 1621009 1621591 := bstep (se 1 (by rfl) ⟨1216193, by rfl⟩ : syracuseStep 1621591 = 2432387) B2432387
theorem B26320477 : Blo 1621009 26320477 := bstep (se 3 (by rfl) ⟨4935089, by rfl⟩ : syracuseStep 26320477 = 9870179) B9870179
theorem B1621611 : Blo 1621009 1621611 := bstep (se 1 (by rfl) ⟨1216208, by rfl⟩ : syracuseStep 1621611 = 2432417) B2432417
theorem B1621623 : Blo 1621009 1621623 := bstep (se 1 (by rfl) ⟨1216217, by rfl⟩ : syracuseStep 1621623 = 2432435) B2432435
theorem B2432651 : Blo 1621009 2432651 := bstep (se 1 (by rfl) ⟨1824488, by rfl⟩ : syracuseStep 2432651 = 3648977) B3648977
theorem B1621643 : Blo 1621009 1621643 := bstep (se 1 (by rfl) ⟨1216232, by rfl⟩ : syracuseStep 1621643 = 2432465) B2432465
theorem B1621655 : Blo 1621009 1621655 := bstep (se 1 (by rfl) ⟨1216241, by rfl⟩ : syracuseStep 1621655 = 2432483) B2432483
theorem B2432663 : Blo 1621009 2432663 := bstep (se 1 (by rfl) ⟨1824497, by rfl⟩ : syracuseStep 2432663 = 3648995) B3648995
theorem B1621675 : Blo 1621009 1621675 := bstep (se 1 (by rfl) ⟨1216256, by rfl⟩ : syracuseStep 1621675 = 2432513) B2432513
theorem B1621687 : Blo 1621009 1621687 := bstep (se 1 (by rfl) ⟨1216265, by rfl⟩ : syracuseStep 1621687 = 2432531) B2432531
theorem B3079873 : Blo 1621009 3079873 := bstep (se 2 (by rfl) ⟨1154952, by rfl⟩ : syracuseStep 3079873 = 2309905) B2309905
theorem B1621707 : Blo 1621009 1621707 := bstep (se 1 (by rfl) ⟨1216280, by rfl⟩ : syracuseStep 1621707 = 2432561) B2432561
theorem B20790989 : Blo 1621009 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B1621719 : Blo 1621009 1621719 := bstep (se 1 (by rfl) ⟨1216289, by rfl⟩ : syracuseStep 1621719 = 2432579) B2432579
theorem B2432729 : Blo 1621009 2432729 := bstep (se 2 (by rfl) ⟨912273, by rfl⟩ : syracuseStep 2432729 = 1824547) B1824547
theorem B1621739 : Blo 1621009 1621739 := bstep (se 1 (by rfl) ⟨1216304, by rfl⟩ : syracuseStep 1621739 = 2432609) B2432609
theorem B1621751 : Blo 1621009 1621751 := bstep (se 1 (by rfl) ⟨1216313, by rfl⟩ : syracuseStep 1621751 = 2432627) B2432627
theorem B2596619 : Blo 1621009 2596619 := bstep (se 1 (by rfl) ⟨1947464, by rfl⟩ : syracuseStep 2596619 = 3894929) B3894929
theorem B1621771 : Blo 1621009 1621771 := bstep (se 1 (by rfl) ⟨1216328, by rfl⟩ : syracuseStep 1621771 = 2432657) B2432657
theorem B6930193 : Blo 1621009 6930193 := bstep (se 2 (by rfl) ⟨2598822, by rfl⟩ : syracuseStep 6930193 = 5197645) B5197645
theorem B1621783 : Blo 1621009 1621783 := bstep (se 1 (by rfl) ⟨1216337, by rfl⟩ : syracuseStep 1621783 = 2432675) B2432675
theorem B1621803 : Blo 1621009 1621803 := bstep (se 1 (by rfl) ⟨1216352, by rfl⟩ : syracuseStep 1621803 = 2432705) B2432705
theorem B1621815 : Blo 1621009 1621815 := bstep (se 1 (by rfl) ⟨1216361, by rfl⟩ : syracuseStep 1621815 = 2432723) B2432723
theorem B1621835 : Blo 1621009 1621835 := bstep (se 1 (by rfl) ⟨1216376, by rfl⟩ : syracuseStep 1621835 = 2432753) B2432753
theorem B2432843 : Blo 1621009 2432843 := bstep (se 1 (by rfl) ⟨1824632, by rfl⟩ : syracuseStep 2432843 = 3649265) B3649265
theorem B1621847 : Blo 1621009 1621847 := bstep (se 1 (by rfl) ⟨1216385, by rfl⟩ : syracuseStep 1621847 = 2432771) B2432771
theorem B5472089 : Blo 1621009 5472089 := bstep (se 2 (by rfl) ⟨2052033, by rfl⟩ : syracuseStep 5472089 = 4104067) B4104067
theorem B2432855 : Blo 1621009 2432855 := bstep (se 1 (by rfl) ⟨1824641, by rfl⟩ : syracuseStep 2432855 = 3649283) B3649283
theorem B1621867 : Blo 1621009 1621867 := bstep (se 1 (by rfl) ⟨1216400, by rfl⟩ : syracuseStep 1621867 = 2432801) B2432801
theorem B1621879 : Blo 1621009 1621879 := bstep (se 1 (by rfl) ⟨1216409, by rfl⟩ : syracuseStep 1621879 = 2432819) B2432819
theorem B3465089 : Blo 1621009 3465089 := bstep (se 2 (by rfl) ⟨1299408, by rfl⟩ : syracuseStep 3465089 = 2598817) B2598817
theorem B2736011 : Blo 1621009 2736011 := bstep (se 1 (by rfl) ⟨2052008, by rfl⟩ : syracuseStep 2736011 = 4104017) B4104017
theorem B1621899 : Blo 1621009 1621899 := bstep (se 1 (by rfl) ⟨1216424, by rfl⟩ : syracuseStep 1621899 = 2432849) B2432849
theorem B1621911 : Blo 1621009 1621911 := bstep (se 1 (by rfl) ⟨1216433, by rfl⟩ : syracuseStep 1621911 = 2432867) B2432867
theorem B2432921 : Blo 1621009 2432921 := bstep (se 2 (by rfl) ⟨912345, by rfl⟩ : syracuseStep 2432921 = 1824691) B1824691
theorem B2924441 : Blo 1621009 2924441 := bstep (se 2 (by rfl) ⟨1096665, by rfl⟩ : syracuseStep 2924441 = 2193331) B2193331
theorem B1621931 : Blo 1621009 1621931 := bstep (se 1 (by rfl) ⟨1216448, by rfl⟩ : syracuseStep 1621931 = 2432897) B2432897
theorem B1621943 : Blo 1621009 1621943 := bstep (se 1 (by rfl) ⟨1216457, by rfl⟩ : syracuseStep 1621943 = 2432915) B2432915
theorem B1621963 : Blo 1621009 1621963 := bstep (se 1 (by rfl) ⟨1216472, by rfl⟩ : syracuseStep 1621963 = 2432945) B2432945
theorem B1621975 : Blo 1621009 1621975 := bstep (se 1 (by rfl) ⟨1216481, by rfl⟩ : syracuseStep 1621975 = 2432963) B2432963
theorem B1621995 : Blo 1621009 1621995 := bstep (se 1 (by rfl) ⟨1216496, by rfl⟩ : syracuseStep 1621995 = 2432993) B2432993
theorem B1622023 : Blo 1621009 1622023 := bstep (se 1 (by rfl) ⟨1216517, by rfl⟩ : syracuseStep 1622023 = 2433035) B2433035
theorem B1622031 : Blo 1621009 1622031 := bstep (se 1 (by rfl) ⟨1216523, by rfl⟩ : syracuseStep 1622031 = 2433047) B2433047
theorem B3080207 : Blo 1621009 3080207 := bstep (se 1 (by rfl) ⟨2310155, by rfl⟩ : syracuseStep 3080207 = 4620311) B4620311
theorem B2433083 : Blo 1621009 2433083 := bstep (se 1 (by rfl) ⟨1824812, by rfl⟩ : syracuseStep 2433083 = 3649625) B3649625
theorem B1622075 : Blo 1621009 1622075 := bstep (se 1 (by rfl) ⟨1216556, by rfl⟩ : syracuseStep 1622075 = 2433113) B2433113
theorem B6160445 : Blo 1621009 6160445 := bstep (se 3 (by rfl) ⟨1155083, by rfl⟩ : syracuseStep 6160445 = 2310167) B2310167
theorem B2736247 : Blo 1621009 2736247 := bstep (se 1 (by rfl) ⟨2052185, by rfl⟩ : syracuseStep 2736247 = 4104371) B4104371
theorem B2433143 : Blo 1621009 2433143 := bstep (se 1 (by rfl) ⟨1824857, by rfl⟩ : syracuseStep 2433143 = 3649715) B3649715
theorem B1622151 : Blo 1621009 1622151 := bstep (se 1 (by rfl) ⟨1216613, by rfl⟩ : syracuseStep 1622151 = 2433227) B2433227
theorem B2433167 : Blo 1621009 2433167 := bstep (se 1 (by rfl) ⟨1824875, by rfl⟩ : syracuseStep 2433167 = 3649751) B3649751
theorem B1622159 : Blo 1621009 1622159 := bstep (se 1 (by rfl) ⟨1216619, by rfl⟩ : syracuseStep 1622159 = 2433239) B2433239
theorem B2433209 : Blo 1621009 2433209 := bstep (se 2 (by rfl) ⟨912453, by rfl⟩ : syracuseStep 2433209 = 1824907) B1824907
theorem B1622203 : Blo 1621009 1622203 := bstep (se 1 (by rfl) ⟨1216652, by rfl⟩ : syracuseStep 1622203 = 2433305) B2433305
theorem B2433287 : Blo 1621009 2433287 := bstep (se 1 (by rfl) ⟨1824965, by rfl⟩ : syracuseStep 2433287 = 3649931) B3649931
theorem B1622279 : Blo 1621009 1622279 := bstep (se 1 (by rfl) ⟨1216709, by rfl⟩ : syracuseStep 1622279 = 2433419) B2433419
theorem B8888591 : Blo 1621009 8888591 := bstep (se 1 (by rfl) ⟨6666443, by rfl⟩ : syracuseStep 8888591 = 13332887) B13332887
theorem B1622287 : Blo 1621009 1622287 := bstep (se 1 (by rfl) ⟨1216715, by rfl⟩ : syracuseStep 1622287 = 2433431) B2433431
theorem B2433323 : Blo 1621009 2433323 := bstep (se 1 (by rfl) ⟨1824992, by rfl⟩ : syracuseStep 2433323 = 3649985) B3649985
theorem B2736443 : Blo 1621009 2736443 := bstep (se 1 (by rfl) ⟨2052332, by rfl⟩ : syracuseStep 2736443 = 4104665) B4104665
theorem B1622331 : Blo 1621009 1622331 := bstep (se 1 (by rfl) ⟨1216748, by rfl⟩ : syracuseStep 1622331 = 2433497) B2433497
theorem B2433353 : Blo 1621009 2433353 := bstep (se 2 (by rfl) ⟨912507, by rfl⟩ : syracuseStep 2433353 = 1825015) B1825015
theorem B1622407 : Blo 1621009 1622407 := bstep (se 1 (by rfl) ⟨1216805, by rfl⟩ : syracuseStep 1622407 = 2433611) B2433611
theorem B1622415 : Blo 1621009 1622415 := bstep (se 1 (by rfl) ⟨1216811, by rfl⟩ : syracuseStep 1622415 = 2433623) B2433623
theorem B2433467 : Blo 1621009 2433467 := bstep (se 1 (by rfl) ⟨1825100, by rfl⟩ : syracuseStep 2433467 = 3650201) B3650201
theorem B1622459 : Blo 1621009 1622459 := bstep (se 1 (by rfl) ⟨1216844, by rfl⟩ : syracuseStep 1622459 = 2433689) B2433689
theorem B18735569 : Blo 1621009 18735569 := bstep (se 2 (by rfl) ⟨7025838, by rfl⟩ : syracuseStep 18735569 = 14051677) B14051677
theorem B1974775 : Blo 1621009 1974775 := bstep (se 1 (by rfl) ⟨1481081, by rfl⟩ : syracuseStep 1974775 = 2962163) B2962163
theorem B2433527 : Blo 1621009 2433527 := bstep (se 1 (by rfl) ⟨1825145, by rfl⟩ : syracuseStep 2433527 = 3650291) B3650291
theorem B1622535 : Blo 1621009 1622535 := bstep (se 1 (by rfl) ⟨1216901, by rfl⟩ : syracuseStep 1622535 = 2433803) B2433803
theorem B4104715 : Blo 1621009 4104715 := bstep (se 1 (by rfl) ⟨3078536, by rfl⟩ : syracuseStep 4104715 = 6157073) B6157073
theorem B2433551 : Blo 1621009 2433551 := bstep (se 1 (by rfl) ⟨1825163, by rfl⟩ : syracuseStep 2433551 = 3650327) B3650327
theorem B1622543 : Blo 1621009 1622543 := bstep (se 1 (by rfl) ⟨1216907, by rfl⟩ : syracuseStep 1622543 = 2433815) B2433815
theorem B8233501 : Blo 1621009 8233501 := bstep (se 3 (by rfl) ⟨1543781, by rfl⟩ : syracuseStep 8233501 = 3087563) B3087563
theorem B3080747 : Blo 1621009 3080747 := bstep (se 1 (by rfl) ⟨2310560, by rfl⟩ : syracuseStep 3080747 = 4621121) B4621121
theorem B2433593 : Blo 1621009 2433593 := bstep (se 2 (by rfl) ⟨912597, by rfl⟩ : syracuseStep 2433593 = 1825195) B1825195
theorem B1622587 : Blo 1621009 1622587 := bstep (se 1 (by rfl) ⟨1216940, by rfl⟩ : syracuseStep 1622587 = 2433881) B2433881
theorem B6324797 : Blo 1621009 6324797 := bstep (se 3 (by rfl) ⟨1185899, by rfl⟩ : syracuseStep 6324797 = 2371799) B2371799
theorem B2433671 : Blo 1621009 2433671 := bstep (se 1 (by rfl) ⟨1825253, by rfl⟩ : syracuseStep 2433671 = 3650507) B3650507
theorem B1622663 : Blo 1621009 1622663 := bstep (se 1 (by rfl) ⟨1216997, by rfl⟩ : syracuseStep 1622663 = 2433995) B2433995
theorem B1622671 : Blo 1621009 1622671 := bstep (se 1 (by rfl) ⟨1217003, by rfl⟩ : syracuseStep 1622671 = 2434007) B2434007
theorem B4104857 : Blo 1621009 4104857 := bstep (se 2 (by rfl) ⟨1539321, by rfl⟩ : syracuseStep 4104857 = 3078643) B3078643
theorem B2433707 : Blo 1621009 2433707 := bstep (se 1 (by rfl) ⟨1825280, by rfl⟩ : syracuseStep 2433707 = 3650561) B3650561
theorem B1622715 : Blo 1621009 1622715 := bstep (se 1 (by rfl) ⟨1217036, by rfl⟩ : syracuseStep 1622715 = 2434073) B2434073
theorem B2736841 : Blo 1621009 2736841 := bstep (se 2 (by rfl) ⟨1026315, by rfl⟩ : syracuseStep 2736841 = 2052631) B2052631
theorem B2433737 : Blo 1621009 2433737 := bstep (se 2 (by rfl) ⟨912651, by rfl⟩ : syracuseStep 2433737 = 1825303) B1825303
theorem B1622791 : Blo 1621009 1622791 := bstep (se 1 (by rfl) ⟨1217093, by rfl⟩ : syracuseStep 1622791 = 2434187) B2434187
theorem B9863951 : Blo 1621009 9863951 := bstep (se 1 (by rfl) ⟨7397963, by rfl⟩ : syracuseStep 9863951 = 14795927) B14795927
theorem B1622799 : Blo 1621009 1622799 := bstep (se 1 (by rfl) ⟨1217099, by rfl⟩ : syracuseStep 1622799 = 2434199) B2434199
theorem B4105019 : Blo 1621009 4105019 := bstep (se 1 (by rfl) ⟨3078764, by rfl⟩ : syracuseStep 4105019 = 6157529) B6157529
theorem B2433851 : Blo 1621009 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B1622843 : Blo 1621009 1622843 := bstep (se 1 (by rfl) ⟨1217132, by rfl⟩ : syracuseStep 1622843 = 2434265) B2434265
theorem B2433911 : Blo 1621009 2433911 := bstep (se 1 (by rfl) ⟨1825433, by rfl⟩ : syracuseStep 2433911 = 3650867) B3650867
theorem B1622919 : Blo 1621009 1622919 := bstep (se 1 (by rfl) ⟨1217189, by rfl⟩ : syracuseStep 1622919 = 2434379) B2434379
theorem B2433935 : Blo 1621009 2433935 := bstep (se 1 (by rfl) ⟨1825451, by rfl⟩ : syracuseStep 2433935 = 3650903) B3650903
theorem B1622927 : Blo 1621009 1622927 := bstep (se 1 (by rfl) ⟨1217195, by rfl⟩ : syracuseStep 1622927 = 2434391) B2434391
theorem B2433977 : Blo 1621009 2433977 := bstep (se 2 (by rfl) ⟨912741, by rfl⟩ : syracuseStep 2433977 = 1825483) B1825483
theorem B1622971 : Blo 1621009 1622971 := bstep (se 1 (by rfl) ⟨1217228, by rfl⟩ : syracuseStep 1622971 = 2434457) B2434457
theorem B4621313 : Blo 1621009 4621313 := bstep (se 2 (by rfl) ⟨1732992, by rfl⟩ : syracuseStep 4621313 = 3465985) B3465985
theorem B2434055 : Blo 1621009 2434055 := bstep (se 1 (by rfl) ⟨1825541, by rfl⟩ : syracuseStep 2434055 = 3651083) B3651083
theorem B5194763 : Blo 1621009 5194763 := bstep (se 1 (by rfl) ⟨3896072, by rfl⟩ : syracuseStep 5194763 = 7792145) B7792145
theorem B2434091 : Blo 1621009 2434091 := bstep (se 1 (by rfl) ⟨1825568, by rfl⟩ : syracuseStep 2434091 = 3651137) B3651137
theorem B2434121 : Blo 1621009 2434121 := bstep (se 2 (by rfl) ⟨912795, by rfl⟩ : syracuseStep 2434121 = 1825591) B1825591
theorem B4105363 : Blo 1621009 4105363 := bstep (se 1 (by rfl) ⟨3079022, by rfl⟩ : syracuseStep 4105363 = 6158045) B6158045
theorem B2434235 : Blo 1621009 2434235 := bstep (se 1 (by rfl) ⟨1825676, by rfl⟩ : syracuseStep 2434235 = 3651353) B3651353
theorem B2434295 : Blo 1621009 2434295 := bstep (se 1 (by rfl) ⟨1825721, by rfl⟩ : syracuseStep 2434295 = 3651443) B3651443
theorem B2434319 : Blo 1621009 2434319 := bstep (se 1 (by rfl) ⟨1825739, by rfl⟩ : syracuseStep 2434319 = 3651479) B3651479
theorem B4105505 : Blo 1621009 4105505 := bstep (se 2 (by rfl) ⟨1539564, by rfl⟩ : syracuseStep 4105505 = 3079129) B3079129
theorem B2434361 : Blo 1621009 2434361 := bstep (se 2 (by rfl) ⟨912885, by rfl⟩ : syracuseStep 2434361 = 1825771) B1825771
theorem B15582557 : Blo 1621009 15582557 := bstep (se 3 (by rfl) ⟨2921729, by rfl⟩ : syracuseStep 15582557 = 5843459) B5843459
theorem B56935811 : Blo 1621009 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B2737543 : Blo 1621009 2737543 := bstep (se 1 (by rfl) ⟨2053157, by rfl⟩ : syracuseStep 2737543 = 4106315) B4106315
theorem B2434439 : Blo 1621009 2434439 := bstep (se 1 (by rfl) ⟨1825829, by rfl⟩ : syracuseStep 2434439 = 3651659) B3651659
theorem B2434475 : Blo 1621009 2434475 := bstep (se 1 (by rfl) ⟨1825856, by rfl⟩ : syracuseStep 2434475 = 3651713) B3651713
theorem B2434505 : Blo 1621009 2434505 := bstep (se 2 (by rfl) ⟨912939, by rfl⟩ : syracuseStep 2434505 = 1825879) B1825879
theorem B4621769 : Blo 1621009 4621769 := bstep (se 2 (by rfl) ⟨1733163, by rfl⟩ : syracuseStep 4621769 = 3466327) B3466327
theorem B4999031 : Blo 1621009 4999031 := bstep (se 1 (by rfl) ⟨3749273, by rfl⟩ : syracuseStep 4999031 = 7498547) B7498547
theorem B8210321 : Blo 1621009 8210321 := bstep (se 2 (by rfl) ⟨3078870, by rfl⟩ : syracuseStep 8210321 = 6157741) B6157741
theorem B6924179 : Blo 1621009 6924179 := bstep (se 1 (by rfl) ⟨5193134, by rfl⟩ : syracuseStep 6924179 = 10386269) B10386269
theorem B5474195 : Blo 1621009 5474195 := bstep (se 1 (by rfl) ⟨4105646, by rfl⟩ : syracuseStep 5474195 = 8211293) B8211293
theorem B2738191 : Blo 1621009 2738191 := bstep (se 1 (by rfl) ⟨2053643, by rfl⟩ : syracuseStep 2738191 = 4107287) B4107287
theorem B4106497 : Blo 1621009 4106497 := bstep (se 2 (by rfl) ⟨1539936, by rfl⟩ : syracuseStep 4106497 = 3079873) B3079873
theorem B5843315 : Blo 1621009 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B3647879 : Blo 1621009 3647879 := bstep (se 1 (by rfl) ⟨2735909, by rfl⟩ : syracuseStep 3647879 = 5471819) B5471819
theorem B8440199 : Blo 1621009 8440199 := bstep (se 1 (by rfl) ⟨6330149, by rfl⟩ : syracuseStep 8440199 = 12660299) B12660299
theorem B14993873 : Blo 1621009 14993873 := bstep (se 2 (by rfl) ⟨5622702, by rfl⟩ : syracuseStep 14993873 = 11245405) B11245405
theorem B1731079 : Blo 1621009 1731079 := bstep (se 1 (by rfl) ⟨1298309, by rfl⟩ : syracuseStep 1731079 = 2596619) B2596619
theorem B2738731 : Blo 1621009 2738731 := bstep (se 1 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 2738731 = 4108097) B4108097
theorem B3648059 : Blo 1621009 3648059 := bstep (se 1 (by rfl) ⟨2736044, by rfl⟩ : syracuseStep 3648059 = 5472089) B5472089
theorem B23390785 : Blo 1621009 23390785 := bstep (se 2 (by rfl) ⟨8771544, by rfl⟩ : syracuseStep 23390785 = 17543089) B17543089
theorem B15592013 : Blo 1621009 15592013 := bstep (se 3 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 15592013 = 5847005) B5847005
theorem B8768087 : Blo 1621009 8768087 := bstep (se 1 (by rfl) ⟨6576065, by rfl⟩ : syracuseStep 8768087 = 13152131) B13152131
theorem B3648185 : Blo 1621009 3648185 := bstep (se 2 (by rfl) ⟨1368069, by rfl⟩ : syracuseStep 3648185 = 2736139) B2736139
theorem B5196545 : Blo 1621009 5196545 := bstep (se 2 (by rfl) ⟨1948704, by rfl⟩ : syracuseStep 5196545 = 3897409) B3897409
theorem B15584015 : Blo 1621009 15584015 := bstep (se 1 (by rfl) ⟨11688011, by rfl⟩ : syracuseStep 15584015 = 23376023) B23376023
theorem B4107095 : Blo 1621009 4107095 := bstep (se 1 (by rfl) ⟨3080321, by rfl⟩ : syracuseStep 4107095 = 6160643) B6160643
theorem B5548985 : Blo 1621009 5548985 := bstep (se 2 (by rfl) ⟨2080869, by rfl⟩ : syracuseStep 5548985 = 4161739) B4161739
theorem B3648527 : Blo 1621009 3648527 := bstep (se 1 (by rfl) ⟨2736395, by rfl⟩ : syracuseStep 3648527 = 5472791) B5472791
theorem B3648545 : Blo 1621009 3648545 := bstep (se 2 (by rfl) ⟨1368204, by rfl⟩ : syracuseStep 3648545 = 2736409) B2736409
theorem B4107307 : Blo 1621009 4107307 := bstep (se 1 (by rfl) ⟨3080480, by rfl⟩ : syracuseStep 4107307 = 6160961) B6160961
theorem B4107449 : Blo 1621009 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B5475599 : Blo 1621009 5475599 := bstep (se 1 (by rfl) ⟨4106699, by rfl⟩ : syracuseStep 5475599 = 8213399) B8213399
theorem B1731899 : Blo 1621009 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B3648887 : Blo 1621009 3648887 := bstep (se 1 (by rfl) ⟨2736665, by rfl⟩ : syracuseStep 3648887 = 5473331) B5473331
theorem B13856285 : Blo 1621009 13856285 := bstep (se 3 (by rfl) ⟨2598053, by rfl⟩ : syracuseStep 13856285 = 5196107) B5196107
theorem B5475869 : Blo 1621009 5475869 := bstep (se 3 (by rfl) ⟨1026725, by rfl⟩ : syracuseStep 5475869 = 2053451) B2053451
theorem B3649067 : Blo 1621009 3649067 := bstep (se 1 (by rfl) ⟨2736800, by rfl⟩ : syracuseStep 3649067 = 5473601) B5473601
theorem B1039158989 : Blo 1621009 1039158989 := bstep (se 3 (by rfl) ⟨194842310, by rfl⟩ : syracuseStep 1039158989 = 389684621) B389684621
theorem B2051831 : Blo 1621009 2051831 := bstep (se 1 (by rfl) ⟨1538873, by rfl⟩ : syracuseStep 2051831 = 3077747) B3077747
theorem B24973057 : Blo 1621009 24973057 := bstep (se 2 (by rfl) ⟨9364896, by rfl⟩ : syracuseStep 24973057 = 18729793) B18729793
theorem B8318771 : Blo 1621009 8318771 := bstep (se 1 (by rfl) ⟨6239078, by rfl⟩ : syracuseStep 8318771 = 12478157) B12478157
theorem B9236339 : Blo 1621009 9236339 := bstep (se 1 (by rfl) ⟨6927254, by rfl⟩ : syracuseStep 9236339 = 13854509) B13854509
theorem B2051983 : Blo 1621009 2051983 := bstep (se 1 (by rfl) ⟨1538987, by rfl⟩ : syracuseStep 2051983 = 3077975) B3077975
theorem B3649427 : Blo 1621009 3649427 := bstep (se 1 (by rfl) ⟨2737070, by rfl⟩ : syracuseStep 3649427 = 5474141) B5474141
theorem B46755737 : Blo 1621009 46755737 := bstep (se 2 (by rfl) ⟨17533401, by rfl⟩ : syracuseStep 46755737 = 35066803) B35066803
theorem B2772937 : Blo 1621009 2772937 := bstep (se 2 (by rfl) ⟨1039851, by rfl⟩ : syracuseStep 2772937 = 2079703) B2079703
theorem B3649481 : Blo 1621009 3649481 := bstep (se 2 (by rfl) ⟨1368555, by rfl⟩ : syracuseStep 3649481 = 2737111) B2737111
theorem B8212427 : Blo 1621009 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B109555733 : Blo 1621009 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B2052155 : Blo 1621009 2052155 := bstep (se 1 (by rfl) ⟨1539116, by rfl⟩ : syracuseStep 2052155 = 3078233) B3078233
theorem B8212751 : Blo 1621009 8212751 := bstep (se 1 (by rfl) ⟨6159563, by rfl⟩ : syracuseStep 8212751 = 12319127) B12319127
theorem B4616507 : Blo 1621009 4616507 := bstep (se 1 (by rfl) ⟨3462380, by rfl⟩ : syracuseStep 4616507 = 6924761) B6924761
theorem B4616747 : Blo 1621009 4616747 := bstep (se 1 (by rfl) ⟨3462560, by rfl⟩ : syracuseStep 4616747 = 6925121) B6925121
theorem B3650183 : Blo 1621009 3650183 := bstep (se 1 (by rfl) ⟨2737637, by rfl⟩ : syracuseStep 3650183 = 5475275) B5475275
theorem B6927049 : Blo 1621009 6927049 := bstep (se 2 (by rfl) ⟨2597643, by rfl⟩ : syracuseStep 6927049 = 5195287) B5195287
theorem B3289801 : Blo 1621009 3289801 := bstep (se 2 (by rfl) ⟨1233675, by rfl⟩ : syracuseStep 3289801 = 2467351) B2467351
theorem B6927119 : Blo 1621009 6927119 := bstep (se 1 (by rfl) ⟨5195339, by rfl⟩ : syracuseStep 6927119 = 10390679) B10390679
theorem B3650363 : Blo 1621009 3650363 := bstep (se 1 (by rfl) ⟨2737772, by rfl⟩ : syracuseStep 3650363 = 5475545) B5475545
theorem B4682611 : Blo 1621009 4682611 := bstep (se 1 (by rfl) ⟨3511958, by rfl⟩ : syracuseStep 4682611 = 7023917) B7023917
theorem B2921363 : Blo 1621009 2921363 := bstep (se 1 (by rfl) ⟨2191022, by rfl⟩ : syracuseStep 2921363 = 4382045) B4382045
theorem B5477273 : Blo 1621009 5477273 := bstep (se 2 (by rfl) ⟨2053977, by rfl⟩ : syracuseStep 5477273 = 4107955) B4107955
theorem B8328089 : Blo 1621009 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B6157241 : Blo 1621009 6157241 := bstep (se 2 (by rfl) ⟨2308965, by rfl⟩ : syracuseStep 6157241 = 4617931) B4617931
theorem B3650489 : Blo 1621009 3650489 := bstep (se 2 (by rfl) ⟨1368933, by rfl⟩ : syracuseStep 3650489 = 2737867) B2737867
theorem B2634697 : Blo 1621009 2634697 := bstep (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) B1976023
theorem B1643527 : Blo 1621009 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B2053127 : Blo 1621009 2053127 := bstep (se 1 (by rfl) ⟨1539845, by rfl⟩ : syracuseStep 2053127 = 3079691) B3079691
theorem B5927947 : Blo 1621009 5927947 := bstep (se 1 (by rfl) ⟨4445960, by rfl⟩ : syracuseStep 5927947 = 8891921) B8891921
theorem B4682785 : Blo 1621009 4682785 := bstep (se 2 (by rfl) ⟨1756044, by rfl⟩ : syracuseStep 4682785 = 3512089) B3512089
theorem B13857925 : Blo 1621009 13857925 := bstep (se 4 (by rfl) ⟨1299180, by rfl⟩ : syracuseStep 13857925 = 2598361) B2598361
theorem B2192519 : Blo 1621009 2192519 := bstep (se 1 (by rfl) ⟨1644389, by rfl⟩ : syracuseStep 2192519 = 3288779) B3288779
theorem B49943789 : Blo 1621009 49943789 := bstep (se 3 (by rfl) ⟨9364460, by rfl⟩ : syracuseStep 49943789 = 18728921) B18728921
theorem B1824007 : Blo 1621009 1824007 := bstep (se 1 (by rfl) ⟨1368005, by rfl⟩ : syracuseStep 1824007 = 2736011) B2736011
theorem B3650831 : Blo 1621009 3650831 := bstep (se 1 (by rfl) ⟨2738123, by rfl⟩ : syracuseStep 3650831 = 5476247) B5476247
theorem B3650849 : Blo 1621009 3650849 := bstep (se 2 (by rfl) ⟨1369068, by rfl⟩ : syracuseStep 3650849 = 2738137) B2738137
theorem B9237797 : Blo 1621009 9237797 := bstep (se 4 (by rfl) ⟨866043, by rfl⟩ : syracuseStep 9237797 = 1732087) B1732087
theorem B1824187 : Blo 1621009 1824187 := bstep (se 1 (by rfl) ⟨1368140, by rfl⟩ : syracuseStep 1824187 = 2736281) B2736281
theorem B3462671 : Blo 1621009 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B3651191 : Blo 1621009 3651191 := bstep (se 1 (by rfl) ⟨2738393, by rfl⟩ : syracuseStep 3651191 = 5476787) B5476787
theorem B1644175 : Blo 1621009 1644175 := bstep (se 1 (by rfl) ⟨1233131, by rfl⟩ : syracuseStep 1644175 = 2466263) B2466263
theorem B2053775 : Blo 1621009 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B3462841 : Blo 1621009 3462841 := bstep (se 2 (by rfl) ⟨1298565, by rfl⟩ : syracuseStep 3462841 = 2597131) B2597131
theorem B8214209 : Blo 1621009 8214209 := bstep (se 2 (by rfl) ⟨3080328, by rfl⟩ : syracuseStep 8214209 = 6160657) B6160657
theorem B16652069 : Blo 1621009 16652069 := bstep (se 4 (by rfl) ⟨1561131, by rfl⟩ : syracuseStep 16652069 = 3122263) B3122263
theorem B3651371 : Blo 1621009 3651371 := bstep (se 1 (by rfl) ⟨2738528, by rfl⟩ : syracuseStep 3651371 = 5477057) B5477057
theorem B2193211 : Blo 1621009 2193211 := bstep (se 1 (by rfl) ⟨1644908, by rfl⟩ : syracuseStep 2193211 = 3289817) B3289817
theorem B1824655 : Blo 1621009 1824655 := bstep (se 1 (by rfl) ⟨1368491, by rfl⟩ : syracuseStep 1824655 = 2736983) B2736983
theorem B6158227 : Blo 1621009 6158227 := bstep (se 1 (by rfl) ⟨4618670, by rfl⟩ : syracuseStep 6158227 = 9237341) B9237341
theorem B4446137 : Blo 1621009 4446137 := bstep (se 2 (by rfl) ⟨1667301, by rfl⟩ : syracuseStep 4446137 = 3334603) B3334603
theorem B9238481 : Blo 1621009 9238481 := bstep (se 2 (by rfl) ⟨3464430, by rfl⟩ : syracuseStep 9238481 = 6928861) B6928861
theorem B3463183 : Blo 1621009 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B5552171 : Blo 1621009 5552171 := bstep (se 1 (by rfl) ⟨4164128, by rfl⟩ : syracuseStep 5552171 = 8328257) B8328257
theorem B3078263 : Blo 1621009 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B3651731 : Blo 1621009 3651731 := bstep (se 1 (by rfl) ⟨2738798, by rfl⟩ : syracuseStep 3651731 = 5477597) B5477597
theorem B3897611 : Blo 1621009 3897611 := bstep (se 1 (by rfl) ⟨2923208, by rfl⟩ : syracuseStep 3897611 = 5846417) B5846417
theorem B3078415 : Blo 1621009 3078415 := bstep (se 1 (by rfl) ⟨2308811, by rfl⟩ : syracuseStep 3078415 = 4617623) B4617623
theorem B9238799 : Blo 1621009 9238799 := bstep (se 1 (by rfl) ⟨6929099, by rfl⟩ : syracuseStep 9238799 = 13858199) B13858199
theorem B1825159 : Blo 1621009 1825159 := bstep (se 1 (by rfl) ⟨1368869, by rfl⟩ : syracuseStep 1825159 = 2737739) B2737739
theorem B16652729 : Blo 1621009 16652729 := bstep (se 2 (by rfl) ⟨6244773, by rfl⟩ : syracuseStep 16652729 = 12489547) B12489547
theorem B2431547 : Blo 1621009 2431547 := bstep (se 1 (by rfl) ⟨1823660, by rfl⟩ : syracuseStep 2431547 = 3647321) B3647321
theorem B1825339 : Blo 1621009 1825339 := bstep (se 1 (by rfl) ⟨1369004, by rfl⟩ : syracuseStep 1825339 = 2738009) B2738009
theorem B9132605 : Blo 1621009 9132605 := bstep (se 3 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 9132605 = 3424727) B3424727
theorem B7707197 : Blo 1621009 7707197 := bstep (se 3 (by rfl) ⟨1445099, by rfl⟩ : syracuseStep 7707197 = 2890199) B2890199
theorem B2431607 : Blo 1621009 2431607 := bstep (se 1 (by rfl) ⟨1823705, by rfl⟩ : syracuseStep 2431607 = 3647411) B3647411
theorem B2431631 : Blo 1621009 2431631 := bstep (se 1 (by rfl) ⟨1823723, by rfl⟩ : syracuseStep 2431631 = 3647447) B3647447
theorem B3078803 : Blo 1621009 3078803 := bstep (se 1 (by rfl) ⟨2309102, by rfl⟩ : syracuseStep 3078803 = 4618205) B4618205
theorem B2431673 : Blo 1621009 2431673 := bstep (se 2 (by rfl) ⟨911877, by rfl⟩ : syracuseStep 2431673 = 1823755) B1823755
theorem B3119801 : Blo 1621009 3119801 := bstep (se 2 (by rfl) ⟨1169925, by rfl⟩ : syracuseStep 3119801 = 2339851) B2339851
theorem B2431751 : Blo 1621009 2431751 := bstep (se 1 (by rfl) ⟨1823813, by rfl⟩ : syracuseStep 2431751 = 3647627) B3647627
theorem B3119887 : Blo 1621009 3119887 := bstep (se 1 (by rfl) ⟨2339915, by rfl⟩ : syracuseStep 3119887 = 4679831) B4679831
theorem B5471009 : Blo 1621009 5471009 := bstep (se 2 (by rfl) ⟨2051628, by rfl⟩ : syracuseStep 5471009 = 4103257) B4103257
theorem B9870113 : Blo 1621009 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B2431787 : Blo 1621009 2431787 := bstep (se 1 (by rfl) ⟨1823840, by rfl⟩ : syracuseStep 2431787 = 3647681) B3647681
theorem B2431817 : Blo 1621009 2431817 := bstep (se 2 (by rfl) ⟨911931, by rfl⟩ : syracuseStep 2431817 = 1823863) B1823863
theorem B2431931 : Blo 1621009 2431931 := bstep (se 1 (by rfl) ⟨1823948, by rfl⟩ : syracuseStep 2431931 = 3647897) B3647897
theorem B8215505 : Blo 1621009 8215505 := bstep (se 2 (by rfl) ⟨3080814, by rfl⟩ : syracuseStep 8215505 = 6161629) B6161629
theorem B2431991 : Blo 1621009 2431991 := bstep (se 1 (by rfl) ⟨1823993, by rfl⟩ : syracuseStep 2431991 = 3647987) B3647987
theorem B2432015 : Blo 1621009 2432015 := bstep (se 1 (by rfl) ⟨1824011, by rfl⟩ : syracuseStep 2432015 = 3648023) B3648023
theorem B1825807 : Blo 1621009 1825807 := bstep (se 1 (by rfl) ⟨1369355, by rfl⟩ : syracuseStep 1825807 = 2738711) B2738711
theorem B4930589 : Blo 1621009 4930589 := bstep (se 3 (by rfl) ⟨924485, by rfl⟩ : syracuseStep 4930589 = 1848971) B1848971
theorem B2432057 : Blo 1621009 2432057 := bstep (se 2 (by rfl) ⟨912021, by rfl⟩ : syracuseStep 2432057 = 1824043) B1824043
theorem B1621051 : Blo 1621009 1621051 := bstep (se 1 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 1621051 = 2431577) B2431577
theorem B6929495 : Blo 1621009 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B2309239 : Blo 1621009 2309239 := bstep (se 1 (by rfl) ⟨1731929, by rfl⟩ : syracuseStep 2309239 = 3463859) B3463859
theorem B3464311 : Blo 1621009 3464311 := bstep (se 1 (by rfl) ⟨2598233, by rfl⟩ : syracuseStep 3464311 = 5196467) B5196467
theorem B1621127 : Blo 1621009 1621127 := bstep (se 1 (by rfl) ⟨1215845, by rfl⟩ : syracuseStep 1621127 = 2431691) B2431691
theorem B2432135 : Blo 1621009 2432135 := bstep (se 1 (by rfl) ⟨1824101, by rfl⟩ : syracuseStep 2432135 = 3648203) B3648203
theorem B1621135 : Blo 1621009 1621135 := bstep (se 1 (by rfl) ⟨1215851, by rfl⟩ : syracuseStep 1621135 = 2431703) B2431703
theorem B2432171 : Blo 1621009 2432171 := bstep (se 1 (by rfl) ⟨1824128, by rfl⟩ : syracuseStep 2432171 = 3648257) B3648257
theorem B1621179 : Blo 1621009 1621179 := bstep (se 1 (by rfl) ⟨1215884, by rfl⟩ : syracuseStep 1621179 = 2431769) B2431769
theorem B4103369 : Blo 1621009 4103369 := bstep (se 2 (by rfl) ⟨1538763, by rfl⟩ : syracuseStep 4103369 = 3077527) B3077527
theorem B2432201 : Blo 1621009 2432201 := bstep (se 2 (by rfl) ⟨912075, by rfl⟩ : syracuseStep 2432201 = 1824151) B1824151
theorem B1621255 : Blo 1621009 1621255 := bstep (se 1 (by rfl) ⟨1215941, by rfl⟩ : syracuseStep 1621255 = 2431883) B2431883
theorem B4381967 : Blo 1621009 4381967 := bstep (se 1 (by rfl) ⟨3286475, by rfl⟩ : syracuseStep 4381967 = 6572951) B6572951
theorem B1621263 : Blo 1621009 1621263 := bstep (se 1 (by rfl) ⟨1215947, by rfl⟩ : syracuseStep 1621263 = 2431895) B2431895
theorem B20774177 : Blo 1621009 20774177 := bstep (se 2 (by rfl) ⟨7790316, by rfl⟩ : syracuseStep 20774177 = 15580633) B15580633
theorem B1621307 : Blo 1621009 1621307 := bstep (se 1 (by rfl) ⟨1215980, by rfl⟩ : syracuseStep 1621307 = 2431961) B2431961
theorem B2432315 : Blo 1621009 2432315 := bstep (se 1 (by rfl) ⟨1824236, by rfl⟩ : syracuseStep 2432315 = 3648473) B3648473
theorem B5471603 : Blo 1621009 5471603 := bstep (se 1 (by rfl) ⟨4103702, by rfl⟩ : syracuseStep 5471603 = 8207405) B8207405
theorem B2432375 : Blo 1621009 2432375 := bstep (se 1 (by rfl) ⟨1824281, by rfl⟩ : syracuseStep 2432375 = 3648563) B3648563
theorem B1621383 : Blo 1621009 1621383 := bstep (se 1 (by rfl) ⟨1216037, by rfl⟩ : syracuseStep 1621383 = 2432075) B2432075
theorem B1621391 : Blo 1621009 1621391 := bstep (se 1 (by rfl) ⟨1216043, by rfl⟩ : syracuseStep 1621391 = 2432087) B2432087
theorem B2432399 : Blo 1621009 2432399 := bstep (se 1 (by rfl) ⟨1824299, by rfl⟩ : syracuseStep 2432399 = 3648599) B3648599
theorem B2735545 : Blo 1621009 2735545 := bstep (se 2 (by rfl) ⟨1025829, by rfl⟩ : syracuseStep 2735545 = 2051659) B2051659
theorem B2432441 : Blo 1621009 2432441 := bstep (se 2 (by rfl) ⟨912165, by rfl⟩ : syracuseStep 2432441 = 1824331) B1824331
theorem B1621435 : Blo 1621009 1621435 := bstep (se 1 (by rfl) ⟨1216076, by rfl⟩ : syracuseStep 1621435 = 2432153) B2432153
theorem B2309563 : Blo 1621009 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B35093969 : Blo 1621009 35093969 := bstep (se 2 (by rfl) ⟨13160238, by rfl⟩ : syracuseStep 35093969 = 26320477) B26320477
theorem B46759427 : Blo 1621009 46759427 := bstep (se 1 (by rfl) ⟨35069570, by rfl⟩ : syracuseStep 46759427 = 70139141) B70139141
theorem B1621511 : Blo 1621009 1621511 := bstep (se 1 (by rfl) ⟨1216133, by rfl⟩ : syracuseStep 1621511 = 2432267) B2432267
theorem B2432519 : Blo 1621009 2432519 := bstep (se 1 (by rfl) ⟨1824389, by rfl⟩ : syracuseStep 2432519 = 3648779) B3648779
theorem B1621519 : Blo 1621009 1621519 := bstep (se 1 (by rfl) ⟨1216139, by rfl⟩ : syracuseStep 1621519 = 2432279) B2432279
theorem B7798295 : Blo 1621009 7798295 := bstep (se 1 (by rfl) ⟨5848721, by rfl⟩ : syracuseStep 7798295 = 11697443) B11697443
theorem B4103723 : Blo 1621009 4103723 := bstep (se 1 (by rfl) ⟨3077792, by rfl⟩ : syracuseStep 4103723 = 6155585) B6155585
theorem B2432555 : Blo 1621009 2432555 := bstep (se 1 (by rfl) ⟨1824416, by rfl⟩ : syracuseStep 2432555 = 3648833) B3648833
theorem B5848619 : Blo 1621009 5848619 := bstep (se 1 (by rfl) ⟨4386464, by rfl⟩ : syracuseStep 5848619 = 8772929) B8772929
theorem B1621563 : Blo 1621009 1621563 := bstep (se 1 (by rfl) ⟨1216172, by rfl⟩ : syracuseStep 1621563 = 2432345) B2432345
theorem B2432585 : Blo 1621009 2432585 := bstep (se 2 (by rfl) ⟨912219, by rfl⟩ : syracuseStep 2432585 = 1824439) B1824439
theorem B6159959 : Blo 1621009 6159959 := bstep (se 1 (by rfl) ⟨4619969, by rfl⟩ : syracuseStep 6159959 = 9239939) B9239939
theorem B1621639 : Blo 1621009 1621639 := bstep (se 1 (by rfl) ⟨1216229, by rfl⟩ : syracuseStep 1621639 = 2432459) B2432459
theorem B1621647 : Blo 1621009 1621647 := bstep (se 1 (by rfl) ⟨1216235, by rfl⟩ : syracuseStep 1621647 = 2432471) B2432471
theorem B1621691 : Blo 1621009 1621691 := bstep (se 1 (by rfl) ⟨1216268, by rfl⟩ : syracuseStep 1621691 = 2432537) B2432537
theorem B2432699 : Blo 1621009 2432699 := bstep (se 1 (by rfl) ⟨1824524, by rfl⟩ : syracuseStep 2432699 = 3649049) B3649049
theorem B9240257 : Blo 1621009 9240257 := bstep (se 2 (by rfl) ⟨3465096, by rfl⟩ : syracuseStep 9240257 = 6930193) B6930193
theorem B2432759 : Blo 1621009 2432759 := bstep (se 1 (by rfl) ⟨1824569, by rfl⟩ : syracuseStep 2432759 = 3649139) B3649139
theorem B1621767 : Blo 1621009 1621767 := bstep (se 1 (by rfl) ⟨1216325, by rfl⟩ : syracuseStep 1621767 = 2432651) B2432651
theorem B1621775 : Blo 1621009 1621775 := bstep (se 1 (by rfl) ⟨1216331, by rfl⟩ : syracuseStep 1621775 = 2432663) B2432663
theorem B2432783 : Blo 1621009 2432783 := bstep (se 1 (by rfl) ⟨1824587, by rfl⟩ : syracuseStep 2432783 = 3649175) B3649175
theorem B13860659 : Blo 1621009 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B2432825 : Blo 1621009 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B1621819 : Blo 1621009 1621819 := bstep (se 1 (by rfl) ⟨1216364, by rfl⟩ : syracuseStep 1621819 = 2432729) B2432729
theorem B9232217 : Blo 1621009 9232217 := bstep (se 2 (by rfl) ⟨3462081, by rfl⟩ : syracuseStep 9232217 = 6924163) B6924163
theorem B7790471 : Blo 1621009 7790471 := bstep (se 1 (by rfl) ⟨5842853, by rfl⟩ : syracuseStep 7790471 = 11685707) B11685707
theorem B1621895 : Blo 1621009 1621895 := bstep (se 1 (by rfl) ⟨1216421, by rfl⟩ : syracuseStep 1621895 = 2432843) B2432843
theorem B2432903 : Blo 1621009 2432903 := bstep (se 1 (by rfl) ⟨1824677, by rfl⟩ : syracuseStep 2432903 = 3649355) B3649355
theorem B1621903 : Blo 1621009 1621903 := bstep (se 1 (by rfl) ⟨1216427, by rfl⟩ : syracuseStep 1621903 = 2432855) B2432855
theorem B2432939 : Blo 1621009 2432939 := bstep (se 1 (by rfl) ⟨1824704, by rfl⟩ : syracuseStep 2432939 = 3649409) B3649409
theorem B2310059 : Blo 1621009 2310059 := bstep (se 1 (by rfl) ⟨1732544, by rfl⟩ : syracuseStep 2310059 = 3465089) B3465089
theorem B1621947 : Blo 1621009 1621947 := bstep (se 1 (by rfl) ⟨1216460, by rfl⟩ : syracuseStep 1621947 = 2432921) B2432921
theorem B1949627 : Blo 1621009 1949627 := bstep (se 1 (by rfl) ⟨1462220, by rfl⟩ : syracuseStep 1949627 = 2924441) B2924441
theorem B2432969 : Blo 1621009 2432969 := bstep (se 2 (by rfl) ⟨912363, by rfl⟩ : syracuseStep 2432969 = 1824727) B1824727
theorem B1622055 : Blo 1621009 1622055 := bstep (se 1 (by rfl) ⟨1216541, by rfl⟩ : syracuseStep 1622055 = 2433083) B2433083
theorem B13148237 : Blo 1621009 13148237 := bstep (se 3 (by rfl) ⟨2465294, by rfl⟩ : syracuseStep 13148237 = 4930589) B4930589
theorem B1622095 : Blo 1621009 1622095 := bstep (se 1 (by rfl) ⟨1216571, by rfl⟩ : syracuseStep 1622095 = 2433143) B2433143
theorem B1622111 : Blo 1621009 1622111 := bstep (se 1 (by rfl) ⟨1216583, by rfl⟩ : syracuseStep 1622111 = 2433167) B2433167
theorem B1622139 : Blo 1621009 1622139 := bstep (se 1 (by rfl) ⟨1216604, by rfl⟩ : syracuseStep 1622139 = 2433209) B2433209
theorem B5472413 : Blo 1621009 5472413 := bstep (se 3 (by rfl) ⟨1026077, by rfl⟩ : syracuseStep 5472413 = 2052155) B2052155
theorem B1622191 : Blo 1621009 1622191 := bstep (se 1 (by rfl) ⟨1216643, by rfl⟩ : syracuseStep 1622191 = 2433287) B2433287
theorem B1622215 : Blo 1621009 1622215 := bstep (se 1 (by rfl) ⟨1216661, by rfl⟩ : syracuseStep 1622215 = 2433323) B2433323
theorem B1622235 : Blo 1621009 1622235 := bstep (se 1 (by rfl) ⟨1216676, by rfl⟩ : syracuseStep 1622235 = 2433353) B2433353
theorem B1622311 : Blo 1621009 1622311 := bstep (se 1 (by rfl) ⟨1216733, by rfl⟩ : syracuseStep 1622311 = 2433467) B2433467
theorem B8208701 : Blo 1621009 8208701 := bstep (se 3 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 8208701 = 3078263) B3078263
theorem B1622351 : Blo 1621009 1622351 := bstep (se 1 (by rfl) ⟨1216763, by rfl⟩ : syracuseStep 1622351 = 2433527) B2433527
theorem B1622367 : Blo 1621009 1622367 := bstep (se 1 (by rfl) ⟨1216775, by rfl⟩ : syracuseStep 1622367 = 2433551) B2433551
theorem B4104553 : Blo 1621009 4104553 := bstep (se 2 (by rfl) ⟨1539207, by rfl⟩ : syracuseStep 4104553 = 3078415) B3078415
theorem B1622395 : Blo 1621009 1622395 := bstep (se 1 (by rfl) ⟨1216796, by rfl⟩ : syracuseStep 1622395 = 2433593) B2433593
theorem B2433455 : Blo 1621009 2433455 := bstep (se 1 (by rfl) ⟨1825091, by rfl⟩ : syracuseStep 2433455 = 3650183) B3650183
theorem B1622447 : Blo 1621009 1622447 := bstep (se 1 (by rfl) ⟨1216835, by rfl⟩ : syracuseStep 1622447 = 2433671) B2433671
theorem B2736571 : Blo 1621009 2736571 := bstep (se 1 (by rfl) ⟨2052428, by rfl⟩ : syracuseStep 2736571 = 4104857) B4104857
theorem B1622471 : Blo 1621009 1622471 := bstep (se 1 (by rfl) ⟨1216853, by rfl⟩ : syracuseStep 1622471 = 2433707) B2433707
theorem B1622491 : Blo 1621009 1622491 := bstep (se 1 (by rfl) ⟨1216868, by rfl⟩ : syracuseStep 1622491 = 2433737) B2433737
theorem B2433545 : Blo 1621009 2433545 := bstep (se 2 (by rfl) ⟨912579, by rfl⟩ : syracuseStep 2433545 = 1825159) B1825159
theorem B2736679 : Blo 1621009 2736679 := bstep (se 1 (by rfl) ⟨2052509, by rfl⟩ : syracuseStep 2736679 = 4105019) B4105019
theorem B2433575 : Blo 1621009 2433575 := bstep (se 1 (by rfl) ⟨1825181, by rfl⟩ : syracuseStep 2433575 = 3650363) B3650363
theorem B1622567 : Blo 1621009 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B1622607 : Blo 1621009 1622607 := bstep (se 1 (by rfl) ⟨1216955, by rfl⟩ : syracuseStep 1622607 = 2433911) B2433911
theorem B1622623 : Blo 1621009 1622623 := bstep (se 1 (by rfl) ⟨1216967, by rfl⟩ : syracuseStep 1622623 = 2433935) B2433935
theorem B4104827 : Blo 1621009 4104827 := bstep (se 1 (by rfl) ⟨3078620, by rfl⟩ : syracuseStep 4104827 = 6157241) B6157241
theorem B2433659 : Blo 1621009 2433659 := bstep (se 1 (by rfl) ⟨1825244, by rfl⟩ : syracuseStep 2433659 = 3650489) B3650489
theorem B1622651 : Blo 1621009 1622651 := bstep (se 1 (by rfl) ⟨1216988, by rfl⟩ : syracuseStep 1622651 = 2433977) B2433977
theorem B1622703 : Blo 1621009 1622703 := bstep (se 1 (by rfl) ⟨1217027, by rfl⟩ : syracuseStep 1622703 = 2434055) B2434055
theorem B5472953 : Blo 1621009 5472953 := bstep (se 2 (by rfl) ⟨2052357, by rfl⟩ : syracuseStep 5472953 = 4104715) B4104715
theorem B1622727 : Blo 1621009 1622727 := bstep (se 1 (by rfl) ⟨1217045, by rfl⟩ : syracuseStep 1622727 = 2434091) B2434091
theorem B10978001 : Blo 1621009 10978001 := bstep (se 2 (by rfl) ⟨4116750, by rfl⟩ : syracuseStep 10978001 = 8233501) B8233501
theorem B1622747 : Blo 1621009 1622747 := bstep (se 1 (by rfl) ⟨1217060, by rfl⟩ : syracuseStep 1622747 = 2434121) B2434121
theorem B2433785 : Blo 1621009 2433785 := bstep (se 2 (by rfl) ⟨912669, by rfl⟩ : syracuseStep 2433785 = 1825339) B1825339
theorem B31187713 : Blo 1621009 31187713 := bstep (se 2 (by rfl) ⟨11695392, by rfl⟩ : syracuseStep 31187713 = 23390785) B23390785
theorem B1622823 : Blo 1621009 1622823 := bstep (se 1 (by rfl) ⟨1217117, by rfl⟩ : syracuseStep 1622823 = 2434235) B2434235
theorem B1622863 : Blo 1621009 1622863 := bstep (se 1 (by rfl) ⟨1217147, by rfl⟩ : syracuseStep 1622863 = 2434295) B2434295
theorem B2433887 : Blo 1621009 2433887 := bstep (se 1 (by rfl) ⟨1825415, by rfl⟩ : syracuseStep 2433887 = 3650831) B3650831
theorem B1622879 : Blo 1621009 1622879 := bstep (se 1 (by rfl) ⟨1217159, by rfl⟩ : syracuseStep 1622879 = 2434319) B2434319
theorem B2737003 : Blo 1621009 2737003 := bstep (se 1 (by rfl) ⟨2052752, by rfl⟩ : syracuseStep 2737003 = 4105505) B4105505
theorem B2433899 : Blo 1621009 2433899 := bstep (se 1 (by rfl) ⟨1825424, by rfl⟩ : syracuseStep 2433899 = 3650849) B3650849
theorem B1622907 : Blo 1621009 1622907 := bstep (se 1 (by rfl) ⟨1217180, by rfl⟩ : syracuseStep 1622907 = 2434361) B2434361
theorem B10388371 : Blo 1621009 10388371 := bstep (se 1 (by rfl) ⟨7791278, by rfl⟩ : syracuseStep 10388371 = 15582557) B15582557
theorem B1622959 : Blo 1621009 1622959 := bstep (se 1 (by rfl) ⟨1217219, by rfl⟩ : syracuseStep 1622959 = 2434439) B2434439
theorem B1622983 : Blo 1621009 1622983 := bstep (se 1 (by rfl) ⟨1217237, by rfl⟩ : syracuseStep 1622983 = 2434475) B2434475
theorem B1623003 : Blo 1621009 1623003 := bstep (se 1 (by rfl) ⟨1217252, by rfl⟩ : syracuseStep 1623003 = 2434505) B2434505
theorem B3081179 : Blo 1621009 3081179 := bstep (se 1 (by rfl) ⟨2310884, by rfl⟩ : syracuseStep 3081179 = 4621769) B4621769
theorem B2434127 : Blo 1621009 2434127 := bstep (se 1 (by rfl) ⟨1825595, by rfl⟩ : syracuseStep 2434127 = 3651191) B3651191
theorem B6243481 : Blo 1621009 6243481 := bstep (se 2 (by rfl) ⟨2341305, by rfl⟩ : syracuseStep 6243481 = 4682611) B4682611
theorem B11101379 : Blo 1621009 11101379 := bstep (se 1 (by rfl) ⟨8326034, by rfl⟩ : syracuseStep 11101379 = 16652069) B16652069
theorem B2434247 : Blo 1621009 2434247 := bstep (se 1 (by rfl) ⟨1825685, by rfl⟩ : syracuseStep 2434247 = 3651371) B3651371
theorem B5473547 : Blo 1621009 5473547 := bstep (se 1 (by rfl) ⟨4105160, by rfl⟩ : syracuseStep 5473547 = 8210321) B8210321
theorem B2434409 : Blo 1621009 2434409 := bstep (se 2 (by rfl) ⟨912903, by rfl⟩ : syracuseStep 2434409 = 1825807) B1825807
theorem B6243713 : Blo 1621009 6243713 := bstep (se 2 (by rfl) ⟨2341392, by rfl⟩ : syracuseStep 6243713 = 4682785) B4682785
theorem B2434487 : Blo 1621009 2434487 := bstep (se 1 (by rfl) ⟨1825865, by rfl⟩ : syracuseStep 2434487 = 3651731) B3651731
theorem B2598407 : Blo 1621009 2598407 := bstep (se 1 (by rfl) ⟨1948805, by rfl⟩ : syracuseStep 2598407 = 3897611) B3897611
theorem B5473817 : Blo 1621009 5473817 := bstep (se 2 (by rfl) ⟨2052681, by rfl⟩ : syracuseStep 5473817 = 4105363) B4105363
theorem B9995915 : Blo 1621009 9995915 := bstep (se 1 (by rfl) ⟨7496936, by rfl⟩ : syracuseStep 9995915 = 14993873) B14993873
theorem B6088403 : Blo 1621009 6088403 := bstep (se 1 (by rfl) ⟨4566302, by rfl⟩ : syracuseStep 6088403 = 9132605) B9132605
theorem B5138131 : Blo 1621009 5138131 := bstep (se 1 (by rfl) ⟨3853598, by rfl⟩ : syracuseStep 5138131 = 7707197) B7707197
theorem B3647339 : Blo 1621009 3647339 := bstep (se 1 (by rfl) ⟨2735504, by rfl⟩ : syracuseStep 3647339 = 5471009) B5471009
theorem B6580075 : Blo 1621009 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B2738063 : Blo 1621009 2738063 := bstep (se 1 (by rfl) ⟨2053547, by rfl⟩ : syracuseStep 2738063 = 4107095) B4107095
theorem B3647393 : Blo 1621009 3647393 := bstep (se 2 (by rfl) ⟨1367772, by rfl⟩ : syracuseStep 3647393 = 2735545) B2735545
theorem B2738299 : Blo 1621009 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B3647735 : Blo 1621009 3647735 := bstep (se 1 (by rfl) ⟨2735801, by rfl⟩ : syracuseStep 3647735 = 5471603) B5471603
theorem B31172951 : Blo 1621009 31172951 := bstep (se 1 (by rfl) ⟨23379713, by rfl⟩ : syracuseStep 31172951 = 46759427) B46759427
theorem B14051717 : Blo 1621009 14051717 := bstep (se 4 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 14051717 = 2634697) B2634697
theorem B4106639 : Blo 1621009 4106639 := bstep (se 1 (by rfl) ⟨3079979, by rfl⟩ : syracuseStep 4106639 = 6159959) B6159959
theorem B11856365 : Blo 1621009 11856365 := bstep (se 3 (by rfl) ⟨2223068, by rfl⟩ : syracuseStep 11856365 = 4446137) B4446137
theorem B8210969 : Blo 1621009 8210969 := bstep (se 2 (by rfl) ⟨3079113, by rfl⟩ : syracuseStep 8210969 = 6158227) B6158227
theorem B6154811 : Blo 1621009 6154811 := bstep (se 1 (by rfl) ⟨4616108, by rfl⟩ : syracuseStep 6154811 = 9232217) B9232217
theorem B3697249 : Blo 1621009 3697249 := bstep (se 2 (by rfl) ⟨1386468, by rfl⟩ : syracuseStep 3697249 = 2772937) B2772937
theorem B5474951 : Blo 1621009 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B12323501 : Blo 1621009 12323501 := bstep (se 3 (by rfl) ⟨2310656, by rfl⟩ : syracuseStep 12323501 = 4621313) B4621313
theorem B5475005 : Blo 1621009 5475005 := bstep (se 3 (by rfl) ⟨1026563, by rfl⟩ : syracuseStep 5475005 = 2053127) B2053127
theorem B4106963 : Blo 1621009 4106963 := bstep (se 1 (by rfl) ⟨3080222, by rfl⟩ : syracuseStep 4106963 = 6160445) B6160445
theorem B31615717 : Blo 1621009 31615717 := bstep (se 4 (by rfl) ⟨2963973, by rfl⟩ : syracuseStep 31615717 = 5927947) B5927947
theorem B3648329 : Blo 1621009 3648329 := bstep (se 2 (by rfl) ⟨1368123, by rfl⟩ : syracuseStep 3648329 = 2736247) B2736247
theorem B5925727 : Blo 1621009 5925727 := bstep (se 1 (by rfl) ⟨4444295, by rfl⟩ : syracuseStep 5925727 = 8888591) B8888591
theorem B5475167 : Blo 1621009 5475167 := bstep (se 1 (by rfl) ⟨4106375, by rfl⟩ : syracuseStep 5475167 = 8212751) B8212751
theorem B5475329 : Blo 1621009 5475329 := bstep (se 2 (by rfl) ⟨2053248, by rfl⟩ : syracuseStep 5475329 = 4106497) B4106497
theorem B2633033 : Blo 1621009 2633033 := bstep (se 2 (by rfl) ⟨987387, by rfl⟩ : syracuseStep 2633033 = 1974775) B1974775
theorem B33295859 : Blo 1621009 33295859 := bstep (se 1 (by rfl) ⟨24971894, by rfl⟩ : syracuseStep 33295859 = 49943789) B49943789
theorem B37957207 : Blo 1621009 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B9236065 : Blo 1621009 9236065 := bstep (se 2 (by rfl) ⟨3463524, by rfl⟩ : syracuseStep 9236065 = 6927049) B6927049
theorem B3649121 : Blo 1621009 3649121 := bstep (se 2 (by rfl) ⟨1368420, by rfl⟩ : syracuseStep 3649121 = 2736841) B2736841
theorem B4386401 : Blo 1621009 4386401 := bstep (se 2 (by rfl) ⟨1644900, by rfl⟩ : syracuseStep 4386401 = 3289801) B3289801
theorem B18468485 : Blo 1621009 18468485 := bstep (se 4 (by rfl) ⟨1731420, by rfl⟩ : syracuseStep 18468485 = 3462841) B3462841
theorem B5476139 : Blo 1621009 5476139 := bstep (se 1 (by rfl) ⟨4107104, by rfl⟩ : syracuseStep 5476139 = 8214209) B8214209
theorem B4616119 : Blo 1621009 4616119 := bstep (se 1 (by rfl) ⟨3462089, by rfl⟩ : syracuseStep 4616119 = 6924179) B6924179
theorem B3649463 : Blo 1621009 3649463 := bstep (se 1 (by rfl) ⟨2737097, by rfl⟩ : syracuseStep 3649463 = 5474195) B5474195
theorem B2191369 : Blo 1621009 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B5476409 : Blo 1621009 5476409 := bstep (se 2 (by rfl) ⟨2053653, by rfl⟩ : syracuseStep 5476409 = 4107307) B4107307
theorem B20795453 : Blo 1621009 20795453 := bstep (se 3 (by rfl) ⟨3899147, by rfl⟩ : syracuseStep 20795453 = 7798295) B7798295
theorem B18477233 : Blo 1621009 18477233 := bstep (se 2 (by rfl) ⟨6928962, by rfl⟩ : syracuseStep 18477233 = 13857925) B13857925
theorem B3895543 : Blo 1621009 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B5476733 : Blo 1621009 5476733 := bstep (se 3 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 5476733 = 2053775) B2053775
theorem B5845391 : Blo 1621009 5845391 := bstep (se 1 (by rfl) ⟨4384043, by rfl⟩ : syracuseStep 5845391 = 8768087) B8768087
theorem B2052535 : Blo 1621009 2052535 := bstep (se 1 (by rfl) ⟨1539401, by rfl⟩ : syracuseStep 2052535 = 3078803) B3078803
theorem B8319469 : Blo 1621009 8319469 := bstep (se 3 (by rfl) ⟨1559900, by rfl⟩ : syracuseStep 8319469 = 3119801) B3119801
theorem B3650057 : Blo 1621009 3650057 := bstep (se 2 (by rfl) ⟨1368771, by rfl⟩ : syracuseStep 3650057 = 2737543) B2737543
theorem B3699323 : Blo 1621009 3699323 := bstep (se 1 (by rfl) ⟨2774492, by rfl⟩ : syracuseStep 3699323 = 5548985) B5548985
theorem B5477003 : Blo 1621009 5477003 := bstep (se 1 (by rfl) ⟨4107752, by rfl⟩ : syracuseStep 5477003 = 8215505) B8215505
theorem B2921311 : Blo 1621009 2921311 := bstep (se 1 (by rfl) ⟨2190983, by rfl⟩ : syracuseStep 2921311 = 4381967) B4381967
theorem B3650399 : Blo 1621009 3650399 := bstep (se 1 (by rfl) ⟨2737799, by rfl⟩ : syracuseStep 3650399 = 5475599) B5475599
theorem B2192233 : Blo 1621009 2192233 := bstep (se 2 (by rfl) ⟨822087, by rfl⟩ : syracuseStep 2192233 = 1644175) B1644175
theorem B13849451 : Blo 1621009 13849451 := bstep (se 1 (by rfl) ⟨10387088, by rfl⟩ : syracuseStep 13849451 = 20774177) B20774177
theorem B12317669 : Blo 1621009 12317669 := bstep (se 4 (by rfl) ⟨1154781, by rfl⟩ : syracuseStep 12317669 = 2309563) B2309563
theorem B33297409 : Blo 1621009 33297409 := bstep (se 2 (by rfl) ⟨12486528, by rfl⟩ : syracuseStep 33297409 = 24973057) B24973057
theorem B9237523 : Blo 1621009 9237523 := bstep (se 1 (by rfl) ⟨6928142, by rfl⟩ : syracuseStep 9237523 = 13856285) B13856285
theorem B3650579 : Blo 1621009 3650579 := bstep (se 1 (by rfl) ⟨2737934, by rfl⟩ : syracuseStep 3650579 = 5475869) B5475869
theorem B5199005 : Blo 1621009 5199005 := bstep (se 3 (by rfl) ⟨974813, by rfl⟩ : syracuseStep 5199005 = 1949627) B1949627
theorem B6157559 : Blo 1621009 6157559 := bstep (se 1 (by rfl) ⟨4618169, by rfl⟩ : syracuseStep 6157559 = 9236339) B9236339
theorem B73037155 : Blo 1621009 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B4617577 : Blo 1621009 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B3650921 : Blo 1621009 3650921 := bstep (se 2 (by rfl) ⟨1369095, by rfl⟩ : syracuseStep 3650921 = 2738191) B2738191
theorem B8213885 : Blo 1621009 8213885 := bstep (se 3 (by rfl) ⟨1540103, by rfl⟩ : syracuseStep 8213885 = 3080207) B3080207
theorem B3077671 : Blo 1621009 3077671 := bstep (se 1 (by rfl) ⟨2308253, by rfl⟩ : syracuseStep 3077671 = 4616507) B4616507
theorem B1824295 : Blo 1621009 1824295 := bstep (se 1 (by rfl) ⟨1368221, by rfl⟩ : syracuseStep 1824295 = 2736443) B2736443
theorem B12490379 : Blo 1621009 12490379 := bstep (se 1 (by rfl) ⟨9367784, by rfl⟩ : syracuseStep 12490379 = 18735569) B18735569
theorem B5846717 : Blo 1621009 5846717 := bstep (se 3 (by rfl) ⟨1096259, by rfl⟩ : syracuseStep 5846717 = 2192519) B2192519
theorem B3077831 : Blo 1621009 3077831 := bstep (se 1 (by rfl) ⟨2308373, by rfl⟩ : syracuseStep 3077831 = 4616747) B4616747
theorem B2053831 : Blo 1621009 2053831 := bstep (se 1 (by rfl) ⟨1540373, by rfl⟩ : syracuseStep 2053831 = 3080747) B3080747
theorem B4216531 : Blo 1621009 4216531 := bstep (se 1 (by rfl) ⟨3162398, by rfl⟩ : syracuseStep 4216531 = 6324797) B6324797
theorem B4618079 : Blo 1621009 4618079 := bstep (se 1 (by rfl) ⟨3463559, by rfl⟩ : syracuseStep 4618079 = 6927119) B6927119
theorem B1947575 : Blo 1621009 1947575 := bstep (se 1 (by rfl) ⟨1460681, by rfl⟩ : syracuseStep 1947575 = 2921363) B2921363
theorem B3651515 : Blo 1621009 3651515 := bstep (se 1 (by rfl) ⟨2738636, by rfl⟩ : syracuseStep 3651515 = 5477273) B5477273
theorem B5552059 : Blo 1621009 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B3463175 : Blo 1621009 3463175 := bstep (se 1 (by rfl) ⟨2597381, by rfl⟩ : syracuseStep 3463175 = 5194763) B5194763
theorem B2308105 : Blo 1621009 2308105 := bstep (se 2 (by rfl) ⟨865539, by rfl⟩ : syracuseStep 2308105 = 1731079) B1731079
theorem B3651641 : Blo 1621009 3651641 := bstep (se 2 (by rfl) ⟨1369365, by rfl⟩ : syracuseStep 3651641 = 2738731) B2738731
theorem B4618397 : Blo 1621009 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B6158531 : Blo 1621009 6158531 := bstep (se 1 (by rfl) ⟨4618898, by rfl⟩ : syracuseStep 6158531 = 9237797) B9237797
theorem B2308447 : Blo 1621009 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B4159849 : Blo 1621009 4159849 := bstep (se 2 (by rfl) ⟨1559943, by rfl⟩ : syracuseStep 4159849 = 3119887) B3119887
theorem B44407277 : Blo 1621009 44407277 := bstep (se 3 (by rfl) ⟨8326364, by rfl⟩ : syracuseStep 44407277 = 16652729) B16652729
theorem B3332687 : Blo 1621009 3332687 := bstep (se 1 (by rfl) ⟨2499515, by rfl⟩ : syracuseStep 3332687 = 4999031) B4999031
theorem B6158987 : Blo 1621009 6158987 := bstep (se 1 (by rfl) ⟨4619240, by rfl⟩ : syracuseStep 6158987 = 9238481) B9238481
theorem B3701447 : Blo 1621009 3701447 := bstep (se 1 (by rfl) ⟨2776085, by rfl⟩ : syracuseStep 3701447 = 5552171) B5552171
theorem B15596317 : Blo 1621009 15596317 := bstep (se 3 (by rfl) ⟨2924309, by rfl⟩ : syracuseStep 15596317 = 5848619) B5848619
theorem B3078985 : Blo 1621009 3078985 := bstep (se 2 (by rfl) ⟨1154619, by rfl⟩ : syracuseStep 3078985 = 2309239) B2309239
theorem B4619081 : Blo 1621009 4619081 := bstep (se 2 (by rfl) ⟨1732155, by rfl⟩ : syracuseStep 4619081 = 3464311) B3464311
theorem B6159199 : Blo 1621009 6159199 := bstep (se 1 (by rfl) ⟨4619399, by rfl⟩ : syracuseStep 6159199 = 9238799) B9238799
theorem B2431919 : Blo 1621009 2431919 := bstep (se 1 (by rfl) ⟨1823939, by rfl⟩ : syracuseStep 2431919 = 3647879) B3647879
theorem B5626799 : Blo 1621009 5626799 := bstep (se 1 (by rfl) ⟨4220099, by rfl⟩ : syracuseStep 5626799 = 8440199) B8440199
theorem B2432009 : Blo 1621009 2432009 := bstep (se 2 (by rfl) ⟨912003, by rfl⟩ : syracuseStep 2432009 = 1824007) B1824007
theorem B1621031 : Blo 1621009 1621031 := bstep (se 1 (by rfl) ⟨1215773, by rfl⟩ : syracuseStep 1621031 = 2431547) B2431547
theorem B2432039 : Blo 1621009 2432039 := bstep (se 1 (by rfl) ⟨1824029, by rfl⟩ : syracuseStep 2432039 = 3648059) B3648059
theorem B10394675 : Blo 1621009 10394675 := bstep (se 1 (by rfl) ⟨7796006, by rfl⟩ : syracuseStep 10394675 = 15592013) B15592013
theorem B1621071 : Blo 1621009 1621071 := bstep (se 1 (by rfl) ⟨1215803, by rfl⟩ : syracuseStep 1621071 = 2431607) B2431607
theorem B1621087 : Blo 1621009 1621087 := bstep (se 1 (by rfl) ⟨1215815, by rfl⟩ : syracuseStep 1621087 = 2431631) B2431631
theorem B1621115 : Blo 1621009 1621115 := bstep (se 1 (by rfl) ⟨1215836, by rfl⟩ : syracuseStep 1621115 = 2431673) B2431673
theorem B2432123 : Blo 1621009 2432123 := bstep (se 1 (by rfl) ⟨1824092, by rfl⟩ : syracuseStep 2432123 = 3648185) B3648185
theorem B3464363 : Blo 1621009 3464363 := bstep (se 1 (by rfl) ⟨2598272, by rfl⟩ : syracuseStep 3464363 = 5196545) B5196545
theorem B1621167 : Blo 1621009 1621167 := bstep (se 1 (by rfl) ⟨1215875, by rfl⟩ : syracuseStep 1621167 = 2431751) B2431751
theorem B1621191 : Blo 1621009 1621191 := bstep (se 1 (by rfl) ⟨1215893, by rfl⟩ : syracuseStep 1621191 = 2431787) B2431787
theorem B1621211 : Blo 1621009 1621211 := bstep (se 1 (by rfl) ⟨1215908, by rfl⟩ : syracuseStep 1621211 = 2431817) B2431817
theorem B2432249 : Blo 1621009 2432249 := bstep (se 2 (by rfl) ⟨912093, by rfl⟩ : syracuseStep 2432249 = 1824187) B1824187
theorem B1621287 : Blo 1621009 1621287 := bstep (se 1 (by rfl) ⟨1215965, by rfl⟩ : syracuseStep 1621287 = 2431931) B2431931
theorem B5471549 : Blo 1621009 5471549 := bstep (se 3 (by rfl) ⟨1025915, by rfl⟩ : syracuseStep 5471549 = 2051831) B2051831
theorem B1621327 : Blo 1621009 1621327 := bstep (se 1 (by rfl) ⟨1215995, by rfl⟩ : syracuseStep 1621327 = 2431991) B2431991
theorem B1621343 : Blo 1621009 1621343 := bstep (se 1 (by rfl) ⟨1216007, by rfl⟩ : syracuseStep 1621343 = 2432015) B2432015
theorem B2432351 : Blo 1621009 2432351 := bstep (se 1 (by rfl) ⟨1824263, by rfl⟩ : syracuseStep 2432351 = 3648527) B3648527
theorem B2432363 : Blo 1621009 2432363 := bstep (se 1 (by rfl) ⟨1824272, by rfl⟩ : syracuseStep 2432363 = 3648545) B3648545
theorem B1621371 : Blo 1621009 1621371 := bstep (se 1 (by rfl) ⟨1216028, by rfl⟩ : syracuseStep 1621371 = 2432057) B2432057
theorem B41557373 : Blo 1621009 41557373 := bstep (se 3 (by rfl) ⟨7792007, by rfl⟩ : syracuseStep 41557373 = 15584015) B15584015
theorem B26303869 : Blo 1621009 26303869 := bstep (se 3 (by rfl) ⟨4931975, by rfl⟩ : syracuseStep 26303869 = 9863951) B9863951
theorem B4619663 : Blo 1621009 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B1621423 : Blo 1621009 1621423 := bstep (se 1 (by rfl) ⟨1216067, by rfl⟩ : syracuseStep 1621423 = 2432135) B2432135
theorem B1621447 : Blo 1621009 1621447 := bstep (se 1 (by rfl) ⟨1216085, by rfl⟩ : syracuseStep 1621447 = 2432171) B2432171
theorem B2735579 : Blo 1621009 2735579 := bstep (se 1 (by rfl) ⟨2051684, by rfl⟩ : syracuseStep 2735579 = 4103369) B4103369
theorem B1621467 : Blo 1621009 1621467 := bstep (se 1 (by rfl) ⟨1216100, by rfl⟩ : syracuseStep 1621467 = 2432201) B2432201
theorem B1621543 : Blo 1621009 1621543 := bstep (se 1 (by rfl) ⟨1216157, by rfl⟩ : syracuseStep 1621543 = 2432315) B2432315
theorem B1621583 : Blo 1621009 1621583 := bstep (se 1 (by rfl) ⟨1216187, by rfl⟩ : syracuseStep 1621583 = 2432375) B2432375
theorem B2432591 : Blo 1621009 2432591 := bstep (se 1 (by rfl) ⟨1824443, by rfl⟩ : syracuseStep 2432591 = 3648887) B3648887
theorem B1621599 : Blo 1621009 1621599 := bstep (se 1 (by rfl) ⟨1216199, by rfl⟩ : syracuseStep 1621599 = 2432399) B2432399
theorem B1621627 : Blo 1621009 1621627 := bstep (se 1 (by rfl) ⟨1216220, by rfl⟩ : syracuseStep 1621627 = 2432441) B2432441
theorem B23395979 : Blo 1621009 23395979 := bstep (se 1 (by rfl) ⟨17546984, by rfl⟩ : syracuseStep 23395979 = 35093969) B35093969
theorem B1621679 : Blo 1621009 1621679 := bstep (se 1 (by rfl) ⟨1216259, by rfl⟩ : syracuseStep 1621679 = 2432519) B2432519
theorem B2735815 : Blo 1621009 2735815 := bstep (se 1 (by rfl) ⟨2051861, by rfl⟩ : syracuseStep 2735815 = 4103723) B4103723
theorem B1621703 : Blo 1621009 1621703 := bstep (se 1 (by rfl) ⟨1216277, by rfl⟩ : syracuseStep 1621703 = 2432555) B2432555
theorem B2432711 : Blo 1621009 2432711 := bstep (se 1 (by rfl) ⟨1824533, by rfl⟩ : syracuseStep 2432711 = 3649067) B3649067
theorem B1621723 : Blo 1621009 1621723 := bstep (se 1 (by rfl) ⟨1216292, by rfl⟩ : syracuseStep 1621723 = 2432585) B2432585
theorem B2924281 : Blo 1621009 2924281 := bstep (se 2 (by rfl) ⟨1096605, by rfl⟩ : syracuseStep 2924281 = 2193211) B2193211
theorem B6160157 : Blo 1621009 6160157 := bstep (se 3 (by rfl) ⟨1155029, by rfl⟩ : syracuseStep 6160157 = 2310059) B2310059
theorem B1621799 : Blo 1621009 1621799 := bstep (se 1 (by rfl) ⟨1216349, by rfl⟩ : syracuseStep 1621799 = 2432699) B2432699
theorem B6160171 : Blo 1621009 6160171 := bstep (se 1 (by rfl) ⟨4620128, by rfl⟩ : syracuseStep 6160171 = 9240257) B9240257
theorem B692772659 : Blo 1621009 692772659 := bstep (se 1 (by rfl) ⟨519579494, by rfl⟩ : syracuseStep 692772659 = 1039158989) B1039158989
theorem B1621839 : Blo 1621009 1621839 := bstep (se 1 (by rfl) ⟨1216379, by rfl⟩ : syracuseStep 1621839 = 2432759) B2432759
theorem B1621855 : Blo 1621009 1621855 := bstep (se 1 (by rfl) ⟨1216391, by rfl⟩ : syracuseStep 1621855 = 2432783) B2432783
theorem B2735977 : Blo 1621009 2735977 := bstep (se 2 (by rfl) ⟨1025991, by rfl⟩ : syracuseStep 2735977 = 2051983) B2051983
theorem B2432873 : Blo 1621009 2432873 := bstep (se 2 (by rfl) ⟨912327, by rfl⟩ : syracuseStep 2432873 = 1824655) B1824655
theorem B5545847 : Blo 1621009 5545847 := bstep (se 1 (by rfl) ⟨4159385, by rfl⟩ : syracuseStep 5545847 = 8318771) B8318771
theorem B9240439 : Blo 1621009 9240439 := bstep (se 1 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 9240439 = 13860659) B13860659
theorem B1621883 : Blo 1621009 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B5193647 : Blo 1621009 5193647 := bstep (se 1 (by rfl) ⟨3895235, by rfl⟩ : syracuseStep 5193647 = 7790471) B7790471
theorem B1621935 : Blo 1621009 1621935 := bstep (se 1 (by rfl) ⟨1216451, by rfl⟩ : syracuseStep 1621935 = 2432903) B2432903
theorem B2432951 : Blo 1621009 2432951 := bstep (se 1 (by rfl) ⟨1824713, by rfl⟩ : syracuseStep 2432951 = 3649427) B3649427
theorem B31170491 : Blo 1621009 31170491 := bstep (se 1 (by rfl) ⟨23377868, by rfl⟩ : syracuseStep 31170491 = 46755737) B46755737
theorem B1621959 : Blo 1621009 1621959 := bstep (se 1 (by rfl) ⟨1216469, by rfl⟩ : syracuseStep 1621959 = 2432939) B2432939
theorem B1621979 : Blo 1621009 1621979 := bstep (se 1 (by rfl) ⟨1216484, by rfl⟩ : syracuseStep 1621979 = 2432969) B2432969
theorem B2432987 : Blo 1621009 2432987 := bstep (se 1 (by rfl) ⟨1824740, by rfl⟩ : syracuseStep 2432987 = 3649481) B3649481
theorem B8765491 : Blo 1621009 8765491 := bstep (se 1 (by rfl) ⟨6574118, by rfl⟩ : syracuseStep 8765491 = 13148237) B13148237
theorem B5472467 : Blo 1621009 5472467 := bstep (se 1 (by rfl) ⟨4104350, by rfl⟩ : syracuseStep 5472467 = 8208701) B8208701
theorem B1622303 : Blo 1621009 1622303 := bstep (se 1 (by rfl) ⟨1216727, by rfl⟩ : syracuseStep 1622303 = 2433455) B2433455
theorem B5194057 : Blo 1621009 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B2433371 : Blo 1621009 2433371 := bstep (se 1 (by rfl) ⟨1825028, by rfl⟩ : syracuseStep 2433371 = 3650057) B3650057
theorem B1622363 : Blo 1621009 1622363 := bstep (se 1 (by rfl) ⟨1216772, by rfl⟩ : syracuseStep 1622363 = 2433545) B2433545
theorem B1622383 : Blo 1621009 1622383 := bstep (se 1 (by rfl) ⟨1216787, by rfl⟩ : syracuseStep 1622383 = 2433575) B2433575
theorem B2736551 : Blo 1621009 2736551 := bstep (se 1 (by rfl) ⟨2052413, by rfl⟩ : syracuseStep 2736551 = 4104827) B4104827
theorem B2466215 : Blo 1621009 2466215 := bstep (se 1 (by rfl) ⟨1849661, by rfl⟩ : syracuseStep 2466215 = 3699323) B3699323
theorem B1622439 : Blo 1621009 1622439 := bstep (se 1 (by rfl) ⟨1216829, by rfl⟩ : syracuseStep 1622439 = 2433659) B2433659
theorem B5546465 : Blo 1621009 5546465 := bstep (se 2 (by rfl) ⟨2079924, by rfl⟩ : syracuseStep 5546465 = 4159849) B4159849
theorem B5472737 : Blo 1621009 5472737 := bstep (se 2 (by rfl) ⟨2052276, by rfl⟩ : syracuseStep 5472737 = 4104553) B4104553
theorem B1622523 : Blo 1621009 1622523 := bstep (se 1 (by rfl) ⟨1216892, by rfl⟩ : syracuseStep 1622523 = 2433785) B2433785
theorem B2433599 : Blo 1621009 2433599 := bstep (se 1 (by rfl) ⟨1825199, by rfl⟩ : syracuseStep 2433599 = 3650399) B3650399
theorem B1622591 : Blo 1621009 1622591 := bstep (se 1 (by rfl) ⟨1216943, by rfl⟩ : syracuseStep 1622591 = 2433887) B2433887
theorem B9232967 : Blo 1621009 9232967 := bstep (se 1 (by rfl) ⟨6924725, by rfl⟩ : syracuseStep 9232967 = 13849451) B13849451
theorem B1622599 : Blo 1621009 1622599 := bstep (se 1 (by rfl) ⟨1216949, by rfl⟩ : syracuseStep 1622599 = 2433899) B2433899
theorem B2736713 : Blo 1621009 2736713 := bstep (se 2 (by rfl) ⟨1026267, by rfl⟩ : syracuseStep 2736713 = 2052535) B2052535
theorem B11092625 : Blo 1621009 11092625 := bstep (se 2 (by rfl) ⟨4159734, by rfl⟩ : syracuseStep 11092625 = 8319469) B8319469
theorem B2433719 : Blo 1621009 2433719 := bstep (se 1 (by rfl) ⟨1825289, by rfl⟩ : syracuseStep 2433719 = 3650579) B3650579
theorem B1622751 : Blo 1621009 1622751 := bstep (se 1 (by rfl) ⟨1217063, by rfl⟩ : syracuseStep 1622751 = 2434127) B2434127
theorem B3466003 : Blo 1621009 3466003 := bstep (se 1 (by rfl) ⟨2599502, by rfl⟩ : syracuseStep 3466003 = 5199005) B5199005
theorem B1622831 : Blo 1621009 1622831 := bstep (se 1 (by rfl) ⟨1217123, by rfl⟩ : syracuseStep 1622831 = 2434247) B2434247
theorem B4105039 : Blo 1621009 4105039 := bstep (se 1 (by rfl) ⟨3078779, by rfl⟩ : syracuseStep 4105039 = 6157559) B6157559
theorem B7021421 : Blo 1621009 7021421 := bstep (se 3 (by rfl) ⟨1316516, by rfl⟩ : syracuseStep 7021421 = 2633033) B2633033
theorem B2433947 : Blo 1621009 2433947 := bstep (se 1 (by rfl) ⟨1825460, by rfl⟩ : syracuseStep 2433947 = 3650921) B3650921
theorem B1622939 : Blo 1621009 1622939 := bstep (se 1 (by rfl) ⟨1217204, by rfl⟩ : syracuseStep 1622939 = 2434409) B2434409
theorem B4162475 : Blo 1621009 4162475 := bstep (se 1 (by rfl) ⟨3121856, by rfl⟩ : syracuseStep 4162475 = 6243713) B6243713
theorem B1622991 : Blo 1621009 1622991 := bstep (se 1 (by rfl) ⟨1217243, by rfl⟩ : syracuseStep 1622991 = 2434487) B2434487
theorem B41583617 : Blo 1621009 41583617 := bstep (se 2 (by rfl) ⟨15593856, by rfl⟩ : syracuseStep 41583617 = 31187713) B31187713
theorem B4105313 : Blo 1621009 4105313 := bstep (se 2 (by rfl) ⟨1539492, by rfl⟩ : syracuseStep 4105313 = 3078985) B3078985
theorem B2434343 : Blo 1621009 2434343 := bstep (se 1 (by rfl) ⟨1825757, by rfl⟩ : syracuseStep 2434343 = 3651515) B3651515
theorem B2434427 : Blo 1621009 2434427 := bstep (se 1 (by rfl) ⟨1825820, by rfl⟩ : syracuseStep 2434427 = 3651641) B3651641
theorem B4105687 : Blo 1621009 4105687 := bstep (se 1 (by rfl) ⟨3079265, by rfl⟩ : syracuseStep 4105687 = 6158531) B6158531
theorem B8324641 : Blo 1621009 8324641 := bstep (se 2 (by rfl) ⟨3121740, by rfl⟩ : syracuseStep 8324641 = 6243481) B6243481
theorem B2737759 : Blo 1621009 2737759 := bstep (se 1 (by rfl) ⟨2053319, by rfl⟩ : syracuseStep 2737759 = 4106639) B4106639
theorem B5473979 : Blo 1621009 5473979 := bstep (se 1 (by rfl) ⟨4105484, by rfl⟩ : syracuseStep 5473979 = 8210969) B8210969
theorem B4105991 : Blo 1621009 4105991 := bstep (se 1 (by rfl) ⟨3079493, by rfl⟩ : syracuseStep 4105991 = 6158987) B6158987
theorem B2467631 : Blo 1621009 2467631 := bstep (se 1 (by rfl) ⟨1850723, by rfl⟩ : syracuseStep 2467631 = 3701447) B3701447
theorem B2737975 : Blo 1621009 2737975 := bstep (se 1 (by rfl) ⟨2053481, by rfl⟩ : syracuseStep 2737975 = 4106963) B4106963
theorem B35071825 : Blo 1621009 35071825 := bstep (se 2 (by rfl) ⟨13151934, by rfl⟩ : syracuseStep 35071825 = 26303869) B26303869
theorem B12314753 : Blo 1621009 12314753 := bstep (se 2 (by rfl) ⟨4618032, by rfl⟩ : syracuseStep 12314753 = 9236065) B9236065
theorem B3647699 : Blo 1621009 3647699 := bstep (se 1 (by rfl) ⟨2735774, by rfl⟩ : syracuseStep 3647699 = 5471549) B5471549
theorem B3647753 : Blo 1621009 3647753 := bstep (se 2 (by rfl) ⟨1367907, by rfl⟩ : syracuseStep 3647753 = 2735815) B2735815
theorem B2738441 : Blo 1621009 2738441 := bstep (se 2 (by rfl) ⟨1026915, by rfl⟩ : syracuseStep 2738441 = 2053831) B2053831
theorem B5622041 : Blo 1621009 5622041 := bstep (se 2 (by rfl) ⟨2108265, by rfl⟩ : syracuseStep 5622041 = 4216531) B4216531
theorem B6850841 : Blo 1621009 6850841 := bstep (se 2 (by rfl) ⟨2569065, by rfl⟩ : syracuseStep 6850841 = 5138131) B5138131
theorem B3647969 : Blo 1621009 3647969 := bstep (se 2 (by rfl) ⟨1367988, by rfl⟩ : syracuseStep 3647969 = 2735977) B2735977
theorem B4106771 : Blo 1621009 4106771 := bstep (se 1 (by rfl) ⟨3080078, by rfl⟩ : syracuseStep 4106771 = 6160157) B6160157
theorem B6154825 : Blo 1621009 6154825 := bstep (se 2 (by rfl) ⟨2308059, by rfl⟩ : syracuseStep 6154825 = 4616119) B4616119
theorem B3697231 : Blo 1621009 3697231 := bstep (se 1 (by rfl) ⟨2772923, by rfl⟩ : syracuseStep 3697231 = 5545847) B5545847
theorem B9235133 : Blo 1621009 9235133 := bstep (se 3 (by rfl) ⟨1731587, by rfl⟩ : syracuseStep 9235133 = 3463175) B3463175
theorem B13863635 : Blo 1621009 13863635 := bstep (se 1 (by rfl) ⟨10397726, by rfl⟩ : syracuseStep 13863635 = 20795453) B20795453
theorem B3648275 : Blo 1621009 3648275 := bstep (se 1 (by rfl) ⟨2736206, by rfl⟩ : syracuseStep 3648275 = 5472413) B5472413
theorem B12315725 : Blo 1621009 12315725 := bstep (se 3 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 12315725 = 4618397) B4618397
theorem B3648635 : Blo 1621009 3648635 := bstep (se 1 (by rfl) ⟨2736476, by rfl⟩ : syracuseStep 3648635 = 5472953) B5472953
theorem B7318667 : Blo 1621009 7318667 := bstep (se 1 (by rfl) ⟨5489000, by rfl⟩ : syracuseStep 7318667 = 10978001) B10978001
theorem B3648761 : Blo 1621009 3648761 := bstep (se 2 (by rfl) ⟨1368285, by rfl⟩ : syracuseStep 3648761 = 2736571) B2736571
theorem B8211779 : Blo 1621009 8211779 := bstep (se 1 (by rfl) ⟨6158834, by rfl⟩ : syracuseStep 8211779 = 12317669) B12317669
theorem B3648905 : Blo 1621009 3648905 := bstep (se 2 (by rfl) ⟨1368339, by rfl⟩ : syracuseStep 3648905 = 2736679) B2736679
theorem B3649031 : Blo 1621009 3649031 := bstep (se 1 (by rfl) ⟨2736773, by rfl⟩ : syracuseStep 3649031 = 5473547) B5473547
theorem B5475923 : Blo 1621009 5475923 := bstep (se 1 (by rfl) ⟨4106942, by rfl⟩ : syracuseStep 5475923 = 8213885) B8213885
theorem B1732271 : Blo 1621009 1732271 := bstep (se 1 (by rfl) ⟨1299203, by rfl⟩ : syracuseStep 1732271 = 2598407) B2598407
theorem B3649211 : Blo 1621009 3649211 := bstep (se 1 (by rfl) ⟨2736908, by rfl⟩ : syracuseStep 3649211 = 5473817) B5473817
theorem B20795089 : Blo 1621009 20795089 := bstep (se 2 (by rfl) ⟨7798158, by rfl⟩ : syracuseStep 20795089 = 15596317) B15596317
theorem B6663943 : Blo 1621009 6663943 := bstep (se 1 (by rfl) ⟨4997957, by rfl⟩ : syracuseStep 6663943 = 9995915) B9995915
theorem B8326919 : Blo 1621009 8326919 := bstep (se 1 (by rfl) ⟨6245189, by rfl⟩ : syracuseStep 8326919 = 12490379) B12490379
theorem B7900969 : Blo 1621009 7900969 := bstep (se 2 (by rfl) ⟨2962863, by rfl⟩ : syracuseStep 7900969 = 5925727) B5925727
theorem B8212265 : Blo 1621009 8212265 := bstep (se 2 (by rfl) ⟨3079599, by rfl⟩ : syracuseStep 8212265 = 6159199) B6159199
theorem B2051887 : Blo 1621009 2051887 := bstep (se 1 (by rfl) ⟨1538915, by rfl⟩ : syracuseStep 2051887 = 3077831) B3077831
theorem B3649337 : Blo 1621009 3649337 := bstep (se 2 (by rfl) ⟨1368501, by rfl⟩ : syracuseStep 3649337 = 2737003) B2737003
theorem B44396545 : Blo 1621009 44396545 := bstep (se 2 (by rfl) ⟨16648704, by rfl⟩ : syracuseStep 44396545 = 33297409) B33297409
theorem B12316697 : Blo 1621009 12316697 := bstep (se 2 (by rfl) ⟨4618761, by rfl⟩ : syracuseStep 12316697 = 9237523) B9237523
theorem B9367811 : Blo 1621009 9367811 := bstep (se 1 (by rfl) ⟨7025858, by rfl⟩ : syracuseStep 9367811 = 14051717) B14051717
theorem B3649967 : Blo 1621009 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B3650003 : Blo 1621009 3650003 := bstep (se 1 (by rfl) ⟨2737502, by rfl⟩ : syracuseStep 3650003 = 5475005) B5475005
theorem B97382873 : Blo 1621009 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B6156769 : Blo 1621009 6156769 := bstep (se 2 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 6156769 = 4617577) B4617577
theorem B3650111 : Blo 1621009 3650111 := bstep (se 1 (by rfl) ⟨2737583, by rfl⟩ : syracuseStep 3650111 = 5475167) B5475167
theorem B3650219 : Blo 1621009 3650219 := bstep (se 1 (by rfl) ⟨2737664, by rfl⟩ : syracuseStep 3650219 = 5475329) B5475329
theorem B1823719 : Blo 1621009 1823719 := bstep (se 1 (by rfl) ⟨1367789, by rfl⟩ : syracuseStep 1823719 = 2735579) B2735579
theorem B22197239 : Blo 1621009 22197239 := bstep (se 1 (by rfl) ⟨16647929, by rfl⟩ : syracuseStep 22197239 = 33295859) B33295859
theorem B8213561 : Blo 1621009 8213561 := bstep (se 2 (by rfl) ⟨3080085, by rfl⟩ : syracuseStep 8213561 = 6160171) B6160171
theorem B3650759 : Blo 1621009 3650759 := bstep (se 1 (by rfl) ⟨2738069, by rfl⟩ : syracuseStep 3650759 = 5476139) B5476139
theorem B7402745 : Blo 1621009 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B3462431 : Blo 1621009 3462431 := bstep (se 1 (by rfl) ⟨2596823, by rfl⟩ : syracuseStep 3462431 = 5193647) B5193647
theorem B20780327 : Blo 1621009 20780327 := bstep (se 1 (by rfl) ⟨15585245, by rfl⟩ : syracuseStep 20780327 = 31170491) B31170491
theorem B2921825 : Blo 1621009 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B3650939 : Blo 1621009 3650939 := bstep (se 1 (by rfl) ⟨2738204, by rfl⟩ : syracuseStep 3650939 = 5476409) B5476409
theorem B12309893 : Blo 1621009 12309893 := bstep (se 4 (by rfl) ⟨1154052, by rfl⟩ : syracuseStep 12309893 = 2308105) B2308105
theorem B12318155 : Blo 1621009 12318155 := bstep (se 1 (by rfl) ⟨9238616, by rfl⟩ : syracuseStep 12318155 = 18477233) B18477233
theorem B3651065 : Blo 1621009 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B3651155 : Blo 1621009 3651155 := bstep (se 1 (by rfl) ⟨2738366, by rfl⟩ : syracuseStep 3651155 = 5476733) B5476733
theorem B3896927 : Blo 1621009 3896927 := bstep (se 1 (by rfl) ⟨2922695, by rfl⟩ : syracuseStep 3896927 = 5845391) B5845391
theorem B3651335 : Blo 1621009 3651335 := bstep (se 1 (by rfl) ⟨2738501, by rfl⟩ : syracuseStep 3651335 = 5477003) B5477003
theorem B3077929 : Blo 1621009 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B29603677 : Blo 1621009 29603677 := bstep (se 3 (by rfl) ⟨5550689, by rfl⟩ : syracuseStep 29603677 = 11101379) B11101379
theorem B4929665 : Blo 1621009 4929665 := bstep (se 2 (by rfl) ⟨1848624, by rfl⟩ : syracuseStep 4929665 = 3697249) B3697249
theorem B42154289 : Blo 1621009 42154289 := bstep (se 2 (by rfl) ⟨15807858, by rfl⟩ : syracuseStep 42154289 = 31615717) B31615717
theorem B3897811 : Blo 1621009 3897811 := bstep (se 1 (by rfl) ⟨2923358, by rfl⟩ : syracuseStep 3897811 = 5846717) B5846717
theorem B2922977 : Blo 1621009 2922977 := bstep (se 2 (by rfl) ⟨1096116, by rfl⟩ : syracuseStep 2922977 = 2192233) B2192233
theorem B13851161 : Blo 1621009 13851161 := bstep (se 2 (by rfl) ⟨5194185, by rfl⟩ : syracuseStep 13851161 = 10388371) B10388371
theorem B3078719 : Blo 1621009 3078719 := bstep (se 1 (by rfl) ⟨2309039, by rfl⟩ : syracuseStep 3078719 = 4618079) B4618079
theorem B2431559 : Blo 1621009 2431559 := bstep (se 1 (by rfl) ⟨1823669, by rfl⟩ : syracuseStep 2431559 = 3647339) B3647339
theorem B1825375 : Blo 1621009 1825375 := bstep (se 1 (by rfl) ⟨1369031, by rfl⟩ : syracuseStep 1825375 = 2738063) B2738063
theorem B2431595 : Blo 1621009 2431595 := bstep (se 1 (by rfl) ⟨1823696, by rfl⟩ : syracuseStep 2431595 = 3647393) B3647393
theorem B15596165 : Blo 1621009 15596165 := bstep (se 4 (by rfl) ⟨1462140, by rfl⟩ : syracuseStep 15596165 = 2924281) B2924281
theorem B2431823 : Blo 1621009 2431823 := bstep (se 1 (by rfl) ⟨1823867, by rfl⟩ : syracuseStep 2431823 = 3647735) B3647735
theorem B8887165 : Blo 1621009 8887165 := bstep (se 3 (by rfl) ⟨1666343, by rfl⟩ : syracuseStep 8887165 = 3332687) B3332687
theorem B20781967 : Blo 1621009 20781967 := bstep (se 1 (by rfl) ⟨15586475, by rfl⟩ : syracuseStep 20781967 = 31172951) B31172951
theorem B29604851 : Blo 1621009 29604851 := bstep (se 1 (by rfl) ⟨22203638, by rfl⟩ : syracuseStep 29604851 = 44407277) B44407277
theorem B7904243 : Blo 1621009 7904243 := bstep (se 1 (by rfl) ⟨5928182, by rfl⟩ : syracuseStep 7904243 = 11856365) B11856365
theorem B4103207 : Blo 1621009 4103207 := bstep (se 1 (by rfl) ⟨3077405, by rfl⟩ : syracuseStep 4103207 = 6154811) B6154811
theorem B8215667 : Blo 1621009 8215667 := bstep (se 1 (by rfl) ⟨6161750, by rfl⟩ : syracuseStep 8215667 = 12323501) B12323501
theorem B15580325 : Blo 1621009 15580325 := bstep (se 4 (by rfl) ⟨1460655, by rfl⟩ : syracuseStep 15580325 = 2921311) B2921311
theorem B2432219 : Blo 1621009 2432219 := bstep (se 1 (by rfl) ⟨1824164, by rfl⟩ : syracuseStep 2432219 = 3648329) B3648329
theorem B16235741 : Blo 1621009 16235741 := bstep (se 3 (by rfl) ⟨3044201, by rfl⟩ : syracuseStep 16235741 = 6088403) B6088403
theorem B3079387 : Blo 1621009 3079387 := bstep (se 1 (by rfl) ⟨2309540, by rfl⟩ : syracuseStep 3079387 = 4619081) B4619081
theorem B1621279 : Blo 1621009 1621279 := bstep (se 1 (by rfl) ⟨1215959, by rfl⟩ : syracuseStep 1621279 = 2431919) B2431919
theorem B3751199 : Blo 1621009 3751199 := bstep (se 1 (by rfl) ⟨2813399, by rfl⟩ : syracuseStep 3751199 = 5626799) B5626799
theorem B1621339 : Blo 1621009 1621339 := bstep (se 1 (by rfl) ⟨1216004, by rfl⟩ : syracuseStep 1621339 = 2432009) B2432009
theorem B1621359 : Blo 1621009 1621359 := bstep (se 1 (by rfl) ⟨1216019, by rfl⟩ : syracuseStep 1621359 = 2432039) B2432039
theorem B6929783 : Blo 1621009 6929783 := bstep (se 1 (by rfl) ⟨5197337, by rfl⟩ : syracuseStep 6929783 = 10394675) B10394675
theorem B4103561 : Blo 1621009 4103561 := bstep (se 2 (by rfl) ⟨1538835, by rfl⟩ : syracuseStep 4103561 = 3077671) B3077671
theorem B2432393 : Blo 1621009 2432393 := bstep (se 2 (by rfl) ⟨912147, by rfl⟩ : syracuseStep 2432393 = 1824295) B1824295
theorem B1621415 : Blo 1621009 1621415 := bstep (se 1 (by rfl) ⟨1216061, by rfl⟩ : syracuseStep 1621415 = 2432123) B2432123
theorem B2309575 : Blo 1621009 2309575 := bstep (se 1 (by rfl) ⟨1732181, by rfl⟩ : syracuseStep 2309575 = 3464363) B3464363
theorem B50609609 : Blo 1621009 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B1621499 : Blo 1621009 1621499 := bstep (se 1 (by rfl) ⟨1216124, by rfl⟩ : syracuseStep 1621499 = 2432249) B2432249
theorem B1621567 : Blo 1621009 1621567 := bstep (se 1 (by rfl) ⟨1216175, by rfl⟩ : syracuseStep 1621567 = 2432351) B2432351
theorem B1621575 : Blo 1621009 1621575 := bstep (se 1 (by rfl) ⟨1216181, by rfl⟩ : syracuseStep 1621575 = 2432363) B2432363
theorem B27704915 : Blo 1621009 27704915 := bstep (se 1 (by rfl) ⟨20778686, by rfl⟩ : syracuseStep 27704915 = 41557373) B41557373
theorem B3079775 : Blo 1621009 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B1621727 : Blo 1621009 1621727 := bstep (se 1 (by rfl) ⟨1216295, by rfl⟩ : syracuseStep 1621727 = 2432591) B2432591
theorem B2432747 : Blo 1621009 2432747 := bstep (se 1 (by rfl) ⟨1824560, by rfl⟩ : syracuseStep 2432747 = 3649121) B3649121
theorem B2924267 : Blo 1621009 2924267 := bstep (se 1 (by rfl) ⟨2193200, by rfl⟩ : syracuseStep 2924267 = 4386401) B4386401
theorem B12312323 : Blo 1621009 12312323 := bstep (se 1 (by rfl) ⟨9234242, by rfl⟩ : syracuseStep 12312323 = 18468485) B18468485
theorem B15597319 : Blo 1621009 15597319 := bstep (se 1 (by rfl) ⟨11697989, by rfl⟩ : syracuseStep 15597319 = 23395979) B23395979
theorem B1621807 : Blo 1621009 1621807 := bstep (se 1 (by rfl) ⟨1216355, by rfl⟩ : syracuseStep 1621807 = 2432711) B2432711
theorem B8773433 : Blo 1621009 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B5193533 : Blo 1621009 5193533 := bstep (se 3 (by rfl) ⟨973787, by rfl⟩ : syracuseStep 5193533 = 1947575) B1947575
theorem B12320585 : Blo 1621009 12320585 := bstep (se 2 (by rfl) ⟨4620219, by rfl⟩ : syracuseStep 12320585 = 9240439) B9240439
theorem B461848439 : Blo 1621009 461848439 := bstep (se 1 (by rfl) ⟨346386329, by rfl⟩ : syracuseStep 461848439 = 692772659) B692772659
theorem B1621915 : Blo 1621009 1621915 := bstep (se 1 (by rfl) ⟨1216436, by rfl⟩ : syracuseStep 1621915 = 2432873) B2432873
theorem B8216477 : Blo 1621009 8216477 := bstep (se 3 (by rfl) ⟨1540589, by rfl⟩ : syracuseStep 8216477 = 3081179) B3081179
theorem B1621967 : Blo 1621009 1621967 := bstep (se 1 (by rfl) ⟨1216475, by rfl⟩ : syracuseStep 1621967 = 2432951) B2432951
theorem B2432975 : Blo 1621009 2432975 := bstep (se 1 (by rfl) ⟨1824731, by rfl⟩ : syracuseStep 2432975 = 3649463) B3649463
theorem B1621991 : Blo 1621009 1621991 := bstep (se 1 (by rfl) ⟨1216493, by rfl⟩ : syracuseStep 1621991 = 2432987) B2432987
theorem B59195393 : Blo 1621009 59195393 := bstep (se 2 (by rfl) ⟨22198272, by rfl⟩ : syracuseStep 59195393 = 44396545) B44396545
theorem B1622247 : Blo 1621009 1622247 := bstep (se 1 (by rfl) ⟨1216685, by rfl⟩ : syracuseStep 1622247 = 2433371) B2433371
theorem B2433311 : Blo 1621009 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B2433335 : Blo 1621009 2433335 := bstep (se 1 (by rfl) ⟨1825001, by rfl⟩ : syracuseStep 2433335 = 3650003) B3650003
theorem B64921915 : Blo 1621009 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B2433407 : Blo 1621009 2433407 := bstep (se 1 (by rfl) ⟨1825055, by rfl⟩ : syracuseStep 2433407 = 3650111) B3650111
theorem B1622399 : Blo 1621009 1622399 := bstep (se 1 (by rfl) ⟨1216799, by rfl⟩ : syracuseStep 1622399 = 2433599) B2433599
theorem B2433479 : Blo 1621009 2433479 := bstep (se 1 (by rfl) ⟨1825109, by rfl⟩ : syracuseStep 2433479 = 3650219) B3650219
theorem B1622479 : Blo 1621009 1622479 := bstep (se 1 (by rfl) ⟨1216859, by rfl⟩ : syracuseStep 1622479 = 2433719) B2433719
theorem B43295309 : Blo 1621009 43295309 := bstep (se 3 (by rfl) ⟨8117870, by rfl⟩ : syracuseStep 43295309 = 16235741) B16235741
theorem B1622631 : Blo 1621009 1622631 := bstep (se 1 (by rfl) ⟨1216973, by rfl⟩ : syracuseStep 1622631 = 2433947) B2433947
theorem B8209025 : Blo 1621009 8209025 := bstep (se 2 (by rfl) ⟨3078384, by rfl⟩ : syracuseStep 8209025 = 6156769) B6156769
theorem B27722411 : Blo 1621009 27722411 := bstep (se 1 (by rfl) ⟨20791808, by rfl⟩ : syracuseStep 27722411 = 41583617) B41583617
theorem B2736875 : Blo 1621009 2736875 := bstep (se 1 (by rfl) ⟨2052656, by rfl⟩ : syracuseStep 2736875 = 4105313) B4105313
theorem B18268909 : Blo 1621009 18268909 := bstep (se 3 (by rfl) ⟨3425420, by rfl⟩ : syracuseStep 18268909 = 6850841) B6850841
theorem B9233149 : Blo 1621009 9233149 := bstep (se 3 (by rfl) ⟨1731215, by rfl⟩ : syracuseStep 9233149 = 3462431) B3462431
theorem B2433833 : Blo 1621009 2433833 := bstep (se 2 (by rfl) ⟨912687, by rfl⟩ : syracuseStep 2433833 = 1825375) B1825375
theorem B2433839 : Blo 1621009 2433839 := bstep (se 1 (by rfl) ⟨1825379, by rfl⟩ : syracuseStep 2433839 = 3650759) B3650759
theorem B13853551 : Blo 1621009 13853551 := bstep (se 1 (by rfl) ⟨10390163, by rfl⟩ : syracuseStep 13853551 = 20780327) B20780327
theorem B1622895 : Blo 1621009 1622895 := bstep (se 1 (by rfl) ⟨1217171, by rfl⟩ : syracuseStep 1622895 = 2434343) B2434343
theorem B2433959 : Blo 1621009 2433959 := bstep (se 1 (by rfl) ⟨1825469, by rfl⟩ : syracuseStep 2433959 = 3650939) B3650939
theorem B1622951 : Blo 1621009 1622951 := bstep (se 1 (by rfl) ⟨1217213, by rfl⟩ : syracuseStep 1622951 = 2434427) B2434427
theorem B2434043 : Blo 1621009 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B4621337 : Blo 1621009 4621337 := bstep (se 2 (by rfl) ⟨1733001, by rfl⟩ : syracuseStep 4621337 = 3466003) B3466003
theorem B2434103 : Blo 1621009 2434103 := bstep (se 1 (by rfl) ⟨1825577, by rfl⟩ : syracuseStep 2434103 = 3651155) B3651155
theorem B2597951 : Blo 1621009 2597951 := bstep (se 1 (by rfl) ⟨1948463, by rfl⟩ : syracuseStep 2597951 = 3896927) B3896927
theorem B5473385 : Blo 1621009 5473385 := bstep (se 2 (by rfl) ⟨2052519, by rfl⟩ : syracuseStep 5473385 = 4105039) B4105039
theorem B2737327 : Blo 1621009 2737327 := bstep (se 1 (by rfl) ⟨2052995, by rfl⟩ : syracuseStep 2737327 = 4105991) B4105991
theorem B2434223 : Blo 1621009 2434223 := bstep (se 1 (by rfl) ⟨1825667, by rfl⟩ : syracuseStep 2434223 = 3651335) B3651335
theorem B8209835 : Blo 1621009 8209835 := bstep (se 1 (by rfl) ⟨6157376, by rfl⟩ : syracuseStep 8209835 = 12314753) B12314753
theorem B4105849 : Blo 1621009 4105849 := bstep (se 2 (by rfl) ⟨1539693, by rfl⟩ : syracuseStep 4105849 = 3079387) B3079387
theorem B2737847 : Blo 1621009 2737847 := bstep (se 1 (by rfl) ⟨2053385, by rfl⟩ : syracuseStep 2737847 = 4106771) B4106771
theorem B9234107 : Blo 1621009 9234107 := bstep (se 1 (by rfl) ⟨6925580, by rfl⟩ : syracuseStep 9234107 = 13851161) B13851161
theorem B10397443 : Blo 1621009 10397443 := bstep (se 1 (by rfl) ⟨7798082, by rfl⟩ : syracuseStep 10397443 = 15596165) B15596165
theorem B9242423 : Blo 1621009 9242423 := bstep (se 1 (by rfl) ⟨6931817, by rfl⟩ : syracuseStep 9242423 = 13863635) B13863635
theorem B5474249 : Blo 1621009 5474249 := bstep (se 2 (by rfl) ⟨2052843, by rfl⟩ : syracuseStep 5474249 = 4105687) B4105687
theorem B19736567 : Blo 1621009 19736567 := bstep (se 1 (by rfl) ⟨14802425, by rfl⟩ : syracuseStep 19736567 = 29604851) B29604851
theorem B5269495 : Blo 1621009 5269495 := bstep (se 1 (by rfl) ⟨3952121, by rfl⟩ : syracuseStep 5269495 = 7904243) B7904243
theorem B8210483 : Blo 1621009 8210483 := bstep (se 1 (by rfl) ⟨6157862, by rfl⟩ : syracuseStep 8210483 = 12315725) B12315725
theorem B6580349 : Blo 1621009 6580349 := bstep (se 3 (by rfl) ⟨1233815, by rfl⟩ : syracuseStep 6580349 = 2467631) B2467631
theorem B2500799 : Blo 1621009 2500799 := bstep (se 1 (by rfl) ⟨1875599, by rfl⟩ : syracuseStep 2500799 = 3751199) B3751199
theorem B5474519 : Blo 1621009 5474519 := bstep (se 1 (by rfl) ⟨4105889, by rfl⟩ : syracuseStep 5474519 = 8211779) B8211779
theorem B1231595837 : Blo 1621009 1231595837 := bstep (se 3 (by rfl) ⟨230924219, by rfl⟩ : syracuseStep 1231595837 = 461848439) B461848439
theorem B46762433 : Blo 1621009 46762433 := bstep (se 2 (by rfl) ⟨17535912, by rfl⟩ : syracuseStep 46762433 = 35071825) B35071825
theorem B39471569 : Blo 1621009 39471569 := bstep (se 2 (by rfl) ⟨14801838, by rfl⟩ : syracuseStep 39471569 = 29603677) B29603677
theorem B5474843 : Blo 1621009 5474843 := bstep (se 1 (by rfl) ⟨4106132, by rfl⟩ : syracuseStep 5474843 = 8212265) B8212265
theorem B8211131 : Blo 1621009 8211131 := bstep (se 1 (by rfl) ⟨6158348, by rfl⟩ : syracuseStep 8211131 = 12316697) B12316697
theorem B3648311 : Blo 1621009 3648311 := bstep (se 1 (by rfl) ⟨2736233, by rfl⟩ : syracuseStep 3648311 = 5472467) B5472467
theorem B6245207 : Blo 1621009 6245207 := bstep (se 1 (by rfl) ⟨4683905, by rfl⟩ : syracuseStep 6245207 = 9367811) B9367811
theorem B3697643 : Blo 1621009 3697643 := bstep (se 1 (by rfl) ⟨2773232, by rfl⟩ : syracuseStep 3697643 = 5546465) B5546465
theorem B3648491 : Blo 1621009 3648491 := bstep (se 1 (by rfl) ⟨2736368, by rfl⟩ : syracuseStep 3648491 = 5472737) B5472737
theorem B6155311 : Blo 1621009 6155311 := bstep (se 1 (by rfl) ⟨4616483, by rfl⟩ : syracuseStep 6155311 = 9232967) B9232967
theorem B6925409 : Blo 1621009 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B4680947 : Blo 1621009 4680947 := bstep (se 1 (by rfl) ⟨3510710, by rfl⟩ : syracuseStep 4680947 = 7021421) B7021421
theorem B14798159 : Blo 1621009 14798159 := bstep (se 1 (by rfl) ⟨11098619, by rfl⟩ : syracuseStep 14798159 = 22197239) B22197239
theorem B5475707 : Blo 1621009 5475707 := bstep (se 1 (by rfl) ⟨4106780, by rfl⟩ : syracuseStep 5475707 = 8213561) B8213561
theorem B4935163 : Blo 1621009 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B8212103 : Blo 1621009 8212103 := bstep (se 1 (by rfl) ⟨6159077, by rfl⟩ : syracuseStep 8212103 = 12318155) B12318155
theorem B3649319 : Blo 1621009 3649319 := bstep (se 1 (by rfl) ⟨2736989, by rfl⟩ : syracuseStep 3649319 = 5473979) B5473979
theorem B27709289 : Blo 1621009 27709289 := bstep (se 2 (by rfl) ⟨10390983, by rfl⟩ : syracuseStep 27709289 = 20781967) B20781967
theorem B7794605 : Blo 1621009 7794605 := bstep (se 3 (by rfl) ⟨1461488, by rfl⟩ : syracuseStep 7794605 = 2922977) B2922977
theorem B3748027 : Blo 1621009 3748027 := bstep (se 1 (by rfl) ⟨2811020, by rfl⟩ : syracuseStep 3748027 = 5622041) B5622041
theorem B28102859 : Blo 1621009 28102859 := bstep (se 1 (by rfl) ⟨21077144, by rfl⟩ : syracuseStep 28102859 = 42154289) B42154289
theorem B2052479 : Blo 1621009 2052479 := bstep (se 1 (by rfl) ⟨1539359, by rfl⟩ : syracuseStep 2052479 = 3078719) B3078719
theorem B6156755 : Blo 1621009 6156755 := bstep (se 1 (by rfl) ⟨4617566, by rfl⟩ : syracuseStep 6156755 = 9235133) B9235133
theorem B22205117 : Blo 1621009 22205117 := bstep (se 3 (by rfl) ⟨4163459, by rfl⟩ : syracuseStep 22205117 = 8326919) B8326919
theorem B5477111 : Blo 1621009 5477111 := bstep (se 1 (by rfl) ⟨4107833, by rfl⟩ : syracuseStep 5477111 = 8215667) B8215667
theorem B4879111 : Blo 1621009 4879111 := bstep (se 1 (by rfl) ⟨3659333, by rfl⟩ : syracuseStep 4879111 = 7318667) B7318667
theorem B3650345 : Blo 1621009 3650345 := bstep (se 2 (by rfl) ⟨1368879, by rfl⟩ : syracuseStep 3650345 = 2737759) B2737759
theorem B27726785 : Blo 1621009 27726785 := bstep (se 2 (by rfl) ⟨10397544, by rfl⟩ : syracuseStep 27726785 = 20795089) B20795089
theorem B33739739 : Blo 1621009 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B8885257 : Blo 1621009 8885257 := bstep (se 2 (by rfl) ⟨3331971, by rfl⟩ : syracuseStep 8885257 = 6663943) B6663943
theorem B20796425 : Blo 1621009 20796425 := bstep (se 2 (by rfl) ⟨7798659, by rfl⟩ : syracuseStep 20796425 = 15597319) B15597319
theorem B18469943 : Blo 1621009 18469943 := bstep (se 1 (by rfl) ⟨13852457, by rfl⟩ : syracuseStep 18469943 = 27704915) B27704915
theorem B3650615 : Blo 1621009 3650615 := bstep (se 1 (by rfl) ⟨2737961, by rfl⟩ : syracuseStep 3650615 = 5475923) B5475923
theorem B2053183 : Blo 1621009 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B3650633 : Blo 1621009 3650633 := bstep (se 2 (by rfl) ⟨1368987, by rfl⟩ : syracuseStep 3650633 = 2737975) B2737975
theorem B20788325 : Blo 1621009 20788325 := bstep (se 4 (by rfl) ⟨1948905, by rfl⟩ : syracuseStep 20788325 = 3897811) B3897811
theorem B3462355 : Blo 1621009 3462355 := bstep (se 1 (by rfl) ⟨2596766, by rfl⟩ : syracuseStep 3462355 = 5193533) B5193533
theorem B8213723 : Blo 1621009 8213723 := bstep (se 1 (by rfl) ⟨6160292, by rfl⟩ : syracuseStep 8213723 = 12320585) B12320585
theorem B5477651 : Blo 1621009 5477651 := bstep (se 1 (by rfl) ⟨4108238, by rfl⟩ : syracuseStep 5477651 = 8216477) B8216477
theorem B11687321 : Blo 1621009 11687321 := bstep (se 2 (by rfl) ⟨4382745, by rfl⟩ : syracuseStep 11687321 = 8765491) B8765491
theorem B1824367 : Blo 1621009 1824367 := bstep (se 1 (by rfl) ⟨1368275, by rfl⟩ : syracuseStep 1824367 = 2736551) B2736551
theorem B1644143 : Blo 1621009 1644143 := bstep (se 1 (by rfl) ⟨1233107, by rfl⟩ : syracuseStep 1644143 = 2466215) B2466215
theorem B13145773 : Blo 1621009 13145773 := bstep (se 3 (by rfl) ⟨2464832, by rfl⟩ : syracuseStep 13145773 = 4929665) B4929665
theorem B1824475 : Blo 1621009 1824475 := bstep (se 1 (by rfl) ⟨1368356, by rfl⟩ : syracuseStep 1824475 = 2736713) B2736713
theorem B7395083 : Blo 1621009 7395083 := bstep (se 1 (by rfl) ⟨5546312, by rfl⟩ : syracuseStep 7395083 = 11092625) B11092625
theorem B2774983 : Blo 1621009 2774983 := bstep (se 1 (by rfl) ⟨2081237, by rfl⟩ : syracuseStep 2774983 = 4162475) B4162475
theorem B8206433 : Blo 1621009 8206433 := bstep (se 2 (by rfl) ⟨3077412, by rfl⟩ : syracuseStep 8206433 = 6154825) B6154825
theorem B4929641 : Blo 1621009 4929641 := bstep (se 2 (by rfl) ⟨1848615, by rfl⟩ : syracuseStep 4929641 = 3697231) B3697231
theorem B1947883 : Blo 1621009 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B8206595 : Blo 1621009 8206595 := bstep (se 1 (by rfl) ⟨6154946, by rfl⟩ : syracuseStep 8206595 = 12309893) B12309893
theorem B2431625 : Blo 1621009 2431625 := bstep (se 2 (by rfl) ⟨911859, by rfl⟩ : syracuseStep 2431625 = 1823719) B1823719
theorem B2431799 : Blo 1621009 2431799 := bstep (se 1 (by rfl) ⟨1823849, by rfl⟩ : syracuseStep 2431799 = 3647699) B3647699
theorem B2431835 : Blo 1621009 2431835 := bstep (se 1 (by rfl) ⟨1823876, by rfl⟩ : syracuseStep 2431835 = 3647753) B3647753
theorem B1825627 : Blo 1621009 1825627 := bstep (se 1 (by rfl) ⟨1369220, by rfl⟩ : syracuseStep 1825627 = 2738441) B2738441
theorem B2431979 : Blo 1621009 2431979 := bstep (se 1 (by rfl) ⟨1823984, by rfl⟩ : syracuseStep 2431979 = 3647969) B3647969
theorem B1621039 : Blo 1621009 1621039 := bstep (se 1 (by rfl) ⟨1215779, by rfl⟩ : syracuseStep 1621039 = 2431559) B2431559
theorem B1621063 : Blo 1621009 1621063 := bstep (se 1 (by rfl) ⟨1215797, by rfl⟩ : syracuseStep 1621063 = 2431595) B2431595
theorem B4619389 : Blo 1621009 4619389 := bstep (se 3 (by rfl) ⟨866135, by rfl⟩ : syracuseStep 4619389 = 1732271) B1732271
theorem B2432183 : Blo 1621009 2432183 := bstep (se 1 (by rfl) ⟨1824137, by rfl⟩ : syracuseStep 2432183 = 3648275) B3648275
theorem B1621215 : Blo 1621009 1621215 := bstep (se 1 (by rfl) ⟨1215911, by rfl⟩ : syracuseStep 1621215 = 2431823) B2431823
theorem B3079433 : Blo 1621009 3079433 := bstep (se 2 (by rfl) ⟨1154787, by rfl⟩ : syracuseStep 3079433 = 2309575) B2309575
theorem B7798045 : Blo 1621009 7798045 := bstep (se 3 (by rfl) ⟨1462133, by rfl⟩ : syracuseStep 7798045 = 2924267) B2924267
theorem B47398213 : Blo 1621009 47398213 := bstep (se 4 (by rfl) ⟨4443582, by rfl⟩ : syracuseStep 47398213 = 8887165) B8887165
theorem B2735471 : Blo 1621009 2735471 := bstep (se 1 (by rfl) ⟨2051603, by rfl⟩ : syracuseStep 2735471 = 4103207) B4103207
theorem B11099521 : Blo 1621009 11099521 := bstep (se 2 (by rfl) ⟨4162320, by rfl⟩ : syracuseStep 11099521 = 8324641) B8324641
theorem B2432423 : Blo 1621009 2432423 := bstep (se 1 (by rfl) ⟨1824317, by rfl⟩ : syracuseStep 2432423 = 3648635) B3648635
theorem B10386883 : Blo 1621009 10386883 := bstep (se 1 (by rfl) ⟨7790162, by rfl⟩ : syracuseStep 10386883 = 15580325) B15580325
theorem B1621479 : Blo 1621009 1621479 := bstep (se 1 (by rfl) ⟨1216109, by rfl⟩ : syracuseStep 1621479 = 2432219) B2432219
theorem B2432507 : Blo 1621009 2432507 := bstep (se 1 (by rfl) ⟨1824380, by rfl⟩ : syracuseStep 2432507 = 3648761) B3648761
theorem B4619855 : Blo 1621009 4619855 := bstep (se 1 (by rfl) ⟨3464891, by rfl⟩ : syracuseStep 4619855 = 6929783) B6929783
theorem B2735707 : Blo 1621009 2735707 := bstep (se 1 (by rfl) ⟨2051780, by rfl⟩ : syracuseStep 2735707 = 4103561) B4103561
theorem B1621595 : Blo 1621009 1621595 := bstep (se 1 (by rfl) ⟨1216196, by rfl⟩ : syracuseStep 1621595 = 2432393) B2432393
theorem B2432603 : Blo 1621009 2432603 := bstep (se 1 (by rfl) ⟨1824452, by rfl⟩ : syracuseStep 2432603 = 3648905) B3648905
theorem B2432687 : Blo 1621009 2432687 := bstep (se 1 (by rfl) ⟨1824515, by rfl⟩ : syracuseStep 2432687 = 3649031) B3649031
theorem B4103905 : Blo 1621009 4103905 := bstep (se 2 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 4103905 = 3077929) B3077929
theorem B10534625 : Blo 1621009 10534625 := bstep (se 2 (by rfl) ⟨3950484, by rfl⟩ : syracuseStep 10534625 = 7900969) B7900969
theorem B2735849 : Blo 1621009 2735849 := bstep (se 2 (by rfl) ⟨1025943, by rfl⟩ : syracuseStep 2735849 = 2051887) B2051887
theorem B2432807 : Blo 1621009 2432807 := bstep (se 1 (by rfl) ⟨1824605, by rfl⟩ : syracuseStep 2432807 = 3649211) B3649211
theorem B1621831 : Blo 1621009 1621831 := bstep (se 1 (by rfl) ⟨1216373, by rfl⟩ : syracuseStep 1621831 = 2432747) B2432747
theorem B8208215 : Blo 1621009 8208215 := bstep (se 1 (by rfl) ⟨6156161, by rfl⟩ : syracuseStep 8208215 = 12312323) B12312323
theorem B2432891 : Blo 1621009 2432891 := bstep (se 1 (by rfl) ⟨1824668, by rfl⟩ : syracuseStep 2432891 = 3649337) B3649337
theorem B5848955 : Blo 1621009 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B1621983 : Blo 1621009 1621983 := bstep (se 1 (by rfl) ⟨1216487, by rfl⟩ : syracuseStep 1621983 = 2432975) B2432975
theorem B18735239 : Blo 1621009 18735239 := bstep (se 1 (by rfl) ⟨14051429, by rfl⟩ : syracuseStep 18735239 = 28102859) B28102859
theorem B1622207 : Blo 1621009 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B1622223 : Blo 1621009 1622223 := bstep (se 1 (by rfl) ⟨1216667, by rfl⟩ : syracuseStep 1622223 = 2433335) B2433335
theorem B4997369 : Blo 1621009 4997369 := bstep (se 2 (by rfl) ⟨1874013, by rfl⟩ : syracuseStep 4997369 = 3748027) B3748027
theorem B1622271 : Blo 1621009 1622271 := bstep (se 1 (by rfl) ⟨1216703, by rfl⟩ : syracuseStep 1622271 = 2433407) B2433407
theorem B1622319 : Blo 1621009 1622319 := bstep (se 1 (by rfl) ⟨1216739, by rfl⟩ : syracuseStep 1622319 = 2433479) B2433479
theorem B4104503 : Blo 1621009 4104503 := bstep (se 1 (by rfl) ⟨3078377, by rfl⟩ : syracuseStep 4104503 = 6156755) B6156755
theorem B2597177 : Blo 1621009 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B5472683 : Blo 1621009 5472683 := bstep (se 1 (by rfl) ⟨4104512, by rfl⟩ : syracuseStep 5472683 = 8209025) B8209025
theorem B18481607 : Blo 1621009 18481607 := bstep (se 1 (by rfl) ⟨13861205, by rfl⟩ : syracuseStep 18481607 = 27722411) B27722411
theorem B14803411 : Blo 1621009 14803411 := bstep (se 1 (by rfl) ⟨11102558, by rfl⟩ : syracuseStep 14803411 = 22205117) B22205117
theorem B2433563 : Blo 1621009 2433563 := bstep (se 1 (by rfl) ⟨1825172, by rfl⟩ : syracuseStep 2433563 = 3650345) B3650345
theorem B1622555 : Blo 1621009 1622555 := bstep (se 1 (by rfl) ⟨1216916, by rfl⟩ : syracuseStep 1622555 = 2433833) B2433833
theorem B1622559 : Blo 1621009 1622559 := bstep (se 1 (by rfl) ⟨1216919, by rfl⟩ : syracuseStep 1622559 = 2433839) B2433839
theorem B1622639 : Blo 1621009 1622639 := bstep (se 1 (by rfl) ⟨1216979, by rfl⟩ : syracuseStep 1622639 = 2433959) B2433959
theorem B1622695 : Blo 1621009 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B3080891 : Blo 1621009 3080891 := bstep (se 1 (by rfl) ⟨2310668, by rfl⟩ : syracuseStep 3080891 = 4621337) B4621337
theorem B12313295 : Blo 1621009 12313295 := bstep (se 1 (by rfl) ⟨9234971, by rfl⟩ : syracuseStep 12313295 = 18469943) B18469943
theorem B2433743 : Blo 1621009 2433743 := bstep (se 1 (by rfl) ⟨1825307, by rfl⟩ : syracuseStep 2433743 = 3650615) B3650615
theorem B1622735 : Blo 1621009 1622735 := bstep (se 1 (by rfl) ⟨1217051, by rfl⟩ : syracuseStep 1622735 = 2434103) B2434103
theorem B2433755 : Blo 1621009 2433755 := bstep (se 1 (by rfl) ⟨1825316, by rfl⟩ : syracuseStep 2433755 = 3650633) B3650633
theorem B1622815 : Blo 1621009 1622815 := bstep (se 1 (by rfl) ⟨1217111, by rfl⟩ : syracuseStep 1622815 = 2434223) B2434223
theorem B7791547 : Blo 1621009 7791547 := bstep (se 1 (by rfl) ⟨5843660, by rfl⟩ : syracuseStep 7791547 = 11687321) B11687321
theorem B5473223 : Blo 1621009 5473223 := bstep (se 1 (by rfl) ⟨4104917, by rfl⟩ : syracuseStep 5473223 = 8209835) B8209835
theorem B5473277 : Blo 1621009 5473277 := bstep (se 3 (by rfl) ⟨1026239, by rfl⟩ : syracuseStep 5473277 = 2052479) B2052479
theorem B6505481 : Blo 1621009 6505481 := bstep (se 2 (by rfl) ⟨2439555, by rfl⟩ : syracuseStep 6505481 = 4879111) B4879111
theorem B2434169 : Blo 1621009 2434169 := bstep (se 2 (by rfl) ⟨912813, by rfl⟩ : syracuseStep 2434169 = 1825627) B1825627
theorem B6161615 : Blo 1621009 6161615 := bstep (se 1 (by rfl) ⟨4621211, by rfl⟩ : syracuseStep 6161615 = 9242423) B9242423
theorem B13157711 : Blo 1621009 13157711 := bstep (se 1 (by rfl) ⟨9868283, by rfl⟩ : syracuseStep 13157711 = 19736567) B19736567
theorem B5473655 : Blo 1621009 5473655 := bstep (se 1 (by rfl) ⟨4105241, by rfl⟩ : syracuseStep 5473655 = 8210483) B8210483
theorem B3286427 : Blo 1621009 3286427 := bstep (se 1 (by rfl) ⟨2464820, by rfl⟩ : syracuseStep 3286427 = 4929641) B4929641
theorem B2737577 : Blo 1621009 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B4384381 : Blo 1621009 4384381 := bstep (se 3 (by rfl) ⟨822071, by rfl⟩ : syracuseStep 4384381 = 1644143) B1644143
theorem B26314379 : Blo 1621009 26314379 := bstep (se 1 (by rfl) ⟨19735784, by rfl⟩ : syracuseStep 26314379 = 39471569) B39471569
theorem B10397393 : Blo 1621009 10397393 := bstep (se 2 (by rfl) ⟨3899022, by rfl⟩ : syracuseStep 10397393 = 7798045) B7798045
theorem B5474087 : Blo 1621009 5474087 := bstep (se 1 (by rfl) ⟨4105565, by rfl⟩ : syracuseStep 5474087 = 8211131) B8211131
theorem B4163471 : Blo 1621009 4163471 := bstep (se 1 (by rfl) ⟨3122603, by rfl⟩ : syracuseStep 4163471 = 6245207) B6245207
theorem B26675189 : Blo 1621009 26675189 := bstep (se 5 (by rfl) ⟨1250399, by rfl⟩ : syracuseStep 26675189 = 2500799) B2500799
theorem B6580217 : Blo 1621009 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B3647609 : Blo 1621009 3647609 := bstep (se 2 (by rfl) ⟨1367853, by rfl⟩ : syracuseStep 3647609 = 2735707) B2735707
theorem B5474465 : Blo 1621009 5474465 := bstep (se 2 (by rfl) ⟨2052924, by rfl⟩ : syracuseStep 5474465 = 4105849) B4105849
theorem B9865439 : Blo 1621009 9865439 := bstep (se 1 (by rfl) ⟨7399079, by rfl⟩ : syracuseStep 9865439 = 14798159) B14798159
theorem B13863257 : Blo 1621009 13863257 := bstep (se 2 (by rfl) ⟨5198721, by rfl⟩ : syracuseStep 13863257 = 10397443) B10397443
theorem B5474735 : Blo 1621009 5474735 := bstep (se 1 (by rfl) ⟨4106051, by rfl⟩ : syracuseStep 5474735 = 8212103) B8212103
theorem B7023083 : Blo 1621009 7023083 := bstep (se 1 (by rfl) ⟨5267312, by rfl⟩ : syracuseStep 7023083 = 10534625) B10534625
theorem B5196403 : Blo 1621009 5196403 := bstep (se 1 (by rfl) ⟨3897302, by rfl⟩ : syracuseStep 5196403 = 7794605) B7794605
theorem B39463595 : Blo 1621009 39463595 := bstep (se 1 (by rfl) ⟨29597696, by rfl⟩ : syracuseStep 39463595 = 59195393) B59195393
theorem B28863539 : Blo 1621009 28863539 := bstep (se 1 (by rfl) ⟨21647654, by rfl⟩ : syracuseStep 28863539 = 43295309) B43295309
theorem B18484523 : Blo 1621009 18484523 := bstep (se 1 (by rfl) ⟨13863392, by rfl⟩ : syracuseStep 18484523 = 27726785) B27726785
theorem B13864283 : Blo 1621009 13864283 := bstep (se 1 (by rfl) ⟨10398212, by rfl⟩ : syracuseStep 13864283 = 20796425) B20796425
theorem B3648923 : Blo 1621009 3648923 := bstep (se 1 (by rfl) ⟨2736692, by rfl⟩ : syracuseStep 3648923 = 5473385) B5473385
theorem B5475815 : Blo 1621009 5475815 := bstep (se 1 (by rfl) ⟨4106861, by rfl⟩ : syracuseStep 5475815 = 8213723) B8213723
theorem B6156071 : Blo 1621009 6156071 := bstep (se 1 (by rfl) ⟨4617053, by rfl⟩ : syracuseStep 6156071 = 9234107) B9234107
theorem B3649499 : Blo 1621009 3649499 := bstep (se 1 (by rfl) ⟨2737124, by rfl⟩ : syracuseStep 3649499 = 5474249) B5474249
theorem B4386899 : Blo 1621009 4386899 := bstep (se 1 (by rfl) ⟨3290174, by rfl⟩ : syracuseStep 4386899 = 6580349) B6580349
theorem B3649679 : Blo 1621009 3649679 := bstep (se 1 (by rfl) ⟨2737259, by rfl⟩ : syracuseStep 3649679 = 5474519) B5474519
theorem B821063891 : Blo 1621009 821063891 := bstep (se 1 (by rfl) ⟨615797918, by rfl⟩ : syracuseStep 821063891 = 1231595837) B1231595837
theorem B3649769 : Blo 1621009 3649769 := bstep (se 2 (by rfl) ⟨1368663, by rfl⟩ : syracuseStep 3649769 = 2737327) B2737327
theorem B4616473 : Blo 1621009 4616473 := bstep (se 2 (by rfl) ⟨1731177, by rfl⟩ : syracuseStep 4616473 = 3462355) B3462355
theorem B31174955 : Blo 1621009 31174955 := bstep (se 1 (by rfl) ⟨23381216, by rfl⟩ : syracuseStep 31174955 = 46762433) B46762433
theorem B3649895 : Blo 1621009 3649895 := bstep (se 1 (by rfl) ⟨2737421, by rfl⟩ : syracuseStep 3649895 = 5474843) B5474843
theorem B63197617 : Blo 1621009 63197617 := bstep (se 2 (by rfl) ⟨23699106, by rfl⟩ : syracuseStep 63197617 = 47398213) B47398213
theorem B14799361 : Blo 1621009 14799361 := bstep (se 2 (by rfl) ⟨5549760, by rfl⟩ : syracuseStep 14799361 = 11099521) B11099521
theorem B13849177 : Blo 1621009 13849177 := bstep (se 2 (by rfl) ⟨5193441, by rfl⟩ : syracuseStep 13849177 = 10386883) B10386883
theorem B4616939 : Blo 1621009 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B2052955 : Blo 1621009 2052955 := bstep (se 1 (by rfl) ⟨1539716, by rfl⟩ : syracuseStep 2052955 = 3079433) B3079433
theorem B17527697 : Blo 1621009 17527697 := bstep (se 2 (by rfl) ⟨6572886, by rfl⟩ : syracuseStep 17527697 = 13145773) B13145773
theorem B1823647 : Blo 1621009 1823647 := bstep (se 1 (by rfl) ⟨1367735, by rfl⟩ : syracuseStep 1823647 = 2735471) B2735471
theorem B3650471 : Blo 1621009 3650471 := bstep (se 1 (by rfl) ⟨2737853, by rfl⟩ : syracuseStep 3650471 = 5475707) B5475707
theorem B1823899 : Blo 1621009 1823899 := bstep (se 1 (by rfl) ⟨1367924, by rfl⟩ : syracuseStep 1823899 = 2735849) B2735849
theorem B3699977 : Blo 1621009 3699977 := bstep (se 2 (by rfl) ⟨1387491, by rfl⟩ : syracuseStep 3699977 = 2774983) B2774983
theorem B7025993 : Blo 1621009 7025993 := bstep (se 2 (by rfl) ⟨2634747, by rfl⟩ : syracuseStep 7025993 = 5269495) B5269495
theorem B47388037 : Blo 1621009 47388037 := bstep (se 4 (by rfl) ⟨4442628, by rfl⟩ : syracuseStep 47388037 = 8885257) B8885257
theorem B6927869 : Blo 1621009 6927869 := bstep (se 3 (by rfl) ⟨1298975, by rfl⟩ : syracuseStep 6927869 = 2597951) B2597951
theorem B86562553 : Blo 1621009 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B1824583 : Blo 1621009 1824583 := bstep (se 1 (by rfl) ⟨1368437, by rfl⟩ : syracuseStep 1824583 = 2736875) B2736875
theorem B3651407 : Blo 1621009 3651407 := bstep (se 1 (by rfl) ⟨2738555, by rfl⟩ : syracuseStep 3651407 = 5477111) B5477111
theorem B12482525 : Blo 1621009 12482525 := bstep (se 3 (by rfl) ⟨2340473, by rfl⟩ : syracuseStep 12482525 = 4680947) B4680947
theorem B22493159 : Blo 1621009 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B13858883 : Blo 1621009 13858883 := bstep (se 1 (by rfl) ⟨10394162, by rfl⟩ : syracuseStep 13858883 = 20788325) B20788325
theorem B3651767 : Blo 1621009 3651767 := bstep (se 1 (by rfl) ⟨2738825, by rfl⟩ : syracuseStep 3651767 = 5477651) B5477651
theorem B12310865 : Blo 1621009 12310865 := bstep (se 2 (by rfl) ⟨4616574, by rfl⟩ : syracuseStep 12310865 = 9233149) B9233149
theorem B1825231 : Blo 1621009 1825231 := bstep (se 1 (by rfl) ⟨1368923, by rfl⟩ : syracuseStep 1825231 = 2737847) B2737847
theorem B18471401 : Blo 1621009 18471401 := bstep (se 2 (by rfl) ⟨6926775, by rfl⟩ : syracuseStep 18471401 = 13853551) B13853551
theorem B4930055 : Blo 1621009 4930055 := bstep (se 1 (by rfl) ⟨3697541, by rfl⟩ : syracuseStep 4930055 = 7395083) B7395083
theorem B97434181 : Blo 1621009 97434181 := bstep (se 4 (by rfl) ⟨9134454, by rfl⟩ : syracuseStep 97434181 = 18268909) B18268909
theorem B8207081 : Blo 1621009 8207081 := bstep (se 2 (by rfl) ⟨3077655, by rfl⟩ : syracuseStep 8207081 = 6155311) B6155311
theorem B5470955 : Blo 1621009 5470955 := bstep (se 1 (by rfl) ⟨4103216, by rfl⟩ : syracuseStep 5470955 = 8206433) B8206433
theorem B6159185 : Blo 1621009 6159185 := bstep (se 2 (by rfl) ⟨2309694, by rfl⟩ : syracuseStep 6159185 = 4619389) B4619389
theorem B5471063 : Blo 1621009 5471063 := bstep (se 1 (by rfl) ⟨4103297, by rfl⟩ : syracuseStep 5471063 = 8206595) B8206595
theorem B12319613 : Blo 1621009 12319613 := bstep (se 3 (by rfl) ⟨2309927, by rfl⟩ : syracuseStep 12319613 = 4619855) B4619855
theorem B1621083 : Blo 1621009 1621083 := bstep (se 1 (by rfl) ⟨1215812, by rfl⟩ : syracuseStep 1621083 = 2431625) B2431625
theorem B1621199 : Blo 1621009 1621199 := bstep (se 1 (by rfl) ⟨1215899, by rfl⟩ : syracuseStep 1621199 = 2431799) B2431799
theorem B2432207 : Blo 1621009 2432207 := bstep (se 1 (by rfl) ⟨1824155, by rfl⟩ : syracuseStep 2432207 = 3648311) B3648311
theorem B1621223 : Blo 1621009 1621223 := bstep (se 1 (by rfl) ⟨1215917, by rfl⟩ : syracuseStep 1621223 = 2431835) B2431835
theorem B2465095 : Blo 1621009 2465095 := bstep (se 1 (by rfl) ⟨1848821, by rfl⟩ : syracuseStep 2465095 = 3697643) B3697643
theorem B1621319 : Blo 1621009 1621319 := bstep (se 1 (by rfl) ⟨1215989, by rfl⟩ : syracuseStep 1621319 = 2431979) B2431979
theorem B2432327 : Blo 1621009 2432327 := bstep (se 1 (by rfl) ⟨1824245, by rfl⟩ : syracuseStep 2432327 = 3648491) B3648491
theorem B1621455 : Blo 1621009 1621455 := bstep (se 1 (by rfl) ⟨1216091, by rfl⟩ : syracuseStep 1621455 = 2432183) B2432183
theorem B2432489 : Blo 1621009 2432489 := bstep (se 2 (by rfl) ⟨912183, by rfl⟩ : syracuseStep 2432489 = 1824367) B1824367
theorem B1621615 : Blo 1621009 1621615 := bstep (se 1 (by rfl) ⟨1216211, by rfl⟩ : syracuseStep 1621615 = 2432423) B2432423
theorem B2432633 : Blo 1621009 2432633 := bstep (se 2 (by rfl) ⟨912237, by rfl⟩ : syracuseStep 2432633 = 1824475) B1824475
theorem B5471873 : Blo 1621009 5471873 := bstep (se 2 (by rfl) ⟨2051952, by rfl⟩ : syracuseStep 5471873 = 4103905) B4103905
theorem B1621671 : Blo 1621009 1621671 := bstep (se 1 (by rfl) ⟨1216253, by rfl⟩ : syracuseStep 1621671 = 2432507) B2432507
theorem B1621735 : Blo 1621009 1621735 := bstep (se 1 (by rfl) ⟨1216301, by rfl⟩ : syracuseStep 1621735 = 2432603) B2432603
theorem B1621791 : Blo 1621009 1621791 := bstep (se 1 (by rfl) ⟨1216343, by rfl⟩ : syracuseStep 1621791 = 2432687) B2432687
theorem B1621871 : Blo 1621009 1621871 := bstep (se 1 (by rfl) ⟨1216403, by rfl⟩ : syracuseStep 1621871 = 2432807) B2432807
theorem B2432879 : Blo 1621009 2432879 := bstep (se 1 (by rfl) ⟨1824659, by rfl⟩ : syracuseStep 2432879 = 3649319) B3649319
theorem B5472143 : Blo 1621009 5472143 := bstep (se 1 (by rfl) ⟨4104107, by rfl⟩ : syracuseStep 5472143 = 8208215) B8208215
theorem B18472859 : Blo 1621009 18472859 := bstep (se 1 (by rfl) ⟨13854644, by rfl⟩ : syracuseStep 18472859 = 27709289) B27709289
theorem B1621927 : Blo 1621009 1621927 := bstep (se 1 (by rfl) ⟨1216445, by rfl⟩ : syracuseStep 1621927 = 2432891) B2432891
theorem B3899303 : Blo 1621009 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B2924599 : Blo 1621009 2924599 := bstep (se 1 (by rfl) ⟨2193449, by rfl⟩ : syracuseStep 2924599 = 4386899) B4386899
theorem B2433119 : Blo 1621009 2433119 := bstep (se 1 (by rfl) ⟨1824839, by rfl⟩ : syracuseStep 2433119 = 3649679) B3649679
theorem B2433179 : Blo 1621009 2433179 := bstep (se 1 (by rfl) ⟨1824884, by rfl⟩ : syracuseStep 2433179 = 3649769) B3649769
theorem B20783303 : Blo 1621009 20783303 := bstep (se 1 (by rfl) ⟨15587477, by rfl⟩ : syracuseStep 20783303 = 31174955) B31174955
theorem B2736335 : Blo 1621009 2736335 := bstep (se 1 (by rfl) ⟨2052251, by rfl⟩ : syracuseStep 2736335 = 4104503) B4104503
theorem B2433263 : Blo 1621009 2433263 := bstep (se 1 (by rfl) ⟨1824947, by rfl⟩ : syracuseStep 2433263 = 3649895) B3649895
theorem B12321071 : Blo 1621009 12321071 := bstep (se 1 (by rfl) ⟨9240803, by rfl⟩ : syracuseStep 12321071 = 18481607) B18481607
theorem B1622375 : Blo 1621009 1622375 := bstep (se 1 (by rfl) ⟨1216781, by rfl⟩ : syracuseStep 1622375 = 2433563) B2433563
theorem B8208863 : Blo 1621009 8208863 := bstep (se 1 (by rfl) ⟨6156647, by rfl⟩ : syracuseStep 8208863 = 12313295) B12313295
theorem B1622495 : Blo 1621009 1622495 := bstep (se 1 (by rfl) ⟨1216871, by rfl⟩ : syracuseStep 1622495 = 2433743) B2433743
theorem B1622503 : Blo 1621009 1622503 := bstep (se 1 (by rfl) ⟨1216877, by rfl⟩ : syracuseStep 1622503 = 2433755) B2433755
theorem B84263489 : Blo 1621009 84263489 := bstep (se 2 (by rfl) ⟨31598808, by rfl⟩ : syracuseStep 84263489 = 63197617) B63197617
theorem B2433641 : Blo 1621009 2433641 := bstep (se 2 (by rfl) ⟨912615, by rfl⟩ : syracuseStep 2433641 = 1825231) B1825231
theorem B2433647 : Blo 1621009 2433647 := bstep (se 1 (by rfl) ⟨1825235, by rfl⟩ : syracuseStep 2433647 = 3650471) B3650471
theorem B1622779 : Blo 1621009 1622779 := bstep (se 1 (by rfl) ⟨1217084, by rfl⟩ : syracuseStep 1622779 = 2434169) B2434169
theorem B18465569 : Blo 1621009 18465569 := bstep (se 2 (by rfl) ⟨6924588, by rfl⟩ : syracuseStep 18465569 = 13849177) B13849177
theorem B2737273 : Blo 1621009 2737273 := bstep (se 2 (by rfl) ⟨1026477, by rfl⟩ : syracuseStep 2737273 = 2052955) B2052955
theorem B6931595 : Blo 1621009 6931595 := bstep (se 1 (by rfl) ⟨5198696, by rfl⟩ : syracuseStep 6931595 = 10397393) B10397393
theorem B2434271 : Blo 1621009 2434271 := bstep (se 1 (by rfl) ⟨1825703, by rfl⟩ : syracuseStep 2434271 = 3651407) B3651407
theorem B10388729 : Blo 1621009 10388729 := bstep (se 2 (by rfl) ⟨3895773, by rfl⟩ : syracuseStep 10388729 = 7791547) B7791547
theorem B18728221 : Blo 1621009 18728221 := bstep (se 3 (by rfl) ⟨3511541, by rfl⟩ : syracuseStep 18728221 = 7023083) B7023083
theorem B18474317 : Blo 1621009 18474317 := bstep (se 3 (by rfl) ⟨3463934, by rfl⟩ : syracuseStep 18474317 = 6927869) B6927869
theorem B2434511 : Blo 1621009 2434511 := bstep (se 1 (by rfl) ⟨1825883, by rfl⟩ : syracuseStep 2434511 = 3651767) B3651767
theorem B9242171 : Blo 1621009 9242171 := bstep (se 1 (by rfl) ⟨6931628, by rfl⟩ : syracuseStep 9242171 = 13863257) B13863257
theorem B12314267 : Blo 1621009 12314267 := bstep (se 1 (by rfl) ⟨9235700, by rfl⟩ : syracuseStep 12314267 = 18471401) B18471401
theorem B3286703 : Blo 1621009 3286703 := bstep (se 1 (by rfl) ⟨2465027, by rfl⟩ : syracuseStep 3286703 = 4930055) B4930055
theorem B3286793 : Blo 1621009 3286793 := bstep (se 2 (by rfl) ⟨1232547, by rfl⟩ : syracuseStep 3286793 = 2465095) B2465095
theorem B3647303 : Blo 1621009 3647303 := bstep (se 1 (by rfl) ⟨2735477, by rfl⟩ : syracuseStep 3647303 = 5470955) B5470955
theorem B4106123 : Blo 1621009 4106123 := bstep (se 1 (by rfl) ⟨3079592, by rfl⟩ : syracuseStep 4106123 = 6159185) B6159185
theorem B3647375 : Blo 1621009 3647375 := bstep (se 1 (by rfl) ⟨2735531, by rfl⟩ : syracuseStep 3647375 = 5471063) B5471063
theorem B12323015 : Blo 1621009 12323015 := bstep (se 1 (by rfl) ⟨9242261, by rfl⟩ : syracuseStep 12323015 = 18484523) B18484523
theorem B9242855 : Blo 1621009 9242855 := bstep (se 1 (by rfl) ⟨6932141, by rfl⟩ : syracuseStep 9242855 = 13864283) B13864283
theorem B3647915 : Blo 1621009 3647915 := bstep (se 1 (by rfl) ⟨2735936, by rfl⟩ : syracuseStep 3647915 = 5471873) B5471873
theorem B33286733 : Blo 1621009 33286733 := bstep (se 3 (by rfl) ⟨6241262, by rfl⟩ : syracuseStep 33286733 = 12482525) B12482525
theorem B3648095 : Blo 1621009 3648095 := bstep (se 1 (by rfl) ⟨2736071, by rfl⟩ : syracuseStep 3648095 = 5472143) B5472143
theorem B12315239 : Blo 1621009 12315239 := bstep (se 1 (by rfl) ⟨9236429, by rfl⟩ : syracuseStep 12315239 = 18472859) B18472859
theorem B2599535 : Blo 1621009 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B547375927 : Blo 1621009 547375927 := bstep (se 1 (by rfl) ⟨410531945, by rfl⟩ : syracuseStep 547375927 = 821063891) B821063891
theorem B1731451 : Blo 1621009 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B3648455 : Blo 1621009 3648455 := bstep (se 1 (by rfl) ⟨2736341, by rfl⟩ : syracuseStep 3648455 = 5472683) B5472683
theorem B6155297 : Blo 1621009 6155297 := bstep (se 2 (by rfl) ⟨2308236, by rfl⟩ : syracuseStep 6155297 = 4616473) B4616473
theorem B11685131 : Blo 1621009 11685131 := bstep (se 1 (by rfl) ⟨8763848, by rfl⟩ : syracuseStep 11685131 = 17527697) B17527697
theorem B19737881 : Blo 1621009 19737881 := bstep (se 2 (by rfl) ⟨7401705, by rfl⟩ : syracuseStep 19737881 = 14803411) B14803411
theorem B3648815 : Blo 1621009 3648815 := bstep (se 1 (by rfl) ⟨2736611, by rfl⟩ : syracuseStep 3648815 = 5473223) B5473223
theorem B3648851 : Blo 1621009 3648851 := bstep (se 1 (by rfl) ⟨2736638, by rfl⟩ : syracuseStep 3648851 = 5473277) B5473277
theorem B4336987 : Blo 1621009 4336987 := bstep (se 1 (by rfl) ⟨3252740, by rfl⟩ : syracuseStep 4336987 = 6505481) B6505481
theorem B9866605 : Blo 1621009 9866605 := bstep (se 3 (by rfl) ⟨1849988, by rfl⟩ : syracuseStep 9866605 = 3699977) B3699977
theorem B129912241 : Blo 1621009 129912241 := bstep (se 2 (by rfl) ⟨48717090, by rfl⟩ : syracuseStep 129912241 = 97434181) B97434181
theorem B4107743 : Blo 1621009 4107743 := bstep (se 1 (by rfl) ⟨3080807, by rfl⟩ : syracuseStep 4107743 = 6161615) B6161615
theorem B3649103 : Blo 1621009 3649103 := bstep (se 1 (by rfl) ⟨2736827, by rfl⟩ : syracuseStep 3649103 = 5473655) B5473655
theorem B17542919 : Blo 1621009 17542919 := bstep (se 1 (by rfl) ⟨13157189, by rfl⟩ : syracuseStep 17542919 = 26314379) B26314379
theorem B3649391 : Blo 1621009 3649391 := bstep (se 1 (by rfl) ⟨2737043, by rfl⟩ : syracuseStep 3649391 = 5474087) B5474087
theorem B14995439 : Blo 1621009 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B4386811 : Blo 1621009 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B3649643 : Blo 1621009 3649643 := bstep (se 1 (by rfl) ⟨2737232, by rfl⟩ : syracuseStep 3649643 = 5474465) B5474465
theorem B3649823 : Blo 1621009 3649823 := bstep (se 1 (by rfl) ⟨2737367, by rfl⟩ : syracuseStep 3649823 = 5474735) B5474735
theorem B26309063 : Blo 1621009 26309063 := bstep (se 1 (by rfl) ⟨19731797, by rfl⟩ : syracuseStep 26309063 = 39463595) B39463595
theorem B8213075 : Blo 1621009 8213075 := bstep (se 1 (by rfl) ⟨6159806, by rfl⟩ : syracuseStep 8213075 = 12319613) B12319613
theorem B5845841 : Blo 1621009 5845841 := bstep (se 2 (by rfl) ⟨2192190, by rfl⟩ : syracuseStep 5845841 = 4384381) B4384381
theorem B3650543 : Blo 1621009 3650543 := bstep (se 1 (by rfl) ⟨2737907, by rfl⟩ : syracuseStep 3650543 = 5475815) B5475815
theorem B12490159 : Blo 1621009 12490159 := bstep (se 1 (by rfl) ⟨9367619, by rfl⟩ : syracuseStep 12490159 = 18735239) B18735239
theorem B3331579 : Blo 1621009 3331579 := bstep (se 1 (by rfl) ⟨2498684, by rfl⟩ : syracuseStep 3331579 = 4997369) B4997369
theorem B2053927 : Blo 1621009 2053927 := bstep (se 1 (by rfl) ⟨1540445, by rfl⟩ : syracuseStep 2053927 = 3080891) B3080891
theorem B19732481 : Blo 1621009 19732481 := bstep (se 2 (by rfl) ⟨7399680, by rfl⟩ : syracuseStep 19732481 = 14799361) B14799361
theorem B6928537 : Blo 1621009 6928537 := bstep (se 2 (by rfl) ⟨2598201, by rfl⟩ : syracuseStep 6928537 = 5196403) B5196403
theorem B4683995 : Blo 1621009 4683995 := bstep (se 1 (by rfl) ⟨3512996, by rfl⟩ : syracuseStep 4683995 = 7025993) B7025993
theorem B8771807 : Blo 1621009 8771807 := bstep (se 1 (by rfl) ⟨6578855, by rfl⟩ : syracuseStep 8771807 = 13157711) B13157711
theorem B1825051 : Blo 1621009 1825051 := bstep (se 1 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 1825051 = 2737577) B2737577
theorem B8763805 : Blo 1621009 8763805 := bstep (se 3 (by rfl) ⟨1643213, by rfl⟩ : syracuseStep 8763805 = 3286427) B3286427
theorem B2431529 : Blo 1621009 2431529 := bstep (se 2 (by rfl) ⟨911823, by rfl⟩ : syracuseStep 2431529 = 1823647) B1823647
theorem B2775647 : Blo 1621009 2775647 := bstep (se 1 (by rfl) ⟨2081735, by rfl⟩ : syracuseStep 2775647 = 4163471) B4163471
theorem B17783459 : Blo 1621009 17783459 := bstep (se 1 (by rfl) ⟨13337594, by rfl⟩ : syracuseStep 17783459 = 26675189) B26675189
theorem B9239255 : Blo 1621009 9239255 := bstep (se 1 (by rfl) ⟨6929441, by rfl⟩ : syracuseStep 9239255 = 13858883) B13858883
theorem B2431739 : Blo 1621009 2431739 := bstep (se 1 (by rfl) ⟨1823804, by rfl⟩ : syracuseStep 2431739 = 3647609) B3647609
theorem B6576959 : Blo 1621009 6576959 := bstep (se 1 (by rfl) ⟨4932719, by rfl⟩ : syracuseStep 6576959 = 9865439) B9865439
theorem B2431865 : Blo 1621009 2431865 := bstep (se 2 (by rfl) ⟨911949, by rfl⟩ : syracuseStep 2431865 = 1823899) B1823899
theorem B8207243 : Blo 1621009 8207243 := bstep (se 1 (by rfl) ⟨6155432, by rfl⟩ : syracuseStep 8207243 = 12310865) B12310865
theorem B5471387 : Blo 1621009 5471387 := bstep (se 1 (by rfl) ⟨4103540, by rfl⟩ : syracuseStep 5471387 = 8207081) B8207081
theorem B63184049 : Blo 1621009 63184049 := bstep (se 2 (by rfl) ⟨23694018, by rfl⟩ : syracuseStep 63184049 = 47388037) B47388037
theorem B12311837 : Blo 1621009 12311837 := bstep (se 3 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 12311837 = 4616939) B4616939
theorem B19242359 : Blo 1621009 19242359 := bstep (se 1 (by rfl) ⟨14431769, by rfl⟩ : syracuseStep 19242359 = 28863539) B28863539
theorem B1621471 : Blo 1621009 1621471 := bstep (se 1 (by rfl) ⟨1216103, by rfl⟩ : syracuseStep 1621471 = 2432207) B2432207
theorem B1621551 : Blo 1621009 1621551 := bstep (se 1 (by rfl) ⟨1216163, by rfl⟩ : syracuseStep 1621551 = 2432327) B2432327
theorem B2432615 : Blo 1621009 2432615 := bstep (se 1 (by rfl) ⟨1824461, by rfl⟩ : syracuseStep 2432615 = 3648923) B3648923
theorem B1621659 : Blo 1621009 1621659 := bstep (se 1 (by rfl) ⟨1216244, by rfl⟩ : syracuseStep 1621659 = 2432489) B2432489
theorem B115416737 : Blo 1621009 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B1621755 : Blo 1621009 1621755 := bstep (se 1 (by rfl) ⟨1216316, by rfl⟩ : syracuseStep 1621755 = 2432633) B2432633
theorem B2432777 : Blo 1621009 2432777 := bstep (se 2 (by rfl) ⟨912291, by rfl⟩ : syracuseStep 2432777 = 1824583) B1824583
theorem B4104047 : Blo 1621009 4104047 := bstep (se 1 (by rfl) ⟨3078035, by rfl⟩ : syracuseStep 4104047 = 6156071) B6156071
theorem B1621919 : Blo 1621009 1621919 := bstep (se 1 (by rfl) ⟨1216439, by rfl⟩ : syracuseStep 1621919 = 2432879) B2432879
theorem B2432999 : Blo 1621009 2432999 := bstep (se 1 (by rfl) ⟨1824749, by rfl⟩ : syracuseStep 2432999 = 3649499) B3649499
theorem B1622079 : Blo 1621009 1622079 := bstep (se 1 (by rfl) ⟨1216559, by rfl⟩ : syracuseStep 1622079 = 2433119) B2433119
theorem B2433095 : Blo 1621009 2433095 := bstep (se 1 (by rfl) ⟨1824821, by rfl⟩ : syracuseStep 2433095 = 3649643) B3649643
theorem B3899465 : Blo 1621009 3899465 := bstep (se 2 (by rfl) ⟨1462299, by rfl⟩ : syracuseStep 3899465 = 2924599) B2924599
theorem B1622119 : Blo 1621009 1622119 := bstep (se 1 (by rfl) ⟨1216589, by rfl⟩ : syracuseStep 1622119 = 2433179) B2433179
theorem B1622175 : Blo 1621009 1622175 := bstep (se 1 (by rfl) ⟨1216631, by rfl⟩ : syracuseStep 1622175 = 2433263) B2433263
theorem B2433215 : Blo 1621009 2433215 := bstep (se 1 (by rfl) ⟨1824911, by rfl⟩ : syracuseStep 2433215 = 3649823) B3649823
theorem B17539375 : Blo 1621009 17539375 := bstep (se 1 (by rfl) ⟨13154531, by rfl⟩ : syracuseStep 17539375 = 26309063) B26309063
theorem B5472575 : Blo 1621009 5472575 := bstep (se 1 (by rfl) ⟨4104431, by rfl⟩ : syracuseStep 5472575 = 8208863) B8208863
theorem B2433401 : Blo 1621009 2433401 := bstep (se 2 (by rfl) ⟨912525, by rfl⟩ : syracuseStep 2433401 = 1825051) B1825051
theorem B1622427 : Blo 1621009 1622427 := bstep (se 1 (by rfl) ⟨1216820, by rfl⟩ : syracuseStep 1622427 = 2433641) B2433641
theorem B1622431 : Blo 1621009 1622431 := bstep (se 1 (by rfl) ⟨1216823, by rfl⟩ : syracuseStep 1622431 = 2433647) B2433647
theorem B2433695 : Blo 1621009 2433695 := bstep (se 1 (by rfl) ⟨1825271, by rfl⟩ : syracuseStep 2433695 = 3650543) B3650543
theorem B4621063 : Blo 1621009 4621063 := bstep (se 1 (by rfl) ⟨3465797, by rfl⟩ : syracuseStep 4621063 = 6931595) B6931595
theorem B1622847 : Blo 1621009 1622847 := bstep (se 1 (by rfl) ⟨1217135, by rfl⟩ : syracuseStep 1622847 = 2434271) B2434271
theorem B1623007 : Blo 1621009 1623007 := bstep (se 1 (by rfl) ⟨1217255, by rfl⟩ : syracuseStep 1623007 = 2434511) B2434511
theorem B6161447 : Blo 1621009 6161447 := bstep (se 1 (by rfl) ⟨4621085, by rfl⟩ : syracuseStep 6161447 = 9242171) B9242171
theorem B729834569 : Blo 1621009 729834569 := bstep (se 2 (by rfl) ⟨273687963, by rfl⟩ : syracuseStep 729834569 = 547375927) B547375927
theorem B8209511 : Blo 1621009 8209511 := bstep (se 1 (by rfl) ⟨6157133, by rfl⟩ : syracuseStep 8209511 = 12314267) B12314267
theorem B2737415 : Blo 1621009 2737415 := bstep (se 1 (by rfl) ⟨2053061, by rfl⟩ : syracuseStep 2737415 = 4106123) B4106123
theorem B3122663 : Blo 1621009 3122663 := bstep (se 1 (by rfl) ⟨2341997, by rfl⟩ : syracuseStep 3122663 = 4683995) B4683995
theorem B6161903 : Blo 1621009 6161903 := bstep (se 1 (by rfl) ⟨4621427, by rfl⟩ : syracuseStep 6161903 = 9242855) B9242855
theorem B24970961 : Blo 1621009 24970961 := bstep (se 2 (by rfl) ⟨9364110, by rfl⟩ : syracuseStep 24970961 = 18728221) B18728221
theorem B8210159 : Blo 1621009 8210159 := bstep (se 1 (by rfl) ⟨6157619, by rfl⟩ : syracuseStep 8210159 = 12315239) B12315239
theorem B11855639 : Blo 1621009 11855639 := bstep (se 1 (by rfl) ⟨8891729, by rfl⟩ : syracuseStep 11855639 = 17783459) B17783459
theorem B4384639 : Blo 1621009 4384639 := bstep (se 1 (by rfl) ⟨3288479, by rfl⟩ : syracuseStep 4384639 = 6576959) B6576959
theorem B4442105 : Blo 1621009 4442105 := bstep (se 2 (by rfl) ⟨1665789, by rfl⟩ : syracuseStep 4442105 = 3331579) B3331579
theorem B3647591 : Blo 1621009 3647591 := bstep (se 1 (by rfl) ⟨2735693, by rfl⟩ : syracuseStep 3647591 = 5471387) B5471387
theorem B13158587 : Blo 1621009 13158587 := bstep (se 1 (by rfl) ⟨9868940, by rfl⟩ : syracuseStep 13158587 = 19737881) B19737881
theorem B2738495 : Blo 1621009 2738495 := bstep (se 1 (by rfl) ⟨2053871, by rfl⟩ : syracuseStep 2738495 = 4107743) B4107743
theorem B2738569 : Blo 1621009 2738569 := bstep (se 2 (by rfl) ⟨1026963, by rfl⟩ : syracuseStep 2738569 = 2053927) B2053927
theorem B5849081 : Blo 1621009 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B9996959 : Blo 1621009 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B13855535 : Blo 1621009 13855535 := bstep (se 1 (by rfl) ⟨10391651, by rfl⟩ : syracuseStep 13855535 = 20783303) B20783303
theorem B56175659 : Blo 1621009 56175659 := bstep (se 1 (by rfl) ⟨42131744, by rfl⟩ : syracuseStep 56175659 = 84263489) B84263489
theorem B5475383 : Blo 1621009 5475383 := bstep (se 1 (by rfl) ⟨4106537, by rfl⟩ : syracuseStep 5475383 = 8213075) B8213075
theorem B11685073 : Blo 1621009 11685073 := bstep (se 2 (by rfl) ⟨4381902, by rfl⟩ : syracuseStep 11685073 = 8763805) B8763805
theorem B6925819 : Blo 1621009 6925819 := bstep (se 1 (by rfl) ⟨5194364, by rfl⟩ : syracuseStep 6925819 = 10388729) B10388729
theorem B12316211 : Blo 1621009 12316211 := bstep (se 1 (by rfl) ⟨9237158, by rfl⟩ : syracuseStep 12316211 = 18474317) B18474317
theorem B2191135 : Blo 1621009 2191135 := bstep (se 1 (by rfl) ⟨1643351, by rfl⟩ : syracuseStep 2191135 = 3286703) B3286703
theorem B2191195 : Blo 1621009 2191195 := bstep (se 1 (by rfl) ⟨1643396, by rfl⟩ : syracuseStep 2191195 = 3286793) B3286793
theorem B3649697 : Blo 1621009 3649697 := bstep (se 2 (by rfl) ⟨1368636, by rfl⟩ : syracuseStep 3649697 = 2737273) B2737273
theorem B7401725 : Blo 1621009 7401725 := bstep (se 3 (by rfl) ⟨1387823, by rfl⟩ : syracuseStep 7401725 = 2775647) B2775647
theorem B1733023 : Blo 1621009 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B173216321 : Blo 1621009 173216321 := bstep (se 2 (by rfl) ⟨64956120, by rfl⟩ : syracuseStep 173216321 = 129912241) B129912241
theorem B76944491 : Blo 1621009 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B11695279 : Blo 1621009 11695279 := bstep (se 1 (by rfl) ⟨8771459, by rfl⟩ : syracuseStep 11695279 = 17542919) B17542919
theorem B1824223 : Blo 1621009 1824223 := bstep (se 1 (by rfl) ⟨1368167, by rfl⟩ : syracuseStep 1824223 = 2736335) B2736335
theorem B8214047 : Blo 1621009 8214047 := bstep (se 1 (by rfl) ⟨6160535, by rfl⟩ : syracuseStep 8214047 = 12321071) B12321071
theorem B9238049 : Blo 1621009 9238049 := bstep (se 2 (by rfl) ⟨3464268, by rfl⟩ : syracuseStep 9238049 = 6928537) B6928537
theorem B12310379 : Blo 1621009 12310379 := bstep (se 1 (by rfl) ⟨9232784, by rfl⟩ : syracuseStep 12310379 = 18465569) B18465569
theorem B3897227 : Blo 1621009 3897227 := bstep (se 1 (by rfl) ⟨2922920, by rfl⟩ : syracuseStep 3897227 = 5845841) B5845841
theorem B2308601 : Blo 1621009 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B2431535 : Blo 1621009 2431535 := bstep (se 1 (by rfl) ⟨1823651, by rfl⟩ : syracuseStep 2431535 = 3647303) B3647303
theorem B2431583 : Blo 1621009 2431583 := bstep (se 1 (by rfl) ⟨1823687, by rfl⟩ : syracuseStep 2431583 = 3647375) B3647375
theorem B13154987 : Blo 1621009 13154987 := bstep (se 1 (by rfl) ⟨9866240, by rfl⟩ : syracuseStep 13154987 = 19732481) B19732481
theorem B8215343 : Blo 1621009 8215343 := bstep (se 1 (by rfl) ⟨6161507, by rfl⟩ : syracuseStep 8215343 = 12323015) B12323015
theorem B5847871 : Blo 1621009 5847871 := bstep (se 1 (by rfl) ⟨4385903, by rfl⟩ : syracuseStep 5847871 = 8771807) B8771807
theorem B2431943 : Blo 1621009 2431943 := bstep (se 1 (by rfl) ⟨1823957, by rfl⟩ : syracuseStep 2431943 = 3647915) B3647915
theorem B1621019 : Blo 1621009 1621019 := bstep (se 1 (by rfl) ⟨1215764, by rfl⟩ : syracuseStep 1621019 = 2431529) B2431529
theorem B22191155 : Blo 1621009 22191155 := bstep (se 1 (by rfl) ⟨16643366, by rfl⟩ : syracuseStep 22191155 = 33286733) B33286733
theorem B2432063 : Blo 1621009 2432063 := bstep (se 1 (by rfl) ⟨1824047, by rfl⟩ : syracuseStep 2432063 = 3648095) B3648095
theorem B5782649 : Blo 1621009 5782649 := bstep (se 2 (by rfl) ⟨2168493, by rfl⟩ : syracuseStep 5782649 = 4336987) B4336987
theorem B6159503 : Blo 1621009 6159503 := bstep (se 1 (by rfl) ⟨4619627, by rfl⟩ : syracuseStep 6159503 = 9239255) B9239255
theorem B13155473 : Blo 1621009 13155473 := bstep (se 2 (by rfl) ⟨4933302, by rfl⟩ : syracuseStep 13155473 = 9866605) B9866605
theorem B1621159 : Blo 1621009 1621159 := bstep (se 1 (by rfl) ⟨1215869, by rfl⟩ : syracuseStep 1621159 = 2431739) B2431739
theorem B16653545 : Blo 1621009 16653545 := bstep (se 2 (by rfl) ⟨6245079, by rfl⟩ : syracuseStep 16653545 = 12490159) B12490159
theorem B1621243 : Blo 1621009 1621243 := bstep (se 1 (by rfl) ⟨1215932, by rfl⟩ : syracuseStep 1621243 = 2431865) B2431865
theorem B5471495 : Blo 1621009 5471495 := bstep (se 1 (by rfl) ⟨4103621, by rfl⟩ : syracuseStep 5471495 = 8207243) B8207243
theorem B2432303 : Blo 1621009 2432303 := bstep (se 1 (by rfl) ⟨1824227, by rfl⟩ : syracuseStep 2432303 = 3648455) B3648455
theorem B4103531 : Blo 1621009 4103531 := bstep (se 1 (by rfl) ⟨3077648, by rfl⟩ : syracuseStep 4103531 = 6155297) B6155297
theorem B42122699 : Blo 1621009 42122699 := bstep (se 1 (by rfl) ⟨31592024, by rfl⟩ : syracuseStep 42122699 = 63184049) B63184049
theorem B7790087 : Blo 1621009 7790087 := bstep (se 1 (by rfl) ⟨5842565, by rfl⟩ : syracuseStep 7790087 = 11685131) B11685131
theorem B8207891 : Blo 1621009 8207891 := bstep (se 1 (by rfl) ⟨6155918, by rfl⟩ : syracuseStep 8207891 = 12311837) B12311837
theorem B2432543 : Blo 1621009 2432543 := bstep (se 1 (by rfl) ⟨1824407, by rfl⟩ : syracuseStep 2432543 = 3648815) B3648815
theorem B2432567 : Blo 1621009 2432567 := bstep (se 1 (by rfl) ⟨1824425, by rfl⟩ : syracuseStep 2432567 = 3648851) B3648851
theorem B12828239 : Blo 1621009 12828239 := bstep (se 1 (by rfl) ⟨9621179, by rfl⟩ : syracuseStep 12828239 = 19242359) B19242359
theorem B2432735 : Blo 1621009 2432735 := bstep (se 1 (by rfl) ⟨1824551, by rfl⟩ : syracuseStep 2432735 = 3649103) B3649103
theorem B1621743 : Blo 1621009 1621743 := bstep (se 1 (by rfl) ⟨1216307, by rfl⟩ : syracuseStep 1621743 = 2432615) B2432615
theorem B1621851 : Blo 1621009 1621851 := bstep (se 1 (by rfl) ⟨1216388, by rfl⟩ : syracuseStep 1621851 = 2432777) B2432777
theorem B2736031 : Blo 1621009 2736031 := bstep (se 1 (by rfl) ⟨2052023, by rfl⟩ : syracuseStep 2736031 = 4104047) B4104047
theorem B2432927 : Blo 1621009 2432927 := bstep (se 1 (by rfl) ⟨1824695, by rfl⟩ : syracuseStep 2432927 = 3649391) B3649391
theorem B1621999 : Blo 1621009 1621999 := bstep (se 1 (by rfl) ⟨1216499, by rfl⟩ : syracuseStep 1621999 = 2432999) B2432999
theorem B1622063 : Blo 1621009 1622063 := bstep (se 1 (by rfl) ⟨1216547, by rfl⟩ : syracuseStep 1622063 = 2433095) B2433095
theorem B2433131 : Blo 1621009 2433131 := bstep (se 1 (by rfl) ⟨1824848, by rfl⟩ : syracuseStep 2433131 = 3649697) B3649697
theorem B1622143 : Blo 1621009 1622143 := bstep (se 1 (by rfl) ⟨1216607, by rfl⟩ : syracuseStep 1622143 = 2433215) B2433215
theorem B1622267 : Blo 1621009 1622267 := bstep (se 1 (by rfl) ⟨1216700, by rfl⟩ : syracuseStep 1622267 = 2433401) B2433401
theorem B1622463 : Blo 1621009 1622463 := bstep (se 1 (by rfl) ⟨1216847, by rfl⟩ : syracuseStep 1622463 = 2433695) B2433695
theorem B2310697 : Blo 1621009 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B486556379 : Blo 1621009 486556379 := bstep (se 1 (by rfl) ⟨364917284, by rfl⟩ : syracuseStep 486556379 = 729834569) B729834569
theorem B5473007 : Blo 1621009 5473007 := bstep (se 1 (by rfl) ⟨4104755, by rfl⟩ : syracuseStep 5473007 = 8209511) B8209511
theorem B6161417 : Blo 1621009 6161417 := bstep (se 2 (by rfl) ⟨2310531, by rfl⟩ : syracuseStep 6161417 = 4621063) B4621063
theorem B5473439 : Blo 1621009 5473439 := bstep (se 1 (by rfl) ⟨4105079, by rfl⟩ : syracuseStep 5473439 = 8210159) B8210159
theorem B2598151 : Blo 1621009 2598151 := bstep (se 1 (by rfl) ⟨1948613, by rfl⟩ : syracuseStep 2598151 = 3897227) B3897227
theorem B9234425 : Blo 1621009 9234425 := bstep (se 2 (by rfl) ⟨3462909, by rfl⟩ : syracuseStep 9234425 = 6925819) B6925819
theorem B4106335 : Blo 1621009 4106335 := bstep (se 1 (by rfl) ⟨3079751, by rfl⟩ : syracuseStep 4106335 = 6159503) B6159503
theorem B11102363 : Blo 1621009 11102363 := bstep (se 1 (by rfl) ⟨8326772, by rfl⟩ : syracuseStep 11102363 = 16653545) B16653545
theorem B3647663 : Blo 1621009 3647663 := bstep (se 1 (by rfl) ⟨2735747, by rfl⟩ : syracuseStep 3647663 = 5471495) B5471495
theorem B8210807 : Blo 1621009 8210807 := bstep (se 1 (by rfl) ⟨6158105, by rfl⟩ : syracuseStep 8210807 = 12316211) B12316211
theorem B3648041 : Blo 1621009 3648041 := bstep (se 2 (by rfl) ⟨1368015, by rfl⟩ : syracuseStep 3648041 = 2736031) B2736031
theorem B2599643 : Blo 1621009 2599643 := bstep (se 1 (by rfl) ⟨1949732, by rfl⟩ : syracuseStep 2599643 = 3899465) B3899465
theorem B4934483 : Blo 1621009 4934483 := bstep (se 1 (by rfl) ⟨3700862, by rfl⟩ : syracuseStep 4934483 = 7401725) B7401725
theorem B3648383 : Blo 1621009 3648383 := bstep (se 1 (by rfl) ⟨2736287, by rfl⟩ : syracuseStep 3648383 = 5472575) B5472575
theorem B15420397 : Blo 1621009 15420397 := bstep (se 3 (by rfl) ⟨2891324, by rfl⟩ : syracuseStep 15420397 = 5782649) B5782649
theorem B115477547 : Blo 1621009 115477547 := bstep (se 1 (by rfl) ⟨86608160, by rfl⟩ : syracuseStep 115477547 = 173216321) B173216321
theorem B4107631 : Blo 1621009 4107631 := bstep (se 1 (by rfl) ⟨3080723, by rfl⟩ : syracuseStep 4107631 = 6161447) B6161447
theorem B4107935 : Blo 1621009 4107935 := bstep (se 1 (by rfl) ⟨3080951, by rfl⟩ : syracuseStep 4107935 = 6161903) B6161903
theorem B5476031 : Blo 1621009 5476031 := bstep (se 1 (by rfl) ⟨4107023, by rfl⟩ : syracuseStep 5476031 = 8214047) B8214047
theorem B6156269 : Blo 1621009 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B2961403 : Blo 1621009 2961403 := bstep (se 1 (by rfl) ⟨2221052, by rfl⟩ : syracuseStep 2961403 = 4442105) B4442105
theorem B15593705 : Blo 1621009 15593705 := bstep (se 2 (by rfl) ⟨5847639, by rfl⟩ : syracuseStep 15593705 = 11695279) B11695279
theorem B6664639 : Blo 1621009 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B8769991 : Blo 1621009 8769991 := bstep (se 1 (by rfl) ⟨6577493, by rfl⟩ : syracuseStep 8769991 = 13154987) B13154987
theorem B9237023 : Blo 1621009 9237023 := bstep (se 1 (by rfl) ⟨6927767, by rfl⟩ : syracuseStep 9237023 = 13855535) B13855535
theorem B5476895 : Blo 1621009 5476895 := bstep (se 1 (by rfl) ⟨4107671, by rfl⟩ : syracuseStep 5476895 = 8215343) B8215343
theorem B66589229 : Blo 1621009 66589229 := bstep (se 3 (by rfl) ⟨12485480, by rfl⟩ : syracuseStep 66589229 = 24970961) B24970961
theorem B37450439 : Blo 1621009 37450439 := bstep (se 1 (by rfl) ⟨28087829, by rfl⟩ : syracuseStep 37450439 = 56175659) B56175659
theorem B3650255 : Blo 1621009 3650255 := bstep (se 1 (by rfl) ⟨2737691, by rfl⟩ : syracuseStep 3650255 = 5475383) B5475383
theorem B8770315 : Blo 1621009 8770315 := bstep (se 1 (by rfl) ⟨6577736, by rfl⟩ : syracuseStep 8770315 = 13155473) B13155473
theorem B2921513 : Blo 1621009 2921513 := bstep (se 2 (by rfl) ⟨1095567, by rfl⟩ : syracuseStep 2921513 = 2191135) B2191135
theorem B2921593 : Blo 1621009 2921593 := bstep (se 2 (by rfl) ⟨1095597, by rfl⟩ : syracuseStep 2921593 = 2191195) B2191195
theorem B5846185 : Blo 1621009 5846185 := bstep (se 2 (by rfl) ⟨2192319, by rfl⟩ : syracuseStep 5846185 = 4384639) B4384639
theorem B23385833 : Blo 1621009 23385833 := bstep (se 2 (by rfl) ⟨8769687, by rfl⟩ : syracuseStep 23385833 = 17539375) B17539375
theorem B3651425 : Blo 1621009 3651425 := bstep (se 2 (by rfl) ⟨1369284, by rfl⟩ : syracuseStep 3651425 = 2738569) B2738569
theorem B51296327 : Blo 1621009 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B1824943 : Blo 1621009 1824943 := bstep (se 1 (by rfl) ⟨1368707, by rfl⟩ : syracuseStep 1824943 = 2737415) B2737415
theorem B6158699 : Blo 1621009 6158699 := bstep (se 1 (by rfl) ⟨4619024, by rfl⟩ : syracuseStep 6158699 = 9238049) B9238049
theorem B7797161 : Blo 1621009 7797161 := bstep (se 2 (by rfl) ⟨2923935, by rfl⟩ : syracuseStep 7797161 = 5847871) B5847871
theorem B7903759 : Blo 1621009 7903759 := bstep (se 1 (by rfl) ⟨5927819, by rfl⟩ : syracuseStep 7903759 = 11855639) B11855639
theorem B8206919 : Blo 1621009 8206919 := bstep (se 1 (by rfl) ⟨6155189, by rfl⟩ : syracuseStep 8206919 = 12310379) B12310379
theorem B2431727 : Blo 1621009 2431727 := bstep (se 1 (by rfl) ⟨1823795, by rfl⟩ : syracuseStep 2431727 = 3647591) B3647591
theorem B8772391 : Blo 1621009 8772391 := bstep (se 1 (by rfl) ⟨6579293, by rfl⟩ : syracuseStep 8772391 = 13158587) B13158587
theorem B1825663 : Blo 1621009 1825663 := bstep (se 1 (by rfl) ⟨1369247, by rfl⟩ : syracuseStep 1825663 = 2738495) B2738495
theorem B15580097 : Blo 1621009 15580097 := bstep (se 2 (by rfl) ⟨5842536, by rfl⟩ : syracuseStep 15580097 = 11685073) B11685073
theorem B3899387 : Blo 1621009 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B1621023 : Blo 1621009 1621023 := bstep (se 1 (by rfl) ⟨1215767, by rfl⟩ : syracuseStep 1621023 = 2431535) B2431535
theorem B1621055 : Blo 1621009 1621055 := bstep (se 1 (by rfl) ⟨1215791, by rfl⟩ : syracuseStep 1621055 = 2431583) B2431583
theorem B2432297 : Blo 1621009 2432297 := bstep (se 2 (by rfl) ⟨912111, by rfl⟩ : syracuseStep 2432297 = 1824223) B1824223
theorem B1621295 : Blo 1621009 1621295 := bstep (se 1 (by rfl) ⟨1215971, by rfl⟩ : syracuseStep 1621295 = 2431943) B2431943
theorem B14794103 : Blo 1621009 14794103 := bstep (se 1 (by rfl) ⟨11095577, by rfl⟩ : syracuseStep 14794103 = 22191155) B22191155
theorem B1621375 : Blo 1621009 1621375 := bstep (se 1 (by rfl) ⟨1216031, by rfl⟩ : syracuseStep 1621375 = 2432063) B2432063
theorem B1621535 : Blo 1621009 1621535 := bstep (se 1 (by rfl) ⟨1216151, by rfl⟩ : syracuseStep 1621535 = 2432303) B2432303
theorem B2735687 : Blo 1621009 2735687 := bstep (se 1 (by rfl) ⟨2051765, by rfl⟩ : syracuseStep 2735687 = 4103531) B4103531
theorem B28081799 : Blo 1621009 28081799 := bstep (se 1 (by rfl) ⟨21061349, by rfl⟩ : syracuseStep 28081799 = 42122699) B42122699
theorem B5193391 : Blo 1621009 5193391 := bstep (se 1 (by rfl) ⟨3895043, by rfl⟩ : syracuseStep 5193391 = 7790087) B7790087
theorem B5471927 : Blo 1621009 5471927 := bstep (se 1 (by rfl) ⟨4103945, by rfl⟩ : syracuseStep 5471927 = 8207891) B8207891
theorem B1621695 : Blo 1621009 1621695 := bstep (se 1 (by rfl) ⟨1216271, by rfl⟩ : syracuseStep 1621695 = 2432543) B2432543
theorem B1621711 : Blo 1621009 1621711 := bstep (se 1 (by rfl) ⟨1216283, by rfl⟩ : syracuseStep 1621711 = 2432567) B2432567
theorem B8552159 : Blo 1621009 8552159 := bstep (se 1 (by rfl) ⟨6414119, by rfl⟩ : syracuseStep 8552159 = 12828239) B12828239
theorem B33308405 : Blo 1621009 33308405 := bstep (se 5 (by rfl) ⟨1561331, by rfl⟩ : syracuseStep 33308405 = 3122663) B3122663
theorem B1621823 : Blo 1621009 1621823 := bstep (se 1 (by rfl) ⟨1216367, by rfl⟩ : syracuseStep 1621823 = 2432735) B2432735
theorem B1621951 : Blo 1621009 1621951 := bstep (se 1 (by rfl) ⟨1216463, by rfl⟩ : syracuseStep 1621951 = 2432927) B2432927
theorem B1622087 : Blo 1621009 1622087 := bstep (se 1 (by rfl) ⟨1216565, by rfl⟩ : syracuseStep 1622087 = 2433131) B2433131
theorem B10395803 : Blo 1621009 10395803 := bstep (se 1 (by rfl) ⟨7796852, by rfl⟩ : syracuseStep 10395803 = 15593705) B15593705
theorem B2433257 : Blo 1621009 2433257 := bstep (se 2 (by rfl) ⟨912471, by rfl⟩ : syracuseStep 2433257 = 1824943) B1824943
theorem B44392819 : Blo 1621009 44392819 := bstep (se 1 (by rfl) ⟨33294614, by rfl⟩ : syracuseStep 44392819 = 66589229) B66589229
theorem B31162805 : Blo 1621009 31162805 := bstep (se 5 (by rfl) ⟨1460756, by rfl⟩ : syracuseStep 31162805 = 2921513) B2921513
theorem B2433503 : Blo 1621009 2433503 := bstep (se 1 (by rfl) ⟨1825127, by rfl⟩ : syracuseStep 2433503 = 3650255) B3650255
theorem B324370919 : Blo 1621009 324370919 := bstep (se 1 (by rfl) ⟨243278189, by rfl⟩ : syracuseStep 324370919 = 486556379) B486556379
theorem B3080929 : Blo 1621009 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B15590555 : Blo 1621009 15590555 := bstep (se 1 (by rfl) ⟨11692916, by rfl⟩ : syracuseStep 15590555 = 23385833) B23385833
theorem B2434217 : Blo 1621009 2434217 := bstep (se 2 (by rfl) ⟨912831, by rfl⟩ : syracuseStep 2434217 = 1825663) B1825663
theorem B2434283 : Blo 1621009 2434283 := bstep (se 1 (by rfl) ⟨1825712, by rfl⟩ : syracuseStep 2434283 = 3651425) B3651425
theorem B4105799 : Blo 1621009 4105799 := bstep (se 1 (by rfl) ⟨3079349, by rfl⟩ : syracuseStep 4105799 = 6158699) B6158699
theorem B5473871 : Blo 1621009 5473871 := bstep (se 1 (by rfl) ⟨4105403, by rfl⟩ : syracuseStep 5473871 = 8210807) B8210807
theorem B6924521 : Blo 1621009 6924521 := bstep (se 2 (by rfl) ⟨2596695, by rfl⟩ : syracuseStep 6924521 = 5193391) B5193391
theorem B18721199 : Blo 1621009 18721199 := bstep (se 1 (by rfl) ⟨14040899, by rfl⟩ : syracuseStep 18721199 = 28081799) B28081799
theorem B2738623 : Blo 1621009 2738623 := bstep (se 1 (by rfl) ⟨2053967, by rfl⟩ : syracuseStep 2738623 = 4107935) B4107935
theorem B3647951 : Blo 1621009 3647951 := bstep (se 1 (by rfl) ⟨2735963, by rfl⟩ : syracuseStep 3647951 = 5471927) B5471927
theorem B10398365 : Blo 1621009 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B307940125 : Blo 1621009 307940125 := bstep (se 3 (by rfl) ⟨57738773, by rfl⟩ : syracuseStep 307940125 = 115477547) B115477547
theorem B5475113 : Blo 1621009 5475113 := bstep (se 2 (by rfl) ⟨2053167, by rfl⟩ : syracuseStep 5475113 = 4106335) B4106335
theorem B3648671 : Blo 1621009 3648671 := bstep (se 1 (by rfl) ⟨2736503, by rfl⟩ : syracuseStep 3648671 = 5473007) B5473007
theorem B11693321 : Blo 1621009 11693321 := bstep (se 2 (by rfl) ⟨4384995, by rfl⟩ : syracuseStep 11693321 = 8769991) B8769991
theorem B4107611 : Blo 1621009 4107611 := bstep (se 1 (by rfl) ⟨3080708, by rfl⟩ : syracuseStep 4107611 = 6161417) B6161417
theorem B10538345 : Blo 1621009 10538345 := bstep (se 2 (by rfl) ⟨3951879, by rfl⟩ : syracuseStep 10538345 = 7903759) B7903759
theorem B3648959 : Blo 1621009 3648959 := bstep (se 1 (by rfl) ⟨2736719, by rfl⟩ : syracuseStep 3648959 = 5473439) B5473439
theorem B11693753 : Blo 1621009 11693753 := bstep (se 2 (by rfl) ⟨4385157, by rfl⟩ : syracuseStep 11693753 = 8770315) B8770315
theorem B6156283 : Blo 1621009 6156283 := bstep (se 1 (by rfl) ⟨4617212, by rfl⟩ : syracuseStep 6156283 = 9234425) B9234425
theorem B34197551 : Blo 1621009 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B7401575 : Blo 1621009 7401575 := bstep (se 1 (by rfl) ⟨5551181, by rfl⟩ : syracuseStep 7401575 = 11102363) B11102363
theorem B3895457 : Blo 1621009 3895457 := bstep (se 2 (by rfl) ⟨1460796, by rfl⟩ : syracuseStep 3895457 = 2921593) B2921593
theorem B7794913 : Blo 1621009 7794913 := bstep (se 2 (by rfl) ⟨2923092, by rfl⟩ : syracuseStep 7794913 = 5846185) B5846185
theorem B5198107 : Blo 1621009 5198107 := bstep (se 1 (by rfl) ⟨3898580, by rfl⟩ : syracuseStep 5198107 = 7797161) B7797161
theorem B1733095 : Blo 1621009 1733095 := bstep (se 1 (by rfl) ⟨1299821, by rfl⟩ : syracuseStep 1733095 = 2599643) B2599643
theorem B5476841 : Blo 1621009 5476841 := bstep (se 2 (by rfl) ⟨2053815, by rfl⟩ : syracuseStep 5476841 = 4107631) B4107631
theorem B3289655 : Blo 1621009 3289655 := bstep (se 1 (by rfl) ⟨2467241, by rfl⟩ : syracuseStep 3289655 = 4934483) B4934483
theorem B1823791 : Blo 1621009 1823791 := bstep (se 1 (by rfl) ⟨1367843, by rfl⟩ : syracuseStep 1823791 = 2735687) B2735687
theorem B3650687 : Blo 1621009 3650687 := bstep (se 1 (by rfl) ⟨2738015, by rfl⟩ : syracuseStep 3650687 = 5476031) B5476031
theorem B22205603 : Blo 1621009 22205603 := bstep (se 1 (by rfl) ⟨16654202, by rfl⟩ : syracuseStep 22205603 = 33308405) B33308405
theorem B6158015 : Blo 1621009 6158015 := bstep (se 1 (by rfl) ⟨4618511, by rfl⟩ : syracuseStep 6158015 = 9237023) B9237023
theorem B3651263 : Blo 1621009 3651263 := bstep (se 1 (by rfl) ⟨2738447, by rfl⟩ : syracuseStep 3651263 = 5476895) B5476895
theorem B24966959 : Blo 1621009 24966959 := bstep (se 1 (by rfl) ⟨18725219, by rfl⟩ : syracuseStep 24966959 = 37450439) B37450439
theorem B8886185 : Blo 1621009 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B11696521 : Blo 1621009 11696521 := bstep (se 2 (by rfl) ⟨4386195, by rfl⟩ : syracuseStep 11696521 = 8772391) B8772391
theorem B20560529 : Blo 1621009 20560529 := bstep (se 2 (by rfl) ⟨7710198, by rfl⟩ : syracuseStep 20560529 = 15420397) B15420397
theorem B2431775 : Blo 1621009 2431775 := bstep (se 1 (by rfl) ⟨1823831, by rfl⟩ : syracuseStep 2431775 = 3647663) B3647663
theorem B3464201 : Blo 1621009 3464201 := bstep (se 2 (by rfl) ⟨1299075, by rfl⟩ : syracuseStep 3464201 = 2598151) B2598151
theorem B2432027 : Blo 1621009 2432027 := bstep (se 1 (by rfl) ⟨1824020, by rfl⟩ : syracuseStep 2432027 = 3648041) B3648041
theorem B5471279 : Blo 1621009 5471279 := bstep (se 1 (by rfl) ⟨4103459, by rfl⟩ : syracuseStep 5471279 = 8206919) B8206919
theorem B1621151 : Blo 1621009 1621151 := bstep (se 1 (by rfl) ⟨1215863, by rfl⟩ : syracuseStep 1621151 = 2431727) B2431727
theorem B2432255 : Blo 1621009 2432255 := bstep (se 1 (by rfl) ⟨1824191, by rfl⟩ : syracuseStep 2432255 = 3648383) B3648383
theorem B10386731 : Blo 1621009 10386731 := bstep (se 1 (by rfl) ⟨7790048, by rfl⟩ : syracuseStep 10386731 = 15580097) B15580097
theorem B1621531 : Blo 1621009 1621531 := bstep (se 1 (by rfl) ⟨1216148, by rfl⟩ : syracuseStep 1621531 = 2432297) B2432297
theorem B9862735 : Blo 1621009 9862735 := bstep (se 1 (by rfl) ⟨7397051, by rfl⟩ : syracuseStep 9862735 = 14794103) B14794103
theorem B5701439 : Blo 1621009 5701439 := bstep (se 1 (by rfl) ⟨4276079, by rfl⟩ : syracuseStep 5701439 = 8552159) B8552159
theorem B15794149 : Blo 1621009 15794149 := bstep (se 4 (by rfl) ⟨1480701, by rfl⟩ : syracuseStep 15794149 = 2961403) B2961403
theorem B4104179 : Blo 1621009 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B22798367 : Blo 1621009 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B6930535 : Blo 1621009 6930535 := bstep (se 1 (by rfl) ⟨5197901, by rfl⟩ : syracuseStep 6930535 = 10395803) B10395803
theorem B1622171 : Blo 1621009 1622171 := bstep (se 1 (by rfl) ⟨1216628, by rfl⟩ : syracuseStep 1622171 = 2433257) B2433257
theorem B20775203 : Blo 1621009 20775203 := bstep (se 1 (by rfl) ⟨15581402, by rfl⟩ : syracuseStep 20775203 = 31162805) B31162805
theorem B1622335 : Blo 1621009 1622335 := bstep (se 1 (by rfl) ⟨1216751, by rfl⟩ : syracuseStep 1622335 = 2433503) B2433503
theorem B6930809 : Blo 1621009 6930809 := bstep (se 2 (by rfl) ⟨2599053, by rfl⟩ : syracuseStep 6930809 = 5198107) B5198107
theorem B10387885 : Blo 1621009 10387885 := bstep (se 3 (by rfl) ⟨1947728, by rfl⟩ : syracuseStep 10387885 = 3895457) B3895457
theorem B2433791 : Blo 1621009 2433791 := bstep (se 1 (by rfl) ⟨1825343, by rfl⟩ : syracuseStep 2433791 = 3650687) B3650687
theorem B14803735 : Blo 1621009 14803735 := bstep (se 1 (by rfl) ⟨11102801, by rfl⟩ : syracuseStep 14803735 = 22205603) B22205603
theorem B1622811 : Blo 1621009 1622811 := bstep (se 1 (by rfl) ⟨1217108, by rfl⟩ : syracuseStep 1622811 = 2434217) B2434217
theorem B1622855 : Blo 1621009 1622855 := bstep (se 1 (by rfl) ⟨1217141, by rfl⟩ : syracuseStep 1622855 = 2434283) B2434283
theorem B2737199 : Blo 1621009 2737199 := bstep (se 1 (by rfl) ⟨2052899, by rfl⟩ : syracuseStep 2737199 = 4105799) B4105799
theorem B4105343 : Blo 1621009 4105343 := bstep (se 1 (by rfl) ⟨3079007, by rfl⟩ : syracuseStep 4105343 = 6158015) B6158015
theorem B2434175 : Blo 1621009 2434175 := bstep (se 1 (by rfl) ⟨1825631, by rfl⟩ : syracuseStep 2434175 = 3651263) B3651263
theorem B5924123 : Blo 1621009 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B13707019 : Blo 1621009 13707019 := bstep (se 1 (by rfl) ⟨10280264, by rfl⟩ : syracuseStep 13707019 = 20560529) B20560529
theorem B6932243 : Blo 1621009 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B3647519 : Blo 1621009 3647519 := bstep (se 1 (by rfl) ⟨2735639, by rfl⟩ : syracuseStep 3647519 = 5471279) B5471279
theorem B13150313 : Blo 1621009 13150313 := bstep (se 2 (by rfl) ⟨4931367, by rfl⟩ : syracuseStep 13150313 = 9862735) B9862735
theorem B66578557 : Blo 1621009 66578557 := bstep (se 3 (by rfl) ⟨12483479, by rfl⟩ : syracuseStep 66578557 = 24966959) B24966959
theorem B6924487 : Blo 1621009 6924487 := bstep (se 1 (by rfl) ⟨5193365, by rfl⟩ : syracuseStep 6924487 = 10386731) B10386731
theorem B2738407 : Blo 1621009 2738407 := bstep (se 1 (by rfl) ⟨2053805, by rfl⟩ : syracuseStep 2738407 = 4107611) B4107611
theorem B9243173 : Blo 1621009 9243173 := bstep (se 4 (by rfl) ⟨866547, by rfl⟩ : syracuseStep 9243173 = 1733095) B1733095
theorem B19737533 : Blo 1621009 19737533 := bstep (se 3 (by rfl) ⟨3700787, by rfl⟩ : syracuseStep 19737533 = 7401575) B7401575
theorem B216247279 : Blo 1621009 216247279 := bstep (se 1 (by rfl) ⟨162185459, by rfl⟩ : syracuseStep 216247279 = 324370919) B324370919
theorem B59190425 : Blo 1621009 59190425 := bstep (se 2 (by rfl) ⟨22196409, by rfl⟩ : syracuseStep 59190425 = 44392819) B44392819
theorem B4107905 : Blo 1621009 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B410586833 : Blo 1621009 410586833 := bstep (se 2 (by rfl) ⟨153970062, by rfl⟩ : syracuseStep 410586833 = 307940125) B307940125
theorem B3649247 : Blo 1621009 3649247 := bstep (se 1 (by rfl) ⟨2736935, by rfl⟩ : syracuseStep 3649247 = 5473871) B5473871
theorem B4616347 : Blo 1621009 4616347 := bstep (se 1 (by rfl) ⟨3462260, by rfl⟩ : syracuseStep 4616347 = 6924521) B6924521
theorem B12480799 : Blo 1621009 12480799 := bstep (se 1 (by rfl) ⟨9360599, by rfl⟩ : syracuseStep 12480799 = 18721199) B18721199
theorem B3650075 : Blo 1621009 3650075 := bstep (se 1 (by rfl) ⟨2737556, by rfl⟩ : syracuseStep 3650075 = 5475113) B5475113
theorem B7795547 : Blo 1621009 7795547 := bstep (se 1 (by rfl) ⟨5846660, by rfl⟩ : syracuseStep 7795547 = 11693321) B11693321
theorem B7025563 : Blo 1621009 7025563 := bstep (se 1 (by rfl) ⟨5269172, by rfl⟩ : syracuseStep 7025563 = 10538345) B10538345
theorem B7795835 : Blo 1621009 7795835 := bstep (se 1 (by rfl) ⟨5846876, by rfl⟩ : syracuseStep 7795835 = 11693753) B11693753
theorem B21058865 : Blo 1621009 21058865 := bstep (se 2 (by rfl) ⟨7897074, by rfl⟩ : syracuseStep 21058865 = 15794149) B15794149
theorem B10393217 : Blo 1621009 10393217 := bstep (se 2 (by rfl) ⟨3897456, by rfl⟩ : syracuseStep 10393217 = 7794913) B7794913
theorem B3651227 : Blo 1621009 3651227 := bstep (se 1 (by rfl) ⟨2738420, by rfl⟩ : syracuseStep 3651227 = 5476841) B5476841
theorem B2193103 : Blo 1621009 2193103 := bstep (se 1 (by rfl) ⟨1644827, by rfl⟩ : syracuseStep 2193103 = 3289655) B3289655
theorem B15595361 : Blo 1621009 15595361 := bstep (se 2 (by rfl) ⟨5848260, by rfl⟩ : syracuseStep 15595361 = 11696521) B11696521
theorem B3651497 : Blo 1621009 3651497 := bstep (se 2 (by rfl) ⟨1369311, by rfl⟩ : syracuseStep 3651497 = 2738623) B2738623
theorem B10393703 : Blo 1621009 10393703 := bstep (se 1 (by rfl) ⟨7795277, by rfl⟩ : syracuseStep 10393703 = 15590555) B15590555
theorem B2431721 : Blo 1621009 2431721 := bstep (se 2 (by rfl) ⟨911895, by rfl⟩ : syracuseStep 2431721 = 1823791) B1823791
theorem B2431967 : Blo 1621009 2431967 := bstep (se 1 (by rfl) ⟨1823975, by rfl⟩ : syracuseStep 2431967 = 3647951) B3647951
theorem B1621183 : Blo 1621009 1621183 := bstep (se 1 (by rfl) ⟨1215887, by rfl⟩ : syracuseStep 1621183 = 2431775) B2431775
theorem B2309467 : Blo 1621009 2309467 := bstep (se 1 (by rfl) ⟨1732100, by rfl⟩ : syracuseStep 2309467 = 3464201) B3464201
theorem B1621351 : Blo 1621009 1621351 := bstep (se 1 (by rfl) ⟨1216013, by rfl⟩ : syracuseStep 1621351 = 2432027) B2432027
theorem B2432447 : Blo 1621009 2432447 := bstep (se 1 (by rfl) ⟨1824335, by rfl⟩ : syracuseStep 2432447 = 3648671) B3648671
theorem B15203837 : Blo 1621009 15203837 := bstep (se 3 (by rfl) ⟨2850719, by rfl⟩ : syracuseStep 15203837 = 5701439) B5701439
theorem B1621503 : Blo 1621009 1621503 := bstep (se 1 (by rfl) ⟨1216127, by rfl⟩ : syracuseStep 1621503 = 2432255) B2432255
theorem B2432639 : Blo 1621009 2432639 := bstep (se 1 (by rfl) ⟨1824479, by rfl⟩ : syracuseStep 2432639 = 3648959) B3648959
theorem B2736119 : Blo 1621009 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B8208377 : Blo 1621009 8208377 := bstep (se 2 (by rfl) ⟨3078141, by rfl⟩ : syracuseStep 8208377 = 6156283) B6156283
theorem B9240713 : Blo 1621009 9240713 := bstep (se 2 (by rfl) ⟨3465267, by rfl⟩ : syracuseStep 9240713 = 6930535) B6930535
theorem B4620539 : Blo 1621009 4620539 := bstep (se 1 (by rfl) ⟨3465404, by rfl⟩ : syracuseStep 4620539 = 6930809) B6930809
theorem B9232649 : Blo 1621009 9232649 := bstep (se 2 (by rfl) ⟨3462243, by rfl⟩ : syracuseStep 9232649 = 6924487) B6924487
theorem B2433383 : Blo 1621009 2433383 := bstep (se 1 (by rfl) ⟨1825037, by rfl⟩ : syracuseStep 2433383 = 3650075) B3650075
theorem B1622527 : Blo 1621009 1622527 := bstep (se 1 (by rfl) ⟨1216895, by rfl⟩ : syracuseStep 1622527 = 2433791) B2433791
theorem B2736895 : Blo 1621009 2736895 := bstep (se 1 (by rfl) ⟨2052671, by rfl⟩ : syracuseStep 2736895 = 4105343) B4105343
theorem B1622783 : Blo 1621009 1622783 := bstep (se 1 (by rfl) ⟨1217087, by rfl⟩ : syracuseStep 1622783 = 2434175) B2434175
theorem B3949415 : Blo 1621009 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B2434151 : Blo 1621009 2434151 := bstep (se 1 (by rfl) ⟨1825613, by rfl⟩ : syracuseStep 2434151 = 3651227) B3651227
theorem B10396907 : Blo 1621009 10396907 := bstep (se 1 (by rfl) ⟨7797680, by rfl⟩ : syracuseStep 10396907 = 15595361) B15595361
theorem B2434331 : Blo 1621009 2434331 := bstep (se 1 (by rfl) ⟨1825748, by rfl⟩ : syracuseStep 2434331 = 3651497) B3651497
theorem B8766875 : Blo 1621009 8766875 := bstep (se 1 (by rfl) ⟨6575156, by rfl⟩ : syracuseStep 8766875 = 13150313) B13150313
theorem B6162115 : Blo 1621009 6162115 := bstep (se 1 (by rfl) ⟨4621586, by rfl⟩ : syracuseStep 6162115 = 9243173) B9243173
theorem B10135891 : Blo 1621009 10135891 := bstep (se 1 (by rfl) ⟨7601918, by rfl⟩ : syracuseStep 10135891 = 15203837) B15203837
theorem B2738603 : Blo 1621009 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B15198911 : Blo 1621009 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B88771409 : Blo 1621009 88771409 := bstep (se 2 (by rfl) ⟨33289278, by rfl⟩ : syracuseStep 88771409 = 66578557) B66578557
theorem B6155129 : Blo 1621009 6155129 := bstep (se 2 (by rfl) ⟨2308173, by rfl⟩ : syracuseStep 6155129 = 4616347) B4616347
theorem B16641065 : Blo 1621009 16641065 := bstep (se 2 (by rfl) ⟨6240399, by rfl⟩ : syracuseStep 16641065 = 12480799) B12480799
theorem B5197031 : Blo 1621009 5197031 := bstep (se 1 (by rfl) ⟨3897773, by rfl⟩ : syracuseStep 5197031 = 7795547) B7795547
theorem B5197223 : Blo 1621009 5197223 := bstep (se 1 (by rfl) ⟨3897917, by rfl⟩ : syracuseStep 5197223 = 7795835) B7795835
theorem B19738313 : Blo 1621009 19738313 := bstep (se 2 (by rfl) ⟨7401867, by rfl⟩ : syracuseStep 19738313 = 14803735) B14803735
theorem B9367417 : Blo 1621009 9367417 := bstep (se 2 (by rfl) ⟨3512781, by rfl⟩ : syracuseStep 9367417 = 7025563) B7025563
theorem B288329705 : Blo 1621009 288329705 := bstep (se 2 (by rfl) ⟨108123639, by rfl⟩ : syracuseStep 288329705 = 216247279) B216247279
theorem B18485981 : Blo 1621009 18485981 := bstep (se 3 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 18485981 = 6932243) B6932243
theorem B273724555 : Blo 1621009 273724555 := bstep (se 1 (by rfl) ⟨205293416, by rfl⟩ : syracuseStep 273724555 = 410586833) B410586833
theorem B1824079 : Blo 1621009 1824079 := bstep (se 1 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 1824079 = 2736119) B2736119
theorem B13850135 : Blo 1621009 13850135 := bstep (se 1 (by rfl) ⟨10387601, by rfl⟩ : syracuseStep 13850135 = 20775203) B20775203
theorem B3651209 : Blo 1621009 3651209 := bstep (se 2 (by rfl) ⟨1369203, by rfl⟩ : syracuseStep 3651209 = 2738407) B2738407
theorem B13850513 : Blo 1621009 13850513 := bstep (se 2 (by rfl) ⟨5193942, by rfl⟩ : syracuseStep 13850513 = 10387885) B10387885
theorem B1824799 : Blo 1621009 1824799 := bstep (se 1 (by rfl) ⟨1368599, by rfl⟩ : syracuseStep 1824799 = 2737199) B2737199
theorem B14039243 : Blo 1621009 14039243 := bstep (se 1 (by rfl) ⟨10529432, by rfl⟩ : syracuseStep 14039243 = 21058865) B21058865
theorem B6928811 : Blo 1621009 6928811 := bstep (se 1 (by rfl) ⟨5196608, by rfl⟩ : syracuseStep 6928811 = 10393217) B10393217
theorem B2431679 : Blo 1621009 2431679 := bstep (se 1 (by rfl) ⟨1823759, by rfl⟩ : syracuseStep 2431679 = 3647519) B3647519
theorem B6929135 : Blo 1621009 6929135 := bstep (se 1 (by rfl) ⟨5196851, by rfl⟩ : syracuseStep 6929135 = 10393703) B10393703
theorem B3079289 : Blo 1621009 3079289 := bstep (se 2 (by rfl) ⟨1154733, by rfl⟩ : syracuseStep 3079289 = 2309467) B2309467
theorem B1621147 : Blo 1621009 1621147 := bstep (se 1 (by rfl) ⟨1215860, by rfl⟩ : syracuseStep 1621147 = 2431721) B2431721
theorem B1621311 : Blo 1621009 1621311 := bstep (se 1 (by rfl) ⟨1215983, by rfl⟩ : syracuseStep 1621311 = 2431967) B2431967
theorem B39460283 : Blo 1621009 39460283 := bstep (se 1 (by rfl) ⟨29595212, by rfl⟩ : syracuseStep 39460283 = 59190425) B59190425
theorem B2924137 : Blo 1621009 2924137 := bstep (se 2 (by rfl) ⟨1096551, by rfl⟩ : syracuseStep 2924137 = 2193103) B2193103
theorem B1621631 : Blo 1621009 1621631 := bstep (se 1 (by rfl) ⟨1216223, by rfl⟩ : syracuseStep 1621631 = 2432447) B2432447
theorem B18276025 : Blo 1621009 18276025 := bstep (se 2 (by rfl) ⟨6853509, by rfl⟩ : syracuseStep 18276025 = 13707019) B13707019
theorem B1621759 : Blo 1621009 1621759 := bstep (se 1 (by rfl) ⟨1216319, by rfl⟩ : syracuseStep 1621759 = 2432639) B2432639
theorem B2432831 : Blo 1621009 2432831 := bstep (se 1 (by rfl) ⟨1824623, by rfl⟩ : syracuseStep 2432831 = 3649247) B3649247
theorem B52633421 : Blo 1621009 52633421 := bstep (se 3 (by rfl) ⟨9868766, by rfl⟩ : syracuseStep 52633421 = 19737533) B19737533
theorem B5472251 : Blo 1621009 5472251 := bstep (se 1 (by rfl) ⟨4104188, by rfl⟩ : syracuseStep 5472251 = 8208377) B8208377
theorem B2433065 : Blo 1621009 2433065 := bstep (se 2 (by rfl) ⟨912399, by rfl⟩ : syracuseStep 2433065 = 1824799) B1824799
theorem B6160475 : Blo 1621009 6160475 := bstep (se 1 (by rfl) ⟨4620356, by rfl⟩ : syracuseStep 6160475 = 9240713) B9240713
theorem B44376173 : Blo 1621009 44376173 := bstep (se 3 (by rfl) ⟨8320532, by rfl⟩ : syracuseStep 44376173 = 16641065) B16641065
theorem B3080359 : Blo 1621009 3080359 := bstep (se 1 (by rfl) ⟨2310269, by rfl⟩ : syracuseStep 3080359 = 4620539) B4620539
theorem B1622255 : Blo 1621009 1622255 := bstep (se 1 (by rfl) ⟨1216691, by rfl⟩ : syracuseStep 1622255 = 2433383) B2433383
theorem B1622767 : Blo 1621009 1622767 := bstep (se 1 (by rfl) ⟨1217075, by rfl⟩ : syracuseStep 1622767 = 2434151) B2434151
theorem B6931271 : Blo 1621009 6931271 := bstep (se 1 (by rfl) ⟨5198453, by rfl⟩ : syracuseStep 6931271 = 10396907) B10396907
theorem B1622887 : Blo 1621009 1622887 := bstep (se 1 (by rfl) ⟨1217165, by rfl⟩ : syracuseStep 1622887 = 2434331) B2434331
theorem B9233423 : Blo 1621009 9233423 := bstep (se 1 (by rfl) ⟨6925067, by rfl⟩ : syracuseStep 9233423 = 13850135) B13850135
theorem B2434139 : Blo 1621009 2434139 := bstep (se 1 (by rfl) ⟨1825604, by rfl⟩ : syracuseStep 2434139 = 3651209) B3651209
theorem B9233675 : Blo 1621009 9233675 := bstep (se 1 (by rfl) ⟨6925256, by rfl⟩ : syracuseStep 9233675 = 13850513) B13850513
theorem B59180939 : Blo 1621009 59180939 := bstep (se 1 (by rfl) ⟨44385704, by rfl⟩ : syracuseStep 59180939 = 88771409) B88771409
theorem B26306855 : Blo 1621009 26306855 := bstep (se 1 (by rfl) ⟨19730141, by rfl⟩ : syracuseStep 26306855 = 39460283) B39460283
theorem B13158875 : Blo 1621009 13158875 := bstep (se 1 (by rfl) ⟨9869156, by rfl⟩ : syracuseStep 13158875 = 19738313) B19738313
theorem B35088947 : Blo 1621009 35088947 := bstep (se 1 (by rfl) ⟨26316710, by rfl⟩ : syracuseStep 35088947 = 52633421) B52633421
theorem B192219803 : Blo 1621009 192219803 := bstep (se 1 (by rfl) ⟨144164852, by rfl⟩ : syracuseStep 192219803 = 288329705) B288329705
theorem B3648167 : Blo 1621009 3648167 := bstep (se 1 (by rfl) ⟨2736125, by rfl⟩ : syracuseStep 3648167 = 5472251) B5472251
theorem B6155099 : Blo 1621009 6155099 := bstep (se 1 (by rfl) ⟨4616324, by rfl⟩ : syracuseStep 6155099 = 9232649) B9232649
theorem B12323987 : Blo 1621009 12323987 := bstep (se 1 (by rfl) ⟨9242990, by rfl⟩ : syracuseStep 12323987 = 18485981) B18485981
theorem B2632943 : Blo 1621009 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B5844583 : Blo 1621009 5844583 := bstep (se 1 (by rfl) ⟨4383437, by rfl⟩ : syracuseStep 5844583 = 8766875) B8766875
theorem B3649193 : Blo 1621009 3649193 := bstep (se 2 (by rfl) ⟨1368447, by rfl⟩ : syracuseStep 3649193 = 2736895) B2736895
theorem B9359495 : Blo 1621009 9359495 := bstep (se 1 (by rfl) ⟨7019621, by rfl⟩ : syracuseStep 9359495 = 14039243) B14039243
theorem B364966073 : Blo 1621009 364966073 := bstep (se 2 (by rfl) ⟨136862277, by rfl⟩ : syracuseStep 364966073 = 273724555) B273724555
theorem B2052859 : Blo 1621009 2052859 := bstep (se 1 (by rfl) ⟨1539644, by rfl⟩ : syracuseStep 2052859 = 3079289) B3079289
theorem B24368033 : Blo 1621009 24368033 := bstep (se 2 (by rfl) ⟨9138012, by rfl⟩ : syracuseStep 24368033 = 18276025) B18276025
theorem B12489889 : Blo 1621009 12489889 := bstep (se 2 (by rfl) ⟨4683708, by rfl⟩ : syracuseStep 12489889 = 9367417) B9367417
theorem B13514521 : Blo 1621009 13514521 := bstep (se 2 (by rfl) ⟨5067945, by rfl⟩ : syracuseStep 13514521 = 10135891) B10135891
theorem B13859261 : Blo 1621009 13859261 := bstep (se 3 (by rfl) ⟨2598611, by rfl⟩ : syracuseStep 13859261 = 5197223) B5197223
theorem B4619207 : Blo 1621009 4619207 := bstep (se 1 (by rfl) ⟨3464405, by rfl⟩ : syracuseStep 4619207 = 6928811) B6928811
theorem B1825735 : Blo 1621009 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B2432105 : Blo 1621009 2432105 := bstep (se 2 (by rfl) ⟨912039, by rfl⟩ : syracuseStep 2432105 = 1824079) B1824079
theorem B1621119 : Blo 1621009 1621119 := bstep (se 1 (by rfl) ⟨1215839, by rfl⟩ : syracuseStep 1621119 = 2431679) B2431679
theorem B10132607 : Blo 1621009 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B4619423 : Blo 1621009 4619423 := bstep (se 1 (by rfl) ⟨3464567, by rfl⟩ : syracuseStep 4619423 = 6929135) B6929135
theorem B4103419 : Blo 1621009 4103419 := bstep (se 1 (by rfl) ⟨3077564, by rfl⟩ : syracuseStep 4103419 = 6155129) B6155129
theorem B3898849 : Blo 1621009 3898849 := bstep (se 2 (by rfl) ⟨1462068, by rfl⟩ : syracuseStep 3898849 = 2924137) B2924137
theorem B3464687 : Blo 1621009 3464687 := bstep (se 1 (by rfl) ⟨2598515, by rfl⟩ : syracuseStep 3464687 = 5197031) B5197031
theorem B8216153 : Blo 1621009 8216153 := bstep (se 2 (by rfl) ⟨3081057, by rfl⟩ : syracuseStep 8216153 = 6162115) B6162115
theorem B1621887 : Blo 1621009 1621887 := bstep (se 1 (by rfl) ⟨1216415, by rfl⟩ : syracuseStep 1621887 = 2432831) B2432831
theorem B1622043 : Blo 1621009 1622043 := bstep (se 1 (by rfl) ⟨1216532, by rfl⟩ : syracuseStep 1622043 = 2433065) B2433065
theorem B243310715 : Blo 1621009 243310715 := bstep (se 1 (by rfl) ⟨182483036, by rfl⟩ : syracuseStep 243310715 = 364966073) B364966073
theorem B4620847 : Blo 1621009 4620847 := bstep (se 1 (by rfl) ⟨3465635, by rfl⟩ : syracuseStep 4620847 = 6931271) B6931271
theorem B16245355 : Blo 1621009 16245355 := bstep (se 1 (by rfl) ⟨12184016, by rfl⟩ : syracuseStep 16245355 = 24368033) B24368033
theorem B1622759 : Blo 1621009 1622759 := bstep (se 1 (by rfl) ⟨1217069, by rfl⟩ : syracuseStep 1622759 = 2434139) B2434139
theorem B2737145 : Blo 1621009 2737145 := bstep (se 2 (by rfl) ⟨1026429, by rfl⟩ : syracuseStep 2737145 = 2052859) B2052859
theorem B39453959 : Blo 1621009 39453959 := bstep (se 1 (by rfl) ⟨29590469, by rfl⟩ : syracuseStep 39453959 = 59180939) B59180939
theorem B2434313 : Blo 1621009 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B7792777 : Blo 1621009 7792777 := bstep (se 2 (by rfl) ⟨2922291, by rfl⟩ : syracuseStep 7792777 = 5844583) B5844583
theorem B1755295 : Blo 1621009 1755295 := bstep (se 1 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 1755295 = 2632943) B2632943
theorem B4106983 : Blo 1621009 4106983 := bstep (se 1 (by rfl) ⟨3080237, by rfl⟩ : syracuseStep 4106983 = 6160475) B6160475
theorem B29584115 : Blo 1621009 29584115 := bstep (se 1 (by rfl) ⟨22188086, by rfl⟩ : syracuseStep 29584115 = 44376173) B44376173
theorem B4107145 : Blo 1621009 4107145 := bstep (se 2 (by rfl) ⟨1540179, by rfl⟩ : syracuseStep 4107145 = 3080359) B3080359
theorem B6155615 : Blo 1621009 6155615 := bstep (se 1 (by rfl) ⟨4616711, by rfl⟩ : syracuseStep 6155615 = 9233423) B9233423
theorem B6155783 : Blo 1621009 6155783 := bstep (se 1 (by rfl) ⟨4616837, by rfl⟩ : syracuseStep 6155783 = 9233675) B9233675
theorem B35090333 : Blo 1621009 35090333 := bstep (se 3 (by rfl) ⟨6579437, by rfl⟩ : syracuseStep 35090333 = 13158875) B13158875
theorem B23392631 : Blo 1621009 23392631 := bstep (se 1 (by rfl) ⟨17544473, by rfl⟩ : syracuseStep 23392631 = 35088947) B35088947
theorem B5198465 : Blo 1621009 5198465 := bstep (se 2 (by rfl) ⟨1949424, by rfl⟩ : syracuseStep 5198465 = 3898849) B3898849
theorem B6755071 : Blo 1621009 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B18019361 : Blo 1621009 18019361 := bstep (se 2 (by rfl) ⟨6757260, by rfl⟩ : syracuseStep 18019361 = 13514521) B13514521
theorem B5477435 : Blo 1621009 5477435 := bstep (se 1 (by rfl) ⟨4108076, by rfl⟩ : syracuseStep 5477435 = 8216153) B8216153
theorem B6239663 : Blo 1621009 6239663 := bstep (se 1 (by rfl) ⟨4679747, by rfl⟩ : syracuseStep 6239663 = 9359495) B9359495
theorem B17537903 : Blo 1621009 17537903 := bstep (se 1 (by rfl) ⟨13153427, by rfl⟩ : syracuseStep 17537903 = 26306855) B26306855
theorem B16653185 : Blo 1621009 16653185 := bstep (se 2 (by rfl) ⟨6244944, by rfl⟩ : syracuseStep 16653185 = 12489889) B12489889
theorem B9239507 : Blo 1621009 9239507 := bstep (se 1 (by rfl) ⟨6929630, by rfl⟩ : syracuseStep 9239507 = 13859261) B13859261
theorem B5471225 : Blo 1621009 5471225 := bstep (se 2 (by rfl) ⟨2051709, by rfl⟩ : syracuseStep 5471225 = 4103419) B4103419
theorem B128146535 : Blo 1621009 128146535 := bstep (se 1 (by rfl) ⟨96109901, by rfl⟩ : syracuseStep 128146535 = 192219803) B192219803
theorem B2432111 : Blo 1621009 2432111 := bstep (se 1 (by rfl) ⟨1824083, by rfl⟩ : syracuseStep 2432111 = 3648167) B3648167
theorem B4103399 : Blo 1621009 4103399 := bstep (se 1 (by rfl) ⟨3077549, by rfl⟩ : syracuseStep 4103399 = 6155099) B6155099
theorem B3079471 : Blo 1621009 3079471 := bstep (se 1 (by rfl) ⟨2309603, by rfl⟩ : syracuseStep 3079471 = 4619207) B4619207
theorem B1621403 : Blo 1621009 1621403 := bstep (se 1 (by rfl) ⟨1216052, by rfl⟩ : syracuseStep 1621403 = 2432105) B2432105
theorem B8215991 : Blo 1621009 8215991 := bstep (se 1 (by rfl) ⟨6161993, by rfl⟩ : syracuseStep 8215991 = 12323987) B12323987
theorem B3079615 : Blo 1621009 3079615 := bstep (se 1 (by rfl) ⟨2309711, by rfl⟩ : syracuseStep 3079615 = 4619423) B4619423
theorem B2309791 : Blo 1621009 2309791 := bstep (se 1 (by rfl) ⟨1732343, by rfl⟩ : syracuseStep 2309791 = 3464687) B3464687
theorem B2432795 : Blo 1621009 2432795 := bstep (se 1 (by rfl) ⟨1824596, by rfl⟩ : syracuseStep 2432795 = 3649193) B3649193
theorem B37446293 : Blo 1621009 37446293 := bstep (se 6 (by rfl) ⟨877647, by rfl⟩ : syracuseStep 37446293 = 1755295) B1755295
theorem B6161129 : Blo 1621009 6161129 := bstep (se 2 (by rfl) ⟨2310423, by rfl⟩ : syracuseStep 6161129 = 4620847) B4620847
theorem B21660473 : Blo 1621009 21660473 := bstep (se 2 (by rfl) ⟨8122677, by rfl⟩ : syracuseStep 21660473 = 16245355) B16245355
theorem B1622875 : Blo 1621009 1622875 := bstep (se 1 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 1622875 = 2434313) B2434313
theorem B13862573 : Blo 1621009 13862573 := bstep (se 3 (by rfl) ⟨2599232, by rfl⟩ : syracuseStep 13862573 = 5198465) B5198465
theorem B4105961 : Blo 1621009 4105961 := bstep (se 2 (by rfl) ⟨1539735, by rfl⟩ : syracuseStep 4105961 = 3079471) B3079471
theorem B11691935 : Blo 1621009 11691935 := bstep (se 1 (by rfl) ⟨8768951, by rfl⟩ : syracuseStep 11691935 = 17537903) B17537903
theorem B4106153 : Blo 1621009 4106153 := bstep (se 2 (by rfl) ⟨1539807, by rfl⟩ : syracuseStep 4106153 = 3079615) B3079615
theorem B11102123 : Blo 1621009 11102123 := bstep (se 1 (by rfl) ⟨8326592, by rfl⟩ : syracuseStep 11102123 = 16653185) B16653185
theorem B3647483 : Blo 1621009 3647483 := bstep (se 1 (by rfl) ⟨2735612, by rfl⟩ : syracuseStep 3647483 = 5471225) B5471225
theorem B10390369 : Blo 1621009 10390369 := bstep (se 2 (by rfl) ⟨3896388, by rfl⟩ : syracuseStep 10390369 = 7792777) B7792777
theorem B12012907 : Blo 1621009 12012907 := bstep (se 1 (by rfl) ⟨9009680, by rfl⟩ : syracuseStep 12012907 = 18019361) B18019361
theorem B5475977 : Blo 1621009 5475977 := bstep (se 2 (by rfl) ⟨2053491, by rfl⟩ : syracuseStep 5475977 = 4106983) B4106983
theorem B9006761 : Blo 1621009 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B5476193 : Blo 1621009 5476193 := bstep (se 2 (by rfl) ⟨2053572, by rfl⟩ : syracuseStep 5476193 = 4107145) B4107145
theorem B19722743 : Blo 1621009 19722743 := bstep (se 1 (by rfl) ⟨14792057, by rfl⟩ : syracuseStep 19722743 = 29584115) B29584115
theorem B85431023 : Blo 1621009 85431023 := bstep (se 1 (by rfl) ⟨64073267, by rfl⟩ : syracuseStep 85431023 = 128146535) B128146535
theorem B5477327 : Blo 1621009 5477327 := bstep (se 1 (by rfl) ⟨4107995, by rfl⟩ : syracuseStep 5477327 = 8215991) B8215991
theorem B23393555 : Blo 1621009 23393555 := bstep (se 1 (by rfl) ⟨17545166, by rfl⟩ : syracuseStep 23393555 = 35090333) B35090333
theorem B162207143 : Blo 1621009 162207143 := bstep (se 1 (by rfl) ⟨121655357, by rfl⟩ : syracuseStep 162207143 = 243310715) B243310715
theorem B15595087 : Blo 1621009 15595087 := bstep (se 1 (by rfl) ⟨11696315, by rfl⟩ : syracuseStep 15595087 = 23392631) B23392631
theorem B1824763 : Blo 1621009 1824763 := bstep (se 1 (by rfl) ⟨1368572, by rfl⟩ : syracuseStep 1824763 = 2737145) B2737145
theorem B3651623 : Blo 1621009 3651623 := bstep (se 1 (by rfl) ⟨2738717, by rfl⟩ : syracuseStep 3651623 = 5477435) B5477435
theorem B26302639 : Blo 1621009 26302639 := bstep (se 1 (by rfl) ⟨19726979, by rfl⟩ : syracuseStep 26302639 = 39453959) B39453959
theorem B4159775 : Blo 1621009 4159775 := bstep (se 1 (by rfl) ⟨3119831, by rfl⟩ : syracuseStep 4159775 = 6239663) B6239663
theorem B6159671 : Blo 1621009 6159671 := bstep (se 1 (by rfl) ⟨4619753, by rfl⟩ : syracuseStep 6159671 = 9239507) B9239507
theorem B1621407 : Blo 1621009 1621407 := bstep (se 1 (by rfl) ⟨1216055, by rfl⟩ : syracuseStep 1621407 = 2432111) B2432111
theorem B2735599 : Blo 1621009 2735599 := bstep (se 1 (by rfl) ⟨2051699, by rfl⟩ : syracuseStep 2735599 = 4103399) B4103399
theorem B3079721 : Blo 1621009 3079721 := bstep (se 2 (by rfl) ⟨1154895, by rfl⟩ : syracuseStep 3079721 = 2309791) B2309791
theorem B4103743 : Blo 1621009 4103743 := bstep (se 1 (by rfl) ⟨3077807, by rfl⟩ : syracuseStep 4103743 = 6155615) B6155615
theorem B4103855 : Blo 1621009 4103855 := bstep (se 1 (by rfl) ⟨3077891, by rfl⟩ : syracuseStep 4103855 = 6155783) B6155783
theorem B1621863 : Blo 1621009 1621863 := bstep (se 1 (by rfl) ⟨1216397, by rfl⟩ : syracuseStep 1621863 = 2432795) B2432795
theorem B35070185 : Blo 1621009 35070185 := bstep (se 2 (by rfl) ⟨13151319, by rfl⟩ : syracuseStep 35070185 = 26302639) B26302639
theorem B13148495 : Blo 1621009 13148495 := bstep (se 1 (by rfl) ⟨9861371, by rfl⟩ : syracuseStep 13148495 = 19722743) B19722743
theorem B9241715 : Blo 1621009 9241715 := bstep (se 1 (by rfl) ⟨6931286, by rfl⟩ : syracuseStep 9241715 = 13862573) B13862573
theorem B13853825 : Blo 1621009 13853825 := bstep (se 2 (by rfl) ⟨5195184, by rfl⟩ : syracuseStep 13853825 = 10390369) B10390369
theorem B2737307 : Blo 1621009 2737307 := bstep (se 1 (by rfl) ⟨2052980, by rfl⟩ : syracuseStep 2737307 = 4105961) B4105961
theorem B2737435 : Blo 1621009 2737435 := bstep (se 1 (by rfl) ⟨2053076, by rfl⟩ : syracuseStep 2737435 = 4106153) B4106153
theorem B2434415 : Blo 1621009 2434415 := bstep (se 1 (by rfl) ⟨1825811, by rfl⟩ : syracuseStep 2434415 = 3651623) B3651623
theorem B16017209 : Blo 1621009 16017209 := bstep (se 2 (by rfl) ⟨6006453, by rfl⟩ : syracuseStep 16017209 = 12012907) B12012907
theorem B3647465 : Blo 1621009 3647465 := bstep (se 2 (by rfl) ⟨1367799, by rfl⟩ : syracuseStep 3647465 = 2735599) B2735599
theorem B20793449 : Blo 1621009 20793449 := bstep (se 2 (by rfl) ⟨7797543, by rfl⟩ : syracuseStep 20793449 = 15595087) B15595087
theorem B4106447 : Blo 1621009 4106447 := bstep (se 1 (by rfl) ⟨3079835, by rfl⟩ : syracuseStep 4106447 = 6159671) B6159671
theorem B2433017 : Blo 1621009 2433017 := bstep (se 2 (by rfl) ⟨912381, by rfl⟩ : syracuseStep 2433017 = 1824763) B1824763
theorem B24964195 : Blo 1621009 24964195 := bstep (se 1 (by rfl) ⟨18723146, by rfl⟩ : syracuseStep 24964195 = 37446293) B37446293
theorem B4107419 : Blo 1621009 4107419 := bstep (se 1 (by rfl) ⟨3080564, by rfl⟩ : syracuseStep 4107419 = 6161129) B6161129
theorem B56954015 : Blo 1621009 56954015 := bstep (se 1 (by rfl) ⟨42715511, by rfl⟩ : syracuseStep 56954015 = 85431023) B85431023
theorem B108138095 : Blo 1621009 108138095 := bstep (se 1 (by rfl) ⟨81103571, by rfl⟩ : syracuseStep 108138095 = 162207143) B162207143
theorem B7794623 : Blo 1621009 7794623 := bstep (se 1 (by rfl) ⟨5845967, by rfl⟩ : syracuseStep 7794623 = 11691935) B11691935
theorem B8212589 : Blo 1621009 8212589 := bstep (se 3 (by rfl) ⟨1539860, by rfl⟩ : syracuseStep 8212589 = 3079721) B3079721
theorem B2773183 : Blo 1621009 2773183 := bstep (se 1 (by rfl) ⟨2079887, by rfl⟩ : syracuseStep 2773183 = 4159775) B4159775
theorem B3650651 : Blo 1621009 3650651 := bstep (se 1 (by rfl) ⟨2737988, by rfl⟩ : syracuseStep 3650651 = 5475977) B5475977
theorem B3650795 : Blo 1621009 3650795 := bstep (se 1 (by rfl) ⟨2738096, by rfl⟩ : syracuseStep 3650795 = 5476193) B5476193
theorem B14440315 : Blo 1621009 14440315 := bstep (se 1 (by rfl) ⟨10830236, by rfl⟩ : syracuseStep 14440315 = 21660473) B21660473
theorem B3651551 : Blo 1621009 3651551 := bstep (se 1 (by rfl) ⟨2738663, by rfl⟩ : syracuseStep 3651551 = 5477327) B5477327
theorem B15595703 : Blo 1621009 15595703 := bstep (se 1 (by rfl) ⟨11696777, by rfl⟩ : syracuseStep 15595703 = 23393555) B23393555
theorem B2431655 : Blo 1621009 2431655 := bstep (se 1 (by rfl) ⟨1823741, by rfl⟩ : syracuseStep 2431655 = 3647483) B3647483
theorem B5471657 : Blo 1621009 5471657 := bstep (se 2 (by rfl) ⟨2051871, by rfl⟩ : syracuseStep 5471657 = 4103743) B4103743
theorem B6004507 : Blo 1621009 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B2735903 : Blo 1621009 2735903 := bstep (se 1 (by rfl) ⟨2051927, by rfl⟩ : syracuseStep 2735903 = 4103855) B4103855
theorem B29605661 : Blo 1621009 29605661 := bstep (se 3 (by rfl) ⟨5551061, by rfl⟩ : syracuseStep 29605661 = 11102123) B11102123
theorem B23380123 : Blo 1621009 23380123 := bstep (se 1 (by rfl) ⟨17535092, by rfl⟩ : syracuseStep 23380123 = 35070185) B35070185
theorem B8765663 : Blo 1621009 8765663 := bstep (se 1 (by rfl) ⟨6574247, by rfl⟩ : syracuseStep 8765663 = 13148495) B13148495
theorem B2433767 : Blo 1621009 2433767 := bstep (se 1 (by rfl) ⟨1825325, by rfl⟩ : syracuseStep 2433767 = 3650651) B3650651
theorem B6161143 : Blo 1621009 6161143 := bstep (se 1 (by rfl) ⟨4620857, by rfl⟩ : syracuseStep 6161143 = 9241715) B9241715
theorem B2433863 : Blo 1621009 2433863 := bstep (se 1 (by rfl) ⟨1825397, by rfl⟩ : syracuseStep 2433863 = 3650795) B3650795
theorem B1622943 : Blo 1621009 1622943 := bstep (se 1 (by rfl) ⟨1217207, by rfl⟩ : syracuseStep 1622943 = 2434415) B2434415
theorem B2434367 : Blo 1621009 2434367 := bstep (se 1 (by rfl) ⟨1825775, by rfl⟩ : syracuseStep 2434367 = 3651551) B3651551
theorem B13862299 : Blo 1621009 13862299 := bstep (se 1 (by rfl) ⟨10396724, by rfl⟩ : syracuseStep 13862299 = 20793449) B20793449
theorem B10397135 : Blo 1621009 10397135 := bstep (se 1 (by rfl) ⟨7797851, by rfl⟩ : syracuseStep 10397135 = 15595703) B15595703
theorem B33285593 : Blo 1621009 33285593 := bstep (se 2 (by rfl) ⟨12482097, by rfl⟩ : syracuseStep 33285593 = 24964195) B24964195
theorem B2737631 : Blo 1621009 2737631 := bstep (se 1 (by rfl) ⟨2053223, by rfl⟩ : syracuseStep 2737631 = 4106447) B4106447
theorem B1622011 : Blo 1621009 1622011 := bstep (se 1 (by rfl) ⟨1216508, by rfl⟩ : syracuseStep 1622011 = 2433017) B2433017
theorem B2738279 : Blo 1621009 2738279 := bstep (se 1 (by rfl) ⟨2053709, by rfl⟩ : syracuseStep 2738279 = 4107419) B4107419
theorem B3647771 : Blo 1621009 3647771 := bstep (se 1 (by rfl) ⟨2735828, by rfl⟩ : syracuseStep 3647771 = 5471657) B5471657
theorem B8006009 : Blo 1621009 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B72092063 : Blo 1621009 72092063 := bstep (se 1 (by rfl) ⟨54069047, by rfl⟩ : syracuseStep 72092063 = 108138095) B108138095
theorem B19253753 : Blo 1621009 19253753 := bstep (se 2 (by rfl) ⟨7220157, by rfl⟩ : syracuseStep 19253753 = 14440315) B14440315
theorem B19737107 : Blo 1621009 19737107 := bstep (se 1 (by rfl) ⟨14802830, by rfl⟩ : syracuseStep 19737107 = 29605661) B29605661
theorem B5196415 : Blo 1621009 5196415 := bstep (se 1 (by rfl) ⟨3897311, by rfl⟩ : syracuseStep 5196415 = 7794623) B7794623
theorem B5475059 : Blo 1621009 5475059 := bstep (se 1 (by rfl) ⟨4106294, by rfl⟩ : syracuseStep 5475059 = 8212589) B8212589
theorem B3697577 : Blo 1621009 3697577 := bstep (se 2 (by rfl) ⟨1386591, by rfl⟩ : syracuseStep 3697577 = 2773183) B2773183
theorem B9235883 : Blo 1621009 9235883 := bstep (se 1 (by rfl) ⟨6926912, by rfl⟩ : syracuseStep 9235883 = 13853825) B13853825
theorem B10678139 : Blo 1621009 10678139 := bstep (se 1 (by rfl) ⟨8008604, by rfl⟩ : syracuseStep 10678139 = 16017209) B16017209
theorem B3649913 : Blo 1621009 3649913 := bstep (se 2 (by rfl) ⟨1368717, by rfl⟩ : syracuseStep 3649913 = 2737435) B2737435
theorem B1823935 : Blo 1621009 1823935 := bstep (se 1 (by rfl) ⟨1367951, by rfl⟩ : syracuseStep 1823935 = 2735903) B2735903
theorem B1824871 : Blo 1621009 1824871 := bstep (se 1 (by rfl) ⟨1368653, by rfl⟩ : syracuseStep 1824871 = 2737307) B2737307
theorem B2431643 : Blo 1621009 2431643 := bstep (se 1 (by rfl) ⟨1823732, by rfl⟩ : syracuseStep 2431643 = 3647465) B3647465
theorem B1621103 : Blo 1621009 1621103 := bstep (se 1 (by rfl) ⟨1215827, by rfl⟩ : syracuseStep 1621103 = 2431655) B2431655
theorem B37969343 : Blo 1621009 37969343 := bstep (se 1 (by rfl) ⟨28477007, by rfl⟩ : syracuseStep 37969343 = 56954015) B56954015
theorem B2433161 : Blo 1621009 2433161 := bstep (se 2 (by rfl) ⟨912435, by rfl⟩ : syracuseStep 2433161 = 1824871) B1824871
theorem B2433275 : Blo 1621009 2433275 := bstep (se 1 (by rfl) ⟨1824956, by rfl⟩ : syracuseStep 2433275 = 3649913) B3649913
theorem B1622511 : Blo 1621009 1622511 := bstep (se 1 (by rfl) ⟨1216883, by rfl⟩ : syracuseStep 1622511 = 2433767) B2433767
theorem B1622575 : Blo 1621009 1622575 := bstep (se 1 (by rfl) ⟨1216931, by rfl⟩ : syracuseStep 1622575 = 2433863) B2433863
theorem B1622911 : Blo 1621009 1622911 := bstep (se 1 (by rfl) ⟨1217183, by rfl⟩ : syracuseStep 1622911 = 2434367) B2434367
theorem B6931423 : Blo 1621009 6931423 := bstep (se 1 (by rfl) ⟨5198567, by rfl⟩ : syracuseStep 6931423 = 10397135) B10397135
theorem B13158071 : Blo 1621009 13158071 := bstep (se 1 (by rfl) ⟨9868553, by rfl⟩ : syracuseStep 13158071 = 19737107) B19737107
theorem B18483065 : Blo 1621009 18483065 := bstep (se 2 (by rfl) ⟨6931149, by rfl⟩ : syracuseStep 18483065 = 13862299) B13862299
theorem B31173497 : Blo 1621009 31173497 := bstep (se 2 (by rfl) ⟨11690061, by rfl⟩ : syracuseStep 31173497 = 23380123) B23380123
theorem B23375101 : Blo 1621009 23375101 := bstep (se 3 (by rfl) ⟨4382831, by rfl⟩ : syracuseStep 23375101 = 8765663) B8765663
theorem B192245501 : Blo 1621009 192245501 := bstep (se 3 (by rfl) ⟨36046031, by rfl⟩ : syracuseStep 192245501 = 72092063) B72092063
theorem B85397429 : Blo 1621009 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B3650039 : Blo 1621009 3650039 := bstep (se 1 (by rfl) ⟨2737529, by rfl⟩ : syracuseStep 3650039 = 5475059) B5475059
theorem B6157255 : Blo 1621009 6157255 := bstep (se 1 (by rfl) ⟨4617941, by rfl⟩ : syracuseStep 6157255 = 9235883) B9235883
theorem B6928553 : Blo 1621009 6928553 := bstep (se 2 (by rfl) ⟨2598207, by rfl⟩ : syracuseStep 6928553 = 5196415) B5196415
theorem B22190395 : Blo 1621009 22190395 := bstep (se 1 (by rfl) ⟨16642796, by rfl⟩ : syracuseStep 22190395 = 33285593) B33285593
theorem B1825087 : Blo 1621009 1825087 := bstep (se 1 (by rfl) ⟨1368815, by rfl⟩ : syracuseStep 1825087 = 2737631) B2737631
theorem B8214857 : Blo 1621009 8214857 := bstep (se 2 (by rfl) ⟨3080571, by rfl⟩ : syracuseStep 8214857 = 6161143) B6161143
theorem B1825519 : Blo 1621009 1825519 := bstep (se 1 (by rfl) ⟨1369139, by rfl⟩ : syracuseStep 1825519 = 2738279) B2738279
theorem B2431847 : Blo 1621009 2431847 := bstep (se 1 (by rfl) ⟨1823885, by rfl⟩ : syracuseStep 2431847 = 3647771) B3647771
theorem B2431913 : Blo 1621009 2431913 := bstep (se 2 (by rfl) ⟨911967, by rfl⟩ : syracuseStep 2431913 = 1823935) B1823935
theorem B12835835 : Blo 1621009 12835835 := bstep (se 1 (by rfl) ⟨9626876, by rfl⟩ : syracuseStep 12835835 = 19253753) B19253753
theorem B1621095 : Blo 1621009 1621095 := bstep (se 1 (by rfl) ⟨1215821, by rfl⟩ : syracuseStep 1621095 = 2431643) B2431643
theorem B2465051 : Blo 1621009 2465051 := bstep (se 1 (by rfl) ⟨1848788, by rfl⟩ : syracuseStep 2465051 = 3697577) B3697577
theorem B25312895 : Blo 1621009 25312895 := bstep (se 1 (by rfl) ⟨18984671, by rfl⟩ : syracuseStep 25312895 = 37969343) B37969343
theorem B7118759 : Blo 1621009 7118759 := bstep (se 1 (by rfl) ⟨5339069, by rfl⟩ : syracuseStep 7118759 = 10678139) B10678139
theorem B1622107 : Blo 1621009 1622107 := bstep (se 1 (by rfl) ⟨1216580, by rfl⟩ : syracuseStep 1622107 = 2433161) B2433161
theorem B1622183 : Blo 1621009 1622183 := bstep (se 1 (by rfl) ⟨1216637, by rfl⟩ : syracuseStep 1622183 = 2433275) B2433275
theorem B2433359 : Blo 1621009 2433359 := bstep (se 1 (by rfl) ⟨1825019, by rfl⟩ : syracuseStep 2433359 = 3650039) B3650039
theorem B2433449 : Blo 1621009 2433449 := bstep (se 2 (by rfl) ⟨912543, by rfl⟩ : syracuseStep 2433449 = 1825087) B1825087
theorem B2434025 : Blo 1621009 2434025 := bstep (se 2 (by rfl) ⟨912759, by rfl⟩ : syracuseStep 2434025 = 1825519) B1825519
theorem B12322043 : Blo 1621009 12322043 := bstep (se 1 (by rfl) ⟨9241532, by rfl⟩ : syracuseStep 12322043 = 18483065) B18483065
theorem B8209673 : Blo 1621009 8209673 := bstep (se 2 (by rfl) ⟨3078627, by rfl⟩ : syracuseStep 8209673 = 6157255) B6157255
theorem B9241897 : Blo 1621009 9241897 := bstep (se 2 (by rfl) ⟨3465711, by rfl⟩ : syracuseStep 9241897 = 6931423) B6931423
theorem B18983357 : Blo 1621009 18983357 := bstep (se 3 (by rfl) ⟨3559379, by rfl⟩ : syracuseStep 18983357 = 7118759) B7118759
theorem B6573469 : Blo 1621009 6573469 := bstep (se 3 (by rfl) ⟨1232525, by rfl⟩ : syracuseStep 6573469 = 2465051) B2465051
theorem B5476571 : Blo 1621009 5476571 := bstep (se 1 (by rfl) ⟨4107428, by rfl⟩ : syracuseStep 5476571 = 8214857) B8214857
theorem B31166801 : Blo 1621009 31166801 := bstep (se 2 (by rfl) ⟨11687550, by rfl⟩ : syracuseStep 31166801 = 23375101) B23375101
theorem B8557223 : Blo 1621009 8557223 := bstep (se 1 (by rfl) ⟨6417917, by rfl⟩ : syracuseStep 8557223 = 12835835) B12835835
theorem B56931619 : Blo 1621009 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B29587193 : Blo 1621009 29587193 := bstep (se 2 (by rfl) ⟨11095197, by rfl⟩ : syracuseStep 29587193 = 22190395) B22190395
theorem B8772047 : Blo 1621009 8772047 := bstep (se 1 (by rfl) ⟨6579035, by rfl⟩ : syracuseStep 8772047 = 13158071) B13158071
theorem B4619035 : Blo 1621009 4619035 := bstep (se 1 (by rfl) ⟨3464276, by rfl⟩ : syracuseStep 4619035 = 6928553) B6928553
theorem B1621231 : Blo 1621009 1621231 := bstep (se 1 (by rfl) ⟨1215923, by rfl⟩ : syracuseStep 1621231 = 2431847) B2431847
theorem B20782331 : Blo 1621009 20782331 := bstep (se 1 (by rfl) ⟨15586748, by rfl⟩ : syracuseStep 20782331 = 31173497) B31173497
theorem B1621275 : Blo 1621009 1621275 := bstep (se 1 (by rfl) ⟨1215956, by rfl⟩ : syracuseStep 1621275 = 2431913) B2431913
theorem B16875263 : Blo 1621009 16875263 := bstep (se 1 (by rfl) ⟨12656447, by rfl⟩ : syracuseStep 16875263 = 25312895) B25312895
theorem B128163667 : Blo 1621009 128163667 := bstep (se 1 (by rfl) ⟨96122750, by rfl⟩ : syracuseStep 128163667 = 192245501) B192245501
theorem B1622239 : Blo 1621009 1622239 := bstep (se 1 (by rfl) ⟨1216679, by rfl⟩ : syracuseStep 1622239 = 2433359) B2433359
theorem B1622299 : Blo 1621009 1622299 := bstep (se 1 (by rfl) ⟨1216724, by rfl⟩ : syracuseStep 1622299 = 2433449) B2433449
theorem B1622683 : Blo 1621009 1622683 := bstep (se 1 (by rfl) ⟨1217012, by rfl⟩ : syracuseStep 1622683 = 2434025) B2434025
theorem B5473115 : Blo 1621009 5473115 := bstep (se 1 (by rfl) ⟨4104836, by rfl⟩ : syracuseStep 5473115 = 8209673) B8209673
theorem B75908825 : Blo 1621009 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B12322529 : Blo 1621009 12322529 := bstep (se 2 (by rfl) ⟨4620948, by rfl⟩ : syracuseStep 12322529 = 9241897) B9241897
theorem B45000701 : Blo 1621009 45000701 := bstep (se 3 (by rfl) ⟨8437631, by rfl⟩ : syracuseStep 45000701 = 16875263) B16875263
theorem B13854887 : Blo 1621009 13854887 := bstep (se 1 (by rfl) ⟨10391165, by rfl⟩ : syracuseStep 13854887 = 20782331) B20782331
theorem B20777867 : Blo 1621009 20777867 := bstep (se 1 (by rfl) ⟨15583400, by rfl⟩ : syracuseStep 20777867 = 31166801) B31166801
theorem B22819261 : Blo 1621009 22819261 := bstep (se 3 (by rfl) ⟨4278611, by rfl⟩ : syracuseStep 22819261 = 8557223) B8557223
theorem B3651047 : Blo 1621009 3651047 := bstep (se 1 (by rfl) ⟨2738285, by rfl⟩ : syracuseStep 3651047 = 5476571) B5476571
theorem B8214695 : Blo 1621009 8214695 := bstep (se 1 (by rfl) ⟨6161021, by rfl⟩ : syracuseStep 8214695 = 12322043) B12322043
theorem B6158713 : Blo 1621009 6158713 := bstep (se 2 (by rfl) ⟨2309517, by rfl⟩ : syracuseStep 6158713 = 4619035) B4619035
theorem B19724795 : Blo 1621009 19724795 := bstep (se 1 (by rfl) ⟨14793596, by rfl⟩ : syracuseStep 19724795 = 29587193) B29587193
theorem B12655571 : Blo 1621009 12655571 := bstep (se 1 (by rfl) ⟨9491678, by rfl⟩ : syracuseStep 12655571 = 18983357) B18983357
theorem B5848031 : Blo 1621009 5848031 := bstep (se 1 (by rfl) ⟨4386023, by rfl⟩ : syracuseStep 5848031 = 8772047) B8772047
theorem B8764625 : Blo 1621009 8764625 := bstep (se 2 (by rfl) ⟨3286734, by rfl⟩ : syracuseStep 8764625 = 6573469) B6573469
theorem B170884889 : Blo 1621009 170884889 := bstep (se 2 (by rfl) ⟨64081833, by rfl⟩ : syracuseStep 170884889 = 128163667) B128163667
theorem B23372333 : Blo 1621009 23372333 := bstep (se 3 (by rfl) ⟨4382312, by rfl⟩ : syracuseStep 23372333 = 8764625) B8764625
theorem B30425681 : Blo 1621009 30425681 := bstep (se 2 (by rfl) ⟨11409630, by rfl⟩ : syracuseStep 30425681 = 22819261) B22819261
theorem B2434031 : Blo 1621009 2434031 := bstep (se 1 (by rfl) ⟨1825523, by rfl⟩ : syracuseStep 2434031 = 3651047) B3651047
theorem B30000467 : Blo 1621009 30000467 := bstep (se 1 (by rfl) ⟨22500350, by rfl⟩ : syracuseStep 30000467 = 45000701) B45000701
theorem B13149863 : Blo 1621009 13149863 := bstep (se 1 (by rfl) ⟨9862397, by rfl⟩ : syracuseStep 13149863 = 19724795) B19724795
theorem B8211617 : Blo 1621009 8211617 := bstep (se 2 (by rfl) ⟨3079356, by rfl⟩ : syracuseStep 8211617 = 6158713) B6158713
theorem B3648743 : Blo 1621009 3648743 := bstep (se 1 (by rfl) ⟨2736557, by rfl⟩ : syracuseStep 3648743 = 5473115) B5473115
theorem B50605883 : Blo 1621009 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B9236591 : Blo 1621009 9236591 := bstep (se 1 (by rfl) ⟨6927443, by rfl⟩ : syracuseStep 9236591 = 13854887) B13854887
theorem B5476463 : Blo 1621009 5476463 := bstep (se 1 (by rfl) ⟨4107347, by rfl⟩ : syracuseStep 5476463 = 8214695) B8214695
theorem B134992757 : Blo 1621009 134992757 := bstep (se 5 (by rfl) ⟨6327785, by rfl⟩ : syracuseStep 134992757 = 12655571) B12655571
theorem B113923259 : Blo 1621009 113923259 := bstep (se 1 (by rfl) ⟨85442444, by rfl⟩ : syracuseStep 113923259 = 170884889) B170884889
theorem B8215019 : Blo 1621009 8215019 := bstep (se 1 (by rfl) ⟨6161264, by rfl⟩ : syracuseStep 8215019 = 12322529) B12322529
theorem B13851911 : Blo 1621009 13851911 := bstep (se 1 (by rfl) ⟨10388933, by rfl⟩ : syracuseStep 13851911 = 20777867) B20777867
theorem B3898687 : Blo 1621009 3898687 := bstep (se 1 (by rfl) ⟨2924015, by rfl⟩ : syracuseStep 3898687 = 5848031) B5848031
theorem B15581555 : Blo 1621009 15581555 := bstep (se 1 (by rfl) ⟨11686166, by rfl⟩ : syracuseStep 15581555 = 23372333) B23372333
theorem B20283787 : Blo 1621009 20283787 := bstep (se 1 (by rfl) ⟨15212840, by rfl⟩ : syracuseStep 20283787 = 30425681) B30425681
theorem B1622687 : Blo 1621009 1622687 := bstep (se 1 (by rfl) ⟨1217015, by rfl⟩ : syracuseStep 1622687 = 2434031) B2434031
theorem B75948839 : Blo 1621009 75948839 := bstep (se 1 (by rfl) ⟨56961629, by rfl⟩ : syracuseStep 75948839 = 113923259) B113923259
theorem B8766575 : Blo 1621009 8766575 := bstep (se 1 (by rfl) ⟨6574931, by rfl⟩ : syracuseStep 8766575 = 13149863) B13149863
theorem B5474411 : Blo 1621009 5474411 := bstep (se 1 (by rfl) ⟨4105808, by rfl⟩ : syracuseStep 5474411 = 8211617) B8211617
theorem B9234607 : Blo 1621009 9234607 := bstep (se 1 (by rfl) ⟨6925955, by rfl⟩ : syracuseStep 9234607 = 13851911) B13851911
theorem B33737255 : Blo 1621009 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B5476679 : Blo 1621009 5476679 := bstep (se 1 (by rfl) ⟨4107509, by rfl⟩ : syracuseStep 5476679 = 8215019) B8215019
theorem B5198249 : Blo 1621009 5198249 := bstep (se 2 (by rfl) ⟨1949343, by rfl⟩ : syracuseStep 5198249 = 3898687) B3898687
theorem B6157727 : Blo 1621009 6157727 := bstep (se 1 (by rfl) ⟨4618295, by rfl⟩ : syracuseStep 6157727 = 9236591) B9236591
theorem B3650975 : Blo 1621009 3650975 := bstep (se 1 (by rfl) ⟨2738231, by rfl⟩ : syracuseStep 3650975 = 5476463) B5476463
theorem B89995171 : Blo 1621009 89995171 := bstep (se 1 (by rfl) ⟨67496378, by rfl⟩ : syracuseStep 89995171 = 134992757) B134992757
theorem B80001245 : Blo 1621009 80001245 := bstep (se 3 (by rfl) ⟨15000233, by rfl⟩ : syracuseStep 80001245 = 30000467) B30000467
theorem B2432495 : Blo 1621009 2432495 := bstep (se 1 (by rfl) ⟨1824371, by rfl⟩ : syracuseStep 2432495 = 3648743) B3648743
theorem B12312809 : Blo 1621009 12312809 := bstep (se 2 (by rfl) ⟨4617303, by rfl⟩ : syracuseStep 12312809 = 9234607) B9234607
theorem B10387703 : Blo 1621009 10387703 := bstep (se 1 (by rfl) ⟨7790777, by rfl⟩ : syracuseStep 10387703 = 15581555) B15581555
theorem B3465499 : Blo 1621009 3465499 := bstep (se 1 (by rfl) ⟨2599124, by rfl⟩ : syracuseStep 3465499 = 5198249) B5198249
theorem B4105151 : Blo 1621009 4105151 := bstep (se 1 (by rfl) ⟨3078863, by rfl⟩ : syracuseStep 4105151 = 6157727) B6157727
theorem B2433983 : Blo 1621009 2433983 := bstep (se 1 (by rfl) ⟨1825487, by rfl⟩ : syracuseStep 2433983 = 3650975) B3650975
theorem B5844383 : Blo 1621009 5844383 := bstep (se 1 (by rfl) ⟨4383287, by rfl⟩ : syracuseStep 5844383 = 8766575) B8766575
theorem B3649607 : Blo 1621009 3649607 := bstep (se 1 (by rfl) ⟨2737205, by rfl⟩ : syracuseStep 3649607 = 5474411) B5474411
theorem B53334163 : Blo 1621009 53334163 := bstep (se 1 (by rfl) ⟨40000622, by rfl⟩ : syracuseStep 53334163 = 80001245) B80001245
theorem B22491503 : Blo 1621009 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B108180197 : Blo 1621009 108180197 := bstep (se 4 (by rfl) ⟨10141893, by rfl⟩ : syracuseStep 108180197 = 20283787) B20283787
theorem B119993561 : Blo 1621009 119993561 := bstep (se 2 (by rfl) ⟨44997585, by rfl⟩ : syracuseStep 119993561 = 89995171) B89995171
theorem B3651119 : Blo 1621009 3651119 := bstep (se 1 (by rfl) ⟨2738339, by rfl⟩ : syracuseStep 3651119 = 5476679) B5476679
theorem B50632559 : Blo 1621009 50632559 := bstep (se 1 (by rfl) ⟨37974419, by rfl⟩ : syracuseStep 50632559 = 75948839) B75948839
theorem B1621663 : Blo 1621009 1621663 := bstep (se 1 (by rfl) ⟨1216247, by rfl⟩ : syracuseStep 1621663 = 2432495) B2432495
theorem B2433071 : Blo 1621009 2433071 := bstep (se 1 (by rfl) ⟨1824803, by rfl⟩ : syracuseStep 2433071 = 3649607) B3649607
theorem B8208539 : Blo 1621009 8208539 := bstep (se 1 (by rfl) ⟨6156404, by rfl⟩ : syracuseStep 8208539 = 12312809) B12312809
theorem B4620665 : Blo 1621009 4620665 := bstep (se 2 (by rfl) ⟨1732749, by rfl⟩ : syracuseStep 4620665 = 3465499) B3465499
theorem B2736767 : Blo 1621009 2736767 := bstep (se 1 (by rfl) ⟨2052575, by rfl⟩ : syracuseStep 2736767 = 4105151) B4105151
theorem B1622655 : Blo 1621009 1622655 := bstep (se 1 (by rfl) ⟨1216991, by rfl⟩ : syracuseStep 1622655 = 2433983) B2433983
theorem B79995707 : Blo 1621009 79995707 := bstep (se 1 (by rfl) ⟨59996780, by rfl⟩ : syracuseStep 79995707 = 119993561) B119993561
theorem B2434079 : Blo 1621009 2434079 := bstep (se 1 (by rfl) ⟨1825559, by rfl⟩ : syracuseStep 2434079 = 3651119) B3651119
theorem B14994335 : Blo 1621009 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B27700541 : Blo 1621009 27700541 := bstep (se 3 (by rfl) ⟨5193851, by rfl⟩ : syracuseStep 27700541 = 10387703) B10387703
theorem B33755039 : Blo 1621009 33755039 := bstep (se 1 (by rfl) ⟨25316279, by rfl⟩ : syracuseStep 33755039 = 50632559) B50632559
theorem B3896255 : Blo 1621009 3896255 := bstep (se 1 (by rfl) ⟨2922191, by rfl⟩ : syracuseStep 3896255 = 5844383) B5844383
theorem B71112217 : Blo 1621009 71112217 := bstep (se 2 (by rfl) ⟨26667081, by rfl⟩ : syracuseStep 71112217 = 53334163) B53334163
theorem B72120131 : Blo 1621009 72120131 := bstep (se 1 (by rfl) ⟨54090098, by rfl⟩ : syracuseStep 72120131 = 108180197) B108180197
theorem B1622047 : Blo 1621009 1622047 := bstep (se 1 (by rfl) ⟨1216535, by rfl⟩ : syracuseStep 1622047 = 2433071) B2433071
theorem B5472359 : Blo 1621009 5472359 := bstep (se 1 (by rfl) ⟨4104269, by rfl⟩ : syracuseStep 5472359 = 8208539) B8208539
theorem B3080443 : Blo 1621009 3080443 := bstep (se 1 (by rfl) ⟨2310332, by rfl⟩ : syracuseStep 3080443 = 4620665) B4620665
theorem B53330471 : Blo 1621009 53330471 := bstep (se 1 (by rfl) ⟨39997853, by rfl⟩ : syracuseStep 53330471 = 79995707) B79995707
theorem B2597503 : Blo 1621009 2597503 := bstep (se 1 (by rfl) ⟨1948127, by rfl⟩ : syracuseStep 2597503 = 3896255) B3896255
theorem B1622719 : Blo 1621009 1622719 := bstep (se 1 (by rfl) ⟨1217039, by rfl⟩ : syracuseStep 1622719 = 2434079) B2434079
theorem B48080087 : Blo 1621009 48080087 := bstep (se 1 (by rfl) ⟨36060065, by rfl⟩ : syracuseStep 48080087 = 72120131) B72120131
theorem B9996223 : Blo 1621009 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B94816289 : Blo 1621009 94816289 := bstep (se 2 (by rfl) ⟨35556108, by rfl⟩ : syracuseStep 94816289 = 71112217) B71112217
theorem B18467027 : Blo 1621009 18467027 := bstep (se 1 (by rfl) ⟨13850270, by rfl⟩ : syracuseStep 18467027 = 27700541) B27700541
theorem B1824511 : Blo 1621009 1824511 := bstep (se 1 (by rfl) ⟨1368383, by rfl⟩ : syracuseStep 1824511 = 2736767) B2736767
theorem B22503359 : Blo 1621009 22503359 := bstep (se 1 (by rfl) ⟨16877519, by rfl⟩ : syracuseStep 22503359 = 33755039) B33755039
theorem B35553647 : Blo 1621009 35553647 := bstep (se 1 (by rfl) ⟨26665235, by rfl⟩ : syracuseStep 35553647 = 53330471) B53330471
theorem B60008957 : Blo 1621009 60008957 := bstep (se 3 (by rfl) ⟨11251679, by rfl⟩ : syracuseStep 60008957 = 22503359) B22503359
theorem B3648239 : Blo 1621009 3648239 := bstep (se 1 (by rfl) ⟨2736179, by rfl⟩ : syracuseStep 3648239 = 5472359) B5472359
theorem B4107257 : Blo 1621009 4107257 := bstep (se 2 (by rfl) ⟨1540221, by rfl⟩ : syracuseStep 4107257 = 3080443) B3080443
theorem B252843437 : Blo 1621009 252843437 := bstep (se 3 (by rfl) ⟨47408144, by rfl⟩ : syracuseStep 252843437 = 94816289) B94816289
theorem B32053391 : Blo 1621009 32053391 := bstep (se 1 (by rfl) ⟨24040043, by rfl⟩ : syracuseStep 32053391 = 48080087) B48080087
theorem B3463337 : Blo 1621009 3463337 := bstep (se 2 (by rfl) ⟨1298751, by rfl⟩ : syracuseStep 3463337 = 2597503) B2597503
theorem B12311351 : Blo 1621009 12311351 := bstep (se 1 (by rfl) ⟨9233513, by rfl⟩ : syracuseStep 12311351 = 18467027) B18467027
theorem B2432681 : Blo 1621009 2432681 := bstep (se 2 (by rfl) ⟨912255, by rfl⟩ : syracuseStep 2432681 = 1824511) B1824511
theorem B13328297 : Blo 1621009 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B2738171 : Blo 1621009 2738171 := bstep (se 1 (by rfl) ⟨2053628, by rfl⟩ : syracuseStep 2738171 = 4107257) B4107257
theorem B23702431 : Blo 1621009 23702431 := bstep (se 1 (by rfl) ⟨17776823, by rfl⟩ : syracuseStep 23702431 = 35553647) B35553647
theorem B9235565 : Blo 1621009 9235565 := bstep (se 3 (by rfl) ⟨1731668, by rfl⟩ : syracuseStep 9235565 = 3463337) B3463337
theorem B168562291 : Blo 1621009 168562291 := bstep (se 1 (by rfl) ⟨126421718, by rfl⟩ : syracuseStep 168562291 = 252843437) B252843437
theorem B21368927 : Blo 1621009 21368927 := bstep (se 1 (by rfl) ⟨16026695, by rfl⟩ : syracuseStep 21368927 = 32053391) B32053391
theorem B40005971 : Blo 1621009 40005971 := bstep (se 1 (by rfl) ⟨30004478, by rfl⟩ : syracuseStep 40005971 = 60008957) B60008957
theorem B8885531 : Blo 1621009 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B2432159 : Blo 1621009 2432159 := bstep (se 1 (by rfl) ⟨1824119, by rfl⟩ : syracuseStep 2432159 = 3648239) B3648239
theorem B8207567 : Blo 1621009 8207567 := bstep (se 1 (by rfl) ⟨6155675, by rfl⟩ : syracuseStep 8207567 = 12311351) B12311351
theorem B1621787 : Blo 1621009 1621787 := bstep (se 1 (by rfl) ⟨1216340, by rfl⟩ : syracuseStep 1621787 = 2432681) B2432681
theorem B14245951 : Blo 1621009 14245951 := bstep (se 1 (by rfl) ⟨10684463, by rfl⟩ : syracuseStep 14245951 = 21368927) B21368927
theorem B5923687 : Blo 1621009 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B224749721 : Blo 1621009 224749721 := bstep (se 2 (by rfl) ⟨84281145, by rfl⟩ : syracuseStep 224749721 = 168562291) B168562291
theorem B6157043 : Blo 1621009 6157043 := bstep (se 1 (by rfl) ⟨4617782, by rfl⟩ : syracuseStep 6157043 = 9235565) B9235565
theorem B26670647 : Blo 1621009 26670647 := bstep (se 1 (by rfl) ⟨20002985, by rfl⟩ : syracuseStep 26670647 = 40005971) B40005971
theorem B31603241 : Blo 1621009 31603241 := bstep (se 2 (by rfl) ⟨11851215, by rfl⟩ : syracuseStep 31603241 = 23702431) B23702431
theorem B1825447 : Blo 1621009 1825447 := bstep (se 1 (by rfl) ⟨1369085, by rfl⟩ : syracuseStep 1825447 = 2738171) B2738171
theorem B1621439 : Blo 1621009 1621439 := bstep (se 1 (by rfl) ⟨1216079, by rfl⟩ : syracuseStep 1621439 = 2432159) B2432159
theorem B5471711 : Blo 1621009 5471711 := bstep (se 1 (by rfl) ⟨4103783, by rfl⟩ : syracuseStep 5471711 = 8207567) B8207567
theorem B4104695 : Blo 1621009 4104695 := bstep (se 1 (by rfl) ⟨3078521, by rfl⟩ : syracuseStep 4104695 = 6157043) B6157043
theorem B2433929 : Blo 1621009 2433929 := bstep (se 2 (by rfl) ⟨912723, by rfl⟩ : syracuseStep 2433929 = 1825447) B1825447
theorem B7898249 : Blo 1621009 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B149833147 : Blo 1621009 149833147 := bstep (se 1 (by rfl) ⟨112374860, by rfl⟩ : syracuseStep 149833147 = 224749721) B224749721
theorem B3647807 : Blo 1621009 3647807 := bstep (se 1 (by rfl) ⟨2735855, by rfl⟩ : syracuseStep 3647807 = 5471711) B5471711
theorem B17780431 : Blo 1621009 17780431 := bstep (se 1 (by rfl) ⟨13335323, by rfl⟩ : syracuseStep 17780431 = 26670647) B26670647
theorem B84275309 : Blo 1621009 84275309 := bstep (se 3 (by rfl) ⟨15801620, by rfl⟩ : syracuseStep 84275309 = 31603241) B31603241
theorem B18994601 : Blo 1621009 18994601 := bstep (se 2 (by rfl) ⟨7122975, by rfl⟩ : syracuseStep 18994601 = 14245951) B14245951
theorem B2736463 : Blo 1621009 2736463 := bstep (se 1 (by rfl) ⟨2052347, by rfl⟩ : syracuseStep 2736463 = 4104695) B4104695
theorem B1622619 : Blo 1621009 1622619 := bstep (se 1 (by rfl) ⟨1216964, by rfl⟩ : syracuseStep 1622619 = 2433929) B2433929
theorem B56183539 : Blo 1621009 56183539 := bstep (se 1 (by rfl) ⟨42137654, by rfl⟩ : syracuseStep 56183539 = 84275309) B84275309
theorem B5265499 : Blo 1621009 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B12663067 : Blo 1621009 12663067 := bstep (se 1 (by rfl) ⟨9497300, by rfl⟩ : syracuseStep 12663067 = 18994601) B18994601
theorem B2431871 : Blo 1621009 2431871 := bstep (se 1 (by rfl) ⟨1823903, by rfl⟩ : syracuseStep 2431871 = 3647807) B3647807
theorem B199777529 : Blo 1621009 199777529 := bstep (se 2 (by rfl) ⟨74916573, by rfl⟩ : syracuseStep 199777529 = 149833147) B149833147
theorem B23707241 : Blo 1621009 23707241 := bstep (se 2 (by rfl) ⟨8890215, by rfl⟩ : syracuseStep 23707241 = 17780431) B17780431
theorem B7020665 : Blo 1621009 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B16884089 : Blo 1621009 16884089 := bstep (se 2 (by rfl) ⟨6331533, by rfl⟩ : syracuseStep 16884089 = 12663067) B12663067
theorem B15804827 : Blo 1621009 15804827 := bstep (se 1 (by rfl) ⟨11853620, by rfl⟩ : syracuseStep 15804827 = 23707241) B23707241
theorem B3648617 : Blo 1621009 3648617 := bstep (se 2 (by rfl) ⟨1368231, by rfl⟩ : syracuseStep 3648617 = 2736463) B2736463
theorem B74911385 : Blo 1621009 74911385 := bstep (se 2 (by rfl) ⟨28091769, by rfl⟩ : syracuseStep 74911385 = 56183539) B56183539
theorem B1621247 : Blo 1621009 1621247 := bstep (se 1 (by rfl) ⟨1215935, by rfl⟩ : syracuseStep 1621247 = 2431871) B2431871
theorem B133185019 : Blo 1621009 133185019 := bstep (se 1 (by rfl) ⟨99888764, by rfl⟩ : syracuseStep 133185019 = 199777529) B199777529
theorem B11256059 : Blo 1621009 11256059 := bstep (se 1 (by rfl) ⟨8442044, by rfl⟩ : syracuseStep 11256059 = 16884089) B16884089
theorem B10536551 : Blo 1621009 10536551 := bstep (se 1 (by rfl) ⟨7902413, by rfl⟩ : syracuseStep 10536551 = 15804827) B15804827
theorem B177580025 : Blo 1621009 177580025 := bstep (se 2 (by rfl) ⟨66592509, by rfl⟩ : syracuseStep 177580025 = 133185019) B133185019
theorem B49940923 : Blo 1621009 49940923 := bstep (se 1 (by rfl) ⟨37455692, by rfl⟩ : syracuseStep 49940923 = 74911385) B74911385
theorem B4680443 : Blo 1621009 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B2432411 : Blo 1621009 2432411 := bstep (se 1 (by rfl) ⟨1824308, by rfl⟩ : syracuseStep 2432411 = 3648617) B3648617
theorem B7504039 : Blo 1621009 7504039 := bstep (se 1 (by rfl) ⟨5628029, by rfl⟩ : syracuseStep 7504039 = 11256059) B11256059
theorem B66587897 : Blo 1621009 66587897 := bstep (se 2 (by rfl) ⟨24970461, by rfl⟩ : syracuseStep 66587897 = 49940923) B49940923
theorem B7024367 : Blo 1621009 7024367 := bstep (se 1 (by rfl) ⟨5268275, by rfl⟩ : syracuseStep 7024367 = 10536551) B10536551
theorem B118386683 : Blo 1621009 118386683 := bstep (se 1 (by rfl) ⟨88790012, by rfl⟩ : syracuseStep 118386683 = 177580025) B177580025
theorem B3120295 : Blo 1621009 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B1621607 : Blo 1621009 1621607 := bstep (se 1 (by rfl) ⟨1216205, by rfl⟩ : syracuseStep 1621607 = 2432411) B2432411
theorem B78924455 : Blo 1621009 78924455 := bstep (se 1 (by rfl) ⟨59193341, by rfl⟩ : syracuseStep 78924455 = 118386683) B118386683
theorem B10005385 : Blo 1621009 10005385 := bstep (se 2 (by rfl) ⟨3752019, by rfl⟩ : syracuseStep 10005385 = 7504039) B7504039
theorem B18731645 : Blo 1621009 18731645 := bstep (se 3 (by rfl) ⟨3512183, by rfl⟩ : syracuseStep 18731645 = 7024367) B7024367
theorem B4160393 : Blo 1621009 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B44391931 : Blo 1621009 44391931 := bstep (se 1 (by rfl) ⟨33293948, by rfl⟩ : syracuseStep 44391931 = 66587897) B66587897
theorem B12487763 : Blo 1621009 12487763 := bstep (se 1 (by rfl) ⟨9365822, by rfl⟩ : syracuseStep 12487763 = 18731645) B18731645
theorem B13340513 : Blo 1621009 13340513 := bstep (se 2 (by rfl) ⟨5002692, by rfl⟩ : syracuseStep 13340513 = 10005385) B10005385
theorem B2773595 : Blo 1621009 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B52616303 : Blo 1621009 52616303 := bstep (se 1 (by rfl) ⟨39462227, by rfl⟩ : syracuseStep 52616303 = 78924455) B78924455
theorem B236756965 : Blo 1621009 236756965 := bstep (se 4 (by rfl) ⟨22195965, by rfl⟩ : syracuseStep 236756965 = 44391931) B44391931
theorem B8325175 : Blo 1621009 8325175 := bstep (se 1 (by rfl) ⟨6243881, by rfl⟩ : syracuseStep 8325175 = 12487763) B12487763
theorem B8893675 : Blo 1621009 8893675 := bstep (se 1 (by rfl) ⟨6670256, by rfl⟩ : syracuseStep 8893675 = 13340513) B13340513
theorem B315675953 : Blo 1621009 315675953 := bstep (se 2 (by rfl) ⟨118378482, by rfl⟩ : syracuseStep 315675953 = 236756965) B236756965
theorem B1849063 : Blo 1621009 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B35077535 : Blo 1621009 35077535 := bstep (se 1 (by rfl) ⟨26308151, by rfl⟩ : syracuseStep 35077535 = 52616303) B52616303
theorem B11100233 : Blo 1621009 11100233 := bstep (se 2 (by rfl) ⟨4162587, by rfl⟩ : syracuseStep 11100233 = 8325175) B8325175
theorem B11858233 : Blo 1621009 11858233 := bstep (se 2 (by rfl) ⟨4446837, by rfl⟩ : syracuseStep 11858233 = 8893675) B8893675
theorem B23385023 : Blo 1621009 23385023 := bstep (se 1 (by rfl) ⟨17538767, by rfl⟩ : syracuseStep 23385023 = 35077535) B35077535
theorem B210450635 : Blo 1621009 210450635 := bstep (se 1 (by rfl) ⟨157837976, by rfl⟩ : syracuseStep 210450635 = 315675953) B315675953
theorem B2465417 : Blo 1621009 2465417 := bstep (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) B1849063
theorem B15810977 : Blo 1621009 15810977 := bstep (se 2 (by rfl) ⟨5929116, by rfl⟩ : syracuseStep 15810977 = 11858233) B11858233
theorem B15590015 : Blo 1621009 15590015 := bstep (se 1 (by rfl) ⟨11692511, by rfl⟩ : syracuseStep 15590015 = 23385023) B23385023
theorem B7400155 : Blo 1621009 7400155 := bstep (se 1 (by rfl) ⟨5550116, by rfl⟩ : syracuseStep 7400155 = 11100233) B11100233
theorem B140300423 : Blo 1621009 140300423 := bstep (se 1 (by rfl) ⟨105225317, by rfl⟩ : syracuseStep 140300423 = 210450635) B210450635
theorem B6574445 : Blo 1621009 6574445 := bstep (se 3 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 6574445 = 2465417) B2465417
theorem B4382963 : Blo 1621009 4382963 := bstep (se 1 (by rfl) ⟨3287222, by rfl⟩ : syracuseStep 4382963 = 6574445) B6574445
theorem B9866873 : Blo 1621009 9866873 := bstep (se 2 (by rfl) ⟨3700077, by rfl⟩ : syracuseStep 9866873 = 7400155) B7400155
theorem B93533615 : Blo 1621009 93533615 := bstep (se 1 (by rfl) ⟨70150211, by rfl⟩ : syracuseStep 93533615 = 140300423) B140300423
theorem B10393343 : Blo 1621009 10393343 := bstep (se 1 (by rfl) ⟨7795007, by rfl⟩ : syracuseStep 10393343 = 15590015) B15590015
theorem B42162605 : Blo 1621009 42162605 := bstep (se 3 (by rfl) ⟨7905488, by rfl⟩ : syracuseStep 42162605 = 15810977) B15810977
theorem B28108403 : Blo 1621009 28108403 := bstep (se 1 (by rfl) ⟨21081302, by rfl⟩ : syracuseStep 28108403 = 42162605) B42162605
theorem B2921975 : Blo 1621009 2921975 := bstep (se 1 (by rfl) ⟨2191481, by rfl⟩ : syracuseStep 2921975 = 4382963) B4382963
theorem B62355743 : Blo 1621009 62355743 := bstep (se 1 (by rfl) ⟨46766807, by rfl⟩ : syracuseStep 62355743 = 93533615) B93533615
theorem B6928895 : Blo 1621009 6928895 := bstep (se 1 (by rfl) ⟨5196671, by rfl⟩ : syracuseStep 6928895 = 10393343) B10393343
theorem B26311661 : Blo 1621009 26311661 := bstep (se 3 (by rfl) ⟨4933436, by rfl⟩ : syracuseStep 26311661 = 9866873) B9866873
theorem B17541107 : Blo 1621009 17541107 := bstep (se 1 (by rfl) ⟨13155830, by rfl⟩ : syracuseStep 17541107 = 26311661) B26311661
theorem B18738935 : Blo 1621009 18738935 := bstep (se 1 (by rfl) ⟨14054201, by rfl⟩ : syracuseStep 18738935 = 28108403) B28108403
theorem B41570495 : Blo 1621009 41570495 := bstep (se 1 (by rfl) ⟨31177871, by rfl⟩ : syracuseStep 41570495 = 62355743) B62355743
theorem B1947983 : Blo 1621009 1947983 := bstep (se 1 (by rfl) ⟨1460987, by rfl⟩ : syracuseStep 1947983 = 2921975) B2921975
theorem B4619263 : Blo 1621009 4619263 := bstep (se 1 (by rfl) ⟨3464447, by rfl⟩ : syracuseStep 4619263 = 6928895) B6928895
theorem B27713663 : Blo 1621009 27713663 := bstep (se 1 (by rfl) ⟨20785247, by rfl⟩ : syracuseStep 27713663 = 41570495) B41570495
theorem B5194621 : Blo 1621009 5194621 := bstep (se 3 (by rfl) ⟨973991, by rfl⟩ : syracuseStep 5194621 = 1947983) B1947983
theorem B11694071 : Blo 1621009 11694071 := bstep (se 1 (by rfl) ⟨8770553, by rfl⟩ : syracuseStep 11694071 = 17541107) B17541107
theorem B6159017 : Blo 1621009 6159017 := bstep (se 2 (by rfl) ⟨2309631, by rfl⟩ : syracuseStep 6159017 = 4619263) B4619263
theorem B12492623 : Blo 1621009 12492623 := bstep (se 1 (by rfl) ⟨9369467, by rfl⟩ : syracuseStep 12492623 = 18738935) B18738935
theorem B4106011 : Blo 1621009 4106011 := bstep (se 1 (by rfl) ⟨3079508, by rfl⟩ : syracuseStep 4106011 = 6159017) B6159017
theorem B18475775 : Blo 1621009 18475775 := bstep (se 1 (by rfl) ⟨13856831, by rfl⟩ : syracuseStep 18475775 = 27713663) B27713663
theorem B6926161 : Blo 1621009 6926161 := bstep (se 2 (by rfl) ⟨2597310, by rfl⟩ : syracuseStep 6926161 = 5194621) B5194621
theorem B8328415 : Blo 1621009 8328415 := bstep (se 1 (by rfl) ⟨6246311, by rfl⟩ : syracuseStep 8328415 = 12492623) B12492623
theorem B7796047 : Blo 1621009 7796047 := bstep (se 1 (by rfl) ⟨5847035, by rfl⟩ : syracuseStep 7796047 = 11694071) B11694071
theorem B5474681 : Blo 1621009 5474681 := bstep (se 2 (by rfl) ⟨2053005, by rfl⟩ : syracuseStep 5474681 = 4106011) B4106011
theorem B9234881 : Blo 1621009 9234881 := bstep (se 2 (by rfl) ⟨3463080, by rfl⟩ : syracuseStep 9234881 = 6926161) B6926161
theorem B11104553 : Blo 1621009 11104553 := bstep (se 2 (by rfl) ⟨4164207, by rfl⟩ : syracuseStep 11104553 = 8328415) B8328415
theorem B12317183 : Blo 1621009 12317183 := bstep (se 1 (by rfl) ⟨9237887, by rfl⟩ : syracuseStep 12317183 = 18475775) B18475775
theorem B10394729 : Blo 1621009 10394729 := bstep (se 2 (by rfl) ⟨3898023, by rfl⟩ : syracuseStep 10394729 = 7796047) B7796047
theorem B8211455 : Blo 1621009 8211455 := bstep (se 1 (by rfl) ⟨6158591, by rfl⟩ : syracuseStep 8211455 = 12317183) B12317183
theorem B3649787 : Blo 1621009 3649787 := bstep (se 1 (by rfl) ⟨2737340, by rfl⟩ : syracuseStep 3649787 = 5474681) B5474681
theorem B6156587 : Blo 1621009 6156587 := bstep (se 1 (by rfl) ⟨4617440, by rfl⟩ : syracuseStep 6156587 = 9234881) B9234881
theorem B29612141 : Blo 1621009 29612141 := bstep (se 3 (by rfl) ⟨5552276, by rfl⟩ : syracuseStep 29612141 = 11104553) B11104553
theorem B6929819 : Blo 1621009 6929819 := bstep (se 1 (by rfl) ⟨5197364, by rfl⟩ : syracuseStep 6929819 = 10394729) B10394729
theorem B2433191 : Blo 1621009 2433191 := bstep (se 1 (by rfl) ⟨1824893, by rfl⟩ : syracuseStep 2433191 = 3649787) B3649787
theorem B4104391 : Blo 1621009 4104391 := bstep (se 1 (by rfl) ⟨3078293, by rfl⟩ : syracuseStep 4104391 = 6156587) B6156587
theorem B5474303 : Blo 1621009 5474303 := bstep (se 1 (by rfl) ⟨4105727, by rfl⟩ : syracuseStep 5474303 = 8211455) B8211455
theorem B19741427 : Blo 1621009 19741427 := bstep (se 1 (by rfl) ⟨14806070, by rfl⟩ : syracuseStep 19741427 = 29612141) B29612141
theorem B4619879 : Blo 1621009 4619879 := bstep (se 1 (by rfl) ⟨3464909, by rfl⟩ : syracuseStep 4619879 = 6929819) B6929819
theorem B1622127 : Blo 1621009 1622127 := bstep (se 1 (by rfl) ⟨1216595, by rfl⟩ : syracuseStep 1622127 = 2433191) B2433191
theorem B5472521 : Blo 1621009 5472521 := bstep (se 2 (by rfl) ⟨2052195, by rfl⟩ : syracuseStep 5472521 = 4104391) B4104391
theorem B3649535 : Blo 1621009 3649535 := bstep (se 1 (by rfl) ⟨2737151, by rfl⟩ : syracuseStep 3649535 = 5474303) B5474303
theorem B13160951 : Blo 1621009 13160951 := bstep (se 1 (by rfl) ⟨9870713, by rfl⟩ : syracuseStep 13160951 = 19741427) B19741427
theorem B3079919 : Blo 1621009 3079919 := bstep (se 1 (by rfl) ⟨2309939, by rfl⟩ : syracuseStep 3079919 = 4619879) B4619879
theorem B8773967 : Blo 1621009 8773967 := bstep (se 1 (by rfl) ⟨6580475, by rfl⟩ : syracuseStep 8773967 = 13160951) B13160951
theorem B2433023 : Blo 1621009 2433023 := bstep (se 1 (by rfl) ⟨1824767, by rfl⟩ : syracuseStep 2433023 = 3649535) B3649535
theorem B3648347 : Blo 1621009 3648347 := bstep (se 1 (by rfl) ⟨2736260, by rfl⟩ : syracuseStep 3648347 = 5472521) B5472521
theorem B2053279 : Blo 1621009 2053279 := bstep (se 1 (by rfl) ⟨1539959, by rfl⟩ : syracuseStep 2053279 = 3079919) B3079919
theorem B23397245 : Blo 1621009 23397245 := bstep (se 3 (by rfl) ⟨4386983, by rfl⟩ : syracuseStep 23397245 = 8773967) B8773967
theorem B2737705 : Blo 1621009 2737705 := bstep (se 2 (by rfl) ⟨1026639, by rfl⟩ : syracuseStep 2737705 = 2053279) B2053279
theorem B2432231 : Blo 1621009 2432231 := bstep (se 1 (by rfl) ⟨1824173, by rfl⟩ : syracuseStep 2432231 = 3648347) B3648347
theorem B1622015 : Blo 1621009 1622015 := bstep (se 1 (by rfl) ⟨1216511, by rfl⟩ : syracuseStep 1622015 = 2433023) B2433023
theorem B15598163 : Blo 1621009 15598163 := bstep (se 1 (by rfl) ⟨11698622, by rfl⟩ : syracuseStep 15598163 = 23397245) B23397245
theorem B3650273 : Blo 1621009 3650273 := bstep (se 2 (by rfl) ⟨1368852, by rfl⟩ : syracuseStep 3650273 = 2737705) B2737705
theorem B1621487 : Blo 1621009 1621487 := bstep (se 1 (by rfl) ⟨1216115, by rfl⟩ : syracuseStep 1621487 = 2432231) B2432231
theorem B2433515 : Blo 1621009 2433515 := bstep (se 1 (by rfl) ⟨1825136, by rfl⟩ : syracuseStep 2433515 = 3650273) B3650273
theorem B10398775 : Blo 1621009 10398775 := bstep (se 1 (by rfl) ⟨7799081, by rfl⟩ : syracuseStep 10398775 = 15598163) B15598163
theorem B1622343 : Blo 1621009 1622343 := bstep (se 1 (by rfl) ⟨1216757, by rfl⟩ : syracuseStep 1622343 = 2433515) B2433515
theorem B13865033 : Blo 1621009 13865033 := bstep (se 2 (by rfl) ⟨5199387, by rfl⟩ : syracuseStep 13865033 = 10398775) B10398775
theorem B9243355 : Blo 1621009 9243355 := bstep (se 1 (by rfl) ⟨6932516, by rfl⟩ : syracuseStep 9243355 = 13865033) B13865033
theorem B12324473 : Blo 1621009 12324473 := bstep (se 2 (by rfl) ⟨4621677, by rfl⟩ : syracuseStep 12324473 = 9243355) B9243355
theorem B8216315 : Blo 1621009 8216315 := bstep (se 1 (by rfl) ⟨6162236, by rfl⟩ : syracuseStep 8216315 = 12324473) B12324473
theorem B5477543 : Blo 1621009 5477543 := bstep (se 1 (by rfl) ⟨4108157, by rfl⟩ : syracuseStep 5477543 = 8216315) B8216315
theorem B3651695 : Blo 1621009 3651695 := bstep (se 1 (by rfl) ⟨2738771, by rfl⟩ : syracuseStep 3651695 = 5477543) B5477543
theorem B2434463 : Blo 1621009 2434463 := bstep (se 1 (by rfl) ⟨1825847, by rfl⟩ : syracuseStep 2434463 = 3651695) B3651695
theorem B1622975 : Blo 1621009 1622975 := bstep (se 1 (by rfl) ⟨1217231, by rfl⟩ : syracuseStep 1622975 = 2434463) B2434463

theorem C0 (j : ℕ) (h1 : 405252 ≤ j) (h2 : j ≤ 405751) : Blo 1621009 (4 * j + 3) := by
  interval_cases j
  · exact B1621011
  · exact B1621015
  · exact B1621019
  · exact B1621023
  · exact B1621027
  · exact B1621031
  · exact B1621035
  · exact B1621039
  · exact B1621043
  · exact B1621047
  · exact B1621051
  · exact B1621055
  · exact B1621059
  · exact B1621063
  · exact B1621067
  · exact B1621071
  · exact B1621075
  · exact B1621079
  · exact B1621083
  · exact B1621087
  · exact B1621091
  · exact B1621095
  · exact B1621099
  · exact B1621103
  · exact B1621107
  · exact B1621111
  · exact B1621115
  · exact B1621119
  · exact B1621123
  · exact B1621127
  · exact B1621131
  · exact B1621135
  · exact B1621139
  · exact B1621143
  · exact B1621147
  · exact B1621151
  · exact B1621155
  · exact B1621159
  · exact B1621163
  · exact B1621167
  · exact B1621171
  · exact B1621175
  · exact B1621179
  · exact B1621183
  · exact B1621187
  · exact B1621191
  · exact B1621195
  · exact B1621199
  · exact B1621203
  · exact B1621207
  · exact B1621211
  · exact B1621215
  · exact B1621219
  · exact B1621223
  · exact B1621227
  · exact B1621231
  · exact B1621235
  · exact B1621239
  · exact B1621243
  · exact B1621247
  · exact B1621251
  · exact B1621255
  · exact B1621259
  · exact B1621263
  · exact B1621267
  · exact B1621271
  · exact B1621275
  · exact B1621279
  · exact B1621283
  · exact B1621287
  · exact B1621291
  · exact B1621295
  · exact B1621299
  · exact B1621303
  · exact B1621307
  · exact B1621311
  · exact B1621315
  · exact B1621319
  · exact B1621323
  · exact B1621327
  · exact B1621331
  · exact B1621335
  · exact B1621339
  · exact B1621343
  · exact B1621347
  · exact B1621351
  · exact B1621355
  · exact B1621359
  · exact B1621363
  · exact B1621367
  · exact B1621371
  · exact B1621375
  · exact B1621379
  · exact B1621383
  · exact B1621387
  · exact B1621391
  · exact B1621395
  · exact B1621399
  · exact B1621403
  · exact B1621407
  · exact B1621411
  · exact B1621415
  · exact B1621419
  · exact B1621423
  · exact B1621427
  · exact B1621431
  · exact B1621435
  · exact B1621439
  · exact B1621443
  · exact B1621447
  · exact B1621451
  · exact B1621455
  · exact B1621459
  · exact B1621463
  · exact B1621467
  · exact B1621471
  · exact B1621475
  · exact B1621479
  · exact B1621483
  · exact B1621487
  · exact B1621491
  · exact B1621495
  · exact B1621499
  · exact B1621503
  · exact B1621507
  · exact B1621511
  · exact B1621515
  · exact B1621519
  · exact B1621523
  · exact B1621527
  · exact B1621531
  · exact B1621535
  · exact B1621539
  · exact B1621543
  · exact B1621547
  · exact B1621551
  · exact B1621555
  · exact B1621559
  · exact B1621563
  · exact B1621567
  · exact B1621571
  · exact B1621575
  · exact B1621579
  · exact B1621583
  · exact B1621587
  · exact B1621591
  · exact B1621595
  · exact B1621599
  · exact B1621603
  · exact B1621607
  · exact B1621611
  · exact B1621615
  · exact B1621619
  · exact B1621623
  · exact B1621627
  · exact B1621631
  · exact B1621635
  · exact B1621639
  · exact B1621643
  · exact B1621647
  · exact B1621651
  · exact B1621655
  · exact B1621659
  · exact B1621663
  · exact B1621667
  · exact B1621671
  · exact B1621675
  · exact B1621679
  · exact B1621683
  · exact B1621687
  · exact B1621691
  · exact B1621695
  · exact B1621699
  · exact B1621703
  · exact B1621707
  · exact B1621711
  · exact B1621715
  · exact B1621719
  · exact B1621723
  · exact B1621727
  · exact B1621731
  · exact B1621735
  · exact B1621739
  · exact B1621743
  · exact B1621747
  · exact B1621751
  · exact B1621755
  · exact B1621759
  · exact B1621763
  · exact B1621767
  · exact B1621771
  · exact B1621775
  · exact B1621779
  · exact B1621783
  · exact B1621787
  · exact B1621791
  · exact B1621795
  · exact B1621799
  · exact B1621803
  · exact B1621807
  · exact B1621811
  · exact B1621815
  · exact B1621819
  · exact B1621823
  · exact B1621827
  · exact B1621831
  · exact B1621835
  · exact B1621839
  · exact B1621843
  · exact B1621847
  · exact B1621851
  · exact B1621855
  · exact B1621859
  · exact B1621863
  · exact B1621867
  · exact B1621871
  · exact B1621875
  · exact B1621879
  · exact B1621883
  · exact B1621887
  · exact B1621891
  · exact B1621895
  · exact B1621899
  · exact B1621903
  · exact B1621907
  · exact B1621911
  · exact B1621915
  · exact B1621919
  · exact B1621923
  · exact B1621927
  · exact B1621931
  · exact B1621935
  · exact B1621939
  · exact B1621943
  · exact B1621947
  · exact B1621951
  · exact B1621955
  · exact B1621959
  · exact B1621963
  · exact B1621967
  · exact B1621971
  · exact B1621975
  · exact B1621979
  · exact B1621983
  · exact B1621987
  · exact B1621991
  · exact B1621995
  · exact B1621999
  · exact B1622003
  · exact B1622007
  · exact B1622011
  · exact B1622015
  · exact B1622019
  · exact B1622023
  · exact B1622027
  · exact B1622031
  · exact B1622035
  · exact B1622039
  · exact B1622043
  · exact B1622047
  · exact B1622051
  · exact B1622055
  · exact B1622059
  · exact B1622063
  · exact B1622067
  · exact B1622071
  · exact B1622075
  · exact B1622079
  · exact B1622083
  · exact B1622087
  · exact B1622091
  · exact B1622095
  · exact B1622099
  · exact B1622103
  · exact B1622107
  · exact B1622111
  · exact B1622115
  · exact B1622119
  · exact B1622123
  · exact B1622127
  · exact B1622131
  · exact B1622135
  · exact B1622139
  · exact B1622143
  · exact B1622147
  · exact B1622151
  · exact B1622155
  · exact B1622159
  · exact B1622163
  · exact B1622167
  · exact B1622171
  · exact B1622175
  · exact B1622179
  · exact B1622183
  · exact B1622187
  · exact B1622191
  · exact B1622195
  · exact B1622199
  · exact B1622203
  · exact B1622207
  · exact B1622211
  · exact B1622215
  · exact B1622219
  · exact B1622223
  · exact B1622227
  · exact B1622231
  · exact B1622235
  · exact B1622239
  · exact B1622243
  · exact B1622247
  · exact B1622251
  · exact B1622255
  · exact B1622259
  · exact B1622263
  · exact B1622267
  · exact B1622271
  · exact B1622275
  · exact B1622279
  · exact B1622283
  · exact B1622287
  · exact B1622291
  · exact B1622295
  · exact B1622299
  · exact B1622303
  · exact B1622307
  · exact B1622311
  · exact B1622315
  · exact B1622319
  · exact B1622323
  · exact B1622327
  · exact B1622331
  · exact B1622335
  · exact B1622339
  · exact B1622343
  · exact B1622347
  · exact B1622351
  · exact B1622355
  · exact B1622359
  · exact B1622363
  · exact B1622367
  · exact B1622371
  · exact B1622375
  · exact B1622379
  · exact B1622383
  · exact B1622387
  · exact B1622391
  · exact B1622395
  · exact B1622399
  · exact B1622403
  · exact B1622407
  · exact B1622411
  · exact B1622415
  · exact B1622419
  · exact B1622423
  · exact B1622427
  · exact B1622431
  · exact B1622435
  · exact B1622439
  · exact B1622443
  · exact B1622447
  · exact B1622451
  · exact B1622455
  · exact B1622459
  · exact B1622463
  · exact B1622467
  · exact B1622471
  · exact B1622475
  · exact B1622479
  · exact B1622483
  · exact B1622487
  · exact B1622491
  · exact B1622495
  · exact B1622499
  · exact B1622503
  · exact B1622507
  · exact B1622511
  · exact B1622515
  · exact B1622519
  · exact B1622523
  · exact B1622527
  · exact B1622531
  · exact B1622535
  · exact B1622539
  · exact B1622543
  · exact B1622547
  · exact B1622551
  · exact B1622555
  · exact B1622559
  · exact B1622563
  · exact B1622567
  · exact B1622571
  · exact B1622575
  · exact B1622579
  · exact B1622583
  · exact B1622587
  · exact B1622591
  · exact B1622595
  · exact B1622599
  · exact B1622603
  · exact B1622607
  · exact B1622611
  · exact B1622615
  · exact B1622619
  · exact B1622623
  · exact B1622627
  · exact B1622631
  · exact B1622635
  · exact B1622639
  · exact B1622643
  · exact B1622647
  · exact B1622651
  · exact B1622655
  · exact B1622659
  · exact B1622663
  · exact B1622667
  · exact B1622671
  · exact B1622675
  · exact B1622679
  · exact B1622683
  · exact B1622687
  · exact B1622691
  · exact B1622695
  · exact B1622699
  · exact B1622703
  · exact B1622707
  · exact B1622711
  · exact B1622715
  · exact B1622719
  · exact B1622723
  · exact B1622727
  · exact B1622731
  · exact B1622735
  · exact B1622739
  · exact B1622743
  · exact B1622747
  · exact B1622751
  · exact B1622755
  · exact B1622759
  · exact B1622763
  · exact B1622767
  · exact B1622771
  · exact B1622775
  · exact B1622779
  · exact B1622783
  · exact B1622787
  · exact B1622791
  · exact B1622795
  · exact B1622799
  · exact B1622803
  · exact B1622807
  · exact B1622811
  · exact B1622815
  · exact B1622819
  · exact B1622823
  · exact B1622827
  · exact B1622831
  · exact B1622835
  · exact B1622839
  · exact B1622843
  · exact B1622847
  · exact B1622851
  · exact B1622855
  · exact B1622859
  · exact B1622863
  · exact B1622867
  · exact B1622871
  · exact B1622875
  · exact B1622879
  · exact B1622883
  · exact B1622887
  · exact B1622891
  · exact B1622895
  · exact B1622899
  · exact B1622903
  · exact B1622907
  · exact B1622911
  · exact B1622915
  · exact B1622919
  · exact B1622923
  · exact B1622927
  · exact B1622931
  · exact B1622935
  · exact B1622939
  · exact B1622943
  · exact B1622947
  · exact B1622951
  · exact B1622955
  · exact B1622959
  · exact B1622963
  · exact B1622967
  · exact B1622971
  · exact B1622975
  · exact B1622979
  · exact B1622983
  · exact B1622987
  · exact B1622991
  · exact B1622995
  · exact B1622999
  · exact B1623003
  · exact B1623007

theorem solution (m : ℕ) (hlo : 1621009 ≤ m) (hhi : m ≤ 1623009) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 405252 ≤ j := by omega
    have hj2 : j ≤ 405751 := by omega
    have hb : Blo 1621009 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
