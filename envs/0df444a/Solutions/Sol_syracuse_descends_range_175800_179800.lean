-- Prove2me | solution 1 for syracuse_descends_range_175800_179800
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:45.854122+00:00
-- url     : https://prove2.me/submissions/cb3b1bc5-2a56-4831-9e95-9df3d022f6cf

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


theorem B1015861 : Blo 175800 1015861 := bbase (se 5 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 1015861 = 95237) (by norm_num)
theorem B557237 : Blo 175800 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B327917 : Blo 175800 327917 := bbase (se 3 (by rfl) ⟨61484, by rfl⟩ : syracuseStep 327917 = 122969) (by norm_num)
theorem B1507733 : Blo 175800 1507733 := bbase (se 6 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 1507733 = 70675) (by norm_num)
theorem B3277205 : Blo 175800 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B262909 : Blo 175800 262909 := bbase (se 3 (by rfl) ⟨49295, by rfl⟩ : syracuseStep 262909 = 98591) (by norm_num)
theorem B1147765 : Blo 175800 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B852869 : Blo 175800 852869 := bbase (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) (by norm_num)
theorem B721813 : Blo 175800 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B197797 : Blo 175800 197797 := bbase (se 4 (by rfl) ⟨18543, by rfl⟩ : syracuseStep 197797 = 37087) (by norm_num)
theorem B197833 : Blo 175800 197833 := bbase (se 2 (by rfl) ⟨74187, by rfl⟩ : syracuseStep 197833 = 148375) (by norm_num)
theorem B197869 : Blo 175800 197869 := bbase (se 3 (by rfl) ⟨37100, by rfl⟩ : syracuseStep 197869 = 74201) (by norm_num)
theorem B197905 : Blo 175800 197905 := bbase (se 2 (by rfl) ⟨74214, by rfl⟩ : syracuseStep 197905 = 148429) (by norm_num)
theorem B197941 : Blo 175800 197941 := bbase (se 5 (by rfl) ⟨9278, by rfl⟩ : syracuseStep 197941 = 18557) (by norm_num)
theorem B197977 : Blo 175800 197977 := bbase (se 2 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 197977 = 148483) (by norm_num)
theorem B198013 : Blo 175800 198013 := bbase (se 3 (by rfl) ⟨37127, by rfl⟩ : syracuseStep 198013 = 74255) (by norm_num)
theorem B198049 : Blo 175800 198049 := bbase (se 2 (by rfl) ⟨74268, by rfl⟩ : syracuseStep 198049 = 148537) (by norm_num)
theorem B198085 : Blo 175800 198085 := bbase (se 4 (by rfl) ⟨18570, by rfl⟩ : syracuseStep 198085 = 37141) (by norm_num)
theorem B460261 : Blo 175800 460261 := bbase (se 4 (by rfl) ⟨43149, by rfl⟩ : syracuseStep 460261 = 86299) (by norm_num)
theorem B198121 : Blo 175800 198121 := bbase (se 2 (by rfl) ⟨74295, by rfl⟩ : syracuseStep 198121 = 148591) (by norm_num)
theorem B1836533 : Blo 175800 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B198157 : Blo 175800 198157 := bbase (se 3 (by rfl) ⟨37154, by rfl⟩ : syracuseStep 198157 = 74309) (by norm_num)
theorem B263717 : Blo 175800 263717 := bbase (se 4 (by rfl) ⟨24723, by rfl⟩ : syracuseStep 263717 = 49447) (by norm_num)
theorem B198193 : Blo 175800 198193 := bbase (se 2 (by rfl) ⟨74322, by rfl⟩ : syracuseStep 198193 = 148645) (by norm_num)
theorem B263741 : Blo 175800 263741 := bbase (se 3 (by rfl) ⟨49451, by rfl⟩ : syracuseStep 263741 = 98903) (by norm_num)
theorem B263765 : Blo 175800 263765 := bbase (se 8 (by rfl) ⟨1545, by rfl⟩ : syracuseStep 263765 = 3091) (by norm_num)
theorem B198229 : Blo 175800 198229 := bbase (se 8 (by rfl) ⟨1161, by rfl⟩ : syracuseStep 198229 = 2323) (by norm_num)
theorem B263789 : Blo 175800 263789 := bbase (se 3 (by rfl) ⟨49460, by rfl⟩ : syracuseStep 263789 = 98921) (by norm_num)
theorem B198265 : Blo 175800 198265 := bbase (se 2 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 198265 = 148699) (by norm_num)
theorem B263813 : Blo 175800 263813 := bbase (se 4 (by rfl) ⟨24732, by rfl⟩ : syracuseStep 263813 = 49465) (by norm_num)
theorem B263837 : Blo 175800 263837 := bbase (se 3 (by rfl) ⟨49469, by rfl⟩ : syracuseStep 263837 = 98939) (by norm_num)
theorem B198301 : Blo 175800 198301 := bbase (se 3 (by rfl) ⟨37181, by rfl⟩ : syracuseStep 198301 = 74363) (by norm_num)
theorem B263861 : Blo 175800 263861 := bbase (se 5 (by rfl) ⟨12368, by rfl⟩ : syracuseStep 263861 = 24737) (by norm_num)
theorem B362165 : Blo 175800 362165 := bbase (se 5 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 362165 = 33953) (by norm_num)
theorem B198337 : Blo 175800 198337 := bbase (se 2 (by rfl) ⟨74376, by rfl⟩ : syracuseStep 198337 = 148753) (by norm_num)
theorem B263885 : Blo 175800 263885 := bbase (se 3 (by rfl) ⟨49478, by rfl⟩ : syracuseStep 263885 = 98957) (by norm_num)
theorem B296669 : Blo 175800 296669 := bbase (se 3 (by rfl) ⟨55625, by rfl⟩ : syracuseStep 296669 = 111251) (by norm_num)
theorem B263909 : Blo 175800 263909 := bbase (se 4 (by rfl) ⟨24741, by rfl⟩ : syracuseStep 263909 = 49483) (by norm_num)
theorem B198373 : Blo 175800 198373 := bbase (se 4 (by rfl) ⟨18597, by rfl⟩ : syracuseStep 198373 = 37195) (by norm_num)
theorem B263933 : Blo 175800 263933 := bbase (se 3 (by rfl) ⟨49487, by rfl⟩ : syracuseStep 263933 = 98975) (by norm_num)
theorem B198409 : Blo 175800 198409 := bbase (se 2 (by rfl) ⟨74403, by rfl⟩ : syracuseStep 198409 = 148807) (by norm_num)
theorem B263957 : Blo 175800 263957 := bbase (se 6 (by rfl) ⟨6186, by rfl⟩ : syracuseStep 263957 = 12373) (by norm_num)
theorem B263981 : Blo 175800 263981 := bbase (se 3 (by rfl) ⟨49496, by rfl⟩ : syracuseStep 263981 = 98993) (by norm_num)
theorem B198445 : Blo 175800 198445 := bbase (se 3 (by rfl) ⟨37208, by rfl⟩ : syracuseStep 198445 = 74417) (by norm_num)
theorem B264005 : Blo 175800 264005 := bbase (se 4 (by rfl) ⟨24750, by rfl⟩ : syracuseStep 264005 = 49501) (by norm_num)
theorem B198481 : Blo 175800 198481 := bbase (se 2 (by rfl) ⟨74430, by rfl⟩ : syracuseStep 198481 = 148861) (by norm_num)
theorem B296797 : Blo 175800 296797 := bbase (se 3 (by rfl) ⟨55649, by rfl⟩ : syracuseStep 296797 = 111299) (by norm_num)
theorem B264029 : Blo 175800 264029 := bbase (se 3 (by rfl) ⟨49505, by rfl⟩ : syracuseStep 264029 = 99011) (by norm_num)
theorem B264053 : Blo 175800 264053 := bbase (se 5 (by rfl) ⟨12377, by rfl⟩ : syracuseStep 264053 = 24755) (by norm_num)
theorem B198517 : Blo 175800 198517 := bbase (se 5 (by rfl) ⟨9305, by rfl⟩ : syracuseStep 198517 = 18611) (by norm_num)
theorem B264077 : Blo 175800 264077 := bbase (se 3 (by rfl) ⟨49514, by rfl⟩ : syracuseStep 264077 = 99029) (by norm_num)
theorem B198553 : Blo 175800 198553 := bbase (se 2 (by rfl) ⟨74457, by rfl⟩ : syracuseStep 198553 = 148915) (by norm_num)
theorem B264101 : Blo 175800 264101 := bbase (se 4 (by rfl) ⟨24759, by rfl⟩ : syracuseStep 264101 = 49519) (by norm_num)
theorem B296885 : Blo 175800 296885 := bbase (se 5 (by rfl) ⟨13916, by rfl⟩ : syracuseStep 296885 = 27833) (by norm_num)
theorem B264125 : Blo 175800 264125 := bbase (se 3 (by rfl) ⟨49523, by rfl⟩ : syracuseStep 264125 = 99047) (by norm_num)
theorem B198589 : Blo 175800 198589 := bbase (se 3 (by rfl) ⟨37235, by rfl⟩ : syracuseStep 198589 = 74471) (by norm_num)
theorem B264149 : Blo 175800 264149 := bbase (se 7 (by rfl) ⟨3095, by rfl⟩ : syracuseStep 264149 = 6191) (by norm_num)
theorem B198625 : Blo 175800 198625 := bbase (se 2 (by rfl) ⟨74484, by rfl⟩ : syracuseStep 198625 = 148969) (by norm_num)
theorem B264173 : Blo 175800 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B1017845 : Blo 175800 1017845 := bbase (se 5 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 1017845 = 95423) (by norm_num)
theorem B264197 : Blo 175800 264197 := bbase (se 4 (by rfl) ⟨24768, by rfl⟩ : syracuseStep 264197 = 49537) (by norm_num)
theorem B198661 : Blo 175800 198661 := bbase (se 4 (by rfl) ⟨18624, by rfl⟩ : syracuseStep 198661 = 37249) (by norm_num)
theorem B264221 : Blo 175800 264221 := bbase (se 3 (by rfl) ⟨49541, by rfl⟩ : syracuseStep 264221 = 99083) (by norm_num)
theorem B198697 : Blo 175800 198697 := bbase (se 2 (by rfl) ⟨74511, by rfl⟩ : syracuseStep 198697 = 149023) (by norm_num)
theorem B297013 : Blo 175800 297013 := bbase (se 5 (by rfl) ⟨13922, by rfl⟩ : syracuseStep 297013 = 27845) (by norm_num)
theorem B264245 : Blo 175800 264245 := bbase (se 5 (by rfl) ⟨12386, by rfl⟩ : syracuseStep 264245 = 24773) (by norm_num)
theorem B264269 : Blo 175800 264269 := bbase (se 3 (by rfl) ⟨49550, by rfl⟩ : syracuseStep 264269 = 99101) (by norm_num)
theorem B198733 : Blo 175800 198733 := bbase (se 3 (by rfl) ⟨37262, by rfl⟩ : syracuseStep 198733 = 74525) (by norm_num)
theorem B264293 : Blo 175800 264293 := bbase (se 4 (by rfl) ⟨24777, by rfl⟩ : syracuseStep 264293 = 49555) (by norm_num)
theorem B198769 : Blo 175800 198769 := bbase (se 2 (by rfl) ⟨74538, by rfl⟩ : syracuseStep 198769 = 149077) (by norm_num)
theorem B264317 : Blo 175800 264317 := bbase (se 3 (by rfl) ⟨49559, by rfl⟩ : syracuseStep 264317 = 99119) (by norm_num)
theorem B297101 : Blo 175800 297101 := bbase (se 3 (by rfl) ⟨55706, by rfl⟩ : syracuseStep 297101 = 111413) (by norm_num)
theorem B264341 : Blo 175800 264341 := bbase (se 6 (by rfl) ⟨6195, by rfl⟩ : syracuseStep 264341 = 12391) (by norm_num)
theorem B198805 : Blo 175800 198805 := bbase (se 6 (by rfl) ⟨4659, by rfl⟩ : syracuseStep 198805 = 9319) (by norm_num)
theorem B264365 : Blo 175800 264365 := bbase (se 3 (by rfl) ⟨49568, by rfl⟩ : syracuseStep 264365 = 99137) (by norm_num)
theorem B198841 : Blo 175800 198841 := bbase (se 2 (by rfl) ⟨74565, by rfl⟩ : syracuseStep 198841 = 149131) (by norm_num)
theorem B264389 : Blo 175800 264389 := bbase (se 4 (by rfl) ⟨24786, by rfl⟩ : syracuseStep 264389 = 49573) (by norm_num)
theorem B264413 : Blo 175800 264413 := bbase (se 3 (by rfl) ⟨49577, by rfl⟩ : syracuseStep 264413 = 99155) (by norm_num)
theorem B198877 : Blo 175800 198877 := bbase (se 3 (by rfl) ⟨37289, by rfl⟩ : syracuseStep 198877 = 74579) (by norm_num)
theorem B264437 : Blo 175800 264437 := bbase (se 5 (by rfl) ⟨12395, by rfl⟩ : syracuseStep 264437 = 24791) (by norm_num)
theorem B198913 : Blo 175800 198913 := bbase (se 2 (by rfl) ⟨74592, by rfl⟩ : syracuseStep 198913 = 149185) (by norm_num)
theorem B297229 : Blo 175800 297229 := bbase (se 3 (by rfl) ⟨55730, by rfl⟩ : syracuseStep 297229 = 111461) (by norm_num)
theorem B264461 : Blo 175800 264461 := bbase (se 3 (by rfl) ⟨49586, by rfl⟩ : syracuseStep 264461 = 99173) (by norm_num)
theorem B362765 : Blo 175800 362765 := bbase (se 3 (by rfl) ⟨68018, by rfl⟩ : syracuseStep 362765 = 136037) (by norm_num)
theorem B264485 : Blo 175800 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B198949 : Blo 175800 198949 := bbase (se 4 (by rfl) ⟨18651, by rfl⟩ : syracuseStep 198949 = 37303) (by norm_num)
theorem B264509 : Blo 175800 264509 := bbase (se 3 (by rfl) ⟨49595, by rfl⟩ : syracuseStep 264509 = 99191) (by norm_num)
theorem B198985 : Blo 175800 198985 := bbase (se 2 (by rfl) ⟨74619, by rfl⟩ : syracuseStep 198985 = 149239) (by norm_num)
theorem B264533 : Blo 175800 264533 := bbase (se 10 (by rfl) ⟨387, by rfl⟩ : syracuseStep 264533 = 775) (by norm_num)
theorem B362837 : Blo 175800 362837 := bbase (se 10 (by rfl) ⟨531, by rfl⟩ : syracuseStep 362837 = 1063) (by norm_num)
theorem B395621 : Blo 175800 395621 := bbase (se 4 (by rfl) ⟨37089, by rfl⟩ : syracuseStep 395621 = 74179) (by norm_num)
theorem B297317 : Blo 175800 297317 := bbase (se 4 (by rfl) ⟨27873, by rfl⟩ : syracuseStep 297317 = 55747) (by norm_num)
theorem B264557 : Blo 175800 264557 := bbase (se 3 (by rfl) ⟨49604, by rfl⟩ : syracuseStep 264557 = 99209) (by norm_num)
theorem B199021 : Blo 175800 199021 := bbase (se 3 (by rfl) ⟨37316, by rfl⟩ : syracuseStep 199021 = 74633) (by norm_num)
theorem B428413 : Blo 175800 428413 := bbase (se 3 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 428413 = 160655) (by norm_num)
theorem B264581 : Blo 175800 264581 := bbase (se 4 (by rfl) ⟨24804, by rfl⟩ : syracuseStep 264581 = 49609) (by norm_num)
theorem B199057 : Blo 175800 199057 := bbase (se 2 (by rfl) ⟨74646, by rfl⟩ : syracuseStep 199057 = 149293) (by norm_num)
theorem B264605 : Blo 175800 264605 := bbase (se 3 (by rfl) ⟨49613, by rfl⟩ : syracuseStep 264605 = 99227) (by norm_num)
theorem B395693 : Blo 175800 395693 := bbase (se 3 (by rfl) ⟨74192, by rfl⟩ : syracuseStep 395693 = 148385) (by norm_num)
theorem B264629 : Blo 175800 264629 := bbase (se 5 (by rfl) ⟨12404, by rfl⟩ : syracuseStep 264629 = 24809) (by norm_num)
theorem B199093 : Blo 175800 199093 := bbase (se 5 (by rfl) ⟨9332, by rfl⟩ : syracuseStep 199093 = 18665) (by norm_num)
theorem B264653 : Blo 175800 264653 := bbase (se 3 (by rfl) ⟨49622, by rfl⟩ : syracuseStep 264653 = 99245) (by norm_num)
theorem B199129 : Blo 175800 199129 := bbase (se 2 (by rfl) ⟨74673, by rfl⟩ : syracuseStep 199129 = 149347) (by norm_num)
theorem B297445 : Blo 175800 297445 := bbase (se 4 (by rfl) ⟨27885, by rfl⟩ : syracuseStep 297445 = 55771) (by norm_num)
theorem B264677 : Blo 175800 264677 := bbase (se 4 (by rfl) ⟨24813, by rfl⟩ : syracuseStep 264677 = 49627) (by norm_num)
theorem B395765 : Blo 175800 395765 := bbase (se 5 (by rfl) ⟨18551, by rfl⟩ : syracuseStep 395765 = 37103) (by norm_num)
theorem B264701 : Blo 175800 264701 := bbase (se 3 (by rfl) ⟨49631, by rfl⟩ : syracuseStep 264701 = 99263) (by norm_num)
theorem B199165 : Blo 175800 199165 := bbase (se 3 (by rfl) ⟨37343, by rfl⟩ : syracuseStep 199165 = 74687) (by norm_num)
theorem B264725 : Blo 175800 264725 := bbase (se 6 (by rfl) ⟨6204, by rfl⟩ : syracuseStep 264725 = 12409) (by norm_num)
theorem B199201 : Blo 175800 199201 := bbase (se 2 (by rfl) ⟨74700, by rfl⟩ : syracuseStep 199201 = 149401) (by norm_num)
theorem B264749 : Blo 175800 264749 := bbase (se 3 (by rfl) ⟨49640, by rfl⟩ : syracuseStep 264749 = 99281) (by norm_num)
theorem B395837 : Blo 175800 395837 := bbase (se 3 (by rfl) ⟨74219, by rfl⟩ : syracuseStep 395837 = 148439) (by norm_num)
theorem B297533 : Blo 175800 297533 := bbase (se 3 (by rfl) ⟨55787, by rfl⟩ : syracuseStep 297533 = 111575) (by norm_num)
theorem B264773 : Blo 175800 264773 := bbase (se 4 (by rfl) ⟨24822, by rfl⟩ : syracuseStep 264773 = 49645) (by norm_num)
theorem B199237 : Blo 175800 199237 := bbase (se 4 (by rfl) ⟨18678, by rfl⟩ : syracuseStep 199237 = 37357) (by norm_num)
theorem B264797 : Blo 175800 264797 := bbase (se 3 (by rfl) ⟨49649, by rfl⟩ : syracuseStep 264797 = 99299) (by norm_num)
theorem B428645 : Blo 175800 428645 := bbase (se 4 (by rfl) ⟨40185, by rfl⟩ : syracuseStep 428645 = 80371) (by norm_num)
theorem B199273 : Blo 175800 199273 := bbase (se 2 (by rfl) ⟨74727, by rfl⟩ : syracuseStep 199273 = 149455) (by norm_num)
theorem B264821 : Blo 175800 264821 := bbase (se 5 (by rfl) ⟨12413, by rfl⟩ : syracuseStep 264821 = 24827) (by norm_num)
theorem B395909 : Blo 175800 395909 := bbase (se 4 (by rfl) ⟨37116, by rfl⟩ : syracuseStep 395909 = 74233) (by norm_num)
theorem B264845 : Blo 175800 264845 := bbase (se 3 (by rfl) ⟨49658, by rfl⟩ : syracuseStep 264845 = 99317) (by norm_num)
theorem B199309 : Blo 175800 199309 := bbase (se 3 (by rfl) ⟨37370, by rfl⟩ : syracuseStep 199309 = 74741) (by norm_num)
theorem B264869 : Blo 175800 264869 := bbase (se 4 (by rfl) ⟨24831, by rfl⟩ : syracuseStep 264869 = 49663) (by norm_num)
theorem B199345 : Blo 175800 199345 := bbase (se 2 (by rfl) ⟨74754, by rfl⟩ : syracuseStep 199345 = 149509) (by norm_num)
theorem B1215157 : Blo 175800 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B297661 : Blo 175800 297661 := bbase (se 3 (by rfl) ⟨55811, by rfl⟩ : syracuseStep 297661 = 111623) (by norm_num)
theorem B264893 : Blo 175800 264893 := bbase (se 3 (by rfl) ⟨49667, by rfl⟩ : syracuseStep 264893 = 99335) (by norm_num)
theorem B395981 : Blo 175800 395981 := bbase (se 3 (by rfl) ⟨74246, by rfl⟩ : syracuseStep 395981 = 148493) (by norm_num)
theorem B264917 : Blo 175800 264917 := bbase (se 7 (by rfl) ⟨3104, by rfl⟩ : syracuseStep 264917 = 6209) (by norm_num)
theorem B199381 : Blo 175800 199381 := bbase (se 7 (by rfl) ⟨2336, by rfl⟩ : syracuseStep 199381 = 4673) (by norm_num)
theorem B264941 : Blo 175800 264941 := bbase (se 3 (by rfl) ⟨49676, by rfl⟩ : syracuseStep 264941 = 99353) (by norm_num)
theorem B428789 : Blo 175800 428789 := bbase (se 5 (by rfl) ⟨20099, by rfl⟩ : syracuseStep 428789 = 40199) (by norm_num)
theorem B199417 : Blo 175800 199417 := bbase (se 2 (by rfl) ⟨74781, by rfl⟩ : syracuseStep 199417 = 149563) (by norm_num)
theorem B264965 : Blo 175800 264965 := bbase (se 4 (by rfl) ⟨24840, by rfl⟩ : syracuseStep 264965 = 49681) (by norm_num)
theorem B396053 : Blo 175800 396053 := bbase (se 6 (by rfl) ⟨9282, by rfl⟩ : syracuseStep 396053 = 18565) (by norm_num)
theorem B297749 : Blo 175800 297749 := bbase (se 6 (by rfl) ⟨6978, by rfl⟩ : syracuseStep 297749 = 13957) (by norm_num)
theorem B264989 : Blo 175800 264989 := bbase (se 3 (by rfl) ⟨49685, by rfl⟩ : syracuseStep 264989 = 99371) (by norm_num)
theorem B199453 : Blo 175800 199453 := bbase (se 3 (by rfl) ⟨37397, by rfl⟩ : syracuseStep 199453 = 74795) (by norm_num)
theorem B265013 : Blo 175800 265013 := bbase (se 5 (by rfl) ⟨12422, by rfl⟩ : syracuseStep 265013 = 24845) (by norm_num)
theorem B199489 : Blo 175800 199489 := bbase (se 2 (by rfl) ⟨74808, by rfl⟩ : syracuseStep 199489 = 149617) (by norm_num)
theorem B265037 : Blo 175800 265037 := bbase (se 3 (by rfl) ⟨49694, by rfl⟩ : syracuseStep 265037 = 99389) (by norm_num)
theorem B396125 : Blo 175800 396125 := bbase (se 3 (by rfl) ⟨74273, by rfl⟩ : syracuseStep 396125 = 148547) (by norm_num)
theorem B265061 : Blo 175800 265061 := bbase (se 4 (by rfl) ⟨24849, by rfl⟩ : syracuseStep 265061 = 49699) (by norm_num)
theorem B199525 : Blo 175800 199525 := bbase (se 4 (by rfl) ⟨18705, by rfl⟩ : syracuseStep 199525 = 37411) (by norm_num)
theorem B265085 : Blo 175800 265085 := bbase (se 3 (by rfl) ⟨49703, by rfl⟩ : syracuseStep 265085 = 99407) (by norm_num)
theorem B199561 : Blo 175800 199561 := bbase (se 2 (by rfl) ⟨74835, by rfl⟩ : syracuseStep 199561 = 149671) (by norm_num)
theorem B297877 : Blo 175800 297877 := bbase (se 6 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 297877 = 13963) (by norm_num)
theorem B265109 : Blo 175800 265109 := bbase (se 6 (by rfl) ⟨6213, by rfl⟩ : syracuseStep 265109 = 12427) (by norm_num)
theorem B396197 : Blo 175800 396197 := bbase (se 4 (by rfl) ⟨37143, by rfl⟩ : syracuseStep 396197 = 74287) (by norm_num)
theorem B265133 : Blo 175800 265133 := bbase (se 3 (by rfl) ⟨49712, by rfl⟩ : syracuseStep 265133 = 99425) (by norm_num)
theorem B199597 : Blo 175800 199597 := bbase (se 3 (by rfl) ⟨37424, by rfl⟩ : syracuseStep 199597 = 74849) (by norm_num)
theorem B265157 : Blo 175800 265157 := bbase (se 4 (by rfl) ⟨24858, by rfl⟩ : syracuseStep 265157 = 49717) (by norm_num)
theorem B199633 : Blo 175800 199633 := bbase (se 2 (by rfl) ⟨74862, by rfl⟩ : syracuseStep 199633 = 149725) (by norm_num)
theorem B265181 : Blo 175800 265181 := bbase (se 3 (by rfl) ⟨49721, by rfl⟩ : syracuseStep 265181 = 99443) (by norm_num)
theorem B429029 : Blo 175800 429029 := bbase (se 4 (by rfl) ⟨40221, by rfl⟩ : syracuseStep 429029 = 80443) (by norm_num)
theorem B396269 : Blo 175800 396269 := bbase (se 3 (by rfl) ⟨74300, by rfl⟩ : syracuseStep 396269 = 148601) (by norm_num)
theorem B297965 : Blo 175800 297965 := bbase (se 3 (by rfl) ⟨55868, by rfl⟩ : syracuseStep 297965 = 111737) (by norm_num)
theorem B265205 : Blo 175800 265205 := bbase (se 5 (by rfl) ⟨12431, by rfl⟩ : syracuseStep 265205 = 24863) (by norm_num)
theorem B199669 : Blo 175800 199669 := bbase (se 5 (by rfl) ⟨9359, by rfl⟩ : syracuseStep 199669 = 18719) (by norm_num)
theorem B265229 : Blo 175800 265229 := bbase (se 3 (by rfl) ⟨49730, by rfl⟩ : syracuseStep 265229 = 99461) (by norm_num)
theorem B199705 : Blo 175800 199705 := bbase (se 2 (by rfl) ⟨74889, by rfl⟩ : syracuseStep 199705 = 149779) (by norm_num)
theorem B265253 : Blo 175800 265253 := bbase (se 4 (by rfl) ⟨24867, by rfl⟩ : syracuseStep 265253 = 49735) (by norm_num)
theorem B396341 : Blo 175800 396341 := bbase (se 5 (by rfl) ⟨18578, by rfl⟩ : syracuseStep 396341 = 37157) (by norm_num)
theorem B265277 : Blo 175800 265277 := bbase (se 3 (by rfl) ⟨49739, by rfl⟩ : syracuseStep 265277 = 99479) (by norm_num)
theorem B199741 : Blo 175800 199741 := bbase (se 3 (by rfl) ⟨37451, by rfl⟩ : syracuseStep 199741 = 74903) (by norm_num)
theorem B265301 : Blo 175800 265301 := bbase (se 8 (by rfl) ⟨1554, by rfl⟩ : syracuseStep 265301 = 3109) (by norm_num)
theorem B199777 : Blo 175800 199777 := bbase (se 2 (by rfl) ⟨74916, by rfl⟩ : syracuseStep 199777 = 149833) (by norm_num)
theorem B298093 : Blo 175800 298093 := bbase (se 3 (by rfl) ⟨55892, by rfl⟩ : syracuseStep 298093 = 111785) (by norm_num)
theorem B265325 : Blo 175800 265325 := bbase (se 3 (by rfl) ⟨49748, by rfl⟩ : syracuseStep 265325 = 99497) (by norm_num)
theorem B396413 : Blo 175800 396413 := bbase (se 3 (by rfl) ⟨74327, by rfl⟩ : syracuseStep 396413 = 148655) (by norm_num)
theorem B265349 : Blo 175800 265349 := bbase (se 4 (by rfl) ⟨24876, by rfl⟩ : syracuseStep 265349 = 49753) (by norm_num)
theorem B199813 : Blo 175800 199813 := bbase (se 4 (by rfl) ⟨18732, by rfl⟩ : syracuseStep 199813 = 37465) (by norm_num)
theorem B265373 : Blo 175800 265373 := bbase (se 3 (by rfl) ⟨49757, by rfl⟩ : syracuseStep 265373 = 99515) (by norm_num)
theorem B199849 : Blo 175800 199849 := bbase (se 2 (by rfl) ⟨74943, by rfl⟩ : syracuseStep 199849 = 149887) (by norm_num)
theorem B265397 : Blo 175800 265397 := bbase (se 5 (by rfl) ⟨12440, by rfl⟩ : syracuseStep 265397 = 24881) (by norm_num)
theorem B396485 : Blo 175800 396485 := bbase (se 4 (by rfl) ⟨37170, by rfl⟩ : syracuseStep 396485 = 74341) (by norm_num)
theorem B298181 : Blo 175800 298181 := bbase (se 4 (by rfl) ⟨27954, by rfl⟩ : syracuseStep 298181 = 55909) (by norm_num)
theorem B265421 : Blo 175800 265421 := bbase (se 3 (by rfl) ⟨49766, by rfl⟩ : syracuseStep 265421 = 99533) (by norm_num)
theorem B199885 : Blo 175800 199885 := bbase (se 3 (by rfl) ⟨37478, by rfl⟩ : syracuseStep 199885 = 74957) (by norm_num)
theorem B265445 : Blo 175800 265445 := bbase (se 4 (by rfl) ⟨24885, by rfl⟩ : syracuseStep 265445 = 49771) (by norm_num)
theorem B199921 : Blo 175800 199921 := bbase (se 2 (by rfl) ⟨74970, by rfl⟩ : syracuseStep 199921 = 149941) (by norm_num)
theorem B265469 : Blo 175800 265469 := bbase (se 3 (by rfl) ⟨49775, by rfl⟩ : syracuseStep 265469 = 99551) (by norm_num)
theorem B396557 : Blo 175800 396557 := bbase (se 3 (by rfl) ⟨74354, by rfl⟩ : syracuseStep 396557 = 148709) (by norm_num)
theorem B265493 : Blo 175800 265493 := bbase (se 6 (by rfl) ⟨6222, by rfl⟩ : syracuseStep 265493 = 12445) (by norm_num)
theorem B199957 : Blo 175800 199957 := bbase (se 6 (by rfl) ⟨4686, by rfl⟩ : syracuseStep 199957 = 9373) (by norm_num)
theorem B265517 : Blo 175800 265517 := bbase (se 3 (by rfl) ⟨49784, by rfl⟩ : syracuseStep 265517 = 99569) (by norm_num)
theorem B199993 : Blo 175800 199993 := bbase (se 2 (by rfl) ⟨74997, by rfl⟩ : syracuseStep 199993 = 149995) (by norm_num)
theorem B298309 : Blo 175800 298309 := bbase (se 4 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 298309 = 55933) (by norm_num)
theorem B265541 : Blo 175800 265541 := bbase (se 4 (by rfl) ⟨24894, by rfl⟩ : syracuseStep 265541 = 49789) (by norm_num)
theorem B396629 : Blo 175800 396629 := bbase (se 11 (by rfl) ⟨290, by rfl⟩ : syracuseStep 396629 = 581) (by norm_num)
theorem B265565 : Blo 175800 265565 := bbase (se 3 (by rfl) ⟨49793, by rfl⟩ : syracuseStep 265565 = 99587) (by norm_num)
theorem B200029 : Blo 175800 200029 := bbase (se 3 (by rfl) ⟨37505, by rfl⟩ : syracuseStep 200029 = 75011) (by norm_num)
theorem B265589 : Blo 175800 265589 := bbase (se 5 (by rfl) ⟨12449, by rfl⟩ : syracuseStep 265589 = 24899) (by norm_num)
theorem B200065 : Blo 175800 200065 := bbase (se 2 (by rfl) ⟨75024, by rfl⟩ : syracuseStep 200065 = 150049) (by norm_num)
theorem B265613 : Blo 175800 265613 := bbase (se 3 (by rfl) ⟨49802, by rfl⟩ : syracuseStep 265613 = 99605) (by norm_num)
theorem B396701 : Blo 175800 396701 := bbase (se 3 (by rfl) ⟨74381, by rfl⟩ : syracuseStep 396701 = 148763) (by norm_num)
theorem B298397 : Blo 175800 298397 := bbase (se 3 (by rfl) ⟨55949, by rfl⟩ : syracuseStep 298397 = 111899) (by norm_num)
theorem B265637 : Blo 175800 265637 := bbase (se 4 (by rfl) ⟨24903, by rfl⟩ : syracuseStep 265637 = 49807) (by norm_num)
theorem B200101 : Blo 175800 200101 := bbase (se 4 (by rfl) ⟨18759, by rfl⟩ : syracuseStep 200101 = 37519) (by norm_num)
theorem B265661 : Blo 175800 265661 := bbase (se 3 (by rfl) ⟨49811, by rfl⟩ : syracuseStep 265661 = 99623) (by norm_num)
theorem B200137 : Blo 175800 200137 := bbase (se 2 (by rfl) ⟨75051, by rfl⟩ : syracuseStep 200137 = 150103) (by norm_num)
theorem B265685 : Blo 175800 265685 := bbase (se 7 (by rfl) ⟨3113, by rfl⟩ : syracuseStep 265685 = 6227) (by norm_num)
theorem B396773 : Blo 175800 396773 := bbase (se 4 (by rfl) ⟨37197, by rfl⟩ : syracuseStep 396773 = 74395) (by norm_num)
theorem B265709 : Blo 175800 265709 := bbase (se 3 (by rfl) ⟨49820, by rfl⟩ : syracuseStep 265709 = 99641) (by norm_num)
theorem B200173 : Blo 175800 200173 := bbase (se 3 (by rfl) ⟨37532, by rfl⟩ : syracuseStep 200173 = 75065) (by norm_num)
theorem B265733 : Blo 175800 265733 := bbase (se 4 (by rfl) ⟨24912, by rfl⟩ : syracuseStep 265733 = 49825) (by norm_num)
theorem B200209 : Blo 175800 200209 := bbase (se 2 (by rfl) ⟨75078, by rfl⟩ : syracuseStep 200209 = 150157) (by norm_num)
theorem B298525 : Blo 175800 298525 := bbase (se 3 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 298525 = 111947) (by norm_num)
theorem B265757 : Blo 175800 265757 := bbase (se 3 (by rfl) ⟨49829, by rfl⟩ : syracuseStep 265757 = 99659) (by norm_num)
theorem B396845 : Blo 175800 396845 := bbase (se 3 (by rfl) ⟨74408, by rfl⟩ : syracuseStep 396845 = 148817) (by norm_num)
theorem B265781 : Blo 175800 265781 := bbase (se 5 (by rfl) ⟨12458, by rfl⟩ : syracuseStep 265781 = 24917) (by norm_num)
theorem B200245 : Blo 175800 200245 := bbase (se 5 (by rfl) ⟨9386, by rfl⟩ : syracuseStep 200245 = 18773) (by norm_num)
theorem B265805 : Blo 175800 265805 := bbase (se 3 (by rfl) ⟨49838, by rfl⟩ : syracuseStep 265805 = 99677) (by norm_num)
theorem B200281 : Blo 175800 200281 := bbase (se 2 (by rfl) ⟨75105, by rfl⟩ : syracuseStep 200281 = 150211) (by norm_num)
theorem B265829 : Blo 175800 265829 := bbase (se 4 (by rfl) ⟨24921, by rfl⟩ : syracuseStep 265829 = 49843) (by norm_num)
theorem B396917 : Blo 175800 396917 := bbase (se 5 (by rfl) ⟨18605, by rfl⟩ : syracuseStep 396917 = 37211) (by norm_num)
theorem B298613 : Blo 175800 298613 := bbase (se 5 (by rfl) ⟨13997, by rfl⟩ : syracuseStep 298613 = 27995) (by norm_num)
theorem B265853 : Blo 175800 265853 := bbase (se 3 (by rfl) ⟨49847, by rfl⟩ : syracuseStep 265853 = 99695) (by norm_num)
theorem B200317 : Blo 175800 200317 := bbase (se 3 (by rfl) ⟨37559, by rfl⟩ : syracuseStep 200317 = 75119) (by norm_num)
theorem B265877 : Blo 175800 265877 := bbase (se 6 (by rfl) ⟨6231, by rfl⟩ : syracuseStep 265877 = 12463) (by norm_num)
theorem B200353 : Blo 175800 200353 := bbase (se 2 (by rfl) ⟨75132, by rfl⟩ : syracuseStep 200353 = 150265) (by norm_num)
theorem B265901 : Blo 175800 265901 := bbase (se 3 (by rfl) ⟨49856, by rfl⟩ : syracuseStep 265901 = 99713) (by norm_num)
theorem B396989 : Blo 175800 396989 := bbase (se 3 (by rfl) ⟨74435, by rfl⟩ : syracuseStep 396989 = 148871) (by norm_num)
theorem B265925 : Blo 175800 265925 := bbase (se 4 (by rfl) ⟨24930, by rfl⟩ : syracuseStep 265925 = 49861) (by norm_num)
theorem B200389 : Blo 175800 200389 := bbase (se 4 (by rfl) ⟨18786, by rfl⟩ : syracuseStep 200389 = 37573) (by norm_num)
theorem B593621 : Blo 175800 593621 := bbase (se 7 (by rfl) ⟨6956, by rfl⟩ : syracuseStep 593621 = 13913) (by norm_num)
theorem B265949 : Blo 175800 265949 := bbase (se 3 (by rfl) ⟨49865, by rfl⟩ : syracuseStep 265949 = 99731) (by norm_num)
theorem B429797 : Blo 175800 429797 := bbase (se 4 (by rfl) ⟨40293, by rfl⟩ : syracuseStep 429797 = 80587) (by norm_num)
theorem B200425 : Blo 175800 200425 := bbase (se 2 (by rfl) ⟨75159, by rfl⟩ : syracuseStep 200425 = 150319) (by norm_num)
theorem B298741 : Blo 175800 298741 := bbase (se 5 (by rfl) ⟨14003, by rfl⟩ : syracuseStep 298741 = 28007) (by norm_num)
theorem B265973 : Blo 175800 265973 := bbase (se 5 (by rfl) ⟨12467, by rfl⟩ : syracuseStep 265973 = 24935) (by norm_num)
theorem B397061 : Blo 175800 397061 := bbase (se 4 (by rfl) ⟨37224, by rfl⟩ : syracuseStep 397061 = 74449) (by norm_num)
theorem B265997 : Blo 175800 265997 := bbase (se 3 (by rfl) ⟨49874, by rfl⟩ : syracuseStep 265997 = 99749) (by norm_num)
theorem B200461 : Blo 175800 200461 := bbase (se 3 (by rfl) ⟨37586, by rfl⟩ : syracuseStep 200461 = 75173) (by norm_num)
theorem B266021 : Blo 175800 266021 := bbase (se 4 (by rfl) ⟨24939, by rfl⟩ : syracuseStep 266021 = 49879) (by norm_num)
theorem B200497 : Blo 175800 200497 := bbase (se 2 (by rfl) ⟨75186, by rfl⟩ : syracuseStep 200497 = 150373) (by norm_num)
theorem B266045 : Blo 175800 266045 := bbase (se 3 (by rfl) ⟨49883, by rfl⟩ : syracuseStep 266045 = 99767) (by norm_num)
theorem B397133 : Blo 175800 397133 := bbase (se 3 (by rfl) ⟨74462, by rfl⟩ : syracuseStep 397133 = 148925) (by norm_num)
theorem B298829 : Blo 175800 298829 := bbase (se 3 (by rfl) ⟨56030, by rfl⟩ : syracuseStep 298829 = 112061) (by norm_num)
theorem B266069 : Blo 175800 266069 := bbase (se 9 (by rfl) ⟨779, by rfl⟩ : syracuseStep 266069 = 1559) (by norm_num)
theorem B200533 : Blo 175800 200533 := bbase (se 9 (by rfl) ⟨587, by rfl⟩ : syracuseStep 200533 = 1175) (by norm_num)
theorem B266093 : Blo 175800 266093 := bbase (se 3 (by rfl) ⟨49892, by rfl⟩ : syracuseStep 266093 = 99785) (by norm_num)
theorem B200569 : Blo 175800 200569 := bbase (se 2 (by rfl) ⟨75213, by rfl⟩ : syracuseStep 200569 = 150427) (by norm_num)
theorem B266117 : Blo 175800 266117 := bbase (se 4 (by rfl) ⟨24948, by rfl⟩ : syracuseStep 266117 = 49897) (by norm_num)
theorem B397205 : Blo 175800 397205 := bbase (se 6 (by rfl) ⟨9309, by rfl⟩ : syracuseStep 397205 = 18619) (by norm_num)
theorem B266141 : Blo 175800 266141 := bbase (se 3 (by rfl) ⟨49901, by rfl⟩ : syracuseStep 266141 = 99803) (by norm_num)
theorem B200605 : Blo 175800 200605 := bbase (se 3 (by rfl) ⟨37613, by rfl⟩ : syracuseStep 200605 = 75227) (by norm_num)
theorem B266165 : Blo 175800 266165 := bbase (se 5 (by rfl) ⟨12476, by rfl⟩ : syracuseStep 266165 = 24953) (by norm_num)
theorem B200641 : Blo 175800 200641 := bbase (se 2 (by rfl) ⟨75240, by rfl⟩ : syracuseStep 200641 = 150481) (by norm_num)
theorem B298957 : Blo 175800 298957 := bbase (se 3 (by rfl) ⟨56054, by rfl⟩ : syracuseStep 298957 = 112109) (by norm_num)
theorem B266189 : Blo 175800 266189 := bbase (se 3 (by rfl) ⟨49910, by rfl⟩ : syracuseStep 266189 = 99821) (by norm_num)
theorem B397277 : Blo 175800 397277 := bbase (se 3 (by rfl) ⟨74489, by rfl⟩ : syracuseStep 397277 = 148979) (by norm_num)
theorem B266213 : Blo 175800 266213 := bbase (se 4 (by rfl) ⟨24957, by rfl⟩ : syracuseStep 266213 = 49915) (by norm_num)
theorem B200677 : Blo 175800 200677 := bbase (se 4 (by rfl) ⟨18813, by rfl⟩ : syracuseStep 200677 = 37627) (by norm_num)
theorem B266237 : Blo 175800 266237 := bbase (se 3 (by rfl) ⟨49919, by rfl⟩ : syracuseStep 266237 = 99839) (by norm_num)
theorem B200713 : Blo 175800 200713 := bbase (se 2 (by rfl) ⟨75267, by rfl⟩ : syracuseStep 200713 = 150535) (by norm_num)
theorem B757781 : Blo 175800 757781 := bbase (se 6 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 757781 = 35521) (by norm_num)
theorem B266261 : Blo 175800 266261 := bbase (se 6 (by rfl) ⟨6240, by rfl⟩ : syracuseStep 266261 = 12481) (by norm_num)
theorem B397349 : Blo 175800 397349 := bbase (se 4 (by rfl) ⟨37251, by rfl⟩ : syracuseStep 397349 = 74503) (by norm_num)
theorem B299045 : Blo 175800 299045 := bbase (se 4 (by rfl) ⟨28035, by rfl⟩ : syracuseStep 299045 = 56071) (by norm_num)
theorem B266285 : Blo 175800 266285 := bbase (se 3 (by rfl) ⟨49928, by rfl⟩ : syracuseStep 266285 = 99857) (by norm_num)
theorem B200749 : Blo 175800 200749 := bbase (se 3 (by rfl) ⟨37640, by rfl⟩ : syracuseStep 200749 = 75281) (by norm_num)
theorem B266309 : Blo 175800 266309 := bbase (se 4 (by rfl) ⟨24966, by rfl⟩ : syracuseStep 266309 = 49933) (by norm_num)
theorem B200785 : Blo 175800 200785 := bbase (se 2 (by rfl) ⟨75294, by rfl⟩ : syracuseStep 200785 = 150589) (by norm_num)
theorem B266333 : Blo 175800 266333 := bbase (se 3 (by rfl) ⟨49937, by rfl⟩ : syracuseStep 266333 = 99875) (by norm_num)
theorem B397421 : Blo 175800 397421 := bbase (se 3 (by rfl) ⟨74516, by rfl⟩ : syracuseStep 397421 = 149033) (by norm_num)
theorem B266357 : Blo 175800 266357 := bbase (se 5 (by rfl) ⟨12485, by rfl⟩ : syracuseStep 266357 = 24971) (by norm_num)
theorem B200821 : Blo 175800 200821 := bbase (se 5 (by rfl) ⟨9413, by rfl⟩ : syracuseStep 200821 = 18827) (by norm_num)
theorem B594053 : Blo 175800 594053 := bbase (se 4 (by rfl) ⟨55692, by rfl⟩ : syracuseStep 594053 = 111385) (by norm_num)
theorem B266381 : Blo 175800 266381 := bbase (se 3 (by rfl) ⟨49946, by rfl⟩ : syracuseStep 266381 = 99893) (by norm_num)
theorem B1020053 : Blo 175800 1020053 := bbase (se 6 (by rfl) ⟨23907, by rfl⟩ : syracuseStep 1020053 = 47815) (by norm_num)
theorem B200857 : Blo 175800 200857 := bbase (se 2 (by rfl) ⟨75321, by rfl⟩ : syracuseStep 200857 = 150643) (by norm_num)
theorem B299173 : Blo 175800 299173 := bbase (se 4 (by rfl) ⟨28047, by rfl⟩ : syracuseStep 299173 = 56095) (by norm_num)
theorem B266405 : Blo 175800 266405 := bbase (se 4 (by rfl) ⟨24975, by rfl⟩ : syracuseStep 266405 = 49951) (by norm_num)
theorem B200885 : Blo 175800 200885 := bbase (se 5 (by rfl) ⟨9416, by rfl⟩ : syracuseStep 200885 = 18833) (by norm_num)
theorem B397493 : Blo 175800 397493 := bbase (se 5 (by rfl) ⟨18632, by rfl⟩ : syracuseStep 397493 = 37265) (by norm_num)
theorem B266429 : Blo 175800 266429 := bbase (se 3 (by rfl) ⟨49955, by rfl⟩ : syracuseStep 266429 = 99911) (by norm_num)
theorem B200893 : Blo 175800 200893 := bbase (se 3 (by rfl) ⟨37667, by rfl⟩ : syracuseStep 200893 = 75335) (by norm_num)
theorem B266453 : Blo 175800 266453 := bbase (se 7 (by rfl) ⟨3122, by rfl⟩ : syracuseStep 266453 = 6245) (by norm_num)
theorem B200929 : Blo 175800 200929 := bbase (se 2 (by rfl) ⟨75348, by rfl⟩ : syracuseStep 200929 = 150697) (by norm_num)
theorem B266477 : Blo 175800 266477 := bbase (se 3 (by rfl) ⟨49964, by rfl⟩ : syracuseStep 266477 = 99929) (by norm_num)
theorem B397565 : Blo 175800 397565 := bbase (se 3 (by rfl) ⟨74543, by rfl⟩ : syracuseStep 397565 = 149087) (by norm_num)
theorem B299261 : Blo 175800 299261 := bbase (se 3 (by rfl) ⟨56111, by rfl⟩ : syracuseStep 299261 = 112223) (by norm_num)
theorem B266501 : Blo 175800 266501 := bbase (se 4 (by rfl) ⟨24984, by rfl⟩ : syracuseStep 266501 = 49969) (by norm_num)
theorem B200965 : Blo 175800 200965 := bbase (se 4 (by rfl) ⟨18840, by rfl⟩ : syracuseStep 200965 = 37681) (by norm_num)
theorem B266525 : Blo 175800 266525 := bbase (se 3 (by rfl) ⟨49973, by rfl⟩ : syracuseStep 266525 = 99947) (by norm_num)
theorem B201001 : Blo 175800 201001 := bbase (se 2 (by rfl) ⟨75375, by rfl⟩ : syracuseStep 201001 = 150751) (by norm_num)
theorem B758069 : Blo 175800 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B266549 : Blo 175800 266549 := bbase (se 5 (by rfl) ⟨12494, by rfl⟩ : syracuseStep 266549 = 24989) (by norm_num)
theorem B397637 : Blo 175800 397637 := bbase (se 4 (by rfl) ⟨37278, by rfl⟩ : syracuseStep 397637 = 74557) (by norm_num)
theorem B266573 : Blo 175800 266573 := bbase (se 3 (by rfl) ⟨49982, by rfl⟩ : syracuseStep 266573 = 99965) (by norm_num)
theorem B201037 : Blo 175800 201037 := bbase (se 3 (by rfl) ⟨37694, by rfl⟩ : syracuseStep 201037 = 75389) (by norm_num)
theorem B266597 : Blo 175800 266597 := bbase (se 4 (by rfl) ⟨24993, by rfl⟩ : syracuseStep 266597 = 49987) (by norm_num)
theorem B201073 : Blo 175800 201073 := bbase (se 2 (by rfl) ⟨75402, by rfl⟩ : syracuseStep 201073 = 150805) (by norm_num)
theorem B299389 : Blo 175800 299389 := bbase (se 3 (by rfl) ⟨56135, by rfl⟩ : syracuseStep 299389 = 112271) (by norm_num)
theorem B266621 : Blo 175800 266621 := bbase (se 3 (by rfl) ⟨49991, by rfl⟩ : syracuseStep 266621 = 99983) (by norm_num)
theorem B397709 : Blo 175800 397709 := bbase (se 3 (by rfl) ⟨74570, by rfl⟩ : syracuseStep 397709 = 149141) (by norm_num)
theorem B266645 : Blo 175800 266645 := bbase (se 6 (by rfl) ⟨6249, by rfl⟩ : syracuseStep 266645 = 12499) (by norm_num)
theorem B201109 : Blo 175800 201109 := bbase (se 6 (by rfl) ⟨4713, by rfl⟩ : syracuseStep 201109 = 9427) (by norm_num)
theorem B266669 : Blo 175800 266669 := bbase (se 3 (by rfl) ⟨50000, by rfl⟩ : syracuseStep 266669 = 100001) (by norm_num)
theorem B201145 : Blo 175800 201145 := bbase (se 2 (by rfl) ⟨75429, by rfl⟩ : syracuseStep 201145 = 150859) (by norm_num)
theorem B266693 : Blo 175800 266693 := bbase (se 4 (by rfl) ⟨25002, by rfl⟩ : syracuseStep 266693 = 50005) (by norm_num)
theorem B397781 : Blo 175800 397781 := bbase (se 7 (by rfl) ⟨4661, by rfl⟩ : syracuseStep 397781 = 9323) (by norm_num)
theorem B299477 : Blo 175800 299477 := bbase (se 7 (by rfl) ⟨3509, by rfl⟩ : syracuseStep 299477 = 7019) (by norm_num)
theorem B266717 : Blo 175800 266717 := bbase (se 3 (by rfl) ⟨50009, by rfl⟩ : syracuseStep 266717 = 100019) (by norm_num)
theorem B201181 : Blo 175800 201181 := bbase (se 3 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 201181 = 75443) (by norm_num)
theorem B266741 : Blo 175800 266741 := bbase (se 5 (by rfl) ⟨12503, by rfl⟩ : syracuseStep 266741 = 25007) (by norm_num)
theorem B201217 : Blo 175800 201217 := bbase (se 2 (by rfl) ⟨75456, by rfl⟩ : syracuseStep 201217 = 150913) (by norm_num)
theorem B266765 : Blo 175800 266765 := bbase (se 3 (by rfl) ⟨50018, by rfl⟩ : syracuseStep 266765 = 100037) (by norm_num)
theorem B397853 : Blo 175800 397853 := bbase (se 3 (by rfl) ⟨74597, by rfl⟩ : syracuseStep 397853 = 149195) (by norm_num)
theorem B266789 : Blo 175800 266789 := bbase (se 4 (by rfl) ⟨25011, by rfl⟩ : syracuseStep 266789 = 50023) (by norm_num)
theorem B201253 : Blo 175800 201253 := bbase (se 4 (by rfl) ⟨18867, by rfl⟩ : syracuseStep 201253 = 37735) (by norm_num)
theorem B594485 : Blo 175800 594485 := bbase (se 5 (by rfl) ⟨27866, by rfl⟩ : syracuseStep 594485 = 55733) (by norm_num)
theorem B266813 : Blo 175800 266813 := bbase (se 3 (by rfl) ⟨50027, by rfl⟩ : syracuseStep 266813 = 100055) (by norm_num)
theorem B201289 : Blo 175800 201289 := bbase (se 2 (by rfl) ⟨75483, by rfl⟩ : syracuseStep 201289 = 150967) (by norm_num)
theorem B299605 : Blo 175800 299605 := bbase (se 8 (by rfl) ⟨1755, by rfl⟩ : syracuseStep 299605 = 3511) (by norm_num)
theorem B266837 : Blo 175800 266837 := bbase (se 8 (by rfl) ⟨1563, by rfl⟩ : syracuseStep 266837 = 3127) (by norm_num)
theorem B397925 : Blo 175800 397925 := bbase (se 4 (by rfl) ⟨37305, by rfl⟩ : syracuseStep 397925 = 74611) (by norm_num)
theorem B266861 : Blo 175800 266861 := bbase (se 3 (by rfl) ⟨50036, by rfl⟩ : syracuseStep 266861 = 100073) (by norm_num)
theorem B201325 : Blo 175800 201325 := bbase (se 3 (by rfl) ⟨37748, by rfl⟩ : syracuseStep 201325 = 75497) (by norm_num)
theorem B266885 : Blo 175800 266885 := bbase (se 4 (by rfl) ⟨25020, by rfl⟩ : syracuseStep 266885 = 50041) (by norm_num)
theorem B201361 : Blo 175800 201361 := bbase (se 2 (by rfl) ⟨75510, by rfl⟩ : syracuseStep 201361 = 151021) (by norm_num)
theorem B266909 : Blo 175800 266909 := bbase (se 3 (by rfl) ⟨50045, by rfl⟩ : syracuseStep 266909 = 100091) (by norm_num)
theorem B397997 : Blo 175800 397997 := bbase (se 3 (by rfl) ⟨74624, by rfl⟩ : syracuseStep 397997 = 149249) (by norm_num)
theorem B299693 : Blo 175800 299693 := bbase (se 3 (by rfl) ⟨56192, by rfl⟩ : syracuseStep 299693 = 112385) (by norm_num)
theorem B266933 : Blo 175800 266933 := bbase (se 5 (by rfl) ⟨12512, by rfl⟩ : syracuseStep 266933 = 25025) (by norm_num)
theorem B201397 : Blo 175800 201397 := bbase (se 5 (by rfl) ⟨9440, by rfl⟩ : syracuseStep 201397 = 18881) (by norm_num)
theorem B266957 : Blo 175800 266957 := bbase (se 3 (by rfl) ⟨50054, by rfl⟩ : syracuseStep 266957 = 100109) (by norm_num)
theorem B201433 : Blo 175800 201433 := bbase (se 2 (by rfl) ⟨75537, by rfl⟩ : syracuseStep 201433 = 151075) (by norm_num)
theorem B266981 : Blo 175800 266981 := bbase (se 4 (by rfl) ⟨25029, by rfl⟩ : syracuseStep 266981 = 50059) (by norm_num)
theorem B398069 : Blo 175800 398069 := bbase (se 5 (by rfl) ⟨18659, by rfl⟩ : syracuseStep 398069 = 37319) (by norm_num)
theorem B267005 : Blo 175800 267005 := bbase (se 3 (by rfl) ⟨50063, by rfl⟩ : syracuseStep 267005 = 100127) (by norm_num)
theorem B201469 : Blo 175800 201469 := bbase (se 3 (by rfl) ⟨37775, by rfl⟩ : syracuseStep 201469 = 75551) (by norm_num)
theorem B267029 : Blo 175800 267029 := bbase (se 6 (by rfl) ⟨6258, by rfl⟩ : syracuseStep 267029 = 12517) (by norm_num)
theorem B1151765 : Blo 175800 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B201505 : Blo 175800 201505 := bbase (se 2 (by rfl) ⟨75564, by rfl⟩ : syracuseStep 201505 = 151129) (by norm_num)
theorem B299821 : Blo 175800 299821 := bbase (se 3 (by rfl) ⟨56216, by rfl⟩ : syracuseStep 299821 = 112433) (by norm_num)
theorem B267053 : Blo 175800 267053 := bbase (se 3 (by rfl) ⟨50072, by rfl⟩ : syracuseStep 267053 = 100145) (by norm_num)
theorem B398141 : Blo 175800 398141 := bbase (se 3 (by rfl) ⟨74651, by rfl⟩ : syracuseStep 398141 = 149303) (by norm_num)
theorem B267077 : Blo 175800 267077 := bbase (se 4 (by rfl) ⟨25038, by rfl⟩ : syracuseStep 267077 = 50077) (by norm_num)
theorem B201541 : Blo 175800 201541 := bbase (se 4 (by rfl) ⟨18894, by rfl⟩ : syracuseStep 201541 = 37789) (by norm_num)
theorem B267101 : Blo 175800 267101 := bbase (se 3 (by rfl) ⟨50081, by rfl⟩ : syracuseStep 267101 = 100163) (by norm_num)
theorem B201577 : Blo 175800 201577 := bbase (se 2 (by rfl) ⟨75591, by rfl⟩ : syracuseStep 201577 = 151183) (by norm_num)
theorem B267125 : Blo 175800 267125 := bbase (se 5 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 267125 = 25043) (by norm_num)
theorem B398213 : Blo 175800 398213 := bbase (se 4 (by rfl) ⟨37332, by rfl⟩ : syracuseStep 398213 = 74665) (by norm_num)
theorem B299909 : Blo 175800 299909 := bbase (se 4 (by rfl) ⟨28116, by rfl⟩ : syracuseStep 299909 = 56233) (by norm_num)
theorem B267149 : Blo 175800 267149 := bbase (se 3 (by rfl) ⟨50090, by rfl⟩ : syracuseStep 267149 = 100181) (by norm_num)
theorem B201613 : Blo 175800 201613 := bbase (se 3 (by rfl) ⟨37802, by rfl⟩ : syracuseStep 201613 = 75605) (by norm_num)
theorem B267173 : Blo 175800 267173 := bbase (se 4 (by rfl) ⟨25047, by rfl⟩ : syracuseStep 267173 = 50095) (by norm_num)
theorem B201649 : Blo 175800 201649 := bbase (se 2 (by rfl) ⟨75618, by rfl⟩ : syracuseStep 201649 = 151237) (by norm_num)
theorem B267197 : Blo 175800 267197 := bbase (se 3 (by rfl) ⟨50099, by rfl⟩ : syracuseStep 267197 = 100199) (by norm_num)
theorem B398285 : Blo 175800 398285 := bbase (se 3 (by rfl) ⟨74678, by rfl⟩ : syracuseStep 398285 = 149357) (by norm_num)
theorem B267221 : Blo 175800 267221 := bbase (se 7 (by rfl) ⟨3131, by rfl⟩ : syracuseStep 267221 = 6263) (by norm_num)
theorem B201685 : Blo 175800 201685 := bbase (se 7 (by rfl) ⟨2363, by rfl⟩ : syracuseStep 201685 = 4727) (by norm_num)
theorem B594917 : Blo 175800 594917 := bbase (se 4 (by rfl) ⟨55773, by rfl⟩ : syracuseStep 594917 = 111547) (by norm_num)
theorem B267245 : Blo 175800 267245 := bbase (se 3 (by rfl) ⟨50108, by rfl⟩ : syracuseStep 267245 = 100217) (by norm_num)
theorem B201721 : Blo 175800 201721 := bbase (se 2 (by rfl) ⟨75645, by rfl⟩ : syracuseStep 201721 = 151291) (by norm_num)
theorem B300037 : Blo 175800 300037 := bbase (se 4 (by rfl) ⟨28128, by rfl⟩ : syracuseStep 300037 = 56257) (by norm_num)
theorem B267269 : Blo 175800 267269 := bbase (se 4 (by rfl) ⟨25056, by rfl⟩ : syracuseStep 267269 = 50113) (by norm_num)
theorem B398357 : Blo 175800 398357 := bbase (se 6 (by rfl) ⟨9336, by rfl⟩ : syracuseStep 398357 = 18673) (by norm_num)
theorem B267293 : Blo 175800 267293 := bbase (se 3 (by rfl) ⟨50117, by rfl⟩ : syracuseStep 267293 = 100235) (by norm_num)
theorem B201757 : Blo 175800 201757 := bbase (se 3 (by rfl) ⟨37829, by rfl⟩ : syracuseStep 201757 = 75659) (by norm_num)
theorem B758821 : Blo 175800 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B267317 : Blo 175800 267317 := bbase (se 5 (by rfl) ⟨12530, by rfl⟩ : syracuseStep 267317 = 25061) (by norm_num)
theorem B201793 : Blo 175800 201793 := bbase (se 2 (by rfl) ⟨75672, by rfl⟩ : syracuseStep 201793 = 151345) (by norm_num)
theorem B431173 : Blo 175800 431173 := bbase (se 4 (by rfl) ⟨40422, by rfl⟩ : syracuseStep 431173 = 80845) (by norm_num)
theorem B267341 : Blo 175800 267341 := bbase (se 3 (by rfl) ⟨50126, by rfl⟩ : syracuseStep 267341 = 100253) (by norm_num)
theorem B398429 : Blo 175800 398429 := bbase (se 3 (by rfl) ⟨74705, by rfl⟩ : syracuseStep 398429 = 149411) (by norm_num)
theorem B300125 : Blo 175800 300125 := bbase (se 3 (by rfl) ⟨56273, by rfl⟩ : syracuseStep 300125 = 112547) (by norm_num)
theorem B267365 : Blo 175800 267365 := bbase (se 4 (by rfl) ⟨25065, by rfl⟩ : syracuseStep 267365 = 50131) (by norm_num)
theorem B201829 : Blo 175800 201829 := bbase (se 4 (by rfl) ⟨18921, by rfl⟩ : syracuseStep 201829 = 37843) (by norm_num)
theorem B267389 : Blo 175800 267389 := bbase (se 3 (by rfl) ⟨50135, by rfl⟩ : syracuseStep 267389 = 100271) (by norm_num)
theorem B201865 : Blo 175800 201865 := bbase (se 2 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 201865 = 151399) (by norm_num)
theorem B267413 : Blo 175800 267413 := bbase (se 6 (by rfl) ⟨6267, by rfl⟩ : syracuseStep 267413 = 12535) (by norm_num)
theorem B398501 : Blo 175800 398501 := bbase (se 4 (by rfl) ⟨37359, by rfl⟩ : syracuseStep 398501 = 74719) (by norm_num)
theorem B267437 : Blo 175800 267437 := bbase (se 3 (by rfl) ⟨50144, by rfl⟩ : syracuseStep 267437 = 100289) (by norm_num)
theorem B201901 : Blo 175800 201901 := bbase (se 3 (by rfl) ⟨37856, by rfl⟩ : syracuseStep 201901 = 75713) (by norm_num)
theorem B267461 : Blo 175800 267461 := bbase (se 4 (by rfl) ⟨25074, by rfl⟩ : syracuseStep 267461 = 50149) (by norm_num)
theorem B201937 : Blo 175800 201937 := bbase (se 2 (by rfl) ⟨75726, by rfl⟩ : syracuseStep 201937 = 151453) (by norm_num)
theorem B300253 : Blo 175800 300253 := bbase (se 3 (by rfl) ⟨56297, by rfl⟩ : syracuseStep 300253 = 112595) (by norm_num)
theorem B267485 : Blo 175800 267485 := bbase (se 3 (by rfl) ⟨50153, by rfl⟩ : syracuseStep 267485 = 100307) (by norm_num)
theorem B398573 : Blo 175800 398573 := bbase (se 3 (by rfl) ⟨74732, by rfl⟩ : syracuseStep 398573 = 149465) (by norm_num)
theorem B267509 : Blo 175800 267509 := bbase (se 5 (by rfl) ⟨12539, by rfl⟩ : syracuseStep 267509 = 25079) (by norm_num)
theorem B201973 : Blo 175800 201973 := bbase (se 5 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 201973 = 18935) (by norm_num)
theorem B267533 : Blo 175800 267533 := bbase (se 3 (by rfl) ⟨50162, by rfl⟩ : syracuseStep 267533 = 100325) (by norm_num)
theorem B202009 : Blo 175800 202009 := bbase (se 2 (by rfl) ⟨75753, by rfl⟩ : syracuseStep 202009 = 151507) (by norm_num)
theorem B267557 : Blo 175800 267557 := bbase (se 4 (by rfl) ⟨25083, by rfl⟩ : syracuseStep 267557 = 50167) (by norm_num)
theorem B398645 : Blo 175800 398645 := bbase (se 5 (by rfl) ⟨18686, by rfl⟩ : syracuseStep 398645 = 37373) (by norm_num)
theorem B300341 : Blo 175800 300341 := bbase (se 5 (by rfl) ⟨14078, by rfl⟩ : syracuseStep 300341 = 28157) (by norm_num)
theorem B267581 : Blo 175800 267581 := bbase (se 3 (by rfl) ⟨50171, by rfl⟩ : syracuseStep 267581 = 100343) (by norm_num)
theorem B202045 : Blo 175800 202045 := bbase (se 3 (by rfl) ⟨37883, by rfl⟩ : syracuseStep 202045 = 75767) (by norm_num)
theorem B267605 : Blo 175800 267605 := bbase (se 14 (by rfl) ⟨24, by rfl⟩ : syracuseStep 267605 = 49) (by norm_num)
theorem B202081 : Blo 175800 202081 := bbase (se 2 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 202081 = 151561) (by norm_num)
theorem B267629 : Blo 175800 267629 := bbase (se 3 (by rfl) ⟨50180, by rfl⟩ : syracuseStep 267629 = 100361) (by norm_num)
theorem B398717 : Blo 175800 398717 := bbase (se 3 (by rfl) ⟨74759, by rfl⟩ : syracuseStep 398717 = 149519) (by norm_num)
theorem B267653 : Blo 175800 267653 := bbase (se 4 (by rfl) ⟨25092, by rfl⟩ : syracuseStep 267653 = 50185) (by norm_num)
theorem B202117 : Blo 175800 202117 := bbase (se 4 (by rfl) ⟨18948, by rfl⟩ : syracuseStep 202117 = 37897) (by norm_num)
theorem B595349 : Blo 175800 595349 := bbase (se 6 (by rfl) ⟨13953, by rfl⟩ : syracuseStep 595349 = 27907) (by norm_num)
theorem B267677 : Blo 175800 267677 := bbase (se 3 (by rfl) ⟨50189, by rfl⟩ : syracuseStep 267677 = 100379) (by norm_num)
theorem B202153 : Blo 175800 202153 := bbase (se 2 (by rfl) ⟨75807, by rfl⟩ : syracuseStep 202153 = 151615) (by norm_num)
theorem B300469 : Blo 175800 300469 := bbase (se 5 (by rfl) ⟨14084, by rfl⟩ : syracuseStep 300469 = 28169) (by norm_num)
theorem B267701 : Blo 175800 267701 := bbase (se 5 (by rfl) ⟨12548, by rfl⟩ : syracuseStep 267701 = 25097) (by norm_num)
theorem B398789 : Blo 175800 398789 := bbase (se 4 (by rfl) ⟨37386, by rfl⟩ : syracuseStep 398789 = 74773) (by norm_num)
theorem B267725 : Blo 175800 267725 := bbase (se 3 (by rfl) ⟨50198, by rfl⟩ : syracuseStep 267725 = 100397) (by norm_num)
theorem B202189 : Blo 175800 202189 := bbase (se 3 (by rfl) ⟨37910, by rfl⟩ : syracuseStep 202189 = 75821) (by norm_num)
theorem B267749 : Blo 175800 267749 := bbase (se 4 (by rfl) ⟨25101, by rfl⟩ : syracuseStep 267749 = 50203) (by norm_num)
theorem B202225 : Blo 175800 202225 := bbase (se 2 (by rfl) ⟨75834, by rfl⟩ : syracuseStep 202225 = 151669) (by norm_num)
theorem B267773 : Blo 175800 267773 := bbase (se 3 (by rfl) ⟨50207, by rfl⟩ : syracuseStep 267773 = 100415) (by norm_num)
theorem B398861 : Blo 175800 398861 := bbase (se 3 (by rfl) ⟨74786, by rfl⟩ : syracuseStep 398861 = 149573) (by norm_num)
theorem B300557 : Blo 175800 300557 := bbase (se 3 (by rfl) ⟨56354, by rfl⟩ : syracuseStep 300557 = 112709) (by norm_num)
theorem B267797 : Blo 175800 267797 := bbase (se 6 (by rfl) ⟨6276, by rfl⟩ : syracuseStep 267797 = 12553) (by norm_num)
theorem B202261 : Blo 175800 202261 := bbase (se 6 (by rfl) ⟨4740, by rfl⟩ : syracuseStep 202261 = 9481) (by norm_num)
theorem B267821 : Blo 175800 267821 := bbase (se 3 (by rfl) ⟨50216, by rfl⟩ : syracuseStep 267821 = 100433) (by norm_num)
theorem B267845 : Blo 175800 267845 := bbase (se 4 (by rfl) ⟨25110, by rfl⟩ : syracuseStep 267845 = 50221) (by norm_num)
theorem B398933 : Blo 175800 398933 := bbase (se 8 (by rfl) ⟨2337, by rfl⟩ : syracuseStep 398933 = 4675) (by norm_num)
theorem B267869 : Blo 175800 267869 := bbase (se 3 (by rfl) ⟨50225, by rfl⟩ : syracuseStep 267869 = 100451) (by norm_num)
theorem B267893 : Blo 175800 267893 := bbase (se 5 (by rfl) ⟨12557, by rfl⟩ : syracuseStep 267893 = 25115) (by norm_num)
theorem B300685 : Blo 175800 300685 := bbase (se 3 (by rfl) ⟨56378, by rfl⟩ : syracuseStep 300685 = 112757) (by norm_num)
theorem B267917 : Blo 175800 267917 := bbase (se 3 (by rfl) ⟨50234, by rfl⟩ : syracuseStep 267917 = 100469) (by norm_num)
theorem B857749 : Blo 175800 857749 := bbase (se 6 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 857749 = 40207) (by norm_num)
theorem B399005 : Blo 175800 399005 := bbase (se 3 (by rfl) ⟨74813, by rfl⟩ : syracuseStep 399005 = 149627) (by norm_num)
theorem B267941 : Blo 175800 267941 := bbase (se 4 (by rfl) ⟨25119, by rfl⟩ : syracuseStep 267941 = 50239) (by norm_num)
theorem B267965 : Blo 175800 267965 := bbase (se 3 (by rfl) ⟨50243, by rfl⟩ : syracuseStep 267965 = 100487) (by norm_num)
theorem B267989 : Blo 175800 267989 := bbase (se 7 (by rfl) ⟨3140, by rfl⟩ : syracuseStep 267989 = 6281) (by norm_num)
theorem B399077 : Blo 175800 399077 := bbase (se 4 (by rfl) ⟨37413, by rfl⟩ : syracuseStep 399077 = 74827) (by norm_num)
theorem B300773 : Blo 175800 300773 := bbase (se 4 (by rfl) ⟨28197, by rfl⟩ : syracuseStep 300773 = 56395) (by norm_num)
theorem B268013 : Blo 175800 268013 := bbase (se 3 (by rfl) ⟨50252, by rfl⟩ : syracuseStep 268013 = 100505) (by norm_num)
theorem B759557 : Blo 175800 759557 := bbase (se 4 (by rfl) ⟨71208, by rfl⟩ : syracuseStep 759557 = 142417) (by norm_num)
theorem B268037 : Blo 175800 268037 := bbase (se 4 (by rfl) ⟨25128, by rfl⟩ : syracuseStep 268037 = 50257) (by norm_num)
theorem B268061 : Blo 175800 268061 := bbase (se 3 (by rfl) ⟨50261, by rfl⟩ : syracuseStep 268061 = 100523) (by norm_num)
theorem B399149 : Blo 175800 399149 := bbase (se 3 (by rfl) ⟨74840, by rfl⟩ : syracuseStep 399149 = 149681) (by norm_num)
theorem B268085 : Blo 175800 268085 := bbase (se 5 (by rfl) ⟨12566, by rfl⟩ : syracuseStep 268085 = 25133) (by norm_num)
theorem B595781 : Blo 175800 595781 := bbase (se 4 (by rfl) ⟨55854, by rfl⟩ : syracuseStep 595781 = 111709) (by norm_num)
theorem B268109 : Blo 175800 268109 := bbase (se 3 (by rfl) ⟨50270, by rfl⟩ : syracuseStep 268109 = 100541) (by norm_num)
theorem B300901 : Blo 175800 300901 := bbase (se 4 (by rfl) ⟨28209, by rfl⟩ : syracuseStep 300901 = 56419) (by norm_num)
theorem B268133 : Blo 175800 268133 := bbase (se 4 (by rfl) ⟨25137, by rfl⟩ : syracuseStep 268133 = 50275) (by norm_num)
theorem B399221 : Blo 175800 399221 := bbase (se 5 (by rfl) ⟨18713, by rfl⟩ : syracuseStep 399221 = 37427) (by norm_num)
theorem B268157 : Blo 175800 268157 := bbase (se 3 (by rfl) ⟨50279, by rfl⟩ : syracuseStep 268157 = 100559) (by norm_num)
theorem B268181 : Blo 175800 268181 := bbase (se 6 (by rfl) ⟨6285, by rfl⟩ : syracuseStep 268181 = 12571) (by norm_num)
theorem B268205 : Blo 175800 268205 := bbase (se 3 (by rfl) ⟨50288, by rfl⟩ : syracuseStep 268205 = 100577) (by norm_num)
theorem B399293 : Blo 175800 399293 := bbase (se 3 (by rfl) ⟨74867, by rfl⟩ : syracuseStep 399293 = 149735) (by norm_num)
theorem B300989 : Blo 175800 300989 := bbase (se 3 (by rfl) ⟨56435, by rfl⟩ : syracuseStep 300989 = 112871) (by norm_num)
theorem B268229 : Blo 175800 268229 := bbase (se 4 (by rfl) ⟨25146, by rfl⟩ : syracuseStep 268229 = 50293) (by norm_num)
theorem B890837 : Blo 175800 890837 := bbase (se 7 (by rfl) ⟨10439, by rfl⟩ : syracuseStep 890837 = 20879) (by norm_num)
theorem B366557 : Blo 175800 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B268253 : Blo 175800 268253 := bbase (se 3 (by rfl) ⟨50297, by rfl⟩ : syracuseStep 268253 = 100595) (by norm_num)
theorem B1349621 : Blo 175800 1349621 := bbase (se 5 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 1349621 = 126527) (by norm_num)
theorem B268277 : Blo 175800 268277 := bbase (se 5 (by rfl) ⟨12575, by rfl⟩ : syracuseStep 268277 = 25151) (by norm_num)
theorem B333821 : Blo 175800 333821 := bbase (se 3 (by rfl) ⟨62591, by rfl⟩ : syracuseStep 333821 = 125183) (by norm_num)
theorem B399365 : Blo 175800 399365 := bbase (se 4 (by rfl) ⟨37440, by rfl⟩ : syracuseStep 399365 = 74881) (by norm_num)
theorem B268301 : Blo 175800 268301 := bbase (se 3 (by rfl) ⟨50306, by rfl⟩ : syracuseStep 268301 = 100613) (by norm_num)
theorem B563221 : Blo 175800 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B268325 : Blo 175800 268325 := bbase (se 4 (by rfl) ⟨25155, by rfl⟩ : syracuseStep 268325 = 50311) (by norm_num)
theorem B301117 : Blo 175800 301117 := bbase (se 3 (by rfl) ⟨56459, by rfl⟩ : syracuseStep 301117 = 112919) (by norm_num)
theorem B268349 : Blo 175800 268349 := bbase (se 3 (by rfl) ⟨50315, by rfl⟩ : syracuseStep 268349 = 100631) (by norm_num)
theorem B399437 : Blo 175800 399437 := bbase (se 3 (by rfl) ⟨74894, by rfl⟩ : syracuseStep 399437 = 149789) (by norm_num)
theorem B268373 : Blo 175800 268373 := bbase (se 8 (by rfl) ⟨1572, by rfl⟩ : syracuseStep 268373 = 3145) (by norm_num)
theorem B268397 : Blo 175800 268397 := bbase (se 3 (by rfl) ⟨50324, by rfl⟩ : syracuseStep 268397 = 100649) (by norm_num)
theorem B268421 : Blo 175800 268421 := bbase (se 4 (by rfl) ⟨25164, by rfl⟩ : syracuseStep 268421 = 50329) (by norm_num)
theorem B333973 : Blo 175800 333973 := bbase (se 6 (by rfl) ⟨7827, by rfl⟩ : syracuseStep 333973 = 15655) (by norm_num)
theorem B399509 : Blo 175800 399509 := bbase (se 6 (by rfl) ⟨9363, by rfl⟩ : syracuseStep 399509 = 18727) (by norm_num)
theorem B301205 : Blo 175800 301205 := bbase (se 6 (by rfl) ⟨7059, by rfl⟩ : syracuseStep 301205 = 14119) (by norm_num)
theorem B268445 : Blo 175800 268445 := bbase (se 3 (by rfl) ⟨50333, by rfl⟩ : syracuseStep 268445 = 100667) (by norm_num)
theorem B268469 : Blo 175800 268469 := bbase (se 5 (by rfl) ⟨12584, by rfl⟩ : syracuseStep 268469 = 25169) (by norm_num)
theorem B268493 : Blo 175800 268493 := bbase (se 3 (by rfl) ⟨50342, by rfl⟩ : syracuseStep 268493 = 100685) (by norm_num)
theorem B399581 : Blo 175800 399581 := bbase (se 3 (by rfl) ⟨74921, by rfl⟩ : syracuseStep 399581 = 149843) (by norm_num)
theorem B268517 : Blo 175800 268517 := bbase (se 4 (by rfl) ⟨25173, by rfl⟩ : syracuseStep 268517 = 50347) (by norm_num)
theorem B596213 : Blo 175800 596213 := bbase (se 5 (by rfl) ⟨27947, by rfl⟩ : syracuseStep 596213 = 55895) (by norm_num)
theorem B268541 : Blo 175800 268541 := bbase (se 3 (by rfl) ⟨50351, by rfl⟩ : syracuseStep 268541 = 100703) (by norm_num)
theorem B301333 : Blo 175800 301333 := bbase (se 6 (by rfl) ⟨7062, by rfl⟩ : syracuseStep 301333 = 14125) (by norm_num)
theorem B268565 : Blo 175800 268565 := bbase (se 6 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 268565 = 12589) (by norm_num)
theorem B399653 : Blo 175800 399653 := bbase (se 4 (by rfl) ⟨37467, by rfl⟩ : syracuseStep 399653 = 74935) (by norm_num)
theorem B268589 : Blo 175800 268589 := bbase (se 3 (by rfl) ⟨50360, by rfl⟩ : syracuseStep 268589 = 100721) (by norm_num)
theorem B268613 : Blo 175800 268613 := bbase (se 4 (by rfl) ⟨25182, by rfl⟩ : syracuseStep 268613 = 50365) (by norm_num)
theorem B268637 : Blo 175800 268637 := bbase (se 3 (by rfl) ⟨50369, by rfl⟩ : syracuseStep 268637 = 100739) (by norm_num)
theorem B399725 : Blo 175800 399725 := bbase (se 3 (by rfl) ⟨74948, by rfl⟩ : syracuseStep 399725 = 149897) (by norm_num)
theorem B301421 : Blo 175800 301421 := bbase (se 3 (by rfl) ⟨56516, by rfl⟩ : syracuseStep 301421 = 113033) (by norm_num)
theorem B268661 : Blo 175800 268661 := bbase (se 5 (by rfl) ⟨12593, by rfl⟩ : syracuseStep 268661 = 25187) (by norm_num)
theorem B268685 : Blo 175800 268685 := bbase (se 3 (by rfl) ⟨50378, by rfl⟩ : syracuseStep 268685 = 100757) (by norm_num)
theorem B268709 : Blo 175800 268709 := bbase (se 4 (by rfl) ⟨25191, by rfl⟩ : syracuseStep 268709 = 50383) (by norm_num)
theorem B399797 : Blo 175800 399797 := bbase (se 5 (by rfl) ⟨18740, by rfl⟩ : syracuseStep 399797 = 37481) (by norm_num)
theorem B268733 : Blo 175800 268733 := bbase (se 3 (by rfl) ⟨50387, by rfl⟩ : syracuseStep 268733 = 100775) (by norm_num)
theorem B334277 : Blo 175800 334277 := bbase (se 4 (by rfl) ⟨31338, by rfl⟩ : syracuseStep 334277 = 62677) (by norm_num)
theorem B268757 : Blo 175800 268757 := bbase (se 7 (by rfl) ⟨3149, by rfl⟩ : syracuseStep 268757 = 6299) (by norm_num)
theorem B301549 : Blo 175800 301549 := bbase (se 3 (by rfl) ⟨56540, by rfl⟩ : syracuseStep 301549 = 113081) (by norm_num)
theorem B268781 : Blo 175800 268781 := bbase (se 3 (by rfl) ⟨50396, by rfl⟩ : syracuseStep 268781 = 100793) (by norm_num)
theorem B399869 : Blo 175800 399869 := bbase (se 3 (by rfl) ⟨74975, by rfl⟩ : syracuseStep 399869 = 149951) (by norm_num)
theorem B268805 : Blo 175800 268805 := bbase (se 4 (by rfl) ⟨25200, by rfl⟩ : syracuseStep 268805 = 50401) (by norm_num)
theorem B203293 : Blo 175800 203293 := bbase (se 3 (by rfl) ⟨38117, by rfl⟩ : syracuseStep 203293 = 76235) (by norm_num)
theorem B268829 : Blo 175800 268829 := bbase (se 3 (by rfl) ⟨50405, by rfl⟩ : syracuseStep 268829 = 100811) (by norm_num)
theorem B268853 : Blo 175800 268853 := bbase (se 5 (by rfl) ⟨12602, by rfl⟩ : syracuseStep 268853 = 25205) (by norm_num)
theorem B399941 : Blo 175800 399941 := bbase (se 4 (by rfl) ⟨37494, by rfl⟩ : syracuseStep 399941 = 74989) (by norm_num)
theorem B301637 : Blo 175800 301637 := bbase (se 4 (by rfl) ⟨28278, by rfl⟩ : syracuseStep 301637 = 56557) (by norm_num)
theorem B268877 : Blo 175800 268877 := bbase (se 3 (by rfl) ⟨50414, by rfl⟩ : syracuseStep 268877 = 100829) (by norm_num)
theorem B268901 : Blo 175800 268901 := bbase (se 4 (by rfl) ⟨25209, by rfl⟩ : syracuseStep 268901 = 50419) (by norm_num)
theorem B268925 : Blo 175800 268925 := bbase (se 3 (by rfl) ⟨50423, by rfl⟩ : syracuseStep 268925 = 100847) (by norm_num)
theorem B400013 : Blo 175800 400013 := bbase (se 3 (by rfl) ⟨75002, by rfl⟩ : syracuseStep 400013 = 150005) (by norm_num)
theorem B268949 : Blo 175800 268949 := bbase (se 6 (by rfl) ⟨6303, by rfl⟩ : syracuseStep 268949 = 12607) (by norm_num)
theorem B596645 : Blo 175800 596645 := bbase (se 4 (by rfl) ⟨55935, by rfl⟩ : syracuseStep 596645 = 111871) (by norm_num)
theorem B268973 : Blo 175800 268973 := bbase (se 3 (by rfl) ⟨50432, by rfl⟩ : syracuseStep 268973 = 100865) (by norm_num)
theorem B301765 : Blo 175800 301765 := bbase (se 4 (by rfl) ⟨28290, by rfl⟩ : syracuseStep 301765 = 56581) (by norm_num)
theorem B268997 : Blo 175800 268997 := bbase (se 4 (by rfl) ⟨25218, by rfl⟩ : syracuseStep 268997 = 50437) (by norm_num)
theorem B400085 : Blo 175800 400085 := bbase (se 7 (by rfl) ⟨4688, by rfl⟩ : syracuseStep 400085 = 9377) (by norm_num)
theorem B269021 : Blo 175800 269021 := bbase (se 3 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 269021 = 100883) (by norm_num)
theorem B269045 : Blo 175800 269045 := bbase (se 5 (by rfl) ⟨12611, by rfl⟩ : syracuseStep 269045 = 25223) (by norm_num)
theorem B269069 : Blo 175800 269069 := bbase (se 3 (by rfl) ⟨50450, by rfl⟩ : syracuseStep 269069 = 100901) (by norm_num)
theorem B400157 : Blo 175800 400157 := bbase (se 3 (by rfl) ⟨75029, by rfl⟩ : syracuseStep 400157 = 150059) (by norm_num)
theorem B301853 : Blo 175800 301853 := bbase (se 3 (by rfl) ⟨56597, by rfl⟩ : syracuseStep 301853 = 113195) (by norm_num)
theorem B269093 : Blo 175800 269093 := bbase (se 4 (by rfl) ⟨25227, by rfl⟩ : syracuseStep 269093 = 50455) (by norm_num)
theorem B269117 : Blo 175800 269117 := bbase (se 3 (by rfl) ⟨50459, by rfl⟩ : syracuseStep 269117 = 100919) (by norm_num)
theorem B269141 : Blo 175800 269141 := bbase (se 9 (by rfl) ⟨788, by rfl⟩ : syracuseStep 269141 = 1577) (by norm_num)
theorem B400229 : Blo 175800 400229 := bbase (se 4 (by rfl) ⟨37521, by rfl⟩ : syracuseStep 400229 = 75043) (by norm_num)
theorem B269165 : Blo 175800 269165 := bbase (se 3 (by rfl) ⟨50468, by rfl⟩ : syracuseStep 269165 = 100937) (by norm_num)
theorem B269189 : Blo 175800 269189 := bbase (se 4 (by rfl) ⟨25236, by rfl⟩ : syracuseStep 269189 = 50473) (by norm_num)
theorem B301981 : Blo 175800 301981 := bbase (se 3 (by rfl) ⟨56621, by rfl⟩ : syracuseStep 301981 = 113243) (by norm_num)
theorem B269213 : Blo 175800 269213 := bbase (se 3 (by rfl) ⟨50477, by rfl⟩ : syracuseStep 269213 = 100955) (by norm_num)
theorem B400301 : Blo 175800 400301 := bbase (se 3 (by rfl) ⟨75056, by rfl⟩ : syracuseStep 400301 = 150113) (by norm_num)
theorem B269237 : Blo 175800 269237 := bbase (se 5 (by rfl) ⟨12620, by rfl⟩ : syracuseStep 269237 = 25241) (by norm_num)
theorem B269261 : Blo 175800 269261 := bbase (se 3 (by rfl) ⟨50486, by rfl⟩ : syracuseStep 269261 = 100973) (by norm_num)
theorem B269285 : Blo 175800 269285 := bbase (se 4 (by rfl) ⟨25245, by rfl⟩ : syracuseStep 269285 = 50491) (by norm_num)
theorem B400373 : Blo 175800 400373 := bbase (se 5 (by rfl) ⟨18767, by rfl⟩ : syracuseStep 400373 = 37535) (by norm_num)
theorem B302069 : Blo 175800 302069 := bbase (se 5 (by rfl) ⟨14159, by rfl⟩ : syracuseStep 302069 = 28319) (by norm_num)
theorem B269309 : Blo 175800 269309 := bbase (se 3 (by rfl) ⟨50495, by rfl⟩ : syracuseStep 269309 = 100991) (by norm_num)
theorem B269333 : Blo 175800 269333 := bbase (se 6 (by rfl) ⟨6312, by rfl⟩ : syracuseStep 269333 = 12625) (by norm_num)
theorem B269357 : Blo 175800 269357 := bbase (se 3 (by rfl) ⟨50504, by rfl⟩ : syracuseStep 269357 = 101009) (by norm_num)
theorem B400445 : Blo 175800 400445 := bbase (se 3 (by rfl) ⟨75083, by rfl⟩ : syracuseStep 400445 = 150167) (by norm_num)
theorem B269381 : Blo 175800 269381 := bbase (se 4 (by rfl) ⟨25254, by rfl⟩ : syracuseStep 269381 = 50509) (by norm_num)
theorem B597077 : Blo 175800 597077 := bbase (se 8 (by rfl) ⟨3498, by rfl⟩ : syracuseStep 597077 = 6997) (by norm_num)
theorem B269405 : Blo 175800 269405 := bbase (se 3 (by rfl) ⟨50513, by rfl⟩ : syracuseStep 269405 = 101027) (by norm_num)
theorem B302197 : Blo 175800 302197 := bbase (se 5 (by rfl) ⟨14165, by rfl⟩ : syracuseStep 302197 = 28331) (by norm_num)
theorem B269429 : Blo 175800 269429 := bbase (se 5 (by rfl) ⟨12629, by rfl⟩ : syracuseStep 269429 = 25259) (by norm_num)
theorem B400517 : Blo 175800 400517 := bbase (se 4 (by rfl) ⟨37548, by rfl⟩ : syracuseStep 400517 = 75097) (by norm_num)
theorem B269453 : Blo 175800 269453 := bbase (se 3 (by rfl) ⟨50522, by rfl⟩ : syracuseStep 269453 = 101045) (by norm_num)
theorem B269477 : Blo 175800 269477 := bbase (se 4 (by rfl) ⟨25263, by rfl⟩ : syracuseStep 269477 = 50527) (by norm_num)
theorem B335029 : Blo 175800 335029 := bbase (se 5 (by rfl) ⟨15704, by rfl⟩ : syracuseStep 335029 = 31409) (by norm_num)
theorem B269501 : Blo 175800 269501 := bbase (se 3 (by rfl) ⟨50531, by rfl⟩ : syracuseStep 269501 = 101063) (by norm_num)
theorem B400589 : Blo 175800 400589 := bbase (se 3 (by rfl) ⟨75110, by rfl⟩ : syracuseStep 400589 = 150221) (by norm_num)
theorem B302285 : Blo 175800 302285 := bbase (se 3 (by rfl) ⟨56678, by rfl⟩ : syracuseStep 302285 = 113357) (by norm_num)
theorem B269525 : Blo 175800 269525 := bbase (se 7 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 269525 = 6317) (by norm_num)
theorem B892133 : Blo 175800 892133 := bbase (se 4 (by rfl) ⟨83637, by rfl⟩ : syracuseStep 892133 = 167275) (by norm_num)
theorem B204005 : Blo 175800 204005 := bbase (se 4 (by rfl) ⟨19125, by rfl⟩ : syracuseStep 204005 = 38251) (by norm_num)
theorem B269549 : Blo 175800 269549 := bbase (se 3 (by rfl) ⟨50540, by rfl⟩ : syracuseStep 269549 = 101081) (by norm_num)
theorem B269573 : Blo 175800 269573 := bbase (se 4 (by rfl) ⟨25272, by rfl⟩ : syracuseStep 269573 = 50545) (by norm_num)
theorem B400661 : Blo 175800 400661 := bbase (se 6 (by rfl) ⟨9390, by rfl⟩ : syracuseStep 400661 = 18781) (by norm_num)
theorem B269597 : Blo 175800 269597 := bbase (se 3 (by rfl) ⟨50549, by rfl⟩ : syracuseStep 269597 = 101099) (by norm_num)
theorem B269621 : Blo 175800 269621 := bbase (se 5 (by rfl) ⟨12638, by rfl⟩ : syracuseStep 269621 = 25277) (by norm_num)
theorem B335173 : Blo 175800 335173 := bbase (se 4 (by rfl) ⟨31422, by rfl⟩ : syracuseStep 335173 = 62845) (by norm_num)
theorem B302413 : Blo 175800 302413 := bbase (se 3 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 302413 = 113405) (by norm_num)
theorem B269645 : Blo 175800 269645 := bbase (se 3 (by rfl) ⟨50558, by rfl⟩ : syracuseStep 269645 = 101117) (by norm_num)
theorem B400733 : Blo 175800 400733 := bbase (se 3 (by rfl) ⟨75137, by rfl⟩ : syracuseStep 400733 = 150275) (by norm_num)
theorem B204133 : Blo 175800 204133 := bbase (se 4 (by rfl) ⟨19137, by rfl⟩ : syracuseStep 204133 = 38275) (by norm_num)
theorem B269669 : Blo 175800 269669 := bbase (se 4 (by rfl) ⟨25281, by rfl⟩ : syracuseStep 269669 = 50563) (by norm_num)
theorem B269693 : Blo 175800 269693 := bbase (se 3 (by rfl) ⟨50567, by rfl⟩ : syracuseStep 269693 = 101135) (by norm_num)
theorem B400805 : Blo 175800 400805 := bbase (se 4 (by rfl) ⟨37575, by rfl⟩ : syracuseStep 400805 = 75151) (by norm_num)
theorem B302501 : Blo 175800 302501 := bbase (se 4 (by rfl) ⟨28359, by rfl⟩ : syracuseStep 302501 = 56719) (by norm_num)
theorem B204205 : Blo 175800 204205 := bbase (se 3 (by rfl) ⟨38288, by rfl⟩ : syracuseStep 204205 = 76577) (by norm_num)
theorem B335333 : Blo 175800 335333 := bbase (se 4 (by rfl) ⟨31437, by rfl⟩ : syracuseStep 335333 = 62875) (by norm_num)
theorem B400877 : Blo 175800 400877 := bbase (se 3 (by rfl) ⟨75164, by rfl⟩ : syracuseStep 400877 = 150329) (by norm_num)
theorem B597509 : Blo 175800 597509 := bbase (se 4 (by rfl) ⟨56016, by rfl⟩ : syracuseStep 597509 = 112033) (by norm_num)
theorem B302629 : Blo 175800 302629 := bbase (se 4 (by rfl) ⟨28371, by rfl⟩ : syracuseStep 302629 = 56743) (by norm_num)
theorem B400949 : Blo 175800 400949 := bbase (se 5 (by rfl) ⟨18794, by rfl⟩ : syracuseStep 400949 = 37589) (by norm_num)
theorem B335477 : Blo 175800 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B401021 : Blo 175800 401021 := bbase (se 3 (by rfl) ⟨75191, by rfl⟩ : syracuseStep 401021 = 150383) (by norm_num)
theorem B302717 : Blo 175800 302717 := bbase (se 3 (by rfl) ⟨56759, by rfl⟩ : syracuseStep 302717 = 113519) (by norm_num)
theorem B335549 : Blo 175800 335549 := bbase (se 3 (by rfl) ⟨62915, by rfl⟩ : syracuseStep 335549 = 125831) (by norm_num)
theorem B401093 : Blo 175800 401093 := bbase (se 4 (by rfl) ⟨37602, by rfl⟩ : syracuseStep 401093 = 75205) (by norm_num)
theorem B564965 : Blo 175800 564965 := bbase (se 4 (by rfl) ⟨52965, by rfl⟩ : syracuseStep 564965 = 105931) (by norm_num)
theorem B302845 : Blo 175800 302845 := bbase (se 3 (by rfl) ⟨56783, by rfl⟩ : syracuseStep 302845 = 113567) (by norm_num)
theorem B401165 : Blo 175800 401165 := bbase (se 3 (by rfl) ⟨75218, by rfl⟩ : syracuseStep 401165 = 150437) (by norm_num)
theorem B401237 : Blo 175800 401237 := bbase (se 9 (by rfl) ⟨1175, by rfl⟩ : syracuseStep 401237 = 2351) (by norm_num)
theorem B302933 : Blo 175800 302933 := bbase (se 9 (by rfl) ⟨887, by rfl⟩ : syracuseStep 302933 = 1775) (by norm_num)
theorem B434069 : Blo 175800 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B335765 : Blo 175800 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B401309 : Blo 175800 401309 := bbase (se 3 (by rfl) ⟨75245, by rfl⟩ : syracuseStep 401309 = 150491) (by norm_num)
theorem B565157 : Blo 175800 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B597941 : Blo 175800 597941 := bbase (se 5 (by rfl) ⟨28028, by rfl⟩ : syracuseStep 597941 = 56057) (by norm_num)
theorem B303061 : Blo 175800 303061 := bbase (se 7 (by rfl) ⟨3551, by rfl⟩ : syracuseStep 303061 = 7103) (by norm_num)
theorem B401381 : Blo 175800 401381 := bbase (se 4 (by rfl) ⟨37629, by rfl⟩ : syracuseStep 401381 = 75259) (by norm_num)
theorem B434173 : Blo 175800 434173 := bbase (se 3 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 434173 = 162815) (by norm_num)
theorem B335917 : Blo 175800 335917 := bbase (se 3 (by rfl) ⟨62984, by rfl⟩ : syracuseStep 335917 = 125969) (by norm_num)
theorem B401453 : Blo 175800 401453 := bbase (se 3 (by rfl) ⟨75272, by rfl⟩ : syracuseStep 401453 = 150545) (by norm_num)
theorem B303149 : Blo 175800 303149 := bbase (se 3 (by rfl) ⟨56840, by rfl⟩ : syracuseStep 303149 = 113681) (by norm_num)
theorem B401525 : Blo 175800 401525 := bbase (se 5 (by rfl) ⟨18821, by rfl⟩ : syracuseStep 401525 = 37643) (by norm_num)
theorem B303277 : Blo 175800 303277 := bbase (se 3 (by rfl) ⟨56864, by rfl⟩ : syracuseStep 303277 = 113729) (by norm_num)
theorem B401597 : Blo 175800 401597 := bbase (se 3 (by rfl) ⟨75299, by rfl⟩ : syracuseStep 401597 = 150599) (by norm_num)
theorem B1646837 : Blo 175800 1646837 := bbase (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) (by norm_num)
theorem B237821 : Blo 175800 237821 := bbase (se 3 (by rfl) ⟨44591, by rfl⟩ : syracuseStep 237821 = 89183) (by norm_num)
theorem B401669 : Blo 175800 401669 := bbase (se 4 (by rfl) ⟨37656, by rfl⟩ : syracuseStep 401669 = 75313) (by norm_num)
theorem B303365 : Blo 175800 303365 := bbase (se 4 (by rfl) ⟨28440, by rfl⟩ : syracuseStep 303365 = 56881) (by norm_num)
theorem B303421 : Blo 175800 303421 := bbase (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) (by norm_num)
theorem B401741 : Blo 175800 401741 := bbase (se 3 (by rfl) ⟨75326, by rfl⟩ : syracuseStep 401741 = 150653) (by norm_num)
theorem B336221 : Blo 175800 336221 := bbase (se 3 (by rfl) ⟨63041, by rfl⟩ : syracuseStep 336221 = 126083) (by norm_num)
theorem B598373 : Blo 175800 598373 := bbase (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) (by norm_num)
theorem B401813 : Blo 175800 401813 := bbase (se 6 (by rfl) ⟨9417, by rfl⟩ : syracuseStep 401813 = 18835) (by norm_num)
theorem B401885 : Blo 175800 401885 := bbase (se 3 (by rfl) ⟨75353, by rfl⟩ : syracuseStep 401885 = 150707) (by norm_num)
theorem B893429 : Blo 175800 893429 := bbase (se 5 (by rfl) ⟨41879, by rfl⟩ : syracuseStep 893429 = 83759) (by norm_num)
theorem B401957 : Blo 175800 401957 := bbase (se 4 (by rfl) ⟨37683, by rfl⟩ : syracuseStep 401957 = 75367) (by norm_num)
theorem B402029 : Blo 175800 402029 := bbase (se 3 (by rfl) ⟨75380, by rfl⟩ : syracuseStep 402029 = 150761) (by norm_num)
theorem B402101 : Blo 175800 402101 := bbase (se 5 (by rfl) ⟨18848, by rfl⟩ : syracuseStep 402101 = 37697) (by norm_num)
theorem B303845 : Blo 175800 303845 := bbase (se 4 (by rfl) ⟨28485, by rfl⟩ : syracuseStep 303845 = 56971) (by norm_num)
theorem B402173 : Blo 175800 402173 := bbase (se 3 (by rfl) ⟨75407, by rfl⟩ : syracuseStep 402173 = 150815) (by norm_num)
theorem B598805 : Blo 175800 598805 := bbase (se 6 (by rfl) ⟨14034, by rfl⟩ : syracuseStep 598805 = 28069) (by norm_num)
theorem B402245 : Blo 175800 402245 := bbase (se 4 (by rfl) ⟨37710, by rfl⟩ : syracuseStep 402245 = 75421) (by norm_num)
theorem B402317 : Blo 175800 402317 := bbase (se 3 (by rfl) ⟨75434, by rfl⟩ : syracuseStep 402317 = 150869) (by norm_num)
theorem B402389 : Blo 175800 402389 := bbase (se 7 (by rfl) ⟨4715, by rfl⟩ : syracuseStep 402389 = 9431) (by norm_num)
theorem B762853 : Blo 175800 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B402461 : Blo 175800 402461 := bbase (se 3 (by rfl) ⟨75461, by rfl⟩ : syracuseStep 402461 = 150923) (by norm_num)
theorem B336973 : Blo 175800 336973 := bbase (se 3 (by rfl) ⟨63182, by rfl⟩ : syracuseStep 336973 = 126365) (by norm_num)
theorem B304229 : Blo 175800 304229 := bbase (se 4 (by rfl) ⟨28521, by rfl⟩ : syracuseStep 304229 = 57043) (by norm_num)
theorem B402533 : Blo 175800 402533 := bbase (se 4 (by rfl) ⟨37737, by rfl⟩ : syracuseStep 402533 = 75475) (by norm_num)
theorem B402605 : Blo 175800 402605 := bbase (se 3 (by rfl) ⟨75488, by rfl⟩ : syracuseStep 402605 = 150977) (by norm_num)
theorem B828613 : Blo 175800 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B599237 : Blo 175800 599237 := bbase (se 4 (by rfl) ⟨56178, by rfl⟩ : syracuseStep 599237 = 112357) (by norm_num)
theorem B337117 : Blo 175800 337117 := bbase (se 3 (by rfl) ⟨63209, by rfl⟩ : syracuseStep 337117 = 126419) (by norm_num)
theorem B402677 : Blo 175800 402677 := bbase (se 5 (by rfl) ⟨18875, by rfl⟩ : syracuseStep 402677 = 37751) (by norm_num)
theorem B501029 : Blo 175800 501029 := bbase (se 4 (by rfl) ⟨46971, by rfl⟩ : syracuseStep 501029 = 93943) (by norm_num)
theorem B402749 : Blo 175800 402749 := bbase (se 3 (by rfl) ⟨75515, by rfl⟩ : syracuseStep 402749 = 151031) (by norm_num)
theorem B337277 : Blo 175800 337277 := bbase (se 3 (by rfl) ⟨63239, by rfl⟩ : syracuseStep 337277 = 126479) (by norm_num)
theorem B402821 : Blo 175800 402821 := bbase (se 4 (by rfl) ⟨37764, by rfl⟩ : syracuseStep 402821 = 75529) (by norm_num)
theorem B206233 : Blo 175800 206233 := bbase (se 2 (by rfl) ⟨77337, by rfl⟩ : syracuseStep 206233 = 154675) (by norm_num)
theorem B402893 : Blo 175800 402893 := bbase (se 3 (by rfl) ⟨75542, by rfl⟩ : syracuseStep 402893 = 151085) (by norm_num)
theorem B2139605 : Blo 175800 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B2041301 : Blo 175800 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B337421 : Blo 175800 337421 := bbase (se 3 (by rfl) ⟨63266, by rfl⟩ : syracuseStep 337421 = 126533) (by norm_num)
theorem B402965 : Blo 175800 402965 := bbase (se 6 (by rfl) ⟨9444, by rfl⟩ : syracuseStep 402965 = 18889) (by norm_num)
theorem B403037 : Blo 175800 403037 := bbase (se 3 (by rfl) ⟨75569, by rfl⟩ : syracuseStep 403037 = 151139) (by norm_num)
theorem B599669 : Blo 175800 599669 := bbase (se 5 (by rfl) ⟨28109, by rfl⟩ : syracuseStep 599669 = 56219) (by norm_num)
theorem B403109 : Blo 175800 403109 := bbase (se 4 (by rfl) ⟨37791, by rfl⟩ : syracuseStep 403109 = 75583) (by norm_num)
theorem B501461 : Blo 175800 501461 := bbase (se 7 (by rfl) ⟨5876, by rfl⟩ : syracuseStep 501461 = 11753) (by norm_num)
theorem B1287893 : Blo 175800 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B403181 : Blo 175800 403181 := bbase (se 3 (by rfl) ⟨75596, by rfl⟩ : syracuseStep 403181 = 151193) (by norm_num)
theorem B861941 : Blo 175800 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B894725 : Blo 175800 894725 := bbase (se 4 (by rfl) ⟨83880, by rfl⟩ : syracuseStep 894725 = 167761) (by norm_num)
theorem B337709 : Blo 175800 337709 := bbase (se 3 (by rfl) ⟨63320, by rfl⟩ : syracuseStep 337709 = 126641) (by norm_num)
theorem B403253 : Blo 175800 403253 := bbase (se 5 (by rfl) ⟨18902, by rfl⟩ : syracuseStep 403253 = 37805) (by norm_num)
theorem B403325 : Blo 175800 403325 := bbase (se 3 (by rfl) ⟨75623, by rfl⟩ : syracuseStep 403325 = 151247) (by norm_num)
theorem B337861 : Blo 175800 337861 := bbase (se 4 (by rfl) ⟨31674, by rfl⟩ : syracuseStep 337861 = 63349) (by norm_num)
theorem B403397 : Blo 175800 403397 := bbase (se 4 (by rfl) ⟨37818, by rfl⟩ : syracuseStep 403397 = 75637) (by norm_num)
theorem B403469 : Blo 175800 403469 := bbase (se 3 (by rfl) ⟨75650, by rfl⟩ : syracuseStep 403469 = 151301) (by norm_num)
theorem B600101 : Blo 175800 600101 := bbase (se 4 (by rfl) ⟨56259, by rfl⟩ : syracuseStep 600101 = 112519) (by norm_num)
theorem B305213 : Blo 175800 305213 := bbase (se 3 (by rfl) ⟨57227, by rfl⟩ : syracuseStep 305213 = 114455) (by norm_num)
theorem B403541 : Blo 175800 403541 := bbase (se 8 (by rfl) ⟨2364, by rfl⟩ : syracuseStep 403541 = 4729) (by norm_num)
theorem B206965 : Blo 175800 206965 := bbase (se 5 (by rfl) ⟨9701, by rfl⟩ : syracuseStep 206965 = 19403) (by norm_num)
theorem B403613 : Blo 175800 403613 := bbase (se 3 (by rfl) ⟨75677, by rfl⟩ : syracuseStep 403613 = 151355) (by norm_num)
theorem B403685 : Blo 175800 403685 := bbase (se 4 (by rfl) ⟨37845, by rfl⟩ : syracuseStep 403685 = 75691) (by norm_num)
theorem B338165 : Blo 175800 338165 := bbase (se 5 (by rfl) ⟨15851, by rfl⟩ : syracuseStep 338165 = 31703) (by norm_num)
theorem B403757 : Blo 175800 403757 := bbase (se 3 (by rfl) ⟨75704, by rfl⟩ : syracuseStep 403757 = 151409) (by norm_num)
theorem B403829 : Blo 175800 403829 := bbase (se 5 (by rfl) ⟨18929, by rfl⟩ : syracuseStep 403829 = 37859) (by norm_num)
theorem B403901 : Blo 175800 403901 := bbase (se 3 (by rfl) ⟨75731, by rfl⟩ : syracuseStep 403901 = 151463) (by norm_num)
theorem B502213 : Blo 175800 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B600533 : Blo 175800 600533 := bbase (se 7 (by rfl) ⟨7037, by rfl⟩ : syracuseStep 600533 = 14075) (by norm_num)
theorem B403973 : Blo 175800 403973 := bbase (se 4 (by rfl) ⟨37872, by rfl⟩ : syracuseStep 403973 = 75745) (by norm_num)
theorem B404045 : Blo 175800 404045 := bbase (se 3 (by rfl) ⟨75758, by rfl⟩ : syracuseStep 404045 = 151517) (by norm_num)
theorem B404117 : Blo 175800 404117 := bbase (se 6 (by rfl) ⟨9471, by rfl⟩ : syracuseStep 404117 = 18943) (by norm_num)
theorem B273053 : Blo 175800 273053 := bbase (se 3 (by rfl) ⟨51197, by rfl⟩ : syracuseStep 273053 = 102395) (by norm_num)
theorem B404189 : Blo 175800 404189 := bbase (se 3 (by rfl) ⟨75785, by rfl⟩ : syracuseStep 404189 = 151571) (by norm_num)
theorem B404261 : Blo 175800 404261 := bbase (se 4 (by rfl) ⟨37899, by rfl⟩ : syracuseStep 404261 = 75799) (by norm_num)
theorem B2796373 : Blo 175800 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B404333 : Blo 175800 404333 := bbase (se 3 (by rfl) ⟨75812, by rfl⟩ : syracuseStep 404333 = 151625) (by norm_num)
theorem B600965 : Blo 175800 600965 := bbase (se 4 (by rfl) ⟨56340, by rfl⟩ : syracuseStep 600965 = 112681) (by norm_num)
theorem B404405 : Blo 175800 404405 := bbase (se 5 (by rfl) ⟨18956, by rfl⟩ : syracuseStep 404405 = 37913) (by norm_num)
theorem B338917 : Blo 175800 338917 := bbase (se 4 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 338917 = 63547) (by norm_num)
theorem B240637 : Blo 175800 240637 := bbase (se 3 (by rfl) ⟨45119, by rfl⟩ : syracuseStep 240637 = 90239) (by norm_num)
theorem B404477 : Blo 175800 404477 := bbase (se 3 (by rfl) ⟨75839, by rfl⟩ : syracuseStep 404477 = 151679) (by norm_num)
theorem B896021 : Blo 175800 896021 := bbase (se 6 (by rfl) ⟨21000, by rfl⟩ : syracuseStep 896021 = 42001) (by norm_num)
theorem B404549 : Blo 175800 404549 := bbase (se 4 (by rfl) ⟨37926, by rfl⟩ : syracuseStep 404549 = 75853) (by norm_num)
theorem B339061 : Blo 175800 339061 := bbase (se 5 (by rfl) ⟨15893, by rfl⟩ : syracuseStep 339061 = 31787) (by norm_num)
theorem B339109 : Blo 175800 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B339221 : Blo 175800 339221 := bbase (se 6 (by rfl) ⟨7950, by rfl⟩ : syracuseStep 339221 = 15901) (by norm_num)
theorem B601397 : Blo 175800 601397 := bbase (se 5 (by rfl) ⟨28190, by rfl⟩ : syracuseStep 601397 = 56381) (by norm_num)
theorem B5680469 : Blo 175800 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B437653 : Blo 175800 437653 := bbase (se 6 (by rfl) ⟨10257, by rfl⟩ : syracuseStep 437653 = 20515) (by norm_num)
theorem B339365 : Blo 175800 339365 := bbase (se 4 (by rfl) ⟨31815, by rfl⟩ : syracuseStep 339365 = 63631) (by norm_num)
theorem B568757 : Blo 175800 568757 := bbase (se 5 (by rfl) ⟨26660, by rfl⟩ : syracuseStep 568757 = 53321) (by norm_num)
theorem B2010581 : Blo 175800 2010581 := bbase (se 7 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 2010581 = 47123) (by norm_num)
theorem B10923605 : Blo 175800 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B1814197 : Blo 175800 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B339653 : Blo 175800 339653 := bbase (se 4 (by rfl) ⟨31842, by rfl⟩ : syracuseStep 339653 = 63685) (by norm_num)
theorem B601829 : Blo 175800 601829 := bbase (se 4 (by rfl) ⟨56421, by rfl⟩ : syracuseStep 601829 = 112843) (by norm_num)
theorem B306965 : Blo 175800 306965 := bbase (se 6 (by rfl) ⟨7194, by rfl⟩ : syracuseStep 306965 = 14389) (by norm_num)
theorem B339805 : Blo 175800 339805 := bbase (se 3 (by rfl) ⟨63713, by rfl⟩ : syracuseStep 339805 = 127427) (by norm_num)
theorem B765845 : Blo 175800 765845 := bbase (se 6 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 765845 = 35899) (by norm_num)
theorem B1847285 : Blo 175800 1847285 := bbase (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) (by norm_num)
theorem B602245 : Blo 175800 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B340109 : Blo 175800 340109 := bbase (se 3 (by rfl) ⟨63770, by rfl⟩ : syracuseStep 340109 = 127541) (by norm_num)
theorem B602261 : Blo 175800 602261 := bbase (se 6 (by rfl) ⟨14115, by rfl⟩ : syracuseStep 602261 = 28231) (by norm_num)
theorem B1519829 : Blo 175800 1519829 := bbase (se 7 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 1519829 = 35621) (by norm_num)
theorem B897317 : Blo 175800 897317 := bbase (se 4 (by rfl) ⟨84123, by rfl⟩ : syracuseStep 897317 = 168247) (by norm_num)
theorem B3650069 : Blo 175800 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B242237 : Blo 175800 242237 := bbase (se 3 (by rfl) ⟨45419, by rfl⟩ : syracuseStep 242237 = 90839) (by norm_num)
theorem B602693 : Blo 175800 602693 := bbase (se 4 (by rfl) ⟨56502, by rfl⟩ : syracuseStep 602693 = 113005) (by norm_num)
theorem B668357 : Blo 175800 668357 := bbase (se 4 (by rfl) ⟨62658, by rfl⟩ : syracuseStep 668357 = 125317) (by norm_num)
theorem B963413 : Blo 175800 963413 := bbase (se 9 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 963413 = 5645) (by norm_num)
theorem B340861 : Blo 175800 340861 := bbase (se 3 (by rfl) ⟨63911, by rfl⟩ : syracuseStep 340861 = 127823) (by norm_num)
theorem B766853 : Blo 175800 766853 := bbase (se 4 (by rfl) ⟨71892, by rfl⟩ : syracuseStep 766853 = 143785) (by norm_num)
theorem B242605 : Blo 175800 242605 := bbase (se 3 (by rfl) ⟨45488, by rfl⟩ : syracuseStep 242605 = 90977) (by norm_num)
theorem B1029077 : Blo 175800 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B668645 : Blo 175800 668645 := bbase (se 4 (by rfl) ⟨62685, by rfl⟩ : syracuseStep 668645 = 125371) (by norm_num)
theorem B603125 : Blo 175800 603125 := bbase (se 5 (by rfl) ⟨28271, by rfl⟩ : syracuseStep 603125 = 56543) (by norm_num)
theorem B341005 : Blo 175800 341005 := bbase (se 3 (by rfl) ⟨63938, by rfl⟩ : syracuseStep 341005 = 127877) (by norm_num)
theorem B341165 : Blo 175800 341165 := bbase (se 3 (by rfl) ⟨63968, by rfl⟩ : syracuseStep 341165 = 127937) (by norm_num)
theorem B505061 : Blo 175800 505061 := bbase (se 4 (by rfl) ⟨47349, by rfl⟩ : syracuseStep 505061 = 94699) (by norm_num)
theorem B341309 : Blo 175800 341309 := bbase (se 3 (by rfl) ⟨63995, by rfl⟩ : syracuseStep 341309 = 127991) (by norm_num)
theorem B865637 : Blo 175800 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B636277 : Blo 175800 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B603557 : Blo 175800 603557 := bbase (se 4 (by rfl) ⟨56583, by rfl⟩ : syracuseStep 603557 = 113167) (by norm_num)
theorem B898613 : Blo 175800 898613 := bbase (se 5 (by rfl) ⟨42122, by rfl⟩ : syracuseStep 898613 = 84245) (by norm_num)
theorem B1357397 : Blo 175800 1357397 := bbase (se 8 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 1357397 = 15907) (by norm_num)
theorem B571013 : Blo 175800 571013 := bbase (se 4 (by rfl) ⟨53532, by rfl⟩ : syracuseStep 571013 = 107065) (by norm_num)
theorem B407189 : Blo 175800 407189 := bbase (se 6 (by rfl) ⟨9543, by rfl⟩ : syracuseStep 407189 = 19087) (by norm_num)
theorem B571141 : Blo 175800 571141 := bbase (se 4 (by rfl) ⟨53544, by rfl⟩ : syracuseStep 571141 = 107089) (by norm_num)
theorem B603989 : Blo 175800 603989 := bbase (se 9 (by rfl) ⟨1769, by rfl⟩ : syracuseStep 603989 = 3539) (by norm_num)
theorem B538613 : Blo 175800 538613 := bbase (se 5 (by rfl) ⟨25247, by rfl⟩ : syracuseStep 538613 = 50495) (by norm_num)
theorem B669829 : Blo 175800 669829 := bbase (se 4 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 669829 = 125593) (by norm_num)
theorem B604421 : Blo 175800 604421 := bbase (se 4 (by rfl) ⟨56664, by rfl⟩ : syracuseStep 604421 = 113329) (by norm_num)
theorem B506245 : Blo 175800 506245 := bbase (se 4 (by rfl) ⟨47460, by rfl⟩ : syracuseStep 506245 = 94921) (by norm_num)
theorem B670133 : Blo 175800 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B506405 : Blo 175800 506405 := bbase (se 4 (by rfl) ⟨47475, by rfl⟩ : syracuseStep 506405 = 94951) (by norm_num)
theorem B604853 : Blo 175800 604853 := bbase (se 5 (by rfl) ⟨28352, by rfl⟩ : syracuseStep 604853 = 56705) (by norm_num)
theorem B506645 : Blo 175800 506645 := bbase (se 6 (by rfl) ⟨11874, by rfl⟩ : syracuseStep 506645 = 23749) (by norm_num)
theorem B899909 : Blo 175800 899909 := bbase (se 4 (by rfl) ⟨84366, by rfl⟩ : syracuseStep 899909 = 168733) (by norm_num)
theorem B506837 : Blo 175800 506837 := bbase (se 7 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 506837 = 11879) (by norm_num)
theorem B179245 : Blo 175800 179245 := bbase (se 3 (by rfl) ⟨33608, by rfl⟩ : syracuseStep 179245 = 67217) (by norm_num)
theorem B605285 : Blo 175800 605285 := bbase (se 4 (by rfl) ⟨56745, by rfl⟩ : syracuseStep 605285 = 113491) (by norm_num)
theorem B933125 : Blo 175800 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B376157 : Blo 175800 376157 := bbase (se 3 (by rfl) ⟨70529, by rfl⟩ : syracuseStep 376157 = 141059) (by norm_num)
theorem B179569 : Blo 175800 179569 := bbase (se 2 (by rfl) ⟨67338, by rfl⟩ : syracuseStep 179569 = 134677) (by norm_num)
theorem B376301 : Blo 175800 376301 := bbase (se 3 (by rfl) ⟨70556, by rfl⟩ : syracuseStep 376301 = 141113) (by norm_num)
theorem B605717 : Blo 175800 605717 := bbase (se 6 (by rfl) ⟨14196, by rfl⟩ : syracuseStep 605717 = 28393) (by norm_num)
theorem B212549 : Blo 175800 212549 := bbase (se 4 (by rfl) ⟨19926, by rfl⟩ : syracuseStep 212549 = 39853) (by norm_num)
theorem B212881 : Blo 175800 212881 := bbase (se 2 (by rfl) ⟨79830, by rfl⟩ : syracuseStep 212881 = 159661) (by norm_num)
theorem B376741 : Blo 175800 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B507829 : Blo 175800 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B606149 : Blo 175800 606149 := bbase (se 4 (by rfl) ⟨56826, by rfl⟩ : syracuseStep 606149 = 113653) (by norm_num)
theorem B966613 : Blo 175800 966613 := bbase (se 7 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 966613 = 22655) (by norm_num)
theorem B213025 : Blo 175800 213025 := bbase (se 2 (by rfl) ⟨79884, by rfl⟩ : syracuseStep 213025 = 159769) (by norm_num)
theorem B901205 : Blo 175800 901205 := bbase (se 8 (by rfl) ⟨5280, by rfl⟩ : syracuseStep 901205 = 10561) (by norm_num)
theorem B377045 : Blo 175800 377045 := bbase (se 7 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 377045 = 8837) (by norm_num)
theorem B344405 : Blo 175800 344405 := bbase (se 10 (by rfl) ⟨504, by rfl⟩ : syracuseStep 344405 = 1009) (by norm_num)
theorem B606581 : Blo 175800 606581 := bbase (se 5 (by rfl) ⟨28433, by rfl⟩ : syracuseStep 606581 = 56867) (by norm_num)
theorem B180721 : Blo 175800 180721 := bbase (se 2 (by rfl) ⟨67770, by rfl⟩ : syracuseStep 180721 = 135541) (by norm_num)
theorem B672245 : Blo 175800 672245 := bbase (se 5 (by rfl) ⟨31511, by rfl⟩ : syracuseStep 672245 = 63023) (by norm_num)
theorem B574037 : Blo 175800 574037 := bbase (se 8 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 574037 = 6727) (by norm_num)
theorem B672533 : Blo 175800 672533 := bbase (se 6 (by rfl) ⟨15762, by rfl⟩ : syracuseStep 672533 = 31525) (by norm_num)
theorem B377797 : Blo 175800 377797 := bbase (se 4 (by rfl) ⟨35418, by rfl⟩ : syracuseStep 377797 = 70837) (by norm_num)
theorem B508933 : Blo 175800 508933 := bbase (se 4 (by rfl) ⟨47712, by rfl⟩ : syracuseStep 508933 = 95425) (by norm_num)
theorem B214049 : Blo 175800 214049 := bbase (se 2 (by rfl) ⟨80268, by rfl⟩ : syracuseStep 214049 = 160537) (by norm_num)
theorem B738341 : Blo 175800 738341 := bbase (se 4 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 738341 = 138439) (by norm_num)
theorem B181297 : Blo 175800 181297 := bbase (se 2 (by rfl) ⟨67986, by rfl⟩ : syracuseStep 181297 = 135973) (by norm_num)
theorem B377941 : Blo 175800 377941 := bbase (se 8 (by rfl) ⟨2214, by rfl⟩ : syracuseStep 377941 = 4429) (by norm_num)
theorem B902501 : Blo 175800 902501 := bbase (se 4 (by rfl) ⟨84609, by rfl⟩ : syracuseStep 902501 = 169219) (by norm_num)
theorem B771461 : Blo 175800 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B607637 : Blo 175800 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B378317 : Blo 175800 378317 := bbase (se 3 (by rfl) ⟨70934, by rfl⟩ : syracuseStep 378317 = 141869) (by norm_num)
theorem B378685 : Blo 175800 378685 := bbase (se 3 (by rfl) ⟨71003, by rfl⟩ : syracuseStep 378685 = 142007) (by norm_num)
theorem B673717 : Blo 175800 673717 := bbase (se 5 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 673717 = 63161) (by norm_num)
theorem B182197 : Blo 175800 182197 := bbase (se 5 (by rfl) ⟨8540, by rfl⟩ : syracuseStep 182197 = 17081) (by norm_num)
theorem B215245 : Blo 175800 215245 := bbase (se 3 (by rfl) ⟨40358, by rfl⟩ : syracuseStep 215245 = 80717) (by norm_num)
theorem B674021 : Blo 175800 674021 := bbase (se 4 (by rfl) ⟨63189, by rfl⟩ : syracuseStep 674021 = 126379) (by norm_num)
theorem B215317 : Blo 175800 215317 := bbase (se 6 (by rfl) ⟨5046, by rfl⟩ : syracuseStep 215317 = 10093) (by norm_num)
theorem B510437 : Blo 175800 510437 := bbase (se 4 (by rfl) ⟨47853, by rfl⟩ : syracuseStep 510437 = 95707) (by norm_num)
theorem B903797 : Blo 175800 903797 := bbase (se 5 (by rfl) ⟨42365, by rfl⟩ : syracuseStep 903797 = 84731) (by norm_num)
theorem B3263125 : Blo 175800 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B1493653 : Blo 175800 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B445085 : Blo 175800 445085 := bbase (se 3 (by rfl) ⟨83453, by rfl⟩ : syracuseStep 445085 = 166907) (by norm_num)
theorem B445277 : Blo 175800 445277 := bbase (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) (by norm_num)
theorem B248845 : Blo 175800 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B281765 : Blo 175800 281765 := bbase (se 4 (by rfl) ⟨26415, by rfl⟩ : syracuseStep 281765 = 52831) (by norm_num)
theorem B445621 : Blo 175800 445621 := bbase (se 5 (by rfl) ⟨20888, by rfl⟩ : syracuseStep 445621 = 41777) (by norm_num)
theorem B806149 : Blo 175800 806149 := bbase (se 4 (by rfl) ⟨75576, by rfl⟩ : syracuseStep 806149 = 151153) (by norm_num)
theorem B380189 : Blo 175800 380189 := bbase (se 3 (by rfl) ⟨71285, by rfl⟩ : syracuseStep 380189 = 142571) (by norm_num)
theorem B281893 : Blo 175800 281893 := bbase (se 4 (by rfl) ⟨26427, by rfl⟩ : syracuseStep 281893 = 52855) (by norm_num)
theorem B445733 : Blo 175800 445733 := bbase (se 4 (by rfl) ⟨41787, by rfl⟩ : syracuseStep 445733 = 83575) (by norm_num)
theorem B544085 : Blo 175800 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B380333 : Blo 175800 380333 := bbase (se 3 (by rfl) ⟨71312, by rfl⟩ : syracuseStep 380333 = 142625) (by norm_num)
theorem B445925 : Blo 175800 445925 := bbase (se 4 (by rfl) ⟨41805, by rfl⟩ : syracuseStep 445925 = 83611) (by norm_num)
theorem B380693 : Blo 175800 380693 := bbase (se 6 (by rfl) ⟨8922, by rfl⟩ : syracuseStep 380693 = 17845) (by norm_num)
theorem B446269 : Blo 175800 446269 := bbase (se 3 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 446269 = 167351) (by norm_num)
theorem B905093 : Blo 175800 905093 := bbase (se 4 (by rfl) ⟨84852, by rfl⟩ : syracuseStep 905093 = 169705) (by norm_num)
theorem B282533 : Blo 175800 282533 := bbase (se 4 (by rfl) ⟨26487, by rfl⟩ : syracuseStep 282533 = 52975) (by norm_num)
theorem B446381 : Blo 175800 446381 := bbase (se 3 (by rfl) ⟨83696, by rfl⟩ : syracuseStep 446381 = 167393) (by norm_num)
theorem B184289 : Blo 175800 184289 := bbase (se 2 (by rfl) ⟨69108, by rfl⟩ : syracuseStep 184289 = 138217) (by norm_num)
theorem B1527893 : Blo 175800 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B446573 : Blo 175800 446573 := bbase (se 3 (by rfl) ⟨83732, by rfl⟩ : syracuseStep 446573 = 167465) (by norm_num)
theorem B676133 : Blo 175800 676133 := bbase (se 4 (by rfl) ⟨63387, by rfl⟩ : syracuseStep 676133 = 126775) (by norm_num)
theorem B282989 : Blo 175800 282989 := bbase (se 3 (by rfl) ⟨53060, by rfl⟩ : syracuseStep 282989 = 106121) (by norm_num)
theorem B446917 : Blo 175800 446917 := bbase (se 4 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 446917 = 83797) (by norm_num)
theorem B217597 : Blo 175800 217597 := bbase (se 3 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 217597 = 81599) (by norm_num)
theorem B283133 : Blo 175800 283133 := bbase (se 3 (by rfl) ⟨53087, by rfl⟩ : syracuseStep 283133 = 106175) (by norm_num)
theorem B447029 : Blo 175800 447029 := bbase (se 5 (by rfl) ⟨20954, by rfl⟩ : syracuseStep 447029 = 41909) (by norm_num)
theorem B676421 : Blo 175800 676421 := bbase (se 4 (by rfl) ⟨63414, by rfl⟩ : syracuseStep 676421 = 126829) (by norm_num)
theorem B283213 : Blo 175800 283213 := bbase (se 3 (by rfl) ⟨53102, by rfl⟩ : syracuseStep 283213 = 106205) (by norm_num)
theorem B545413 : Blo 175800 545413 := bbase (se 4 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 545413 = 102265) (by norm_num)
theorem B283277 : Blo 175800 283277 := bbase (se 3 (by rfl) ⟨53114, by rfl⟩ : syracuseStep 283277 = 106229) (by norm_num)
theorem B381581 : Blo 175800 381581 := bbase (se 3 (by rfl) ⟨71546, by rfl⟩ : syracuseStep 381581 = 143093) (by norm_num)
theorem B840389 : Blo 175800 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B447221 : Blo 175800 447221 := bbase (se 5 (by rfl) ⟨20963, by rfl⟩ : syracuseStep 447221 = 41927) (by norm_num)
theorem B283405 : Blo 175800 283405 := bbase (se 3 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 283405 = 106277) (by norm_num)
theorem B381829 : Blo 175800 381829 := bbase (se 4 (by rfl) ⟨35796, by rfl⟩ : syracuseStep 381829 = 71593) (by norm_num)
theorem B447565 : Blo 175800 447565 := bbase (se 3 (by rfl) ⟨83918, by rfl⟩ : syracuseStep 447565 = 167837) (by norm_num)
theorem B906389 : Blo 175800 906389 := bbase (se 6 (by rfl) ⟨21243, by rfl⟩ : syracuseStep 906389 = 42487) (by norm_num)
theorem B1365173 : Blo 175800 1365173 := bbase (se 5 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 1365173 = 127985) (by norm_num)
theorem B447677 : Blo 175800 447677 := bbase (se 3 (by rfl) ⟨83939, by rfl⟩ : syracuseStep 447677 = 167879) (by norm_num)
theorem B480581 : Blo 175800 480581 := bbase (se 4 (by rfl) ⟨45054, by rfl⟩ : syracuseStep 480581 = 90109) (by norm_num)
theorem B447869 : Blo 175800 447869 := bbase (se 3 (by rfl) ⟨83975, by rfl⟩ : syracuseStep 447869 = 167951) (by norm_num)
theorem B382333 : Blo 175800 382333 := bbase (se 3 (by rfl) ⟨71687, by rfl⟩ : syracuseStep 382333 = 143375) (by norm_num)
theorem B316885 : Blo 175800 316885 := bbase (se 7 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 316885 = 7427) (by norm_num)
theorem B251437 : Blo 175800 251437 := bbase (se 3 (by rfl) ⟨47144, by rfl⟩ : syracuseStep 251437 = 94289) (by norm_num)
theorem B448213 : Blo 175800 448213 := bbase (se 7 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 448213 = 10505) (by norm_num)
theorem B677605 : Blo 175800 677605 := bbase (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) (by norm_num)
theorem B644869 : Blo 175800 644869 := bbase (se 4 (by rfl) ⟨60456, by rfl⟩ : syracuseStep 644869 = 120913) (by norm_num)
theorem B448325 : Blo 175800 448325 := bbase (se 4 (by rfl) ⟨42030, by rfl⟩ : syracuseStep 448325 = 84061) (by norm_num)
theorem B382925 : Blo 175800 382925 := bbase (se 3 (by rfl) ⟨71798, by rfl⟩ : syracuseStep 382925 = 143597) (by norm_num)
theorem B284629 : Blo 175800 284629 := bbase (se 7 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 284629 = 6671) (by norm_num)
theorem B448517 : Blo 175800 448517 := bbase (se 4 (by rfl) ⟨42048, by rfl⟩ : syracuseStep 448517 = 84097) (by norm_num)
theorem B677909 : Blo 175800 677909 := bbase (se 6 (by rfl) ⟨15888, by rfl⟩ : syracuseStep 677909 = 31777) (by norm_num)
theorem B1136693 : Blo 175800 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B252029 : Blo 175800 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B252109 : Blo 175800 252109 := bbase (se 3 (by rfl) ⟨47270, by rfl⟩ : syracuseStep 252109 = 94541) (by norm_num)
theorem B383221 : Blo 175800 383221 := bbase (se 5 (by rfl) ⟨17963, by rfl⟩ : syracuseStep 383221 = 35927) (by norm_num)
theorem B317765 : Blo 175800 317765 := bbase (se 4 (by rfl) ⟨29790, by rfl⟩ : syracuseStep 317765 = 59581) (by norm_num)
theorem B252229 : Blo 175800 252229 := bbase (se 4 (by rfl) ⟨23646, by rfl⟩ : syracuseStep 252229 = 47293) (by norm_num)
theorem B448861 : Blo 175800 448861 := bbase (se 3 (by rfl) ⟨84161, by rfl⟩ : syracuseStep 448861 = 168323) (by norm_num)
theorem B252325 : Blo 175800 252325 := bbase (se 4 (by rfl) ⟨23655, by rfl⟩ : syracuseStep 252325 = 47311) (by norm_num)
theorem B907685 : Blo 175800 907685 := bbase (se 4 (by rfl) ⟨85095, by rfl⟩ : syracuseStep 907685 = 170191) (by norm_num)
theorem B448973 : Blo 175800 448973 := bbase (se 3 (by rfl) ⟨84182, by rfl⟩ : syracuseStep 448973 = 168365) (by norm_num)
theorem B317981 : Blo 175800 317981 := bbase (se 3 (by rfl) ⟨59621, by rfl⟩ : syracuseStep 317981 = 119243) (by norm_num)
theorem B2546261 : Blo 175800 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B285301 : Blo 175800 285301 := bbase (se 5 (by rfl) ⟨13373, by rfl⟩ : syracuseStep 285301 = 26747) (by norm_num)
theorem B449165 : Blo 175800 449165 := bbase (se 3 (by rfl) ⟨84218, by rfl⟩ : syracuseStep 449165 = 168437) (by norm_num)
theorem B1694357 : Blo 175800 1694357 := bbase (se 6 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 1694357 = 79423) (by norm_num)
theorem B383717 : Blo 175800 383717 := bbase (se 4 (by rfl) ⟨35973, by rfl⟩ : syracuseStep 383717 = 71947) (by norm_num)
theorem B318269 : Blo 175800 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B252821 : Blo 175800 252821 := bbase (se 6 (by rfl) ⟨5925, by rfl⟩ : syracuseStep 252821 = 11851) (by norm_num)
theorem B383933 : Blo 175800 383933 := bbase (se 3 (by rfl) ⟨71987, by rfl⟩ : syracuseStep 383933 = 143975) (by norm_num)
theorem B449509 : Blo 175800 449509 := bbase (se 4 (by rfl) ⟨42141, by rfl⟩ : syracuseStep 449509 = 84283) (by norm_num)
theorem B1006613 : Blo 175800 1006613 := bbase (se 6 (by rfl) ⟨23592, by rfl⟩ : syracuseStep 1006613 = 47185) (by norm_num)
theorem B449621 : Blo 175800 449621 := bbase (se 8 (by rfl) ⟨2634, by rfl⟩ : syracuseStep 449621 = 5269) (by norm_num)
theorem B613493 : Blo 175800 613493 := bbase (se 5 (by rfl) ⟨28757, by rfl⟩ : syracuseStep 613493 = 57515) (by norm_num)
theorem B449813 : Blo 175800 449813 := bbase (se 6 (by rfl) ⟨10542, by rfl⟩ : syracuseStep 449813 = 21085) (by norm_num)
theorem B187805 : Blo 175800 187805 := bbase (se 3 (by rfl) ⟨35213, by rfl⟩ : syracuseStep 187805 = 70427) (by norm_num)
theorem B253373 : Blo 175800 253373 := bbase (se 3 (by rfl) ⟨47507, by rfl⟩ : syracuseStep 253373 = 95015) (by norm_num)
theorem B187877 : Blo 175800 187877 := bbase (se 4 (by rfl) ⟨17613, by rfl⟩ : syracuseStep 187877 = 35227) (by norm_num)
theorem B286301 : Blo 175800 286301 := bbase (se 3 (by rfl) ⟨53681, by rfl⟩ : syracuseStep 286301 = 107363) (by norm_num)
theorem B482917 : Blo 175800 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B450157 : Blo 175800 450157 := bbase (se 3 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 450157 = 168809) (by norm_num)
theorem B188065 : Blo 175800 188065 := bbase (se 2 (by rfl) ⟨70524, by rfl⟩ : syracuseStep 188065 = 141049) (by norm_num)
theorem B908981 : Blo 175800 908981 := bbase (se 5 (by rfl) ⟨42608, by rfl⟩ : syracuseStep 908981 = 85217) (by norm_num)
theorem B450269 : Blo 175800 450269 := bbase (se 3 (by rfl) ⟨84425, by rfl⟩ : syracuseStep 450269 = 168851) (by norm_num)
theorem B319285 : Blo 175800 319285 := bbase (se 5 (by rfl) ⟨14966, by rfl⟩ : syracuseStep 319285 = 29933) (by norm_num)
theorem B188249 : Blo 175800 188249 := bbase (se 2 (by rfl) ⟨70593, by rfl⟩ : syracuseStep 188249 = 141187) (by norm_num)
theorem B450461 : Blo 175800 450461 := bbase (se 3 (by rfl) ⟨84461, by rfl⟩ : syracuseStep 450461 = 168923) (by norm_num)
theorem B483349 : Blo 175800 483349 := bbase (se 6 (by rfl) ⟨11328, by rfl⟩ : syracuseStep 483349 = 22657) (by norm_num)
theorem B286805 : Blo 175800 286805 := bbase (se 8 (by rfl) ⟨1680, by rfl⟩ : syracuseStep 286805 = 3361) (by norm_num)
theorem B680021 : Blo 175800 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B254125 : Blo 175800 254125 := bbase (se 3 (by rfl) ⟨47648, by rfl⟩ : syracuseStep 254125 = 95297) (by norm_num)
theorem B450805 : Blo 175800 450805 := bbase (se 5 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 450805 = 42263) (by norm_num)
theorem B909605 : Blo 175800 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B450917 : Blo 175800 450917 := bbase (se 4 (by rfl) ⟨42273, by rfl⟩ : syracuseStep 450917 = 84547) (by norm_num)
theorem B680309 : Blo 175800 680309 := bbase (se 5 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 680309 = 63779) (by norm_num)
theorem B287221 : Blo 175800 287221 := bbase (se 5 (by rfl) ⟨13463, by rfl⟩ : syracuseStep 287221 = 26927) (by norm_num)
theorem B451109 : Blo 175800 451109 := bbase (se 4 (by rfl) ⟨42291, by rfl⟩ : syracuseStep 451109 = 84583) (by norm_num)
theorem B189001 : Blo 175800 189001 := bbase (se 2 (by rfl) ⟨70875, by rfl⟩ : syracuseStep 189001 = 141751) (by norm_num)
theorem B647765 : Blo 175800 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B647797 : Blo 175800 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B189073 : Blo 175800 189073 := bbase (se 2 (by rfl) ⟨70902, by rfl⟩ : syracuseStep 189073 = 141805) (by norm_num)
theorem B189253 : Blo 175800 189253 := bbase (se 4 (by rfl) ⟨17742, by rfl⟩ : syracuseStep 189253 = 35485) (by norm_num)
theorem B451453 : Blo 175800 451453 := bbase (se 3 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 451453 = 169295) (by norm_num)
theorem B254917 : Blo 175800 254917 := bbase (se 4 (by rfl) ⟨23898, by rfl⟩ : syracuseStep 254917 = 47797) (by norm_num)
theorem B1139669 : Blo 175800 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B451565 : Blo 175800 451565 := bbase (se 3 (by rfl) ⟨84668, by rfl⟩ : syracuseStep 451565 = 169337) (by norm_num)
theorem B386077 : Blo 175800 386077 := bbase (se 3 (by rfl) ⟨72389, by rfl⟩ : syracuseStep 386077 = 144779) (by norm_num)
theorem B287813 : Blo 175800 287813 := bbase (se 4 (by rfl) ⟨26982, by rfl⟩ : syracuseStep 287813 = 53965) (by norm_num)
theorem B451757 : Blo 175800 451757 := bbase (se 3 (by rfl) ⟨84704, by rfl⟩ : syracuseStep 451757 = 169409) (by norm_num)
theorem B189697 : Blo 175800 189697 := bbase (se 2 (by rfl) ⟨71136, by rfl⟩ : syracuseStep 189697 = 142273) (by norm_num)
theorem B255253 : Blo 175800 255253 := bbase (se 6 (by rfl) ⟨5982, by rfl⟩ : syracuseStep 255253 = 11965) (by norm_num)
theorem B222517 : Blo 175800 222517 := bbase (se 5 (by rfl) ⟨10430, by rfl⟩ : syracuseStep 222517 = 20861) (by norm_num)
theorem B189821 : Blo 175800 189821 := bbase (se 3 (by rfl) ⟨35591, by rfl⟩ : syracuseStep 189821 = 71183) (by norm_num)
theorem B222689 : Blo 175800 222689 := bbase (se 2 (by rfl) ⟨83508, by rfl⟩ : syracuseStep 222689 = 167017) (by norm_num)
theorem B255469 : Blo 175800 255469 := bbase (se 3 (by rfl) ⟨47900, by rfl⟩ : syracuseStep 255469 = 95801) (by norm_num)
theorem B1271285 : Blo 175800 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B452101 : Blo 175800 452101 := bbase (se 4 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 452101 = 84769) (by norm_num)
theorem B681493 : Blo 175800 681493 := bbase (se 6 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 681493 = 31945) (by norm_num)
theorem B222745 : Blo 175800 222745 := bbase (se 2 (by rfl) ⟨83529, by rfl⟩ : syracuseStep 222745 = 167059) (by norm_num)
theorem B452213 : Blo 175800 452213 := bbase (se 5 (by rfl) ⟨21197, by rfl⟩ : syracuseStep 452213 = 42395) (by norm_num)
theorem B222841 : Blo 175800 222841 := bbase (se 2 (by rfl) ⟨83565, by rfl⟩ : syracuseStep 222841 = 167131) (by norm_num)
theorem B190073 : Blo 175800 190073 := bbase (se 2 (by rfl) ⟨71277, by rfl⟩ : syracuseStep 190073 = 142555) (by norm_num)
theorem B550597 : Blo 175800 550597 := bbase (se 4 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 550597 = 103237) (by norm_num)
theorem B223013 : Blo 175800 223013 := bbase (se 4 (by rfl) ⟨20907, by rfl⟩ : syracuseStep 223013 = 41815) (by norm_num)
theorem B452405 : Blo 175800 452405 := bbase (se 5 (by rfl) ⟨21206, by rfl⟩ : syracuseStep 452405 = 42413) (by norm_num)
theorem B681797 : Blo 175800 681797 := bbase (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) (by norm_num)
theorem B223069 : Blo 175800 223069 := bbase (se 3 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 223069 = 83651) (by norm_num)
theorem B255845 : Blo 175800 255845 := bbase (se 4 (by rfl) ⟨23985, by rfl⟩ : syracuseStep 255845 = 47971) (by norm_num)
theorem B223165 : Blo 175800 223165 := bbase (se 3 (by rfl) ⟨41843, by rfl⟩ : syracuseStep 223165 = 83687) (by norm_num)
theorem B190517 : Blo 175800 190517 := bbase (se 5 (by rfl) ⟨8930, by rfl⟩ : syracuseStep 190517 = 17861) (by norm_num)
theorem B845909 : Blo 175800 845909 := bbase (se 8 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 845909 = 9913) (by norm_num)
theorem B223337 : Blo 175800 223337 := bbase (se 2 (by rfl) ⟨83751, by rfl⟩ : syracuseStep 223337 = 167503) (by norm_num)
theorem B256117 : Blo 175800 256117 := bbase (se 5 (by rfl) ⟨12005, by rfl⟩ : syracuseStep 256117 = 24011) (by norm_num)
theorem B452749 : Blo 175800 452749 := bbase (se 3 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 452749 = 169781) (by norm_num)
theorem B223393 : Blo 175800 223393 := bbase (se 2 (by rfl) ⟨83772, by rfl⟩ : syracuseStep 223393 = 167545) (by norm_num)
theorem B452861 : Blo 175800 452861 := bbase (se 3 (by rfl) ⟨84911, by rfl⟩ : syracuseStep 452861 = 169823) (by norm_num)
theorem B223489 : Blo 175800 223489 := bbase (se 2 (by rfl) ⟨83808, by rfl⟩ : syracuseStep 223489 = 167617) (by norm_num)
theorem B190765 : Blo 175800 190765 := bbase (se 3 (by rfl) ⟨35768, by rfl⟩ : syracuseStep 190765 = 71537) (by norm_num)
theorem B223661 : Blo 175800 223661 := bbase (se 3 (by rfl) ⟨41936, by rfl⟩ : syracuseStep 223661 = 83873) (by norm_num)
theorem B453053 : Blo 175800 453053 := bbase (se 3 (by rfl) ⟨84947, by rfl⟩ : syracuseStep 453053 = 169895) (by norm_num)
theorem B223717 : Blo 175800 223717 := bbase (se 4 (by rfl) ⟨20973, by rfl⟩ : syracuseStep 223717 = 41947) (by norm_num)
theorem B223813 : Blo 175800 223813 := bbase (se 4 (by rfl) ⟨20982, by rfl⟩ : syracuseStep 223813 = 41965) (by norm_num)
theorem B813685 : Blo 175800 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B191209 : Blo 175800 191209 := bbase (se 2 (by rfl) ⟨71703, by rfl⟩ : syracuseStep 191209 = 143407) (by norm_num)
theorem B223985 : Blo 175800 223985 := bbase (se 2 (by rfl) ⟨83994, by rfl⟩ : syracuseStep 223985 = 167989) (by norm_num)
theorem B453397 : Blo 175800 453397 := bbase (se 6 (by rfl) ⟨10626, by rfl⟩ : syracuseStep 453397 = 21253) (by norm_num)
theorem B191269 : Blo 175800 191269 := bbase (se 4 (by rfl) ⟨17931, by rfl⟩ : syracuseStep 191269 = 35863) (by norm_num)
theorem B224041 : Blo 175800 224041 := bbase (se 2 (by rfl) ⟨84015, by rfl⟩ : syracuseStep 224041 = 168031) (by norm_num)
theorem B453509 : Blo 175800 453509 := bbase (se 4 (by rfl) ⟨42516, by rfl⟩ : syracuseStep 453509 = 85033) (by norm_num)
theorem B224137 : Blo 175800 224137 := bbase (se 2 (by rfl) ⟨84051, by rfl⟩ : syracuseStep 224137 = 168103) (by norm_num)
theorem B224309 : Blo 175800 224309 := bbase (se 5 (by rfl) ⟨10514, by rfl⟩ : syracuseStep 224309 = 21029) (by norm_num)
theorem B453701 : Blo 175800 453701 := bbase (se 4 (by rfl) ⟨42534, by rfl⟩ : syracuseStep 453701 = 85069) (by norm_num)
theorem B191585 : Blo 175800 191585 := bbase (se 2 (by rfl) ⟨71844, by rfl⟩ : syracuseStep 191585 = 143689) (by norm_num)
theorem B224365 : Blo 175800 224365 := bbase (se 3 (by rfl) ⟨42068, by rfl⟩ : syracuseStep 224365 = 84137) (by norm_num)
theorem B257197 : Blo 175800 257197 := bbase (se 3 (by rfl) ⟨48224, by rfl⟩ : syracuseStep 257197 = 96449) (by norm_num)
theorem B224461 : Blo 175800 224461 := bbase (se 3 (by rfl) ⟨42086, by rfl⟩ : syracuseStep 224461 = 84173) (by norm_num)
theorem B224633 : Blo 175800 224633 := bbase (se 2 (by rfl) ⟨84237, by rfl⟩ : syracuseStep 224633 = 168475) (by norm_num)
theorem B454045 : Blo 175800 454045 := bbase (se 3 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 454045 = 170267) (by norm_num)
theorem B224689 : Blo 175800 224689 := bbase (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) (by norm_num)
theorem B454157 : Blo 175800 454157 := bbase (se 3 (by rfl) ⟨85154, by rfl⟩ : syracuseStep 454157 = 170309) (by norm_num)
theorem B224785 : Blo 175800 224785 := bbase (se 2 (by rfl) ⟨84294, by rfl⟩ : syracuseStep 224785 = 168589) (by norm_num)
theorem B192065 : Blo 175800 192065 := bbase (se 2 (by rfl) ⟨72024, by rfl⟩ : syracuseStep 192065 = 144049) (by norm_num)
theorem B224957 : Blo 175800 224957 := bbase (se 3 (by rfl) ⟨42179, by rfl⟩ : syracuseStep 224957 = 84359) (by norm_num)
theorem B454349 : Blo 175800 454349 := bbase (se 3 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 454349 = 170381) (by norm_num)
theorem B454373 : Blo 175800 454373 := bbase (se 4 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 454373 = 85195) (by norm_num)
theorem B257773 : Blo 175800 257773 := bbase (se 3 (by rfl) ⟨48332, by rfl⟩ : syracuseStep 257773 = 96665) (by norm_num)
theorem B225013 : Blo 175800 225013 := bbase (se 5 (by rfl) ⟨10547, by rfl⟩ : syracuseStep 225013 = 21095) (by norm_num)
theorem B913157 : Blo 175800 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B323357 : Blo 175800 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B225109 : Blo 175800 225109 := bbase (se 9 (by rfl) ⟨659, by rfl⟩ : syracuseStep 225109 = 1319) (by norm_num)
theorem B323437 : Blo 175800 323437 := bbase (se 3 (by rfl) ⟨60644, by rfl⟩ : syracuseStep 323437 = 121289) (by norm_num)
theorem B815093 : Blo 175800 815093 := bbase (se 5 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 815093 = 76415) (by norm_num)
theorem B225281 : Blo 175800 225281 := bbase (se 2 (by rfl) ⟨84480, by rfl⟩ : syracuseStep 225281 = 168961) (by norm_num)
theorem B454693 : Blo 175800 454693 := bbase (se 4 (by rfl) ⟨42627, by rfl⟩ : syracuseStep 454693 = 85255) (by norm_num)
theorem B225337 : Blo 175800 225337 := bbase (se 2 (by rfl) ⟨84501, by rfl⟩ : syracuseStep 225337 = 169003) (by norm_num)
theorem B323669 : Blo 175800 323669 := bbase (se 8 (by rfl) ⟨1896, by rfl⟩ : syracuseStep 323669 = 3793) (by norm_num)
theorem B454805 : Blo 175800 454805 := bbase (se 6 (by rfl) ⟨10659, by rfl⟩ : syracuseStep 454805 = 21319) (by norm_num)
theorem B225433 : Blo 175800 225433 := bbase (se 2 (by rfl) ⟨84537, by rfl⟩ : syracuseStep 225433 = 169075) (by norm_num)
theorem B913589 : Blo 175800 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B225605 : Blo 175800 225605 := bbase (se 4 (by rfl) ⟨21150, by rfl⟩ : syracuseStep 225605 = 42301) (by norm_num)
theorem B454997 : Blo 175800 454997 := bbase (se 10 (by rfl) ⟨666, by rfl⟩ : syracuseStep 454997 = 1333) (by norm_num)
theorem B225661 : Blo 175800 225661 := bbase (se 3 (by rfl) ⟨42311, by rfl⟩ : syracuseStep 225661 = 84623) (by norm_num)
theorem B225757 : Blo 175800 225757 := bbase (se 3 (by rfl) ⟨42329, by rfl⟩ : syracuseStep 225757 = 84659) (by norm_num)
theorem B356933 : Blo 175800 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B225929 : Blo 175800 225929 := bbase (se 2 (by rfl) ⟨84723, by rfl⟩ : syracuseStep 225929 = 169447) (by norm_num)
theorem B225985 : Blo 175800 225985 := bbase (se 2 (by rfl) ⟨84744, by rfl⟩ : syracuseStep 225985 = 169489) (by norm_num)
theorem B193313 : Blo 175800 193313 := bbase (se 2 (by rfl) ⟨72492, by rfl⟩ : syracuseStep 193313 = 144985) (by norm_num)
theorem B226081 : Blo 175800 226081 := bbase (se 2 (by rfl) ⟨84780, by rfl⟩ : syracuseStep 226081 = 169561) (by norm_num)
theorem B848677 : Blo 175800 848677 := bbase (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) (by norm_num)
theorem B226201 : Blo 175800 226201 := bbase (se 2 (by rfl) ⟨84825, by rfl⟩ : syracuseStep 226201 = 169651) (by norm_num)
theorem B226253 : Blo 175800 226253 := bbase (se 3 (by rfl) ⟨42422, by rfl⟩ : syracuseStep 226253 = 84845) (by norm_num)
theorem B226309 : Blo 175800 226309 := bbase (se 4 (by rfl) ⟨21216, by rfl⟩ : syracuseStep 226309 = 42433) (by norm_num)
theorem B226405 : Blo 175800 226405 := bbase (se 4 (by rfl) ⟨21225, by rfl⟩ : syracuseStep 226405 = 42451) (by norm_num)
theorem B259213 : Blo 175800 259213 := bbase (se 3 (by rfl) ⟨48602, by rfl⟩ : syracuseStep 259213 = 97205) (by norm_num)
theorem B226577 : Blo 175800 226577 := bbase (se 2 (by rfl) ⟨84966, by rfl⟩ : syracuseStep 226577 = 169933) (by norm_num)
theorem B226633 : Blo 175800 226633 := bbase (se 2 (by rfl) ⟨84987, by rfl⟩ : syracuseStep 226633 = 169975) (by norm_num)
theorem B423253 : Blo 175800 423253 := bbase (se 13 (by rfl) ⟨77, by rfl⟩ : syracuseStep 423253 = 155) (by norm_num)
theorem B3437909 : Blo 175800 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B423301 : Blo 175800 423301 := bbase (se 4 (by rfl) ⟨39684, by rfl⟩ : syracuseStep 423301 = 79369) (by norm_num)
theorem B226729 : Blo 175800 226729 := bbase (se 2 (by rfl) ⟨85023, by rfl⟩ : syracuseStep 226729 = 170047) (by norm_num)
theorem B292405 : Blo 175800 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B226901 : Blo 175800 226901 := bbase (se 8 (by rfl) ⟨1329, by rfl⟩ : syracuseStep 226901 = 2659) (by norm_num)
theorem B226957 : Blo 175800 226957 := bbase (se 3 (by rfl) ⟨42554, by rfl⟩ : syracuseStep 226957 = 85109) (by norm_num)
theorem B227053 : Blo 175800 227053 := bbase (se 3 (by rfl) ⟨42572, by rfl⟩ : syracuseStep 227053 = 85145) (by norm_num)
theorem B456445 : Blo 175800 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B227225 : Blo 175800 227225 := bbase (se 2 (by rfl) ⟨85209, by rfl⟩ : syracuseStep 227225 = 170419) (by norm_num)
theorem B227281 : Blo 175800 227281 := bbase (se 2 (by rfl) ⟨85230, by rfl⟩ : syracuseStep 227281 = 170461) (by norm_num)
theorem B423917 : Blo 175800 423917 := bbase (se 3 (by rfl) ⟨79484, by rfl⟩ : syracuseStep 423917 = 158969) (by norm_num)
theorem B227377 : Blo 175800 227377 := bbase (se 2 (by rfl) ⟨85266, by rfl⟩ : syracuseStep 227377 = 170533) (by norm_num)
theorem B751781 : Blo 175800 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B227549 : Blo 175800 227549 := bbase (se 3 (by rfl) ⟨42665, by rfl⟩ : syracuseStep 227549 = 85331) (by norm_num)
theorem B424261 : Blo 175800 424261 := bbase (se 4 (by rfl) ⟨39774, by rfl⟩ : syracuseStep 424261 = 79549) (by norm_num)
theorem B719189 : Blo 175800 719189 := bbase (se 10 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 719189 = 2107) (by norm_num)
theorem B1341845 : Blo 175800 1341845 := bbase (se 6 (by rfl) ⟨31449, by rfl⟩ : syracuseStep 1341845 = 62899) (by norm_num)
theorem B1505749 : Blo 175800 1505749 := bbase (se 7 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 1505749 = 35291) (by norm_num)
theorem B424493 : Blo 175800 424493 := bbase (se 3 (by rfl) ⟨79592, by rfl⟩ : syracuseStep 424493 = 159185) (by norm_num)
theorem B424685 : Blo 175800 424685 := bbase (se 3 (by rfl) ⟨79628, by rfl⟩ : syracuseStep 424685 = 159257) (by norm_num)
theorem B1014677 : Blo 175800 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B228253 : Blo 175800 228253 := bbase (se 3 (by rfl) ⟨42797, by rfl⟩ : syracuseStep 228253 = 85595) (by norm_num)
theorem B687109 : Blo 175800 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B424973 : Blo 175800 424973 := bbase (se 3 (by rfl) ⟨79682, by rfl⟩ : syracuseStep 424973 = 159365) (by norm_num)
theorem B752773 : Blo 175800 752773 := bbase (se 4 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 752773 = 141145) (by norm_num)
theorem B458005 : Blo 175800 458005 := bbase (se 6 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 458005 = 21469) (by norm_num)
theorem B359869 : Blo 175800 359869 := bbase (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) (by norm_num)
theorem B720485 : Blo 175800 720485 := bbase (se 4 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 720485 = 135091) (by norm_num)
theorem B491285 : Blo 175800 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B360389 : Blo 175800 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B229603 : Blo 175800 229603 := bstep (se 1 (by rfl) ⟨172202, by rfl⟩ : syracuseStep 229603 = 344405) B344405
theorem B492227 : Blo 175800 492227 := bstep (se 1 (by rfl) ⟨369170, by rfl⟩ : syracuseStep 492227 = 738341) B738341
theorem B3211973 : Blo 175800 3211973 := bstep (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) B602245
theorem B197779 : Blo 175800 197779 := bstep (se 1 (by rfl) ⟨148334, by rfl⟩ : syracuseStep 197779 = 296669) B296669
theorem B197923 : Blo 175800 197923 := bstep (se 1 (by rfl) ⟨148442, by rfl⟩ : syracuseStep 197923 = 296885) B296885
theorem B1017137 : Blo 175800 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B755021 : Blo 175800 755021 := bstep (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) B283133
theorem B9733517 : Blo 175800 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B198067 : Blo 175800 198067 := bstep (se 1 (by rfl) ⟨148550, by rfl⟩ : syracuseStep 198067 = 297101) B297101
theorem B1148357 : Blo 175800 1148357 := bstep (se 4 (by rfl) ⟨107658, by rfl⟩ : syracuseStep 1148357 = 215317) B215317
theorem B951821 : Blo 175800 951821 := bstep (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) B356933
theorem B263729 : Blo 175800 263729 := bstep (se 2 (by rfl) ⟨98898, by rfl⟩ : syracuseStep 263729 = 197797) B197797
theorem B263747 : Blo 175800 263747 := bstep (se 1 (by rfl) ⟨197810, by rfl⟩ : syracuseStep 263747 = 395621) B395621
theorem B198211 : Blo 175800 198211 := bstep (se 1 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 198211 = 297317) B297317
theorem B263777 : Blo 175800 263777 := bstep (se 2 (by rfl) ⟨98916, by rfl⟩ : syracuseStep 263777 = 197833) B197833
theorem B263795 : Blo 175800 263795 := bstep (se 1 (by rfl) ⟨197846, by rfl⟩ : syracuseStep 263795 = 395693) B395693
theorem B263825 : Blo 175800 263825 := bstep (se 2 (by rfl) ⟨98934, by rfl⟩ : syracuseStep 263825 = 197869) B197869
theorem B263843 : Blo 175800 263843 := bstep (se 1 (by rfl) ⟨197882, by rfl⟩ : syracuseStep 263843 = 395765) B395765
theorem B263873 : Blo 175800 263873 := bstep (se 2 (by rfl) ⟨98952, by rfl⟩ : syracuseStep 263873 = 197905) B197905
theorem B2262725 : Blo 175800 2262725 := bstep (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) B424261
theorem B755405 : Blo 175800 755405 := bstep (se 3 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 755405 = 283277) B283277
theorem B263891 : Blo 175800 263891 := bstep (se 1 (by rfl) ⟨197918, by rfl⟩ : syracuseStep 263891 = 395837) B395837
theorem B198355 : Blo 175800 198355 := bstep (se 1 (by rfl) ⟨148766, by rfl⟩ : syracuseStep 198355 = 297533) B297533
theorem B296689 : Blo 175800 296689 := bstep (se 2 (by rfl) ⟨111258, by rfl⟩ : syracuseStep 296689 = 222517) B222517
theorem B263921 : Blo 175800 263921 := bstep (se 2 (by rfl) ⟨98970, by rfl⟩ : syracuseStep 263921 = 197941) B197941
theorem B263939 : Blo 175800 263939 := bstep (se 1 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 263939 = 395909) B395909
theorem B296723 : Blo 175800 296723 := bstep (se 1 (by rfl) ⟨222542, by rfl⟩ : syracuseStep 296723 = 445085) B445085
theorem B263969 : Blo 175800 263969 := bstep (se 2 (by rfl) ⟨98988, by rfl⟩ : syracuseStep 263969 = 197977) B197977
theorem B263987 : Blo 175800 263987 := bstep (se 1 (by rfl) ⟨197990, by rfl⟩ : syracuseStep 263987 = 395981) B395981
theorem B264017 : Blo 175800 264017 := bstep (se 2 (by rfl) ⟨99006, by rfl⟩ : syracuseStep 264017 = 198013) B198013
theorem B264035 : Blo 175800 264035 := bstep (se 1 (by rfl) ⟨198026, by rfl⟩ : syracuseStep 264035 = 396053) B396053
theorem B198499 : Blo 175800 198499 := bstep (se 1 (by rfl) ⟨148874, by rfl⟩ : syracuseStep 198499 = 297749) B297749
theorem B264065 : Blo 175800 264065 := bstep (se 2 (by rfl) ⟨99024, by rfl⟩ : syracuseStep 264065 = 198049) B198049
theorem B296851 : Blo 175800 296851 := bstep (se 1 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 296851 = 445277) B445277
theorem B264083 : Blo 175800 264083 := bstep (se 1 (by rfl) ⟨198062, by rfl⟩ : syracuseStep 264083 = 396125) B396125
theorem B264113 : Blo 175800 264113 := bstep (se 2 (by rfl) ⟨99042, by rfl⟩ : syracuseStep 264113 = 198085) B198085
theorem B264131 : Blo 175800 264131 := bstep (se 1 (by rfl) ⟨198098, by rfl⟩ : syracuseStep 264131 = 396197) B396197
theorem B264161 : Blo 175800 264161 := bstep (se 2 (by rfl) ⟨99060, by rfl⟩ : syracuseStep 264161 = 198121) B198121
theorem B264179 : Blo 175800 264179 := bstep (se 1 (by rfl) ⟨198134, by rfl⟩ : syracuseStep 264179 = 396269) B396269
theorem B198643 : Blo 175800 198643 := bstep (se 1 (by rfl) ⟨148982, by rfl⟩ : syracuseStep 198643 = 297965) B297965
theorem B264209 : Blo 175800 264209 := bstep (se 2 (by rfl) ⟨99078, by rfl⟩ : syracuseStep 264209 = 198157) B198157
theorem B296993 : Blo 175800 296993 := bstep (se 2 (by rfl) ⟨111372, by rfl⟩ : syracuseStep 296993 = 222745) B222745
theorem B264227 : Blo 175800 264227 := bstep (se 1 (by rfl) ⟨198170, by rfl⟩ : syracuseStep 264227 = 396341) B396341
theorem B264257 : Blo 175800 264257 := bstep (se 2 (by rfl) ⟨99096, by rfl⟩ : syracuseStep 264257 = 198193) B198193
theorem B264275 : Blo 175800 264275 := bstep (se 1 (by rfl) ⟨198206, by rfl⟩ : syracuseStep 264275 = 396413) B396413
theorem B264305 : Blo 175800 264305 := bstep (se 2 (by rfl) ⟨99114, by rfl⟩ : syracuseStep 264305 = 198229) B198229
theorem B264323 : Blo 175800 264323 := bstep (se 1 (by rfl) ⟨198242, by rfl⟩ : syracuseStep 264323 = 396485) B396485
theorem B198787 : Blo 175800 198787 := bstep (se 1 (by rfl) ⟨149090, by rfl⟩ : syracuseStep 198787 = 298181) B298181
theorem B297121 : Blo 175800 297121 := bstep (se 2 (by rfl) ⟨111420, by rfl⟩ : syracuseStep 297121 = 222841) B222841
theorem B264353 : Blo 175800 264353 := bstep (se 2 (by rfl) ⟨99132, by rfl⟩ : syracuseStep 264353 = 198265) B198265
theorem B264371 : Blo 175800 264371 := bstep (se 1 (by rfl) ⟨198278, by rfl⟩ : syracuseStep 264371 = 396557) B396557
theorem B297155 : Blo 175800 297155 := bstep (se 1 (by rfl) ⟨222866, by rfl⟩ : syracuseStep 297155 = 445733) B445733
theorem B1345733 : Blo 175800 1345733 := bstep (se 4 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 1345733 = 252325) B252325
theorem B264401 : Blo 175800 264401 := bstep (se 2 (by rfl) ⟨99150, by rfl⟩ : syracuseStep 264401 = 198301) B198301
theorem B264419 : Blo 175800 264419 := bstep (se 1 (by rfl) ⟨198314, by rfl⟩ : syracuseStep 264419 = 396629) B396629
theorem B362723 : Blo 175800 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B264449 : Blo 175800 264449 := bstep (se 2 (by rfl) ⟨99168, by rfl⟩ : syracuseStep 264449 = 198337) B198337
theorem B264467 : Blo 175800 264467 := bstep (se 1 (by rfl) ⟨198350, by rfl⟩ : syracuseStep 264467 = 396701) B396701
theorem B198931 : Blo 175800 198931 := bstep (se 1 (by rfl) ⟨149198, by rfl⟩ : syracuseStep 198931 = 298397) B298397
theorem B264497 : Blo 175800 264497 := bstep (se 2 (by rfl) ⟨99186, by rfl⟩ : syracuseStep 264497 = 198373) B198373
theorem B297283 : Blo 175800 297283 := bstep (se 1 (by rfl) ⟨222962, by rfl⟩ : syracuseStep 297283 = 445925) B445925
theorem B264515 : Blo 175800 264515 := bstep (se 1 (by rfl) ⟨198386, by rfl⟩ : syracuseStep 264515 = 396773) B396773
theorem B264545 : Blo 175800 264545 := bstep (se 2 (by rfl) ⟨99204, by rfl⟩ : syracuseStep 264545 = 198409) B198409
theorem B264563 : Blo 175800 264563 := bstep (se 1 (by rfl) ⟨198422, by rfl⟩ : syracuseStep 264563 = 396845) B396845
theorem B264593 : Blo 175800 264593 := bstep (se 2 (by rfl) ⟨99222, by rfl⟩ : syracuseStep 264593 = 198445) B198445
theorem B264611 : Blo 175800 264611 := bstep (se 1 (by rfl) ⟨198458, by rfl⟩ : syracuseStep 264611 = 396917) B396917
theorem B199075 : Blo 175800 199075 := bstep (se 1 (by rfl) ⟨149306, by rfl⟩ : syracuseStep 199075 = 298613) B298613
theorem B264641 : Blo 175800 264641 := bstep (se 2 (by rfl) ⟨99240, by rfl⟩ : syracuseStep 264641 = 198481) B198481
theorem B395729 : Blo 175800 395729 := bstep (se 2 (by rfl) ⟨148398, by rfl⟩ : syracuseStep 395729 = 296797) B296797
theorem B297425 : Blo 175800 297425 := bstep (se 2 (by rfl) ⟨111534, by rfl⟩ : syracuseStep 297425 = 223069) B223069
theorem B264659 : Blo 175800 264659 := bstep (se 1 (by rfl) ⟨198494, by rfl⟩ : syracuseStep 264659 = 396989) B396989
theorem B395747 : Blo 175800 395747 := bstep (se 1 (by rfl) ⟨296810, by rfl⟩ : syracuseStep 395747 = 593621) B593621
theorem B264689 : Blo 175800 264689 := bstep (se 2 (by rfl) ⟨99258, by rfl⟩ : syracuseStep 264689 = 198517) B198517
theorem B264707 : Blo 175800 264707 := bstep (se 1 (by rfl) ⟨198530, by rfl⟩ : syracuseStep 264707 = 397061) B397061
theorem B264737 : Blo 175800 264737 := bstep (se 2 (by rfl) ⟨99276, by rfl⟩ : syracuseStep 264737 = 198553) B198553
theorem B264755 : Blo 175800 264755 := bstep (se 1 (by rfl) ⟨198566, by rfl⟩ : syracuseStep 264755 = 397133) B397133
theorem B199219 : Blo 175800 199219 := bstep (se 1 (by rfl) ⟨149414, by rfl⟩ : syracuseStep 199219 = 298829) B298829
theorem B297553 : Blo 175800 297553 := bstep (se 2 (by rfl) ⟨111582, by rfl⟩ : syracuseStep 297553 = 223165) B223165
theorem B264785 : Blo 175800 264785 := bstep (se 2 (by rfl) ⟨99294, by rfl⟩ : syracuseStep 264785 = 198589) B198589
theorem B264803 : Blo 175800 264803 := bstep (se 1 (by rfl) ⟨198602, by rfl⟩ : syracuseStep 264803 = 397205) B397205
theorem B297587 : Blo 175800 297587 := bstep (se 1 (by rfl) ⟨223190, by rfl⟩ : syracuseStep 297587 = 446381) B446381
theorem B264833 : Blo 175800 264833 := bstep (se 2 (by rfl) ⟨99312, by rfl⟩ : syracuseStep 264833 = 198625) B198625
theorem B264851 : Blo 175800 264851 := bstep (se 1 (by rfl) ⟨198638, by rfl⟩ : syracuseStep 264851 = 397277) B397277
theorem B264881 : Blo 175800 264881 := bstep (se 2 (by rfl) ⟨99330, by rfl⟩ : syracuseStep 264881 = 198661) B198661
theorem B264899 : Blo 175800 264899 := bstep (se 1 (by rfl) ⟨198674, by rfl⟩ : syracuseStep 264899 = 397349) B397349
theorem B199363 : Blo 175800 199363 := bstep (se 1 (by rfl) ⟨149522, by rfl⟩ : syracuseStep 199363 = 299045) B299045
theorem B264929 : Blo 175800 264929 := bstep (se 2 (by rfl) ⟨99348, by rfl⟩ : syracuseStep 264929 = 198697) B198697
theorem B1018595 : Blo 175800 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B396017 : Blo 175800 396017 := bstep (se 2 (by rfl) ⟨148506, by rfl⟩ : syracuseStep 396017 = 297013) B297013
theorem B297715 : Blo 175800 297715 := bstep (se 1 (by rfl) ⟨223286, by rfl⟩ : syracuseStep 297715 = 446573) B446573
theorem B264947 : Blo 175800 264947 := bstep (se 1 (by rfl) ⟨198710, by rfl⟩ : syracuseStep 264947 = 397421) B397421
theorem B396035 : Blo 175800 396035 := bstep (se 1 (by rfl) ⟨297026, by rfl⟩ : syracuseStep 396035 = 594053) B594053
theorem B264977 : Blo 175800 264977 := bstep (se 2 (by rfl) ⟨99366, by rfl⟩ : syracuseStep 264977 = 198733) B198733
theorem B264995 : Blo 175800 264995 := bstep (se 1 (by rfl) ⟨198746, by rfl⟩ : syracuseStep 264995 = 397493) B397493
theorem B265025 : Blo 175800 265025 := bstep (se 2 (by rfl) ⟨99384, by rfl⟩ : syracuseStep 265025 = 198769) B198769
theorem B1084229 : Blo 175800 1084229 := bstep (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) B203293
theorem B265043 : Blo 175800 265043 := bstep (se 1 (by rfl) ⟨198782, by rfl⟩ : syracuseStep 265043 = 397565) B397565
theorem B199507 : Blo 175800 199507 := bstep (se 1 (by rfl) ⟨149630, by rfl⟩ : syracuseStep 199507 = 299261) B299261
theorem B265073 : Blo 175800 265073 := bstep (se 2 (by rfl) ⟨99402, by rfl⟩ : syracuseStep 265073 = 198805) B198805
theorem B297857 : Blo 175800 297857 := bstep (se 2 (by rfl) ⟨111696, by rfl⟩ : syracuseStep 297857 = 223393) B223393
theorem B265091 : Blo 175800 265091 := bstep (se 1 (by rfl) ⟨198818, by rfl⟩ : syracuseStep 265091 = 397637) B397637
theorem B265121 : Blo 175800 265121 := bstep (se 2 (by rfl) ⟨99420, by rfl⟩ : syracuseStep 265121 = 198841) B198841
theorem B265139 : Blo 175800 265139 := bstep (se 1 (by rfl) ⟨198854, by rfl⟩ : syracuseStep 265139 = 397709) B397709
theorem B265169 : Blo 175800 265169 := bstep (se 2 (by rfl) ⟨99438, by rfl⟩ : syracuseStep 265169 = 198877) B198877
theorem B265187 : Blo 175800 265187 := bstep (se 1 (by rfl) ⟨198890, by rfl⟩ : syracuseStep 265187 = 397781) B397781
theorem B199651 : Blo 175800 199651 := bstep (se 1 (by rfl) ⟨149738, by rfl⟩ : syracuseStep 199651 = 299477) B299477
theorem B297985 : Blo 175800 297985 := bstep (se 2 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 297985 = 223489) B223489
theorem B265217 : Blo 175800 265217 := bstep (se 2 (by rfl) ⟨99456, by rfl⟩ : syracuseStep 265217 = 198913) B198913
theorem B396305 : Blo 175800 396305 := bstep (se 2 (by rfl) ⟨148614, by rfl⟩ : syracuseStep 396305 = 297229) B297229
theorem B265235 : Blo 175800 265235 := bstep (se 1 (by rfl) ⟨198926, by rfl⟩ : syracuseStep 265235 = 397853) B397853
theorem B396323 : Blo 175800 396323 := bstep (se 1 (by rfl) ⟨297242, by rfl⟩ : syracuseStep 396323 = 594485) B594485
theorem B298019 : Blo 175800 298019 := bstep (se 1 (by rfl) ⟨223514, by rfl⟩ : syracuseStep 298019 = 447029) B447029
theorem B265265 : Blo 175800 265265 := bstep (se 2 (by rfl) ⟨99474, by rfl⟩ : syracuseStep 265265 = 198949) B198949
theorem B265283 : Blo 175800 265283 := bstep (se 1 (by rfl) ⟨198962, by rfl⟩ : syracuseStep 265283 = 397925) B397925
theorem B265313 : Blo 175800 265313 := bstep (se 2 (by rfl) ⟨99492, by rfl⟩ : syracuseStep 265313 = 198985) B198985
theorem B265331 : Blo 175800 265331 := bstep (se 1 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 265331 = 397997) B397997
theorem B199795 : Blo 175800 199795 := bstep (se 1 (by rfl) ⟨149846, by rfl⟩ : syracuseStep 199795 = 299693) B299693
theorem B265361 : Blo 175800 265361 := bstep (se 2 (by rfl) ⟨99510, by rfl⟩ : syracuseStep 265361 = 199021) B199021
theorem B298147 : Blo 175800 298147 := bstep (se 1 (by rfl) ⟨223610, by rfl⟩ : syracuseStep 298147 = 447221) B447221
theorem B265379 : Blo 175800 265379 := bstep (se 1 (by rfl) ⟨199034, by rfl⟩ : syracuseStep 265379 = 398069) B398069
theorem B265409 : Blo 175800 265409 := bstep (se 2 (by rfl) ⟨99528, by rfl⟩ : syracuseStep 265409 = 199057) B199057
theorem B265427 : Blo 175800 265427 := bstep (se 1 (by rfl) ⟨199070, by rfl⟩ : syracuseStep 265427 = 398141) B398141
theorem B265457 : Blo 175800 265457 := bstep (se 2 (by rfl) ⟨99546, by rfl⟩ : syracuseStep 265457 = 199093) B199093
theorem B265475 : Blo 175800 265475 := bstep (se 1 (by rfl) ⟨199106, by rfl⟩ : syracuseStep 265475 = 398213) B398213
theorem B199939 : Blo 175800 199939 := bstep (se 1 (by rfl) ⟨149954, by rfl⟩ : syracuseStep 199939 = 299909) B299909
theorem B265505 : Blo 175800 265505 := bstep (se 2 (by rfl) ⟨99564, by rfl⟩ : syracuseStep 265505 = 199129) B199129
theorem B396593 : Blo 175800 396593 := bstep (se 2 (by rfl) ⟨148722, by rfl⟩ : syracuseStep 396593 = 297445) B297445
theorem B298289 : Blo 175800 298289 := bstep (se 2 (by rfl) ⟨111858, by rfl⟩ : syracuseStep 298289 = 223717) B223717
theorem B265523 : Blo 175800 265523 := bstep (se 1 (by rfl) ⟨199142, by rfl⟩ : syracuseStep 265523 = 398285) B398285
theorem B396611 : Blo 175800 396611 := bstep (se 1 (by rfl) ⟨297458, by rfl⟩ : syracuseStep 396611 = 594917) B594917
theorem B265553 : Blo 175800 265553 := bstep (se 2 (by rfl) ⟨99582, by rfl⟩ : syracuseStep 265553 = 199165) B199165
theorem B265571 : Blo 175800 265571 := bstep (se 1 (by rfl) ⟨199178, by rfl⟩ : syracuseStep 265571 = 398357) B398357
theorem B265601 : Blo 175800 265601 := bstep (se 2 (by rfl) ⟨99600, by rfl⟩ : syracuseStep 265601 = 199201) B199201
theorem B265619 : Blo 175800 265619 := bstep (se 1 (by rfl) ⟨199214, by rfl⟩ : syracuseStep 265619 = 398429) B398429
theorem B200083 : Blo 175800 200083 := bstep (se 1 (by rfl) ⟨150062, by rfl⟩ : syracuseStep 200083 = 300125) B300125
theorem B298417 : Blo 175800 298417 := bstep (se 2 (by rfl) ⟨111906, by rfl⟩ : syracuseStep 298417 = 223813) B223813
theorem B265649 : Blo 175800 265649 := bstep (se 2 (by rfl) ⟨99618, by rfl⟩ : syracuseStep 265649 = 199237) B199237
theorem B265667 : Blo 175800 265667 := bstep (se 1 (by rfl) ⟨199250, by rfl⟩ : syracuseStep 265667 = 398501) B398501
theorem B298451 : Blo 175800 298451 := bstep (se 1 (by rfl) ⟨223838, by rfl⟩ : syracuseStep 298451 = 447677) B447677
theorem B265697 : Blo 175800 265697 := bstep (se 2 (by rfl) ⟨99636, by rfl⟩ : syracuseStep 265697 = 199273) B199273
theorem B1084913 : Blo 175800 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B265715 : Blo 175800 265715 := bstep (se 1 (by rfl) ⟨199286, by rfl⟩ : syracuseStep 265715 = 398573) B398573
theorem B265745 : Blo 175800 265745 := bstep (se 2 (by rfl) ⟨99654, by rfl⟩ : syracuseStep 265745 = 199309) B199309
theorem B265763 : Blo 175800 265763 := bstep (se 1 (by rfl) ⟨199322, by rfl⟩ : syracuseStep 265763 = 398645) B398645
theorem B200227 : Blo 175800 200227 := bstep (se 1 (by rfl) ⟨150170, by rfl⟩ : syracuseStep 200227 = 300341) B300341
theorem B265793 : Blo 175800 265793 := bstep (se 2 (by rfl) ⟨99672, by rfl⟩ : syracuseStep 265793 = 199345) B199345
theorem B396881 : Blo 175800 396881 := bstep (se 2 (by rfl) ⟨148830, by rfl⟩ : syracuseStep 396881 = 297661) B297661
theorem B298579 : Blo 175800 298579 := bstep (se 1 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 298579 = 447869) B447869
theorem B265811 : Blo 175800 265811 := bstep (se 1 (by rfl) ⟨199358, by rfl⟩ : syracuseStep 265811 = 398717) B398717
theorem B396899 : Blo 175800 396899 := bstep (se 1 (by rfl) ⟨297674, by rfl⟩ : syracuseStep 396899 = 595349) B595349
theorem B265841 : Blo 175800 265841 := bstep (se 2 (by rfl) ⟨99690, by rfl⟩ : syracuseStep 265841 = 199381) B199381
theorem B265859 : Blo 175800 265859 := bstep (se 1 (by rfl) ⟨199394, by rfl⟩ : syracuseStep 265859 = 398789) B398789
theorem B265889 : Blo 175800 265889 := bstep (se 2 (by rfl) ⟨99708, by rfl⟩ : syracuseStep 265889 = 199417) B199417
theorem B265907 : Blo 175800 265907 := bstep (se 1 (by rfl) ⟨199430, by rfl⟩ : syracuseStep 265907 = 398861) B398861
theorem B200371 : Blo 175800 200371 := bstep (se 1 (by rfl) ⟨150278, by rfl⟩ : syracuseStep 200371 = 300557) B300557
theorem B265937 : Blo 175800 265937 := bstep (se 2 (by rfl) ⟨99726, by rfl⟩ : syracuseStep 265937 = 199453) B199453
theorem B298721 : Blo 175800 298721 := bstep (se 2 (by rfl) ⟨112020, by rfl⟩ : syracuseStep 298721 = 224041) B224041
theorem B265955 : Blo 175800 265955 := bstep (se 1 (by rfl) ⟨199466, by rfl⟩ : syracuseStep 265955 = 398933) B398933
theorem B265985 : Blo 175800 265985 := bstep (se 2 (by rfl) ⟨99744, by rfl⟩ : syracuseStep 265985 = 199489) B199489
theorem B266003 : Blo 175800 266003 := bstep (se 1 (by rfl) ⟨199502, by rfl⟩ : syracuseStep 266003 = 399005) B399005
theorem B266033 : Blo 175800 266033 := bstep (se 2 (by rfl) ⟨99762, by rfl⟩ : syracuseStep 266033 = 199525) B199525
theorem B266051 : Blo 175800 266051 := bstep (se 1 (by rfl) ⟨199538, by rfl⟩ : syracuseStep 266051 = 399077) B399077
theorem B200515 : Blo 175800 200515 := bstep (se 1 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 200515 = 300773) B300773
theorem B298849 : Blo 175800 298849 := bstep (se 2 (by rfl) ⟨112068, by rfl⟩ : syracuseStep 298849 = 224137) B224137
theorem B266081 : Blo 175800 266081 := bstep (se 2 (by rfl) ⟨99780, by rfl⟩ : syracuseStep 266081 = 199561) B199561
theorem B397169 : Blo 175800 397169 := bstep (se 2 (by rfl) ⟨148938, by rfl⟩ : syracuseStep 397169 = 297877) B297877
theorem B266099 : Blo 175800 266099 := bstep (se 1 (by rfl) ⟨199574, by rfl⟩ : syracuseStep 266099 = 399149) B399149
theorem B397187 : Blo 175800 397187 := bstep (se 1 (by rfl) ⟨297890, by rfl⟩ : syracuseStep 397187 = 595781) B595781
theorem B298883 : Blo 175800 298883 := bstep (se 1 (by rfl) ⟨224162, by rfl⟩ : syracuseStep 298883 = 448325) B448325
theorem B266129 : Blo 175800 266129 := bstep (se 2 (by rfl) ⟨99798, by rfl⟩ : syracuseStep 266129 = 199597) B199597
theorem B266147 : Blo 175800 266147 := bstep (se 1 (by rfl) ⟨199610, by rfl⟩ : syracuseStep 266147 = 399221) B399221
theorem B593837 : Blo 175800 593837 := bstep (se 3 (by rfl) ⟨111344, by rfl⟩ : syracuseStep 593837 = 222689) B222689
theorem B266177 : Blo 175800 266177 := bstep (se 2 (by rfl) ⟨99816, by rfl⟩ : syracuseStep 266177 = 199633) B199633
theorem B266195 : Blo 175800 266195 := bstep (se 1 (by rfl) ⟨199646, by rfl⟩ : syracuseStep 266195 = 399293) B399293
theorem B200659 : Blo 175800 200659 := bstep (se 1 (by rfl) ⟨150494, by rfl⟩ : syracuseStep 200659 = 300989) B300989
theorem B593891 : Blo 175800 593891 := bstep (se 1 (by rfl) ⟨445418, by rfl⟩ : syracuseStep 593891 = 890837) B890837
theorem B266225 : Blo 175800 266225 := bstep (se 2 (by rfl) ⟨99834, by rfl⟩ : syracuseStep 266225 = 199669) B199669
theorem B299011 : Blo 175800 299011 := bstep (se 1 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 299011 = 448517) B448517
theorem B266243 : Blo 175800 266243 := bstep (se 1 (by rfl) ⟨199682, by rfl⟩ : syracuseStep 266243 = 399365) B399365
theorem B331793 : Blo 175800 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B266273 : Blo 175800 266273 := bstep (se 2 (by rfl) ⟨99852, by rfl⟩ : syracuseStep 266273 = 199705) B199705
theorem B266291 : Blo 175800 266291 := bstep (se 1 (by rfl) ⟨199718, by rfl⟩ : syracuseStep 266291 = 399437) B399437
theorem B266321 : Blo 175800 266321 := bstep (se 2 (by rfl) ⟨99870, by rfl⟩ : syracuseStep 266321 = 199741) B199741
theorem B266339 : Blo 175800 266339 := bstep (se 1 (by rfl) ⟨199754, by rfl⟩ : syracuseStep 266339 = 399509) B399509
theorem B200803 : Blo 175800 200803 := bstep (se 1 (by rfl) ⟨150602, by rfl⟩ : syracuseStep 200803 = 301205) B301205
theorem B266369 : Blo 175800 266369 := bstep (se 2 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 266369 = 199777) B199777
theorem B397457 : Blo 175800 397457 := bstep (se 2 (by rfl) ⟨149046, by rfl⟩ : syracuseStep 397457 = 298093) B298093
theorem B299153 : Blo 175800 299153 := bstep (se 2 (by rfl) ⟨112182, by rfl⟩ : syracuseStep 299153 = 224365) B224365
theorem B266387 : Blo 175800 266387 := bstep (se 1 (by rfl) ⟨199790, by rfl⟩ : syracuseStep 266387 = 399581) B399581
theorem B397475 : Blo 175800 397475 := bstep (se 1 (by rfl) ⟨298106, by rfl⟩ : syracuseStep 397475 = 596213) B596213
theorem B266417 : Blo 175800 266417 := bstep (se 2 (by rfl) ⟨99906, by rfl⟩ : syracuseStep 266417 = 199813) B199813
theorem B266435 : Blo 175800 266435 := bstep (se 1 (by rfl) ⟨199826, by rfl⟩ : syracuseStep 266435 = 399653) B399653
theorem B266465 : Blo 175800 266465 := bstep (se 2 (by rfl) ⟨99924, by rfl⟩ : syracuseStep 266465 = 199849) B199849
theorem B594161 : Blo 175800 594161 := bstep (se 2 (by rfl) ⟨222810, by rfl⟩ : syracuseStep 594161 = 445621) B445621
theorem B266483 : Blo 175800 266483 := bstep (se 1 (by rfl) ⟨199862, by rfl⟩ : syracuseStep 266483 = 399725) B399725
theorem B200947 : Blo 175800 200947 := bstep (se 1 (by rfl) ⟨150710, by rfl⟩ : syracuseStep 200947 = 301421) B301421
theorem B299281 : Blo 175800 299281 := bstep (se 2 (by rfl) ⟨112230, by rfl⟩ : syracuseStep 299281 = 224461) B224461
theorem B266513 : Blo 175800 266513 := bstep (se 2 (by rfl) ⟨99942, by rfl⟩ : syracuseStep 266513 = 199885) B199885
theorem B266531 : Blo 175800 266531 := bstep (se 1 (by rfl) ⟨199898, by rfl⟩ : syracuseStep 266531 = 399797) B399797
theorem B299315 : Blo 175800 299315 := bstep (se 1 (by rfl) ⟨224486, by rfl⟩ : syracuseStep 299315 = 448973) B448973
theorem B266561 : Blo 175800 266561 := bstep (se 2 (by rfl) ⟨99960, by rfl⟩ : syracuseStep 266561 = 199921) B199921
theorem B266579 : Blo 175800 266579 := bstep (se 1 (by rfl) ⟨199934, by rfl⟩ : syracuseStep 266579 = 399869) B399869
theorem B266609 : Blo 175800 266609 := bstep (se 2 (by rfl) ⟨99978, by rfl⟩ : syracuseStep 266609 = 199957) B199957
theorem B266627 : Blo 175800 266627 := bstep (se 1 (by rfl) ⟨199970, by rfl⟩ : syracuseStep 266627 = 399941) B399941
theorem B201091 : Blo 175800 201091 := bstep (se 1 (by rfl) ⟨150818, by rfl⟩ : syracuseStep 201091 = 301637) B301637
theorem B266657 : Blo 175800 266657 := bstep (se 2 (by rfl) ⟨99996, by rfl⟩ : syracuseStep 266657 = 199993) B199993
theorem B397745 : Blo 175800 397745 := bstep (se 2 (by rfl) ⟨149154, by rfl⟩ : syracuseStep 397745 = 298309) B298309
theorem B299443 : Blo 175800 299443 := bstep (se 1 (by rfl) ⟨224582, by rfl⟩ : syracuseStep 299443 = 449165) B449165
theorem B266675 : Blo 175800 266675 := bstep (se 1 (by rfl) ⟨200006, by rfl⟩ : syracuseStep 266675 = 400013) B400013
theorem B397763 : Blo 175800 397763 := bstep (se 1 (by rfl) ⟨298322, by rfl⟩ : syracuseStep 397763 = 596645) B596645
theorem B14913989 : Blo 175800 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B266705 : Blo 175800 266705 := bstep (se 2 (by rfl) ⟨100014, by rfl⟩ : syracuseStep 266705 = 200029) B200029
theorem B266723 : Blo 175800 266723 := bstep (se 1 (by rfl) ⟨200042, by rfl⟩ : syracuseStep 266723 = 400085) B400085
theorem B266753 : Blo 175800 266753 := bstep (se 2 (by rfl) ⟨100032, by rfl⟩ : syracuseStep 266753 = 200065) B200065
theorem B266771 : Blo 175800 266771 := bstep (se 1 (by rfl) ⟨200078, by rfl⟩ : syracuseStep 266771 = 400157) B400157
theorem B201235 : Blo 175800 201235 := bstep (se 1 (by rfl) ⟨150926, by rfl⟩ : syracuseStep 201235 = 301853) B301853
theorem B266801 : Blo 175800 266801 := bstep (se 2 (by rfl) ⟨100050, by rfl⟩ : syracuseStep 266801 = 200101) B200101
theorem B299585 : Blo 175800 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B266819 : Blo 175800 266819 := bstep (se 1 (by rfl) ⟨200114, by rfl⟩ : syracuseStep 266819 = 400229) B400229
theorem B266849 : Blo 175800 266849 := bstep (se 2 (by rfl) ⟨100068, by rfl⟩ : syracuseStep 266849 = 200137) B200137
theorem B266867 : Blo 175800 266867 := bstep (se 1 (by rfl) ⟨200150, by rfl⟩ : syracuseStep 266867 = 400301) B400301
theorem B266897 : Blo 175800 266897 := bstep (se 2 (by rfl) ⟨100086, by rfl⟩ : syracuseStep 266897 = 200173) B200173
theorem B266915 : Blo 175800 266915 := bstep (se 1 (by rfl) ⟨200186, by rfl⟩ : syracuseStep 266915 = 400373) B400373
theorem B201379 : Blo 175800 201379 := bstep (se 1 (by rfl) ⟨151034, by rfl⟩ : syracuseStep 201379 = 302069) B302069
theorem B299713 : Blo 175800 299713 := bstep (se 2 (by rfl) ⟨112392, by rfl⟩ : syracuseStep 299713 = 224785) B224785
theorem B266945 : Blo 175800 266945 := bstep (se 2 (by rfl) ⟨100104, by rfl⟩ : syracuseStep 266945 = 200209) B200209
theorem B398033 : Blo 175800 398033 := bstep (se 2 (by rfl) ⟨149262, by rfl⟩ : syracuseStep 398033 = 298525) B298525
theorem B266963 : Blo 175800 266963 := bstep (se 1 (by rfl) ⟨200222, by rfl⟩ : syracuseStep 266963 = 400445) B400445
theorem B398051 : Blo 175800 398051 := bstep (se 1 (by rfl) ⟨298538, by rfl⟩ : syracuseStep 398051 = 597077) B597077
theorem B299747 : Blo 175800 299747 := bstep (se 1 (by rfl) ⟨224810, by rfl⟩ : syracuseStep 299747 = 449621) B449621
theorem B266993 : Blo 175800 266993 := bstep (se 2 (by rfl) ⟨100122, by rfl⟩ : syracuseStep 266993 = 200245) B200245
theorem B267011 : Blo 175800 267011 := bstep (se 1 (by rfl) ⟨200258, by rfl⟩ : syracuseStep 267011 = 400517) B400517
theorem B594701 : Blo 175800 594701 := bstep (se 3 (by rfl) ⟨111506, by rfl⟩ : syracuseStep 594701 = 223013) B223013
theorem B267041 : Blo 175800 267041 := bstep (se 2 (by rfl) ⟨100140, by rfl⟩ : syracuseStep 267041 = 200281) B200281
theorem B267059 : Blo 175800 267059 := bstep (se 1 (by rfl) ⟨200294, by rfl⟩ : syracuseStep 267059 = 400589) B400589
theorem B201523 : Blo 175800 201523 := bstep (se 1 (by rfl) ⟨151142, by rfl⟩ : syracuseStep 201523 = 302285) B302285
theorem B594755 : Blo 175800 594755 := bstep (se 1 (by rfl) ⟨446066, by rfl⟩ : syracuseStep 594755 = 892133) B892133
theorem B267089 : Blo 175800 267089 := bstep (se 2 (by rfl) ⟨100158, by rfl⟩ : syracuseStep 267089 = 200317) B200317
theorem B299875 : Blo 175800 299875 := bstep (se 1 (by rfl) ⟨224906, by rfl⟩ : syracuseStep 299875 = 449813) B449813
theorem B267107 : Blo 175800 267107 := bstep (se 1 (by rfl) ⟨200330, by rfl⟩ : syracuseStep 267107 = 400661) B400661
theorem B267137 : Blo 175800 267137 := bstep (se 2 (by rfl) ⟨100176, by rfl⟩ : syracuseStep 267137 = 200353) B200353
theorem B267155 : Blo 175800 267155 := bstep (se 1 (by rfl) ⟨200366, by rfl⟩ : syracuseStep 267155 = 400733) B400733
theorem B267185 : Blo 175800 267185 := bstep (se 2 (by rfl) ⟨100194, by rfl⟩ : syracuseStep 267185 = 200389) B200389
theorem B267203 : Blo 175800 267203 := bstep (se 1 (by rfl) ⟨200402, by rfl⟩ : syracuseStep 267203 = 400805) B400805
theorem B201667 : Blo 175800 201667 := bstep (se 1 (by rfl) ⟨151250, by rfl⟩ : syracuseStep 201667 = 302501) B302501
theorem B267233 : Blo 175800 267233 := bstep (se 2 (by rfl) ⟨100212, by rfl⟩ : syracuseStep 267233 = 200425) B200425
theorem B398321 : Blo 175800 398321 := bstep (se 2 (by rfl) ⟨149370, by rfl⟩ : syracuseStep 398321 = 298741) B298741
theorem B300017 : Blo 175800 300017 := bstep (se 2 (by rfl) ⟨112506, by rfl⟩ : syracuseStep 300017 = 225013) B225013
theorem B267251 : Blo 175800 267251 := bstep (se 1 (by rfl) ⟨200438, by rfl⟩ : syracuseStep 267251 = 400877) B400877
theorem B398339 : Blo 175800 398339 := bstep (se 1 (by rfl) ⟨298754, by rfl⟩ : syracuseStep 398339 = 597509) B597509
theorem B267281 : Blo 175800 267281 := bstep (se 2 (by rfl) ⟨100230, by rfl⟩ : syracuseStep 267281 = 200461) B200461
theorem B267299 : Blo 175800 267299 := bstep (se 1 (by rfl) ⟨200474, by rfl⟩ : syracuseStep 267299 = 400949) B400949
theorem B267329 : Blo 175800 267329 := bstep (se 2 (by rfl) ⟨100248, by rfl⟩ : syracuseStep 267329 = 200497) B200497
theorem B595025 : Blo 175800 595025 := bstep (se 2 (by rfl) ⟨223134, by rfl⟩ : syracuseStep 595025 = 446269) B446269
theorem B267347 : Blo 175800 267347 := bstep (se 1 (by rfl) ⟨200510, by rfl⟩ : syracuseStep 267347 = 401021) B401021
theorem B201811 : Blo 175800 201811 := bstep (se 1 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 201811 = 302717) B302717
theorem B300145 : Blo 175800 300145 := bstep (se 2 (by rfl) ⟨112554, by rfl⟩ : syracuseStep 300145 = 225109) B225109
theorem B267377 : Blo 175800 267377 := bstep (se 2 (by rfl) ⟨100266, by rfl⟩ : syracuseStep 267377 = 200533) B200533
theorem B267395 : Blo 175800 267395 := bstep (se 1 (by rfl) ⟨200546, by rfl⟩ : syracuseStep 267395 = 401093) B401093
theorem B431249 : Blo 175800 431249 := bstep (se 2 (by rfl) ⟨161718, by rfl⟩ : syracuseStep 431249 = 323437) B323437
theorem B300179 : Blo 175800 300179 := bstep (se 1 (by rfl) ⟨225134, by rfl⟩ : syracuseStep 300179 = 450269) B450269
theorem B267425 : Blo 175800 267425 := bstep (se 2 (by rfl) ⟨100284, by rfl⟩ : syracuseStep 267425 = 200569) B200569
theorem B267443 : Blo 175800 267443 := bstep (se 1 (by rfl) ⟨200582, by rfl⟩ : syracuseStep 267443 = 401165) B401165
theorem B1021133 : Blo 175800 1021133 := bstep (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) B382925
theorem B267473 : Blo 175800 267473 := bstep (se 2 (by rfl) ⟨100302, by rfl⟩ : syracuseStep 267473 = 200605) B200605
theorem B267491 : Blo 175800 267491 := bstep (se 1 (by rfl) ⟨200618, by rfl⟩ : syracuseStep 267491 = 401237) B401237
theorem B201955 : Blo 175800 201955 := bstep (se 1 (by rfl) ⟨151466, by rfl⟩ : syracuseStep 201955 = 302933) B302933
theorem B267521 : Blo 175800 267521 := bstep (se 2 (by rfl) ⟨100320, by rfl⟩ : syracuseStep 267521 = 200641) B200641
theorem B398609 : Blo 175800 398609 := bstep (se 2 (by rfl) ⟨149478, by rfl⟩ : syracuseStep 398609 = 298957) B298957
theorem B300307 : Blo 175800 300307 := bstep (se 1 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 300307 = 450461) B450461
theorem B267539 : Blo 175800 267539 := bstep (se 1 (by rfl) ⟨200654, by rfl⟩ : syracuseStep 267539 = 401309) B401309
theorem B398627 : Blo 175800 398627 := bstep (se 1 (by rfl) ⟨298970, by rfl⟩ : syracuseStep 398627 = 597941) B597941
theorem B267569 : Blo 175800 267569 := bstep (se 2 (by rfl) ⟨100338, by rfl⟩ : syracuseStep 267569 = 200677) B200677
theorem B267587 : Blo 175800 267587 := bstep (se 1 (by rfl) ⟨200690, by rfl⟩ : syracuseStep 267587 = 401381) B401381
theorem B890189 : Blo 175800 890189 := bstep (se 3 (by rfl) ⟨166910, by rfl⟩ : syracuseStep 890189 = 333821) B333821
theorem B267617 : Blo 175800 267617 := bstep (se 2 (by rfl) ⟨100356, by rfl⟩ : syracuseStep 267617 = 200713) B200713
theorem B267635 : Blo 175800 267635 := bstep (se 1 (by rfl) ⟨200726, by rfl⟩ : syracuseStep 267635 = 401453) B401453
theorem B202099 : Blo 175800 202099 := bstep (se 1 (by rfl) ⟨151574, by rfl⟩ : syracuseStep 202099 = 303149) B303149
theorem B267665 : Blo 175800 267665 := bstep (se 2 (by rfl) ⟨100374, by rfl⟩ : syracuseStep 267665 = 200749) B200749
theorem B300449 : Blo 175800 300449 := bstep (se 2 (by rfl) ⟨112668, by rfl⟩ : syracuseStep 300449 = 225337) B225337
theorem B267683 : Blo 175800 267683 := bstep (se 1 (by rfl) ⟨200762, by rfl⟩ : syracuseStep 267683 = 401525) B401525
theorem B267713 : Blo 175800 267713 := bstep (se 2 (by rfl) ⟨100392, by rfl⟩ : syracuseStep 267713 = 200785) B200785
theorem B267731 : Blo 175800 267731 := bstep (se 1 (by rfl) ⟨200798, by rfl⟩ : syracuseStep 267731 = 401597) B401597
theorem B267761 : Blo 175800 267761 := bstep (se 2 (by rfl) ⟨100410, by rfl⟩ : syracuseStep 267761 = 200821) B200821
theorem B267779 : Blo 175800 267779 := bstep (se 1 (by rfl) ⟨200834, by rfl⟩ : syracuseStep 267779 = 401669) B401669
theorem B202243 : Blo 175800 202243 := bstep (se 1 (by rfl) ⟨151682, by rfl⟩ : syracuseStep 202243 = 303365) B303365
theorem B300577 : Blo 175800 300577 := bstep (se 2 (by rfl) ⟨112716, by rfl⟩ : syracuseStep 300577 = 225433) B225433
theorem B267809 : Blo 175800 267809 := bstep (se 2 (by rfl) ⟨100428, by rfl⟩ : syracuseStep 267809 = 200857) B200857
theorem B398897 : Blo 175800 398897 := bstep (se 2 (by rfl) ⟨149586, by rfl⟩ : syracuseStep 398897 = 299173) B299173
theorem B267827 : Blo 175800 267827 := bstep (se 1 (by rfl) ⟨200870, by rfl⟩ : syracuseStep 267827 = 401741) B401741
theorem B398915 : Blo 175800 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B300611 : Blo 175800 300611 := bstep (se 1 (by rfl) ⟨225458, by rfl⟩ : syracuseStep 300611 = 450917) B450917
theorem B267857 : Blo 175800 267857 := bstep (se 2 (by rfl) ⟨100446, by rfl⟩ : syracuseStep 267857 = 200893) B200893
theorem B267875 : Blo 175800 267875 := bstep (se 1 (by rfl) ⟨200906, by rfl⟩ : syracuseStep 267875 = 401813) B401813
theorem B595565 : Blo 175800 595565 := bstep (se 3 (by rfl) ⟨111668, by rfl⟩ : syracuseStep 595565 = 223337) B223337
theorem B267905 : Blo 175800 267905 := bstep (se 2 (by rfl) ⟨100464, by rfl⟩ : syracuseStep 267905 = 200929) B200929
theorem B267923 : Blo 175800 267923 := bstep (se 1 (by rfl) ⟨200942, by rfl⟩ : syracuseStep 267923 = 401885) B401885
theorem B595619 : Blo 175800 595619 := bstep (se 1 (by rfl) ⟨446714, by rfl⟩ : syracuseStep 595619 = 893429) B893429
theorem B267953 : Blo 175800 267953 := bstep (se 2 (by rfl) ⟨100482, by rfl⟩ : syracuseStep 267953 = 200965) B200965
theorem B300739 : Blo 175800 300739 := bstep (se 1 (by rfl) ⟨225554, by rfl⟩ : syracuseStep 300739 = 451109) B451109
theorem B267971 : Blo 175800 267971 := bstep (se 1 (by rfl) ⟨200978, by rfl⟩ : syracuseStep 267971 = 401957) B401957
theorem B268001 : Blo 175800 268001 := bstep (se 2 (by rfl) ⟨100500, by rfl⟩ : syracuseStep 268001 = 201001) B201001
theorem B431843 : Blo 175800 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B268019 : Blo 175800 268019 := bstep (se 1 (by rfl) ⟨201014, by rfl⟩ : syracuseStep 268019 = 402029) B402029
theorem B2004749 : Blo 175800 2004749 := bstep (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) B751781
theorem B268049 : Blo 175800 268049 := bstep (se 2 (by rfl) ⟨100518, by rfl⟩ : syracuseStep 268049 = 201037) B201037
theorem B268067 : Blo 175800 268067 := bstep (se 1 (by rfl) ⟨201050, by rfl⟩ : syracuseStep 268067 = 402101) B402101
theorem B268097 : Blo 175800 268097 := bstep (se 2 (by rfl) ⟨100536, by rfl⟩ : syracuseStep 268097 = 201073) B201073
theorem B399185 : Blo 175800 399185 := bstep (se 2 (by rfl) ⟨149694, by rfl⟩ : syracuseStep 399185 = 299389) B299389
theorem B300881 : Blo 175800 300881 := bstep (se 2 (by rfl) ⟨112830, by rfl⟩ : syracuseStep 300881 = 225661) B225661
theorem B268115 : Blo 175800 268115 := bstep (se 1 (by rfl) ⟨201086, by rfl⟩ : syracuseStep 268115 = 402173) B402173
theorem B399203 : Blo 175800 399203 := bstep (se 1 (by rfl) ⟨299402, by rfl⟩ : syracuseStep 399203 = 598805) B598805
theorem B268145 : Blo 175800 268145 := bstep (se 2 (by rfl) ⟨100554, by rfl⟩ : syracuseStep 268145 = 201109) B201109
theorem B268163 : Blo 175800 268163 := bstep (se 1 (by rfl) ⟨201122, by rfl⟩ : syracuseStep 268163 = 402245) B402245
theorem B268193 : Blo 175800 268193 := bstep (se 2 (by rfl) ⟨100572, by rfl⟩ : syracuseStep 268193 = 201145) B201145
theorem B595889 : Blo 175800 595889 := bstep (se 2 (by rfl) ⟨223458, by rfl⟩ : syracuseStep 595889 = 446917) B446917
theorem B268211 : Blo 175800 268211 := bstep (se 1 (by rfl) ⟨201158, by rfl⟩ : syracuseStep 268211 = 402317) B402317
theorem B301009 : Blo 175800 301009 := bstep (se 2 (by rfl) ⟨112878, by rfl⟩ : syracuseStep 301009 = 225757) B225757
theorem B268241 : Blo 175800 268241 := bstep (se 2 (by rfl) ⟨100590, by rfl⟩ : syracuseStep 268241 = 201181) B201181
theorem B759779 : Blo 175800 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B268259 : Blo 175800 268259 := bstep (se 1 (by rfl) ⟨201194, by rfl⟩ : syracuseStep 268259 = 402389) B402389
theorem B301043 : Blo 175800 301043 := bstep (se 1 (by rfl) ⟨225782, by rfl⟩ : syracuseStep 301043 = 451565) B451565
theorem B268289 : Blo 175800 268289 := bstep (se 2 (by rfl) ⟨100608, by rfl⟩ : syracuseStep 268289 = 201217) B201217
theorem B268307 : Blo 175800 268307 := bstep (se 1 (by rfl) ⟨201230, by rfl⟩ : syracuseStep 268307 = 402461) B402461
theorem B268337 : Blo 175800 268337 := bstep (se 2 (by rfl) ⟨100626, by rfl⟩ : syracuseStep 268337 = 201253) B201253
theorem B2267189 : Blo 175800 2267189 := bstep (se 5 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 2267189 = 212549) B212549
theorem B202819 : Blo 175800 202819 := bstep (se 1 (by rfl) ⟨152114, by rfl⟩ : syracuseStep 202819 = 304229) B304229
theorem B268355 : Blo 175800 268355 := bstep (se 1 (by rfl) ⟨201266, by rfl⟩ : syracuseStep 268355 = 402533) B402533
theorem B268385 : Blo 175800 268385 := bstep (se 2 (by rfl) ⟨100644, by rfl⟩ : syracuseStep 268385 = 201289) B201289
theorem B399473 : Blo 175800 399473 := bstep (se 2 (by rfl) ⟨149802, by rfl⟩ : syracuseStep 399473 = 299605) B299605
theorem B301171 : Blo 175800 301171 := bstep (se 1 (by rfl) ⟨225878, by rfl⟩ : syracuseStep 301171 = 451757) B451757
theorem B268403 : Blo 175800 268403 := bstep (se 1 (by rfl) ⟨201302, by rfl⟩ : syracuseStep 268403 = 402605) B402605
theorem B399491 : Blo 175800 399491 := bstep (se 1 (by rfl) ⟨299618, by rfl⟩ : syracuseStep 399491 = 599237) B599237
theorem B268433 : Blo 175800 268433 := bstep (se 2 (by rfl) ⟨100662, by rfl⟩ : syracuseStep 268433 = 201325) B201325
theorem B268451 : Blo 175800 268451 := bstep (se 1 (by rfl) ⟨201338, by rfl⟩ : syracuseStep 268451 = 402677) B402677
theorem B727217 : Blo 175800 727217 := bstep (se 2 (by rfl) ⟨272706, by rfl⟩ : syracuseStep 727217 = 545413) B545413
theorem B268481 : Blo 175800 268481 := bstep (se 2 (by rfl) ⟨100680, by rfl⟩ : syracuseStep 268481 = 201361) B201361
theorem B334019 : Blo 175800 334019 := bstep (se 1 (by rfl) ⟨250514, by rfl⟩ : syracuseStep 334019 = 501029) B501029
theorem B1808581 : Blo 175800 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B268499 : Blo 175800 268499 := bstep (se 1 (by rfl) ⟨201374, by rfl⟩ : syracuseStep 268499 = 402749) B402749
theorem B268529 : Blo 175800 268529 := bstep (se 2 (by rfl) ⟨100698, by rfl⟩ : syracuseStep 268529 = 201397) B201397
theorem B301313 : Blo 175800 301313 := bstep (se 2 (by rfl) ⟨112992, by rfl⟩ : syracuseStep 301313 = 225985) B225985
theorem B268547 : Blo 175800 268547 := bstep (se 1 (by rfl) ⟨201410, by rfl⟩ : syracuseStep 268547 = 402821) B402821
theorem B268577 : Blo 175800 268577 := bstep (se 2 (by rfl) ⟨100716, by rfl⟩ : syracuseStep 268577 = 201433) B201433
theorem B268595 : Blo 175800 268595 := bstep (se 1 (by rfl) ⟨201446, by rfl⟩ : syracuseStep 268595 = 402893) B402893
theorem B268625 : Blo 175800 268625 := bstep (se 2 (by rfl) ⟨100734, by rfl⟩ : syracuseStep 268625 = 201469) B201469
theorem B268643 : Blo 175800 268643 := bstep (se 1 (by rfl) ⟨201482, by rfl⟩ : syracuseStep 268643 = 402965) B402965
theorem B301441 : Blo 175800 301441 := bstep (se 2 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 301441 = 226081) B226081
theorem B268673 : Blo 175800 268673 := bstep (se 2 (by rfl) ⟨100752, by rfl⟩ : syracuseStep 268673 = 201505) B201505
theorem B399761 : Blo 175800 399761 := bstep (se 2 (by rfl) ⟨149910, by rfl⟩ : syracuseStep 399761 = 299821) B299821
theorem B268691 : Blo 175800 268691 := bstep (se 1 (by rfl) ⟨201518, by rfl⟩ : syracuseStep 268691 = 403037) B403037
theorem B399779 : Blo 175800 399779 := bstep (se 1 (by rfl) ⟨299834, by rfl⟩ : syracuseStep 399779 = 599669) B599669
theorem B301475 : Blo 175800 301475 := bstep (se 1 (by rfl) ⟨226106, by rfl⟩ : syracuseStep 301475 = 452213) B452213
theorem B268721 : Blo 175800 268721 := bstep (se 2 (by rfl) ⟨100770, by rfl⟩ : syracuseStep 268721 = 201541) B201541
theorem B268739 : Blo 175800 268739 := bstep (se 1 (by rfl) ⟨201554, by rfl⟩ : syracuseStep 268739 = 403109) B403109
theorem B596429 : Blo 175800 596429 := bstep (se 3 (by rfl) ⟨111830, by rfl⟩ : syracuseStep 596429 = 223661) B223661
theorem B268769 : Blo 175800 268769 := bstep (se 2 (by rfl) ⟨100788, by rfl⟩ : syracuseStep 268769 = 201577) B201577
theorem B334307 : Blo 175800 334307 := bstep (se 1 (by rfl) ⟨250730, by rfl⟩ : syracuseStep 334307 = 501461) B501461
theorem B858595 : Blo 175800 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B268787 : Blo 175800 268787 := bstep (se 1 (by rfl) ⟨201590, by rfl⟩ : syracuseStep 268787 = 403181) B403181
theorem B596483 : Blo 175800 596483 := bstep (se 1 (by rfl) ⟨447362, by rfl⟩ : syracuseStep 596483 = 894725) B894725
theorem B268817 : Blo 175800 268817 := bstep (se 2 (by rfl) ⟨100806, by rfl⟩ : syracuseStep 268817 = 201613) B201613
theorem B301601 : Blo 175800 301601 := bstep (se 2 (by rfl) ⟨113100, by rfl⟩ : syracuseStep 301601 = 226201) B226201
theorem B301603 : Blo 175800 301603 := bstep (se 1 (by rfl) ⟨226202, by rfl⟩ : syracuseStep 301603 = 452405) B452405
theorem B268835 : Blo 175800 268835 := bstep (se 1 (by rfl) ⟨201626, by rfl⟩ : syracuseStep 268835 = 403253) B403253
theorem B268865 : Blo 175800 268865 := bstep (se 2 (by rfl) ⟨100824, by rfl⟩ : syracuseStep 268865 = 201649) B201649
theorem B268883 : Blo 175800 268883 := bstep (se 1 (by rfl) ⟨201662, by rfl⟩ : syracuseStep 268883 = 403325) B403325
theorem B268913 : Blo 175800 268913 := bstep (se 2 (by rfl) ⟨100842, by rfl⟩ : syracuseStep 268913 = 201685) B201685
theorem B268931 : Blo 175800 268931 := bstep (se 1 (by rfl) ⟨201698, by rfl⟩ : syracuseStep 268931 = 403397) B403397
theorem B268961 : Blo 175800 268961 := bstep (se 2 (by rfl) ⟨100860, by rfl⟩ : syracuseStep 268961 = 201721) B201721
theorem B400049 : Blo 175800 400049 := bstep (se 2 (by rfl) ⟨150018, by rfl⟩ : syracuseStep 400049 = 300037) B300037
theorem B301745 : Blo 175800 301745 := bstep (se 2 (by rfl) ⟨113154, by rfl⟩ : syracuseStep 301745 = 226309) B226309
theorem B268979 : Blo 175800 268979 := bstep (se 1 (by rfl) ⟨201734, by rfl⟩ : syracuseStep 268979 = 403469) B403469
theorem B400067 : Blo 175800 400067 := bstep (se 1 (by rfl) ⟨300050, by rfl⟩ : syracuseStep 400067 = 600101) B600101
theorem B269009 : Blo 175800 269009 := bstep (se 2 (by rfl) ⟨100878, by rfl⟩ : syracuseStep 269009 = 201757) B201757
theorem B563939 : Blo 175800 563939 := bstep (se 1 (by rfl) ⟨422954, by rfl⟩ : syracuseStep 563939 = 845909) B845909
theorem B269027 : Blo 175800 269027 := bstep (se 1 (by rfl) ⟨201770, by rfl⟩ : syracuseStep 269027 = 403541) B403541
theorem B269057 : Blo 175800 269057 := bstep (se 2 (by rfl) ⟨100896, by rfl⟩ : syracuseStep 269057 = 201793) B201793
theorem B596753 : Blo 175800 596753 := bstep (se 2 (by rfl) ⟨223782, by rfl⟩ : syracuseStep 596753 = 447565) B447565
theorem B269075 : Blo 175800 269075 := bstep (se 1 (by rfl) ⟨201806, by rfl⟩ : syracuseStep 269075 = 403613) B403613
theorem B301873 : Blo 175800 301873 := bstep (se 2 (by rfl) ⟨113202, by rfl⟩ : syracuseStep 301873 = 226405) B226405
theorem B269105 : Blo 175800 269105 := bstep (se 2 (by rfl) ⟨100914, by rfl⟩ : syracuseStep 269105 = 201829) B201829
theorem B269123 : Blo 175800 269123 := bstep (se 1 (by rfl) ⟨201842, by rfl⟩ : syracuseStep 269123 = 403685) B403685
theorem B301907 : Blo 175800 301907 := bstep (se 1 (by rfl) ⟨226430, by rfl⟩ : syracuseStep 301907 = 452861) B452861
theorem B269153 : Blo 175800 269153 := bstep (se 2 (by rfl) ⟨100932, by rfl⟩ : syracuseStep 269153 = 201865) B201865
theorem B269171 : Blo 175800 269171 := bstep (se 1 (by rfl) ⟨201878, by rfl⟩ : syracuseStep 269171 = 403757) B403757
theorem B269201 : Blo 175800 269201 := bstep (se 2 (by rfl) ⟨100950, by rfl⟩ : syracuseStep 269201 = 201901) B201901
theorem B269219 : Blo 175800 269219 := bstep (se 1 (by rfl) ⟨201914, by rfl⟩ : syracuseStep 269219 = 403829) B403829
theorem B269249 : Blo 175800 269249 := bstep (se 2 (by rfl) ⟨100968, by rfl⟩ : syracuseStep 269249 = 201937) B201937
theorem B400337 : Blo 175800 400337 := bstep (se 2 (by rfl) ⟨150126, by rfl⟩ : syracuseStep 400337 = 300253) B300253
theorem B302035 : Blo 175800 302035 := bstep (se 1 (by rfl) ⟨226526, by rfl⟩ : syracuseStep 302035 = 453053) B453053
theorem B269267 : Blo 175800 269267 := bstep (se 1 (by rfl) ⟨201950, by rfl⟩ : syracuseStep 269267 = 403901) B403901
theorem B400355 : Blo 175800 400355 := bstep (se 1 (by rfl) ⟨300266, by rfl⟩ : syracuseStep 400355 = 600533) B600533
theorem B269297 : Blo 175800 269297 := bstep (se 2 (by rfl) ⟨100986, by rfl⟩ : syracuseStep 269297 = 201973) B201973
theorem B269315 : Blo 175800 269315 := bstep (se 1 (by rfl) ⟨201986, by rfl⟩ : syracuseStep 269315 = 403973) B403973
theorem B269345 : Blo 175800 269345 := bstep (se 2 (by rfl) ⟨101004, by rfl⟩ : syracuseStep 269345 = 202009) B202009
theorem B269363 : Blo 175800 269363 := bstep (se 1 (by rfl) ⟨202022, by rfl⟩ : syracuseStep 269363 = 404045) B404045
theorem B269393 : Blo 175800 269393 := bstep (se 2 (by rfl) ⟨101022, by rfl⟩ : syracuseStep 269393 = 202045) B202045
theorem B302177 : Blo 175800 302177 := bstep (se 2 (by rfl) ⟨113316, by rfl⟩ : syracuseStep 302177 = 226633) B226633
theorem B269411 : Blo 175800 269411 := bstep (se 1 (by rfl) ⟨202058, by rfl⟩ : syracuseStep 269411 = 404117) B404117
theorem B564337 : Blo 175800 564337 := bstep (se 2 (by rfl) ⟨211626, by rfl⟩ : syracuseStep 564337 = 423253) B423253
theorem B269441 : Blo 175800 269441 := bstep (se 2 (by rfl) ⟨101040, by rfl⟩ : syracuseStep 269441 = 202081) B202081
theorem B269459 : Blo 175800 269459 := bstep (se 1 (by rfl) ⟨202094, by rfl⟩ : syracuseStep 269459 = 404189) B404189
theorem B564401 : Blo 175800 564401 := bstep (se 2 (by rfl) ⟨211650, by rfl⟩ : syracuseStep 564401 = 423301) B423301
theorem B269489 : Blo 175800 269489 := bstep (se 2 (by rfl) ⟨101058, by rfl⟩ : syracuseStep 269489 = 202117) B202117
theorem B269507 : Blo 175800 269507 := bstep (se 1 (by rfl) ⟨202130, by rfl⟩ : syracuseStep 269507 = 404261) B404261
theorem B302305 : Blo 175800 302305 := bstep (se 2 (by rfl) ⟨113364, by rfl⟩ : syracuseStep 302305 = 226729) B226729
theorem B269537 : Blo 175800 269537 := bstep (se 2 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 269537 = 202153) B202153
theorem B400625 : Blo 175800 400625 := bstep (se 2 (by rfl) ⟨150234, by rfl⟩ : syracuseStep 400625 = 300469) B300469
theorem B269555 : Blo 175800 269555 := bstep (se 1 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 269555 = 404333) B404333
theorem B400643 : Blo 175800 400643 := bstep (se 1 (by rfl) ⟨300482, by rfl⟩ : syracuseStep 400643 = 600965) B600965
theorem B302339 : Blo 175800 302339 := bstep (se 1 (by rfl) ⟨226754, by rfl⟩ : syracuseStep 302339 = 453509) B453509
theorem B957701 : Blo 175800 957701 := bstep (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) B179569
theorem B269585 : Blo 175800 269585 := bstep (se 2 (by rfl) ⟨101094, by rfl⟩ : syracuseStep 269585 = 202189) B202189
theorem B269603 : Blo 175800 269603 := bstep (se 1 (by rfl) ⟨202202, by rfl⟩ : syracuseStep 269603 = 404405) B404405
theorem B597293 : Blo 175800 597293 := bstep (se 3 (by rfl) ⟨111992, by rfl⟩ : syracuseStep 597293 = 223985) B223985
theorem B269633 : Blo 175800 269633 := bstep (se 2 (by rfl) ⟨101112, by rfl⟩ : syracuseStep 269633 = 202225) B202225
theorem B269651 : Blo 175800 269651 := bstep (se 1 (by rfl) ⟨202238, by rfl⟩ : syracuseStep 269651 = 404477) B404477
theorem B597347 : Blo 175800 597347 := bstep (se 1 (by rfl) ⟨448010, by rfl⟩ : syracuseStep 597347 = 896021) B896021
theorem B269681 : Blo 175800 269681 := bstep (se 2 (by rfl) ⟨101130, by rfl⟩ : syracuseStep 269681 = 202261) B202261
theorem B302467 : Blo 175800 302467 := bstep (se 1 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 302467 = 453701) B453701
theorem B269699 : Blo 175800 269699 := bstep (se 1 (by rfl) ⟨202274, by rfl⟩ : syracuseStep 269699 = 404549) B404549
theorem B335249 : Blo 175800 335249 := bstep (se 2 (by rfl) ⟨125718, by rfl⟩ : syracuseStep 335249 = 251437) B251437
theorem B400913 : Blo 175800 400913 := bstep (se 2 (by rfl) ⟨150342, by rfl⟩ : syracuseStep 400913 = 300685) B300685
theorem B302609 : Blo 175800 302609 := bstep (se 2 (by rfl) ⟨113478, by rfl⟩ : syracuseStep 302609 = 226957) B226957
theorem B400931 : Blo 175800 400931 := bstep (se 1 (by rfl) ⟨300698, by rfl⟩ : syracuseStep 400931 = 601397) B601397
theorem B597617 : Blo 175800 597617 := bstep (se 2 (by rfl) ⟨224106, by rfl⟩ : syracuseStep 597617 = 448213) B448213
theorem B302737 : Blo 175800 302737 := bstep (se 2 (by rfl) ⟨113526, by rfl⟩ : syracuseStep 302737 = 227053) B227053
theorem B761521 : Blo 175800 761521 := bstep (se 2 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 761521 = 571141) B571141
theorem B859825 : Blo 175800 859825 := bstep (se 2 (by rfl) ⟨322434, by rfl⟩ : syracuseStep 859825 = 644869) B644869
theorem B302771 : Blo 175800 302771 := bstep (se 1 (by rfl) ⟨227078, by rfl⟩ : syracuseStep 302771 = 454157) B454157
theorem B7282403 : Blo 175800 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B401201 : Blo 175800 401201 := bstep (se 2 (by rfl) ⟨150450, by rfl⟩ : syracuseStep 401201 = 300901) B300901
theorem B302899 : Blo 175800 302899 := bstep (se 1 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 302899 = 454349) B454349
theorem B302915 : Blo 175800 302915 := bstep (se 1 (by rfl) ⟨227186, by rfl⟩ : syracuseStep 302915 = 454373) B454373
theorem B401219 : Blo 175800 401219 := bstep (se 1 (by rfl) ⟨300914, by rfl⟩ : syracuseStep 401219 = 601829) B601829
theorem B204643 : Blo 175800 204643 := bstep (se 1 (by rfl) ⟨153482, by rfl⟩ : syracuseStep 204643 = 306965) B306965
theorem B1351565 : Blo 175800 1351565 := bstep (se 3 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 1351565 = 506837) B506837
theorem B303041 : Blo 175800 303041 := bstep (se 2 (by rfl) ⟨113640, by rfl⟩ : syracuseStep 303041 = 227281) B227281
theorem B303169 : Blo 175800 303169 := bstep (se 2 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 303169 = 227377) B227377
theorem B401489 : Blo 175800 401489 := bstep (se 2 (by rfl) ⟨150558, by rfl⟩ : syracuseStep 401489 = 301117) B301117
theorem B401507 : Blo 175800 401507 := bstep (se 1 (by rfl) ⟨301130, by rfl⟩ : syracuseStep 401507 = 602261) B602261
theorem B303203 : Blo 175800 303203 := bstep (se 1 (by rfl) ⟨227402, by rfl⟩ : syracuseStep 303203 = 454805) B454805
theorem B598157 : Blo 175800 598157 := bstep (se 3 (by rfl) ⟨112154, by rfl⟩ : syracuseStep 598157 = 224309) B224309
theorem B893105 : Blo 175800 893105 := bstep (se 2 (by rfl) ⟨334914, by rfl⟩ : syracuseStep 893105 = 669829) B669829
theorem B598211 : Blo 175800 598211 := bstep (se 1 (by rfl) ⟨448658, by rfl⟩ : syracuseStep 598211 = 897317) B897317
theorem B303331 : Blo 175800 303331 := bstep (se 1 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 303331 = 454997) B454997
theorem B336145 : Blo 175800 336145 := bstep (se 2 (by rfl) ⟨126054, by rfl⟩ : syracuseStep 336145 = 252109) B252109
theorem B3449141 : Blo 175800 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B401777 : Blo 175800 401777 := bstep (se 2 (by rfl) ⟨150666, by rfl⟩ : syracuseStep 401777 = 301333) B301333
theorem B401795 : Blo 175800 401795 := bstep (se 1 (by rfl) ⟨301346, by rfl⟩ : syracuseStep 401795 = 602693) B602693
theorem B336305 : Blo 175800 336305 := bstep (se 2 (by rfl) ⟨126114, by rfl⟩ : syracuseStep 336305 = 252229) B252229
theorem B598481 : Blo 175800 598481 := bstep (se 2 (by rfl) ⟨224430, by rfl⟩ : syracuseStep 598481 = 448861) B448861
theorem B2007665 : Blo 175800 2007665 := bstep (se 2 (by rfl) ⟨752874, by rfl⟩ : syracuseStep 2007665 = 1505749) B1505749
theorem B402065 : Blo 175800 402065 := bstep (se 2 (by rfl) ⟨150774, by rfl⟩ : syracuseStep 402065 = 301549) B301549
theorem B402083 : Blo 175800 402083 := bstep (se 1 (by rfl) ⟨301562, by rfl⟩ : syracuseStep 402083 = 603125) B603125
theorem B336707 : Blo 175800 336707 := bstep (se 1 (by rfl) ⟨252530, by rfl⟩ : syracuseStep 336707 = 505061) B505061
theorem B402353 : Blo 175800 402353 := bstep (se 2 (by rfl) ⟨150882, by rfl⟩ : syracuseStep 402353 = 301765) B301765
theorem B402371 : Blo 175800 402371 := bstep (se 1 (by rfl) ⟨301778, by rfl⟩ : syracuseStep 402371 = 603557) B603557
theorem B599021 : Blo 175800 599021 := bstep (se 3 (by rfl) ⟨112316, by rfl⟩ : syracuseStep 599021 = 224633) B224633
theorem B599075 : Blo 175800 599075 := bstep (se 1 (by rfl) ⟨449306, by rfl⟩ : syracuseStep 599075 = 898613) B898613
theorem B500813 : Blo 175800 500813 := bstep (se 3 (by rfl) ⟨93902, by rfl⟩ : syracuseStep 500813 = 187805) B187805
theorem B271459 : Blo 175800 271459 := bstep (se 1 (by rfl) ⟨203594, by rfl⟩ : syracuseStep 271459 = 407189) B407189
theorem B304337 : Blo 175800 304337 := bstep (se 2 (by rfl) ⟨114126, by rfl⟩ : syracuseStep 304337 = 228253) B228253
theorem B402641 : Blo 175800 402641 := bstep (se 2 (by rfl) ⟨150990, by rfl⟩ : syracuseStep 402641 = 301981) B301981
theorem B402659 : Blo 175800 402659 := bstep (se 1 (by rfl) ⟨301994, by rfl⟩ : syracuseStep 402659 = 603989) B603989
theorem B501005 : Blo 175800 501005 := bstep (se 3 (by rfl) ⟨93938, by rfl⟩ : syracuseStep 501005 = 187877) B187877
theorem B599345 : Blo 175800 599345 := bstep (se 2 (by rfl) ⟨224754, by rfl⟩ : syracuseStep 599345 = 449509) B449509
theorem B2434373 : Blo 175800 2434373 := bstep (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) B456445
theorem B238993 : Blo 175800 238993 := bstep (se 2 (by rfl) ⟨89622, by rfl⟩ : syracuseStep 238993 = 179245) B179245
theorem B402929 : Blo 175800 402929 := bstep (se 2 (by rfl) ⟨151098, by rfl⟩ : syracuseStep 402929 = 302197) B302197
theorem B402947 : Blo 175800 402947 := bstep (se 1 (by rfl) ⟨302210, by rfl⟩ : syracuseStep 402947 = 604421) B604421
theorem B763469 : Blo 175800 763469 := bstep (se 3 (by rfl) ⟨143150, by rfl⟩ : syracuseStep 763469 = 286301) B286301
theorem B894563 : Blo 175800 894563 := bstep (se 1 (by rfl) ⟨670922, by rfl⟩ : syracuseStep 894563 = 1341845) B1341845
theorem B337603 : Blo 175800 337603 := bstep (se 1 (by rfl) ⟨253202, by rfl⟩ : syracuseStep 337603 = 506405) B506405
theorem B403217 : Blo 175800 403217 := bstep (se 2 (by rfl) ⟨151206, by rfl⟩ : syracuseStep 403217 = 302413) B302413
theorem B403235 : Blo 175800 403235 := bstep (se 1 (by rfl) ⟨302426, by rfl⟩ : syracuseStep 403235 = 604853) B604853
theorem B272177 : Blo 175800 272177 := bstep (se 2 (by rfl) ⟨102066, by rfl⟩ : syracuseStep 272177 = 204133) B204133
theorem B894797 : Blo 175800 894797 := bstep (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) B335549
theorem B599885 : Blo 175800 599885 := bstep (se 3 (by rfl) ⟨112478, by rfl⟩ : syracuseStep 599885 = 224957) B224957
theorem B337763 : Blo 175800 337763 := bstep (se 1 (by rfl) ⟨253322, by rfl⟩ : syracuseStep 337763 = 506645) B506645
theorem B599939 : Blo 175800 599939 := bstep (se 1 (by rfl) ⟨449954, by rfl⟩ : syracuseStep 599939 = 899909) B899909
theorem B272273 : Blo 175800 272273 := bstep (se 2 (by rfl) ⟨102102, by rfl⟩ : syracuseStep 272273 = 204205) B204205
theorem B403505 : Blo 175800 403505 := bstep (se 2 (by rfl) ⟨151314, by rfl⟩ : syracuseStep 403505 = 302629) B302629
theorem B403523 : Blo 175800 403523 := bstep (se 1 (by rfl) ⟨302642, by rfl⟩ : syracuseStep 403523 = 605285) B605285
theorem B600209 : Blo 175800 600209 := bstep (se 2 (by rfl) ⟨225078, by rfl⟩ : syracuseStep 600209 = 450157) B450157
theorem B2009285 : Blo 175800 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B501997 : Blo 175800 501997 := bstep (se 3 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 501997 = 188249) B188249
theorem B3909941 : Blo 175800 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B403793 : Blo 175800 403793 := bstep (se 2 (by rfl) ⟨151422, by rfl⟩ : syracuseStep 403793 = 302845) B302845
theorem B403811 : Blo 175800 403811 := bstep (se 1 (by rfl) ⟨302858, by rfl⟩ : syracuseStep 403811 = 605717) B605717
theorem B895373 : Blo 175800 895373 := bstep (se 3 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 895373 = 335765) B335765
theorem B1288817 : Blo 175800 1288817 := bstep (se 2 (by rfl) ⟨483306, by rfl⟩ : syracuseStep 1288817 = 966613) B966613
theorem B404081 : Blo 175800 404081 := bstep (se 2 (by rfl) ⟨151530, by rfl⟩ : syracuseStep 404081 = 303061) B303061
theorem B240259 : Blo 175800 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B404099 : Blo 175800 404099 := bstep (se 1 (by rfl) ⟨303074, by rfl⟩ : syracuseStep 404099 = 606149) B606149
theorem B600749 : Blo 175800 600749 := bstep (se 3 (by rfl) ⟨112640, by rfl⟩ : syracuseStep 600749 = 225281) B225281
theorem B600803 : Blo 175800 600803 := bstep (se 1 (by rfl) ⟨450602, by rfl⟩ : syracuseStep 600803 = 901205) B901205
theorem B1354481 : Blo 175800 1354481 := bstep (se 2 (by rfl) ⟨507930, by rfl⟩ : syracuseStep 1354481 = 1015861) B1015861
theorem B371491 : Blo 175800 371491 := bstep (se 1 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 371491 = 557237) B557237
theorem B338833 : Blo 175800 338833 := bstep (se 2 (by rfl) ⟨127062, by rfl⟩ : syracuseStep 338833 = 254125) B254125
theorem B404369 : Blo 175800 404369 := bstep (se 2 (by rfl) ⟨151638, by rfl⟩ : syracuseStep 404369 = 303277) B303277
theorem B404387 : Blo 175800 404387 := bstep (se 1 (by rfl) ⟨303290, by rfl⟩ : syracuseStep 404387 = 606581) B606581
theorem B601073 : Blo 175800 601073 := bstep (se 2 (by rfl) ⟨225402, by rfl⟩ : syracuseStep 601073 = 450805) B450805
theorem B404561 : Blo 175800 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B535693 : Blo 175800 535693 := bstep (se 3 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 535693 = 200885) B200885
theorem B568579 : Blo 175800 568579 := bstep (se 1 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 568579 = 852869) B852869
theorem B634189 : Blo 175800 634189 := bstep (se 3 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 634189 = 237821) B237821
theorem B863729 : Blo 175800 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B601613 : Blo 175800 601613 := bstep (se 3 (by rfl) ⟨112802, by rfl⟩ : syracuseStep 601613 = 225605) B225605
theorem B601667 : Blo 175800 601667 := bstep (se 1 (by rfl) ⟨451250, by rfl⟩ : syracuseStep 601667 = 902501) B902501
theorem B405091 : Blo 175800 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B1224355 : Blo 175800 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B175811 : Blo 175800 175811 := bstep (se 1 (by rfl) ⟨131858, by rfl⟩ : syracuseStep 175811 = 263717) B263717
theorem B175827 : Blo 175800 175827 := bstep (se 1 (by rfl) ⟨131870, by rfl⟩ : syracuseStep 175827 = 263741) B263741
theorem B175843 : Blo 175800 175843 := bstep (se 1 (by rfl) ⟨131882, by rfl⟩ : syracuseStep 175843 = 263765) B263765
theorem B175859 : Blo 175800 175859 := bstep (se 1 (by rfl) ⟨131894, by rfl⟩ : syracuseStep 175859 = 263789) B263789
theorem B175875 : Blo 175800 175875 := bstep (se 1 (by rfl) ⟨131906, by rfl⟩ : syracuseStep 175875 = 263813) B263813
theorem B175891 : Blo 175800 175891 := bstep (se 1 (by rfl) ⟨131918, by rfl⟩ : syracuseStep 175891 = 263837) B263837
theorem B175907 : Blo 175800 175907 := bstep (se 1 (by rfl) ⟨131930, by rfl⟩ : syracuseStep 175907 = 263861) B263861
theorem B175923 : Blo 175800 175923 := bstep (se 1 (by rfl) ⟨131942, by rfl⟩ : syracuseStep 175923 = 263885) B263885
theorem B175939 : Blo 175800 175939 := bstep (se 1 (by rfl) ⟨131954, by rfl⟩ : syracuseStep 175939 = 263909) B263909
theorem B601937 : Blo 175800 601937 := bstep (se 2 (by rfl) ⟨225726, by rfl⟩ : syracuseStep 601937 = 451453) B451453
theorem B175955 : Blo 175800 175955 := bstep (se 1 (by rfl) ⟨131966, by rfl⟩ : syracuseStep 175955 = 263933) B263933
theorem B175971 : Blo 175800 175971 := bstep (se 1 (by rfl) ⟨131978, by rfl⟩ : syracuseStep 175971 = 263957) B263957
theorem B962417 : Blo 175800 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B175987 : Blo 175800 175987 := bstep (se 1 (by rfl) ⟨131990, by rfl⟩ : syracuseStep 175987 = 263981) B263981
theorem B176003 : Blo 175800 176003 := bstep (se 1 (by rfl) ⟨132002, by rfl⟩ : syracuseStep 176003 = 264005) B264005
theorem B176019 : Blo 175800 176019 := bstep (se 1 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 176019 = 264029) B264029
theorem B176035 : Blo 175800 176035 := bstep (se 1 (by rfl) ⟨132026, by rfl⟩ : syracuseStep 176035 = 264053) B264053
theorem B503729 : Blo 175800 503729 := bstep (se 2 (by rfl) ⟨188898, by rfl⟩ : syracuseStep 503729 = 377797) B377797
theorem B339889 : Blo 175800 339889 := bstep (se 2 (by rfl) ⟨127458, by rfl⟩ : syracuseStep 339889 = 254917) B254917
theorem B176051 : Blo 175800 176051 := bstep (se 1 (by rfl) ⟨132038, by rfl⟩ : syracuseStep 176051 = 264077) B264077
theorem B176067 : Blo 175800 176067 := bstep (se 1 (by rfl) ⟨132050, by rfl⟩ : syracuseStep 176067 = 264101) B264101
theorem B176083 : Blo 175800 176083 := bstep (se 1 (by rfl) ⟨132062, by rfl⟩ : syracuseStep 176083 = 264125) B264125
theorem B176099 : Blo 175800 176099 := bstep (se 1 (by rfl) ⟨132074, by rfl⟩ : syracuseStep 176099 = 264149) B264149
theorem B176115 : Blo 175800 176115 := bstep (se 1 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 176115 = 264173) B264173
theorem B176131 : Blo 175800 176131 := bstep (se 1 (by rfl) ⟨132098, by rfl⟩ : syracuseStep 176131 = 264197) B264197
theorem B176147 : Blo 175800 176147 := bstep (se 1 (by rfl) ⟨132110, by rfl⟩ : syracuseStep 176147 = 264221) B264221
theorem B176163 : Blo 175800 176163 := bstep (se 1 (by rfl) ⟨132122, by rfl⟩ : syracuseStep 176163 = 264245) B264245
theorem B176179 : Blo 175800 176179 := bstep (se 1 (by rfl) ⟨132134, by rfl⟩ : syracuseStep 176179 = 264269) B264269
theorem B176195 : Blo 175800 176195 := bstep (se 1 (by rfl) ⟨132146, by rfl⟩ : syracuseStep 176195 = 264293) B264293
theorem B176211 : Blo 175800 176211 := bstep (se 1 (by rfl) ⟨132158, by rfl⟩ : syracuseStep 176211 = 264317) B264317
theorem B176227 : Blo 175800 176227 := bstep (se 1 (by rfl) ⟨132170, by rfl⟩ : syracuseStep 176227 = 264341) B264341
theorem B503921 : Blo 175800 503921 := bstep (se 2 (by rfl) ⟨188970, by rfl⟩ : syracuseStep 503921 = 377941) B377941
theorem B176243 : Blo 175800 176243 := bstep (se 1 (by rfl) ⟨132182, by rfl⟩ : syracuseStep 176243 = 264365) B264365
theorem B176259 : Blo 175800 176259 := bstep (se 1 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 176259 = 264389) B264389
theorem B176275 : Blo 175800 176275 := bstep (se 1 (by rfl) ⟨132206, by rfl⟩ : syracuseStep 176275 = 264413) B264413
theorem B176291 : Blo 175800 176291 := bstep (se 1 (by rfl) ⟨132218, by rfl⟩ : syracuseStep 176291 = 264437) B264437
theorem B176307 : Blo 175800 176307 := bstep (se 1 (by rfl) ⟨132230, by rfl⟩ : syracuseStep 176307 = 264461) B264461
theorem B176323 : Blo 175800 176323 := bstep (se 1 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 176323 = 264485) B264485
theorem B176339 : Blo 175800 176339 := bstep (se 1 (by rfl) ⟨132254, by rfl⟩ : syracuseStep 176339 = 264509) B264509
theorem B176355 : Blo 175800 176355 := bstep (se 1 (by rfl) ⟨132266, by rfl⟩ : syracuseStep 176355 = 264533) B264533
theorem B176371 : Blo 175800 176371 := bstep (se 1 (by rfl) ⟨132278, by rfl⟩ : syracuseStep 176371 = 264557) B264557
theorem B176387 : Blo 175800 176387 := bstep (se 1 (by rfl) ⟨132290, by rfl⟩ : syracuseStep 176387 = 264581) B264581
theorem B176403 : Blo 175800 176403 := bstep (se 1 (by rfl) ⟨132302, by rfl⟩ : syracuseStep 176403 = 264605) B264605
theorem B176419 : Blo 175800 176419 := bstep (se 1 (by rfl) ⟨132314, by rfl⟩ : syracuseStep 176419 = 264629) B264629
theorem B176435 : Blo 175800 176435 := bstep (se 1 (by rfl) ⟨132326, by rfl⟩ : syracuseStep 176435 = 264653) B264653
theorem B176451 : Blo 175800 176451 := bstep (se 1 (by rfl) ⟨132338, by rfl⟩ : syracuseStep 176451 = 264677) B264677
theorem B340291 : Blo 175800 340291 := bstep (se 1 (by rfl) ⟨255218, by rfl⟩ : syracuseStep 340291 = 510437) B510437
theorem B176467 : Blo 175800 176467 := bstep (se 1 (by rfl) ⟨132350, by rfl⟩ : syracuseStep 176467 = 264701) B264701
theorem B176483 : Blo 175800 176483 := bstep (se 1 (by rfl) ⟨132362, by rfl⟩ : syracuseStep 176483 = 264725) B264725
theorem B602477 : Blo 175800 602477 := bstep (se 3 (by rfl) ⟨112964, by rfl⟩ : syracuseStep 602477 = 225929) B225929
theorem B340337 : Blo 175800 340337 := bstep (se 2 (by rfl) ⟨127626, by rfl⟩ : syracuseStep 340337 = 255253) B255253
theorem B176499 : Blo 175800 176499 := bstep (se 1 (by rfl) ⟨132374, by rfl⟩ : syracuseStep 176499 = 264749) B264749
theorem B176515 : Blo 175800 176515 := bstep (se 1 (by rfl) ⟨132386, by rfl⟩ : syracuseStep 176515 = 264773) B264773
theorem B176531 : Blo 175800 176531 := bstep (se 1 (by rfl) ⟨132398, by rfl⟩ : syracuseStep 176531 = 264797) B264797
theorem B176547 : Blo 175800 176547 := bstep (se 1 (by rfl) ⟨132410, by rfl⟩ : syracuseStep 176547 = 264821) B264821
theorem B602531 : Blo 175800 602531 := bstep (se 1 (by rfl) ⟨451898, by rfl⟩ : syracuseStep 602531 = 903797) B903797
theorem B176563 : Blo 175800 176563 := bstep (se 1 (by rfl) ⟨132422, by rfl⟩ : syracuseStep 176563 = 264845) B264845
theorem B176579 : Blo 175800 176579 := bstep (se 1 (by rfl) ⟨132434, by rfl⟩ : syracuseStep 176579 = 264869) B264869
theorem B176595 : Blo 175800 176595 := bstep (se 1 (by rfl) ⟨132446, by rfl⟩ : syracuseStep 176595 = 264893) B264893
theorem B176611 : Blo 175800 176611 := bstep (se 1 (by rfl) ⟨132458, by rfl⟩ : syracuseStep 176611 = 264917) B264917
theorem B176627 : Blo 175800 176627 := bstep (se 1 (by rfl) ⟨132470, by rfl⟩ : syracuseStep 176627 = 264941) B264941
theorem B176643 : Blo 175800 176643 := bstep (se 1 (by rfl) ⟨132482, by rfl⟩ : syracuseStep 176643 = 264965) B264965
theorem B2241037 : Blo 175800 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B176659 : Blo 175800 176659 := bstep (se 1 (by rfl) ⟨132494, by rfl⟩ : syracuseStep 176659 = 264989) B264989
theorem B176675 : Blo 175800 176675 := bstep (se 1 (by rfl) ⟨132506, by rfl⟩ : syracuseStep 176675 = 265013) B265013
theorem B176691 : Blo 175800 176691 := bstep (se 1 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 176691 = 265037) B265037
theorem B176707 : Blo 175800 176707 := bstep (se 1 (by rfl) ⟨132530, by rfl⟩ : syracuseStep 176707 = 265061) B265061
theorem B176723 : Blo 175800 176723 := bstep (se 1 (by rfl) ⟨132542, by rfl⟩ : syracuseStep 176723 = 265085) B265085
theorem B176739 : Blo 175800 176739 := bstep (se 1 (by rfl) ⟨132554, by rfl⟩ : syracuseStep 176739 = 265109) B265109
theorem B176755 : Blo 175800 176755 := bstep (se 1 (by rfl) ⟨132566, by rfl⟩ : syracuseStep 176755 = 265133) B265133
theorem B176771 : Blo 175800 176771 := bstep (se 1 (by rfl) ⟨132578, by rfl⟩ : syracuseStep 176771 = 265157) B265157
theorem B340625 : Blo 175800 340625 := bstep (se 2 (by rfl) ⟨127734, by rfl⟩ : syracuseStep 340625 = 255469) B255469
theorem B176787 : Blo 175800 176787 := bstep (se 1 (by rfl) ⟨132590, by rfl⟩ : syracuseStep 176787 = 265181) B265181
theorem B176803 : Blo 175800 176803 := bstep (se 1 (by rfl) ⟨132602, by rfl⟩ : syracuseStep 176803 = 265205) B265205
theorem B602801 : Blo 175800 602801 := bstep (se 2 (by rfl) ⟨226050, by rfl⟩ : syracuseStep 602801 = 452101) B452101
theorem B176819 : Blo 175800 176819 := bstep (se 1 (by rfl) ⟨132614, by rfl⟩ : syracuseStep 176819 = 265229) B265229
theorem B176835 : Blo 175800 176835 := bstep (se 1 (by rfl) ⟨132626, by rfl⟩ : syracuseStep 176835 = 265253) B265253
theorem B176851 : Blo 175800 176851 := bstep (se 1 (by rfl) ⟨132638, by rfl⟩ : syracuseStep 176851 = 265277) B265277
theorem B176867 : Blo 175800 176867 := bstep (se 1 (by rfl) ⟨132650, by rfl⟩ : syracuseStep 176867 = 265301) B265301
theorem B176883 : Blo 175800 176883 := bstep (se 1 (by rfl) ⟨132662, by rfl⟩ : syracuseStep 176883 = 265325) B265325
theorem B176899 : Blo 175800 176899 := bstep (se 1 (by rfl) ⟨132674, by rfl⟩ : syracuseStep 176899 = 265349) B265349
theorem B176915 : Blo 175800 176915 := bstep (se 1 (by rfl) ⟨132686, by rfl⟩ : syracuseStep 176915 = 265373) B265373
theorem B176931 : Blo 175800 176931 := bstep (se 1 (by rfl) ⟨132698, by rfl⟩ : syracuseStep 176931 = 265397) B265397
theorem B176947 : Blo 175800 176947 := bstep (se 1 (by rfl) ⟨132710, by rfl⟩ : syracuseStep 176947 = 265421) B265421
theorem B176963 : Blo 175800 176963 := bstep (se 1 (by rfl) ⟨132722, by rfl⟩ : syracuseStep 176963 = 265445) B265445
theorem B176979 : Blo 175800 176979 := bstep (se 1 (by rfl) ⟨132734, by rfl⟩ : syracuseStep 176979 = 265469) B265469
theorem B176995 : Blo 175800 176995 := bstep (se 1 (by rfl) ⟨132746, by rfl⟩ : syracuseStep 176995 = 265493) B265493
theorem B177011 : Blo 175800 177011 := bstep (se 1 (by rfl) ⟨132758, by rfl⟩ : syracuseStep 177011 = 265517) B265517
theorem B177027 : Blo 175800 177027 := bstep (se 1 (by rfl) ⟨132770, by rfl⟩ : syracuseStep 177027 = 265541) B265541
theorem B177043 : Blo 175800 177043 := bstep (se 1 (by rfl) ⟨132782, by rfl⟩ : syracuseStep 177043 = 265565) B265565
theorem B177059 : Blo 175800 177059 := bstep (se 1 (by rfl) ⟨132794, by rfl⟩ : syracuseStep 177059 = 265589) B265589
theorem B734129 : Blo 175800 734129 := bstep (se 2 (by rfl) ⟨275298, by rfl⟩ : syracuseStep 734129 = 550597) B550597
theorem B177075 : Blo 175800 177075 := bstep (se 1 (by rfl) ⟨132806, by rfl⟩ : syracuseStep 177075 = 265613) B265613
theorem B177091 : Blo 175800 177091 := bstep (se 1 (by rfl) ⟨132818, by rfl⟩ : syracuseStep 177091 = 265637) B265637
theorem B177107 : Blo 175800 177107 := bstep (se 1 (by rfl) ⟨132830, by rfl⟩ : syracuseStep 177107 = 265661) B265661
theorem B177123 : Blo 175800 177123 := bstep (se 1 (by rfl) ⟨132842, by rfl⟩ : syracuseStep 177123 = 265685) B265685
theorem B177139 : Blo 175800 177139 := bstep (se 1 (by rfl) ⟨132854, by rfl⟩ : syracuseStep 177139 = 265709) B265709
theorem B177155 : Blo 175800 177155 := bstep (se 1 (by rfl) ⟨132866, by rfl⟩ : syracuseStep 177155 = 265733) B265733
theorem B177171 : Blo 175800 177171 := bstep (se 1 (by rfl) ⟨132878, by rfl⟩ : syracuseStep 177171 = 265757) B265757
theorem B177187 : Blo 175800 177187 := bstep (se 1 (by rfl) ⟨132890, by rfl⟩ : syracuseStep 177187 = 265781) B265781
theorem B177203 : Blo 175800 177203 := bstep (se 1 (by rfl) ⟨132902, by rfl⟩ : syracuseStep 177203 = 265805) B265805
theorem B177219 : Blo 175800 177219 := bstep (se 1 (by rfl) ⟨132914, by rfl⟩ : syracuseStep 177219 = 265829) B265829
theorem B504913 : Blo 175800 504913 := bstep (se 2 (by rfl) ⟨189342, by rfl⟩ : syracuseStep 504913 = 378685) B378685
theorem B177235 : Blo 175800 177235 := bstep (se 1 (by rfl) ⟨132926, by rfl⟩ : syracuseStep 177235 = 265853) B265853
theorem B177251 : Blo 175800 177251 := bstep (se 1 (by rfl) ⟨132938, by rfl⟩ : syracuseStep 177251 = 265877) B265877
theorem B177267 : Blo 175800 177267 := bstep (se 1 (by rfl) ⟨132950, by rfl⟩ : syracuseStep 177267 = 265901) B265901
theorem B177283 : Blo 175800 177283 := bstep (se 1 (by rfl) ⟨132962, by rfl⟩ : syracuseStep 177283 = 265925) B265925
theorem B177299 : Blo 175800 177299 := bstep (se 1 (by rfl) ⟨132974, by rfl⟩ : syracuseStep 177299 = 265949) B265949
theorem B177315 : Blo 175800 177315 := bstep (se 1 (by rfl) ⟨132986, by rfl⟩ : syracuseStep 177315 = 265973) B265973
theorem B177331 : Blo 175800 177331 := bstep (se 1 (by rfl) ⟨132998, by rfl⟩ : syracuseStep 177331 = 265997) B265997
theorem B177347 : Blo 175800 177347 := bstep (se 1 (by rfl) ⟨133010, by rfl⟩ : syracuseStep 177347 = 266021) B266021
theorem B603341 : Blo 175800 603341 := bstep (se 3 (by rfl) ⟨113126, by rfl⟩ : syracuseStep 603341 = 226253) B226253
theorem B177363 : Blo 175800 177363 := bstep (se 1 (by rfl) ⟨133022, by rfl⟩ : syracuseStep 177363 = 266045) B266045
theorem B177379 : Blo 175800 177379 := bstep (se 1 (by rfl) ⟨133034, by rfl⟩ : syracuseStep 177379 = 266069) B266069
theorem B898289 : Blo 175800 898289 := bstep (se 2 (by rfl) ⟨336858, by rfl⟩ : syracuseStep 898289 = 673717) B673717
theorem B242929 : Blo 175800 242929 := bstep (se 2 (by rfl) ⟨91098, by rfl⟩ : syracuseStep 242929 = 182197) B182197
theorem B177395 : Blo 175800 177395 := bstep (se 1 (by rfl) ⟨133046, by rfl⟩ : syracuseStep 177395 = 266093) B266093
theorem B177411 : Blo 175800 177411 := bstep (se 1 (by rfl) ⟨133058, by rfl⟩ : syracuseStep 177411 = 266117) B266117
theorem B603395 : Blo 175800 603395 := bstep (se 1 (by rfl) ⟨452546, by rfl⟩ : syracuseStep 603395 = 905093) B905093
theorem B963845 : Blo 175800 963845 := bstep (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) B180721
theorem B177427 : Blo 175800 177427 := bstep (se 1 (by rfl) ⟨133070, by rfl⟩ : syracuseStep 177427 = 266141) B266141
theorem B177443 : Blo 175800 177443 := bstep (se 1 (by rfl) ⟨133082, by rfl⟩ : syracuseStep 177443 = 266165) B266165
theorem B177459 : Blo 175800 177459 := bstep (se 1 (by rfl) ⟨133094, by rfl⟩ : syracuseStep 177459 = 266189) B266189
theorem B177475 : Blo 175800 177475 := bstep (se 1 (by rfl) ⟨133106, by rfl⟩ : syracuseStep 177475 = 266213) B266213
theorem B177491 : Blo 175800 177491 := bstep (se 1 (by rfl) ⟨133118, by rfl⟩ : syracuseStep 177491 = 266237) B266237
theorem B505187 : Blo 175800 505187 := bstep (se 1 (by rfl) ⟨378890, by rfl⟩ : syracuseStep 505187 = 757781) B757781
theorem B177507 : Blo 175800 177507 := bstep (se 1 (by rfl) ⟨133130, by rfl⟩ : syracuseStep 177507 = 266261) B266261
theorem B177523 : Blo 175800 177523 := bstep (se 1 (by rfl) ⟨133142, by rfl⟩ : syracuseStep 177523 = 266285) B266285
theorem B177539 : Blo 175800 177539 := bstep (se 1 (by rfl) ⟨133154, by rfl⟩ : syracuseStep 177539 = 266309) B266309
theorem B177555 : Blo 175800 177555 := bstep (se 1 (by rfl) ⟨133166, by rfl⟩ : syracuseStep 177555 = 266333) B266333
theorem B177571 : Blo 175800 177571 := bstep (se 1 (by rfl) ⟨133178, by rfl⟩ : syracuseStep 177571 = 266357) B266357
theorem B570797 : Blo 175800 570797 := bstep (se 3 (by rfl) ⟨107024, by rfl⟩ : syracuseStep 570797 = 214049) B214049
theorem B177587 : Blo 175800 177587 := bstep (se 1 (by rfl) ⟨133190, by rfl⟩ : syracuseStep 177587 = 266381) B266381
theorem B177603 : Blo 175800 177603 := bstep (se 1 (by rfl) ⟨133202, by rfl⟩ : syracuseStep 177603 = 266405) B266405
theorem B177619 : Blo 175800 177619 := bstep (se 1 (by rfl) ⟨133214, by rfl⟩ : syracuseStep 177619 = 266429) B266429
theorem B177635 : Blo 175800 177635 := bstep (se 1 (by rfl) ⟨133226, by rfl⟩ : syracuseStep 177635 = 266453) B266453
theorem B341489 : Blo 175800 341489 := bstep (se 2 (by rfl) ⟨128058, by rfl⟩ : syracuseStep 341489 = 256117) B256117
theorem B177651 : Blo 175800 177651 := bstep (se 1 (by rfl) ⟨133238, by rfl⟩ : syracuseStep 177651 = 266477) B266477
theorem B177667 : Blo 175800 177667 := bstep (se 1 (by rfl) ⟨133250, by rfl⟩ : syracuseStep 177667 = 266501) B266501
theorem B767501 : Blo 175800 767501 := bstep (se 3 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 767501 = 287813) B287813
theorem B603665 : Blo 175800 603665 := bstep (se 2 (by rfl) ⟨226374, by rfl⟩ : syracuseStep 603665 = 452749) B452749
theorem B177683 : Blo 175800 177683 := bstep (se 1 (by rfl) ⟨133262, by rfl⟩ : syracuseStep 177683 = 266525) B266525
theorem B505379 : Blo 175800 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B177699 : Blo 175800 177699 := bstep (se 1 (by rfl) ⟨133274, by rfl⟩ : syracuseStep 177699 = 266549) B266549
theorem B177715 : Blo 175800 177715 := bstep (se 1 (by rfl) ⟨133286, by rfl⟩ : syracuseStep 177715 = 266573) B266573
theorem B177731 : Blo 175800 177731 := bstep (se 1 (by rfl) ⟨133298, by rfl⟩ : syracuseStep 177731 = 266597) B266597
theorem B177747 : Blo 175800 177747 := bstep (se 1 (by rfl) ⟨133310, by rfl⟩ : syracuseStep 177747 = 266621) B266621
theorem B177763 : Blo 175800 177763 := bstep (se 1 (by rfl) ⟨133322, by rfl⟩ : syracuseStep 177763 = 266645) B266645
theorem B177779 : Blo 175800 177779 := bstep (se 1 (by rfl) ⟨133334, by rfl⟩ : syracuseStep 177779 = 266669) B266669
theorem B177795 : Blo 175800 177795 := bstep (se 1 (by rfl) ⟨133346, by rfl⟩ : syracuseStep 177795 = 266693) B266693
theorem B177811 : Blo 175800 177811 := bstep (se 1 (by rfl) ⟨133358, by rfl⟩ : syracuseStep 177811 = 266717) B266717
theorem B177827 : Blo 175800 177827 := bstep (se 1 (by rfl) ⟨133370, by rfl⟩ : syracuseStep 177827 = 266741) B266741
theorem B177843 : Blo 175800 177843 := bstep (se 1 (by rfl) ⟨133382, by rfl⟩ : syracuseStep 177843 = 266765) B266765
theorem B177859 : Blo 175800 177859 := bstep (se 1 (by rfl) ⟨133394, by rfl⟩ : syracuseStep 177859 = 266789) B266789
theorem B177875 : Blo 175800 177875 := bstep (se 1 (by rfl) ⟨133406, by rfl⟩ : syracuseStep 177875 = 266813) B266813
theorem B177891 : Blo 175800 177891 := bstep (se 1 (by rfl) ⟨133418, by rfl⟩ : syracuseStep 177891 = 266837) B266837
theorem B177907 : Blo 175800 177907 := bstep (se 1 (by rfl) ⟨133430, by rfl⟩ : syracuseStep 177907 = 266861) B266861
theorem B177923 : Blo 175800 177923 := bstep (se 1 (by rfl) ⟨133442, by rfl⟩ : syracuseStep 177923 = 266885) B266885
theorem B177939 : Blo 175800 177939 := bstep (se 1 (by rfl) ⟨133454, by rfl⟩ : syracuseStep 177939 = 266909) B266909
theorem B177955 : Blo 175800 177955 := bstep (se 1 (by rfl) ⟨133466, by rfl⟩ : syracuseStep 177955 = 266933) B266933
theorem B177971 : Blo 175800 177971 := bstep (se 1 (by rfl) ⟨133478, by rfl⟩ : syracuseStep 177971 = 266957) B266957
theorem B177987 : Blo 175800 177987 := bstep (se 1 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 177987 = 266981) B266981
theorem B571217 : Blo 175800 571217 := bstep (se 2 (by rfl) ⟨214206, by rfl⟩ : syracuseStep 571217 = 428413) B428413
theorem B178003 : Blo 175800 178003 := bstep (se 1 (by rfl) ⟨133502, by rfl⟩ : syracuseStep 178003 = 267005) B267005
theorem B178019 : Blo 175800 178019 := bstep (se 1 (by rfl) ⟨133514, by rfl⟩ : syracuseStep 178019 = 267029) B267029
theorem B767843 : Blo 175800 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B178035 : Blo 175800 178035 := bstep (se 1 (by rfl) ⟨133526, by rfl⟩ : syracuseStep 178035 = 267053) B267053
theorem B178051 : Blo 175800 178051 := bstep (se 1 (by rfl) ⟨133538, by rfl⟩ : syracuseStep 178051 = 267077) B267077
theorem B178067 : Blo 175800 178067 := bstep (se 1 (by rfl) ⟨133550, by rfl⟩ : syracuseStep 178067 = 267101) B267101
theorem B178083 : Blo 175800 178083 := bstep (se 1 (by rfl) ⟨133562, by rfl⟩ : syracuseStep 178083 = 267125) B267125
theorem B669617 : Blo 175800 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B178099 : Blo 175800 178099 := bstep (se 1 (by rfl) ⟨133574, by rfl⟩ : syracuseStep 178099 = 267149) B267149
theorem B178115 : Blo 175800 178115 := bstep (se 1 (by rfl) ⟨133586, by rfl⟩ : syracuseStep 178115 = 267173) B267173
theorem B1521605 : Blo 175800 1521605 := bstep (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) B285301
theorem B178131 : Blo 175800 178131 := bstep (se 1 (by rfl) ⟨133598, by rfl⟩ : syracuseStep 178131 = 267197) B267197
theorem B178147 : Blo 175800 178147 := bstep (se 1 (by rfl) ⟨133610, by rfl⟩ : syracuseStep 178147 = 267221) B267221
theorem B178163 : Blo 175800 178163 := bstep (se 1 (by rfl) ⟨133622, by rfl⟩ : syracuseStep 178163 = 267245) B267245
theorem B178179 : Blo 175800 178179 := bstep (se 1 (by rfl) ⟨133634, by rfl⟩ : syracuseStep 178179 = 267269) B267269
theorem B178195 : Blo 175800 178195 := bstep (se 1 (by rfl) ⟨133646, by rfl⟩ : syracuseStep 178195 = 267293) B267293
theorem B178211 : Blo 175800 178211 := bstep (se 1 (by rfl) ⟨133658, by rfl⟩ : syracuseStep 178211 = 267317) B267317
theorem B604205 : Blo 175800 604205 := bstep (se 3 (by rfl) ⟨113288, by rfl⟩ : syracuseStep 604205 = 226577) B226577
theorem B178227 : Blo 175800 178227 := bstep (se 1 (by rfl) ⟨133670, by rfl⟩ : syracuseStep 178227 = 267341) B267341
theorem B178243 : Blo 175800 178243 := bstep (se 1 (by rfl) ⟨133682, by rfl⟩ : syracuseStep 178243 = 267365) B267365
theorem B178259 : Blo 175800 178259 := bstep (se 1 (by rfl) ⟨133694, by rfl⟩ : syracuseStep 178259 = 267389) B267389
theorem B178275 : Blo 175800 178275 := bstep (se 1 (by rfl) ⟨133706, by rfl⟩ : syracuseStep 178275 = 267413) B267413
theorem B604259 : Blo 175800 604259 := bstep (se 1 (by rfl) ⟨453194, by rfl⟩ : syracuseStep 604259 = 906389) B906389
theorem B178291 : Blo 175800 178291 := bstep (se 1 (by rfl) ⟨133718, by rfl⟩ : syracuseStep 178291 = 267437) B267437
theorem B178307 : Blo 175800 178307 := bstep (se 1 (by rfl) ⟨133730, by rfl⟩ : syracuseStep 178307 = 267461) B267461
theorem B178323 : Blo 175800 178323 := bstep (se 1 (by rfl) ⟨133742, by rfl⟩ : syracuseStep 178323 = 267485) B267485
theorem B178339 : Blo 175800 178339 := bstep (se 1 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 178339 = 267509) B267509
theorem B178355 : Blo 175800 178355 := bstep (se 1 (by rfl) ⟨133766, by rfl⟩ : syracuseStep 178355 = 267533) B267533
theorem B178371 : Blo 175800 178371 := bstep (se 1 (by rfl) ⟨133778, by rfl⟩ : syracuseStep 178371 = 267557) B267557
theorem B178387 : Blo 175800 178387 := bstep (se 1 (by rfl) ⟨133790, by rfl⟩ : syracuseStep 178387 = 267581) B267581
theorem B178403 : Blo 175800 178403 := bstep (se 1 (by rfl) ⟨133802, by rfl⟩ : syracuseStep 178403 = 267605) B267605
theorem B1620209 : Blo 175800 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B178419 : Blo 175800 178419 := bstep (se 1 (by rfl) ⟨133814, by rfl⟩ : syracuseStep 178419 = 267629) B267629
theorem B178435 : Blo 175800 178435 := bstep (se 1 (by rfl) ⟨133826, by rfl⟩ : syracuseStep 178435 = 267653) B267653
theorem B178451 : Blo 175800 178451 := bstep (se 1 (by rfl) ⟨133838, by rfl⟩ : syracuseStep 178451 = 267677) B267677
theorem B178467 : Blo 175800 178467 := bstep (se 1 (by rfl) ⟨133850, by rfl⟩ : syracuseStep 178467 = 267701) B267701
theorem B178483 : Blo 175800 178483 := bstep (se 1 (by rfl) ⟨133862, by rfl⟩ : syracuseStep 178483 = 267725) B267725
theorem B178499 : Blo 175800 178499 := bstep (se 1 (by rfl) ⟨133874, by rfl⟩ : syracuseStep 178499 = 267749) B267749
theorem B506189 : Blo 175800 506189 := bstep (se 3 (by rfl) ⟨94910, by rfl⟩ : syracuseStep 506189 = 189821) B189821
theorem B178515 : Blo 175800 178515 := bstep (se 1 (by rfl) ⟨133886, by rfl⟩ : syracuseStep 178515 = 267773) B267773
theorem B178531 : Blo 175800 178531 := bstep (se 1 (by rfl) ⟨133898, by rfl⟩ : syracuseStep 178531 = 267797) B267797
theorem B604529 : Blo 175800 604529 := bstep (se 2 (by rfl) ⟨226698, by rfl⟩ : syracuseStep 604529 = 453397) B453397
theorem B178547 : Blo 175800 178547 := bstep (se 1 (by rfl) ⟨133910, by rfl⟩ : syracuseStep 178547 = 267821) B267821
theorem B178563 : Blo 175800 178563 := bstep (se 1 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 178563 = 267845) B267845
theorem B178579 : Blo 175800 178579 := bstep (se 1 (by rfl) ⟨133934, by rfl⟩ : syracuseStep 178579 = 267869) B267869
theorem B178595 : Blo 175800 178595 := bstep (se 1 (by rfl) ⟨133946, by rfl⟩ : syracuseStep 178595 = 267893) B267893
theorem B178611 : Blo 175800 178611 := bstep (se 1 (by rfl) ⟨133958, by rfl⟩ : syracuseStep 178611 = 267917) B267917
theorem B178627 : Blo 175800 178627 := bstep (se 1 (by rfl) ⟨133970, by rfl⟩ : syracuseStep 178627 = 267941) B267941
theorem B178643 : Blo 175800 178643 := bstep (se 1 (by rfl) ⟨133982, by rfl⟩ : syracuseStep 178643 = 267965) B267965
theorem B178659 : Blo 175800 178659 := bstep (se 1 (by rfl) ⟨133994, by rfl⟩ : syracuseStep 178659 = 267989) B267989
theorem B178675 : Blo 175800 178675 := bstep (se 1 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 178675 = 268013) B268013
theorem B506371 : Blo 175800 506371 := bstep (se 1 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 506371 = 759557) B759557
theorem B178691 : Blo 175800 178691 := bstep (se 1 (by rfl) ⟨134018, by rfl⟩ : syracuseStep 178691 = 268037) B268037
theorem B178707 : Blo 175800 178707 := bstep (se 1 (by rfl) ⟨134030, by rfl⟩ : syracuseStep 178707 = 268061) B268061
theorem B178723 : Blo 175800 178723 := bstep (se 1 (by rfl) ⟨134042, by rfl⟩ : syracuseStep 178723 = 268085) B268085
theorem B178739 : Blo 175800 178739 := bstep (se 1 (by rfl) ⟨134054, by rfl⟩ : syracuseStep 178739 = 268109) B268109
theorem B178755 : Blo 175800 178755 := bstep (se 1 (by rfl) ⟨134066, by rfl⟩ : syracuseStep 178755 = 268133) B268133
theorem B178771 : Blo 175800 178771 := bstep (se 1 (by rfl) ⟨134078, by rfl⟩ : syracuseStep 178771 = 268157) B268157
theorem B178787 : Blo 175800 178787 := bstep (se 1 (by rfl) ⟨134090, by rfl⟩ : syracuseStep 178787 = 268181) B268181
theorem B178803 : Blo 175800 178803 := bstep (se 1 (by rfl) ⟨134102, by rfl⟩ : syracuseStep 178803 = 268205) B268205
theorem B178819 : Blo 175800 178819 := bstep (se 1 (by rfl) ⟨134114, by rfl⟩ : syracuseStep 178819 = 268229) B268229
theorem B178835 : Blo 175800 178835 := bstep (se 1 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 178835 = 268253) B268253
theorem B899747 : Blo 175800 899747 := bstep (se 1 (by rfl) ⟨674810, by rfl⟩ : syracuseStep 899747 = 1349621) B1349621
theorem B178851 : Blo 175800 178851 := bstep (se 1 (by rfl) ⟨134138, by rfl⟩ : syracuseStep 178851 = 268277) B268277
theorem B178867 : Blo 175800 178867 := bstep (se 1 (by rfl) ⟨134150, by rfl⟩ : syracuseStep 178867 = 268301) B268301
theorem B178883 : Blo 175800 178883 := bstep (se 1 (by rfl) ⟨134162, by rfl⟩ : syracuseStep 178883 = 268325) B268325
theorem B178899 : Blo 175800 178899 := bstep (se 1 (by rfl) ⟨134174, by rfl⟩ : syracuseStep 178899 = 268349) B268349
theorem B178915 : Blo 175800 178915 := bstep (se 1 (by rfl) ⟨134186, by rfl⟩ : syracuseStep 178915 = 268373) B268373
theorem B178931 : Blo 175800 178931 := bstep (se 1 (by rfl) ⟨134198, by rfl⟩ : syracuseStep 178931 = 268397) B268397
theorem B178947 : Blo 175800 178947 := bstep (se 1 (by rfl) ⟨134210, by rfl⟩ : syracuseStep 178947 = 268421) B268421
theorem B178963 : Blo 175800 178963 := bstep (se 1 (by rfl) ⟨134222, by rfl⟩ : syracuseStep 178963 = 268445) B268445
theorem B178979 : Blo 175800 178979 := bstep (se 1 (by rfl) ⟨134234, by rfl⟩ : syracuseStep 178979 = 268469) B268469
theorem B178995 : Blo 175800 178995 := bstep (se 1 (by rfl) ⟨134246, by rfl⟩ : syracuseStep 178995 = 268493) B268493
theorem B179011 : Blo 175800 179011 := bstep (se 1 (by rfl) ⟨134258, by rfl⟩ : syracuseStep 179011 = 268517) B268517
theorem B179027 : Blo 175800 179027 := bstep (se 1 (by rfl) ⟨134270, by rfl⟩ : syracuseStep 179027 = 268541) B268541
theorem B179043 : Blo 175800 179043 := bstep (se 1 (by rfl) ⟨134282, by rfl⟩ : syracuseStep 179043 = 268565) B268565
theorem B179059 : Blo 175800 179059 := bstep (se 1 (by rfl) ⟨134294, by rfl⟩ : syracuseStep 179059 = 268589) B268589
theorem B211843 : Blo 175800 211843 := bstep (se 1 (by rfl) ⟨158882, by rfl⟩ : syracuseStep 211843 = 317765) B317765
theorem B179075 : Blo 175800 179075 := bstep (se 1 (by rfl) ⟨134306, by rfl⟩ : syracuseStep 179075 = 268613) B268613
theorem B605069 : Blo 175800 605069 := bstep (se 3 (by rfl) ⟨113450, by rfl⟩ : syracuseStep 605069 = 226901) B226901
theorem B342929 : Blo 175800 342929 := bstep (se 2 (by rfl) ⟨128598, by rfl⟩ : syracuseStep 342929 = 257197) B257197
theorem B179091 : Blo 175800 179091 := bstep (se 1 (by rfl) ⟨134318, by rfl⟩ : syracuseStep 179091 = 268637) B268637
theorem B179107 : Blo 175800 179107 := bstep (se 1 (by rfl) ⟨134330, by rfl⟩ : syracuseStep 179107 = 268661) B268661
theorem B179123 : Blo 175800 179123 := bstep (se 1 (by rfl) ⟨134342, by rfl⟩ : syracuseStep 179123 = 268685) B268685
theorem B179139 : Blo 175800 179139 := bstep (se 1 (by rfl) ⟨134354, by rfl⟩ : syracuseStep 179139 = 268709) B268709
theorem B605123 : Blo 175800 605123 := bstep (se 1 (by rfl) ⟨453842, by rfl⟩ : syracuseStep 605123 = 907685) B907685
theorem B179155 : Blo 175800 179155 := bstep (se 1 (by rfl) ⟨134366, by rfl⟩ : syracuseStep 179155 = 268733) B268733
theorem B179171 : Blo 175800 179171 := bstep (se 1 (by rfl) ⟨134378, by rfl⟩ : syracuseStep 179171 = 268757) B268757
theorem B506861 : Blo 175800 506861 := bstep (se 3 (by rfl) ⟨95036, by rfl⟩ : syracuseStep 506861 = 190073) B190073
theorem B179187 : Blo 175800 179187 := bstep (se 1 (by rfl) ⟨134390, by rfl⟩ : syracuseStep 179187 = 268781) B268781
theorem B179203 : Blo 175800 179203 := bstep (se 1 (by rfl) ⟨134402, by rfl⟩ : syracuseStep 179203 = 268805) B268805
theorem B211987 : Blo 175800 211987 := bstep (se 1 (by rfl) ⟨158990, by rfl⟩ : syracuseStep 211987 = 317981) B317981
theorem B179219 : Blo 175800 179219 := bstep (se 1 (by rfl) ⟨134414, by rfl⟩ : syracuseStep 179219 = 268829) B268829
theorem B179235 : Blo 175800 179235 := bstep (se 1 (by rfl) ⟨134426, by rfl⟩ : syracuseStep 179235 = 268853) B268853
theorem B375857 : Blo 175800 375857 := bstep (se 2 (by rfl) ⟨140946, by rfl⟩ : syracuseStep 375857 = 281893) B281893
theorem B179251 : Blo 175800 179251 := bstep (se 1 (by rfl) ⟨134438, by rfl⟩ : syracuseStep 179251 = 268877) B268877
theorem B179267 : Blo 175800 179267 := bstep (se 1 (by rfl) ⟨134450, by rfl⟩ : syracuseStep 179267 = 268901) B268901
theorem B179283 : Blo 175800 179283 := bstep (se 1 (by rfl) ⟨134462, by rfl⟩ : syracuseStep 179283 = 268925) B268925
theorem B1129571 : Blo 175800 1129571 := bstep (se 1 (by rfl) ⟨847178, by rfl⟩ : syracuseStep 1129571 = 1694357) B1694357
theorem B179299 : Blo 175800 179299 := bstep (se 1 (by rfl) ⟨134474, by rfl⟩ : syracuseStep 179299 = 268949) B268949
theorem B179315 : Blo 175800 179315 := bstep (se 1 (by rfl) ⟨134486, by rfl⟩ : syracuseStep 179315 = 268973) B268973
theorem B179331 : Blo 175800 179331 := bstep (se 1 (by rfl) ⟨134498, by rfl⟩ : syracuseStep 179331 = 268997) B268997
theorem B965773 : Blo 175800 965773 := bstep (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) B362165
theorem B179347 : Blo 175800 179347 := bstep (se 1 (by rfl) ⟨134510, by rfl⟩ : syracuseStep 179347 = 269021) B269021
theorem B179363 : Blo 175800 179363 := bstep (se 1 (by rfl) ⟨134522, by rfl⟩ : syracuseStep 179363 = 269045) B269045
theorem B179379 : Blo 175800 179379 := bstep (se 1 (by rfl) ⟨134534, by rfl⟩ : syracuseStep 179379 = 269069) B269069
theorem B179395 : Blo 175800 179395 := bstep (se 1 (by rfl) ⟨134546, by rfl⟩ : syracuseStep 179395 = 269093) B269093
theorem B605393 : Blo 175800 605393 := bstep (se 2 (by rfl) ⟨227022, by rfl⟩ : syracuseStep 605393 = 454045) B454045
theorem B179411 : Blo 175800 179411 := bstep (se 1 (by rfl) ⟨134558, by rfl⟩ : syracuseStep 179411 = 269117) B269117
theorem B179427 : Blo 175800 179427 := bstep (se 1 (by rfl) ⟨134570, by rfl⟩ : syracuseStep 179427 = 269141) B269141
theorem B179443 : Blo 175800 179443 := bstep (se 1 (by rfl) ⟨134582, by rfl⟩ : syracuseStep 179443 = 269165) B269165
theorem B179459 : Blo 175800 179459 := bstep (se 1 (by rfl) ⟨134594, by rfl⟩ : syracuseStep 179459 = 269189) B269189
theorem B179475 : Blo 175800 179475 := bstep (se 1 (by rfl) ⟨134606, by rfl⟩ : syracuseStep 179475 = 269213) B269213
theorem B179491 : Blo 175800 179491 := bstep (se 1 (by rfl) ⟨134618, by rfl⟩ : syracuseStep 179491 = 269237) B269237
theorem B179507 : Blo 175800 179507 := bstep (se 1 (by rfl) ⟨134630, by rfl⟩ : syracuseStep 179507 = 269261) B269261
theorem B179523 : Blo 175800 179523 := bstep (se 1 (by rfl) ⟨134642, by rfl⟩ : syracuseStep 179523 = 269285) B269285
theorem B179539 : Blo 175800 179539 := bstep (se 1 (by rfl) ⟨134654, by rfl⟩ : syracuseStep 179539 = 269309) B269309
theorem B671075 : Blo 175800 671075 := bstep (se 1 (by rfl) ⟨503306, by rfl⟩ : syracuseStep 671075 = 1006613) B1006613
theorem B179555 : Blo 175800 179555 := bstep (se 1 (by rfl) ⟨134666, by rfl⟩ : syracuseStep 179555 = 269333) B269333
theorem B179571 : Blo 175800 179571 := bstep (se 1 (by rfl) ⟨134678, by rfl⟩ : syracuseStep 179571 = 269357) B269357
theorem B179587 : Blo 175800 179587 := bstep (se 1 (by rfl) ⟨134690, by rfl⟩ : syracuseStep 179587 = 269381) B269381
theorem B179603 : Blo 175800 179603 := bstep (se 1 (by rfl) ⟨134702, by rfl⟩ : syracuseStep 179603 = 269405) B269405
theorem B408995 : Blo 175800 408995 := bstep (se 1 (by rfl) ⟨306746, by rfl⟩ : syracuseStep 408995 = 613493) B613493
theorem B179619 : Blo 175800 179619 := bstep (se 1 (by rfl) ⟨134714, by rfl⟩ : syracuseStep 179619 = 269429) B269429
theorem B179635 : Blo 175800 179635 := bstep (se 1 (by rfl) ⟨134726, by rfl⟩ : syracuseStep 179635 = 269453) B269453
theorem B179651 : Blo 175800 179651 := bstep (se 1 (by rfl) ⟨134738, by rfl⟩ : syracuseStep 179651 = 269477) B269477
theorem B900557 : Blo 175800 900557 := bstep (se 3 (by rfl) ⟨168854, by rfl⟩ : syracuseStep 900557 = 337709) B337709
theorem B179667 : Blo 175800 179667 := bstep (se 1 (by rfl) ⟨134750, by rfl⟩ : syracuseStep 179667 = 269501) B269501
theorem B179683 : Blo 175800 179683 := bstep (se 1 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 179683 = 269525) B269525
theorem B179699 : Blo 175800 179699 := bstep (se 1 (by rfl) ⟨134774, by rfl⟩ : syracuseStep 179699 = 269549) B269549
theorem B179715 : Blo 175800 179715 := bstep (se 1 (by rfl) ⟨134786, by rfl⟩ : syracuseStep 179715 = 269573) B269573
theorem B179731 : Blo 175800 179731 := bstep (se 1 (by rfl) ⟨134798, by rfl⟩ : syracuseStep 179731 = 269597) B269597
theorem B179747 : Blo 175800 179747 := bstep (se 1 (by rfl) ⟨134810, by rfl⟩ : syracuseStep 179747 = 269621) B269621
theorem B179763 : Blo 175800 179763 := bstep (se 1 (by rfl) ⟨134822, by rfl⟩ : syracuseStep 179763 = 269645) B269645
theorem B179779 : Blo 175800 179779 := bstep (se 1 (by rfl) ⟨134834, by rfl⟩ : syracuseStep 179779 = 269669) B269669
theorem B1293893 : Blo 175800 1293893 := bstep (se 4 (by rfl) ⟨121302, by rfl⟩ : syracuseStep 1293893 = 242605) B242605
theorem B179795 : Blo 175800 179795 := bstep (se 1 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 179795 = 269693) B269693
theorem B343697 : Blo 175800 343697 := bstep (se 2 (by rfl) ⟨128886, by rfl⟩ : syracuseStep 343697 = 257773) B257773
theorem B605933 : Blo 175800 605933 := bstep (se 3 (by rfl) ⟨113612, by rfl⟩ : syracuseStep 605933 = 227225) B227225
theorem B605987 : Blo 175800 605987 := bstep (se 1 (by rfl) ⟨454490, by rfl⟩ : syracuseStep 605987 = 908981) B908981
theorem B376643 : Blo 175800 376643 := bstep (se 1 (by rfl) ⟨282482, by rfl⟩ : syracuseStep 376643 = 564965) B564965
theorem B606257 : Blo 175800 606257 := bstep (se 2 (by rfl) ⟨227346, by rfl⟩ : syracuseStep 606257 = 454693) B454693
theorem B3031181 : Blo 175800 3031181 := bstep (se 3 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 3031181 = 1136693) B1136693
theorem B508045 : Blo 175800 508045 := bstep (se 3 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 508045 = 190517) B190517
theorem B1097891 : Blo 175800 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B606403 : Blo 175800 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B966917 : Blo 175800 966917 := bstep (se 4 (by rfl) ⟨90648, by rfl⟩ : syracuseStep 966917 = 181297) B181297
theorem B672077 : Blo 175800 672077 := bstep (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) B252029
theorem B606797 : Blo 175800 606797 := bstep (se 3 (by rfl) ⟨113774, by rfl⟩ : syracuseStep 606797 = 227549) B227549
theorem B967373 : Blo 175800 967373 := bstep (se 3 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 967373 = 362765) B362765
theorem B377617 : Blo 175800 377617 := bstep (se 2 (by rfl) ⟨141606, by rfl⟩ : syracuseStep 377617 = 283213) B283213
theorem B967565 : Blo 175800 967565 := bstep (se 3 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 967565 = 362837) B362837
theorem B1426403 : Blo 175800 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1360867 : Blo 175800 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B377873 : Blo 175800 377873 := bstep (se 2 (by rfl) ⟨141702, by rfl⟩ : syracuseStep 377873 = 283405) B283405
theorem B1131569 : Blo 175800 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B574627 : Blo 175800 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B509105 : Blo 175800 509105 := bstep (se 2 (by rfl) ⟨190914, by rfl⟩ : syracuseStep 509105 = 381829) B381829
theorem B574897 : Blo 175800 574897 := bstep (se 2 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 574897 = 431173) B431173
theorem B345617 : Blo 175800 345617 := bstep (se 2 (by rfl) ⟨129606, by rfl⟩ : syracuseStep 345617 = 259213) B259213
theorem B182035 : Blo 175800 182035 := bstep (se 1 (by rfl) ⟨136526, by rfl⟩ : syracuseStep 182035 = 273053) B273053
theorem B509777 : Blo 175800 509777 := bstep (se 2 (by rfl) ⟨191166, by rfl⟩ : syracuseStep 509777 = 382333) B382333
theorem B1099909 : Blo 175800 1099909 := bstep (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) B206233
theorem B3786979 : Blo 175800 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B379171 : Blo 175800 379171 := bstep (se 1 (by rfl) ⟨284378, by rfl⟩ : syracuseStep 379171 = 568757) B568757
theorem B903473 : Blo 175800 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B674189 : Blo 175800 674189 := bstep (se 3 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 674189 = 252821) B252821
theorem B608771 : Blo 175800 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B510563 : Blo 175800 510563 := bstep (se 1 (by rfl) ⟨382922, by rfl⟩ : syracuseStep 510563 = 765845) B765845
theorem B379505 : Blo 175800 379505 := bstep (se 2 (by rfl) ⟨142314, by rfl⟩ : syracuseStep 379505 = 284629) B284629
theorem B543395 : Blo 175800 543395 := bstep (se 1 (by rfl) ⟨407546, by rfl⟩ : syracuseStep 543395 = 815093) B815093
theorem B1231523 : Blo 175800 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B1133261 : Blo 175800 1133261 := bstep (se 3 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 1133261 = 424973) B424973
theorem B215779 : Blo 175800 215779 := bstep (se 1 (by rfl) ⟨161834, by rfl⟩ : syracuseStep 215779 = 323669) B323669
theorem B609059 : Blo 175800 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B445297 : Blo 175800 445297 := bstep (se 2 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 445297 = 333973) B333973
theorem B510893 : Blo 175800 510893 := bstep (se 3 (by rfl) ⟨95792, by rfl⟩ : syracuseStep 510893 = 191585) B191585
theorem B510961 : Blo 175800 510961 := bstep (se 2 (by rfl) ⟨191610, by rfl⟩ : syracuseStep 510961 = 383221) B383221
theorem B445571 : Blo 175800 445571 := bstep (se 1 (by rfl) ⟨334178, by rfl⟩ : syracuseStep 445571 = 668357) B668357
theorem B674993 : Blo 175800 674993 := bstep (se 2 (by rfl) ⟨253122, by rfl⟩ : syracuseStep 674993 = 506245) B506245
theorem B642275 : Blo 175800 642275 := bstep (se 1 (by rfl) ⟨481706, by rfl⟩ : syracuseStep 642275 = 963413) B963413
theorem B511235 : Blo 175800 511235 := bstep (se 1 (by rfl) ⟨383426, by rfl⟩ : syracuseStep 511235 = 766853) B766853
theorem B544013 : Blo 175800 544013 := bstep (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) B204005
theorem B445763 : Blo 175800 445763 := bstep (se 1 (by rfl) ⟨334322, by rfl⟩ : syracuseStep 445763 = 668645) B668645
theorem B1003013 : Blo 175800 1003013 := bstep (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) B188065
theorem B577091 : Blo 175800 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B904931 : Blo 175800 904931 := bstep (se 1 (by rfl) ⟨678698, by rfl⟩ : syracuseStep 904931 = 1357397) B1357397
theorem B380675 : Blo 175800 380675 := bstep (se 1 (by rfl) ⟨285506, by rfl⟩ : syracuseStep 380675 = 571013) B571013
theorem B675661 : Blo 175800 675661 := bstep (se 3 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 675661 = 253373) B253373
theorem B282611 : Blo 175800 282611 := bstep (se 1 (by rfl) ⟨211958, by rfl⟩ : syracuseStep 282611 = 423917) B423917
theorem B512173 : Blo 175800 512173 := bstep (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) B192065
theorem B1003697 : Blo 175800 1003697 := bstep (se 2 (by rfl) ⟨376386, by rfl⟩ : syracuseStep 1003697 = 752773) B752773
theorem B479459 : Blo 175800 479459 := bstep (se 1 (by rfl) ⟨359594, by rfl⟩ : syracuseStep 479459 = 719189) B719189
theorem B446705 : Blo 175800 446705 := bstep (se 2 (by rfl) ⟨167514, by rfl⟩ : syracuseStep 446705 = 335029) B335029
theorem B446755 : Blo 175800 446755 := bstep (se 1 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 446755 = 670133) B670133
theorem B610673 : Blo 175800 610673 := bstep (se 2 (by rfl) ⟨229002, by rfl⟩ : syracuseStep 610673 = 458005) B458005
theorem B282995 : Blo 175800 282995 := bstep (se 1 (by rfl) ⟨212246, by rfl⟩ : syracuseStep 282995 = 424493) B424493
theorem B446897 : Blo 175800 446897 := bstep (se 2 (by rfl) ⟨167586, by rfl⟩ : syracuseStep 446897 = 335173) B335173
theorem B283123 : Blo 175800 283123 := bstep (se 1 (by rfl) ⟨212342, by rfl⟩ : syracuseStep 283123 = 424685) B424685
theorem B905741 : Blo 175800 905741 := bstep (se 3 (by rfl) ⟨169826, by rfl⟩ : syracuseStep 905741 = 339653) B339653
theorem B479825 : Blo 175800 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B676451 : Blo 175800 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B643889 : Blo 175800 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B250771 : Blo 175800 250771 := bstep (se 1 (by rfl) ⟨188078, by rfl⟩ : syracuseStep 250771 = 376157) B376157
theorem B250867 : Blo 175800 250867 := bstep (se 1 (by rfl) ⟨188150, by rfl⟩ : syracuseStep 250867 = 376301) B376301
theorem B480323 : Blo 175800 480323 := bstep (se 1 (by rfl) ⟨360242, by rfl⟩ : syracuseStep 480323 = 720485) B720485
theorem B283841 : Blo 175800 283841 := bstep (se 2 (by rfl) ⟨106440, by rfl⟩ : syracuseStep 283841 = 212881) B212881
theorem B677105 : Blo 175800 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B578897 : Blo 175800 578897 := bstep (se 2 (by rfl) ⟨217086, by rfl⟩ : syracuseStep 578897 = 434173) B434173
theorem B644465 : Blo 175800 644465 := bstep (se 2 (by rfl) ⟨241674, by rfl⟩ : syracuseStep 644465 = 483349) B483349
theorem B284033 : Blo 175800 284033 := bstep (se 2 (by rfl) ⟨106512, by rfl⟩ : syracuseStep 284033 = 213025) B213025
theorem B447889 : Blo 175800 447889 := bstep (se 2 (by rfl) ⟨167958, by rfl⟩ : syracuseStep 447889 = 335917) B335917
theorem B251363 : Blo 175800 251363 := bstep (se 1 (by rfl) ⟨188522, by rfl⟩ : syracuseStep 251363 = 377045) B377045
theorem B218611 : Blo 175800 218611 := bstep (se 1 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 218611 = 327917) B327917
theorem B1005155 : Blo 175800 1005155 := bstep (se 1 (by rfl) ⟨753866, by rfl⟩ : syracuseStep 1005155 = 1507733) B1507733
theorem B2184803 : Blo 175800 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B448163 : Blo 175800 448163 := bstep (se 1 (by rfl) ⟨336122, by rfl⟩ : syracuseStep 448163 = 672245) B672245
theorem B382691 : Blo 175800 382691 := bstep (se 1 (by rfl) ⟨287018, by rfl⟩ : syracuseStep 382691 = 574037) B574037
theorem B448355 : Blo 175800 448355 := bstep (se 1 (by rfl) ⟨336266, by rfl⟩ : syracuseStep 448355 = 672533) B672533
theorem B1103813 : Blo 175800 1103813 := bstep (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) B206965
theorem B382961 : Blo 175800 382961 := bstep (se 2 (by rfl) ⟨143610, by rfl⟩ : syracuseStep 382961 = 287221) B287221
theorem B252001 : Blo 175800 252001 := bstep (se 2 (by rfl) ⟨94500, by rfl⟩ : syracuseStep 252001 = 189001) B189001
theorem B514307 : Blo 175800 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B252337 : Blo 175800 252337 := bstep (se 2 (by rfl) ⟨94626, by rfl⟩ : syracuseStep 252337 = 189253) B189253
theorem B1530353 : Blo 175800 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B678563 : Blo 175800 678563 := bstep (se 1 (by rfl) ⟨508922, by rfl⟩ : syracuseStep 678563 = 1017845) B1017845
theorem B678577 : Blo 175800 678577 := bstep (se 2 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 678577 = 508933) B508933
theorem B514769 : Blo 175800 514769 := bstep (se 2 (by rfl) ⟨193038, by rfl⟩ : syracuseStep 514769 = 386077) B386077
theorem B449297 : Blo 175800 449297 := bstep (se 2 (by rfl) ⟨168486, by rfl⟩ : syracuseStep 449297 = 336973) B336973
theorem B449347 : Blo 175800 449347 := bstep (se 1 (by rfl) ⟨337010, by rfl⟩ : syracuseStep 449347 = 674021) B674021
theorem B645965 : Blo 175800 645965 := bstep (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) B242237
theorem B449489 : Blo 175800 449489 := bstep (se 2 (by rfl) ⟨168558, by rfl⟩ : syracuseStep 449489 = 337117) B337117
theorem B252929 : Blo 175800 252929 := bstep (se 2 (by rfl) ⟨94848, by rfl⟩ : syracuseStep 252929 = 189697) B189697
theorem B285763 : Blo 175800 285763 := bstep (se 1 (by rfl) ⟨214322, by rfl⟩ : syracuseStep 285763 = 428645) B428645
theorem B285859 : Blo 175800 285859 := bstep (se 1 (by rfl) ⟨214394, by rfl⟩ : syracuseStep 285859 = 428789) B428789
theorem B810253 : Blo 175800 810253 := bstep (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) B303845
theorem B286019 : Blo 175800 286019 := bstep (se 1 (by rfl) ⟨214514, by rfl⟩ : syracuseStep 286019 = 429029) B429029
theorem B908657 : Blo 175800 908657 := bstep (se 2 (by rfl) ⟨340746, by rfl⟩ : syracuseStep 908657 = 681493) B681493
theorem B515501 : Blo 175800 515501 := bstep (se 3 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 515501 = 193313) B193313
theorem B187843 : Blo 175800 187843 := bstep (se 1 (by rfl) ⟨140882, by rfl⟩ : syracuseStep 187843 = 281765) B281765
theorem B253459 : Blo 175800 253459 := bstep (se 1 (by rfl) ⟨190094, by rfl⟩ : syracuseStep 253459 = 380189) B380189
theorem B253795 : Blo 175800 253795 := bstep (se 1 (by rfl) ⟨190346, by rfl⟩ : syracuseStep 253795 = 380693) B380693
theorem B450481 : Blo 175800 450481 := bstep (se 2 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 450481 = 337861) B337861
theorem B680035 : Blo 175800 680035 := bstep (se 1 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 680035 = 1020053) B1020053
theorem B450755 : Blo 175800 450755 := bstep (se 1 (by rfl) ⟨338066, by rfl⟩ : syracuseStep 450755 = 676133) B676133
theorem B188659 : Blo 175800 188659 := bstep (se 1 (by rfl) ⟨141494, by rfl⟩ : syracuseStep 188659 = 282989) B282989
theorem B286993 : Blo 175800 286993 := bstep (se 2 (by rfl) ⟨107622, by rfl⟩ : syracuseStep 286993 = 215245) B215245
theorem B450947 : Blo 175800 450947 := bstep (se 1 (by rfl) ⟨338210, by rfl⟩ : syracuseStep 450947 = 676421) B676421
theorem B254353 : Blo 175800 254353 := bstep (se 2 (by rfl) ⟨95382, by rfl⟩ : syracuseStep 254353 = 190765) B190765
theorem B254387 : Blo 175800 254387 := bstep (se 1 (by rfl) ⟨190790, by rfl⟩ : syracuseStep 254387 = 381581) B381581
theorem B1008389 : Blo 175800 1008389 := bstep (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) B189073
theorem B910115 : Blo 175800 910115 := bstep (se 1 (by rfl) ⟨682586, by rfl⟩ : syracuseStep 910115 = 1365173) B1365173
theorem B4350833 : Blo 175800 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B1991537 : Blo 175800 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B320387 : Blo 175800 320387 := bstep (se 1 (by rfl) ⟨240290, by rfl⟩ : syracuseStep 320387 = 480581) B480581
theorem B254945 : Blo 175800 254945 := bstep (se 2 (by rfl) ⟨95604, by rfl⟩ : syracuseStep 254945 = 191209) B191209
theorem B255025 : Blo 175800 255025 := bstep (se 2 (by rfl) ⟨95634, by rfl⟩ : syracuseStep 255025 = 191269) B191269
theorem B1008845 : Blo 175800 1008845 := bstep (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) B378317
theorem B451889 : Blo 175800 451889 := bstep (se 2 (by rfl) ⟨169458, by rfl⟩ : syracuseStep 451889 = 338917) B338917
theorem B1402181 : Blo 175800 1402181 := bstep (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) B262909
theorem B320849 : Blo 175800 320849 := bstep (se 2 (by rfl) ⟨120318, by rfl⟩ : syracuseStep 320849 = 240637) B240637
theorem B451939 : Blo 175800 451939 := bstep (se 1 (by rfl) ⟨338954, by rfl⟩ : syracuseStep 451939 = 677909) B677909
theorem B452081 : Blo 175800 452081 := bstep (se 2 (by rfl) ⟨169530, by rfl⟩ : syracuseStep 452081 = 339061) B339061
theorem B222851 : Blo 175800 222851 := bstep (se 1 (by rfl) ⟨167138, by rfl⟩ : syracuseStep 222851 = 334277) B334277
theorem B1074865 : Blo 175800 1074865 := bstep (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) B806149
theorem B1697507 : Blo 175800 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B255811 : Blo 175800 255811 := bstep (se 1 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 255811 = 383717) B383717
theorem B583537 : Blo 175800 583537 := bstep (se 2 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 583537 = 437653) B437653
theorem B255955 : Blo 175800 255955 := bstep (se 1 (by rfl) ⟨191966, by rfl⟩ : syracuseStep 255955 = 383933) B383933
theorem B2418929 : Blo 175800 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B682253 : Blo 175800 682253 := bstep (se 3 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 682253 = 255845) B255845
theorem B223555 : Blo 175800 223555 := bstep (se 1 (by rfl) ⟨167666, by rfl⟩ : syracuseStep 223555 = 335333) B335333
theorem B223651 : Blo 175800 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B453073 : Blo 175800 453073 := bstep (se 2 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 453073 = 339805) B339805
theorem B289379 : Blo 175800 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B191203 : Blo 175800 191203 := bstep (se 1 (by rfl) ⟨143402, by rfl⟩ : syracuseStep 191203 = 286805) B286805
theorem B453347 : Blo 175800 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B813901 : Blo 175800 813901 := bstep (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) B305213
theorem B224147 : Blo 175800 224147 := bstep (se 1 (by rfl) ⟨168110, by rfl⟩ : syracuseStep 224147 = 336221) B336221
theorem B453539 : Blo 175800 453539 := bstep (se 1 (by rfl) ⟨340154, by rfl⟩ : syracuseStep 453539 = 680309) B680309
theorem B290129 : Blo 175800 290129 := bstep (se 2 (by rfl) ⟨108798, by rfl⟩ : syracuseStep 290129 = 217597) B217597
theorem B224851 : Blo 175800 224851 := bstep (se 1 (by rfl) ⟨168638, by rfl⟩ : syracuseStep 224851 = 337277) B337277
theorem B847523 : Blo 175800 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B224947 : Blo 175800 224947 := bstep (se 1 (by rfl) ⟨168710, by rfl⟩ : syracuseStep 224947 = 337421) B337421
theorem B4419269 : Blo 175800 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B454481 : Blo 175800 454481 := bstep (se 2 (by rfl) ⟨170430, by rfl⟩ : syracuseStep 454481 = 340861) B340861
theorem B454531 : Blo 175800 454531 := bstep (se 1 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 454531 = 681797) B681797
theorem B454673 : Blo 175800 454673 := bstep (se 2 (by rfl) ⟨170502, by rfl⟩ : syracuseStep 454673 = 341005) B341005
theorem B1011761 : Blo 175800 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B225443 : Blo 175800 225443 := bstep (se 1 (by rfl) ⟨169082, by rfl⟩ : syracuseStep 225443 = 338165) B338165
theorem B848369 : Blo 175800 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B422513 : Blo 175800 422513 := bstep (se 2 (by rfl) ⟨158442, by rfl⟩ : syracuseStep 422513 = 316885) B316885
theorem B389873 : Blo 175800 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B848717 : Blo 175800 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B226147 : Blo 175800 226147 := bstep (se 1 (by rfl) ⟨169610, by rfl⟩ : syracuseStep 226147 = 339221) B339221
theorem B1143665 : Blo 175800 1143665 := bstep (se 2 (by rfl) ⟨428874, by rfl⟩ : syracuseStep 1143665 = 857749) B857749
theorem B226243 : Blo 175800 226243 := bstep (se 1 (by rfl) ⟨169682, by rfl⟩ : syracuseStep 226243 = 339365) B339365
theorem B1340387 : Blo 175800 1340387 := bstep (se 1 (by rfl) ⟨1005290, by rfl⟩ : syracuseStep 1340387 = 2010581) B2010581
theorem B2454725 : Blo 175800 2454725 := bstep (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) B460261
theorem B750961 : Blo 175800 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B226739 : Blo 175800 226739 := bstep (se 1 (by rfl) ⟨170054, by rfl⟩ : syracuseStep 226739 = 340109) B340109
theorem B1013219 : Blo 175800 1013219 := bstep (se 1 (by rfl) ⟨759914, by rfl⟩ : syracuseStep 1013219 = 1519829) B1519829
theorem B718733 : Blo 175800 718733 := bstep (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) B269525
theorem B686051 : Blo 175800 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B2488333 : Blo 175800 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B227443 : Blo 175800 227443 := bstep (se 1 (by rfl) ⟨170582, by rfl⟩ : syracuseStep 227443 = 341165) B341165
theorem B227539 : Blo 175800 227539 := bstep (se 1 (by rfl) ⟨170654, by rfl⟩ : syracuseStep 227539 = 341309) B341309
theorem B2291939 : Blo 175800 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B1014221 : Blo 175800 1014221 := bstep (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) B380333
theorem B359075 : Blo 175800 359075 := bstep (se 1 (by rfl) ⟨269306, by rfl⟩ : syracuseStep 359075 = 538613) B538613
theorem B916145 : Blo 175800 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B1702853 : Blo 175800 1702853 := bstep (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) B319285
theorem B3013685 : Blo 175800 3013685 := bstep (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) B282533
theorem B1146125 : Blo 175800 1146125 := bstep (se 3 (by rfl) ⟨214898, by rfl⟩ : syracuseStep 1146125 = 429797) B429797
theorem B1507085 : Blo 175800 1507085 := bstep (se 3 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 1507085 = 565157) B565157
theorem B2817845 : Blo 175800 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B327523 : Blo 175800 327523 := bstep (se 1 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 327523 = 491285) B491285
theorem B491437 : Blo 175800 491437 := bstep (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) B184289
theorem B1343789 : Blo 175800 1343789 := bstep (se 3 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 1343789 = 503921) B503921
theorem B328151 : Blo 175800 328151 := bstep (se 1 (by rfl) ⟨246113, by rfl⟩ : syracuseStep 328151 = 492227) B492227
theorem B950935 : Blo 175800 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B754379 : Blo 175800 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B6489011 : Blo 175800 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B230411 : Blo 175800 230411 := bstep (se 1 (by rfl) ⟨172808, by rfl⟩ : syracuseStep 230411 = 345617) B345617
theorem B1508483 : Blo 175800 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B197815 : Blo 175800 197815 := bstep (se 1 (by rfl) ⟨148361, by rfl⟩ : syracuseStep 197815 = 296723) B296723
theorem B197995 : Blo 175800 197995 := bstep (se 1 (by rfl) ⟨148496, by rfl⟩ : syracuseStep 197995 = 296993) B296993
theorem B198103 : Blo 175800 198103 := bstep (se 1 (by rfl) ⟨148577, by rfl⟩ : syracuseStep 198103 = 297155) B297155
theorem B361945 : Blo 175800 361945 := bstep (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) B271459
theorem B263705 : Blo 175800 263705 := bstep (se 2 (by rfl) ⟨98889, by rfl⟩ : syracuseStep 263705 = 197779) B197779
theorem B263819 : Blo 175800 263819 := bstep (se 1 (by rfl) ⟨197864, by rfl⟩ : syracuseStep 263819 = 395729) B395729
theorem B198283 : Blo 175800 198283 := bstep (se 1 (by rfl) ⟨148712, by rfl⟩ : syracuseStep 198283 = 297425) B297425
theorem B263831 : Blo 175800 263831 := bstep (se 1 (by rfl) ⟨197873, by rfl⟩ : syracuseStep 263831 = 395747) B395747
theorem B263897 : Blo 175800 263897 := bstep (se 2 (by rfl) ⟨98961, by rfl⟩ : syracuseStep 263897 = 197923) B197923
theorem B198391 : Blo 175800 198391 := bstep (se 1 (by rfl) ⟨148793, by rfl⟩ : syracuseStep 198391 = 297587) B297587
theorem B362263 : Blo 175800 362263 := bstep (se 1 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 362263 = 543395) B543395
theorem B821015 : Blo 175800 821015 := bstep (se 1 (by rfl) ⟨615761, by rfl⟩ : syracuseStep 821015 = 1231523) B1231523
theorem B755507 : Blo 175800 755507 := bstep (se 1 (by rfl) ⟨566630, by rfl⟩ : syracuseStep 755507 = 1133261) B1133261
theorem B264011 : Blo 175800 264011 := bstep (se 1 (by rfl) ⟨198008, by rfl⟩ : syracuseStep 264011 = 396017) B396017
theorem B264023 : Blo 175800 264023 := bstep (se 1 (by rfl) ⟨198017, by rfl⟩ : syracuseStep 264023 = 396035) B396035
theorem B722819 : Blo 175800 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B264089 : Blo 175800 264089 := bstep (se 2 (by rfl) ⟨99033, by rfl⟩ : syracuseStep 264089 = 198067) B198067
theorem B198571 : Blo 175800 198571 := bstep (se 1 (by rfl) ⟨148928, by rfl⟩ : syracuseStep 198571 = 297857) B297857
theorem B264203 : Blo 175800 264203 := bstep (se 1 (by rfl) ⟨198152, by rfl⟩ : syracuseStep 264203 = 396305) B396305
theorem B264215 : Blo 175800 264215 := bstep (se 1 (by rfl) ⟨198161, by rfl⟩ : syracuseStep 264215 = 396323) B396323
theorem B198679 : Blo 175800 198679 := bstep (se 1 (by rfl) ⟨149009, by rfl⟩ : syracuseStep 198679 = 298019) B298019
theorem B297047 : Blo 175800 297047 := bstep (se 1 (by rfl) ⟨222785, by rfl⟩ : syracuseStep 297047 = 445571) B445571
theorem B264281 : Blo 175800 264281 := bstep (se 2 (by rfl) ⟨99105, by rfl⟩ : syracuseStep 264281 = 198211) B198211
theorem B428183 : Blo 175800 428183 := bstep (se 1 (by rfl) ⟨321137, by rfl⟩ : syracuseStep 428183 = 642275) B642275
theorem B362675 : Blo 175800 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B264395 : Blo 175800 264395 := bstep (se 1 (by rfl) ⟨198296, by rfl⟩ : syracuseStep 264395 = 396593) B396593
theorem B198859 : Blo 175800 198859 := bstep (se 1 (by rfl) ⟨149144, by rfl⟩ : syracuseStep 198859 = 298289) B298289
theorem B297175 : Blo 175800 297175 := bstep (se 1 (by rfl) ⟨222881, by rfl⟩ : syracuseStep 297175 = 445763) B445763
theorem B264407 : Blo 175800 264407 := bstep (se 1 (by rfl) ⟨198305, by rfl⟩ : syracuseStep 264407 = 396611) B396611
theorem B264473 : Blo 175800 264473 := bstep (se 2 (by rfl) ⟨99177, by rfl⟩ : syracuseStep 264473 = 198355) B198355
theorem B198967 : Blo 175800 198967 := bstep (se 1 (by rfl) ⟨149225, by rfl⟩ : syracuseStep 198967 = 298451) B298451
theorem B395585 : Blo 175800 395585 := bstep (se 2 (by rfl) ⟨148344, by rfl⟩ : syracuseStep 395585 = 296689) B296689
theorem B723275 : Blo 175800 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B3869045 : Blo 175800 3869045 := bstep (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) B362723
theorem B264587 : Blo 175800 264587 := bstep (se 1 (by rfl) ⟨198440, by rfl⟩ : syracuseStep 264587 = 396881) B396881
theorem B264599 : Blo 175800 264599 := bstep (se 1 (by rfl) ⟨198449, by rfl⟩ : syracuseStep 264599 = 396899) B396899
theorem B264665 : Blo 175800 264665 := bstep (se 2 (by rfl) ⟨99249, by rfl⟩ : syracuseStep 264665 = 198499) B198499
theorem B199147 : Blo 175800 199147 := bstep (se 1 (by rfl) ⟨149360, by rfl⟩ : syracuseStep 199147 = 298721) B298721
theorem B395801 : Blo 175800 395801 := bstep (se 2 (by rfl) ⟨148425, by rfl⟩ : syracuseStep 395801 = 296851) B296851
theorem B264779 : Blo 175800 264779 := bstep (se 1 (by rfl) ⟨198584, by rfl⟩ : syracuseStep 264779 = 397169) B397169
theorem B264791 : Blo 175800 264791 := bstep (se 1 (by rfl) ⟨198593, by rfl⟩ : syracuseStep 264791 = 397187) B397187
theorem B199255 : Blo 175800 199255 := bstep (se 1 (by rfl) ⟨149441, by rfl⟩ : syracuseStep 199255 = 298883) B298883
theorem B395891 : Blo 175800 395891 := bstep (se 1 (by rfl) ⟨296918, by rfl⟩ : syracuseStep 395891 = 593837) B593837
theorem B395927 : Blo 175800 395927 := bstep (se 1 (by rfl) ⟨296945, by rfl⟩ : syracuseStep 395927 = 593891) B593891
theorem B264857 : Blo 175800 264857 := bstep (se 2 (by rfl) ⟨99321, by rfl⟩ : syracuseStep 264857 = 198643) B198643
theorem B264971 : Blo 175800 264971 := bstep (se 1 (by rfl) ⟨198728, by rfl⟩ : syracuseStep 264971 = 397457) B397457
theorem B199435 : Blo 175800 199435 := bstep (se 1 (by rfl) ⟨149576, by rfl⟩ : syracuseStep 199435 = 299153) B299153
theorem B264983 : Blo 175800 264983 := bstep (se 1 (by rfl) ⟨198737, by rfl⟩ : syracuseStep 264983 = 397475) B397475
theorem B396107 : Blo 175800 396107 := bstep (se 1 (by rfl) ⟨297080, by rfl⟩ : syracuseStep 396107 = 594161) B594161
theorem B297803 : Blo 175800 297803 := bstep (se 1 (by rfl) ⟨223352, by rfl⟩ : syracuseStep 297803 = 446705) B446705
theorem B265049 : Blo 175800 265049 := bstep (se 2 (by rfl) ⟨99393, by rfl⟩ : syracuseStep 265049 = 198787) B198787
theorem B199543 : Blo 175800 199543 := bstep (se 1 (by rfl) ⟨149657, by rfl⟩ : syracuseStep 199543 = 299315) B299315
theorem B396161 : Blo 175800 396161 := bstep (se 2 (by rfl) ⟨148560, by rfl⟩ : syracuseStep 396161 = 297121) B297121
theorem B297931 : Blo 175800 297931 := bstep (se 1 (by rfl) ⟨223448, by rfl⟩ : syracuseStep 297931 = 446897) B446897
theorem B265163 : Blo 175800 265163 := bstep (se 1 (by rfl) ⟨198872, by rfl⟩ : syracuseStep 265163 = 397745) B397745
theorem B265175 : Blo 175800 265175 := bstep (se 1 (by rfl) ⟨198881, by rfl⟩ : syracuseStep 265175 = 397763) B397763
theorem B5049305 : Blo 175800 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B265241 : Blo 175800 265241 := bstep (se 2 (by rfl) ⟨99465, by rfl⟩ : syracuseStep 265241 = 198931) B198931
theorem B199723 : Blo 175800 199723 := bstep (se 1 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 199723 = 299585) B299585
theorem B1149997 : Blo 175800 1149997 := bstep (se 3 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 1149997 = 431249) B431249
theorem B396377 : Blo 175800 396377 := bstep (se 2 (by rfl) ⟨148641, by rfl⟩ : syracuseStep 396377 = 297283) B297283
theorem B298073 : Blo 175800 298073 := bstep (se 2 (by rfl) ⟨111777, by rfl⟩ : syracuseStep 298073 = 223555) B223555
theorem B265355 : Blo 175800 265355 := bstep (se 1 (by rfl) ⟨199016, by rfl⟩ : syracuseStep 265355 = 398033) B398033
theorem B265367 : Blo 175800 265367 := bstep (se 1 (by rfl) ⟨199025, by rfl⟩ : syracuseStep 265367 = 398051) B398051
theorem B199831 : Blo 175800 199831 := bstep (se 1 (by rfl) ⟨149873, by rfl⟩ : syracuseStep 199831 = 299747) B299747
theorem B396467 : Blo 175800 396467 := bstep (se 1 (by rfl) ⟨297350, by rfl⟩ : syracuseStep 396467 = 594701) B594701
theorem B396503 : Blo 175800 396503 := bstep (se 1 (by rfl) ⟨297377, by rfl⟩ : syracuseStep 396503 = 594755) B594755
theorem B298201 : Blo 175800 298201 := bstep (se 2 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 298201 = 223651) B223651
theorem B265433 : Blo 175800 265433 := bstep (se 2 (by rfl) ⟨99537, by rfl⟩ : syracuseStep 265433 = 199075) B199075
theorem B265547 : Blo 175800 265547 := bstep (se 1 (by rfl) ⟨199160, by rfl⟩ : syracuseStep 265547 = 398321) B398321
theorem B200011 : Blo 175800 200011 := bstep (se 1 (by rfl) ⟨150008, by rfl⟩ : syracuseStep 200011 = 300017) B300017
theorem B265559 : Blo 175800 265559 := bstep (se 1 (by rfl) ⟨199169, by rfl⟩ : syracuseStep 265559 = 398339) B398339
theorem B396683 : Blo 175800 396683 := bstep (se 1 (by rfl) ⟨297512, by rfl⟩ : syracuseStep 396683 = 595025) B595025
theorem B265625 : Blo 175800 265625 := bstep (se 2 (by rfl) ⟨99609, by rfl⟩ : syracuseStep 265625 = 199219) B199219
theorem B200119 : Blo 175800 200119 := bstep (se 1 (by rfl) ⟨150089, by rfl⟩ : syracuseStep 200119 = 300179) B300179
theorem B396737 : Blo 175800 396737 := bstep (se 2 (by rfl) ⟨148776, by rfl⟩ : syracuseStep 396737 = 297553) B297553
theorem B265739 : Blo 175800 265739 := bstep (se 1 (by rfl) ⟨199304, by rfl⟩ : syracuseStep 265739 = 398609) B398609
theorem B265751 : Blo 175800 265751 := bstep (se 1 (by rfl) ⟨199313, by rfl⟩ : syracuseStep 265751 = 398627) B398627
theorem B593459 : Blo 175800 593459 := bstep (se 1 (by rfl) ⟨445094, by rfl⟩ : syracuseStep 593459 = 890189) B890189
theorem B429643 : Blo 175800 429643 := bstep (se 1 (by rfl) ⟨322232, by rfl⟩ : syracuseStep 429643 = 644465) B644465
theorem B265817 : Blo 175800 265817 := bstep (se 2 (by rfl) ⟨99681, by rfl⟩ : syracuseStep 265817 = 199363) B199363
theorem B200299 : Blo 175800 200299 := bstep (se 1 (by rfl) ⟨150224, by rfl⟩ : syracuseStep 200299 = 300449) B300449
theorem B396953 : Blo 175800 396953 := bstep (se 2 (by rfl) ⟨148857, by rfl⟩ : syracuseStep 396953 = 297715) B297715
theorem B757421 : Blo 175800 757421 := bstep (se 3 (by rfl) ⟨142016, by rfl⟩ : syracuseStep 757421 = 284033) B284033
theorem B265931 : Blo 175800 265931 := bstep (se 1 (by rfl) ⟨199448, by rfl⟩ : syracuseStep 265931 = 398897) B398897
theorem B265943 : Blo 175800 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B200407 : Blo 175800 200407 := bstep (se 1 (by rfl) ⟨150305, by rfl⟩ : syracuseStep 200407 = 300611) B300611
theorem B397043 : Blo 175800 397043 := bstep (se 1 (by rfl) ⟨297782, by rfl⟩ : syracuseStep 397043 = 595565) B595565
theorem B1085201 : Blo 175800 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B397079 : Blo 175800 397079 := bstep (se 1 (by rfl) ⟨297809, by rfl⟩ : syracuseStep 397079 = 595619) B595619
theorem B298775 : Blo 175800 298775 := bstep (se 1 (by rfl) ⟨224081, by rfl⟩ : syracuseStep 298775 = 448163) B448163
theorem B266009 : Blo 175800 266009 := bstep (se 2 (by rfl) ⟨99753, by rfl⟩ : syracuseStep 266009 = 199507) B199507
theorem B593729 : Blo 175800 593729 := bstep (se 2 (by rfl) ⟨222648, by rfl⟩ : syracuseStep 593729 = 445297) B445297
theorem B266123 : Blo 175800 266123 := bstep (se 1 (by rfl) ⟨199592, by rfl⟩ : syracuseStep 266123 = 399185) B399185
theorem B200587 : Blo 175800 200587 := bstep (se 1 (by rfl) ⟨150440, by rfl⟩ : syracuseStep 200587 = 300881) B300881
theorem B298903 : Blo 175800 298903 := bstep (se 1 (by rfl) ⟨224177, by rfl⟩ : syracuseStep 298903 = 448355) B448355
theorem B266135 : Blo 175800 266135 := bstep (se 1 (by rfl) ⟨199601, by rfl⟩ : syracuseStep 266135 = 399203) B399203
theorem B397259 : Blo 175800 397259 := bstep (se 1 (by rfl) ⟨297944, by rfl⟩ : syracuseStep 397259 = 595889) B595889
theorem B266201 : Blo 175800 266201 := bstep (se 2 (by rfl) ⟨99825, by rfl⟩ : syracuseStep 266201 = 199651) B199651
theorem B200695 : Blo 175800 200695 := bstep (se 1 (by rfl) ⟨150521, by rfl⟩ : syracuseStep 200695 = 301043) B301043
theorem B397313 : Blo 175800 397313 := bstep (se 2 (by rfl) ⟨148992, by rfl⟩ : syracuseStep 397313 = 297985) B297985
theorem B1511459 : Blo 175800 1511459 := bstep (se 1 (by rfl) ⟨1133594, by rfl⟩ : syracuseStep 1511459 = 2267189) B2267189
theorem B266315 : Blo 175800 266315 := bstep (se 1 (by rfl) ⟨199736, by rfl⟩ : syracuseStep 266315 = 399473) B399473
theorem B266327 : Blo 175800 266327 := bstep (se 1 (by rfl) ⟨199745, by rfl⟩ : syracuseStep 266327 = 399491) B399491
theorem B1347677 : Blo 175800 1347677 := bstep (se 3 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 1347677 = 505379) B505379
theorem B266393 : Blo 175800 266393 := bstep (se 2 (by rfl) ⟨99897, by rfl⟩ : syracuseStep 266393 = 199795) B199795
theorem B200875 : Blo 175800 200875 := bstep (se 1 (by rfl) ⟨150656, by rfl⟩ : syracuseStep 200875 = 301313) B301313
theorem B397529 : Blo 175800 397529 := bstep (se 2 (by rfl) ⟨149073, by rfl⟩ : syracuseStep 397529 = 298147) B298147
theorem B266507 : Blo 175800 266507 := bstep (se 1 (by rfl) ⟨199880, by rfl⟩ : syracuseStep 266507 = 399761) B399761
theorem B266519 : Blo 175800 266519 := bstep (se 1 (by rfl) ⟨199889, by rfl⟩ : syracuseStep 266519 = 399779) B399779
theorem B200983 : Blo 175800 200983 := bstep (se 1 (by rfl) ⟨150737, by rfl⟩ : syracuseStep 200983 = 301475) B301475
theorem B397619 : Blo 175800 397619 := bstep (se 1 (by rfl) ⟨298214, by rfl⟩ : syracuseStep 397619 = 596429) B596429
theorem B1020235 : Blo 175800 1020235 := bstep (se 1 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 1020235 = 1530353) B1530353
theorem B397655 : Blo 175800 397655 := bstep (se 1 (by rfl) ⟨298241, by rfl⟩ : syracuseStep 397655 = 596483) B596483
theorem B758105 : Blo 175800 758105 := bstep (se 2 (by rfl) ⟨284289, by rfl⟩ : syracuseStep 758105 = 568579) B568579
theorem B266585 : Blo 175800 266585 := bstep (se 2 (by rfl) ⟨99969, by rfl⟩ : syracuseStep 266585 = 199939) B199939
theorem B594269 : Blo 175800 594269 := bstep (se 3 (by rfl) ⟨111425, by rfl⟩ : syracuseStep 594269 = 222851) B222851
theorem B266699 : Blo 175800 266699 := bstep (se 1 (by rfl) ⟨200024, by rfl⟩ : syracuseStep 266699 = 400049) B400049
theorem B201163 : Blo 175800 201163 := bstep (se 1 (by rfl) ⟨150872, by rfl⟩ : syracuseStep 201163 = 301745) B301745
theorem B266711 : Blo 175800 266711 := bstep (se 1 (by rfl) ⟨200033, by rfl⟩ : syracuseStep 266711 = 400067) B400067
theorem B397835 : Blo 175800 397835 := bstep (se 1 (by rfl) ⟨298376, by rfl⟩ : syracuseStep 397835 = 596753) B596753
theorem B299531 : Blo 175800 299531 := bstep (se 1 (by rfl) ⟨224648, by rfl⟩ : syracuseStep 299531 = 449297) B449297
theorem B266777 : Blo 175800 266777 := bstep (se 2 (by rfl) ⟨100041, by rfl⟩ : syracuseStep 266777 = 200083) B200083
theorem B430643 : Blo 175800 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B201271 : Blo 175800 201271 := bstep (se 1 (by rfl) ⟨150953, by rfl⟩ : syracuseStep 201271 = 301907) B301907
theorem B397889 : Blo 175800 397889 := bstep (se 2 (by rfl) ⟨149208, by rfl⟩ : syracuseStep 397889 = 298417) B298417
theorem B1151581 : Blo 175800 1151581 := bstep (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) B431843
theorem B1020509 : Blo 175800 1020509 := bstep (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) B382691
theorem B299659 : Blo 175800 299659 := bstep (se 1 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 299659 = 449489) B449489
theorem B266891 : Blo 175800 266891 := bstep (se 1 (by rfl) ⟨200168, by rfl⟩ : syracuseStep 266891 = 400337) B400337
theorem B266903 : Blo 175800 266903 := bstep (se 1 (by rfl) ⟨200177, by rfl⟩ : syracuseStep 266903 = 400355) B400355
theorem B266969 : Blo 175800 266969 := bstep (se 2 (by rfl) ⟨100113, by rfl⟩ : syracuseStep 266969 = 200227) B200227
theorem B201451 : Blo 175800 201451 := bstep (se 1 (by rfl) ⟨151088, by rfl⟩ : syracuseStep 201451 = 302177) B302177
theorem B398105 : Blo 175800 398105 := bstep (se 2 (by rfl) ⟨149289, by rfl⟩ : syracuseStep 398105 = 298579) B298579
theorem B299801 : Blo 175800 299801 := bstep (se 2 (by rfl) ⟨112425, by rfl⟩ : syracuseStep 299801 = 224851) B224851
theorem B267083 : Blo 175800 267083 := bstep (se 1 (by rfl) ⟨200312, by rfl⟩ : syracuseStep 267083 = 400625) B400625
theorem B267095 : Blo 175800 267095 := bstep (se 1 (by rfl) ⟨200321, by rfl⟩ : syracuseStep 267095 = 400643) B400643
theorem B201559 : Blo 175800 201559 := bstep (se 1 (by rfl) ⟨151169, by rfl⟩ : syracuseStep 201559 = 302339) B302339
theorem B398195 : Blo 175800 398195 := bstep (se 1 (by rfl) ⟨298646, by rfl⟩ : syracuseStep 398195 = 597293) B597293
theorem B398231 : Blo 175800 398231 := bstep (se 1 (by rfl) ⟨298673, by rfl⟩ : syracuseStep 398231 = 597347) B597347
theorem B299929 : Blo 175800 299929 := bstep (se 2 (by rfl) ⟨112473, by rfl⟩ : syracuseStep 299929 = 224947) B224947
theorem B267161 : Blo 175800 267161 := bstep (se 2 (by rfl) ⟨100185, by rfl⟩ : syracuseStep 267161 = 200371) B200371
theorem B267275 : Blo 175800 267275 := bstep (se 1 (by rfl) ⟨200456, by rfl⟩ : syracuseStep 267275 = 400913) B400913
theorem B201739 : Blo 175800 201739 := bstep (se 1 (by rfl) ⟨151304, by rfl⟩ : syracuseStep 201739 = 302609) B302609
theorem B267287 : Blo 175800 267287 := bstep (se 1 (by rfl) ⟨200465, by rfl⟩ : syracuseStep 267287 = 400931) B400931
theorem B398411 : Blo 175800 398411 := bstep (se 1 (by rfl) ⟨298808, by rfl⟩ : syracuseStep 398411 = 597617) B597617
theorem B267353 : Blo 175800 267353 := bstep (se 2 (by rfl) ⟨100257, by rfl⟩ : syracuseStep 267353 = 200515) B200515
theorem B201847 : Blo 175800 201847 := bstep (se 1 (by rfl) ⟨151385, by rfl⟩ : syracuseStep 201847 = 302771) B302771
theorem B398465 : Blo 175800 398465 := bstep (se 2 (by rfl) ⟨149424, by rfl⟩ : syracuseStep 398465 = 298849) B298849
theorem B4854935 : Blo 175800 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B267467 : Blo 175800 267467 := bstep (se 1 (by rfl) ⟨200600, by rfl⟩ : syracuseStep 267467 = 401201) B401201
theorem B201943 : Blo 175800 201943 := bstep (se 1 (by rfl) ⟨151457, by rfl⟩ : syracuseStep 201943 = 302915) B302915
theorem B267479 : Blo 175800 267479 := bstep (se 1 (by rfl) ⟨200609, by rfl⟩ : syracuseStep 267479 = 401219) B401219
theorem B267545 : Blo 175800 267545 := bstep (se 2 (by rfl) ⟨100329, by rfl⟩ : syracuseStep 267545 = 200659) B200659
theorem B202027 : Blo 175800 202027 := bstep (se 1 (by rfl) ⟨151520, by rfl⟩ : syracuseStep 202027 = 303041) B303041
theorem B398681 : Blo 175800 398681 := bstep (se 2 (by rfl) ⟨149505, by rfl⟩ : syracuseStep 398681 = 299011) B299011
theorem B267659 : Blo 175800 267659 := bstep (se 1 (by rfl) ⟨200744, by rfl⟩ : syracuseStep 267659 = 401489) B401489
theorem B267671 : Blo 175800 267671 := bstep (se 1 (by rfl) ⟨200753, by rfl⟩ : syracuseStep 267671 = 401507) B401507
theorem B202135 : Blo 175800 202135 := bstep (se 1 (by rfl) ⟨151601, by rfl⟩ : syracuseStep 202135 = 303203) B303203
theorem B398771 : Blo 175800 398771 := bstep (se 1 (by rfl) ⟨299078, by rfl⟩ : syracuseStep 398771 = 598157) B598157
theorem B595403 : Blo 175800 595403 := bstep (se 1 (by rfl) ⟨446552, by rfl⟩ : syracuseStep 595403 = 893105) B893105
theorem B398807 : Blo 175800 398807 := bstep (se 1 (by rfl) ⟨299105, by rfl⟩ : syracuseStep 398807 = 598211) B598211
theorem B300503 : Blo 175800 300503 := bstep (se 1 (by rfl) ⟨225377, by rfl⟩ : syracuseStep 300503 = 450755) B450755
theorem B267737 : Blo 175800 267737 := bstep (se 2 (by rfl) ⟨100401, by rfl⟩ : syracuseStep 267737 = 200803) B200803
theorem B2299427 : Blo 175800 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B267851 : Blo 175800 267851 := bstep (se 1 (by rfl) ⟨200888, by rfl⟩ : syracuseStep 267851 = 401777) B401777
theorem B300631 : Blo 175800 300631 := bstep (se 1 (by rfl) ⟨225473, by rfl⟩ : syracuseStep 300631 = 450947) B450947
theorem B267863 : Blo 175800 267863 := bstep (se 1 (by rfl) ⟨200897, by rfl⟩ : syracuseStep 267863 = 401795) B401795
theorem B398987 : Blo 175800 398987 := bstep (se 1 (by rfl) ⟨299240, by rfl⟩ : syracuseStep 398987 = 598481) B598481
theorem B267929 : Blo 175800 267929 := bstep (se 2 (by rfl) ⟨100473, by rfl⟩ : syracuseStep 267929 = 200947) B200947
theorem B399041 : Blo 175800 399041 := bstep (se 2 (by rfl) ⟨149640, by rfl⟩ : syracuseStep 399041 = 299281) B299281
theorem B595673 : Blo 175800 595673 := bstep (se 2 (by rfl) ⟨223377, by rfl⟩ : syracuseStep 595673 = 446755) B446755
theorem B268043 : Blo 175800 268043 := bstep (se 1 (by rfl) ⟨201032, by rfl⟩ : syracuseStep 268043 = 402065) B402065
theorem B268055 : Blo 175800 268055 := bstep (se 1 (by rfl) ⟨201041, by rfl⟩ : syracuseStep 268055 = 402083) B402083
theorem B268121 : Blo 175800 268121 := bstep (se 2 (by rfl) ⟨100545, by rfl⟩ : syracuseStep 268121 = 201091) B201091
theorem B399257 : Blo 175800 399257 := bstep (se 2 (by rfl) ⟨149721, by rfl⟩ : syracuseStep 399257 = 299443) B299443
theorem B268235 : Blo 175800 268235 := bstep (se 1 (by rfl) ⟨201176, by rfl⟩ : syracuseStep 268235 = 402353) B402353
theorem B268247 : Blo 175800 268247 := bstep (se 1 (by rfl) ⟨201185, by rfl⟩ : syracuseStep 268247 = 402371) B402371
theorem B399347 : Blo 175800 399347 := bstep (se 1 (by rfl) ⟨299510, by rfl⟩ : syracuseStep 399347 = 599021) B599021
theorem B399383 : Blo 175800 399383 := bstep (se 1 (by rfl) ⟨299537, by rfl⟩ : syracuseStep 399383 = 599075) B599075
theorem B268313 : Blo 175800 268313 := bstep (se 2 (by rfl) ⟨100617, by rfl⟩ : syracuseStep 268313 = 201235) B201235
theorem B333875 : Blo 175800 333875 := bstep (se 1 (by rfl) ⟨250406, by rfl⟩ : syracuseStep 333875 = 500813) B500813
theorem B5150789 : Blo 175800 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B268427 : Blo 175800 268427 := bstep (se 1 (by rfl) ⟨201320, by rfl⟩ : syracuseStep 268427 = 402641) B402641
theorem B268439 : Blo 175800 268439 := bstep (se 1 (by rfl) ⟨201329, by rfl⟩ : syracuseStep 268439 = 402659) B402659
theorem B399563 : Blo 175800 399563 := bstep (se 1 (by rfl) ⟨299672, by rfl⟩ : syracuseStep 399563 = 599345) B599345
theorem B301259 : Blo 175800 301259 := bstep (se 1 (by rfl) ⟨225944, by rfl⟩ : syracuseStep 301259 = 451889) B451889
theorem B268505 : Blo 175800 268505 := bstep (se 2 (by rfl) ⟨100689, by rfl⟩ : syracuseStep 268505 = 201379) B201379
theorem B399617 : Blo 175800 399617 := bstep (se 2 (by rfl) ⟨149856, by rfl⟩ : syracuseStep 399617 = 299713) B299713
theorem B301387 : Blo 175800 301387 := bstep (se 1 (by rfl) ⟨226040, by rfl⟩ : syracuseStep 301387 = 452081) B452081
theorem B268619 : Blo 175800 268619 := bstep (se 1 (by rfl) ⟨201464, by rfl⟩ : syracuseStep 268619 = 402929) B402929
theorem B268631 : Blo 175800 268631 := bstep (se 1 (by rfl) ⟨201473, by rfl⟩ : syracuseStep 268631 = 402947) B402947
theorem B596375 : Blo 175800 596375 := bstep (se 1 (by rfl) ⟨447281, by rfl⟩ : syracuseStep 596375 = 894563) B894563
theorem B268697 : Blo 175800 268697 := bstep (se 2 (by rfl) ⟨100761, by rfl⟩ : syracuseStep 268697 = 201523) B201523
theorem B399833 : Blo 175800 399833 := bstep (se 2 (by rfl) ⟨149937, by rfl⟩ : syracuseStep 399833 = 299875) B299875
theorem B301529 : Blo 175800 301529 := bstep (se 2 (by rfl) ⟨113073, by rfl⟩ : syracuseStep 301529 = 226147) B226147
theorem B268811 : Blo 175800 268811 := bstep (se 1 (by rfl) ⟨201608, by rfl⟩ : syracuseStep 268811 = 403217) B403217
theorem B268823 : Blo 175800 268823 := bstep (se 1 (by rfl) ⟨201617, by rfl⟩ : syracuseStep 268823 = 403235) B403235
theorem B334361 : Blo 175800 334361 := bstep (se 2 (by rfl) ⟨125385, by rfl⟩ : syracuseStep 334361 = 250771) B250771
theorem B596531 : Blo 175800 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B399923 : Blo 175800 399923 := bstep (se 1 (by rfl) ⟨299942, by rfl⟩ : syracuseStep 399923 = 599885) B599885
theorem B399959 : Blo 175800 399959 := bstep (se 1 (by rfl) ⟨299969, by rfl⟩ : syracuseStep 399959 = 599939) B599939
theorem B301657 : Blo 175800 301657 := bstep (se 2 (by rfl) ⟨113121, by rfl⟩ : syracuseStep 301657 = 226243) B226243
theorem B268889 : Blo 175800 268889 := bstep (se 2 (by rfl) ⟨100833, by rfl⟩ : syracuseStep 268889 = 201667) B201667
theorem B891485 : Blo 175800 891485 := bstep (se 3 (by rfl) ⟨167153, by rfl⟩ : syracuseStep 891485 = 334307) B334307
theorem B269003 : Blo 175800 269003 := bstep (se 1 (by rfl) ⟨201752, by rfl⟩ : syracuseStep 269003 = 403505) B403505
theorem B269015 : Blo 175800 269015 := bstep (se 1 (by rfl) ⟨201761, by rfl⟩ : syracuseStep 269015 = 403523) B403523
theorem B400139 : Blo 175800 400139 := bstep (se 1 (by rfl) ⟨300104, by rfl⟩ : syracuseStep 400139 = 600209) B600209
theorem B269081 : Blo 175800 269081 := bstep (se 2 (by rfl) ⟨100905, by rfl⟩ : syracuseStep 269081 = 201811) B201811
theorem B400193 : Blo 175800 400193 := bstep (se 2 (by rfl) ⟨150072, by rfl⟩ : syracuseStep 400193 = 300145) B300145
theorem B1612619 : Blo 175800 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B269195 : Blo 175800 269195 := bstep (se 1 (by rfl) ⟨201896, by rfl⟩ : syracuseStep 269195 = 403793) B403793
theorem B269207 : Blo 175800 269207 := bstep (se 1 (by rfl) ⟨201905, by rfl⟩ : syracuseStep 269207 = 403811) B403811
theorem B596915 : Blo 175800 596915 := bstep (se 1 (by rfl) ⟨447686, by rfl⟩ : syracuseStep 596915 = 895373) B895373
theorem B269273 : Blo 175800 269273 := bstep (se 2 (by rfl) ⟨100977, by rfl⟩ : syracuseStep 269273 = 201955) B201955
theorem B400409 : Blo 175800 400409 := bstep (se 2 (by rfl) ⟨150153, by rfl⟩ : syracuseStep 400409 = 300307) B300307
theorem B859211 : Blo 175800 859211 := bstep (se 1 (by rfl) ⟨644408, by rfl⟩ : syracuseStep 859211 = 1288817) B1288817
theorem B269387 : Blo 175800 269387 := bstep (se 1 (by rfl) ⟨202040, by rfl⟩ : syracuseStep 269387 = 404081) B404081
theorem B269399 : Blo 175800 269399 := bstep (se 1 (by rfl) ⟨202049, by rfl⟩ : syracuseStep 269399 = 404099) B404099
theorem B400499 : Blo 175800 400499 := bstep (se 1 (by rfl) ⟨300374, by rfl⟩ : syracuseStep 400499 = 600749) B600749
theorem B302231 : Blo 175800 302231 := bstep (se 1 (by rfl) ⟨226673, by rfl⟩ : syracuseStep 302231 = 453347) B453347
theorem B400535 : Blo 175800 400535 := bstep (se 1 (by rfl) ⟨300401, by rfl⟩ : syracuseStep 400535 = 600803) B600803
theorem B269465 : Blo 175800 269465 := bstep (se 2 (by rfl) ⟨101049, by rfl⟩ : syracuseStep 269465 = 202099) B202099
theorem B597185 : Blo 175800 597185 := bstep (se 2 (by rfl) ⟨223944, by rfl⟩ : syracuseStep 597185 = 447889) B447889
theorem B269579 : Blo 175800 269579 := bstep (se 1 (by rfl) ⟨202184, by rfl⟩ : syracuseStep 269579 = 404369) B404369
theorem B302359 : Blo 175800 302359 := bstep (se 1 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 302359 = 453539) B453539
theorem B269591 : Blo 175800 269591 := bstep (se 1 (by rfl) ⟨202193, by rfl⟩ : syracuseStep 269591 = 404387) B404387
theorem B400715 : Blo 175800 400715 := bstep (se 1 (by rfl) ⟨300536, by rfl⟩ : syracuseStep 400715 = 601073) B601073
theorem B269657 : Blo 175800 269657 := bstep (se 2 (by rfl) ⟨101121, by rfl⟩ : syracuseStep 269657 = 202243) B202243
theorem B400769 : Blo 175800 400769 := bstep (se 2 (by rfl) ⟨150288, by rfl⟩ : syracuseStep 400769 = 300577) B300577
theorem B400985 : Blo 175800 400985 := bstep (se 2 (by rfl) ⟨150369, by rfl⟩ : syracuseStep 400985 = 300739) B300739
theorem B401075 : Blo 175800 401075 := bstep (se 1 (by rfl) ⟨300806, by rfl⟩ : syracuseStep 401075 = 601613) B601613
theorem B401111 : Blo 175800 401111 := bstep (se 1 (by rfl) ⟨300833, by rfl⟩ : syracuseStep 401111 = 601667) B601667
theorem B597725 : Blo 175800 597725 := bstep (se 3 (by rfl) ⟨112073, by rfl⟩ : syracuseStep 597725 = 224147) B224147
theorem B401291 : Blo 175800 401291 := bstep (se 1 (by rfl) ⟨300968, by rfl⟩ : syracuseStep 401291 = 601937) B601937
theorem B302987 : Blo 175800 302987 := bstep (se 1 (by rfl) ⟨227240, by rfl⟩ : syracuseStep 302987 = 454481) B454481
theorem B401345 : Blo 175800 401345 := bstep (se 2 (by rfl) ⟨150504, by rfl⟩ : syracuseStep 401345 = 301009) B301009
theorem B335819 : Blo 175800 335819 := bstep (se 1 (by rfl) ⟨251864, by rfl⟩ : syracuseStep 335819 = 503729) B503729
theorem B303115 : Blo 175800 303115 := bstep (se 1 (by rfl) ⟨227336, by rfl⟩ : syracuseStep 303115 = 454673) B454673
theorem B3317777 : Blo 175800 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B270425 : Blo 175800 270425 := bstep (se 2 (by rfl) ⟨101409, by rfl⟩ : syracuseStep 270425 = 202819) B202819
theorem B336001 : Blo 175800 336001 := bstep (se 2 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 336001 = 252001) B252001
theorem B401561 : Blo 175800 401561 := bstep (se 2 (by rfl) ⟨150585, by rfl⟩ : syracuseStep 401561 = 301171) B301171
theorem B303257 : Blo 175800 303257 := bstep (se 2 (by rfl) ⟨113721, by rfl⟩ : syracuseStep 303257 = 227443) B227443
theorem B401651 : Blo 175800 401651 := bstep (se 1 (by rfl) ⟨301238, by rfl⟩ : syracuseStep 401651 = 602477) B602477
theorem B401687 : Blo 175800 401687 := bstep (se 1 (by rfl) ⟨301265, by rfl⟩ : syracuseStep 401687 = 602531) B602531
theorem B303385 : Blo 175800 303385 := bstep (se 2 (by rfl) ⟨113769, by rfl⟩ : syracuseStep 303385 = 227539) B227539
theorem B565579 : Blo 175800 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B401867 : Blo 175800 401867 := bstep (se 1 (by rfl) ⟨301400, by rfl⟩ : syracuseStep 401867 = 602801) B602801
theorem B401921 : Blo 175800 401921 := bstep (se 2 (by rfl) ⟨150720, by rfl⟩ : syracuseStep 401921 = 301441) B301441
theorem B565811 : Blo 175800 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B336449 : Blo 175800 336449 := bstep (se 2 (by rfl) ⟨126168, by rfl⟩ : syracuseStep 336449 = 252337) B252337
theorem B762443 : Blo 175800 762443 := bstep (se 1 (by rfl) ⟨571832, by rfl⟩ : syracuseStep 762443 = 1143665) B1143665
theorem B893591 : Blo 175800 893591 := bstep (se 1 (by rfl) ⟨670193, by rfl⟩ : syracuseStep 893591 = 1340387) B1340387
theorem B402137 : Blo 175800 402137 := bstep (se 2 (by rfl) ⟨150801, by rfl⟩ : syracuseStep 402137 = 301603) B301603
theorem B402227 : Blo 175800 402227 := bstep (se 1 (by rfl) ⟨301670, by rfl⟩ : syracuseStep 402227 = 603341) B603341
theorem B598859 : Blo 175800 598859 := bstep (se 1 (by rfl) ⟨449144, by rfl⟩ : syracuseStep 598859 = 898289) B898289
theorem B402263 : Blo 175800 402263 := bstep (se 1 (by rfl) ⟨301697, by rfl⟩ : syracuseStep 402263 = 603395) B603395
theorem B336791 : Blo 175800 336791 := bstep (se 1 (by rfl) ⟨252593, by rfl⟩ : syracuseStep 336791 = 505187) B505187
theorem B402443 : Blo 175800 402443 := bstep (se 1 (by rfl) ⟨301832, by rfl⟩ : syracuseStep 402443 = 603665) B603665
theorem B402497 : Blo 175800 402497 := bstep (se 2 (by rfl) ⟨150936, by rfl⟩ : syracuseStep 402497 = 301873) B301873
theorem B599129 : Blo 175800 599129 := bstep (se 2 (by rfl) ⟨224673, by rfl⟩ : syracuseStep 599129 = 449347) B449347
theorem B402713 : Blo 175800 402713 := bstep (se 2 (by rfl) ⟨151017, by rfl⟩ : syracuseStep 402713 = 302035) B302035
theorem B402803 : Blo 175800 402803 := bstep (se 1 (by rfl) ⟨302102, by rfl⟩ : syracuseStep 402803 = 604205) B604205
theorem B3417461 : Blo 175800 3417461 := bstep (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) B320387
theorem B402839 : Blo 175800 402839 := bstep (se 1 (by rfl) ⟨302129, by rfl⟩ : syracuseStep 402839 = 604259) B604259
theorem B337459 : Blo 175800 337459 := bstep (se 1 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 337459 = 506189) B506189
theorem B403019 : Blo 175800 403019 := bstep (se 1 (by rfl) ⟨302264, by rfl⟩ : syracuseStep 403019 = 604529) B604529
theorem B403073 : Blo 175800 403073 := bstep (se 2 (by rfl) ⟨151152, by rfl⟩ : syracuseStep 403073 = 302305) B302305
theorem B239383 : Blo 175800 239383 := bstep (se 1 (by rfl) ⟨179537, by rfl⟩ : syracuseStep 239383 = 359075) B359075
theorem B599831 : Blo 175800 599831 := bstep (se 1 (by rfl) ⟨449873, by rfl⟩ : syracuseStep 599831 = 899747) B899747
theorem B403289 : Blo 175800 403289 := bstep (se 2 (by rfl) ⟨151233, by rfl⟩ : syracuseStep 403289 = 302467) B302467
theorem B403379 : Blo 175800 403379 := bstep (se 1 (by rfl) ⟨302534, by rfl⟩ : syracuseStep 403379 = 605069) B605069
theorem B403415 : Blo 175800 403415 := bstep (se 1 (by rfl) ⟨302561, by rfl⟩ : syracuseStep 403415 = 605123) B605123
theorem B337907 : Blo 175800 337907 := bstep (se 1 (by rfl) ⟨253430, by rfl⟩ : syracuseStep 337907 = 506861) B506861
theorem B337945 : Blo 175800 337945 := bstep (se 2 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 337945 = 253459) B253459
theorem B2009123 : Blo 175800 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B403595 : Blo 175800 403595 := bstep (se 1 (by rfl) ⟨302696, by rfl⟩ : syracuseStep 403595 = 605393) B605393
theorem B764083 : Blo 175800 764083 := bstep (se 1 (by rfl) ⟨573062, by rfl⟩ : syracuseStep 764083 = 1146125) B1146125
theorem B403649 : Blo 175800 403649 := bstep (se 2 (by rfl) ⟨151368, by rfl⟩ : syracuseStep 403649 = 302737) B302737
theorem B272663 : Blo 175800 272663 := bstep (se 1 (by rfl) ⟨204497, by rfl⟩ : syracuseStep 272663 = 408995) B408995
theorem B600371 : Blo 175800 600371 := bstep (se 1 (by rfl) ⟨450278, by rfl⟩ : syracuseStep 600371 = 900557) B900557
theorem B862595 : Blo 175800 862595 := bstep (se 1 (by rfl) ⟨646946, by rfl⟩ : syracuseStep 862595 = 1293893) B1293893
theorem B403865 : Blo 175800 403865 := bstep (se 2 (by rfl) ⟨151449, by rfl⟩ : syracuseStep 403865 = 302899) B302899
theorem B338393 : Blo 175800 338393 := bstep (se 2 (by rfl) ⟨126897, by rfl⟩ : syracuseStep 338393 = 253795) B253795
theorem B436697 : Blo 175800 436697 := bstep (se 2 (by rfl) ⟨163761, by rfl⟩ : syracuseStep 436697 = 327523) B327523
theorem B272857 : Blo 175800 272857 := bstep (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) B204643
theorem B403955 : Blo 175800 403955 := bstep (se 1 (by rfl) ⟨302966, by rfl⟩ : syracuseStep 403955 = 605933) B605933
theorem B403991 : Blo 175800 403991 := bstep (se 1 (by rfl) ⟨302993, by rfl⟩ : syracuseStep 403991 = 605987) B605987
theorem B1878563 : Blo 175800 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B600641 : Blo 175800 600641 := bstep (se 2 (by rfl) ⟨225240, by rfl⟩ : syracuseStep 600641 = 450481) B450481
theorem B404171 : Blo 175800 404171 := bstep (se 1 (by rfl) ⟨303128, by rfl⟩ : syracuseStep 404171 = 606257) B606257
theorem B404225 : Blo 175800 404225 := bstep (se 2 (by rfl) ⟨151584, by rfl⟩ : syracuseStep 404225 = 303169) B303169
theorem B731927 : Blo 175800 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B306137 : Blo 175800 306137 := bstep (se 2 (by rfl) ⟨114801, by rfl⟩ : syracuseStep 306137 = 229603) B229603
theorem B404441 : Blo 175800 404441 := bstep (se 2 (by rfl) ⟨151665, by rfl⟩ : syracuseStep 404441 = 303331) B303331
theorem B404531 : Blo 175800 404531 := bstep (se 1 (by rfl) ⟨303398, by rfl⟩ : syracuseStep 404531 = 606797) B606797
theorem B601181 : Blo 175800 601181 := bstep (se 3 (by rfl) ⟨112721, by rfl⟩ : syracuseStep 601181 = 225443) B225443
theorem B2141315 : Blo 175800 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B339137 : Blo 175800 339137 := bstep (se 2 (by rfl) ⟨127176, by rfl⟩ : syracuseStep 339137 = 254353) B254353
theorem B339403 : Blo 175800 339403 := bstep (se 1 (by rfl) ⟨254552, by rfl⟩ : syracuseStep 339403 = 509105) B509105
theorem B503347 : Blo 175800 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B765571 : Blo 175800 765571 := bstep (se 1 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 765571 = 1148357) B1148357
theorem B634547 : Blo 175800 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B503489 : Blo 175800 503489 := bstep (se 2 (by rfl) ⟨188808, by rfl⟩ : syracuseStep 503489 = 377617) B377617
theorem B175819 : Blo 175800 175819 := bstep (se 1 (by rfl) ⟨131864, by rfl⟩ : syracuseStep 175819 = 263729) B263729
theorem B175831 : Blo 175800 175831 := bstep (se 1 (by rfl) ⟨131873, by rfl⟩ : syracuseStep 175831 = 263747) B263747
theorem B175851 : Blo 175800 175851 := bstep (se 1 (by rfl) ⟨131888, by rfl⟩ : syracuseStep 175851 = 263777) B263777
theorem B175863 : Blo 175800 175863 := bstep (se 1 (by rfl) ⟨131897, by rfl⟩ : syracuseStep 175863 = 263795) B263795
theorem B175883 : Blo 175800 175883 := bstep (se 1 (by rfl) ⟨131912, by rfl⟩ : syracuseStep 175883 = 263825) B263825
theorem B175895 : Blo 175800 175895 := bstep (se 1 (by rfl) ⟨131921, by rfl⟩ : syracuseStep 175895 = 263843) B263843
theorem B175915 : Blo 175800 175915 := bstep (se 1 (by rfl) ⟨131936, by rfl⟩ : syracuseStep 175915 = 263873) B263873
theorem B503603 : Blo 175800 503603 := bstep (se 1 (by rfl) ⟨377702, by rfl⟩ : syracuseStep 503603 = 755405) B755405
theorem B175927 : Blo 175800 175927 := bstep (se 1 (by rfl) ⟨131945, by rfl⟩ : syracuseStep 175927 = 263891) B263891
theorem B175947 : Blo 175800 175947 := bstep (se 1 (by rfl) ⟨131960, by rfl⟩ : syracuseStep 175947 = 263921) B263921
theorem B175959 : Blo 175800 175959 := bstep (se 1 (by rfl) ⟨131969, by rfl⟩ : syracuseStep 175959 = 263939) B263939
theorem B175979 : Blo 175800 175979 := bstep (se 1 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 175979 = 263969) B263969
theorem B175991 : Blo 175800 175991 := bstep (se 1 (by rfl) ⟨131993, by rfl⟩ : syracuseStep 175991 = 263987) B263987
theorem B176011 : Blo 175800 176011 := bstep (se 1 (by rfl) ⟨132008, by rfl⟩ : syracuseStep 176011 = 264017) B264017
theorem B339851 : Blo 175800 339851 := bstep (se 1 (by rfl) ⟨254888, by rfl⟩ : syracuseStep 339851 = 509777) B509777
theorem B176023 : Blo 175800 176023 := bstep (se 1 (by rfl) ⟨132017, by rfl⟩ : syracuseStep 176023 = 264035) B264035
theorem B176043 : Blo 175800 176043 := bstep (se 1 (by rfl) ⟨132032, by rfl⟩ : syracuseStep 176043 = 264065) B264065
theorem B176055 : Blo 175800 176055 := bstep (se 1 (by rfl) ⟨132041, by rfl⟩ : syracuseStep 176055 = 264083) B264083
theorem B176075 : Blo 175800 176075 := bstep (se 1 (by rfl) ⟨132056, by rfl⟩ : syracuseStep 176075 = 264113) B264113
theorem B176087 : Blo 175800 176087 := bstep (se 1 (by rfl) ⟨132065, by rfl⟩ : syracuseStep 176087 = 264131) B264131
theorem B1814489 : Blo 175800 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B176107 : Blo 175800 176107 := bstep (se 1 (by rfl) ⟨132080, by rfl⟩ : syracuseStep 176107 = 264161) B264161
theorem B176119 : Blo 175800 176119 := bstep (se 1 (by rfl) ⟨132089, by rfl⟩ : syracuseStep 176119 = 264179) B264179
theorem B176139 : Blo 175800 176139 := bstep (se 1 (by rfl) ⟨132104, by rfl⟩ : syracuseStep 176139 = 264209) B264209
theorem B176151 : Blo 175800 176151 := bstep (se 1 (by rfl) ⟨132113, by rfl⟩ : syracuseStep 176151 = 264227) B264227
theorem B176171 : Blo 175800 176171 := bstep (se 1 (by rfl) ⟨132128, by rfl⟩ : syracuseStep 176171 = 264257) B264257
theorem B176183 : Blo 175800 176183 := bstep (se 1 (by rfl) ⟨132137, by rfl⟩ : syracuseStep 176183 = 264275) B264275
theorem B340033 : Blo 175800 340033 := bstep (se 2 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 340033 = 255025) B255025
theorem B176203 : Blo 175800 176203 := bstep (se 1 (by rfl) ⟨132152, by rfl⟩ : syracuseStep 176203 = 264305) B264305
theorem B176215 : Blo 175800 176215 := bstep (se 1 (by rfl) ⟨132161, by rfl⟩ : syracuseStep 176215 = 264323) B264323
theorem B176235 : Blo 175800 176235 := bstep (se 1 (by rfl) ⟨132176, by rfl⟩ : syracuseStep 176235 = 264353) B264353
theorem B176247 : Blo 175800 176247 := bstep (se 1 (by rfl) ⟨132185, by rfl⟩ : syracuseStep 176247 = 264371) B264371
theorem B897155 : Blo 175800 897155 := bstep (se 1 (by rfl) ⟨672866, by rfl⟩ : syracuseStep 897155 = 1345733) B1345733
theorem B176267 : Blo 175800 176267 := bstep (se 1 (by rfl) ⟨132200, by rfl⟩ : syracuseStep 176267 = 264401) B264401
theorem B176279 : Blo 175800 176279 := bstep (se 1 (by rfl) ⟨132209, by rfl⟩ : syracuseStep 176279 = 264419) B264419
theorem B176299 : Blo 175800 176299 := bstep (se 1 (by rfl) ⟨132224, by rfl⟩ : syracuseStep 176299 = 264449) B264449
theorem B176311 : Blo 175800 176311 := bstep (se 1 (by rfl) ⟨132233, by rfl⟩ : syracuseStep 176311 = 264467) B264467
theorem B176331 : Blo 175800 176331 := bstep (se 1 (by rfl) ⟨132248, by rfl⟩ : syracuseStep 176331 = 264497) B264497
theorem B602315 : Blo 175800 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B176343 : Blo 175800 176343 := bstep (se 1 (by rfl) ⟨132257, by rfl⟩ : syracuseStep 176343 = 264515) B264515
theorem B766169 : Blo 175800 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B176363 : Blo 175800 176363 := bstep (se 1 (by rfl) ⟨132272, by rfl⟩ : syracuseStep 176363 = 264545) B264545
theorem B176375 : Blo 175800 176375 := bstep (se 1 (by rfl) ⟨132281, by rfl⟩ : syracuseStep 176375 = 264563) B264563
theorem B176395 : Blo 175800 176395 := bstep (se 1 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 176395 = 264593) B264593
theorem B176407 : Blo 175800 176407 := bstep (se 1 (by rfl) ⟨132305, by rfl⟩ : syracuseStep 176407 = 264611) B264611
theorem B176427 : Blo 175800 176427 := bstep (se 1 (by rfl) ⟨132320, by rfl⟩ : syracuseStep 176427 = 264641) B264641
theorem B176439 : Blo 175800 176439 := bstep (se 1 (by rfl) ⟨132329, by rfl⟩ : syracuseStep 176439 = 264659) B264659
theorem B176459 : Blo 175800 176459 := bstep (se 1 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 176459 = 264689) B264689
theorem B405847 : Blo 175800 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B176471 : Blo 175800 176471 := bstep (se 1 (by rfl) ⟨132353, by rfl⟩ : syracuseStep 176471 = 264707) B264707
theorem B176491 : Blo 175800 176491 := bstep (se 1 (by rfl) ⟨132368, by rfl⟩ : syracuseStep 176491 = 264737) B264737
theorem B176503 : Blo 175800 176503 := bstep (se 1 (by rfl) ⟨132377, by rfl⟩ : syracuseStep 176503 = 264755) B264755
theorem B176523 : Blo 175800 176523 := bstep (se 1 (by rfl) ⟨132392, by rfl⟩ : syracuseStep 176523 = 264785) B264785
theorem B176535 : Blo 175800 176535 := bstep (se 1 (by rfl) ⟨132401, by rfl⟩ : syracuseStep 176535 = 264803) B264803
theorem B340375 : Blo 175800 340375 := bstep (se 1 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 340375 = 510563) B510563
theorem B176555 : Blo 175800 176555 := bstep (se 1 (by rfl) ⟨132416, by rfl⟩ : syracuseStep 176555 = 264833) B264833
theorem B176567 : Blo 175800 176567 := bstep (se 1 (by rfl) ⟨132425, by rfl⟩ : syracuseStep 176567 = 264851) B264851
theorem B176587 : Blo 175800 176587 := bstep (se 1 (by rfl) ⟨132440, by rfl⟩ : syracuseStep 176587 = 264881) B264881
theorem B176599 : Blo 175800 176599 := bstep (se 1 (by rfl) ⟨132449, by rfl⟩ : syracuseStep 176599 = 264899) B264899
theorem B602585 : Blo 175800 602585 := bstep (se 2 (by rfl) ⟨225969, by rfl⟩ : syracuseStep 602585 = 451939) B451939
theorem B176619 : Blo 175800 176619 := bstep (se 1 (by rfl) ⟨132464, by rfl⟩ : syracuseStep 176619 = 264929) B264929
theorem B176631 : Blo 175800 176631 := bstep (se 1 (by rfl) ⟨132473, by rfl⟩ : syracuseStep 176631 = 264947) B264947
theorem B176651 : Blo 175800 176651 := bstep (se 1 (by rfl) ⟨132488, by rfl⟩ : syracuseStep 176651 = 264977) B264977
theorem B176663 : Blo 175800 176663 := bstep (se 1 (by rfl) ⟨132497, by rfl⟩ : syracuseStep 176663 = 264995) B264995
theorem B176683 : Blo 175800 176683 := bstep (se 1 (by rfl) ⟨132512, by rfl⟩ : syracuseStep 176683 = 265025) B265025
theorem B176695 : Blo 175800 176695 := bstep (se 1 (by rfl) ⟨132521, by rfl⟩ : syracuseStep 176695 = 265043) B265043
theorem B766529 : Blo 175800 766529 := bstep (se 2 (by rfl) ⟨287448, by rfl⟩ : syracuseStep 766529 = 574897) B574897
theorem B176715 : Blo 175800 176715 := bstep (se 1 (by rfl) ⟨132536, by rfl⟩ : syracuseStep 176715 = 265073) B265073
theorem B176727 : Blo 175800 176727 := bstep (se 1 (by rfl) ⟨132545, by rfl⟩ : syracuseStep 176727 = 265091) B265091
theorem B176747 : Blo 175800 176747 := bstep (se 1 (by rfl) ⟨132560, by rfl⟩ : syracuseStep 176747 = 265121) B265121
theorem B340595 : Blo 175800 340595 := bstep (se 1 (by rfl) ⟨255446, by rfl⟩ : syracuseStep 340595 = 510893) B510893
theorem B176759 : Blo 175800 176759 := bstep (se 1 (by rfl) ⟨132569, by rfl⟩ : syracuseStep 176759 = 265139) B265139
theorem B176779 : Blo 175800 176779 := bstep (se 1 (by rfl) ⟨132584, by rfl⟩ : syracuseStep 176779 = 265169) B265169
theorem B176791 : Blo 175800 176791 := bstep (se 1 (by rfl) ⟨132593, by rfl⟩ : syracuseStep 176791 = 265187) B265187
theorem B176811 : Blo 175800 176811 := bstep (se 1 (by rfl) ⟨132608, by rfl⟩ : syracuseStep 176811 = 265217) B265217
theorem B176823 : Blo 175800 176823 := bstep (se 1 (by rfl) ⟨132617, by rfl⟩ : syracuseStep 176823 = 265235) B265235
theorem B176843 : Blo 175800 176843 := bstep (se 1 (by rfl) ⟨132632, by rfl⟩ : syracuseStep 176843 = 265265) B265265
theorem B176855 : Blo 175800 176855 := bstep (se 1 (by rfl) ⟨132641, by rfl⟩ : syracuseStep 176855 = 265283) B265283
theorem B176875 : Blo 175800 176875 := bstep (se 1 (by rfl) ⟨132656, by rfl⟩ : syracuseStep 176875 = 265313) B265313
theorem B176887 : Blo 175800 176887 := bstep (se 1 (by rfl) ⟨132665, by rfl⟩ : syracuseStep 176887 = 265331) B265331
theorem B176907 : Blo 175800 176907 := bstep (se 1 (by rfl) ⟨132680, by rfl⟩ : syracuseStep 176907 = 265361) B265361
theorem B176919 : Blo 175800 176919 := bstep (se 1 (by rfl) ⟨132689, by rfl⟩ : syracuseStep 176919 = 265379) B265379
theorem B176939 : Blo 175800 176939 := bstep (se 1 (by rfl) ⟨132704, by rfl⟩ : syracuseStep 176939 = 265409) B265409
theorem B1717037 : Blo 175800 1717037 := bstep (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) B643889
theorem B176951 : Blo 175800 176951 := bstep (se 1 (by rfl) ⟨132713, by rfl⟩ : syracuseStep 176951 = 265427) B265427
theorem B176971 : Blo 175800 176971 := bstep (se 1 (by rfl) ⟨132728, by rfl⟩ : syracuseStep 176971 = 265457) B265457
theorem B176983 : Blo 175800 176983 := bstep (se 1 (by rfl) ⟨132737, by rfl⟩ : syracuseStep 176983 = 265475) B265475
theorem B340823 : Blo 175800 340823 := bstep (se 1 (by rfl) ⟨255617, by rfl⟩ : syracuseStep 340823 = 511235) B511235
theorem B177003 : Blo 175800 177003 := bstep (se 1 (by rfl) ⟨132752, by rfl⟩ : syracuseStep 177003 = 265505) B265505
theorem B177015 : Blo 175800 177015 := bstep (se 1 (by rfl) ⟨132761, by rfl⟩ : syracuseStep 177015 = 265523) B265523
theorem B177035 : Blo 175800 177035 := bstep (se 1 (by rfl) ⟨132776, by rfl⟩ : syracuseStep 177035 = 265553) B265553
theorem B177047 : Blo 175800 177047 := bstep (se 1 (by rfl) ⟨132785, by rfl⟩ : syracuseStep 177047 = 265571) B265571
theorem B177067 : Blo 175800 177067 := bstep (se 1 (by rfl) ⟨132800, by rfl⟩ : syracuseStep 177067 = 265601) B265601
theorem B177079 : Blo 175800 177079 := bstep (se 1 (by rfl) ⟨132809, by rfl⟩ : syracuseStep 177079 = 265619) B265619
theorem B177099 : Blo 175800 177099 := bstep (se 1 (by rfl) ⟨132824, by rfl⟩ : syracuseStep 177099 = 265649) B265649
theorem B177111 : Blo 175800 177111 := bstep (se 1 (by rfl) ⟨132833, by rfl⟩ : syracuseStep 177111 = 265667) B265667
theorem B177131 : Blo 175800 177131 := bstep (se 1 (by rfl) ⟨132848, by rfl⟩ : syracuseStep 177131 = 265697) B265697
theorem B177143 : Blo 175800 177143 := bstep (se 1 (by rfl) ⟨132857, by rfl⟩ : syracuseStep 177143 = 265715) B265715
theorem B668675 : Blo 175800 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B177163 : Blo 175800 177163 := bstep (se 1 (by rfl) ⟨132872, by rfl⟩ : syracuseStep 177163 = 265745) B265745
theorem B177175 : Blo 175800 177175 := bstep (se 1 (by rfl) ⟨132881, by rfl⟩ : syracuseStep 177175 = 265763) B265763
theorem B242713 : Blo 175800 242713 := bstep (se 2 (by rfl) ⟨91017, by rfl⟩ : syracuseStep 242713 = 182035) B182035
theorem B177195 : Blo 175800 177195 := bstep (se 1 (by rfl) ⟨132896, by rfl⟩ : syracuseStep 177195 = 265793) B265793
theorem B177207 : Blo 175800 177207 := bstep (se 1 (by rfl) ⟨132905, by rfl⟩ : syracuseStep 177207 = 265811) B265811
theorem B177227 : Blo 175800 177227 := bstep (se 1 (by rfl) ⟨132920, by rfl⟩ : syracuseStep 177227 = 265841) B265841
theorem B177239 : Blo 175800 177239 := bstep (se 1 (by rfl) ⟨132929, by rfl⟩ : syracuseStep 177239 = 265859) B265859
theorem B341081 : Blo 175800 341081 := bstep (se 2 (by rfl) ⟨127905, by rfl⟩ : syracuseStep 341081 = 255811) B255811
theorem B177259 : Blo 175800 177259 := bstep (se 1 (by rfl) ⟨132944, by rfl⟩ : syracuseStep 177259 = 265889) B265889
theorem B177271 : Blo 175800 177271 := bstep (se 1 (by rfl) ⟨132953, by rfl⟩ : syracuseStep 177271 = 265907) B265907
theorem B177291 : Blo 175800 177291 := bstep (se 1 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 177291 = 265937) B265937
theorem B177303 : Blo 175800 177303 := bstep (se 1 (by rfl) ⟨132977, by rfl⟩ : syracuseStep 177303 = 265955) B265955
theorem B603287 : Blo 175800 603287 := bstep (se 1 (by rfl) ⟨452465, by rfl⟩ : syracuseStep 603287 = 904931) B904931
theorem B177323 : Blo 175800 177323 := bstep (se 1 (by rfl) ⟨132992, by rfl⟩ : syracuseStep 177323 = 265985) B265985
theorem B177335 : Blo 175800 177335 := bstep (se 1 (by rfl) ⟨133001, by rfl⟩ : syracuseStep 177335 = 266003) B266003
theorem B177355 : Blo 175800 177355 := bstep (se 1 (by rfl) ⟨133016, by rfl⟩ : syracuseStep 177355 = 266033) B266033
theorem B177367 : Blo 175800 177367 := bstep (se 1 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 177367 = 266051) B266051
theorem B177387 : Blo 175800 177387 := bstep (se 1 (by rfl) ⟨133040, by rfl⟩ : syracuseStep 177387 = 266081) B266081
theorem B177399 : Blo 175800 177399 := bstep (se 1 (by rfl) ⟨133049, by rfl⟩ : syracuseStep 177399 = 266099) B266099
theorem B177419 : Blo 175800 177419 := bstep (se 1 (by rfl) ⟨133064, by rfl⟩ : syracuseStep 177419 = 266129) B266129
theorem B177431 : Blo 175800 177431 := bstep (se 1 (by rfl) ⟨133073, by rfl⟩ : syracuseStep 177431 = 266147) B266147
theorem B341273 : Blo 175800 341273 := bstep (se 2 (by rfl) ⟨127977, by rfl⟩ : syracuseStep 341273 = 255955) B255955
theorem B177451 : Blo 175800 177451 := bstep (se 1 (by rfl) ⟨133088, by rfl⟩ : syracuseStep 177451 = 266177) B266177
theorem B177463 : Blo 175800 177463 := bstep (se 1 (by rfl) ⟨133097, by rfl⟩ : syracuseStep 177463 = 266195) B266195
theorem B177483 : Blo 175800 177483 := bstep (se 1 (by rfl) ⟨133112, by rfl⟩ : syracuseStep 177483 = 266225) B266225
theorem B177495 : Blo 175800 177495 := bstep (se 1 (by rfl) ⟨133121, by rfl⟩ : syracuseStep 177495 = 266243) B266243
theorem B177515 : Blo 175800 177515 := bstep (se 1 (by rfl) ⟨133136, by rfl⟩ : syracuseStep 177515 = 266273) B266273
theorem B177527 : Blo 175800 177527 := bstep (se 1 (by rfl) ⟨133145, by rfl⟩ : syracuseStep 177527 = 266291) B266291
theorem B177547 : Blo 175800 177547 := bstep (se 1 (by rfl) ⟨133160, by rfl⟩ : syracuseStep 177547 = 266321) B266321
theorem B177559 : Blo 175800 177559 := bstep (se 1 (by rfl) ⟨133169, by rfl⟩ : syracuseStep 177559 = 266339) B266339
theorem B177579 : Blo 175800 177579 := bstep (se 1 (by rfl) ⟨133184, by rfl⟩ : syracuseStep 177579 = 266369) B266369
theorem B177591 : Blo 175800 177591 := bstep (se 1 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 177591 = 266387) B266387
theorem B669131 : Blo 175800 669131 := bstep (se 1 (by rfl) ⟨501848, by rfl⟩ : syracuseStep 669131 = 1003697) B1003697
theorem B177611 : Blo 175800 177611 := bstep (se 1 (by rfl) ⟨133208, by rfl⟩ : syracuseStep 177611 = 266417) B266417
theorem B177623 : Blo 175800 177623 := bstep (se 1 (by rfl) ⟨133217, by rfl⟩ : syracuseStep 177623 = 266435) B266435
theorem B177643 : Blo 175800 177643 := bstep (se 1 (by rfl) ⟨133232, by rfl⟩ : syracuseStep 177643 = 266465) B266465
theorem B177655 : Blo 175800 177655 := bstep (se 1 (by rfl) ⟨133241, by rfl⟩ : syracuseStep 177655 = 266483) B266483
theorem B177675 : Blo 175800 177675 := bstep (se 1 (by rfl) ⟨133256, by rfl⟩ : syracuseStep 177675 = 266513) B266513
theorem B177687 : Blo 175800 177687 := bstep (se 1 (by rfl) ⟨133265, by rfl⟩ : syracuseStep 177687 = 266531) B266531
theorem B177707 : Blo 175800 177707 := bstep (se 1 (by rfl) ⟨133280, by rfl⟩ : syracuseStep 177707 = 266561) B266561
theorem B177719 : Blo 175800 177719 := bstep (se 1 (by rfl) ⟨133289, by rfl⟩ : syracuseStep 177719 = 266579) B266579
theorem B177739 : Blo 175800 177739 := bstep (se 1 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 177739 = 266609) B266609
theorem B177751 : Blo 175800 177751 := bstep (se 1 (by rfl) ⟨133313, by rfl⟩ : syracuseStep 177751 = 266627) B266627
theorem B177771 : Blo 175800 177771 := bstep (se 1 (by rfl) ⟨133328, by rfl⟩ : syracuseStep 177771 = 266657) B266657
theorem B177783 : Blo 175800 177783 := bstep (se 1 (by rfl) ⟨133337, by rfl⟩ : syracuseStep 177783 = 266675) B266675
theorem B9942659 : Blo 175800 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B177803 : Blo 175800 177803 := bstep (se 1 (by rfl) ⟨133352, by rfl⟩ : syracuseStep 177803 = 266705) B266705
theorem B669329 : Blo 175800 669329 := bstep (se 2 (by rfl) ⟨250998, by rfl⟩ : syracuseStep 669329 = 501997) B501997
theorem B177815 : Blo 175800 177815 := bstep (se 1 (by rfl) ⟨133361, by rfl⟩ : syracuseStep 177815 = 266723) B266723
theorem B177835 : Blo 175800 177835 := bstep (se 1 (by rfl) ⟨133376, by rfl⟩ : syracuseStep 177835 = 266753) B266753
theorem B603827 : Blo 175800 603827 := bstep (se 1 (by rfl) ⟨452870, by rfl⟩ : syracuseStep 603827 = 905741) B905741
theorem B177847 : Blo 175800 177847 := bstep (se 1 (by rfl) ⟨133385, by rfl⟩ : syracuseStep 177847 = 266771) B266771
theorem B177867 : Blo 175800 177867 := bstep (se 1 (by rfl) ⟨133400, by rfl⟩ : syracuseStep 177867 = 266801) B266801
theorem B177879 : Blo 175800 177879 := bstep (se 1 (by rfl) ⟨133409, by rfl⟩ : syracuseStep 177879 = 266819) B266819
theorem B177899 : Blo 175800 177899 := bstep (se 1 (by rfl) ⟨133424, by rfl⟩ : syracuseStep 177899 = 266849) B266849
theorem B177911 : Blo 175800 177911 := bstep (se 1 (by rfl) ⟨133433, by rfl⟩ : syracuseStep 177911 = 266867) B266867
theorem B177931 : Blo 175800 177931 := bstep (se 1 (by rfl) ⟨133448, by rfl⟩ : syracuseStep 177931 = 266897) B266897
theorem B177943 : Blo 175800 177943 := bstep (se 1 (by rfl) ⟨133457, by rfl⟩ : syracuseStep 177943 = 266915) B266915
theorem B177963 : Blo 175800 177963 := bstep (se 1 (by rfl) ⟨133472, by rfl⟩ : syracuseStep 177963 = 266945) B266945
theorem B177975 : Blo 175800 177975 := bstep (se 1 (by rfl) ⟨133481, by rfl⟩ : syracuseStep 177975 = 266963) B266963
theorem B177995 : Blo 175800 177995 := bstep (se 1 (by rfl) ⟨133496, by rfl⟩ : syracuseStep 177995 = 266993) B266993
theorem B178007 : Blo 175800 178007 := bstep (se 1 (by rfl) ⟨133505, by rfl⟩ : syracuseStep 178007 = 267011) B267011
theorem B178027 : Blo 175800 178027 := bstep (se 1 (by rfl) ⟨133520, by rfl⟩ : syracuseStep 178027 = 267041) B267041
theorem B178039 : Blo 175800 178039 := bstep (se 1 (by rfl) ⟨133529, by rfl⟩ : syracuseStep 178039 = 267059) B267059
theorem B178059 : Blo 175800 178059 := bstep (se 1 (by rfl) ⟨133544, by rfl⟩ : syracuseStep 178059 = 267089) B267089
theorem B178071 : Blo 175800 178071 := bstep (se 1 (by rfl) ⟨133553, by rfl⟩ : syracuseStep 178071 = 267107) B267107
theorem B178091 : Blo 175800 178091 := bstep (se 1 (by rfl) ⟨133568, by rfl⟩ : syracuseStep 178091 = 267137) B267137
theorem B178103 : Blo 175800 178103 := bstep (se 1 (by rfl) ⟨133577, by rfl⟩ : syracuseStep 178103 = 267155) B267155
theorem B604097 : Blo 175800 604097 := bstep (se 2 (by rfl) ⟨226536, by rfl⟩ : syracuseStep 604097 = 453073) B453073
theorem B178123 : Blo 175800 178123 := bstep (se 1 (by rfl) ⟨133592, by rfl⟩ : syracuseStep 178123 = 267185) B267185
theorem B178135 : Blo 175800 178135 := bstep (se 1 (by rfl) ⟨133601, by rfl⟩ : syracuseStep 178135 = 267203) B267203
theorem B178155 : Blo 175800 178155 := bstep (se 1 (by rfl) ⟨133616, by rfl⟩ : syracuseStep 178155 = 267233) B267233
theorem B178167 : Blo 175800 178167 := bstep (se 1 (by rfl) ⟨133625, by rfl⟩ : syracuseStep 178167 = 267251) B267251
theorem B178187 : Blo 175800 178187 := bstep (se 1 (by rfl) ⟨133640, by rfl⟩ : syracuseStep 178187 = 267281) B267281
theorem B178199 : Blo 175800 178199 := bstep (se 1 (by rfl) ⟨133649, by rfl⟩ : syracuseStep 178199 = 267299) B267299
theorem B178219 : Blo 175800 178219 := bstep (se 1 (by rfl) ⟨133664, by rfl⟩ : syracuseStep 178219 = 267329) B267329
theorem B14956597 : Blo 175800 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B178231 : Blo 175800 178231 := bstep (se 1 (by rfl) ⟨133673, by rfl⟩ : syracuseStep 178231 = 267347) B267347
theorem B178251 : Blo 175800 178251 := bstep (se 1 (by rfl) ⟨133688, by rfl⟩ : syracuseStep 178251 = 267377) B267377
theorem B178263 : Blo 175800 178263 := bstep (se 1 (by rfl) ⟨133697, by rfl⟩ : syracuseStep 178263 = 267395) B267395
theorem B178283 : Blo 175800 178283 := bstep (se 1 (by rfl) ⟨133712, by rfl⟩ : syracuseStep 178283 = 267425) B267425
theorem B178295 : Blo 175800 178295 := bstep (se 1 (by rfl) ⟨133721, by rfl⟩ : syracuseStep 178295 = 267443) B267443
theorem B178315 : Blo 175800 178315 := bstep (se 1 (by rfl) ⟨133736, by rfl⟩ : syracuseStep 178315 = 267473) B267473
theorem B178327 : Blo 175800 178327 := bstep (se 1 (by rfl) ⟨133745, by rfl⟩ : syracuseStep 178327 = 267491) B267491
theorem B178347 : Blo 175800 178347 := bstep (se 1 (by rfl) ⟨133760, by rfl⟩ : syracuseStep 178347 = 267521) B267521
theorem B178359 : Blo 175800 178359 := bstep (se 1 (by rfl) ⟨133769, by rfl⟩ : syracuseStep 178359 = 267539) B267539
theorem B178379 : Blo 175800 178379 := bstep (se 1 (by rfl) ⟨133784, by rfl⟩ : syracuseStep 178379 = 267569) B267569
theorem B178391 : Blo 175800 178391 := bstep (se 1 (by rfl) ⟨133793, by rfl⟩ : syracuseStep 178391 = 267587) B267587
theorem B178411 : Blo 175800 178411 := bstep (se 1 (by rfl) ⟨133808, by rfl⟩ : syracuseStep 178411 = 267617) B267617
theorem B178423 : Blo 175800 178423 := bstep (se 1 (by rfl) ⟨133817, by rfl⟩ : syracuseStep 178423 = 267635) B267635
theorem B178443 : Blo 175800 178443 := bstep (se 1 (by rfl) ⟨133832, by rfl⟩ : syracuseStep 178443 = 267665) B267665
theorem B178455 : Blo 175800 178455 := bstep (se 1 (by rfl) ⟨133841, by rfl⟩ : syracuseStep 178455 = 267683) B267683
theorem B178475 : Blo 175800 178475 := bstep (se 1 (by rfl) ⟨133856, by rfl⟩ : syracuseStep 178475 = 267713) B267713
theorem B178487 : Blo 175800 178487 := bstep (se 1 (by rfl) ⟨133865, by rfl⟩ : syracuseStep 178487 = 267731) B267731
theorem B178507 : Blo 175800 178507 := bstep (se 1 (by rfl) ⟨133880, by rfl⟩ : syracuseStep 178507 = 267761) B267761
theorem B178519 : Blo 175800 178519 := bstep (se 1 (by rfl) ⟨133889, by rfl⟩ : syracuseStep 178519 = 267779) B267779
theorem B178539 : Blo 175800 178539 := bstep (se 1 (by rfl) ⟨133904, by rfl⟩ : syracuseStep 178539 = 267809) B267809
theorem B178551 : Blo 175800 178551 := bstep (se 1 (by rfl) ⟨133913, by rfl⟩ : syracuseStep 178551 = 267827) B267827
theorem B178571 : Blo 175800 178571 := bstep (se 1 (by rfl) ⟨133928, by rfl⟩ : syracuseStep 178571 = 267857) B267857
theorem B670103 : Blo 175800 670103 := bstep (se 1 (by rfl) ⟨502577, by rfl⟩ : syracuseStep 670103 = 1005155) B1005155
theorem B178583 : Blo 175800 178583 := bstep (se 1 (by rfl) ⟨133937, by rfl⟩ : syracuseStep 178583 = 267875) B267875
theorem B1456535 : Blo 175800 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B178603 : Blo 175800 178603 := bstep (se 1 (by rfl) ⟨133952, by rfl⟩ : syracuseStep 178603 = 267905) B267905
theorem B178615 : Blo 175800 178615 := bstep (se 1 (by rfl) ⟨133961, by rfl⟩ : syracuseStep 178615 = 267923) B267923
theorem B178635 : Blo 175800 178635 := bstep (se 1 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 178635 = 267953) B267953
theorem B178647 : Blo 175800 178647 := bstep (se 1 (by rfl) ⟨133985, by rfl⟩ : syracuseStep 178647 = 267971) B267971
theorem B604637 : Blo 175800 604637 := bstep (se 3 (by rfl) ⟨113369, by rfl⟩ : syracuseStep 604637 = 226739) B226739
theorem B178667 : Blo 175800 178667 := bstep (se 1 (by rfl) ⟨134000, by rfl⟩ : syracuseStep 178667 = 268001) B268001
theorem B178679 : Blo 175800 178679 := bstep (se 1 (by rfl) ⟨134009, by rfl⟩ : syracuseStep 178679 = 268019) B268019
theorem B178699 : Blo 175800 178699 := bstep (se 1 (by rfl) ⟨134024, by rfl⟩ : syracuseStep 178699 = 268049) B268049
theorem B178711 : Blo 175800 178711 := bstep (se 1 (by rfl) ⟨134033, by rfl⟩ : syracuseStep 178711 = 268067) B268067
theorem B178731 : Blo 175800 178731 := bstep (se 1 (by rfl) ⟨134048, by rfl⟩ : syracuseStep 178731 = 268097) B268097
theorem B178743 : Blo 175800 178743 := bstep (se 1 (by rfl) ⟨134057, by rfl⟩ : syracuseStep 178743 = 268115) B268115
theorem B178763 : Blo 175800 178763 := bstep (se 1 (by rfl) ⟨134072, by rfl⟩ : syracuseStep 178763 = 268145) B268145
theorem B178775 : Blo 175800 178775 := bstep (se 1 (by rfl) ⟨134081, by rfl⟩ : syracuseStep 178775 = 268163) B268163
theorem B670301 : Blo 175800 670301 := bstep (se 3 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 670301 = 251363) B251363
theorem B178795 : Blo 175800 178795 := bstep (se 1 (by rfl) ⟨134096, by rfl⟩ : syracuseStep 178795 = 268193) B268193
theorem B178807 : Blo 175800 178807 := bstep (se 1 (by rfl) ⟨134105, by rfl⟩ : syracuseStep 178807 = 268211) B268211
theorem B735875 : Blo 175800 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B178827 : Blo 175800 178827 := bstep (se 1 (by rfl) ⟨134120, by rfl⟩ : syracuseStep 178827 = 268241) B268241
theorem B506519 : Blo 175800 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B178839 : Blo 175800 178839 := bstep (se 1 (by rfl) ⟨134129, by rfl⟩ : syracuseStep 178839 = 268259) B268259
theorem B178859 : Blo 175800 178859 := bstep (se 1 (by rfl) ⟨134144, by rfl⟩ : syracuseStep 178859 = 268289) B268289
theorem B178871 : Blo 175800 178871 := bstep (se 1 (by rfl) ⟨134153, by rfl⟩ : syracuseStep 178871 = 268307) B268307
theorem B178891 : Blo 175800 178891 := bstep (se 1 (by rfl) ⟨134168, by rfl⟩ : syracuseStep 178891 = 268337) B268337
theorem B178903 : Blo 175800 178903 := bstep (se 1 (by rfl) ⟨134177, by rfl⟩ : syracuseStep 178903 = 268355) B268355
theorem B178923 : Blo 175800 178923 := bstep (se 1 (by rfl) ⟨134192, by rfl⟩ : syracuseStep 178923 = 268385) B268385
theorem B178935 : Blo 175800 178935 := bstep (se 1 (by rfl) ⟨134201, by rfl⟩ : syracuseStep 178935 = 268403) B268403
theorem B178955 : Blo 175800 178955 := bstep (se 1 (by rfl) ⟨134216, by rfl⟩ : syracuseStep 178955 = 268433) B268433
theorem B178967 : Blo 175800 178967 := bstep (se 1 (by rfl) ⟨134225, by rfl⟩ : syracuseStep 178967 = 268451) B268451
theorem B178987 : Blo 175800 178987 := bstep (se 1 (by rfl) ⟨134240, by rfl⟩ : syracuseStep 178987 = 268481) B268481
theorem B178999 : Blo 175800 178999 := bstep (se 1 (by rfl) ⟨134249, by rfl⟩ : syracuseStep 178999 = 268499) B268499
theorem B179019 : Blo 175800 179019 := bstep (se 1 (by rfl) ⟨134264, by rfl⟩ : syracuseStep 179019 = 268529) B268529
theorem B179031 : Blo 175800 179031 := bstep (se 1 (by rfl) ⟨134273, by rfl⟩ : syracuseStep 179031 = 268547) B268547
theorem B179051 : Blo 175800 179051 := bstep (se 1 (by rfl) ⟨134288, by rfl⟩ : syracuseStep 179051 = 268577) B268577
theorem B179063 : Blo 175800 179063 := bstep (se 1 (by rfl) ⟨134297, by rfl⟩ : syracuseStep 179063 = 268595) B268595
theorem B179083 : Blo 175800 179083 := bstep (se 1 (by rfl) ⟨134312, by rfl⟩ : syracuseStep 179083 = 268625) B268625
theorem B179095 : Blo 175800 179095 := bstep (se 1 (by rfl) ⟨134321, by rfl⟩ : syracuseStep 179095 = 268643) B268643
theorem B179115 : Blo 175800 179115 := bstep (se 1 (by rfl) ⟨134336, by rfl⟩ : syracuseStep 179115 = 268673) B268673
theorem B179127 : Blo 175800 179127 := bstep (se 1 (by rfl) ⟨134345, by rfl⟩ : syracuseStep 179127 = 268691) B268691
theorem B179147 : Blo 175800 179147 := bstep (se 1 (by rfl) ⟨134360, by rfl⟩ : syracuseStep 179147 = 268721) B268721
theorem B179159 : Blo 175800 179159 := bstep (se 1 (by rfl) ⟨134369, by rfl⟩ : syracuseStep 179159 = 268739) B268739
theorem B179179 : Blo 175800 179179 := bstep (se 1 (by rfl) ⟨134384, by rfl⟩ : syracuseStep 179179 = 268769) B268769
theorem B179191 : Blo 175800 179191 := bstep (se 1 (by rfl) ⟨134393, by rfl⟩ : syracuseStep 179191 = 268787) B268787
theorem B179211 : Blo 175800 179211 := bstep (se 1 (by rfl) ⟨134408, by rfl⟩ : syracuseStep 179211 = 268817) B268817
theorem B179223 : Blo 175800 179223 := bstep (se 1 (by rfl) ⟨134417, by rfl⟩ : syracuseStep 179223 = 268835) B268835
theorem B179243 : Blo 175800 179243 := bstep (se 1 (by rfl) ⟨134432, by rfl⟩ : syracuseStep 179243 = 268865) B268865
theorem B179255 : Blo 175800 179255 := bstep (se 1 (by rfl) ⟨134441, by rfl⟩ : syracuseStep 179255 = 268883) B268883
theorem B179275 : Blo 175800 179275 := bstep (se 1 (by rfl) ⟨134456, by rfl⟩ : syracuseStep 179275 = 268913) B268913
theorem B179287 : Blo 175800 179287 := bstep (se 1 (by rfl) ⟨134465, by rfl⟩ : syracuseStep 179287 = 268931) B268931
theorem B179307 : Blo 175800 179307 := bstep (se 1 (by rfl) ⟨134480, by rfl⟩ : syracuseStep 179307 = 268961) B268961
theorem B179319 : Blo 175800 179319 := bstep (se 1 (by rfl) ⟨134489, by rfl⟩ : syracuseStep 179319 = 268979) B268979
theorem B179339 : Blo 175800 179339 := bstep (se 1 (by rfl) ⟨134504, by rfl⟩ : syracuseStep 179339 = 269009) B269009
theorem B375959 : Blo 175800 375959 := bstep (se 1 (by rfl) ⟨281969, by rfl⟩ : syracuseStep 375959 = 563939) B563939
theorem B179351 : Blo 175800 179351 := bstep (se 1 (by rfl) ⟨134513, by rfl⟩ : syracuseStep 179351 = 269027) B269027
theorem B179371 : Blo 175800 179371 := bstep (se 1 (by rfl) ⟨134528, by rfl⟩ : syracuseStep 179371 = 269057) B269057
theorem B179383 : Blo 175800 179383 := bstep (se 1 (by rfl) ⟨134537, by rfl⟩ : syracuseStep 179383 = 269075) B269075
theorem B179403 : Blo 175800 179403 := bstep (se 1 (by rfl) ⟨134552, by rfl⟩ : syracuseStep 179403 = 269105) B269105
theorem B179415 : Blo 175800 179415 := bstep (se 1 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 179415 = 269123) B269123
theorem B179435 : Blo 175800 179435 := bstep (se 1 (by rfl) ⟨134576, by rfl⟩ : syracuseStep 179435 = 269153) B269153
theorem B179447 : Blo 175800 179447 := bstep (se 1 (by rfl) ⟨134585, by rfl⟩ : syracuseStep 179447 = 269171) B269171
theorem B179467 : Blo 175800 179467 := bstep (se 1 (by rfl) ⟨134600, by rfl⟩ : syracuseStep 179467 = 269201) B269201
theorem B179479 : Blo 175800 179479 := bstep (se 1 (by rfl) ⟨134609, by rfl⟩ : syracuseStep 179479 = 269219) B269219
theorem B179499 : Blo 175800 179499 := bstep (se 1 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 179499 = 269249) B269249
theorem B179511 : Blo 175800 179511 := bstep (se 1 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 179511 = 269267) B269267
theorem B179531 : Blo 175800 179531 := bstep (se 1 (by rfl) ⟨134648, by rfl⟩ : syracuseStep 179531 = 269297) B269297
theorem B179543 : Blo 175800 179543 := bstep (se 1 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 179543 = 269315) B269315
theorem B179563 : Blo 175800 179563 := bstep (se 1 (by rfl) ⟨134672, by rfl⟩ : syracuseStep 179563 = 269345) B269345
theorem B179575 : Blo 175800 179575 := bstep (se 1 (by rfl) ⟨134681, by rfl⟩ : syracuseStep 179575 = 269363) B269363
theorem B179595 : Blo 175800 179595 := bstep (se 1 (by rfl) ⟨134696, by rfl⟩ : syracuseStep 179595 = 269393) B269393
theorem B4078997 : Blo 175800 4078997 := bstep (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) B191203
theorem B179607 : Blo 175800 179607 := bstep (se 1 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 179607 = 269411) B269411
theorem B179627 : Blo 175800 179627 := bstep (se 1 (by rfl) ⟨134720, by rfl⟩ : syracuseStep 179627 = 269441) B269441
theorem B179639 : Blo 175800 179639 := bstep (se 1 (by rfl) ⟨134729, by rfl⟩ : syracuseStep 179639 = 269459) B269459
theorem B376267 : Blo 175800 376267 := bstep (se 1 (by rfl) ⟨282200, by rfl⟩ : syracuseStep 376267 = 564401) B564401
theorem B179659 : Blo 175800 179659 := bstep (se 1 (by rfl) ⟨134744, by rfl⟩ : syracuseStep 179659 = 269489) B269489
theorem B179671 : Blo 175800 179671 := bstep (se 1 (by rfl) ⟨134753, by rfl⟩ : syracuseStep 179671 = 269507) B269507
theorem B540121 : Blo 175800 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B179691 : Blo 175800 179691 := bstep (se 1 (by rfl) ⟨134768, by rfl⟩ : syracuseStep 179691 = 269537) B269537
theorem B179703 : Blo 175800 179703 := bstep (se 1 (by rfl) ⟨134777, by rfl⟩ : syracuseStep 179703 = 269555) B269555
theorem B179723 : Blo 175800 179723 := bstep (se 1 (by rfl) ⟨134792, by rfl⟩ : syracuseStep 179723 = 269585) B269585
theorem B179735 : Blo 175800 179735 := bstep (se 1 (by rfl) ⟨134801, by rfl⟩ : syracuseStep 179735 = 269603) B269603
theorem B179755 : Blo 175800 179755 := bstep (se 1 (by rfl) ⟨134816, by rfl⟩ : syracuseStep 179755 = 269633) B269633
theorem B1523245 : Blo 175800 1523245 := bstep (se 3 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 1523245 = 571217) B571217
theorem B179767 : Blo 175800 179767 := bstep (se 1 (by rfl) ⟨134825, by rfl⟩ : syracuseStep 179767 = 269651) B269651
theorem B605771 : Blo 175800 605771 := bstep (se 1 (by rfl) ⟨454328, by rfl⟩ : syracuseStep 605771 = 908657) B908657
theorem B179787 : Blo 175800 179787 := bstep (se 1 (by rfl) ⟨134840, by rfl⟩ : syracuseStep 179787 = 269681) B269681
theorem B179799 : Blo 175800 179799 := bstep (se 1 (by rfl) ⟨134849, by rfl⟩ : syracuseStep 179799 = 269699) B269699
theorem B343667 : Blo 175800 343667 := bstep (se 1 (by rfl) ⟨257750, by rfl⟩ : syracuseStep 343667 = 515501) B515501
theorem B900881 : Blo 175800 900881 := bstep (se 2 (by rfl) ⟨337830, by rfl⟩ : syracuseStep 900881 = 675661) B675661
theorem B606041 : Blo 175800 606041 := bstep (se 2 (by rfl) ⟨227265, by rfl⟩ : syracuseStep 606041 = 454531) B454531
theorem B901043 : Blo 175800 901043 := bstep (se 1 (by rfl) ⟨675782, by rfl⟩ : syracuseStep 901043 = 1351565) B1351565
theorem B1130597 : Blo 175800 1130597 := bstep (se 4 (by rfl) ⟨105993, by rfl⟩ : syracuseStep 1130597 = 211987) B211987
theorem B672259 : Blo 175800 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B606743 : Blo 175800 606743 := bstep (se 1 (by rfl) ⟨455057, by rfl⟩ : syracuseStep 606743 = 910115) B910115
theorem B2900555 : Blo 175800 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B1327691 : Blo 175800 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B377497 : Blo 175800 377497 := bstep (se 2 (by rfl) ⟨141561, by rfl⟩ : syracuseStep 377497 = 283123) B283123
theorem B672563 : Blo 175800 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B1524581 : Blo 175800 1524581 := bstep (se 4 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 1524581 = 285859) B285859
theorem B1622915 : Blo 175800 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B213899 : Blo 175800 213899 := bstep (se 1 (by rfl) ⟨160424, by rfl⟩ : syracuseStep 213899 = 320849) B320849
theorem B508979 : Blo 175800 508979 := bstep (se 1 (by rfl) ⟨381734, by rfl⟩ : syracuseStep 508979 = 763469) B763469
theorem B1131671 : Blo 175800 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B181451 : Blo 175800 181451 := bstep (se 1 (by rfl) ⟨136088, by rfl⟩ : syracuseStep 181451 = 272177) B272177
theorem B1295621 : Blo 175800 1295621 := bstep (se 4 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 1295621 = 242929) B242929
theorem B804269 : Blo 175800 804269 := bstep (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) B301601
theorem B673217 : Blo 175800 673217 := bstep (se 2 (by rfl) ⟨252456, by rfl⟩ : syracuseStep 673217 = 504913) B504913
theorem B2606627 : Blo 175800 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B771677 : Blo 175800 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B1001281 : Blo 175800 1001281 := bstep (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) B750961
theorem B902987 : Blo 175800 902987 := bstep (se 1 (by rfl) ⟨677240, by rfl⟩ : syracuseStep 902987 = 1354481) B1354481
theorem B1624157 : Blo 175800 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B575819 : Blo 175800 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B641611 : Blo 175800 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B674477 : Blo 175800 674477 := bstep (se 3 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 674477 = 252929) B252929
theorem B674507 : Blo 175800 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B2411441 : Blo 175800 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B281675 : Blo 175800 281675 := bstep (se 1 (by rfl) ⟨211256, by rfl⟩ : syracuseStep 281675 = 422513) B422513
theorem B675161 : Blo 175800 675161 := bstep (se 2 (by rfl) ⟨253185, by rfl⟩ : syracuseStep 675161 = 506371) B506371
theorem B642563 : Blo 175800 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B773677 : Blo 175800 773677 := bstep (se 3 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 773677 = 290129) B290129
theorem B904769 : Blo 175800 904769 := bstep (se 2 (by rfl) ⟨339288, by rfl⟩ : syracuseStep 904769 = 678577) B678577
theorem B380531 : Blo 175800 380531 := bstep (se 1 (by rfl) ⟨285398, by rfl⟩ : syracuseStep 380531 = 570797) B570797
theorem B675479 : Blo 175800 675479 := bstep (se 1 (by rfl) ⟨506609, by rfl⟩ : syracuseStep 675479 = 1013219) B1013219
theorem B511667 : Blo 175800 511667 := bstep (se 1 (by rfl) ⟨383750, by rfl⟩ : syracuseStep 511667 = 767501) B767501
theorem B282457 : Blo 175800 282457 := bstep (se 2 (by rfl) ⟨105921, by rfl⟩ : syracuseStep 282457 = 211843) B211843
theorem B511895 : Blo 175800 511895 := bstep (se 1 (by rfl) ⟨383921, by rfl⟩ : syracuseStep 511895 = 767843) B767843
theorem B479155 : Blo 175800 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B446411 : Blo 175800 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B479197 : Blo 175800 479197 := bstep (se 3 (by rfl) ⟨89849, by rfl⟩ : syracuseStep 479197 = 179699) B179699
theorem B381017 : Blo 175800 381017 := bstep (se 2 (by rfl) ⟨142881, by rfl⟩ : syracuseStep 381017 = 285763) B285763
theorem B1527959 : Blo 175800 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B2904245 : Blo 175800 2904245 := bstep (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) B272273
theorem B676147 : Blo 175800 676147 := bstep (se 1 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 676147 = 1014221) B1014221
theorem B610763 : Blo 175800 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B250457 : Blo 175800 250457 := bstep (se 2 (by rfl) ⟨93921, by rfl⟩ : syracuseStep 250457 = 187843) B187843
theorem B1135235 : Blo 175800 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B250571 : Blo 175800 250571 := bstep (se 1 (by rfl) ⟨187928, by rfl⟩ : syracuseStep 250571 = 375857) B375857
theorem B447383 : Blo 175800 447383 := bstep (se 1 (by rfl) ⟨335537, by rfl⟩ : syracuseStep 447383 = 671075) B671075
theorem B1004723 : Blo 175800 1004723 := bstep (se 1 (by rfl) ⟨753542, by rfl⟩ : syracuseStep 1004723 = 1507085) B1507085
theorem B251095 : Blo 175800 251095 := bstep (se 1 (by rfl) ⟨188321, by rfl⟩ : syracuseStep 251095 = 376643) B376643
theorem B2020787 : Blo 175800 2020787 := bstep (se 1 (by rfl) ⟨1515590, by rfl⟩ : syracuseStep 2020787 = 3031181) B3031181
theorem B906713 : Blo 175800 906713 := bstep (se 2 (by rfl) ⟨340017, by rfl⟩ : syracuseStep 906713 = 680035) B680035
theorem B644611 : Blo 175800 644611 := bstep (se 1 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 644611 = 966917) B966917
theorem B677393 : Blo 175800 677393 := bstep (se 2 (by rfl) ⟨254022, by rfl⟩ : syracuseStep 677393 = 508045) B508045
theorem B448051 : Blo 175800 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B808537 : Blo 175800 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B448193 : Blo 175800 448193 := bstep (se 2 (by rfl) ⟨168072, by rfl⟩ : syracuseStep 448193 = 336145) B336145
theorem B382657 : Blo 175800 382657 := bstep (se 2 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 382657 = 286993) B286993
theorem B644915 : Blo 175800 644915 := bstep (se 1 (by rfl) ⟨483686, by rfl⟩ : syracuseStep 644915 = 967373) B967373
theorem B645043 : Blo 175800 645043 := bstep (se 1 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 645043 = 967565) B967565
theorem B251915 : Blo 175800 251915 := bstep (se 1 (by rfl) ⟨188936, by rfl⟩ : syracuseStep 251915 = 377873) B377873
theorem B678091 : Blo 175800 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B1628461 : Blo 175800 1628461 := bstep (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) B610673
theorem B678365 : Blo 175800 678365 := bstep (se 3 (by rfl) ⟨127193, by rfl⟩ : syracuseStep 678365 = 254387) B254387
theorem B1006181 : Blo 175800 1006181 := bstep (se 4 (by rfl) ⟨94329, by rfl⟩ : syracuseStep 1006181 = 188659) B188659
theorem B2022245 : Blo 175800 2022245 := bstep (se 4 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 2022245 = 379171) B379171
theorem B449459 : Blo 175800 449459 := bstep (se 1 (by rfl) ⟨337094, by rfl⟩ : syracuseStep 449459 = 674189) B674189
theorem B908333 : Blo 175800 908333 := bstep (se 3 (by rfl) ⟨170312, by rfl⟩ : syracuseStep 908333 = 340625) B340625
theorem B679063 : Blo 175800 679063 := bstep (se 1 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 679063 = 1018595) B1018595
theorem B1039661 : Blo 175800 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B449995 : Blo 175800 449995 := bstep (se 1 (by rfl) ⟨337496, by rfl⟩ : syracuseStep 449995 = 674993) B674993
theorem B1433153 : Blo 175800 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B450137 : Blo 175800 450137 := bstep (se 2 (by rfl) ⟨168801, by rfl⟩ : syracuseStep 450137 = 337603) B337603
theorem B778049 : Blo 175800 778049 := bstep (se 2 (by rfl) ⟨291768, by rfl⟩ : syracuseStep 778049 = 583537) B583537
theorem B253783 : Blo 175800 253783 := bstep (se 1 (by rfl) ⟨190337, by rfl⟩ : syracuseStep 253783 = 380675) B380675
theorem B679853 : Blo 175800 679853 := bstep (se 3 (by rfl) ⟨127472, by rfl⟩ : syracuseStep 679853 = 254945) B254945
theorem B188407 : Blo 175800 188407 := bstep (se 1 (by rfl) ⟨141305, by rfl⟩ : syracuseStep 188407 = 282611) B282611
theorem B221195 : Blo 175800 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B11952197 : Blo 175800 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B319639 : Blo 175800 319639 := bstep (se 1 (by rfl) ⟨239729, by rfl⟩ : syracuseStep 319639 = 479459) B479459
theorem B1466545 : Blo 175800 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B188663 : Blo 175800 188663 := bstep (se 1 (by rfl) ⟨141497, by rfl⟩ : syracuseStep 188663 = 282995) B282995
theorem B319883 : Blo 175800 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B450967 : Blo 175800 450967 := bstep (se 1 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 450967 = 676451) B676451
theorem B6545933 : Blo 175800 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B811565 : Blo 175800 811565 := bstep (se 3 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 811565 = 304337) B304337
theorem B1336013 : Blo 175800 1336013 := bstep (se 3 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 1336013 = 501005) B501005
theorem B320215 : Blo 175800 320215 := bstep (se 1 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 320215 = 480323) B480323
theorem B189227 : Blo 175800 189227 := bstep (se 1 (by rfl) ⟨141920, by rfl⟩ : syracuseStep 189227 = 283841) B283841
theorem B680755 : Blo 175800 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B451403 : Blo 175800 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B320345 : Blo 175800 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B385931 : Blo 175800 385931 := bstep (se 1 (by rfl) ⟨289448, by rfl⟩ : syracuseStep 385931 = 578897) B578897
theorem B287705 : Blo 175800 287705 := bstep (se 2 (by rfl) ⟨107889, by rfl⟩ : syracuseStep 287705 = 215779) B215779
theorem B1336499 : Blo 175800 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B451777 : Blo 175800 451777 := bstep (se 2 (by rfl) ⟨169416, by rfl⟩ : syracuseStep 451777 = 338833) B338833
theorem B681281 : Blo 175800 681281 := bstep (se 2 (by rfl) ⟨255480, by rfl⟩ : syracuseStep 681281 = 510961) B510961
theorem B255307 : Blo 175800 255307 := bstep (se 1 (by rfl) ⟨191480, by rfl⟩ : syracuseStep 255307 = 382961) B382961
theorem B484811 : Blo 175800 484811 := bstep (se 1 (by rfl) ⟨363608, by rfl⟩ : syracuseStep 484811 = 727217) B727217
theorem B222679 : Blo 175800 222679 := bstep (se 1 (by rfl) ⟨167009, by rfl⟩ : syracuseStep 222679 = 334019) B334019
theorem B714257 : Blo 175800 714257 := bstep (se 2 (by rfl) ⟨267846, by rfl⟩ : syracuseStep 714257 = 535693) B535693
theorem B845585 : Blo 175800 845585 := bstep (se 2 (by rfl) ⟨317094, by rfl⟩ : syracuseStep 845585 = 634189) B634189
theorem B452375 : Blo 175800 452375 := bstep (se 1 (by rfl) ⟨339281, by rfl⟩ : syracuseStep 452375 = 678563) B678563
theorem B190679 : Blo 175800 190679 := bstep (se 1 (by rfl) ⟨143009, by rfl⟩ : syracuseStep 190679 = 286019) B286019
theorem B1632473 : Blo 175800 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B223499 : Blo 175800 223499 := bstep (se 1 (by rfl) ⟨167624, by rfl⟩ : syracuseStep 223499 = 335249) B335249
theorem B453185 : Blo 175800 453185 := bstep (se 2 (by rfl) ⟨169944, by rfl⟩ : syracuseStep 453185 = 339889) B339889
theorem B1337957 : Blo 175800 1337957 := bstep (se 4 (by rfl) ⟨125433, by rfl⟩ : syracuseStep 1337957 = 250867) B250867
theorem B682897 : Blo 175800 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B224203 : Blo 175800 224203 := bstep (se 1 (by rfl) ⟨168152, by rfl⟩ : syracuseStep 224203 = 336305) B336305
theorem B1338443 : Blo 175800 1338443 := bstep (se 1 (by rfl) ⟨1003832, by rfl⟩ : syracuseStep 1338443 = 2007665) B2007665
theorem B453721 : Blo 175800 453721 := bstep (se 2 (by rfl) ⟨170145, by rfl⟩ : syracuseStep 453721 = 340291) B340291
theorem B224471 : Blo 175800 224471 := bstep (se 1 (by rfl) ⟨168353, by rfl⟩ : syracuseStep 224471 = 336707) B336707
theorem B1371485 : Blo 175800 1371485 := bstep (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) B514307
theorem B7925141 : Blo 175800 7925141 := bstep (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) B371491
theorem B225175 : Blo 175800 225175 := bstep (se 1 (by rfl) ⟨168881, by rfl⟩ : syracuseStep 225175 = 337763) B337763
theorem B1339523 : Blo 175800 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B454835 : Blo 175800 454835 := bstep (se 1 (by rfl) ⟨341126, by rfl⟩ : syracuseStep 454835 = 682253) B682253
theorem B1012013 : Blo 175800 1012013 := bstep (se 3 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 1012013 = 379505) B379505
theorem B1372717 : Blo 175800 1372717 := bstep (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) B514769
theorem B291481 : Blo 175800 291481 := bstep (se 2 (by rfl) ⟨109305, by rfl⟩ : syracuseStep 291481 = 218611) B218611
theorem B1274629 : Blo 175800 1274629 := bstep (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) B238993
theorem B717661 : Blo 175800 717661 := bstep (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) B269123
theorem B2946179 : Blo 175800 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1078829 : Blo 175800 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B226891 : Blo 175800 226891 := bstep (se 1 (by rfl) ⟨170168, by rfl⟩ : syracuseStep 226891 = 340337) B340337
theorem B489419 : Blo 175800 489419 := bstep (se 1 (by rfl) ⟨367064, by rfl⟩ : syracuseStep 489419 = 734129) B734129
theorem B1144793 : Blo 175800 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B2553869 : Blo 175800 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B227659 : Blo 175800 227659 := bstep (se 1 (by rfl) ⟨170744, by rfl⟩ : syracuseStep 227659 = 341489) B341489
theorem B1014403 : Blo 175800 1014403 := bstep (se 1 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 1014403 = 1521605) B1521605
theorem B457367 : Blo 175800 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B752449 : Blo 175800 752449 := bstep (se 2 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 752449 = 564337) B564337
theorem B1080139 : Blo 175800 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1538909 : Blo 175800 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B1080337 : Blo 175800 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B916525 : Blo 175800 916525 := bstep (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) B343697
theorem B2260061 : Blo 175800 2260061 := bstep (se 3 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 2260061 = 847523) B847523
theorem B228619 : Blo 175800 228619 := bstep (se 1 (by rfl) ⟨171464, by rfl⟩ : syracuseStep 228619 = 342929) B342929
theorem B753047 : Blo 175800 753047 := bstep (se 1 (by rfl) ⟨564785, by rfl⟩ : syracuseStep 753047 = 1129571) B1129571
theorem B1015361 : Blo 175800 1015361 := bstep (se 2 (by rfl) ⟨380760, by rfl⟩ : syracuseStep 1015361 = 761521) B761521
theorem B1146433 : Blo 175800 1146433 := bstep (se 2 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 1146433 = 859825) B859825
theorem B2620997 : Blo 175800 2620997 := bstep (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) B491437
theorem B589853 : Blo 175800 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B753731 : Blo 175800 753731 := bstep (se 1 (by rfl) ⟨565298, by rfl⟩ : syracuseStep 753731 = 1130597) B1130597
theorem B426185 : Blo 175800 426185 := bstep (se 2 (by rfl) ⟨159819, by rfl⟩ : syracuseStep 426185 = 319639) B319639
theorem B721133 : Blo 175800 721133 := bstep (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) B270425
theorem B1933703 : Blo 175800 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B885127 : Blo 175800 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B754105 : Blo 175800 754105 := bstep (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) B565579
theorem B1016387 : Blo 175800 1016387 := bstep (se 1 (by rfl) ⟨762290, by rfl⟩ : syracuseStep 1016387 = 1524581) B1524581
theorem B1081943 : Blo 175800 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B4326007 : Blo 175800 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B754447 : Blo 175800 754447 := bstep (se 1 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 754447 = 1131671) B1131671
theorem B426953 : Blo 175800 426953 := bstep (se 2 (by rfl) ⟨160107, by rfl⟩ : syracuseStep 426953 = 320215) B320215
theorem B853021 : Blo 175800 853021 := bstep (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) B319883
theorem B198031 : Blo 175800 198031 := bstep (se 1 (by rfl) ⟨148523, by rfl⟩ : syracuseStep 198031 = 297047) B297047
theorem B1082771 : Blo 175800 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B1148381 : Blo 175800 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B263723 : Blo 175800 263723 := bstep (se 1 (by rfl) ⟨197792, by rfl⟩ : syracuseStep 263723 = 395585) B395585
theorem B263753 : Blo 175800 263753 := bstep (se 2 (by rfl) ⟨98907, by rfl⟩ : syracuseStep 263753 = 197815) B197815
theorem B263867 : Blo 175800 263867 := bstep (se 1 (by rfl) ⟨197900, by rfl⟩ : syracuseStep 263867 = 395801) B395801
theorem B263927 : Blo 175800 263927 := bstep (se 1 (by rfl) ⟨197945, by rfl⟩ : syracuseStep 263927 = 395891) B395891
theorem B263951 : Blo 175800 263951 := bstep (se 1 (by rfl) ⟨197963, by rfl⟩ : syracuseStep 263951 = 395927) B395927
theorem B263993 : Blo 175800 263993 := bstep (se 2 (by rfl) ⟨98997, by rfl⟩ : syracuseStep 263993 = 197995) B197995
theorem B264071 : Blo 175800 264071 := bstep (se 1 (by rfl) ⟨198053, by rfl⟩ : syracuseStep 264071 = 396107) B396107
theorem B198535 : Blo 175800 198535 := bstep (se 1 (by rfl) ⟨148901, by rfl⟩ : syracuseStep 198535 = 297803) B297803
theorem B264107 : Blo 175800 264107 := bstep (se 1 (by rfl) ⟨198080, by rfl⟩ : syracuseStep 264107 = 396161) B396161
theorem B296905 : Blo 175800 296905 := bstep (se 2 (by rfl) ⟨111339, by rfl⟩ : syracuseStep 296905 = 222679) B222679
theorem B264137 : Blo 175800 264137 := bstep (se 2 (by rfl) ⟨99051, by rfl⟩ : syracuseStep 264137 = 198103) B198103
theorem B1607627 : Blo 175800 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B264251 : Blo 175800 264251 := bstep (se 1 (by rfl) ⟨198188, by rfl⟩ : syracuseStep 264251 = 396377) B396377
theorem B198715 : Blo 175800 198715 := bstep (se 1 (by rfl) ⟨149036, by rfl⟩ : syracuseStep 198715 = 298073) B298073
theorem B264311 : Blo 175800 264311 := bstep (se 1 (by rfl) ⟨198233, by rfl⟩ : syracuseStep 264311 = 396467) B396467
theorem B264335 : Blo 175800 264335 := bstep (se 1 (by rfl) ⟨198251, by rfl⟩ : syracuseStep 264335 = 396503) B396503
theorem B264377 : Blo 175800 264377 := bstep (se 2 (by rfl) ⟨99141, by rfl⟩ : syracuseStep 264377 = 198283) B198283
theorem B2033909 : Blo 175800 2033909 := bstep (se 5 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 2033909 = 190679) B190679
theorem B264455 : Blo 175800 264455 := bstep (se 1 (by rfl) ⟨198341, by rfl⟩ : syracuseStep 264455 = 396683) B396683
theorem B264491 : Blo 175800 264491 := bstep (se 1 (by rfl) ⟨198368, by rfl⟩ : syracuseStep 264491 = 396737) B396737
theorem B264521 : Blo 175800 264521 := bstep (se 2 (by rfl) ⟨99195, by rfl⟩ : syracuseStep 264521 = 198391) B198391
theorem B428375 : Blo 175800 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B395639 : Blo 175800 395639 := bstep (se 1 (by rfl) ⟨296729, by rfl⟩ : syracuseStep 395639 = 593459) B593459
theorem B264635 : Blo 175800 264635 := bstep (se 1 (by rfl) ⟨198476, by rfl⟩ : syracuseStep 264635 = 396953) B396953
theorem B264695 : Blo 175800 264695 := bstep (se 1 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 264695 = 397043) B397043
theorem B723467 : Blo 175800 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B264719 : Blo 175800 264719 := bstep (se 1 (by rfl) ⟨198539, by rfl⟩ : syracuseStep 264719 = 397079) B397079
theorem B199183 : Blo 175800 199183 := bstep (se 1 (by rfl) ⟨149387, by rfl⟩ : syracuseStep 199183 = 298775) B298775
theorem B395819 : Blo 175800 395819 := bstep (se 1 (by rfl) ⟨296864, by rfl⟩ : syracuseStep 395819 = 593729) B593729
theorem B264761 : Blo 175800 264761 := bstep (se 2 (by rfl) ⟨99285, by rfl⟩ : syracuseStep 264761 = 198571) B198571
theorem B297607 : Blo 175800 297607 := bstep (se 1 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 297607 = 446411) B446411
theorem B264839 : Blo 175800 264839 := bstep (se 1 (by rfl) ⟨198629, by rfl⟩ : syracuseStep 264839 = 397259) B397259
theorem B264875 : Blo 175800 264875 := bstep (se 1 (by rfl) ⟨198656, by rfl⟩ : syracuseStep 264875 = 397313) B397313
theorem B264905 : Blo 175800 264905 := bstep (se 2 (by rfl) ⟨99339, by rfl⟩ : syracuseStep 264905 = 198679) B198679
theorem B1018639 : Blo 175800 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B1936163 : Blo 175800 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B265019 : Blo 175800 265019 := bstep (se 1 (by rfl) ⟨198764, by rfl⟩ : syracuseStep 265019 = 397529) B397529
theorem B265079 : Blo 175800 265079 := bstep (se 1 (by rfl) ⟨198809, by rfl⟩ : syracuseStep 265079 = 397619) B397619
theorem B265103 : Blo 175800 265103 := bstep (se 1 (by rfl) ⟨198827, by rfl⟩ : syracuseStep 265103 = 397655) B397655
theorem B396179 : Blo 175800 396179 := bstep (se 1 (by rfl) ⟨297134, by rfl⟩ : syracuseStep 396179 = 594269) B594269
theorem B1018777 : Blo 175800 1018777 := bstep (se 2 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 1018777 = 764083) B764083
theorem B265145 : Blo 175800 265145 := bstep (se 2 (by rfl) ⟨99429, by rfl⟩ : syracuseStep 265145 = 198859) B198859
theorem B396233 : Blo 175800 396233 := bstep (se 2 (by rfl) ⟨148587, by rfl⟩ : syracuseStep 396233 = 297175) B297175
theorem B265223 : Blo 175800 265223 := bstep (se 1 (by rfl) ⟨198917, by rfl⟩ : syracuseStep 265223 = 397835) B397835
theorem B199687 : Blo 175800 199687 := bstep (se 1 (by rfl) ⟨149765, by rfl⟩ : syracuseStep 199687 = 299531) B299531
theorem B265259 : Blo 175800 265259 := bstep (se 1 (by rfl) ⟨198944, by rfl⟩ : syracuseStep 265259 = 397889) B397889
theorem B12946493 : Blo 175800 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B265289 : Blo 175800 265289 := bstep (se 2 (by rfl) ⟨99483, by rfl⟩ : syracuseStep 265289 = 198967) B198967
theorem B756823 : Blo 175800 756823 := bstep (se 1 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 756823 = 1135235) B1135235
theorem B265403 : Blo 175800 265403 := bstep (se 1 (by rfl) ⟨199052, by rfl⟩ : syracuseStep 265403 = 398105) B398105
theorem B199867 : Blo 175800 199867 := bstep (se 1 (by rfl) ⟨149900, by rfl⟩ : syracuseStep 199867 = 299801) B299801
theorem B265463 : Blo 175800 265463 := bstep (se 1 (by rfl) ⟨199097, by rfl⟩ : syracuseStep 265463 = 398195) B398195
theorem B298255 : Blo 175800 298255 := bstep (se 1 (by rfl) ⟨223691, by rfl⟩ : syracuseStep 298255 = 447383) B447383
theorem B265487 : Blo 175800 265487 := bstep (se 1 (by rfl) ⟨199115, by rfl⟩ : syracuseStep 265487 = 398231) B398231
theorem B363809 : Blo 175800 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B265529 : Blo 175800 265529 := bstep (se 2 (by rfl) ⟨99573, by rfl⟩ : syracuseStep 265529 = 199147) B199147
theorem B265607 : Blo 175800 265607 := bstep (se 1 (by rfl) ⟨199205, by rfl⟩ : syracuseStep 265607 = 398411) B398411
theorem B265643 : Blo 175800 265643 := bstep (se 1 (by rfl) ⟨199232, by rfl⟩ : syracuseStep 265643 = 398465) B398465
theorem B265673 : Blo 175800 265673 := bstep (se 2 (by rfl) ⟨99627, by rfl⟩ : syracuseStep 265673 = 199255) B199255
theorem B265787 : Blo 175800 265787 := bstep (se 1 (by rfl) ⟨199340, by rfl⟩ : syracuseStep 265787 = 398681) B398681
theorem B265847 : Blo 175800 265847 := bstep (se 1 (by rfl) ⟨199385, by rfl⟩ : syracuseStep 265847 = 398771) B398771
theorem B1347191 : Blo 175800 1347191 := bstep (se 1 (by rfl) ⟨1010393, by rfl⟩ : syracuseStep 1347191 = 2020787) B2020787
theorem B396935 : Blo 175800 396935 := bstep (se 1 (by rfl) ⟨297701, by rfl⟩ : syracuseStep 396935 = 595403) B595403
theorem B265871 : Blo 175800 265871 := bstep (se 1 (by rfl) ⟨199403, by rfl⟩ : syracuseStep 265871 = 398807) B398807
theorem B200335 : Blo 175800 200335 := bstep (se 1 (by rfl) ⟨150251, by rfl⟩ : syracuseStep 200335 = 300503) B300503
theorem B265913 : Blo 175800 265913 := bstep (se 2 (by rfl) ⟨99717, by rfl⟩ : syracuseStep 265913 = 199435) B199435
theorem B265991 : Blo 175800 265991 := bstep (se 1 (by rfl) ⟨199493, by rfl⟩ : syracuseStep 265991 = 398987) B398987
theorem B298795 : Blo 175800 298795 := bstep (se 1 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 298795 = 448193) B448193
theorem B266027 : Blo 175800 266027 := bstep (se 1 (by rfl) ⟨199520, by rfl⟩ : syracuseStep 266027 = 399041) B399041
theorem B397115 : Blo 175800 397115 := bstep (se 1 (by rfl) ⟨297836, by rfl⟩ : syracuseStep 397115 = 595673) B595673
theorem B266057 : Blo 175800 266057 := bstep (se 2 (by rfl) ⟨99771, by rfl⟩ : syracuseStep 266057 = 199543) B199543
theorem B429943 : Blo 175800 429943 := bstep (se 1 (by rfl) ⟨322457, by rfl⟩ : syracuseStep 429943 = 644915) B644915
theorem B397241 : Blo 175800 397241 := bstep (se 2 (by rfl) ⟨148965, by rfl⟩ : syracuseStep 397241 = 297931) B297931
theorem B298937 : Blo 175800 298937 := bstep (se 2 (by rfl) ⟨112101, by rfl⟩ : syracuseStep 298937 = 224203) B224203
theorem B266171 : Blo 175800 266171 := bstep (se 1 (by rfl) ⟨199628, by rfl⟩ : syracuseStep 266171 = 399257) B399257
theorem B266231 : Blo 175800 266231 := bstep (se 1 (by rfl) ⟨199673, by rfl⟩ : syracuseStep 266231 = 399347) B399347
theorem B266255 : Blo 175800 266255 := bstep (se 1 (by rfl) ⟨199691, by rfl⟩ : syracuseStep 266255 = 399383) B399383
theorem B266297 : Blo 175800 266297 := bstep (se 2 (by rfl) ⟨99861, by rfl⟩ : syracuseStep 266297 = 199723) B199723
theorem B6951005 : Blo 175800 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B266375 : Blo 175800 266375 := bstep (se 1 (by rfl) ⟨199781, by rfl⟩ : syracuseStep 266375 = 399563) B399563
theorem B200839 : Blo 175800 200839 := bstep (se 1 (by rfl) ⟨150629, by rfl⟩ : syracuseStep 200839 = 301259) B301259
theorem B266411 : Blo 175800 266411 := bstep (se 1 (by rfl) ⟨199808, by rfl⟩ : syracuseStep 266411 = 399617) B399617
theorem B266441 : Blo 175800 266441 := bstep (se 2 (by rfl) ⟨99915, by rfl⟩ : syracuseStep 266441 = 199831) B199831
theorem B397583 : Blo 175800 397583 := bstep (se 1 (by rfl) ⟨298187, by rfl⟩ : syracuseStep 397583 = 596375) B596375
theorem B397601 : Blo 175800 397601 := bstep (se 2 (by rfl) ⟨149100, by rfl⟩ : syracuseStep 397601 = 298201) B298201
theorem B266555 : Blo 175800 266555 := bstep (se 1 (by rfl) ⟨199916, by rfl⟩ : syracuseStep 266555 = 399833) B399833
theorem B201019 : Blo 175800 201019 := bstep (se 1 (by rfl) ⟨150764, by rfl⟩ : syracuseStep 201019 = 301529) B301529
theorem B266615 : Blo 175800 266615 := bstep (se 1 (by rfl) ⟨199961, by rfl⟩ : syracuseStep 266615 = 399923) B399923
theorem B266639 : Blo 175800 266639 := bstep (se 1 (by rfl) ⟨199979, by rfl⟩ : syracuseStep 266639 = 399959) B399959
theorem B594323 : Blo 175800 594323 := bstep (se 1 (by rfl) ⟨445742, by rfl⟩ : syracuseStep 594323 = 891485) B891485
theorem B266681 : Blo 175800 266681 := bstep (se 2 (by rfl) ⟨100005, by rfl⟩ : syracuseStep 266681 = 200011) B200011
theorem B266759 : Blo 175800 266759 := bstep (se 1 (by rfl) ⟨200069, by rfl⟩ : syracuseStep 266759 = 400139) B400139
theorem B266795 : Blo 175800 266795 := bstep (se 1 (by rfl) ⟨200096, by rfl⟩ : syracuseStep 266795 = 400193) B400193
theorem B1348163 : Blo 175800 1348163 := bstep (se 1 (by rfl) ⟨1011122, by rfl⟩ : syracuseStep 1348163 = 2022245) B2022245
theorem B266825 : Blo 175800 266825 := bstep (se 2 (by rfl) ⟨100059, by rfl⟩ : syracuseStep 266825 = 200119) B200119
theorem B397943 : Blo 175800 397943 := bstep (se 1 (by rfl) ⟨298457, by rfl⟩ : syracuseStep 397943 = 596915) B596915
theorem B299639 : Blo 175800 299639 := bstep (se 1 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 299639 = 449459) B449459
theorem B266939 : Blo 175800 266939 := bstep (se 1 (by rfl) ⟨200204, by rfl⟩ : syracuseStep 266939 = 400409) B400409
theorem B266999 : Blo 175800 266999 := bstep (se 1 (by rfl) ⟨200249, by rfl⟩ : syracuseStep 266999 = 400499) B400499
theorem B267023 : Blo 175800 267023 := bstep (se 1 (by rfl) ⟨200267, by rfl⟩ : syracuseStep 267023 = 400535) B400535
theorem B201487 : Blo 175800 201487 := bstep (se 1 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 201487 = 302231) B302231
theorem B398123 : Blo 175800 398123 := bstep (se 1 (by rfl) ⟨298592, by rfl⟩ : syracuseStep 398123 = 597185) B597185
theorem B267065 : Blo 175800 267065 := bstep (se 2 (by rfl) ⟨100149, by rfl⟩ : syracuseStep 267065 = 200299) B200299
theorem B1020761 : Blo 175800 1020761 := bstep (se 2 (by rfl) ⟨382785, by rfl⟩ : syracuseStep 1020761 = 765571) B765571
theorem B693107 : Blo 175800 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B267143 : Blo 175800 267143 := bstep (se 1 (by rfl) ⟨200357, by rfl⟩ : syracuseStep 267143 = 400715) B400715
theorem B267179 : Blo 175800 267179 := bstep (se 1 (by rfl) ⟨200384, by rfl⟩ : syracuseStep 267179 = 400769) B400769
theorem B267209 : Blo 175800 267209 := bstep (se 2 (by rfl) ⟨100203, by rfl⟩ : syracuseStep 267209 = 200407) B200407
theorem B955435 : Blo 175800 955435 := bstep (se 1 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 955435 = 1433153) B1433153
theorem B300091 : Blo 175800 300091 := bstep (se 1 (by rfl) ⟨225068, by rfl⟩ : syracuseStep 300091 = 450137) B450137
theorem B267323 : Blo 175800 267323 := bstep (se 1 (by rfl) ⟨200492, by rfl⟩ : syracuseStep 267323 = 400985) B400985
theorem B267383 : Blo 175800 267383 := bstep (se 1 (by rfl) ⟨200537, by rfl⟩ : syracuseStep 267383 = 401075) B401075
theorem B267407 : Blo 175800 267407 := bstep (se 1 (by rfl) ⟨200555, by rfl⟩ : syracuseStep 267407 = 401111) B401111
theorem B398483 : Blo 175800 398483 := bstep (se 1 (by rfl) ⟨298862, by rfl⟩ : syracuseStep 398483 = 597725) B597725
theorem B267449 : Blo 175800 267449 := bstep (se 2 (by rfl) ⟨100293, by rfl⟩ : syracuseStep 267449 = 200587) B200587
theorem B398537 : Blo 175800 398537 := bstep (se 2 (by rfl) ⟨149451, by rfl⟩ : syracuseStep 398537 = 298903) B298903
theorem B300233 : Blo 175800 300233 := bstep (se 2 (by rfl) ⟨112587, by rfl⟩ : syracuseStep 300233 = 225175) B225175
theorem B267527 : Blo 175800 267527 := bstep (se 1 (by rfl) ⟨200645, by rfl⟩ : syracuseStep 267527 = 401291) B401291
theorem B201991 : Blo 175800 201991 := bstep (se 1 (by rfl) ⟨151493, by rfl⟩ : syracuseStep 201991 = 302987) B302987
theorem B267563 : Blo 175800 267563 := bstep (se 1 (by rfl) ⟨200672, by rfl⟩ : syracuseStep 267563 = 401345) B401345
theorem B267593 : Blo 175800 267593 := bstep (se 2 (by rfl) ⟨100347, by rfl⟩ : syracuseStep 267593 = 200695) B200695
theorem B7968131 : Blo 175800 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B267707 : Blo 175800 267707 := bstep (se 1 (by rfl) ⟨200780, by rfl⟩ : syracuseStep 267707 = 401561) B401561
theorem B202171 : Blo 175800 202171 := bstep (se 1 (by rfl) ⟨151628, by rfl⟩ : syracuseStep 202171 = 303257) B303257
theorem B267767 : Blo 175800 267767 := bstep (se 1 (by rfl) ⟨200825, by rfl⟩ : syracuseStep 267767 = 401651) B401651
theorem B267791 : Blo 175800 267791 := bstep (se 1 (by rfl) ⟨200843, by rfl⟩ : syracuseStep 267791 = 401687) B401687
theorem B267833 : Blo 175800 267833 := bstep (se 2 (by rfl) ⟨100437, by rfl⟩ : syracuseStep 267833 = 200875) B200875
theorem B267911 : Blo 175800 267911 := bstep (se 1 (by rfl) ⟨200933, by rfl⟩ : syracuseStep 267911 = 401867) B401867
theorem B267947 : Blo 175800 267947 := bstep (se 1 (by rfl) ⟨200960, by rfl⟩ : syracuseStep 267947 = 401921) B401921
theorem B4363955 : Blo 175800 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B267977 : Blo 175800 267977 := bstep (se 2 (by rfl) ⟨100491, by rfl⟩ : syracuseStep 267977 = 200983) B200983
theorem B595727 : Blo 175800 595727 := bstep (se 1 (by rfl) ⟨446795, by rfl⟩ : syracuseStep 595727 = 893591) B893591
theorem B890675 : Blo 175800 890675 := bstep (se 1 (by rfl) ⟨668006, by rfl⟩ : syracuseStep 890675 = 1336013) B1336013
theorem B268091 : Blo 175800 268091 := bstep (se 1 (by rfl) ⟨201068, by rfl⟩ : syracuseStep 268091 = 402137) B402137
theorem B268151 : Blo 175800 268151 := bstep (se 1 (by rfl) ⟨201113, by rfl⟩ : syracuseStep 268151 = 402227) B402227
theorem B399239 : Blo 175800 399239 := bstep (se 1 (by rfl) ⟨299429, by rfl⟩ : syracuseStep 399239 = 598859) B598859
theorem B300935 : Blo 175800 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B268175 : Blo 175800 268175 := bstep (se 1 (by rfl) ⟨201131, by rfl⟩ : syracuseStep 268175 = 402263) B402263
theorem B268217 : Blo 175800 268217 := bstep (se 2 (by rfl) ⟨100581, by rfl⟩ : syracuseStep 268217 = 201163) B201163
theorem B268295 : Blo 175800 268295 := bstep (se 1 (by rfl) ⟨201221, by rfl⟩ : syracuseStep 268295 = 402443) B402443
theorem B595997 : Blo 175800 595997 := bstep (se 3 (by rfl) ⟨111749, by rfl⟩ : syracuseStep 595997 = 223499) B223499
theorem B268331 : Blo 175800 268331 := bstep (se 1 (by rfl) ⟨201248, by rfl⟩ : syracuseStep 268331 = 402497) B402497
theorem B399419 : Blo 175800 399419 := bstep (se 1 (by rfl) ⟨299564, by rfl⟩ : syracuseStep 399419 = 599129) B599129
theorem B268361 : Blo 175800 268361 := bstep (se 2 (by rfl) ⟨100635, by rfl⟩ : syracuseStep 268361 = 201271) B201271
theorem B890999 : Blo 175800 890999 := bstep (se 1 (by rfl) ⟨668249, by rfl⟩ : syracuseStep 890999 = 1336499) B1336499
theorem B399545 : Blo 175800 399545 := bstep (se 2 (by rfl) ⟨149829, by rfl⟩ : syracuseStep 399545 = 299659) B299659
theorem B268475 : Blo 175800 268475 := bstep (se 1 (by rfl) ⟨201356, by rfl⟩ : syracuseStep 268475 = 402713) B402713
theorem B268535 : Blo 175800 268535 := bstep (se 1 (by rfl) ⟨201401, by rfl⟩ : syracuseStep 268535 = 402803) B402803
theorem B268559 : Blo 175800 268559 := bstep (se 1 (by rfl) ⟨201419, by rfl⟩ : syracuseStep 268559 = 402839) B402839
theorem B268601 : Blo 175800 268601 := bstep (se 2 (by rfl) ⟨100725, by rfl⟩ : syracuseStep 268601 = 201451) B201451
theorem B268679 : Blo 175800 268679 := bstep (se 1 (by rfl) ⟨201509, by rfl⟩ : syracuseStep 268679 = 403019) B403019
theorem B14522773 : Blo 175800 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B268715 : Blo 175800 268715 := bstep (se 1 (by rfl) ⟨201536, by rfl⟩ : syracuseStep 268715 = 403073) B403073
theorem B268745 : Blo 175800 268745 := bstep (se 2 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 268745 = 201559) B201559
theorem B956881 : Blo 175800 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B563723 : Blo 175800 563723 := bstep (se 1 (by rfl) ⟨422792, by rfl⟩ : syracuseStep 563723 = 845585) B845585
theorem B399887 : Blo 175800 399887 := bstep (se 1 (by rfl) ⟨299915, by rfl⟩ : syracuseStep 399887 = 599831) B599831
theorem B301583 : Blo 175800 301583 := bstep (se 1 (by rfl) ⟨226187, by rfl⟩ : syracuseStep 301583 = 452375) B452375
theorem B399905 : Blo 175800 399905 := bstep (se 2 (by rfl) ⟨149964, by rfl⟩ : syracuseStep 399905 = 299929) B299929
theorem B268859 : Blo 175800 268859 := bstep (se 1 (by rfl) ⟨201644, by rfl⟩ : syracuseStep 268859 = 403289) B403289
theorem B268919 : Blo 175800 268919 := bstep (se 1 (by rfl) ⟨201689, by rfl⟩ : syracuseStep 268919 = 403379) B403379
theorem B268943 : Blo 175800 268943 := bstep (se 1 (by rfl) ⟨201707, by rfl⟩ : syracuseStep 268943 = 403415) B403415
theorem B268985 : Blo 175800 268985 := bstep (se 2 (by rfl) ⟨100869, by rfl⟩ : syracuseStep 268985 = 201739) B201739
theorem B269063 : Blo 175800 269063 := bstep (se 1 (by rfl) ⟨201797, by rfl⟩ : syracuseStep 269063 = 403595) B403595
theorem B269099 : Blo 175800 269099 := bstep (se 1 (by rfl) ⟨201824, by rfl⟩ : syracuseStep 269099 = 403649) B403649
theorem B1088315 : Blo 175800 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B269129 : Blo 175800 269129 := bstep (se 2 (by rfl) ⟨100923, by rfl⟩ : syracuseStep 269129 = 201847) B201847
theorem B400247 : Blo 175800 400247 := bstep (se 1 (by rfl) ⟨300185, by rfl⟩ : syracuseStep 400247 = 600371) B600371
theorem B269243 : Blo 175800 269243 := bstep (se 1 (by rfl) ⟨201932, by rfl⟩ : syracuseStep 269243 = 403865) B403865
theorem B334793 : Blo 175800 334793 := bstep (se 2 (by rfl) ⟨125547, by rfl⟩ : syracuseStep 334793 = 251095) B251095
theorem B269257 : Blo 175800 269257 := bstep (se 2 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 269257 = 201943) B201943
theorem B269303 : Blo 175800 269303 := bstep (se 1 (by rfl) ⟨201977, by rfl⟩ : syracuseStep 269303 = 403955) B403955
theorem B269327 : Blo 175800 269327 := bstep (se 1 (by rfl) ⟨201995, by rfl⟩ : syracuseStep 269327 = 403991) B403991
theorem B400427 : Blo 175800 400427 := bstep (se 1 (by rfl) ⟨300320, by rfl⟩ : syracuseStep 400427 = 600641) B600641
theorem B302123 : Blo 175800 302123 := bstep (se 1 (by rfl) ⟨226592, by rfl⟩ : syracuseStep 302123 = 453185) B453185
theorem B269369 : Blo 175800 269369 := bstep (se 2 (by rfl) ⟨101013, by rfl⟩ : syracuseStep 269369 = 202027) B202027
theorem B1219645 : Blo 175800 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B891971 : Blo 175800 891971 := bstep (se 1 (by rfl) ⟨668978, by rfl⟩ : syracuseStep 891971 = 1337957) B1337957
theorem B269447 : Blo 175800 269447 := bstep (se 1 (by rfl) ⟨202085, by rfl⟩ : syracuseStep 269447 = 404171) B404171
theorem B269483 : Blo 175800 269483 := bstep (se 1 (by rfl) ⟨202112, by rfl⟩ : syracuseStep 269483 = 404225) B404225
theorem B269513 : Blo 175800 269513 := bstep (se 2 (by rfl) ⟨101067, by rfl⟩ : syracuseStep 269513 = 202135) B202135
theorem B269627 : Blo 175800 269627 := bstep (se 1 (by rfl) ⟨202220, by rfl⟩ : syracuseStep 269627 = 404441) B404441
theorem B859481 : Blo 175800 859481 := bstep (se 2 (by rfl) ⟨322305, by rfl⟩ : syracuseStep 859481 = 644611) B644611
theorem B269687 : Blo 175800 269687 := bstep (se 1 (by rfl) ⟨202265, by rfl⟩ : syracuseStep 269687 = 404531) B404531
theorem B892295 : Blo 175800 892295 := bstep (se 1 (by rfl) ⟨669221, by rfl⟩ : syracuseStep 892295 = 1338443) B1338443
theorem B400787 : Blo 175800 400787 := bstep (se 1 (by rfl) ⟨300590, by rfl⟩ : syracuseStep 400787 = 601181) B601181
theorem B597401 : Blo 175800 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B302521 : Blo 175800 302521 := bstep (se 2 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 302521 = 226891) B226891
theorem B400841 : Blo 175800 400841 := bstep (se 2 (by rfl) ⟨150315, by rfl⟩ : syracuseStep 400841 = 300631) B300631
theorem B5283427 : Blo 175800 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B335659 : Blo 175800 335659 := bstep (se 1 (by rfl) ⟨251744, by rfl⟩ : syracuseStep 335659 = 503489) B503489
theorem B335735 : Blo 175800 335735 := bstep (se 1 (by rfl) ⟨251801, by rfl⟩ : syracuseStep 335735 = 503603) B503603
theorem B860057 : Blo 175800 860057 := bstep (se 2 (by rfl) ⟨322521, by rfl⟩ : syracuseStep 860057 = 645043) B645043
theorem B598103 : Blo 175800 598103 := bstep (se 1 (by rfl) ⟨448577, by rfl⟩ : syracuseStep 598103 = 897155) B897155
theorem B893015 : Blo 175800 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B303223 : Blo 175800 303223 := bstep (se 1 (by rfl) ⟨227417, by rfl⟩ : syracuseStep 303223 = 454835) B454835
theorem B401543 : Blo 175800 401543 := bstep (se 1 (by rfl) ⟨301157, by rfl⟩ : syracuseStep 401543 = 602315) B602315
theorem B401723 : Blo 175800 401723 := bstep (se 1 (by rfl) ⟨301292, by rfl⟩ : syracuseStep 401723 = 602585) B602585
theorem B2171281 : Blo 175800 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B303545 : Blo 175800 303545 := bstep (se 2 (by rfl) ⟨113829, by rfl⟩ : syracuseStep 303545 = 227659) B227659
theorem B401849 : Blo 175800 401849 := bstep (se 2 (by rfl) ⟨150693, by rfl⟩ : syracuseStep 401849 = 301387) B301387
theorem B598589 : Blo 175800 598589 := bstep (se 3 (by rfl) ⟨112235, by rfl⟩ : syracuseStep 598589 = 224471) B224471
theorem B402191 : Blo 175800 402191 := bstep (se 1 (by rfl) ⟨301643, by rfl⟩ : syracuseStep 402191 = 603287) B603287
theorem B402209 : Blo 175800 402209 := bstep (se 2 (by rfl) ⟨150828, by rfl⟩ : syracuseStep 402209 = 301657) B301657
theorem B1352537 : Blo 175800 1352537 := bstep (se 2 (by rfl) ⟨507201, by rfl⟩ : syracuseStep 1352537 = 1014403) B1014403
theorem B6628439 : Blo 175800 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B402551 : Blo 175800 402551 := bstep (se 1 (by rfl) ⟨301913, by rfl⟩ : syracuseStep 402551 = 603827) B603827
theorem B402731 : Blo 175800 402731 := bstep (se 1 (by rfl) ⟨302048, by rfl⟩ : syracuseStep 402731 = 604097) B604097
theorem B763195 : Blo 175800 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B1222033 : Blo 175800 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B403091 : Blo 175800 403091 := bstep (se 1 (by rfl) ⟨302318, by rfl⟩ : syracuseStep 403091 = 604637) B604637
theorem B304825 : Blo 175800 304825 := bstep (se 2 (by rfl) ⟨114309, by rfl⟩ : syracuseStep 304825 = 228619) B228619
theorem B403145 : Blo 175800 403145 := bstep (se 2 (by rfl) ⟨151179, by rfl⟩ : syracuseStep 403145 = 302359) B302359
theorem B337679 : Blo 175800 337679 := bstep (se 1 (by rfl) ⟨253259, by rfl⟩ : syracuseStep 337679 = 506519) B506519
theorem B1353509 : Blo 175800 1353509 := bstep (se 4 (by rfl) ⟨126891, by rfl⟩ : syracuseStep 1353509 = 253783) B253783
theorem B1025939 : Blo 175800 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B501689 : Blo 175800 501689 := bstep (se 2 (by rfl) ⟨188133, by rfl⟩ : syracuseStep 501689 = 376267) B376267
theorem B599993 : Blo 175800 599993 := bstep (se 2 (by rfl) ⟨224997, by rfl⟩ : syracuseStep 599993 = 449995) B449995
theorem B502031 : Blo 175800 502031 := bstep (se 1 (by rfl) ⟨376523, by rfl⟩ : syracuseStep 502031 = 753047) B753047
theorem B1747331 : Blo 175800 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B403847 : Blo 175800 403847 := bstep (se 1 (by rfl) ⟨302885, by rfl⟩ : syracuseStep 403847 = 605771) B605771
theorem B600587 : Blo 175800 600587 := bstep (se 1 (by rfl) ⟨450440, by rfl⟩ : syracuseStep 600587 = 900881) B900881
theorem B404027 : Blo 175800 404027 := bstep (se 1 (by rfl) ⟨303020, by rfl⟩ : syracuseStep 404027 = 606041) B606041
theorem B600695 : Blo 175800 600695 := bstep (se 1 (by rfl) ⟨450521, by rfl⟩ : syracuseStep 600695 = 901043) B901043
theorem B404153 : Blo 175800 404153 := bstep (se 2 (by rfl) ⟨151557, by rfl⟩ : syracuseStep 404153 = 303115) B303115
theorem B895859 : Blo 175800 895859 := bstep (se 1 (by rfl) ⟨671894, by rfl⟩ : syracuseStep 895859 = 1343789) B1343789
theorem B404495 : Blo 175800 404495 := bstep (se 1 (by rfl) ⟨303371, by rfl⟩ : syracuseStep 404495 = 606743) B606743
theorem B404513 : Blo 175800 404513 := bstep (se 2 (by rfl) ⟨151692, by rfl⟩ : syracuseStep 404513 = 303385) B303385
theorem B502919 : Blo 175800 502919 := bstep (se 1 (by rfl) ⟨377189, by rfl⟩ : syracuseStep 502919 = 754379) B754379
theorem B601289 : Blo 175800 601289 := bstep (se 2 (by rfl) ⟨225483, by rfl⟩ : syracuseStep 601289 = 450967) B450967
theorem B503101 : Blo 175800 503101 := bstep (se 3 (by rfl) ⟨94331, by rfl⟩ : syracuseStep 503101 = 188663) B188663
theorem B896345 : Blo 175800 896345 := bstep (se 2 (by rfl) ⟨336129, by rfl⟩ : syracuseStep 896345 = 672259) B672259
theorem B339319 : Blo 175800 339319 := bstep (se 1 (by rfl) ⟨254489, by rfl⟩ : syracuseStep 339319 = 508979) B508979
theorem B863747 : Blo 175800 863747 := bstep (se 1 (by rfl) ⟨647810, by rfl⟩ : syracuseStep 863747 = 1295621) B1295621
theorem B503329 : Blo 175800 503329 := bstep (se 2 (by rfl) ⟨188748, by rfl⟩ : syracuseStep 503329 = 377497) B377497
theorem B175803 : Blo 175800 175803 := bstep (se 1 (by rfl) ⟨131852, by rfl⟩ : syracuseStep 175803 = 263705) B263705
theorem B175879 : Blo 175800 175879 := bstep (se 1 (by rfl) ⟨131909, by rfl⟩ : syracuseStep 175879 = 263819) B263819
theorem B175887 : Blo 175800 175887 := bstep (se 1 (by rfl) ⟨131915, by rfl⟩ : syracuseStep 175887 = 263831) B263831
theorem B175931 : Blo 175800 175931 := bstep (se 1 (by rfl) ⟨131948, by rfl⟩ : syracuseStep 175931 = 263897) B263897
theorem B503671 : Blo 175800 503671 := bstep (se 1 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 503671 = 755507) B755507
theorem B176007 : Blo 175800 176007 := bstep (se 1 (by rfl) ⟨132005, by rfl⟩ : syracuseStep 176007 = 264011) B264011
theorem B601991 : Blo 175800 601991 := bstep (se 1 (by rfl) ⟨451493, by rfl⟩ : syracuseStep 601991 = 902987) B902987
theorem B176015 : Blo 175800 176015 := bstep (se 1 (by rfl) ⟨132011, by rfl⟩ : syracuseStep 176015 = 264023) B264023
theorem B176059 : Blo 175800 176059 := bstep (se 1 (by rfl) ⟨132044, by rfl⟩ : syracuseStep 176059 = 264089) B264089
theorem B176135 : Blo 175800 176135 := bstep (se 1 (by rfl) ⟨132101, by rfl⟩ : syracuseStep 176135 = 264203) B264203
theorem B176143 : Blo 175800 176143 := bstep (se 1 (by rfl) ⟨132107, by rfl⟩ : syracuseStep 176143 = 264215) B264215
theorem B176187 : Blo 175800 176187 := bstep (se 1 (by rfl) ⟨132140, by rfl⟩ : syracuseStep 176187 = 264281) B264281
theorem B176263 : Blo 175800 176263 := bstep (se 1 (by rfl) ⟨132197, by rfl⟩ : syracuseStep 176263 = 264395) B264395
theorem B176271 : Blo 175800 176271 := bstep (se 1 (by rfl) ⟨132203, by rfl⟩ : syracuseStep 176271 = 264407) B264407
theorem B176315 : Blo 175800 176315 := bstep (se 1 (by rfl) ⟨132236, by rfl⟩ : syracuseStep 176315 = 264473) B264473
theorem B667885 : Blo 175800 667885 := bstep (se 3 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 667885 = 250457) B250457
theorem B602369 : Blo 175800 602369 := bstep (se 2 (by rfl) ⟨225888, by rfl⟩ : syracuseStep 602369 = 451777) B451777
theorem B176391 : Blo 175800 176391 := bstep (se 1 (by rfl) ⟨132293, by rfl⟩ : syracuseStep 176391 = 264587) B264587
theorem B176399 : Blo 175800 176399 := bstep (se 1 (by rfl) ⟨132299, by rfl⟩ : syracuseStep 176399 = 264599) B264599
theorem B176443 : Blo 175800 176443 := bstep (se 1 (by rfl) ⟨132332, by rfl⟩ : syracuseStep 176443 = 264665) B264665
theorem B176519 : Blo 175800 176519 := bstep (se 1 (by rfl) ⟨132389, by rfl⟩ : syracuseStep 176519 = 264779) B264779
theorem B176527 : Blo 175800 176527 := bstep (se 1 (by rfl) ⟨132395, by rfl⟩ : syracuseStep 176527 = 264791) B264791
theorem B340409 : Blo 175800 340409 := bstep (se 2 (by rfl) ⟨127653, by rfl⟩ : syracuseStep 340409 = 255307) B255307
theorem B176571 : Blo 175800 176571 := bstep (se 1 (by rfl) ⟨132428, by rfl⟩ : syracuseStep 176571 = 264857) B264857
theorem B176647 : Blo 175800 176647 := bstep (se 1 (by rfl) ⟨132485, by rfl⟩ : syracuseStep 176647 = 264971) B264971
theorem B176655 : Blo 175800 176655 := bstep (se 1 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 176655 = 264983) B264983
theorem B668189 : Blo 175800 668189 := bstep (se 3 (by rfl) ⟨125285, by rfl⟩ : syracuseStep 668189 = 250571) B250571
theorem B176699 : Blo 175800 176699 := bstep (se 1 (by rfl) ⟨132524, by rfl⟩ : syracuseStep 176699 = 265049) B265049
theorem B176775 : Blo 175800 176775 := bstep (se 1 (by rfl) ⟨132581, by rfl⟩ : syracuseStep 176775 = 265163) B265163
theorem B176783 : Blo 175800 176783 := bstep (se 1 (by rfl) ⟨132587, by rfl⟩ : syracuseStep 176783 = 265175) B265175
theorem B176827 : Blo 175800 176827 := bstep (se 1 (by rfl) ⟨132620, by rfl⟩ : syracuseStep 176827 = 265241) B265241
theorem B176903 : Blo 175800 176903 := bstep (se 1 (by rfl) ⟨132677, by rfl⟩ : syracuseStep 176903 = 265355) B265355
theorem B176911 : Blo 175800 176911 := bstep (se 1 (by rfl) ⟨132683, by rfl⟩ : syracuseStep 176911 = 265367) B265367
theorem B504605 : Blo 175800 504605 := bstep (se 3 (by rfl) ⟨94613, by rfl⟩ : syracuseStep 504605 = 189227) B189227
theorem B176955 : Blo 175800 176955 := bstep (se 1 (by rfl) ⟨132716, by rfl⟩ : syracuseStep 176955 = 265433) B265433
theorem B177031 : Blo 175800 177031 := bstep (se 1 (by rfl) ⟨132773, by rfl⟩ : syracuseStep 177031 = 265547) B265547
theorem B177039 : Blo 175800 177039 := bstep (se 1 (by rfl) ⟨132779, by rfl⟩ : syracuseStep 177039 = 265559) B265559
theorem B177083 : Blo 175800 177083 := bstep (se 1 (by rfl) ⟨132812, by rfl⟩ : syracuseStep 177083 = 265625) B265625
theorem B177159 : Blo 175800 177159 := bstep (se 1 (by rfl) ⟨132869, by rfl⟩ : syracuseStep 177159 = 265739) B265739
theorem B177167 : Blo 175800 177167 := bstep (se 1 (by rfl) ⟨132875, by rfl⟩ : syracuseStep 177167 = 265751) B265751
theorem B570397 : Blo 175800 570397 := bstep (se 3 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 570397 = 213899) B213899
theorem B603179 : Blo 175800 603179 := bstep (se 1 (by rfl) ⟨452384, by rfl⟩ : syracuseStep 603179 = 904769) B904769
theorem B177211 : Blo 175800 177211 := bstep (se 1 (by rfl) ⟨132908, by rfl⟩ : syracuseStep 177211 = 265817) B265817
theorem B504947 : Blo 175800 504947 := bstep (se 1 (by rfl) ⟨378710, by rfl⟩ : syracuseStep 504947 = 757421) B757421
theorem B341111 : Blo 175800 341111 := bstep (se 1 (by rfl) ⟨255833, by rfl⟩ : syracuseStep 341111 = 511667) B511667
theorem B177287 : Blo 175800 177287 := bstep (se 1 (by rfl) ⟨132965, by rfl⟩ : syracuseStep 177287 = 265931) B265931
theorem B177295 : Blo 175800 177295 := bstep (se 1 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 177295 = 265943) B265943
theorem B177339 : Blo 175800 177339 := bstep (se 1 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 177339 = 266009) B266009
theorem B177415 : Blo 175800 177415 := bstep (se 1 (by rfl) ⟨133061, by rfl⟩ : syracuseStep 177415 = 266123) B266123
theorem B177423 : Blo 175800 177423 := bstep (se 1 (by rfl) ⟨133067, by rfl⟩ : syracuseStep 177423 = 266135) B266135
theorem B341263 : Blo 175800 341263 := bstep (se 1 (by rfl) ⟨255947, by rfl⟩ : syracuseStep 341263 = 511895) B511895
theorem B177467 : Blo 175800 177467 := bstep (se 1 (by rfl) ⟨133100, by rfl⟩ : syracuseStep 177467 = 266201) B266201
theorem B177543 : Blo 175800 177543 := bstep (se 1 (by rfl) ⟨133157, by rfl⟩ : syracuseStep 177543 = 266315) B266315
theorem B177551 : Blo 175800 177551 := bstep (se 1 (by rfl) ⟨133163, by rfl⟩ : syracuseStep 177551 = 266327) B266327
theorem B898451 : Blo 175800 898451 := bstep (se 1 (by rfl) ⟨673838, by rfl⟩ : syracuseStep 898451 = 1347677) B1347677
theorem B177595 : Blo 175800 177595 := bstep (se 1 (by rfl) ⟨133196, by rfl⟩ : syracuseStep 177595 = 266393) B266393
theorem B177671 : Blo 175800 177671 := bstep (se 1 (by rfl) ⟨133253, by rfl⟩ : syracuseStep 177671 = 266507) B266507
theorem B177679 : Blo 175800 177679 := bstep (se 1 (by rfl) ⟨133259, by rfl⟩ : syracuseStep 177679 = 266519) B266519
theorem B505403 : Blo 175800 505403 := bstep (se 1 (by rfl) ⟨379052, by rfl⟩ : syracuseStep 505403 = 758105) B758105
theorem B177723 : Blo 175800 177723 := bstep (se 1 (by rfl) ⟨133292, by rfl⟩ : syracuseStep 177723 = 266585) B266585
theorem B177799 : Blo 175800 177799 := bstep (se 1 (by rfl) ⟨133349, by rfl⟩ : syracuseStep 177799 = 266699) B266699
theorem B177807 : Blo 175800 177807 := bstep (se 1 (by rfl) ⟨133355, by rfl⟩ : syracuseStep 177807 = 266711) B266711
theorem B177851 : Blo 175800 177851 := bstep (se 1 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 177851 = 266777) B266777
theorem B3421925 : Blo 175800 3421925 := bstep (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) B641611
theorem B177927 : Blo 175800 177927 := bstep (se 1 (by rfl) ⟨133445, by rfl⟩ : syracuseStep 177927 = 266891) B266891
theorem B177935 : Blo 175800 177935 := bstep (se 1 (by rfl) ⟨133451, by rfl⟩ : syracuseStep 177935 = 266903) B266903
theorem B177979 : Blo 175800 177979 := bstep (se 1 (by rfl) ⟨133484, by rfl⟩ : syracuseStep 177979 = 266969) B266969
theorem B178055 : Blo 175800 178055 := bstep (se 1 (by rfl) ⟨133541, by rfl⟩ : syracuseStep 178055 = 267083) B267083
theorem B178063 : Blo 175800 178063 := bstep (se 1 (by rfl) ⟨133547, by rfl⟩ : syracuseStep 178063 = 267095) B267095
theorem B178107 : Blo 175800 178107 := bstep (se 1 (by rfl) ⟨133580, by rfl⟩ : syracuseStep 178107 = 267161) B267161
theorem B178183 : Blo 175800 178183 := bstep (se 1 (by rfl) ⟨133637, by rfl⟩ : syracuseStep 178183 = 267275) B267275
theorem B178191 : Blo 175800 178191 := bstep (se 1 (by rfl) ⟨133643, by rfl⟩ : syracuseStep 178191 = 267287) B267287
theorem B178235 : Blo 175800 178235 := bstep (se 1 (by rfl) ⟨133676, by rfl⟩ : syracuseStep 178235 = 267353) B267353
theorem B669815 : Blo 175800 669815 := bstep (se 1 (by rfl) ⟨502361, by rfl⟩ : syracuseStep 669815 = 1004723) B1004723
theorem B1554565 : Blo 175800 1554565 := bstep (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) B291481
theorem B178311 : Blo 175800 178311 := bstep (se 1 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 178311 = 267467) B267467
theorem B178319 : Blo 175800 178319 := bstep (se 1 (by rfl) ⟨133739, by rfl⟩ : syracuseStep 178319 = 267479) B267479
theorem B178363 : Blo 175800 178363 := bstep (se 1 (by rfl) ⟨133772, by rfl⟩ : syracuseStep 178363 = 267545) B267545
theorem B178439 : Blo 175800 178439 := bstep (se 1 (by rfl) ⟨133829, by rfl⟩ : syracuseStep 178439 = 267659) B267659
theorem B178447 : Blo 175800 178447 := bstep (se 1 (by rfl) ⟨133835, by rfl⟩ : syracuseStep 178447 = 267671) B267671
theorem B178491 : Blo 175800 178491 := bstep (se 1 (by rfl) ⟨133868, by rfl⟩ : syracuseStep 178491 = 267737) B267737
theorem B604475 : Blo 175800 604475 := bstep (se 1 (by rfl) ⟨453356, by rfl⟩ : syracuseStep 604475 = 906713) B906713
theorem B178567 : Blo 175800 178567 := bstep (se 1 (by rfl) ⟨133925, by rfl⟩ : syracuseStep 178567 = 267851) B267851
theorem B178575 : Blo 175800 178575 := bstep (se 1 (by rfl) ⟨133931, by rfl⟩ : syracuseStep 178575 = 267863) B267863
theorem B178619 : Blo 175800 178619 := bstep (se 1 (by rfl) ⟨133964, by rfl⟩ : syracuseStep 178619 = 267929) B267929
theorem B2144717 : Blo 175800 2144717 := bstep (se 3 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 2144717 = 804269) B804269
theorem B178695 : Blo 175800 178695 := bstep (se 1 (by rfl) ⟨134021, by rfl⟩ : syracuseStep 178695 = 268043) B268043
theorem B178703 : Blo 175800 178703 := bstep (se 1 (by rfl) ⟨134027, by rfl⟩ : syracuseStep 178703 = 268055) B268055
theorem B178747 : Blo 175800 178747 := bstep (se 1 (by rfl) ⟨134060, by rfl⟩ : syracuseStep 178747 = 268121) B268121
theorem B178823 : Blo 175800 178823 := bstep (se 1 (by rfl) ⟨134117, by rfl⟩ : syracuseStep 178823 = 268235) B268235
theorem B178831 : Blo 175800 178831 := bstep (se 1 (by rfl) ⟨134123, by rfl⟩ : syracuseStep 178831 = 268247) B268247
theorem B178875 : Blo 175800 178875 := bstep (se 1 (by rfl) ⟨134156, by rfl⟩ : syracuseStep 178875 = 268313) B268313
theorem B178951 : Blo 175800 178951 := bstep (se 1 (by rfl) ⟨134213, by rfl⟩ : syracuseStep 178951 = 268427) B268427
theorem B178959 : Blo 175800 178959 := bstep (se 1 (by rfl) ⟨134219, by rfl⟩ : syracuseStep 178959 = 268439) B268439
theorem B604961 : Blo 175800 604961 := bstep (se 2 (by rfl) ⟨226860, by rfl⟩ : syracuseStep 604961 = 453721) B453721
theorem B179003 : Blo 175800 179003 := bstep (se 1 (by rfl) ⟨134252, by rfl⟩ : syracuseStep 179003 = 268505) B268505
theorem B179079 : Blo 175800 179079 := bstep (se 1 (by rfl) ⟨134309, by rfl⟩ : syracuseStep 179079 = 268619) B268619
theorem B179087 : Blo 175800 179087 := bstep (se 1 (by rfl) ⟨134315, by rfl⟩ : syracuseStep 179087 = 268631) B268631
theorem B179131 : Blo 175800 179131 := bstep (se 1 (by rfl) ⟨134348, by rfl⟩ : syracuseStep 179131 = 268697) B268697
theorem B179207 : Blo 175800 179207 := bstep (se 1 (by rfl) ⟨134405, by rfl⟩ : syracuseStep 179207 = 268811) B268811
theorem B179215 : Blo 175800 179215 := bstep (se 1 (by rfl) ⟨134411, by rfl⟩ : syracuseStep 179215 = 268823) B268823
theorem B179259 : Blo 175800 179259 := bstep (se 1 (by rfl) ⟨134444, by rfl⟩ : syracuseStep 179259 = 268889) B268889
theorem B670787 : Blo 175800 670787 := bstep (se 1 (by rfl) ⟨503090, by rfl⟩ : syracuseStep 670787 = 1006181) B1006181
theorem B179335 : Blo 175800 179335 := bstep (se 1 (by rfl) ⟨134501, by rfl⟩ : syracuseStep 179335 = 269003) B269003
theorem B179343 : Blo 175800 179343 := bstep (se 1 (by rfl) ⟨134507, by rfl⟩ : syracuseStep 179343 = 269015) B269015
theorem B179387 : Blo 175800 179387 := bstep (se 1 (by rfl) ⟨134540, by rfl⟩ : syracuseStep 179387 = 269081) B269081
theorem B179463 : Blo 175800 179463 := bstep (se 1 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 179463 = 269195) B269195
theorem B179471 : Blo 175800 179471 := bstep (se 1 (by rfl) ⟨134603, by rfl⟩ : syracuseStep 179471 = 269207) B269207
theorem B179515 : Blo 175800 179515 := bstep (se 1 (by rfl) ⟨134636, by rfl⟩ : syracuseStep 179515 = 269273) B269273
theorem B605555 : Blo 175800 605555 := bstep (se 1 (by rfl) ⟨454166, by rfl⟩ : syracuseStep 605555 = 908333) B908333
theorem B572807 : Blo 175800 572807 := bstep (se 1 (by rfl) ⟨429605, by rfl⟩ : syracuseStep 572807 = 859211) B859211
theorem B179591 : Blo 175800 179591 := bstep (se 1 (by rfl) ⟨134693, by rfl⟩ : syracuseStep 179591 = 269387) B269387
theorem B179599 : Blo 175800 179599 := bstep (se 1 (by rfl) ⟨134699, by rfl⟩ : syracuseStep 179599 = 269399) B269399
theorem B671129 : Blo 175800 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B179643 : Blo 175800 179643 := bstep (se 1 (by rfl) ⟨134732, by rfl⟩ : syracuseStep 179643 = 269465) B269465
theorem B179719 : Blo 175800 179719 := bstep (se 1 (by rfl) ⟨134789, by rfl⟩ : syracuseStep 179719 = 269579) B269579
theorem B179727 : Blo 175800 179727 := bstep (se 1 (by rfl) ⟨134795, by rfl⟩ : syracuseStep 179727 = 269591) B269591
theorem B179771 : Blo 175800 179771 := bstep (se 1 (by rfl) ⟨134828, by rfl⟩ : syracuseStep 179771 = 269657) B269657
theorem B376609 : Blo 175800 376609 := bstep (se 2 (by rfl) ⟨141228, by rfl⟩ : syracuseStep 376609 = 282457) B282457
theorem B638873 : Blo 175800 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B638929 : Blo 175800 638929 := bstep (se 2 (by rfl) ⟨239598, by rfl⟩ : syracuseStep 638929 = 479197) B479197
theorem B2211851 : Blo 175800 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B671773 : Blo 175800 671773 := bstep (se 3 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 671773 = 251915) B251915
theorem B541043 : Blo 175800 541043 := bstep (se 1 (by rfl) ⟨405782, by rfl⟩ : syracuseStep 541043 = 811565) B811565
theorem B377207 : Blo 175800 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B508295 : Blo 175800 508295 := bstep (se 1 (by rfl) ⟨381221, by rfl⟩ : syracuseStep 508295 = 762443) B762443
theorem B901529 : Blo 175800 901529 := bstep (se 2 (by rfl) ⟨338073, by rfl⟩ : syracuseStep 901529 = 676147) B676147
theorem B1360313 : Blo 175800 1360313 := bstep (se 2 (by rfl) ⟨510117, by rfl⟩ : syracuseStep 1360313 = 1020235) B1020235
theorem B541129 : Blo 175800 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B967133 : Blo 175800 967133 := bstep (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) B362675
theorem B213563 : Blo 175800 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B2278307 : Blo 175800 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B476171 : Blo 175800 476171 := bstep (se 1 (by rfl) ⟨357128, by rfl⟩ : syracuseStep 476171 = 714257) B714257
theorem B1590749 : Blo 175800 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B181775 : Blo 175800 181775 := bstep (se 1 (by rfl) ⟨136331, by rfl⟩ : syracuseStep 181775 = 272663) B272663
theorem B575063 : Blo 175800 575063 := bstep (se 1 (by rfl) ⟨431297, by rfl⟩ : syracuseStep 575063 = 862595) B862595
theorem B1427543 : Blo 175800 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B510209 : Blo 175800 510209 := bstep (se 2 (by rfl) ⟨191328, by rfl⟩ : syracuseStep 510209 = 382657) B382657
theorem B19942129 : Blo 175800 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B510779 : Blo 175800 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B674675 : Blo 175800 674675 := bstep (se 1 (by rfl) ⟨506006, by rfl⟩ : syracuseStep 674675 = 1012013) B1012013
theorem B904121 : Blo 175800 904121 := bstep (se 2 (by rfl) ⟨339045, by rfl⟩ : syracuseStep 904121 = 678091) B678091
theorem B511019 : Blo 175800 511019 := bstep (se 1 (by rfl) ⟨383264, by rfl⟩ : syracuseStep 511019 = 766529) B766529
theorem B1002557 : Blo 175800 1002557 := bstep (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) B375959
theorem B805949 : Blo 175800 805949 := bstep (se 3 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 805949 = 302231) B302231
theorem B445783 : Blo 175800 445783 := bstep (se 1 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 445783 = 668675) B668675
theorem B446087 : Blo 175800 446087 := bstep (se 1 (by rfl) ⟨334565, by rfl⟩ : syracuseStep 446087 = 669131) B669131
theorem B1003265 : Blo 175800 1003265 := bstep (se 2 (by rfl) ⟨376224, by rfl⟩ : syracuseStep 1003265 = 752449) B752449
theorem B446219 : Blo 175800 446219 := bstep (se 1 (by rfl) ⟨334664, by rfl⟩ : syracuseStep 446219 = 669329) B669329
theorem B905417 : Blo 175800 905417 := bstep (se 2 (by rfl) ⟨339531, by rfl⟩ : syracuseStep 905417 = 679063) B679063
theorem B446735 : Blo 175800 446735 := bstep (se 1 (by rfl) ⟨335051, by rfl⟩ : syracuseStep 446735 = 670103) B670103
theorem B971023 : Blo 175800 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B446867 : Blo 175800 446867 := bstep (se 1 (by rfl) ⟨335150, by rfl⟩ : syracuseStep 446867 = 670301) B670301
theorem B1528577 : Blo 175800 1528577 := bstep (se 2 (by rfl) ⟨573216, by rfl⟩ : syracuseStep 1528577 = 1146433) B1146433
theorem B676907 : Blo 175800 676907 := bstep (se 1 (by rfl) ⟨507680, by rfl⟩ : syracuseStep 676907 = 1015361) B1015361
theorem B251209 : Blo 175800 251209 := bstep (se 2 (by rfl) ⟨94203, by rfl⟩ : syracuseStep 251209 = 188407) B188407
theorem B448001 : Blo 175800 448001 := bstep (se 2 (by rfl) ⟨168000, by rfl⟩ : syracuseStep 448001 = 336001) B336001
theorem B1955393 : Blo 175800 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B218767 : Blo 175800 218767 := bstep (se 1 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 218767 = 328151) B328151
theorem B448375 : Blo 175800 448375 := bstep (se 1 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 448375 = 672563) B672563
theorem B1005655 : Blo 175800 1005655 := bstep (se 1 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 1005655 = 1508483) B1508483
theorem B1267913 : Blo 175800 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B448811 : Blo 175800 448811 := bstep (se 1 (by rfl) ⟨336608, by rfl⟩ : syracuseStep 448811 = 673217) B673217
theorem B514451 : Blo 175800 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B547343 : Blo 175800 547343 := bstep (se 1 (by rfl) ⟨410507, by rfl⟩ : syracuseStep 547343 = 821015) B821015
theorem B481879 : Blo 175800 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B285455 : Blo 175800 285455 := bstep (se 1 (by rfl) ⟨214091, by rfl⟩ : syracuseStep 285455 = 428183) B428183
theorem B482183 : Blo 175800 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B383879 : Blo 175800 383879 := bstep (se 1 (by rfl) ⟨287909, by rfl⟩ : syracuseStep 383879 = 575819) B575819
theorem B2579363 : Blo 175800 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B449651 : Blo 175800 449651 := bstep (se 1 (by rfl) ⟨337238, by rfl⟩ : syracuseStep 449651 = 674477) B674477
theorem B449671 : Blo 175800 449671 := bstep (se 1 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 449671 = 674507) B674507
theorem B482593 : Blo 175800 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B3366203 : Blo 175800 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B449945 : Blo 175800 449945 := bstep (se 2 (by rfl) ⟨168729, by rfl⟩ : syracuseStep 449945 = 337459) B337459
theorem B450107 : Blo 175800 450107 := bstep (se 1 (by rfl) ⟨337580, by rfl⟩ : syracuseStep 450107 = 675161) B675161
theorem B483017 : Blo 175800 483017 := bstep (se 2 (by rfl) ⟨181131, by rfl⟩ : syracuseStep 483017 = 362263) B362263
theorem B319177 : Blo 175800 319177 := bstep (se 2 (by rfl) ⟨119691, by rfl⟩ : syracuseStep 319177 = 239383) B239383
theorem B253687 : Blo 175800 253687 := bstep (se 1 (by rfl) ⟨190265, by rfl⟩ : syracuseStep 253687 = 380531) B380531
theorem B1335041 : Blo 175800 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B450319 : Blo 175800 450319 := bstep (se 1 (by rfl) ⟨337739, by rfl⟩ : syracuseStep 450319 = 675479) B675479
theorem B1007639 : Blo 175800 1007639 := bstep (se 1 (by rfl) ⟨755729, by rfl⟩ : syracuseStep 1007639 = 1511459) B1511459
theorem B614429 : Blo 175800 614429 := bstep (se 3 (by rfl) ⟨115205, by rfl⟩ : syracuseStep 614429 = 230411) B230411
theorem B450593 : Blo 175800 450593 := bstep (se 2 (by rfl) ⟨168972, by rfl⟩ : syracuseStep 450593 = 337945) B337945
theorem B254011 : Blo 175800 254011 := bstep (se 1 (by rfl) ⟨190508, by rfl⟩ : syracuseStep 254011 = 381017) B381017
theorem B680339 : Blo 175800 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B483869 : Blo 175800 483869 := bstep (se 3 (by rfl) ⟨90725, by rfl⟩ : syracuseStep 483869 = 181451) B181451
theorem B451595 : Blo 175800 451595 := bstep (se 1 (by rfl) ⟨338696, by rfl⟩ : syracuseStep 451595 = 677393) B677393
theorem B1532951 : Blo 175800 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B910529 : Blo 175800 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B222583 : Blo 175800 222583 := bstep (se 1 (by rfl) ⟨166937, by rfl⟩ : syracuseStep 222583 = 333875) B333875
theorem B3433859 : Blo 175800 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B1533329 : Blo 175800 1533329 := bstep (se 2 (by rfl) ⟨574998, by rfl⟩ : syracuseStep 1533329 = 1149997) B1149997
theorem B452243 : Blo 175800 452243 := bstep (se 1 (by rfl) ⟨339182, by rfl⟩ : syracuseStep 452243 = 678365) B678365
theorem B222907 : Blo 175800 222907 := bstep (se 1 (by rfl) ⟨167180, by rfl⟩ : syracuseStep 222907 = 334361) B334361
theorem B1075079 : Blo 175800 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B452537 : Blo 175800 452537 := bstep (se 2 (by rfl) ⟨169701, by rfl⟩ : syracuseStep 452537 = 339403) B339403
theorem B6514805 : Blo 175800 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B518699 : Blo 175800 518699 := bstep (se 1 (by rfl) ⟨389024, by rfl⟩ : syracuseStep 518699 = 778049) B778049
theorem B453235 : Blo 175800 453235 := bstep (se 1 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 453235 = 679853) B679853
theorem B223879 : Blo 175800 223879 := bstep (se 1 (by rfl) ⟨167909, by rfl⟩ : syracuseStep 223879 = 335819) B335819
theorem B6810317 : Blo 175800 6810317 := bstep (se 3 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 6810317 = 2553869) B2553869
theorem B453377 : Blo 175800 453377 := bstep (se 2 (by rfl) ⟨170016, by rfl⟩ : syracuseStep 453377 = 340033) B340033
theorem B224299 : Blo 175800 224299 := bstep (se 1 (by rfl) ⟨168224, by rfl⟩ : syracuseStep 224299 = 336449) B336449
theorem B453833 : Blo 175800 453833 := bstep (se 2 (by rfl) ⟨170187, by rfl⟩ : syracuseStep 453833 = 340375) B340375
theorem B257287 : Blo 175800 257287 := bstep (se 1 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 257287 = 385931) B385931
theorem B224527 : Blo 175800 224527 := bstep (se 1 (by rfl) ⟨168395, by rfl⟩ : syracuseStep 224527 = 336791) B336791
theorem B191803 : Blo 175800 191803 := bstep (se 1 (by rfl) ⟨143852, by rfl⟩ : syracuseStep 191803 = 287705) B287705
theorem B1830289 : Blo 175800 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1535441 : Blo 175800 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B454187 : Blo 175800 454187 := bstep (se 1 (by rfl) ⟨340640, by rfl⟩ : syracuseStep 454187 = 681281) B681281
theorem B323207 : Blo 175800 323207 := bstep (se 1 (by rfl) ⟨242405, by rfl⟩ : syracuseStep 323207 = 484811) B484811
theorem B1699505 : Blo 175800 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B225271 : Blo 175800 225271 := bstep (se 1 (by rfl) ⟨168953, by rfl⟩ : syracuseStep 225271 = 337907) B337907
theorem B1339415 : Blo 175800 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B323617 : Blo 175800 323617 := bstep (se 2 (by rfl) ⟨121356, by rfl⟩ : syracuseStep 323617 = 242713) B242713
theorem B5009501 : Blo 175800 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B225595 : Blo 175800 225595 := bstep (se 1 (by rfl) ⟨169196, by rfl⟩ : syracuseStep 225595 = 338393) B338393
theorem B291131 : Blo 175800 291131 := bstep (se 1 (by rfl) ⟨218348, by rfl⟩ : syracuseStep 291131 = 436697) B436697
theorem B487951 : Blo 175800 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B1078049 : Blo 175800 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B226091 : Blo 175800 226091 := bstep (se 1 (by rfl) ⟨169568, by rfl⟩ : syracuseStep 226091 = 339137) B339137
theorem B914323 : Blo 175800 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B423031 : Blo 175800 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B816365 : Blo 175800 816365 := bstep (se 3 (by rfl) ⟨153068, by rfl⟩ : syracuseStep 816365 = 306137) B306137
theorem B226567 : Blo 175800 226567 := bstep (se 1 (by rfl) ⟨169925, by rfl⟩ : syracuseStep 226567 = 339851) B339851
theorem B1209659 : Blo 175800 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B751133 : Blo 175800 751133 := bstep (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) B281675
theorem B4126277 : Blo 175800 4126277 := bstep (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) B773677
theorem B2291429 : Blo 175800 2291429 := bstep (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) B429643
theorem B227063 : Blo 175800 227063 := bstep (se 1 (by rfl) ⟨170297, by rfl⟩ : syracuseStep 227063 = 340595) B340595
theorem B1144691 : Blo 175800 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B227215 : Blo 175800 227215 := bstep (se 1 (by rfl) ⟨170411, by rfl⟩ : syracuseStep 227215 = 340823) B340823
theorem B227387 : Blo 175800 227387 := bstep (se 1 (by rfl) ⟨170540, by rfl⟩ : syracuseStep 227387 = 341081) B341081
theorem B1964119 : Blo 175800 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B227515 : Blo 175800 227515 := bstep (se 1 (by rfl) ⟨170636, by rfl⟩ : syracuseStep 227515 = 341273) B341273
theorem B719219 : Blo 175800 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B1440185 : Blo 175800 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B326279 : Blo 175800 326279 := bstep (se 1 (by rfl) ⟨244709, by rfl⟩ : syracuseStep 326279 = 489419) B489419
theorem B1440449 : Blo 175800 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B490583 : Blo 175800 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B720161 : Blo 175800 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B2030993 : Blo 175800 2030993 := bstep (se 2 (by rfl) ⟨761622, by rfl⟩ : syracuseStep 2030993 = 1523245) B1523245
theorem B1506707 : Blo 175800 1506707 := bstep (se 1 (by rfl) ⟨1130030, by rfl⟩ : syracuseStep 1506707 = 2260061) B2260061
theorem B2719331 : Blo 175800 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B229111 : Blo 175800 229111 := bstep (se 1 (by rfl) ⟨171833, by rfl⟩ : syracuseStep 229111 = 343667) B343667
theorem B5898269 : Blo 175800 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B1572941 : Blo 175800 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B360695 : Blo 175800 360695 := bstep (se 1 (by rfl) ⟨270521, by rfl⟩ : syracuseStep 360695 = 541043) B541043
theorem B721295 : Blo 175800 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B1180169 : Blo 175800 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B21955157 : Blo 175800 21955157 := bstep (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) B257287
theorem B721505 : Blo 175800 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B5768009 : Blo 175800 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B721847 : Blo 175800 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B951695 : Blo 175800 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B263759 : Blo 175800 263759 := bstep (se 1 (by rfl) ⟨197819, by rfl⟩ : syracuseStep 263759 = 395639) B395639
theorem B263879 : Blo 175800 263879 := bstep (se 1 (by rfl) ⟨197909, by rfl⟩ : syracuseStep 263879 = 395819) B395819
theorem B1017593 : Blo 175800 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B296777 : Blo 175800 296777 := bstep (se 2 (by rfl) ⟨111291, by rfl⟩ : syracuseStep 296777 = 222583) B222583
theorem B264041 : Blo 175800 264041 := bstep (se 2 (by rfl) ⟨99015, by rfl⟩ : syracuseStep 264041 = 198031) B198031
theorem B264119 : Blo 175800 264119 := bstep (se 1 (by rfl) ⟨198089, by rfl⟩ : syracuseStep 264119 = 396179) B396179
theorem B264155 : Blo 175800 264155 := bstep (se 1 (by rfl) ⟨198116, by rfl⟩ : syracuseStep 264155 = 396233) B396233
theorem B297209 : Blo 175800 297209 := bstep (se 2 (by rfl) ⟨111453, by rfl⟩ : syracuseStep 297209 = 222907) B222907
theorem B297391 : Blo 175800 297391 := bstep (se 1 (by rfl) ⟨223043, by rfl⟩ : syracuseStep 297391 = 446087) B446087
theorem B264623 : Blo 175800 264623 := bstep (se 1 (by rfl) ⟨198467, by rfl⟩ : syracuseStep 264623 = 396935) B396935
theorem B297479 : Blo 175800 297479 := bstep (se 1 (by rfl) ⟨223109, by rfl⟩ : syracuseStep 297479 = 446219) B446219
theorem B264713 : Blo 175800 264713 := bstep (se 2 (by rfl) ⟨99267, by rfl⟩ : syracuseStep 264713 = 198535) B198535
theorem B264743 : Blo 175800 264743 := bstep (se 1 (by rfl) ⟨198557, by rfl⟩ : syracuseStep 264743 = 397115) B397115
theorem B395873 : Blo 175800 395873 := bstep (se 2 (by rfl) ⟨148452, by rfl⟩ : syracuseStep 395873 = 296905) B296905
theorem B264827 : Blo 175800 264827 := bstep (se 1 (by rfl) ⟨198620, by rfl⟩ : syracuseStep 264827 = 397241) B397241
theorem B199291 : Blo 175800 199291 := bstep (se 1 (by rfl) ⟨149468, by rfl⟩ : syracuseStep 199291 = 298937) B298937
theorem B264953 : Blo 175800 264953 := bstep (se 2 (by rfl) ⟨99357, by rfl⟩ : syracuseStep 264953 = 198715) B198715
theorem B297823 : Blo 175800 297823 := bstep (se 1 (by rfl) ⟨223367, by rfl⟩ : syracuseStep 297823 = 446735) B446735
theorem B265055 : Blo 175800 265055 := bstep (se 1 (by rfl) ⟨198791, by rfl⟩ : syracuseStep 265055 = 397583) B397583
theorem B265067 : Blo 175800 265067 := bstep (se 1 (by rfl) ⟨198800, by rfl⟩ : syracuseStep 265067 = 397601) B397601
theorem B396215 : Blo 175800 396215 := bstep (se 1 (by rfl) ⟨297161, by rfl⟩ : syracuseStep 396215 = 594323) B594323
theorem B297911 : Blo 175800 297911 := bstep (se 1 (by rfl) ⟨223433, by rfl⟩ : syracuseStep 297911 = 446867) B446867
theorem B265295 : Blo 175800 265295 := bstep (se 1 (by rfl) ⟨198971, by rfl⟩ : syracuseStep 265295 = 397943) B397943
theorem B199759 : Blo 175800 199759 := bstep (se 1 (by rfl) ⟨149819, by rfl⟩ : syracuseStep 199759 = 299639) B299639
theorem B1019051 : Blo 175800 1019051 := bstep (se 1 (by rfl) ⟨764288, by rfl⟩ : syracuseStep 1019051 = 1528577) B1528577
theorem B265415 : Blo 175800 265415 := bstep (se 1 (by rfl) ⟨199061, by rfl⟩ : syracuseStep 265415 = 398123) B398123
theorem B462071 : Blo 175800 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B265577 : Blo 175800 265577 := bstep (se 2 (by rfl) ⟨99591, by rfl⟩ : syracuseStep 265577 = 199183) B199183
theorem B265655 : Blo 175800 265655 := bstep (se 1 (by rfl) ⟨199241, by rfl⟩ : syracuseStep 265655 = 398483) B398483
theorem B265691 : Blo 175800 265691 := bstep (se 1 (by rfl) ⟨199268, by rfl⟩ : syracuseStep 265691 = 398537) B398537
theorem B200155 : Blo 175800 200155 := bstep (se 1 (by rfl) ⟨150116, by rfl⟩ : syracuseStep 200155 = 300233) B300233
theorem B396809 : Blo 175800 396809 := bstep (se 2 (by rfl) ⟨148803, by rfl⟩ : syracuseStep 396809 = 297607) B297607
theorem B298505 : Blo 175800 298505 := bstep (se 2 (by rfl) ⟨111939, by rfl⟩ : syracuseStep 298505 = 223879) B223879
theorem B5312087 : Blo 175800 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B298667 : Blo 175800 298667 := bstep (se 1 (by rfl) ⟨224000, by rfl⟩ : syracuseStep 298667 = 448001) B448001
theorem B397151 : Blo 175800 397151 := bstep (se 1 (by rfl) ⟨297863, by rfl⟩ : syracuseStep 397151 = 595727) B595727
theorem B593783 : Blo 175800 593783 := bstep (se 1 (by rfl) ⟨445337, by rfl⟩ : syracuseStep 593783 = 890675) B890675
theorem B266159 : Blo 175800 266159 := bstep (se 1 (by rfl) ⟨199619, by rfl⟩ : syracuseStep 266159 = 399239) B399239
theorem B200623 : Blo 175800 200623 := bstep (se 1 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 200623 = 300935) B300935
theorem B266249 : Blo 175800 266249 := bstep (se 2 (by rfl) ⟨99843, by rfl⟩ : syracuseStep 266249 = 199687) B199687
theorem B397331 : Blo 175800 397331 := bstep (se 1 (by rfl) ⟨297998, by rfl⟩ : syracuseStep 397331 = 595997) B595997
theorem B266279 : Blo 175800 266279 := bstep (se 1 (by rfl) ⟨199709, by rfl⟩ : syracuseStep 266279 = 399419) B399419
theorem B299065 : Blo 175800 299065 := bstep (se 2 (by rfl) ⟨112149, by rfl⟩ : syracuseStep 299065 = 224299) B224299
theorem B593999 : Blo 175800 593999 := bstep (se 1 (by rfl) ⟨445499, by rfl⟩ : syracuseStep 593999 = 890999) B890999
theorem B266363 : Blo 175800 266363 := bstep (se 1 (by rfl) ⟨199772, by rfl⟩ : syracuseStep 266363 = 399545) B399545
theorem B299207 : Blo 175800 299207 := bstep (se 1 (by rfl) ⟨224405, by rfl⟩ : syracuseStep 299207 = 448811) B448811
theorem B266489 : Blo 175800 266489 := bstep (se 2 (by rfl) ⟨99933, by rfl⟩ : syracuseStep 266489 = 199867) B199867
theorem B364895 : Blo 175800 364895 := bstep (se 1 (by rfl) ⟨273671, by rfl⟩ : syracuseStep 364895 = 547343) B547343
theorem B266591 : Blo 175800 266591 := bstep (se 1 (by rfl) ⟨199943, by rfl⟩ : syracuseStep 266591 = 399887) B399887
theorem B201055 : Blo 175800 201055 := bstep (se 1 (by rfl) ⟨150791, by rfl⟩ : syracuseStep 201055 = 301583) B301583
theorem B397673 : Blo 175800 397673 := bstep (se 2 (by rfl) ⟨149127, by rfl⟩ : syracuseStep 397673 = 298255) B298255
theorem B299369 : Blo 175800 299369 := bstep (se 2 (by rfl) ⟨112263, by rfl⟩ : syracuseStep 299369 = 224527) B224527
theorem B266603 : Blo 175800 266603 := bstep (se 1 (by rfl) ⟨199952, by rfl⟩ : syracuseStep 266603 = 399905) B399905
theorem B594377 : Blo 175800 594377 := bstep (se 2 (by rfl) ⟨222891, by rfl⟩ : syracuseStep 594377 = 445783) B445783
theorem B725543 : Blo 175800 725543 := bstep (se 1 (by rfl) ⟨544157, by rfl⟩ : syracuseStep 725543 = 1088315) B1088315
theorem B266831 : Blo 175800 266831 := bstep (se 1 (by rfl) ⟨200123, by rfl⟩ : syracuseStep 266831 = 400247) B400247
theorem B266951 : Blo 175800 266951 := bstep (se 1 (by rfl) ⟨200213, by rfl⟩ : syracuseStep 266951 = 400427) B400427
theorem B201415 : Blo 175800 201415 := bstep (se 1 (by rfl) ⟨151061, by rfl⟩ : syracuseStep 201415 = 302123) B302123
theorem B594647 : Blo 175800 594647 := bstep (se 1 (by rfl) ⟨445985, by rfl⟩ : syracuseStep 594647 = 891971) B891971
theorem B299767 : Blo 175800 299767 := bstep (se 1 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 299767 = 449651) B449651
theorem B267113 : Blo 175800 267113 := bstep (se 2 (by rfl) ⟨100167, by rfl⟩ : syracuseStep 267113 = 200335) B200335
theorem B594863 : Blo 175800 594863 := bstep (se 1 (by rfl) ⟨446147, by rfl⟩ : syracuseStep 594863 = 892295) B892295
theorem B267191 : Blo 175800 267191 := bstep (se 1 (by rfl) ⟨200393, by rfl⟩ : syracuseStep 267191 = 400787) B400787
theorem B398267 : Blo 175800 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B299963 : Blo 175800 299963 := bstep (se 1 (by rfl) ⟨224972, by rfl⟩ : syracuseStep 299963 = 449945) B449945
theorem B267227 : Blo 175800 267227 := bstep (se 1 (by rfl) ⟨200420, by rfl⟩ : syracuseStep 267227 = 400841) B400841
theorem B300071 : Blo 175800 300071 := bstep (se 1 (by rfl) ⟨225053, by rfl⟩ : syracuseStep 300071 = 450107) B450107
theorem B398393 : Blo 175800 398393 := bstep (se 2 (by rfl) ⟨149397, by rfl⟩ : syracuseStep 398393 = 298795) B298795
theorem B890027 : Blo 175800 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B300361 : Blo 175800 300361 := bstep (se 2 (by rfl) ⟨112635, by rfl⟩ : syracuseStep 300361 = 225271) B225271
theorem B300395 : Blo 175800 300395 := bstep (se 1 (by rfl) ⟨225296, by rfl⟩ : syracuseStep 300395 = 450593) B450593
theorem B431489 : Blo 175800 431489 := bstep (se 2 (by rfl) ⟨161808, by rfl⟩ : syracuseStep 431489 = 323617) B323617
theorem B398735 : Blo 175800 398735 := bstep (se 1 (by rfl) ⟨299051, by rfl⟩ : syracuseStep 398735 = 598103) B598103
theorem B595343 : Blo 175800 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B267695 : Blo 175800 267695 := bstep (se 1 (by rfl) ⟨200771, by rfl⟩ : syracuseStep 267695 = 401543) B401543
theorem B267785 : Blo 175800 267785 := bstep (se 2 (by rfl) ⟨100419, by rfl⟩ : syracuseStep 267785 = 200839) B200839
theorem B267815 : Blo 175800 267815 := bstep (se 1 (by rfl) ⟨200861, by rfl⟩ : syracuseStep 267815 = 401723) B401723
theorem B267899 : Blo 175800 267899 := bstep (se 1 (by rfl) ⟨200924, by rfl⟩ : syracuseStep 267899 = 401849) B401849
theorem B890513 : Blo 175800 890513 := bstep (se 2 (by rfl) ⟨333942, by rfl⟩ : syracuseStep 890513 = 667885) B667885
theorem B399059 : Blo 175800 399059 := bstep (se 1 (by rfl) ⟨299294, by rfl⟩ : syracuseStep 399059 = 598589) B598589
theorem B300793 : Blo 175800 300793 := bstep (se 2 (by rfl) ⟨112797, by rfl⟩ : syracuseStep 300793 = 225595) B225595
theorem B268025 : Blo 175800 268025 := bstep (se 2 (by rfl) ⟨100509, by rfl⟩ : syracuseStep 268025 = 201019) B201019
theorem B268127 : Blo 175800 268127 := bstep (se 1 (by rfl) ⟨201095, by rfl⟩ : syracuseStep 268127 = 402191) B402191
theorem B268139 : Blo 175800 268139 := bstep (se 1 (by rfl) ⟨201104, by rfl⟩ : syracuseStep 268139 = 402209) B402209
theorem B3381101 : Blo 175800 3381101 := bstep (se 3 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 3381101 = 1267913) B1267913
theorem B301063 : Blo 175800 301063 := bstep (se 1 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 301063 = 451595) B451595
theorem B1021967 : Blo 175800 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B268367 : Blo 175800 268367 := bstep (se 1 (by rfl) ⟨201275, by rfl⟩ : syracuseStep 268367 = 402551) B402551
theorem B268487 : Blo 175800 268487 := bstep (se 1 (by rfl) ⟨201365, by rfl⟩ : syracuseStep 268487 = 402731) B402731
theorem B1022219 : Blo 175800 1022219 := bstep (se 1 (by rfl) ⟨766664, by rfl⟩ : syracuseStep 1022219 = 1533329) B1533329
theorem B268649 : Blo 175800 268649 := bstep (se 2 (by rfl) ⟨100743, by rfl⟩ : syracuseStep 268649 = 201487) B201487
theorem B301495 : Blo 175800 301495 := bstep (se 1 (by rfl) ⟨226121, by rfl⟩ : syracuseStep 301495 = 452243) B452243
theorem B268727 : Blo 175800 268727 := bstep (se 1 (by rfl) ⟨201545, by rfl⟩ : syracuseStep 268727 = 403091) B403091
theorem B268763 : Blo 175800 268763 := bstep (se 1 (by rfl) ⟨201572, by rfl⟩ : syracuseStep 268763 = 403145) B403145
theorem B3840493 : Blo 175800 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B1219097 : Blo 175800 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B334459 : Blo 175800 334459 := bstep (se 1 (by rfl) ⟨250844, by rfl⟩ : syracuseStep 334459 = 501689) B501689
theorem B399995 : Blo 175800 399995 := bstep (se 1 (by rfl) ⟨299996, by rfl⟩ : syracuseStep 399995 = 599993) B599993
theorem B301691 : Blo 175800 301691 := bstep (se 1 (by rfl) ⟨226268, by rfl⟩ : syracuseStep 301691 = 452537) B452537
theorem B760529 : Blo 175800 760529 := bstep (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) B570397
theorem B400121 : Blo 175800 400121 := bstep (se 2 (by rfl) ⟨150045, by rfl⟩ : syracuseStep 400121 = 300091) B300091
theorem B564041 : Blo 175800 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B334687 : Blo 175800 334687 := bstep (se 1 (by rfl) ⟨251015, by rfl⟩ : syracuseStep 334687 = 502031) B502031
theorem B269231 : Blo 175800 269231 := bstep (se 1 (by rfl) ⟨201923, by rfl⟩ : syracuseStep 269231 = 403847) B403847
theorem B400391 : Blo 175800 400391 := bstep (se 1 (by rfl) ⟨300293, by rfl⟩ : syracuseStep 400391 = 600587) B600587
theorem B302089 : Blo 175800 302089 := bstep (se 2 (by rfl) ⟨113283, by rfl⟩ : syracuseStep 302089 = 226567) B226567
theorem B269321 : Blo 175800 269321 := bstep (se 2 (by rfl) ⟨100995, by rfl⟩ : syracuseStep 269321 = 201991) B201991
theorem B269351 : Blo 175800 269351 := bstep (se 1 (by rfl) ⟨202013, by rfl⟩ : syracuseStep 269351 = 404027) B404027
theorem B400463 : Blo 175800 400463 := bstep (se 1 (by rfl) ⟨300347, by rfl⟩ : syracuseStep 400463 = 600695) B600695
theorem B334945 : Blo 175800 334945 := bstep (se 2 (by rfl) ⟨125604, by rfl⟩ : syracuseStep 334945 = 251209) B251209
theorem B269435 : Blo 175800 269435 := bstep (se 1 (by rfl) ⟨202076, by rfl⟩ : syracuseStep 269435 = 404153) B404153
theorem B302251 : Blo 175800 302251 := bstep (se 1 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 302251 = 453377) B453377
theorem B597239 : Blo 175800 597239 := bstep (se 1 (by rfl) ⟨447929, by rfl⟩ : syracuseStep 597239 = 895859) B895859
theorem B269561 : Blo 175800 269561 := bstep (se 2 (by rfl) ⟨101085, by rfl⟩ : syracuseStep 269561 = 202171) B202171
theorem B269663 : Blo 175800 269663 := bstep (se 1 (by rfl) ⟨202247, by rfl⟩ : syracuseStep 269663 = 404495) B404495
theorem B269675 : Blo 175800 269675 := bstep (se 1 (by rfl) ⟨202256, by rfl⟩ : syracuseStep 269675 = 404513) B404513
theorem B761213 : Blo 175800 761213 := bstep (se 3 (by rfl) ⟨142727, by rfl⟩ : syracuseStep 761213 = 285455) B285455
theorem B335279 : Blo 175800 335279 := bstep (se 1 (by rfl) ⟨251459, by rfl⟩ : syracuseStep 335279 = 502919) B502919
theorem B400859 : Blo 175800 400859 := bstep (se 1 (by rfl) ⟨300644, by rfl⟩ : syracuseStep 400859 = 601289) B601289
theorem B302555 : Blo 175800 302555 := bstep (se 1 (by rfl) ⟨226916, by rfl⟩ : syracuseStep 302555 = 453833) B453833
theorem B597563 : Blo 175800 597563 := bstep (se 1 (by rfl) ⟨448172, by rfl⟩ : syracuseStep 597563 = 896345) B896345
theorem B1023677 : Blo 175800 1023677 := bstep (se 3 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 1023677 = 383879) B383879
theorem B302791 : Blo 175800 302791 := bstep (se 1 (by rfl) ⟨227093, by rfl⟩ : syracuseStep 302791 = 454187) B454187
theorem B597833 : Blo 175800 597833 := bstep (se 2 (by rfl) ⟨224187, by rfl⟩ : syracuseStep 597833 = 448375) B448375
theorem B302953 : Blo 175800 302953 := bstep (se 2 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 302953 = 227215) B227215
theorem B892781 : Blo 175800 892781 := bstep (se 3 (by rfl) ⟨167396, by rfl⟩ : syracuseStep 892781 = 334793) B334793
theorem B401327 : Blo 175800 401327 := bstep (se 1 (by rfl) ⟨300995, by rfl⟩ : syracuseStep 401327 = 601991) B601991
theorem B892943 : Blo 175800 892943 := bstep (se 1 (by rfl) ⟨669707, by rfl⟩ : syracuseStep 892943 = 1339415) B1339415
theorem B401579 : Blo 175800 401579 := bstep (se 1 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 401579 = 602369) B602369
theorem B2072753 : Blo 175800 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B303353 : Blo 175800 303353 := bstep (se 2 (by rfl) ⟨113757, by rfl⟩ : syracuseStep 303353 = 227515) B227515
theorem B336403 : Blo 175800 336403 := bstep (se 1 (by rfl) ⟨252302, by rfl⟩ : syracuseStep 336403 = 504605) B504605
theorem B402119 : Blo 175800 402119 := bstep (se 1 (by rfl) ⟨301589, by rfl⟩ : syracuseStep 402119 = 603179) B603179
theorem B336631 : Blo 175800 336631 := bstep (se 1 (by rfl) ⟨252473, by rfl⟩ : syracuseStep 336631 = 504947) B504947
theorem B598967 : Blo 175800 598967 := bstep (se 1 (by rfl) ⟨449225, by rfl⟩ : syracuseStep 598967 = 898451) B898451
theorem B500755 : Blo 175800 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B336935 : Blo 175800 336935 := bstep (se 1 (by rfl) ⟨252701, by rfl⟩ : syracuseStep 336935 = 505403) B505403
theorem B763127 : Blo 175800 763127 := bstep (se 1 (by rfl) ⟨572345, by rfl⟩ : syracuseStep 763127 = 1144691) B1144691
theorem B1221925 : Blo 175800 1221925 := bstep (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) B229111
theorem B599561 : Blo 175800 599561 := bstep (se 2 (by rfl) ⟨224835, by rfl⟩ : syracuseStep 599561 = 449671) B449671
theorem B402983 : Blo 175800 402983 := bstep (se 1 (by rfl) ⟨302237, by rfl⟩ : syracuseStep 402983 = 604475) B604475
theorem B960299 : Blo 175800 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B403307 : Blo 175800 403307 := bstep (se 1 (by rfl) ⟨302480, by rfl⟩ : syracuseStep 403307 = 604961) B604961
theorem B1288045 : Blo 175800 1288045 := bstep (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) B483017
theorem B403361 : Blo 175800 403361 := bstep (se 2 (by rfl) ⟨151260, by rfl⟩ : syracuseStep 403361 = 302521) B302521
theorem B403703 : Blo 175800 403703 := bstep (se 1 (by rfl) ⟨302777, by rfl⟩ : syracuseStep 403703 = 605555) B605555
theorem B1353995 : Blo 175800 1353995 := bstep (se 1 (by rfl) ⟨1015496, by rfl⟩ : syracuseStep 1353995 = 2030993) B2030993
theorem B338249 : Blo 175800 338249 := bstep (se 2 (by rfl) ⟨126843, by rfl⟩ : syracuseStep 338249 = 253687) B253687
theorem B600425 : Blo 175800 600425 := bstep (se 2 (by rfl) ⟨225159, by rfl⟩ : syracuseStep 600425 = 450319) B450319
theorem B502145 : Blo 175800 502145 := bstep (se 2 (by rfl) ⟨188304, by rfl⟩ : syracuseStep 502145 = 376609) B376609
theorem B1812887 : Blo 175800 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B895697 : Blo 175800 895697 := bstep (se 2 (by rfl) ⟨335886, by rfl⟩ : syracuseStep 895697 = 671773) B671773
theorem B502487 : Blo 175800 502487 := bstep (se 1 (by rfl) ⟨376865, by rfl⟩ : syracuseStep 502487 = 753731) B753731
theorem B338681 : Blo 175800 338681 := bstep (se 2 (by rfl) ⟨127005, by rfl⟩ : syracuseStep 338681 = 254011) B254011
theorem B404297 : Blo 175800 404297 := bstep (se 2 (by rfl) ⟨151611, by rfl⟩ : syracuseStep 404297 = 303223) B303223
theorem B1289135 : Blo 175800 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B601019 : Blo 175800 601019 := bstep (se 1 (by rfl) ⟨450764, by rfl⟩ : syracuseStep 601019 = 901529) B901529
theorem B2895041 : Blo 175800 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B1518871 : Blo 175800 1518871 := bstep (se 1 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 1518871 = 2278307) B2278307
theorem B1060499 : Blo 175800 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B765587 : Blo 175800 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B1355453 : Blo 175800 1355453 := bstep (se 3 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 1355453 = 508295) B508295
theorem B175815 : Blo 175800 175815 := bstep (se 1 (by rfl) ⟨131861, by rfl⟩ : syracuseStep 175815 = 263723) B263723
theorem B175835 : Blo 175800 175835 := bstep (se 1 (by rfl) ⟨131876, by rfl⟩ : syracuseStep 175835 = 263753) B263753
theorem B175911 : Blo 175800 175911 := bstep (se 1 (by rfl) ⟨131933, by rfl⟩ : syracuseStep 175911 = 263867) B263867
theorem B175951 : Blo 175800 175951 := bstep (se 1 (by rfl) ⟨131963, by rfl⟩ : syracuseStep 175951 = 263927) B263927
theorem B175967 : Blo 175800 175967 := bstep (se 1 (by rfl) ⟨131975, by rfl⟩ : syracuseStep 175967 = 263951) B263951
theorem B175995 : Blo 175800 175995 := bstep (se 1 (by rfl) ⟨131996, by rfl⟩ : syracuseStep 175995 = 263993) B263993
theorem B176047 : Blo 175800 176047 := bstep (se 1 (by rfl) ⟨132035, by rfl⟩ : syracuseStep 176047 = 264071) B264071
theorem B176071 : Blo 175800 176071 := bstep (se 1 (by rfl) ⟨132053, by rfl⟩ : syracuseStep 176071 = 264107) B264107
theorem B176091 : Blo 175800 176091 := bstep (se 1 (by rfl) ⟨132068, by rfl⟩ : syracuseStep 176091 = 264137) B264137
theorem B176167 : Blo 175800 176167 := bstep (se 1 (by rfl) ⟨132125, by rfl⟩ : syracuseStep 176167 = 264251) B264251
theorem B176207 : Blo 175800 176207 := bstep (se 1 (by rfl) ⟨132155, by rfl⟩ : syracuseStep 176207 = 264311) B264311
theorem B176223 : Blo 175800 176223 := bstep (se 1 (by rfl) ⟨132167, by rfl⟩ : syracuseStep 176223 = 264335) B264335
theorem B176251 : Blo 175800 176251 := bstep (se 1 (by rfl) ⟨132188, by rfl⟩ : syracuseStep 176251 = 264377) B264377
theorem B569501 : Blo 175800 569501 := bstep (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) B213563
theorem B1355939 : Blo 175800 1355939 := bstep (se 1 (by rfl) ⟨1016954, by rfl⟩ : syracuseStep 1355939 = 2033909) B2033909
theorem B340139 : Blo 175800 340139 := bstep (se 1 (by rfl) ⟨255104, by rfl⟩ : syracuseStep 340139 = 510209) B510209
theorem B176303 : Blo 175800 176303 := bstep (se 1 (by rfl) ⟨132227, by rfl⟩ : syracuseStep 176303 = 264455) B264455
theorem B176327 : Blo 175800 176327 := bstep (se 1 (by rfl) ⟨132245, by rfl⟩ : syracuseStep 176327 = 264491) B264491
theorem B176347 : Blo 175800 176347 := bstep (se 1 (by rfl) ⟨132260, by rfl⟩ : syracuseStep 176347 = 264521) B264521
theorem B176423 : Blo 175800 176423 := bstep (se 1 (by rfl) ⟨132317, by rfl⟩ : syracuseStep 176423 = 264635) B264635
theorem B176463 : Blo 175800 176463 := bstep (se 1 (by rfl) ⟨132347, by rfl⟩ : syracuseStep 176463 = 264695) B264695
theorem B176479 : Blo 175800 176479 := bstep (se 1 (by rfl) ⟨132359, by rfl⟩ : syracuseStep 176479 = 264719) B264719
theorem B176507 : Blo 175800 176507 := bstep (se 1 (by rfl) ⟨132380, by rfl⟩ : syracuseStep 176507 = 264761) B264761
theorem B176559 : Blo 175800 176559 := bstep (se 1 (by rfl) ⟨132419, by rfl⟩ : syracuseStep 176559 = 264839) B264839
theorem B176583 : Blo 175800 176583 := bstep (se 1 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 176583 = 264875) B264875
theorem B176603 : Blo 175800 176603 := bstep (se 1 (by rfl) ⟨132452, by rfl⟩ : syracuseStep 176603 = 264905) B264905
theorem B1290775 : Blo 175800 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B176679 : Blo 175800 176679 := bstep (se 1 (by rfl) ⟨132509, by rfl⟩ : syracuseStep 176679 = 265019) B265019
theorem B340519 : Blo 175800 340519 := bstep (se 1 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 340519 = 510779) B510779
theorem B176719 : Blo 175800 176719 := bstep (se 1 (by rfl) ⟨132539, by rfl⟩ : syracuseStep 176719 = 265079) B265079
theorem B176735 : Blo 175800 176735 := bstep (se 1 (by rfl) ⟨132551, by rfl⟩ : syracuseStep 176735 = 265103) B265103
theorem B176763 : Blo 175800 176763 := bstep (se 1 (by rfl) ⟨132572, by rfl⟩ : syracuseStep 176763 = 265145) B265145
theorem B602747 : Blo 175800 602747 := bstep (se 1 (by rfl) ⟨452060, by rfl⟩ : syracuseStep 602747 = 904121) B904121
theorem B176815 : Blo 175800 176815 := bstep (se 1 (by rfl) ⟨132611, by rfl⟩ : syracuseStep 176815 = 265223) B265223
theorem B176839 : Blo 175800 176839 := bstep (se 1 (by rfl) ⟨132629, by rfl⟩ : syracuseStep 176839 = 265259) B265259
theorem B340679 : Blo 175800 340679 := bstep (se 1 (by rfl) ⟨255509, by rfl⟩ : syracuseStep 340679 = 511019) B511019
theorem B668371 : Blo 175800 668371 := bstep (se 1 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 668371 = 1002557) B1002557
theorem B537299 : Blo 175800 537299 := bstep (se 1 (by rfl) ⟨402974, by rfl⟩ : syracuseStep 537299 = 805949) B805949
theorem B8630995 : Blo 175800 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B176859 : Blo 175800 176859 := bstep (se 1 (by rfl) ⟨132644, by rfl⟩ : syracuseStep 176859 = 265289) B265289
theorem B602909 : Blo 175800 602909 := bstep (se 3 (by rfl) ⟨113045, by rfl⟩ : syracuseStep 602909 = 226091) B226091
theorem B176935 : Blo 175800 176935 := bstep (se 1 (by rfl) ⟨132701, by rfl⟩ : syracuseStep 176935 = 265403) B265403
theorem B176975 : Blo 175800 176975 := bstep (se 1 (by rfl) ⟨132731, by rfl⟩ : syracuseStep 176975 = 265463) B265463
theorem B176991 : Blo 175800 176991 := bstep (se 1 (by rfl) ⟨132743, by rfl⟩ : syracuseStep 176991 = 265487) B265487
theorem B177019 : Blo 175800 177019 := bstep (se 1 (by rfl) ⟨132764, by rfl⟩ : syracuseStep 177019 = 265529) B265529
theorem B406433 : Blo 175800 406433 := bstep (se 2 (by rfl) ⟨152412, by rfl⟩ : syracuseStep 406433 = 304825) B304825
theorem B177071 : Blo 175800 177071 := bstep (se 1 (by rfl) ⟨132803, by rfl⟩ : syracuseStep 177071 = 265607) B265607
theorem B177095 : Blo 175800 177095 := bstep (se 1 (by rfl) ⟨132821, by rfl⟩ : syracuseStep 177095 = 265643) B265643
theorem B177115 : Blo 175800 177115 := bstep (se 1 (by rfl) ⟨132836, by rfl⟩ : syracuseStep 177115 = 265673) B265673
theorem B177191 : Blo 175800 177191 := bstep (se 1 (by rfl) ⟨132893, by rfl⟩ : syracuseStep 177191 = 265787) B265787
theorem B177231 : Blo 175800 177231 := bstep (se 1 (by rfl) ⟨132923, by rfl⟩ : syracuseStep 177231 = 265847) B265847
theorem B898127 : Blo 175800 898127 := bstep (se 1 (by rfl) ⟨673595, by rfl⟩ : syracuseStep 898127 = 1347191) B1347191
theorem B177247 : Blo 175800 177247 := bstep (se 1 (by rfl) ⟨132935, by rfl⟩ : syracuseStep 177247 = 265871) B265871
theorem B177275 : Blo 175800 177275 := bstep (se 1 (by rfl) ⟨132956, by rfl⟩ : syracuseStep 177275 = 265913) B265913
theorem B668843 : Blo 175800 668843 := bstep (se 1 (by rfl) ⟨501632, by rfl⟩ : syracuseStep 668843 = 1003265) B1003265
theorem B177327 : Blo 175800 177327 := bstep (se 1 (by rfl) ⟨132995, by rfl⟩ : syracuseStep 177327 = 265991) B265991
theorem B177351 : Blo 175800 177351 := bstep (se 1 (by rfl) ⟨133013, by rfl⟩ : syracuseStep 177351 = 266027) B266027
theorem B177371 : Blo 175800 177371 := bstep (se 1 (by rfl) ⟨133028, by rfl⟩ : syracuseStep 177371 = 266057) B266057
theorem B177447 : Blo 175800 177447 := bstep (se 1 (by rfl) ⟨133085, by rfl⟩ : syracuseStep 177447 = 266171) B266171
theorem B177487 : Blo 175800 177487 := bstep (se 1 (by rfl) ⟨133115, by rfl⟩ : syracuseStep 177487 = 266231) B266231
theorem B177503 : Blo 175800 177503 := bstep (se 1 (by rfl) ⟨133127, by rfl⟩ : syracuseStep 177503 = 266255) B266255
theorem B177531 : Blo 175800 177531 := bstep (se 1 (by rfl) ⟨133148, by rfl⟩ : syracuseStep 177531 = 266297) B266297
theorem B4634003 : Blo 175800 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B2602405 : Blo 175800 2602405 := bstep (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) B487951
theorem B177583 : Blo 175800 177583 := bstep (se 1 (by rfl) ⟨133187, by rfl⟩ : syracuseStep 177583 = 266375) B266375
theorem B177607 : Blo 175800 177607 := bstep (se 1 (by rfl) ⟨133205, by rfl⟩ : syracuseStep 177607 = 266411) B266411
theorem B177627 : Blo 175800 177627 := bstep (se 1 (by rfl) ⟨133220, by rfl⟩ : syracuseStep 177627 = 266441) B266441
theorem B603611 : Blo 175800 603611 := bstep (se 1 (by rfl) ⟨452708, by rfl⟩ : syracuseStep 603611 = 905417) B905417
theorem B177703 : Blo 175800 177703 := bstep (se 1 (by rfl) ⟨133277, by rfl⟩ : syracuseStep 177703 = 266555) B266555
theorem B177743 : Blo 175800 177743 := bstep (se 1 (by rfl) ⟨133307, by rfl⟩ : syracuseStep 177743 = 266615) B266615
theorem B177759 : Blo 175800 177759 := bstep (se 1 (by rfl) ⟨133319, by rfl⟩ : syracuseStep 177759 = 266639) B266639
theorem B177787 : Blo 175800 177787 := bstep (se 1 (by rfl) ⟨133340, by rfl⟩ : syracuseStep 177787 = 266681) B266681
theorem B177839 : Blo 175800 177839 := bstep (se 1 (by rfl) ⟨133379, by rfl⟩ : syracuseStep 177839 = 266759) B266759
theorem B177863 : Blo 175800 177863 := bstep (se 1 (by rfl) ⟨133397, by rfl⟩ : syracuseStep 177863 = 266795) B266795
theorem B898775 : Blo 175800 898775 := bstep (se 1 (by rfl) ⟨674081, by rfl⟩ : syracuseStep 898775 = 1348163) B1348163
theorem B177883 : Blo 175800 177883 := bstep (se 1 (by rfl) ⟨133412, by rfl⟩ : syracuseStep 177883 = 266825) B266825
theorem B177959 : Blo 175800 177959 := bstep (se 1 (by rfl) ⟨133469, by rfl⟩ : syracuseStep 177959 = 266939) B266939
theorem B177999 : Blo 175800 177999 := bstep (se 1 (by rfl) ⟨133499, by rfl⟩ : syracuseStep 177999 = 266999) B266999
theorem B178015 : Blo 175800 178015 := bstep (se 1 (by rfl) ⟨133511, by rfl⟩ : syracuseStep 178015 = 267023) B267023
theorem B178043 : Blo 175800 178043 := bstep (se 1 (by rfl) ⟨133532, by rfl⟩ : syracuseStep 178043 = 267065) B267065
theorem B178095 : Blo 175800 178095 := bstep (se 1 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 178095 = 267143) B267143
theorem B178119 : Blo 175800 178119 := bstep (se 1 (by rfl) ⟨133589, by rfl⟩ : syracuseStep 178119 = 267179) B267179
theorem B178139 : Blo 175800 178139 := bstep (se 1 (by rfl) ⟨133604, by rfl⟩ : syracuseStep 178139 = 267209) B267209
theorem B178215 : Blo 175800 178215 := bstep (se 1 (by rfl) ⟨133661, by rfl⟩ : syracuseStep 178215 = 267323) B267323
theorem B178255 : Blo 175800 178255 := bstep (se 1 (by rfl) ⟨133691, by rfl⟩ : syracuseStep 178255 = 267383) B267383
theorem B178271 : Blo 175800 178271 := bstep (se 1 (by rfl) ⟨133703, by rfl⟩ : syracuseStep 178271 = 267407) B267407
theorem B178299 : Blo 175800 178299 := bstep (se 1 (by rfl) ⟨133724, by rfl⟩ : syracuseStep 178299 = 267449) B267449
theorem B604313 : Blo 175800 604313 := bstep (se 2 (by rfl) ⟨226617, by rfl⟩ : syracuseStep 604313 = 453235) B453235
theorem B3225757 : Blo 175800 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B178351 : Blo 175800 178351 := bstep (se 1 (by rfl) ⟨133763, by rfl⟩ : syracuseStep 178351 = 267527) B267527
theorem B178375 : Blo 175800 178375 := bstep (se 1 (by rfl) ⟨133781, by rfl⟩ : syracuseStep 178375 = 267563) B267563
theorem B178395 : Blo 175800 178395 := bstep (se 1 (by rfl) ⟨133796, by rfl⟩ : syracuseStep 178395 = 267593) B267593
theorem B178471 : Blo 175800 178471 := bstep (se 1 (by rfl) ⟨133853, by rfl⟩ : syracuseStep 178471 = 267707) B267707
theorem B26589505 : Blo 175800 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B178511 : Blo 175800 178511 := bstep (se 1 (by rfl) ⟨133883, by rfl⟩ : syracuseStep 178511 = 267767) B267767
theorem B178527 : Blo 175800 178527 := bstep (se 1 (by rfl) ⟨133895, by rfl⟩ : syracuseStep 178527 = 267791) B267791
theorem B178555 : Blo 175800 178555 := bstep (se 1 (by rfl) ⟨133916, by rfl⟩ : syracuseStep 178555 = 267833) B267833
theorem B178607 : Blo 175800 178607 := bstep (se 1 (by rfl) ⟨133955, by rfl⟩ : syracuseStep 178607 = 267911) B267911
theorem B178631 : Blo 175800 178631 := bstep (se 1 (by rfl) ⟨133973, by rfl⟩ : syracuseStep 178631 = 267947) B267947
theorem B178651 : Blo 175800 178651 := bstep (se 1 (by rfl) ⟨133988, by rfl⟩ : syracuseStep 178651 = 267977) B267977
theorem B1358369 : Blo 175800 1358369 := bstep (se 2 (by rfl) ⟨509388, by rfl⟩ : syracuseStep 1358369 = 1018777) B1018777
theorem B178727 : Blo 175800 178727 := bstep (se 1 (by rfl) ⟨134045, by rfl⟩ : syracuseStep 178727 = 268091) B268091
theorem B178767 : Blo 175800 178767 := bstep (se 1 (by rfl) ⟨134075, by rfl⟩ : syracuseStep 178767 = 268151) B268151
theorem B178783 : Blo 175800 178783 := bstep (se 1 (by rfl) ⟨134087, by rfl⟩ : syracuseStep 178783 = 268175) B268175
theorem B178811 : Blo 175800 178811 := bstep (se 1 (by rfl) ⟨134108, by rfl⟩ : syracuseStep 178811 = 268217) B268217
theorem B178863 : Blo 175800 178863 := bstep (se 1 (by rfl) ⟨134147, by rfl⟩ : syracuseStep 178863 = 268295) B268295
theorem B178887 : Blo 175800 178887 := bstep (se 1 (by rfl) ⟨134165, by rfl⟩ : syracuseStep 178887 = 268331) B268331
theorem B178907 : Blo 175800 178907 := bstep (se 1 (by rfl) ⟨134180, by rfl⟩ : syracuseStep 178907 = 268361) B268361
theorem B178983 : Blo 175800 178983 := bstep (se 1 (by rfl) ⟨134237, by rfl⟩ : syracuseStep 178983 = 268475) B268475
theorem B179023 : Blo 175800 179023 := bstep (se 1 (by rfl) ⟨134267, by rfl⟩ : syracuseStep 179023 = 268535) B268535
theorem B179039 : Blo 175800 179039 := bstep (se 1 (by rfl) ⟨134279, by rfl⟩ : syracuseStep 179039 = 268559) B268559
theorem B179067 : Blo 175800 179067 := bstep (se 1 (by rfl) ⟨134300, by rfl⟩ : syracuseStep 179067 = 268601) B268601
theorem B179119 : Blo 175800 179119 := bstep (se 1 (by rfl) ⟨134339, by rfl⟩ : syracuseStep 179119 = 268679) B268679
theorem B342967 : Blo 175800 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B179143 : Blo 175800 179143 := bstep (se 1 (by rfl) ⟨134357, by rfl⟩ : syracuseStep 179143 = 268715) B268715
theorem B179163 : Blo 175800 179163 := bstep (se 1 (by rfl) ⟨134372, by rfl⟩ : syracuseStep 179163 = 268745) B268745
theorem B375815 : Blo 175800 375815 := bstep (se 1 (by rfl) ⟨281861, by rfl⟩ : syracuseStep 375815 = 563723) B563723
theorem B179239 : Blo 175800 179239 := bstep (se 1 (by rfl) ⟨134429, by rfl⟩ : syracuseStep 179239 = 268859) B268859
theorem B179279 : Blo 175800 179279 := bstep (se 1 (by rfl) ⟨134459, by rfl⟩ : syracuseStep 179279 = 268919) B268919
theorem B670801 : Blo 175800 670801 := bstep (se 2 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 670801 = 503101) B503101
theorem B179295 : Blo 175800 179295 := bstep (se 1 (by rfl) ⟨134471, by rfl⟩ : syracuseStep 179295 = 268943) B268943
theorem B179323 : Blo 175800 179323 := bstep (se 1 (by rfl) ⟨134492, by rfl⟩ : syracuseStep 179323 = 268985) B268985
theorem B179375 : Blo 175800 179375 := bstep (se 1 (by rfl) ⟨134531, by rfl⟩ : syracuseStep 179375 = 269063) B269063
theorem B2440385 : Blo 175800 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B179399 : Blo 175800 179399 := bstep (se 1 (by rfl) ⟨134549, by rfl⟩ : syracuseStep 179399 = 269099) B269099
theorem B179419 : Blo 175800 179419 := bstep (se 1 (by rfl) ⟨134564, by rfl⟩ : syracuseStep 179419 = 269129) B269129
theorem B1719575 : Blo 175800 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B179495 : Blo 175800 179495 := bstep (se 1 (by rfl) ⟨134621, by rfl⟩ : syracuseStep 179495 = 269243) B269243
theorem B605501 : Blo 175800 605501 := bstep (se 3 (by rfl) ⟨113531, by rfl⟩ : syracuseStep 605501 = 227063) B227063
theorem B179535 : Blo 175800 179535 := bstep (se 1 (by rfl) ⟨134651, by rfl⟩ : syracuseStep 179535 = 269303) B269303
theorem B179551 : Blo 175800 179551 := bstep (se 1 (by rfl) ⟨134663, by rfl⟩ : syracuseStep 179551 = 269327) B269327
theorem B179579 : Blo 175800 179579 := bstep (se 1 (by rfl) ⟨134684, by rfl⟩ : syracuseStep 179579 = 269369) B269369
theorem B671105 : Blo 175800 671105 := bstep (se 2 (by rfl) ⟨251664, by rfl⟩ : syracuseStep 671105 = 503329) B503329
theorem B179631 : Blo 175800 179631 := bstep (se 1 (by rfl) ⟨134723, by rfl⟩ : syracuseStep 179631 = 269447) B269447
theorem B179655 : Blo 175800 179655 := bstep (se 1 (by rfl) ⟨134741, by rfl⟩ : syracuseStep 179655 = 269483) B269483
theorem B179675 : Blo 175800 179675 := bstep (se 1 (by rfl) ⟨134756, by rfl⟩ : syracuseStep 179675 = 269513) B269513
theorem B179751 : Blo 175800 179751 := bstep (se 1 (by rfl) ⟨134813, by rfl⟩ : syracuseStep 179751 = 269627) B269627
theorem B572987 : Blo 175800 572987 := bstep (se 1 (by rfl) ⟨429740, by rfl⟩ : syracuseStep 572987 = 859481) B859481
theorem B179791 : Blo 175800 179791 := bstep (se 1 (by rfl) ⟨134843, by rfl⟩ : syracuseStep 179791 = 269687) B269687
theorem B2866877 : Blo 175800 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B671561 : Blo 175800 671561 := bstep (se 2 (by rfl) ⟨251835, by rfl⟩ : syracuseStep 671561 = 503671) B503671
theorem B573257 : Blo 175800 573257 := bstep (se 2 (by rfl) ⟨214971, by rfl⟩ : syracuseStep 573257 = 429943) B429943
theorem B573371 : Blo 175800 573371 := bstep (se 1 (by rfl) ⟨430028, by rfl⟩ : syracuseStep 573371 = 860057) B860057
theorem B671759 : Blo 175800 671759 := bstep (se 1 (by rfl) ⟨503819, by rfl⟩ : syracuseStep 671759 = 1007639) B1007639
theorem B409619 : Blo 175800 409619 := bstep (se 1 (by rfl) ⟨307214, by rfl⟩ : syracuseStep 409619 = 614429) B614429
theorem B606365 : Blo 175800 606365 := bstep (se 3 (by rfl) ⟨113693, by rfl⟩ : syracuseStep 606365 = 227387) B227387
theorem B1294697 : Blo 175800 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B901691 : Blo 175800 901691 := bstep (se 1 (by rfl) ⟨676268, by rfl⟩ : syracuseStep 901691 = 1352537) B1352537
theorem B607019 : Blo 175800 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B1917917 : Blo 175800 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B902339 : Blo 175800 902339 := bstep (se 1 (by rfl) ⟨676754, by rfl⟩ : syracuseStep 902339 = 1353509) B1353509
theorem B4343203 : Blo 175800 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B1164887 : Blo 175800 1164887 := bstep (se 1 (by rfl) ⟨873665, by rfl⟩ : syracuseStep 1164887 = 1747331) B1747331
theorem B345799 : Blo 175800 345799 := bstep (se 1 (by rfl) ⟨259349, by rfl⟩ : syracuseStep 345799 = 518699) B518699
theorem B4540211 : Blo 175800 4540211 := bstep (se 1 (by rfl) ⟨3405158, by rfl⟩ : syracuseStep 4540211 = 6810317) B6810317
theorem B575831 : Blo 175800 575831 := bstep (se 1 (by rfl) ⟨431873, by rfl⟩ : syracuseStep 575831 = 863747) B863747
theorem B215471 : Blo 175800 215471 := bstep (se 1 (by rfl) ⟨161603, by rfl⟩ : syracuseStep 215471 = 323207) B323207
theorem B1133003 : Blo 175800 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B445459 : Blo 175800 445459 := bstep (se 1 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 445459 = 668189) B668189
theorem B970157 : Blo 175800 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B642505 : Blo 175800 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B544243 : Blo 175800 544243 := bstep (se 1 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 544243 = 816365) B816365
theorem B2281283 : Blo 175800 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B1527619 : Blo 175800 1527619 := bstep (se 1 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 1527619 = 2291429) B2291429
theorem B446543 : Blo 175800 446543 := bstep (se 1 (by rfl) ⟨334907, by rfl⟩ : syracuseStep 446543 = 669815) B669815
theorem B1626193 : Blo 175800 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B1429811 : Blo 175800 1429811 := bstep (se 1 (by rfl) ⟨1072358, by rfl⟩ : syracuseStep 1429811 = 2144717) B2144717
theorem B643457 : Blo 175800 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B217519 : Blo 175800 217519 := bstep (se 1 (by rfl) ⟨163139, by rfl⟩ : syracuseStep 217519 = 326279) B326279
theorem B447191 : Blo 175800 447191 := bstep (se 1 (by rfl) ⟨335393, by rfl⟩ : syracuseStep 447191 = 670787) B670787
theorem B480107 : Blo 175800 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B381871 : Blo 175800 381871 := bstep (se 1 (by rfl) ⟨286403, by rfl⟩ : syracuseStep 381871 = 572807) B572807
theorem B1004471 : Blo 175800 1004471 := bstep (se 1 (by rfl) ⟨753353, by rfl⟩ : syracuseStep 1004471 = 1506707) B1506707
theorem B447419 : Blo 175800 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B447545 : Blo 175800 447545 := bstep (se 2 (by rfl) ⟨167829, by rfl⟩ : syracuseStep 447545 = 335659) B335659
theorem B284123 : Blo 175800 284123 := bstep (se 1 (by rfl) ⟨213092, by rfl⟩ : syracuseStep 284123 = 426185) B426185
theorem B480755 : Blo 175800 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B251471 : Blo 175800 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B906875 : Blo 175800 906875 := bstep (se 1 (by rfl) ⟨680156, by rfl⟩ : syracuseStep 906875 = 1360313) B1360313
theorem B644755 : Blo 175800 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B677591 : Blo 175800 677591 := bstep (se 1 (by rfl) ⟨508193, by rfl⟩ : syracuseStep 677591 = 1016387) B1016387
theorem B1005473 : Blo 175800 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B284635 : Blo 175800 284635 := bstep (se 1 (by rfl) ⟨213476, by rfl⟩ : syracuseStep 284635 = 426953) B426953
theorem B317447 : Blo 175800 317447 := bstep (se 1 (by rfl) ⟨238085, by rfl⟩ : syracuseStep 317447 = 476171) B476171
theorem B1005929 : Blo 175800 1005929 := bstep (se 2 (by rfl) ⟨377223, by rfl⟩ : syracuseStep 1005929 = 754447) B754447
theorem B383375 : Blo 175800 383375 := bstep (se 1 (by rfl) ⟨287531, by rfl⟩ : syracuseStep 383375 = 575063) B575063
theorem B907757 : Blo 175800 907757 := bstep (se 3 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 907757 = 340409) B340409
theorem B809453 : Blo 175800 809453 := bstep (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) B303545
theorem B1071751 : Blo 175800 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1137361 : Blo 175800 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B482311 : Blo 175800 482311 := bstep (se 1 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 482311 = 723467) B723467
theorem B1629377 : Blo 175800 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B449783 : Blo 175800 449783 := bstep (se 1 (by rfl) ⟨337337, by rfl⟩ : syracuseStep 449783 = 674675) B674675
theorem B2874797 : Blo 175800 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B909629 : Blo 175800 909629 := bstep (se 3 (by rfl) ⟨170555, by rfl⟩ : syracuseStep 909629 = 341111) B341111
theorem B680507 : Blo 175800 680507 := bstep (se 1 (by rfl) ⟨510380, by rfl⟩ : syracuseStep 680507 = 1020761) B1020761
theorem B451271 : Blo 175800 451271 := bstep (se 1 (by rfl) ⟨338453, by rfl⟩ : syracuseStep 451271 = 676907) B676907
theorem B1303595 : Blo 175800 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B2909303 : Blo 175800 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B484733 : Blo 175800 484733 := bstep (se 3 (by rfl) ⟨90887, by rfl⟩ : syracuseStep 484733 = 181775) B181775
theorem B5432741 : Blo 175800 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B1009097 : Blo 175800 1009097 := bstep (se 2 (by rfl) ⟨378411, by rfl⟩ : syracuseStep 1009097 = 756823) B756823
theorem B255737 : Blo 175800 255737 := bstep (se 2 (by rfl) ⟨95901, by rfl⟩ : syracuseStep 255737 = 191803) B191803
theorem B452425 : Blo 175800 452425 := bstep (se 2 (by rfl) ⟨169659, by rfl⟩ : syracuseStep 452425 = 339319) B339319
theorem B321455 : Blo 175800 321455 := bstep (se 1 (by rfl) ⟨241091, by rfl⟩ : syracuseStep 321455 = 482183) B482183
theorem B223823 : Blo 175800 223823 := bstep (se 1 (by rfl) ⟨167867, by rfl⟩ : syracuseStep 223823 = 335735) B335735
theorem B453559 : Blo 175800 453559 := bstep (se 1 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 453559 = 680339) B680339
theorem B322579 : Blo 175800 322579 := bstep (se 1 (by rfl) ⟨241934, by rfl⟩ : syracuseStep 322579 = 483869) B483869
theorem B4418959 : Blo 175800 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B1142333 : Blo 175800 1142333 := bstep (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) B428375
theorem B2289239 : Blo 175800 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B225119 : Blo 175800 225119 := bstep (se 1 (by rfl) ⟨168839, by rfl⟩ : syracuseStep 225119 = 337679) B337679
theorem B683959 : Blo 175800 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B1273913 : Blo 175800 1273913 := bstep (se 2 (by rfl) ⟨477717, by rfl⟩ : syracuseStep 1273913 = 955435) B955435
theorem B455017 : Blo 175800 455017 := bstep (se 2 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 455017 = 341263) B341263
theorem B291689 : Blo 175800 291689 := bstep (se 2 (by rfl) ⟨109383, by rfl⟩ : syracuseStep 291689 = 218767) B218767
theorem B3339667 : Blo 175800 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B1340873 : Blo 175800 1340873 := bstep (se 2 (by rfl) ⟨502827, by rfl⟩ : syracuseStep 1340873 = 1005655) B1005655
theorem B2618825 : Blo 175800 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B194087 : Blo 175800 194087 := bstep (se 1 (by rfl) ⟨145565, by rfl⟩ : syracuseStep 194087 = 291131) B291131
theorem B1308221 : Blo 175800 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B19363697 : Blo 175800 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B1275841 : Blo 175800 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B8976541 : Blo 175800 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B2750851 : Blo 175800 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B4094509 : Blo 175800 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B359009 : Blo 175800 359009 := bstep (se 2 (by rfl) ⟨134628, by rfl⟩ : syracuseStep 359009 = 269257) B269257
theorem B7044569 : Blo 175800 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B425569 : Blo 175800 425569 := bstep (se 2 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 425569 = 319177) B319177
theorem B425915 : Blo 175800 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B851905 : Blo 175800 851905 := bstep (se 2 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 851905 = 638929) B638929
theorem B1048627 : Blo 175800 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B15728717 : Blo 175800 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B786779 : Blo 175800 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B1278611 : Blo 175800 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B197851 : Blo 175800 197851 := bstep (se 1 (by rfl) ⟨148388, by rfl⟩ : syracuseStep 197851 = 296777) B296777
theorem B198139 : Blo 175800 198139 := bstep (se 1 (by rfl) ⟨148604, by rfl⟩ : syracuseStep 198139 = 297209) B297209
theorem B755335 : Blo 175800 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B198319 : Blo 175800 198319 := bstep (se 1 (by rfl) ⟨148739, by rfl⟩ : syracuseStep 198319 = 297479) B297479
theorem B263915 : Blo 175800 263915 := bstep (se 1 (by rfl) ⟨197936, by rfl⟩ : syracuseStep 263915 = 395873) B395873
theorem B264143 : Blo 175800 264143 := bstep (se 1 (by rfl) ⟨198107, by rfl⟩ : syracuseStep 264143 = 396215) B396215
theorem B198607 : Blo 175800 198607 := bstep (se 1 (by rfl) ⟨148955, by rfl⟩ : syracuseStep 198607 = 297911) B297911
theorem B461065 : Blo 175800 461065 := bstep (se 2 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 461065 = 345799) B345799
theorem B1280285 : Blo 175800 1280285 := bstep (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) B480107
theorem B264539 : Blo 175800 264539 := bstep (se 1 (by rfl) ⟨198404, by rfl⟩ : syracuseStep 264539 = 396809) B396809
theorem B199003 : Blo 175800 199003 := bstep (se 1 (by rfl) ⟨149252, by rfl⟩ : syracuseStep 199003 = 298505) B298505
theorem B3541391 : Blo 175800 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B199111 : Blo 175800 199111 := bstep (se 1 (by rfl) ⟨149333, by rfl⟩ : syracuseStep 199111 = 298667) B298667
theorem B264767 : Blo 175800 264767 := bstep (se 1 (by rfl) ⟨198575, by rfl⟩ : syracuseStep 264767 = 397151) B397151
theorem B395855 : Blo 175800 395855 := bstep (se 1 (by rfl) ⟨296891, by rfl⟩ : syracuseStep 395855 = 593783) B593783
theorem B264887 : Blo 175800 264887 := bstep (se 1 (by rfl) ⟨198665, by rfl⟩ : syracuseStep 264887 = 397331) B397331
theorem B395999 : Blo 175800 395999 := bstep (se 1 (by rfl) ⟨296999, by rfl⟩ : syracuseStep 395999 = 593999) B593999
theorem B297695 : Blo 175800 297695 := bstep (se 1 (by rfl) ⟨223271, by rfl⟩ : syracuseStep 297695 = 446543) B446543
theorem B199471 : Blo 175800 199471 := bstep (se 1 (by rfl) ⟨149603, by rfl⟩ : syracuseStep 199471 = 299207) B299207
theorem B953207 : Blo 175800 953207 := bstep (se 1 (by rfl) ⟨714905, by rfl⟩ : syracuseStep 953207 = 1429811) B1429811
theorem B265115 : Blo 175800 265115 := bstep (se 1 (by rfl) ⟨198836, by rfl⟩ : syracuseStep 265115 = 397673) B397673
theorem B199579 : Blo 175800 199579 := bstep (se 1 (by rfl) ⟨149684, by rfl⟩ : syracuseStep 199579 = 299369) B299369
theorem B428971 : Blo 175800 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B396251 : Blo 175800 396251 := bstep (se 1 (by rfl) ⟨297188, by rfl⟩ : syracuseStep 396251 = 594377) B594377
theorem B396431 : Blo 175800 396431 := bstep (se 1 (by rfl) ⟨297323, by rfl⟩ : syracuseStep 396431 = 594647) B594647
theorem B298127 : Blo 175800 298127 := bstep (se 1 (by rfl) ⟨223595, by rfl⟩ : syracuseStep 298127 = 447191) B447191
theorem B396521 : Blo 175800 396521 := bstep (se 2 (by rfl) ⟨148695, by rfl⟩ : syracuseStep 396521 = 297391) B297391
theorem B396575 : Blo 175800 396575 := bstep (se 1 (by rfl) ⟨297431, by rfl⟩ : syracuseStep 396575 = 594863) B594863
theorem B265511 : Blo 175800 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B199975 : Blo 175800 199975 := bstep (se 1 (by rfl) ⟨149981, by rfl⟩ : syracuseStep 199975 = 299963) B299963
theorem B298279 : Blo 175800 298279 := bstep (se 1 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 298279 = 447419) B447419
theorem B200047 : Blo 175800 200047 := bstep (se 1 (by rfl) ⟨150035, by rfl⟩ : syracuseStep 200047 = 300071) B300071
theorem B298363 : Blo 175800 298363 := bstep (se 1 (by rfl) ⟨223772, by rfl⟩ : syracuseStep 298363 = 447545) B447545
theorem B265595 : Blo 175800 265595 := bstep (se 1 (by rfl) ⟨199196, by rfl⟩ : syracuseStep 265595 = 398393) B398393
theorem B593351 : Blo 175800 593351 := bstep (se 1 (by rfl) ⟨445013, by rfl⟩ : syracuseStep 593351 = 890027) B890027
theorem B265721 : Blo 175800 265721 := bstep (se 2 (by rfl) ⟨99645, by rfl⟩ : syracuseStep 265721 = 199291) B199291
theorem B200263 : Blo 175800 200263 := bstep (se 1 (by rfl) ⟨150197, by rfl⟩ : syracuseStep 200263 = 300395) B300395
theorem B265823 : Blo 175800 265823 := bstep (se 1 (by rfl) ⟨199367, by rfl⟩ : syracuseStep 265823 = 398735) B398735
theorem B396895 : Blo 175800 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B593675 : Blo 175800 593675 := bstep (se 1 (by rfl) ⟨445256, by rfl⟩ : syracuseStep 593675 = 890513) B890513
theorem B397097 : Blo 175800 397097 := bstep (se 2 (by rfl) ⟨148911, by rfl⟩ : syracuseStep 397097 = 297823) B297823
theorem B266039 : Blo 175800 266039 := bstep (se 1 (by rfl) ⟨199529, by rfl⟩ : syracuseStep 266039 = 399059) B399059
theorem B6983533 : Blo 175800 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B593945 : Blo 175800 593945 := bstep (se 2 (by rfl) ⟨222729, by rfl⟩ : syracuseStep 593945 = 445459) B445459
theorem B430105 : Blo 175800 430105 := bstep (se 2 (by rfl) ⟨161289, by rfl⟩ : syracuseStep 430105 = 322579) B322579
theorem B266345 : Blo 175800 266345 := bstep (se 2 (by rfl) ⟨99879, by rfl⟩ : syracuseStep 266345 = 199759) B199759
theorem B266663 : Blo 175800 266663 := bstep (se 1 (by rfl) ⟨199997, by rfl⟩ : syracuseStep 266663 = 399995) B399995
theorem B201127 : Blo 175800 201127 := bstep (se 1 (by rfl) ⟨150845, by rfl⟩ : syracuseStep 201127 = 301691) B301691
theorem B266747 : Blo 175800 266747 := bstep (se 1 (by rfl) ⟨200060, by rfl⟩ : syracuseStep 266747 = 400121) B400121
theorem B856673 : Blo 175800 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B266873 : Blo 175800 266873 := bstep (se 2 (by rfl) ⟨100077, by rfl⟩ : syracuseStep 266873 = 200155) B200155
theorem B725657 : Blo 175800 725657 := bstep (se 2 (by rfl) ⟨272121, by rfl⟩ : syracuseStep 725657 = 544243) B544243
theorem B266927 : Blo 175800 266927 := bstep (se 1 (by rfl) ⟨200195, by rfl⟩ : syracuseStep 266927 = 400391) B400391
theorem B266975 : Blo 175800 266975 := bstep (se 1 (by rfl) ⟨200231, by rfl⟩ : syracuseStep 266975 = 400463) B400463
theorem B1086251 : Blo 175800 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B398159 : Blo 175800 398159 := bstep (se 1 (by rfl) ⟨298619, by rfl⟩ : syracuseStep 398159 = 597239) B597239
theorem B299855 : Blo 175800 299855 := bstep (se 1 (by rfl) ⟨224891, by rfl⟩ : syracuseStep 299855 = 449783) B449783
theorem B267239 : Blo 175800 267239 := bstep (se 1 (by rfl) ⟨200429, by rfl⟩ : syracuseStep 267239 = 400859) B400859
theorem B201703 : Blo 175800 201703 := bstep (se 1 (by rfl) ⟨151277, by rfl⟩ : syracuseStep 201703 = 302555) B302555
theorem B398375 : Blo 175800 398375 := bstep (se 1 (by rfl) ⟨298781, by rfl⟩ : syracuseStep 398375 = 597563) B597563
theorem B2036825 : Blo 175800 2036825 := bstep (se 2 (by rfl) ⟨763809, by rfl⟩ : syracuseStep 2036825 = 1527619) B1527619
theorem B857213 : Blo 175800 857213 := bstep (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) B321455
theorem B398555 : Blo 175800 398555 := bstep (se 1 (by rfl) ⟨298916, by rfl⟩ : syracuseStep 398555 = 597833) B597833
theorem B267497 : Blo 175800 267497 := bstep (se 2 (by rfl) ⟨100311, by rfl⟩ : syracuseStep 267497 = 200623) B200623
theorem B595187 : Blo 175800 595187 := bstep (se 1 (by rfl) ⟨446390, by rfl⟩ : syracuseStep 595187 = 892781) B892781
theorem B267551 : Blo 175800 267551 := bstep (se 1 (by rfl) ⟨200663, by rfl⟩ : syracuseStep 267551 = 401327) B401327
theorem B595295 : Blo 175800 595295 := bstep (se 1 (by rfl) ⟨446471, by rfl⟩ : syracuseStep 595295 = 892943) B892943
theorem B398753 : Blo 175800 398753 := bstep (se 2 (by rfl) ⟨149532, by rfl⟩ : syracuseStep 398753 = 299065) B299065
theorem B2168257 : Blo 175800 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B267719 : Blo 175800 267719 := bstep (se 1 (by rfl) ⟨200789, by rfl⟩ : syracuseStep 267719 = 401579) B401579
theorem B1381835 : Blo 175800 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B202235 : Blo 175800 202235 := bstep (se 1 (by rfl) ⟨151676, by rfl⟩ : syracuseStep 202235 = 303353) B303353
theorem B268073 : Blo 175800 268073 := bstep (se 2 (by rfl) ⟨100527, by rfl⟩ : syracuseStep 268073 = 201055) B201055
theorem B300847 : Blo 175800 300847 := bstep (se 1 (by rfl) ⟨225635, by rfl⟩ : syracuseStep 300847 = 451271) B451271
theorem B268079 : Blo 175800 268079 := bstep (se 1 (by rfl) ⟨201059, by rfl⟩ : syracuseStep 268079 = 402119) B402119
theorem B399311 : Blo 175800 399311 := bstep (se 1 (by rfl) ⟨299483, by rfl⟩ : syracuseStep 399311 = 598967) B598967
theorem B1939535 : Blo 175800 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B268553 : Blo 175800 268553 := bstep (se 2 (by rfl) ⟨100707, by rfl⟩ : syracuseStep 268553 = 201415) B201415
theorem B891161 : Blo 175800 891161 := bstep (se 2 (by rfl) ⟨334185, by rfl⟩ : syracuseStep 891161 = 668371) B668371
theorem B11507993 : Blo 175800 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B399689 : Blo 175800 399689 := bstep (se 2 (by rfl) ⟨149883, by rfl⟩ : syracuseStep 399689 = 299767) B299767
theorem B399707 : Blo 175800 399707 := bstep (se 1 (by rfl) ⟨299780, by rfl⟩ : syracuseStep 399707 = 599561) B599561
theorem B268655 : Blo 175800 268655 := bstep (se 1 (by rfl) ⟨201491, by rfl⟩ : syracuseStep 268655 = 402983) B402983
theorem B268871 : Blo 175800 268871 := bstep (se 1 (by rfl) ⟨201653, by rfl⟩ : syracuseStep 268871 = 403307) B403307
theorem B268907 : Blo 175800 268907 := bstep (se 1 (by rfl) ⟨201680, by rfl⟩ : syracuseStep 268907 = 403361) B403361
theorem B3250925 : Blo 175800 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B269135 : Blo 175800 269135 := bstep (se 1 (by rfl) ⟨201851, by rfl⟩ : syracuseStep 269135 = 403703) B403703
theorem B596861 : Blo 175800 596861 := bstep (se 3 (by rfl) ⟨111911, by rfl⟩ : syracuseStep 596861 = 223823) B223823
theorem B400283 : Blo 175800 400283 := bstep (se 1 (by rfl) ⟨300212, by rfl⟩ : syracuseStep 400283 = 600425) B600425
theorem B334763 : Blo 175800 334763 := bstep (se 1 (by rfl) ⟨251072, by rfl⟩ : syracuseStep 334763 = 502145) B502145
theorem B400481 : Blo 175800 400481 := bstep (se 2 (by rfl) ⟨150180, by rfl⟩ : syracuseStep 400481 = 300361) B300361
theorem B597131 : Blo 175800 597131 := bstep (se 1 (by rfl) ⟨447848, by rfl⟩ : syracuseStep 597131 = 895697) B895697
theorem B334991 : Blo 175800 334991 := bstep (se 1 (by rfl) ⟨251243, by rfl⟩ : syracuseStep 334991 = 502487) B502487
theorem B269531 : Blo 175800 269531 := bstep (se 1 (by rfl) ⟨202148, by rfl⟩ : syracuseStep 269531 = 404297) B404297
theorem B859423 : Blo 175800 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B400679 : Blo 175800 400679 := bstep (se 1 (by rfl) ⟨300509, by rfl⟩ : syracuseStep 400679 = 601019) B601019
theorem B859673 : Blo 175800 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B401057 : Blo 175800 401057 := bstep (se 2 (by rfl) ⟨150396, by rfl⟩ : syracuseStep 401057 = 300793) B300793
theorem B761555 : Blo 175800 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B401417 : Blo 175800 401417 := bstep (se 2 (by rfl) ⟨150531, by rfl⟩ : syracuseStep 401417 = 301063) B301063
theorem B4301009 : Blo 175800 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B11968721 : Blo 175800 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B401831 : Blo 175800 401831 := bstep (se 1 (by rfl) ⟨301373, by rfl⟩ : syracuseStep 401831 = 602747) B602747
theorem B401939 : Blo 175800 401939 := bstep (se 1 (by rfl) ⟨301454, by rfl⟩ : syracuseStep 401939 = 602909) B602909
theorem B401993 : Blo 175800 401993 := bstep (se 2 (by rfl) ⟨150747, by rfl⟩ : syracuseStep 401993 = 301495) B301495
theorem B270955 : Blo 175800 270955 := bstep (se 1 (by rfl) ⟨203216, by rfl⟩ : syracuseStep 270955 = 406433) B406433
theorem B5120657 : Blo 175800 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B598751 : Blo 175800 598751 := bstep (se 1 (by rfl) ⟨449063, by rfl⟩ : syracuseStep 598751 = 898127) B898127
theorem B3089335 : Blo 175800 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B1516481 : Blo 175800 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B893915 : Blo 175800 893915 := bstep (se 1 (by rfl) ⟨670436, by rfl⟩ : syracuseStep 893915 = 1340873) B1340873
theorem B402407 : Blo 175800 402407 := bstep (se 1 (by rfl) ⟨301805, by rfl⟩ : syracuseStep 402407 = 603611) B603611
theorem B894077 : Blo 175800 894077 := bstep (se 3 (by rfl) ⟨167639, by rfl⟩ : syracuseStep 894077 = 335279) B335279
theorem B599183 : Blo 175800 599183 := bstep (se 1 (by rfl) ⟨449387, by rfl⟩ : syracuseStep 599183 = 898775) B898775
theorem B402785 : Blo 175800 402785 := bstep (se 2 (by rfl) ⟨151044, by rfl⟩ : syracuseStep 402785 = 302089) B302089
theorem B402875 : Blo 175800 402875 := bstep (se 1 (by rfl) ⟨302156, by rfl⟩ : syracuseStep 402875 = 604313) B604313
theorem B894401 : Blo 175800 894401 := bstep (se 2 (by rfl) ⟨335400, by rfl⟩ : syracuseStep 894401 = 670801) B670801
theorem B403001 : Blo 175800 403001 := bstep (se 2 (by rfl) ⟨151125, by rfl⟩ : syracuseStep 403001 = 302251) B302251
theorem B2827997 : Blo 175800 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B239339 : Blo 175800 239339 := bstep (se 1 (by rfl) ⟨179504, by rfl⟩ : syracuseStep 239339 = 359009) B359009
theorem B567425 : Blo 175800 567425 := bstep (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) B425569
theorem B403667 : Blo 175800 403667 := bstep (se 1 (by rfl) ⟨302750, by rfl⟩ : syracuseStep 403667 = 605501) B605501
theorem B600317 : Blo 175800 600317 := bstep (se 3 (by rfl) ⟨112559, by rfl⟩ : syracuseStep 600317 = 225119) B225119
theorem B403721 : Blo 175800 403721 := bstep (se 2 (by rfl) ⟨151395, by rfl⟩ : syracuseStep 403721 = 302791) B302791
theorem B4696379 : Blo 175800 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B1911251 : Blo 175800 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B403937 : Blo 175800 403937 := bstep (se 2 (by rfl) ⟨151476, by rfl⟩ : syracuseStep 403937 = 302953) B302953
theorem B273079 : Blo 175800 273079 := bstep (se 1 (by rfl) ⟨204809, by rfl⟩ : syracuseStep 273079 = 409619) B409619
theorem B404243 : Blo 175800 404243 := bstep (se 1 (by rfl) ⟨303182, by rfl⟩ : syracuseStep 404243 = 606365) B606365
theorem B863131 : Blo 175800 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B601127 : Blo 175800 601127 := bstep (se 1 (by rfl) ⟨450845, by rfl⟩ : syracuseStep 601127 = 901691) B901691
theorem B3845339 : Blo 175800 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B961853 : Blo 175800 961853 := bstep (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) B360695
theorem B601559 : Blo 175800 601559 := bstep (se 1 (by rfl) ⟨451169, by rfl⟩ : syracuseStep 601559 = 902339) B902339
theorem B634463 : Blo 175800 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B175839 : Blo 175800 175839 := bstep (se 1 (by rfl) ⟨131879, by rfl⟩ : syracuseStep 175839 = 263759) B263759
theorem B175919 : Blo 175800 175919 := bstep (se 1 (by rfl) ⟨131939, by rfl⟩ : syracuseStep 175919 = 263879) B263879
theorem B3026807 : Blo 175800 3026807 := bstep (se 1 (by rfl) ⟨2270105, by rfl⟩ : syracuseStep 3026807 = 4540211) B4540211
theorem B176027 : Blo 175800 176027 := bstep (se 1 (by rfl) ⟨132020, by rfl⟩ : syracuseStep 176027 = 264041) B264041
theorem B176079 : Blo 175800 176079 := bstep (se 1 (by rfl) ⟨132059, by rfl⟩ : syracuseStep 176079 = 264119) B264119
theorem B176103 : Blo 175800 176103 := bstep (se 1 (by rfl) ⟨132077, by rfl⟩ : syracuseStep 176103 = 264155) B264155
theorem B667673 : Blo 175800 667673 := bstep (se 2 (by rfl) ⟨250377, by rfl⟩ : syracuseStep 667673 = 500755) B500755
theorem B176415 : Blo 175800 176415 := bstep (se 1 (by rfl) ⟨132311, by rfl⟩ : syracuseStep 176415 = 264623) B264623
theorem B176475 : Blo 175800 176475 := bstep (se 1 (by rfl) ⟨132356, by rfl⟩ : syracuseStep 176475 = 264713) B264713
theorem B176495 : Blo 175800 176495 := bstep (se 1 (by rfl) ⟨132371, by rfl⟩ : syracuseStep 176495 = 264743) B264743
theorem B176551 : Blo 175800 176551 := bstep (se 1 (by rfl) ⟨132413, by rfl⟩ : syracuseStep 176551 = 264827) B264827
theorem B176635 : Blo 175800 176635 := bstep (se 1 (by rfl) ⟨132476, by rfl⟩ : syracuseStep 176635 = 264953) B264953
theorem B176703 : Blo 175800 176703 := bstep (se 1 (by rfl) ⟨132527, by rfl⟩ : syracuseStep 176703 = 265055) B265055
theorem B176711 : Blo 175800 176711 := bstep (se 1 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 176711 = 265067) B265067
theorem B176863 : Blo 175800 176863 := bstep (se 1 (by rfl) ⟨132647, by rfl⟩ : syracuseStep 176863 = 265295) B265295
theorem B1618717 : Blo 175800 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B176943 : Blo 175800 176943 := bstep (se 1 (by rfl) ⟨132707, by rfl⟩ : syracuseStep 176943 = 265415) B265415
theorem B308047 : Blo 175800 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B177051 : Blo 175800 177051 := bstep (se 1 (by rfl) ⟨132788, by rfl⟩ : syracuseStep 177051 = 265577) B265577
theorem B1160101 : Blo 175800 1160101 := bstep (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) B217519
theorem B177103 : Blo 175800 177103 := bstep (se 1 (by rfl) ⟨132827, by rfl⟩ : syracuseStep 177103 = 265655) B265655
theorem B177127 : Blo 175800 177127 := bstep (se 1 (by rfl) ⟨132845, by rfl⟩ : syracuseStep 177127 = 265691) B265691
theorem B603233 : Blo 175800 603233 := bstep (se 2 (by rfl) ⟨226212, by rfl⟩ : syracuseStep 603233 = 452425) B452425
theorem B1717393 : Blo 175800 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B1520855 : Blo 175800 1520855 := bstep (se 1 (by rfl) ⟨1140641, by rfl⟩ : syracuseStep 1520855 = 2281283) B2281283
theorem B177439 : Blo 175800 177439 := bstep (se 1 (by rfl) ⟨133079, by rfl⟩ : syracuseStep 177439 = 266159) B266159
theorem B177499 : Blo 175800 177499 := bstep (se 1 (by rfl) ⟨133124, by rfl⟩ : syracuseStep 177499 = 266249) B266249
theorem B177519 : Blo 175800 177519 := bstep (se 1 (by rfl) ⟨133139, by rfl⟩ : syracuseStep 177519 = 266279) B266279
theorem B177575 : Blo 175800 177575 := bstep (se 1 (by rfl) ⟨133181, by rfl⟩ : syracuseStep 177575 = 266363) B266363
theorem B177659 : Blo 175800 177659 := bstep (se 1 (by rfl) ⟨133244, by rfl⟩ : syracuseStep 177659 = 266489) B266489
theorem B243263 : Blo 175800 243263 := bstep (se 1 (by rfl) ⟨182447, by rfl⟩ : syracuseStep 243263 = 364895) B364895
theorem B177727 : Blo 175800 177727 := bstep (se 1 (by rfl) ⟨133295, by rfl⟩ : syracuseStep 177727 = 266591) B266591
theorem B177735 : Blo 175800 177735 := bstep (se 1 (by rfl) ⟨133301, by rfl⟩ : syracuseStep 177735 = 266603) B266603
theorem B177887 : Blo 175800 177887 := bstep (se 1 (by rfl) ⟨133415, by rfl⟩ : syracuseStep 177887 = 266831) B266831
theorem B177967 : Blo 175800 177967 := bstep (se 1 (by rfl) ⟨133475, by rfl⟩ : syracuseStep 177967 = 266951) B266951
theorem B178075 : Blo 175800 178075 := bstep (se 1 (by rfl) ⟨133556, by rfl⟩ : syracuseStep 178075 = 267113) B267113
theorem B669647 : Blo 175800 669647 := bstep (se 1 (by rfl) ⟨502235, by rfl⟩ : syracuseStep 669647 = 1004471) B1004471
theorem B178127 : Blo 175800 178127 := bstep (se 1 (by rfl) ⟨133595, by rfl⟩ : syracuseStep 178127 = 267191) B267191
theorem B178151 : Blo 175800 178151 := bstep (se 1 (by rfl) ⟨133613, by rfl⟩ : syracuseStep 178151 = 267227) B267227
theorem B178463 : Blo 175800 178463 := bstep (se 1 (by rfl) ⟨133847, by rfl⟩ : syracuseStep 178463 = 267695) B267695
theorem B178523 : Blo 175800 178523 := bstep (se 1 (by rfl) ⟨133892, by rfl⟩ : syracuseStep 178523 = 267785) B267785
theorem B178543 : Blo 175800 178543 := bstep (se 1 (by rfl) ⟨133907, by rfl⟩ : syracuseStep 178543 = 267815) B267815
theorem B178599 : Blo 175800 178599 := bstep (se 1 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 178599 = 267899) B267899
theorem B604583 : Blo 175800 604583 := bstep (se 1 (by rfl) ⟨453437, by rfl⟩ : syracuseStep 604583 = 906875) B906875
theorem B178683 : Blo 175800 178683 := bstep (se 1 (by rfl) ⟨134012, by rfl⟩ : syracuseStep 178683 = 268025) B268025
theorem B178751 : Blo 175800 178751 := bstep (se 1 (by rfl) ⟨134063, by rfl⟩ : syracuseStep 178751 = 268127) B268127
theorem B178759 : Blo 175800 178759 := bstep (se 1 (by rfl) ⟨134069, by rfl⟩ : syracuseStep 178759 = 268139) B268139
theorem B604745 : Blo 175800 604745 := bstep (se 2 (by rfl) ⟨226779, by rfl⟩ : syracuseStep 604745 = 453559) B453559
theorem B670315 : Blo 175800 670315 := bstep (se 1 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 670315 = 1005473) B1005473
theorem B211631 : Blo 175800 211631 := bstep (se 1 (by rfl) ⟨158723, by rfl⟩ : syracuseStep 211631 = 317447) B317447
theorem B178911 : Blo 175800 178911 := bstep (se 1 (by rfl) ⟨134183, by rfl⟩ : syracuseStep 178911 = 268367) B268367
theorem B178991 : Blo 175800 178991 := bstep (se 1 (by rfl) ⟨134243, by rfl⟩ : syracuseStep 178991 = 268487) B268487
theorem B670589 : Blo 175800 670589 := bstep (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) B251471
theorem B670619 : Blo 175800 670619 := bstep (se 1 (by rfl) ⟨502964, by rfl⟩ : syracuseStep 670619 = 1005929) B1005929
theorem B179099 : Blo 175800 179099 := bstep (se 1 (by rfl) ⟨134324, by rfl⟩ : syracuseStep 179099 = 268649) B268649
theorem B179151 : Blo 175800 179151 := bstep (se 1 (by rfl) ⟨134363, by rfl⟩ : syracuseStep 179151 = 268727) B268727
theorem B179175 : Blo 175800 179175 := bstep (se 1 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 179175 = 268763) B268763
theorem B605171 : Blo 175800 605171 := bstep (se 1 (by rfl) ⟨453878, by rfl⟩ : syracuseStep 605171 = 907757) B907757
theorem B539635 : Blo 175800 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B179487 : Blo 175800 179487 := bstep (se 1 (by rfl) ⟨134615, by rfl⟩ : syracuseStep 179487 = 269231) B269231
theorem B179547 : Blo 175800 179547 := bstep (se 1 (by rfl) ⟨134660, by rfl⟩ : syracuseStep 179547 = 269321) B269321
theorem B179567 : Blo 175800 179567 := bstep (se 1 (by rfl) ⟨134675, by rfl⟩ : syracuseStep 179567 = 269351) B269351
theorem B179623 : Blo 175800 179623 := bstep (se 1 (by rfl) ⟨134717, by rfl⟩ : syracuseStep 179623 = 269435) B269435
theorem B179707 : Blo 175800 179707 := bstep (se 1 (by rfl) ⟨134780, by rfl⟩ : syracuseStep 179707 = 269561) B269561
theorem B179775 : Blo 175800 179775 := bstep (se 1 (by rfl) ⟨134831, by rfl⟩ : syracuseStep 179775 = 269663) B269663
theorem B179783 : Blo 175800 179783 := bstep (se 1 (by rfl) ⟨134837, by rfl⟩ : syracuseStep 179783 = 269675) B269675
theorem B507475 : Blo 175800 507475 := bstep (se 1 (by rfl) ⟨380606, by rfl⟩ : syracuseStep 507475 = 761213) B761213
theorem B1916531 : Blo 175800 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B606419 : Blo 175800 606419 := bstep (se 1 (by rfl) ⟨454814, by rfl⟩ : syracuseStep 606419 = 909629) B909629
theorem B606689 : Blo 175800 606689 := bstep (se 2 (by rfl) ⟨227508, by rfl⟩ : syracuseStep 606689 = 455017) B455017
theorem B869063 : Blo 175800 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B1721033 : Blo 175800 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B508751 : Blo 175800 508751 := bstep (se 1 (by rfl) ⟨381563, by rfl⟩ : syracuseStep 508751 = 763127) B763127
theorem B3621827 : Blo 175800 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B672731 : Blo 175800 672731 := bstep (se 1 (by rfl) ⟨504548, by rfl⟩ : syracuseStep 672731 = 1009097) B1009097
theorem B574589 : Blo 175800 574589 := bstep (se 3 (by rfl) ⟨107735, by rfl⟩ : syracuseStep 574589 = 215471) B215471
theorem B640199 : Blo 175800 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B509161 : Blo 175800 509161 := bstep (se 2 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 509161 = 381871) B381871
theorem B902663 : Blo 175800 902663 := bstep (se 1 (by rfl) ⟨676997, by rfl⟩ : syracuseStep 902663 = 1353995) B1353995
theorem B903149 : Blo 175800 903149 := bstep (se 3 (by rfl) ⟨169340, by rfl⟩ : syracuseStep 903149 = 338681) B338681
theorem B1526159 : Blo 175800 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B510391 : Blo 175800 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B903635 : Blo 175800 903635 := bstep (se 1 (by rfl) ⟨677726, by rfl⟩ : syracuseStep 903635 = 1355453) B1355453
theorem B379513 : Blo 175800 379513 := bstep (se 2 (by rfl) ⟨142317, by rfl⟩ : syracuseStep 379513 = 284635) B284635
theorem B379667 : Blo 175800 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B903959 : Blo 175800 903959 := bstep (se 1 (by rfl) ⟨677969, by rfl⟩ : syracuseStep 903959 = 1355939) B1355939
theorem B5459345 : Blo 175800 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B445895 : Blo 175800 445895 := bstep (se 1 (by rfl) ⟨334421, by rfl⟩ : syracuseStep 445895 = 668843) B668843
theorem B445945 : Blo 175800 445945 := bstep (se 2 (by rfl) ⟨167229, by rfl⟩ : syracuseStep 445945 = 334459) B334459
theorem B1429001 : Blo 175800 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B872147 : Blo 175800 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B446249 : Blo 175800 446249 := bstep (se 2 (by rfl) ⟨167343, by rfl⟩ : syracuseStep 446249 = 334687) B334687
theorem B643081 : Blo 175800 643081 := bstep (se 2 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 643081 = 482311) B482311
theorem B446593 : Blo 175800 446593 := bstep (se 2 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 446593 = 334945) B334945
theorem B905579 : Blo 175800 905579 := bstep (se 1 (by rfl) ⟨679184, by rfl⟩ : syracuseStep 905579 = 1358369) B1358369
theorem B250543 : Blo 175800 250543 := bstep (se 1 (by rfl) ⟨187907, by rfl⟩ : syracuseStep 250543 = 375815) B375815
theorem B1626923 : Blo 175800 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B447403 : Blo 175800 447403 := bstep (se 1 (by rfl) ⟨335552, by rfl⟩ : syracuseStep 447403 = 671105) B671105
theorem B381991 : Blo 175800 381991 := bstep (se 1 (by rfl) ⟨286493, by rfl⟩ : syracuseStep 381991 = 572987) B572987
theorem B447707 : Blo 175800 447707 := bstep (se 1 (by rfl) ⟨335780, by rfl⟩ : syracuseStep 447707 = 671561) B671561
theorem B382171 : Blo 175800 382171 := bstep (se 1 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 382171 = 573257) B573257
theorem B1135873 : Blo 175800 1135873 := bstep (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) B851905
theorem B283943 : Blo 175800 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B382247 : Blo 175800 382247 := bstep (se 1 (by rfl) ⟨286685, by rfl⟩ : syracuseStep 382247 = 573371) B573371
theorem B447839 : Blo 175800 447839 := bstep (se 1 (by rfl) ⟨335879, by rfl⟩ : syracuseStep 447839 = 671759) B671759
theorem B480863 : Blo 175800 480863 := bstep (se 1 (by rfl) ⟨360647, by rfl⟩ : syracuseStep 480863 = 721295) B721295
theorem B14636771 : Blo 175800 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B907037 : Blo 175800 907037 := bstep (se 3 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 907037 = 340139) B340139
theorem B481231 : Blo 175800 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B448537 : Blo 175800 448537 := bstep (se 2 (by rfl) ⟨168201, by rfl⟩ : syracuseStep 448537 = 336403) B336403
theorem B448841 : Blo 175800 448841 := bstep (se 2 (by rfl) ⟨168315, by rfl⟩ : syracuseStep 448841 = 336631) B336631
theorem B776591 : Blo 175800 776591 := bstep (se 1 (by rfl) ⟨582443, by rfl⟩ : syracuseStep 776591 = 1164887) B1164887
theorem B678395 : Blo 175800 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B383887 : Blo 175800 383887 := bstep (se 1 (by rfl) ⟨287915, by rfl⟩ : syracuseStep 383887 = 575831) B575831
theorem B1924013 : Blo 175800 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B1629233 : Blo 175800 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B5790937 : Blo 175800 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B679367 : Blo 175800 679367 := bstep (se 1 (by rfl) ⟨509525, by rfl⟩ : syracuseStep 679367 = 1019051) B1019051
theorem B483695 : Blo 175800 483695 := bstep (se 1 (by rfl) ⟨362771, by rfl⟩ : syracuseStep 483695 = 725543) B725543
theorem B287659 : Blo 175800 287659 := bstep (se 1 (by rfl) ⟨215744, by rfl⟩ : syracuseStep 287659 = 431489) B431489
theorem B189415 : Blo 175800 189415 := bstep (se 1 (by rfl) ⟨142061, by rfl⟩ : syracuseStep 189415 = 284123) B284123
theorem B320503 : Blo 175800 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B451727 : Blo 175800 451727 := bstep (se 1 (by rfl) ⟨338795, by rfl⟩ : syracuseStep 451727 = 677591) B677591
theorem B2254067 : Blo 175800 2254067 := bstep (se 1 (by rfl) ⟨1690550, by rfl⟩ : syracuseStep 2254067 = 3381101) B3381101
theorem B681311 : Blo 175800 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B517565 : Blo 175800 517565 := bstep (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) B194087
theorem B681479 : Blo 175800 681479 := bstep (se 1 (by rfl) ⟨511109, by rfl⟩ : syracuseStep 681479 = 1022219) B1022219
theorem B255583 : Blo 175800 255583 := bstep (se 1 (by rfl) ⟨191687, by rfl⟩ : syracuseStep 255583 = 383375) B383375
theorem B2025161 : Blo 175800 2025161 := bstep (se 2 (by rfl) ⟨759435, by rfl⟩ : syracuseStep 2025161 = 1518871) B1518871
theorem B5891945 : Blo 175800 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B681965 : Blo 175800 681965 := bstep (se 3 (by rfl) ⟨127868, by rfl⟩ : syracuseStep 681965 = 255737) B255737
theorem B682451 : Blo 175800 682451 := bstep (se 1 (by rfl) ⟨511838, by rfl⟩ : syracuseStep 682451 = 1023677) B1023677
theorem B911945 : Blo 175800 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B453671 : Blo 175800 453671 := bstep (se 1 (by rfl) ⟨340253, by rfl⟩ : syracuseStep 453671 = 680507) B680507
theorem B224623 : Blo 175800 224623 := bstep (se 1 (by rfl) ⟨168467, by rfl⟩ : syracuseStep 224623 = 336935) B336935
theorem B454025 : Blo 175800 454025 := bstep (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) B340519
theorem B323155 : Blo 175800 323155 := bstep (se 1 (by rfl) ⟨242366, by rfl⟩ : syracuseStep 323155 = 484733) B484733
theorem B225499 : Blo 175800 225499 := bstep (se 1 (by rfl) ⟨169124, by rfl⟩ : syracuseStep 225499 = 338249) B338249
theorem B1208591 : Blo 175800 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B4452889 : Blo 175800 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B2028077 : Blo 175800 2028077 := bstep (se 3 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 2028077 = 760529) B760529
theorem B3469873 : Blo 175800 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B1930027 : Blo 175800 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B1504109 : Blo 175800 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B1701121 : Blo 175800 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B849275 : Blo 175800 849275 := bstep (se 1 (by rfl) ⟨636956, by rfl⟩ : syracuseStep 849275 = 1273913) B1273913
theorem B35452673 : Blo 175800 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B227119 : Blo 175800 227119 := bstep (se 1 (by rfl) ⟨170339, by rfl⟩ : syracuseStep 227119 = 340679) B340679
theorem B358199 : Blo 175800 358199 := bstep (se 1 (by rfl) ⟨268649, by rfl⟩ : syracuseStep 358199 = 537299) B537299
theorem B3667801 : Blo 175800 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B194459 : Blo 175800 194459 := bstep (se 1 (by rfl) ⟨145844, by rfl⟩ : syracuseStep 194459 = 291689) B291689
theorem B2587085 : Blo 175800 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B457289 : Blo 175800 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B12909131 : Blo 175800 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B1146383 : Blo 175800 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B10485811 : Blo 175800 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B524519 : Blo 175800 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B852407 : Blo 175800 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B1147355 : Blo 175800 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B426799 : Blo 175800 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B361273 : Blo 175800 361273 := bstep (se 2 (by rfl) ⟨135477, by rfl⟩ : syracuseStep 361273 = 270955) B270955
theorem B427337 : Blo 175800 427337 := bstep (se 2 (by rfl) ⟨160251, by rfl⟩ : syracuseStep 427337 = 320503) B320503
theorem B853523 : Blo 175800 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B2360927 : Blo 175800 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B263801 : Blo 175800 263801 := bstep (se 2 (by rfl) ⟨98925, by rfl⟩ : syracuseStep 263801 = 197851) B197851
theorem B263903 : Blo 175800 263903 := bstep (se 1 (by rfl) ⟨197927, by rfl⟩ : syracuseStep 263903 = 395855) B395855
theorem B1935085 : Blo 175800 1935085 := bstep (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) B725657
theorem B198463 : Blo 175800 198463 := bstep (se 1 (by rfl) ⟨148847, by rfl⟩ : syracuseStep 198463 = 297695) B297695
theorem B263999 : Blo 175800 263999 := bstep (se 1 (by rfl) ⟨197999, by rfl⟩ : syracuseStep 263999 = 395999) B395999
theorem B264167 : Blo 175800 264167 := bstep (se 1 (by rfl) ⟨198125, by rfl⟩ : syracuseStep 264167 = 396251) B396251
theorem B264185 : Blo 175800 264185 := bstep (se 2 (by rfl) ⟨99069, by rfl⟩ : syracuseStep 264185 = 198139) B198139
theorem B264287 : Blo 175800 264287 := bstep (se 1 (by rfl) ⟨198215, by rfl⟩ : syracuseStep 264287 = 396431) B396431
theorem B198751 : Blo 175800 198751 := bstep (se 1 (by rfl) ⟨149063, by rfl⟩ : syracuseStep 198751 = 298127) B298127
theorem B264347 : Blo 175800 264347 := bstep (se 1 (by rfl) ⟨198260, by rfl⟩ : syracuseStep 264347 = 396521) B396521
theorem B264383 : Blo 175800 264383 := bstep (se 1 (by rfl) ⟨198287, by rfl⟩ : syracuseStep 264383 = 396575) B396575
theorem B264425 : Blo 175800 264425 := bstep (se 2 (by rfl) ⟨99159, by rfl⟩ : syracuseStep 264425 = 198319) B198319
theorem B3639563 : Blo 175800 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B395567 : Blo 175800 395567 := bstep (se 1 (by rfl) ⟨296675, by rfl⟩ : syracuseStep 395567 = 593351) B593351
theorem B297263 : Blo 175800 297263 := bstep (se 1 (by rfl) ⟨222947, by rfl⟩ : syracuseStep 297263 = 445895) B445895
theorem B952667 : Blo 175800 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B395783 : Blo 175800 395783 := bstep (se 1 (by rfl) ⟨296837, by rfl⟩ : syracuseStep 395783 = 593675) B593675
theorem B297499 : Blo 175800 297499 := bstep (se 1 (by rfl) ⟨223124, by rfl⟩ : syracuseStep 297499 = 446249) B446249
theorem B264731 : Blo 175800 264731 := bstep (se 1 (by rfl) ⟨198548, by rfl⟩ : syracuseStep 264731 = 397097) B397097
theorem B264809 : Blo 175800 264809 := bstep (se 2 (by rfl) ⟨99303, by rfl⟩ : syracuseStep 264809 = 198607) B198607
theorem B395963 : Blo 175800 395963 := bstep (se 1 (by rfl) ⟨296972, by rfl⟩ : syracuseStep 395963 = 593945) B593945
theorem B36637717 : Blo 175800 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B265337 : Blo 175800 265337 := bstep (se 2 (by rfl) ⟨99501, by rfl⟩ : syracuseStep 265337 = 199003) B199003
theorem B265439 : Blo 175800 265439 := bstep (se 1 (by rfl) ⟨199079, by rfl⟩ : syracuseStep 265439 = 398159) B398159
theorem B199903 : Blo 175800 199903 := bstep (se 1 (by rfl) ⟨149927, by rfl⟩ : syracuseStep 199903 = 299855) B299855
theorem B265481 : Blo 175800 265481 := bstep (se 2 (by rfl) ⟨99555, by rfl⟩ : syracuseStep 265481 = 199111) B199111
theorem B265583 : Blo 175800 265583 := bstep (se 1 (by rfl) ⟨199187, by rfl⟩ : syracuseStep 265583 = 398375) B398375
theorem B757181 : Blo 175800 757181 := bstep (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) B283943
theorem B298471 : Blo 175800 298471 := bstep (se 1 (by rfl) ⟨223853, by rfl⟩ : syracuseStep 298471 = 447707) B447707
theorem B265703 : Blo 175800 265703 := bstep (se 1 (by rfl) ⟨199277, by rfl⟩ : syracuseStep 265703 = 398555) B398555
theorem B396791 : Blo 175800 396791 := bstep (se 1 (by rfl) ⟨297593, by rfl⟩ : syracuseStep 396791 = 595187) B595187
theorem B396863 : Blo 175800 396863 := bstep (se 1 (by rfl) ⟨297647, by rfl⟩ : syracuseStep 396863 = 595295) B595295
theorem B298559 : Blo 175800 298559 := bstep (se 1 (by rfl) ⟨223919, by rfl⟩ : syracuseStep 298559 = 447839) B447839
theorem B364105 : Blo 175800 364105 := bstep (se 2 (by rfl) ⟨136539, by rfl⟩ : syracuseStep 364105 = 273079) B273079
theorem B265835 : Blo 175800 265835 := bstep (se 1 (by rfl) ⟨199376, by rfl⟩ : syracuseStep 265835 = 398753) B398753
theorem B921223 : Blo 175800 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B265961 : Blo 175800 265961 := bstep (se 2 (by rfl) ⟨99735, by rfl⟩ : syracuseStep 265961 = 199471) B199471
theorem B266105 : Blo 175800 266105 := bstep (se 2 (by rfl) ⟨99789, by rfl⟩ : syracuseStep 266105 = 199579) B199579
theorem B1150841 : Blo 175800 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B266207 : Blo 175800 266207 := bstep (se 1 (by rfl) ⟨199655, by rfl⟩ : syracuseStep 266207 = 399311) B399311
theorem B594107 : Blo 175800 594107 := bstep (se 1 (by rfl) ⟨445580, by rfl⟩ : syracuseStep 594107 = 891161) B891161
theorem B7671995 : Blo 175800 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B299227 : Blo 175800 299227 := bstep (se 1 (by rfl) ⟨224420, by rfl⟩ : syracuseStep 299227 = 448841) B448841
theorem B266459 : Blo 175800 266459 := bstep (se 1 (by rfl) ⟨199844, by rfl⟩ : syracuseStep 266459 = 399689) B399689
theorem B266471 : Blo 175800 266471 := bstep (se 1 (by rfl) ⟨199853, by rfl⟩ : syracuseStep 266471 = 399707) B399707
theorem B1282301 : Blo 175800 1282301 := bstep (se 3 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 1282301 = 480863) B480863
theorem B266633 : Blo 175800 266633 := bstep (se 2 (by rfl) ⟨99987, by rfl⟩ : syracuseStep 266633 = 199975) B199975
theorem B299497 : Blo 175800 299497 := bstep (se 2 (by rfl) ⟨112311, by rfl⟩ : syracuseStep 299497 = 224623) B224623
theorem B266729 : Blo 175800 266729 := bstep (se 2 (by rfl) ⟨100023, by rfl⟩ : syracuseStep 266729 = 200047) B200047
theorem B2167283 : Blo 175800 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B397817 : Blo 175800 397817 := bstep (se 2 (by rfl) ⟨149181, by rfl⟩ : syracuseStep 397817 = 298363) B298363
theorem B397907 : Blo 175800 397907 := bstep (se 1 (by rfl) ⟨298430, by rfl⟩ : syracuseStep 397907 = 596861) B596861
theorem B266855 : Blo 175800 266855 := bstep (se 1 (by rfl) ⟨200141, by rfl⟩ : syracuseStep 266855 = 400283) B400283
theorem B594593 : Blo 175800 594593 := bstep (se 2 (by rfl) ⟨222972, by rfl⟩ : syracuseStep 594593 = 445945) B445945
theorem B1086155 : Blo 175800 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B266987 : Blo 175800 266987 := bstep (se 1 (by rfl) ⟨200240, by rfl⟩ : syracuseStep 266987 = 400481) B400481
theorem B398087 : Blo 175800 398087 := bstep (se 1 (by rfl) ⟨298565, by rfl⟩ : syracuseStep 398087 = 597131) B597131
theorem B267017 : Blo 175800 267017 := bstep (se 2 (by rfl) ⟨100131, by rfl⟩ : syracuseStep 267017 = 200263) B200263
theorem B529193 : Blo 175800 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B267119 : Blo 175800 267119 := bstep (se 1 (by rfl) ⟨200339, by rfl⟩ : syracuseStep 267119 = 400679) B400679
theorem B267371 : Blo 175800 267371 := bstep (se 1 (by rfl) ⟨200528, by rfl⟩ : syracuseStep 267371 = 401057) B401057
theorem B9311377 : Blo 175800 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B267611 : Blo 175800 267611 := bstep (se 1 (by rfl) ⟨200708, by rfl⟩ : syracuseStep 267611 = 401417) B401417
theorem B857441 : Blo 175800 857441 := bstep (se 2 (by rfl) ⟨321540, by rfl⟩ : syracuseStep 857441 = 643081) B643081
theorem B595457 : Blo 175800 595457 := bstep (se 2 (by rfl) ⟨223296, by rfl⟩ : syracuseStep 595457 = 446593) B446593
theorem B267887 : Blo 175800 267887 := bstep (se 1 (by rfl) ⟨200915, by rfl⟩ : syracuseStep 267887 = 401831) B401831
theorem B300665 : Blo 175800 300665 := bstep (se 2 (by rfl) ⟨112749, by rfl⟩ : syracuseStep 300665 = 225499) B225499
theorem B267959 : Blo 175800 267959 := bstep (se 1 (by rfl) ⟨200969, by rfl⟩ : syracuseStep 267959 = 401939) B401939
theorem B267995 : Blo 175800 267995 := bstep (se 1 (by rfl) ⟨200996, by rfl⟩ : syracuseStep 267995 = 401993) B401993
theorem B3413771 : Blo 175800 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B399167 : Blo 175800 399167 := bstep (se 1 (by rfl) ⟨299375, by rfl⟩ : syracuseStep 399167 = 598751) B598751
theorem B268169 : Blo 175800 268169 := bstep (se 2 (by rfl) ⟨100563, by rfl⟩ : syracuseStep 268169 = 201127) B201127
theorem B595943 : Blo 175800 595943 := bstep (se 1 (by rfl) ⟨446957, by rfl⟩ : syracuseStep 595943 = 893915) B893915
theorem B268271 : Blo 175800 268271 := bstep (se 1 (by rfl) ⟨201203, by rfl⟩ : syracuseStep 268271 = 402407) B402407
theorem B5937185 : Blo 175800 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B4626497 : Blo 175800 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B596051 : Blo 175800 596051 := bstep (se 1 (by rfl) ⟨447038, by rfl⟩ : syracuseStep 596051 = 894077) B894077
theorem B399455 : Blo 175800 399455 := bstep (se 1 (by rfl) ⟨299591, by rfl⟩ : syracuseStep 399455 = 599183) B599183
theorem B301151 : Blo 175800 301151 := bstep (se 1 (by rfl) ⟨225863, by rfl⟩ : syracuseStep 301151 = 451727) B451727
theorem B334057 : Blo 175800 334057 := bstep (se 2 (by rfl) ⟨125271, by rfl⟩ : syracuseStep 334057 = 250543) B250543
theorem B268523 : Blo 175800 268523 := bstep (se 1 (by rfl) ⟨201392, by rfl⟩ : syracuseStep 268523 = 402785) B402785
theorem B268583 : Blo 175800 268583 := bstep (se 1 (by rfl) ⟨201437, by rfl⟩ : syracuseStep 268583 = 402875) B402875
theorem B596267 : Blo 175800 596267 := bstep (se 1 (by rfl) ⟨447200, by rfl⟩ : syracuseStep 596267 = 894401) B894401
theorem B268667 : Blo 175800 268667 := bstep (se 1 (by rfl) ⟨201500, by rfl⟩ : syracuseStep 268667 = 403001) B403001
theorem B4069757 : Blo 175800 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B1350107 : Blo 175800 1350107 := bstep (se 1 (by rfl) ⟨1012580, by rfl⟩ : syracuseStep 1350107 = 2025161) B2025161
theorem B596537 : Blo 175800 596537 := bstep (se 2 (by rfl) ⟨223701, by rfl⟩ : syracuseStep 596537 = 447403) B447403
theorem B268937 : Blo 175800 268937 := bstep (se 2 (by rfl) ⟨100851, by rfl⟩ : syracuseStep 268937 = 201703) B201703
theorem B269111 : Blo 175800 269111 := bstep (se 1 (by rfl) ⟨201833, by rfl⟩ : syracuseStep 269111 = 403667) B403667
theorem B400211 : Blo 175800 400211 := bstep (se 1 (by rfl) ⟨300158, by rfl⟩ : syracuseStep 400211 = 600317) B600317
theorem B269147 : Blo 175800 269147 := bstep (se 1 (by rfl) ⟨201860, by rfl⟩ : syracuseStep 269147 = 403721) B403721
theorem B2431853 : Blo 175800 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B269291 : Blo 175800 269291 := bstep (se 1 (by rfl) ⟨201968, by rfl⟩ : syracuseStep 269291 = 403937) B403937
theorem B2268161 : Blo 175800 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B1514497 : Blo 175800 1514497 := bstep (se 2 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 1514497 = 1135873) B1135873
theorem B564349 : Blo 175800 564349 := bstep (se 3 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 564349 = 211631) B211631
theorem B269495 : Blo 175800 269495 := bstep (se 1 (by rfl) ⟨202121, by rfl⟩ : syracuseStep 269495 = 404243) B404243
theorem B2891009 : Blo 175800 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B400751 : Blo 175800 400751 := bstep (se 1 (by rfl) ⟨300563, by rfl⟩ : syracuseStep 400751 = 601127) B601127
theorem B302447 : Blo 175800 302447 := bstep (se 1 (by rfl) ⟨226835, by rfl⟩ : syracuseStep 302447 = 453671) B453671
theorem B2563559 : Blo 175800 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B302683 : Blo 175800 302683 := bstep (se 1 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 302683 = 454025) B454025
theorem B401039 : Blo 175800 401039 := bstep (se 1 (by rfl) ⟨300779, by rfl⟩ : syracuseStep 401039 = 601559) B601559
theorem B401129 : Blo 175800 401129 := bstep (se 2 (by rfl) ⟨150423, by rfl⟩ : syracuseStep 401129 = 300847) B300847
theorem B302825 : Blo 175800 302825 := bstep (se 2 (by rfl) ⟨113559, by rfl⟩ : syracuseStep 302825 = 227119) B227119
theorem B4890401 : Blo 175800 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B598049 : Blo 175800 598049 := bstep (se 2 (by rfl) ⟨224268, by rfl⟩ : syracuseStep 598049 = 448537) B448537
theorem B1352051 : Blo 175800 1352051 := bstep (se 1 (by rfl) ⟨1014038, by rfl⟩ : syracuseStep 1352051 = 2028077) B2028077
theorem B402155 : Blo 175800 402155 := bstep (se 1 (by rfl) ⟨301616, by rfl⟩ : syracuseStep 402155 = 603233) B603233
theorem B893753 : Blo 175800 893753 := bstep (se 2 (by rfl) ⟨335157, by rfl⟩ : syracuseStep 893753 = 670315) B670315
theorem B2564941 : Blo 175800 2564941 := bstep (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) B961853
theorem B566183 : Blo 175800 566183 := bstep (se 1 (by rfl) ⟨424637, by rfl⟩ : syracuseStep 566183 = 849275) B849275
theorem B23635115 : Blo 175800 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B238799 : Blo 175800 238799 := bstep (se 1 (by rfl) ⟨179099, by rfl⟩ : syracuseStep 238799 = 358199) B358199
theorem B403055 : Blo 175800 403055 := bstep (se 1 (by rfl) ⟨302291, by rfl⟩ : syracuseStep 403055 = 604583) B604583
theorem B304859 : Blo 175800 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B403163 : Blo 175800 403163 := bstep (se 1 (by rfl) ⟨302372, by rfl⟩ : syracuseStep 403163 = 604745) B604745
theorem B403447 : Blo 175800 403447 := bstep (se 1 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 403447 = 605171) B605171
theorem B764255 : Blo 175800 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B404279 : Blo 175800 404279 := bstep (se 1 (by rfl) ⟨303209, by rfl⟩ : syracuseStep 404279 = 606419) B606419
theorem B404459 : Blo 175800 404459 := bstep (se 1 (by rfl) ⟨303344, by rfl⟩ : syracuseStep 404459 = 606689) B606689
theorem B339167 : Blo 175800 339167 := bstep (se 1 (by rfl) ⟨254375, by rfl⟩ : syracuseStep 339167 = 508751) B508751
theorem B601775 : Blo 175800 601775 := bstep (se 1 (by rfl) ⟨451331, by rfl⟩ : syracuseStep 601775 = 902663) B902663
theorem B175943 : Blo 175800 175943 := bstep (se 1 (by rfl) ⟨131957, by rfl⟩ : syracuseStep 175943 = 263915) B263915
theorem B176095 : Blo 175800 176095 := bstep (se 1 (by rfl) ⟨132071, by rfl⟩ : syracuseStep 176095 = 264143) B264143
theorem B602099 : Blo 175800 602099 := bstep (se 1 (by rfl) ⟨451574, by rfl⟩ : syracuseStep 602099 = 903149) B903149
theorem B176359 : Blo 175800 176359 := bstep (se 1 (by rfl) ⟨132269, by rfl⟩ : syracuseStep 176359 = 264539) B264539
theorem B602423 : Blo 175800 602423 := bstep (se 1 (by rfl) ⟨451817, by rfl⟩ : syracuseStep 602423 = 903635) B903635
theorem B176511 : Blo 175800 176511 := bstep (se 1 (by rfl) ⟨132383, by rfl⟩ : syracuseStep 176511 = 264767) B264767
theorem B176591 : Blo 175800 176591 := bstep (se 1 (by rfl) ⟨132443, by rfl⟩ : syracuseStep 176591 = 264887) B264887
theorem B602639 : Blo 175800 602639 := bstep (se 1 (by rfl) ⟨451979, by rfl⟩ : syracuseStep 602639 = 903959) B903959
theorem B635471 : Blo 175800 635471 := bstep (se 1 (by rfl) ⟨476603, by rfl⟩ : syracuseStep 635471 = 953207) B953207
theorem B176743 : Blo 175800 176743 := bstep (se 1 (by rfl) ⟨132557, by rfl⟩ : syracuseStep 176743 = 265115) B265115
theorem B4338461 : Blo 175800 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B2896669 : Blo 175800 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B340777 : Blo 175800 340777 := bstep (se 2 (by rfl) ⟨127791, by rfl⟩ : syracuseStep 340777 = 255583) B255583
theorem B177007 : Blo 175800 177007 := bstep (se 1 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 177007 = 265511) B265511
theorem B177063 : Blo 175800 177063 := bstep (se 1 (by rfl) ⟨132797, by rfl⟩ : syracuseStep 177063 = 265595) B265595
theorem B177147 : Blo 175800 177147 := bstep (se 1 (by rfl) ⟨132860, by rfl⟩ : syracuseStep 177147 = 265721) B265721
theorem B177215 : Blo 175800 177215 := bstep (se 1 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 177215 = 265823) B265823
theorem B177359 : Blo 175800 177359 := bstep (se 1 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 177359 = 266039) B266039
theorem B177563 : Blo 175800 177563 := bstep (se 1 (by rfl) ⟨133172, by rfl⟩ : syracuseStep 177563 = 266345) B266345
theorem B603719 : Blo 175800 603719 := bstep (se 1 (by rfl) ⟨452789, by rfl⟩ : syracuseStep 603719 = 905579) B905579
theorem B177775 : Blo 175800 177775 := bstep (se 1 (by rfl) ⟨133331, by rfl⟩ : syracuseStep 177775 = 266663) B266663
theorem B177831 : Blo 175800 177831 := bstep (se 1 (by rfl) ⟨133373, by rfl⟩ : syracuseStep 177831 = 266747) B266747
theorem B571115 : Blo 175800 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B177915 : Blo 175800 177915 := bstep (se 1 (by rfl) ⟨133436, by rfl⟩ : syracuseStep 177915 = 266873) B266873
theorem B177951 : Blo 175800 177951 := bstep (se 1 (by rfl) ⟨133463, by rfl⟩ : syracuseStep 177951 = 266927) B266927
theorem B177983 : Blo 175800 177983 := bstep (se 1 (by rfl) ⟨133487, by rfl⟩ : syracuseStep 177983 = 266975) B266975
theorem B178159 : Blo 175800 178159 := bstep (se 1 (by rfl) ⟨133619, by rfl⟩ : syracuseStep 178159 = 267239) B267239
theorem B1357883 : Blo 175800 1357883 := bstep (se 1 (by rfl) ⟨1018412, by rfl⟩ : syracuseStep 1357883 = 2036825) B2036825
theorem B571475 : Blo 175800 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B178331 : Blo 175800 178331 := bstep (se 1 (by rfl) ⟨133748, by rfl⟩ : syracuseStep 178331 = 267497) B267497
theorem B506017 : Blo 175800 506017 := bstep (se 2 (by rfl) ⟨189756, by rfl⟩ : syracuseStep 506017 = 379513) B379513
theorem B178367 : Blo 175800 178367 := bstep (se 1 (by rfl) ⟨133775, by rfl⟩ : syracuseStep 178367 = 267551) B267551
theorem B1816829 : Blo 175800 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B178479 : Blo 175800 178479 := bstep (se 1 (by rfl) ⟨133859, by rfl⟩ : syracuseStep 178479 = 267719) B267719
theorem B604691 : Blo 175800 604691 := bstep (se 1 (by rfl) ⟨453518, by rfl⟩ : syracuseStep 604691 = 907037) B907037
theorem B178715 : Blo 175800 178715 := bstep (se 1 (by rfl) ⟨134036, by rfl⟩ : syracuseStep 178715 = 268073) B268073
theorem B178719 : Blo 175800 178719 := bstep (se 1 (by rfl) ⟨134039, by rfl⟩ : syracuseStep 178719 = 268079) B268079
theorem B571961 : Blo 175800 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B539293 : Blo 175800 539293 := bstep (se 3 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 539293 = 202235) B202235
theorem B1293023 : Blo 175800 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B179035 : Blo 175800 179035 := bstep (se 1 (by rfl) ⟨134276, by rfl⟩ : syracuseStep 179035 = 268553) B268553
theorem B179103 : Blo 175800 179103 := bstep (se 1 (by rfl) ⟨134327, by rfl⟩ : syracuseStep 179103 = 268655) B268655
theorem B179247 : Blo 175800 179247 := bstep (se 1 (by rfl) ⟨134435, by rfl⟩ : syracuseStep 179247 = 268871) B268871
theorem B179271 : Blo 175800 179271 := bstep (se 1 (by rfl) ⟨134453, by rfl⟩ : syracuseStep 179271 = 268907) B268907
theorem B179423 : Blo 175800 179423 := bstep (se 1 (by rfl) ⟨134567, by rfl⟩ : syracuseStep 179423 = 269135) B269135
theorem B638237 : Blo 175800 638237 := bstep (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) B239339
theorem B179687 : Blo 175800 179687 := bstep (se 1 (by rfl) ⟨134765, by rfl⟩ : syracuseStep 179687 = 269531) B269531
theorem B15711853 : Blo 175800 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B573115 : Blo 175800 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B507703 : Blo 175800 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B573473 : Blo 175800 573473 := bstep (se 2 (by rfl) ⟨215052, by rfl⟩ : syracuseStep 573473 = 430105) B430105
theorem B2867339 : Blo 175800 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B7979147 : Blo 175800 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B345043 : Blo 175800 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B2573369 : Blo 175800 2573369 := bstep (se 2 (by rfl) ⟨965013, by rfl⟩ : syracuseStep 2573369 = 1930027) B1930027
theorem B410729 : Blo 175800 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B1885331 : Blo 175800 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B509321 : Blo 175800 509321 := bstep (se 2 (by rfl) ⟨190995, by rfl⟩ : syracuseStep 509321 = 381991) B381991
theorem B378283 : Blo 175800 378283 := bstep (se 1 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 378283 = 567425) B567425
theorem B1590821 : Blo 175800 1590821 := bstep (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) B298279
theorem B3130919 : Blo 175800 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B509561 : Blo 175800 509561 := bstep (se 2 (by rfl) ⟨191085, by rfl⟩ : syracuseStep 509561 = 382171) B382171
theorem B5130701 : Blo 175800 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B2017871 : Blo 175800 2017871 := bstep (se 1 (by rfl) ⟨1513403, by rfl⟩ : syracuseStep 2017871 = 3026807) B3026807
theorem B641641 : Blo 175800 641641 := bstep (se 2 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 641641 = 481231) B481231
theorem B445115 : Blo 175800 445115 := bstep (se 1 (by rfl) ⟨333836, by rfl⟩ : syracuseStep 445115 = 667673) B667673
theorem B805727 : Blo 175800 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B1723493 : Blo 175800 1723493 := bstep (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) B323155
theorem B1002739 : Blo 175800 1002739 := bstep (se 1 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 1002739 = 1504109) B1504109
theorem B511849 : Blo 175800 511849 := bstep (se 2 (by rfl) ⟨191943, by rfl⟩ : syracuseStep 511849 = 383887) B383887
theorem B446431 : Blo 175800 446431 := bstep (se 1 (by rfl) ⟨334823, by rfl⟩ : syracuseStep 446431 = 669647) B669647
theorem B7721249 : Blo 175800 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B1724723 : Blo 175800 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B8606087 : Blo 175800 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B447059 : Blo 175800 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B447079 : Blo 175800 447079 := bstep (se 1 (by rfl) ⟨335309, by rfl⟩ : syracuseStep 447079 = 670619) B670619
theorem B676633 : Blo 175800 676633 := bstep (se 2 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 676633 = 507475) B507475
theorem B1398169 : Blo 175800 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B2414551 : Blo 175800 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B448487 : Blo 175800 448487 := bstep (se 1 (by rfl) ⟨336365, by rfl⟩ : syracuseStep 448487 = 672731) B672731
theorem B383059 : Blo 175800 383059 := bstep (se 1 (by rfl) ⟨287294, by rfl⟩ : syracuseStep 383059 = 574589) B574589
theorem B383545 : Blo 175800 383545 := bstep (se 2 (by rfl) ⟨143829, by rfl⟩ : syracuseStep 383545 = 287659) B287659
theorem B4119113 : Blo 175800 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B252553 : Blo 175800 252553 := bstep (se 2 (by rfl) ⟨94707, by rfl⟩ : syracuseStep 252553 = 189415) B189415
theorem B678881 : Blo 175800 678881 := bstep (se 2 (by rfl) ⟨254580, by rfl⟩ : syracuseStep 678881 = 509161) B509161
theorem B2317501 : Blo 175800 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B1007113 : Blo 175800 1007113 := bstep (se 2 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 1007113 = 755335) B755335
theorem B581431 : Blo 175800 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B614753 : Blo 175800 614753 := bstep (se 2 (by rfl) ⟨230532, by rfl⟩ : syracuseStep 614753 = 461065) B461065
theorem B680521 : Blo 175800 680521 := bstep (se 2 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 680521 = 510391) B510391
theorem B254831 : Blo 175800 254831 := bstep (se 1 (by rfl) ⟨191123, by rfl⟩ : syracuseStep 254831 = 382247) B382247
theorem B9757847 : Blo 175800 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B648701 : Blo 175800 648701 := bstep (se 3 (by rfl) ⟨121631, by rfl⟩ : syracuseStep 648701 = 243263) B243263
theorem B517727 : Blo 175800 517727 := bstep (se 1 (by rfl) ⟨388295, by rfl⟩ : syracuseStep 517727 = 776591) B776591
theorem B452263 : Blo 175800 452263 := bstep (se 1 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 452263 = 678395) B678395
theorem B223175 : Blo 175800 223175 := bstep (se 1 (by rfl) ⟨167381, by rfl⟩ : syracuseStep 223175 = 334763) B334763
theorem B223327 : Blo 175800 223327 := bstep (se 1 (by rfl) ⟨167495, by rfl⟩ : syracuseStep 223327 = 334991) B334991
theorem B6187205 : Blo 175800 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B452911 : Blo 175800 452911 := bstep (se 1 (by rfl) ⟨339683, by rfl⟩ : syracuseStep 452911 = 679367) B679367
theorem B518557 : Blo 175800 518557 := bstep (se 3 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 518557 = 194459) B194459
theorem B322463 : Blo 175800 322463 := bstep (se 1 (by rfl) ⟨241847, by rfl⟩ : syracuseStep 322463 = 483695) B483695
theorem B1010987 : Blo 175800 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B1502711 : Blo 175800 1502711 := bstep (se 1 (by rfl) ⟨1127033, by rfl⟩ : syracuseStep 1502711 = 2254067) B2254067
theorem B454207 : Blo 175800 454207 := bstep (se 1 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 454207 = 681311) B681311
theorem B454319 : Blo 175800 454319 := bstep (se 1 (by rfl) ⟨340739, by rfl⟩ : syracuseStep 454319 = 681479) B681479
theorem B2158289 : Blo 175800 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B454643 : Blo 175800 454643 := bstep (se 1 (by rfl) ⟨340982, by rfl⟩ : syracuseStep 454643 = 681965) B681965
theorem B1274167 : Blo 175800 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B454967 : Blo 175800 454967 := bstep (se 1 (by rfl) ⟨341225, by rfl⟩ : syracuseStep 454967 = 682451) B682451
theorem B1012445 : Blo 175800 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B422975 : Blo 175800 422975 := bstep (se 1 (by rfl) ⟨317231, by rfl⟩ : syracuseStep 422975 = 634463) B634463
theorem B1013903 : Blo 175800 1013903 := bstep (se 1 (by rfl) ⟨760427, by rfl⟩ : syracuseStep 1013903 = 1520855) B1520855
theorem B719513 : Blo 175800 719513 := bstep (se 2 (by rfl) ⟨269817, by rfl⟩ : syracuseStep 719513 = 539635) B539635
theorem B1145897 : Blo 175800 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B1277687 : Blo 175800 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B2426375 : Blo 175800 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B263711 : Blo 175800 263711 := bstep (se 1 (by rfl) ⟨197783, by rfl⟩ : syracuseStep 263711 = 395567) B395567
theorem B198175 : Blo 175800 198175 := bstep (se 1 (by rfl) ⟨148631, by rfl⟩ : syracuseStep 198175 = 297263) B297263
theorem B263855 : Blo 175800 263855 := bstep (se 1 (by rfl) ⟨197891, by rfl⟩ : syracuseStep 263855 = 395783) B395783
theorem B1345247 : Blo 175800 1345247 := bstep (se 1 (by rfl) ⟨1008935, by rfl⟩ : syracuseStep 1345247 = 2017871) B2017871
theorem B296743 : Blo 175800 296743 := bstep (se 1 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 296743 = 445115) B445115
theorem B263975 : Blo 175800 263975 := bstep (se 1 (by rfl) ⟨197981, by rfl⟩ : syracuseStep 263975 = 395963) B395963
theorem B1148995 : Blo 175800 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B11569229 : Blo 175800 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B1411181 : Blo 175800 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B264527 : Blo 175800 264527 := bstep (se 1 (by rfl) ⟨198395, by rfl⟩ : syracuseStep 264527 = 396791) B396791
theorem B264575 : Blo 175800 264575 := bstep (se 1 (by rfl) ⟨198431, by rfl⟩ : syracuseStep 264575 = 396863) B396863
theorem B199039 : Blo 175800 199039 := bstep (se 1 (by rfl) ⟨149279, by rfl⟩ : syracuseStep 199039 = 298559) B298559
theorem B264617 : Blo 175800 264617 := bstep (se 2 (by rfl) ⟨99231, by rfl⟩ : syracuseStep 264617 = 198463) B198463
theorem B396071 : Blo 175800 396071 := bstep (se 1 (by rfl) ⟨297053, by rfl⟩ : syracuseStep 396071 = 594107) B594107
theorem B5114663 : Blo 175800 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B297769 : Blo 175800 297769 := bstep (se 2 (by rfl) ⟨111663, by rfl⟩ : syracuseStep 297769 = 223327) B223327
theorem B265001 : Blo 175800 265001 := bstep (se 2 (by rfl) ⟨99375, by rfl⟩ : syracuseStep 265001 = 198751) B198751
theorem B854867 : Blo 175800 854867 := bstep (se 1 (by rfl) ⟨641150, by rfl⟩ : syracuseStep 854867 = 1282301) B1282301
theorem B1149815 : Blo 175800 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B5737391 : Blo 175800 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B265211 : Blo 175800 265211 := bstep (se 1 (by rfl) ⟨198908, by rfl⟩ : syracuseStep 265211 = 397817) B397817
theorem B298039 : Blo 175800 298039 := bstep (se 1 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 298039 = 447059) B447059
theorem B265271 : Blo 175800 265271 := bstep (se 1 (by rfl) ⟨198953, by rfl⟩ : syracuseStep 265271 = 397907) B397907
theorem B396395 : Blo 175800 396395 := bstep (se 1 (by rfl) ⟨297296, by rfl⟩ : syracuseStep 396395 = 594593) B594593
theorem B724103 : Blo 175800 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B265391 : Blo 175800 265391 := bstep (se 1 (by rfl) ⟨199043, by rfl⟩ : syracuseStep 265391 = 398087) B398087
theorem B691409 : Blo 175800 691409 := bstep (se 2 (by rfl) ⟨259278, by rfl⟩ : syracuseStep 691409 = 518557) B518557
theorem B396665 : Blo 175800 396665 := bstep (se 2 (by rfl) ⟨148749, by rfl⟩ : syracuseStep 396665 = 297499) B297499
theorem B855521 : Blo 175800 855521 := bstep (se 2 (by rfl) ⟨320820, by rfl⟩ : syracuseStep 855521 = 641641) B641641
theorem B396971 : Blo 175800 396971 := bstep (se 1 (by rfl) ⟨297728, by rfl⟩ : syracuseStep 396971 = 595457) B595457
theorem B200443 : Blo 175800 200443 := bstep (se 1 (by rfl) ⟨150332, by rfl⟩ : syracuseStep 200443 = 300665) B300665
theorem B266111 : Blo 175800 266111 := bstep (se 1 (by rfl) ⟨199583, by rfl⟩ : syracuseStep 266111 = 399167) B399167
theorem B397295 : Blo 175800 397295 := bstep (se 1 (by rfl) ⟨297971, by rfl⟩ : syracuseStep 397295 = 595943) B595943
theorem B298991 : Blo 175800 298991 := bstep (se 1 (by rfl) ⟨224243, by rfl⟩ : syracuseStep 298991 = 448487) B448487
theorem B3084331 : Blo 175800 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B397367 : Blo 175800 397367 := bstep (se 1 (by rfl) ⟨298025, by rfl⟩ : syracuseStep 397367 = 596051) B596051
theorem B266303 : Blo 175800 266303 := bstep (se 1 (by rfl) ⟨199727, by rfl⟩ : syracuseStep 266303 = 399455) B399455
theorem B200767 : Blo 175800 200767 := bstep (se 1 (by rfl) ⟨150575, by rfl⟩ : syracuseStep 200767 = 301151) B301151
theorem B397511 : Blo 175800 397511 := bstep (se 1 (by rfl) ⟨298133, by rfl⟩ : syracuseStep 397511 = 596267) B596267
theorem B6295805 : Blo 175800 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B266537 : Blo 175800 266537 := bstep (se 2 (by rfl) ⟨99951, by rfl⟩ : syracuseStep 266537 = 199903) B199903
theorem B397691 : Blo 175800 397691 := bstep (se 1 (by rfl) ⟨298268, by rfl⟩ : syracuseStep 397691 = 596537) B596537
theorem B266807 : Blo 175800 266807 := bstep (se 1 (by rfl) ⟨200105, by rfl⟩ : syracuseStep 266807 = 400211) B400211
theorem B397961 : Blo 175800 397961 := bstep (se 2 (by rfl) ⟨149235, by rfl⟩ : syracuseStep 397961 = 298471) B298471
theorem B1512107 : Blo 175800 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B267167 : Blo 175800 267167 := bstep (se 1 (by rfl) ⟨200375, by rfl⟩ : syracuseStep 267167 = 400751) B400751
theorem B201631 : Blo 175800 201631 := bstep (se 1 (by rfl) ⟨151223, by rfl⟩ : syracuseStep 201631 = 302447) B302447
theorem B1709039 : Blo 175800 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B267359 : Blo 175800 267359 := bstep (se 1 (by rfl) ⟨200519, by rfl⟩ : syracuseStep 267359 = 401039) B401039
theorem B1840229 : Blo 175800 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B267419 : Blo 175800 267419 := bstep (se 1 (by rfl) ⟨200564, by rfl⟩ : syracuseStep 267419 = 401129) B401129
theorem B201883 : Blo 175800 201883 := bstep (se 1 (by rfl) ⟨151412, by rfl⟩ : syracuseStep 201883 = 302825) B302825
theorem B595133 : Blo 175800 595133 := bstep (se 3 (by rfl) ⟨111587, by rfl⟩ : syracuseStep 595133 = 223175) B223175
theorem B595241 : Blo 175800 595241 := bstep (se 2 (by rfl) ⟨223215, by rfl⟩ : syracuseStep 595241 = 446431) B446431
theorem B398699 : Blo 175800 398699 := bstep (se 1 (by rfl) ⟨299024, by rfl⟩ : syracuseStep 398699 = 598049) B598049
theorem B15832493 : Blo 175800 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B398969 : Blo 175800 398969 := bstep (se 2 (by rfl) ⟨149613, by rfl⟩ : syracuseStep 398969 = 299227) B299227
theorem B268103 : Blo 175800 268103 := bstep (se 1 (by rfl) ⟨201077, by rfl⟩ : syracuseStep 268103 = 402155) B402155
theorem B595835 : Blo 175800 595835 := bstep (se 1 (by rfl) ⟨446876, by rfl⟩ : syracuseStep 595835 = 893753) B893753
theorem B399329 : Blo 175800 399329 := bstep (se 2 (by rfl) ⟨149748, by rfl⟩ : syracuseStep 399329 = 299497) B299497
theorem B596105 : Blo 175800 596105 := bstep (se 2 (by rfl) ⟨223539, by rfl⟩ : syracuseStep 596105 = 447079) B447079
theorem B432467 : Blo 175800 432467 := bstep (se 1 (by rfl) ⟨324350, by rfl⟩ : syracuseStep 432467 = 648701) B648701
theorem B268703 : Blo 175800 268703 := bstep (se 1 (by rfl) ⟨201527, by rfl⟩ : syracuseStep 268703 = 403055) B403055
theorem B203239 : Blo 175800 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B268775 : Blo 175800 268775 := bstep (se 1 (by rfl) ⟨201581, by rfl⟩ : syracuseStep 268775 = 403163) B403163
theorem B269519 : Blo 175800 269519 := bstep (se 1 (by rfl) ⟨202139, by rfl⟩ : syracuseStep 269519 = 404279) B404279
theorem B269639 : Blo 175800 269639 := bstep (se 1 (by rfl) ⟨202229, by rfl⟩ : syracuseStep 269639 = 404459) B404459
theorem B859901 : Blo 175800 859901 := bstep (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) B322463
theorem B401183 : Blo 175800 401183 := bstep (se 1 (by rfl) ⟨300887, by rfl⟩ : syracuseStep 401183 = 601775) B601775
theorem B302879 : Blo 175800 302879 := bstep (se 1 (by rfl) ⟨227159, by rfl⟩ : syracuseStep 302879 = 454319) B454319
theorem B3219401 : Blo 175800 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B401399 : Blo 175800 401399 := bstep (se 1 (by rfl) ⟨301049, by rfl⟩ : syracuseStep 401399 = 602099) B602099
theorem B303095 : Blo 175800 303095 := bstep (se 1 (by rfl) ⟨227321, by rfl⟩ : syracuseStep 303095 = 454643) B454643
theorem B401615 : Blo 175800 401615 := bstep (se 1 (by rfl) ⟨301211, by rfl⟩ : syracuseStep 401615 = 602423) B602423
theorem B303311 : Blo 175800 303311 := bstep (se 1 (by rfl) ⟨227483, by rfl⟩ : syracuseStep 303311 = 454967) B454967
theorem B401759 : Blo 175800 401759 := bstep (se 1 (by rfl) ⟨301319, by rfl⟩ : syracuseStep 401759 = 602639) B602639
theorem B7709357 : Blo 175800 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B336737 : Blo 175800 336737 := bstep (se 2 (by rfl) ⟨126276, by rfl⟩ : syracuseStep 336737 = 252553) B252553
theorem B402479 : Blo 175800 402479 := bstep (se 1 (by rfl) ⟨301859, by rfl⟩ : syracuseStep 402479 = 603719) B603719
theorem B3090001 : Blo 175800 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B403127 : Blo 175800 403127 := bstep (se 1 (by rfl) ⟨302345, by rfl⟩ : syracuseStep 403127 = 604691) B604691
theorem B862015 : Blo 175800 862015 := bstep (se 1 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 862015 = 1293023) B1293023
theorem B763931 : Blo 175800 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B403577 : Blo 175800 403577 := bstep (se 2 (by rfl) ⟨151341, by rfl⟩ : syracuseStep 403577 = 302683) B302683
theorem B20949137 : Blo 175800 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B764153 : Blo 175800 764153 := bstep (se 2 (by rfl) ⟨286557, by rfl⟩ : syracuseStep 764153 = 573115) B573115
theorem B1911559 : Blo 175800 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B5319431 : Blo 175800 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B568271 : Blo 175800 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B764903 : Blo 175800 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B1715579 : Blo 175800 1715579 := bstep (se 1 (by rfl) ⟨1286684, by rfl⟩ : syracuseStep 1715579 = 2573369) B2573369
theorem B20589997 : Blo 175800 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B1256887 : Blo 175800 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B339547 : Blo 175800 339547 := bstep (se 1 (by rfl) ⟨254660, by rfl⟩ : syracuseStep 339547 = 509321) B509321
theorem B569015 : Blo 175800 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B1060547 : Blo 175800 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B569065 : Blo 175800 569065 := bstep (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) B426799
theorem B175867 : Blo 175800 175867 := bstep (se 1 (by rfl) ⟨131900, by rfl⟩ : syracuseStep 175867 = 263801) B263801
theorem B339707 : Blo 175800 339707 := bstep (se 1 (by rfl) ⟨254780, by rfl⟩ : syracuseStep 339707 = 509561) B509561
theorem B3419921 : Blo 175800 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B175935 : Blo 175800 175935 := bstep (se 1 (by rfl) ⟨131951, by rfl⟩ : syracuseStep 175935 = 263903) B263903
theorem B175999 : Blo 175800 175999 := bstep (se 1 (by rfl) ⟨131999, by rfl⟩ : syracuseStep 175999 = 263999) B263999
theorem B5779421 : Blo 175800 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B176111 : Blo 175800 176111 := bstep (se 1 (by rfl) ⟨132083, by rfl⟩ : syracuseStep 176111 = 264167) B264167
theorem B176123 : Blo 175800 176123 := bstep (se 1 (by rfl) ⟨132092, by rfl⟩ : syracuseStep 176123 = 264185) B264185
theorem B176191 : Blo 175800 176191 := bstep (se 1 (by rfl) ⟨132143, by rfl⟩ : syracuseStep 176191 = 264287) B264287
theorem B176231 : Blo 175800 176231 := bstep (se 1 (by rfl) ⟨132173, by rfl⟩ : syracuseStep 176231 = 264347) B264347
theorem B176255 : Blo 175800 176255 := bstep (se 1 (by rfl) ⟨132191, by rfl⟩ : syracuseStep 176255 = 264383) B264383
theorem B176283 : Blo 175800 176283 := bstep (se 1 (by rfl) ⟨132212, by rfl⟩ : syracuseStep 176283 = 264425) B264425
theorem B635111 : Blo 175800 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B3420467 : Blo 175800 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B176487 : Blo 175800 176487 := bstep (se 1 (by rfl) ⟨132365, by rfl⟩ : syracuseStep 176487 = 264731) B264731
theorem B176539 : Blo 175800 176539 := bstep (se 1 (by rfl) ⟨132404, by rfl⟩ : syracuseStep 176539 = 264809) B264809
theorem B504377 : Blo 175800 504377 := bstep (se 2 (by rfl) ⟨189141, by rfl⟩ : syracuseStep 504377 = 378283) B378283
theorem B537151 : Blo 175800 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B176891 : Blo 175800 176891 := bstep (se 1 (by rfl) ⟨132668, by rfl⟩ : syracuseStep 176891 = 265337) B265337
theorem B176959 : Blo 175800 176959 := bstep (se 1 (by rfl) ⟨132719, by rfl⟩ : syracuseStep 176959 = 265439) B265439
theorem B176987 : Blo 175800 176987 := bstep (se 1 (by rfl) ⟨132740, by rfl⟩ : syracuseStep 176987 = 265481) B265481
theorem B603017 : Blo 175800 603017 := bstep (se 2 (by rfl) ⟨226131, by rfl⟩ : syracuseStep 603017 = 452263) B452263
theorem B177055 : Blo 175800 177055 := bstep (se 1 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 177055 = 265583) B265583
theorem B504787 : Blo 175800 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B177135 : Blo 175800 177135 := bstep (se 1 (by rfl) ⟨132851, by rfl⟩ : syracuseStep 177135 = 265703) B265703
theorem B177223 : Blo 175800 177223 := bstep (se 1 (by rfl) ⟨132917, by rfl⟩ : syracuseStep 177223 = 265835) B265835
theorem B177307 : Blo 175800 177307 := bstep (se 1 (by rfl) ⟨132980, by rfl⟩ : syracuseStep 177307 = 265961) B265961
theorem B177403 : Blo 175800 177403 := bstep (se 1 (by rfl) ⟨133052, by rfl⟩ : syracuseStep 177403 = 266105) B266105
theorem B767227 : Blo 175800 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B177471 : Blo 175800 177471 := bstep (se 1 (by rfl) ⟨133103, by rfl⟩ : syracuseStep 177471 = 266207) B266207
theorem B537929 : Blo 175800 537929 := bstep (se 2 (by rfl) ⟨201723, by rfl⟩ : syracuseStep 537929 = 403447) B403447
theorem B177639 : Blo 175800 177639 := bstep (se 1 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 177639 = 266459) B266459
theorem B177647 : Blo 175800 177647 := bstep (se 1 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 177647 = 266471) B266471
theorem B177755 : Blo 175800 177755 := bstep (se 1 (by rfl) ⟨133316, by rfl⟩ : syracuseStep 177755 = 266633) B266633
theorem B1095277 : Blo 175800 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B2045573 : Blo 175800 2045573 := bstep (se 4 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 2045573 = 383545) B383545
theorem B177819 : Blo 175800 177819 := bstep (se 1 (by rfl) ⟨133364, by rfl⟩ : syracuseStep 177819 = 266729) B266729
theorem B603881 : Blo 175800 603881 := bstep (se 2 (by rfl) ⟨226455, by rfl⟩ : syracuseStep 603881 = 452911) B452911
theorem B177903 : Blo 175800 177903 := bstep (se 1 (by rfl) ⟨133427, by rfl⟩ : syracuseStep 177903 = 266855) B266855
theorem B177991 : Blo 175800 177991 := bstep (se 1 (by rfl) ⟨133493, by rfl⟩ : syracuseStep 177991 = 266987) B266987
theorem B178011 : Blo 175800 178011 := bstep (se 1 (by rfl) ⟨133508, by rfl⟩ : syracuseStep 178011 = 267017) B267017
theorem B636797 : Blo 175800 636797 := bstep (se 3 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 636797 = 238799) B238799
theorem B178079 : Blo 175800 178079 := bstep (se 1 (by rfl) ⟨133559, by rfl⟩ : syracuseStep 178079 = 267119) B267119
theorem B178247 : Blo 175800 178247 := bstep (se 1 (by rfl) ⟨133685, by rfl⟩ : syracuseStep 178247 = 267371) B267371
theorem B178407 : Blo 175800 178407 := bstep (se 1 (by rfl) ⟨133805, by rfl⟩ : syracuseStep 178407 = 267611) B267611
theorem B571627 : Blo 175800 571627 := bstep (se 1 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 571627 = 857441) B857441
theorem B178591 : Blo 175800 178591 := bstep (se 1 (by rfl) ⟨133943, by rfl⟩ : syracuseStep 178591 = 267887) B267887
theorem B178639 : Blo 175800 178639 := bstep (se 1 (by rfl) ⟨133979, by rfl⟩ : syracuseStep 178639 = 267959) B267959
theorem B178663 : Blo 175800 178663 := bstep (se 1 (by rfl) ⟨133997, by rfl⟩ : syracuseStep 178663 = 267995) B267995
theorem B2275847 : Blo 175800 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B178779 : Blo 175800 178779 := bstep (se 1 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 178779 = 268169) B268169
theorem B178847 : Blo 175800 178847 := bstep (se 1 (by rfl) ⟨134135, by rfl⟩ : syracuseStep 178847 = 268271) B268271
theorem B179015 : Blo 175800 179015 := bstep (se 1 (by rfl) ⟨134261, by rfl⟩ : syracuseStep 179015 = 268523) B268523
theorem B179055 : Blo 175800 179055 := bstep (se 1 (by rfl) ⟨134291, by rfl⟩ : syracuseStep 179055 = 268583) B268583
theorem B179111 : Blo 175800 179111 := bstep (se 1 (by rfl) ⟨134333, by rfl⟩ : syracuseStep 179111 = 268667) B268667
theorem B900071 : Blo 175800 900071 := bstep (se 1 (by rfl) ⟨675053, by rfl⟩ : syracuseStep 900071 = 1350107) B1350107
theorem B179291 : Blo 175800 179291 := bstep (se 1 (by rfl) ⟨134468, by rfl⟩ : syracuseStep 179291 = 268937) B268937
theorem B179407 : Blo 175800 179407 := bstep (se 1 (by rfl) ⟨134555, by rfl⟩ : syracuseStep 179407 = 269111) B269111
theorem B179431 : Blo 175800 179431 := bstep (se 1 (by rfl) ⟨134573, by rfl⟩ : syracuseStep 179431 = 269147) B269147
theorem B1621235 : Blo 175800 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B179527 : Blo 175800 179527 := bstep (se 1 (by rfl) ⟨134645, by rfl⟩ : syracuseStep 179527 = 269291) B269291
theorem B605609 : Blo 175800 605609 := bstep (se 2 (by rfl) ⟨227103, by rfl⟩ : syracuseStep 605609 = 454207) B454207
theorem B179663 : Blo 175800 179663 := bstep (se 1 (by rfl) ⟨134747, by rfl⟩ : syracuseStep 179663 = 269495) B269495
theorem B1228297 : Blo 175800 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B3260267 : Blo 175800 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B409835 : Blo 175800 409835 := bstep (se 1 (by rfl) ⟨307376, by rfl⟩ : syracuseStep 409835 = 614753) B614753
theorem B901367 : Blo 175800 901367 := bstep (se 1 (by rfl) ⟨676025, by rfl⟩ : syracuseStep 901367 = 1352051) B1352051
theorem B377455 : Blo 175800 377455 := bstep (se 1 (by rfl) ⟨283091, by rfl⟩ : syracuseStep 377455 = 566183) B566183
theorem B6505231 : Blo 175800 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B902177 : Blo 175800 902177 := bstep (se 2 (by rfl) ⟨338316, by rfl⟩ : syracuseStep 902177 = 676633) B676633
theorem B345151 : Blo 175800 345151 := bstep (se 1 (by rfl) ⟨258863, by rfl⟩ : syracuseStep 345151 = 517727) B517727
theorem B1525229 : Blo 175800 1525229 := bstep (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) B571961
theorem B509503 : Blo 175800 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B673991 : Blo 175800 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B1001807 : Blo 175800 1001807 := bstep (se 1 (by rfl) ⟨751355, by rfl⟩ : syracuseStep 1001807 = 1502711) B1502711
theorem B510745 : Blo 175800 510745 := bstep (se 2 (by rfl) ⟨191529, by rfl⟩ : syracuseStep 510745 = 383059) B383059
theorem B674689 : Blo 175800 674689 := bstep (se 2 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 674689 = 506017) B506017
theorem B445409 : Blo 175800 445409 := bstep (se 2 (by rfl) ⟨167028, by rfl⟩ : syracuseStep 445409 = 334057) B334057
theorem B674963 : Blo 175800 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B904445 : Blo 175800 904445 := bstep (se 3 (by rfl) ⟨169583, by rfl⟩ : syracuseStep 904445 = 339167) B339167
theorem B281983 : Blo 175800 281983 := bstep (se 1 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 281983 = 422975) B422975
theorem B380743 : Blo 175800 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B2019329 : Blo 175800 2019329 := bstep (se 2 (by rfl) ⟨757248, by rfl⟩ : syracuseStep 2019329 = 1514497) B1514497
theorem B905255 : Blo 175800 905255 := bstep (se 1 (by rfl) ⟨678941, by rfl⟩ : syracuseStep 905255 = 1357883) B1357883
theorem B380983 : Blo 175800 380983 := bstep (se 1 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 380983 = 571475) B571475
theorem B675935 : Blo 175800 675935 := bstep (se 1 (by rfl) ⟨506951, by rfl⟩ : syracuseStep 675935 = 1013903) B1013903
theorem B479675 : Blo 175800 479675 := bstep (se 1 (by rfl) ⟨359756, by rfl⟩ : syracuseStep 479675 = 719513) B719513
theorem B676937 : Blo 175800 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B775241 : Blo 175800 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B382315 : Blo 175800 382315 := bstep (se 1 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 382315 = 573473) B573473
theorem B13981081 : Blo 175800 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B349679 : Blo 175800 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B907361 : Blo 175800 907361 := bstep (se 2 (by rfl) ⟨340260, by rfl⟩ : syracuseStep 907361 = 680521) B680521
theorem B284891 : Blo 175800 284891 := bstep (se 1 (by rfl) ⟨213668, by rfl⟩ : syracuseStep 284891 = 427337) B427337
theorem B2087279 : Blo 175800 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B481697 : Blo 175800 481697 := bstep (se 2 (by rfl) ⟨180636, by rfl⟩ : syracuseStep 481697 = 361273) B361273
theorem B679549 : Blo 175800 679549 := bstep (se 3 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 679549 = 254831) B254831
theorem B2580113 : Blo 175800 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B48850289 : Blo 175800 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B2713171 : Blo 175800 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B1336985 : Blo 175800 1336985 := bstep (se 2 (by rfl) ⟨501369, by rfl⟩ : syracuseStep 1336985 = 1002739) B1002739
theorem B2746075 : Blo 175800 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B452587 : Blo 175800 452587 := bstep (se 1 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 452587 = 678881) B678881
theorem B485473 : Blo 175800 485473 := bstep (se 2 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 485473 = 364105) B364105
theorem B682465 : Blo 175800 682465 := bstep (se 2 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 682465 = 511849) B511849
theorem B1698889 : Blo 175800 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B15756743 : Blo 175800 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B3862225 : Blo 175800 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B454369 : Blo 175800 454369 := bstep (se 2 (by rfl) ⟨170388, by rfl⟩ : syracuseStep 454369 = 340777) B340777
theorem B4124803 : Blo 175800 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B12415169 : Blo 175800 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1864225 : Blo 175800 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B1438859 : Blo 175800 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B423647 : Blo 175800 423647 := bstep (se 1 (by rfl) ⟨317735, by rfl⟩ : syracuseStep 423647 = 635471) B635471
theorem B1701965 : Blo 175800 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B719057 : Blo 175800 719057 := bstep (se 2 (by rfl) ⟨269646, by rfl⟩ : syracuseStep 719057 = 539293) B539293
theorem B752465 : Blo 175800 752465 := bstep (se 2 (by rfl) ⟨282174, by rfl⟩ : syracuseStep 752465 = 564349) B564349
theorem B1211219 : Blo 175800 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B1342817 : Blo 175800 1342817 := bstep (se 2 (by rfl) ⟨503556, by rfl⟩ : syracuseStep 1342817 = 1007113) B1007113
theorem B851791 : Blo 175800 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B1016819 : Blo 175800 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B3048677 : Blo 175800 3048677 := bstep (se 4 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 3048677 = 571627) B571627
theorem B460201 : Blo 175800 460201 := bstep (se 2 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 460201 = 345151) B345151
theorem B264047 : Blo 175800 264047 := bstep (se 1 (by rfl) ⟨198035, by rfl⟩ : syracuseStep 264047 = 396071) B396071
theorem B3409775 : Blo 175800 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B296939 : Blo 175800 296939 := bstep (se 1 (by rfl) ⟨222704, by rfl⟩ : syracuseStep 296939 = 445409) B445409
theorem B264233 : Blo 175800 264233 := bstep (se 2 (by rfl) ⟨99087, by rfl⟩ : syracuseStep 264233 = 198175) B198175
theorem B264263 : Blo 175800 264263 := bstep (se 1 (by rfl) ⟨198197, by rfl⟩ : syracuseStep 264263 = 396395) B396395
theorem B460939 : Blo 175800 460939 := bstep (se 1 (by rfl) ⟨345704, by rfl⟩ : syracuseStep 460939 = 691409) B691409
theorem B264443 : Blo 175800 264443 := bstep (se 1 (by rfl) ⟨198332, by rfl⟩ : syracuseStep 264443 = 396665) B396665
theorem B395657 : Blo 175800 395657 := bstep (se 2 (by rfl) ⟨148371, by rfl⟩ : syracuseStep 395657 = 296743) B296743
theorem B1149353 : Blo 175800 1149353 := bstep (se 2 (by rfl) ⟨431007, by rfl⟩ : syracuseStep 1149353 = 862015) B862015
theorem B264647 : Blo 175800 264647 := bstep (se 1 (by rfl) ⟨198485, by rfl⟩ : syracuseStep 264647 = 396971) B396971
theorem B1083941 : Blo 175800 1083941 := bstep (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) B203239
theorem B264863 : Blo 175800 264863 := bstep (se 1 (by rfl) ⟨198647, by rfl⟩ : syracuseStep 264863 = 397295) B397295
theorem B199327 : Blo 175800 199327 := bstep (se 1 (by rfl) ⟨149495, by rfl⟩ : syracuseStep 199327 = 298991) B298991
theorem B1346219 : Blo 175800 1346219 := bstep (se 1 (by rfl) ⟨1009664, by rfl⟩ : syracuseStep 1346219 = 2019329) B2019329
theorem B264911 : Blo 175800 264911 := bstep (se 1 (by rfl) ⟨198683, by rfl⟩ : syracuseStep 264911 = 397367) B397367
theorem B265007 : Blo 175800 265007 := bstep (se 1 (by rfl) ⟨198755, by rfl⟩ : syracuseStep 265007 = 397511) B397511
theorem B4197203 : Blo 175800 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B265127 : Blo 175800 265127 := bstep (se 1 (by rfl) ⟨198845, by rfl⟩ : syracuseStep 265127 = 397691) B397691
theorem B265307 : Blo 175800 265307 := bstep (se 1 (by rfl) ⟨198980, by rfl⟩ : syracuseStep 265307 = 397961) B397961
theorem B265385 : Blo 175800 265385 := bstep (se 2 (by rfl) ⟨99519, by rfl⟩ : syracuseStep 265385 = 199039) B199039
theorem B396755 : Blo 175800 396755 := bstep (se 1 (by rfl) ⟨297566, by rfl⟩ : syracuseStep 396755 = 595133) B595133
theorem B396827 : Blo 175800 396827 := bstep (se 1 (by rfl) ⟨297620, by rfl⟩ : syracuseStep 396827 = 595241) B595241
theorem B265799 : Blo 175800 265799 := bstep (se 1 (by rfl) ⟨199349, by rfl⟩ : syracuseStep 265799 = 398699) B398699
theorem B10554995 : Blo 175800 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B233119 : Blo 175800 233119 := bstep (se 1 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 233119 = 349679) B349679
theorem B397025 : Blo 175800 397025 := bstep (se 2 (by rfl) ⟨148884, by rfl⟩ : syracuseStep 397025 = 297769) B297769
theorem B265979 : Blo 175800 265979 := bstep (se 1 (by rfl) ⟨199484, by rfl⟩ : syracuseStep 265979 = 398969) B398969
theorem B397223 : Blo 175800 397223 := bstep (se 1 (by rfl) ⟨297917, by rfl⟩ : syracuseStep 397223 = 595835) B595835
theorem B266219 : Blo 175800 266219 := bstep (se 1 (by rfl) ⟨199664, by rfl⟩ : syracuseStep 266219 = 399329) B399329
theorem B397385 : Blo 175800 397385 := bstep (se 2 (by rfl) ⟨149019, by rfl⟩ : syracuseStep 397385 = 298039) B298039
theorem B397403 : Blo 175800 397403 := bstep (se 1 (by rfl) ⟨298052, by rfl⟩ : syracuseStep 397403 = 596105) B596105
theorem B2265185 : Blo 175800 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B758753 : Blo 175800 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B267257 : Blo 175800 267257 := bstep (se 2 (by rfl) ⟨100221, by rfl⟩ : syracuseStep 267257 = 200443) B200443
theorem B267455 : Blo 175800 267455 := bstep (se 1 (by rfl) ⟨200591, by rfl⟩ : syracuseStep 267455 = 401183) B401183
theorem B201919 : Blo 175800 201919 := bstep (se 1 (by rfl) ⟨151439, by rfl⟩ : syracuseStep 201919 = 302879) B302879
theorem B267599 : Blo 175800 267599 := bstep (se 1 (by rfl) ⟨200699, by rfl⟩ : syracuseStep 267599 = 401399) B401399
theorem B202063 : Blo 175800 202063 := bstep (se 1 (by rfl) ⟨151547, by rfl⟩ : syracuseStep 202063 = 303095) B303095
theorem B267689 : Blo 175800 267689 := bstep (se 2 (by rfl) ⟨100383, by rfl⟩ : syracuseStep 267689 = 200767) B200767
theorem B267743 : Blo 175800 267743 := bstep (se 1 (by rfl) ⟨200807, by rfl⟩ : syracuseStep 267743 = 401615) B401615
theorem B202207 : Blo 175800 202207 := bstep (se 1 (by rfl) ⟨151655, by rfl⟩ : syracuseStep 202207 = 303311) B303311
theorem B267839 : Blo 175800 267839 := bstep (se 1 (by rfl) ⟨200879, by rfl⟩ : syracuseStep 267839 = 401759) B401759
theorem B759709 : Blo 175800 759709 := bstep (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) B284891
theorem B268319 : Blo 175800 268319 := bstep (se 1 (by rfl) ⟨201239, by rfl⟩ : syracuseStep 268319 = 402479) B402479
theorem B891323 : Blo 175800 891323 := bstep (se 1 (by rfl) ⟨668492, by rfl⟩ : syracuseStep 891323 = 1336985) B1336985
theorem B268751 : Blo 175800 268751 := bstep (se 1 (by rfl) ⟨201563, by rfl⟩ : syracuseStep 268751 = 403127) B403127
theorem B268841 : Blo 175800 268841 := bstep (se 2 (by rfl) ⟨100815, by rfl⟩ : syracuseStep 268841 = 201631) B201631
theorem B269051 : Blo 175800 269051 := bstep (se 1 (by rfl) ⟨201788, by rfl⟩ : syracuseStep 269051 = 403577) B403577
theorem B13966091 : Blo 175800 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B269177 : Blo 175800 269177 := bstep (se 2 (by rfl) ⟨100941, by rfl⟩ : syracuseStep 269177 = 201883) B201883
theorem B1022969 : Blo 175800 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B3546287 : Blo 175800 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B2039741 : Blo 175800 2039741 := bstep (se 3 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 2039741 = 764903) B764903
theorem B336251 : Blo 175800 336251 := bstep (se 1 (by rfl) ⟨252188, by rfl⟩ : syracuseStep 336251 = 504377) B504377
theorem B402011 : Blo 175800 402011 := bstep (se 1 (by rfl) ⟨301508, by rfl⟩ : syracuseStep 402011 = 603017) B603017
theorem B959239 : Blo 175800 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B402587 : Blo 175800 402587 := bstep (se 1 (by rfl) ⟨301940, by rfl⟩ : syracuseStep 402587 = 603881) B603881
theorem B1517231 : Blo 175800 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B2828125 : Blo 175800 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B501643 : Blo 175800 501643 := bstep (se 1 (by rfl) ⟨376232, by rfl⟩ : syracuseStep 501643 = 752465) B752465
theorem B600047 : Blo 175800 600047 := bstep (se 1 (by rfl) ⟨450035, by rfl⟩ : syracuseStep 600047 = 900071) B900071
theorem B895211 : Blo 175800 895211 := bstep (se 1 (by rfl) ⟨671408, by rfl⟩ : syracuseStep 895211 = 1342817) B1342817
theorem B403739 : Blo 175800 403739 := bstep (se 1 (by rfl) ⟨302804, by rfl⟩ : syracuseStep 403739 = 605609) B605609
theorem B2173511 : Blo 175800 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B273223 : Blo 175800 273223 := bstep (se 1 (by rfl) ⟨204917, by rfl⟩ : syracuseStep 273223 = 409835) B409835
theorem B600911 : Blo 175800 600911 := bstep (se 1 (by rfl) ⟨450683, by rfl⟩ : syracuseStep 600911 = 901367) B901367
theorem B601451 : Blo 175800 601451 := bstep (se 1 (by rfl) ⟨451088, by rfl⟩ : syracuseStep 601451 = 902177) B902177
theorem B503273 : Blo 175800 503273 := bstep (se 2 (by rfl) ⟨188727, by rfl⟩ : syracuseStep 503273 = 377455) B377455
theorem B1617583 : Blo 175800 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B175807 : Blo 175800 175807 := bstep (se 1 (by rfl) ⟨131855, by rfl⟩ : syracuseStep 175807 = 263711) B263711
theorem B175903 : Blo 175800 175903 := bstep (se 1 (by rfl) ⟨131927, by rfl⟩ : syracuseStep 175903 = 263855) B263855
theorem B896831 : Blo 175800 896831 := bstep (se 1 (by rfl) ⟨672623, by rfl⟩ : syracuseStep 896831 = 1345247) B1345247
theorem B175983 : Blo 175800 175983 := bstep (se 1 (by rfl) ⟨131987, by rfl⟩ : syracuseStep 175983 = 263975) B263975
theorem B7712819 : Blo 175800 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B667871 : Blo 175800 667871 := bstep (se 1 (by rfl) ⟨500903, by rfl⟩ : syracuseStep 667871 = 1001807) B1001807
theorem B176351 : Blo 175800 176351 := bstep (se 1 (by rfl) ⟨132263, by rfl⟩ : syracuseStep 176351 = 264527) B264527
theorem B176383 : Blo 175800 176383 := bstep (se 1 (by rfl) ⟨132287, by rfl⟩ : syracuseStep 176383 = 264575) B264575
theorem B176411 : Blo 175800 176411 := bstep (se 1 (by rfl) ⟨132308, by rfl⟩ : syracuseStep 176411 = 264617) B264617
theorem B176667 : Blo 175800 176667 := bstep (se 1 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 176667 = 265001) B265001
theorem B569911 : Blo 175800 569911 := bstep (se 1 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 569911 = 854867) B854867
theorem B176807 : Blo 175800 176807 := bstep (se 1 (by rfl) ⟨132605, by rfl⟩ : syracuseStep 176807 = 265211) B265211
theorem B176847 : Blo 175800 176847 := bstep (se 1 (by rfl) ⟨132635, by rfl⟩ : syracuseStep 176847 = 265271) B265271
theorem B3617561 : Blo 175800 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B176927 : Blo 175800 176927 := bstep (se 1 (by rfl) ⟨132695, by rfl⟩ : syracuseStep 176927 = 265391) B265391
theorem B602963 : Blo 175800 602963 := bstep (se 1 (by rfl) ⟨452222, by rfl⟩ : syracuseStep 602963 = 904445) B904445
theorem B897965 : Blo 175800 897965 := bstep (se 3 (by rfl) ⟨168368, by rfl⟩ : syracuseStep 897965 = 336737) B336737
theorem B570347 : Blo 175800 570347 := bstep (se 1 (by rfl) ⟨427760, by rfl⟩ : syracuseStep 570347 = 855521) B855521
theorem B177407 : Blo 175800 177407 := bstep (se 1 (by rfl) ⟨133055, by rfl⟩ : syracuseStep 177407 = 266111) B266111
theorem B603449 : Blo 175800 603449 := bstep (se 2 (by rfl) ⟨226293, by rfl⟩ : syracuseStep 603449 = 452587) B452587
theorem B603503 : Blo 175800 603503 := bstep (se 1 (by rfl) ⟨452627, by rfl⟩ : syracuseStep 603503 = 905255) B905255
theorem B177535 : Blo 175800 177535 := bstep (se 1 (by rfl) ⟨133151, by rfl⟩ : syracuseStep 177535 = 266303) B266303
theorem B177691 : Blo 175800 177691 := bstep (se 1 (by rfl) ⟨133268, by rfl⟩ : syracuseStep 177691 = 266537) B266537
theorem B177871 : Blo 175800 177871 := bstep (se 1 (by rfl) ⟨133403, by rfl⟩ : syracuseStep 177871 = 266807) B266807
theorem B178111 : Blo 175800 178111 := bstep (se 1 (by rfl) ⟨133583, by rfl⟩ : syracuseStep 178111 = 267167) B267167
theorem B178239 : Blo 175800 178239 := bstep (se 1 (by rfl) ⟨133679, by rfl⟩ : syracuseStep 178239 = 267359) B267359
theorem B1226819 : Blo 175800 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B178279 : Blo 175800 178279 := bstep (se 1 (by rfl) ⟨133709, by rfl⟩ : syracuseStep 178279 = 267419) B267419
theorem B899585 : Blo 175800 899585 := bstep (se 2 (by rfl) ⟨337344, by rfl⟩ : syracuseStep 899585 = 674689) B674689
theorem B178735 : Blo 175800 178735 := bstep (se 1 (by rfl) ⟨134051, by rfl⟩ : syracuseStep 178735 = 268103) B268103
theorem B604907 : Blo 175800 604907 := bstep (se 1 (by rfl) ⟨453680, by rfl⟩ : syracuseStep 604907 = 907361) B907361
theorem B1391519 : Blo 175800 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B179135 : Blo 175800 179135 := bstep (se 1 (by rfl) ⟨134351, by rfl⟩ : syracuseStep 179135 = 268703) B268703
theorem B179183 : Blo 175800 179183 := bstep (se 1 (by rfl) ⟨134387, by rfl⟩ : syracuseStep 179183 = 268775) B268775
theorem B375977 : Blo 175800 375977 := bstep (se 2 (by rfl) ⟨140991, by rfl⟩ : syracuseStep 375977 = 281983) B281983
theorem B179679 : Blo 175800 179679 := bstep (se 1 (by rfl) ⟨134759, by rfl⟩ : syracuseStep 179679 = 269519) B269519
theorem B1916405 : Blo 175800 1916405 := bstep (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) B179663
theorem B179759 : Blo 175800 179759 := bstep (se 1 (by rfl) ⟨134819, by rfl⟩ : syracuseStep 179759 = 269639) B269639
theorem B605825 : Blo 175800 605825 := bstep (se 2 (by rfl) ⟨227184, by rfl⟩ : syracuseStep 605825 = 454369) B454369
theorem B1720075 : Blo 175800 1720075 := bstep (se 1 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 1720075 = 2580113) B2580113
theorem B2146267 : Blo 175800 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B4112441 : Blo 175800 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B507977 : Blo 175800 507977 := bstep (se 2 (by rfl) ⟨190491, by rfl⟩ : syracuseStep 507977 = 380983) B380983
theorem B673049 : Blo 175800 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B509287 : Blo 175800 509287 := bstep (se 1 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 509287 = 763931) B763931
theorem B509435 : Blo 175800 509435 := bstep (se 1 (by rfl) ⟨382076, by rfl⟩ : syracuseStep 509435 = 764153) B764153
theorem B509753 : Blo 175800 509753 := bstep (se 2 (by rfl) ⟨191157, by rfl⟩ : syracuseStep 509753 = 382315) B382315
theorem B378847 : Blo 175800 378847 := bstep (se 1 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 378847 = 568271) B568271
theorem B1460369 : Blo 175800 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B6703397 : Blo 175800 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B10504495 : Blo 175800 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B3066173 : Blo 175800 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B379343 : Blo 175800 379343 := bstep (se 1 (by rfl) ⟨284507, by rfl⟩ : syracuseStep 379343 = 569015) B569015
theorem B2279947 : Blo 175800 2279947 := bstep (se 1 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 2279947 = 3419921) B3419921
theorem B3852947 : Blo 175800 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B8276779 : Blo 175800 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B2280311 : Blo 175800 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B1363715 : Blo 175800 1363715 := bstep (se 1 (by rfl) ⟨1022786, by rfl⟩ : syracuseStep 1363715 = 2045573) B2045573
theorem B20598533 : Blo 175800 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B282431 : Blo 175800 282431 := bstep (se 1 (by rfl) ⟨211823, by rfl⟩ : syracuseStep 282431 = 423647) B423647
theorem B1134643 : Blo 175800 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B479371 : Blo 175800 479371 := bstep (se 1 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 479371 = 719057) B719057
theorem B807479 : Blo 175800 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B906065 : Blo 175800 906065 := bstep (se 2 (by rfl) ⟨339774, by rfl⟩ : syracuseStep 906065 = 679549) B679549
theorem B1135721 : Blo 175800 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B8673641 : Blo 175800 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B940787 : Blo 175800 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B449327 : Blo 175800 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B3824927 : Blo 175800 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B679337 : Blo 175800 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B482735 : Blo 175800 482735 := bstep (se 1 (by rfl) ⟨362051, by rfl⟩ : syracuseStep 482735 = 724103) B724103
theorem B449975 : Blo 175800 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B4120001 : Blo 175800 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B3661433 : Blo 175800 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B450623 : Blo 175800 450623 := bstep (se 1 (by rfl) ⟨337967, by rfl⟩ : syracuseStep 450623 = 675935) B675935
theorem B1531993 : Blo 175800 1531993 := bstep (se 2 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 1531993 = 1148995) B1148995
theorem B647297 : Blo 175800 647297 := bstep (se 2 (by rfl) ⟨242736, by rfl⟩ : syracuseStep 647297 = 485473) B485473
theorem B319783 : Blo 175800 319783 := bstep (se 1 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 319783 = 479675) B479675
theorem B1008071 : Blo 175800 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B909953 : Blo 175800 909953 := bstep (se 2 (by rfl) ⟨341232, by rfl⟩ : syracuseStep 909953 = 682465) B682465
theorem B1139359 : Blo 175800 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B451291 : Blo 175800 451291 := bstep (se 1 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 451291 = 676937) B676937
theorem B516827 : Blo 175800 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B2548745 : Blo 175800 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B680993 : Blo 175800 680993 := bstep (se 2 (by rfl) ⟨255372, by rfl⟩ : syracuseStep 680993 = 510745) B510745
theorem B288311 : Blo 175800 288311 := bstep (se 1 (by rfl) ⟨216233, by rfl⟩ : syracuseStep 288311 = 432467) B432467
theorem B321131 : Blo 175800 321131 := bstep (se 1 (by rfl) ⟨240848, by rfl⟩ : syracuseStep 321131 = 481697) B481697
theorem B27453329 : Blo 175800 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B452729 : Blo 175800 452729 := bstep (se 2 (by rfl) ⟨169773, by rfl⟩ : syracuseStep 452729 = 339547) B339547
theorem B5499737 : Blo 175800 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B5139571 : Blo 175800 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B2485633 : Blo 175800 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B716201 : Blo 175800 716201 := bstep (se 2 (by rfl) ⟨268575, by rfl⟩ : syracuseStep 716201 = 537151) B537151
theorem B32566859 : Blo 175800 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B18641441 : Blo 175800 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B1143719 : Blo 175800 1143719 := bstep (se 1 (by rfl) ⟨857789, by rfl⟩ : syracuseStep 1143719 = 1715579) B1715579
theorem B226471 : Blo 175800 226471 := bstep (se 1 (by rfl) ⟨169853, by rfl⟩ : syracuseStep 226471 = 339707) B339707
theorem B423407 : Blo 175800 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B358619 : Blo 175800 358619 := bstep (se 1 (by rfl) ⟨268964, by rfl⟩ : syracuseStep 358619 = 537929) B537929
theorem B424531 : Blo 175800 424531 := bstep (se 1 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 424531 = 636797) B636797
theorem B2030629 : Blo 175800 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B2293069 : Blo 175800 2293069 := bstep (se 3 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 2293069 = 859901) B859901
theorem B1637729 : Blo 175800 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B1080823 : Blo 175800 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B426377 : Blo 175800 426377 := bstep (se 2 (by rfl) ⟨159891, by rfl⟩ : syracuseStep 426377 = 319783) B319783
theorem B2032451 : Blo 175800 2032451 := bstep (se 1 (by rfl) ⟨1524338, by rfl⟩ : syracuseStep 2032451 = 3048677) B3048677
theorem B1278985 : Blo 175800 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B197959 : Blo 175800 197959 := bstep (se 1 (by rfl) ⟨148469, by rfl⟩ : syracuseStep 197959 = 296939) B296939
theorem B263771 : Blo 175800 263771 := bstep (se 1 (by rfl) ⟨197828, by rfl⟩ : syracuseStep 263771 = 395657) B395657
theorem B722627 : Blo 175800 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B1378205 : Blo 175800 1378205 := bstep (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) B516827
theorem B264503 : Blo 175800 264503 := bstep (se 1 (by rfl) ⟨198377, by rfl⟩ : syracuseStep 264503 = 396755) B396755
theorem B264551 : Blo 175800 264551 := bstep (se 1 (by rfl) ⟨198413, by rfl⟩ : syracuseStep 264551 = 396827) B396827
theorem B3770833 : Blo 175800 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B264683 : Blo 175800 264683 := bstep (se 1 (by rfl) ⟨198512, by rfl⟩ : syracuseStep 264683 = 397025) B397025
theorem B13732355 : Blo 175800 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B264815 : Blo 175800 264815 := bstep (se 1 (by rfl) ⟨198611, by rfl⟩ : syracuseStep 264815 = 397223) B397223
theorem B264923 : Blo 175800 264923 := bstep (se 1 (by rfl) ⟨198692, by rfl⟩ : syracuseStep 264923 = 397385) B397385
theorem B264935 : Blo 175800 264935 := bstep (se 1 (by rfl) ⟨198701, by rfl⟩ : syracuseStep 264935 = 397403) B397403
theorem B1510123 : Blo 175800 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B757147 : Blo 175800 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B265769 : Blo 175800 265769 := bstep (se 2 (by rfl) ⟨99663, by rfl⟩ : syracuseStep 265769 = 199327) B199327
theorem B364297 : Blo 175800 364297 := bstep (se 2 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 364297 = 273223) B273223
theorem B6852761 : Blo 175800 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B594215 : Blo 175800 594215 := bstep (se 1 (by rfl) ⟨445661, by rfl⟩ : syracuseStep 594215 = 891323) B891323
theorem B627191 : Blo 175800 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B3314177 : Blo 175800 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B9310727 : Blo 175800 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B299551 : Blo 175800 299551 := bstep (se 1 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 299551 = 449327) B449327
theorem B2364191 : Blo 175800 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B299983 : Blo 175800 299983 := bstep (se 1 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 299983 = 449975) B449975
theorem B300415 : Blo 175800 300415 := bstep (se 1 (by rfl) ⟨225311, by rfl⟩ : syracuseStep 300415 = 450623) B450623
theorem B1512857 : Blo 175800 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B431531 : Blo 175800 431531 := bstep (se 1 (by rfl) ⟨323648, by rfl⟩ : syracuseStep 431531 = 647297) B647297
theorem B268007 : Blo 175800 268007 := bstep (se 1 (by rfl) ⟨201005, by rfl⟩ : syracuseStep 268007 = 402011) B402011
theorem B759881 : Blo 175800 759881 := bstep (se 2 (by rfl) ⟨284955, by rfl⟩ : syracuseStep 759881 = 569911) B569911
theorem B268391 : Blo 175800 268391 := bstep (se 1 (by rfl) ⟨201293, by rfl⟩ : syracuseStep 268391 = 402587) B402587
theorem B400031 : Blo 175800 400031 := bstep (se 1 (by rfl) ⟨300023, by rfl⟩ : syracuseStep 400031 = 600047) B600047
theorem B301819 : Blo 175800 301819 := bstep (se 1 (by rfl) ⟨226364, by rfl⟩ : syracuseStep 301819 = 452729) B452729
theorem B596807 : Blo 175800 596807 := bstep (se 1 (by rfl) ⟨447605, by rfl⟩ : syracuseStep 596807 = 895211) B895211
theorem B269159 : Blo 175800 269159 := bstep (se 1 (by rfl) ⟨201869, by rfl⟩ : syracuseStep 269159 = 403739) B403739
theorem B301961 : Blo 175800 301961 := bstep (se 2 (by rfl) ⟨113235, by rfl⟩ : syracuseStep 301961 = 226471) B226471
theorem B269225 : Blo 175800 269225 := bstep (se 2 (by rfl) ⟨100959, by rfl⟩ : syracuseStep 269225 = 201919) B201919
theorem B269417 : Blo 175800 269417 := bstep (se 2 (by rfl) ⟨101031, by rfl⟩ : syracuseStep 269417 = 202063) B202063
theorem B400607 : Blo 175800 400607 := bstep (se 1 (by rfl) ⟨300455, by rfl⟩ : syracuseStep 400607 = 600911) B600911
theorem B269609 : Blo 175800 269609 := bstep (se 2 (by rfl) ⟨101103, by rfl⟩ : syracuseStep 269609 = 202207) B202207
theorem B400967 : Blo 175800 400967 := bstep (se 1 (by rfl) ⟨300725, by rfl⟩ : syracuseStep 400967 = 601451) B601451
theorem B335515 : Blo 175800 335515 := bstep (se 1 (by rfl) ⟨251636, by rfl⟩ : syracuseStep 335515 = 503273) B503273
theorem B597887 : Blo 175800 597887 := bstep (se 1 (by rfl) ⟨448415, by rfl⟩ : syracuseStep 597887 = 896831) B896831
theorem B12427627 : Blo 175800 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B401975 : Blo 175800 401975 := bstep (se 1 (by rfl) ⟨301481, by rfl⟩ : syracuseStep 401975 = 602963) B602963
theorem B762479 : Blo 175800 762479 := bstep (se 1 (by rfl) ⟨571859, by rfl⟩ : syracuseStep 762479 = 1143719) B1143719
theorem B598643 : Blo 175800 598643 := bstep (se 1 (by rfl) ⟨448982, by rfl⟩ : syracuseStep 598643 = 897965) B897965
theorem B566041 : Blo 175800 566041 := bstep (se 2 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 566041 = 424531) B424531
theorem B402299 : Blo 175800 402299 := bstep (se 1 (by rfl) ⟨301724, by rfl⟩ : syracuseStep 402299 = 603449) B603449
theorem B402335 : Blo 175800 402335 := bstep (se 1 (by rfl) ⟨301751, by rfl⟩ : syracuseStep 402335 = 603503) B603503
theorem B599723 : Blo 175800 599723 := bstep (se 1 (by rfl) ⟨449792, by rfl⟩ : syracuseStep 599723 = 899585) B899585
theorem B3057425 : Blo 175800 3057425 := bstep (se 2 (by rfl) ⟨1146534, by rfl⟩ : syracuseStep 3057425 = 2293069) B2293069
theorem B403271 : Blo 175800 403271 := bstep (se 1 (by rfl) ⟨302453, by rfl⟩ : syracuseStep 403271 = 604907) B604907
theorem B927679 : Blo 175800 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B1091819 : Blo 175800 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B403883 : Blo 175800 403883 := bstep (se 1 (by rfl) ⟨302912, by rfl⟩ : syracuseStep 403883 = 605825) B605825
theorem B2861689 : Blo 175800 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B338651 : Blo 175800 338651 := bstep (se 1 (by rfl) ⟨253988, by rfl⟩ : syracuseStep 338651 = 507977) B507977
theorem B2042657 : Blo 175800 2042657 := bstep (se 2 (by rfl) ⟨765996, by rfl⟩ : syracuseStep 2042657 = 1531993) B1531993
theorem B1519145 : Blo 175800 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B601721 : Blo 175800 601721 := bstep (se 2 (by rfl) ⟨225645, by rfl⟩ : syracuseStep 601721 = 451291) B451291
theorem B896669 : Blo 175800 896669 := bstep (se 3 (by rfl) ⟨168125, by rfl⟩ : syracuseStep 896669 = 336251) B336251
theorem B339623 : Blo 175800 339623 := bstep (se 1 (by rfl) ⟨254717, by rfl⟩ : syracuseStep 339623 = 509435) B509435
theorem B176031 : Blo 175800 176031 := bstep (se 1 (by rfl) ⟨132023, by rfl⟩ : syracuseStep 176031 = 264047) B264047
theorem B2273183 : Blo 175800 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B176155 : Blo 175800 176155 := bstep (se 1 (by rfl) ⟨132116, by rfl⟩ : syracuseStep 176155 = 264233) B264233
theorem B176175 : Blo 175800 176175 := bstep (se 1 (by rfl) ⟨132131, by rfl⟩ : syracuseStep 176175 = 264263) B264263
theorem B176295 : Blo 175800 176295 := bstep (se 1 (by rfl) ⟨132221, by rfl⟩ : syracuseStep 176295 = 264443) B264443
theorem B4468931 : Blo 175800 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B2044115 : Blo 175800 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B766235 : Blo 175800 766235 := bstep (se 1 (by rfl) ⟨574676, by rfl⟩ : syracuseStep 766235 = 1149353) B1149353
theorem B176431 : Blo 175800 176431 := bstep (se 1 (by rfl) ⟨132323, by rfl⟩ : syracuseStep 176431 = 264647) B264647
theorem B176575 : Blo 175800 176575 := bstep (se 1 (by rfl) ⟨132431, by rfl⟩ : syracuseStep 176575 = 264863) B264863
theorem B897479 : Blo 175800 897479 := bstep (se 1 (by rfl) ⟨673109, by rfl⟩ : syracuseStep 897479 = 1346219) B1346219
theorem B176607 : Blo 175800 176607 := bstep (se 1 (by rfl) ⟨132455, by rfl⟩ : syracuseStep 176607 = 264911) B264911
theorem B176671 : Blo 175800 176671 := bstep (se 1 (by rfl) ⟨132503, by rfl⟩ : syracuseStep 176671 = 265007) B265007
theorem B2798135 : Blo 175800 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B1520207 : Blo 175800 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B176751 : Blo 175800 176751 := bstep (se 1 (by rfl) ⟨132563, by rfl⟩ : syracuseStep 176751 = 265127) B265127
theorem B176871 : Blo 175800 176871 := bstep (se 1 (by rfl) ⟨132653, by rfl⟩ : syracuseStep 176871 = 265307) B265307
theorem B176923 : Blo 175800 176923 := bstep (se 1 (by rfl) ⟨132692, by rfl⟩ : syracuseStep 176923 = 265385) B265385
theorem B177199 : Blo 175800 177199 := bstep (se 1 (by rfl) ⟨132899, by rfl⟩ : syracuseStep 177199 = 265799) B265799
theorem B177319 : Blo 175800 177319 := bstep (se 1 (by rfl) ⟨132989, by rfl⟩ : syracuseStep 177319 = 265979) B265979
theorem B668857 : Blo 175800 668857 := bstep (se 2 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 668857 = 501643) B501643
theorem B505129 : Blo 175800 505129 := bstep (se 2 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 505129 = 378847) B378847
theorem B177479 : Blo 175800 177479 := bstep (se 1 (by rfl) ⟨133109, by rfl⟩ : syracuseStep 177479 = 266219) B266219
theorem B538319 : Blo 175800 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B14005993 : Blo 175800 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B604043 : Blo 175800 604043 := bstep (se 1 (by rfl) ⟨453032, by rfl⟩ : syracuseStep 604043 = 906065) B906065
theorem B505835 : Blo 175800 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B178171 : Blo 175800 178171 := bstep (se 1 (by rfl) ⟨133628, by rfl⟩ : syracuseStep 178171 = 267257) B267257
theorem B178303 : Blo 175800 178303 := bstep (se 1 (by rfl) ⟨133727, by rfl⟩ : syracuseStep 178303 = 267455) B267455
theorem B178399 : Blo 175800 178399 := bstep (se 1 (by rfl) ⟨133799, by rfl⟩ : syracuseStep 178399 = 267599) B267599
theorem B178459 : Blo 175800 178459 := bstep (se 1 (by rfl) ⟨133844, by rfl⟩ : syracuseStep 178459 = 267689) B267689
theorem B178495 : Blo 175800 178495 := bstep (se 1 (by rfl) ⟨133871, by rfl⟩ : syracuseStep 178495 = 267743) B267743
theorem B178559 : Blo 175800 178559 := bstep (se 1 (by rfl) ⟨133919, by rfl⟩ : syracuseStep 178559 = 267839) B267839
theorem B1129085 : Blo 175800 1129085 := bstep (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) B423407
theorem B178879 : Blo 175800 178879 := bstep (se 1 (by rfl) ⟨134159, by rfl⟩ : syracuseStep 178879 = 268319) B268319
theorem B5782427 : Blo 175800 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B179167 : Blo 175800 179167 := bstep (se 1 (by rfl) ⟨134375, by rfl⟩ : syracuseStep 179167 = 268751) B268751
theorem B179227 : Blo 175800 179227 := bstep (se 1 (by rfl) ⟨134420, by rfl⟩ : syracuseStep 179227 = 268841) B268841
theorem B179367 : Blo 175800 179367 := bstep (se 1 (by rfl) ⟨134525, by rfl⟩ : syracuseStep 179367 = 269051) B269051
theorem B179451 : Blo 175800 179451 := bstep (se 1 (by rfl) ⟨134588, by rfl⟩ : syracuseStep 179451 = 269177) B269177
theorem B1359341 : Blo 175800 1359341 := bstep (se 3 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 1359341 = 509753) B509753
theorem B310825 : Blo 175800 310825 := bstep (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) B233119
theorem B2440955 : Blo 175800 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B1359827 : Blo 175800 1359827 := bstep (se 1 (by rfl) ⟨1019870, by rfl⟩ : syracuseStep 1359827 = 2039741) B2039741
theorem B639161 : Blo 175800 639161 := bstep (se 2 (by rfl) ⟨239685, by rfl⟩ : syracuseStep 639161 = 479371) B479371
theorem B672047 : Blo 175800 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B606635 : Blo 175800 606635 := bstep (se 1 (by rfl) ⟨454976, by rfl⟩ : syracuseStep 606635 = 909953) B909953
theorem B214087 : Blo 175800 214087 := bstep (se 1 (by rfl) ⟨160565, by rfl⟩ : syracuseStep 214087 = 321131) B321131
theorem B18302219 : Blo 175800 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B10274525 : Blo 175800 10274525 := bstep (se 3 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 10274525 = 3852947) B3852947
theorem B477467 : Blo 175800 477467 := bstep (se 1 (by rfl) ⟨358100, by rfl⟩ : syracuseStep 477467 = 716201) B716201
theorem B21711239 : Blo 175800 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B445247 : Blo 175800 445247 := bstep (se 1 (by rfl) ⟨333935, by rfl⟩ : syracuseStep 445247 = 667871) B667871
theorem B2411707 : Blo 175800 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B380231 : Blo 175800 380231 := bstep (se 1 (by rfl) ⟨285173, by rfl⟩ : syracuseStep 380231 = 570347) B570347
theorem B2707505 : Blo 175800 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B250651 : Blo 175800 250651 := bstep (se 1 (by rfl) ⟨187988, by rfl⟩ : syracuseStep 250651 = 375977) B375977
theorem B2741627 : Blo 175800 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B677879 : Blo 175800 677879 := bstep (se 1 (by rfl) ⟨508409, by rfl⟩ : syracuseStep 677879 = 1016819) B1016819
theorem B448699 : Blo 175800 448699 := bstep (se 1 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 448699 = 673049) B673049
theorem B252895 : Blo 175800 252895 := bstep (se 1 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 252895 = 379343) B379343
theorem B679049 : Blo 175800 679049 := bstep (se 2 (by rfl) ⟨254643, by rfl⟩ : syracuseStep 679049 = 509287) B509287
theorem B613601 : Blo 175800 613601 := bstep (se 2 (by rfl) ⟨230100, by rfl⟩ : syracuseStep 613601 = 460201) B460201
theorem B3825269 : Blo 175800 3825269 := bstep (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) B358619
theorem B909143 : Blo 175800 909143 := bstep (se 1 (by rfl) ⟨681857, by rfl⟩ : syracuseStep 909143 = 1363715) B1363715
theorem B188287 : Blo 175800 188287 := bstep (se 1 (by rfl) ⟨141215, by rfl⟩ : syracuseStep 188287 = 282431) B282431
theorem B614585 : Blo 175800 614585 := bstep (se 2 (by rfl) ⟨230469, by rfl⟩ : syracuseStep 614585 = 460939) B460939
theorem B3039929 : Blo 175800 3039929 := bstep (se 2 (by rfl) ⟨1139973, by rfl⟩ : syracuseStep 3039929 = 2279947) B2279947
theorem B11035705 : Blo 175800 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B681979 : Blo 175800 681979 := bstep (se 1 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 681979 = 1022969) B1022969
theorem B2549951 : Blo 175800 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B2156777 : Blo 175800 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B452891 : Blo 175800 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B321823 : Blo 175800 321823 := bstep (se 1 (by rfl) ⟨241367, by rfl⟩ : syracuseStep 321823 = 482735) B482735
theorem B2746667 : Blo 175800 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B3894317 : Blo 175800 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B3075317 : Blo 175800 3075317 := bstep (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) B288311
theorem B1699163 : Blo 175800 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B453995 : Blo 175800 453995 := bstep (se 1 (by rfl) ⟨340496, by rfl⟩ : syracuseStep 453995 = 680993) B680993
theorem B1011487 : Blo 175800 1011487 := bstep (se 1 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 1011487 = 1517231) B1517231
theorem B5796029 : Blo 175800 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B3666491 : Blo 175800 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B1012945 : Blo 175800 1012945 := bstep (se 2 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 1012945 = 759709) B759709
theorem B5141879 : Blo 175800 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B817879 : Blo 175800 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B28146653 : Blo 175800 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B1441097 : Blo 175800 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B1277603 : Blo 175800 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B2293433 : Blo 175800 2293433 := bstep (se 2 (by rfl) ⟨860037, by rfl⟩ : syracuseStep 2293433 = 1720075) B1720075
theorem B426107 : Blo 175800 426107 := bstep (se 1 (by rfl) ⟨319580, by rfl⟩ : syracuseStep 426107 = 639161) B639161
theorem B1638893 : Blo 175800 1638893 := bstep (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) B614585
theorem B754721 : Blo 175800 754721 := bstep (se 2 (by rfl) ⟨283020, by rfl⟩ : syracuseStep 754721 = 566041) B566041
theorem B6849683 : Blo 175800 6849683 := bstep (se 1 (by rfl) ⟨5137262, by rfl⟩ : syracuseStep 6849683 = 10274525) B10274525
theorem B918803 : Blo 175800 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B1705313 : Blo 175800 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B14714273 : Blo 175800 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B263945 : Blo 175800 263945 := bstep (se 2 (by rfl) ⟨98979, by rfl⟩ : syracuseStep 263945 = 197959) B197959
theorem B296831 : Blo 175800 296831 := bstep (se 1 (by rfl) ⟨222623, by rfl⟩ : syracuseStep 296831 = 445247) B445247
theorem B1805003 : Blo 175800 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B396143 : Blo 175800 396143 := bstep (se 1 (by rfl) ⟨297107, by rfl⟩ : syracuseStep 396143 = 594215) B594215
theorem B429097 : Blo 175800 429097 := bstep (se 2 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 429097 = 321823) B321823
theorem B1576127 : Blo 175800 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B7311005 : Blo 175800 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B3215609 : Blo 175800 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B266687 : Blo 175800 266687 := bstep (se 1 (by rfl) ⟨200015, by rfl⟩ : syracuseStep 266687 = 400031) B400031
theorem B397871 : Blo 175800 397871 := bstep (se 1 (by rfl) ⟨298403, by rfl⟩ : syracuseStep 397871 = 596807) B596807
theorem B201307 : Blo 175800 201307 := bstep (se 1 (by rfl) ⟨150980, by rfl⟩ : syracuseStep 201307 = 301961) B301961
theorem B267071 : Blo 175800 267071 := bstep (se 1 (by rfl) ⟨200303, by rfl⟩ : syracuseStep 267071 = 400607) B400607
theorem B1348649 : Blo 175800 1348649 := bstep (se 2 (by rfl) ⟨505743, by rfl⟩ : syracuseStep 1348649 = 1011487) B1011487
theorem B267311 : Blo 175800 267311 := bstep (se 1 (by rfl) ⟨200483, by rfl⟩ : syracuseStep 267311 = 400967) B400967
theorem B398591 : Blo 175800 398591 := bstep (se 1 (by rfl) ⟨298943, by rfl⟩ : syracuseStep 398591 = 597887) B597887
theorem B267983 : Blo 175800 267983 := bstep (se 1 (by rfl) ⟨200987, by rfl⟩ : syracuseStep 267983 = 401975) B401975
theorem B399095 : Blo 175800 399095 := bstep (se 1 (by rfl) ⟨299321, by rfl⟩ : syracuseStep 399095 = 598643) B598643
theorem B268199 : Blo 175800 268199 := bstep (se 1 (by rfl) ⟨201149, by rfl⟩ : syracuseStep 268199 = 402299) B402299
theorem B268223 : Blo 175800 268223 := bstep (se 1 (by rfl) ⟨201167, by rfl⟩ : syracuseStep 268223 = 402335) B402335
theorem B399401 : Blo 175800 399401 := bstep (se 2 (by rfl) ⟨149775, by rfl⟩ : syracuseStep 399401 = 299551) B299551
theorem B334201 : Blo 175800 334201 := bstep (se 2 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 334201 = 250651) B250651
theorem B399815 : Blo 175800 399815 := bstep (se 1 (by rfl) ⟨299861, by rfl⟩ : syracuseStep 399815 = 599723) B599723
theorem B2038283 : Blo 175800 2038283 := bstep (se 1 (by rfl) ⟨1528712, by rfl⟩ : syracuseStep 2038283 = 3057425) B3057425
theorem B268847 : Blo 175800 268847 := bstep (se 1 (by rfl) ⟨201635, by rfl⟩ : syracuseStep 268847 = 403271) B403271
theorem B399977 : Blo 175800 399977 := bstep (se 2 (by rfl) ⟨149991, by rfl⟩ : syracuseStep 399977 = 299983) B299983
theorem B727879 : Blo 175800 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B301927 : Blo 175800 301927 := bstep (se 1 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 301927 = 452891) B452891
theorem B891809 : Blo 175800 891809 := bstep (se 2 (by rfl) ⟨334428, by rfl⟩ : syracuseStep 891809 = 668857) B668857
theorem B1350593 : Blo 175800 1350593 := bstep (se 2 (by rfl) ⟨506472, by rfl⟩ : syracuseStep 1350593 = 1012945) B1012945
theorem B269255 : Blo 175800 269255 := bstep (se 1 (by rfl) ⟨201941, by rfl⟩ : syracuseStep 269255 = 403883) B403883
theorem B400553 : Blo 175800 400553 := bstep (se 2 (by rfl) ⟨150207, by rfl⟩ : syracuseStep 400553 = 300415) B300415
theorem B2596211 : Blo 175800 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B302663 : Blo 175800 302663 := bstep (se 1 (by rfl) ⟨226997, by rfl⟩ : syracuseStep 302663 = 453995) B453995
theorem B401147 : Blo 175800 401147 := bstep (se 1 (by rfl) ⟨300860, by rfl⟩ : syracuseStep 401147 = 601721) B601721
theorem B597779 : Blo 175800 597779 := bstep (se 1 (by rfl) ⟨448334, by rfl⟩ : syracuseStep 597779 = 896669) B896669
theorem B1515455 : Blo 175800 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B598265 : Blo 175800 598265 := bstep (se 2 (by rfl) ⟨224349, by rfl⟩ : syracuseStep 598265 = 448699) B448699
theorem B598319 : Blo 175800 598319 := bstep (se 1 (by rfl) ⟨448739, by rfl⟩ : syracuseStep 598319 = 897479) B897479
theorem B1090505 : Blo 175800 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B402425 : Blo 175800 402425 := bstep (se 2 (by rfl) ⟨150909, by rfl⟩ : syracuseStep 402425 = 301819) B301819
theorem B402695 : Blo 175800 402695 := bstep (se 1 (by rfl) ⟨302021, by rfl⟩ : syracuseStep 402695 = 604043) B604043
theorem B337193 : Blo 175800 337193 := bstep (se 2 (by rfl) ⟨126447, by rfl⟩ : syracuseStep 337193 = 252895) B252895
theorem B337223 : Blo 175800 337223 := bstep (se 1 (by rfl) ⟨252917, by rfl⟩ : syracuseStep 337223 = 505835) B505835
theorem B960731 : Blo 175800 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B404423 : Blo 175800 404423 := bstep (se 1 (by rfl) ⟨303317, by rfl⟩ : syracuseStep 404423 = 606635) B606635
theorem B1354967 : Blo 175800 1354967 := bstep (se 1 (by rfl) ⟨1016225, by rfl⟩ : syracuseStep 1354967 = 2032451) B2032451
theorem B12201479 : Blo 175800 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B175847 : Blo 175800 175847 := bstep (se 1 (by rfl) ⟨131885, by rfl⟩ : syracuseStep 175847 = 263771) B263771
theorem B176335 : Blo 175800 176335 := bstep (se 1 (by rfl) ⟨132251, by rfl⟩ : syracuseStep 176335 = 264503) B264503
theorem B176367 : Blo 175800 176367 := bstep (se 1 (by rfl) ⟨132275, by rfl⟩ : syracuseStep 176367 = 264551) B264551
theorem B176455 : Blo 175800 176455 := bstep (se 1 (by rfl) ⟨132341, by rfl⟩ : syracuseStep 176455 = 264683) B264683
theorem B9154903 : Blo 175800 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B176543 : Blo 175800 176543 := bstep (se 1 (by rfl) ⟨132407, by rfl⟩ : syracuseStep 176543 = 264815) B264815
theorem B176615 : Blo 175800 176615 := bstep (se 1 (by rfl) ⟨132461, by rfl⟩ : syracuseStep 176615 = 264923) B264923
theorem B176623 : Blo 175800 176623 := bstep (se 1 (by rfl) ⟨132467, by rfl⟩ : syracuseStep 176623 = 264935) B264935
theorem B177179 : Blo 175800 177179 := bstep (se 1 (by rfl) ⟨132884, by rfl⟩ : syracuseStep 177179 = 265769) B265769
theorem B4568507 : Blo 175800 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B2209451 : Blo 175800 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B6207151 : Blo 175800 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B5027777 : Blo 175800 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B3815585 : Blo 175800 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B2013497 : Blo 175800 2013497 := bstep (se 2 (by rfl) ⟨755061, by rfl⟩ : syracuseStep 2013497 = 1510123) B1510123
theorem B178671 : Blo 175800 178671 := bstep (se 1 (by rfl) ⟨134003, by rfl⟩ : syracuseStep 178671 = 268007) B268007
theorem B506587 : Blo 175800 506587 := bstep (se 1 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 506587 = 759881) B759881
theorem B178927 : Blo 175800 178927 := bstep (se 1 (by rfl) ⟨134195, by rfl⟩ : syracuseStep 178927 = 268391) B268391
theorem B4602997 : Blo 175800 4602997 := bstep (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) B431531
theorem B179439 : Blo 175800 179439 := bstep (se 1 (by rfl) ⟨134579, by rfl⟩ : syracuseStep 179439 = 269159) B269159
theorem B179483 : Blo 175800 179483 := bstep (se 1 (by rfl) ⟨134612, by rfl⟩ : syracuseStep 179483 = 269225) B269225
theorem B179611 : Blo 175800 179611 := bstep (se 1 (by rfl) ⟨134708, by rfl⟩ : syracuseStep 179611 = 269417) B269417
theorem B409067 : Blo 175800 409067 := bstep (se 1 (by rfl) ⟨306800, by rfl⟩ : syracuseStep 409067 = 613601) B613601
theorem B179739 : Blo 175800 179739 := bstep (se 1 (by rfl) ⟨134804, by rfl⟩ : syracuseStep 179739 = 269609) B269609
theorem B606095 : Blo 175800 606095 := bstep (se 1 (by rfl) ⟨454571, by rfl⟩ : syracuseStep 606095 = 909143) B909143
theorem B508319 : Blo 175800 508319 := bstep (se 1 (by rfl) ⟨381239, by rfl⟩ : syracuseStep 508319 = 762479) B762479
theorem B7324445 : Blo 175800 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B673505 : Blo 175800 673505 := bstep (se 2 (by rfl) ⟨252564, by rfl⟩ : syracuseStep 673505 = 505129) B505129
theorem B1361771 : Blo 175800 1361771 := bstep (se 1 (by rfl) ⟨1021328, by rfl⟩ : syracuseStep 1361771 = 2042657) B2042657
theorem B2050211 : Blo 175800 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B1132775 : Blo 175800 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B1362743 : Blo 175800 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B510823 : Blo 175800 510823 := bstep (se 1 (by rfl) ⟨383117, by rfl⟩ : syracuseStep 510823 = 766235) B766235
theorem B2444327 : Blo 175800 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B3427919 : Blo 175800 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B3854951 : Blo 175800 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B18764435 : Blo 175800 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B1004197 : Blo 175800 1004197 := bstep (se 4 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 1004197 = 188287) B188287
theorem B414433 : Blo 175800 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B447353 : Blo 175800 447353 := bstep (se 2 (by rfl) ⟨167757, by rfl⟩ : syracuseStep 447353 = 335515) B335515
theorem B906227 : Blo 175800 906227 := bstep (se 1 (by rfl) ⟨679670, by rfl⟩ : syracuseStep 906227 = 1359341) B1359341
theorem B1528955 : Blo 175800 1528955 := bstep (se 1 (by rfl) ⟨1146716, by rfl⟩ : syracuseStep 1528955 = 2293433) B2293433
theorem B1627303 : Blo 175800 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B906551 : Blo 175800 906551 := bstep (se 1 (by rfl) ⟨679913, by rfl⟩ : syracuseStep 906551 = 1359827) B1359827
theorem B448031 : Blo 175800 448031 := bstep (se 1 (by rfl) ⟨336023, by rfl⟩ : syracuseStep 448031 = 672047) B672047
theorem B284251 : Blo 175800 284251 := bstep (se 1 (by rfl) ⟨213188, by rfl⟩ : syracuseStep 284251 = 426377) B426377
theorem B16570169 : Blo 175800 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B481751 : Blo 175800 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B285449 : Blo 175800 285449 := bstep (se 2 (by rfl) ⟨107043, by rfl⟩ : syracuseStep 285449 = 214087) B214087
theorem B318311 : Blo 175800 318311 := bstep (se 1 (by rfl) ⟨238733, by rfl⟩ : syracuseStep 318311 = 477467) B477467
theorem B14474159 : Blo 175800 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B253487 : Blo 175800 253487 := bstep (se 1 (by rfl) ⟨190115, by rfl⟩ : syracuseStep 253487 = 380231) B380231
theorem B1236905 : Blo 175800 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B909305 : Blo 175800 909305 := bstep (se 2 (by rfl) ⟨340989, by rfl⟩ : syracuseStep 909305 = 681979) B681979
theorem B418127 : Blo 175800 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B1008571 : Blo 175800 1008571 := bstep (se 1 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 1008571 = 1512857) B1512857
theorem B451919 : Blo 175800 451919 := bstep (se 1 (by rfl) ⟨338939, by rfl⟩ : syracuseStep 451919 = 677879) B677879
theorem B1009529 : Blo 175800 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B452699 : Blo 175800 452699 := bstep (se 1 (by rfl) ⟨339524, by rfl⟩ : syracuseStep 452699 = 679049) B679049
theorem B485729 : Blo 175800 485729 := bstep (se 2 (by rfl) ⟨182148, by rfl⟩ : syracuseStep 485729 = 364297) B364297
theorem B2550179 : Blo 175800 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B2026619 : Blo 175800 2026619 := bstep (se 1 (by rfl) ⟨1519964, by rfl⟩ : syracuseStep 2026619 = 3039929) B3039929
theorem B1699967 : Blo 175800 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B1437851 : Blo 175800 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B225767 : Blo 175800 225767 := bstep (se 1 (by rfl) ⟨169325, by rfl⟩ : syracuseStep 225767 = 338651) B338651
theorem B18674657 : Blo 175800 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B1012763 : Blo 175800 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B226415 : Blo 175800 226415 := bstep (se 1 (by rfl) ⟨169811, by rfl⟩ : syracuseStep 226415 = 339623) B339623
theorem B3864019 : Blo 175800 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B2979287 : Blo 175800 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B1865423 : Blo 175800 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B1013471 : Blo 175800 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B358879 : Blo 175800 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B752723 : Blo 175800 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B851735 : Blo 175800 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B4882963 : Blo 175800 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B1115005 : Blo 175800 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B1344761 : Blo 175800 1344761 := bstep (se 2 (by rfl) ⟨504285, by rfl⟩ : syracuseStep 1344761 = 1008571) B1008571
theorem B197887 : Blo 175800 197887 := bstep (se 1 (by rfl) ⟨148415, by rfl⟩ : syracuseStep 197887 = 296831) B296831
theorem B755183 : Blo 175800 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B264095 : Blo 175800 264095 := bstep (se 1 (by rfl) ⟨198071, by rfl⟩ : syracuseStep 264095 = 396143) B396143
theorem B1050751 : Blo 175800 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B265247 : Blo 175800 265247 := bstep (se 1 (by rfl) ⟨198935, by rfl⟩ : syracuseStep 265247 = 397871) B397871
theorem B298235 : Blo 175800 298235 := bstep (se 1 (by rfl) ⟨223676, by rfl⟩ : syracuseStep 298235 = 447353) B447353
theorem B1019303 : Blo 175800 1019303 := bstep (se 1 (by rfl) ⟨764477, by rfl⟩ : syracuseStep 1019303 = 1528955) B1528955
theorem B265727 : Blo 175800 265727 := bstep (se 1 (by rfl) ⟨199295, by rfl⟩ : syracuseStep 265727 = 398591) B398591
theorem B298687 : Blo 175800 298687 := bstep (se 1 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 298687 = 448031) B448031
theorem B266063 : Blo 175800 266063 := bstep (se 1 (by rfl) ⟨199547, by rfl⟩ : syracuseStep 266063 = 399095) B399095
theorem B11046779 : Blo 175800 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B266267 : Blo 175800 266267 := bstep (se 1 (by rfl) ⟨199700, by rfl⟩ : syracuseStep 266267 = 399401) B399401
theorem B266543 : Blo 175800 266543 := bstep (se 1 (by rfl) ⟨199907, by rfl⟩ : syracuseStep 266543 = 399815) B399815
theorem B266651 : Blo 175800 266651 := bstep (se 1 (by rfl) ⟨199988, by rfl⟩ : syracuseStep 266651 = 399977) B399977
theorem B594539 : Blo 175800 594539 := bstep (se 1 (by rfl) ⟨445904, by rfl⟩ : syracuseStep 594539 = 891809) B891809
theorem B267035 : Blo 175800 267035 := bstep (se 1 (by rfl) ⟨200276, by rfl⟩ : syracuseStep 267035 = 400553) B400553
theorem B201775 : Blo 175800 201775 := bstep (se 1 (by rfl) ⟨151331, by rfl⟩ : syracuseStep 201775 = 302663) B302663
theorem B267431 : Blo 175800 267431 := bstep (se 1 (by rfl) ⟨200573, by rfl⟩ : syracuseStep 267431 = 401147) B401147
theorem B398519 : Blo 175800 398519 := bstep (se 1 (by rfl) ⟨298889, by rfl⟩ : syracuseStep 398519 = 597779) B597779
theorem B824603 : Blo 175800 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B398843 : Blo 175800 398843 := bstep (se 1 (by rfl) ⟨299132, by rfl⟩ : syracuseStep 398843 = 598265) B598265
theorem B398879 : Blo 175800 398879 := bstep (se 1 (by rfl) ⟨299159, by rfl⟩ : syracuseStep 398879 = 598319) B598319
theorem B24549317 : Blo 175800 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B727003 : Blo 175800 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B268283 : Blo 175800 268283 := bstep (se 1 (by rfl) ⟨201212, by rfl⟩ : syracuseStep 268283 = 402425) B402425
theorem B268409 : Blo 175800 268409 := bstep (se 2 (by rfl) ⟨100653, by rfl⟩ : syracuseStep 268409 = 201307) B201307
theorem B268463 : Blo 175800 268463 := bstep (se 1 (by rfl) ⟨201347, by rfl⟩ : syracuseStep 268463 = 402695) B402695
theorem B301279 : Blo 175800 301279 := bstep (se 1 (by rfl) ⟨225959, by rfl⟩ : syracuseStep 301279 = 451919) B451919
theorem B301799 : Blo 175800 301799 := bstep (se 1 (by rfl) ⟨226349, by rfl⟩ : syracuseStep 301799 = 452699) B452699
theorem B2169737 : Blo 175800 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B5152025 : Blo 175800 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B269615 : Blo 175800 269615 := bstep (se 1 (by rfl) ⟨202211, by rfl⟩ : syracuseStep 269615 = 404423) B404423
theorem B761197 : Blo 175800 761197 := bstep (se 3 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 761197 = 285449) B285449
theorem B1351079 : Blo 175800 1351079 := bstep (se 1 (by rfl) ⟨1013309, by rfl⟩ : syracuseStep 1351079 = 2026619) B2026619
theorem B8134319 : Blo 175800 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B958567 : Blo 175800 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B402569 : Blo 175800 402569 := bstep (se 2 (by rfl) ⟨150963, by rfl⟩ : syracuseStep 402569 = 301927) B301927
theorem B3351851 : Blo 175800 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B501815 : Blo 175800 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B272711 : Blo 175800 272711 := bstep (se 1 (by rfl) ⟨204533, by rfl⟩ : syracuseStep 272711 = 409067) B409067
theorem B567823 : Blo 175800 567823 := bstep (se 1 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 567823 = 851735) B851735
theorem B404063 : Blo 175800 404063 := bstep (se 1 (by rfl) ⟨303047, by rfl⟩ : syracuseStep 404063 = 606095) B606095
theorem B338879 : Blo 175800 338879 := bstep (se 1 (by rfl) ⟨254159, by rfl⟩ : syracuseStep 338879 = 508319) B508319
theorem B1092595 : Blo 175800 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B503147 : Blo 175800 503147 := bstep (se 1 (by rfl) ⟨377360, by rfl⟩ : syracuseStep 503147 = 754721) B754721
theorem B4566455 : Blo 175800 4566455 := bstep (se 1 (by rfl) ⟨3424841, by rfl⟩ : syracuseStep 4566455 = 6849683) B6849683
theorem B9809515 : Blo 175800 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B175963 : Blo 175800 175963 := bstep (se 1 (by rfl) ⟨131972, by rfl⟩ : syracuseStep 175963 = 263945) B263945
theorem B602045 : Blo 175800 602045 := bstep (se 3 (by rfl) ⟨112883, by rfl⟩ : syracuseStep 602045 = 225767) B225767
theorem B2143739 : Blo 175800 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B603773 : Blo 175800 603773 := bstep (se 3 (by rfl) ⟨113207, by rfl⟩ : syracuseStep 603773 = 226415) B226415
theorem B177791 : Blo 175800 177791 := bstep (se 1 (by rfl) ⟨133343, by rfl⟩ : syracuseStep 177791 = 266687) B266687
theorem B2569967 : Blo 175800 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B178047 : Blo 175800 178047 := bstep (se 1 (by rfl) ⟨133535, by rfl⟩ : syracuseStep 178047 = 267071) B267071
theorem B604151 : Blo 175800 604151 := bstep (se 1 (by rfl) ⟨453113, by rfl⟩ : syracuseStep 604151 = 906227) B906227
theorem B899099 : Blo 175800 899099 := bstep (se 1 (by rfl) ⟨674324, by rfl⟩ : syracuseStep 899099 = 1348649) B1348649
theorem B178207 : Blo 175800 178207 := bstep (se 1 (by rfl) ⟨133655, by rfl⟩ : syracuseStep 178207 = 267311) B267311
theorem B899261 : Blo 175800 899261 := bstep (se 3 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 899261 = 337223) B337223
theorem B604367 : Blo 175800 604367 := bstep (se 1 (by rfl) ⟨453275, by rfl⟩ : syracuseStep 604367 = 906551) B906551
theorem B178655 : Blo 175800 178655 := bstep (se 1 (by rfl) ⟨133991, by rfl⟩ : syracuseStep 178655 = 267983) B267983
theorem B178799 : Blo 175800 178799 := bstep (se 1 (by rfl) ⟨134099, by rfl⟩ : syracuseStep 178799 = 268199) B268199
theorem B178815 : Blo 175800 178815 := bstep (se 1 (by rfl) ⟨134111, by rfl⟩ : syracuseStep 178815 = 268223) B268223
theorem B572129 : Blo 175800 572129 := bstep (se 2 (by rfl) ⟨214548, by rfl⟩ : syracuseStep 572129 = 429097) B429097
theorem B1358855 : Blo 175800 1358855 := bstep (se 1 (by rfl) ⟨1019141, by rfl⟩ : syracuseStep 1358855 = 2038283) B2038283
theorem B179231 : Blo 175800 179231 := bstep (se 1 (by rfl) ⟨134423, by rfl⟩ : syracuseStep 179231 = 268847) B268847
theorem B9649439 : Blo 175800 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B900395 : Blo 175800 900395 := bstep (se 1 (by rfl) ⟨675296, by rfl⟩ : syracuseStep 900395 = 1350593) B1350593
theorem B179503 : Blo 175800 179503 := bstep (se 1 (by rfl) ⟨134627, by rfl⟩ : syracuseStep 179503 = 269255) B269255
theorem B606203 : Blo 175800 606203 := bstep (se 1 (by rfl) ⟨454652, by rfl⟩ : syracuseStep 606203 = 909305) B909305
theorem B12206537 : Blo 175800 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B673019 : Blo 175800 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B640487 : Blo 175800 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B379001 : Blo 175800 379001 := bstep (se 2 (by rfl) ⟨142125, by rfl⟩ : syracuseStep 379001 = 284251) B284251
theorem B903311 : Blo 175800 903311 := bstep (se 1 (by rfl) ⟨677483, by rfl⟩ : syracuseStep 903311 = 1354967) B1354967
theorem B8276201 : Blo 175800 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B1133311 : Blo 175800 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B445601 : Blo 175800 445601 := bstep (se 2 (by rfl) ⟨167100, by rfl⟩ : syracuseStep 445601 = 334201) B334201
theorem B478505 : Blo 175800 478505 := bstep (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) B358879
theorem B675175 : Blo 175800 675175 := bstep (se 1 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 675175 = 1012763) B1012763
theorem B675449 : Blo 175800 675449 := bstep (se 2 (by rfl) ⟨253293, by rfl⟩ : syracuseStep 675449 = 506587) B506587
theorem B1986191 : Blo 175800 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B3395317 : Blo 175800 3395317 := bstep (se 5 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 3395317 = 318311) B318311
theorem B970505 : Blo 175800 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B675647 : Blo 175800 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B2543723 : Blo 175800 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B675965 : Blo 175800 675965 := bstep (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) B253487
theorem B284071 : Blo 175800 284071 := bstep (se 1 (by rfl) ⟨213053, by rfl⟩ : syracuseStep 284071 = 426107) B426107
theorem B612535 : Blo 175800 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B1136875 : Blo 175800 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B449003 : Blo 175800 449003 := bstep (se 1 (by rfl) ⟨336752, by rfl⟩ : syracuseStep 449003 = 673505) B673505
theorem B907847 : Blo 175800 907847 := bstep (se 1 (by rfl) ⟨680885, by rfl⟩ : syracuseStep 907847 = 1361771) B1361771
theorem B1366807 : Blo 175800 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B1203335 : Blo 175800 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B908495 : Blo 175800 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B1629551 : Blo 175800 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B2285279 : Blo 175800 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B4874003 : Blo 175800 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B12509623 : Blo 175800 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B681097 : Blo 175800 681097 := bstep (se 2 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 681097 = 510823) B510823
theorem B321167 : Blo 175800 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B5891869 : Blo 175800 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B1730807 : Blo 175800 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B1010303 : Blo 175800 1010303 := bstep (se 1 (by rfl) ⟨757727, by rfl⟩ : syracuseStep 1010303 = 1515455) B1515455
theorem B224795 : Blo 175800 224795 := bstep (se 1 (by rfl) ⟨168596, by rfl⟩ : syracuseStep 224795 = 337193) B337193
theorem B1338929 : Blo 175800 1338929 := bstep (se 2 (by rfl) ⟨502098, by rfl⟩ : syracuseStep 1338929 = 1004197) B1004197
theorem B552577 : Blo 175800 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B323819 : Blo 175800 323819 := bstep (se 1 (by rfl) ⟨242864, by rfl⟩ : syracuseStep 323819 = 485729) B485729
theorem B1700119 : Blo 175800 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B12449771 : Blo 175800 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B3045671 : Blo 175800 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B1243615 : Blo 175800 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B1342331 : Blo 175800 1342331 := bstep (se 1 (by rfl) ⟨1006748, by rfl⟩ : syracuseStep 1342331 = 2013497) B2013497
theorem B1278089 : Blo 175800 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B263849 : Blo 175800 263849 := bstep (se 2 (by rfl) ⟨98943, by rfl⟩ : syracuseStep 263849 = 197887) B197887
theorem B297067 : Blo 175800 297067 := bstep (se 1 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 297067 = 445601) B445601
theorem B198823 : Blo 175800 198823 := bstep (se 1 (by rfl) ⟨149117, by rfl⟩ : syracuseStep 198823 = 298235) B298235
theorem B66717989 : Blo 175800 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B396359 : Blo 175800 396359 := bstep (se 1 (by rfl) ⟨297269, by rfl⟩ : syracuseStep 396359 = 594539) B594539
theorem B757097 : Blo 175800 757097 := bstep (se 2 (by rfl) ⟨283911, by rfl⟩ : syracuseStep 757097 = 567823) B567823
theorem B265679 : Blo 175800 265679 := bstep (se 1 (by rfl) ⟨199259, by rfl⟩ : syracuseStep 265679 = 398519) B398519
theorem B265895 : Blo 175800 265895 := bstep (se 1 (by rfl) ⟨199421, by rfl⟩ : syracuseStep 265895 = 398843) B398843
theorem B1511081 : Blo 175800 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B265919 : Blo 175800 265919 := bstep (se 1 (by rfl) ⟨199439, by rfl⟩ : syracuseStep 265919 = 398879) B398879
theorem B1707965 : Blo 175800 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B299335 : Blo 175800 299335 := bstep (se 1 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 299335 = 449003) B449003
theorem B201199 : Blo 175800 201199 := bstep (se 1 (by rfl) ⟨150899, by rfl⟩ : syracuseStep 201199 = 301799) B301799
theorem B1446491 : Blo 175800 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B1086367 : Blo 175800 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B398249 : Blo 175800 398249 := bstep (se 2 (by rfl) ⟨149343, by rfl⟩ : syracuseStep 398249 = 298687) B298687
theorem B4527089 : Blo 175800 4527089 := bstep (se 2 (by rfl) ⟨1697658, by rfl⟩ : syracuseStep 4527089 = 3395317) B3395317
theorem B3249335 : Blo 175800 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B2266825 : Blo 175800 2266825 := bstep (se 2 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 2266825 = 1700119) B1700119
theorem B268379 : Blo 175800 268379 := bstep (se 1 (by rfl) ⟨201284, by rfl⟩ : syracuseStep 268379 = 402569) B402569
theorem B727229 : Blo 175800 727229 := bstep (se 3 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 727229 = 272711) B272711
theorem B2234567 : Blo 175800 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B334543 : Blo 175800 334543 := bstep (se 1 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 334543 = 501815) B501815
theorem B269033 : Blo 175800 269033 := bstep (se 2 (by rfl) ⟨100887, by rfl⟩ : syracuseStep 269033 = 201775) B201775
theorem B1153871 : Blo 175800 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B269375 : Blo 175800 269375 := bstep (se 1 (by rfl) ⟨202031, by rfl⟩ : syracuseStep 269375 = 404063) B404063
theorem B335431 : Blo 175800 335431 := bstep (se 1 (by rfl) ⟨251573, by rfl⟩ : syracuseStep 335431 = 503147) B503147
theorem B892619 : Blo 175800 892619 := bstep (se 1 (by rfl) ⟨669464, by rfl⟩ : syracuseStep 892619 = 1338929) B1338929
theorem B401363 : Blo 175800 401363 := bstep (se 1 (by rfl) ⟨301022, by rfl⟩ : syracuseStep 401363 = 602045) B602045
theorem B401705 : Blo 175800 401705 := bstep (se 2 (by rfl) ⟨150639, by rfl⟩ : syracuseStep 401705 = 301279) B301279
theorem B1515833 : Blo 175800 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B402515 : Blo 175800 402515 := bstep (se 1 (by rfl) ⟨301886, by rfl⟩ : syracuseStep 402515 = 603773) B603773
theorem B1713311 : Blo 175800 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B8299847 : Blo 175800 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B402767 : Blo 175800 402767 := bstep (se 1 (by rfl) ⟨302075, by rfl⟩ : syracuseStep 402767 = 604151) B604151
theorem B599399 : Blo 175800 599399 := bstep (se 1 (by rfl) ⟨449549, by rfl⟩ : syracuseStep 599399 = 899099) B899099
theorem B599453 : Blo 175800 599453 := bstep (se 3 (by rfl) ⟨112397, by rfl⟩ : syracuseStep 599453 = 224795) B224795
theorem B599507 : Blo 175800 599507 := bstep (se 1 (by rfl) ⟨449630, by rfl⟩ : syracuseStep 599507 = 899261) B899261
theorem B402911 : Blo 175800 402911 := bstep (se 1 (by rfl) ⟨302183, by rfl⟩ : syracuseStep 402911 = 604367) B604367
theorem B894887 : Blo 175800 894887 := bstep (se 1 (by rfl) ⟨671165, by rfl⟩ : syracuseStep 894887 = 1342331) B1342331
theorem B6432959 : Blo 175800 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B600263 : Blo 175800 600263 := bstep (se 1 (by rfl) ⟨450197, by rfl⟩ : syracuseStep 600263 = 900395) B900395
theorem B404135 : Blo 175800 404135 := bstep (se 1 (by rfl) ⟨303101, by rfl⟩ : syracuseStep 404135 = 606203) B606203
theorem B8137691 : Blo 175800 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B896507 : Blo 175800 896507 := bstep (se 1 (by rfl) ⟨672380, by rfl⟩ : syracuseStep 896507 = 1344761) B1344761
theorem B503455 : Blo 175800 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B1486673 : Blo 175800 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B176063 : Blo 175800 176063 := bstep (se 1 (by rfl) ⟨132047, by rfl⟩ : syracuseStep 176063 = 264095) B264095
theorem B602207 : Blo 175800 602207 := bstep (se 1 (by rfl) ⟨451655, by rfl⟩ : syracuseStep 602207 = 903311) B903311
theorem B5517467 : Blo 175800 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B176831 : Blo 175800 176831 := bstep (se 1 (by rfl) ⟨132623, by rfl⟩ : syracuseStep 176831 = 265247) B265247
theorem B177151 : Blo 175800 177151 := bstep (se 1 (by rfl) ⟨132863, by rfl⟩ : syracuseStep 177151 = 265727) B265727
theorem B1324127 : Blo 175800 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B177375 : Blo 175800 177375 := bstep (se 1 (by rfl) ⟨133031, by rfl⟩ : syracuseStep 177375 = 266063) B266063
theorem B177511 : Blo 175800 177511 := bstep (se 1 (by rfl) ⟨133133, by rfl⟩ : syracuseStep 177511 = 266267) B266267
theorem B177695 : Blo 175800 177695 := bstep (se 1 (by rfl) ⟨133271, by rfl⟩ : syracuseStep 177695 = 266543) B266543
theorem B177767 : Blo 175800 177767 := bstep (se 1 (by rfl) ⟨133325, by rfl⟩ : syracuseStep 177767 = 266651) B266651
theorem B8795765 : Blo 175800 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B178023 : Blo 175800 178023 := bstep (se 1 (by rfl) ⟨133517, by rfl⟩ : syracuseStep 178023 = 267035) B267035
theorem B178287 : Blo 175800 178287 := bstep (se 1 (by rfl) ⟨133715, by rfl⟩ : syracuseStep 178287 = 267431) B267431
theorem B16366211 : Blo 175800 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B1456793 : Blo 175800 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B178855 : Blo 175800 178855 := bstep (se 1 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 178855 = 268283) B268283
theorem B178939 : Blo 175800 178939 := bstep (se 1 (by rfl) ⟨134204, by rfl⟩ : syracuseStep 178939 = 268409) B268409
theorem B178975 : Blo 175800 178975 := bstep (se 1 (by rfl) ⟨134231, by rfl⟩ : syracuseStep 178975 = 268463) B268463
theorem B605231 : Blo 175800 605231 := bstep (se 1 (by rfl) ⟨453923, by rfl⟩ : syracuseStep 605231 = 907847) B907847
theorem B900233 : Blo 175800 900233 := bstep (se 2 (by rfl) ⟨337587, by rfl⟩ : syracuseStep 900233 = 675175) B675175
theorem B802223 : Blo 175800 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B605663 : Blo 175800 605663 := bstep (se 1 (by rfl) ⟨454247, by rfl⟩ : syracuseStep 605663 = 908495) B908495
theorem B736769 : Blo 175800 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B179743 : Blo 175800 179743 := bstep (se 1 (by rfl) ⟨134807, by rfl⟩ : syracuseStep 179743 = 269615) B269615
theorem B900719 : Blo 175800 900719 := bstep (se 1 (by rfl) ⟨675539, by rfl⟩ : syracuseStep 900719 = 1351079) B1351079
theorem B5422879 : Blo 175800 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B1523519 : Blo 175800 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B214111 : Blo 175800 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B673535 : Blo 175800 673535 := bstep (se 1 (by rfl) ⟨505151, by rfl⟩ : syracuseStep 673535 = 1010303) B1010303
theorem B378761 : Blo 175800 378761 := bstep (se 2 (by rfl) ⟨142035, by rfl⟩ : syracuseStep 378761 = 284071) B284071
theorem B969337 : Blo 175800 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B215879 : Blo 175800 215879 := bstep (se 1 (by rfl) ⟨161909, by rfl⟩ : syracuseStep 215879 = 323819) B323819
theorem B52317413 : Blo 175800 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B1658153 : Blo 175800 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B1429159 : Blo 175800 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B1822409 : Blo 175800 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B381419 : Blo 175800 381419 := bstep (se 1 (by rfl) ⟨286064, by rfl⟩ : syracuseStep 381419 = 572129) B572129
theorem B905903 : Blo 175800 905903 := bstep (se 1 (by rfl) ⟨679427, by rfl⟩ : syracuseStep 905903 = 1358855) B1358855
theorem B6510617 : Blo 175800 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B448679 : Blo 175800 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B252667 : Blo 175800 252667 := bstep (se 1 (by rfl) ⟨189500, by rfl⟩ : syracuseStep 252667 = 379001) B379001
theorem B908129 : Blo 175800 908129 := bstep (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) B681097
theorem B679535 : Blo 175800 679535 := bstep (se 1 (by rfl) ⟨509651, by rfl⟩ : syracuseStep 679535 = 1019303) B1019303
theorem B7855825 : Blo 175800 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B450299 : Blo 175800 450299 := bstep (se 1 (by rfl) ⟨337724, by rfl⟩ : syracuseStep 450299 = 675449) B675449
theorem B647003 : Blo 175800 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B450431 : Blo 175800 450431 := bstep (se 1 (by rfl) ⟨337823, by rfl⟩ : syracuseStep 450431 = 675647) B675647
theorem B7364519 : Blo 175800 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1695815 : Blo 175800 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B450643 : Blo 175800 450643 := bstep (se 1 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 450643 = 675965) B675965
theorem B1401001 : Blo 175800 1401001 := bstep (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) B1050751
theorem B3434683 : Blo 175800 3434683 := bstep (se 1 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 3434683 = 5152025) B5152025
theorem B225919 : Blo 175800 225919 := bstep (se 1 (by rfl) ⟨169439, by rfl⟩ : syracuseStep 225919 = 338879) B338879
theorem B3044303 : Blo 175800 3044303 := bstep (se 1 (by rfl) ⟨2283227, by rfl⟩ : syracuseStep 3044303 = 4566455) B4566455
theorem B816713 : Blo 175800 816713 := bstep (se 2 (by rfl) ⟨306267, by rfl⟩ : syracuseStep 816713 = 612535) B612535
theorem B1276013 : Blo 175800 1276013 := bstep (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) B478505
theorem B2030447 : Blo 175800 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B1014929 : Blo 175800 1014929 := bstep (se 2 (by rfl) ⟨380598, by rfl⟩ : syracuseStep 1014929 = 761197) B761197
theorem B852059 : Blo 175800 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B264239 : Blo 175800 264239 := bstep (se 1 (by rfl) ⟨198179, by rfl⟩ : syracuseStep 264239 = 396359) B396359
theorem B1214939 : Blo 175800 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B396089 : Blo 175800 396089 := bstep (se 2 (by rfl) ⟨148533, by rfl⟩ : syracuseStep 396089 = 297067) B297067
theorem B265097 : Blo 175800 265097 := bstep (se 2 (by rfl) ⟨99411, by rfl⟩ : syracuseStep 265097 = 198823) B198823
theorem B265499 : Blo 175800 265499 := bstep (se 1 (by rfl) ⟨199124, by rfl⟩ : syracuseStep 265499 = 398249) B398249
theorem B3018059 : Blo 175800 3018059 := bstep (se 1 (by rfl) ⟨2263544, by rfl⟩ : syracuseStep 3018059 = 4527089) B4527089
theorem B2166223 : Blo 175800 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B29888021 : Blo 175800 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B299119 : Blo 175800 299119 := bstep (se 1 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 299119 = 448679) B448679
theorem B1905545 : Blo 175800 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B595079 : Blo 175800 595079 := bstep (se 1 (by rfl) ⟨446309, by rfl⟩ : syracuseStep 595079 = 892619) B892619
theorem B300199 : Blo 175800 300199 := bstep (se 1 (by rfl) ⟨225149, by rfl⟩ : syracuseStep 300199 = 450299) B450299
theorem B431335 : Blo 175800 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B300287 : Blo 175800 300287 := bstep (se 1 (by rfl) ⟨225215, by rfl⟩ : syracuseStep 300287 = 450431) B450431
theorem B267575 : Blo 175800 267575 := bstep (se 1 (by rfl) ⟨200681, by rfl⟩ : syracuseStep 267575 = 401363) B401363
theorem B267803 : Blo 175800 267803 := bstep (se 1 (by rfl) ⟨200852, by rfl⟩ : syracuseStep 267803 = 401705) B401705
theorem B399113 : Blo 175800 399113 := bstep (se 2 (by rfl) ⟨149667, by rfl⟩ : syracuseStep 399113 = 299335) B299335
theorem B1939277 : Blo 175800 1939277 := bstep (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) B727229
theorem B268265 : Blo 175800 268265 := bstep (se 2 (by rfl) ⟨100599, by rfl⟩ : syracuseStep 268265 = 201199) B201199
theorem B268343 : Blo 175800 268343 := bstep (se 1 (by rfl) ⟨201257, by rfl⟩ : syracuseStep 268343 = 402515) B402515
theorem B301225 : Blo 175800 301225 := bstep (se 2 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 301225 = 225919) B225919
theorem B268511 : Blo 175800 268511 := bstep (se 1 (by rfl) ⟨201383, by rfl⟩ : syracuseStep 268511 = 402767) B402767
theorem B399599 : Blo 175800 399599 := bstep (se 1 (by rfl) ⟨299699, by rfl⟩ : syracuseStep 399599 = 599399) B599399
theorem B399635 : Blo 175800 399635 := bstep (se 1 (by rfl) ⟨299726, by rfl⟩ : syracuseStep 399635 = 599453) B599453
theorem B399671 : Blo 175800 399671 := bstep (se 1 (by rfl) ⟨299753, by rfl⟩ : syracuseStep 399671 = 599507) B599507
theorem B268607 : Blo 175800 268607 := bstep (se 1 (by rfl) ⟨201455, by rfl⟩ : syracuseStep 268607 = 402911) B402911
theorem B1448489 : Blo 175800 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B596591 : Blo 175800 596591 := bstep (se 1 (by rfl) ⟨447443, by rfl⟩ : syracuseStep 596591 = 894887) B894887
theorem B400175 : Blo 175800 400175 := bstep (se 1 (by rfl) ⟨300131, by rfl⟩ : syracuseStep 400175 = 600263) B600263
theorem B269423 : Blo 175800 269423 := bstep (se 1 (by rfl) ⟨202067, by rfl⟩ : syracuseStep 269423 = 404135) B404135
theorem B3022433 : Blo 175800 3022433 := bstep (se 2 (by rfl) ⟨1133412, by rfl⟩ : syracuseStep 3022433 = 2266825) B2266825
theorem B597671 : Blo 175800 597671 := bstep (se 1 (by rfl) ⟨448253, by rfl⟩ : syracuseStep 597671 = 896507) B896507
theorem B991115 : Blo 175800 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B401471 : Blo 175800 401471 := bstep (se 1 (by rfl) ⟨301103, by rfl⟩ : syracuseStep 401471 = 602207) B602207
theorem B3678311 : Blo 175800 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B336889 : Blo 175800 336889 := bstep (se 2 (by rfl) ⟨126333, by rfl⟩ : syracuseStep 336889 = 252667) B252667
theorem B1353631 : Blo 175800 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B403487 : Blo 175800 403487 := bstep (se 1 (by rfl) ⟨302615, by rfl⟩ : syracuseStep 403487 = 605231) B605231
theorem B600155 : Blo 175800 600155 := bstep (se 1 (by rfl) ⟨450116, by rfl⟩ : syracuseStep 600155 = 900233) B900233
theorem B534815 : Blo 175800 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B403775 : Blo 175800 403775 := bstep (se 1 (by rfl) ⟨302831, by rfl⟩ : syracuseStep 403775 = 605663) B605663
theorem B600479 : Blo 175800 600479 := bstep (se 1 (by rfl) ⟨450359, by rfl⟩ : syracuseStep 600479 = 900719) B900719
theorem B600857 : Blo 175800 600857 := bstep (se 2 (by rfl) ⟨225321, by rfl⟩ : syracuseStep 600857 = 450643) B450643
theorem B175899 : Blo 175800 175899 := bstep (se 1 (by rfl) ⟨131924, by rfl⟩ : syracuseStep 175899 = 263849) B263849
theorem B44478659 : Blo 175800 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B34878275 : Blo 175800 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B504731 : Blo 175800 504731 := bstep (se 1 (by rfl) ⟨378548, by rfl⟩ : syracuseStep 504731 = 757097) B757097
theorem B177119 : Blo 175800 177119 := bstep (se 1 (by rfl) ⟨132839, by rfl⟩ : syracuseStep 177119 = 265679) B265679
theorem B177263 : Blo 175800 177263 := bstep (se 1 (by rfl) ⟨132947, by rfl⟩ : syracuseStep 177263 = 265895) B265895
theorem B177279 : Blo 175800 177279 := bstep (se 1 (by rfl) ⟨132959, by rfl⟩ : syracuseStep 177279 = 265919) B265919
theorem B964327 : Blo 175800 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B603935 : Blo 175800 603935 := bstep (se 1 (by rfl) ⟨452951, by rfl⟩ : syracuseStep 603935 = 905903) B905903
theorem B1292449 : Blo 175800 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B4340411 : Blo 175800 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B178919 : Blo 175800 178919 := bstep (se 1 (by rfl) ⟨134189, by rfl⟩ : syracuseStep 178919 = 268379) B268379
theorem B179355 : Blo 175800 179355 := bstep (se 1 (by rfl) ⟨134516, by rfl⟩ : syracuseStep 179355 = 269033) B269033
theorem B769247 : Blo 175800 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B179583 : Blo 175800 179583 := bstep (se 1 (by rfl) ⟨134687, by rfl⟩ : syracuseStep 179583 = 269375) B269375
theorem B671273 : Blo 175800 671273 := bstep (se 2 (by rfl) ⟨251727, by rfl⟩ : syracuseStep 671273 = 503455) B503455
theorem B1130543 : Blo 175800 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B5425127 : Blo 175800 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B575677 : Blo 175800 575677 := bstep (se 3 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 575677 = 215879) B215879
theorem B446057 : Blo 175800 446057 := bstep (se 2 (by rfl) ⟨167271, by rfl⟩ : syracuseStep 446057 = 334543) B334543
theorem B544475 : Blo 175800 544475 := bstep (se 1 (by rfl) ⟨408356, by rfl⟩ : syracuseStep 544475 = 816713) B816713
theorem B971195 : Blo 175800 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B447241 : Blo 175800 447241 := bstep (se 2 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 447241 = 335431) B335431
theorem B676619 : Blo 175800 676619 := bstep (se 1 (by rfl) ⟨507464, by rfl⟩ : syracuseStep 676619 = 1014929) B1014929
theorem B10474433 : Blo 175800 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B7230505 : Blo 175800 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B449023 : Blo 175800 449023 := bstep (se 1 (by rfl) ⟨336767, by rfl⟩ : syracuseStep 449023 = 673535) B673535
theorem B285481 : Blo 175800 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B1105435 : Blo 175800 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B1007387 : Blo 175800 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B1138643 : Blo 175800 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B4579577 : Blo 175800 4579577 := bstep (se 2 (by rfl) ⟨1717341, by rfl⟩ : syracuseStep 4579577 = 3434683) B3434683
theorem B3531005 : Blo 175800 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B254279 : Blo 175800 254279 := bstep (se 1 (by rfl) ⟨190709, by rfl⟩ : syracuseStep 254279 = 381419) B381419
theorem B1010029 : Blo 175800 1010029 := bstep (se 3 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 1010029 = 378761) B378761
theorem B453023 : Blo 175800 453023 := bstep (se 1 (by rfl) ⟨339767, by rfl⟩ : syracuseStep 453023 = 679535) B679535
theorem B4909679 : Blo 175800 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B1010555 : Blo 175800 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B5958845 : Blo 175800 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B1142207 : Blo 175800 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B5533231 : Blo 175800 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B4288639 : Blo 175800 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B2421677 : Blo 175800 2421677 := bstep (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) B908129
theorem B2029535 : Blo 175800 2029535 := bstep (se 1 (by rfl) ⟨1522151, by rfl⟩ : syracuseStep 2029535 = 3044303) B3044303
theorem B5863843 : Blo 175800 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B850675 : Blo 175800 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B10910807 : Blo 175800 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B491179 : Blo 175800 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B1015679 : Blo 175800 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B753695 : Blo 175800 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B2589853 : Blo 175800 2589853 := bstep (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) B971195
theorem B264059 : Blo 175800 264059 := bstep (se 1 (by rfl) ⟨198044, by rfl⟩ : syracuseStep 264059 = 396089) B396089
theorem B19925347 : Blo 175800 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B297371 : Blo 175800 297371 := bstep (se 1 (by rfl) ⟨223028, by rfl⟩ : syracuseStep 297371 = 446057) B446057
theorem B362983 : Blo 175800 362983 := bstep (se 1 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 362983 = 544475) B544475
theorem B1804841 : Blo 175800 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B1346705 : Blo 175800 1346705 := bstep (se 2 (by rfl) ⟨505014, by rfl⟩ : syracuseStep 1346705 = 1010029) B1010029
theorem B6982955 : Blo 175800 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B396719 : Blo 175800 396719 := bstep (se 1 (by rfl) ⟨297539, by rfl⟩ : syracuseStep 396719 = 595079) B595079
theorem B200191 : Blo 175800 200191 := bstep (se 1 (by rfl) ⟨150143, by rfl⟩ : syracuseStep 200191 = 300287) B300287
theorem B266075 : Blo 175800 266075 := bstep (se 1 (by rfl) ⟨199556, by rfl⟩ : syracuseStep 266075 = 399113) B399113
theorem B266399 : Blo 175800 266399 := bstep (se 1 (by rfl) ⟨199799, by rfl⟩ : syracuseStep 266399 = 399599) B399599
theorem B266423 : Blo 175800 266423 := bstep (se 1 (by rfl) ⟨199817, by rfl⟩ : syracuseStep 266423 = 399635) B399635
theorem B266447 : Blo 175800 266447 := bstep (se 1 (by rfl) ⟨199835, by rfl⟩ : syracuseStep 266447 = 399671) B399671
theorem B397727 : Blo 175800 397727 := bstep (se 1 (by rfl) ⟨298295, by rfl⟩ : syracuseStep 397727 = 596591) B596591
theorem B266783 : Blo 175800 266783 := bstep (se 1 (by rfl) ⟨200087, by rfl⟩ : syracuseStep 266783 = 400175) B400175
theorem B2888297 : Blo 175800 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B7377641 : Blo 175800 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B398447 : Blo 175800 398447 := bstep (se 1 (by rfl) ⟨298835, by rfl⟩ : syracuseStep 398447 = 597671) B597671
theorem B660743 : Blo 175800 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B759095 : Blo 175800 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B267647 : Blo 175800 267647 := bstep (se 1 (by rfl) ⟨200735, by rfl⟩ : syracuseStep 267647 = 401471) B401471
theorem B398825 : Blo 175800 398825 := bstep (se 2 (by rfl) ⟨149559, by rfl⟩ : syracuseStep 398825 = 299119) B299119
theorem B3053051 : Blo 175800 3053051 := bstep (se 1 (by rfl) ⟨2289788, by rfl⟩ : syracuseStep 3053051 = 4579577) B4579577
theorem B596321 : Blo 175800 596321 := bstep (se 2 (by rfl) ⟨223620, by rfl⟩ : syracuseStep 596321 = 447241) B447241
theorem B268991 : Blo 175800 268991 := bstep (se 1 (by rfl) ⟨201743, by rfl⟩ : syracuseStep 268991 = 403487) B403487
theorem B9640673 : Blo 175800 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B400103 : Blo 175800 400103 := bstep (se 1 (by rfl) ⟨300077, by rfl⟩ : syracuseStep 400103 = 600155) B600155
theorem B269183 : Blo 175800 269183 := bstep (se 1 (by rfl) ⟨201887, by rfl⟩ : syracuseStep 269183 = 403775) B403775
theorem B400265 : Blo 175800 400265 := bstep (se 2 (by rfl) ⟨150099, by rfl⟩ : syracuseStep 400265 = 300199) B300199
theorem B400319 : Blo 175800 400319 := bstep (se 1 (by rfl) ⟨300239, by rfl⟩ : syracuseStep 400319 = 600479) B600479
theorem B302015 : Blo 175800 302015 := bstep (se 1 (by rfl) ⟨226511, by rfl⟩ : syracuseStep 302015 = 453023) B453023
theorem B400571 : Blo 175800 400571 := bstep (se 1 (by rfl) ⟨300428, by rfl⟩ : syracuseStep 400571 = 600857) B600857
theorem B3972563 : Blo 175800 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B761471 : Blo 175800 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B1285769 : Blo 175800 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B401633 : Blo 175800 401633 := bstep (se 2 (by rfl) ⟨150612, by rfl⟩ : syracuseStep 401633 = 301225) B301225
theorem B336487 : Blo 175800 336487 := bstep (se 1 (by rfl) ⟨252365, by rfl⟩ : syracuseStep 336487 = 504731) B504731
theorem B1614451 : Blo 175800 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B598697 : Blo 175800 598697 := bstep (se 2 (by rfl) ⟨224511, by rfl⟩ : syracuseStep 598697 = 449023) B449023
theorem B402623 : Blo 175800 402623 := bstep (se 1 (by rfl) ⟨301967, by rfl⟩ : syracuseStep 402623 = 603935) B603935
theorem B1353023 : Blo 175800 1353023 := bstep (se 1 (by rfl) ⟨1014767, by rfl⟩ : syracuseStep 1353023 = 2029535) B2029535
theorem B2893607 : Blo 175800 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B2272157 : Blo 175800 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B3616751 : Blo 175800 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B176159 : Blo 175800 176159 := bstep (se 1 (by rfl) ⟨132119, by rfl⟩ : syracuseStep 176159 = 264239) B264239
theorem B176731 : Blo 175800 176731 := bstep (se 1 (by rfl) ⟨132548, by rfl⟩ : syracuseStep 176731 = 265097) B265097
theorem B176999 : Blo 175800 176999 := bstep (se 1 (by rfl) ⟨132749, by rfl⟩ : syracuseStep 176999 = 265499) B265499
theorem B2012039 : Blo 175800 2012039 := bstep (se 1 (by rfl) ⟨1509029, by rfl⟩ : syracuseStep 2012039 = 3018059) B3018059
theorem B767569 : Blo 175800 767569 := bstep (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) B575677
theorem B178383 : Blo 175800 178383 := bstep (se 1 (by rfl) ⟨133787, by rfl⟩ : syracuseStep 178383 = 267575) B267575
theorem B178535 : Blo 175800 178535 := bstep (se 1 (by rfl) ⟨133901, by rfl⟩ : syracuseStep 178535 = 267803) B267803
theorem B1292851 : Blo 175800 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B178843 : Blo 175800 178843 := bstep (se 1 (by rfl) ⟨134132, by rfl⟩ : syracuseStep 178843 = 268265) B268265
theorem B178895 : Blo 175800 178895 := bstep (se 1 (by rfl) ⟨134171, by rfl⟩ : syracuseStep 178895 = 268343) B268343
theorem B179007 : Blo 175800 179007 := bstep (se 1 (by rfl) ⟨134255, by rfl⟩ : syracuseStep 179007 = 268511) B268511
theorem B179071 : Blo 175800 179071 := bstep (se 1 (by rfl) ⟨134303, by rfl⟩ : syracuseStep 179071 = 268607) B268607
theorem B179615 : Blo 175800 179615 := bstep (se 1 (by rfl) ⟨134711, by rfl⟩ : syracuseStep 179615 = 269423) B269423
theorem B2014955 : Blo 175800 2014955 := bstep (se 1 (by rfl) ⟨1511216, by rfl⟩ : syracuseStep 2014955 = 3022433) B3022433
theorem B671591 : Blo 175800 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B5718185 : Blo 175800 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B575113 : Blo 175800 575113 := bstep (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) B431335
theorem B673703 : Blo 175800 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B1723265 : Blo 175800 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B23252183 : Blo 175800 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B7818457 : Blo 175800 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B1134233 : Blo 175800 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B380641 : Blo 175800 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B512831 : Blo 175800 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B447515 : Blo 175800 447515 := bstep (se 1 (by rfl) ⟨335636, by rfl⟩ : syracuseStep 447515 = 671273) B671273
theorem B677119 : Blo 175800 677119 := bstep (se 1 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 677119 = 1015679) B1015679
theorem B678077 : Blo 175800 678077 := bstep (se 3 (by rfl) ⟨127139, by rfl⟩ : syracuseStep 678077 = 254279) B254279
theorem B449185 : Blo 175800 449185 := bstep (se 2 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 449185 = 336889) B336889
theorem B451079 : Blo 175800 451079 := bstep (se 1 (by rfl) ⟨338309, by rfl⟩ : syracuseStep 451079 = 676619) B676619
theorem B1270363 : Blo 175800 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B2452207 : Blo 175800 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B2354003 : Blo 175800 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B3239837 : Blo 175800 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B3862637 : Blo 175800 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B356543 : Blo 175800 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B3273119 : Blo 175800 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B29652439 : Blo 175800 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B1473913 : Blo 175800 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B7273871 : Blo 175800 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B654905 : Blo 175800 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B198247 : Blo 175800 198247 := bstep (se 1 (by rfl) ⟨148685, by rfl⟩ : syracuseStep 198247 = 297371) B297371
theorem B1148843 : Blo 175800 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B3803125 : Blo 175800 3803125 := bstep (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) B356543
theorem B15501455 : Blo 175800 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B4655303 : Blo 175800 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B264479 : Blo 175800 264479 := bstep (se 1 (by rfl) ⟨198359, by rfl⟩ : syracuseStep 264479 = 396719) B396719
theorem B756155 : Blo 175800 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B265151 : Blo 175800 265151 := bstep (se 1 (by rfl) ⟨198863, by rfl⟩ : syracuseStep 265151 = 397727) B397727
theorem B4918427 : Blo 175800 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B298343 : Blo 175800 298343 := bstep (se 1 (by rfl) ⟨223757, by rfl⟩ : syracuseStep 298343 = 447515) B447515
theorem B265631 : Blo 175800 265631 := bstep (se 1 (by rfl) ⟨199223, by rfl⟩ : syracuseStep 265631 = 398447) B398447
theorem B265883 : Blo 175800 265883 := bstep (se 1 (by rfl) ⟨199412, by rfl⟩ : syracuseStep 265883 = 398825) B398825
theorem B2035367 : Blo 175800 2035367 := bstep (se 1 (by rfl) ⟨1526525, by rfl⟩ : syracuseStep 2035367 = 3053051) B3053051
theorem B397547 : Blo 175800 397547 := bstep (se 1 (by rfl) ⟨298160, by rfl⟩ : syracuseStep 397547 = 596321) B596321
theorem B10424609 : Blo 175800 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B6427115 : Blo 175800 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B266735 : Blo 175800 266735 := bstep (se 1 (by rfl) ⟨200051, by rfl⟩ : syracuseStep 266735 = 400103) B400103
theorem B266843 : Blo 175800 266843 := bstep (se 1 (by rfl) ⟨200132, by rfl⟩ : syracuseStep 266843 = 400265) B400265
theorem B266879 : Blo 175800 266879 := bstep (se 1 (by rfl) ⟨200159, by rfl⟩ : syracuseStep 266879 = 400319) B400319
theorem B201343 : Blo 175800 201343 := bstep (se 1 (by rfl) ⟨151007, by rfl⟩ : syracuseStep 201343 = 302015) B302015
theorem B266921 : Blo 175800 266921 := bstep (se 2 (by rfl) ⟨100095, by rfl⟩ : syracuseStep 266921 = 200191) B200191
theorem B267047 : Blo 175800 267047 := bstep (se 1 (by rfl) ⟨200285, by rfl⟩ : syracuseStep 267047 = 400571) B400571
theorem B857179 : Blo 175800 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B267755 : Blo 175800 267755 := bstep (se 1 (by rfl) ⟨200816, by rfl⟩ : syracuseStep 267755 = 401633) B401633
theorem B300719 : Blo 175800 300719 := bstep (se 1 (by rfl) ⟨225539, by rfl⟩ : syracuseStep 300719 = 451079) B451079
theorem B399131 : Blo 175800 399131 := bstep (se 1 (by rfl) ⟨299348, by rfl⟩ : syracuseStep 399131 = 598697) B598697
theorem B268415 : Blo 175800 268415 := bstep (se 1 (by rfl) ⟨201311, by rfl⟩ : syracuseStep 268415 = 402623) B402623
theorem B1514771 : Blo 175800 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B1023425 : Blo 175800 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B25109365 : Blo 175800 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B598913 : Blo 175800 598913 := bstep (se 2 (by rfl) ⟨224592, by rfl⟩ : syracuseStep 598913 = 449185) B449185
theorem B436603 : Blo 175800 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B9644669 : Blo 175800 9644669 := bstep (se 3 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 9644669 = 3616751) B3616751
theorem B502463 : Blo 175800 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B3812123 : Blo 175800 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B176039 : Blo 175800 176039 := bstep (se 1 (by rfl) ⟨132029, by rfl⟩ : syracuseStep 176039 = 264059) B264059
theorem B3453137 : Blo 175800 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B897803 : Blo 175800 897803 := bstep (se 1 (by rfl) ⟨673352, by rfl⟩ : syracuseStep 897803 = 1346705) B1346705
theorem B766817 : Blo 175800 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B177383 : Blo 175800 177383 := bstep (se 1 (by rfl) ⟨133037, by rfl⟩ : syracuseStep 177383 = 266075) B266075
theorem B177599 : Blo 175800 177599 := bstep (se 1 (by rfl) ⟨133199, by rfl⟩ : syracuseStep 177599 = 266399) B266399
theorem B177615 : Blo 175800 177615 := bstep (se 1 (by rfl) ⟨133211, by rfl⟩ : syracuseStep 177615 = 266423) B266423
theorem B177631 : Blo 175800 177631 := bstep (se 1 (by rfl) ⟨133223, by rfl⟩ : syracuseStep 177631 = 266447) B266447
theorem B177855 : Blo 175800 177855 := bstep (se 1 (by rfl) ⟨133391, by rfl⟩ : syracuseStep 177855 = 266783) B266783
theorem B440495 : Blo 175800 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B506063 : Blo 175800 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B178431 : Blo 175800 178431 := bstep (se 1 (by rfl) ⟨133823, by rfl⟩ : syracuseStep 178431 = 267647) B267647
theorem B179327 : Blo 175800 179327 := bstep (se 1 (by rfl) ⟨134495, by rfl⟩ : syracuseStep 179327 = 268991) B268991
theorem B179455 : Blo 175800 179455 := bstep (se 1 (by rfl) ⟨134591, by rfl⟩ : syracuseStep 179455 = 269183) B269183
theorem B507521 : Blo 175800 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B507647 : Blo 175800 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B902015 : Blo 175800 902015 := bstep (se 1 (by rfl) ⟨676511, by rfl⟩ : syracuseStep 902015 = 1353023) B1353023
theorem B902825 : Blo 175800 902825 := bstep (se 2 (by rfl) ⟨338559, by rfl⟩ : syracuseStep 902825 = 677119) B677119
theorem B39536585 : Blo 175800 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B2575091 : Blo 175800 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B2182079 : Blo 175800 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B1723801 : Blo 175800 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B447727 : Blo 175800 447727 := bstep (se 1 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 447727 = 671591) B671591
theorem B1693817 : Blo 175800 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B448649 : Blo 175800 448649 := bstep (se 2 (by rfl) ⟨168243, by rfl⟩ : syracuseStep 448649 = 336487) B336487
theorem B2152601 : Blo 175800 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B449135 : Blo 175800 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B1203227 : Blo 175800 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B1367549 : Blo 175800 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B1925531 : Blo 175800 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B26567129 : Blo 175800 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B483977 : Blo 175800 483977 := bstep (se 2 (by rfl) ⟨181491, by rfl⟩ : syracuseStep 483977 = 362983) B362983
theorem B3269609 : Blo 175800 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B452051 : Blo 175800 452051 := bstep (se 1 (by rfl) ⟨339038, by rfl⟩ : syracuseStep 452051 = 678077) B678077
theorem B2648375 : Blo 175800 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B1929071 : Blo 175800 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B2159891 : Blo 175800 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B1341359 : Blo 175800 1341359 := bstep (se 1 (by rfl) ⟨1006019, by rfl⟩ : syracuseStep 1341359 = 2012039) B2012039
theorem B1965217 : Blo 175800 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B4849247 : Blo 175800 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B1343303 : Blo 175800 1343303 := bstep (se 1 (by rfl) ⟨1007477, by rfl⟩ : syracuseStep 1343303 = 2014955) B2014955
theorem B3278951 : Blo 175800 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B264329 : Blo 175800 264329 := bstep (se 2 (by rfl) ⟨99123, by rfl⟩ : syracuseStep 264329 = 198247) B198247
theorem B198895 : Blo 175800 198895 := bstep (se 1 (by rfl) ⟨149171, by rfl⟩ : syracuseStep 198895 = 298343) B298343
theorem B265031 : Blo 175800 265031 := bstep (se 1 (by rfl) ⟨198773, by rfl⟩ : syracuseStep 265031 = 397547) B397547
theorem B6949739 : Blo 175800 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B200479 : Blo 175800 200479 := bstep (se 1 (by rfl) ⟨150359, by rfl⟩ : syracuseStep 200479 = 300719) B300719
theorem B266087 : Blo 175800 266087 := bstep (se 1 (by rfl) ⟨199565, by rfl⟩ : syracuseStep 266087 = 399131) B399131
theorem B299099 : Blo 175800 299099 := bstep (se 1 (by rfl) ⟨224324, by rfl⟩ : syracuseStep 299099 = 448649) B448649
theorem B299423 : Blo 175800 299423 := bstep (se 1 (by rfl) ⟨224567, by rfl⟩ : syracuseStep 299423 = 449135) B449135
theorem B2298401 : Blo 175800 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B1283687 : Blo 175800 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B399275 : Blo 175800 399275 := bstep (se 1 (by rfl) ⟨299456, by rfl⟩ : syracuseStep 399275 = 598913) B598913
theorem B268457 : Blo 175800 268457 := bstep (se 2 (by rfl) ⟨100671, by rfl⟩ : syracuseStep 268457 = 201343) B201343
theorem B301367 : Blo 175800 301367 := bstep (se 1 (by rfl) ⟨226025, by rfl⟩ : syracuseStep 301367 = 452051) B452051
theorem B596969 : Blo 175800 596969 := bstep (se 2 (by rfl) ⟨223863, by rfl⟩ : syracuseStep 596969 = 447727) B447727
theorem B6429779 : Blo 175800 6429779 := bstep (se 1 (by rfl) ⟨4822334, by rfl⟩ : syracuseStep 6429779 = 9644669) B9644669
theorem B1286047 : Blo 175800 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B2302091 : Blo 175800 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B598535 : Blo 175800 598535 := bstep (se 1 (by rfl) ⟨448901, by rfl⟩ : syracuseStep 598535 = 897803) B897803
theorem B894239 : Blo 175800 894239 := bstep (se 1 (by rfl) ⟨670679, by rfl⟩ : syracuseStep 894239 = 1341359) B1341359
theorem B337375 : Blo 175800 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B338347 : Blo 175800 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B338431 : Blo 175800 338431 := bstep (se 1 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 338431 = 507647) B507647
theorem B895535 : Blo 175800 895535 := bstep (se 1 (by rfl) ⟨671651, by rfl⟩ : syracuseStep 895535 = 1343303) B1343303
theorem B601343 : Blo 175800 601343 := bstep (se 1 (by rfl) ⟨451007, by rfl⟩ : syracuseStep 601343 = 902015) B902015
theorem B601883 : Blo 175800 601883 := bstep (se 1 (by rfl) ⟨451412, by rfl⟩ : syracuseStep 601883 = 902825) B902825
theorem B765895 : Blo 175800 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B26357723 : Blo 175800 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B10334303 : Blo 175800 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B176319 : Blo 175800 176319 := bstep (se 1 (by rfl) ⟨132239, by rfl⟩ : syracuseStep 176319 = 264479) B264479
theorem B1716727 : Blo 175800 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B176767 : Blo 175800 176767 := bstep (se 1 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 176767 = 265151) B265151
theorem B1454719 : Blo 175800 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B177087 : Blo 175800 177087 := bstep (se 1 (by rfl) ⟨132815, by rfl⟩ : syracuseStep 177087 = 265631) B265631
theorem B177255 : Blo 175800 177255 := bstep (se 1 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 177255 = 265883) B265883
theorem B1356911 : Blo 175800 1356911 := bstep (se 1 (by rfl) ⟨1017683, by rfl⟩ : syracuseStep 1356911 = 2035367) B2035367
theorem B177823 : Blo 175800 177823 := bstep (se 1 (by rfl) ⟨133367, by rfl⟩ : syracuseStep 177823 = 266735) B266735
theorem B177895 : Blo 175800 177895 := bstep (se 1 (by rfl) ⟨133421, by rfl⟩ : syracuseStep 177895 = 266843) B266843
theorem B177919 : Blo 175800 177919 := bstep (se 1 (by rfl) ⟨133439, by rfl⟩ : syracuseStep 177919 = 266879) B266879
theorem B177947 : Blo 175800 177947 := bstep (se 1 (by rfl) ⟨133460, by rfl⟩ : syracuseStep 177947 = 266921) B266921
theorem B178031 : Blo 175800 178031 := bstep (se 1 (by rfl) ⟨133523, by rfl⟩ : syracuseStep 178031 = 267047) B267047
theorem B178503 : Blo 175800 178503 := bstep (se 1 (by rfl) ⟨133877, by rfl⟩ : syracuseStep 178503 = 267755) B267755
theorem B1129211 : Blo 175800 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B178943 : Blo 175800 178943 := bstep (se 1 (by rfl) ⟨134207, by rfl⟩ : syracuseStep 178943 = 268415) B268415
theorem B802151 : Blo 175800 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B17711419 : Blo 175800 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B2179739 : Blo 175800 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B2016413 : Blo 175800 2016413 := bstep (se 3 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 2016413 = 756155) B756155
theorem B2541415 : Blo 175800 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B511211 : Blo 175800 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B3232831 : Blo 175800 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B33479153 : Blo 175800 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B3103535 : Blo 175800 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B5070833 : Blo 175800 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B4284743 : Blo 175800 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B582137 : Blo 175800 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B1435067 : Blo 175800 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B1009847 : Blo 175800 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B682283 : Blo 175800 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B911699 : Blo 175800 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B322651 : Blo 175800 322651 := bstep (se 1 (by rfl) ⟨241988, by rfl⟩ : syracuseStep 322651 = 483977) B483977
theorem B1142905 : Blo 175800 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B1765583 : Blo 175800 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B1339901 : Blo 175800 1339901 := bstep (se 3 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 1339901 = 502463) B502463
theorem B1439927 : Blo 175800 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B293663 : Blo 175800 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B2620289 : Blo 175800 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B1344275 : Blo 175800 1344275 := bstep (se 1 (by rfl) ⟨1008206, by rfl⟩ : syracuseStep 1344275 = 2016413) B2016413
theorem B1804517 : Blo 175800 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B199399 : Blo 175800 199399 := bstep (se 1 (by rfl) ⟨149549, by rfl⟩ : syracuseStep 199399 = 299099) B299099
theorem B199615 : Blo 175800 199615 := bstep (se 1 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 199615 = 299423) B299423
theorem B265193 : Blo 175800 265193 := bstep (se 2 (by rfl) ⟨99447, by rfl⟩ : syracuseStep 265193 = 198895) B198895
theorem B855791 : Blo 175800 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B266183 : Blo 175800 266183 := bstep (se 1 (by rfl) ⟨199637, by rfl⟩ : syracuseStep 266183 = 399275) B399275
theorem B430201 : Blo 175800 430201 := bstep (se 2 (by rfl) ⟨161325, by rfl⟩ : syracuseStep 430201 = 322651) B322651
theorem B200911 : Blo 175800 200911 := bstep (se 1 (by rfl) ⟨150683, by rfl⟩ : syracuseStep 200911 = 301367) B301367
theorem B22319435 : Blo 175800 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B2069023 : Blo 175800 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B397979 : Blo 175800 397979 := bstep (se 1 (by rfl) ⟨298484, by rfl⟩ : syracuseStep 397979 = 596969) B596969
theorem B267305 : Blo 175800 267305 := bstep (se 2 (by rfl) ⟨100239, by rfl⟩ : syracuseStep 267305 = 200479) B200479
theorem B1021193 : Blo 175800 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B3380555 : Blo 175800 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B399023 : Blo 175800 399023 := bstep (se 1 (by rfl) ⟨299267, by rfl⟩ : syracuseStep 399023 = 598535) B598535
theorem B1939625 : Blo 175800 1939625 := bstep (se 2 (by rfl) ⟨727359, by rfl⟩ : syracuseStep 1939625 = 1454719) B1454719
theorem B596159 : Blo 175800 596159 := bstep (se 1 (by rfl) ⟨447119, by rfl⟩ : syracuseStep 596159 = 894239) B894239
theorem B956711 : Blo 175800 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B597023 : Blo 175800 597023 := bstep (se 1 (by rfl) ⟨447767, by rfl⟩ : syracuseStep 597023 = 895535) B895535
theorem B400895 : Blo 175800 400895 := bstep (se 1 (by rfl) ⟨300671, by rfl⟩ : syracuseStep 400895 = 601343) B601343
theorem B401255 : Blo 175800 401255 := bstep (se 1 (by rfl) ⟨300941, by rfl⟩ : syracuseStep 401255 = 601883) B601883
theorem B17571815 : Blo 175800 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B6889535 : Blo 175800 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B893267 : Blo 175800 893267 := bstep (se 1 (by rfl) ⟨669950, by rfl⟩ : syracuseStep 893267 = 1339901) B1339901
theorem B959951 : Blo 175800 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B1746859 : Blo 175800 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B534767 : Blo 175800 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B1714729 : Blo 175800 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B1453159 : Blo 175800 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B176219 : Blo 175800 176219 := bstep (se 1 (by rfl) ⟨132164, by rfl⟩ : syracuseStep 176219 = 264329) B264329
theorem B176687 : Blo 175800 176687 := bstep (se 1 (by rfl) ⟨132515, by rfl⟩ : syracuseStep 176687 = 265031) B265031
theorem B4633159 : Blo 175800 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B3388553 : Blo 175800 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B177391 : Blo 175800 177391 := bstep (se 1 (by rfl) ⟨133043, by rfl⟩ : syracuseStep 177391 = 266087) B266087
theorem B178971 : Blo 175800 178971 := bstep (se 1 (by rfl) ⟨134228, by rfl⟩ : syracuseStep 178971 = 268457) B268457
theorem B1523873 : Blo 175800 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B4310441 : Blo 175800 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B673231 : Blo 175800 673231 := bstep (se 1 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 673231 = 1009847) B1009847
theorem B607799 : Blo 175800 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B1363229 : Blo 175800 1363229 := bstep (se 3 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 1363229 = 511211) B511211
theorem B904607 : Blo 175800 904607 := bstep (se 1 (by rfl) ⟨678455, by rfl⟩ : syracuseStep 904607 = 1356911) B1356911
theorem B23615225 : Blo 175800 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B11425981 : Blo 175800 11425981 := bstep (se 3 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 11425981 = 4284743) B4284743
theorem B2185967 : Blo 175800 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B449833 : Blo 175800 449833 := bstep (se 2 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 449833 = 337375) B337375
theorem B1532267 : Blo 175800 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B451129 : Blo 175800 451129 := bstep (se 2 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 451129 = 338347) B338347
theorem B451241 : Blo 175800 451241 := bstep (se 2 (by rfl) ⟨169215, by rfl⟩ : syracuseStep 451241 = 338431) B338431
theorem B4286519 : Blo 175800 4286519 := bstep (se 1 (by rfl) ⟨3214889, by rfl⟩ : syracuseStep 4286519 = 6429779) B6429779
theorem B1534727 : Blo 175800 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B388091 : Blo 175800 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B2288969 : Blo 175800 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B454855 : Blo 175800 454855 := bstep (se 1 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 454855 = 682283) B682283
theorem B783101 : Blo 175800 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B1177055 : Blo 175800 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B752807 : Blo 175800 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B1015915 : Blo 175800 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B2294405 : Blo 175800 2294405 := bstep (se 4 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 2294405 = 430201) B430201
theorem B2329145 : Blo 175800 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B14879623 : Blo 175800 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B265319 : Blo 175800 265319 := bstep (se 1 (by rfl) ⟨198989, by rfl⟩ : syracuseStep 265319 = 397979) B397979
theorem B265865 : Blo 175800 265865 := bstep (se 2 (by rfl) ⟨99699, by rfl⟩ : syracuseStep 265865 = 199399) B199399
theorem B266015 : Blo 175800 266015 := bstep (se 1 (by rfl) ⟨199511, by rfl⟩ : syracuseStep 266015 = 399023) B399023
theorem B2559869 : Blo 175800 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B266153 : Blo 175800 266153 := bstep (se 2 (by rfl) ⟨99807, by rfl⟩ : syracuseStep 266153 = 199615) B199615
theorem B397439 : Blo 175800 397439 := bstep (se 1 (by rfl) ⟨298079, by rfl⟩ : syracuseStep 397439 = 596159) B596159
theorem B398015 : Blo 175800 398015 := bstep (se 1 (by rfl) ⟨298511, by rfl⟩ : syracuseStep 398015 = 597023) B597023
theorem B267263 : Blo 175800 267263 := bstep (se 1 (by rfl) ⟨200447, by rfl⟩ : syracuseStep 267263 = 400895) B400895
theorem B267503 : Blo 175800 267503 := bstep (se 1 (by rfl) ⟨200627, by rfl⟩ : syracuseStep 267503 = 401255) B401255
theorem B4593023 : Blo 175800 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B595511 : Blo 175800 595511 := bstep (se 1 (by rfl) ⟨446633, by rfl⟩ : syracuseStep 595511 = 893267) B893267
theorem B1021511 : Blo 175800 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B267881 : Blo 175800 267881 := bstep (se 2 (by rfl) ⟨100455, by rfl⟩ : syracuseStep 267881 = 200911) B200911
theorem B300827 : Blo 175800 300827 := bstep (se 1 (by rfl) ⟨225620, by rfl⟩ : syracuseStep 300827 = 451241) B451241
theorem B2758697 : Blo 175800 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B2857679 : Blo 175800 2857679 := bstep (se 1 (by rfl) ⟨2143259, by rfl⟩ : syracuseStep 2857679 = 4286519) B4286519
theorem B1023151 : Blo 175800 1023151 := bstep (se 1 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 1023151 = 1534727) B1534727
theorem B599777 : Blo 175800 599777 := bstep (se 2 (by rfl) ⟨224916, by rfl⟩ : syracuseStep 599777 = 449833) B449833
theorem B501871 : Blo 175800 501871 := bstep (se 1 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 501871 = 752807) B752807
theorem B896183 : Blo 175800 896183 := bstep (se 1 (by rfl) ⟨672137, by rfl⟩ : syracuseStep 896183 = 1344275) B1344275
theorem B601505 : Blo 175800 601505 := bstep (se 2 (by rfl) ⟨225564, by rfl⟩ : syracuseStep 601505 = 451129) B451129
theorem B405199 : Blo 175800 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B897641 : Blo 175800 897641 := bstep (se 2 (by rfl) ⟨336615, by rfl⟩ : syracuseStep 897641 = 673231) B673231
theorem B176795 : Blo 175800 176795 := bstep (se 1 (by rfl) ⟨132596, by rfl⟩ : syracuseStep 176795 = 265193) B265193
theorem B603071 : Blo 175800 603071 := bstep (se 1 (by rfl) ⟨452303, by rfl⟩ : syracuseStep 603071 = 904607) B904607
theorem B570527 : Blo 175800 570527 := bstep (se 1 (by rfl) ⟨427895, by rfl⟩ : syracuseStep 570527 = 855791) B855791
theorem B177455 : Blo 175800 177455 := bstep (se 1 (by rfl) ⟨133091, by rfl⟩ : syracuseStep 177455 = 266183) B266183
theorem B178203 : Blo 175800 178203 := bstep (se 1 (by rfl) ⟨133652, by rfl⟩ : syracuseStep 178203 = 267305) B267305
theorem B15743483 : Blo 175800 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B1293083 : Blo 175800 1293083 := bstep (se 1 (by rfl) ⟨969812, by rfl⟩ : syracuseStep 1293083 = 1939625) B1939625
theorem B637807 : Blo 175800 637807 := bstep (se 1 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 637807 = 956711) B956711
theorem B11714543 : Blo 175800 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B606473 : Blo 175800 606473 := bstep (se 2 (by rfl) ⟨227427, by rfl⟩ : syracuseStep 606473 = 454855) B454855
theorem B7750181 : Blo 175800 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B1426045 : Blo 175800 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B6177545 : Blo 175800 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B1525979 : Blo 175800 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B2873627 : Blo 175800 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B1203011 : Blo 175800 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B908819 : Blo 175800 908819 := bstep (se 1 (by rfl) ⟨681614, by rfl⟩ : syracuseStep 908819 = 1363229) B1363229
theorem B2286305 : Blo 175800 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B680795 : Blo 175800 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B2253703 : Blo 175800 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B5829245 : Blo 175800 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B258727 : Blo 175800 258727 := bstep (se 1 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 258727 = 388091) B388091
theorem B15234641 : Blo 175800 15234641 := bstep (se 2 (by rfl) ⟨5712990, by rfl⟩ : syracuseStep 15234641 = 11425981) B11425981
theorem B522067 : Blo 175800 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B2259035 : Blo 175800 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B784703 : Blo 175800 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B1901393 : Blo 175800 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B1017319 : Blo 175800 1017319 := bstep (se 1 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 1017319 = 1525979) B1525979
theorem B1706579 : Blo 175800 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B264959 : Blo 175800 264959 := bstep (se 1 (by rfl) ⟨198719, by rfl⟩ : syracuseStep 264959 = 397439) B397439
theorem B265343 : Blo 175800 265343 := bstep (se 1 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 265343 = 398015) B398015
theorem B397007 : Blo 175800 397007 := bstep (se 1 (by rfl) ⟨297755, by rfl⟩ : syracuseStep 397007 = 595511) B595511
theorem B200551 : Blo 175800 200551 := bstep (se 1 (by rfl) ⟨150413, by rfl⟩ : syracuseStep 200551 = 300827) B300827
theorem B1839131 : Blo 175800 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B1905119 : Blo 175800 1905119 := bstep (se 1 (by rfl) ⟨1428839, by rfl⟩ : syracuseStep 1905119 = 2857679) B2857679
theorem B399851 : Blo 175800 399851 := bstep (se 1 (by rfl) ⟨299888, by rfl⟩ : syracuseStep 399851 = 599777) B599777
theorem B597455 : Blo 175800 597455 := bstep (se 1 (by rfl) ⟨448091, by rfl⟩ : syracuseStep 597455 = 896183) B896183
theorem B401003 : Blo 175800 401003 := bstep (se 1 (by rfl) ⟨300752, by rfl⟩ : syracuseStep 401003 = 601505) B601505
theorem B696089 : Blo 175800 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B598427 : Blo 175800 598427 := bstep (se 1 (by rfl) ⟨448820, by rfl⟩ : syracuseStep 598427 = 897641) B897641
theorem B402047 : Blo 175800 402047 := bstep (se 1 (by rfl) ⟨301535, by rfl⟩ : syracuseStep 402047 = 603071) B603071
theorem B10495655 : Blo 175800 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B862055 : Blo 175800 862055 := bstep (se 1 (by rfl) ⟨646541, by rfl⟩ : syracuseStep 862055 = 1293083) B1293083
theorem B7809695 : Blo 175800 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B1354553 : Blo 175800 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B404315 : Blo 175800 404315 := bstep (se 1 (by rfl) ⟨303236, by rfl⟩ : syracuseStep 404315 = 606473) B606473
theorem B1552763 : Blo 175800 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B176879 : Blo 175800 176879 := bstep (se 1 (by rfl) ⟨132659, by rfl⟩ : syracuseStep 176879 = 265319) B265319
theorem B177243 : Blo 175800 177243 := bstep (se 1 (by rfl) ⟨132932, by rfl⟩ : syracuseStep 177243 = 265865) B265865
theorem B177343 : Blo 175800 177343 := bstep (se 1 (by rfl) ⟨133007, by rfl⟩ : syracuseStep 177343 = 266015) B266015
theorem B177435 : Blo 175800 177435 := bstep (se 1 (by rfl) ⟨133076, by rfl⟩ : syracuseStep 177435 = 266153) B266153
theorem B669161 : Blo 175800 669161 := bstep (se 2 (by rfl) ⟨250935, by rfl⟩ : syracuseStep 669161 = 501871) B501871
theorem B178175 : Blo 175800 178175 := bstep (se 1 (by rfl) ⟨133631, by rfl⟩ : syracuseStep 178175 = 267263) B267263
theorem B178335 : Blo 175800 178335 := bstep (se 1 (by rfl) ⟨133751, by rfl⟩ : syracuseStep 178335 = 267503) B267503
theorem B3062015 : Blo 175800 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B178587 : Blo 175800 178587 := bstep (se 1 (by rfl) ⟨133940, by rfl⟩ : syracuseStep 178587 = 267881) B267881
theorem B19839497 : Blo 175800 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B1915751 : Blo 175800 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B802007 : Blo 175800 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B540265 : Blo 175800 540265 := bstep (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) B405199
theorem B605879 : Blo 175800 605879 := bstep (se 1 (by rfl) ⟨454409, by rfl⟩ : syracuseStep 605879 = 908819) B908819
theorem B1524203 : Blo 175800 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B344969 : Blo 175800 344969 := bstep (se 2 (by rfl) ⟨129363, by rfl⟩ : syracuseStep 344969 = 258727) B258727
theorem B3886163 : Blo 175800 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B380351 : Blo 175800 380351 := bstep (se 1 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 380351 = 570527) B570527
theorem B1364201 : Blo 175800 1364201 := bstep (se 2 (by rfl) ⟨511575, by rfl⟩ : syracuseStep 1364201 = 1023151) B1023151
theorem B5166787 : Blo 175800 5166787 := bstep (se 1 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 5166787 = 7750181) B7750181
theorem B1529603 : Blo 175800 1529603 := bstep (se 1 (by rfl) ⟨1147202, by rfl⟩ : syracuseStep 1529603 = 2294405) B2294405
theorem B4118363 : Blo 175800 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B3004937 : Blo 175800 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B681007 : Blo 175800 681007 := bstep (se 1 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 681007 = 1021511) B1021511
theorem B453863 : Blo 175800 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B10156427 : Blo 175800 10156427 := bstep (se 1 (by rfl) ⟨7617320, by rfl⟩ : syracuseStep 10156427 = 15234641) B15234641
theorem B850409 : Blo 175800 850409 := bstep (se 2 (by rfl) ⟨318903, by rfl⟩ : syracuseStep 850409 = 637807) B637807
theorem B1506023 : Blo 175800 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B523135 : Blo 175800 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B1016135 : Blo 175800 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B229979 : Blo 175800 229979 := bstep (se 1 (by rfl) ⟨172484, by rfl⟩ : syracuseStep 229979 = 344969) B344969
theorem B2590775 : Blo 175800 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B264671 : Blo 175800 264671 := bstep (se 1 (by rfl) ⟨198503, by rfl⟩ : syracuseStep 264671 = 397007) B397007
theorem B1019735 : Blo 175800 1019735 := bstep (se 1 (by rfl) ⟨764801, by rfl⟩ : syracuseStep 1019735 = 1529603) B1529603
theorem B266567 : Blo 175800 266567 := bstep (se 1 (by rfl) ⟨199925, by rfl⟩ : syracuseStep 266567 = 399851) B399851
theorem B2003291 : Blo 175800 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B398303 : Blo 175800 398303 := bstep (se 1 (by rfl) ⟨298727, by rfl⟩ : syracuseStep 398303 = 597455) B597455
theorem B267335 : Blo 175800 267335 := bstep (se 1 (by rfl) ⟨200501, by rfl⟩ : syracuseStep 267335 = 401003) B401003
theorem B267401 : Blo 175800 267401 := bstep (se 2 (by rfl) ⟨100275, by rfl⟩ : syracuseStep 267401 = 200551) B200551
theorem B464059 : Blo 175800 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B398951 : Blo 175800 398951 := bstep (se 1 (by rfl) ⟨299213, by rfl⟩ : syracuseStep 398951 = 598427) B598427
theorem B268031 : Blo 175800 268031 := bstep (se 1 (by rfl) ⟨201023, by rfl⟩ : syracuseStep 268031 = 402047) B402047
theorem B269543 : Blo 175800 269543 := bstep (se 1 (by rfl) ⟨202157, by rfl⟩ : syracuseStep 269543 = 404315) B404315
theorem B302575 : Blo 175800 302575 := bstep (se 1 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 302575 = 453863) B453863
theorem B6889049 : Blo 175800 6889049 := bstep (se 2 (by rfl) ⟨2583393, by rfl⟩ : syracuseStep 6889049 = 5166787) B5166787
theorem B697513 : Blo 175800 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B2041343 : Blo 175800 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B566939 : Blo 175800 566939 := bstep (se 1 (by rfl) ⟨425204, by rfl⟩ : syracuseStep 566939 = 850409) B850409
theorem B534671 : Blo 175800 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B403919 : Blo 175800 403919 := bstep (se 1 (by rfl) ⟨302939, by rfl⟩ : syracuseStep 403919 = 605879) B605879
theorem B176639 : Blo 175800 176639 := bstep (se 1 (by rfl) ⟨132479, by rfl⟩ : syracuseStep 176639 = 264959) B264959
theorem B1356425 : Blo 175800 1356425 := bstep (se 2 (by rfl) ⟨508659, by rfl⟩ : syracuseStep 1356425 = 1017319) B1017319
theorem B176895 : Blo 175800 176895 := bstep (se 1 (by rfl) ⟨132671, by rfl⟩ : syracuseStep 176895 = 265343) B265343
theorem B1226087 : Blo 175800 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B6997103 : Blo 175800 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B574703 : Blo 175800 574703 := bstep (se 1 (by rfl) ⟨431027, by rfl⟩ : syracuseStep 574703 = 862055) B862055
theorem B52905325 : Blo 175800 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B903035 : Blo 175800 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B1035175 : Blo 175800 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B446107 : Blo 175800 446107 := bstep (se 1 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 446107 = 669161) B669161
theorem B6770951 : Blo 175800 6770951 := bstep (se 1 (by rfl) ⟨5078213, by rfl⟩ : syracuseStep 6770951 = 10156427) B10156427
theorem B1004015 : Blo 175800 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B1267595 : Blo 175800 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B908009 : Blo 175800 908009 := bstep (se 2 (by rfl) ⟨340503, by rfl⟩ : syracuseStep 908009 = 681007) B681007
theorem B1137719 : Blo 175800 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B253567 : Blo 175800 253567 := bstep (se 1 (by rfl) ⟨190175, by rfl⟩ : syracuseStep 253567 = 380351) B380351
theorem B909467 : Blo 175800 909467 := bstep (se 1 (by rfl) ⟨682100, by rfl⟩ : syracuseStep 909467 = 1364201) B1364201
theorem B1270079 : Blo 175800 1270079 := bstep (se 1 (by rfl) ⟨952559, by rfl⟩ : syracuseStep 1270079 = 1905119) B1905119
theorem B2745575 : Blo 175800 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B5206463 : Blo 175800 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B1277167 : Blo 175800 1277167 := bstep (se 1 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 1277167 = 1915751) B1915751
theorem B720353 : Blo 175800 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B265535 : Blo 175800 265535 := bstep (se 1 (by rfl) ⟨199151, by rfl⟩ : syracuseStep 265535 = 398303) B398303
theorem B265967 : Blo 175800 265967 := bstep (se 1 (by rfl) ⟨199475, by rfl⟩ : syracuseStep 265967 = 398951) B398951
theorem B1380233 : Blo 175800 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B758479 : Blo 175800 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B594809 : Blo 175800 594809 := bstep (se 2 (by rfl) ⟨223053, by rfl⟩ : syracuseStep 594809 = 446107) B446107
theorem B4592699 : Blo 175800 4592699 := bstep (se 1 (by rfl) ⟨3444524, by rfl⟩ : syracuseStep 4592699 = 6889049) B6889049
theorem B269279 : Blo 175800 269279 := bstep (se 1 (by rfl) ⟨201959, by rfl⟩ : syracuseStep 269279 = 403919) B403919
theorem B403433 : Blo 175800 403433 := bstep (se 2 (by rfl) ⟨151287, by rfl⟩ : syracuseStep 403433 = 302575) B302575
theorem B338089 : Blo 175800 338089 := bstep (se 2 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 338089 = 253567) B253567
theorem B4664735 : Blo 175800 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B602023 : Blo 175800 602023 := bstep (se 1 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 602023 = 903035) B903035
theorem B930017 : Blo 175800 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B176447 : Blo 175800 176447 := bstep (se 1 (by rfl) ⟨132335, by rfl⟩ : syracuseStep 176447 = 264671) B264671
theorem B177711 : Blo 175800 177711 := bstep (se 1 (by rfl) ⟨133283, by rfl⟩ : syracuseStep 177711 = 266567) B266567
theorem B669343 : Blo 175800 669343 := bstep (se 1 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 669343 = 1004015) B1004015
theorem B178223 : Blo 175800 178223 := bstep (se 1 (by rfl) ⟨133667, by rfl⟩ : syracuseStep 178223 = 267335) B267335
theorem B178267 : Blo 175800 178267 := bstep (se 1 (by rfl) ⟨133700, by rfl⟩ : syracuseStep 178267 = 267401) B267401
theorem B178687 : Blo 175800 178687 := bstep (se 1 (by rfl) ⟨134015, by rfl⟩ : syracuseStep 178687 = 268031) B268031
theorem B605339 : Blo 175800 605339 := bstep (se 1 (by rfl) ⟨454004, by rfl⟩ : syracuseStep 605339 = 908009) B908009
theorem B179695 : Blo 175800 179695 := bstep (se 1 (by rfl) ⟨134771, by rfl⟩ : syracuseStep 179695 = 269543) B269543
theorem B606311 : Blo 175800 606311 := bstep (se 1 (by rfl) ⟨454733, by rfl⟩ : syracuseStep 606311 = 909467) B909467
theorem B1360895 : Blo 175800 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B377959 : Blo 175800 377959 := bstep (se 1 (by rfl) ⟨283469, by rfl⟩ : syracuseStep 377959 = 566939) B566939
theorem B904283 : Blo 175800 904283 := bstep (se 1 (by rfl) ⟨678212, by rfl⟩ : syracuseStep 904283 = 1356425) B1356425
theorem B480235 : Blo 175800 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B677423 : Blo 175800 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B383135 : Blo 175800 383135 := bstep (se 1 (by rfl) ⟨287351, by rfl⟩ : syracuseStep 383135 = 574703) B574703
theorem B1727183 : Blo 175800 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B613277 : Blo 175800 613277 := bstep (se 3 (by rfl) ⟨114989, by rfl⟩ : syracuseStep 613277 = 229979) B229979
theorem B70540433 : Blo 175800 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B679823 : Blo 175800 679823 := bstep (se 1 (by rfl) ⟨509867, by rfl⟩ : syracuseStep 679823 = 1019735) B1019735
theorem B4513967 : Blo 175800 4513967 := bstep (se 1 (by rfl) ⟨3385475, by rfl⟩ : syracuseStep 4513967 = 6770951) B6770951
theorem B1335527 : Blo 175800 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B845063 : Blo 175800 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B846719 : Blo 175800 846719 := bstep (se 1 (by rfl) ⟨635039, by rfl⟩ : syracuseStep 846719 = 1270079) B1270079
theorem B1830383 : Blo 175800 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B356447 : Blo 175800 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B618745 : Blo 175800 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B3470975 : Blo 175800 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B817391 : Blo 175800 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B1702889 : Blo 175800 1702889 := bstep (se 2 (by rfl) ⟨638583, by rfl⟩ : syracuseStep 1702889 = 1277167) B1277167
theorem B950525 : Blo 175800 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B920155 : Blo 175800 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B396539 : Blo 175800 396539 := bstep (se 1 (by rfl) ⟨297404, by rfl⟩ : syracuseStep 396539 = 594809) B594809
theorem B47026955 : Blo 175800 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B890351 : Blo 175800 890351 := bstep (se 1 (by rfl) ⟨667763, by rfl⟩ : syracuseStep 890351 = 1335527) B1335527
theorem B824993 : Blo 175800 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B1021693 : Blo 175800 1021693 := bstep (se 3 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 1021693 = 383135) B383135
theorem B563375 : Blo 175800 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B268955 : Blo 175800 268955 := bstep (se 1 (by rfl) ⟨201716, by rfl⟩ : syracuseStep 268955 = 403433) B403433
theorem B564479 : Blo 175800 564479 := bstep (se 1 (by rfl) ⟨423359, by rfl⟩ : syracuseStep 564479 = 846719) B846719
theorem B892457 : Blo 175800 892457 := bstep (se 2 (by rfl) ⟨334671, by rfl⟩ : syracuseStep 892457 = 669343) B669343
theorem B1220255 : Blo 175800 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B403559 : Blo 175800 403559 := bstep (se 1 (by rfl) ⟨302669, by rfl⟩ : syracuseStep 403559 = 605339) B605339
theorem B404207 : Blo 175800 404207 := bstep (se 1 (by rfl) ⟨303155, by rfl⟩ : syracuseStep 404207 = 606311) B606311
theorem B503945 : Blo 175800 503945 := bstep (se 2 (by rfl) ⟨188979, by rfl⟩ : syracuseStep 503945 = 377959) B377959
theorem B602855 : Blo 175800 602855 := bstep (se 1 (by rfl) ⟨452141, by rfl⟩ : syracuseStep 602855 = 904283) B904283
theorem B177023 : Blo 175800 177023 := bstep (se 1 (by rfl) ⟨132767, by rfl⟩ : syracuseStep 177023 = 265535) B265535
theorem B177311 : Blo 175800 177311 := bstep (se 1 (by rfl) ⟨132983, by rfl⟩ : syracuseStep 177311 = 265967) B265967
theorem B3061799 : Blo 175800 3061799 := bstep (se 1 (by rfl) ⟨2296349, by rfl⟩ : syracuseStep 3061799 = 4592699) B4592699
theorem B408851 : Blo 175800 408851 := bstep (se 1 (by rfl) ⟨306638, by rfl⟩ : syracuseStep 408851 = 613277) B613277
theorem B179519 : Blo 175800 179519 := bstep (se 1 (by rfl) ⟨134639, by rfl⟩ : syracuseStep 179519 = 269279) B269279
theorem B2179709 : Blo 175800 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B640313 : Blo 175800 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B4605821 : Blo 175800 4605821 := bstep (se 3 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 4605821 = 1727183) B1727183
theorem B2313983 : Blo 175800 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B1135259 : Blo 175800 1135259 := bstep (se 1 (by rfl) ⟨851444, by rfl⟩ : syracuseStep 1135259 = 1702889) B1702889
theorem B3629053 : Blo 175800 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B450785 : Blo 175800 450785 := bstep (se 2 (by rfl) ⟨169044, by rfl⟩ : syracuseStep 450785 = 338089) B338089
theorem B451615 : Blo 175800 451615 := bstep (se 1 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 451615 = 677423) B677423
theorem B453215 : Blo 175800 453215 := bstep (se 1 (by rfl) ⟨339911, by rfl⟩ : syracuseStep 453215 = 679823) B679823
theorem B3009311 : Blo 175800 3009311 := bstep (se 1 (by rfl) ⟨2256983, by rfl⟩ : syracuseStep 3009311 = 4513967) B4513967
theorem B1011305 : Blo 175800 1011305 := bstep (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) B758479
theorem B3109823 : Blo 175800 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B620011 : Blo 175800 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B12843157 : Blo 175800 12843157 := bstep (se 6 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 12843157 = 602023) B602023
theorem B426875 : Blo 175800 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B264359 : Blo 175800 264359 := bstep (se 1 (by rfl) ⟨198269, by rfl⟩ : syracuseStep 264359 = 396539) B396539
theorem B1542655 : Blo 175800 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B756839 : Blo 175800 756839 := bstep (se 1 (by rfl) ⟨567629, by rfl⟩ : syracuseStep 756839 = 1135259) B1135259
theorem B593567 : Blo 175800 593567 := bstep (se 1 (by rfl) ⟨445175, by rfl⟩ : syracuseStep 593567 = 890351) B890351
theorem B594971 : Blo 175800 594971 := bstep (se 1 (by rfl) ⟨446228, by rfl⟩ : syracuseStep 594971 = 892457) B892457
theorem B300523 : Blo 175800 300523 := bstep (se 1 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 300523 = 450785) B450785
theorem B269039 : Blo 175800 269039 := bstep (se 1 (by rfl) ⟨201779, by rfl⟩ : syracuseStep 269039 = 403559) B403559
theorem B302143 : Blo 175800 302143 := bstep (se 1 (by rfl) ⟨226607, by rfl⟩ : syracuseStep 302143 = 453215) B453215
theorem B269471 : Blo 175800 269471 := bstep (se 1 (by rfl) ⟨202103, by rfl⟩ : syracuseStep 269471 = 404207) B404207
theorem B2006207 : Blo 175800 2006207 := bstep (se 1 (by rfl) ⟨1504655, by rfl⟩ : syracuseStep 2006207 = 3009311) B3009311
theorem B826681 : Blo 175800 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B335963 : Blo 175800 335963 := bstep (se 1 (by rfl) ⟨251972, by rfl⟩ : syracuseStep 335963 = 503945) B503945
theorem B401903 : Blo 175800 401903 := bstep (se 1 (by rfl) ⟨301427, by rfl⟩ : syracuseStep 401903 = 602855) B602855
theorem B2073215 : Blo 175800 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B2041199 : Blo 175800 2041199 := bstep (se 1 (by rfl) ⟨1530899, by rfl⟩ : syracuseStep 2041199 = 3061799) B3061799
theorem B272567 : Blo 175800 272567 := bstep (se 1 (by rfl) ⟨204425, by rfl⟩ : syracuseStep 272567 = 408851) B408851
theorem B633683 : Blo 175800 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B1453139 : Blo 175800 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B602153 : Blo 175800 602153 := bstep (se 2 (by rfl) ⟨225807, by rfl⟩ : syracuseStep 602153 = 451615) B451615
theorem B1226873 : Blo 175800 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B179303 : Blo 175800 179303 := bstep (se 1 (by rfl) ⟨134477, by rfl⟩ : syracuseStep 179303 = 268955) B268955
theorem B376319 : Blo 175800 376319 := bstep (se 1 (by rfl) ⟨282239, by rfl⟩ : syracuseStep 376319 = 564479) B564479
theorem B1362257 : Blo 175800 1362257 := bstep (se 2 (by rfl) ⟨510846, by rfl⟩ : syracuseStep 1362257 = 1021693) B1021693
theorem B674203 : Blo 175800 674203 := bstep (se 1 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 674203 = 1011305) B1011305
theorem B17124209 : Blo 175800 17124209 := bstep (se 2 (by rfl) ⟨6421578, by rfl⟩ : syracuseStep 17124209 = 12843157) B12843157
theorem B4838737 : Blo 175800 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B3070547 : Blo 175800 3070547 := bstep (se 1 (by rfl) ⟨2302910, by rfl⟩ : syracuseStep 3070547 = 4605821) B4605821
theorem B31351303 : Blo 175800 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B549995 : Blo 175800 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B813503 : Blo 175800 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B1502333 : Blo 175800 1502333 := bstep (se 3 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 1502333 = 563375) B563375
theorem B5866613 : Blo 175800 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B395711 : Blo 175800 395711 := bstep (se 1 (by rfl) ⟨296783, by rfl⟩ : syracuseStep 395711 = 593567) B593567
theorem B8227493 : Blo 175800 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B396647 : Blo 175800 396647 := bstep (se 1 (by rfl) ⟨297485, by rfl⟩ : syracuseStep 396647 = 594971) B594971
theorem B267935 : Blo 175800 267935 := bstep (se 1 (by rfl) ⟨200951, by rfl⟩ : syracuseStep 267935 = 401903) B401903
theorem B1382143 : Blo 175800 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B400697 : Blo 175800 400697 := bstep (se 2 (by rfl) ⟨150261, by rfl⟩ : syracuseStep 400697 = 300523) B300523
theorem B401435 : Blo 175800 401435 := bstep (se 1 (by rfl) ⟨301076, by rfl⟩ : syracuseStep 401435 = 602153) B602153
theorem B402857 : Blo 175800 402857 := bstep (se 2 (by rfl) ⟨151071, by rfl⟩ : syracuseStep 402857 = 302143) B302143
theorem B176239 : Blo 175800 176239 := bstep (se 1 (by rfl) ⟨132179, by rfl⟩ : syracuseStep 176239 = 264359) B264359
theorem B11416139 : Blo 175800 11416139 := bstep (se 1 (by rfl) ⟨8562104, by rfl⟩ : syracuseStep 11416139 = 17124209) B17124209
theorem B504559 : Blo 175800 504559 := bstep (se 1 (by rfl) ⟨378419, by rfl⟩ : syracuseStep 504559 = 756839) B756839
theorem B898937 : Blo 175800 898937 := bstep (se 2 (by rfl) ⟨337101, by rfl⟩ : syracuseStep 898937 = 674203) B674203
theorem B2047031 : Blo 175800 2047031 := bstep (se 1 (by rfl) ⟨1535273, by rfl⟩ : syracuseStep 2047031 = 3070547) B3070547
theorem B179359 : Blo 175800 179359 := bstep (se 1 (by rfl) ⟨134519, by rfl⟩ : syracuseStep 179359 = 269039) B269039
theorem B179647 : Blo 175800 179647 := bstep (se 1 (by rfl) ⟨134735, by rfl⟩ : syracuseStep 179647 = 269471) B269471
theorem B1360799 : Blo 175800 1360799 := bstep (se 1 (by rfl) ⟨1020599, by rfl⟩ : syracuseStep 1360799 = 2041199) B2041199
theorem B181711 : Blo 175800 181711 := bstep (se 1 (by rfl) ⟨136283, by rfl⟩ : syracuseStep 181711 = 272567) B272567
theorem B542335 : Blo 175800 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B968759 : Blo 175800 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B1001555 : Blo 175800 1001555 := bstep (se 1 (by rfl) ⟨751166, by rfl⟩ : syracuseStep 1001555 = 1502333) B1502333
theorem B1689821 : Blo 175800 1689821 := bstep (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) B633683
theorem B1102241 : Blo 175800 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B250879 : Blo 175800 250879 := bstep (se 1 (by rfl) ⟨188159, by rfl⟩ : syracuseStep 250879 = 376319) B376319
theorem B908171 : Blo 175800 908171 := bstep (se 1 (by rfl) ⟨681128, by rfl⟩ : syracuseStep 908171 = 1362257) B1362257
theorem B167206949 : Blo 175800 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B1337471 : Blo 175800 1337471 := bstep (se 1 (by rfl) ⟨1003103, by rfl⟩ : syracuseStep 1337471 = 2006207) B2006207
theorem B223975 : Blo 175800 223975 := bstep (se 1 (by rfl) ⟨167981, by rfl⟩ : syracuseStep 223975 = 335963) B335963
theorem B3271661 : Blo 175800 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B6451649 : Blo 175800 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B4553333 : Blo 175800 4553333 := bstep (se 5 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 4553333 = 426875) B426875
theorem B263807 : Blo 175800 263807 := bstep (se 1 (by rfl) ⟨197855, by rfl⟩ : syracuseStep 263807 = 395711) B395711
theorem B723113 : Blo 175800 723113 := bstep (se 2 (by rfl) ⟨271167, by rfl⟩ : syracuseStep 723113 = 542335) B542335
theorem B264431 : Blo 175800 264431 := bstep (se 1 (by rfl) ⟨198323, by rfl⟩ : syracuseStep 264431 = 396647) B396647
theorem B298633 : Blo 175800 298633 := bstep (se 2 (by rfl) ⟨111987, by rfl⟩ : syracuseStep 298633 = 223975) B223975
theorem B267131 : Blo 175800 267131 := bstep (se 1 (by rfl) ⟨200348, by rfl⟩ : syracuseStep 267131 = 400697) B400697
theorem B267623 : Blo 175800 267623 := bstep (se 1 (by rfl) ⟨200717, by rfl⟩ : syracuseStep 267623 = 401435) B401435
theorem B268571 : Blo 175800 268571 := bstep (se 1 (by rfl) ⟨201428, by rfl⟩ : syracuseStep 268571 = 402857) B402857
theorem B334505 : Blo 175800 334505 := bstep (se 2 (by rfl) ⟨125439, by rfl⟩ : syracuseStep 334505 = 250879) B250879
theorem B891647 : Blo 175800 891647 := bstep (se 1 (by rfl) ⟨668735, by rfl⟩ : syracuseStep 891647 = 1337471) B1337471
theorem B1842857 : Blo 175800 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B4301099 : Blo 175800 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B7610759 : Blo 175800 7610759 := bstep (se 1 (by rfl) ⟨5708069, by rfl⟩ : syracuseStep 7610759 = 11416139) B11416139
theorem B599291 : Blo 175800 599291 := bstep (se 1 (by rfl) ⟨449468, by rfl⟩ : syracuseStep 599291 = 898937) B898937
theorem B3911075 : Blo 175800 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B667703 : Blo 175800 667703 := bstep (se 1 (by rfl) ⟨500777, by rfl⟩ : syracuseStep 667703 = 1001555) B1001555
theorem B1126547 : Blo 175800 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B5484995 : Blo 175800 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B242281 : Blo 175800 242281 := bstep (se 2 (by rfl) ⟨90855, by rfl⟩ : syracuseStep 242281 = 181711) B181711
theorem B734827 : Blo 175800 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B178623 : Blo 175800 178623 := bstep (se 1 (by rfl) ⟨133967, by rfl⟩ : syracuseStep 178623 = 267935) B267935
theorem B605447 : Blo 175800 605447 := bstep (se 1 (by rfl) ⟨454085, by rfl⟩ : syracuseStep 605447 = 908171) B908171
theorem B672745 : Blo 175800 672745 := bstep (se 2 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 672745 = 504559) B504559
theorem B2181107 : Blo 175800 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B3035555 : Blo 175800 3035555 := bstep (se 1 (by rfl) ⟨2276666, by rfl⟩ : syracuseStep 3035555 = 4553333) B4553333
theorem B1364687 : Blo 175800 1364687 := bstep (se 1 (by rfl) ⟨1023515, by rfl⟩ : syracuseStep 1364687 = 2047031) B2047031
theorem B907199 : Blo 175800 907199 := bstep (se 1 (by rfl) ⟨680399, by rfl⟩ : syracuseStep 907199 = 1360799) B1360799
theorem B645839 : Blo 175800 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B111471299 : Blo 175800 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B430559 : Blo 175800 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B594431 : Blo 175800 594431 := bstep (se 1 (by rfl) ⟨445823, by rfl⟩ : syracuseStep 594431 = 891647) B891647
theorem B398177 : Blo 175800 398177 := bstep (se 2 (by rfl) ⟨149316, by rfl⟩ : syracuseStep 398177 = 298633) B298633
theorem B399527 : Blo 175800 399527 := bstep (se 1 (by rfl) ⟨299645, by rfl⟩ : syracuseStep 399527 = 599291) B599291
theorem B403631 : Blo 175800 403631 := bstep (se 1 (by rfl) ⟨302723, by rfl⟩ : syracuseStep 403631 = 605447) B605447
theorem B175871 : Blo 175800 175871 := bstep (se 1 (by rfl) ⟨131903, by rfl⟩ : syracuseStep 175871 = 263807) B263807
theorem B896993 : Blo 175800 896993 := bstep (se 2 (by rfl) ⟨336372, by rfl⟩ : syracuseStep 896993 = 672745) B672745
theorem B1454071 : Blo 175800 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B176287 : Blo 175800 176287 := bstep (se 1 (by rfl) ⟨132215, by rfl⟩ : syracuseStep 176287 = 264431) B264431
theorem B178087 : Blo 175800 178087 := bstep (se 1 (by rfl) ⟨133565, by rfl⟩ : syracuseStep 178087 = 267131) B267131
theorem B178415 : Blo 175800 178415 := bstep (se 1 (by rfl) ⟨133811, by rfl⟩ : syracuseStep 178415 = 267623) B267623
theorem B604799 : Blo 175800 604799 := bstep (se 1 (by rfl) ⟨453599, by rfl⟩ : syracuseStep 604799 = 907199) B907199
theorem B179047 : Blo 175800 179047 := bstep (se 1 (by rfl) ⟨134285, by rfl⟩ : syracuseStep 179047 = 268571) B268571
theorem B1228571 : Blo 175800 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B2867399 : Blo 175800 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B2607383 : Blo 175800 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B445135 : Blo 175800 445135 := bstep (se 1 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 445135 = 667703) B667703
theorem B3656663 : Blo 175800 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B482075 : Blo 175800 482075 := bstep (se 1 (by rfl) ⟨361556, by rfl⟩ : syracuseStep 482075 = 723113) B723113
theorem B2023703 : Blo 175800 2023703 := bstep (se 1 (by rfl) ⟨1517777, by rfl⟩ : syracuseStep 2023703 = 3035555) B3035555
theorem B909791 : Blo 175800 909791 := bstep (se 1 (by rfl) ⟨682343, by rfl⟩ : syracuseStep 909791 = 1364687) B1364687
theorem B223003 : Blo 175800 223003 := bstep (se 1 (by rfl) ⟨167252, by rfl⟩ : syracuseStep 223003 = 334505) B334505
theorem B5073839 : Blo 175800 5073839 := bstep (se 1 (by rfl) ⟨3805379, by rfl⟩ : syracuseStep 5073839 = 7610759) B7610759
theorem B323041 : Blo 175800 323041 := bstep (se 2 (by rfl) ⟨121140, by rfl⟩ : syracuseStep 323041 = 242281) B242281
theorem B74314199 : Blo 175800 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B979769 : Blo 175800 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B751031 : Blo 175800 751031 := bstep (se 1 (by rfl) ⟨563273, by rfl⟩ : syracuseStep 751031 = 1126547) B1126547
theorem B1738255 : Blo 175800 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B297337 : Blo 175800 297337 := bstep (se 2 (by rfl) ⟨111501, by rfl⟩ : syracuseStep 297337 = 223003) B223003
theorem B396287 : Blo 175800 396287 := bstep (se 1 (by rfl) ⟨297215, by rfl⟩ : syracuseStep 396287 = 594431) B594431
theorem B265451 : Blo 175800 265451 := bstep (se 1 (by rfl) ⟨199088, by rfl⟩ : syracuseStep 265451 = 398177) B398177
theorem B593513 : Blo 175800 593513 := bstep (se 2 (by rfl) ⟨222567, by rfl⟩ : syracuseStep 593513 = 445135) B445135
theorem B266351 : Blo 175800 266351 := bstep (se 1 (by rfl) ⟨199763, by rfl⟩ : syracuseStep 266351 = 399527) B399527
theorem B430721 : Blo 175800 430721 := bstep (se 2 (by rfl) ⟨161520, by rfl⟩ : syracuseStep 430721 = 323041) B323041
theorem B1938761 : Blo 175800 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B1349135 : Blo 175800 1349135 := bstep (se 1 (by rfl) ⟨1011851, by rfl⟩ : syracuseStep 1349135 = 2023703) B2023703
theorem B269087 : Blo 175800 269087 := bstep (se 1 (by rfl) ⟨201815, by rfl⟩ : syracuseStep 269087 = 403631) B403631
theorem B3382559 : Blo 175800 3382559 := bstep (se 1 (by rfl) ⟨2536919, by rfl⟩ : syracuseStep 3382559 = 5073839) B5073839
theorem B597995 : Blo 175800 597995 := bstep (se 1 (by rfl) ⟨448496, by rfl⟩ : syracuseStep 597995 = 896993) B896993
theorem B500687 : Blo 175800 500687 := bstep (se 1 (by rfl) ⟨375515, by rfl⟩ : syracuseStep 500687 = 751031) B751031
theorem B403199 : Blo 175800 403199 := bstep (se 1 (by rfl) ⟨302399, by rfl⟩ : syracuseStep 403199 = 604799) B604799
theorem B1911599 : Blo 175800 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B2437775 : Blo 175800 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B606527 : Blo 175800 606527 := bstep (se 1 (by rfl) ⟨454895, by rfl⟩ : syracuseStep 606527 = 909791) B909791
theorem B287039 : Blo 175800 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B321383 : Blo 175800 321383 := bstep (se 1 (by rfl) ⟨241037, by rfl⟩ : syracuseStep 321383 = 482075) B482075
theorem B49542799 : Blo 175800 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B653179 : Blo 175800 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B819047 : Blo 175800 819047 := bstep (se 1 (by rfl) ⟨614285, by rfl⟩ : syracuseStep 819047 = 1228571) B1228571
theorem B264191 : Blo 175800 264191 := bstep (se 1 (by rfl) ⟨198143, by rfl⟩ : syracuseStep 264191 = 396287) B396287
theorem B395675 : Blo 175800 395675 := bstep (se 1 (by rfl) ⟨296756, by rfl⟩ : syracuseStep 395675 = 593513) B593513
theorem B396449 : Blo 175800 396449 := bstep (se 2 (by rfl) ⟨148668, by rfl⟩ : syracuseStep 396449 = 297337) B297337
theorem B398663 : Blo 175800 398663 := bstep (se 1 (by rfl) ⟨298997, by rfl⟩ : syracuseStep 398663 = 597995) B597995
theorem B333791 : Blo 175800 333791 := bstep (se 1 (by rfl) ⟨250343, by rfl⟩ : syracuseStep 333791 = 500687) B500687
theorem B268799 : Blo 175800 268799 := bstep (se 1 (by rfl) ⟨201599, by rfl⟩ : syracuseStep 268799 = 403199) B403199
theorem B404351 : Blo 175800 404351 := bstep (se 1 (by rfl) ⟨303263, by rfl⟩ : syracuseStep 404351 = 606527) B606527
theorem B176967 : Blo 175800 176967 := bstep (se 1 (by rfl) ⟨132725, by rfl⟩ : syracuseStep 176967 = 265451) B265451
theorem B177567 : Blo 175800 177567 := bstep (se 1 (by rfl) ⟨133175, by rfl⟩ : syracuseStep 177567 = 266351) B266351
theorem B1292507 : Blo 175800 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B899423 : Blo 175800 899423 := bstep (se 1 (by rfl) ⟨674567, by rfl⟩ : syracuseStep 899423 = 1349135) B1349135
theorem B179391 : Blo 175800 179391 := bstep (se 1 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 179391 = 269087) B269087
theorem B214255 : Blo 175800 214255 := bstep (se 1 (by rfl) ⟨160691, by rfl⟩ : syracuseStep 214255 = 321383) B321383
theorem B870905 : Blo 175800 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B1625183 : Blo 175800 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B546031 : Blo 175800 546031 := bstep (se 1 (by rfl) ⟨409523, by rfl⟩ : syracuseStep 546031 = 819047) B819047
theorem B2317673 : Blo 175800 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B287147 : Blo 175800 287147 := bstep (se 1 (by rfl) ⟨215360, by rfl⟩ : syracuseStep 287147 = 430721) B430721
theorem B2255039 : Blo 175800 2255039 := bstep (se 1 (by rfl) ⟨1691279, by rfl⟩ : syracuseStep 2255039 = 3382559) B3382559
theorem B191359 : Blo 175800 191359 := bstep (se 1 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 191359 = 287039) B287039
theorem B1274399 : Blo 175800 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B66057065 : Blo 175800 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B263783 : Blo 175800 263783 := bstep (se 1 (by rfl) ⟨197837, by rfl⟩ : syracuseStep 263783 = 395675) B395675
theorem B1083455 : Blo 175800 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B264299 : Blo 175800 264299 := bstep (se 1 (by rfl) ⟨198224, by rfl⟩ : syracuseStep 264299 = 396449) B396449
theorem B265775 : Blo 175800 265775 := bstep (se 1 (by rfl) ⟨199331, by rfl⟩ : syracuseStep 265775 = 398663) B398663
theorem B728041 : Blo 175800 728041 := bstep (se 2 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 728041 = 546031) B546031
theorem B269567 : Blo 175800 269567 := bstep (se 1 (by rfl) ⟨202175, by rfl⟩ : syracuseStep 269567 = 404351) B404351
theorem B861671 : Blo 175800 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B599615 : Blo 175800 599615 := bstep (se 1 (by rfl) ⟨449711, by rfl⟩ : syracuseStep 599615 = 899423) B899423
theorem B176127 : Blo 175800 176127 := bstep (se 1 (by rfl) ⟨132095, by rfl⟩ : syracuseStep 176127 = 264191) B264191
theorem B179199 : Blo 175800 179199 := bstep (se 1 (by rfl) ⟨134399, by rfl⟩ : syracuseStep 179199 = 268799) B268799
theorem B6180461 : Blo 175800 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B580603 : Blo 175800 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B255145 : Blo 175800 255145 := bstep (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) B191359
theorem B222527 : Blo 175800 222527 := bstep (se 1 (by rfl) ⟨166895, by rfl⟩ : syracuseStep 222527 = 333791) B333791
theorem B191431 : Blo 175800 191431 := bstep (se 1 (by rfl) ⟨143573, by rfl⟩ : syracuseStep 191431 = 287147) B287147
theorem B1142693 : Blo 175800 1142693 := bstep (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) B214255
theorem B1503359 : Blo 175800 1503359 := bstep (se 1 (by rfl) ⟨1127519, by rfl⟩ : syracuseStep 1503359 = 2255039) B2255039
theorem B849599 : Blo 175800 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B44038043 : Blo 175800 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B722303 : Blo 175800 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B593405 : Blo 175800 593405 := bstep (se 3 (by rfl) ⟨111263, by rfl⟩ : syracuseStep 593405 = 222527) B222527
theorem B399743 : Blo 175800 399743 := bstep (se 1 (by rfl) ⟨299807, by rfl⟩ : syracuseStep 399743 = 599615) B599615
theorem B761795 : Blo 175800 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B566399 : Blo 175800 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B175855 : Blo 175800 175855 := bstep (se 1 (by rfl) ⟨131891, by rfl⟩ : syracuseStep 175855 = 263783) B263783
theorem B176199 : Blo 175800 176199 := bstep (se 1 (by rfl) ⟨132149, by rfl⟩ : syracuseStep 176199 = 264299) B264299
theorem B340193 : Blo 175800 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B177183 : Blo 175800 177183 := bstep (se 1 (by rfl) ⟨132887, by rfl⟩ : syracuseStep 177183 = 265775) B265775
theorem B179711 : Blo 175800 179711 := bstep (se 1 (by rfl) ⟨134783, by rfl⟩ : syracuseStep 179711 = 269567) B269567
theorem B574447 : Blo 175800 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B1002239 : Blo 175800 1002239 := bstep (se 1 (by rfl) ⟨751679, by rfl⟩ : syracuseStep 1002239 = 1503359) B1503359
theorem B970721 : Blo 175800 970721 := bstep (se 2 (by rfl) ⟨364020, by rfl⟩ : syracuseStep 970721 = 728041) B728041
theorem B774137 : Blo 175800 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B4120307 : Blo 175800 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B255241 : Blo 175800 255241 := bstep (se 2 (by rfl) ⟨95715, by rfl⟩ : syracuseStep 255241 = 191431) B191431
theorem B29358695 : Blo 175800 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B395603 : Blo 175800 395603 := bstep (se 1 (by rfl) ⟨296702, by rfl⟩ : syracuseStep 395603 = 593405) B593405
theorem B1510397 : Blo 175800 1510397 := bstep (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) B566399
theorem B266495 : Blo 175800 266495 := bstep (se 1 (by rfl) ⟨199871, by rfl⟩ : syracuseStep 266495 = 399743) B399743
theorem B19572463 : Blo 175800 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B765929 : Blo 175800 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B668159 : Blo 175800 668159 := bstep (se 1 (by rfl) ⟨501119, by rfl⟩ : syracuseStep 668159 = 1002239) B1002239
theorem B507863 : Blo 175800 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B1361285 : Blo 175800 1361285 := bstep (se 4 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 1361285 = 255241) B255241
theorem B481535 : Blo 175800 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B647147 : Blo 175800 647147 := bstep (se 1 (by rfl) ⟨485360, by rfl⟩ : syracuseStep 647147 = 970721) B970721
theorem B516091 : Blo 175800 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B2746871 : Blo 175800 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B226795 : Blo 175800 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B263735 : Blo 175800 263735 := bstep (se 1 (by rfl) ⟨197801, by rfl⟩ : syracuseStep 263735 = 395603) B395603
theorem B302393 : Blo 175800 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B338575 : Blo 175800 338575 := bstep (se 1 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 338575 = 507863) B507863
theorem B26096617 : Blo 175800 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B177663 : Blo 175800 177663 := bstep (se 1 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 177663 = 266495) B266495
theorem B510619 : Blo 175800 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B445439 : Blo 175800 445439 := bstep (se 1 (by rfl) ⟨334079, by rfl⟩ : syracuseStep 445439 = 668159) B668159
theorem B1725725 : Blo 175800 1725725 := bstep (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) B647147
theorem B907523 : Blo 175800 907523 := bstep (se 1 (by rfl) ⟨680642, by rfl⟩ : syracuseStep 907523 = 1361285) B1361285
theorem B1006931 : Blo 175800 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B321023 : Blo 175800 321023 := bstep (se 1 (by rfl) ⟨240767, by rfl⟩ : syracuseStep 321023 = 481535) B481535
theorem B1831247 : Blo 175800 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B688121 : Blo 175800 688121 := bstep (se 2 (by rfl) ⟨258045, by rfl⟩ : syracuseStep 688121 = 516091) B516091
theorem B296959 : Blo 175800 296959 := bstep (se 1 (by rfl) ⟨222719, by rfl⟩ : syracuseStep 296959 = 445439) B445439
theorem B1150483 : Blo 175800 1150483 := bstep (se 1 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 1150483 = 1725725) B1725725
theorem B201595 : Blo 175800 201595 := bstep (se 1 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 201595 = 302393) B302393
theorem B1220831 : Blo 175800 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B175823 : Blo 175800 175823 := bstep (se 1 (by rfl) ⟨131867, by rfl⟩ : syracuseStep 175823 = 263735) B263735
theorem B605015 : Blo 175800 605015 := bstep (se 1 (by rfl) ⟨453761, by rfl⟩ : syracuseStep 605015 = 907523) B907523
theorem B671287 : Blo 175800 671287 := bstep (se 1 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 671287 = 1006931) B1006931
theorem B214015 : Blo 175800 214015 := bstep (se 1 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 214015 = 321023) B321023
theorem B451433 : Blo 175800 451433 := bstep (se 2 (by rfl) ⟨169287, by rfl⟩ : syracuseStep 451433 = 338575) B338575
theorem B680825 : Blo 175800 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B34795489 : Blo 175800 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B458747 : Blo 175800 458747 := bstep (se 1 (by rfl) ⟨344060, by rfl⟩ : syracuseStep 458747 = 688121) B688121
theorem B395945 : Blo 175800 395945 := bstep (se 2 (by rfl) ⟨148479, by rfl⟩ : syracuseStep 395945 = 296959) B296959
theorem B300955 : Blo 175800 300955 := bstep (se 1 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 300955 = 451433) B451433
theorem B268793 : Blo 175800 268793 := bstep (se 2 (by rfl) ⟨100797, by rfl⟩ : syracuseStep 268793 = 201595) B201595
theorem B403343 : Blo 175800 403343 := bstep (se 1 (by rfl) ⟨302507, by rfl⟩ : syracuseStep 403343 = 605015) B605015
theorem B895049 : Blo 175800 895049 := bstep (se 2 (by rfl) ⟨335643, by rfl⟩ : syracuseStep 895049 = 671287) B671287
theorem B305831 : Blo 175800 305831 := bstep (se 1 (by rfl) ⟨229373, by rfl⟩ : syracuseStep 305831 = 458747) B458747
theorem B285353 : Blo 175800 285353 := bstep (se 2 (by rfl) ⟨107007, by rfl⟩ : syracuseStep 285353 = 214015) B214015
theorem B1533977 : Blo 175800 1533977 := bstep (se 2 (by rfl) ⟨575241, by rfl⟩ : syracuseStep 1533977 = 1150483) B1150483
theorem B46393985 : Blo 175800 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B813887 : Blo 175800 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B453883 : Blo 175800 453883 := bstep (se 1 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 453883 = 680825) B680825
theorem B263963 : Blo 175800 263963 := bstep (se 1 (by rfl) ⟨197972, by rfl⟩ : syracuseStep 263963 = 395945) B395945
theorem B268895 : Blo 175800 268895 := bstep (se 1 (by rfl) ⟨201671, by rfl⟩ : syracuseStep 268895 = 403343) B403343
theorem B1022651 : Blo 175800 1022651 := bstep (se 1 (by rfl) ⟨766988, by rfl⟩ : syracuseStep 1022651 = 1533977) B1533977
theorem B596699 : Blo 175800 596699 := bstep (se 1 (by rfl) ⟨447524, by rfl⟩ : syracuseStep 596699 = 895049) B895049
theorem B203887 : Blo 175800 203887 := bstep (se 1 (by rfl) ⟨152915, by rfl⟩ : syracuseStep 203887 = 305831) B305831
theorem B401273 : Blo 175800 401273 := bstep (se 2 (by rfl) ⟨150477, by rfl⟩ : syracuseStep 401273 = 300955) B300955
theorem B605177 : Blo 175800 605177 := bstep (se 2 (by rfl) ⟨226941, by rfl⟩ : syracuseStep 605177 = 453883) B453883
theorem B179195 : Blo 175800 179195 := bstep (se 1 (by rfl) ⟨134396, by rfl⟩ : syracuseStep 179195 = 268793) B268793
theorem B123717293 : Blo 175800 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B542591 : Blo 175800 542591 := bstep (se 1 (by rfl) ⟨406943, by rfl⟩ : syracuseStep 542591 = 813887) B813887
theorem B190235 : Blo 175800 190235 := bstep (se 1 (by rfl) ⟨142676, by rfl⟩ : syracuseStep 190235 = 285353) B285353
theorem B82478195 : Blo 175800 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B361727 : Blo 175800 361727 := bstep (se 1 (by rfl) ⟨271295, by rfl⟩ : syracuseStep 361727 = 542591) B542591
theorem B397799 : Blo 175800 397799 := bstep (se 1 (by rfl) ⟨298349, by rfl⟩ : syracuseStep 397799 = 596699) B596699
theorem B267515 : Blo 175800 267515 := bstep (se 1 (by rfl) ⟨200636, by rfl⟩ : syracuseStep 267515 = 401273) B401273
theorem B271849 : Blo 175800 271849 := bstep (se 2 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 271849 = 203887) B203887
theorem B403451 : Blo 175800 403451 := bstep (se 1 (by rfl) ⟨302588, by rfl⟩ : syracuseStep 403451 = 605177) B605177
theorem B175975 : Blo 175800 175975 := bstep (se 1 (by rfl) ⟨131981, by rfl⟩ : syracuseStep 175975 = 263963) B263963
theorem B179263 : Blo 175800 179263 := bstep (se 1 (by rfl) ⟨134447, by rfl⟩ : syracuseStep 179263 = 268895) B268895
theorem B507293 : Blo 175800 507293 := bstep (se 3 (by rfl) ⟨95117, by rfl⟩ : syracuseStep 507293 = 190235) B190235
theorem B681767 : Blo 175800 681767 := bstep (se 1 (by rfl) ⟨511325, by rfl⟩ : syracuseStep 681767 = 1022651) B1022651
theorem B54985463 : Blo 175800 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B362465 : Blo 175800 362465 := bstep (se 2 (by rfl) ⟨135924, by rfl⟩ : syracuseStep 362465 = 271849) B271849
theorem B265199 : Blo 175800 265199 := bstep (se 1 (by rfl) ⟨198899, by rfl⟩ : syracuseStep 265199 = 397799) B397799
theorem B268967 : Blo 175800 268967 := bstep (se 1 (by rfl) ⟨201725, by rfl⟩ : syracuseStep 268967 = 403451) B403451
theorem B338195 : Blo 175800 338195 := bstep (se 1 (by rfl) ⟨253646, by rfl⟩ : syracuseStep 338195 = 507293) B507293
theorem B241151 : Blo 175800 241151 := bstep (se 1 (by rfl) ⟨180863, by rfl⟩ : syracuseStep 241151 = 361727) B361727
theorem B178343 : Blo 175800 178343 := bstep (se 1 (by rfl) ⟨133757, by rfl⟩ : syracuseStep 178343 = 267515) B267515
theorem B454511 : Blo 175800 454511 := bstep (se 1 (by rfl) ⟨340883, by rfl⟩ : syracuseStep 454511 = 681767) B681767
theorem B303007 : Blo 175800 303007 := bstep (se 1 (by rfl) ⟨227255, by rfl⟩ : syracuseStep 303007 = 454511) B454511
theorem B241643 : Blo 175800 241643 := bstep (se 1 (by rfl) ⟨181232, by rfl⟩ : syracuseStep 241643 = 362465) B362465
theorem B176799 : Blo 175800 176799 := bstep (se 1 (by rfl) ⟨132599, by rfl⟩ : syracuseStep 176799 = 265199) B265199
theorem B179311 : Blo 175800 179311 := bstep (se 1 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 179311 = 268967) B268967
theorem B901853 : Blo 175800 901853 := bstep (se 3 (by rfl) ⟨169097, by rfl⟩ : syracuseStep 901853 = 338195) B338195
theorem B643069 : Blo 175800 643069 := bstep (se 3 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 643069 = 241151) B241151
theorem B36656975 : Blo 175800 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B857425 : Blo 175800 857425 := bstep (se 2 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 857425 = 643069) B643069
theorem B404009 : Blo 175800 404009 := bstep (se 2 (by rfl) ⟨151503, by rfl⟩ : syracuseStep 404009 = 303007) B303007
theorem B601235 : Blo 175800 601235 := bstep (se 1 (by rfl) ⟨450926, by rfl⟩ : syracuseStep 601235 = 901853) B901853
theorem B644381 : Blo 175800 644381 := bstep (se 3 (by rfl) ⟨120821, by rfl⟩ : syracuseStep 644381 = 241643) B241643
theorem B24437983 : Blo 175800 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B429587 : Blo 175800 429587 := bstep (se 1 (by rfl) ⟨322190, by rfl⟩ : syracuseStep 429587 = 644381) B644381
theorem B269339 : Blo 175800 269339 := bstep (se 1 (by rfl) ⟨202004, by rfl⟩ : syracuseStep 269339 = 404009) B404009
theorem B400823 : Blo 175800 400823 := bstep (se 1 (by rfl) ⟨300617, by rfl⟩ : syracuseStep 400823 = 601235) B601235
theorem B32583977 : Blo 175800 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B1143233 : Blo 175800 1143233 := bstep (se 2 (by rfl) ⟨428712, by rfl⟩ : syracuseStep 1143233 = 857425) B857425
theorem B267215 : Blo 175800 267215 := bstep (se 1 (by rfl) ⟨200411, by rfl⟩ : syracuseStep 267215 = 400823) B400823
theorem B762155 : Blo 175800 762155 := bstep (se 1 (by rfl) ⟨571616, by rfl⟩ : syracuseStep 762155 = 1143233) B1143233
theorem B179559 : Blo 175800 179559 := bstep (se 1 (by rfl) ⟨134669, by rfl⟩ : syracuseStep 179559 = 269339) B269339
theorem B286391 : Blo 175800 286391 := bstep (se 1 (by rfl) ⟨214793, by rfl⟩ : syracuseStep 286391 = 429587) B429587
theorem B21722651 : Blo 175800 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B178143 : Blo 175800 178143 := bstep (se 1 (by rfl) ⟨133607, by rfl⟩ : syracuseStep 178143 = 267215) B267215
theorem B508103 : Blo 175800 508103 := bstep (se 1 (by rfl) ⟨381077, by rfl⟩ : syracuseStep 508103 = 762155) B762155
theorem B190927 : Blo 175800 190927 := bstep (se 1 (by rfl) ⟨143195, by rfl⟩ : syracuseStep 190927 = 286391) B286391
theorem B14481767 : Blo 175800 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B1018277 : Blo 175800 1018277 := bstep (se 4 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 1018277 = 190927) B190927
theorem B338735 : Blo 175800 338735 := bstep (se 1 (by rfl) ⟨254051, by rfl⟩ : syracuseStep 338735 = 508103) B508103
theorem B9654511 : Blo 175800 9654511 := bstep (se 1 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 9654511 = 14481767) B14481767
theorem B678851 : Blo 175800 678851 := bstep (se 1 (by rfl) ⟨509138, by rfl⟩ : syracuseStep 678851 = 1018277) B1018277
theorem B12872681 : Blo 175800 12872681 := bstep (se 2 (by rfl) ⟨4827255, by rfl⟩ : syracuseStep 12872681 = 9654511) B9654511
theorem B225823 : Blo 175800 225823 := bstep (se 1 (by rfl) ⟨169367, by rfl⟩ : syracuseStep 225823 = 338735) B338735
theorem B301097 : Blo 175800 301097 := bstep (se 2 (by rfl) ⟨112911, by rfl⟩ : syracuseStep 301097 = 225823) B225823
theorem B452567 : Blo 175800 452567 := bstep (se 1 (by rfl) ⟨339425, by rfl⟩ : syracuseStep 452567 = 678851) B678851
theorem B8581787 : Blo 175800 8581787 := bstep (se 1 (by rfl) ⟨6436340, by rfl⟩ : syracuseStep 8581787 = 12872681) B12872681
theorem B200731 : Blo 175800 200731 := bstep (se 1 (by rfl) ⟨150548, by rfl⟩ : syracuseStep 200731 = 301097) B301097
theorem B301711 : Blo 175800 301711 := bstep (se 1 (by rfl) ⟨226283, by rfl⟩ : syracuseStep 301711 = 452567) B452567
theorem B5721191 : Blo 175800 5721191 := bstep (se 1 (by rfl) ⟨4290893, by rfl⟩ : syracuseStep 5721191 = 8581787) B8581787
theorem B267641 : Blo 175800 267641 := bstep (se 2 (by rfl) ⟨100365, by rfl⟩ : syracuseStep 267641 = 200731) B200731
theorem B402281 : Blo 175800 402281 := bstep (se 2 (by rfl) ⟨150855, by rfl⟩ : syracuseStep 402281 = 301711) B301711
theorem B3814127 : Blo 175800 3814127 := bstep (se 1 (by rfl) ⟨2860595, by rfl⟩ : syracuseStep 3814127 = 5721191) B5721191
theorem B268187 : Blo 175800 268187 := bstep (se 1 (by rfl) ⟨201140, by rfl⟩ : syracuseStep 268187 = 402281) B402281
theorem B178427 : Blo 175800 178427 := bstep (se 1 (by rfl) ⟨133820, by rfl⟩ : syracuseStep 178427 = 267641) B267641
theorem B2542751 : Blo 175800 2542751 := bstep (se 1 (by rfl) ⟨1907063, by rfl⟩ : syracuseStep 2542751 = 3814127) B3814127
theorem B178791 : Blo 175800 178791 := bstep (se 1 (by rfl) ⟨134093, by rfl⟩ : syracuseStep 178791 = 268187) B268187
theorem B1695167 : Blo 175800 1695167 := bstep (se 1 (by rfl) ⟨1271375, by rfl⟩ : syracuseStep 1695167 = 2542751) B2542751
theorem B1130111 : Blo 175800 1130111 := bstep (se 1 (by rfl) ⟨847583, by rfl⟩ : syracuseStep 1130111 = 1695167) B1695167
theorem B753407 : Blo 175800 753407 := bstep (se 1 (by rfl) ⟨565055, by rfl⟩ : syracuseStep 753407 = 1130111) B1130111
theorem B502271 : Blo 175800 502271 := bstep (se 1 (by rfl) ⟨376703, by rfl⟩ : syracuseStep 502271 = 753407) B753407
theorem B334847 : Blo 175800 334847 := bstep (se 1 (by rfl) ⟨251135, by rfl⟩ : syracuseStep 334847 = 502271) B502271
theorem B223231 : Blo 175800 223231 := bstep (se 1 (by rfl) ⟨167423, by rfl⟩ : syracuseStep 223231 = 334847) B334847
theorem B297641 : Blo 175800 297641 := bstep (se 2 (by rfl) ⟨111615, by rfl⟩ : syracuseStep 297641 = 223231) B223231
theorem B198427 : Blo 175800 198427 := bstep (se 1 (by rfl) ⟨148820, by rfl⟩ : syracuseStep 198427 = 297641) B297641
theorem B264569 : Blo 175800 264569 := bstep (se 2 (by rfl) ⟨99213, by rfl⟩ : syracuseStep 264569 = 198427) B198427
theorem B176379 : Blo 175800 176379 := bstep (se 1 (by rfl) ⟨132284, by rfl⟩ : syracuseStep 176379 = 264569) B264569

theorem C0 (j : ℕ) (h1 : 43950 ≤ j) (h2 : j ≤ 44649) : Blo 175800 (4 * j + 3) := by
  interval_cases j
  · exact B175803
  · exact B175807
  · exact B175811
  · exact B175815
  · exact B175819
  · exact B175823
  · exact B175827
  · exact B175831
  · exact B175835
  · exact B175839
  · exact B175843
  · exact B175847
  · exact B175851
  · exact B175855
  · exact B175859
  · exact B175863
  · exact B175867
  · exact B175871
  · exact B175875
  · exact B175879
  · exact B175883
  · exact B175887
  · exact B175891
  · exact B175895
  · exact B175899
  · exact B175903
  · exact B175907
  · exact B175911
  · exact B175915
  · exact B175919
  · exact B175923
  · exact B175927
  · exact B175931
  · exact B175935
  · exact B175939
  · exact B175943
  · exact B175947
  · exact B175951
  · exact B175955
  · exact B175959
  · exact B175963
  · exact B175967
  · exact B175971
  · exact B175975
  · exact B175979
  · exact B175983
  · exact B175987
  · exact B175991
  · exact B175995
  · exact B175999
  · exact B176003
  · exact B176007
  · exact B176011
  · exact B176015
  · exact B176019
  · exact B176023
  · exact B176027
  · exact B176031
  · exact B176035
  · exact B176039
  · exact B176043
  · exact B176047
  · exact B176051
  · exact B176055
  · exact B176059
  · exact B176063
  · exact B176067
  · exact B176071
  · exact B176075
  · exact B176079
  · exact B176083
  · exact B176087
  · exact B176091
  · exact B176095
  · exact B176099
  · exact B176103
  · exact B176107
  · exact B176111
  · exact B176115
  · exact B176119
  · exact B176123
  · exact B176127
  · exact B176131
  · exact B176135
  · exact B176139
  · exact B176143
  · exact B176147
  · exact B176151
  · exact B176155
  · exact B176159
  · exact B176163
  · exact B176167
  · exact B176171
  · exact B176175
  · exact B176179
  · exact B176183
  · exact B176187
  · exact B176191
  · exact B176195
  · exact B176199
  · exact B176203
  · exact B176207
  · exact B176211
  · exact B176215
  · exact B176219
  · exact B176223
  · exact B176227
  · exact B176231
  · exact B176235
  · exact B176239
  · exact B176243
  · exact B176247
  · exact B176251
  · exact B176255
  · exact B176259
  · exact B176263
  · exact B176267
  · exact B176271
  · exact B176275
  · exact B176279
  · exact B176283
  · exact B176287
  · exact B176291
  · exact B176295
  · exact B176299
  · exact B176303
  · exact B176307
  · exact B176311
  · exact B176315
  · exact B176319
  · exact B176323
  · exact B176327
  · exact B176331
  · exact B176335
  · exact B176339
  · exact B176343
  · exact B176347
  · exact B176351
  · exact B176355
  · exact B176359
  · exact B176363
  · exact B176367
  · exact B176371
  · exact B176375
  · exact B176379
  · exact B176383
  · exact B176387
  · exact B176391
  · exact B176395
  · exact B176399
  · exact B176403
  · exact B176407
  · exact B176411
  · exact B176415
  · exact B176419
  · exact B176423
  · exact B176427
  · exact B176431
  · exact B176435
  · exact B176439
  · exact B176443
  · exact B176447
  · exact B176451
  · exact B176455
  · exact B176459
  · exact B176463
  · exact B176467
  · exact B176471
  · exact B176475
  · exact B176479
  · exact B176483
  · exact B176487
  · exact B176491
  · exact B176495
  · exact B176499
  · exact B176503
  · exact B176507
  · exact B176511
  · exact B176515
  · exact B176519
  · exact B176523
  · exact B176527
  · exact B176531
  · exact B176535
  · exact B176539
  · exact B176543
  · exact B176547
  · exact B176551
  · exact B176555
  · exact B176559
  · exact B176563
  · exact B176567
  · exact B176571
  · exact B176575
  · exact B176579
  · exact B176583
  · exact B176587
  · exact B176591
  · exact B176595
  · exact B176599
  · exact B176603
  · exact B176607
  · exact B176611
  · exact B176615
  · exact B176619
  · exact B176623
  · exact B176627
  · exact B176631
  · exact B176635
  · exact B176639
  · exact B176643
  · exact B176647
  · exact B176651
  · exact B176655
  · exact B176659
  · exact B176663
  · exact B176667
  · exact B176671
  · exact B176675
  · exact B176679
  · exact B176683
  · exact B176687
  · exact B176691
  · exact B176695
  · exact B176699
  · exact B176703
  · exact B176707
  · exact B176711
  · exact B176715
  · exact B176719
  · exact B176723
  · exact B176727
  · exact B176731
  · exact B176735
  · exact B176739
  · exact B176743
  · exact B176747
  · exact B176751
  · exact B176755
  · exact B176759
  · exact B176763
  · exact B176767
  · exact B176771
  · exact B176775
  · exact B176779
  · exact B176783
  · exact B176787
  · exact B176791
  · exact B176795
  · exact B176799
  · exact B176803
  · exact B176807
  · exact B176811
  · exact B176815
  · exact B176819
  · exact B176823
  · exact B176827
  · exact B176831
  · exact B176835
  · exact B176839
  · exact B176843
  · exact B176847
  · exact B176851
  · exact B176855
  · exact B176859
  · exact B176863
  · exact B176867
  · exact B176871
  · exact B176875
  · exact B176879
  · exact B176883
  · exact B176887
  · exact B176891
  · exact B176895
  · exact B176899
  · exact B176903
  · exact B176907
  · exact B176911
  · exact B176915
  · exact B176919
  · exact B176923
  · exact B176927
  · exact B176931
  · exact B176935
  · exact B176939
  · exact B176943
  · exact B176947
  · exact B176951
  · exact B176955
  · exact B176959
  · exact B176963
  · exact B176967
  · exact B176971
  · exact B176975
  · exact B176979
  · exact B176983
  · exact B176987
  · exact B176991
  · exact B176995
  · exact B176999
  · exact B177003
  · exact B177007
  · exact B177011
  · exact B177015
  · exact B177019
  · exact B177023
  · exact B177027
  · exact B177031
  · exact B177035
  · exact B177039
  · exact B177043
  · exact B177047
  · exact B177051
  · exact B177055
  · exact B177059
  · exact B177063
  · exact B177067
  · exact B177071
  · exact B177075
  · exact B177079
  · exact B177083
  · exact B177087
  · exact B177091
  · exact B177095
  · exact B177099
  · exact B177103
  · exact B177107
  · exact B177111
  · exact B177115
  · exact B177119
  · exact B177123
  · exact B177127
  · exact B177131
  · exact B177135
  · exact B177139
  · exact B177143
  · exact B177147
  · exact B177151
  · exact B177155
  · exact B177159
  · exact B177163
  · exact B177167
  · exact B177171
  · exact B177175
  · exact B177179
  · exact B177183
  · exact B177187
  · exact B177191
  · exact B177195
  · exact B177199
  · exact B177203
  · exact B177207
  · exact B177211
  · exact B177215
  · exact B177219
  · exact B177223
  · exact B177227
  · exact B177231
  · exact B177235
  · exact B177239
  · exact B177243
  · exact B177247
  · exact B177251
  · exact B177255
  · exact B177259
  · exact B177263
  · exact B177267
  · exact B177271
  · exact B177275
  · exact B177279
  · exact B177283
  · exact B177287
  · exact B177291
  · exact B177295
  · exact B177299
  · exact B177303
  · exact B177307
  · exact B177311
  · exact B177315
  · exact B177319
  · exact B177323
  · exact B177327
  · exact B177331
  · exact B177335
  · exact B177339
  · exact B177343
  · exact B177347
  · exact B177351
  · exact B177355
  · exact B177359
  · exact B177363
  · exact B177367
  · exact B177371
  · exact B177375
  · exact B177379
  · exact B177383
  · exact B177387
  · exact B177391
  · exact B177395
  · exact B177399
  · exact B177403
  · exact B177407
  · exact B177411
  · exact B177415
  · exact B177419
  · exact B177423
  · exact B177427
  · exact B177431
  · exact B177435
  · exact B177439
  · exact B177443
  · exact B177447
  · exact B177451
  · exact B177455
  · exact B177459
  · exact B177463
  · exact B177467
  · exact B177471
  · exact B177475
  · exact B177479
  · exact B177483
  · exact B177487
  · exact B177491
  · exact B177495
  · exact B177499
  · exact B177503
  · exact B177507
  · exact B177511
  · exact B177515
  · exact B177519
  · exact B177523
  · exact B177527
  · exact B177531
  · exact B177535
  · exact B177539
  · exact B177543
  · exact B177547
  · exact B177551
  · exact B177555
  · exact B177559
  · exact B177563
  · exact B177567
  · exact B177571
  · exact B177575
  · exact B177579
  · exact B177583
  · exact B177587
  · exact B177591
  · exact B177595
  · exact B177599
  · exact B177603
  · exact B177607
  · exact B177611
  · exact B177615
  · exact B177619
  · exact B177623
  · exact B177627
  · exact B177631
  · exact B177635
  · exact B177639
  · exact B177643
  · exact B177647
  · exact B177651
  · exact B177655
  · exact B177659
  · exact B177663
  · exact B177667
  · exact B177671
  · exact B177675
  · exact B177679
  · exact B177683
  · exact B177687
  · exact B177691
  · exact B177695
  · exact B177699
  · exact B177703
  · exact B177707
  · exact B177711
  · exact B177715
  · exact B177719
  · exact B177723
  · exact B177727
  · exact B177731
  · exact B177735
  · exact B177739
  · exact B177743
  · exact B177747
  · exact B177751
  · exact B177755
  · exact B177759
  · exact B177763
  · exact B177767
  · exact B177771
  · exact B177775
  · exact B177779
  · exact B177783
  · exact B177787
  · exact B177791
  · exact B177795
  · exact B177799
  · exact B177803
  · exact B177807
  · exact B177811
  · exact B177815
  · exact B177819
  · exact B177823
  · exact B177827
  · exact B177831
  · exact B177835
  · exact B177839
  · exact B177843
  · exact B177847
  · exact B177851
  · exact B177855
  · exact B177859
  · exact B177863
  · exact B177867
  · exact B177871
  · exact B177875
  · exact B177879
  · exact B177883
  · exact B177887
  · exact B177891
  · exact B177895
  · exact B177899
  · exact B177903
  · exact B177907
  · exact B177911
  · exact B177915
  · exact B177919
  · exact B177923
  · exact B177927
  · exact B177931
  · exact B177935
  · exact B177939
  · exact B177943
  · exact B177947
  · exact B177951
  · exact B177955
  · exact B177959
  · exact B177963
  · exact B177967
  · exact B177971
  · exact B177975
  · exact B177979
  · exact B177983
  · exact B177987
  · exact B177991
  · exact B177995
  · exact B177999
  · exact B178003
  · exact B178007
  · exact B178011
  · exact B178015
  · exact B178019
  · exact B178023
  · exact B178027
  · exact B178031
  · exact B178035
  · exact B178039
  · exact B178043
  · exact B178047
  · exact B178051
  · exact B178055
  · exact B178059
  · exact B178063
  · exact B178067
  · exact B178071
  · exact B178075
  · exact B178079
  · exact B178083
  · exact B178087
  · exact B178091
  · exact B178095
  · exact B178099
  · exact B178103
  · exact B178107
  · exact B178111
  · exact B178115
  · exact B178119
  · exact B178123
  · exact B178127
  · exact B178131
  · exact B178135
  · exact B178139
  · exact B178143
  · exact B178147
  · exact B178151
  · exact B178155
  · exact B178159
  · exact B178163
  · exact B178167
  · exact B178171
  · exact B178175
  · exact B178179
  · exact B178183
  · exact B178187
  · exact B178191
  · exact B178195
  · exact B178199
  · exact B178203
  · exact B178207
  · exact B178211
  · exact B178215
  · exact B178219
  · exact B178223
  · exact B178227
  · exact B178231
  · exact B178235
  · exact B178239
  · exact B178243
  · exact B178247
  · exact B178251
  · exact B178255
  · exact B178259
  · exact B178263
  · exact B178267
  · exact B178271
  · exact B178275
  · exact B178279
  · exact B178283
  · exact B178287
  · exact B178291
  · exact B178295
  · exact B178299
  · exact B178303
  · exact B178307
  · exact B178311
  · exact B178315
  · exact B178319
  · exact B178323
  · exact B178327
  · exact B178331
  · exact B178335
  · exact B178339
  · exact B178343
  · exact B178347
  · exact B178351
  · exact B178355
  · exact B178359
  · exact B178363
  · exact B178367
  · exact B178371
  · exact B178375
  · exact B178379
  · exact B178383
  · exact B178387
  · exact B178391
  · exact B178395
  · exact B178399
  · exact B178403
  · exact B178407
  · exact B178411
  · exact B178415
  · exact B178419
  · exact B178423
  · exact B178427
  · exact B178431
  · exact B178435
  · exact B178439
  · exact B178443
  · exact B178447
  · exact B178451
  · exact B178455
  · exact B178459
  · exact B178463
  · exact B178467
  · exact B178471
  · exact B178475
  · exact B178479
  · exact B178483
  · exact B178487
  · exact B178491
  · exact B178495
  · exact B178499
  · exact B178503
  · exact B178507
  · exact B178511
  · exact B178515
  · exact B178519
  · exact B178523
  · exact B178527
  · exact B178531
  · exact B178535
  · exact B178539
  · exact B178543
  · exact B178547
  · exact B178551
  · exact B178555
  · exact B178559
  · exact B178563
  · exact B178567
  · exact B178571
  · exact B178575
  · exact B178579
  · exact B178583
  · exact B178587
  · exact B178591
  · exact B178595
  · exact B178599

theorem C1 (j : ℕ) (h1 : 44650 ≤ j) (h2 : j ≤ 44949) : Blo 175800 (4 * j + 3) := by
  interval_cases j
  · exact B178603
  · exact B178607
  · exact B178611
  · exact B178615
  · exact B178619
  · exact B178623
  · exact B178627
  · exact B178631
  · exact B178635
  · exact B178639
  · exact B178643
  · exact B178647
  · exact B178651
  · exact B178655
  · exact B178659
  · exact B178663
  · exact B178667
  · exact B178671
  · exact B178675
  · exact B178679
  · exact B178683
  · exact B178687
  · exact B178691
  · exact B178695
  · exact B178699
  · exact B178703
  · exact B178707
  · exact B178711
  · exact B178715
  · exact B178719
  · exact B178723
  · exact B178727
  · exact B178731
  · exact B178735
  · exact B178739
  · exact B178743
  · exact B178747
  · exact B178751
  · exact B178755
  · exact B178759
  · exact B178763
  · exact B178767
  · exact B178771
  · exact B178775
  · exact B178779
  · exact B178783
  · exact B178787
  · exact B178791
  · exact B178795
  · exact B178799
  · exact B178803
  · exact B178807
  · exact B178811
  · exact B178815
  · exact B178819
  · exact B178823
  · exact B178827
  · exact B178831
  · exact B178835
  · exact B178839
  · exact B178843
  · exact B178847
  · exact B178851
  · exact B178855
  · exact B178859
  · exact B178863
  · exact B178867
  · exact B178871
  · exact B178875
  · exact B178879
  · exact B178883
  · exact B178887
  · exact B178891
  · exact B178895
  · exact B178899
  · exact B178903
  · exact B178907
  · exact B178911
  · exact B178915
  · exact B178919
  · exact B178923
  · exact B178927
  · exact B178931
  · exact B178935
  · exact B178939
  · exact B178943
  · exact B178947
  · exact B178951
  · exact B178955
  · exact B178959
  · exact B178963
  · exact B178967
  · exact B178971
  · exact B178975
  · exact B178979
  · exact B178983
  · exact B178987
  · exact B178991
  · exact B178995
  · exact B178999
  · exact B179003
  · exact B179007
  · exact B179011
  · exact B179015
  · exact B179019
  · exact B179023
  · exact B179027
  · exact B179031
  · exact B179035
  · exact B179039
  · exact B179043
  · exact B179047
  · exact B179051
  · exact B179055
  · exact B179059
  · exact B179063
  · exact B179067
  · exact B179071
  · exact B179075
  · exact B179079
  · exact B179083
  · exact B179087
  · exact B179091
  · exact B179095
  · exact B179099
  · exact B179103
  · exact B179107
  · exact B179111
  · exact B179115
  · exact B179119
  · exact B179123
  · exact B179127
  · exact B179131
  · exact B179135
  · exact B179139
  · exact B179143
  · exact B179147
  · exact B179151
  · exact B179155
  · exact B179159
  · exact B179163
  · exact B179167
  · exact B179171
  · exact B179175
  · exact B179179
  · exact B179183
  · exact B179187
  · exact B179191
  · exact B179195
  · exact B179199
  · exact B179203
  · exact B179207
  · exact B179211
  · exact B179215
  · exact B179219
  · exact B179223
  · exact B179227
  · exact B179231
  · exact B179235
  · exact B179239
  · exact B179243
  · exact B179247
  · exact B179251
  · exact B179255
  · exact B179259
  · exact B179263
  · exact B179267
  · exact B179271
  · exact B179275
  · exact B179279
  · exact B179283
  · exact B179287
  · exact B179291
  · exact B179295
  · exact B179299
  · exact B179303
  · exact B179307
  · exact B179311
  · exact B179315
  · exact B179319
  · exact B179323
  · exact B179327
  · exact B179331
  · exact B179335
  · exact B179339
  · exact B179343
  · exact B179347
  · exact B179351
  · exact B179355
  · exact B179359
  · exact B179363
  · exact B179367
  · exact B179371
  · exact B179375
  · exact B179379
  · exact B179383
  · exact B179387
  · exact B179391
  · exact B179395
  · exact B179399
  · exact B179403
  · exact B179407
  · exact B179411
  · exact B179415
  · exact B179419
  · exact B179423
  · exact B179427
  · exact B179431
  · exact B179435
  · exact B179439
  · exact B179443
  · exact B179447
  · exact B179451
  · exact B179455
  · exact B179459
  · exact B179463
  · exact B179467
  · exact B179471
  · exact B179475
  · exact B179479
  · exact B179483
  · exact B179487
  · exact B179491
  · exact B179495
  · exact B179499
  · exact B179503
  · exact B179507
  · exact B179511
  · exact B179515
  · exact B179519
  · exact B179523
  · exact B179527
  · exact B179531
  · exact B179535
  · exact B179539
  · exact B179543
  · exact B179547
  · exact B179551
  · exact B179555
  · exact B179559
  · exact B179563
  · exact B179567
  · exact B179571
  · exact B179575
  · exact B179579
  · exact B179583
  · exact B179587
  · exact B179591
  · exact B179595
  · exact B179599
  · exact B179603
  · exact B179607
  · exact B179611
  · exact B179615
  · exact B179619
  · exact B179623
  · exact B179627
  · exact B179631
  · exact B179635
  · exact B179639
  · exact B179643
  · exact B179647
  · exact B179651
  · exact B179655
  · exact B179659
  · exact B179663
  · exact B179667
  · exact B179671
  · exact B179675
  · exact B179679
  · exact B179683
  · exact B179687
  · exact B179691
  · exact B179695
  · exact B179699
  · exact B179703
  · exact B179707
  · exact B179711
  · exact B179715
  · exact B179719
  · exact B179723
  · exact B179727
  · exact B179731
  · exact B179735
  · exact B179739
  · exact B179743
  · exact B179747
  · exact B179751
  · exact B179755
  · exact B179759
  · exact B179763
  · exact B179767
  · exact B179771
  · exact B179775
  · exact B179779
  · exact B179783
  · exact B179787
  · exact B179791
  · exact B179795
  · exact B179799

theorem solution (m : ℕ) (hlo : 175800 ≤ m) (hhi : m ≤ 179800) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 43950 ≤ j := by omega
    have hj2 : j ≤ 44949 := by omega
    have hb : Blo 175800 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 44650 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
