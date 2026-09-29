-- Prove2me | solution 1 for syracuse_descends_range_1603000_1605000
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:11:00.683443+00:00
-- url     : https://prove2.me/submissions/bd8801ce-cafd-433c-a322-7f364d970a06

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


theorem B13697045 : Blo 1603000 13697045 := bbase (se 6 (by rfl) ⟨321024, by rfl⟩ : syracuseStep 13697045 = 642049) (by norm_num)
theorem B5488661 : Blo 1603000 5488661 := bbase (se 6 (by rfl) ⟨128640, by rfl⟩ : syracuseStep 5488661 = 257281) (by norm_num)
theorem B5783573 : Blo 1603000 5783573 := bbase (se 6 (by rfl) ⟨135552, by rfl⟩ : syracuseStep 5783573 = 271105) (by norm_num)
theorem B12181589 : Blo 1603000 12181589 := bbase (se 8 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 12181589 = 142753) (by norm_num)
theorem B1712225 : Blo 1603000 1712225 := bbase (se 2 (by rfl) ⟨642084, by rfl⟩ : syracuseStep 1712225 = 1284169) (by norm_num)
theorem B4759717 : Blo 1603000 4759717 := bbase (se 4 (by rfl) ⟨446223, by rfl⟩ : syracuseStep 4759717 = 892447) (by norm_num)
theorem B1736893 : Blo 1603000 1736893 := bbase (se 3 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 1736893 = 651335) (by norm_num)
theorem B3424493 : Blo 1603000 3424493 := bbase (se 3 (by rfl) ⟨642092, by rfl⟩ : syracuseStep 3424493 = 1284185) (by norm_num)
theorem B5415173 : Blo 1603000 5415173 := bbase (se 4 (by rfl) ⟨507672, by rfl⟩ : syracuseStep 5415173 = 1015345) (by norm_num)
theorem B10281269 : Blo 1603000 10281269 := bbase (se 5 (by rfl) ⟨481934, by rfl⟩ : syracuseStep 10281269 = 963869) (by norm_num)
theorem B8118629 : Blo 1603000 8118629 := bbase (se 4 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 8118629 = 1522243) (by norm_num)
theorem B2892133 : Blo 1603000 2892133 := bbase (se 4 (by rfl) ⟨271137, by rfl⟩ : syracuseStep 2892133 = 542275) (by norm_num)
theorem B3424637 : Blo 1603000 3424637 := bbase (se 3 (by rfl) ⟨642119, by rfl⟩ : syracuseStep 3424637 = 1284239) (by norm_num)
theorem B2638253 : Blo 1603000 2638253 := bbase (se 3 (by rfl) ⟨494672, by rfl⟩ : syracuseStep 2638253 = 989345) (by norm_num)
theorem B2892205 : Blo 1603000 2892205 := bbase (se 3 (by rfl) ⟨542288, by rfl⟩ : syracuseStep 2892205 = 1084577) (by norm_num)
theorem B5136853 : Blo 1603000 5136853 := bbase (se 7 (by rfl) ⟨60197, by rfl⟩ : syracuseStep 5136853 = 120395) (by norm_num)
theorem B12173813 : Blo 1603000 12173813 := bbase (se 5 (by rfl) ⟨570647, by rfl⟩ : syracuseStep 12173813 = 1141295) (by norm_num)
theorem B1712669 : Blo 1603000 1712669 := bbase (se 3 (by rfl) ⟨321125, by rfl⟩ : syracuseStep 1712669 = 642251) (by norm_num)
theorem B5415605 : Blo 1603000 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B3424997 : Blo 1603000 3424997 := bbase (se 4 (by rfl) ⟨321093, by rfl⟩ : syracuseStep 3424997 = 642187) (by norm_num)
theorem B1925893 : Blo 1603000 1925893 := bbase (se 4 (by rfl) ⟨180552, by rfl⟩ : syracuseStep 1925893 = 361105) (by norm_num)
theorem B1712917 : Blo 1603000 1712917 := bbase (se 6 (by rfl) ⟨40146, by rfl⟩ : syracuseStep 1712917 = 80293) (by norm_num)
theorem B7709509 : Blo 1603000 7709509 := bbase (se 4 (by rfl) ⟨722766, by rfl⟩ : syracuseStep 7709509 = 1445533) (by norm_num)
theorem B5137253 : Blo 1603000 5137253 := bbase (se 4 (by rfl) ⟨481617, by rfl⟩ : syracuseStep 5137253 = 963235) (by norm_num)
theorem B1926109 : Blo 1603000 1926109 := bbase (se 3 (by rfl) ⟨361145, by rfl⟩ : syracuseStep 1926109 = 722291) (by norm_num)
theorem B4875317 : Blo 1603000 4875317 := bbase (se 5 (by rfl) ⟨228530, by rfl⟩ : syracuseStep 4875317 = 457061) (by norm_num)
theorem B3253325 : Blo 1603000 3253325 := bbase (se 3 (by rfl) ⟨609998, by rfl⟩ : syracuseStep 3253325 = 1219997) (by norm_num)
theorem B5416037 : Blo 1603000 5416037 := bbase (se 4 (by rfl) ⟨507753, by rfl⟩ : syracuseStep 5416037 = 1015507) (by norm_num)
theorem B1803397 : Blo 1603000 1803397 := bbase (se 4 (by rfl) ⟨169068, by rfl⟩ : syracuseStep 1803397 = 338137) (by norm_num)
theorem B4334741 : Blo 1603000 4334741 := bbase (se 6 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 4334741 = 203191) (by norm_num)
theorem B1803433 : Blo 1603000 1803433 := bbase (se 2 (by rfl) ⟨676287, by rfl⟩ : syracuseStep 1803433 = 1352575) (by norm_num)
theorem B7521461 : Blo 1603000 7521461 := bbase (se 5 (by rfl) ⟨352568, by rfl⟩ : syracuseStep 7521461 = 705137) (by norm_num)
theorem B1803469 : Blo 1603000 1803469 := bbase (se 3 (by rfl) ⟨338150, by rfl⟩ : syracuseStep 1803469 = 676301) (by norm_num)
theorem B1713361 : Blo 1603000 1713361 := bbase (se 2 (by rfl) ⟨642510, by rfl⟩ : syracuseStep 1713361 = 1285021) (by norm_num)
theorem B1803505 : Blo 1603000 1803505 := bbase (se 2 (by rfl) ⟨676314, by rfl⟩ : syracuseStep 1803505 = 1352629) (by norm_num)
theorem B1926397 : Blo 1603000 1926397 := bbase (se 3 (by rfl) ⟨361199, by rfl⟩ : syracuseStep 1926397 = 722399) (by norm_num)
theorem B1713421 : Blo 1603000 1713421 := bbase (se 3 (by rfl) ⟨321266, by rfl⟩ : syracuseStep 1713421 = 642533) (by norm_num)
theorem B1828117 : Blo 1603000 1828117 := bbase (se 6 (by rfl) ⟨42846, by rfl⟩ : syracuseStep 1828117 = 85693) (by norm_num)
theorem B1803541 : Blo 1603000 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B1803577 : Blo 1603000 1803577 := bbase (se 2 (by rfl) ⟨676341, by rfl⟩ : syracuseStep 1803577 = 1352683) (by norm_num)
theorem B1803613 : Blo 1603000 1803613 := bbase (se 3 (by rfl) ⟨338177, by rfl⟩ : syracuseStep 1803613 = 676355) (by norm_num)
theorem B1803649 : Blo 1603000 1803649 := bbase (se 2 (by rfl) ⟨676368, by rfl⟩ : syracuseStep 1803649 = 1352737) (by norm_num)
theorem B1803685 : Blo 1603000 1803685 := bbase (se 4 (by rfl) ⟨169095, by rfl⟩ : syracuseStep 1803685 = 338191) (by norm_num)
theorem B3851717 : Blo 1603000 3851717 := bbase (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) (by norm_num)
theorem B1803721 : Blo 1603000 1803721 := bbase (se 2 (by rfl) ⟨676395, by rfl⟩ : syracuseStep 1803721 = 1352791) (by norm_num)
theorem B1803757 : Blo 1603000 1803757 := bbase (se 3 (by rfl) ⟨338204, by rfl⟩ : syracuseStep 1803757 = 676409) (by norm_num)
theorem B1803793 : Blo 1603000 1803793 := bbase (se 2 (by rfl) ⟨676422, by rfl⟩ : syracuseStep 1803793 = 1352845) (by norm_num)
theorem B5416469 : Blo 1603000 5416469 := bbase (se 6 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 5416469 = 253897) (by norm_num)
theorem B6088229 : Blo 1603000 6088229 := bbase (se 4 (by rfl) ⟨570771, by rfl⟩ : syracuseStep 6088229 = 1141543) (by norm_num)
theorem B1803829 : Blo 1603000 1803829 := bbase (se 5 (by rfl) ⟨84554, by rfl⟩ : syracuseStep 1803829 = 169109) (by norm_num)
theorem B2639413 : Blo 1603000 2639413 := bbase (se 5 (by rfl) ⟨123722, by rfl⟩ : syracuseStep 2639413 = 247445) (by norm_num)
theorem B1713737 : Blo 1603000 1713737 := bbase (se 2 (by rfl) ⟨642651, by rfl⟩ : syracuseStep 1713737 = 1285303) (by norm_num)
theorem B1803865 : Blo 1603000 1803865 := bbase (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) (by norm_num)
theorem B3425885 : Blo 1603000 3425885 := bbase (se 3 (by rfl) ⟨642353, by rfl⟩ : syracuseStep 3425885 = 1284707) (by norm_num)
theorem B8119925 : Blo 1603000 8119925 := bbase (se 5 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 8119925 = 761243) (by norm_num)
theorem B1803901 : Blo 1603000 1803901 := bbase (se 3 (by rfl) ⟨338231, by rfl⟩ : syracuseStep 1803901 = 676463) (by norm_num)
theorem B1803937 : Blo 1603000 1803937 := bbase (se 2 (by rfl) ⟨676476, by rfl⟩ : syracuseStep 1803937 = 1352953) (by norm_num)
theorem B2705069 : Blo 1603000 2705069 := bbase (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) (by norm_num)
theorem B1803973 : Blo 1603000 1803973 := bbase (se 4 (by rfl) ⟨169122, by rfl⟩ : syracuseStep 1803973 = 338245) (by norm_num)
theorem B1804009 : Blo 1603000 1804009 := bbase (se 2 (by rfl) ⟨676503, by rfl⟩ : syracuseStep 1804009 = 1353007) (by norm_num)
theorem B1804045 : Blo 1603000 1804045 := bbase (se 3 (by rfl) ⟨338258, by rfl⟩ : syracuseStep 1804045 = 676517) (by norm_num)
theorem B1828645 : Blo 1603000 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B2705197 : Blo 1603000 2705197 := bbase (se 3 (by rfl) ⟨507224, by rfl⟩ : syracuseStep 2705197 = 1014449) (by norm_num)
theorem B1804081 : Blo 1603000 1804081 := bbase (se 2 (by rfl) ⟨676530, by rfl⟩ : syracuseStep 1804081 = 1353061) (by norm_num)
theorem B6088517 : Blo 1603000 6088517 := bbase (se 4 (by rfl) ⟨570798, by rfl⟩ : syracuseStep 6088517 = 1141597) (by norm_num)
theorem B1804117 : Blo 1603000 1804117 := bbase (se 9 (by rfl) ⟨5285, by rfl⟩ : syracuseStep 1804117 = 10571) (by norm_num)
theorem B3426133 : Blo 1603000 3426133 := bbase (se 9 (by rfl) ⟨10037, by rfl⟩ : syracuseStep 3426133 = 20075) (by norm_num)
theorem B9135989 : Blo 1603000 9135989 := bbase (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) (by norm_num)
theorem B1804153 : Blo 1603000 1804153 := bbase (se 2 (by rfl) ⟨676557, by rfl⟩ : syracuseStep 1804153 = 1353115) (by norm_num)
theorem B2705285 : Blo 1603000 2705285 := bbase (se 4 (by rfl) ⟨253620, by rfl⟩ : syracuseStep 2705285 = 507241) (by norm_num)
theorem B1828765 : Blo 1603000 1828765 := bbase (se 3 (by rfl) ⟨342893, by rfl⟩ : syracuseStep 1828765 = 685787) (by norm_num)
theorem B1804189 : Blo 1603000 1804189 := bbase (se 3 (by rfl) ⟨338285, by rfl⟩ : syracuseStep 1804189 = 676571) (by norm_num)
theorem B6588325 : Blo 1603000 6588325 := bbase (se 4 (by rfl) ⟨617655, by rfl⟩ : syracuseStep 6588325 = 1235311) (by norm_num)
theorem B1804225 : Blo 1603000 1804225 := bbase (se 2 (by rfl) ⟨676584, by rfl⟩ : syracuseStep 1804225 = 1353169) (by norm_num)
theorem B1804261 : Blo 1603000 1804261 := bbase (se 4 (by rfl) ⟨169149, by rfl⟩ : syracuseStep 1804261 = 338299) (by norm_num)
theorem B2705413 : Blo 1603000 2705413 := bbase (se 4 (by rfl) ⟨253632, by rfl⟩ : syracuseStep 2705413 = 507265) (by norm_num)
theorem B1804297 : Blo 1603000 1804297 := bbase (se 2 (by rfl) ⟨676611, by rfl⟩ : syracuseStep 1804297 = 1353223) (by norm_num)
theorem B1804333 : Blo 1603000 1804333 := bbase (se 3 (by rfl) ⟨338312, by rfl⟩ : syracuseStep 1804333 = 676625) (by norm_num)
theorem B1804369 : Blo 1603000 1804369 := bbase (se 2 (by rfl) ⟨676638, by rfl⟩ : syracuseStep 1804369 = 1353277) (by norm_num)
theorem B2705501 : Blo 1603000 2705501 := bbase (se 3 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 2705501 = 1014563) (by norm_num)
theorem B1804405 : Blo 1603000 1804405 := bbase (se 5 (by rfl) ⟨84581, by rfl⟩ : syracuseStep 1804405 = 169163) (by norm_num)
theorem B1804441 : Blo 1603000 1804441 := bbase (se 2 (by rfl) ⟨676665, by rfl⟩ : syracuseStep 1804441 = 1353331) (by norm_num)
theorem B1804477 : Blo 1603000 1804477 := bbase (se 3 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 1804477 = 676679) (by norm_num)
theorem B2705629 : Blo 1603000 2705629 := bbase (se 3 (by rfl) ⟨507305, by rfl⟩ : syracuseStep 2705629 = 1014611) (by norm_num)
theorem B1804513 : Blo 1603000 1804513 := bbase (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) (by norm_num)
theorem B1804549 : Blo 1603000 1804549 := bbase (se 4 (by rfl) ⟨169176, by rfl⟩ : syracuseStep 1804549 = 338353) (by norm_num)
theorem B3606821 : Blo 1603000 3606821 := bbase (se 4 (by rfl) ⟨338139, by rfl⟩ : syracuseStep 3606821 = 676279) (by norm_num)
theorem B1804585 : Blo 1603000 1804585 := bbase (se 2 (by rfl) ⟨676719, by rfl⟩ : syracuseStep 1804585 = 1353439) (by norm_num)
theorem B2705717 : Blo 1603000 2705717 := bbase (se 5 (by rfl) ⟨126830, by rfl⟩ : syracuseStep 2705717 = 253661) (by norm_num)
theorem B4565317 : Blo 1603000 4565317 := bbase (se 4 (by rfl) ⟨427998, by rfl⟩ : syracuseStep 4565317 = 855997) (by norm_num)
theorem B1804621 : Blo 1603000 1804621 := bbase (se 3 (by rfl) ⟨338366, by rfl⟩ : syracuseStep 1804621 = 676733) (by norm_num)
theorem B3426637 : Blo 1603000 3426637 := bbase (se 3 (by rfl) ⟨642494, by rfl⟩ : syracuseStep 3426637 = 1284989) (by norm_num)
theorem B3606893 : Blo 1603000 3606893 := bbase (se 3 (by rfl) ⟨676292, by rfl⟩ : syracuseStep 3606893 = 1352585) (by norm_num)
theorem B1804657 : Blo 1603000 1804657 := bbase (se 2 (by rfl) ⟨676746, by rfl⟩ : syracuseStep 1804657 = 1353493) (by norm_num)
theorem B1804693 : Blo 1603000 1804693 := bbase (se 6 (by rfl) ⟨42297, by rfl⟩ : syracuseStep 1804693 = 84595) (by norm_num)
theorem B3606965 : Blo 1603000 3606965 := bbase (se 5 (by rfl) ⟨169076, by rfl⟩ : syracuseStep 3606965 = 338153) (by norm_num)
theorem B2705845 : Blo 1603000 2705845 := bbase (se 5 (by rfl) ⟨126836, by rfl⟩ : syracuseStep 2705845 = 253673) (by norm_num)
theorem B1804729 : Blo 1603000 1804729 := bbase (se 2 (by rfl) ⟨676773, by rfl⟩ : syracuseStep 1804729 = 1353547) (by norm_num)
theorem B1804765 : Blo 1603000 1804765 := bbase (se 3 (by rfl) ⟨338393, by rfl⟩ : syracuseStep 1804765 = 676787) (by norm_num)
theorem B4565477 : Blo 1603000 4565477 := bbase (se 4 (by rfl) ⟨428013, by rfl⟩ : syracuseStep 4565477 = 856027) (by norm_num)
theorem B3607037 : Blo 1603000 3607037 := bbase (se 3 (by rfl) ⟨676319, by rfl⟩ : syracuseStep 3607037 = 1352639) (by norm_num)
theorem B1804801 : Blo 1603000 1804801 := bbase (se 2 (by rfl) ⟨676800, by rfl⟩ : syracuseStep 1804801 = 1353601) (by norm_num)
theorem B1927685 : Blo 1603000 1927685 := bbase (se 4 (by rfl) ⟨180720, by rfl⟩ : syracuseStep 1927685 = 361441) (by norm_num)
theorem B2705933 : Blo 1603000 2705933 := bbase (se 3 (by rfl) ⟨507362, by rfl⟩ : syracuseStep 2705933 = 1014725) (by norm_num)
theorem B1804837 : Blo 1603000 1804837 := bbase (se 4 (by rfl) ⟨169203, by rfl⟩ : syracuseStep 1804837 = 338407) (by norm_num)
theorem B3607109 : Blo 1603000 3607109 := bbase (se 4 (by rfl) ⟨338166, by rfl⟩ : syracuseStep 3607109 = 676333) (by norm_num)
theorem B1804873 : Blo 1603000 1804873 := bbase (se 2 (by rfl) ⟨676827, by rfl⟩ : syracuseStep 1804873 = 1353655) (by norm_num)
theorem B4115029 : Blo 1603000 4115029 := bbase (se 8 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 4115029 = 48223) (by norm_num)
theorem B4057685 : Blo 1603000 4057685 := bbase (se 8 (by rfl) ⟨23775, by rfl⟩ : syracuseStep 4057685 = 47551) (by norm_num)
theorem B1804909 : Blo 1603000 1804909 := bbase (se 3 (by rfl) ⟨338420, by rfl⟩ : syracuseStep 1804909 = 676841) (by norm_num)
theorem B5778037 : Blo 1603000 5778037 := bbase (se 5 (by rfl) ⟨270845, by rfl⟩ : syracuseStep 5778037 = 541691) (by norm_num)
theorem B3607181 : Blo 1603000 3607181 := bbase (se 3 (by rfl) ⟨676346, by rfl⟩ : syracuseStep 3607181 = 1352693) (by norm_num)
theorem B2706061 : Blo 1603000 2706061 := bbase (se 3 (by rfl) ⟨507386, by rfl⟩ : syracuseStep 2706061 = 1014773) (by norm_num)
theorem B1804945 : Blo 1603000 1804945 := bbase (se 2 (by rfl) ⟨676854, by rfl⟩ : syracuseStep 1804945 = 1353709) (by norm_num)
theorem B2058905 : Blo 1603000 2058905 := bbase (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) (by norm_num)
theorem B1804981 : Blo 1603000 1804981 := bbase (se 5 (by rfl) ⟨84608, by rfl⟩ : syracuseStep 1804981 = 169217) (by norm_num)
theorem B3607253 : Blo 1603000 3607253 := bbase (se 7 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 3607253 = 84545) (by norm_num)
theorem B4565717 : Blo 1603000 4565717 := bbase (se 7 (by rfl) ⟨53504, by rfl⟩ : syracuseStep 4565717 = 107009) (by norm_num)
theorem B1805017 : Blo 1603000 1805017 := bbase (se 2 (by rfl) ⟨676881, by rfl⟩ : syracuseStep 1805017 = 1353763) (by norm_num)
theorem B2706149 : Blo 1603000 2706149 := bbase (se 4 (by rfl) ⟨253701, by rfl⟩ : syracuseStep 2706149 = 507403) (by norm_num)
theorem B4336373 : Blo 1603000 4336373 := bbase (se 5 (by rfl) ⟨203267, by rfl⟩ : syracuseStep 4336373 = 406535) (by norm_num)
theorem B1805053 : Blo 1603000 1805053 := bbase (se 3 (by rfl) ⟨338447, by rfl⟩ : syracuseStep 1805053 = 676895) (by norm_num)
theorem B8227589 : Blo 1603000 8227589 := bbase (se 4 (by rfl) ⟨771336, by rfl⟩ : syracuseStep 8227589 = 1542673) (by norm_num)
theorem B4057877 : Blo 1603000 4057877 := bbase (se 6 (by rfl) ⟨95106, by rfl⟩ : syracuseStep 4057877 = 190213) (by norm_num)
theorem B10275605 : Blo 1603000 10275605 := bbase (se 6 (by rfl) ⟨240834, by rfl⟩ : syracuseStep 10275605 = 481669) (by norm_num)
theorem B3607325 : Blo 1603000 3607325 := bbase (se 3 (by rfl) ⟨676373, by rfl⟩ : syracuseStep 3607325 = 1352747) (by norm_num)
theorem B1805089 : Blo 1603000 1805089 := bbase (se 2 (by rfl) ⟨676908, by rfl⟩ : syracuseStep 1805089 = 1353817) (by norm_num)
theorem B1805125 : Blo 1603000 1805125 := bbase (se 4 (by rfl) ⟨169230, by rfl⟩ : syracuseStep 1805125 = 338461) (by norm_num)
theorem B3607397 : Blo 1603000 3607397 := bbase (se 4 (by rfl) ⟨338193, by rfl⟩ : syracuseStep 3607397 = 676387) (by norm_num)
theorem B2706277 : Blo 1603000 2706277 := bbase (se 4 (by rfl) ⟨253713, by rfl⟩ : syracuseStep 2706277 = 507427) (by norm_num)
theorem B1805161 : Blo 1603000 1805161 := bbase (se 2 (by rfl) ⟨676935, by rfl⟩ : syracuseStep 1805161 = 1353871) (by norm_num)
theorem B6851461 : Blo 1603000 6851461 := bbase (se 4 (by rfl) ⟨642324, by rfl⟩ : syracuseStep 6851461 = 1284649) (by norm_num)
theorem B8121221 : Blo 1603000 8121221 := bbase (se 4 (by rfl) ⟨761364, by rfl⟩ : syracuseStep 8121221 = 1522729) (by norm_num)
theorem B1805197 : Blo 1603000 1805197 := bbase (se 3 (by rfl) ⟨338474, by rfl⟩ : syracuseStep 1805197 = 676949) (by norm_num)
theorem B4565909 : Blo 1603000 4565909 := bbase (se 6 (by rfl) ⟨107013, by rfl⟩ : syracuseStep 4565909 = 214027) (by norm_num)
theorem B3607469 : Blo 1603000 3607469 := bbase (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) (by norm_num)
theorem B1805233 : Blo 1603000 1805233 := bbase (se 2 (by rfl) ⟨676962, by rfl⟩ : syracuseStep 1805233 = 1353925) (by norm_num)
theorem B2706365 : Blo 1603000 2706365 := bbase (se 3 (by rfl) ⟨507443, by rfl⟩ : syracuseStep 2706365 = 1014887) (by norm_num)
theorem B1805269 : Blo 1603000 1805269 := bbase (se 7 (by rfl) ⟨21155, by rfl⟩ : syracuseStep 1805269 = 42311) (by norm_num)
theorem B6089701 : Blo 1603000 6089701 := bbase (se 4 (by rfl) ⟨570909, by rfl⟩ : syracuseStep 6089701 = 1141819) (by norm_num)
theorem B3607541 : Blo 1603000 3607541 := bbase (se 5 (by rfl) ⟨169103, by rfl⟩ : syracuseStep 3607541 = 338207) (by norm_num)
theorem B1805305 : Blo 1603000 1805305 := bbase (se 2 (by rfl) ⟨676989, by rfl⟩ : syracuseStep 1805305 = 1353979) (by norm_num)
theorem B1805341 : Blo 1603000 1805341 := bbase (se 3 (by rfl) ⟨338501, by rfl⟩ : syracuseStep 1805341 = 677003) (by norm_num)
theorem B1829941 : Blo 1603000 1829941 := bbase (se 5 (by rfl) ⟨85778, by rfl⟩ : syracuseStep 1829941 = 171557) (by norm_num)
theorem B3607613 : Blo 1603000 3607613 := bbase (se 3 (by rfl) ⟨676427, by rfl⟩ : syracuseStep 3607613 = 1352855) (by norm_num)
theorem B2706493 : Blo 1603000 2706493 := bbase (se 3 (by rfl) ⟨507467, by rfl⟩ : syracuseStep 2706493 = 1014935) (by norm_num)
theorem B1805377 : Blo 1603000 1805377 := bbase (se 2 (by rfl) ⟨677016, by rfl⟩ : syracuseStep 1805377 = 1354033) (by norm_num)
theorem B1805413 : Blo 1603000 1805413 := bbase (se 4 (by rfl) ⟨169257, by rfl⟩ : syracuseStep 1805413 = 338515) (by norm_num)
theorem B4058221 : Blo 1603000 4058221 := bbase (se 3 (by rfl) ⟨760916, by rfl⟩ : syracuseStep 4058221 = 1521833) (by norm_num)
theorem B3607685 : Blo 1603000 3607685 := bbase (se 4 (by rfl) ⟨338220, by rfl⟩ : syracuseStep 3607685 = 676441) (by norm_num)
theorem B1805449 : Blo 1603000 1805449 := bbase (se 2 (by rfl) ⟨677043, by rfl⟩ : syracuseStep 1805449 = 1354087) (by norm_num)
theorem B2706581 : Blo 1603000 2706581 := bbase (se 6 (by rfl) ⟨63435, by rfl⟩ : syracuseStep 2706581 = 126871) (by norm_num)
theorem B1805485 : Blo 1603000 1805485 := bbase (se 3 (by rfl) ⟨338528, by rfl⟩ : syracuseStep 1805485 = 677057) (by norm_num)
theorem B3427525 : Blo 1603000 3427525 := bbase (se 4 (by rfl) ⟨321330, by rfl⟩ : syracuseStep 3427525 = 642661) (by norm_num)
theorem B3607757 : Blo 1603000 3607757 := bbase (se 3 (by rfl) ⟨676454, by rfl⟩ : syracuseStep 3607757 = 1352909) (by norm_num)
theorem B1805521 : Blo 1603000 1805521 := bbase (se 2 (by rfl) ⟨677070, by rfl⟩ : syracuseStep 1805521 = 1354141) (by norm_num)
theorem B4058333 : Blo 1603000 4058333 := bbase (se 3 (by rfl) ⟨760937, by rfl⟩ : syracuseStep 4058333 = 1521875) (by norm_num)
theorem B1805557 : Blo 1603000 1805557 := bbase (se 5 (by rfl) ⟨84635, by rfl⟩ : syracuseStep 1805557 = 169271) (by norm_num)
theorem B3607829 : Blo 1603000 3607829 := bbase (se 6 (by rfl) ⟨84558, by rfl⟩ : syracuseStep 3607829 = 169117) (by norm_num)
theorem B6090005 : Blo 1603000 6090005 := bbase (se 6 (by rfl) ⟨142734, by rfl⟩ : syracuseStep 6090005 = 285469) (by norm_num)
theorem B2706709 : Blo 1603000 2706709 := bbase (se 6 (by rfl) ⟨63438, by rfl⟩ : syracuseStep 2706709 = 126877) (by norm_num)
theorem B1805593 : Blo 1603000 1805593 := bbase (se 2 (by rfl) ⟨677097, by rfl⟩ : syracuseStep 1805593 = 1354195) (by norm_num)
theorem B3607901 : Blo 1603000 3607901 := bbase (se 3 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 3607901 = 1352963) (by norm_num)
theorem B2706797 : Blo 1603000 2706797 := bbase (se 3 (by rfl) ⟨507524, by rfl⟩ : syracuseStep 2706797 = 1015049) (by norm_num)
theorem B4058525 : Blo 1603000 4058525 := bbase (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) (by norm_num)
theorem B3607973 : Blo 1603000 3607973 := bbase (se 4 (by rfl) ⟨338247, by rfl⟩ : syracuseStep 3607973 = 676495) (by norm_num)
theorem B4115893 : Blo 1603000 4115893 := bbase (se 5 (by rfl) ⟨192932, by rfl⟩ : syracuseStep 4115893 = 385865) (by norm_num)
theorem B3608045 : Blo 1603000 3608045 := bbase (se 3 (by rfl) ⟨676508, by rfl⟩ : syracuseStep 3608045 = 1353017) (by norm_num)
theorem B2706925 : Blo 1603000 2706925 := bbase (se 3 (by rfl) ⟨507548, by rfl⟩ : syracuseStep 2706925 = 1015097) (by norm_num)
theorem B3853813 : Blo 1603000 3853813 := bbase (se 5 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 3853813 = 361295) (by norm_num)
theorem B2780669 : Blo 1603000 2780669 := bbase (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) (by norm_num)
theorem B3608117 : Blo 1603000 3608117 := bbase (se 5 (by rfl) ⟨169130, by rfl⟩ : syracuseStep 3608117 = 338261) (by norm_num)
theorem B2707013 : Blo 1603000 2707013 := bbase (se 4 (by rfl) ⟨253782, by rfl⟩ : syracuseStep 2707013 = 507565) (by norm_num)
theorem B5410421 : Blo 1603000 5410421 := bbase (se 5 (by rfl) ⟨253613, by rfl⟩ : syracuseStep 5410421 = 507227) (by norm_num)
theorem B3608189 : Blo 1603000 3608189 := bbase (se 3 (by rfl) ⟨676535, by rfl⟩ : syracuseStep 3608189 = 1353071) (by norm_num)
theorem B3608261 : Blo 1603000 3608261 := bbase (se 4 (by rfl) ⟨338274, by rfl⟩ : syracuseStep 3608261 = 676549) (by norm_num)
theorem B2707141 : Blo 1603000 2707141 := bbase (se 4 (by rfl) ⟨253794, by rfl⟩ : syracuseStep 2707141 = 507589) (by norm_num)
theorem B24678101 : Blo 1603000 24678101 := bbase (se 7 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 24678101 = 578393) (by norm_num)
theorem B4058869 : Blo 1603000 4058869 := bbase (se 5 (by rfl) ⟨190259, by rfl⟩ : syracuseStep 4058869 = 380519) (by norm_num)
theorem B3608333 : Blo 1603000 3608333 := bbase (se 3 (by rfl) ⟨676562, by rfl⟩ : syracuseStep 3608333 = 1353125) (by norm_num)
theorem B1625881 : Blo 1603000 1625881 := bbase (se 2 (by rfl) ⟨609705, by rfl⟩ : syracuseStep 1625881 = 1219411) (by norm_num)
theorem B2707229 : Blo 1603000 2707229 := bbase (se 3 (by rfl) ⟨507605, by rfl⟩ : syracuseStep 2707229 = 1015211) (by norm_num)
theorem B3608405 : Blo 1603000 3608405 := bbase (se 9 (by rfl) ⟨10571, by rfl⟩ : syracuseStep 3608405 = 21143) (by norm_num)
theorem B4058981 : Blo 1603000 4058981 := bbase (se 4 (by rfl) ⟨380529, by rfl⟩ : syracuseStep 4058981 = 761059) (by norm_num)
theorem B4337509 : Blo 1603000 4337509 := bbase (se 4 (by rfl) ⟨406641, by rfl⟩ : syracuseStep 4337509 = 813283) (by norm_num)
theorem B4566901 : Blo 1603000 4566901 := bbase (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) (by norm_num)
theorem B3608477 : Blo 1603000 3608477 := bbase (se 3 (by rfl) ⟨676589, by rfl⟩ : syracuseStep 3608477 = 1353179) (by norm_num)
theorem B2707357 : Blo 1603000 2707357 := bbase (se 3 (by rfl) ⟨507629, by rfl⟩ : syracuseStep 2707357 = 1015259) (by norm_num)
theorem B3608549 : Blo 1603000 3608549 := bbase (se 4 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 3608549 = 676603) (by norm_num)
theorem B2707445 : Blo 1603000 2707445 := bbase (se 5 (by rfl) ⟨126911, by rfl⟩ : syracuseStep 2707445 = 253823) (by norm_num)
theorem B3043325 : Blo 1603000 3043325 := bbase (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) (by norm_num)
theorem B9138197 : Blo 1603000 9138197 := bbase (se 6 (by rfl) ⟨214176, by rfl⟩ : syracuseStep 9138197 = 428353) (by norm_num)
theorem B5410853 : Blo 1603000 5410853 := bbase (se 4 (by rfl) ⟨507267, by rfl⟩ : syracuseStep 5410853 = 1014535) (by norm_num)
theorem B4059173 : Blo 1603000 4059173 := bbase (se 4 (by rfl) ⟨380547, by rfl⟩ : syracuseStep 4059173 = 761095) (by norm_num)
theorem B3608621 : Blo 1603000 3608621 := bbase (se 3 (by rfl) ⟨676616, by rfl⟩ : syracuseStep 3608621 = 1353233) (by norm_num)
theorem B1626193 : Blo 1603000 1626193 := bbase (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) (by norm_num)
theorem B3854429 : Blo 1603000 3854429 := bbase (se 3 (by rfl) ⟨722705, by rfl⟩ : syracuseStep 3854429 = 1445411) (by norm_num)
theorem B3608693 : Blo 1603000 3608693 := bbase (se 5 (by rfl) ⟨169157, by rfl⟩ : syracuseStep 3608693 = 338315) (by norm_num)
theorem B2707573 : Blo 1603000 2707573 := bbase (se 5 (by rfl) ⟨126917, by rfl⟩ : syracuseStep 2707573 = 253835) (by norm_num)
theorem B1626241 : Blo 1603000 1626241 := bbase (se 2 (by rfl) ⟨609840, by rfl⟩ : syracuseStep 1626241 = 1219681) (by norm_num)
theorem B3043469 : Blo 1603000 3043469 := bbase (se 3 (by rfl) ⟨570650, by rfl⟩ : syracuseStep 3043469 = 1141301) (by norm_num)
theorem B3854485 : Blo 1603000 3854485 := bbase (se 6 (by rfl) ⟨90339, by rfl⟩ : syracuseStep 3854485 = 180679) (by norm_num)
theorem B8122517 : Blo 1603000 8122517 := bbase (se 6 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 8122517 = 380743) (by norm_num)
theorem B2404517 : Blo 1603000 2404517 := bbase (se 4 (by rfl) ⟨225423, by rfl⟩ : syracuseStep 2404517 = 450847) (by norm_num)
theorem B2404541 : Blo 1603000 2404541 := bbase (se 3 (by rfl) ⟨450851, by rfl⟩ : syracuseStep 2404541 = 901703) (by norm_num)
theorem B3608765 : Blo 1603000 3608765 := bbase (se 3 (by rfl) ⟨676643, by rfl⟩ : syracuseStep 3608765 = 1353287) (by norm_num)
theorem B2707661 : Blo 1603000 2707661 := bbase (se 3 (by rfl) ⟨507686, by rfl⟩ : syracuseStep 2707661 = 1015373) (by norm_num)
theorem B2404565 : Blo 1603000 2404565 := bbase (se 7 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 2404565 = 56357) (by norm_num)
theorem B2404589 : Blo 1603000 2404589 := bbase (se 3 (by rfl) ⟨450860, by rfl⟩ : syracuseStep 2404589 = 901721) (by norm_num)
theorem B2404613 : Blo 1603000 2404613 := bbase (se 4 (by rfl) ⟨225432, by rfl⟩ : syracuseStep 2404613 = 450865) (by norm_num)
theorem B3608837 : Blo 1603000 3608837 := bbase (se 4 (by rfl) ⟨338328, by rfl⟩ : syracuseStep 3608837 = 676657) (by norm_num)
theorem B12521749 : Blo 1603000 12521749 := bbase (se 6 (by rfl) ⟨293478, by rfl⟩ : syracuseStep 12521749 = 586957) (by norm_num)
theorem B2404637 : Blo 1603000 2404637 := bbase (se 3 (by rfl) ⟨450869, by rfl⟩ : syracuseStep 2404637 = 901739) (by norm_num)
theorem B2404661 : Blo 1603000 2404661 := bbase (se 5 (by rfl) ⟨112718, by rfl⟩ : syracuseStep 2404661 = 225437) (by norm_num)
theorem B2404685 : Blo 1603000 2404685 := bbase (se 3 (by rfl) ⟨450878, by rfl⟩ : syracuseStep 2404685 = 901757) (by norm_num)
theorem B3608909 : Blo 1603000 3608909 := bbase (se 3 (by rfl) ⟨676670, by rfl⟩ : syracuseStep 3608909 = 1353341) (by norm_num)
theorem B2707789 : Blo 1603000 2707789 := bbase (se 3 (by rfl) ⟨507710, by rfl⟩ : syracuseStep 2707789 = 1015421) (by norm_num)
theorem B21123413 : Blo 1603000 21123413 := bbase (se 10 (by rfl) ⟨30942, by rfl⟩ : syracuseStep 21123413 = 61885) (by norm_num)
theorem B2404709 : Blo 1603000 2404709 := bbase (se 4 (by rfl) ⟨225441, by rfl⟩ : syracuseStep 2404709 = 450883) (by norm_num)
theorem B2404733 : Blo 1603000 2404733 := bbase (se 3 (by rfl) ⟨450887, by rfl⟩ : syracuseStep 2404733 = 901775) (by norm_num)
theorem B2167165 : Blo 1603000 2167165 := bbase (se 3 (by rfl) ⟨406343, by rfl⟩ : syracuseStep 2167165 = 812687) (by norm_num)
theorem B4059517 : Blo 1603000 4059517 := bbase (se 3 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 4059517 = 1522319) (by norm_num)
theorem B2568581 : Blo 1603000 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B2404757 : Blo 1603000 2404757 := bbase (se 6 (by rfl) ⟨56361, by rfl⟩ : syracuseStep 2404757 = 112723) (by norm_num)
theorem B3608981 : Blo 1603000 3608981 := bbase (se 6 (by rfl) ⟨84585, by rfl⟩ : syracuseStep 3608981 = 169171) (by norm_num)
theorem B2707877 : Blo 1603000 2707877 := bbase (se 4 (by rfl) ⟨253863, by rfl⟩ : syracuseStep 2707877 = 507727) (by norm_num)
theorem B2404781 : Blo 1603000 2404781 := bbase (se 3 (by rfl) ⟨450896, by rfl⟩ : syracuseStep 2404781 = 901793) (by norm_num)
theorem B3043757 : Blo 1603000 3043757 := bbase (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) (by norm_num)
theorem B2404805 : Blo 1603000 2404805 := bbase (se 4 (by rfl) ⟨225450, by rfl⟩ : syracuseStep 2404805 = 450901) (by norm_num)
theorem B5411285 : Blo 1603000 5411285 := bbase (se 7 (by rfl) ⟨63413, by rfl⟩ : syracuseStep 5411285 = 126827) (by norm_num)
theorem B2404829 : Blo 1603000 2404829 := bbase (se 3 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 2404829 = 901811) (by norm_num)
theorem B3609053 : Blo 1603000 3609053 := bbase (se 3 (by rfl) ⟨676697, by rfl⟩ : syracuseStep 3609053 = 1353395) (by norm_num)
theorem B2568677 : Blo 1603000 2568677 := bbase (se 4 (by rfl) ⟨240813, by rfl⟩ : syracuseStep 2568677 = 481627) (by norm_num)
theorem B4059629 : Blo 1603000 4059629 := bbase (se 3 (by rfl) ⟨761180, by rfl⟩ : syracuseStep 4059629 = 1522361) (by norm_num)
theorem B2404853 : Blo 1603000 2404853 := bbase (se 5 (by rfl) ⟨112727, by rfl⟩ : syracuseStep 2404853 = 225455) (by norm_num)
theorem B2568709 : Blo 1603000 2568709 := bbase (se 4 (by rfl) ⟨240816, by rfl⟩ : syracuseStep 2568709 = 481633) (by norm_num)
theorem B2404877 : Blo 1603000 2404877 := bbase (se 3 (by rfl) ⟨450914, by rfl⟩ : syracuseStep 2404877 = 901829) (by norm_num)
theorem B2404901 : Blo 1603000 2404901 := bbase (se 4 (by rfl) ⟨225459, by rfl⟩ : syracuseStep 2404901 = 450919) (by norm_num)
theorem B3609125 : Blo 1603000 3609125 := bbase (se 4 (by rfl) ⟨338355, by rfl⟩ : syracuseStep 3609125 = 676711) (by norm_num)
theorem B2708005 : Blo 1603000 2708005 := bbase (se 4 (by rfl) ⟨253875, by rfl⟩ : syracuseStep 2708005 = 507751) (by norm_num)
theorem B5141045 : Blo 1603000 5141045 := bbase (se 5 (by rfl) ⟨240986, by rfl⟩ : syracuseStep 5141045 = 481973) (by norm_num)
theorem B2404925 : Blo 1603000 2404925 := bbase (se 3 (by rfl) ⟨450923, by rfl⟩ : syracuseStep 2404925 = 901847) (by norm_num)
theorem B3043909 : Blo 1603000 3043909 := bbase (se 4 (by rfl) ⟨285366, by rfl⟩ : syracuseStep 3043909 = 570733) (by norm_num)
theorem B2404949 : Blo 1603000 2404949 := bbase (se 8 (by rfl) ⟨14091, by rfl⟩ : syracuseStep 2404949 = 28183) (by norm_num)
theorem B2404973 : Blo 1603000 2404973 := bbase (se 3 (by rfl) ⟨450932, by rfl⟩ : syracuseStep 2404973 = 901865) (by norm_num)
theorem B3609197 : Blo 1603000 3609197 := bbase (se 3 (by rfl) ⟨676724, by rfl⟩ : syracuseStep 3609197 = 1353449) (by norm_num)
theorem B7705205 : Blo 1603000 7705205 := bbase (se 5 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 7705205 = 722363) (by norm_num)
theorem B2708093 : Blo 1603000 2708093 := bbase (se 3 (by rfl) ⟨507767, by rfl⟩ : syracuseStep 2708093 = 1015535) (by norm_num)
theorem B2404997 : Blo 1603000 2404997 := bbase (se 4 (by rfl) ⟨225468, by rfl⟩ : syracuseStep 2404997 = 450937) (by norm_num)
theorem B2405021 : Blo 1603000 2405021 := bbase (se 3 (by rfl) ⟨450941, by rfl⟩ : syracuseStep 2405021 = 901883) (by norm_num)
theorem B4059821 : Blo 1603000 4059821 := bbase (se 3 (by rfl) ⟨761216, by rfl⟩ : syracuseStep 4059821 = 1522433) (by norm_num)
theorem B2405045 : Blo 1603000 2405045 := bbase (se 5 (by rfl) ⟨112736, by rfl⟩ : syracuseStep 2405045 = 225473) (by norm_num)
theorem B3609269 : Blo 1603000 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B1626809 : Blo 1603000 1626809 := bbase (se 2 (by rfl) ⟨610053, by rfl⟩ : syracuseStep 1626809 = 1220107) (by norm_num)
theorem B4338373 : Blo 1603000 4338373 := bbase (se 4 (by rfl) ⟨406722, by rfl⟩ : syracuseStep 4338373 = 813445) (by norm_num)
theorem B2405069 : Blo 1603000 2405069 := bbase (se 3 (by rfl) ⟨450950, by rfl⟩ : syracuseStep 2405069 = 901901) (by norm_num)
theorem B2405093 : Blo 1603000 2405093 := bbase (se 4 (by rfl) ⟨225477, by rfl⟩ : syracuseStep 2405093 = 450955) (by norm_num)
theorem B2405117 : Blo 1603000 2405117 := bbase (se 3 (by rfl) ⟨450959, by rfl⟩ : syracuseStep 2405117 = 901919) (by norm_num)
theorem B3609341 : Blo 1603000 3609341 := bbase (se 3 (by rfl) ⟨676751, by rfl⟩ : syracuseStep 3609341 = 1353503) (by norm_num)
theorem B2708221 : Blo 1603000 2708221 := bbase (se 3 (by rfl) ⟨507791, by rfl⟩ : syracuseStep 2708221 = 1015583) (by norm_num)
theorem B2167565 : Blo 1603000 2167565 := bbase (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) (by norm_num)
theorem B2405141 : Blo 1603000 2405141 := bbase (se 6 (by rfl) ⟨56370, by rfl⟩ : syracuseStep 2405141 = 112741) (by norm_num)
theorem B2405165 : Blo 1603000 2405165 := bbase (se 3 (by rfl) ⟨450968, by rfl⟩ : syracuseStep 2405165 = 901937) (by norm_num)
theorem B2405189 : Blo 1603000 2405189 := bbase (se 4 (by rfl) ⟨225486, by rfl⟩ : syracuseStep 2405189 = 450973) (by norm_num)
theorem B3609413 : Blo 1603000 3609413 := bbase (se 4 (by rfl) ⟨338382, by rfl⟩ : syracuseStep 3609413 = 676765) (by norm_num)
theorem B2708309 : Blo 1603000 2708309 := bbase (se 9 (by rfl) ⟨7934, by rfl⟩ : syracuseStep 2708309 = 15869) (by norm_num)
theorem B2405213 : Blo 1603000 2405213 := bbase (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) (by norm_num)
theorem B2405237 : Blo 1603000 2405237 := bbase (se 5 (by rfl) ⟨112745, by rfl⟩ : syracuseStep 2405237 = 225491) (by norm_num)
theorem B3044213 : Blo 1603000 3044213 := bbase (se 5 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 3044213 = 285395) (by norm_num)
theorem B5411717 : Blo 1603000 5411717 := bbase (se 4 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 5411717 = 1014697) (by norm_num)
theorem B2405261 : Blo 1603000 2405261 := bbase (se 3 (by rfl) ⟨450986, by rfl⟩ : syracuseStep 2405261 = 901973) (by norm_num)
theorem B3609485 : Blo 1603000 3609485 := bbase (se 3 (by rfl) ⟨676778, by rfl⟩ : syracuseStep 3609485 = 1353557) (by norm_num)
theorem B2405285 : Blo 1603000 2405285 := bbase (se 4 (by rfl) ⟨225495, by rfl⟩ : syracuseStep 2405285 = 450991) (by norm_num)
theorem B2257837 : Blo 1603000 2257837 := bbase (se 3 (by rfl) ⟨423344, by rfl⟩ : syracuseStep 2257837 = 846689) (by norm_num)
theorem B2405309 : Blo 1603000 2405309 := bbase (se 3 (by rfl) ⟨450995, by rfl⟩ : syracuseStep 2405309 = 901991) (by norm_num)
theorem B4568005 : Blo 1603000 4568005 := bbase (se 4 (by rfl) ⟨428250, by rfl⟩ : syracuseStep 4568005 = 856501) (by norm_num)
theorem B2405333 : Blo 1603000 2405333 := bbase (se 7 (by rfl) ⟨28187, by rfl⟩ : syracuseStep 2405333 = 56375) (by norm_num)
theorem B3609557 : Blo 1603000 3609557 := bbase (se 7 (by rfl) ⟨42299, by rfl⟩ : syracuseStep 3609557 = 84599) (by norm_num)
theorem B2708437 : Blo 1603000 2708437 := bbase (se 7 (by rfl) ⟨31739, by rfl⟩ : syracuseStep 2708437 = 63479) (by norm_num)
theorem B2405357 : Blo 1603000 2405357 := bbase (se 3 (by rfl) ⟨451004, by rfl⟩ : syracuseStep 2405357 = 902009) (by norm_num)
theorem B3085301 : Blo 1603000 3085301 := bbase (se 5 (by rfl) ⟨144623, by rfl⟩ : syracuseStep 3085301 = 289247) (by norm_num)
theorem B2405381 : Blo 1603000 2405381 := bbase (se 4 (by rfl) ⟨225504, by rfl⟩ : syracuseStep 2405381 = 451009) (by norm_num)
theorem B4060165 : Blo 1603000 4060165 := bbase (se 4 (by rfl) ⟨380640, by rfl⟩ : syracuseStep 4060165 = 761281) (by norm_num)
theorem B2405405 : Blo 1603000 2405405 := bbase (se 3 (by rfl) ⟨451013, by rfl⟩ : syracuseStep 2405405 = 902027) (by norm_num)
theorem B3609629 : Blo 1603000 3609629 := bbase (se 3 (by rfl) ⟨676805, by rfl⟩ : syracuseStep 3609629 = 1353611) (by norm_num)
theorem B2405429 : Blo 1603000 2405429 := bbase (se 5 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 2405429 = 225509) (by norm_num)
theorem B10417205 : Blo 1603000 10417205 := bbase (se 5 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 10417205 = 976613) (by norm_num)
theorem B2405453 : Blo 1603000 2405453 := bbase (se 3 (by rfl) ⟨451022, by rfl⟩ : syracuseStep 2405453 = 902045) (by norm_num)
theorem B2405477 : Blo 1603000 2405477 := bbase (se 4 (by rfl) ⟨225513, by rfl⟩ : syracuseStep 2405477 = 451027) (by norm_num)
theorem B3609701 : Blo 1603000 3609701 := bbase (se 4 (by rfl) ⟨338409, by rfl⟩ : syracuseStep 3609701 = 676819) (by norm_num)
theorem B4060277 : Blo 1603000 4060277 := bbase (se 5 (by rfl) ⟨190325, by rfl⟩ : syracuseStep 4060277 = 380651) (by norm_num)
theorem B2405501 : Blo 1603000 2405501 := bbase (se 3 (by rfl) ⟨451031, by rfl⟩ : syracuseStep 2405501 = 902063) (by norm_num)
theorem B3855485 : Blo 1603000 3855485 := bbase (se 3 (by rfl) ⟨722903, by rfl⟩ : syracuseStep 3855485 = 1445807) (by norm_num)
theorem B2405525 : Blo 1603000 2405525 := bbase (se 6 (by rfl) ⟨56379, by rfl⟩ : syracuseStep 2405525 = 112759) (by norm_num)
theorem B2405549 : Blo 1603000 2405549 := bbase (se 3 (by rfl) ⟨451040, by rfl⟩ : syracuseStep 2405549 = 902081) (by norm_num)
theorem B3609773 : Blo 1603000 3609773 := bbase (se 3 (by rfl) ⟨676832, by rfl⟩ : syracuseStep 3609773 = 1353665) (by norm_num)
theorem B2405573 : Blo 1603000 2405573 := bbase (se 4 (by rfl) ⟨225522, by rfl⟩ : syracuseStep 2405573 = 451045) (by norm_num)
theorem B2438365 : Blo 1603000 2438365 := bbase (se 3 (by rfl) ⟨457193, by rfl⟩ : syracuseStep 2438365 = 914387) (by norm_num)
theorem B2405597 : Blo 1603000 2405597 := bbase (se 3 (by rfl) ⟨451049, by rfl⟩ : syracuseStep 2405597 = 902099) (by norm_num)
theorem B2405621 : Blo 1603000 2405621 := bbase (se 5 (by rfl) ⟨112763, by rfl⟩ : syracuseStep 2405621 = 225527) (by norm_num)
theorem B3609845 : Blo 1603000 3609845 := bbase (se 5 (by rfl) ⟨169211, by rfl⟩ : syracuseStep 3609845 = 338423) (by norm_num)
theorem B2405645 : Blo 1603000 2405645 := bbase (se 3 (by rfl) ⟨451058, by rfl⟩ : syracuseStep 2405645 = 902117) (by norm_num)
theorem B2028817 : Blo 1603000 2028817 := bbase (se 2 (by rfl) ⟨760806, by rfl⟩ : syracuseStep 2028817 = 1521613) (by norm_num)
theorem B2405669 : Blo 1603000 2405669 := bbase (se 4 (by rfl) ⟨225531, by rfl⟩ : syracuseStep 2405669 = 451063) (by norm_num)
theorem B5412149 : Blo 1603000 5412149 := bbase (se 5 (by rfl) ⟨253694, by rfl⟩ : syracuseStep 5412149 = 507389) (by norm_num)
theorem B4060469 : Blo 1603000 4060469 := bbase (se 5 (by rfl) ⟨190334, by rfl⟩ : syracuseStep 4060469 = 380669) (by norm_num)
theorem B2405693 : Blo 1603000 2405693 := bbase (se 3 (by rfl) ⟨451067, by rfl⟩ : syracuseStep 2405693 = 902135) (by norm_num)
theorem B3609917 : Blo 1603000 3609917 := bbase (se 3 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 3609917 = 1353719) (by norm_num)
theorem B2405717 : Blo 1603000 2405717 := bbase (se 13 (by rfl) ⟨440, by rfl⟩ : syracuseStep 2405717 = 881) (by norm_num)
theorem B6092117 : Blo 1603000 6092117 := bbase (se 13 (by rfl) ⟨1115, by rfl⟩ : syracuseStep 6092117 = 2231) (by norm_num)
theorem B2405741 : Blo 1603000 2405741 := bbase (se 3 (by rfl) ⟨451076, by rfl⟩ : syracuseStep 2405741 = 902153) (by norm_num)
theorem B2405765 : Blo 1603000 2405765 := bbase (se 4 (by rfl) ⟨225540, by rfl⟩ : syracuseStep 2405765 = 451081) (by norm_num)
theorem B3609989 : Blo 1603000 3609989 := bbase (se 4 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 3609989 = 676873) (by norm_num)
theorem B2282909 : Blo 1603000 2282909 := bbase (se 3 (by rfl) ⟨428045, by rfl⟩ : syracuseStep 2282909 = 856091) (by norm_num)
theorem B2405789 : Blo 1603000 2405789 := bbase (se 3 (by rfl) ⟨451085, by rfl⟩ : syracuseStep 2405789 = 902171) (by norm_num)
theorem B8123813 : Blo 1603000 8123813 := bbase (se 4 (by rfl) ⟨761607, by rfl⟩ : syracuseStep 8123813 = 1523215) (by norm_num)
theorem B2405813 : Blo 1603000 2405813 := bbase (se 5 (by rfl) ⟨112772, by rfl⟩ : syracuseStep 2405813 = 225545) (by norm_num)
theorem B2028989 : Blo 1603000 2028989 := bbase (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) (by norm_num)
theorem B2405837 : Blo 1603000 2405837 := bbase (se 3 (by rfl) ⟨451094, by rfl⟩ : syracuseStep 2405837 = 902189) (by norm_num)
theorem B3610061 : Blo 1603000 3610061 := bbase (se 3 (by rfl) ⟨676886, by rfl⟩ : syracuseStep 3610061 = 1353773) (by norm_num)
theorem B2405861 : Blo 1603000 2405861 := bbase (se 4 (by rfl) ⟨225549, by rfl⟩ : syracuseStep 2405861 = 451099) (by norm_num)
theorem B2029045 : Blo 1603000 2029045 := bbase (se 5 (by rfl) ⟨95111, by rfl⟩ : syracuseStep 2029045 = 190223) (by norm_num)
theorem B2405885 : Blo 1603000 2405885 := bbase (se 3 (by rfl) ⟨451103, by rfl⟩ : syracuseStep 2405885 = 902207) (by norm_num)
theorem B2168317 : Blo 1603000 2168317 := bbase (se 3 (by rfl) ⟨406559, by rfl⟩ : syracuseStep 2168317 = 813119) (by norm_num)
theorem B2405909 : Blo 1603000 2405909 := bbase (se 6 (by rfl) ⟨56388, by rfl⟩ : syracuseStep 2405909 = 112777) (by norm_num)
theorem B3610133 : Blo 1603000 3610133 := bbase (se 6 (by rfl) ⟨84612, by rfl⟩ : syracuseStep 3610133 = 169225) (by norm_num)
theorem B2405933 : Blo 1603000 2405933 := bbase (se 3 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 2405933 = 902225) (by norm_num)
theorem B2168365 : Blo 1603000 2168365 := bbase (se 3 (by rfl) ⟨406568, by rfl⟩ : syracuseStep 2168365 = 813137) (by norm_num)
theorem B2405957 : Blo 1603000 2405957 := bbase (se 4 (by rfl) ⟨225558, by rfl⟩ : syracuseStep 2405957 = 451117) (by norm_num)
theorem B2029141 : Blo 1603000 2029141 := bbase (se 8 (by rfl) ⟨11889, by rfl⟩ : syracuseStep 2029141 = 23779) (by norm_num)
theorem B2405981 : Blo 1603000 2405981 := bbase (se 3 (by rfl) ⟨451121, by rfl⟩ : syracuseStep 2405981 = 902243) (by norm_num)
theorem B3610205 : Blo 1603000 3610205 := bbase (se 3 (by rfl) ⟨676913, by rfl⟩ : syracuseStep 3610205 = 1353827) (by norm_num)
theorem B3044965 : Blo 1603000 3044965 := bbase (se 4 (by rfl) ⟨285465, by rfl⟩ : syracuseStep 3044965 = 570931) (by norm_num)
theorem B2406005 : Blo 1603000 2406005 := bbase (se 5 (by rfl) ⟨112781, by rfl⟩ : syracuseStep 2406005 = 225563) (by norm_num)
theorem B6092405 : Blo 1603000 6092405 := bbase (se 5 (by rfl) ⟨285581, by rfl⟩ : syracuseStep 6092405 = 571163) (by norm_num)
theorem B2406029 : Blo 1603000 2406029 := bbase (se 3 (by rfl) ⟨451130, by rfl⟩ : syracuseStep 2406029 = 902261) (by norm_num)
theorem B4060813 : Blo 1603000 4060813 := bbase (se 3 (by rfl) ⟨761402, by rfl⟩ : syracuseStep 4060813 = 1522805) (by norm_num)
theorem B2406053 : Blo 1603000 2406053 := bbase (se 4 (by rfl) ⟨225567, by rfl⟩ : syracuseStep 2406053 = 451135) (by norm_num)
theorem B3610277 : Blo 1603000 3610277 := bbase (se 4 (by rfl) ⟨338463, by rfl⟩ : syracuseStep 3610277 = 676927) (by norm_num)
theorem B6174389 : Blo 1603000 6174389 := bbase (se 5 (by rfl) ⟨289424, by rfl⟩ : syracuseStep 6174389 = 578849) (by norm_num)
theorem B2406077 : Blo 1603000 2406077 := bbase (se 3 (by rfl) ⟨451139, by rfl⟩ : syracuseStep 2406077 = 902279) (by norm_num)
theorem B2406101 : Blo 1603000 2406101 := bbase (se 7 (by rfl) ⟨28196, by rfl⟩ : syracuseStep 2406101 = 56393) (by norm_num)
theorem B2889437 : Blo 1603000 2889437 := bbase (se 3 (by rfl) ⟨541769, by rfl⟩ : syracuseStep 2889437 = 1083539) (by norm_num)
theorem B3471077 : Blo 1603000 3471077 := bbase (se 4 (by rfl) ⟨325413, by rfl⟩ : syracuseStep 3471077 = 650827) (by norm_num)
theorem B5412581 : Blo 1603000 5412581 := bbase (se 4 (by rfl) ⟨507429, by rfl⟩ : syracuseStep 5412581 = 1014859) (by norm_num)
theorem B2406125 : Blo 1603000 2406125 := bbase (se 3 (by rfl) ⟨451148, by rfl⟩ : syracuseStep 2406125 = 902297) (by norm_num)
theorem B3610349 : Blo 1603000 3610349 := bbase (se 3 (by rfl) ⟨676940, by rfl⟩ : syracuseStep 3610349 = 1353881) (by norm_num)
theorem B3045109 : Blo 1603000 3045109 := bbase (se 5 (by rfl) ⟨142739, by rfl⟩ : syracuseStep 3045109 = 285479) (by norm_num)
theorem B4060925 : Blo 1603000 4060925 := bbase (se 3 (by rfl) ⟨761423, by rfl⟩ : syracuseStep 4060925 = 1522847) (by norm_num)
theorem B2029313 : Blo 1603000 2029313 := bbase (se 2 (by rfl) ⟨760992, by rfl⟩ : syracuseStep 2029313 = 1521985) (by norm_num)
theorem B2406149 : Blo 1603000 2406149 := bbase (se 4 (by rfl) ⟨225576, by rfl⟩ : syracuseStep 2406149 = 451153) (by norm_num)
theorem B2168581 : Blo 1603000 2168581 := bbase (se 4 (by rfl) ⟨203304, by rfl⟩ : syracuseStep 2168581 = 406609) (by norm_num)
theorem B2406173 : Blo 1603000 2406173 := bbase (se 3 (by rfl) ⟨451157, by rfl⟩ : syracuseStep 2406173 = 902315) (by norm_num)
theorem B2406197 : Blo 1603000 2406197 := bbase (se 5 (by rfl) ⟨112790, by rfl⟩ : syracuseStep 2406197 = 225581) (by norm_num)
theorem B3610421 : Blo 1603000 3610421 := bbase (se 5 (by rfl) ⟨169238, by rfl⟩ : syracuseStep 3610421 = 338477) (by norm_num)
theorem B2029369 : Blo 1603000 2029369 := bbase (se 2 (by rfl) ⟨761013, by rfl⟩ : syracuseStep 2029369 = 1522027) (by norm_num)
theorem B6854453 : Blo 1603000 6854453 := bbase (se 5 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 6854453 = 642605) (by norm_num)
theorem B8116037 : Blo 1603000 8116037 := bbase (se 4 (by rfl) ⟨760878, by rfl⟩ : syracuseStep 8116037 = 1521757) (by norm_num)
theorem B2406221 : Blo 1603000 2406221 := bbase (se 3 (by rfl) ⟨451166, by rfl⟩ : syracuseStep 2406221 = 902333) (by norm_num)
theorem B2406245 : Blo 1603000 2406245 := bbase (se 4 (by rfl) ⟨225585, by rfl⟩ : syracuseStep 2406245 = 451171) (by norm_num)
theorem B2406269 : Blo 1603000 2406269 := bbase (se 3 (by rfl) ⟨451175, by rfl⟩ : syracuseStep 2406269 = 902351) (by norm_num)
theorem B3610493 : Blo 1603000 3610493 := bbase (se 3 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 3610493 = 1353935) (by norm_num)
theorem B2742149 : Blo 1603000 2742149 := bbase (se 4 (by rfl) ⟨257076, by rfl⟩ : syracuseStep 2742149 = 514153) (by norm_num)
theorem B3045269 : Blo 1603000 3045269 := bbase (se 6 (by rfl) ⟨71373, by rfl⟩ : syracuseStep 3045269 = 142747) (by norm_num)
theorem B2406293 : Blo 1603000 2406293 := bbase (se 6 (by rfl) ⟨56397, by rfl⟩ : syracuseStep 2406293 = 112795) (by norm_num)
theorem B2029465 : Blo 1603000 2029465 := bbase (se 2 (by rfl) ⟨761049, by rfl⟩ : syracuseStep 2029465 = 1522099) (by norm_num)
theorem B2406317 : Blo 1603000 2406317 := bbase (se 3 (by rfl) ⟨451184, by rfl⟩ : syracuseStep 2406317 = 902369) (by norm_num)
theorem B4061117 : Blo 1603000 4061117 := bbase (se 3 (by rfl) ⟨761459, by rfl⟩ : syracuseStep 4061117 = 1522919) (by norm_num)
theorem B2406341 : Blo 1603000 2406341 := bbase (se 4 (by rfl) ⟨225594, by rfl⟩ : syracuseStep 2406341 = 451189) (by norm_num)
theorem B3610565 : Blo 1603000 3610565 := bbase (se 4 (by rfl) ⟨338490, by rfl⟩ : syracuseStep 3610565 = 676981) (by norm_num)
theorem B2406365 : Blo 1603000 2406365 := bbase (se 3 (by rfl) ⟨451193, by rfl⟩ : syracuseStep 2406365 = 902387) (by norm_num)
theorem B2570221 : Blo 1603000 2570221 := bbase (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) (by norm_num)
theorem B2406389 : Blo 1603000 2406389 := bbase (se 5 (by rfl) ⟨112799, by rfl⟩ : syracuseStep 2406389 = 225599) (by norm_num)
theorem B2406413 : Blo 1603000 2406413 := bbase (se 3 (by rfl) ⟨451202, by rfl⟩ : syracuseStep 2406413 = 902405) (by norm_num)
theorem B3610637 : Blo 1603000 3610637 := bbase (se 3 (by rfl) ⟨676994, by rfl⟩ : syracuseStep 3610637 = 1353989) (by norm_num)
theorem B3045413 : Blo 1603000 3045413 := bbase (se 4 (by rfl) ⟨285507, by rfl⟩ : syracuseStep 3045413 = 571015) (by norm_num)
theorem B2406437 : Blo 1603000 2406437 := bbase (se 4 (by rfl) ⟨225603, by rfl⟩ : syracuseStep 2406437 = 451207) (by norm_num)
theorem B3905597 : Blo 1603000 3905597 := bbase (se 3 (by rfl) ⟨732299, by rfl⟩ : syracuseStep 3905597 = 1464599) (by norm_num)
theorem B2439229 : Blo 1603000 2439229 := bbase (se 3 (by rfl) ⟨457355, by rfl⟩ : syracuseStep 2439229 = 914711) (by norm_num)
theorem B2406461 : Blo 1603000 2406461 := bbase (se 3 (by rfl) ⟨451211, by rfl⟩ : syracuseStep 2406461 = 902423) (by norm_num)
theorem B2029637 : Blo 1603000 2029637 := bbase (se 4 (by rfl) ⟨190278, by rfl⟩ : syracuseStep 2029637 = 380557) (by norm_num)
theorem B2406485 : Blo 1603000 2406485 := bbase (se 8 (by rfl) ⟨14100, by rfl⟩ : syracuseStep 2406485 = 28201) (by norm_num)
theorem B3610709 : Blo 1603000 3610709 := bbase (se 8 (by rfl) ⟨21156, by rfl⟩ : syracuseStep 3610709 = 42313) (by norm_num)
theorem B3250277 : Blo 1603000 3250277 := bbase (se 4 (by rfl) ⟨304713, by rfl⟩ : syracuseStep 3250277 = 609427) (by norm_num)
theorem B2406509 : Blo 1603000 2406509 := bbase (se 3 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 2406509 = 902441) (by norm_num)
theorem B2029693 : Blo 1603000 2029693 := bbase (se 3 (by rfl) ⟨380567, by rfl⟩ : syracuseStep 2029693 = 761135) (by norm_num)
theorem B2406533 : Blo 1603000 2406533 := bbase (se 4 (by rfl) ⟨225612, by rfl⟩ : syracuseStep 2406533 = 451225) (by norm_num)
theorem B2283661 : Blo 1603000 2283661 := bbase (se 3 (by rfl) ⟨428186, by rfl⟩ : syracuseStep 2283661 = 856373) (by norm_num)
theorem B5413013 : Blo 1603000 5413013 := bbase (se 6 (by rfl) ⟨126867, by rfl⟩ : syracuseStep 5413013 = 253735) (by norm_num)
theorem B2406557 : Blo 1603000 2406557 := bbase (se 3 (by rfl) ⟨451229, by rfl⟩ : syracuseStep 2406557 = 902459) (by norm_num)
theorem B3610781 : Blo 1603000 3610781 := bbase (se 3 (by rfl) ⟨677021, by rfl⟩ : syracuseStep 3610781 = 1354043) (by norm_num)
theorem B2406581 : Blo 1603000 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B2406605 : Blo 1603000 2406605 := bbase (se 3 (by rfl) ⟨451238, by rfl⟩ : syracuseStep 2406605 = 902477) (by norm_num)
theorem B2029789 : Blo 1603000 2029789 := bbase (se 3 (by rfl) ⟨380585, by rfl⟩ : syracuseStep 2029789 = 761171) (by norm_num)
theorem B2406629 : Blo 1603000 2406629 := bbase (se 4 (by rfl) ⟨225621, by rfl⟩ : syracuseStep 2406629 = 451243) (by norm_num)
theorem B3610853 : Blo 1603000 3610853 := bbase (se 4 (by rfl) ⟨338517, by rfl⟩ : syracuseStep 3610853 = 677035) (by norm_num)
theorem B11565301 : Blo 1603000 11565301 := bbase (se 5 (by rfl) ⟨542123, by rfl⟩ : syracuseStep 11565301 = 1084247) (by norm_num)
theorem B2406653 : Blo 1603000 2406653 := bbase (se 3 (by rfl) ⟨451247, by rfl⟩ : syracuseStep 2406653 = 902495) (by norm_num)
theorem B2406677 : Blo 1603000 2406677 := bbase (se 6 (by rfl) ⟨56406, by rfl⟩ : syracuseStep 2406677 = 112813) (by norm_num)
theorem B4061461 : Blo 1603000 4061461 := bbase (se 6 (by rfl) ⟨95190, by rfl⟩ : syracuseStep 4061461 = 190381) (by norm_num)
theorem B2406701 : Blo 1603000 2406701 := bbase (se 3 (by rfl) ⟨451256, by rfl⟩ : syracuseStep 2406701 = 902513) (by norm_num)
theorem B3610925 : Blo 1603000 3610925 := bbase (se 3 (by rfl) ⟨677048, by rfl⟩ : syracuseStep 3610925 = 1354097) (by norm_num)
theorem B3045701 : Blo 1603000 3045701 := bbase (se 4 (by rfl) ⟨285534, by rfl⟩ : syracuseStep 3045701 = 571069) (by norm_num)
theorem B2406725 : Blo 1603000 2406725 := bbase (se 4 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 2406725 = 451261) (by norm_num)
theorem B2406749 : Blo 1603000 2406749 := bbase (se 3 (by rfl) ⟨451265, by rfl⟩ : syracuseStep 2406749 = 902531) (by norm_num)
theorem B6256997 : Blo 1603000 6256997 := bbase (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) (by norm_num)
theorem B2406773 : Blo 1603000 2406773 := bbase (se 5 (by rfl) ⟨112817, by rfl⟩ : syracuseStep 2406773 = 225635) (by norm_num)
theorem B3610997 : Blo 1603000 3610997 := bbase (se 5 (by rfl) ⟨169265, by rfl⟩ : syracuseStep 3610997 = 338531) (by norm_num)
theorem B4061573 : Blo 1603000 4061573 := bbase (se 4 (by rfl) ⟨380772, by rfl⟩ : syracuseStep 4061573 = 761545) (by norm_num)
theorem B2029961 : Blo 1603000 2029961 := bbase (se 2 (by rfl) ⟨761235, by rfl⟩ : syracuseStep 2029961 = 1522471) (by norm_num)
theorem B2406797 : Blo 1603000 2406797 := bbase (se 3 (by rfl) ⟨451274, by rfl⟩ : syracuseStep 2406797 = 902549) (by norm_num)
theorem B2406821 : Blo 1603000 2406821 := bbase (se 4 (by rfl) ⟨225639, by rfl⟩ : syracuseStep 2406821 = 451279) (by norm_num)
theorem B4569509 : Blo 1603000 4569509 := bbase (se 4 (by rfl) ⟨428391, by rfl⟩ : syracuseStep 4569509 = 856783) (by norm_num)
theorem B2406845 : Blo 1603000 2406845 := bbase (se 3 (by rfl) ⟨451283, by rfl⟩ : syracuseStep 2406845 = 902567) (by norm_num)
theorem B3611069 : Blo 1603000 3611069 := bbase (se 3 (by rfl) ⟨677075, by rfl⟩ : syracuseStep 3611069 = 1354151) (by norm_num)
theorem B2030017 : Blo 1603000 2030017 := bbase (se 2 (by rfl) ⟨761256, by rfl⟩ : syracuseStep 2030017 = 1522513) (by norm_num)
theorem B5487061 : Blo 1603000 5487061 := bbase (se 7 (by rfl) ⟨64301, by rfl⟩ : syracuseStep 5487061 = 128603) (by norm_num)
theorem B2406869 : Blo 1603000 2406869 := bbase (se 7 (by rfl) ⟨28205, by rfl⟩ : syracuseStep 2406869 = 56411) (by norm_num)
theorem B3045853 : Blo 1603000 3045853 := bbase (se 3 (by rfl) ⟨571097, by rfl⟩ : syracuseStep 3045853 = 1142195) (by norm_num)
theorem B7707109 : Blo 1603000 7707109 := bbase (se 4 (by rfl) ⟨722541, by rfl⟩ : syracuseStep 7707109 = 1445083) (by norm_num)
theorem B2406893 : Blo 1603000 2406893 := bbase (se 3 (by rfl) ⟨451292, by rfl⟩ : syracuseStep 2406893 = 902585) (by norm_num)
theorem B7707125 : Blo 1603000 7707125 := bbase (se 5 (by rfl) ⟨361271, by rfl⟩ : syracuseStep 7707125 = 722543) (by norm_num)
theorem B2931197 : Blo 1603000 2931197 := bbase (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) (by norm_num)
theorem B2406917 : Blo 1603000 2406917 := bbase (se 4 (by rfl) ⟨225648, by rfl⟩ : syracuseStep 2406917 = 451297) (by norm_num)
theorem B3611141 : Blo 1603000 3611141 := bbase (se 4 (by rfl) ⟨338544, by rfl⟩ : syracuseStep 3611141 = 677089) (by norm_num)
theorem B2406941 : Blo 1603000 2406941 := bbase (se 3 (by rfl) ⟨451301, by rfl⟩ : syracuseStep 2406941 = 902603) (by norm_num)
theorem B2030113 : Blo 1603000 2030113 := bbase (se 2 (by rfl) ⟨761292, by rfl⟩ : syracuseStep 2030113 = 1522585) (by norm_num)
theorem B2406965 : Blo 1603000 2406965 := bbase (se 5 (by rfl) ⟨112826, by rfl⟩ : syracuseStep 2406965 = 225653) (by norm_num)
theorem B5413445 : Blo 1603000 5413445 := bbase (se 4 (by rfl) ⟨507510, by rfl⟩ : syracuseStep 5413445 = 1015021) (by norm_num)
theorem B4061765 : Blo 1603000 4061765 := bbase (se 4 (by rfl) ⟨380790, by rfl⟩ : syracuseStep 4061765 = 761581) (by norm_num)
theorem B2406989 : Blo 1603000 2406989 := bbase (se 3 (by rfl) ⟨451310, by rfl⟩ : syracuseStep 2406989 = 902621) (by norm_num)
theorem B3611213 : Blo 1603000 3611213 := bbase (se 3 (by rfl) ⟨677102, by rfl⟩ : syracuseStep 3611213 = 1354205) (by norm_num)
theorem B2407013 : Blo 1603000 2407013 := bbase (se 4 (by rfl) ⟨225657, by rfl⟩ : syracuseStep 2407013 = 451315) (by norm_num)
theorem B5282405 : Blo 1603000 5282405 := bbase (se 4 (by rfl) ⟨495225, by rfl⟩ : syracuseStep 5282405 = 990451) (by norm_num)
theorem B2407037 : Blo 1603000 2407037 := bbase (se 3 (by rfl) ⟨451319, by rfl⟩ : syracuseStep 2407037 = 902639) (by norm_num)
theorem B2407061 : Blo 1603000 2407061 := bbase (se 6 (by rfl) ⟨56415, by rfl⟩ : syracuseStep 2407061 = 112831) (by norm_num)
theorem B2407085 : Blo 1603000 2407085 := bbase (se 3 (by rfl) ⟨451328, by rfl⟩ : syracuseStep 2407085 = 902657) (by norm_num)
theorem B11885237 : Blo 1603000 11885237 := bbase (se 5 (by rfl) ⟨557120, by rfl⟩ : syracuseStep 11885237 = 1114241) (by norm_num)
theorem B8125109 : Blo 1603000 8125109 := bbase (se 5 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 8125109 = 761729) (by norm_num)
theorem B2407109 : Blo 1603000 2407109 := bbase (se 4 (by rfl) ⟨225666, by rfl⟩ : syracuseStep 2407109 = 451333) (by norm_num)
theorem B2030285 : Blo 1603000 2030285 := bbase (se 3 (by rfl) ⟨380678, by rfl⟩ : syracuseStep 2030285 = 761357) (by norm_num)
theorem B2407133 : Blo 1603000 2407133 := bbase (se 3 (by rfl) ⟨451337, by rfl⟩ : syracuseStep 2407133 = 902675) (by norm_num)
theorem B2407157 : Blo 1603000 2407157 := bbase (se 5 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 2407157 = 225671) (by norm_num)
theorem B2030341 : Blo 1603000 2030341 := bbase (se 4 (by rfl) ⟨190344, by rfl⟩ : syracuseStep 2030341 = 380689) (by norm_num)
theorem B3046157 : Blo 1603000 3046157 := bbase (se 3 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 3046157 = 1142309) (by norm_num)
theorem B2407181 : Blo 1603000 2407181 := bbase (se 3 (by rfl) ⟨451346, by rfl⟩ : syracuseStep 2407181 = 902693) (by norm_num)
theorem B9132821 : Blo 1603000 9132821 := bbase (se 6 (by rfl) ⟨214050, by rfl⟩ : syracuseStep 9132821 = 428101) (by norm_num)
theorem B6093589 : Blo 1603000 6093589 := bbase (se 6 (by rfl) ⟨142818, by rfl⟩ : syracuseStep 6093589 = 285637) (by norm_num)
theorem B2407205 : Blo 1603000 2407205 := bbase (se 4 (by rfl) ⟨225675, by rfl⟩ : syracuseStep 2407205 = 451351) (by norm_num)
theorem B6855461 : Blo 1603000 6855461 := bbase (se 4 (by rfl) ⟨642699, by rfl⟩ : syracuseStep 6855461 = 1285399) (by norm_num)
theorem B2407229 : Blo 1603000 2407229 := bbase (se 3 (by rfl) ⟨451355, by rfl⟩ : syracuseStep 2407229 = 902711) (by norm_num)
theorem B2407253 : Blo 1603000 2407253 := bbase (se 9 (by rfl) ⟨7052, by rfl⟩ : syracuseStep 2407253 = 14105) (by norm_num)
theorem B2030437 : Blo 1603000 2030437 := bbase (se 4 (by rfl) ⟨190353, by rfl⟩ : syracuseStep 2030437 = 380707) (by norm_num)
theorem B2407277 : Blo 1603000 2407277 := bbase (se 3 (by rfl) ⟨451364, by rfl⟩ : syracuseStep 2407277 = 902729) (by norm_num)
theorem B2407301 : Blo 1603000 2407301 := bbase (se 4 (by rfl) ⟨225684, by rfl⟩ : syracuseStep 2407301 = 451369) (by norm_num)
theorem B5782421 : Blo 1603000 5782421 := bbase (se 6 (by rfl) ⟨135525, by rfl⟩ : syracuseStep 5782421 = 271051) (by norm_num)
theorem B4062109 : Blo 1603000 4062109 := bbase (se 3 (by rfl) ⟨761645, by rfl⟩ : syracuseStep 4062109 = 1523291) (by norm_num)
theorem B2407325 : Blo 1603000 2407325 := bbase (se 3 (by rfl) ⟨451373, by rfl⟩ : syracuseStep 2407325 = 902747) (by norm_num)
theorem B2284453 : Blo 1603000 2284453 := bbase (se 4 (by rfl) ⟨214167, by rfl⟩ : syracuseStep 2284453 = 428335) (by norm_num)
theorem B2407349 : Blo 1603000 2407349 := bbase (se 5 (by rfl) ⟨112844, by rfl⟩ : syracuseStep 2407349 = 225689) (by norm_num)
theorem B6847429 : Blo 1603000 6847429 := bbase (se 4 (by rfl) ⟨641946, by rfl⟩ : syracuseStep 6847429 = 1283893) (by norm_num)
theorem B2407373 : Blo 1603000 2407373 := bbase (se 3 (by rfl) ⟨451382, by rfl⟩ : syracuseStep 2407373 = 902765) (by norm_num)
theorem B2407397 : Blo 1603000 2407397 := bbase (se 4 (by rfl) ⟨225693, by rfl⟩ : syracuseStep 2407397 = 451387) (by norm_num)
theorem B5413877 : Blo 1603000 5413877 := bbase (se 5 (by rfl) ⟨253775, by rfl⟩ : syracuseStep 5413877 = 507551) (by norm_num)
theorem B2407421 : Blo 1603000 2407421 := bbase (se 3 (by rfl) ⟨451391, by rfl⟩ : syracuseStep 2407421 = 902783) (by norm_num)
theorem B4062221 : Blo 1603000 4062221 := bbase (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) (by norm_num)
theorem B2030609 : Blo 1603000 2030609 := bbase (se 2 (by rfl) ⟨761478, by rfl⟩ : syracuseStep 2030609 = 1522957) (by norm_num)
theorem B2407445 : Blo 1603000 2407445 := bbase (se 6 (by rfl) ⟨56424, by rfl⟩ : syracuseStep 2407445 = 112849) (by norm_num)
theorem B5782565 : Blo 1603000 5782565 := bbase (se 4 (by rfl) ⟨542115, by rfl⟩ : syracuseStep 5782565 = 1084231) (by norm_num)
theorem B2407469 : Blo 1603000 2407469 := bbase (se 3 (by rfl) ⟨451400, by rfl⟩ : syracuseStep 2407469 = 902801) (by norm_num)
theorem B6093893 : Blo 1603000 6093893 := bbase (se 4 (by rfl) ⟨571302, by rfl⟩ : syracuseStep 6093893 = 1142605) (by norm_num)
theorem B2407493 : Blo 1603000 2407493 := bbase (se 4 (by rfl) ⟨225702, by rfl⟩ : syracuseStep 2407493 = 451405) (by norm_num)
theorem B2030665 : Blo 1603000 2030665 := bbase (se 2 (by rfl) ⟨761499, by rfl⟩ : syracuseStep 2030665 = 1522999) (by norm_num)
theorem B8117333 : Blo 1603000 8117333 := bbase (se 8 (by rfl) ⟨47562, by rfl⟩ : syracuseStep 8117333 = 95125) (by norm_num)
theorem B15416405 : Blo 1603000 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B14630005 : Blo 1603000 14630005 := bbase (se 5 (by rfl) ⟨685781, by rfl⟩ : syracuseStep 14630005 = 1371563) (by norm_num)
theorem B2604197 : Blo 1603000 2604197 := bbase (se 4 (by rfl) ⟨244143, by rfl⟩ : syracuseStep 2604197 = 488287) (by norm_num)
theorem B2030761 : Blo 1603000 2030761 := bbase (se 2 (by rfl) ⟨761535, by rfl⟩ : syracuseStep 2030761 = 1523071) (by norm_num)
theorem B4062413 : Blo 1603000 4062413 := bbase (se 3 (by rfl) ⟨761702, by rfl⟩ : syracuseStep 4062413 = 1523405) (by norm_num)
theorem B2284789 : Blo 1603000 2284789 := bbase (se 5 (by rfl) ⟨107099, by rfl⟩ : syracuseStep 2284789 = 214199) (by norm_num)
theorem B5209381 : Blo 1603000 5209381 := bbase (se 4 (by rfl) ⟨488379, by rfl⟩ : syracuseStep 5209381 = 976759) (by norm_num)
theorem B2030933 : Blo 1603000 2030933 := bbase (se 11 (by rfl) ⟨1487, by rfl⟩ : syracuseStep 2030933 = 2975) (by norm_num)
theorem B2030989 : Blo 1603000 2030989 := bbase (se 3 (by rfl) ⟨380810, by rfl⟩ : syracuseStep 2030989 = 761621) (by norm_num)
theorem B5414309 : Blo 1603000 5414309 := bbase (se 4 (by rfl) ⟨507591, by rfl⟩ : syracuseStep 5414309 = 1015183) (by norm_num)
theorem B6503861 : Blo 1603000 6503861 := bbase (se 5 (by rfl) ⟨304868, by rfl⟩ : syracuseStep 6503861 = 609737) (by norm_num)
theorem B3087805 : Blo 1603000 3087805 := bbase (se 3 (by rfl) ⟨578963, by rfl⟩ : syracuseStep 3087805 = 1157927) (by norm_num)
theorem B2285005 : Blo 1603000 2285005 := bbase (se 3 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 2285005 = 856877) (by norm_num)
theorem B2031085 : Blo 1603000 2031085 := bbase (se 3 (by rfl) ⟨380828, by rfl⟩ : syracuseStep 2031085 = 761657) (by norm_num)
theorem B3046909 : Blo 1603000 3046909 := bbase (se 3 (by rfl) ⟨571295, by rfl⟩ : syracuseStep 3046909 = 1142591) (by norm_num)
theorem B5135957 : Blo 1603000 5135957 := bbase (se 8 (by rfl) ⟨30093, by rfl⟩ : syracuseStep 5135957 = 60187) (by norm_num)
theorem B2031257 : Blo 1603000 2031257 := bbase (se 2 (by rfl) ⟨761721, by rfl⟩ : syracuseStep 2031257 = 1523443) (by norm_num)
theorem B6848165 : Blo 1603000 6848165 := bbase (se 4 (by rfl) ⟨642015, by rfl⟩ : syracuseStep 6848165 = 1284031) (by norm_num)
theorem B2031313 : Blo 1603000 2031313 := bbase (se 2 (by rfl) ⟨761742, by rfl⟩ : syracuseStep 2031313 = 1523485) (by norm_num)
theorem B1711849 : Blo 1603000 1711849 := bbase (se 2 (by rfl) ⟨641943, by rfl⟩ : syracuseStep 1711849 = 1283887) (by norm_num)
theorem B5414741 : Blo 1603000 5414741 := bbase (se 9 (by rfl) ⟨15863, by rfl⟩ : syracuseStep 5414741 = 31727) (by norm_num)
theorem B1711973 : Blo 1603000 1711973 := bbase (se 4 (by rfl) ⟨160497, by rfl⟩ : syracuseStep 1711973 = 320995) (by norm_num)
theorem B12345205 : Blo 1603000 12345205 := bbase (se 5 (by rfl) ⟨578681, by rfl⟩ : syracuseStep 12345205 = 1157363) (by norm_num)
theorem B13705109 : Blo 1603000 13705109 := bbase (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) (by norm_num)
theorem B9134005 : Blo 1603000 9134005 := bbase (se 5 (by rfl) ⟨428156, by rfl⟩ : syracuseStep 9134005 = 856313) (by norm_num)
theorem B28934101 : Blo 1603000 28934101 := bbase (se 7 (by rfl) ⟨339071, by rfl⟩ : syracuseStep 28934101 = 678143) (by norm_num)
theorem B5414957 : Blo 1603000 5414957 := bstep (se 3 (by rfl) ⟨1015304, by rfl⟩ : syracuseStep 5414957 = 2030609) B2030609
theorem B3252305 : Blo 1603000 3252305 := bstep (se 2 (by rfl) ⟨1219614, by rfl⟩ : syracuseStep 3252305 = 2439229) B2439229
theorem B5415011 : Blo 1603000 5415011 := bstep (se 1 (by rfl) ⟨4061258, by rfl⟩ : syracuseStep 5415011 = 8122517) B8122517
theorem B27779213 : Blo 1603000 27779213 := bstep (se 3 (by rfl) ⟨5208602, by rfl⟩ : syracuseStep 27779213 = 10417205) B10417205
theorem B8675533 : Blo 1603000 8675533 := bstep (se 3 (by rfl) ⟨1626662, by rfl⟩ : syracuseStep 8675533 = 3253325) B3253325
theorem B14082275 : Blo 1603000 14082275 := bstep (se 1 (by rfl) ⟨10561706, by rfl⟩ : syracuseStep 14082275 = 21123413) B21123413
theorem B1712387 : Blo 1603000 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B10281293 : Blo 1603000 10281293 := bstep (se 3 (by rfl) ⟨1927742, by rfl⟩ : syracuseStep 10281293 = 3855485) B3855485
theorem B5415281 : Blo 1603000 5415281 := bstep (se 2 (by rfl) ⟨2030730, by rfl⟩ : syracuseStep 5415281 = 4061461) B4061461
theorem B16695665 : Blo 1603000 16695665 := bstep (se 2 (by rfl) ⟨6260874, by rfl⟩ : syracuseStep 16695665 = 12521749) B12521749
theorem B5136803 : Blo 1603000 5136803 := bstep (se 1 (by rfl) ⟨3852602, by rfl⟩ : syracuseStep 5136803 = 7705205) B7705205
theorem B6087089 : Blo 1603000 6087089 := bstep (se 2 (by rfl) ⟨2282658, by rfl⟩ : syracuseStep 6087089 = 4565317) B4565317
theorem B3424835 : Blo 1603000 3424835 := bstep (se 1 (by rfl) ⟨2568626, by rfl⟩ : syracuseStep 3424835 = 5137253) B5137253
theorem B6849137 : Blo 1603000 6849137 := bstep (se 2 (by rfl) ⟨2568426, by rfl⟩ : syracuseStep 6849137 = 5136853) B5136853
theorem B7316081 : Blo 1603000 7316081 := bstep (se 2 (by rfl) ⟨2743530, by rfl⟩ : syracuseStep 7316081 = 5487061) B5487061
theorem B3424945 : Blo 1603000 3424945 := bstep (se 2 (by rfl) ⟨1284354, by rfl⟩ : syracuseStep 3424945 = 2568709) B2568709
theorem B5014307 : Blo 1603000 5014307 := bstep (se 1 (by rfl) ⟨3760730, by rfl⟩ : syracuseStep 5014307 = 7521461) B7521461
theorem B5415821 : Blo 1603000 5415821 := bstep (se 3 (by rfl) ⟨1015466, by rfl⟩ : syracuseStep 5415821 = 2030933) B2030933
theorem B5784497 : Blo 1603000 5784497 := bstep (se 2 (by rfl) ⟨2169186, by rfl⟩ : syracuseStep 5784497 = 4338373) B4338373
theorem B5415875 : Blo 1603000 5415875 := bstep (se 1 (by rfl) ⟨4061906, by rfl⟩ : syracuseStep 5415875 = 8123813) B8123813
theorem B6087757 : Blo 1603000 6087757 := bstep (se 3 (by rfl) ⟨1141454, by rfl⟩ : syracuseStep 6087757 = 2282909) B2282909
theorem B1803379 : Blo 1603000 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B17343629 : Blo 1603000 17343629 := bstep (se 3 (by rfl) ⟨3251930, by rfl⟩ : syracuseStep 17343629 = 6503861) B6503861
theorem B9135281 : Blo 1603000 9135281 := bstep (se 2 (by rfl) ⟨3425730, by rfl⟩ : syracuseStep 9135281 = 6851461) B6851461
theorem B5416145 : Blo 1603000 5416145 := bstep (se 2 (by rfl) ⟨2031054, by rfl⟩ : syracuseStep 5416145 = 4062109) B4062109
theorem B1828099 : Blo 1603000 1828099 := bstep (se 1 (by rfl) ⟨1371074, by rfl⟩ : syracuseStep 1828099 = 2742149) B2742149
theorem B1803523 : Blo 1603000 1803523 := bstep (se 1 (by rfl) ⟨1352642, by rfl⟩ : syracuseStep 1803523 = 2705285) B2705285
theorem B6849805 : Blo 1603000 6849805 := bstep (se 3 (by rfl) ⟨1284338, by rfl⟩ : syracuseStep 6849805 = 2568677) B2568677
theorem B8119601 : Blo 1603000 8119601 := bstep (se 2 (by rfl) ⟨3044850, by rfl⟩ : syracuseStep 8119601 = 6089701) B6089701
theorem B1803667 : Blo 1603000 1803667 := bstep (se 1 (by rfl) ⟨1352750, by rfl⟩ : syracuseStep 1803667 = 2705501) B2705501
theorem B19506673 : Blo 1603000 19506673 := bstep (se 2 (by rfl) ⟨7315002, by rfl⟩ : syracuseStep 19506673 = 14630005) B14630005
theorem B1803811 : Blo 1603000 1803811 := bstep (se 1 (by rfl) ⟨1352858, by rfl⟩ : syracuseStep 1803811 = 2705717) B2705717
theorem B4171331 : Blo 1603000 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B5138083 : Blo 1603000 5138083 := bstep (se 1 (by rfl) ⟨3853562, by rfl⟩ : syracuseStep 5138083 = 7707125) B7707125
theorem B1803955 : Blo 1603000 1803955 := bstep (se 1 (by rfl) ⟨1352966, by rfl⟩ : syracuseStep 1803955 = 2705933) B2705933
theorem B2705089 : Blo 1603000 2705089 := bstep (se 2 (by rfl) ⟨1014408, by rfl⟩ : syracuseStep 2705089 = 2028817) B2028817
theorem B2705123 : Blo 1603000 2705123 := bstep (se 1 (by rfl) ⟨2028842, by rfl⟩ : syracuseStep 2705123 = 4057685) B4057685
theorem B5490413 : Blo 1603000 5490413 := bstep (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) B2058905
theorem B5416685 : Blo 1603000 5416685 := bstep (se 3 (by rfl) ⟨1015628, by rfl⟩ : syracuseStep 5416685 = 2031257) B2031257
theorem B7923491 : Blo 1603000 7923491 := bstep (se 1 (by rfl) ⟨5942618, by rfl⟩ : syracuseStep 7923491 = 11885237) B11885237
theorem B5416739 : Blo 1603000 5416739 := bstep (se 1 (by rfl) ⟨4062554, by rfl⟩ : syracuseStep 5416739 = 8125109) B8125109
theorem B1804099 : Blo 1603000 1804099 := bstep (se 1 (by rfl) ⟨1353074, by rfl⟩ : syracuseStep 1804099 = 2706149) B2706149
theorem B6850403 : Blo 1603000 6850403 := bstep (se 1 (by rfl) ⟨5137802, by rfl⟩ : syracuseStep 6850403 = 10275605) B10275605
theorem B2705251 : Blo 1603000 2705251 := bstep (se 1 (by rfl) ⟨2028938, by rfl⟩ : syracuseStep 2705251 = 4057877) B4057877
theorem B6088547 : Blo 1603000 6088547 := bstep (se 1 (by rfl) ⟨4566410, by rfl⟩ : syracuseStep 6088547 = 9132821) B9132821
theorem B17352629 : Blo 1603000 17352629 := bstep (se 5 (by rfl) ⟨813404, by rfl⟩ : syracuseStep 17352629 = 1626809) B1626809
theorem B1804243 : Blo 1603000 1804243 := bstep (se 1 (by rfl) ⟨1353182, by rfl⟩ : syracuseStep 1804243 = 2706365) B2706365
theorem B2705393 : Blo 1603000 2705393 := bstep (se 2 (by rfl) ⟨1014522, by rfl⟩ : syracuseStep 2705393 = 2029045) B2029045
theorem B5138417 : Blo 1603000 5138417 := bstep (se 2 (by rfl) ⟨1926906, by rfl⟩ : syracuseStep 5138417 = 3853813) B3853813
theorem B21940237 : Blo 1603000 21940237 := bstep (se 3 (by rfl) ⟨4113794, by rfl⟩ : syracuseStep 21940237 = 8227589) B8227589
theorem B41084981 : Blo 1603000 41084981 := bstep (se 5 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 41084981 = 3851717) B3851717
theorem B1804387 : Blo 1603000 1804387 := bstep (se 1 (by rfl) ⟨1353290, by rfl⟩ : syracuseStep 1804387 = 2706581) B2706581
theorem B2705521 : Blo 1603000 2705521 := bstep (se 2 (by rfl) ⟨1014570, by rfl⟩ : syracuseStep 2705521 = 2029141) B2029141
theorem B2705555 : Blo 1603000 2705555 := bstep (se 1 (by rfl) ⟨2029166, by rfl⟩ : syracuseStep 2705555 = 4058333) B4058333
theorem B1804531 : Blo 1603000 1804531 := bstep (se 1 (by rfl) ⟨1353398, by rfl⟩ : syracuseStep 1804531 = 2706797) B2706797
theorem B4565261 : Blo 1603000 4565261 := bstep (se 3 (by rfl) ⟨855986, by rfl⟩ : syracuseStep 4565261 = 1711973) B1711973
theorem B2705683 : Blo 1603000 2705683 := bstep (se 1 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 2705683 = 4058525) B4058525
theorem B30820661 : Blo 1603000 30820661 := bstep (se 5 (by rfl) ⟨1444718, by rfl⟩ : syracuseStep 30820661 = 2889437) B2889437
theorem B1853779 : Blo 1603000 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B1804675 : Blo 1603000 1804675 := bstep (se 1 (by rfl) ⟨1353506, by rfl⟩ : syracuseStep 1804675 = 2707013) B2707013
theorem B12175757 : Blo 1603000 12175757 := bstep (se 3 (by rfl) ⟨2282954, by rfl⟩ : syracuseStep 12175757 = 4565909) B4565909
theorem B3606929 : Blo 1603000 3606929 := bstep (se 2 (by rfl) ⟨1352598, by rfl⟩ : syracuseStep 3606929 = 2705197) B2705197
theorem B2705825 : Blo 1603000 2705825 := bstep (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) B2029369
theorem B3606947 : Blo 1603000 3606947 := bstep (se 1 (by rfl) ⟨2705210, by rfl⟩ : syracuseStep 3606947 = 5410421) B5410421
theorem B4565443 : Blo 1603000 4565443 := bstep (se 1 (by rfl) ⟨3424082, by rfl⟩ : syracuseStep 4565443 = 6848165) B6848165
theorem B16452067 : Blo 1603000 16452067 := bstep (se 1 (by rfl) ⟨12339050, by rfl⟩ : syracuseStep 16452067 = 24678101) B24678101
theorem B6089201 : Blo 1603000 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B16460273 : Blo 1603000 16460273 := bstep (se 2 (by rfl) ⟨6172602, by rfl⟩ : syracuseStep 16460273 = 12345205) B12345205
theorem B1804819 : Blo 1603000 1804819 := bstep (se 1 (by rfl) ⟨1353614, by rfl⟩ : syracuseStep 1804819 = 2707229) B2707229
theorem B2705953 : Blo 1603000 2705953 := bstep (se 2 (by rfl) ⟨1014732, by rfl⟩ : syracuseStep 2705953 = 2029465) B2029465
theorem B8784433 : Blo 1603000 8784433 := bstep (se 2 (by rfl) ⟨3294162, by rfl⟩ : syracuseStep 8784433 = 6588325) B6588325
theorem B2705987 : Blo 1603000 2705987 := bstep (se 1 (by rfl) ⟨2029490, by rfl⟩ : syracuseStep 2705987 = 4058981) B4058981
theorem B9136739 : Blo 1603000 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B38578801 : Blo 1603000 38578801 := bstep (se 2 (by rfl) ⟨14467050, by rfl⟩ : syracuseStep 38578801 = 28934101) B28934101
theorem B8227469 : Blo 1603000 8227469 := bstep (se 3 (by rfl) ⟨1542650, by rfl⟩ : syracuseStep 8227469 = 3085301) B3085301
theorem B3426961 : Blo 1603000 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B1804963 : Blo 1603000 1804963 := bstep (se 1 (by rfl) ⟨1353722, by rfl⟩ : syracuseStep 1804963 = 2707445) B2707445
theorem B3607217 : Blo 1603000 3607217 := bstep (se 2 (by rfl) ⟨1352706, by rfl⟩ : syracuseStep 3607217 = 2705413) B2705413
theorem B3607235 : Blo 1603000 3607235 := bstep (se 1 (by rfl) ⟨2705426, by rfl⟩ : syracuseStep 3607235 = 5410853) B5410853
theorem B2706115 : Blo 1603000 2706115 := bstep (se 1 (by rfl) ⟨2029586, by rfl⟩ : syracuseStep 2706115 = 4059173) B4059173
theorem B8121059 : Blo 1603000 8121059 := bstep (se 1 (by rfl) ⟨6090794, by rfl⟩ : syracuseStep 8121059 = 12181589) B12181589
theorem B1805107 : Blo 1603000 1805107 := bstep (se 1 (by rfl) ⟨1353830, by rfl⟩ : syracuseStep 1805107 = 2707661) B2707661
theorem B2706257 : Blo 1603000 2706257 := bstep (se 2 (by rfl) ⟨1014846, by rfl⟩ : syracuseStep 2706257 = 2029693) B2029693
theorem B4565933 : Blo 1603000 4565933 := bstep (se 3 (by rfl) ⟨856112, by rfl⟩ : syracuseStep 4565933 = 1712225) B1712225
theorem B1805251 : Blo 1603000 1805251 := bstep (se 1 (by rfl) ⟨1353938, by rfl⟩ : syracuseStep 1805251 = 2707877) B2707877
theorem B9759685 : Blo 1603000 9759685 := bstep (se 4 (by rfl) ⟨914970, by rfl⟩ : syracuseStep 9759685 = 1829941) B1829941
theorem B3607505 : Blo 1603000 3607505 := bstep (se 2 (by rfl) ⟨1352814, by rfl⟩ : syracuseStep 3607505 = 2705629) B2705629
theorem B2706385 : Blo 1603000 2706385 := bstep (se 2 (by rfl) ⟨1014894, by rfl⟩ : syracuseStep 2706385 = 2029789) B2029789
theorem B3607523 : Blo 1603000 3607523 := bstep (se 1 (by rfl) ⟨2705642, by rfl⟩ : syracuseStep 3607523 = 5411285) B5411285
theorem B15420401 : Blo 1603000 15420401 := bstep (se 2 (by rfl) ⟨5782650, by rfl⟩ : syracuseStep 15420401 = 11565301) B11565301
theorem B2706419 : Blo 1603000 2706419 := bstep (se 1 (by rfl) ⟨2029814, by rfl⟩ : syracuseStep 2706419 = 4059629) B4059629
theorem B3427363 : Blo 1603000 3427363 := bstep (se 1 (by rfl) ⟨2570522, by rfl⟩ : syracuseStep 3427363 = 5141045) B5141045
theorem B1805395 : Blo 1603000 1805395 := bstep (se 1 (by rfl) ⟨1354046, by rfl⟩ : syracuseStep 1805395 = 2708093) B2708093
theorem B2706547 : Blo 1603000 2706547 := bstep (se 1 (by rfl) ⟨2029910, by rfl⟩ : syracuseStep 2706547 = 4059821) B4059821
theorem B1805539 : Blo 1603000 1805539 := bstep (se 1 (by rfl) ⟨1354154, by rfl⟩ : syracuseStep 1805539 = 2708309) B2708309
theorem B3607793 : Blo 1603000 3607793 := bstep (se 2 (by rfl) ⟨1352922, by rfl⟩ : syracuseStep 3607793 = 2705845) B2705845
theorem B2706689 : Blo 1603000 2706689 := bstep (se 2 (by rfl) ⟨1015008, by rfl⟩ : syracuseStep 2706689 = 2030017) B2030017
theorem B3607811 : Blo 1603000 3607811 := bstep (se 1 (by rfl) ⟨2705858, by rfl⟩ : syracuseStep 3607811 = 5411717) B5411717
theorem B10276145 : Blo 1603000 10276145 := bstep (se 2 (by rfl) ⟨3853554, by rfl⟩ : syracuseStep 10276145 = 7707109) B7707109
theorem B2706817 : Blo 1603000 2706817 := bstep (se 2 (by rfl) ⟨1015056, by rfl⟩ : syracuseStep 2706817 = 2030113) B2030113
theorem B2706851 : Blo 1603000 2706851 := bstep (se 1 (by rfl) ⟨2030138, by rfl⟩ : syracuseStep 2706851 = 4060277) B4060277
theorem B4058545 : Blo 1603000 4058545 := bstep (se 2 (by rfl) ⟨1521954, by rfl⟩ : syracuseStep 4058545 = 3043909) B3043909
theorem B20557253 : Blo 1603000 20557253 := bstep (se 4 (by rfl) ⟨1927242, by rfl⟩ : syracuseStep 20557253 = 3854485) B3854485
theorem B8121869 : Blo 1603000 8121869 := bstep (se 3 (by rfl) ⟨1522850, by rfl⟩ : syracuseStep 8121869 = 3045701) B3045701
theorem B3608081 : Blo 1603000 3608081 := bstep (se 2 (by rfl) ⟨1353030, by rfl⟩ : syracuseStep 3608081 = 2706061) B2706061
theorem B3608099 : Blo 1603000 3608099 := bstep (se 1 (by rfl) ⟨2706074, by rfl⟩ : syracuseStep 3608099 = 5412149) B5412149
theorem B2706979 : Blo 1603000 2706979 := bstep (se 1 (by rfl) ⟨2030234, by rfl⟩ : syracuseStep 2706979 = 4060469) B4060469
theorem B2567857 : Blo 1603000 2567857 := bstep (se 2 (by rfl) ⟨962946, by rfl⟩ : syracuseStep 2567857 = 1925893) B1925893
theorem B2707121 : Blo 1603000 2707121 := bstep (se 2 (by rfl) ⟨1015170, by rfl⟩ : syracuseStep 2707121 = 2030341) B2030341
theorem B4058819 : Blo 1603000 4058819 := bstep (se 1 (by rfl) ⟨3044114, by rfl⟩ : syracuseStep 4058819 = 6088229) B6088229
theorem B4116259 : Blo 1603000 4116259 := bstep (se 1 (by rfl) ⟨3087194, by rfl⟩ : syracuseStep 4116259 = 6174389) B6174389
theorem B3608369 : Blo 1603000 3608369 := bstep (se 2 (by rfl) ⟨1353138, by rfl⟩ : syracuseStep 3608369 = 2706277) B2706277
theorem B2707249 : Blo 1603000 2707249 := bstep (se 2 (by rfl) ⟨1015218, by rfl⟩ : syracuseStep 2707249 = 2030437) B2030437
theorem B2314051 : Blo 1603000 2314051 := bstep (se 1 (by rfl) ⟨1735538, by rfl⟩ : syracuseStep 2314051 = 3471077) B3471077
theorem B3608387 : Blo 1603000 3608387 := bstep (se 1 (by rfl) ⟨2706290, by rfl⟩ : syracuseStep 3608387 = 5412581) B5412581
theorem B5410637 : Blo 1603000 5410637 := bstep (se 3 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 5410637 = 2028989) B2028989
theorem B2707283 : Blo 1603000 2707283 := bstep (se 1 (by rfl) ⟨2030462, by rfl⟩ : syracuseStep 2707283 = 4060925) B4060925
theorem B5410691 : Blo 1603000 5410691 := bstep (se 1 (by rfl) ⟨4058018, by rfl⟩ : syracuseStep 5410691 = 8116037) B8116037
theorem B4059011 : Blo 1603000 4059011 := bstep (se 1 (by rfl) ⟨3044258, by rfl⟩ : syracuseStep 4059011 = 6088517) B6088517
theorem B6090659 : Blo 1603000 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B9129905 : Blo 1603000 9129905 := bstep (se 2 (by rfl) ⟨3423714, by rfl⟩ : syracuseStep 9129905 = 6847429) B6847429
theorem B6090673 : Blo 1603000 6090673 := bstep (se 2 (by rfl) ⟨2284002, by rfl⟩ : syracuseStep 6090673 = 4568005) B4568005
theorem B2707411 : Blo 1603000 2707411 := bstep (se 1 (by rfl) ⟨2030558, by rfl⟩ : syracuseStep 2707411 = 4061117) B4061117
theorem B5140493 : Blo 1603000 5140493 := bstep (se 3 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 5140493 = 1927685) B1927685
theorem B2166851 : Blo 1603000 2166851 := bstep (se 1 (by rfl) ⟨1625138, by rfl⟩ : syracuseStep 2166851 = 3250277) B3250277
theorem B4567117 : Blo 1603000 4567117 := bstep (se 3 (by rfl) ⟨856334, by rfl⟩ : syracuseStep 4567117 = 1712669) B1712669
theorem B3608657 : Blo 1603000 3608657 := bstep (se 2 (by rfl) ⟨1353246, by rfl⟩ : syracuseStep 3608657 = 2706493) B2706493
theorem B2707553 : Blo 1603000 2707553 := bstep (se 2 (by rfl) ⟨1015332, by rfl⟩ : syracuseStep 2707553 = 2030665) B2030665
theorem B3608675 : Blo 1603000 3608675 := bstep (se 1 (by rfl) ⟨2706506, by rfl⟩ : syracuseStep 3608675 = 5413013) B5413013
theorem B5410961 : Blo 1603000 5410961 := bstep (se 2 (by rfl) ⟨2029110, by rfl⟩ : syracuseStep 5410961 = 4058221) B4058221
theorem B2404529 : Blo 1603000 2404529 := bstep (se 2 (by rfl) ⟨901698, by rfl⟩ : syracuseStep 2404529 = 1803397) B1803397
theorem B2404547 : Blo 1603000 2404547 := bstep (se 1 (by rfl) ⟨1803410, by rfl⟩ : syracuseStep 2404547 = 3606821) B3606821
theorem B9752773 : Blo 1603000 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B2404577 : Blo 1603000 2404577 := bstep (se 2 (by rfl) ⟨901716, by rfl⟩ : syracuseStep 2404577 = 1803433) B1803433
theorem B2707681 : Blo 1603000 2707681 := bstep (se 2 (by rfl) ⟨1015380, by rfl⟩ : syracuseStep 2707681 = 2030761) B2030761
theorem B2404595 : Blo 1603000 2404595 := bstep (se 1 (by rfl) ⟨1803446, by rfl⟩ : syracuseStep 2404595 = 3606893) B3606893
theorem B2707715 : Blo 1603000 2707715 := bstep (se 1 (by rfl) ⟨2030786, by rfl⟩ : syracuseStep 2707715 = 4061573) B4061573
theorem B2404625 : Blo 1603000 2404625 := bstep (se 2 (by rfl) ⟨901734, by rfl⟩ : syracuseStep 2404625 = 1803469) B1803469
theorem B2404643 : Blo 1603000 2404643 := bstep (se 1 (by rfl) ⟨1803482, by rfl⟩ : syracuseStep 2404643 = 3606965) B3606965
theorem B2404673 : Blo 1603000 2404673 := bstep (se 2 (by rfl) ⟨901752, by rfl⟩ : syracuseStep 2404673 = 1803505) B1803505
theorem B3043651 : Blo 1603000 3043651 := bstep (se 1 (by rfl) ⟨2282738, by rfl⟩ : syracuseStep 3043651 = 4565477) B4565477
theorem B2568529 : Blo 1603000 2568529 := bstep (se 2 (by rfl) ⟨963198, by rfl⟩ : syracuseStep 2568529 = 1926397) B1926397
theorem B2404691 : Blo 1603000 2404691 := bstep (se 1 (by rfl) ⟨1803518, by rfl⟩ : syracuseStep 2404691 = 3607037) B3607037
theorem B2437489 : Blo 1603000 2437489 := bstep (se 2 (by rfl) ⟨914058, by rfl⟩ : syracuseStep 2437489 = 1828117) B1828117
theorem B2404721 : Blo 1603000 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B3608945 : Blo 1603000 3608945 := bstep (se 2 (by rfl) ⟨1353354, by rfl⟩ : syracuseStep 3608945 = 2706709) B2706709
theorem B2404739 : Blo 1603000 2404739 := bstep (se 1 (by rfl) ⟨1803554, by rfl⟩ : syracuseStep 2404739 = 3607109) B3607109
theorem B3608963 : Blo 1603000 3608963 := bstep (se 1 (by rfl) ⟨2706722, by rfl⟩ : syracuseStep 3608963 = 5413445) B5413445
theorem B2707843 : Blo 1603000 2707843 := bstep (se 1 (by rfl) ⟨2030882, by rfl⟩ : syracuseStep 2707843 = 4061765) B4061765
theorem B2404769 : Blo 1603000 2404769 := bstep (se 2 (by rfl) ⟨901788, by rfl⟩ : syracuseStep 2404769 = 1803577) B1803577
theorem B2404787 : Blo 1603000 2404787 := bstep (se 1 (by rfl) ⟨1803590, by rfl⟩ : syracuseStep 2404787 = 3607181) B3607181
theorem B2404817 : Blo 1603000 2404817 := bstep (se 2 (by rfl) ⟨901806, by rfl⟩ : syracuseStep 2404817 = 1803613) B1803613
theorem B2404835 : Blo 1603000 2404835 := bstep (se 1 (by rfl) ⟨1803626, by rfl⟩ : syracuseStep 2404835 = 3607253) B3607253
theorem B3043811 : Blo 1603000 3043811 := bstep (se 1 (by rfl) ⟨2282858, by rfl⟩ : syracuseStep 3043811 = 4565717) B4565717
theorem B2404865 : Blo 1603000 2404865 := bstep (se 2 (by rfl) ⟨901824, by rfl⟩ : syracuseStep 2404865 = 1803649) B1803649
theorem B2707985 : Blo 1603000 2707985 := bstep (se 2 (by rfl) ⟨1015494, by rfl⟩ : syracuseStep 2707985 = 2030989) B2030989
theorem B2404883 : Blo 1603000 2404883 := bstep (se 1 (by rfl) ⟨1803662, by rfl⟩ : syracuseStep 2404883 = 3607325) B3607325
theorem B2404913 : Blo 1603000 2404913 := bstep (se 2 (by rfl) ⟨901842, by rfl⟩ : syracuseStep 2404913 = 1803685) B1803685
theorem B2404931 : Blo 1603000 2404931 := bstep (se 1 (by rfl) ⟨1803698, by rfl⟩ : syracuseStep 2404931 = 3607397) B3607397
theorem B4117073 : Blo 1603000 4117073 := bstep (se 2 (by rfl) ⟨1543902, by rfl⟩ : syracuseStep 4117073 = 3087805) B3087805
theorem B2404961 : Blo 1603000 2404961 := bstep (se 2 (by rfl) ⟨901860, by rfl⟩ : syracuseStep 2404961 = 1803721) B1803721
theorem B3854947 : Blo 1603000 3854947 := bstep (se 1 (by rfl) ⟨2891210, by rfl⟩ : syracuseStep 3854947 = 5782421) B5782421
theorem B2404979 : Blo 1603000 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B11563661 : Blo 1603000 11563661 := bstep (se 3 (by rfl) ⟨2168186, by rfl⟩ : syracuseStep 11563661 = 4336373) B4336373
theorem B2405009 : Blo 1603000 2405009 := bstep (se 2 (by rfl) ⟨901878, by rfl⟩ : syracuseStep 2405009 = 1803757) B1803757
theorem B3609233 : Blo 1603000 3609233 := bstep (se 2 (by rfl) ⟨1353462, by rfl⟩ : syracuseStep 3609233 = 2706925) B2706925
theorem B2708113 : Blo 1603000 2708113 := bstep (se 2 (by rfl) ⟨1015542, by rfl⟩ : syracuseStep 2708113 = 2031085) B2031085
theorem B2405027 : Blo 1603000 2405027 := bstep (se 1 (by rfl) ⟨1803770, by rfl⟩ : syracuseStep 2405027 = 3607541) B3607541
theorem B3609251 : Blo 1603000 3609251 := bstep (se 1 (by rfl) ⟨2706938, by rfl⟩ : syracuseStep 3609251 = 5413877) B5413877
theorem B5411501 : Blo 1603000 5411501 := bstep (se 3 (by rfl) ⟨1014656, by rfl⟩ : syracuseStep 5411501 = 2029313) B2029313
theorem B2708147 : Blo 1603000 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B2405057 : Blo 1603000 2405057 := bstep (se 2 (by rfl) ⟨901896, by rfl⟩ : syracuseStep 2405057 = 1803793) B1803793
theorem B3855043 : Blo 1603000 3855043 := bstep (se 1 (by rfl) ⟨2891282, by rfl⟩ : syracuseStep 3855043 = 5782565) B5782565
theorem B5780173 : Blo 1603000 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B2405075 : Blo 1603000 2405075 := bstep (se 1 (by rfl) ⟨1803806, by rfl⟩ : syracuseStep 2405075 = 3607613) B3607613
theorem B5411555 : Blo 1603000 5411555 := bstep (se 1 (by rfl) ⟨4058666, by rfl⟩ : syracuseStep 5411555 = 8117333) B8117333
theorem B10277603 : Blo 1603000 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B2405105 : Blo 1603000 2405105 := bstep (se 2 (by rfl) ⟨901914, by rfl⟩ : syracuseStep 2405105 = 1803829) B1803829
theorem B3519217 : Blo 1603000 3519217 := bstep (se 2 (by rfl) ⟨1319706, by rfl⟩ : syracuseStep 3519217 = 2639413) B2639413
theorem B2405123 : Blo 1603000 2405123 := bstep (se 1 (by rfl) ⟨1803842, by rfl⟩ : syracuseStep 2405123 = 3607685) B3607685
theorem B2405153 : Blo 1603000 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B4059953 : Blo 1603000 4059953 := bstep (se 2 (by rfl) ⟨1522482, by rfl⟩ : syracuseStep 4059953 = 3044965) B3044965
theorem B2405171 : Blo 1603000 2405171 := bstep (se 1 (by rfl) ⟨1803878, by rfl⟩ : syracuseStep 2405171 = 3607757) B3607757
theorem B2708275 : Blo 1603000 2708275 := bstep (se 1 (by rfl) ⟨2031206, by rfl⟩ : syracuseStep 2708275 = 4062413) B4062413
theorem B2405201 : Blo 1603000 2405201 := bstep (se 2 (by rfl) ⟨901950, by rfl⟩ : syracuseStep 2405201 = 1803901) B1803901
theorem B2405219 : Blo 1603000 2405219 := bstep (se 1 (by rfl) ⟨1803914, by rfl⟩ : syracuseStep 2405219 = 3607829) B3607829
theorem B4060003 : Blo 1603000 4060003 := bstep (se 1 (by rfl) ⟨3045002, by rfl⟩ : syracuseStep 4060003 = 6090005) B6090005
theorem B2405249 : Blo 1603000 2405249 := bstep (se 2 (by rfl) ⟨901968, by rfl⟩ : syracuseStep 2405249 = 1803937) B1803937
theorem B2405267 : Blo 1603000 2405267 := bstep (se 1 (by rfl) ⟨1803950, by rfl⟩ : syracuseStep 2405267 = 3607901) B3607901
theorem B2405297 : Blo 1603000 2405297 := bstep (se 2 (by rfl) ⟨901986, by rfl⟩ : syracuseStep 2405297 = 1803973) B1803973
theorem B3609521 : Blo 1603000 3609521 := bstep (se 2 (by rfl) ⟨1353570, by rfl⟩ : syracuseStep 3609521 = 2707141) B2707141
theorem B2708417 : Blo 1603000 2708417 := bstep (se 2 (by rfl) ⟨1015656, by rfl⟩ : syracuseStep 2708417 = 2031313) B2031313
theorem B2405315 : Blo 1603000 2405315 := bstep (se 1 (by rfl) ⟨1803986, by rfl⟩ : syracuseStep 2405315 = 3607973) B3607973
theorem B3609539 : Blo 1603000 3609539 := bstep (se 1 (by rfl) ⟨2707154, by rfl⟩ : syracuseStep 3609539 = 5414309) B5414309
theorem B2282465 : Blo 1603000 2282465 := bstep (se 2 (by rfl) ⟨855924, by rfl⟩ : syracuseStep 2282465 = 1711849) B1711849
theorem B2405345 : Blo 1603000 2405345 := bstep (se 2 (by rfl) ⟨902004, by rfl⟩ : syracuseStep 2405345 = 1804009) B1804009
theorem B5411825 : Blo 1603000 5411825 := bstep (se 2 (by rfl) ⟨2029434, by rfl⟩ : syracuseStep 5411825 = 4058869) B4058869
theorem B4060145 : Blo 1603000 4060145 := bstep (se 2 (by rfl) ⟨1522554, by rfl⟩ : syracuseStep 4060145 = 3045109) B3045109
theorem B2405363 : Blo 1603000 2405363 := bstep (se 1 (by rfl) ⟨1804022, by rfl⟩ : syracuseStep 2405363 = 3608045) B3608045
theorem B2405393 : Blo 1603000 2405393 := bstep (se 2 (by rfl) ⟨902022, by rfl⟩ : syracuseStep 2405393 = 1804045) B1804045
theorem B2167841 : Blo 1603000 2167841 := bstep (se 2 (by rfl) ⟨812940, by rfl⟩ : syracuseStep 2167841 = 1625881) B1625881
theorem B2405411 : Blo 1603000 2405411 := bstep (se 1 (by rfl) ⟨1804058, by rfl⟩ : syracuseStep 2405411 = 3608117) B3608117
theorem B2405441 : Blo 1603000 2405441 := bstep (se 2 (by rfl) ⟨902040, by rfl⟩ : syracuseStep 2405441 = 1804081) B1804081
theorem B2405459 : Blo 1603000 2405459 := bstep (se 1 (by rfl) ⟨1804094, by rfl⟩ : syracuseStep 2405459 = 3608189) B3608189
theorem B2405489 : Blo 1603000 2405489 := bstep (se 2 (by rfl) ⟨902058, by rfl⟩ : syracuseStep 2405489 = 1804117) B1804117
theorem B4568177 : Blo 1603000 4568177 := bstep (se 2 (by rfl) ⟨1713066, by rfl⟩ : syracuseStep 4568177 = 3426133) B3426133
theorem B2405507 : Blo 1603000 2405507 := bstep (se 1 (by rfl) ⟨1804130, by rfl⟩ : syracuseStep 2405507 = 3608261) B3608261
theorem B2405537 : Blo 1603000 2405537 := bstep (se 2 (by rfl) ⟨902076, by rfl⟩ : syracuseStep 2405537 = 1804153) B1804153
theorem B2405555 : Blo 1603000 2405555 := bstep (se 1 (by rfl) ⟨1804166, by rfl⟩ : syracuseStep 2405555 = 3608333) B3608333
theorem B2438353 : Blo 1603000 2438353 := bstep (se 2 (by rfl) ⟨914382, by rfl⟩ : syracuseStep 2438353 = 1828765) B1828765
theorem B2405585 : Blo 1603000 2405585 := bstep (se 2 (by rfl) ⟨902094, by rfl⟩ : syracuseStep 2405585 = 1804189) B1804189
theorem B3609809 : Blo 1603000 3609809 := bstep (se 2 (by rfl) ⟨1353678, by rfl⟩ : syracuseStep 3609809 = 2707357) B2707357
theorem B2405603 : Blo 1603000 2405603 := bstep (se 1 (by rfl) ⟨1804202, by rfl⟩ : syracuseStep 2405603 = 3608405) B3608405
theorem B3609827 : Blo 1603000 3609827 := bstep (se 1 (by rfl) ⟨2707370, by rfl⟩ : syracuseStep 3609827 = 5414741) B5414741
theorem B12178673 : Blo 1603000 12178673 := bstep (se 2 (by rfl) ⟨4567002, by rfl⟩ : syracuseStep 12178673 = 9134005) B9134005
theorem B2405633 : Blo 1603000 2405633 := bstep (se 2 (by rfl) ⟨902112, by rfl⟩ : syracuseStep 2405633 = 1804225) B1804225
theorem B2405651 : Blo 1603000 2405651 := bstep (se 1 (by rfl) ⟨1804238, by rfl⟩ : syracuseStep 2405651 = 3608477) B3608477
theorem B2405681 : Blo 1603000 2405681 := bstep (se 2 (by rfl) ⟨902130, by rfl⟩ : syracuseStep 2405681 = 1804261) B1804261
theorem B31266101 : Blo 1603000 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B2405699 : Blo 1603000 2405699 := bstep (se 1 (by rfl) ⟨1804274, by rfl⟩ : syracuseStep 2405699 = 3608549) B3608549
theorem B2028883 : Blo 1603000 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B2405729 : Blo 1603000 2405729 := bstep (se 2 (by rfl) ⟨902148, by rfl⟩ : syracuseStep 2405729 = 1804297) B1804297
theorem B9131363 : Blo 1603000 9131363 := bstep (se 1 (by rfl) ⟨6848522, by rfl⟩ : syracuseStep 9131363 = 13697045) B13697045
theorem B3659107 : Blo 1603000 3659107 := bstep (se 1 (by rfl) ⟨2744330, by rfl⟩ : syracuseStep 3659107 = 5488661) B5488661
theorem B6092131 : Blo 1603000 6092131 := bstep (se 1 (by rfl) ⟨4569098, by rfl⟩ : syracuseStep 6092131 = 9138197) B9138197
theorem B2405747 : Blo 1603000 2405747 := bstep (se 1 (by rfl) ⟨1804310, by rfl⟩ : syracuseStep 2405747 = 3608621) B3608621
theorem B15422861 : Blo 1603000 15422861 := bstep (se 3 (by rfl) ⟨2891786, by rfl⟩ : syracuseStep 15422861 = 5783573) B5783573
theorem B2405777 : Blo 1603000 2405777 := bstep (se 2 (by rfl) ⟨902166, by rfl⟩ : syracuseStep 2405777 = 1804333) B1804333
theorem B2569619 : Blo 1603000 2569619 := bstep (se 1 (by rfl) ⟨1927214, by rfl⟩ : syracuseStep 2569619 = 3854429) B3854429
theorem B2405795 : Blo 1603000 2405795 := bstep (se 1 (by rfl) ⟨1804346, by rfl⟩ : syracuseStep 2405795 = 3608693) B3608693
theorem B2028979 : Blo 1603000 2028979 := bstep (se 1 (by rfl) ⟨1521734, by rfl⟩ : syracuseStep 2028979 = 3043469) B3043469
theorem B2405825 : Blo 1603000 2405825 := bstep (se 2 (by rfl) ⟨902184, by rfl⟩ : syracuseStep 2405825 = 1804369) B1804369
theorem B2168257 : Blo 1603000 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B1603011 : Blo 1603000 1603011 := bstep (se 1 (by rfl) ⟨1202258, by rfl⟩ : syracuseStep 1603011 = 2404517) B2404517
theorem B1603027 : Blo 1603000 1603027 := bstep (se 1 (by rfl) ⟨1202270, by rfl⟩ : syracuseStep 1603027 = 2404541) B2404541
theorem B2405843 : Blo 1603000 2405843 := bstep (se 1 (by rfl) ⟨1804382, by rfl⟩ : syracuseStep 2405843 = 3608765) B3608765
theorem B1603043 : Blo 1603000 1603043 := bstep (se 1 (by rfl) ⟨1202282, by rfl⟩ : syracuseStep 1603043 = 2404565) B2404565
theorem B2405873 : Blo 1603000 2405873 := bstep (se 2 (by rfl) ⟨902202, by rfl⟩ : syracuseStep 2405873 = 1804405) B1804405
theorem B3610097 : Blo 1603000 3610097 := bstep (se 2 (by rfl) ⟨1353786, by rfl⟩ : syracuseStep 3610097 = 2707573) B2707573
theorem B1603059 : Blo 1603000 1603059 := bstep (se 1 (by rfl) ⟨1202294, by rfl⟩ : syracuseStep 1603059 = 2404589) B2404589
theorem B2282995 : Blo 1603000 2282995 := bstep (se 1 (by rfl) ⟨1712246, by rfl⟩ : syracuseStep 2282995 = 3424493) B3424493
theorem B2168321 : Blo 1603000 2168321 := bstep (se 2 (by rfl) ⟨813120, by rfl⟩ : syracuseStep 2168321 = 1626241) B1626241
theorem B1603075 : Blo 1603000 1603075 := bstep (se 1 (by rfl) ⟨1202306, by rfl⟩ : syracuseStep 1603075 = 2404613) B2404613
theorem B2405891 : Blo 1603000 2405891 := bstep (se 1 (by rfl) ⟨1804418, by rfl⟩ : syracuseStep 2405891 = 3608837) B3608837
theorem B3610115 : Blo 1603000 3610115 := bstep (se 1 (by rfl) ⟨2707586, by rfl⟩ : syracuseStep 3610115 = 5415173) B5415173
theorem B5412365 : Blo 1603000 5412365 := bstep (se 3 (by rfl) ⟨1014818, by rfl⟩ : syracuseStep 5412365 = 2029637) B2029637
theorem B3044881 : Blo 1603000 3044881 := bstep (se 2 (by rfl) ⟨1141830, by rfl⟩ : syracuseStep 3044881 = 2283661) B2283661
theorem B1603091 : Blo 1603000 1603091 := bstep (se 1 (by rfl) ⟨1202318, by rfl⟩ : syracuseStep 1603091 = 2404637) B2404637
theorem B2405921 : Blo 1603000 2405921 := bstep (se 2 (by rfl) ⟨902220, by rfl⟩ : syracuseStep 2405921 = 1804441) B1804441
theorem B1603107 : Blo 1603000 1603107 := bstep (se 1 (by rfl) ⟨1202330, by rfl⟩ : syracuseStep 1603107 = 2404661) B2404661
theorem B6854179 : Blo 1603000 6854179 := bstep (se 1 (by rfl) ⟨5140634, by rfl⟩ : syracuseStep 6854179 = 10281269) B10281269
theorem B6346289 : Blo 1603000 6346289 := bstep (se 2 (by rfl) ⟨2379858, by rfl⟩ : syracuseStep 6346289 = 4759717) B4759717
theorem B1603123 : Blo 1603000 1603123 := bstep (se 1 (by rfl) ⟨1202342, by rfl⟩ : syracuseStep 1603123 = 2404685) B2404685
theorem B2405939 : Blo 1603000 2405939 := bstep (se 1 (by rfl) ⟨1804454, by rfl⟩ : syracuseStep 2405939 = 3608909) B3608909
theorem B1603139 : Blo 1603000 1603139 := bstep (se 1 (by rfl) ⟨1202354, by rfl⟩ : syracuseStep 1603139 = 2404709) B2404709
theorem B5412419 : Blo 1603000 5412419 := bstep (se 1 (by rfl) ⟨4059314, by rfl⟩ : syracuseStep 5412419 = 8118629) B8118629
theorem B2405969 : Blo 1603000 2405969 := bstep (se 2 (by rfl) ⟨902238, by rfl⟩ : syracuseStep 2405969 = 1804477) B1804477
theorem B1603155 : Blo 1603000 1603155 := bstep (se 1 (by rfl) ⟨1202366, by rfl⟩ : syracuseStep 1603155 = 2404733) B2404733
theorem B1603171 : Blo 1603000 1603171 := bstep (se 1 (by rfl) ⟨1202378, by rfl⟩ : syracuseStep 1603171 = 2404757) B2404757
theorem B2405987 : Blo 1603000 2405987 := bstep (se 1 (by rfl) ⟨1804490, by rfl⟩ : syracuseStep 2405987 = 3608981) B3608981
theorem B1758835 : Blo 1603000 1758835 := bstep (se 1 (by rfl) ⟨1319126, by rfl⟩ : syracuseStep 1758835 = 2638253) B2638253
theorem B1603187 : Blo 1603000 1603187 := bstep (se 1 (by rfl) ⟨1202390, by rfl⟩ : syracuseStep 1603187 = 2404781) B2404781
theorem B2406017 : Blo 1603000 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B1603203 : Blo 1603000 1603203 := bstep (se 1 (by rfl) ⟨1202402, by rfl⟩ : syracuseStep 1603203 = 2404805) B2404805
theorem B1603219 : Blo 1603000 1603219 := bstep (se 1 (by rfl) ⟨1202414, by rfl⟩ : syracuseStep 1603219 = 2404829) B2404829
theorem B2406035 : Blo 1603000 2406035 := bstep (se 1 (by rfl) ⟨1804526, by rfl⟩ : syracuseStep 2406035 = 3609053) B3609053
theorem B8115875 : Blo 1603000 8115875 := bstep (se 1 (by rfl) ⟨6086906, by rfl⟩ : syracuseStep 8115875 = 12173813) B12173813
theorem B1603235 : Blo 1603000 1603235 := bstep (se 1 (by rfl) ⟨1202426, by rfl⟩ : syracuseStep 1603235 = 2404853) B2404853
theorem B2406065 : Blo 1603000 2406065 := bstep (se 2 (by rfl) ⟨902274, by rfl⟩ : syracuseStep 2406065 = 1804549) B1804549
theorem B1603251 : Blo 1603000 1603251 := bstep (se 1 (by rfl) ⟨1202438, by rfl⟩ : syracuseStep 1603251 = 2404877) B2404877
theorem B1603267 : Blo 1603000 1603267 := bstep (se 1 (by rfl) ⟨1202450, by rfl⟩ : syracuseStep 1603267 = 2404901) B2404901
theorem B2406083 : Blo 1603000 2406083 := bstep (se 1 (by rfl) ⟨1804562, by rfl⟩ : syracuseStep 2406083 = 3609125) B3609125
theorem B1603283 : Blo 1603000 1603283 := bstep (se 1 (by rfl) ⟨1202462, by rfl⟩ : syracuseStep 1603283 = 2404925) B2404925
theorem B2406113 : Blo 1603000 2406113 := bstep (se 2 (by rfl) ⟨902292, by rfl⟩ : syracuseStep 2406113 = 1804585) B1804585
theorem B1603299 : Blo 1603000 1603299 := bstep (se 1 (by rfl) ⟨1202474, by rfl⟩ : syracuseStep 1603299 = 2404949) B2404949
theorem B1603315 : Blo 1603000 1603315 := bstep (se 1 (by rfl) ⟨1202486, by rfl⟩ : syracuseStep 1603315 = 2404973) B2404973
theorem B2406131 : Blo 1603000 2406131 := bstep (se 1 (by rfl) ⟨1804598, by rfl⟩ : syracuseStep 2406131 = 3609197) B3609197
theorem B1603331 : Blo 1603000 1603331 := bstep (se 1 (by rfl) ⟨1202498, by rfl⟩ : syracuseStep 1603331 = 2404997) B2404997
theorem B6944525 : Blo 1603000 6944525 := bstep (se 3 (by rfl) ⟨1302098, by rfl⟩ : syracuseStep 6944525 = 2604197) B2604197
theorem B2406161 : Blo 1603000 2406161 := bstep (se 2 (by rfl) ⟨902310, by rfl⟩ : syracuseStep 2406161 = 1804621) B1804621
theorem B4568849 : Blo 1603000 4568849 := bstep (se 2 (by rfl) ⟨1713318, by rfl⟩ : syracuseStep 4568849 = 3426637) B3426637
theorem B1603347 : Blo 1603000 1603347 := bstep (se 1 (by rfl) ⟨1202510, by rfl⟩ : syracuseStep 1603347 = 2405021) B2405021
theorem B3610385 : Blo 1603000 3610385 := bstep (se 2 (by rfl) ⟨1353894, by rfl⟩ : syracuseStep 3610385 = 2707789) B2707789
theorem B1603363 : Blo 1603000 1603363 := bstep (se 1 (by rfl) ⟨1202522, by rfl⟩ : syracuseStep 1603363 = 2405045) B2405045
theorem B2406179 : Blo 1603000 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B3610403 : Blo 1603000 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B1603379 : Blo 1603000 1603379 := bstep (se 1 (by rfl) ⟨1202534, by rfl⟩ : syracuseStep 1603379 = 2405069) B2405069
theorem B3856177 : Blo 1603000 3856177 := bstep (se 2 (by rfl) ⟨1446066, by rfl⟩ : syracuseStep 3856177 = 2892133) B2892133
theorem B1603395 : Blo 1603000 1603395 := bstep (se 1 (by rfl) ⟨1202546, by rfl⟩ : syracuseStep 1603395 = 2405093) B2405093
theorem B2283331 : Blo 1603000 2283331 := bstep (se 1 (by rfl) ⟨1712498, by rfl⟩ : syracuseStep 2283331 = 3424997) B3424997
theorem B2406209 : Blo 1603000 2406209 := bstep (se 2 (by rfl) ⟨902328, by rfl⟩ : syracuseStep 2406209 = 1804657) B1804657
theorem B5412689 : Blo 1603000 5412689 := bstep (se 2 (by rfl) ⟨2029758, by rfl⟩ : syracuseStep 5412689 = 4059517) B4059517
theorem B1603411 : Blo 1603000 1603411 := bstep (se 1 (by rfl) ⟨1202558, by rfl⟩ : syracuseStep 1603411 = 2405117) B2405117
theorem B2406227 : Blo 1603000 2406227 := bstep (se 1 (by rfl) ⟨1804670, by rfl⟩ : syracuseStep 2406227 = 3609341) B3609341
theorem B1603427 : Blo 1603000 1603427 := bstep (se 1 (by rfl) ⟨1202570, by rfl⟩ : syracuseStep 1603427 = 2405141) B2405141
theorem B2406257 : Blo 1603000 2406257 := bstep (se 2 (by rfl) ⟨902346, by rfl⟩ : syracuseStep 2406257 = 1804693) B1804693
theorem B1603443 : Blo 1603000 1603443 := bstep (se 1 (by rfl) ⟨1202582, by rfl⟩ : syracuseStep 1603443 = 2405165) B2405165
theorem B1603459 : Blo 1603000 1603459 := bstep (se 1 (by rfl) ⟨1202594, by rfl⟩ : syracuseStep 1603459 = 2405189) B2405189
theorem B2406275 : Blo 1603000 2406275 := bstep (se 1 (by rfl) ⟨1804706, by rfl⟩ : syracuseStep 2406275 = 3609413) B3609413
theorem B1603475 : Blo 1603000 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B2406305 : Blo 1603000 2406305 := bstep (se 2 (by rfl) ⟨902364, by rfl⟩ : syracuseStep 2406305 = 1804729) B1804729
theorem B1603491 : Blo 1603000 1603491 := bstep (se 1 (by rfl) ⟨1202618, by rfl⟩ : syracuseStep 1603491 = 2405237) B2405237
theorem B2029475 : Blo 1603000 2029475 := bstep (se 1 (by rfl) ⟨1522106, by rfl⟩ : syracuseStep 2029475 = 3044213) B3044213
theorem B1603507 : Blo 1603000 1603507 := bstep (se 1 (by rfl) ⟨1202630, by rfl⟩ : syracuseStep 1603507 = 2405261) B2405261
theorem B2406323 : Blo 1603000 2406323 := bstep (se 1 (by rfl) ⟨1804742, by rfl⟩ : syracuseStep 2406323 = 3609485) B3609485
theorem B1603523 : Blo 1603000 1603523 := bstep (se 1 (by rfl) ⟨1202642, by rfl⟩ : syracuseStep 1603523 = 2405285) B2405285
theorem B30816197 : Blo 1603000 30816197 := bstep (se 4 (by rfl) ⟨2889018, by rfl⟩ : syracuseStep 30816197 = 5778037) B5778037
theorem B2406353 : Blo 1603000 2406353 := bstep (se 2 (by rfl) ⟨902382, by rfl⟩ : syracuseStep 2406353 = 1804765) B1804765
theorem B4061137 : Blo 1603000 4061137 := bstep (se 2 (by rfl) ⟨1522926, by rfl⟩ : syracuseStep 4061137 = 3045853) B3045853
theorem B1603539 : Blo 1603000 1603539 := bstep (se 1 (by rfl) ⟨1202654, by rfl⟩ : syracuseStep 1603539 = 2405309) B2405309
theorem B1603555 : Blo 1603000 1603555 := bstep (se 1 (by rfl) ⟨1202666, by rfl⟩ : syracuseStep 1603555 = 2405333) B2405333
theorem B2406371 : Blo 1603000 2406371 := bstep (se 1 (by rfl) ⟨1804778, by rfl⟩ : syracuseStep 2406371 = 3609557) B3609557
theorem B1603571 : Blo 1603000 1603571 := bstep (se 1 (by rfl) ⟨1202678, by rfl⟩ : syracuseStep 1603571 = 2405357) B2405357
theorem B2406401 : Blo 1603000 2406401 := bstep (se 2 (by rfl) ⟨902400, by rfl⟩ : syracuseStep 2406401 = 1804801) B1804801
theorem B1603587 : Blo 1603000 1603587 := bstep (se 1 (by rfl) ⟨1202690, by rfl⟩ : syracuseStep 1603587 = 2405381) B2405381
theorem B1603603 : Blo 1603000 1603603 := bstep (se 1 (by rfl) ⟨1202702, by rfl⟩ : syracuseStep 1603603 = 2405405) B2405405
theorem B2406419 : Blo 1603000 2406419 := bstep (se 1 (by rfl) ⟨1804814, by rfl⟩ : syracuseStep 2406419 = 3609629) B3609629
theorem B3250211 : Blo 1603000 3250211 := bstep (se 1 (by rfl) ⟨2437658, by rfl⟩ : syracuseStep 3250211 = 4875317) B4875317
theorem B1603619 : Blo 1603000 1603619 := bstep (se 1 (by rfl) ⟨1202714, by rfl⟩ : syracuseStep 1603619 = 2405429) B2405429
theorem B2406449 : Blo 1603000 2406449 := bstep (se 2 (by rfl) ⟨902418, by rfl⟩ : syracuseStep 2406449 = 1804837) B1804837
theorem B3610673 : Blo 1603000 3610673 := bstep (se 2 (by rfl) ⟨1354002, by rfl⟩ : syracuseStep 3610673 = 2708005) B2708005
theorem B1603635 : Blo 1603000 1603635 := bstep (se 1 (by rfl) ⟨1202726, by rfl⟩ : syracuseStep 1603635 = 2405453) B2405453
theorem B1603651 : Blo 1603000 1603651 := bstep (se 1 (by rfl) ⟨1202738, by rfl⟩ : syracuseStep 1603651 = 2405477) B2405477
theorem B2406467 : Blo 1603000 2406467 := bstep (se 1 (by rfl) ⟨1804850, by rfl⟩ : syracuseStep 2406467 = 3609701) B3609701
theorem B3610691 : Blo 1603000 3610691 := bstep (se 1 (by rfl) ⟨2708018, by rfl⟩ : syracuseStep 3610691 = 5416037) B5416037
theorem B1603667 : Blo 1603000 1603667 := bstep (se 1 (by rfl) ⟨1202750, by rfl⟩ : syracuseStep 1603667 = 2405501) B2405501
theorem B2406497 : Blo 1603000 2406497 := bstep (se 2 (by rfl) ⟨902436, by rfl⟩ : syracuseStep 2406497 = 1804873) B1804873
theorem B2889827 : Blo 1603000 2889827 := bstep (se 1 (by rfl) ⟨2167370, by rfl⟩ : syracuseStep 2889827 = 4334741) B4334741
theorem B1603683 : Blo 1603000 1603683 := bstep (se 1 (by rfl) ⟨1202762, by rfl⟩ : syracuseStep 1603683 = 2405525) B2405525
theorem B5486705 : Blo 1603000 5486705 := bstep (se 2 (by rfl) ⟨2057514, by rfl⟩ : syracuseStep 5486705 = 4115029) B4115029
theorem B1603699 : Blo 1603000 1603699 := bstep (se 1 (by rfl) ⟨1202774, by rfl⟩ : syracuseStep 1603699 = 2405549) B2405549
theorem B2406515 : Blo 1603000 2406515 := bstep (se 1 (by rfl) ⟨1804886, by rfl⟩ : syracuseStep 2406515 = 3609773) B3609773
theorem B1603715 : Blo 1603000 1603715 := bstep (se 1 (by rfl) ⟨1202786, by rfl⟩ : syracuseStep 1603715 = 2405573) B2405573
theorem B2406545 : Blo 1603000 2406545 := bstep (se 2 (by rfl) ⟨902454, by rfl⟩ : syracuseStep 2406545 = 1804909) B1804909
theorem B1603731 : Blo 1603000 1603731 := bstep (se 1 (by rfl) ⟨1202798, by rfl⟩ : syracuseStep 1603731 = 2405597) B2405597
theorem B1603747 : Blo 1603000 1603747 := bstep (se 1 (by rfl) ⟨1202810, by rfl⟩ : syracuseStep 1603747 = 2405621) B2405621
theorem B2406563 : Blo 1603000 2406563 := bstep (se 1 (by rfl) ⟨1804922, by rfl⟩ : syracuseStep 2406563 = 3609845) B3609845
theorem B1603763 : Blo 1603000 1603763 := bstep (se 1 (by rfl) ⟨1202822, by rfl⟩ : syracuseStep 1603763 = 2405645) B2405645
theorem B2406593 : Blo 1603000 2406593 := bstep (se 2 (by rfl) ⟨902472, by rfl⟩ : syracuseStep 2406593 = 1804945) B1804945
theorem B1603779 : Blo 1603000 1603779 := bstep (se 1 (by rfl) ⟨1202834, by rfl⟩ : syracuseStep 1603779 = 2405669) B2405669
theorem B1603795 : Blo 1603000 1603795 := bstep (se 1 (by rfl) ⟨1202846, by rfl⟩ : syracuseStep 1603795 = 2405693) B2405693
theorem B2406611 : Blo 1603000 2406611 := bstep (se 1 (by rfl) ⟨1804958, by rfl⟩ : syracuseStep 2406611 = 3609917) B3609917
theorem B1603811 : Blo 1603000 1603811 := bstep (se 1 (by rfl) ⟨1202858, by rfl⟩ : syracuseStep 1603811 = 2405717) B2405717
theorem B4061411 : Blo 1603000 4061411 := bstep (se 1 (by rfl) ⟨3046058, by rfl⟩ : syracuseStep 4061411 = 6092117) B6092117
theorem B2406641 : Blo 1603000 2406641 := bstep (se 2 (by rfl) ⟨902490, by rfl⟩ : syracuseStep 2406641 = 1804981) B1804981
theorem B1603827 : Blo 1603000 1603827 := bstep (se 1 (by rfl) ⟨1202870, by rfl⟩ : syracuseStep 1603827 = 2405741) B2405741
theorem B1603843 : Blo 1603000 1603843 := bstep (se 1 (by rfl) ⟨1202882, by rfl⟩ : syracuseStep 1603843 = 2405765) B2405765
theorem B2406659 : Blo 1603000 2406659 := bstep (se 1 (by rfl) ⟨1804994, by rfl⟩ : syracuseStep 2406659 = 3609989) B3609989
theorem B1603859 : Blo 1603000 1603859 := bstep (se 1 (by rfl) ⟨1202894, by rfl⟩ : syracuseStep 1603859 = 2405789) B2405789
theorem B2406689 : Blo 1603000 2406689 := bstep (se 2 (by rfl) ⟨902508, by rfl⟩ : syracuseStep 2406689 = 1805017) B1805017
theorem B1603875 : Blo 1603000 1603875 := bstep (se 1 (by rfl) ⟨1202906, by rfl⟩ : syracuseStep 1603875 = 2405813) B2405813
theorem B1603891 : Blo 1603000 1603891 := bstep (se 1 (by rfl) ⟨1202918, by rfl⟩ : syracuseStep 1603891 = 2405837) B2405837
theorem B2406707 : Blo 1603000 2406707 := bstep (se 1 (by rfl) ⟨1805030, by rfl⟩ : syracuseStep 2406707 = 3610061) B3610061
theorem B1603907 : Blo 1603000 1603907 := bstep (se 1 (by rfl) ⟨1202930, by rfl⟩ : syracuseStep 1603907 = 2405861) B2405861
theorem B9263429 : Blo 1603000 9263429 := bstep (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) B1736893
theorem B9132365 : Blo 1603000 9132365 := bstep (se 3 (by rfl) ⟨1712318, by rfl⟩ : syracuseStep 9132365 = 3424637) B3424637
theorem B2406737 : Blo 1603000 2406737 := bstep (se 2 (by rfl) ⟨902526, by rfl⟩ : syracuseStep 2406737 = 1805053) B1805053
theorem B3610961 : Blo 1603000 3610961 := bstep (se 2 (by rfl) ⟨1354110, by rfl⟩ : syracuseStep 3610961 = 2708221) B2708221
theorem B1603923 : Blo 1603000 1603923 := bstep (se 1 (by rfl) ⟨1202942, by rfl⟩ : syracuseStep 1603923 = 2405885) B2405885
theorem B1603939 : Blo 1603000 1603939 := bstep (se 1 (by rfl) ⟨1202954, by rfl⟩ : syracuseStep 1603939 = 2405909) B2405909
theorem B2406755 : Blo 1603000 2406755 := bstep (se 1 (by rfl) ⟨1805066, by rfl⟩ : syracuseStep 2406755 = 3610133) B3610133
theorem B3610979 : Blo 1603000 3610979 := bstep (se 1 (by rfl) ⟨2708234, by rfl⟩ : syracuseStep 3610979 = 5416469) B5416469
theorem B5413229 : Blo 1603000 5413229 := bstep (se 3 (by rfl) ⟨1014980, by rfl⟩ : syracuseStep 5413229 = 2029961) B2029961
theorem B2283889 : Blo 1603000 2283889 := bstep (se 2 (by rfl) ⟨856458, by rfl⟩ : syracuseStep 2283889 = 1712917) B1712917
theorem B8124785 : Blo 1603000 8124785 := bstep (se 2 (by rfl) ⟨3046794, by rfl⟩ : syracuseStep 8124785 = 6093589) B6093589
theorem B1603955 : Blo 1603000 1603955 := bstep (se 1 (by rfl) ⟨1202966, by rfl⟩ : syracuseStep 1603955 = 2405933) B2405933
theorem B2406785 : Blo 1603000 2406785 := bstep (se 2 (by rfl) ⟨902544, by rfl⟩ : syracuseStep 2406785 = 1805089) B1805089
theorem B1603971 : Blo 1603000 1603971 := bstep (se 1 (by rfl) ⟨1202978, by rfl⟩ : syracuseStep 1603971 = 2405957) B2405957
theorem B1603987 : Blo 1603000 1603987 := bstep (se 1 (by rfl) ⟨1202990, by rfl⟩ : syracuseStep 1603987 = 2405981) B2405981
theorem B2283923 : Blo 1603000 2283923 := bstep (se 1 (by rfl) ⟨1712942, by rfl⟩ : syracuseStep 2283923 = 3425885) B3425885
theorem B2406803 : Blo 1603000 2406803 := bstep (se 1 (by rfl) ⟨1805102, by rfl⟩ : syracuseStep 2406803 = 3610205) B3610205
theorem B5413283 : Blo 1603000 5413283 := bstep (se 1 (by rfl) ⟨4059962, by rfl⟩ : syracuseStep 5413283 = 8119925) B8119925
theorem B1604003 : Blo 1603000 1604003 := bstep (se 1 (by rfl) ⟨1203002, by rfl⟩ : syracuseStep 1604003 = 2406005) B2406005
theorem B4061603 : Blo 1603000 4061603 := bstep (se 1 (by rfl) ⟨3046202, by rfl⟩ : syracuseStep 4061603 = 6092405) B6092405
theorem B10279345 : Blo 1603000 10279345 := bstep (se 2 (by rfl) ⟨3854754, by rfl⟩ : syracuseStep 10279345 = 7709509) B7709509
theorem B2406833 : Blo 1603000 2406833 := bstep (se 2 (by rfl) ⟨902562, by rfl⟩ : syracuseStep 2406833 = 1805125) B1805125
theorem B1604019 : Blo 1603000 1604019 := bstep (se 1 (by rfl) ⟨1203014, by rfl⟩ : syracuseStep 1604019 = 2406029) B2406029
theorem B1604035 : Blo 1603000 1604035 := bstep (se 1 (by rfl) ⟨1203026, by rfl⟩ : syracuseStep 1604035 = 2406053) B2406053
theorem B2406851 : Blo 1603000 2406851 := bstep (se 1 (by rfl) ⟨1805138, by rfl⟩ : syracuseStep 2406851 = 3610277) B3610277
theorem B8116685 : Blo 1603000 8116685 := bstep (se 3 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 8116685 = 3043757) B3043757
theorem B1604051 : Blo 1603000 1604051 := bstep (se 1 (by rfl) ⟨1203038, by rfl⟩ : syracuseStep 1604051 = 2406077) B2406077
theorem B2406881 : Blo 1603000 2406881 := bstep (se 2 (by rfl) ⟨902580, by rfl⟩ : syracuseStep 2406881 = 1805161) B1805161
theorem B1604067 : Blo 1603000 1604067 := bstep (se 1 (by rfl) ⟨1203050, by rfl⟩ : syracuseStep 1604067 = 2406101) B2406101
theorem B1604083 : Blo 1603000 1604083 := bstep (se 1 (by rfl) ⟨1203062, by rfl⟩ : syracuseStep 1604083 = 2406125) B2406125
theorem B2406899 : Blo 1603000 2406899 := bstep (se 1 (by rfl) ⟨1805174, by rfl⟩ : syracuseStep 2406899 = 3610349) B3610349
theorem B1604099 : Blo 1603000 1604099 := bstep (se 1 (by rfl) ⟨1203074, by rfl⟩ : syracuseStep 1604099 = 2406149) B2406149
theorem B2406929 : Blo 1603000 2406929 := bstep (se 2 (by rfl) ⟨902598, by rfl⟩ : syracuseStep 2406929 = 1805197) B1805197
theorem B1604115 : Blo 1603000 1604115 := bstep (se 1 (by rfl) ⟨1203086, by rfl⟩ : syracuseStep 1604115 = 2406173) B2406173
theorem B1604131 : Blo 1603000 1604131 := bstep (se 1 (by rfl) ⟨1203098, by rfl⟩ : syracuseStep 1604131 = 2406197) B2406197
theorem B2406947 : Blo 1603000 2406947 := bstep (se 1 (by rfl) ⟨1805210, by rfl⟩ : syracuseStep 2406947 = 3610421) B3610421
theorem B4569635 : Blo 1603000 4569635 := bstep (se 1 (by rfl) ⟨3427226, by rfl⟩ : syracuseStep 4569635 = 6854453) B6854453
theorem B3045937 : Blo 1603000 3045937 := bstep (se 2 (by rfl) ⟨1142226, by rfl⟩ : syracuseStep 3045937 = 2284453) B2284453
theorem B1604147 : Blo 1603000 1604147 := bstep (se 1 (by rfl) ⟨1203110, by rfl⟩ : syracuseStep 1604147 = 2406221) B2406221
theorem B2406977 : Blo 1603000 2406977 := bstep (se 2 (by rfl) ⟨902616, by rfl⟩ : syracuseStep 2406977 = 1805233) B1805233
theorem B1604163 : Blo 1603000 1604163 := bstep (se 1 (by rfl) ⟨1203122, by rfl⟩ : syracuseStep 1604163 = 2406245) B2406245
theorem B1604179 : Blo 1603000 1604179 := bstep (se 1 (by rfl) ⟨1203134, by rfl⟩ : syracuseStep 1604179 = 2406269) B2406269
theorem B2406995 : Blo 1603000 2406995 := bstep (se 1 (by rfl) ⟨1805246, by rfl⟩ : syracuseStep 2406995 = 3610493) B3610493
theorem B2030179 : Blo 1603000 2030179 := bstep (se 1 (by rfl) ⟨1522634, by rfl⟩ : syracuseStep 2030179 = 3045269) B3045269
theorem B1604195 : Blo 1603000 1604195 := bstep (se 1 (by rfl) ⟨1203146, by rfl⟩ : syracuseStep 1604195 = 2406293) B2406293
theorem B2407025 : Blo 1603000 2407025 := bstep (se 2 (by rfl) ⟨902634, by rfl⟩ : syracuseStep 2407025 = 1805269) B1805269
theorem B3611249 : Blo 1603000 3611249 := bstep (se 2 (by rfl) ⟨1354218, by rfl⟩ : syracuseStep 3611249 = 2708437) B2708437
theorem B1604211 : Blo 1603000 1604211 := bstep (se 1 (by rfl) ⟨1203158, by rfl⟩ : syracuseStep 1604211 = 2406317) B2406317
theorem B1604227 : Blo 1603000 1604227 := bstep (se 1 (by rfl) ⟨1203170, by rfl⟩ : syracuseStep 1604227 = 2406341) B2406341
theorem B2407043 : Blo 1603000 2407043 := bstep (se 1 (by rfl) ⟨1805282, by rfl⟩ : syracuseStep 2407043 = 3610565) B3610565
theorem B1604243 : Blo 1603000 1604243 := bstep (se 1 (by rfl) ⟨1203182, by rfl⟩ : syracuseStep 1604243 = 2406365) B2406365
theorem B2407073 : Blo 1603000 2407073 := bstep (se 2 (by rfl) ⟨902652, by rfl⟩ : syracuseStep 2407073 = 1805305) B1805305
theorem B1604259 : Blo 1603000 1604259 := bstep (se 1 (by rfl) ⟨1203194, by rfl⟩ : syracuseStep 1604259 = 2406389) B2406389
theorem B5413553 : Blo 1603000 5413553 := bstep (se 2 (by rfl) ⟨2030082, by rfl⟩ : syracuseStep 5413553 = 4060165) B4060165
theorem B1604275 : Blo 1603000 1604275 := bstep (se 1 (by rfl) ⟨1203206, by rfl⟩ : syracuseStep 1604275 = 2406413) B2406413
theorem B2407091 : Blo 1603000 2407091 := bstep (se 1 (by rfl) ⟨1805318, by rfl⟩ : syracuseStep 2407091 = 3610637) B3610637
theorem B2030275 : Blo 1603000 2030275 := bstep (se 1 (by rfl) ⟨1522706, by rfl⟩ : syracuseStep 2030275 = 3045413) B3045413
theorem B1604291 : Blo 1603000 1604291 := bstep (se 1 (by rfl) ⟨1203218, by rfl⟩ : syracuseStep 1604291 = 2406437) B2406437
theorem B2407121 : Blo 1603000 2407121 := bstep (se 2 (by rfl) ⟨902670, by rfl⟩ : syracuseStep 2407121 = 1805341) B1805341
theorem B2603731 : Blo 1603000 2603731 := bstep (se 1 (by rfl) ⟨1952798, by rfl⟩ : syracuseStep 2603731 = 3905597) B3905597
theorem B1604307 : Blo 1603000 1604307 := bstep (se 1 (by rfl) ⟨1203230, by rfl⟩ : syracuseStep 1604307 = 2406461) B2406461
theorem B1604323 : Blo 1603000 1604323 := bstep (se 1 (by rfl) ⟨1203242, by rfl⟩ : syracuseStep 1604323 = 2406485) B2406485
theorem B2407139 : Blo 1603000 2407139 := bstep (se 1 (by rfl) ⟨1805354, by rfl⟩ : syracuseStep 2407139 = 3610709) B3610709
theorem B1604339 : Blo 1603000 1604339 := bstep (se 1 (by rfl) ⟨1203254, by rfl⟩ : syracuseStep 1604339 = 2406509) B2406509
theorem B2407169 : Blo 1603000 2407169 := bstep (se 2 (by rfl) ⟨902688, by rfl⟩ : syracuseStep 2407169 = 1805377) B1805377
theorem B1604355 : Blo 1603000 1604355 := bstep (se 1 (by rfl) ⟨1203266, by rfl⟩ : syracuseStep 1604355 = 2406533) B2406533
theorem B1604371 : Blo 1603000 1604371 := bstep (se 1 (by rfl) ⟨1203278, by rfl⟩ : syracuseStep 1604371 = 2406557) B2406557
theorem B2407187 : Blo 1603000 2407187 := bstep (se 1 (by rfl) ⟨1805390, by rfl⟩ : syracuseStep 2407187 = 3610781) B3610781
theorem B1604387 : Blo 1603000 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B2407217 : Blo 1603000 2407217 := bstep (se 2 (by rfl) ⟨902706, by rfl⟩ : syracuseStep 2407217 = 1805413) B1805413
theorem B1604403 : Blo 1603000 1604403 := bstep (se 1 (by rfl) ⟨1203302, by rfl⟩ : syracuseStep 1604403 = 2406605) B2406605
theorem B1604419 : Blo 1603000 1604419 := bstep (se 1 (by rfl) ⟨1203314, by rfl⟩ : syracuseStep 1604419 = 2406629) B2406629
theorem B2407235 : Blo 1603000 2407235 := bstep (se 1 (by rfl) ⟨1805426, by rfl⟩ : syracuseStep 2407235 = 3610853) B3610853
theorem B1604435 : Blo 1603000 1604435 := bstep (se 1 (by rfl) ⟨1203326, by rfl⟩ : syracuseStep 1604435 = 2406653) B2406653
theorem B2407265 : Blo 1603000 2407265 := bstep (se 2 (by rfl) ⟨902724, by rfl⟩ : syracuseStep 2407265 = 1805449) B1805449
theorem B1604451 : Blo 1603000 1604451 := bstep (se 1 (by rfl) ⟨1203338, by rfl⟩ : syracuseStep 1604451 = 2406677) B2406677
theorem B4569965 : Blo 1603000 4569965 := bstep (se 3 (by rfl) ⟨856868, by rfl⟩ : syracuseStep 4569965 = 1713737) B1713737
theorem B1604467 : Blo 1603000 1604467 := bstep (se 1 (by rfl) ⟨1203350, by rfl⟩ : syracuseStep 1604467 = 2406701) B2406701
theorem B2407283 : Blo 1603000 2407283 := bstep (se 1 (by rfl) ⟨1805462, by rfl⟩ : syracuseStep 2407283 = 3610925) B3610925
theorem B1604483 : Blo 1603000 1604483 := bstep (se 1 (by rfl) ⟨1203362, by rfl⟩ : syracuseStep 1604483 = 2406725) B2406725
theorem B2407313 : Blo 1603000 2407313 := bstep (se 2 (by rfl) ⟨902742, by rfl⟩ : syracuseStep 2407313 = 1805485) B1805485
theorem B1604499 : Blo 1603000 1604499 := bstep (se 1 (by rfl) ⟨1203374, by rfl⟩ : syracuseStep 1604499 = 2406749) B2406749
theorem B1604515 : Blo 1603000 1604515 := bstep (se 1 (by rfl) ⟨1203386, by rfl⟩ : syracuseStep 1604515 = 2406773) B2406773
theorem B2407331 : Blo 1603000 2407331 := bstep (se 1 (by rfl) ⟨1805498, by rfl⟩ : syracuseStep 2407331 = 3610997) B3610997
theorem B4570033 : Blo 1603000 4570033 := bstep (se 2 (by rfl) ⟨1713762, by rfl⟩ : syracuseStep 4570033 = 3427525) B3427525
theorem B1604531 : Blo 1603000 1604531 := bstep (se 1 (by rfl) ⟨1203398, by rfl⟩ : syracuseStep 1604531 = 2406797) B2406797
theorem B2284481 : Blo 1603000 2284481 := bstep (se 2 (by rfl) ⟨856680, by rfl⟩ : syracuseStep 2284481 = 1713361) B1713361
theorem B1604547 : Blo 1603000 1604547 := bstep (se 1 (by rfl) ⟨1203410, by rfl⟩ : syracuseStep 1604547 = 2406821) B2406821
theorem B3046339 : Blo 1603000 3046339 := bstep (se 1 (by rfl) ⟨2284754, by rfl⟩ : syracuseStep 3046339 = 4569509) B4569509
theorem B2407361 : Blo 1603000 2407361 := bstep (se 2 (by rfl) ⟨902760, by rfl⟩ : syracuseStep 2407361 = 1805521) B1805521
theorem B3251153 : Blo 1603000 3251153 := bstep (se 2 (by rfl) ⟨1219182, by rfl⟩ : syracuseStep 3251153 = 2438365) B2438365
theorem B1604563 : Blo 1603000 1604563 := bstep (se 1 (by rfl) ⟨1203422, by rfl⟩ : syracuseStep 1604563 = 2406845) B2406845
theorem B2407379 : Blo 1603000 2407379 := bstep (se 1 (by rfl) ⟨1805534, by rfl⟩ : syracuseStep 2407379 = 3611069) B3611069
theorem B1604579 : Blo 1603000 1604579 := bstep (se 1 (by rfl) ⟨1203434, by rfl⟩ : syracuseStep 1604579 = 2406869) B2406869
theorem B3046385 : Blo 1603000 3046385 := bstep (se 2 (by rfl) ⟨1142394, by rfl⟩ : syracuseStep 3046385 = 2284789) B2284789
theorem B2407409 : Blo 1603000 2407409 := bstep (se 2 (by rfl) ⟨902778, by rfl⟩ : syracuseStep 2407409 = 1805557) B1805557
theorem B1604595 : Blo 1603000 1604595 := bstep (se 1 (by rfl) ⟨1203446, by rfl⟩ : syracuseStep 1604595 = 2406893) B2406893
theorem B1604611 : Blo 1603000 1604611 := bstep (se 1 (by rfl) ⟨1203458, by rfl⟩ : syracuseStep 1604611 = 2406917) B2406917
theorem B2407427 : Blo 1603000 2407427 := bstep (se 1 (by rfl) ⟨1805570, by rfl⟩ : syracuseStep 2407427 = 3611141) B3611141
theorem B2284561 : Blo 1603000 2284561 := bstep (se 2 (by rfl) ⟨856710, by rfl⟩ : syracuseStep 2284561 = 1713421) B1713421
theorem B1604627 : Blo 1603000 1604627 := bstep (se 1 (by rfl) ⟨1203470, by rfl⟩ : syracuseStep 1604627 = 2406941) B2406941
theorem B2407457 : Blo 1603000 2407457 := bstep (se 2 (by rfl) ⟨902796, by rfl⟩ : syracuseStep 2407457 = 1805593) B1805593
theorem B1604643 : Blo 1603000 1604643 := bstep (se 1 (by rfl) ⟨1203482, by rfl⟩ : syracuseStep 1604643 = 2406965) B2406965
theorem B6945841 : Blo 1603000 6945841 := bstep (se 2 (by rfl) ⟨2604690, by rfl⟩ : syracuseStep 6945841 = 5209381) B5209381
theorem B1604659 : Blo 1603000 1604659 := bstep (se 1 (by rfl) ⟨1203494, by rfl⟩ : syracuseStep 1604659 = 2406989) B2406989
theorem B2407475 : Blo 1603000 2407475 := bstep (se 1 (by rfl) ⟨1805606, by rfl⟩ : syracuseStep 2407475 = 3611213) B3611213
theorem B1604675 : Blo 1603000 1604675 := bstep (se 1 (by rfl) ⟨1203506, by rfl⟩ : syracuseStep 1604675 = 2407013) B2407013
theorem B3521603 : Blo 1603000 3521603 := bstep (se 1 (by rfl) ⟨2641202, by rfl⟩ : syracuseStep 3521603 = 5282405) B5282405
theorem B1604691 : Blo 1603000 1604691 := bstep (se 1 (by rfl) ⟨1203518, by rfl⟩ : syracuseStep 1604691 = 2407037) B2407037
theorem B1604707 : Blo 1603000 1604707 := bstep (se 1 (by rfl) ⟨1203530, by rfl⟩ : syracuseStep 1604707 = 2407061) B2407061
theorem B1604723 : Blo 1603000 1604723 := bstep (se 1 (by rfl) ⟨1203542, by rfl⟩ : syracuseStep 1604723 = 2407085) B2407085
theorem B1604739 : Blo 1603000 1604739 := bstep (se 1 (by rfl) ⟨1203554, by rfl⟩ : syracuseStep 1604739 = 2407109) B2407109
theorem B1604755 : Blo 1603000 1604755 := bstep (se 1 (by rfl) ⟨1203566, by rfl⟩ : syracuseStep 1604755 = 2407133) B2407133
theorem B1604771 : Blo 1603000 1604771 := bstep (se 1 (by rfl) ⟨1203578, by rfl⟩ : syracuseStep 1604771 = 2407157) B2407157
theorem B2030771 : Blo 1603000 2030771 := bstep (se 1 (by rfl) ⟨1523078, by rfl⟩ : syracuseStep 2030771 = 3046157) B3046157
theorem B1604787 : Blo 1603000 1604787 := bstep (se 1 (by rfl) ⟨1203590, by rfl⟩ : syracuseStep 1604787 = 2407181) B2407181
theorem B1604803 : Blo 1603000 1604803 := bstep (se 1 (by rfl) ⟨1203602, by rfl⟩ : syracuseStep 1604803 = 2407205) B2407205
theorem B4570307 : Blo 1603000 4570307 := bstep (se 1 (by rfl) ⟨3427730, by rfl⟩ : syracuseStep 4570307 = 6855461) B6855461
theorem B5414093 : Blo 1603000 5414093 := bstep (se 3 (by rfl) ⟨1015142, by rfl⟩ : syracuseStep 5414093 = 2030285) B2030285
theorem B1604819 : Blo 1603000 1604819 := bstep (se 1 (by rfl) ⟨1203614, by rfl⟩ : syracuseStep 1604819 = 2407229) B2407229
theorem B1604835 : Blo 1603000 1604835 := bstep (se 1 (by rfl) ⟨1203626, by rfl⟩ : syracuseStep 1604835 = 2407253) B2407253
theorem B5487857 : Blo 1603000 5487857 := bstep (se 2 (by rfl) ⟨2057946, by rfl⟩ : syracuseStep 5487857 = 4115893) B4115893
theorem B1604851 : Blo 1603000 1604851 := bstep (se 1 (by rfl) ⟨1203638, by rfl⟩ : syracuseStep 1604851 = 2407277) B2407277
theorem B5414147 : Blo 1603000 5414147 := bstep (se 1 (by rfl) ⟨4060610, by rfl⟩ : syracuseStep 5414147 = 8121221) B8121221
theorem B1604867 : Blo 1603000 1604867 := bstep (se 1 (by rfl) ⟨1203650, by rfl⟩ : syracuseStep 1604867 = 2407301) B2407301
theorem B3046673 : Blo 1603000 3046673 := bstep (se 2 (by rfl) ⟨1142502, by rfl⟩ : syracuseStep 3046673 = 2285005) B2285005
theorem B1604883 : Blo 1603000 1604883 := bstep (se 1 (by rfl) ⟨1203662, by rfl⟩ : syracuseStep 1604883 = 2407325) B2407325
theorem B1604899 : Blo 1603000 1604899 := bstep (se 1 (by rfl) ⟨1203674, by rfl⟩ : syracuseStep 1604899 = 2407349) B2407349
theorem B1604915 : Blo 1603000 1604915 := bstep (se 1 (by rfl) ⟨1203686, by rfl⟩ : syracuseStep 1604915 = 2407373) B2407373
theorem B1604931 : Blo 1603000 1604931 := bstep (se 1 (by rfl) ⟨1203698, by rfl⟩ : syracuseStep 1604931 = 2407397) B2407397
theorem B11558213 : Blo 1603000 11558213 := bstep (se 4 (by rfl) ⟨1083582, by rfl⟩ : syracuseStep 11558213 = 2167165) B2167165
theorem B2891089 : Blo 1603000 2891089 := bstep (se 2 (by rfl) ⟨1084158, by rfl⟩ : syracuseStep 2891089 = 2168317) B2168317
theorem B4062545 : Blo 1603000 4062545 := bstep (se 2 (by rfl) ⟨1523454, by rfl⟩ : syracuseStep 4062545 = 3046909) B3046909
theorem B1604947 : Blo 1603000 1604947 := bstep (se 1 (by rfl) ⟨1203710, by rfl⟩ : syracuseStep 1604947 = 2407421) B2407421
theorem B1604963 : Blo 1603000 1604963 := bstep (se 1 (by rfl) ⟨1203722, by rfl⟩ : syracuseStep 1604963 = 2407445) B2407445
theorem B1604979 : Blo 1603000 1604979 := bstep (se 1 (by rfl) ⟨1203734, by rfl⟩ : syracuseStep 1604979 = 2407469) B2407469
theorem B4062595 : Blo 1603000 4062595 := bstep (se 1 (by rfl) ⟨3046946, by rfl⟩ : syracuseStep 4062595 = 6093893) B6093893
theorem B1604995 : Blo 1603000 1604995 := bstep (se 1 (by rfl) ⟨1203746, by rfl⟩ : syracuseStep 1604995 = 2407493) B2407493
theorem B2891153 : Blo 1603000 2891153 := bstep (se 2 (by rfl) ⟨1084182, by rfl⟩ : syracuseStep 2891153 = 2168365) B2168365
theorem B5414417 : Blo 1603000 5414417 := bstep (se 2 (by rfl) ⟨2030406, by rfl⟩ : syracuseStep 5414417 = 4060813) B4060813
theorem B12041797 : Blo 1603000 12041797 := bstep (se 4 (by rfl) ⟨1128918, by rfl⟩ : syracuseStep 12041797 = 2257837) B2257837
theorem B15425093 : Blo 1603000 15425093 := bstep (se 4 (by rfl) ⟨1446102, by rfl⟩ : syracuseStep 15425093 = 2892205) B2892205
theorem B2891441 : Blo 1603000 2891441 := bstep (se 2 (by rfl) ⟨1084290, by rfl⟩ : syracuseStep 2891441 = 2168581) B2168581
theorem B3423971 : Blo 1603000 3423971 := bstep (se 1 (by rfl) ⟨2567978, by rfl⟩ : syracuseStep 3423971 = 5135957) B5135957
theorem B5783345 : Blo 1603000 5783345 := bstep (se 2 (by rfl) ⟨2168754, by rfl⟩ : syracuseStep 5783345 = 4337509) B4337509
theorem B10272581 : Blo 1603000 10272581 := bstep (se 4 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 10272581 = 1926109) B1926109
theorem B29253649 : Blo 1603000 29253649 := bstep (se 2 (by rfl) ⟨10970118, by rfl⟩ : syracuseStep 29253649 = 21940237) B21940237
theorem B9388183 : Blo 1603000 9388183 := bstep (se 1 (by rfl) ⟨7041137, by rfl⟩ : syracuseStep 9388183 = 14082275) B14082275
theorem B46850309 : Blo 1603000 46850309 := bstep (se 4 (by rfl) ⟨4392216, by rfl⟩ : syracuseStep 46850309 = 8784433) B8784433
theorem B37044485 : Blo 1603000 37044485 := bstep (se 4 (by rfl) ⟨3472920, by rfl⟩ : syracuseStep 37044485 = 6945841) B6945841
theorem B11567377 : Blo 1603000 11567377 := bstep (se 2 (by rfl) ⟨4337766, by rfl⟩ : syracuseStep 11567377 = 8675533) B8675533
theorem B3424535 : Blo 1603000 3424535 := bstep (se 1 (by rfl) ⟨2568401, by rfl⟩ : syracuseStep 3424535 = 5136803) B5136803
theorem B34668917 : Blo 1603000 34668917 := bstep (se 5 (by rfl) ⟨1625105, by rfl⟩ : syracuseStep 34668917 = 3250211) B3250211
theorem B7709107 : Blo 1603000 7709107 := bstep (se 1 (by rfl) ⟨5781830, by rfl⟩ : syracuseStep 7709107 = 11563661) B11563661
theorem B5415389 : Blo 1603000 5415389 := bstep (se 3 (by rfl) ⟨1015385, by rfl⟩ : syracuseStep 5415389 = 2030771) B2030771
theorem B13705793 : Blo 1603000 13705793 := bstep (se 2 (by rfl) ⟨5139672, by rfl⟩ : syracuseStep 13705793 = 10279345) B10279345
theorem B6087257 : Blo 1603000 6087257 := bstep (se 2 (by rfl) ⟨2282721, by rfl⟩ : syracuseStep 6087257 = 4565443) B4565443
theorem B51438401 : Blo 1603000 51438401 := bstep (se 2 (by rfl) ⟨19289400, by rfl⟩ : syracuseStep 51438401 = 38578801) B38578801
theorem B8119115 : Blo 1603000 8119115 := bstep (se 1 (by rfl) ⟨6089336, by rfl⟩ : syracuseStep 8119115 = 12178673) B12178673
theorem B27403109 : Blo 1603000 27403109 := bstep (se 4 (by rfl) ⟨2569041, by rfl⟩ : syracuseStep 27403109 = 5138083) B5138083
theorem B6087575 : Blo 1603000 6087575 := bstep (se 1 (by rfl) ⟨4565681, by rfl⟩ : syracuseStep 6087575 = 9131363) B9131363
theorem B10281907 : Blo 1603000 10281907 := bstep (se 1 (by rfl) ⟨7711430, by rfl⟩ : syracuseStep 10281907 = 15422861) B15422861
theorem B1713079 : Blo 1603000 1713079 := bstep (se 1 (by rfl) ⟨1284809, by rfl⟩ : syracuseStep 1713079 = 2569619) B2569619
theorem B7709741 : Blo 1603000 7709741 := bstep (se 3 (by rfl) ⟨1445576, by rfl⟩ : syracuseStep 7709741 = 2891153) B2891153
theorem B1803415 : Blo 1603000 1803415 := bstep (se 1 (by rfl) ⟨1352561, by rfl⟩ : syracuseStep 1803415 = 2705123) B2705123
theorem B4629683 : Blo 1603000 4629683 := bstep (se 1 (by rfl) ⟨3472262, by rfl⟩ : syracuseStep 4629683 = 6944525) B6944525
theorem B11568419 : Blo 1603000 11568419 := bstep (se 1 (by rfl) ⟨8676314, by rfl⟩ : syracuseStep 11568419 = 17352629) B17352629
theorem B1803595 : Blo 1603000 1803595 := bstep (se 1 (by rfl) ⟨1352696, by rfl⟩ : syracuseStep 1803595 = 2705393) B2705393
theorem B1926551 : Blo 1603000 1926551 := bstep (se 1 (by rfl) ⟨1444913, by rfl⟩ : syracuseStep 1926551 = 2889827) B2889827
theorem B1803703 : Blo 1603000 1803703 := bstep (se 1 (by rfl) ⟨1352777, by rfl⟩ : syracuseStep 1803703 = 2705555) B2705555
theorem B20547107 : Blo 1603000 20547107 := bstep (se 1 (by rfl) ⟨15410330, by rfl⟩ : syracuseStep 20547107 = 30820661) B30820661
theorem B10978861 : Blo 1603000 10978861 := bstep (se 3 (by rfl) ⟨2058536, by rfl⟩ : syracuseStep 10978861 = 4117073) B4117073
theorem B6088243 : Blo 1603000 6088243 := bstep (se 1 (by rfl) ⟨4566182, by rfl⟩ : syracuseStep 6088243 = 9132365) B9132365
theorem B5416523 : Blo 1603000 5416523 := bstep (se 1 (by rfl) ⟨4062392, by rfl⟩ : syracuseStep 5416523 = 8124785) B8124785
theorem B1803883 : Blo 1603000 1803883 := bstep (se 1 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 1803883 = 2705825) B2705825
theorem B1803991 : Blo 1603000 1803991 := bstep (se 1 (by rfl) ⟨1352993, by rfl⟩ : syracuseStep 1803991 = 2705987) B2705987
theorem B13698821 : Blo 1603000 13698821 := bstep (se 4 (by rfl) ⟨1284264, by rfl⟩ : syracuseStep 13698821 = 2568529) B2568529
theorem B2705177 : Blo 1603000 2705177 := bstep (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) B2028883
theorem B5416793 : Blo 1603000 5416793 := bstep (se 2 (by rfl) ⟨2031297, by rfl⟩ : syracuseStep 5416793 = 4062595) B4062595
theorem B1804171 : Blo 1603000 1804171 := bstep (se 1 (by rfl) ⟨1353128, by rfl⟩ : syracuseStep 1804171 = 2706257) B2706257
theorem B2705305 : Blo 1603000 2705305 := bstep (se 2 (by rfl) ⟨1014489, by rfl⟩ : syracuseStep 2705305 = 2028979) B2028979
theorem B1804279 : Blo 1603000 1804279 := bstep (se 1 (by rfl) ⟨1353209, by rfl⟩ : syracuseStep 1804279 = 2706419) B2706419
theorem B13371485 : Blo 1603000 13371485 := bstep (se 3 (by rfl) ⟨2507153, by rfl⟩ : syracuseStep 13371485 = 5014307) B5014307
theorem B2345113 : Blo 1603000 2345113 := bstep (se 2 (by rfl) ⟨879417, by rfl⟩ : syracuseStep 2345113 = 1758835) B1758835
theorem B1804459 : Blo 1603000 1804459 := bstep (se 1 (by rfl) ⟨1353344, by rfl⟩ : syracuseStep 1804459 = 2706689) B2706689
theorem B6850763 : Blo 1603000 6850763 := bstep (se 1 (by rfl) ⟨5138072, by rfl⟩ : syracuseStep 6850763 = 10276145) B10276145
theorem B3606785 : Blo 1603000 3606785 := bstep (se 2 (by rfl) ⟨1352544, by rfl⟩ : syracuseStep 3606785 = 2705089) B2705089
theorem B1804567 : Blo 1603000 1804567 := bstep (se 1 (by rfl) ⟨1353425, by rfl⟩ : syracuseStep 1804567 = 2706851) B2706851
theorem B10283395 : Blo 1603000 10283395 := bstep (se 1 (by rfl) ⟨7712546, by rfl⟩ : syracuseStep 10283395 = 15425093) B15425093
theorem B1804747 : Blo 1603000 1804747 := bstep (se 1 (by rfl) ⟨1353560, by rfl⟩ : syracuseStep 1804747 = 2707121) B2707121
theorem B1927627 : Blo 1603000 1927627 := bstep (se 1 (by rfl) ⟨1445720, by rfl⟩ : syracuseStep 1927627 = 2891441) B2891441
theorem B2705879 : Blo 1603000 2705879 := bstep (se 1 (by rfl) ⟨2029409, by rfl⟩ : syracuseStep 2705879 = 4058819) B4058819
theorem B3607001 : Blo 1603000 3607001 := bstep (se 2 (by rfl) ⟨1352625, by rfl⟩ : syracuseStep 3607001 = 2705251) B2705251
theorem B3607091 : Blo 1603000 3607091 := bstep (se 1 (by rfl) ⟨2705318, by rfl⟩ : syracuseStep 3607091 = 5410637) B5410637
theorem B1804855 : Blo 1603000 1804855 := bstep (se 1 (by rfl) ⟨1353641, by rfl⟩ : syracuseStep 1804855 = 2707283) B2707283
theorem B8120897 : Blo 1603000 8120897 := bstep (se 2 (by rfl) ⟨3045336, by rfl⟩ : syracuseStep 8120897 = 6090673) B6090673
theorem B3607127 : Blo 1603000 3607127 := bstep (se 1 (by rfl) ⟨2705345, by rfl⟩ : syracuseStep 3607127 = 5410691) B5410691
theorem B2706007 : Blo 1603000 2706007 := bstep (se 1 (by rfl) ⟨2029505, by rfl⟩ : syracuseStep 2706007 = 4059011) B4059011
theorem B3426995 : Blo 1603000 3426995 := bstep (se 1 (by rfl) ⟨2570246, by rfl⟩ : syracuseStep 3426995 = 5140493) B5140493
theorem B1805035 : Blo 1603000 1805035 := bstep (se 1 (by rfl) ⟨1353776, by rfl⟩ : syracuseStep 1805035 = 2707553) B2707553
theorem B3607307 : Blo 1603000 3607307 := bstep (se 1 (by rfl) ⟨2705480, by rfl⟩ : syracuseStep 3607307 = 5410961) B5410961
theorem B6089489 : Blo 1603000 6089489 := bstep (se 2 (by rfl) ⟨2283558, by rfl⟩ : syracuseStep 6089489 = 4567117) B4567117
theorem B3607361 : Blo 1603000 3607361 := bstep (se 2 (by rfl) ⟨1352760, by rfl⟩ : syracuseStep 3607361 = 2705521) B2705521
theorem B1805143 : Blo 1603000 1805143 := bstep (se 1 (by rfl) ⟨1353857, by rfl⟩ : syracuseStep 1805143 = 2707715) B2707715
theorem B5778269 : Blo 1603000 5778269 := bstep (se 3 (by rfl) ⟨1083425, by rfl⟩ : syracuseStep 5778269 = 2166851) B2166851
theorem B9390941 : Blo 1603000 9390941 := bstep (se 3 (by rfl) ⟨1760801, by rfl⟩ : syracuseStep 9390941 = 3521603) B3521603
theorem B13003697 : Blo 1603000 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B4058059 : Blo 1603000 4058059 := bstep (se 1 (by rfl) ⟨3043544, by rfl⟩ : syracuseStep 4058059 = 6087089) B6087089
theorem B1805323 : Blo 1603000 1805323 := bstep (se 1 (by rfl) ⟨1353992, by rfl⟩ : syracuseStep 1805323 = 2707985) B2707985
theorem B3607577 : Blo 1603000 3607577 := bstep (se 2 (by rfl) ⟨1352841, by rfl⟩ : syracuseStep 3607577 = 2705683) B2705683
theorem B4877387 : Blo 1603000 4877387 := bstep (se 1 (by rfl) ⟨3658040, by rfl⟩ : syracuseStep 4877387 = 7316081) B7316081
theorem B4058201 : Blo 1603000 4058201 := bstep (se 2 (by rfl) ⟨1521825, by rfl⟩ : syracuseStep 4058201 = 3043651) B3043651
theorem B3607667 : Blo 1603000 3607667 := bstep (se 1 (by rfl) ⟨2705750, by rfl⟩ : syracuseStep 3607667 = 5411501) B5411501
theorem B1805431 : Blo 1603000 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B3607703 : Blo 1603000 3607703 := bstep (se 1 (by rfl) ⟨2705777, by rfl⟩ : syracuseStep 3607703 = 5411555) B5411555
theorem B6851735 : Blo 1603000 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B2706635 : Blo 1603000 2706635 := bstep (se 1 (by rfl) ⟨2029976, by rfl⟩ : syracuseStep 2706635 = 4059953) B4059953
theorem B1805611 : Blo 1603000 1805611 := bstep (se 1 (by rfl) ⟨1354208, by rfl⟩ : syracuseStep 1805611 = 2708417) B2708417
theorem B3607883 : Blo 1603000 3607883 := bstep (se 1 (by rfl) ⟨2705912, by rfl⟩ : syracuseStep 3607883 = 5411825) B5411825
theorem B2706763 : Blo 1603000 2706763 := bstep (se 1 (by rfl) ⟨2030072, by rfl⟩ : syracuseStep 2706763 = 4060145) B4060145
theorem B4566365 : Blo 1603000 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B3607937 : Blo 1603000 3607937 := bstep (se 2 (by rfl) ⟨1352976, by rfl⟩ : syracuseStep 3607937 = 2705953) B2705953
theorem B11562419 : Blo 1603000 11562419 := bstep (se 1 (by rfl) ⟨8671814, by rfl⟩ : syracuseStep 11562419 = 17343629) B17343629
theorem B6090187 : Blo 1603000 6090187 := bstep (se 1 (by rfl) ⟨4567640, by rfl⟩ : syracuseStep 6090187 = 9135281) B9135281
theorem B2706905 : Blo 1603000 2706905 := bstep (se 2 (by rfl) ⟨1015089, by rfl⟩ : syracuseStep 2706905 = 2030179) B2030179
theorem B5139929 : Blo 1603000 5139929 := bstep (se 2 (by rfl) ⟨1927473, by rfl⟩ : syracuseStep 5139929 = 3854947) B3854947
theorem B20844067 : Blo 1603000 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B4566593 : Blo 1603000 4566593 := bstep (se 2 (by rfl) ⟨1712472, by rfl⟩ : syracuseStep 4566593 = 3424945) B3424945
theorem B3608153 : Blo 1603000 3608153 := bstep (se 2 (by rfl) ⟨1353057, by rfl⟩ : syracuseStep 3608153 = 2706115) B2706115
theorem B2707033 : Blo 1603000 2707033 := bstep (se 2 (by rfl) ⟨1015137, by rfl⟩ : syracuseStep 2707033 = 2030275) B2030275
theorem B3608243 : Blo 1603000 3608243 := bstep (se 1 (by rfl) ⟨2706182, by rfl⟩ : syracuseStep 3608243 = 5412365) B5412365
theorem B4230859 : Blo 1603000 4230859 := bstep (se 1 (by rfl) ⟨3173144, by rfl⟩ : syracuseStep 4230859 = 6346289) B6346289
theorem B3608279 : Blo 1603000 3608279 := bstep (se 1 (by rfl) ⟨2706209, by rfl⟩ : syracuseStep 3608279 = 5412419) B5412419
theorem B2780887 : Blo 1603000 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B6090461 : Blo 1603000 6090461 := bstep (se 3 (by rfl) ⟨1141961, by rfl⟩ : syracuseStep 6090461 = 2283923) B2283923
theorem B5410583 : Blo 1603000 5410583 := bstep (se 1 (by rfl) ⟨4057937, by rfl⟩ : syracuseStep 5410583 = 8115875) B8115875
theorem B3608459 : Blo 1603000 3608459 := bstep (se 1 (by rfl) ⟨2706344, by rfl⟩ : syracuseStep 3608459 = 5412689) B5412689
theorem B4059031 : Blo 1603000 4059031 := bstep (se 1 (by rfl) ⟨3044273, by rfl⟩ : syracuseStep 4059031 = 6088547) B6088547
theorem B4566935 : Blo 1603000 4566935 := bstep (se 1 (by rfl) ⟨3425201, by rfl⟩ : syracuseStep 4566935 = 6850403) B6850403
theorem B13012913 : Blo 1603000 13012913 := bstep (se 2 (by rfl) ⟨4879842, by rfl⟩ : syracuseStep 13012913 = 9759685) B9759685
theorem B3608513 : Blo 1603000 3608513 := bstep (se 2 (by rfl) ⟨1353192, by rfl⟩ : syracuseStep 3608513 = 2706385) B2706385
theorem B27389987 : Blo 1603000 27389987 := bstep (se 1 (by rfl) ⟨20542490, by rfl⟩ : syracuseStep 27389987 = 41084981) B41084981
theorem B3657803 : Blo 1603000 3657803 := bstep (se 1 (by rfl) ⟨2743352, by rfl⟩ : syracuseStep 3657803 = 5486705) B5486705
theorem B2707607 : Blo 1603000 2707607 := bstep (se 1 (by rfl) ⟨2030705, by rfl⟩ : syracuseStep 2707607 = 4061411) B4061411
theorem B2404505 : Blo 1603000 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B3608729 : Blo 1603000 3608729 := bstep (se 2 (by rfl) ⟨1353273, by rfl⟩ : syracuseStep 3608729 = 2706547) B2706547
theorem B3043507 : Blo 1603000 3043507 := bstep (se 1 (by rfl) ⟨2282630, by rfl⟩ : syracuseStep 3043507 = 4565261) B4565261
theorem B3608819 : Blo 1603000 3608819 := bstep (se 1 (by rfl) ⟨2706614, by rfl⟩ : syracuseStep 3608819 = 5413229) B5413229
theorem B2404619 : Blo 1603000 2404619 := bstep (se 1 (by rfl) ⟨1803464, by rfl⟩ : syracuseStep 2404619 = 3606929) B3606929
theorem B2404631 : Blo 1603000 2404631 := bstep (se 1 (by rfl) ⟨1803473, by rfl⟩ : syracuseStep 2404631 = 3606947) B3606947
theorem B3608855 : Blo 1603000 3608855 := bstep (se 1 (by rfl) ⟨2706641, by rfl⟩ : syracuseStep 3608855 = 5413283) B5413283
theorem B2707735 : Blo 1603000 2707735 := bstep (se 1 (by rfl) ⟨2030801, by rfl⟩ : syracuseStep 2707735 = 4061603) B4061603
theorem B18264365 : Blo 1603000 18264365 := bstep (se 3 (by rfl) ⟨3424568, by rfl⟩ : syracuseStep 18264365 = 6849137) B6849137
theorem B5411123 : Blo 1603000 5411123 := bstep (se 1 (by rfl) ⟨4058342, by rfl⟩ : syracuseStep 5411123 = 8116685) B8116685
theorem B4059467 : Blo 1603000 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B10973515 : Blo 1603000 10973515 := bstep (se 1 (by rfl) ⟨8230136, by rfl⟩ : syracuseStep 10973515 = 16460273) B16460273
theorem B2437465 : Blo 1603000 2437465 := bstep (se 2 (by rfl) ⟨914049, by rfl⟩ : syracuseStep 2437465 = 1828099) B1828099
theorem B2404697 : Blo 1603000 2404697 := bstep (se 2 (by rfl) ⟨901761, by rfl⟩ : syracuseStep 2404697 = 1803523) B1803523
theorem B12341605 : Blo 1603000 12341605 := bstep (se 4 (by rfl) ⟨1157025, by rfl⟩ : syracuseStep 12341605 = 2314051) B2314051
theorem B6091159 : Blo 1603000 6091159 := bstep (se 1 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 6091159 = 9136739) B9136739
theorem B5484979 : Blo 1603000 5484979 := bstep (se 1 (by rfl) ⟨4113734, by rfl⟩ : syracuseStep 5484979 = 8227469) B8227469
theorem B3854785 : Blo 1603000 3854785 := bstep (se 2 (by rfl) ⟨1445544, by rfl⟩ : syracuseStep 3854785 = 2891089) B2891089
theorem B2404811 : Blo 1603000 2404811 := bstep (se 1 (by rfl) ⟨1803608, by rfl⟩ : syracuseStep 2404811 = 3607217) B3607217
theorem B3609035 : Blo 1603000 3609035 := bstep (se 1 (by rfl) ⟨2706776, by rfl⟩ : syracuseStep 3609035 = 5413553) B5413553
theorem B2404823 : Blo 1603000 2404823 := bstep (se 1 (by rfl) ⟨1803617, by rfl⟩ : syracuseStep 2404823 = 3607235) B3607235
theorem B4878809 : Blo 1603000 4878809 := bstep (se 2 (by rfl) ⟨1829553, by rfl⟩ : syracuseStep 4878809 = 3659107) B3659107
theorem B8122841 : Blo 1603000 8122841 := bstep (se 2 (by rfl) ⟨3046065, by rfl⟩ : syracuseStep 8122841 = 6092131) B6092131
theorem B3609089 : Blo 1603000 3609089 := bstep (se 2 (by rfl) ⟨1353408, by rfl⟩ : syracuseStep 3609089 = 2706817) B2706817
theorem B2404889 : Blo 1603000 2404889 := bstep (se 2 (by rfl) ⟨901833, by rfl⟩ : syracuseStep 2404889 = 1803667) B1803667
theorem B5411393 : Blo 1603000 5411393 := bstep (se 2 (by rfl) ⟨2029272, by rfl⟩ : syracuseStep 5411393 = 4058545) B4058545
theorem B9130589 : Blo 1603000 9130589 := bstep (se 3 (by rfl) ⟨1711985, by rfl⟩ : syracuseStep 9130589 = 3423971) B3423971
theorem B3043955 : Blo 1603000 3043955 := bstep (se 1 (by rfl) ⟨2282966, by rfl⟩ : syracuseStep 3043955 = 4565933) B4565933
theorem B2405003 : Blo 1603000 2405003 := bstep (se 1 (by rfl) ⟨1803752, by rfl⟩ : syracuseStep 2405003 = 3607505) B3607505
theorem B2167435 : Blo 1603000 2167435 := bstep (se 1 (by rfl) ⟨1625576, by rfl⟩ : syracuseStep 2167435 = 3251153) B3251153
theorem B2405015 : Blo 1603000 2405015 := bstep (se 1 (by rfl) ⟨1803761, by rfl⟩ : syracuseStep 2405015 = 3607523) B3607523
theorem B3043993 : Blo 1603000 3043993 := bstep (se 2 (by rfl) ⟨1141497, by rfl⟩ : syracuseStep 3043993 = 2282995) B2282995
theorem B4059841 : Blo 1603000 4059841 := bstep (se 2 (by rfl) ⟨1522440, by rfl⟩ : syracuseStep 4059841 = 3044881) B3044881
theorem B2405081 : Blo 1603000 2405081 := bstep (se 2 (by rfl) ⟨901905, by rfl⟩ : syracuseStep 2405081 = 1803811) B1803811
theorem B3609305 : Blo 1603000 3609305 := bstep (se 2 (by rfl) ⟨1353489, by rfl⟩ : syracuseStep 3609305 = 2706979) B2706979
theorem B9138905 : Blo 1603000 9138905 := bstep (se 2 (by rfl) ⟨3427089, by rfl⟩ : syracuseStep 9138905 = 6854179) B6854179
theorem B3609395 : Blo 1603000 3609395 := bstep (se 1 (by rfl) ⟨2707046, by rfl⟩ : syracuseStep 3609395 = 5414093) B5414093
theorem B2405195 : Blo 1603000 2405195 := bstep (se 1 (by rfl) ⟨1803896, by rfl⟩ : syracuseStep 2405195 = 3607793) B3607793
theorem B3658571 : Blo 1603000 3658571 := bstep (se 1 (by rfl) ⟨2743928, by rfl⟩ : syracuseStep 3658571 = 5487857) B5487857
theorem B2405207 : Blo 1603000 2405207 := bstep (se 1 (by rfl) ⟨1803905, by rfl⟩ : syracuseStep 2405207 = 3607811) B3607811
theorem B3609431 : Blo 1603000 3609431 := bstep (se 1 (by rfl) ⟨2707073, by rfl⟩ : syracuseStep 3609431 = 5414147) B5414147
theorem B7705475 : Blo 1603000 7705475 := bstep (se 1 (by rfl) ⟨5779106, by rfl⟩ : syracuseStep 7705475 = 11558213) B11558213
theorem B2708363 : Blo 1603000 2708363 := bstep (se 1 (by rfl) ⟨2031272, by rfl⟩ : syracuseStep 2708363 = 4062545) B4062545
theorem B2405273 : Blo 1603000 2405273 := bstep (se 2 (by rfl) ⟨901977, by rfl⟩ : syracuseStep 2405273 = 1803955) B1803955
theorem B2405387 : Blo 1603000 2405387 := bstep (se 1 (by rfl) ⟨1804040, by rfl⟩ : syracuseStep 2405387 = 3608081) B3608081
theorem B3609611 : Blo 1603000 3609611 := bstep (se 1 (by rfl) ⟨2707208, by rfl⟩ : syracuseStep 3609611 = 5414417) B5414417
theorem B2405399 : Blo 1603000 2405399 := bstep (se 1 (by rfl) ⟨1804049, by rfl⟩ : syracuseStep 2405399 = 3608099) B3608099
theorem B3609665 : Blo 1603000 3609665 := bstep (se 2 (by rfl) ⟨1353624, by rfl⟩ : syracuseStep 3609665 = 2707249) B2707249
theorem B5141569 : Blo 1603000 5141569 := bstep (se 2 (by rfl) ⟨1928088, by rfl⟩ : syracuseStep 5141569 = 3856177) B3856177
theorem B2405465 : Blo 1603000 2405465 := bstep (se 2 (by rfl) ⟨902049, by rfl⟩ : syracuseStep 2405465 = 1804099) B1804099
theorem B3044441 : Blo 1603000 3044441 := bstep (se 2 (by rfl) ⟨1141665, by rfl⟩ : syracuseStep 3044441 = 2283331) B2283331
theorem B5411933 : Blo 1603000 5411933 := bstep (se 3 (by rfl) ⟨1014737, by rfl⟩ : syracuseStep 5411933 = 2029475) B2029475
theorem B6091949 : Blo 1603000 6091949 := bstep (se 3 (by rfl) ⟨1142240, by rfl⟩ : syracuseStep 6091949 = 2284481) B2284481
theorem B2405579 : Blo 1603000 2405579 := bstep (se 1 (by rfl) ⟨1804184, by rfl⟩ : syracuseStep 2405579 = 3608369) B3608369
theorem B3855563 : Blo 1603000 3855563 := bstep (se 1 (by rfl) ⟨2891672, by rfl⟩ : syracuseStep 3855563 = 5783345) B5783345
theorem B2405591 : Blo 1603000 2405591 := bstep (se 1 (by rfl) ⟨1804193, by rfl⟩ : syracuseStep 2405591 = 3608387) B3608387
theorem B4060439 : Blo 1603000 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B2405657 : Blo 1603000 2405657 := bstep (se 2 (by rfl) ⟨902121, by rfl⟩ : syracuseStep 2405657 = 1804243) B1804243
theorem B3609881 : Blo 1603000 3609881 := bstep (se 2 (by rfl) ⟨1353705, by rfl⟩ : syracuseStep 3609881 = 2707411) B2707411
theorem B13702445 : Blo 1603000 13702445 := bstep (se 3 (by rfl) ⟨2569208, by rfl⟩ : syracuseStep 13702445 = 5138417) B5138417
theorem B3609971 : Blo 1603000 3609971 := bstep (se 1 (by rfl) ⟨2707478, by rfl⟩ : syracuseStep 3609971 = 5414957) B5414957
theorem B2405771 : Blo 1603000 2405771 := bstep (se 1 (by rfl) ⟨1804328, by rfl⟩ : syracuseStep 2405771 = 3608657) B3608657
theorem B2168203 : Blo 1603000 2168203 := bstep (se 1 (by rfl) ⟨1626152, by rfl⟩ : syracuseStep 2168203 = 3252305) B3252305
theorem B2405783 : Blo 1603000 2405783 := bstep (se 1 (by rfl) ⟨1804337, by rfl⟩ : syracuseStep 2405783 = 3608675) B3608675
theorem B3610007 : Blo 1603000 3610007 := bstep (se 1 (by rfl) ⟨2707505, by rfl⟩ : syracuseStep 3610007 = 5415011) B5415011
theorem B5780909 : Blo 1603000 5780909 := bstep (se 3 (by rfl) ⟨1083920, by rfl⟩ : syracuseStep 5780909 = 2167841) B2167841
theorem B18519475 : Blo 1603000 18519475 := bstep (se 1 (by rfl) ⟨13889606, by rfl⟩ : syracuseStep 18519475 = 27779213) B27779213
theorem B1603019 : Blo 1603000 1603019 := bstep (se 1 (by rfl) ⟨1202264, by rfl⟩ : syracuseStep 1603019 = 2404529) B2404529
theorem B1603031 : Blo 1603000 1603031 := bstep (se 1 (by rfl) ⟨1202273, by rfl⟩ : syracuseStep 1603031 = 2404547) B2404547
theorem B2405849 : Blo 1603000 2405849 := bstep (se 2 (by rfl) ⟨902193, by rfl⟩ : syracuseStep 2405849 = 1804387) B1804387
theorem B1603051 : Blo 1603000 1603051 := bstep (se 1 (by rfl) ⟨1202288, by rfl⟩ : syracuseStep 1603051 = 2404577) B2404577
theorem B1603063 : Blo 1603000 1603063 := bstep (se 1 (by rfl) ⟨1202297, by rfl⟩ : syracuseStep 1603063 = 2404595) B2404595
theorem B1603083 : Blo 1603000 1603083 := bstep (se 1 (by rfl) ⟨1202312, by rfl⟩ : syracuseStep 1603083 = 2404625) B2404625
theorem B1603095 : Blo 1603000 1603095 := bstep (se 1 (by rfl) ⟨1202321, by rfl⟩ : syracuseStep 1603095 = 2404643) B2404643
theorem B1603115 : Blo 1603000 1603115 := bstep (se 1 (by rfl) ⟨1202336, by rfl⟩ : syracuseStep 1603115 = 2404673) B2404673
theorem B6854195 : Blo 1603000 6854195 := bstep (se 1 (by rfl) ⟨5140646, by rfl⟩ : syracuseStep 6854195 = 10281293) B10281293
theorem B1603127 : Blo 1603000 1603127 := bstep (se 1 (by rfl) ⟨1202345, by rfl⟩ : syracuseStep 1603127 = 2404691) B2404691
theorem B1603147 : Blo 1603000 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B2405963 : Blo 1603000 2405963 := bstep (se 1 (by rfl) ⟨1804472, by rfl⟩ : syracuseStep 2405963 = 3608945) B3608945
theorem B3610187 : Blo 1603000 3610187 := bstep (se 1 (by rfl) ⟨2707640, by rfl⟩ : syracuseStep 3610187 = 5415281) B5415281
theorem B11130443 : Blo 1603000 11130443 := bstep (se 1 (by rfl) ⟨8347832, by rfl⟩ : syracuseStep 11130443 = 16695665) B16695665
theorem B1603159 : Blo 1603000 1603159 := bstep (se 1 (by rfl) ⟨1202369, by rfl⟩ : syracuseStep 1603159 = 2404739) B2404739
theorem B2405975 : Blo 1603000 2405975 := bstep (se 1 (by rfl) ⟨1804481, by rfl⟩ : syracuseStep 2405975 = 3608963) B3608963
theorem B1603179 : Blo 1603000 1603179 := bstep (se 1 (by rfl) ⟨1202384, by rfl⟩ : syracuseStep 1603179 = 2404769) B2404769
theorem B1603191 : Blo 1603000 1603191 := bstep (se 1 (by rfl) ⟨1202393, by rfl⟩ : syracuseStep 1603191 = 2404787) B2404787
theorem B3610241 : Blo 1603000 3610241 := bstep (se 2 (by rfl) ⟨1353840, by rfl⟩ : syracuseStep 3610241 = 2707681) B2707681
theorem B1603211 : Blo 1603000 1603211 := bstep (se 1 (by rfl) ⟨1202408, by rfl⟩ : syracuseStep 1603211 = 2404817) B2404817
theorem B1603223 : Blo 1603000 1603223 := bstep (se 1 (by rfl) ⟨1202417, by rfl⟩ : syracuseStep 1603223 = 2404835) B2404835
theorem B2029207 : Blo 1603000 2029207 := bstep (se 1 (by rfl) ⟨1521905, by rfl⟩ : syracuseStep 2029207 = 3043811) B3043811
theorem B2406041 : Blo 1603000 2406041 := bstep (se 2 (by rfl) ⟨902265, by rfl⟩ : syracuseStep 2406041 = 1804531) B1804531
theorem B1603243 : Blo 1603000 1603243 := bstep (se 1 (by rfl) ⟨1202432, by rfl⟩ : syracuseStep 1603243 = 2404865) B2404865
theorem B1603255 : Blo 1603000 1603255 := bstep (se 1 (by rfl) ⟨1202441, by rfl⟩ : syracuseStep 1603255 = 2404883) B2404883
theorem B1603275 : Blo 1603000 1603275 := bstep (se 1 (by rfl) ⟨1202456, by rfl⟩ : syracuseStep 1603275 = 2404913) B2404913
theorem B1603287 : Blo 1603000 1603287 := bstep (se 1 (by rfl) ⟨1202465, by rfl⟩ : syracuseStep 1603287 = 2404931) B2404931
theorem B2283223 : Blo 1603000 2283223 := bstep (se 1 (by rfl) ⟨1712417, by rfl⟩ : syracuseStep 2283223 = 3424835) B3424835
theorem B1603307 : Blo 1603000 1603307 := bstep (se 1 (by rfl) ⟨1202480, by rfl⟩ : syracuseStep 1603307 = 2404961) B2404961
theorem B1603319 : Blo 1603000 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B1603339 : Blo 1603000 1603339 := bstep (se 1 (by rfl) ⟨1202504, by rfl⟩ : syracuseStep 1603339 = 2405009) B2405009
theorem B2406155 : Blo 1603000 2406155 := bstep (se 1 (by rfl) ⟨1804616, by rfl⟩ : syracuseStep 2406155 = 3609233) B3609233
theorem B1603351 : Blo 1603000 1603351 := bstep (se 1 (by rfl) ⟨1202513, by rfl⟩ : syracuseStep 1603351 = 2405027) B2405027
theorem B2406167 : Blo 1603000 2406167 := bstep (se 1 (by rfl) ⟨1804625, by rfl⟩ : syracuseStep 2406167 = 3609251) B3609251
theorem B2471705 : Blo 1603000 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B1603371 : Blo 1603000 1603371 := bstep (se 1 (by rfl) ⟨1202528, by rfl⟩ : syracuseStep 1603371 = 2405057) B2405057
theorem B1603383 : Blo 1603000 1603383 := bstep (se 1 (by rfl) ⟨1202537, by rfl⟩ : syracuseStep 1603383 = 2405075) B2405075
theorem B3249985 : Blo 1603000 3249985 := bstep (se 2 (by rfl) ⟨1218744, by rfl⟩ : syracuseStep 3249985 = 2437489) B2437489
theorem B3045185 : Blo 1603000 3045185 := bstep (se 2 (by rfl) ⟨1141944, by rfl⟩ : syracuseStep 3045185 = 2283889) B2283889
theorem B1603403 : Blo 1603000 1603403 := bstep (se 1 (by rfl) ⟨1202552, by rfl⟩ : syracuseStep 1603403 = 2405105) B2405105
theorem B1603415 : Blo 1603000 1603415 := bstep (se 1 (by rfl) ⟨1202561, by rfl⟩ : syracuseStep 1603415 = 2405123) B2405123
theorem B2406233 : Blo 1603000 2406233 := bstep (se 2 (by rfl) ⟨902337, by rfl⟩ : syracuseStep 2406233 = 1804675) B1804675
theorem B3610457 : Blo 1603000 3610457 := bstep (se 2 (by rfl) ⟨1353921, by rfl⟩ : syracuseStep 3610457 = 2707843) B2707843
theorem B1603435 : Blo 1603000 1603435 := bstep (se 1 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 1603435 = 2405153) B2405153
theorem B1603447 : Blo 1603000 1603447 := bstep (se 1 (by rfl) ⟨1202585, by rfl⟩ : syracuseStep 1603447 = 2405171) B2405171
theorem B1603467 : Blo 1603000 1603467 := bstep (se 1 (by rfl) ⟨1202600, by rfl⟩ : syracuseStep 1603467 = 2405201) B2405201
theorem B1603479 : Blo 1603000 1603479 := bstep (se 1 (by rfl) ⟨1202609, by rfl⟩ : syracuseStep 1603479 = 2405219) B2405219
theorem B1603499 : Blo 1603000 1603499 := bstep (se 1 (by rfl) ⟨1202624, by rfl⟩ : syracuseStep 1603499 = 2405249) B2405249
theorem B3610547 : Blo 1603000 3610547 := bstep (se 1 (by rfl) ⟨2707910, by rfl⟩ : syracuseStep 3610547 = 5415821) B5415821
theorem B1603511 : Blo 1603000 1603511 := bstep (se 1 (by rfl) ⟨1202633, by rfl⟩ : syracuseStep 1603511 = 2405267) B2405267
theorem B1603531 : Blo 1603000 1603531 := bstep (se 1 (by rfl) ⟨1202648, by rfl⟩ : syracuseStep 1603531 = 2405297) B2405297
theorem B2406347 : Blo 1603000 2406347 := bstep (se 1 (by rfl) ⟨1804760, by rfl⟩ : syracuseStep 2406347 = 3609521) B3609521
theorem B3856331 : Blo 1603000 3856331 := bstep (se 1 (by rfl) ⟨2892248, by rfl⟩ : syracuseStep 3856331 = 5784497) B5784497
theorem B1603543 : Blo 1603000 1603543 := bstep (se 1 (by rfl) ⟨1202657, by rfl⟩ : syracuseStep 1603543 = 2405315) B2405315
theorem B2406359 : Blo 1603000 2406359 := bstep (se 1 (by rfl) ⟨1804769, by rfl⟩ : syracuseStep 2406359 = 3609539) B3609539
theorem B21936089 : Blo 1603000 21936089 := bstep (se 2 (by rfl) ⟨8226033, by rfl⟩ : syracuseStep 21936089 = 16452067) B16452067
theorem B3610583 : Blo 1603000 3610583 := bstep (se 1 (by rfl) ⟨2707937, by rfl⟩ : syracuseStep 3610583 = 5415875) B5415875
theorem B1603563 : Blo 1603000 1603563 := bstep (se 1 (by rfl) ⟨1202672, by rfl⟩ : syracuseStep 1603563 = 2405345) B2405345
theorem B1603575 : Blo 1603000 1603575 := bstep (se 1 (by rfl) ⟨1202681, by rfl⟩ : syracuseStep 1603575 = 2405363) B2405363
theorem B1603595 : Blo 1603000 1603595 := bstep (se 1 (by rfl) ⟨1202696, by rfl⟩ : syracuseStep 1603595 = 2405393) B2405393
theorem B1603607 : Blo 1603000 1603607 := bstep (se 1 (by rfl) ⟨1202705, by rfl⟩ : syracuseStep 1603607 = 2405411) B2405411
theorem B2406425 : Blo 1603000 2406425 := bstep (se 2 (by rfl) ⟨902409, by rfl⟩ : syracuseStep 2406425 = 1804819) B1804819
theorem B1603627 : Blo 1603000 1603627 := bstep (se 1 (by rfl) ⟨1202720, by rfl⟩ : syracuseStep 1603627 = 2405441) B2405441
theorem B8124461 : Blo 1603000 8124461 := bstep (se 3 (by rfl) ⟨1523336, by rfl⟩ : syracuseStep 8124461 = 3046673) B3046673
theorem B1603639 : Blo 1603000 1603639 := bstep (se 1 (by rfl) ⟨1202729, by rfl⟩ : syracuseStep 1603639 = 2405459) B2405459
theorem B4061249 : Blo 1603000 4061249 := bstep (se 2 (by rfl) ⟨1522968, by rfl⟩ : syracuseStep 4061249 = 3045937) B3045937
theorem B1603659 : Blo 1603000 1603659 := bstep (se 1 (by rfl) ⟨1202744, by rfl⟩ : syracuseStep 1603659 = 2405489) B2405489
theorem B3045451 : Blo 1603000 3045451 := bstep (se 1 (by rfl) ⟨2284088, by rfl⟩ : syracuseStep 3045451 = 4568177) B4568177
theorem B1603671 : Blo 1603000 1603671 := bstep (se 1 (by rfl) ⟨1202753, by rfl⟩ : syracuseStep 1603671 = 2405507) B2405507
theorem B1603691 : Blo 1603000 1603691 := bstep (se 1 (by rfl) ⟨1202768, by rfl⟩ : syracuseStep 1603691 = 2405537) B2405537
theorem B1603703 : Blo 1603000 1603703 := bstep (se 1 (by rfl) ⟨1202777, by rfl⟩ : syracuseStep 1603703 = 2405555) B2405555
theorem B1603723 : Blo 1603000 1603723 := bstep (se 1 (by rfl) ⟨1202792, by rfl⟩ : syracuseStep 1603723 = 2405585) B2405585
theorem B2406539 : Blo 1603000 2406539 := bstep (se 1 (by rfl) ⟨1804904, by rfl⟩ : syracuseStep 2406539 = 3609809) B3609809
theorem B3610763 : Blo 1603000 3610763 := bstep (se 1 (by rfl) ⟨2708072, by rfl⟩ : syracuseStep 3610763 = 5416145) B5416145
theorem B1603735 : Blo 1603000 1603735 := bstep (se 1 (by rfl) ⟨1202801, by rfl⟩ : syracuseStep 1603735 = 2405603) B2405603
theorem B2406551 : Blo 1603000 2406551 := bstep (se 1 (by rfl) ⟨1804913, by rfl⟩ : syracuseStep 2406551 = 3609827) B3609827
theorem B1603755 : Blo 1603000 1603755 := bstep (se 1 (by rfl) ⟨1202816, by rfl⟩ : syracuseStep 1603755 = 2405633) B2405633
theorem B1603767 : Blo 1603000 1603767 := bstep (se 1 (by rfl) ⟨1202825, by rfl⟩ : syracuseStep 1603767 = 2405651) B2405651
theorem B4569281 : Blo 1603000 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B3610817 : Blo 1603000 3610817 := bstep (se 2 (by rfl) ⟨1354056, by rfl⟩ : syracuseStep 3610817 = 2708113) B2708113
theorem B1603787 : Blo 1603000 1603787 := bstep (se 1 (by rfl) ⟨1202840, by rfl⟩ : syracuseStep 1603787 = 2405681) B2405681
theorem B5413067 : Blo 1603000 5413067 := bstep (se 1 (by rfl) ⟨4059800, by rfl⟩ : syracuseStep 5413067 = 8119601) B8119601
theorem B1603799 : Blo 1603000 1603799 := bstep (se 1 (by rfl) ⟨1202849, by rfl⟩ : syracuseStep 1603799 = 2405699) B2405699
theorem B2406617 : Blo 1603000 2406617 := bstep (se 2 (by rfl) ⟨902481, by rfl⟩ : syracuseStep 2406617 = 1804963) B1804963
theorem B1603819 : Blo 1603000 1603819 := bstep (se 1 (by rfl) ⟨1202864, by rfl⟩ : syracuseStep 1603819 = 2405729) B2405729
theorem B1603831 : Blo 1603000 1603831 := bstep (se 1 (by rfl) ⟨1202873, by rfl⟩ : syracuseStep 1603831 = 2405747) B2405747
theorem B1603851 : Blo 1603000 1603851 := bstep (se 1 (by rfl) ⟨1202888, by rfl⟩ : syracuseStep 1603851 = 2405777) B2405777
theorem B7706897 : Blo 1603000 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B1603863 : Blo 1603000 1603863 := bstep (se 1 (by rfl) ⟨1202897, by rfl⟩ : syracuseStep 1603863 = 2405795) B2405795
theorem B3471641 : Blo 1603000 3471641 := bstep (se 2 (by rfl) ⟨1301865, by rfl⟩ : syracuseStep 3471641 = 2603731) B2603731
theorem B1603883 : Blo 1603000 1603883 := bstep (se 1 (by rfl) ⟨1202912, by rfl⟩ : syracuseStep 1603883 = 2405825) B2405825
theorem B1603895 : Blo 1603000 1603895 := bstep (se 1 (by rfl) ⟨1202921, by rfl⟩ : syracuseStep 1603895 = 2405843) B2405843
theorem B4692289 : Blo 1603000 4692289 := bstep (se 2 (by rfl) ⟨1759608, by rfl⟩ : syracuseStep 4692289 = 3519217) B3519217
theorem B1603915 : Blo 1603000 1603915 := bstep (se 1 (by rfl) ⟨1202936, by rfl⟩ : syracuseStep 1603915 = 2405873) B2405873
theorem B2406731 : Blo 1603000 2406731 := bstep (se 1 (by rfl) ⟨1805048, by rfl⟩ : syracuseStep 2406731 = 3610097) B3610097
theorem B1603927 : Blo 1603000 1603927 := bstep (se 1 (by rfl) ⟨1202945, by rfl⟩ : syracuseStep 1603927 = 2405891) B2405891
theorem B2406743 : Blo 1603000 2406743 := bstep (se 1 (by rfl) ⟨1805057, by rfl⟩ : syracuseStep 2406743 = 3610115) B3610115
theorem B20560229 : Blo 1603000 20560229 := bstep (se 4 (by rfl) ⟨1927521, by rfl⟩ : syracuseStep 20560229 = 3855043) B3855043
theorem B1603947 : Blo 1603000 1603947 := bstep (se 1 (by rfl) ⟨1202960, by rfl⟩ : syracuseStep 1603947 = 2405921) B2405921
theorem B1603959 : Blo 1603000 1603959 := bstep (se 1 (by rfl) ⟨1202969, by rfl⟩ : syracuseStep 1603959 = 2405939) B2405939
theorem B1603979 : Blo 1603000 1603979 := bstep (se 1 (by rfl) ⟨1202984, by rfl⟩ : syracuseStep 1603979 = 2405969) B2405969
theorem B1603991 : Blo 1603000 1603991 := bstep (se 1 (by rfl) ⟨1202993, by rfl⟩ : syracuseStep 1603991 = 2405987) B2405987
theorem B2406809 : Blo 1603000 2406809 := bstep (se 2 (by rfl) ⟨902553, by rfl⟩ : syracuseStep 2406809 = 1805107) B1805107
theorem B3611033 : Blo 1603000 3611033 := bstep (se 2 (by rfl) ⟨1354137, by rfl⟩ : syracuseStep 3611033 = 2708275) B2708275
theorem B1604011 : Blo 1603000 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B1604023 : Blo 1603000 1604023 := bstep (se 1 (by rfl) ⟨1203017, by rfl⟩ : syracuseStep 1604023 = 2406035) B2406035
theorem B1604043 : Blo 1603000 1604043 := bstep (se 1 (by rfl) ⟨1203032, by rfl⟩ : syracuseStep 1604043 = 2406065) B2406065
theorem B1604055 : Blo 1603000 1604055 := bstep (se 1 (by rfl) ⟨1203041, by rfl⟩ : syracuseStep 1604055 = 2406083) B2406083
theorem B5413337 : Blo 1603000 5413337 := bstep (se 2 (by rfl) ⟨2030001, by rfl⟩ : syracuseStep 5413337 = 4060003) B4060003
theorem B1604075 : Blo 1603000 1604075 := bstep (se 1 (by rfl) ⟨1203056, by rfl⟩ : syracuseStep 1604075 = 2406113) B2406113
theorem B3660275 : Blo 1603000 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B1604087 : Blo 1603000 1604087 := bstep (se 1 (by rfl) ⟨1203065, by rfl⟩ : syracuseStep 1604087 = 2406131) B2406131
theorem B3611123 : Blo 1603000 3611123 := bstep (se 1 (by rfl) ⟨2708342, by rfl⟩ : syracuseStep 3611123 = 5416685) B5416685
theorem B1604107 : Blo 1603000 1604107 := bstep (se 1 (by rfl) ⟨1203080, by rfl⟩ : syracuseStep 1604107 = 2406161) B2406161
theorem B3045899 : Blo 1603000 3045899 := bstep (se 1 (by rfl) ⟨2284424, by rfl⟩ : syracuseStep 3045899 = 4568849) B4568849
theorem B2406923 : Blo 1603000 2406923 := bstep (se 1 (by rfl) ⟨1805192, by rfl⟩ : syracuseStep 2406923 = 3610385) B3610385
theorem B1604119 : Blo 1603000 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B2406935 : Blo 1603000 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B5282327 : Blo 1603000 5282327 := bstep (se 1 (by rfl) ⟨3961745, by rfl⟩ : syracuseStep 5282327 = 7923491) B7923491
theorem B3611159 : Blo 1603000 3611159 := bstep (se 1 (by rfl) ⟨2708369, by rfl⟩ : syracuseStep 3611159 = 5416739) B5416739
theorem B1604139 : Blo 1603000 1604139 := bstep (se 1 (by rfl) ⟨1203104, by rfl⟩ : syracuseStep 1604139 = 2406209) B2406209
theorem B1604151 : Blo 1603000 1604151 := bstep (se 1 (by rfl) ⟨1203113, by rfl⟩ : syracuseStep 1604151 = 2406227) B2406227
theorem B6093377 : Blo 1603000 6093377 := bstep (se 2 (by rfl) ⟨2285016, by rfl⟩ : syracuseStep 6093377 = 4570033) B4570033
theorem B1604171 : Blo 1603000 1604171 := bstep (se 1 (by rfl) ⟨1203128, by rfl⟩ : syracuseStep 1604171 = 2406257) B2406257
theorem B1604183 : Blo 1603000 1604183 := bstep (se 1 (by rfl) ⟨1203137, by rfl⟩ : syracuseStep 1604183 = 2406275) B2406275
theorem B4061785 : Blo 1603000 4061785 := bstep (se 2 (by rfl) ⟨1523169, by rfl⟩ : syracuseStep 4061785 = 3046339) B3046339
theorem B2407001 : Blo 1603000 2407001 := bstep (se 2 (by rfl) ⟨902625, by rfl⟩ : syracuseStep 2407001 = 1805251) B1805251
theorem B1604203 : Blo 1603000 1604203 := bstep (se 1 (by rfl) ⟨1203152, by rfl⟩ : syracuseStep 1604203 = 2406305) B2406305
theorem B1604215 : Blo 1603000 1604215 := bstep (se 1 (by rfl) ⟨1203161, by rfl⟩ : syracuseStep 1604215 = 2406323) B2406323
theorem B20544131 : Blo 1603000 20544131 := bstep (se 1 (by rfl) ⟨15408098, by rfl⟩ : syracuseStep 20544131 = 30816197) B30816197
theorem B1604235 : Blo 1603000 1604235 := bstep (se 1 (by rfl) ⟨1203176, by rfl⟩ : syracuseStep 1604235 = 2406353) B2406353
theorem B1604247 : Blo 1603000 1604247 := bstep (se 1 (by rfl) ⟨1203185, by rfl⟩ : syracuseStep 1604247 = 2406371) B2406371
theorem B1604267 : Blo 1603000 1604267 := bstep (se 1 (by rfl) ⟨1203200, by rfl⟩ : syracuseStep 1604267 = 2406401) B2406401
theorem B5782189 : Blo 1603000 5782189 := bstep (se 3 (by rfl) ⟨1084160, by rfl⟩ : syracuseStep 5782189 = 2168321) B2168321
theorem B1604279 : Blo 1603000 1604279 := bstep (se 1 (by rfl) ⟨1203209, by rfl⟩ : syracuseStep 1604279 = 2406419) B2406419
theorem B3046081 : Blo 1603000 3046081 := bstep (se 2 (by rfl) ⟨1142280, by rfl⟩ : syracuseStep 3046081 = 2284561) B2284561
theorem B1604299 : Blo 1603000 1604299 := bstep (se 1 (by rfl) ⟨1203224, by rfl⟩ : syracuseStep 1604299 = 2406449) B2406449
theorem B2407115 : Blo 1603000 2407115 := bstep (se 1 (by rfl) ⟨1805336, by rfl⟩ : syracuseStep 2407115 = 3610673) B3610673
theorem B1604311 : Blo 1603000 1604311 := bstep (se 1 (by rfl) ⟨1203233, by rfl⟩ : syracuseStep 1604311 = 2406467) B2406467
theorem B2407127 : Blo 1603000 2407127 := bstep (se 1 (by rfl) ⟨1805345, by rfl⟩ : syracuseStep 2407127 = 3610691) B3610691
theorem B4569817 : Blo 1603000 4569817 := bstep (se 2 (by rfl) ⟨1713681, by rfl⟩ : syracuseStep 4569817 = 3427363) B3427363
theorem B1604331 : Blo 1603000 1604331 := bstep (se 1 (by rfl) ⟨1203248, by rfl⟩ : syracuseStep 1604331 = 2406497) B2406497
theorem B1604343 : Blo 1603000 1604343 := bstep (se 1 (by rfl) ⟨1203257, by rfl⟩ : syracuseStep 1604343 = 2406515) B2406515
theorem B1604363 : Blo 1603000 1604363 := bstep (se 1 (by rfl) ⟨1203272, by rfl⟩ : syracuseStep 1604363 = 2406545) B2406545
theorem B8117009 : Blo 1603000 8117009 := bstep (se 2 (by rfl) ⟨3043878, by rfl⟩ : syracuseStep 8117009 = 6087757) B6087757
theorem B1604375 : Blo 1603000 1604375 := bstep (se 1 (by rfl) ⟨1203281, by rfl⟩ : syracuseStep 1604375 = 2406563) B2406563
theorem B2407193 : Blo 1603000 2407193 := bstep (se 2 (by rfl) ⟨902697, by rfl⟩ : syracuseStep 2407193 = 1805395) B1805395
theorem B1604395 : Blo 1603000 1604395 := bstep (se 1 (by rfl) ⟨1203296, by rfl⟩ : syracuseStep 1604395 = 2406593) B2406593
theorem B1604407 : Blo 1603000 1604407 := bstep (se 1 (by rfl) ⟨1203305, by rfl⟩ : syracuseStep 1604407 = 2406611) B2406611
theorem B1604427 : Blo 1603000 1604427 := bstep (se 1 (by rfl) ⟨1203320, by rfl⟩ : syracuseStep 1604427 = 2406641) B2406641
theorem B1604439 : Blo 1603000 1604439 := bstep (se 1 (by rfl) ⟨1203329, by rfl⟩ : syracuseStep 1604439 = 2406659) B2406659
theorem B1604459 : Blo 1603000 1604459 := bstep (se 1 (by rfl) ⟨1203344, by rfl⟩ : syracuseStep 1604459 = 2406689) B2406689
theorem B1604471 : Blo 1603000 1604471 := bstep (se 1 (by rfl) ⟨1203353, by rfl⟩ : syracuseStep 1604471 = 2406707) B2406707
theorem B6175619 : Blo 1603000 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B1604491 : Blo 1603000 1604491 := bstep (se 1 (by rfl) ⟨1203368, by rfl⟩ : syracuseStep 1604491 = 2406737) B2406737
theorem B2407307 : Blo 1603000 2407307 := bstep (se 1 (by rfl) ⟨1805480, by rfl⟩ : syracuseStep 2407307 = 3610961) B3610961
theorem B1604503 : Blo 1603000 1604503 := bstep (se 1 (by rfl) ⟨1203377, by rfl⟩ : syracuseStep 1604503 = 2406755) B2406755
theorem B2407319 : Blo 1603000 2407319 := bstep (se 1 (by rfl) ⟨1805489, by rfl⟩ : syracuseStep 2407319 = 3610979) B3610979
theorem B1604523 : Blo 1603000 1604523 := bstep (se 1 (by rfl) ⟨1203392, by rfl⟩ : syracuseStep 1604523 = 2406785) B2406785
theorem B8117171 : Blo 1603000 8117171 := bstep (se 1 (by rfl) ⟨6087878, by rfl⟩ : syracuseStep 8117171 = 12175757) B12175757
theorem B1604535 : Blo 1603000 1604535 := bstep (se 1 (by rfl) ⟨1203401, by rfl⟩ : syracuseStep 1604535 = 2406803) B2406803
theorem B3251137 : Blo 1603000 3251137 := bstep (se 2 (by rfl) ⟨1219176, by rfl⟩ : syracuseStep 3251137 = 2438353) B2438353
theorem B1604555 : Blo 1603000 1604555 := bstep (se 1 (by rfl) ⟨1203416, by rfl⟩ : syracuseStep 1604555 = 2406833) B2406833
theorem B1604567 : Blo 1603000 1604567 := bstep (se 1 (by rfl) ⟨1203425, by rfl⟩ : syracuseStep 1604567 = 2406851) B2406851
theorem B2407385 : Blo 1603000 2407385 := bstep (se 2 (by rfl) ⟨902769, by rfl⟩ : syracuseStep 2407385 = 1805539) B1805539
theorem B1604587 : Blo 1603000 1604587 := bstep (se 1 (by rfl) ⟨1203440, by rfl⟩ : syracuseStep 1604587 = 2406881) B2406881
theorem B1604599 : Blo 1603000 1604599 := bstep (se 1 (by rfl) ⟨1203449, by rfl⟩ : syracuseStep 1604599 = 2406899) B2406899
theorem B1604619 : Blo 1603000 1604619 := bstep (se 1 (by rfl) ⟨1203464, by rfl⟩ : syracuseStep 1604619 = 2406929) B2406929
theorem B9133073 : Blo 1603000 9133073 := bstep (se 2 (by rfl) ⟨3424902, by rfl⟩ : syracuseStep 9133073 = 6849805) B6849805
theorem B1604631 : Blo 1603000 1604631 := bstep (se 1 (by rfl) ⟨1203473, by rfl⟩ : syracuseStep 1604631 = 2406947) B2406947
theorem B3046423 : Blo 1603000 3046423 := bstep (se 1 (by rfl) ⟨2284817, by rfl⟩ : syracuseStep 3046423 = 4569635) B4569635
theorem B1604651 : Blo 1603000 1604651 := bstep (se 1 (by rfl) ⟨1203488, by rfl⟩ : syracuseStep 1604651 = 2406977) B2406977
theorem B1604663 : Blo 1603000 1604663 := bstep (se 1 (by rfl) ⟨1203497, by rfl⟩ : syracuseStep 1604663 = 2406995) B2406995
theorem B1604683 : Blo 1603000 1604683 := bstep (se 1 (by rfl) ⟨1203512, by rfl⟩ : syracuseStep 1604683 = 2407025) B2407025
theorem B2407499 : Blo 1603000 2407499 := bstep (se 1 (by rfl) ⟨1805624, by rfl⟩ : syracuseStep 2407499 = 3611249) B3611249
theorem B1604695 : Blo 1603000 1604695 := bstep (se 1 (by rfl) ⟨1203521, by rfl⟩ : syracuseStep 1604695 = 2407043) B2407043
theorem B1604715 : Blo 1603000 1604715 := bstep (se 1 (by rfl) ⟨1203536, by rfl⟩ : syracuseStep 1604715 = 2407073) B2407073
theorem B1604727 : Blo 1603000 1604727 := bstep (se 1 (by rfl) ⟨1203545, by rfl⟩ : syracuseStep 1604727 = 2407091) B2407091
theorem B1604747 : Blo 1603000 1604747 := bstep (se 1 (by rfl) ⟨1203560, by rfl⟩ : syracuseStep 1604747 = 2407121) B2407121
theorem B5414039 : Blo 1603000 5414039 := bstep (se 1 (by rfl) ⟨4060529, by rfl⟩ : syracuseStep 5414039 = 8121059) B8121059
theorem B1604759 : Blo 1603000 1604759 := bstep (se 1 (by rfl) ⟨1203569, by rfl⟩ : syracuseStep 1604759 = 2407139) B2407139
theorem B1604779 : Blo 1603000 1604779 := bstep (se 1 (by rfl) ⟨1203584, by rfl⟩ : syracuseStep 1604779 = 2407169) B2407169
theorem B1604791 : Blo 1603000 1604791 := bstep (se 1 (by rfl) ⟨1203593, by rfl⟩ : syracuseStep 1604791 = 2407187) B2407187
theorem B1604811 : Blo 1603000 1604811 := bstep (se 1 (by rfl) ⟨1203608, by rfl⟩ : syracuseStep 1604811 = 2407217) B2407217
theorem B1604823 : Blo 1603000 1604823 := bstep (se 1 (by rfl) ⟨1203617, by rfl⟩ : syracuseStep 1604823 = 2407235) B2407235
theorem B1604843 : Blo 1603000 1604843 := bstep (se 1 (by rfl) ⟨1203632, by rfl⟩ : syracuseStep 1604843 = 2407265) B2407265
theorem B3046643 : Blo 1603000 3046643 := bstep (se 1 (by rfl) ⟨2284982, by rfl⟩ : syracuseStep 3046643 = 4569965) B4569965
theorem B1604855 : Blo 1603000 1604855 := bstep (se 1 (by rfl) ⟨1203641, by rfl⟩ : syracuseStep 1604855 = 2407283) B2407283
theorem B2891009 : Blo 1603000 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B1604875 : Blo 1603000 1604875 := bstep (se 1 (by rfl) ⟨1203656, by rfl⟩ : syracuseStep 1604875 = 2407313) B2407313
theorem B1604887 : Blo 1603000 1604887 := bstep (se 1 (by rfl) ⟨1203665, by rfl⟩ : syracuseStep 1604887 = 2407331) B2407331
theorem B1604907 : Blo 1603000 1604907 := bstep (se 1 (by rfl) ⟨1203680, by rfl⟩ : syracuseStep 1604907 = 2407361) B2407361
theorem B1604919 : Blo 1603000 1604919 := bstep (se 1 (by rfl) ⟨1203689, by rfl⟩ : syracuseStep 1604919 = 2407379) B2407379
theorem B26008897 : Blo 1603000 26008897 := bstep (se 2 (by rfl) ⟨9753336, by rfl⟩ : syracuseStep 26008897 = 19506673) B19506673
theorem B10280267 : Blo 1603000 10280267 := bstep (se 1 (by rfl) ⟨7710200, by rfl⟩ : syracuseStep 10280267 = 15420401) B15420401
theorem B2030923 : Blo 1603000 2030923 := bstep (se 1 (by rfl) ⟨1523192, by rfl⟩ : syracuseStep 2030923 = 3046385) B3046385
theorem B1604939 : Blo 1603000 1604939 := bstep (se 1 (by rfl) ⟨1203704, by rfl⟩ : syracuseStep 1604939 = 2407409) B2407409
theorem B1604951 : Blo 1603000 1604951 := bstep (se 1 (by rfl) ⟨1203713, by rfl⟩ : syracuseStep 1604951 = 2407427) B2407427
theorem B1604971 : Blo 1603000 1604971 := bstep (se 1 (by rfl) ⟨1203728, by rfl⟩ : syracuseStep 1604971 = 2407457) B2407457
theorem B1604983 : Blo 1603000 1604983 := bstep (se 1 (by rfl) ⟨1203737, by rfl⟩ : syracuseStep 1604983 = 2407475) B2407475
theorem B16055729 : Blo 1603000 16055729 := bstep (se 2 (by rfl) ⟨6020898, by rfl⟩ : syracuseStep 16055729 = 12041797) B12041797
theorem B3046871 : Blo 1603000 3046871 := bstep (se 1 (by rfl) ⟨2285153, by rfl⟩ : syracuseStep 3046871 = 4570307) B4570307
theorem B3423809 : Blo 1603000 3423809 := bstep (se 2 (by rfl) ⟨1283928, by rfl⟩ : syracuseStep 3423809 = 2567857) B2567857
theorem B13704835 : Blo 1603000 13704835 := bstep (se 1 (by rfl) ⟨10278626, by rfl⟩ : syracuseStep 13704835 = 20557253) B20557253
theorem B5414579 : Blo 1603000 5414579 := bstep (se 1 (by rfl) ⟨4060934, by rfl⟩ : syracuseStep 5414579 = 8121869) B8121869
theorem B5488345 : Blo 1603000 5488345 := bstep (se 2 (by rfl) ⟨2058129, by rfl⟩ : syracuseStep 5488345 = 4116259) B4116259
theorem B6848387 : Blo 1603000 6848387 := bstep (se 1 (by rfl) ⟨5136290, by rfl⟩ : syracuseStep 6848387 = 10272581) B10272581
theorem B6086573 : Blo 1603000 6086573 := bstep (se 3 (by rfl) ⟨1141232, by rfl⟩ : syracuseStep 6086573 = 2282465) B2282465
theorem B5414849 : Blo 1603000 5414849 := bstep (se 2 (by rfl) ⟨2030568, by rfl⟩ : syracuseStep 5414849 = 4061137) B4061137
theorem B6086603 : Blo 1603000 6086603 := bstep (se 1 (by rfl) ⟨4564952, by rfl⟩ : syracuseStep 6086603 = 9129905) B9129905
theorem B18259991 : Blo 1603000 18259991 := bstep (se 1 (by rfl) ⟨13694993, by rfl⟩ : syracuseStep 18259991 = 27389987) B27389987
theorem B12517577 : Blo 1603000 12517577 := bstep (se 2 (by rfl) ⟨4694091, by rfl⟩ : syracuseStep 12517577 = 9388183) B9388183
theorem B3252539 : Blo 1603000 3252539 := bstep (se 1 (by rfl) ⟨2439404, by rfl⟩ : syracuseStep 3252539 = 4878809) B4878809
theorem B5415227 : Blo 1603000 5415227 := bstep (se 1 (by rfl) ⟨4061420, by rfl⟩ : syracuseStep 5415227 = 8122841) B8122841
theorem B6087059 : Blo 1603000 6087059 := bstep (se 1 (by rfl) ⟨4565294, by rfl⟩ : syracuseStep 6087059 = 9130589) B9130589
theorem B14631353 : Blo 1603000 14631353 := bstep (se 2 (by rfl) ⟨5486757, by rfl⟩ : syracuseStep 14631353 = 10973515) B10973515
theorem B12345821 : Blo 1603000 12345821 := bstep (se 3 (by rfl) ⟨2314841, by rfl⟩ : syracuseStep 12345821 = 4629683) B4629683
theorem B34292267 : Blo 1603000 34292267 := bstep (se 1 (by rfl) ⟨25719200, by rfl⟩ : syracuseStep 34292267 = 51438401) B51438401
theorem B18268739 : Blo 1603000 18268739 := bstep (se 1 (by rfl) ⟨13701554, by rfl⟩ : syracuseStep 18268739 = 27403109) B27403109
theorem B5136983 : Blo 1603000 5136983 := bstep (se 1 (by rfl) ⟨3852737, by rfl⟩ : syracuseStep 5136983 = 7705475) B7705475
theorem B7709357 : Blo 1603000 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B5415713 : Blo 1603000 5415713 := bstep (se 2 (by rfl) ⟨2030892, by rfl⟩ : syracuseStep 5415713 = 4061785) B4061785
theorem B9134963 : Blo 1603000 9134963 := bstep (se 1 (by rfl) ⟨6851222, by rfl⟩ : syracuseStep 9134963 = 13702445) B13702445
theorem B7709585 : Blo 1603000 7709585 := bstep (se 2 (by rfl) ⟨2891094, by rfl⟩ : syracuseStep 7709585 = 5782189) B5782189
theorem B13698071 : Blo 1603000 13698071 := bstep (se 1 (by rfl) ⟨10273553, by rfl⟩ : syracuseStep 13698071 = 20547107) B20547107
theorem B5137469 : Blo 1603000 5137469 := bstep (se 3 (by rfl) ⟨963275, by rfl⟩ : syracuseStep 5137469 = 1926551) B1926551
theorem B1803451 : Blo 1603000 1803451 := bstep (se 1 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 1803451 = 2705177) B2705177
theorem B4334849 : Blo 1603000 4334849 := bstep (se 2 (by rfl) ⟨1625568, by rfl⟩ : syracuseStep 4334849 = 3251137) B3251137
theorem B14624059 : Blo 1603000 14624059 := bstep (se 1 (by rfl) ⟨10968044, by rfl⟩ : syracuseStep 14624059 = 21936089) B21936089
theorem B5416307 : Blo 1603000 5416307 := bstep (se 1 (by rfl) ⟨4062230, by rfl⟩ : syracuseStep 5416307 = 8124461) B8124461
theorem B5137931 : Blo 1603000 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B13706819 : Blo 1603000 13706819 := bstep (se 1 (by rfl) ⟨10280114, by rfl⟩ : syracuseStep 13706819 = 20560229) B20560229
theorem B1803919 : Blo 1603000 1803919 := bstep (se 1 (by rfl) ⟨1352939, by rfl⟩ : syracuseStep 1803919 = 2705879) B2705879
theorem B34678529 : Blo 1603000 34678529 := bstep (se 2 (by rfl) ⟨13004448, by rfl⟩ : syracuseStep 34678529 = 26008897) B26008897
theorem B3852179 : Blo 1603000 3852179 := bstep (se 1 (by rfl) ⟨2889134, by rfl⟩ : syracuseStep 3852179 = 5778269) B5778269
theorem B6260627 : Blo 1603000 6260627 := bstep (se 1 (by rfl) ⟨4695470, by rfl⟩ : syracuseStep 6260627 = 9390941) B9390941
theorem B24692633 : Blo 1603000 24692633 := bstep (se 2 (by rfl) ⟨9259737, by rfl⟩ : syracuseStep 24692633 = 18519475) B18519475
theorem B8120249 : Blo 1603000 8120249 := bstep (se 2 (by rfl) ⟨3045093, by rfl⟩ : syracuseStep 8120249 = 6090187) B6090187
theorem B6088715 : Blo 1603000 6088715 := bstep (se 1 (by rfl) ⟨4566536, by rfl⟩ : syracuseStep 6088715 = 9133073) B9133073
theorem B2705467 : Blo 1603000 2705467 := bstep (se 1 (by rfl) ⟨2029100, by rfl⟩ : syracuseStep 2705467 = 4058201) B4058201
theorem B1804423 : Blo 1603000 1804423 := bstep (se 1 (by rfl) ⟨1353317, by rfl⟩ : syracuseStep 1804423 = 2706635) B2706635
theorem B2705609 : Blo 1603000 2705609 := bstep (se 2 (by rfl) ⟨1014603, by rfl⟩ : syracuseStep 2705609 = 2029207) B2029207
theorem B7317793 : Blo 1603000 7317793 := bstep (se 2 (by rfl) ⟨2744172, by rfl⟩ : syracuseStep 7317793 = 5488345) B5488345
theorem B9136421 : Blo 1603000 9136421 := bstep (se 4 (by rfl) ⟨856539, by rfl⟩ : syracuseStep 9136421 = 1713079) B1713079
theorem B1804603 : Blo 1603000 1804603 := bstep (se 1 (by rfl) ⟨1353452, by rfl⟩ : syracuseStep 1804603 = 2706905) B2706905
theorem B3426619 : Blo 1603000 3426619 := bstep (se 1 (by rfl) ⟨2569964, by rfl⟩ : syracuseStep 3426619 = 5139929) B5139929
theorem B3607055 : Blo 1603000 3607055 := bstep (se 1 (by rfl) ⟨2705291, by rfl⟩ : syracuseStep 3607055 = 5410583) B5410583
theorem B3607073 : Blo 1603000 3607073 := bstep (se 2 (by rfl) ⟨1352652, by rfl⟩ : syracuseStep 3607073 = 2705305) B2705305
theorem B4565591 : Blo 1603000 4565591 := bstep (se 1 (by rfl) ⟨3424193, by rfl⟩ : syracuseStep 4565591 = 6848387) B6848387
theorem B4057715 : Blo 1603000 4057715 := bstep (se 1 (by rfl) ⟨3043286, by rfl⟩ : syracuseStep 4057715 = 6086573) B6086573
theorem B4057735 : Blo 1603000 4057735 := bstep (se 1 (by rfl) ⟨3043301, by rfl⟩ : syracuseStep 4057735 = 6086603) B6086603
theorem B39004865 : Blo 1603000 39004865 := bstep (se 2 (by rfl) ⟨14626824, by rfl⟩ : syracuseStep 39004865 = 29253649) B29253649
theorem B1805071 : Blo 1603000 1805071 := bstep (se 1 (by rfl) ⟨1353803, by rfl⟩ : syracuseStep 1805071 = 2707607) B2707607
theorem B12176243 : Blo 1603000 12176243 := bstep (se 1 (by rfl) ⟨9132182, by rfl⟩ : syracuseStep 12176243 = 18264365) B18264365
theorem B3607415 : Blo 1603000 3607415 := bstep (se 1 (by rfl) ⟨2705561, by rfl⟩ : syracuseStep 3607415 = 5411123) B5411123
theorem B2706311 : Blo 1603000 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B4058009 : Blo 1603000 4058009 := bstep (se 2 (by rfl) ⟨1521753, by rfl⟩ : syracuseStep 4058009 = 3043507) B3043507
theorem B23112611 : Blo 1603000 23112611 := bstep (se 1 (by rfl) ⟨17334458, by rfl⟩ : syracuseStep 23112611 = 34668917) B34668917
theorem B26364853 : Blo 1603000 26364853 := bstep (se 5 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 26364853 = 2471705) B2471705
theorem B3607595 : Blo 1603000 3607595 := bstep (se 1 (by rfl) ⟨2705696, by rfl⟩ : syracuseStep 3607595 = 5411393) B5411393
theorem B9137195 : Blo 1603000 9137195 := bstep (se 1 (by rfl) ⟨6852896, by rfl⟩ : syracuseStep 9137195 = 13705793) B13705793
theorem B4058171 : Blo 1603000 4058171 := bstep (se 1 (by rfl) ⟨3043628, by rfl⟩ : syracuseStep 4058171 = 6087257) B6087257
theorem B8121545 : Blo 1603000 8121545 := bstep (se 2 (by rfl) ⟨3045579, by rfl⟩ : syracuseStep 8121545 = 6091159) B6091159
theorem B5139713 : Blo 1603000 5139713 := bstep (se 2 (by rfl) ⟨1927392, by rfl⟩ : syracuseStep 5139713 = 3854785) B3854785
theorem B1805575 : Blo 1603000 1805575 := bstep (se 1 (by rfl) ⟨1354181, by rfl⟩ : syracuseStep 1805575 = 2708363) B2708363
theorem B4058383 : Blo 1603000 4058383 := bstep (se 1 (by rfl) ⟨3043787, by rfl⟩ : syracuseStep 4058383 = 6087575) B6087575
theorem B5139827 : Blo 1603000 5139827 := bstep (se 1 (by rfl) ⟨3854870, by rfl⟩ : syracuseStep 5139827 = 7709741) B7709741
theorem B3607955 : Blo 1603000 3607955 := bstep (se 1 (by rfl) ⟨2705966, by rfl⟩ : syracuseStep 3607955 = 5411933) B5411933
theorem B3608009 : Blo 1603000 3608009 := bstep (se 2 (by rfl) ⟨1353003, by rfl⟩ : syracuseStep 3608009 = 2706007) B2706007
theorem B2706959 : Blo 1603000 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B7712279 : Blo 1603000 7712279 := bstep (se 1 (by rfl) ⟨5784209, by rfl⟩ : syracuseStep 7712279 = 11568419) B11568419
theorem B4058657 : Blo 1603000 4058657 := bstep (se 2 (by rfl) ⟨1521996, by rfl⟩ : syracuseStep 4058657 = 3043993) B3043993
theorem B3853939 : Blo 1603000 3853939 := bstep (se 1 (by rfl) ⟨2890454, by rfl⟩ : syracuseStep 3853939 = 5780909) B5780909
theorem B13709209 : Blo 1603000 13709209 := bstep (se 2 (by rfl) ⟨5140953, by rfl⟩ : syracuseStep 13709209 = 10281907) B10281907
theorem B5410745 : Blo 1603000 5410745 := bstep (se 2 (by rfl) ⟨2029029, by rfl⟩ : syracuseStep 5410745 = 4058059) B4058059
theorem B9760733 : Blo 1603000 9760733 := bstep (se 3 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 9760733 = 3660275) B3660275
theorem B2707499 : Blo 1603000 2707499 := bstep (se 1 (by rfl) ⟨2030624, by rfl⟩ : syracuseStep 2707499 = 4061249) B4061249
theorem B4567175 : Blo 1603000 4567175 := bstep (se 1 (by rfl) ⟨3425381, by rfl⟩ : syracuseStep 4567175 = 6850763) B6850763
theorem B3608711 : Blo 1603000 3608711 := bstep (se 1 (by rfl) ⟨2706533, by rfl⟩ : syracuseStep 3608711 = 5413067) B5413067
theorem B2404523 : Blo 1603000 2404523 := bstep (se 1 (by rfl) ⟨1803392, by rfl⟩ : syracuseStep 2404523 = 3606785) B3606785
theorem B9130157 : Blo 1603000 9130157 := bstep (se 3 (by rfl) ⟨1711904, by rfl⟩ : syracuseStep 9130157 = 3423809) B3423809
theorem B2314427 : Blo 1603000 2314427 := bstep (se 1 (by rfl) ⟨1735820, by rfl⟩ : syracuseStep 2314427 = 3471641) B3471641
theorem B2404553 : Blo 1603000 2404553 := bstep (se 2 (by rfl) ⟨901707, by rfl⟩ : syracuseStep 2404553 = 1803415) B1803415
theorem B2404667 : Blo 1603000 2404667 := bstep (se 1 (by rfl) ⟨1803500, by rfl⟩ : syracuseStep 2404667 = 3607001) B3607001
theorem B3608891 : Blo 1603000 3608891 := bstep (se 1 (by rfl) ⟨2706668, by rfl⟩ : syracuseStep 3608891 = 5413337) B5413337
theorem B2404727 : Blo 1603000 2404727 := bstep (se 1 (by rfl) ⟨1803545, by rfl⟩ : syracuseStep 2404727 = 3607091) B3607091
theorem B2404751 : Blo 1603000 2404751 := bstep (se 1 (by rfl) ⟨1803563, by rfl⟩ : syracuseStep 2404751 = 3607127) B3607127
theorem B2404793 : Blo 1603000 2404793 := bstep (se 2 (by rfl) ⟨901797, by rfl⟩ : syracuseStep 2404793 = 1803595) B1803595
theorem B3609017 : Blo 1603000 3609017 := bstep (se 2 (by rfl) ⟨1353381, by rfl⟩ : syracuseStep 3609017 = 2706763) B2706763
theorem B2707897 : Blo 1603000 2707897 := bstep (se 2 (by rfl) ⟨1015461, by rfl⟩ : syracuseStep 2707897 = 2030923) B2030923
theorem B9138653 : Blo 1603000 9138653 := bstep (se 3 (by rfl) ⟨1713497, by rfl⟩ : syracuseStep 9138653 = 3426995) B3426995
theorem B2404871 : Blo 1603000 2404871 := bstep (se 1 (by rfl) ⟨1803653, by rfl⟩ : syracuseStep 2404871 = 3607307) B3607307
theorem B5411339 : Blo 1603000 5411339 := bstep (se 1 (by rfl) ⟨4058504, by rfl⟩ : syracuseStep 5411339 = 8117009) B8117009
theorem B4059659 : Blo 1603000 4059659 := bstep (se 1 (by rfl) ⟨3044744, by rfl⟩ : syracuseStep 4059659 = 6089489) B6089489
theorem B2404907 : Blo 1603000 2404907 := bstep (se 1 (by rfl) ⟨1803680, by rfl⟩ : syracuseStep 2404907 = 3607361) B3607361
theorem B2407439 : Blo 1603000 2407439 := bstep (se 1 (by rfl) ⟨1805579, by rfl⟩ : syracuseStep 2407439 = 3611159) B3611159
theorem B2404937 : Blo 1603000 2404937 := bstep (se 2 (by rfl) ⟨901851, by rfl⟩ : syracuseStep 2404937 = 1803703) B1803703
theorem B4117079 : Blo 1603000 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B5411447 : Blo 1603000 5411447 := bstep (se 1 (by rfl) ⟨4058585, by rfl⟩ : syracuseStep 5411447 = 8117171) B8117171
theorem B2405051 : Blo 1603000 2405051 := bstep (se 1 (by rfl) ⟨1803788, by rfl⟩ : syracuseStep 2405051 = 3607577) B3607577
theorem B27792089 : Blo 1603000 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B2405111 : Blo 1603000 2405111 := bstep (se 1 (by rfl) ⟨1803833, by rfl⟩ : syracuseStep 2405111 = 3607667) B3607667
theorem B2405135 : Blo 1603000 2405135 := bstep (se 1 (by rfl) ⟨1803851, by rfl⟩ : syracuseStep 2405135 = 3607703) B3607703
theorem B4567823 : Blo 1603000 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B3609359 : Blo 1603000 3609359 := bstep (se 1 (by rfl) ⟨2707019, by rfl⟩ : syracuseStep 3609359 = 5414039) B5414039
theorem B3609377 : Blo 1603000 3609377 := bstep (se 2 (by rfl) ⟨1353516, by rfl⟩ : syracuseStep 3609377 = 2707033) B2707033
theorem B2405177 : Blo 1603000 2405177 := bstep (se 2 (by rfl) ⟨901941, by rfl⟩ : syracuseStep 2405177 = 1803883) B1803883
theorem B18273113 : Blo 1603000 18273113 := bstep (se 2 (by rfl) ⟨6852417, by rfl⟩ : syracuseStep 18273113 = 13704835) B13704835
theorem B2405255 : Blo 1603000 2405255 := bstep (se 1 (by rfl) ⟨1803941, by rfl⟩ : syracuseStep 2405255 = 3607883) B3607883
theorem B6853511 : Blo 1603000 6853511 := bstep (se 1 (by rfl) ⟨5140133, by rfl⟩ : syracuseStep 6853511 = 10280267) B10280267
theorem B3044243 : Blo 1603000 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B2405291 : Blo 1603000 2405291 := bstep (se 1 (by rfl) ⟨1803968, by rfl⟩ : syracuseStep 2405291 = 3607937) B3607937
theorem B5641145 : Blo 1603000 5641145 := bstep (se 2 (by rfl) ⟨2115429, by rfl⟩ : syracuseStep 5641145 = 4230859) B4230859
theorem B2405321 : Blo 1603000 2405321 := bstep (se 2 (by rfl) ⟨901995, by rfl⟩ : syracuseStep 2405321 = 1803991) B1803991
theorem B3044297 : Blo 1603000 3044297 := bstep (se 2 (by rfl) ⟨1141611, by rfl⟩ : syracuseStep 3044297 = 2283223) B2283223
theorem B3707849 : Blo 1603000 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B10703819 : Blo 1603000 10703819 := bstep (se 1 (by rfl) ⟨8027864, by rfl⟩ : syracuseStep 10703819 = 16055729) B16055729
theorem B3044395 : Blo 1603000 3044395 := bstep (se 1 (by rfl) ⟨2283296, by rfl⟩ : syracuseStep 3044395 = 4566593) B4566593
theorem B2405435 : Blo 1603000 2405435 := bstep (se 1 (by rfl) ⟨1804076, by rfl⟩ : syracuseStep 2405435 = 3608153) B3608153
theorem B2405495 : Blo 1603000 2405495 := bstep (se 1 (by rfl) ⟨1804121, by rfl⟩ : syracuseStep 2405495 = 3608243) B3608243
theorem B3609719 : Blo 1603000 3609719 := bstep (se 1 (by rfl) ⟨2707289, by rfl⟩ : syracuseStep 3609719 = 5414579) B5414579
theorem B2405519 : Blo 1603000 2405519 := bstep (se 1 (by rfl) ⟨1804139, by rfl⟩ : syracuseStep 2405519 = 3608279) B3608279
theorem B4060307 : Blo 1603000 4060307 := bstep (se 1 (by rfl) ⟨3045230, by rfl⟩ : syracuseStep 4060307 = 6090461) B6090461
theorem B2405561 : Blo 1603000 2405561 := bstep (se 2 (by rfl) ⟨902085, by rfl⟩ : syracuseStep 2405561 = 1804171) B1804171
theorem B5412041 : Blo 1603000 5412041 := bstep (se 2 (by rfl) ⟨2029515, by rfl⟩ : syracuseStep 5412041 = 4059031) B4059031
theorem B2405639 : Blo 1603000 2405639 := bstep (se 1 (by rfl) ⟨1804229, by rfl⟩ : syracuseStep 2405639 = 3608459) B3608459
theorem B3044623 : Blo 1603000 3044623 := bstep (se 1 (by rfl) ⟨2283467, by rfl⟩ : syracuseStep 3044623 = 4566935) B4566935
theorem B2405675 : Blo 1603000 2405675 := bstep (se 1 (by rfl) ⟨1804256, by rfl⟩ : syracuseStep 2405675 = 3608513) B3608513
theorem B3609899 : Blo 1603000 3609899 := bstep (se 1 (by rfl) ⟨2707424, by rfl⟩ : syracuseStep 3609899 = 5414849) B5414849
theorem B2405705 : Blo 1603000 2405705 := bstep (se 2 (by rfl) ⟨902139, by rfl⟩ : syracuseStep 2405705 = 1804279) B1804279
theorem B4060601 : Blo 1603000 4060601 := bstep (se 2 (by rfl) ⟨1522725, by rfl⟩ : syracuseStep 4060601 = 3045451) B3045451
theorem B1603003 : Blo 1603000 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B2405819 : Blo 1603000 2405819 := bstep (se 1 (by rfl) ⟨1804364, by rfl⟩ : syracuseStep 2405819 = 3608729) B3608729
theorem B2405879 : Blo 1603000 2405879 := bstep (se 1 (by rfl) ⟨1804409, by rfl⟩ : syracuseStep 2405879 = 3608819) B3608819
theorem B31233539 : Blo 1603000 31233539 := bstep (se 1 (by rfl) ⟨23425154, by rfl⟩ : syracuseStep 31233539 = 46850309) B46850309
theorem B24696323 : Blo 1603000 24696323 := bstep (se 1 (by rfl) ⟨18522242, by rfl⟩ : syracuseStep 24696323 = 37044485) B37044485
theorem B1603079 : Blo 1603000 1603079 := bstep (se 1 (by rfl) ⟨1202309, by rfl⟩ : syracuseStep 1603079 = 2404619) B2404619
theorem B1603087 : Blo 1603000 1603087 := bstep (se 1 (by rfl) ⟨1202315, by rfl⟩ : syracuseStep 1603087 = 2404631) B2404631
theorem B2283023 : Blo 1603000 2283023 := bstep (se 1 (by rfl) ⟨1712267, by rfl⟩ : syracuseStep 2283023 = 3424535) B3424535
theorem B2405903 : Blo 1603000 2405903 := bstep (se 1 (by rfl) ⟨1804427, by rfl⟩ : syracuseStep 2405903 = 3608855) B3608855
theorem B9754141 : Blo 1603000 9754141 := bstep (se 3 (by rfl) ⟨1828901, by rfl⟩ : syracuseStep 9754141 = 3657803) B3657803
theorem B3126817 : Blo 1603000 3126817 := bstep (se 2 (by rfl) ⟨1172556, by rfl⟩ : syracuseStep 3126817 = 2345113) B2345113
theorem B2405945 : Blo 1603000 2405945 := bstep (se 2 (by rfl) ⟨902229, by rfl⟩ : syracuseStep 2405945 = 1804459) B1804459
theorem B1603131 : Blo 1603000 1603131 := bstep (se 1 (by rfl) ⟨1202348, by rfl⟩ : syracuseStep 1603131 = 2404697) B2404697
theorem B35657293 : Blo 1603000 35657293 := bstep (se 3 (by rfl) ⟨6685742, by rfl⟩ : syracuseStep 35657293 = 13371485) B13371485
theorem B1603207 : Blo 1603000 1603207 := bstep (se 1 (by rfl) ⟨1202405, by rfl⟩ : syracuseStep 1603207 = 2404811) B2404811
theorem B2406023 : Blo 1603000 2406023 := bstep (se 1 (by rfl) ⟨1804517, by rfl⟩ : syracuseStep 2406023 = 3609035) B3609035
theorem B1603215 : Blo 1603000 1603215 := bstep (se 1 (by rfl) ⟨1202411, by rfl⟩ : syracuseStep 1603215 = 2404823) B2404823
theorem B3610259 : Blo 1603000 3610259 := bstep (se 1 (by rfl) ⟨2707694, by rfl⟩ : syracuseStep 3610259 = 5415389) B5415389
theorem B2406059 : Blo 1603000 2406059 := bstep (se 1 (by rfl) ⟨1804544, by rfl⟩ : syracuseStep 2406059 = 3609089) B3609089
theorem B1603259 : Blo 1603000 1603259 := bstep (se 1 (by rfl) ⟨1202444, by rfl⟩ : syracuseStep 1603259 = 2404889) B2404889
theorem B15423169 : Blo 1603000 15423169 := bstep (se 2 (by rfl) ⟨5783688, by rfl⟩ : syracuseStep 15423169 = 11567377) B11567377
theorem B2406089 : Blo 1603000 2406089 := bstep (se 2 (by rfl) ⟨902283, by rfl⟩ : syracuseStep 2406089 = 1804567) B1804567
theorem B3610313 : Blo 1603000 3610313 := bstep (se 2 (by rfl) ⟨1353867, by rfl⟩ : syracuseStep 3610313 = 2707735) B2707735
theorem B2029303 : Blo 1603000 2029303 := bstep (se 1 (by rfl) ⟨1521977, by rfl⟩ : syracuseStep 2029303 = 3043955) B3043955
theorem B6256385 : Blo 1603000 6256385 := bstep (se 2 (by rfl) ⟨2346144, by rfl⟩ : syracuseStep 6256385 = 4692289) B4692289
theorem B1603335 : Blo 1603000 1603335 := bstep (se 1 (by rfl) ⟨1202501, by rfl⟩ : syracuseStep 1603335 = 2405003) B2405003
theorem B1603343 : Blo 1603000 1603343 := bstep (se 1 (by rfl) ⟨1202507, by rfl⟩ : syracuseStep 1603343 = 2405015) B2405015
theorem B3249953 : Blo 1603000 3249953 := bstep (se 2 (by rfl) ⟨1218732, by rfl⟩ : syracuseStep 3249953 = 2437465) B2437465
theorem B16455473 : Blo 1603000 16455473 := bstep (se 2 (by rfl) ⟨6170802, by rfl⟩ : syracuseStep 16455473 = 12341605) B12341605
theorem B1603387 : Blo 1603000 1603387 := bstep (se 1 (by rfl) ⟨1202540, by rfl⟩ : syracuseStep 1603387 = 2405081) B2405081
theorem B2406203 : Blo 1603000 2406203 := bstep (se 1 (by rfl) ⟨1804652, by rfl⟩ : syracuseStep 2406203 = 3609305) B3609305
theorem B6092603 : Blo 1603000 6092603 := bstep (se 1 (by rfl) ⟨4569452, by rfl⟩ : syracuseStep 6092603 = 9138905) B9138905
theorem B13711193 : Blo 1603000 13711193 := bstep (se 2 (by rfl) ⟨5141697, by rfl⟩ : syracuseStep 13711193 = 10283395) B10283395
theorem B2406263 : Blo 1603000 2406263 := bstep (se 1 (by rfl) ⟨1804697, by rfl⟩ : syracuseStep 2406263 = 3609395) B3609395
theorem B1603463 : Blo 1603000 1603463 := bstep (se 1 (by rfl) ⟨1202597, by rfl⟩ : syracuseStep 1603463 = 2405195) B2405195
theorem B5412743 : Blo 1603000 5412743 := bstep (se 1 (by rfl) ⟨4059557, by rfl⟩ : syracuseStep 5412743 = 8119115) B8119115
theorem B2439047 : Blo 1603000 2439047 := bstep (se 1 (by rfl) ⟨1829285, by rfl⟩ : syracuseStep 2439047 = 3658571) B3658571
theorem B1603471 : Blo 1603000 1603471 := bstep (se 1 (by rfl) ⟨1202603, by rfl⟩ : syracuseStep 1603471 = 2405207) B2405207
theorem B2406287 : Blo 1603000 2406287 := bstep (se 1 (by rfl) ⟨1804715, by rfl⟩ : syracuseStep 2406287 = 3609431) B3609431
theorem B10278809 : Blo 1603000 10278809 := bstep (se 2 (by rfl) ⟨3854553, by rfl⟩ : syracuseStep 10278809 = 7709107) B7709107
theorem B2406329 : Blo 1603000 2406329 := bstep (se 2 (by rfl) ⟨902373, by rfl⟩ : syracuseStep 2406329 = 1804747) B1804747
theorem B1603515 : Blo 1603000 1603515 := bstep (se 1 (by rfl) ⟨1202636, by rfl⟩ : syracuseStep 1603515 = 2405273) B2405273
theorem B1603591 : Blo 1603000 1603591 := bstep (se 1 (by rfl) ⟨1202693, by rfl⟩ : syracuseStep 1603591 = 2405387) B2405387
theorem B2406407 : Blo 1603000 2406407 := bstep (se 1 (by rfl) ⟨1804805, by rfl⟩ : syracuseStep 2406407 = 3609611) B3609611
theorem B1603599 : Blo 1603000 1603599 := bstep (se 1 (by rfl) ⟨1202699, by rfl⟩ : syracuseStep 1603599 = 2405399) B2405399
theorem B2406443 : Blo 1603000 2406443 := bstep (se 1 (by rfl) ⟨1804832, by rfl⟩ : syracuseStep 2406443 = 3609665) B3609665
theorem B1603643 : Blo 1603000 1603643 := bstep (se 1 (by rfl) ⟨1202732, by rfl⟩ : syracuseStep 1603643 = 2405465) B2405465
theorem B2029627 : Blo 1603000 2029627 := bstep (se 1 (by rfl) ⟨1522220, by rfl⟩ : syracuseStep 2029627 = 3044441) B3044441
theorem B2406473 : Blo 1603000 2406473 := bstep (se 2 (by rfl) ⟨902427, by rfl⟩ : syracuseStep 2406473 = 1804855) B1804855
theorem B4061299 : Blo 1603000 4061299 := bstep (se 1 (by rfl) ⟨3045974, by rfl⟩ : syracuseStep 4061299 = 6091949) B6091949
theorem B1603719 : Blo 1603000 1603719 := bstep (se 1 (by rfl) ⟨1202789, by rfl⟩ : syracuseStep 1603719 = 2405579) B2405579
theorem B2570375 : Blo 1603000 2570375 := bstep (se 1 (by rfl) ⟨1927781, by rfl⟩ : syracuseStep 2570375 = 3855563) B3855563
theorem B1603727 : Blo 1603000 1603727 := bstep (se 1 (by rfl) ⟨1202795, by rfl⟩ : syracuseStep 1603727 = 2405591) B2405591
theorem B2889913 : Blo 1603000 2889913 := bstep (se 2 (by rfl) ⟨1083717, by rfl⟩ : syracuseStep 2889913 = 2167435) B2167435
theorem B1603771 : Blo 1603000 1603771 := bstep (se 1 (by rfl) ⟨1202828, by rfl⟩ : syracuseStep 1603771 = 2405657) B2405657
theorem B2406587 : Blo 1603000 2406587 := bstep (se 1 (by rfl) ⟨1804940, by rfl⟩ : syracuseStep 2406587 = 3609881) B3609881
theorem B2406647 : Blo 1603000 2406647 := bstep (se 1 (by rfl) ⟨1804985, by rfl⟩ : syracuseStep 2406647 = 3609971) B3609971
theorem B5413121 : Blo 1603000 5413121 := bstep (se 2 (by rfl) ⟨2029920, by rfl⟩ : syracuseStep 5413121 = 4059841) B4059841
theorem B4061441 : Blo 1603000 4061441 := bstep (se 2 (by rfl) ⟨1523040, by rfl⟩ : syracuseStep 4061441 = 3046081) B3046081
theorem B1603847 : Blo 1603000 1603847 := bstep (se 1 (by rfl) ⟨1202885, by rfl⟩ : syracuseStep 1603847 = 2405771) B2405771
theorem B1603855 : Blo 1603000 1603855 := bstep (se 1 (by rfl) ⟨1202891, by rfl⟩ : syracuseStep 1603855 = 2405783) B2405783
theorem B2406671 : Blo 1603000 2406671 := bstep (se 1 (by rfl) ⟨1805003, by rfl⟩ : syracuseStep 2406671 = 3610007) B3610007
theorem B6093089 : Blo 1603000 6093089 := bstep (se 2 (by rfl) ⟨2284908, by rfl⟩ : syracuseStep 6093089 = 4569817) B4569817
theorem B2406713 : Blo 1603000 2406713 := bstep (se 2 (by rfl) ⟨902517, by rfl⟩ : syracuseStep 2406713 = 1805035) B1805035
theorem B1603899 : Blo 1603000 1603899 := bstep (se 1 (by rfl) ⟨1202924, by rfl⟩ : syracuseStep 1603899 = 2405849) B2405849
theorem B4569463 : Blo 1603000 4569463 := bstep (se 1 (by rfl) ⟨3427097, by rfl⟩ : syracuseStep 4569463 = 6854195) B6854195
theorem B1603975 : Blo 1603000 1603975 := bstep (se 1 (by rfl) ⟨1202981, by rfl⟩ : syracuseStep 1603975 = 2405963) B2405963
theorem B2406791 : Blo 1603000 2406791 := bstep (se 1 (by rfl) ⟨1805093, by rfl⟩ : syracuseStep 2406791 = 3610187) B3610187
theorem B7420295 : Blo 1603000 7420295 := bstep (se 1 (by rfl) ⟨5565221, by rfl⟩ : syracuseStep 7420295 = 11130443) B11130443
theorem B3611015 : Blo 1603000 3611015 := bstep (se 1 (by rfl) ⟨2708261, by rfl⟩ : syracuseStep 3611015 = 5416523) B5416523
theorem B1603983 : Blo 1603000 1603983 := bstep (se 1 (by rfl) ⟨1202987, by rfl⟩ : syracuseStep 1603983 = 2405975) B2405975
theorem B2406827 : Blo 1603000 2406827 := bstep (se 1 (by rfl) ⟨1805120, by rfl⟩ : syracuseStep 2406827 = 3610241) B3610241
theorem B1604027 : Blo 1603000 1604027 := bstep (se 1 (by rfl) ⟨1203020, by rfl⟩ : syracuseStep 1604027 = 2406041) B2406041
theorem B2406857 : Blo 1603000 2406857 := bstep (se 2 (by rfl) ⟨902571, by rfl⟩ : syracuseStep 2406857 = 1805143) B1805143
theorem B9132547 : Blo 1603000 9132547 := bstep (se 1 (by rfl) ⟨6849410, by rfl⟩ : syracuseStep 9132547 = 13698821) B13698821
theorem B1604103 : Blo 1603000 1604103 := bstep (se 1 (by rfl) ⟨1203077, by rfl⟩ : syracuseStep 1604103 = 2406155) B2406155
theorem B1604111 : Blo 1603000 1604111 := bstep (se 1 (by rfl) ⟨1203083, by rfl⟩ : syracuseStep 1604111 = 2406167) B2406167
theorem B2030123 : Blo 1603000 2030123 := bstep (se 1 (by rfl) ⟨1522592, by rfl⟩ : syracuseStep 2030123 = 3045185) B3045185
theorem B1604155 : Blo 1603000 1604155 := bstep (se 1 (by rfl) ⟨1203116, by rfl⟩ : syracuseStep 1604155 = 2406233) B2406233
theorem B2406971 : Blo 1603000 2406971 := bstep (se 1 (by rfl) ⟨1805228, by rfl⟩ : syracuseStep 2406971 = 3610457) B3610457
theorem B3611195 : Blo 1603000 3611195 := bstep (se 1 (by rfl) ⟨2708396, by rfl⟩ : syracuseStep 3611195 = 5416793) B5416793
theorem B2407031 : Blo 1603000 2407031 := bstep (se 1 (by rfl) ⟨1805273, by rfl⟩ : syracuseStep 2407031 = 3610547) B3610547
theorem B1604231 : Blo 1603000 1604231 := bstep (se 1 (by rfl) ⟨1203173, by rfl⟩ : syracuseStep 1604231 = 2406347) B2406347
theorem B2570887 : Blo 1603000 2570887 := bstep (se 1 (by rfl) ⟨1928165, by rfl⟩ : syracuseStep 2570887 = 3856331) B3856331
theorem B1604239 : Blo 1603000 1604239 := bstep (se 1 (by rfl) ⟨1203179, by rfl⟩ : syracuseStep 1604239 = 2406359) B2406359
theorem B2407055 : Blo 1603000 2407055 := bstep (se 1 (by rfl) ⟨1805291, by rfl⟩ : syracuseStep 2407055 = 3610583) B3610583
theorem B2407097 : Blo 1603000 2407097 := bstep (se 2 (by rfl) ⟨902661, by rfl⟩ : syracuseStep 2407097 = 1805323) B1805323
theorem B1604283 : Blo 1603000 1604283 := bstep (se 1 (by rfl) ⟨1203212, by rfl⟩ : syracuseStep 1604283 = 2406425) B2406425
theorem B4061897 : Blo 1603000 4061897 := bstep (se 2 (by rfl) ⟨1523211, by rfl⟩ : syracuseStep 4061897 = 3046423) B3046423
theorem B6855425 : Blo 1603000 6855425 := bstep (se 2 (by rfl) ⟨2570784, by rfl⟩ : syracuseStep 6855425 = 5141569) B5141569
theorem B1604359 : Blo 1603000 1604359 := bstep (se 1 (by rfl) ⟨1203269, by rfl⟩ : syracuseStep 1604359 = 2406539) B2406539
theorem B2407175 : Blo 1603000 2407175 := bstep (se 1 (by rfl) ⟨1805381, by rfl⟩ : syracuseStep 2407175 = 3610763) B3610763
theorem B1604367 : Blo 1603000 1604367 := bstep (se 1 (by rfl) ⟨1203275, by rfl⟩ : syracuseStep 1604367 = 2406551) B2406551
theorem B3046187 : Blo 1603000 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B2407211 : Blo 1603000 2407211 := bstep (se 1 (by rfl) ⟨1805408, by rfl⟩ : syracuseStep 2407211 = 3610817) B3610817
theorem B1604411 : Blo 1603000 1604411 := bstep (se 1 (by rfl) ⟨1203308, by rfl⟩ : syracuseStep 1604411 = 2406617) B2406617
theorem B2407241 : Blo 1603000 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B1604487 : Blo 1603000 1604487 := bstep (se 1 (by rfl) ⟨1203365, by rfl⟩ : syracuseStep 1604487 = 2406731) B2406731
theorem B1604495 : Blo 1603000 1604495 := bstep (se 1 (by rfl) ⟨1203371, by rfl⟩ : syracuseStep 1604495 = 2406743) B2406743
theorem B1604539 : Blo 1603000 1604539 := bstep (se 1 (by rfl) ⟨1203404, by rfl⟩ : syracuseStep 1604539 = 2406809) B2406809
theorem B2407355 : Blo 1603000 2407355 := bstep (se 1 (by rfl) ⟨1805516, by rfl⟩ : syracuseStep 2407355 = 3611033) B3611033
theorem B2407415 : Blo 1603000 2407415 := bstep (se 1 (by rfl) ⟨1805561, by rfl⟩ : syracuseStep 2407415 = 3611123) B3611123
theorem B2030599 : Blo 1603000 2030599 := bstep (se 1 (by rfl) ⟨1522949, by rfl⟩ : syracuseStep 2030599 = 3045899) B3045899
theorem B1604615 : Blo 1603000 1604615 := bstep (se 1 (by rfl) ⟨1203461, by rfl⟩ : syracuseStep 1604615 = 2406923) B2406923
theorem B1604623 : Blo 1603000 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B3521551 : Blo 1603000 3521551 := bstep (se 1 (by rfl) ⟨2641163, by rfl⟩ : syracuseStep 3521551 = 5282327) B5282327
theorem B5413931 : Blo 1603000 5413931 := bstep (se 1 (by rfl) ⟨4060448, by rfl⟩ : syracuseStep 5413931 = 8120897) B8120897
theorem B4062251 : Blo 1603000 4062251 := bstep (se 1 (by rfl) ⟨3046688, by rfl⟩ : syracuseStep 4062251 = 6093377) B6093377
theorem B2407481 : Blo 1603000 2407481 := bstep (se 2 (by rfl) ⟨902805, by rfl⟩ : syracuseStep 2407481 = 1805611) B1805611
theorem B1604667 : Blo 1603000 1604667 := bstep (se 1 (by rfl) ⟨1203500, by rfl⟩ : syracuseStep 1604667 = 2407001) B2407001
theorem B13696087 : Blo 1603000 13696087 := bstep (se 1 (by rfl) ⟨10272065, by rfl⟩ : syracuseStep 13696087 = 20544131) B20544131
theorem B1604743 : Blo 1603000 1604743 := bstep (se 1 (by rfl) ⟨1203557, by rfl⟩ : syracuseStep 1604743 = 2407115) B2407115
theorem B1604751 : Blo 1603000 1604751 := bstep (se 1 (by rfl) ⟨1203563, by rfl⟩ : syracuseStep 1604751 = 2407127) B2407127
theorem B2890937 : Blo 1603000 2890937 := bstep (se 2 (by rfl) ⟨1084101, by rfl⟩ : syracuseStep 2890937 = 2168203) B2168203
theorem B1604795 : Blo 1603000 1604795 := bstep (se 1 (by rfl) ⟨1203596, by rfl⟩ : syracuseStep 1604795 = 2407193) B2407193
theorem B1604871 : Blo 1603000 1604871 := bstep (se 1 (by rfl) ⟨1203653, by rfl⟩ : syracuseStep 1604871 = 2407307) B2407307
theorem B1604879 : Blo 1603000 1604879 := bstep (se 1 (by rfl) ⟨1203659, by rfl⟩ : syracuseStep 1604879 = 2407319) B2407319
theorem B1604923 : Blo 1603000 1604923 := bstep (se 1 (by rfl) ⟨1203692, by rfl⟩ : syracuseStep 1604923 = 2407385) B2407385
theorem B3251591 : Blo 1603000 3251591 := bstep (se 1 (by rfl) ⟨2438693, by rfl⟩ : syracuseStep 3251591 = 4877387) B4877387
theorem B1604999 : Blo 1603000 1604999 := bstep (se 1 (by rfl) ⟨1203749, by rfl⟩ : syracuseStep 1604999 = 2407499) B2407499
theorem B14638481 : Blo 1603000 14638481 := bstep (se 2 (by rfl) ⟨5489430, by rfl⟩ : syracuseStep 14638481 = 10978861) B10978861
theorem B8117657 : Blo 1603000 8117657 := bstep (se 2 (by rfl) ⟨3044121, by rfl⟩ : syracuseStep 8117657 = 6088243) B6088243
theorem B2031095 : Blo 1603000 2031095 := bstep (se 1 (by rfl) ⟨1523321, by rfl⟩ : syracuseStep 2031095 = 3046643) B3046643
theorem B29253221 : Blo 1603000 29253221 := bstep (se 4 (by rfl) ⟨2742489, by rfl⟩ : syracuseStep 29253221 = 5484979) B5484979
theorem B7708279 : Blo 1603000 7708279 := bstep (se 1 (by rfl) ⟨5781209, by rfl⟩ : syracuseStep 7708279 = 11562419) B11562419
theorem B2031247 : Blo 1603000 2031247 := bstep (se 1 (by rfl) ⟨1523435, by rfl⟩ : syracuseStep 2031247 = 3046871) B3046871
theorem B10280677 : Blo 1603000 10280677 := bstep (se 4 (by rfl) ⟨963813, by rfl⟩ : syracuseStep 10280677 = 1927627) B1927627
theorem B4333313 : Blo 1603000 4333313 := bstep (se 2 (by rfl) ⟨1624992, by rfl⟩ : syracuseStep 4333313 = 3249985) B3249985
theorem B34676525 : Blo 1603000 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B8675275 : Blo 1603000 8675275 := bstep (se 1 (by rfl) ⟨6506456, by rfl⟩ : syracuseStep 8675275 = 13012913) B13012913
theorem B12173327 : Blo 1603000 12173327 := bstep (se 1 (by rfl) ⟨9129995, by rfl⟩ : syracuseStep 12173327 = 18259991) B18259991
theorem B6086771 : Blo 1603000 6086771 := bstep (se 1 (by rfl) ⟨4565078, by rfl⟩ : syracuseStep 6086771 = 9130157) B9130157
theorem B5415065 : Blo 1603000 5415065 := bstep (se 2 (by rfl) ⟨2030649, by rfl⟩ : syracuseStep 5415065 = 4061299) B4061299
theorem B9757057 : Blo 1603000 9757057 := bstep (se 2 (by rfl) ⟨3658896, by rfl⟩ : syracuseStep 9757057 = 7317793) B7317793
theorem B3424655 : Blo 1603000 3424655 := bstep (se 1 (by rfl) ⟨2568491, by rfl⟩ : syracuseStep 3424655 = 5136983) B5136983
theorem B2744719 : Blo 1603000 2744719 := bstep (se 1 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 2744719 = 4117079) B4117079
theorem B7709165 : Blo 1603000 7709165 := bstep (se 3 (by rfl) ⟨1445468, by rfl⟩ : syracuseStep 7709165 = 2890937) B2890937
theorem B12182075 : Blo 1603000 12182075 := bstep (se 1 (by rfl) ⟨9136556, by rfl⟩ : syracuseStep 12182075 = 18273113) B18273113
theorem B3760763 : Blo 1603000 3760763 := bstep (se 1 (by rfl) ⟨2820572, by rfl⟩ : syracuseStep 3760763 = 5641145) B5641145
theorem B7135879 : Blo 1603000 7135879 := bstep (se 1 (by rfl) ⟨5351909, by rfl⟩ : syracuseStep 7135879 = 10703819) B10703819
theorem B3424979 : Blo 1603000 3424979 := bstep (se 1 (by rfl) ⟨2568734, by rfl⟩ : syracuseStep 3424979 = 5137469) B5137469
theorem B3425287 : Blo 1603000 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B23119019 : Blo 1603000 23119019 := bstep (se 1 (by rfl) ⟨17339264, by rfl⟩ : syracuseStep 23119019 = 34678529) B34678529
theorem B4170923 : Blo 1603000 4170923 := bstep (se 1 (by rfl) ⟨3128192, by rfl⟩ : syracuseStep 4170923 = 6256385) B6256385
theorem B10970315 : Blo 1603000 10970315 := bstep (se 1 (by rfl) ⟨8227736, by rfl⟩ : syracuseStep 10970315 = 16455473) B16455473
theorem B35153137 : Blo 1603000 35153137 := bstep (se 2 (by rfl) ⟨13182426, by rfl⟩ : syracuseStep 35153137 = 26364853) B26364853
theorem B5416253 : Blo 1603000 5416253 := bstep (se 3 (by rfl) ⟨1015547, by rfl⟩ : syracuseStep 5416253 = 2031095) B2031095
theorem B4695401 : Blo 1603000 4695401 := bstep (se 2 (by rfl) ⟨1760775, by rfl⟩ : syracuseStep 4695401 = 3521551) B3521551
theorem B6088061 : Blo 1603000 6088061 := bstep (se 3 (by rfl) ⟨1141511, by rfl⟩ : syracuseStep 6088061 = 2283023) B2283023
theorem B1713583 : Blo 1603000 1713583 := bstep (se 1 (by rfl) ⟨1285187, by rfl⟩ : syracuseStep 1713583 = 2570375) B2570375
theorem B18261449 : Blo 1603000 18261449 := bstep (se 2 (by rfl) ⟨6848043, by rfl⟩ : syracuseStep 18261449 = 13696087) B13696087
theorem B1803739 : Blo 1603000 1803739 := bstep (se 1 (by rfl) ⟨1352804, by rfl⟩ : syracuseStep 1803739 = 2705609) B2705609
theorem B2705143 : Blo 1603000 2705143 := bstep (se 1 (by rfl) ⟨2028857, by rfl⟩ : syracuseStep 2705143 = 4057715) B4057715
theorem B19498745 : Blo 1603000 19498745 := bstep (se 2 (by rfl) ⟨7312029, by rfl⟩ : syracuseStep 19498745 = 14624059) B14624059
theorem B26003243 : Blo 1603000 26003243 := bstep (se 1 (by rfl) ⟨19502432, by rfl⟩ : syracuseStep 26003243 = 39004865) B39004865
theorem B1804207 : Blo 1603000 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B2705339 : Blo 1603000 2705339 := bstep (se 1 (by rfl) ⟨2029004, by rfl⟩ : syracuseStep 2705339 = 4058009) B4058009
theorem B2705447 : Blo 1603000 2705447 := bstep (se 1 (by rfl) ⟨2029085, by rfl⟩ : syracuseStep 2705447 = 4058171) B4058171
theorem B5138585 : Blo 1603000 5138585 := bstep (se 2 (by rfl) ⟨1926969, by rfl⟩ : syracuseStep 5138585 = 3853939) B3853939
theorem B3426475 : Blo 1603000 3426475 := bstep (se 1 (by rfl) ⟨2569856, by rfl⟩ : syracuseStep 3426475 = 5139713) B5139713
theorem B3426551 : Blo 1603000 3426551 := bstep (se 1 (by rfl) ⟨2569913, by rfl⟩ : syracuseStep 3426551 = 5139827) B5139827
theorem B20564225 : Blo 1603000 20564225 := bstep (se 2 (by rfl) ⟨7711584, by rfl⟩ : syracuseStep 20564225 = 15423169) B15423169
theorem B9758987 : Blo 1603000 9758987 := bstep (se 1 (by rfl) ⟨7319240, by rfl⟩ : syracuseStep 9758987 = 14638481) B14638481
theorem B13707569 : Blo 1603000 13707569 := bstep (se 2 (by rfl) ⟨5140338, by rfl⟩ : syracuseStep 13707569 = 10280677) B10280677
theorem B2705737 : Blo 1603000 2705737 := bstep (se 2 (by rfl) ⟨1014651, by rfl⟩ : syracuseStep 2705737 = 2029303) B2029303
theorem B1804639 : Blo 1603000 1804639 := bstep (se 1 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 1804639 = 2706959) B2706959
theorem B2705771 : Blo 1603000 2705771 := bstep (se 1 (by rfl) ⟨2029328, by rfl⟩ : syracuseStep 2705771 = 4058657) B4058657
theorem B18278945 : Blo 1603000 18278945 := bstep (se 2 (by rfl) ⟨6854604, by rfl⟩ : syracuseStep 18278945 = 13709209) B13709209
theorem B3607163 : Blo 1603000 3607163 := bstep (se 1 (by rfl) ⟨2705372, by rfl⟩ : syracuseStep 3607163 = 5410745) B5410745
theorem B6507155 : Blo 1603000 6507155 := bstep (se 1 (by rfl) ⟨4880366, by rfl⟩ : syracuseStep 6507155 = 9760733) B9760733
theorem B1804999 : Blo 1603000 1804999 := bstep (se 1 (by rfl) ⟨1353749, by rfl⟩ : syracuseStep 1804999 = 2707499) B2707499
theorem B3607289 : Blo 1603000 3607289 := bstep (se 2 (by rfl) ⟨1352733, by rfl⟩ : syracuseStep 3607289 = 2705467) B2705467
theorem B2706169 : Blo 1603000 2706169 := bstep (se 2 (by rfl) ⟨1014813, by rfl⟩ : syracuseStep 2706169 = 2029627) B2029627
theorem B3853217 : Blo 1603000 3853217 := bstep (se 2 (by rfl) ⟨1444956, by rfl⟩ : syracuseStep 3853217 = 2889913) B2889913
theorem B4058039 : Blo 1603000 4058039 := bstep (se 1 (by rfl) ⟨3043529, by rfl⟩ : syracuseStep 4058039 = 6087059) B6087059
theorem B3607559 : Blo 1603000 3607559 := bstep (se 1 (by rfl) ⟨2705669, by rfl⟩ : syracuseStep 3607559 = 5411339) B5411339
theorem B2706439 : Blo 1603000 2706439 := bstep (se 1 (by rfl) ⟨2029829, by rfl⟩ : syracuseStep 2706439 = 4059659) B4059659
theorem B3607631 : Blo 1603000 3607631 := bstep (se 1 (by rfl) ⟨2705723, by rfl⟩ : syracuseStep 3607631 = 5411447) B5411447
theorem B5139571 : Blo 1603000 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B6171805 : Blo 1603000 6171805 := bstep (se 3 (by rfl) ⟨1157213, by rfl⟩ : syracuseStep 6171805 = 2314427) B2314427
theorem B6089975 : Blo 1603000 6089975 := bstep (se 1 (by rfl) ⟨4567481, by rfl⟩ : syracuseStep 6089975 = 9134963) B9134963
theorem B12176729 : Blo 1603000 12176729 := bstep (se 2 (by rfl) ⟨4566273, by rfl⟩ : syracuseStep 12176729 = 9132547) B9132547
theorem B2706871 : Blo 1603000 2706871 := bstep (se 1 (by rfl) ⟨2030153, by rfl⟩ : syracuseStep 2706871 = 4060307) B4060307
theorem B3608027 : Blo 1603000 3608027 := bstep (se 1 (by rfl) ⟨2706020, by rfl⟩ : syracuseStep 3608027 = 5412041) B5412041
theorem B5410313 : Blo 1603000 5410313 := bstep (se 2 (by rfl) ⟨2028867, by rfl⟩ : syracuseStep 5410313 = 4057735) B4057735
theorem B3427849 : Blo 1603000 3427849 := bstep (se 2 (by rfl) ⟨1285443, by rfl⟩ : syracuseStep 3427849 = 2570887) B2570887
theorem B2707067 : Blo 1603000 2707067 := bstep (se 1 (by rfl) ⟨2030300, by rfl⟩ : syracuseStep 2707067 = 4060601) B4060601
theorem B19787453 : Blo 1603000 19787453 := bstep (se 3 (by rfl) ⟨3710147, by rfl⟩ : syracuseStep 19787453 = 7420295) B7420295
theorem B9137879 : Blo 1603000 9137879 := bstep (se 1 (by rfl) ⟨6853409, by rfl⟩ : syracuseStep 9137879 = 13706819) B13706819
theorem B2166635 : Blo 1603000 2166635 := bstep (se 1 (by rfl) ⟨1624976, by rfl⟩ : syracuseStep 2166635 = 3249953) B3249953
theorem B3608495 : Blo 1603000 3608495 := bstep (se 1 (by rfl) ⟨2706371, by rfl⟩ : syracuseStep 3608495 = 5412743) B5412743
theorem B1626031 : Blo 1603000 1626031 := bstep (se 1 (by rfl) ⟨1219523, by rfl⟩ : syracuseStep 1626031 = 2439047) B2439047
theorem B2568119 : Blo 1603000 2568119 := bstep (se 1 (by rfl) ⟨1926089, by rfl⟩ : syracuseStep 2568119 = 3852179) B3852179
theorem B4173751 : Blo 1603000 4173751 := bstep (se 1 (by rfl) ⟨3130313, by rfl⟩ : syracuseStep 4173751 = 6260627) B6260627
theorem B16461755 : Blo 1603000 16461755 := bstep (se 1 (by rfl) ⟨12346316, by rfl⟩ : syracuseStep 16461755 = 24692633) B24692633
theorem B6852539 : Blo 1603000 6852539 := bstep (se 1 (by rfl) ⟨5139404, by rfl⟩ : syracuseStep 6852539 = 10278809) B10278809
theorem B4059143 : Blo 1603000 4059143 := bstep (se 1 (by rfl) ⟨3044357, by rfl⟩ : syracuseStep 4059143 = 6088715) B6088715
theorem B2707465 : Blo 1603000 2707465 := bstep (se 2 (by rfl) ⟨1015299, by rfl⟩ : syracuseStep 2707465 = 2030599) B2030599
theorem B4059193 : Blo 1603000 4059193 := bstep (se 2 (by rfl) ⟨1522197, by rfl⟩ : syracuseStep 4059193 = 3044395) B3044395
theorem B3608747 : Blo 1603000 3608747 := bstep (se 1 (by rfl) ⟨2706560, by rfl⟩ : syracuseStep 3608747 = 5413121) B5413121
theorem B2707627 : Blo 1603000 2707627 := bstep (se 1 (by rfl) ⟨2030720, by rfl⟩ : syracuseStep 2707627 = 4061441) B4061441
theorem B6090947 : Blo 1603000 6090947 := bstep (se 1 (by rfl) ⟨4568210, by rfl⟩ : syracuseStep 6090947 = 9136421) B9136421
theorem B2404601 : Blo 1603000 2404601 := bstep (se 2 (by rfl) ⟨901725, by rfl⟩ : syracuseStep 2404601 = 1803451) B1803451
theorem B2404703 : Blo 1603000 2404703 := bstep (se 1 (by rfl) ⟨1803527, by rfl⟩ : syracuseStep 2404703 = 3607055) B3607055
theorem B5411177 : Blo 1603000 5411177 := bstep (se 2 (by rfl) ⟨2029191, by rfl⟩ : syracuseStep 5411177 = 4058383) B4058383
theorem B4059497 : Blo 1603000 4059497 := bstep (se 2 (by rfl) ⟨1522311, by rfl⟩ : syracuseStep 4059497 = 3044623) B3044623
theorem B2404715 : Blo 1603000 2404715 := bstep (se 1 (by rfl) ⟨1803536, by rfl⟩ : syracuseStep 2404715 = 3607073) B3607073
theorem B3043727 : Blo 1603000 3043727 := bstep (se 1 (by rfl) ⟨2282795, by rfl⟩ : syracuseStep 3043727 = 4565591) B4565591
theorem B2707931 : Blo 1603000 2707931 := bstep (se 1 (by rfl) ⟨2030948, by rfl⟩ : syracuseStep 2707931 = 4061897) B4061897
theorem B2404943 : Blo 1603000 2404943 := bstep (se 1 (by rfl) ⟨1803707, by rfl⟩ : syracuseStep 2404943 = 3607415) B3607415
theorem B2405063 : Blo 1603000 2405063 := bstep (se 1 (by rfl) ⟨1803797, by rfl⟩ : syracuseStep 2405063 = 3607595) B3607595
theorem B3609287 : Blo 1603000 3609287 := bstep (se 1 (by rfl) ⟨2706965, by rfl⟩ : syracuseStep 3609287 = 5413931) B5413931
theorem B6091463 : Blo 1603000 6091463 := bstep (se 1 (by rfl) ⟨4568597, by rfl⟩ : syracuseStep 6091463 = 9137195) B9137195
theorem B2708167 : Blo 1603000 2708167 := bstep (se 1 (by rfl) ⟨2031125, by rfl⟩ : syracuseStep 2708167 = 4062251) B4062251
theorem B13005521 : Blo 1603000 13005521 := bstep (se 2 (by rfl) ⟨4877070, by rfl⟩ : syracuseStep 13005521 = 9754141) B9754141
theorem B47543057 : Blo 1603000 47543057 := bstep (se 2 (by rfl) ⟨17828646, by rfl⟩ : syracuseStep 47543057 = 35657293) B35657293
theorem B8123165 : Blo 1603000 8123165 := bstep (se 3 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 8123165 = 3046187) B3046187
theorem B10277705 : Blo 1603000 10277705 := bstep (se 2 (by rfl) ⟨3854139, by rfl⟩ : syracuseStep 10277705 = 7708279) B7708279
theorem B2405225 : Blo 1603000 2405225 := bstep (se 2 (by rfl) ⟨901959, by rfl⟩ : syracuseStep 2405225 = 1803919) B1803919
theorem B2708329 : Blo 1603000 2708329 := bstep (se 2 (by rfl) ⟨1015623, by rfl⟩ : syracuseStep 2708329 = 2031247) B2031247
theorem B2167727 : Blo 1603000 2167727 := bstep (se 1 (by rfl) ⟨1625795, by rfl⟩ : syracuseStep 2167727 = 3251591) B3251591
theorem B2405303 : Blo 1603000 2405303 := bstep (se 1 (by rfl) ⟨1803977, by rfl⟩ : syracuseStep 2405303 = 3607955) B3607955
theorem B5411771 : Blo 1603000 5411771 := bstep (se 1 (by rfl) ⟨4058828, by rfl⟩ : syracuseStep 5411771 = 8117657) B8117657
theorem B2405339 : Blo 1603000 2405339 := bstep (se 1 (by rfl) ⟨1804004, by rfl⟩ : syracuseStep 2405339 = 3608009) B3608009
theorem B5141519 : Blo 1603000 5141519 := bstep (se 1 (by rfl) ⟨3856139, by rfl⟩ : syracuseStep 5141519 = 7712279) B7712279
theorem B20558893 : Blo 1603000 20558893 := bstep (se 3 (by rfl) ⟨3854792, by rfl⟩ : syracuseStep 20558893 = 7709585) B7709585
theorem B19502147 : Blo 1603000 19502147 := bstep (se 1 (by rfl) ⟨14626610, by rfl⟩ : syracuseStep 19502147 = 29253221) B29253221
theorem B2888875 : Blo 1603000 2888875 := bstep (se 1 (by rfl) ⟨2166656, by rfl⟩ : syracuseStep 2888875 = 4333313) B4333313
theorem B3044783 : Blo 1603000 3044783 := bstep (se 1 (by rfl) ⟨2283587, by rfl⟩ : syracuseStep 3044783 = 4567175) B4567175
theorem B2405807 : Blo 1603000 2405807 := bstep (se 1 (by rfl) ⟨1804355, by rfl⟩ : syracuseStep 2405807 = 3608711) B3608711
theorem B1603015 : Blo 1603000 1603015 := bstep (se 1 (by rfl) ⟨1202261, by rfl⟩ : syracuseStep 1603015 = 2404523) B2404523
theorem B1603035 : Blo 1603000 1603035 := bstep (se 1 (by rfl) ⟨1202276, by rfl⟩ : syracuseStep 1603035 = 2404553) B2404553
theorem B8345051 : Blo 1603000 8345051 := bstep (se 1 (by rfl) ⟨6258788, by rfl⟩ : syracuseStep 8345051 = 12517577) B12517577
theorem B2405897 : Blo 1603000 2405897 := bstep (se 2 (by rfl) ⟨902211, by rfl⟩ : syracuseStep 2405897 = 1804423) B1804423
theorem B1603111 : Blo 1603000 1603111 := bstep (se 1 (by rfl) ⟨1202333, by rfl⟩ : syracuseStep 1603111 = 2404667) B2404667
theorem B2405927 : Blo 1603000 2405927 := bstep (se 1 (by rfl) ⟨1804445, by rfl⟩ : syracuseStep 2405927 = 3608891) B3608891
theorem B3610151 : Blo 1603000 3610151 := bstep (se 1 (by rfl) ⟨2707613, by rfl⟩ : syracuseStep 3610151 = 5415227) B5415227
theorem B1603151 : Blo 1603000 1603151 := bstep (se 1 (by rfl) ⟨1202363, by rfl⟩ : syracuseStep 1603151 = 2404727) B2404727
theorem B1603167 : Blo 1603000 1603167 := bstep (se 1 (by rfl) ⟨1202375, by rfl⟩ : syracuseStep 1603167 = 2404751) B2404751
theorem B1603195 : Blo 1603000 1603195 := bstep (se 1 (by rfl) ⟨1202396, by rfl⟩ : syracuseStep 1603195 = 2404793) B2404793
theorem B9754235 : Blo 1603000 9754235 := bstep (se 1 (by rfl) ⟨7315676, by rfl⟩ : syracuseStep 9754235 = 14631353) B14631353
theorem B2406011 : Blo 1603000 2406011 := bstep (se 1 (by rfl) ⟨1804508, by rfl⟩ : syracuseStep 2406011 = 3609017) B3609017
theorem B8230547 : Blo 1603000 8230547 := bstep (se 1 (by rfl) ⟨6172910, by rfl⟩ : syracuseStep 8230547 = 12345821) B12345821
theorem B6092435 : Blo 1603000 6092435 := bstep (se 1 (by rfl) ⟨4569326, by rfl⟩ : syracuseStep 6092435 = 9138653) B9138653
theorem B1603247 : Blo 1603000 1603247 := bstep (se 1 (by rfl) ⟨1202435, by rfl⟩ : syracuseStep 1603247 = 2404871) B2404871
theorem B1603271 : Blo 1603000 1603271 := bstep (se 1 (by rfl) ⟨1202453, by rfl⟩ : syracuseStep 1603271 = 2404907) B2404907
theorem B22861511 : Blo 1603000 22861511 := bstep (se 1 (by rfl) ⟨17146133, by rfl⟩ : syracuseStep 22861511 = 34292267) B34292267
theorem B12179159 : Blo 1603000 12179159 := bstep (se 1 (by rfl) ⟨9134369, by rfl⟩ : syracuseStep 12179159 = 18268739) B18268739
theorem B1603291 : Blo 1603000 1603291 := bstep (se 1 (by rfl) ⟨1202468, by rfl⟩ : syracuseStep 1603291 = 2404937) B2404937
theorem B2406137 : Blo 1603000 2406137 := bstep (se 2 (by rfl) ⟨902301, by rfl⟩ : syracuseStep 2406137 = 1804603) B1804603
theorem B4568825 : Blo 1603000 4568825 := bstep (se 2 (by rfl) ⟨1713309, by rfl⟩ : syracuseStep 4568825 = 3426619) B3426619
theorem B1603367 : Blo 1603000 1603367 := bstep (se 1 (by rfl) ⟨1202525, by rfl⟩ : syracuseStep 1603367 = 2405051) B2405051
theorem B18528059 : Blo 1603000 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B6092617 : Blo 1603000 6092617 := bstep (se 2 (by rfl) ⟨2284731, by rfl⟩ : syracuseStep 6092617 = 4569463) B4569463
theorem B1603407 : Blo 1603000 1603407 := bstep (se 1 (by rfl) ⟨1202555, by rfl⟩ : syracuseStep 1603407 = 2405111) B2405111
theorem B1603423 : Blo 1603000 1603423 := bstep (se 1 (by rfl) ⟨1202567, by rfl⟩ : syracuseStep 1603423 = 2405135) B2405135
theorem B3045215 : Blo 1603000 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B2406239 : Blo 1603000 2406239 := bstep (se 1 (by rfl) ⟨1804679, by rfl⟩ : syracuseStep 2406239 = 3609359) B3609359
theorem B2406251 : Blo 1603000 2406251 := bstep (se 1 (by rfl) ⟨1804688, by rfl⟩ : syracuseStep 2406251 = 3609377) B3609377
theorem B3610475 : Blo 1603000 3610475 := bstep (se 1 (by rfl) ⟨2707856, by rfl⟩ : syracuseStep 3610475 = 5415713) B5415713
theorem B1603451 : Blo 1603000 1603451 := bstep (se 1 (by rfl) ⟨1202588, by rfl⟩ : syracuseStep 1603451 = 2405177) B2405177
theorem B3610529 : Blo 1603000 3610529 := bstep (se 2 (by rfl) ⟨1353948, by rfl⟩ : syracuseStep 3610529 = 2707897) B2707897
theorem B1603503 : Blo 1603000 1603503 := bstep (se 1 (by rfl) ⟨1202627, by rfl⟩ : syracuseStep 1603503 = 2405255) B2405255
theorem B1603527 : Blo 1603000 1603527 := bstep (se 1 (by rfl) ⟨1202645, by rfl⟩ : syracuseStep 1603527 = 2405291) B2405291
theorem B1603547 : Blo 1603000 1603547 := bstep (se 1 (by rfl) ⟨1202660, by rfl⟩ : syracuseStep 1603547 = 2405321) B2405321
theorem B2029531 : Blo 1603000 2029531 := bstep (se 1 (by rfl) ⟨1522148, by rfl⟩ : syracuseStep 2029531 = 3044297) B3044297
theorem B2471899 : Blo 1603000 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B9132047 : Blo 1603000 9132047 := bstep (se 1 (by rfl) ⟨6849035, by rfl⟩ : syracuseStep 9132047 = 13698071) B13698071
theorem B1603623 : Blo 1603000 1603623 := bstep (se 1 (by rfl) ⟨1202717, by rfl⟩ : syracuseStep 1603623 = 2405435) B2405435
theorem B1603663 : Blo 1603000 1603663 := bstep (se 1 (by rfl) ⟨1202747, by rfl⟩ : syracuseStep 1603663 = 2405495) B2405495
theorem B2406479 : Blo 1603000 2406479 := bstep (se 1 (by rfl) ⟨1804859, by rfl⟩ : syracuseStep 2406479 = 3609719) B3609719
theorem B1603679 : Blo 1603000 1603679 := bstep (se 1 (by rfl) ⟨1202759, by rfl⟩ : syracuseStep 1603679 = 2405519) B2405519
theorem B1603707 : Blo 1603000 1603707 := bstep (se 1 (by rfl) ⟨1202780, by rfl⟩ : syracuseStep 1603707 = 2405561) B2405561
theorem B8673437 : Blo 1603000 8673437 := bstep (se 3 (by rfl) ⟨1626269, by rfl⟩ : syracuseStep 8673437 = 3252539) B3252539
theorem B2889899 : Blo 1603000 2889899 := bstep (se 1 (by rfl) ⟨2167424, by rfl⟩ : syracuseStep 2889899 = 4334849) B4334849
theorem B1603759 : Blo 1603000 1603759 := bstep (se 1 (by rfl) ⟨1202819, by rfl⟩ : syracuseStep 1603759 = 2405639) B2405639
theorem B1603783 : Blo 1603000 1603783 := bstep (se 1 (by rfl) ⟨1202837, by rfl⟩ : syracuseStep 1603783 = 2405675) B2405675
theorem B2406599 : Blo 1603000 2406599 := bstep (se 1 (by rfl) ⟨1804949, by rfl⟩ : syracuseStep 2406599 = 3609899) B3609899
theorem B1603803 : Blo 1603000 1603803 := bstep (se 1 (by rfl) ⟨1202852, by rfl⟩ : syracuseStep 1603803 = 2405705) B2405705
theorem B3610871 : Blo 1603000 3610871 := bstep (se 1 (by rfl) ⟨2708153, by rfl⟩ : syracuseStep 3610871 = 5416307) B5416307
theorem B1603879 : Blo 1603000 1603879 := bstep (se 1 (by rfl) ⟨1202909, by rfl⟩ : syracuseStep 1603879 = 2405819) B2405819
theorem B1603919 : Blo 1603000 1603919 := bstep (se 1 (by rfl) ⟨1202939, by rfl⟩ : syracuseStep 1603919 = 2405879) B2405879
theorem B20822359 : Blo 1603000 20822359 := bstep (se 1 (by rfl) ⟨15616769, by rfl⟩ : syracuseStep 20822359 = 31233539) B31233539
theorem B16464215 : Blo 1603000 16464215 := bstep (se 1 (by rfl) ⟨12348161, by rfl⟩ : syracuseStep 16464215 = 24696323) B24696323
theorem B1603935 : Blo 1603000 1603935 := bstep (se 1 (by rfl) ⟨1202951, by rfl⟩ : syracuseStep 1603935 = 2405903) B2405903
theorem B2406761 : Blo 1603000 2406761 := bstep (se 2 (by rfl) ⟨902535, by rfl⟩ : syracuseStep 2406761 = 1805071) B1805071
theorem B1603963 : Blo 1603000 1603963 := bstep (se 1 (by rfl) ⟨1202972, by rfl⟩ : syracuseStep 1603963 = 2405945) B2405945
theorem B1604015 : Blo 1603000 1604015 := bstep (se 1 (by rfl) ⟨1203011, by rfl⟩ : syracuseStep 1604015 = 2406023) B2406023
theorem B2406839 : Blo 1603000 2406839 := bstep (se 1 (by rfl) ⟨1805129, by rfl⟩ : syracuseStep 2406839 = 3610259) B3610259
theorem B1604039 : Blo 1603000 1604039 := bstep (se 1 (by rfl) ⟨1203029, by rfl⟩ : syracuseStep 1604039 = 2406059) B2406059
theorem B1604059 : Blo 1603000 1604059 := bstep (se 1 (by rfl) ⟨1203044, by rfl⟩ : syracuseStep 1604059 = 2406089) B2406089
theorem B2406875 : Blo 1603000 2406875 := bstep (se 1 (by rfl) ⟨1805156, by rfl⟩ : syracuseStep 2406875 = 3610313) B3610313
theorem B1604135 : Blo 1603000 1604135 := bstep (se 1 (by rfl) ⟨1203101, by rfl⟩ : syracuseStep 1604135 = 2406203) B2406203
theorem B4061735 : Blo 1603000 4061735 := bstep (se 1 (by rfl) ⟨3046301, by rfl⟩ : syracuseStep 4061735 = 6092603) B6092603
theorem B9140795 : Blo 1603000 9140795 := bstep (se 1 (by rfl) ⟨6855596, by rfl⟩ : syracuseStep 9140795 = 13711193) B13711193
theorem B1604175 : Blo 1603000 1604175 := bstep (se 1 (by rfl) ⟨1203131, by rfl⟩ : syracuseStep 1604175 = 2406263) B2406263
theorem B1604191 : Blo 1603000 1604191 := bstep (se 1 (by rfl) ⟨1203143, by rfl⟩ : syracuseStep 1604191 = 2406287) B2406287
theorem B5413499 : Blo 1603000 5413499 := bstep (se 1 (by rfl) ⟨4060124, by rfl⟩ : syracuseStep 5413499 = 8120249) B8120249
theorem B1604219 : Blo 1603000 1604219 := bstep (se 1 (by rfl) ⟨1203164, by rfl⟩ : syracuseStep 1604219 = 2406329) B2406329
theorem B1604271 : Blo 1603000 1604271 := bstep (se 1 (by rfl) ⟨1203203, by rfl⟩ : syracuseStep 1604271 = 2406407) B2406407
theorem B1604295 : Blo 1603000 1604295 := bstep (se 1 (by rfl) ⟨1203221, by rfl⟩ : syracuseStep 1604295 = 2406443) B2406443
theorem B1604315 : Blo 1603000 1604315 := bstep (se 1 (by rfl) ⟨1203236, by rfl⟩ : syracuseStep 1604315 = 2406473) B2406473
theorem B5413661 : Blo 1603000 5413661 := bstep (se 3 (by rfl) ⟨1015061, by rfl⟩ : syracuseStep 5413661 = 2030123) B2030123
theorem B1604391 : Blo 1603000 1604391 := bstep (se 1 (by rfl) ⟨1203293, by rfl⟩ : syracuseStep 1604391 = 2406587) B2406587
theorem B1604431 : Blo 1603000 1604431 := bstep (se 1 (by rfl) ⟨1203323, by rfl⟩ : syracuseStep 1604431 = 2406647) B2406647
theorem B1604447 : Blo 1603000 1604447 := bstep (se 1 (by rfl) ⟨1203335, by rfl⟩ : syracuseStep 1604447 = 2406671) B2406671
theorem B4062059 : Blo 1603000 4062059 := bstep (se 1 (by rfl) ⟨3046544, by rfl⟩ : syracuseStep 4062059 = 6093089) B6093089
theorem B1604475 : Blo 1603000 1604475 := bstep (se 1 (by rfl) ⟨1203356, by rfl⟩ : syracuseStep 1604475 = 2406713) B2406713
theorem B1604527 : Blo 1603000 1604527 := bstep (se 1 (by rfl) ⟨1203395, by rfl⟩ : syracuseStep 1604527 = 2406791) B2406791
theorem B2407343 : Blo 1603000 2407343 := bstep (se 1 (by rfl) ⟨1805507, by rfl⟩ : syracuseStep 2407343 = 3611015) B3611015
theorem B1604551 : Blo 1603000 1604551 := bstep (se 1 (by rfl) ⟨1203413, by rfl⟩ : syracuseStep 1604551 = 2406827) B2406827
theorem B1604571 : Blo 1603000 1604571 := bstep (se 1 (by rfl) ⟨1203428, by rfl⟩ : syracuseStep 1604571 = 2406857) B2406857
theorem B2407433 : Blo 1603000 2407433 := bstep (se 2 (by rfl) ⟨902787, by rfl⟩ : syracuseStep 2407433 = 1805575) B1805575
theorem B1604647 : Blo 1603000 1604647 := bstep (se 1 (by rfl) ⟨1203485, by rfl⟩ : syracuseStep 1604647 = 2406971) B2406971
theorem B2407463 : Blo 1603000 2407463 := bstep (se 1 (by rfl) ⟨1805597, by rfl⟩ : syracuseStep 2407463 = 3611195) B3611195
theorem B1604687 : Blo 1603000 1604687 := bstep (se 1 (by rfl) ⟨1203515, by rfl⟩ : syracuseStep 1604687 = 2407031) B2407031
theorem B1604703 : Blo 1603000 1604703 := bstep (se 1 (by rfl) ⟨1203527, by rfl⟩ : syracuseStep 1604703 = 2407055) B2407055
theorem B1604731 : Blo 1603000 1604731 := bstep (se 1 (by rfl) ⟨1203548, by rfl⟩ : syracuseStep 1604731 = 2407097) B2407097
theorem B4570283 : Blo 1603000 4570283 := bstep (se 1 (by rfl) ⟨3427712, by rfl⟩ : syracuseStep 4570283 = 6855425) B6855425
theorem B1604783 : Blo 1603000 1604783 := bstep (se 1 (by rfl) ⟨1203587, by rfl⟩ : syracuseStep 1604783 = 2407175) B2407175
theorem B1604807 : Blo 1603000 1604807 := bstep (se 1 (by rfl) ⟨1203605, by rfl⟩ : syracuseStep 1604807 = 2407211) B2407211
theorem B1604827 : Blo 1603000 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B8117495 : Blo 1603000 8117495 := bstep (se 1 (by rfl) ⟨6088121, by rfl⟩ : syracuseStep 8117495 = 12176243) B12176243
theorem B15408407 : Blo 1603000 15408407 := bstep (se 1 (by rfl) ⟨11556305, by rfl⟩ : syracuseStep 15408407 = 23112611) B23112611
theorem B1604903 : Blo 1603000 1604903 := bstep (se 1 (by rfl) ⟨1203677, by rfl⟩ : syracuseStep 1604903 = 2407355) B2407355
theorem B1604943 : Blo 1603000 1604943 := bstep (se 1 (by rfl) ⟨1203707, by rfl⟩ : syracuseStep 1604943 = 2407415) B2407415
theorem B1604959 : Blo 1603000 1604959 := bstep (se 1 (by rfl) ⟨1203719, by rfl⟩ : syracuseStep 1604959 = 2407439) B2407439
theorem B1604987 : Blo 1603000 1604987 := bstep (se 1 (by rfl) ⟨1203740, by rfl⟩ : syracuseStep 1604987 = 2407481) B2407481
theorem B4169089 : Blo 1603000 4169089 := bstep (se 2 (by rfl) ⟨1563408, by rfl⟩ : syracuseStep 4169089 = 3126817) B3126817
theorem B92470733 : Blo 1603000 92470733 := bstep (se 3 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 92470733 = 34676525) B34676525
theorem B5414363 : Blo 1603000 5414363 := bstep (se 1 (by rfl) ⟨4060772, by rfl⟩ : syracuseStep 5414363 = 8121545) B8121545
theorem B18276029 : Blo 1603000 18276029 := bstep (se 3 (by rfl) ⟨3426755, by rfl⟩ : syracuseStep 18276029 = 6853511) B6853511
theorem B8117981 : Blo 1603000 8117981 := bstep (se 3 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 8117981 = 3044243) B3044243
theorem B11567033 : Blo 1603000 11567033 := bstep (se 2 (by rfl) ⟨4337637, by rfl⟩ : syracuseStep 11567033 = 8675275) B8675275
theorem B27763145 : Blo 1603000 27763145 := bstep (se 2 (by rfl) ⟨10411179, by rfl⟩ : syracuseStep 27763145 = 20822359) B20822359
theorem B13009409 : Blo 1603000 13009409 := bstep (se 2 (by rfl) ⟨4878528, by rfl⟩ : syracuseStep 13009409 = 9757057) B9757057
theorem B31695371 : Blo 1603000 31695371 := bstep (se 1 (by rfl) ⟨23771528, by rfl⟩ : syracuseStep 31695371 = 47543057) B47543057
theorem B5415443 : Blo 1603000 5415443 := bstep (se 1 (by rfl) ⟨4061582, by rfl⟩ : syracuseStep 5415443 = 8123165) B8123165
theorem B13001431 : Blo 1603000 13001431 := bstep (se 1 (by rfl) ⟨9751073, by rfl⟩ : syracuseStep 13001431 = 19502147) B19502147
theorem B3130267 : Blo 1603000 3130267 := bstep (se 1 (by rfl) ⟨2347700, by rfl⟩ : syracuseStep 3130267 = 4695401) B4695401
theorem B12174299 : Blo 1603000 12174299 := bstep (se 1 (by rfl) ⟨9130724, by rfl⟩ : syracuseStep 12174299 = 18261449) B18261449
theorem B5563367 : Blo 1603000 5563367 := bstep (se 1 (by rfl) ⟨4172525, by rfl⟩ : syracuseStep 5563367 = 8345051) B8345051
theorem B8119439 : Blo 1603000 8119439 := bstep (se 1 (by rfl) ⟨6089579, by rfl⟩ : syracuseStep 8119439 = 12179159) B12179159
theorem B17335495 : Blo 1603000 17335495 := bstep (se 1 (by rfl) ⟨13001621, by rfl⟩ : syracuseStep 17335495 = 26003243) B26003243
theorem B1803559 : Blo 1603000 1803559 := bstep (se 1 (by rfl) ⟨1352669, by rfl⟩ : syracuseStep 1803559 = 2705339) B2705339
theorem B6088031 : Blo 1603000 6088031 := bstep (se 1 (by rfl) ⟨4566023, by rfl⟩ : syracuseStep 6088031 = 9132047) B9132047
theorem B1803631 : Blo 1603000 1803631 := bstep (se 1 (by rfl) ⟨1352723, by rfl⟩ : syracuseStep 1803631 = 2705447) B2705447
theorem B27411857 : Blo 1603000 27411857 := bstep (se 2 (by rfl) ⟨10279446, by rfl⟩ : syracuseStep 27411857 = 20558893) B20558893
theorem B3425723 : Blo 1603000 3425723 := bstep (se 1 (by rfl) ⟨2569292, by rfl⟩ : syracuseStep 3425723 = 5138585) B5138585
theorem B1926599 : Blo 1603000 1926599 := bstep (se 1 (by rfl) ⟨1444949, by rfl⟩ : syracuseStep 1926599 = 2889899) B2889899
theorem B6505991 : Blo 1603000 6505991 := bstep (se 1 (by rfl) ⟨4879493, by rfl⟩ : syracuseStep 6505991 = 9758987) B9758987
theorem B1803847 : Blo 1603000 1803847 := bstep (se 1 (by rfl) ⟨1352885, by rfl⟩ : syracuseStep 1803847 = 2705771) B2705771
theorem B10028701 : Blo 1603000 10028701 := bstep (se 3 (by rfl) ⟨1880381, by rfl⟩ : syracuseStep 10028701 = 3760763) B3760763
theorem B2705359 : Blo 1603000 2705359 := bstep (se 1 (by rfl) ⟨2029019, by rfl⟩ : syracuseStep 2705359 = 4058039) B4058039
theorem B12183533 : Blo 1603000 12183533 := bstep (se 3 (by rfl) ⟨2284412, by rfl⟩ : syracuseStep 12183533 = 4568825) B4568825
theorem B22235141 : Blo 1603000 22235141 := bstep (se 4 (by rfl) ⟨2084544, by rfl⟩ : syracuseStep 22235141 = 4169089) B4169089
theorem B49408157 : Blo 1603000 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B8120573 : Blo 1603000 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B5777693 : Blo 1603000 5777693 := bstep (se 3 (by rfl) ⟨1083317, by rfl⟩ : syracuseStep 5777693 = 2166635) B2166635
theorem B22260005 : Blo 1603000 22260005 := bstep (se 4 (by rfl) ⟨2086875, by rfl⟩ : syracuseStep 22260005 = 4173751) B4173751
theorem B61647155 : Blo 1603000 61647155 := bstep (se 1 (by rfl) ⟨46235366, by rfl⟩ : syracuseStep 61647155 = 92470733) B92470733
theorem B3606857 : Blo 1603000 3606857 := bstep (se 2 (by rfl) ⟨1352571, by rfl⟩ : syracuseStep 3606857 = 2705143) B2705143
theorem B3606875 : Blo 1603000 3606875 := bstep (se 1 (by rfl) ⟨2705156, by rfl⟩ : syracuseStep 3606875 = 5410313) B5410313
theorem B1804711 : Blo 1603000 1804711 := bstep (se 1 (by rfl) ⟨1353533, by rfl⟩ : syracuseStep 1804711 = 2707067) B2707067
theorem B10275245 : Blo 1603000 10275245 := bstep (se 3 (by rfl) ⟨1926608, by rfl⟩ : syracuseStep 10275245 = 3853217) B3853217
theorem B12184019 : Blo 1603000 12184019 := bstep (se 1 (by rfl) ⟨9138014, by rfl⟩ : syracuseStep 12184019 = 18276029) B18276029
theorem B13191635 : Blo 1603000 13191635 := bstep (se 1 (by rfl) ⟨9893726, by rfl⟩ : syracuseStep 13191635 = 19787453) B19787453
theorem B2706041 : Blo 1603000 2706041 := bstep (se 2 (by rfl) ⟨1014765, by rfl⟩ : syracuseStep 2706041 = 2029531) B2029531
theorem B3295865 : Blo 1603000 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B7711355 : Blo 1603000 7711355 := bstep (se 1 (by rfl) ⟨5783516, by rfl⟩ : syracuseStep 7711355 = 11567033) B11567033
theorem B2706095 : Blo 1603000 2706095 := bstep (se 1 (by rfl) ⟨2029571, by rfl⟩ : syracuseStep 2706095 = 4059143) B4059143
theorem B4057847 : Blo 1603000 4057847 := bstep (se 1 (by rfl) ⟨3043385, by rfl⟩ : syracuseStep 4057847 = 6086771) B6086771
theorem B3607451 : Blo 1603000 3607451 := bstep (se 1 (by rfl) ⟨2705588, by rfl⟩ : syracuseStep 3607451 = 5411177) B5411177
theorem B2706331 : Blo 1603000 2706331 := bstep (se 1 (by rfl) ⟨2029748, by rfl⟩ : syracuseStep 2706331 = 4059497) B4059497
theorem B1805287 : Blo 1603000 1805287 := bstep (se 1 (by rfl) ⟨1353965, by rfl⟩ : syracuseStep 1805287 = 2707931) B2707931
theorem B5139443 : Blo 1603000 5139443 := bstep (se 1 (by rfl) ⟨3854582, by rfl⟩ : syracuseStep 5139443 = 7709165) B7709165
theorem B8121383 : Blo 1603000 8121383 := bstep (se 1 (by rfl) ⟨6091037, by rfl⟩ : syracuseStep 8121383 = 12182075) B12182075
theorem B23129165 : Blo 1603000 23129165 := bstep (se 3 (by rfl) ⟨4336718, by rfl⟩ : syracuseStep 23129165 = 8673437) B8673437
theorem B3607649 : Blo 1603000 3607649 := bstep (se 2 (by rfl) ⟨1352868, by rfl⟩ : syracuseStep 3607649 = 2705737) B2705737
theorem B8670347 : Blo 1603000 8670347 := bstep (se 1 (by rfl) ⟨6502760, by rfl⟩ : syracuseStep 8670347 = 13005521) B13005521
theorem B6851803 : Blo 1603000 6851803 := bstep (se 1 (by rfl) ⟨5138852, by rfl⟩ : syracuseStep 6851803 = 10277705) B10277705
theorem B3607847 : Blo 1603000 3607847 := bstep (se 1 (by rfl) ⟨2705885, by rfl⟩ : syracuseStep 3607847 = 5411771) B5411771
theorem B3427679 : Blo 1603000 3427679 := bstep (se 1 (by rfl) ⟨2570759, by rfl⟩ : syracuseStep 3427679 = 5141519) B5141519
theorem B2780615 : Blo 1603000 2780615 := bstep (se 1 (by rfl) ⟨2085461, by rfl⟩ : syracuseStep 2780615 = 4170923) B4170923
theorem B15412679 : Blo 1603000 15412679 := bstep (se 1 (by rfl) ⟨11559509, by rfl⟩ : syracuseStep 15412679 = 23119019) B23119019
theorem B9514505 : Blo 1603000 9514505 := bstep (se 2 (by rfl) ⟨3567939, by rfl⟩ : syracuseStep 9514505 = 7135879) B7135879
theorem B4058707 : Blo 1603000 4058707 := bstep (se 1 (by rfl) ⟨3044030, by rfl⟩ : syracuseStep 4058707 = 6088061) B6088061
theorem B3608225 : Blo 1603000 3608225 := bstep (se 2 (by rfl) ⟨1353084, by rfl⟩ : syracuseStep 3608225 = 2706169) B2706169
theorem B15241007 : Blo 1603000 15241007 := bstep (se 1 (by rfl) ⟨11430755, by rfl⟩ : syracuseStep 15241007 = 22861511) B22861511
theorem B4567049 : Blo 1603000 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B3608585 : Blo 1603000 3608585 := bstep (se 2 (by rfl) ⟨1353219, by rfl⟩ : syracuseStep 3608585 = 2706439) B2706439
theorem B6852761 : Blo 1603000 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B13709483 : Blo 1603000 13709483 := bstep (se 1 (by rfl) ⟨10282112, by rfl⟩ : syracuseStep 13709483 = 20564225) B20564225
theorem B9138379 : Blo 1603000 9138379 := bstep (se 1 (by rfl) ⟨6853784, by rfl⟩ : syracuseStep 9138379 = 13707569) B13707569
theorem B8229073 : Blo 1603000 8229073 := bstep (se 2 (by rfl) ⟨3085902, by rfl⟩ : syracuseStep 8229073 = 6171805) B6171805
theorem B46870849 : Blo 1603000 46870849 := bstep (se 2 (by rfl) ⟨17576568, by rfl⟩ : syracuseStep 46870849 = 35153137) B35153137
theorem B12185963 : Blo 1603000 12185963 := bstep (se 1 (by rfl) ⟨9139472, by rfl⟩ : syracuseStep 12185963 = 18278945) B18278945
theorem B2707823 : Blo 1603000 2707823 := bstep (se 1 (by rfl) ⟨2030867, by rfl⟩ : syracuseStep 2707823 = 4061735) B4061735
theorem B2404775 : Blo 1603000 2404775 := bstep (se 1 (by rfl) ⟨1803581, by rfl⟩ : syracuseStep 2404775 = 3607163) B3607163
theorem B3608999 : Blo 1603000 3608999 := bstep (se 1 (by rfl) ⟨2706749, by rfl⟩ : syracuseStep 3608999 = 5413499) B5413499
theorem B4338103 : Blo 1603000 4338103 := bstep (se 1 (by rfl) ⟨3253577, by rfl⟩ : syracuseStep 4338103 = 6507155) B6507155
theorem B23122421 : Blo 1603000 23122421 := bstep (se 5 (by rfl) ⟨1083863, by rfl⟩ : syracuseStep 23122421 = 2167727) B2167727
theorem B2404859 : Blo 1603000 2404859 := bstep (se 1 (by rfl) ⟨1803644, by rfl⟩ : syracuseStep 2404859 = 3607289) B3607289
theorem B3609107 : Blo 1603000 3609107 := bstep (se 1 (by rfl) ⟨2706830, by rfl⟩ : syracuseStep 3609107 = 5413661) B5413661
theorem B2708039 : Blo 1603000 2708039 := bstep (se 1 (by rfl) ⟨2031029, by rfl⟩ : syracuseStep 2708039 = 4062059) B4062059
theorem B3609161 : Blo 1603000 3609161 := bstep (se 2 (by rfl) ⟨1353435, by rfl⟩ : syracuseStep 3609161 = 2706871) B2706871
theorem B2404985 : Blo 1603000 2404985 := bstep (se 2 (by rfl) ⟨901869, by rfl⟩ : syracuseStep 2404985 = 1803739) B1803739
theorem B2405039 : Blo 1603000 2405039 := bstep (se 1 (by rfl) ⟨1803779, by rfl⟩ : syracuseStep 2405039 = 3607559) B3607559
theorem B2405087 : Blo 1603000 2405087 := bstep (se 1 (by rfl) ⟨1803815, by rfl⟩ : syracuseStep 2405087 = 3607631) B3607631
theorem B5411663 : Blo 1603000 5411663 := bstep (se 1 (by rfl) ⟨4058747, by rfl⟩ : syracuseStep 5411663 = 8117495) B8117495
theorem B4059983 : Blo 1603000 4059983 := bstep (se 1 (by rfl) ⟨3044987, by rfl⟩ : syracuseStep 4059983 = 6089975) B6089975
theorem B2405351 : Blo 1603000 2405351 := bstep (se 1 (by rfl) ⟨1804013, by rfl⟩ : syracuseStep 2405351 = 3608027) B3608027
theorem B3609575 : Blo 1603000 3609575 := bstep (se 1 (by rfl) ⟨2707181, by rfl⟩ : syracuseStep 3609575 = 5414363) B5414363
theorem B8123489 : Blo 1603000 8123489 := bstep (se 2 (by rfl) ⟨3046308, by rfl⟩ : syracuseStep 8123489 = 6092617) B6092617
theorem B6091919 : Blo 1603000 6091919 := bstep (se 1 (by rfl) ⟨4568939, by rfl⟩ : syracuseStep 6091919 = 9137879) B9137879
theorem B5411987 : Blo 1603000 5411987 := bstep (se 1 (by rfl) ⟨4058990, by rfl⟩ : syracuseStep 5411987 = 8117981) B8117981
theorem B2405609 : Blo 1603000 2405609 := bstep (se 2 (by rfl) ⟨902103, by rfl⟩ : syracuseStep 2405609 = 1804207) B1804207
theorem B2168041 : Blo 1603000 2168041 := bstep (se 2 (by rfl) ⟨813015, by rfl⟩ : syracuseStep 2168041 = 1626031) B1626031
theorem B2405663 : Blo 1603000 2405663 := bstep (se 1 (by rfl) ⟨1804247, by rfl⟩ : syracuseStep 2405663 = 3608495) B3608495
theorem B10974503 : Blo 1603000 10974503 := bstep (se 1 (by rfl) ⟨8230877, by rfl⟩ : syracuseStep 10974503 = 16461755) B16461755
theorem B4568359 : Blo 1603000 4568359 := bstep (se 1 (by rfl) ⟨3426269, by rfl⟩ : syracuseStep 4568359 = 6852539) B6852539
theorem B8115551 : Blo 1603000 8115551 := bstep (se 1 (by rfl) ⟨6086663, by rfl⟩ : syracuseStep 8115551 = 12173327) B12173327
theorem B3609953 : Blo 1603000 3609953 := bstep (se 2 (by rfl) ⟨1353732, by rfl⟩ : syracuseStep 3609953 = 2707465) B2707465
theorem B18281861 : Blo 1603000 18281861 := bstep (se 4 (by rfl) ⟨1713924, by rfl⟩ : syracuseStep 18281861 = 3427849) B3427849
theorem B5412257 : Blo 1603000 5412257 := bstep (se 2 (by rfl) ⟨2029596, by rfl⟩ : syracuseStep 5412257 = 4059193) B4059193
theorem B3610043 : Blo 1603000 3610043 := bstep (se 1 (by rfl) ⟨2707532, by rfl⟩ : syracuseStep 3610043 = 5415065) B5415065
theorem B2405831 : Blo 1603000 2405831 := bstep (se 1 (by rfl) ⟨1804373, by rfl⟩ : syracuseStep 2405831 = 3608747) B3608747
theorem B4060631 : Blo 1603000 4060631 := bstep (se 1 (by rfl) ⟨3045473, by rfl⟩ : syracuseStep 4060631 = 6090947) B6090947
theorem B1603067 : Blo 1603000 1603067 := bstep (se 1 (by rfl) ⟨1202300, by rfl⟩ : syracuseStep 1603067 = 2404601) B2404601
theorem B4568633 : Blo 1603000 4568633 := bstep (se 2 (by rfl) ⟨1713237, by rfl⟩ : syracuseStep 4568633 = 3426475) B3426475
theorem B3610169 : Blo 1603000 3610169 := bstep (se 2 (by rfl) ⟨1353813, by rfl⟩ : syracuseStep 3610169 = 2707627) B2707627
theorem B1603135 : Blo 1603000 1603135 := bstep (se 1 (by rfl) ⟨1202351, by rfl⟩ : syracuseStep 1603135 = 2404703) B2404703
theorem B1603143 : Blo 1603000 1603143 := bstep (se 1 (by rfl) ⟨1202357, by rfl⟩ : syracuseStep 1603143 = 2404715) B2404715
theorem B2029151 : Blo 1603000 2029151 := bstep (se 1 (by rfl) ⟨1521863, by rfl⟩ : syracuseStep 2029151 = 3043727) B3043727
theorem B2283103 : Blo 1603000 2283103 := bstep (se 1 (by rfl) ⟨1712327, by rfl⟩ : syracuseStep 2283103 = 3424655) B3424655
theorem B1603295 : Blo 1603000 1603295 := bstep (se 1 (by rfl) ⟨1202471, by rfl⟩ : syracuseStep 1603295 = 2404943) B2404943
theorem B12187421 : Blo 1603000 12187421 := bstep (se 3 (by rfl) ⟨2285141, by rfl⟩ : syracuseStep 12187421 = 4570283) B4570283
theorem B2406185 : Blo 1603000 2406185 := bstep (se 2 (by rfl) ⟨902319, by rfl⟩ : syracuseStep 2406185 = 1804639) B1804639
theorem B1603375 : Blo 1603000 1603375 := bstep (se 1 (by rfl) ⟨1202531, by rfl⟩ : syracuseStep 1603375 = 2405063) B2405063
theorem B2406191 : Blo 1603000 2406191 := bstep (se 1 (by rfl) ⟨1804643, by rfl⟩ : syracuseStep 2406191 = 3609287) B3609287
theorem B4060975 : Blo 1603000 4060975 := bstep (se 1 (by rfl) ⟨3045731, by rfl⟩ : syracuseStep 4060975 = 6091463) B6091463
theorem B2283319 : Blo 1603000 2283319 := bstep (se 1 (by rfl) ⟨1712489, by rfl⟩ : syracuseStep 2283319 = 3424979) B3424979
theorem B1603483 : Blo 1603000 1603483 := bstep (se 1 (by rfl) ⟨1202612, by rfl⟩ : syracuseStep 1603483 = 2405225) B2405225
theorem B1603535 : Blo 1603000 1603535 := bstep (se 1 (by rfl) ⟨1202651, by rfl⟩ : syracuseStep 1603535 = 2405303) B2405303
theorem B1603559 : Blo 1603000 1603559 := bstep (se 1 (by rfl) ⟨1202669, by rfl⟩ : syracuseStep 1603559 = 2405339) B2405339
theorem B7313543 : Blo 1603000 7313543 := bstep (se 1 (by rfl) ⟨5485157, by rfl⟩ : syracuseStep 7313543 = 10970315) B10970315
theorem B3610835 : Blo 1603000 3610835 := bstep (se 1 (by rfl) ⟨2708126, by rfl⟩ : syracuseStep 3610835 = 5416253) B5416253
theorem B15407333 : Blo 1603000 15407333 := bstep (se 4 (by rfl) ⟨1444437, by rfl⟩ : syracuseStep 15407333 = 2888875) B2888875
theorem B2406665 : Blo 1603000 2406665 := bstep (se 2 (by rfl) ⟨902499, by rfl⟩ : syracuseStep 2406665 = 1804999) B1804999
theorem B3610889 : Blo 1603000 3610889 := bstep (se 2 (by rfl) ⟨1354083, by rfl⟩ : syracuseStep 3610889 = 2708167) B2708167
theorem B2029855 : Blo 1603000 2029855 := bstep (se 1 (by rfl) ⟨1522391, by rfl⟩ : syracuseStep 2029855 = 3044783) B3044783
theorem B1603871 : Blo 1603000 1603871 := bstep (se 1 (by rfl) ⟨1202903, by rfl⟩ : syracuseStep 1603871 = 2405807) B2405807
theorem B1603931 : Blo 1603000 1603931 := bstep (se 1 (by rfl) ⟨1202948, by rfl⟩ : syracuseStep 1603931 = 2405897) B2405897
theorem B1603951 : Blo 1603000 1603951 := bstep (se 1 (by rfl) ⟨1202963, by rfl⟩ : syracuseStep 1603951 = 2405927) B2405927
theorem B2406767 : Blo 1603000 2406767 := bstep (se 1 (by rfl) ⟨1805075, by rfl⟩ : syracuseStep 2406767 = 3610151) B3610151
theorem B6502823 : Blo 1603000 6502823 := bstep (se 1 (by rfl) ⟨4877117, by rfl⟩ : syracuseStep 6502823 = 9754235) B9754235
theorem B1604007 : Blo 1603000 1604007 := bstep (se 1 (by rfl) ⟨1203005, by rfl⟩ : syracuseStep 1604007 = 2406011) B2406011
theorem B5487031 : Blo 1603000 5487031 := bstep (se 1 (by rfl) ⟨4115273, by rfl⟩ : syracuseStep 5487031 = 8230547) B8230547
theorem B4061623 : Blo 1603000 4061623 := bstep (se 1 (by rfl) ⟨3046217, by rfl⟩ : syracuseStep 4061623 = 6092435) B6092435
theorem B3611105 : Blo 1603000 3611105 := bstep (se 2 (by rfl) ⟨1354164, by rfl⟩ : syracuseStep 3611105 = 2708329) B2708329
theorem B12999163 : Blo 1603000 12999163 := bstep (se 1 (by rfl) ⟨9749372, by rfl⟩ : syracuseStep 12999163 = 19498745) B19498745
theorem B1604091 : Blo 1603000 1604091 := bstep (se 1 (by rfl) ⟨1203068, by rfl⟩ : syracuseStep 1604091 = 2406137) B2406137
theorem B1604159 : Blo 1603000 1604159 := bstep (se 1 (by rfl) ⟨1203119, by rfl⟩ : syracuseStep 1604159 = 2406239) B2406239
theorem B1604167 : Blo 1603000 1604167 := bstep (se 1 (by rfl) ⟨1203125, by rfl⟩ : syracuseStep 1604167 = 2406251) B2406251
theorem B2406983 : Blo 1603000 2406983 := bstep (se 1 (by rfl) ⟨1805237, by rfl⟩ : syracuseStep 2406983 = 3610475) B3610475
theorem B2407019 : Blo 1603000 2407019 := bstep (se 1 (by rfl) ⟨1805264, by rfl⟩ : syracuseStep 2407019 = 3610529) B3610529
theorem B1604319 : Blo 1603000 1604319 := bstep (se 1 (by rfl) ⟨1203239, by rfl⟩ : syracuseStep 1604319 = 2406479) B2406479
theorem B1604399 : Blo 1603000 1604399 := bstep (se 1 (by rfl) ⟨1203299, by rfl⟩ : syracuseStep 1604399 = 2406599) B2406599
theorem B2284367 : Blo 1603000 2284367 := bstep (se 1 (by rfl) ⟨1713275, by rfl⟩ : syracuseStep 2284367 = 3426551) B3426551
theorem B2407247 : Blo 1603000 2407247 := bstep (se 1 (by rfl) ⟨1805435, by rfl⟩ : syracuseStep 2407247 = 3610871) B3610871
theorem B10976143 : Blo 1603000 10976143 := bstep (se 1 (by rfl) ⟨8232107, by rfl⟩ : syracuseStep 10976143 = 16464215) B16464215
theorem B1604507 : Blo 1603000 1604507 := bstep (se 1 (by rfl) ⟨1203380, by rfl⟩ : syracuseStep 1604507 = 2406761) B2406761
theorem B1604559 : Blo 1603000 1604559 := bstep (se 1 (by rfl) ⟨1203419, by rfl⟩ : syracuseStep 1604559 = 2406839) B2406839
theorem B1604583 : Blo 1603000 1604583 := bstep (se 1 (by rfl) ⟨1203437, by rfl⟩ : syracuseStep 1604583 = 2406875) B2406875
theorem B6093863 : Blo 1603000 6093863 := bstep (se 1 (by rfl) ⟨4570397, by rfl⟩ : syracuseStep 6093863 = 9140795) B9140795
theorem B2284777 : Blo 1603000 2284777 := bstep (se 2 (by rfl) ⟨856791, by rfl⟩ : syracuseStep 2284777 = 1713583) B1713583
theorem B1604895 : Blo 1603000 1604895 := bstep (se 1 (by rfl) ⟨1203671, by rfl⟩ : syracuseStep 1604895 = 2407343) B2407343
theorem B1604955 : Blo 1603000 1604955 := bstep (se 1 (by rfl) ⟨1203716, by rfl⟩ : syracuseStep 1604955 = 2407433) B2407433
theorem B1604975 : Blo 1603000 1604975 := bstep (se 1 (by rfl) ⟨1203731, by rfl⟩ : syracuseStep 1604975 = 2407463) B2407463
theorem B14638501 : Blo 1603000 14638501 := bstep (se 4 (by rfl) ⟨1372359, by rfl⟩ : syracuseStep 14638501 = 2744719) B2744719
theorem B10272271 : Blo 1603000 10272271 := bstep (se 1 (by rfl) ⟨7704203, by rfl⟩ : syracuseStep 10272271 = 15408407) B15408407
theorem B8117819 : Blo 1603000 8117819 := bstep (se 1 (by rfl) ⟨6088364, by rfl⟩ : syracuseStep 8117819 = 12176729) B12176729
theorem B6848317 : Blo 1603000 6848317 := bstep (se 3 (by rfl) ⟨1284059, by rfl⟩ : syracuseStep 6848317 = 2568119) B2568119
theorem B5415497 : Blo 1603000 5415497 := bstep (se 2 (by rfl) ⟨2030811, by rfl⟩ : syracuseStep 5415497 = 4061623) B4061623
theorem B5784137 : Blo 1603000 5784137 := bstep (se 2 (by rfl) ⟨2169051, by rfl⟩ : syracuseStep 5784137 = 4338103) B4338103
theorem B5415659 : Blo 1603000 5415659 := bstep (se 1 (by rfl) ⟨4061744, by rfl⟩ : syracuseStep 5415659 = 8123489) B8123489
theorem B7316335 : Blo 1603000 7316335 := bstep (se 1 (by rfl) ⟨5487251, by rfl⟩ : syracuseStep 7316335 = 10974503) B10974503
theorem B17335241 : Blo 1603000 17335241 := bstep (se 2 (by rfl) ⟨6500715, by rfl⟩ : syracuseStep 17335241 = 13001431) B13001431
theorem B5137597 : Blo 1603000 5137597 := bstep (se 3 (by rfl) ⟨963299, by rfl⟩ : syracuseStep 5137597 = 1926599) B1926599
theorem B7414973 : Blo 1603000 7414973 := bstep (se 3 (by rfl) ⟨1390307, by rfl⟩ : syracuseStep 7414973 = 2780615) B2780615
theorem B4875695 : Blo 1603000 4875695 := bstep (se 1 (by rfl) ⟨3656771, by rfl⟩ : syracuseStep 4875695 = 7313543) B7313543
theorem B3851795 : Blo 1603000 3851795 := bstep (se 1 (by rfl) ⟨2888846, by rfl⟩ : syracuseStep 3851795 = 5777693) B5777693
theorem B4335215 : Blo 1603000 4335215 := bstep (se 1 (by rfl) ⟨3251411, by rfl⟩ : syracuseStep 4335215 = 6502823) B6502823
theorem B6850163 : Blo 1603000 6850163 := bstep (se 1 (by rfl) ⟨5137622, by rfl⟩ : syracuseStep 6850163 = 10275245) B10275245
theorem B9135737 : Blo 1603000 9135737 := bstep (se 2 (by rfl) ⟨3425901, by rfl⟩ : syracuseStep 9135737 = 6851803) B6851803
theorem B1804027 : Blo 1603000 1804027 := bstep (se 1 (by rfl) ⟨1353020, by rfl⟩ : syracuseStep 1804027 = 2706041) B2706041
theorem B2197243 : Blo 1603000 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B1804063 : Blo 1603000 1804063 := bstep (se 1 (by rfl) ⟨1353047, by rfl⟩ : syracuseStep 1804063 = 2706095) B2706095
theorem B2705231 : Blo 1603000 2705231 := bstep (se 1 (by rfl) ⟨2028923, by rfl⟩ : syracuseStep 2705231 = 4057847) B4057847
theorem B3426295 : Blo 1603000 3426295 := bstep (se 1 (by rfl) ⟨2569721, by rfl⟩ : syracuseStep 3426295 = 5139443) B5139443
theorem B15419443 : Blo 1603000 15419443 := bstep (se 1 (by rfl) ⟨11564582, by rfl⟩ : syracuseStep 15419443 = 23129165) B23129165
theorem B78072005 : Blo 1603000 78072005 := bstep (se 4 (by rfl) ⟨7319250, by rfl⟩ : syracuseStep 78072005 = 14638501) B14638501
theorem B13371601 : Blo 1603000 13371601 := bstep (se 2 (by rfl) ⟨5014350, by rfl⟩ : syracuseStep 13371601 = 10028701) B10028701
theorem B29264165 : Blo 1603000 29264165 := bstep (se 4 (by rfl) ⟨2743515, by rfl⟩ : syracuseStep 29264165 = 5487031) B5487031
theorem B10275119 : Blo 1603000 10275119 := bstep (se 1 (by rfl) ⟨7706339, by rfl⟩ : syracuseStep 10275119 = 15412679) B15412679
theorem B6343003 : Blo 1603000 6343003 := bstep (se 1 (by rfl) ⟨4757252, by rfl⟩ : syracuseStep 6343003 = 9514505) B9514505
theorem B10160671 : Blo 1603000 10160671 := bstep (se 1 (by rfl) ⟨7620503, by rfl⟩ : syracuseStep 10160671 = 15241007) B15241007
theorem B3607145 : Blo 1603000 3607145 := bstep (se 2 (by rfl) ⟨1352679, by rfl⟩ : syracuseStep 3607145 = 2705359) B2705359
theorem B1805215 : Blo 1603000 1805215 := bstep (se 1 (by rfl) ⟨1353911, by rfl⟩ : syracuseStep 1805215 = 2707823) B2707823
theorem B12184505 : Blo 1603000 12184505 := bstep (se 2 (by rfl) ⟨4569189, by rfl⟩ : syracuseStep 12184505 = 9138379) B9138379
theorem B10972097 : Blo 1603000 10972097 := bstep (se 2 (by rfl) ⟨4114536, by rfl⟩ : syracuseStep 10972097 = 8229073) B8229073
theorem B18508763 : Blo 1603000 18508763 := bstep (se 1 (by rfl) ⟨13881572, by rfl⟩ : syracuseStep 18508763 = 27763145) B27763145
theorem B21130247 : Blo 1603000 21130247 := bstep (se 1 (by rfl) ⟨15847685, by rfl⟩ : syracuseStep 21130247 = 31695371) B31695371
theorem B2706473 : Blo 1603000 2706473 := bstep (se 2 (by rfl) ⟨1014927, by rfl⟩ : syracuseStep 2706473 = 2029855) B2029855
theorem B1805359 : Blo 1603000 1805359 := bstep (se 1 (by rfl) ⟨1354019, by rfl⟩ : syracuseStep 1805359 = 2708039) B2708039
theorem B131755085 : Blo 1603000 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B3607775 : Blo 1603000 3607775 := bstep (se 1 (by rfl) ⟨2705831, by rfl⟩ : syracuseStep 3607775 = 5411663) B5411663
theorem B2706655 : Blo 1603000 2706655 := bstep (se 1 (by rfl) ⟨2029991, by rfl⟩ : syracuseStep 2706655 = 4059983) B4059983
theorem B3607991 : Blo 1603000 3607991 := bstep (se 1 (by rfl) ⟨2705993, by rfl⟩ : syracuseStep 3607991 = 5411987) B5411987
theorem B5410367 : Blo 1603000 5410367 := bstep (se 1 (by rfl) ⟨4057775, by rfl⟩ : syracuseStep 5410367 = 8115551) B8115551
theorem B4058687 : Blo 1603000 4058687 := bstep (se 1 (by rfl) ⟨3044015, by rfl⟩ : syracuseStep 4058687 = 6088031) B6088031
theorem B3608171 : Blo 1603000 3608171 := bstep (se 1 (by rfl) ⟨2706128, by rfl⟩ : syracuseStep 3608171 = 5412257) B5412257
theorem B2707087 : Blo 1603000 2707087 := bstep (se 1 (by rfl) ⟨2030315, by rfl⟩ : syracuseStep 2707087 = 4060631) B4060631
theorem B4337327 : Blo 1603000 4337327 := bstep (se 1 (by rfl) ⟨3252995, by rfl⟩ : syracuseStep 4337327 = 6505991) B6505991
theorem B14634857 : Blo 1603000 14634857 := bstep (se 2 (by rfl) ⟨5488071, by rfl⟩ : syracuseStep 14634857 = 10976143) B10976143
theorem B3608441 : Blo 1603000 3608441 := bstep (se 2 (by rfl) ⟨1353165, by rfl⟩ : syracuseStep 3608441 = 2706331) B2706331
theorem B4173689 : Blo 1603000 4173689 := bstep (se 2 (by rfl) ⟨1565133, by rfl⟩ : syracuseStep 4173689 = 3130267) B3130267
theorem B12185477 : Blo 1603000 12185477 := bstep (se 4 (by rfl) ⟨1142388, by rfl⟩ : syracuseStep 12185477 = 2284777) B2284777
theorem B8122355 : Blo 1603000 8122355 := bstep (se 1 (by rfl) ⟨6091766, by rfl⟩ : syracuseStep 8122355 = 12183533) B12183533
theorem B14823427 : Blo 1603000 14823427 := bstep (se 1 (by rfl) ⟨11117570, by rfl⟩ : syracuseStep 14823427 = 22235141) B22235141
theorem B14840003 : Blo 1603000 14840003 := bstep (se 1 (by rfl) ⟨11130002, by rfl⟩ : syracuseStep 14840003 = 22260005) B22260005
theorem B2404571 : Blo 1603000 2404571 := bstep (se 1 (by rfl) ⟨1803428, by rfl⟩ : syracuseStep 2404571 = 3606857) B3606857
theorem B2404583 : Blo 1603000 2404583 := bstep (se 1 (by rfl) ⟨1803437, by rfl⟩ : syracuseStep 2404583 = 3606875) B3606875
theorem B5411069 : Blo 1603000 5411069 := bstep (se 3 (by rfl) ⟨1014575, by rfl⟩ : syracuseStep 5411069 = 2029151) B2029151
theorem B23113993 : Blo 1603000 23113993 := bstep (se 2 (by rfl) ⟨8667747, by rfl⟩ : syracuseStep 23113993 = 17335495) B17335495
theorem B12177701 : Blo 1603000 12177701 := bstep (se 4 (by rfl) ⟨1141659, by rfl⟩ : syracuseStep 12177701 = 2283319) B2283319
theorem B8122679 : Blo 1603000 8122679 := bstep (se 1 (by rfl) ⟨6092009, by rfl⟩ : syracuseStep 8122679 = 12184019) B12184019
theorem B8794423 : Blo 1603000 8794423 := bstep (se 1 (by rfl) ⟨6595817, by rfl⟩ : syracuseStep 8794423 = 13191635) B13191635
theorem B2404745 : Blo 1603000 2404745 := bstep (se 2 (by rfl) ⟨901779, by rfl⟩ : syracuseStep 2404745 = 1803559) B1803559
theorem B6091145 : Blo 1603000 6091145 := bstep (se 2 (by rfl) ⟨2284179, by rfl⟩ : syracuseStep 6091145 = 4568359) B4568359
theorem B5140903 : Blo 1603000 5140903 := bstep (se 1 (by rfl) ⟨3855677, by rfl⟩ : syracuseStep 5140903 = 7711355) B7711355
theorem B2404841 : Blo 1603000 2404841 := bstep (se 2 (by rfl) ⟨901815, by rfl⟩ : syracuseStep 2404841 = 1803631) B1803631
theorem B2404967 : Blo 1603000 2404967 := bstep (se 1 (by rfl) ⟨1803725, by rfl⟩ : syracuseStep 2404967 = 3607451) B3607451
theorem B2405099 : Blo 1603000 2405099 := bstep (se 1 (by rfl) ⟨1803824, by rfl⟩ : syracuseStep 2405099 = 3607649) B3607649
theorem B5780231 : Blo 1603000 5780231 := bstep (se 1 (by rfl) ⟨4335173, by rfl⟩ : syracuseStep 5780231 = 8670347) B8670347
theorem B2405129 : Blo 1603000 2405129 := bstep (se 2 (by rfl) ⟨901923, by rfl⟩ : syracuseStep 2405129 = 1803847) B1803847
theorem B5411609 : Blo 1603000 5411609 := bstep (se 2 (by rfl) ⟨2029353, by rfl⟩ : syracuseStep 5411609 = 4058707) B4058707
theorem B3044137 : Blo 1603000 3044137 := bstep (se 2 (by rfl) ⟨1141551, by rfl⟩ : syracuseStep 3044137 = 2283103) B2283103
theorem B2405231 : Blo 1603000 2405231 := bstep (se 1 (by rfl) ⟨1803923, by rfl⟩ : syracuseStep 2405231 = 3607847) B3607847
theorem B6091645 : Blo 1603000 6091645 := bstep (se 3 (by rfl) ⟨1142183, by rfl⟩ : syracuseStep 6091645 = 2284367) B2284367
theorem B5411879 : Blo 1603000 5411879 := bstep (se 1 (by rfl) ⟨4058909, by rfl⟩ : syracuseStep 5411879 = 8117819) B8117819
theorem B9131089 : Blo 1603000 9131089 := bstep (se 2 (by rfl) ⟨3424158, by rfl⟩ : syracuseStep 9131089 = 6848317) B6848317
theorem B2405483 : Blo 1603000 2405483 := bstep (se 1 (by rfl) ⟨1804112, by rfl⟩ : syracuseStep 2405483 = 3608225) B3608225
theorem B3044699 : Blo 1603000 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B2405723 : Blo 1603000 2405723 := bstep (se 1 (by rfl) ⟨1804292, by rfl⟩ : syracuseStep 2405723 = 3608585) B3608585
theorem B4568507 : Blo 1603000 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B9139655 : Blo 1603000 9139655 := bstep (se 1 (by rfl) ⟨6854741, by rfl⟩ : syracuseStep 9139655 = 13709483) B13709483
theorem B8123975 : Blo 1603000 8123975 := bstep (se 1 (by rfl) ⟨6092981, by rfl⟩ : syracuseStep 8123975 = 12185963) B12185963
theorem B1603183 : Blo 1603000 1603183 := bstep (se 1 (by rfl) ⟨1202387, by rfl⟩ : syracuseStep 1603183 = 2404775) B2404775
theorem B2405999 : Blo 1603000 2405999 := bstep (se 1 (by rfl) ⟨1804499, by rfl⟩ : syracuseStep 2405999 = 3608999) B3608999
theorem B15414947 : Blo 1603000 15414947 := bstep (se 1 (by rfl) ⟨11561210, by rfl⟩ : syracuseStep 15414947 = 23122421) B23122421
theorem B1603239 : Blo 1603000 1603239 := bstep (se 1 (by rfl) ⟨1202429, by rfl⟩ : syracuseStep 1603239 = 2404859) B2404859
theorem B8672939 : Blo 1603000 8672939 := bstep (se 1 (by rfl) ⟨6504704, by rfl⟩ : syracuseStep 8672939 = 13009409) B13009409
theorem B2406071 : Blo 1603000 2406071 := bstep (se 1 (by rfl) ⟨1804553, by rfl⟩ : syracuseStep 2406071 = 3609107) B3609107
theorem B3610295 : Blo 1603000 3610295 := bstep (se 1 (by rfl) ⟨2707721, by rfl⟩ : syracuseStep 3610295 = 5415443) B5415443
theorem B2406107 : Blo 1603000 2406107 := bstep (se 1 (by rfl) ⟨1804580, by rfl⟩ : syracuseStep 2406107 = 3609161) B3609161
theorem B1603323 : Blo 1603000 1603323 := bstep (se 1 (by rfl) ⟨1202492, by rfl⟩ : syracuseStep 1603323 = 2404985) B2404985
theorem B62494465 : Blo 1603000 62494465 := bstep (se 2 (by rfl) ⟨23435424, by rfl⟩ : syracuseStep 62494465 = 46870849) B46870849
theorem B1603359 : Blo 1603000 1603359 := bstep (se 1 (by rfl) ⟨1202519, by rfl⟩ : syracuseStep 1603359 = 2405039) B2405039
theorem B1603391 : Blo 1603000 1603391 := bstep (se 1 (by rfl) ⟨1202543, by rfl⟩ : syracuseStep 1603391 = 2405087) B2405087
theorem B2406281 : Blo 1603000 2406281 := bstep (se 2 (by rfl) ⟨902355, by rfl⟩ : syracuseStep 2406281 = 1804711) B1804711
theorem B8116199 : Blo 1603000 8116199 := bstep (se 1 (by rfl) ⟨6087149, by rfl⟩ : syracuseStep 8116199 = 12174299) B12174299
theorem B1603567 : Blo 1603000 1603567 := bstep (se 1 (by rfl) ⟨1202675, by rfl⟩ : syracuseStep 1603567 = 2405351) B2405351
theorem B2406383 : Blo 1603000 2406383 := bstep (se 1 (by rfl) ⟨1804787, by rfl⟩ : syracuseStep 2406383 = 3609575) B3609575
theorem B3708911 : Blo 1603000 3708911 := bstep (se 1 (by rfl) ⟨2781683, by rfl⟩ : syracuseStep 3708911 = 5563367) B5563367
theorem B17332217 : Blo 1603000 17332217 := bstep (se 2 (by rfl) ⟨6499581, by rfl⟩ : syracuseStep 17332217 = 12999163) B12999163
theorem B5412959 : Blo 1603000 5412959 := bstep (se 1 (by rfl) ⟨4059719, by rfl⟩ : syracuseStep 5412959 = 8119439) B8119439
theorem B4061279 : Blo 1603000 4061279 := bstep (se 1 (by rfl) ⟨3045959, by rfl⟩ : syracuseStep 4061279 = 6091919) B6091919
theorem B1603739 : Blo 1603000 1603739 := bstep (se 1 (by rfl) ⟨1202804, by rfl⟩ : syracuseStep 1603739 = 2405609) B2405609
theorem B1603775 : Blo 1603000 1603775 := bstep (se 1 (by rfl) ⟨1202831, by rfl⟩ : syracuseStep 1603775 = 2405663) B2405663
theorem B2406635 : Blo 1603000 2406635 := bstep (se 1 (by rfl) ⟨1804976, by rfl⟩ : syracuseStep 2406635 = 3609953) B3609953
theorem B12187907 : Blo 1603000 12187907 := bstep (se 1 (by rfl) ⟨9140930, by rfl⟩ : syracuseStep 12187907 = 18281861) B18281861
theorem B18274571 : Blo 1603000 18274571 := bstep (se 1 (by rfl) ⟨13705928, by rfl⟩ : syracuseStep 18274571 = 27411857) B27411857
theorem B2283815 : Blo 1603000 2283815 := bstep (se 1 (by rfl) ⟨1712861, by rfl⟩ : syracuseStep 2283815 = 3425723) B3425723
theorem B2406695 : Blo 1603000 2406695 := bstep (se 1 (by rfl) ⟨1805021, by rfl⟩ : syracuseStep 2406695 = 3610043) B3610043
theorem B1603887 : Blo 1603000 1603887 := bstep (se 1 (by rfl) ⟨1202915, by rfl⟩ : syracuseStep 1603887 = 2405831) B2405831
theorem B3045755 : Blo 1603000 3045755 := bstep (se 1 (by rfl) ⟨2284316, by rfl⟩ : syracuseStep 3045755 = 4568633) B4568633
theorem B2406779 : Blo 1603000 2406779 := bstep (se 1 (by rfl) ⟨1805084, by rfl⟩ : syracuseStep 2406779 = 3610169) B3610169
theorem B8124947 : Blo 1603000 8124947 := bstep (se 1 (by rfl) ⟨6093710, by rfl⟩ : syracuseStep 8124947 = 12187421) B12187421
theorem B1604123 : Blo 1603000 1604123 := bstep (se 1 (by rfl) ⟨1203092, by rfl⟩ : syracuseStep 1604123 = 2406185) B2406185
theorem B1604127 : Blo 1603000 1604127 := bstep (se 1 (by rfl) ⟨1203095, by rfl⟩ : syracuseStep 1604127 = 2406191) B2406191
theorem B2407049 : Blo 1603000 2407049 := bstep (se 2 (by rfl) ⟨902643, by rfl⟩ : syracuseStep 2407049 = 1805287) B1805287
theorem B2407223 : Blo 1603000 2407223 := bstep (se 1 (by rfl) ⟨1805417, by rfl⟩ : syracuseStep 2407223 = 3610835) B3610835
theorem B10271555 : Blo 1603000 10271555 := bstep (se 1 (by rfl) ⟨7703666, by rfl⟩ : syracuseStep 10271555 = 15407333) B15407333
theorem B5413715 : Blo 1603000 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B1604443 : Blo 1603000 1604443 := bstep (se 1 (by rfl) ⟨1203332, by rfl⟩ : syracuseStep 1604443 = 2406665) B2406665
theorem B2407259 : Blo 1603000 2407259 := bstep (se 1 (by rfl) ⟨1805444, by rfl⟩ : syracuseStep 2407259 = 3610889) B3610889
theorem B41098103 : Blo 1603000 41098103 := bstep (se 1 (by rfl) ⟨30823577, by rfl⟩ : syracuseStep 41098103 = 61647155) B61647155
theorem B1604511 : Blo 1603000 1604511 := bstep (se 1 (by rfl) ⟨1203383, by rfl⟩ : syracuseStep 1604511 = 2406767) B2406767
theorem B2890721 : Blo 1603000 2890721 := bstep (se 2 (by rfl) ⟨1084020, by rfl⟩ : syracuseStep 2890721 = 2168041) B2168041
theorem B2407403 : Blo 1603000 2407403 := bstep (se 1 (by rfl) ⟨1805552, by rfl⟩ : syracuseStep 2407403 = 3611105) B3611105
theorem B1604655 : Blo 1603000 1604655 := bstep (se 1 (by rfl) ⟨1203491, by rfl⟩ : syracuseStep 1604655 = 2406983) B2406983
theorem B1604679 : Blo 1603000 1604679 := bstep (se 1 (by rfl) ⟨1203509, by rfl⟩ : syracuseStep 1604679 = 2407019) B2407019
theorem B1604831 : Blo 1603000 1604831 := bstep (se 1 (by rfl) ⟨1203623, by rfl⟩ : syracuseStep 1604831 = 2407247) B2407247
theorem B13696361 : Blo 1603000 13696361 := bstep (se 2 (by rfl) ⟨5136135, by rfl⟩ : syracuseStep 13696361 = 10272271) B10272271
theorem B5414255 : Blo 1603000 5414255 := bstep (se 1 (by rfl) ⟨4060691, by rfl⟩ : syracuseStep 5414255 = 8121383) B8121383
theorem B4062575 : Blo 1603000 4062575 := bstep (se 1 (by rfl) ⟨3046931, by rfl⟩ : syracuseStep 4062575 = 6093863) B6093863
theorem B2285119 : Blo 1603000 2285119 := bstep (se 1 (by rfl) ⟨1713839, by rfl⟩ : syracuseStep 2285119 = 3427679) B3427679
theorem B5414633 : Blo 1603000 5414633 := bstep (se 2 (by rfl) ⟨2030487, by rfl⟩ : syracuseStep 5414633 = 4060975) B4060975
theorem B8118467 : Blo 1603000 8118467 := bstep (se 1 (by rfl) ⟨6088850, by rfl⟩ : syracuseStep 8118467 = 12177701) B12177701
theorem B5415119 : Blo 1603000 5415119 := bstep (se 1 (by rfl) ⟨4061339, by rfl⟩ : syracuseStep 5415119 = 8122679) B8122679
theorem B30818657 : Blo 1603000 30818657 := bstep (se 2 (by rfl) ⟨11556996, by rfl⟩ : syracuseStep 30818657 = 23113993) B23113993
theorem B216760981 : Blo 1603000 216760981 := bstep (se 6 (by rfl) ⟨5080335, by rfl⟩ : syracuseStep 216760981 = 10160671) B10160671
theorem B5415983 : Blo 1603000 5415983 := bstep (se 1 (by rfl) ⟨4061987, by rfl⟩ : syracuseStep 5415983 = 8123975) B8123975
theorem B1803487 : Blo 1603000 1803487 := bstep (se 1 (by rfl) ⟨1352615, by rfl⟩ : syracuseStep 1803487 = 2705231) B2705231
theorem B12174785 : Blo 1603000 12174785 := bstep (se 2 (by rfl) ⟨4565544, by rfl⟩ : syracuseStep 12174785 = 9131089) B9131089
theorem B12183047 : Blo 1603000 12183047 := bstep (se 1 (by rfl) ⟨9137285, by rfl⟩ : syracuseStep 12183047 = 18274571) B18274571
theorem B6850079 : Blo 1603000 6850079 := bstep (se 1 (by rfl) ⟨5137559, by rfl⟩ : syracuseStep 6850079 = 10275119) B10275119
theorem B6850129 : Blo 1603000 6850129 := bstep (se 2 (by rfl) ⟨2568798, by rfl⟩ : syracuseStep 6850129 = 5137597) B5137597
theorem B11560573 : Blo 1603000 11560573 := bstep (se 3 (by rfl) ⟨2167607, by rfl⟩ : syracuseStep 11560573 = 4335215) B4335215
theorem B5416631 : Blo 1603000 5416631 := bstep (se 1 (by rfl) ⟨4062473, by rfl⟩ : syracuseStep 5416631 = 8124947) B8124947
theorem B12339175 : Blo 1603000 12339175 := bstep (se 1 (by rfl) ⟨9254381, by rfl⟩ : syracuseStep 12339175 = 18508763) B18508763
theorem B1927147 : Blo 1603000 1927147 := bstep (se 1 (by rfl) ⟨1445360, by rfl⟩ : syracuseStep 1927147 = 2890721) B2890721
theorem B1804315 : Blo 1603000 1804315 := bstep (se 1 (by rfl) ⟨1353236, by rfl⟩ : syracuseStep 1804315 = 2706473) B2706473
theorem B87836723 : Blo 1603000 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B3856091 : Blo 1603000 3856091 := bstep (se 1 (by rfl) ⟨2892068, by rfl⟩ : syracuseStep 3856091 = 5784137) B5784137
theorem B3606911 : Blo 1603000 3606911 := bstep (se 1 (by rfl) ⟨2705183, by rfl⟩ : syracuseStep 3606911 = 5410367) B5410367
theorem B2705791 : Blo 1603000 2705791 := bstep (se 1 (by rfl) ⟨2029343, by rfl⟩ : syracuseStep 2705791 = 4058687) B4058687
theorem B56347325 : Blo 1603000 56347325 := bstep (se 3 (by rfl) ⟨10565123, by rfl⟩ : syracuseStep 56347325 = 21130247) B21130247
theorem B3610331 : Blo 1603000 3610331 := bstep (se 1 (by rfl) ⟨2707748, by rfl⟩ : syracuseStep 3610331 = 5415497) B5415497
theorem B3607379 : Blo 1603000 3607379 := bstep (se 1 (by rfl) ⟨2705534, by rfl⟩ : syracuseStep 3607379 = 5411069) B5411069
theorem B17828801 : Blo 1603000 17828801 := bstep (se 2 (by rfl) ⟨6685800, by rfl⟩ : syracuseStep 17828801 = 13371601) B13371601
theorem B11725897 : Blo 1603000 11725897 := bstep (se 2 (by rfl) ⟨4397211, by rfl⟩ : syracuseStep 11725897 = 8794423) B8794423
theorem B8457337 : Blo 1603000 8457337 := bstep (se 2 (by rfl) ⟨3171501, by rfl⟩ : syracuseStep 8457337 = 6343003) B6343003
theorem B3853487 : Blo 1603000 3853487 := bstep (se 1 (by rfl) ⟨2890115, by rfl⟩ : syracuseStep 3853487 = 5780231) B5780231
theorem B3607739 : Blo 1603000 3607739 := bstep (se 1 (by rfl) ⟨2705804, by rfl⟩ : syracuseStep 3607739 = 5411609) B5411609
theorem B3607919 : Blo 1603000 3607919 := bstep (se 1 (by rfl) ⟨2705939, by rfl⟩ : syracuseStep 3607919 = 5411879) B5411879
theorem B6090173 : Blo 1603000 6090173 := bstep (se 3 (by rfl) ⟨1141907, by rfl⟩ : syracuseStep 6090173 = 2283815) B2283815
theorem B4943315 : Blo 1603000 4943315 := bstep (se 1 (by rfl) ⟨3707486, by rfl⟩ : syracuseStep 4943315 = 7414973) B7414973
theorem B2567863 : Blo 1603000 2567863 := bstep (se 1 (by rfl) ⟨1925897, by rfl⟩ : syracuseStep 2567863 = 3851795) B3851795
theorem B4058849 : Blo 1603000 4058849 := bstep (se 2 (by rfl) ⟨1522068, by rfl⟩ : syracuseStep 4058849 = 3044137) B3044137
theorem B4566775 : Blo 1603000 4566775 := bstep (se 1 (by rfl) ⟨3425081, by rfl⟩ : syracuseStep 4566775 = 6850163) B6850163
theorem B6090491 : Blo 1603000 6090491 := bstep (se 1 (by rfl) ⟨4567868, by rfl⟩ : syracuseStep 6090491 = 9135737) B9135737
theorem B10276631 : Blo 1603000 10276631 := bstep (se 1 (by rfl) ⟨7707473, by rfl⟩ : syracuseStep 10276631 = 15414947) B15414947
theorem B8122193 : Blo 1603000 8122193 := bstep (se 2 (by rfl) ⟨3045822, by rfl⟩ : syracuseStep 8122193 = 6091645) B6091645
theorem B5410799 : Blo 1603000 5410799 := bstep (se 1 (by rfl) ⟨4058099, by rfl⟩ : syracuseStep 5410799 = 8116199) B8116199
theorem B11554811 : Blo 1603000 11554811 := bstep (se 1 (by rfl) ⟨8666108, by rfl⟩ : syracuseStep 11554811 = 17332217) B17332217
theorem B3608639 : Blo 1603000 3608639 := bstep (se 1 (by rfl) ⟨2706479, by rfl⟩ : syracuseStep 3608639 = 5412959) B5412959
theorem B2707519 : Blo 1603000 2707519 := bstep (se 1 (by rfl) ⟨2030639, by rfl⟩ : syracuseStep 2707519 = 4061279) B4061279
theorem B52048003 : Blo 1603000 52048003 := bstep (se 1 (by rfl) ⟨39036002, by rfl⟩ : syracuseStep 52048003 = 78072005) B78072005
theorem B19509443 : Blo 1603000 19509443 := bstep (se 1 (by rfl) ⟨14632082, by rfl⟩ : syracuseStep 19509443 = 29264165) B29264165
theorem B3608873 : Blo 1603000 3608873 := bstep (se 2 (by rfl) ⟨1353327, by rfl⟩ : syracuseStep 3608873 = 2706655) B2706655
theorem B2404763 : Blo 1603000 2404763 := bstep (se 1 (by rfl) ⟨1803572, by rfl⟩ : syracuseStep 2404763 = 3607145) B3607145
theorem B3609143 : Blo 1603000 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B27398735 : Blo 1603000 27398735 := bstep (se 1 (by rfl) ⟨20549051, by rfl⟩ : syracuseStep 27398735 = 41098103) B41098103
theorem B8123003 : Blo 1603000 8123003 := bstep (se 1 (by rfl) ⟨6092252, by rfl⟩ : syracuseStep 8123003 = 12184505) B12184505
theorem B2405183 : Blo 1603000 2405183 := bstep (se 1 (by rfl) ⟨1803887, by rfl⟩ : syracuseStep 2405183 = 3607775) B3607775
theorem B3609449 : Blo 1603000 3609449 := bstep (se 2 (by rfl) ⟨1353543, by rfl⟩ : syracuseStep 3609449 = 2707087) B2707087
theorem B9130907 : Blo 1603000 9130907 := bstep (se 1 (by rfl) ⟨6848180, by rfl⟩ : syracuseStep 9130907 = 13696361) B13696361
theorem B3609503 : Blo 1603000 3609503 := bstep (se 1 (by rfl) ⟨2707127, by rfl⟩ : syracuseStep 3609503 = 5414255) B5414255
theorem B2708383 : Blo 1603000 2708383 := bstep (se 1 (by rfl) ⟨2031287, by rfl⟩ : syracuseStep 2708383 = 4062575) B4062575
theorem B2405327 : Blo 1603000 2405327 := bstep (se 1 (by rfl) ⟨1803995, by rfl⟩ : syracuseStep 2405327 = 3607991) B3607991
theorem B2405369 : Blo 1603000 2405369 := bstep (se 2 (by rfl) ⟨902013, by rfl⟩ : syracuseStep 2405369 = 1804027) B1804027
theorem B2929657 : Blo 1603000 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B83325953 : Blo 1603000 83325953 := bstep (se 2 (by rfl) ⟨31247232, by rfl⟩ : syracuseStep 83325953 = 62494465) B62494465
theorem B2405417 : Blo 1603000 2405417 := bstep (se 2 (by rfl) ⟨902031, by rfl⟩ : syracuseStep 2405417 = 1804063) B1804063
theorem B2405447 : Blo 1603000 2405447 := bstep (se 1 (by rfl) ⟨1804085, by rfl⟩ : syracuseStep 2405447 = 3608171) B3608171
theorem B3609755 : Blo 1603000 3609755 := bstep (se 1 (by rfl) ⟨2707316, by rfl⟩ : syracuseStep 3609755 = 5414633) B5414633
theorem B2405627 : Blo 1603000 2405627 := bstep (se 1 (by rfl) ⟨1804220, by rfl⟩ : syracuseStep 2405627 = 3608441) B3608441
theorem B2782459 : Blo 1603000 2782459 := bstep (se 1 (by rfl) ⟨2086844, by rfl⟩ : syracuseStep 2782459 = 4173689) B4173689
theorem B8123651 : Blo 1603000 8123651 := bstep (se 1 (by rfl) ⟨6092738, by rfl⟩ : syracuseStep 8123651 = 12185477) B12185477
theorem B4568393 : Blo 1603000 4568393 := bstep (se 2 (by rfl) ⟨1713147, by rfl⟩ : syracuseStep 4568393 = 3426295) B3426295
theorem B19764569 : Blo 1603000 19764569 := bstep (se 2 (by rfl) ⟨7411713, by rfl⟩ : syracuseStep 19764569 = 14823427) B14823427
theorem B20559257 : Blo 1603000 20559257 := bstep (se 2 (by rfl) ⟨7709721, by rfl⟩ : syracuseStep 20559257 = 15419443) B15419443
theorem B9893335 : Blo 1603000 9893335 := bstep (se 1 (by rfl) ⟨7420001, by rfl⟩ : syracuseStep 9893335 = 14840003) B14840003
theorem B1603047 : Blo 1603000 1603047 := bstep (se 1 (by rfl) ⟨1202285, by rfl⟩ : syracuseStep 1603047 = 2404571) B2404571
theorem B1603055 : Blo 1603000 1603055 := bstep (se 1 (by rfl) ⟨1202291, by rfl⟩ : syracuseStep 1603055 = 2404583) B2404583
theorem B1603163 : Blo 1603000 1603163 := bstep (se 1 (by rfl) ⟨1202372, by rfl⟩ : syracuseStep 1603163 = 2404745) B2404745
theorem B4060763 : Blo 1603000 4060763 := bstep (se 1 (by rfl) ⟨3045572, by rfl⟩ : syracuseStep 4060763 = 6091145) B6091145
theorem B1603227 : Blo 1603000 1603227 := bstep (se 1 (by rfl) ⟨1202420, by rfl⟩ : syracuseStep 1603227 = 2404841) B2404841
theorem B1603311 : Blo 1603000 1603311 := bstep (se 1 (by rfl) ⟨1202483, by rfl⟩ : syracuseStep 1603311 = 2404967) B2404967
theorem B1603399 : Blo 1603000 1603399 := bstep (se 1 (by rfl) ⟨1202549, by rfl⟩ : syracuseStep 1603399 = 2405099) B2405099
theorem B3610439 : Blo 1603000 3610439 := bstep (se 1 (by rfl) ⟨2707829, by rfl⟩ : syracuseStep 3610439 = 5415659) B5415659
theorem B1603419 : Blo 1603000 1603419 := bstep (se 1 (by rfl) ⟨1202564, by rfl⟩ : syracuseStep 1603419 = 2405129) B2405129
theorem B6854537 : Blo 1603000 6854537 := bstep (se 2 (by rfl) ⟨2570451, by rfl⟩ : syracuseStep 6854537 = 5140903) B5140903
theorem B1603487 : Blo 1603000 1603487 := bstep (se 1 (by rfl) ⟨1202615, by rfl⟩ : syracuseStep 1603487 = 2405231) B2405231
theorem B11556827 : Blo 1603000 11556827 := bstep (se 1 (by rfl) ⟨8667620, by rfl⟩ : syracuseStep 11556827 = 17335241) B17335241
theorem B1603655 : Blo 1603000 1603655 := bstep (se 1 (by rfl) ⟨1202741, by rfl⟩ : syracuseStep 1603655 = 2405483) B2405483
theorem B2029799 : Blo 1603000 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B1603815 : Blo 1603000 1603815 := bstep (se 1 (by rfl) ⟨1202861, by rfl⟩ : syracuseStep 1603815 = 2405723) B2405723
theorem B3250463 : Blo 1603000 3250463 := bstep (se 1 (by rfl) ⟨2437847, by rfl⟩ : syracuseStep 3250463 = 4875695) B4875695
theorem B3045671 : Blo 1603000 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B6093103 : Blo 1603000 6093103 := bstep (se 1 (by rfl) ⟨4569827, by rfl⟩ : syracuseStep 6093103 = 9139655) B9139655
theorem B1603999 : Blo 1603000 1603999 := bstep (se 1 (by rfl) ⟨1202999, by rfl⟩ : syracuseStep 1603999 = 2405999) B2405999
theorem B5781959 : Blo 1603000 5781959 := bstep (se 1 (by rfl) ⟨4336469, by rfl⟩ : syracuseStep 5781959 = 8672939) B8672939
theorem B1604047 : Blo 1603000 1604047 := bstep (se 1 (by rfl) ⟨1203035, by rfl⟩ : syracuseStep 1604047 = 2406071) B2406071
theorem B2406863 : Blo 1603000 2406863 := bstep (se 1 (by rfl) ⟨1805147, by rfl⟩ : syracuseStep 2406863 = 3610295) B3610295
theorem B1604071 : Blo 1603000 1604071 := bstep (se 1 (by rfl) ⟨1203053, by rfl⟩ : syracuseStep 1604071 = 2406107) B2406107
theorem B9755113 : Blo 1603000 9755113 := bstep (se 2 (by rfl) ⟨3658167, by rfl⟩ : syracuseStep 9755113 = 7316335) B7316335
theorem B2406953 : Blo 1603000 2406953 := bstep (se 2 (by rfl) ⟨902607, by rfl⟩ : syracuseStep 2406953 = 1805215) B1805215
theorem B1604187 : Blo 1603000 1604187 := bstep (se 1 (by rfl) ⟨1203140, by rfl⟩ : syracuseStep 1604187 = 2406281) B2406281
theorem B1604255 : Blo 1603000 1604255 := bstep (se 1 (by rfl) ⟨1203191, by rfl⟩ : syracuseStep 1604255 = 2406383) B2406383
theorem B2472607 : Blo 1603000 2472607 := bstep (se 1 (by rfl) ⟨1854455, by rfl⟩ : syracuseStep 2472607 = 3708911) B3708911
theorem B2407145 : Blo 1603000 2407145 := bstep (se 2 (by rfl) ⟨902679, by rfl⟩ : syracuseStep 2407145 = 1805359) B1805359
theorem B1604423 : Blo 1603000 1604423 := bstep (se 1 (by rfl) ⟨1203317, by rfl⟩ : syracuseStep 1604423 = 2406635) B2406635
theorem B8125271 : Blo 1603000 8125271 := bstep (se 1 (by rfl) ⟨6093953, by rfl⟩ : syracuseStep 8125271 = 12187907) B12187907
theorem B1604463 : Blo 1603000 1604463 := bstep (se 1 (by rfl) ⟨1203347, by rfl⟩ : syracuseStep 1604463 = 2406695) B2406695
theorem B2030503 : Blo 1603000 2030503 := bstep (se 1 (by rfl) ⟨1522877, by rfl⟩ : syracuseStep 2030503 = 3045755) B3045755
theorem B1604519 : Blo 1603000 1604519 := bstep (se 1 (by rfl) ⟨1203389, by rfl⟩ : syracuseStep 1604519 = 2406779) B2406779
theorem B1604699 : Blo 1603000 1604699 := bstep (se 1 (by rfl) ⟨1203524, by rfl⟩ : syracuseStep 1604699 = 2407049) B2407049
theorem B1604815 : Blo 1603000 1604815 := bstep (se 1 (by rfl) ⟨1203611, by rfl⟩ : syracuseStep 1604815 = 2407223) B2407223
theorem B6847703 : Blo 1603000 6847703 := bstep (se 1 (by rfl) ⟨5135777, by rfl⟩ : syracuseStep 6847703 = 10271555) B10271555
theorem B1604839 : Blo 1603000 1604839 := bstep (se 1 (by rfl) ⟨1203629, by rfl⟩ : syracuseStep 1604839 = 2407259) B2407259
theorem B7314731 : Blo 1603000 7314731 := bstep (se 1 (by rfl) ⟨5486048, by rfl⟩ : syracuseStep 7314731 = 10972097) B10972097
theorem B1604935 : Blo 1603000 1604935 := bstep (se 1 (by rfl) ⟨1203701, by rfl⟩ : syracuseStep 1604935 = 2407403) B2407403
theorem B3046825 : Blo 1603000 3046825 := bstep (se 2 (by rfl) ⟨1142559, by rfl⟩ : syracuseStep 3046825 = 2285119) B2285119
theorem B39026285 : Blo 1603000 39026285 := bstep (se 3 (by rfl) ⟨7317428, by rfl⟩ : syracuseStep 39026285 = 14634857) B14634857
theorem B2891551 : Blo 1603000 2891551 := bstep (se 1 (by rfl) ⟨2168663, by rfl⟩ : syracuseStep 2891551 = 4337327) B4337327
theorem B5414903 : Blo 1603000 5414903 := bstep (se 1 (by rfl) ⟨4061177, by rfl⟩ : syracuseStep 5414903 = 8122355) B8122355
theorem B20545771 : Blo 1603000 20545771 := bstep (se 1 (by rfl) ⟨15409328, by rfl⟩ : syracuseStep 20545771 = 30818657) B30818657
theorem B5415335 : Blo 1603000 5415335 := bstep (se 1 (by rfl) ⟨4061501, by rfl⟩ : syracuseStep 5415335 = 8123003) B8123003
theorem B6087271 : Blo 1603000 6087271 := bstep (se 1 (by rfl) ⟨4565453, by rfl⟩ : syracuseStep 6087271 = 9130907) B9130907
theorem B45105797 : Blo 1603000 45105797 := bstep (se 4 (by rfl) ⟨4228668, by rfl⟩ : syracuseStep 45105797 = 8457337) B8457337
theorem B8667901 : Blo 1603000 8667901 := bstep (se 3 (by rfl) ⟨1625231, by rfl⟩ : syracuseStep 8667901 = 3250463) B3250463
theorem B5415767 : Blo 1603000 5415767 := bstep (se 1 (by rfl) ⟨4061825, by rfl⟩ : syracuseStep 5415767 = 8123651) B8123651
theorem B289014641 : Blo 1603000 289014641 := bstep (se 2 (by rfl) ⟨108380490, by rfl⟩ : syracuseStep 289014641 = 216760981) B216760981
theorem B13706171 : Blo 1603000 13706171 := bstep (se 1 (by rfl) ⟨10279628, by rfl⟩ : syracuseStep 13706171 = 20559257) B20559257
theorem B13182173 : Blo 1603000 13182173 := bstep (se 3 (by rfl) ⟨2471657, by rfl⟩ : syracuseStep 13182173 = 4943315) B4943315
theorem B58557815 : Blo 1603000 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B5416847 : Blo 1603000 5416847 := bstep (se 1 (by rfl) ⟨4062635, by rfl⟩ : syracuseStep 5416847 = 8125271) B8125271
theorem B10282909 : Blo 1603000 10282909 := bstep (se 3 (by rfl) ⟨1928045, by rfl⟩ : syracuseStep 10282909 = 3856091) B3856091
theorem B13191113 : Blo 1603000 13191113 := bstep (se 2 (by rfl) ⟨4946667, by rfl⟩ : syracuseStep 13191113 = 9893335) B9893335
theorem B4565135 : Blo 1603000 4565135 := bstep (se 1 (by rfl) ⟨3423851, by rfl⟩ : syracuseStep 4565135 = 6847703) B6847703
theorem B4876487 : Blo 1603000 4876487 := bstep (se 1 (by rfl) ⟨3657365, by rfl⟩ : syracuseStep 4876487 = 7314731) B7314731
theorem B6089033 : Blo 1603000 6089033 := bstep (se 2 (by rfl) ⟨2283387, by rfl⟩ : syracuseStep 6089033 = 4566775) B4566775
theorem B2705899 : Blo 1603000 2705899 := bstep (se 1 (by rfl) ⟨2029424, by rfl⟩ : syracuseStep 2705899 = 4058849) B4058849
theorem B6851087 : Blo 1603000 6851087 := bstep (se 1 (by rfl) ⟨5138315, by rfl⟩ : syracuseStep 6851087 = 10276631) B10276631
theorem B16452233 : Blo 1603000 16452233 := bstep (se 2 (by rfl) ⟨6169587, by rfl⟩ : syracuseStep 16452233 = 12339175) B12339175
theorem B3607199 : Blo 1603000 3607199 := bstep (se 1 (by rfl) ⟨2705399, by rfl⟩ : syracuseStep 3607199 = 5410799) B5410799
theorem B7703207 : Blo 1603000 7703207 := bstep (se 1 (by rfl) ⟨5777405, by rfl⟩ : syracuseStep 7703207 = 11554811) B11554811
theorem B222202541 : Blo 1603000 222202541 := bstep (se 3 (by rfl) ⟨41662976, by rfl⟩ : syracuseStep 222202541 = 83325953) B83325953
theorem B69397337 : Blo 1603000 69397337 := bstep (se 2 (by rfl) ⟨26024001, by rfl⟩ : syracuseStep 69397337 = 52048003) B52048003
theorem B3607721 : Blo 1603000 3607721 := bstep (se 2 (by rfl) ⟨1352895, by rfl⟩ : syracuseStep 3607721 = 2705791) B2705791
theorem B3296809 : Blo 1603000 3296809 := bstep (se 2 (by rfl) ⟨1236303, by rfl⟩ : syracuseStep 3296809 = 2472607) B2472607
theorem B13176379 : Blo 1603000 13176379 := bstep (se 1 (by rfl) ⟨9882284, by rfl⟩ : syracuseStep 13176379 = 19764569) B19764569
theorem B8122031 : Blo 1603000 8122031 := bstep (se 1 (by rfl) ⟨6091523, by rfl⟩ : syracuseStep 8122031 = 12183047) B12183047
theorem B4566719 : Blo 1603000 4566719 := bstep (se 1 (by rfl) ⟨3425039, by rfl⟩ : syracuseStep 4566719 = 6850079) B6850079
theorem B2707175 : Blo 1603000 2707175 := bstep (se 1 (by rfl) ⟨2030381, by rfl⟩ : syracuseStep 2707175 = 4060763) B4060763
theorem B2707337 : Blo 1603000 2707337 := bstep (se 2 (by rfl) ⟨1015251, by rfl⟩ : syracuseStep 2707337 = 2030503) B2030503
theorem B14839781 : Blo 1603000 14839781 := bstep (se 4 (by rfl) ⟨1391229, by rfl⟩ : syracuseStep 14839781 = 2782459) B2782459
theorem B7704551 : Blo 1603000 7704551 := bstep (se 1 (by rfl) ⟨5778413, by rfl⟩ : syracuseStep 7704551 = 11556827) B11556827
theorem B15634529 : Blo 1603000 15634529 := bstep (se 2 (by rfl) ⟨5862948, by rfl⟩ : syracuseStep 15634529 = 11725897) B11725897
theorem B2404607 : Blo 1603000 2404607 := bstep (se 1 (by rfl) ⟨1803455, by rfl⟩ : syracuseStep 2404607 = 3606911) B3606911
theorem B2404649 : Blo 1603000 2404649 := bstep (se 2 (by rfl) ⟨901743, by rfl⟩ : syracuseStep 2404649 = 1803487) B1803487
theorem B3854639 : Blo 1603000 3854639 := bstep (se 1 (by rfl) ⟨2890979, by rfl⟩ : syracuseStep 3854639 = 5781959) B5781959
theorem B37564883 : Blo 1603000 37564883 := bstep (se 1 (by rfl) ⟨28173662, by rfl⟩ : syracuseStep 37564883 = 56347325) B56347325
theorem B2404919 : Blo 1603000 2404919 := bstep (se 1 (by rfl) ⟨1803689, by rfl⟩ : syracuseStep 2404919 = 3607379) B3607379
theorem B2568991 : Blo 1603000 2568991 := bstep (se 1 (by rfl) ⟨1926743, by rfl⟩ : syracuseStep 2568991 = 3853487) B3853487
theorem B2405159 : Blo 1603000 2405159 := bstep (se 1 (by rfl) ⟨1803869, by rfl⟩ : syracuseStep 2405159 = 3607739) B3607739
theorem B15414097 : Blo 1603000 15414097 := bstep (se 2 (by rfl) ⟨5780286, by rfl⟩ : syracuseStep 15414097 = 11560573) B11560573
theorem B2405279 : Blo 1603000 2405279 := bstep (se 1 (by rfl) ⟨1803959, by rfl⟩ : syracuseStep 2405279 = 3607919) B3607919
theorem B4060115 : Blo 1603000 4060115 := bstep (se 1 (by rfl) ⟨3045086, by rfl⟩ : syracuseStep 4060115 = 6090173) B6090173
theorem B3855401 : Blo 1603000 3855401 := bstep (se 2 (by rfl) ⟨1445775, by rfl⟩ : syracuseStep 3855401 = 2891551) B2891551
theorem B4060327 : Blo 1603000 4060327 := bstep (se 1 (by rfl) ⟨3045245, by rfl⟩ : syracuseStep 4060327 = 6090491) B6090491
theorem B2569529 : Blo 1603000 2569529 := bstep (se 2 (by rfl) ⟨963573, by rfl⟩ : syracuseStep 2569529 = 1927147) B1927147
theorem B3609935 : Blo 1603000 3609935 := bstep (se 1 (by rfl) ⟨2707451, by rfl⟩ : syracuseStep 3609935 = 5414903) B5414903
theorem B2405753 : Blo 1603000 2405753 := bstep (se 2 (by rfl) ⟨902157, by rfl⟩ : syracuseStep 2405753 = 1804315) B1804315
theorem B2405759 : Blo 1603000 2405759 := bstep (se 1 (by rfl) ⟨1804319, by rfl⟩ : syracuseStep 2405759 = 3608639) B3608639
theorem B3610025 : Blo 1603000 3610025 := bstep (se 2 (by rfl) ⟨1353759, by rfl⟩ : syracuseStep 3610025 = 2707519) B2707519
theorem B5412311 : Blo 1603000 5412311 := bstep (se 1 (by rfl) ⟨4059233, by rfl⟩ : syracuseStep 5412311 = 8118467) B8118467
theorem B13006295 : Blo 1603000 13006295 := bstep (se 1 (by rfl) ⟨9754721, by rfl⟩ : syracuseStep 13006295 = 19509443) B19509443
theorem B3610079 : Blo 1603000 3610079 := bstep (se 1 (by rfl) ⟨2707559, by rfl⟩ : syracuseStep 3610079 = 5415119) B5415119
theorem B2405915 : Blo 1603000 2405915 := bstep (se 1 (by rfl) ⟨1804436, by rfl⟩ : syracuseStep 2405915 = 3608873) B3608873
theorem B1603175 : Blo 1603000 1603175 := bstep (se 1 (by rfl) ⟨1202381, by rfl⟩ : syracuseStep 1603175 = 2404763) B2404763
theorem B2406095 : Blo 1603000 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B18265823 : Blo 1603000 18265823 := bstep (se 1 (by rfl) ⟨13699367, by rfl⟩ : syracuseStep 18265823 = 27398735) B27398735
theorem B8124137 : Blo 1603000 8124137 := bstep (se 2 (by rfl) ⟨3046551, by rfl⟩ : syracuseStep 8124137 = 6093103) B6093103
theorem B1603455 : Blo 1603000 1603455 := bstep (se 1 (by rfl) ⟨1202591, by rfl⟩ : syracuseStep 1603455 = 2405183) B2405183
theorem B2406299 : Blo 1603000 2406299 := bstep (se 1 (by rfl) ⟨1804724, by rfl⟩ : syracuseStep 2406299 = 3609449) B3609449
theorem B5412797 : Blo 1603000 5412797 := bstep (se 3 (by rfl) ⟨1014899, by rfl⟩ : syracuseStep 5412797 = 2029799) B2029799
theorem B2406335 : Blo 1603000 2406335 := bstep (se 1 (by rfl) ⟨1804751, by rfl⟩ : syracuseStep 2406335 = 3609503) B3609503
theorem B1603551 : Blo 1603000 1603551 := bstep (se 1 (by rfl) ⟨1202663, by rfl⟩ : syracuseStep 1603551 = 2405327) B2405327
theorem B13006817 : Blo 1603000 13006817 := bstep (se 2 (by rfl) ⟨4877556, by rfl⟩ : syracuseStep 13006817 = 9755113) B9755113
theorem B1603579 : Blo 1603000 1603579 := bstep (se 1 (by rfl) ⟨1202684, by rfl⟩ : syracuseStep 1603579 = 2405369) B2405369
theorem B1603611 : Blo 1603000 1603611 := bstep (se 1 (by rfl) ⟨1202708, by rfl⟩ : syracuseStep 1603611 = 2405417) B2405417
theorem B3610655 : Blo 1603000 3610655 := bstep (se 1 (by rfl) ⟨2707991, by rfl⟩ : syracuseStep 3610655 = 5415983) B5415983
theorem B1603631 : Blo 1603000 1603631 := bstep (se 1 (by rfl) ⟨1202723, by rfl⟩ : syracuseStep 1603631 = 2405447) B2405447
theorem B2406503 : Blo 1603000 2406503 := bstep (se 1 (by rfl) ⟨1804877, by rfl⟩ : syracuseStep 2406503 = 3609755) B3609755
theorem B1603751 : Blo 1603000 1603751 := bstep (se 1 (by rfl) ⟨1202813, by rfl⟩ : syracuseStep 1603751 = 2405627) B2405627
theorem B3045595 : Blo 1603000 3045595 := bstep (se 1 (by rfl) ⟨2284196, by rfl⟩ : syracuseStep 3045595 = 4568393) B4568393
theorem B8116523 : Blo 1603000 8116523 := bstep (se 1 (by rfl) ⟨6087392, by rfl⟩ : syracuseStep 8116523 = 12174785) B12174785
theorem B3611087 : Blo 1603000 3611087 := bstep (se 1 (by rfl) ⟨2708315, by rfl⟩ : syracuseStep 3611087 = 5416631) B5416631
theorem B2406887 : Blo 1603000 2406887 := bstep (se 1 (by rfl) ⟨1805165, by rfl⟩ : syracuseStep 2406887 = 3610331) B3610331
theorem B3611177 : Blo 1603000 3611177 := bstep (se 2 (by rfl) ⟨1354191, by rfl⟩ : syracuseStep 3611177 = 2708383) B2708383
theorem B2406959 : Blo 1603000 2406959 := bstep (se 1 (by rfl) ⟨1805219, by rfl⟩ : syracuseStep 2406959 = 3610439) B3610439
theorem B4569691 : Blo 1603000 4569691 := bstep (se 1 (by rfl) ⟨3427268, by rfl⟩ : syracuseStep 4569691 = 6854537) B6854537
theorem B3906209 : Blo 1603000 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B2030447 : Blo 1603000 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B1604575 : Blo 1603000 1604575 := bstep (se 1 (by rfl) ⟨1203431, by rfl⟩ : syracuseStep 1604575 = 2406863) B2406863
theorem B1604635 : Blo 1603000 1604635 := bstep (se 1 (by rfl) ⟨1203476, by rfl⟩ : syracuseStep 1604635 = 2406953) B2406953
theorem B1604763 : Blo 1603000 1604763 := bstep (se 1 (by rfl) ⟨1203572, by rfl⟩ : syracuseStep 1604763 = 2407145) B2407145
theorem B4062433 : Blo 1603000 4062433 := bstep (se 2 (by rfl) ⟨1523412, by rfl⟩ : syracuseStep 4062433 = 3046825) B3046825
theorem B11885867 : Blo 1603000 11885867 := bstep (se 1 (by rfl) ⟨8914400, by rfl⟩ : syracuseStep 11885867 = 17828801) B17828801
theorem B9133505 : Blo 1603000 9133505 := bstep (se 2 (by rfl) ⟨3425064, by rfl⟩ : syracuseStep 9133505 = 6850129) B6850129
theorem B3423817 : Blo 1603000 3423817 := bstep (se 2 (by rfl) ⟨1283931, by rfl⟩ : syracuseStep 3423817 = 2567863) B2567863
theorem B26017523 : Blo 1603000 26017523 := bstep (se 1 (by rfl) ⟨19513142, by rfl⟩ : syracuseStep 26017523 = 39026285) B39026285
theorem B5414795 : Blo 1603000 5414795 := bstep (se 1 (by rfl) ⟨4061096, by rfl⟩ : syracuseStep 5414795 = 8122193) B8122193
theorem B25043255 : Blo 1603000 25043255 := bstep (se 1 (by rfl) ⟨18782441, by rfl⟩ : syracuseStep 25043255 = 37564883) B37564883
theorem B27394361 : Blo 1603000 27394361 := bstep (se 2 (by rfl) ⟨10272885, by rfl⟩ : syracuseStep 27394361 = 20545771) B20545771
theorem B192676427 : Blo 1603000 192676427 := bstep (se 1 (by rfl) ⟨144507320, by rfl⟩ : syracuseStep 192676427 = 289014641) B289014641
theorem B3425321 : Blo 1603000 3425321 := bstep (se 2 (by rfl) ⟨1284495, by rfl⟩ : syracuseStep 3425321 = 2568991) B2568991
theorem B5416091 : Blo 1603000 5416091 := bstep (se 1 (by rfl) ⟨4062068, by rfl⟩ : syracuseStep 5416091 = 8124137) B8124137
theorem B46228805 : Blo 1603000 46228805 := bstep (se 4 (by rfl) ⟨4333950, by rfl⟩ : syracuseStep 46228805 = 8667901) B8667901
theorem B5416577 : Blo 1603000 5416577 := bstep (se 2 (by rfl) ⟨2031216, by rfl⟩ : syracuseStep 5416577 = 4062433) B4062433
theorem B4565089 : Blo 1603000 4565089 := bstep (se 2 (by rfl) ⟨1711908, by rfl⟩ : syracuseStep 4565089 = 3423817) B3423817
theorem B7923911 : Blo 1603000 7923911 := bstep (se 1 (by rfl) ⟨5942933, by rfl⟩ : syracuseStep 7923911 = 11885867) B11885867
theorem B6089003 : Blo 1603000 6089003 := bstep (se 1 (by rfl) ⟨4566752, by rfl⟩ : syracuseStep 6089003 = 9133505) B9133505
theorem B1804783 : Blo 1603000 1804783 := bstep (se 1 (by rfl) ⟨1353587, by rfl⟩ : syracuseStep 1804783 = 2707175) B2707175
theorem B17345015 : Blo 1603000 17345015 := bstep (se 1 (by rfl) ⟨13008761, by rfl⟩ : syracuseStep 17345015 = 26017523) B26017523
theorem B1804891 : Blo 1603000 1804891 := bstep (se 1 (by rfl) ⟨1353668, by rfl⟩ : syracuseStep 1804891 = 2707337) B2707337
theorem B10423019 : Blo 1603000 10423019 := bstep (se 1 (by rfl) ⟨7817264, by rfl⟩ : syracuseStep 10423019 = 15634529) B15634529
theorem B9137447 : Blo 1603000 9137447 := bstep (se 1 (by rfl) ⟨6853085, by rfl⟩ : syracuseStep 9137447 = 13706171) B13706171
theorem B2706743 : Blo 1603000 2706743 := bstep (se 1 (by rfl) ⟨2030057, by rfl⟩ : syracuseStep 2706743 = 4060115) B4060115
theorem B3607865 : Blo 1603000 3607865 := bstep (se 2 (by rfl) ⟨1352949, by rfl⟩ : syracuseStep 3607865 = 2705899) B2705899
theorem B6852077 : Blo 1603000 6852077 := bstep (se 3 (by rfl) ⟨1284764, by rfl⟩ : syracuseStep 6852077 = 2569529) B2569529
theorem B39038543 : Blo 1603000 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B3608207 : Blo 1603000 3608207 := bstep (se 1 (by rfl) ⟨2706155, by rfl⟩ : syracuseStep 3608207 = 5412311) B5412311
theorem B8670863 : Blo 1603000 8670863 := bstep (se 1 (by rfl) ⟨6503147, by rfl⟩ : syracuseStep 8670863 = 13006295) B13006295
theorem B12177215 : Blo 1603000 12177215 := bstep (se 1 (by rfl) ⟨9132911, by rfl⟩ : syracuseStep 12177215 = 18265823) B18265823
theorem B3608531 : Blo 1603000 3608531 := bstep (se 1 (by rfl) ⟨2706398, by rfl⟩ : syracuseStep 3608531 = 5412797) B5412797
theorem B8671211 : Blo 1603000 8671211 := bstep (se 1 (by rfl) ⟨6503408, by rfl⟩ : syracuseStep 8671211 = 13006817) B13006817
theorem B3043423 : Blo 1603000 3043423 := bstep (se 1 (by rfl) ⟨2282567, by rfl⟩ : syracuseStep 3043423 = 4565135) B4565135
theorem B5411015 : Blo 1603000 5411015 := bstep (se 1 (by rfl) ⟨4058261, by rfl⟩ : syracuseStep 5411015 = 8116523) B8116523
theorem B4059355 : Blo 1603000 4059355 := bstep (se 1 (by rfl) ⟨3044516, by rfl⟩ : syracuseStep 4059355 = 6089033) B6089033
theorem B4567391 : Blo 1603000 4567391 := bstep (se 1 (by rfl) ⟨3425543, by rfl⟩ : syracuseStep 4567391 = 6851087) B6851087
theorem B2404799 : Blo 1603000 2404799 := bstep (se 1 (by rfl) ⟨1803599, by rfl⟩ : syracuseStep 2404799 = 3607199) B3607199
theorem B592540109 : Blo 1603000 592540109 := bstep (se 3 (by rfl) ⟨111101270, by rfl⟩ : syracuseStep 592540109 = 222202541) B222202541
theorem B46264891 : Blo 1603000 46264891 := bstep (se 1 (by rfl) ⟨34698668, by rfl⟩ : syracuseStep 46264891 = 69397337) B69397337
theorem B4395745 : Blo 1603000 4395745 := bstep (se 2 (by rfl) ⟨1648404, by rfl⟩ : syracuseStep 4395745 = 3296809) B3296809
theorem B17568505 : Blo 1603000 17568505 := bstep (se 2 (by rfl) ⟨6588189, by rfl⟩ : syracuseStep 17568505 = 13176379) B13176379
theorem B2405147 : Blo 1603000 2405147 := bstep (se 1 (by rfl) ⟨1803860, by rfl⟩ : syracuseStep 2405147 = 3607721) B3607721
theorem B3044479 : Blo 1603000 3044479 := bstep (se 1 (by rfl) ⟨2283359, by rfl⟩ : syracuseStep 3044479 = 4566719) B4566719
theorem B13710545 : Blo 1603000 13710545 := bstep (se 2 (by rfl) ⟨5141454, by rfl⟩ : syracuseStep 13710545 = 10282909) B10282909
theorem B3609863 : Blo 1603000 3609863 := bstep (se 1 (by rfl) ⟨2707397, by rfl⟩ : syracuseStep 3609863 = 5414795) B5414795
theorem B39572749 : Blo 1603000 39572749 := bstep (se 3 (by rfl) ⟨7419890, by rfl⟩ : syracuseStep 39572749 = 14839781) B14839781
theorem B1603071 : Blo 1603000 1603071 := bstep (se 1 (by rfl) ⟨1202303, by rfl⟩ : syracuseStep 1603071 = 2404607) B2404607
theorem B1603099 : Blo 1603000 1603099 := bstep (se 1 (by rfl) ⟨1202324, by rfl⟩ : syracuseStep 1603099 = 2404649) B2404649
theorem B3610223 : Blo 1603000 3610223 := bstep (se 1 (by rfl) ⟨2707667, by rfl⟩ : syracuseStep 3610223 = 5415335) B5415335
theorem B4060793 : Blo 1603000 4060793 := bstep (se 2 (by rfl) ⟨1522797, by rfl⟩ : syracuseStep 4060793 = 3045595) B3045595
theorem B1603279 : Blo 1603000 1603279 := bstep (se 1 (by rfl) ⟨1202459, by rfl⟩ : syracuseStep 1603279 = 2404919) B2404919
theorem B30070531 : Blo 1603000 30070531 := bstep (se 1 (by rfl) ⟨22552898, by rfl⟩ : syracuseStep 30070531 = 45105797) B45105797
theorem B1603439 : Blo 1603000 1603439 := bstep (se 1 (by rfl) ⟨1202579, by rfl⟩ : syracuseStep 1603439 = 2405159) B2405159
theorem B3610511 : Blo 1603000 3610511 := bstep (se 1 (by rfl) ⟨2707883, by rfl⟩ : syracuseStep 3610511 = 5415767) B5415767
theorem B1603519 : Blo 1603000 1603519 := bstep (se 1 (by rfl) ⟨1202639, by rfl⟩ : syracuseStep 1603519 = 2405279) B2405279
theorem B2570267 : Blo 1603000 2570267 := bstep (se 1 (by rfl) ⟨1927700, by rfl⟩ : syracuseStep 2570267 = 3855401) B3855401
theorem B6092921 : Blo 1603000 6092921 := bstep (se 2 (by rfl) ⟨2284845, by rfl⟩ : syracuseStep 6092921 = 4569691) B4569691
theorem B10279037 : Blo 1603000 10279037 := bstep (se 3 (by rfl) ⟨1927319, by rfl⟩ : syracuseStep 10279037 = 3854639) B3854639
theorem B8116361 : Blo 1603000 8116361 := bstep (se 2 (by rfl) ⟨3043635, by rfl⟩ : syracuseStep 8116361 = 6087271) B6087271
theorem B8788115 : Blo 1603000 8788115 := bstep (se 1 (by rfl) ⟨6591086, by rfl⟩ : syracuseStep 8788115 = 13182173) B13182173
theorem B2406623 : Blo 1603000 2406623 := bstep (se 1 (by rfl) ⟨1804967, by rfl⟩ : syracuseStep 2406623 = 3609935) B3609935
theorem B1603835 : Blo 1603000 1603835 := bstep (se 1 (by rfl) ⟨1202876, by rfl⟩ : syracuseStep 1603835 = 2405753) B2405753
theorem B1603839 : Blo 1603000 1603839 := bstep (se 1 (by rfl) ⟨1202879, by rfl⟩ : syracuseStep 1603839 = 2405759) B2405759
theorem B2406683 : Blo 1603000 2406683 := bstep (se 1 (by rfl) ⟨1805012, by rfl⟩ : syracuseStep 2406683 = 3610025) B3610025
theorem B2406719 : Blo 1603000 2406719 := bstep (se 1 (by rfl) ⟨1805039, by rfl⟩ : syracuseStep 2406719 = 3610079) B3610079
theorem B1603943 : Blo 1603000 1603943 := bstep (se 1 (by rfl) ⟨1202957, by rfl⟩ : syracuseStep 1603943 = 2405915) B2405915
theorem B20552129 : Blo 1603000 20552129 := bstep (se 2 (by rfl) ⟨7707048, by rfl⟩ : syracuseStep 20552129 = 15414097) B15414097
theorem B1604063 : Blo 1603000 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B3611231 : Blo 1603000 3611231 := bstep (se 1 (by rfl) ⟨2708423, by rfl⟩ : syracuseStep 3611231 = 5416847) B5416847
theorem B1604199 : Blo 1603000 1604199 := bstep (se 1 (by rfl) ⟨1203149, by rfl⟩ : syracuseStep 1604199 = 2406299) B2406299
theorem B1604223 : Blo 1603000 1604223 := bstep (se 1 (by rfl) ⟨1203167, by rfl⟩ : syracuseStep 1604223 = 2406335) B2406335
theorem B2407103 : Blo 1603000 2407103 := bstep (se 1 (by rfl) ⟨1805327, by rfl⟩ : syracuseStep 2407103 = 3610655) B3610655
theorem B1604335 : Blo 1603000 1604335 := bstep (se 1 (by rfl) ⟨1203251, by rfl⟩ : syracuseStep 1604335 = 2406503) B2406503
theorem B3250991 : Blo 1603000 3250991 := bstep (se 1 (by rfl) ⟨2438243, by rfl⟩ : syracuseStep 3250991 = 4876487) B4876487
theorem B5413769 : Blo 1603000 5413769 := bstep (se 2 (by rfl) ⟨2030163, by rfl⟩ : syracuseStep 5413769 = 4060327) B4060327
theorem B2407391 : Blo 1603000 2407391 := bstep (se 1 (by rfl) ⟨1805543, by rfl⟩ : syracuseStep 2407391 = 3611087) B3611087
theorem B1604591 : Blo 1603000 1604591 := bstep (se 1 (by rfl) ⟨1203443, by rfl⟩ : syracuseStep 1604591 = 2406887) B2406887
theorem B2407451 : Blo 1603000 2407451 := bstep (se 1 (by rfl) ⟨1805588, by rfl⟩ : syracuseStep 2407451 = 3611177) B3611177
theorem B1604639 : Blo 1603000 1604639 := bstep (se 1 (by rfl) ⟨1203479, by rfl⟩ : syracuseStep 1604639 = 2406959) B2406959
theorem B10968155 : Blo 1603000 10968155 := bstep (se 1 (by rfl) ⟨8226116, by rfl⟩ : syracuseStep 10968155 = 16452233) B16452233
theorem B2604139 : Blo 1603000 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B5135471 : Blo 1603000 5135471 := bstep (se 1 (by rfl) ⟨3851603, by rfl⟩ : syracuseStep 5135471 = 7703207) B7703207
theorem B5414525 : Blo 1603000 5414525 := bstep (se 3 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 5414525 = 2030447) B2030447
theorem B5414687 : Blo 1603000 5414687 := bstep (se 1 (by rfl) ⟨4061015, by rfl⟩ : syracuseStep 5414687 = 8122031) B8122031
theorem B35176301 : Blo 1603000 35176301 := bstep (se 3 (by rfl) ⟨6595556, by rfl⟩ : syracuseStep 35176301 = 13191113) B13191113
theorem B5136367 : Blo 1603000 5136367 := bstep (se 1 (by rfl) ⟨3852275, by rfl⟩ : syracuseStep 5136367 = 7704551) B7704551
theorem B6086785 : Blo 1603000 6086785 := bstep (se 2 (by rfl) ⟨2282544, by rfl⟩ : syracuseStep 6086785 = 4565089) B4565089
theorem B16695503 : Blo 1603000 16695503 := bstep (se 1 (by rfl) ⟨12521627, by rfl⟩ : syracuseStep 16695503 = 25043255) B25043255
theorem B395026739 : Blo 1603000 395026739 := bstep (se 1 (by rfl) ⟨296270054, by rfl⟩ : syracuseStep 395026739 = 592540109) B592540109
theorem B128450951 : Blo 1603000 128450951 := bstep (se 1 (by rfl) ⟨96338213, by rfl⟩ : syracuseStep 128450951 = 192676427) B192676427
theorem B61686521 : Blo 1603000 61686521 := bstep (se 2 (by rfl) ⟨23132445, by rfl⟩ : syracuseStep 61686521 = 46264891) B46264891
theorem B30819203 : Blo 1603000 30819203 := bstep (se 1 (by rfl) ⟨23114402, by rfl⟩ : syracuseStep 30819203 = 46228805) B46228805
theorem B1713511 : Blo 1603000 1713511 := bstep (se 1 (by rfl) ⟨1285133, by rfl⟩ : syracuseStep 1713511 = 2570267) B2570267
theorem B5858743 : Blo 1603000 5858743 := bstep (se 1 (by rfl) ⟨4394057, by rfl⟩ : syracuseStep 5858743 = 8788115) B8788115
theorem B1804495 : Blo 1603000 1804495 := bstep (se 1 (by rfl) ⟨1353371, by rfl⟩ : syracuseStep 1804495 = 2706743) B2706743
theorem B40094041 : Blo 1603000 40094041 := bstep (se 2 (by rfl) ⟨15035265, by rfl⟩ : syracuseStep 40094041 = 30070531) B30070531
theorem B4057897 : Blo 1603000 4057897 := bstep (se 2 (by rfl) ⟨1521711, by rfl⟩ : syracuseStep 4057897 = 3043423) B3043423
theorem B3607343 : Blo 1603000 3607343 := bstep (se 1 (by rfl) ⟨2705507, by rfl⟩ : syracuseStep 3607343 = 5411015) B5411015
theorem B18262907 : Blo 1603000 18262907 := bstep (se 1 (by rfl) ⟨13697180, by rfl⟩ : syracuseStep 18262907 = 27394361) B27394361
theorem B21130429 : Blo 1603000 21130429 := bstep (se 3 (by rfl) ⟨3961955, by rfl⟩ : syracuseStep 21130429 = 7923911) B7923911
theorem B13888741 : Blo 1603000 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B5860993 : Blo 1603000 5860993 := bstep (se 2 (by rfl) ⟨2197872, by rfl⟩ : syracuseStep 5860993 = 4395745) B4395745
theorem B23424673 : Blo 1603000 23424673 := bstep (se 2 (by rfl) ⟨8784252, by rfl⟩ : syracuseStep 23424673 = 17568505) B17568505
theorem B2707195 : Blo 1603000 2707195 := bstep (se 1 (by rfl) ⟨2030396, by rfl⟩ : syracuseStep 2707195 = 4060793) B4060793
theorem B6852691 : Blo 1603000 6852691 := bstep (se 1 (by rfl) ⟨5139518, by rfl⟩ : syracuseStep 6852691 = 10279037) B10279037
theorem B5410907 : Blo 1603000 5410907 := bstep (se 1 (by rfl) ⟨4058180, by rfl⟩ : syracuseStep 5410907 = 8116361) B8116361
theorem B4059305 : Blo 1603000 4059305 := bstep (se 2 (by rfl) ⟨1522239, by rfl⟩ : syracuseStep 4059305 = 3044479) B3044479
theorem B4059335 : Blo 1603000 4059335 := bstep (se 1 (by rfl) ⟨3044501, by rfl⟩ : syracuseStep 4059335 = 6089003) B6089003
theorem B13701419 : Blo 1603000 13701419 := bstep (se 1 (by rfl) ⟨10276064, by rfl⟩ : syracuseStep 13701419 = 20552129) B20552129
theorem B11563343 : Blo 1603000 11563343 := bstep (se 1 (by rfl) ⟨8672507, by rfl⟩ : syracuseStep 11563343 = 17345015) B17345015
theorem B2167327 : Blo 1603000 2167327 := bstep (se 1 (by rfl) ⟨1625495, by rfl⟩ : syracuseStep 2167327 = 3250991) B3250991
theorem B3609179 : Blo 1603000 3609179 := bstep (se 1 (by rfl) ⟨2706884, by rfl⟩ : syracuseStep 3609179 = 5413769) B5413769
theorem B7312103 : Blo 1603000 7312103 := bstep (se 1 (by rfl) ⟨5484077, by rfl⟩ : syracuseStep 7312103 = 10968155) B10968155
theorem B6091631 : Blo 1603000 6091631 := bstep (se 1 (by rfl) ⟨4568723, by rfl⟩ : syracuseStep 6091631 = 9137447) B9137447
theorem B2405243 : Blo 1603000 2405243 := bstep (se 1 (by rfl) ⟨1803932, by rfl⟩ : syracuseStep 2405243 = 3607865) B3607865
theorem B4568051 : Blo 1603000 4568051 := bstep (se 1 (by rfl) ⟨3426038, by rfl⟩ : syracuseStep 4568051 = 6852077) B6852077
theorem B3609683 : Blo 1603000 3609683 := bstep (se 1 (by rfl) ⟨2707262, by rfl⟩ : syracuseStep 3609683 = 5414525) B5414525
theorem B2405471 : Blo 1603000 2405471 := bstep (se 1 (by rfl) ⟨1804103, by rfl⟩ : syracuseStep 2405471 = 3608207) B3608207
theorem B5780575 : Blo 1603000 5780575 := bstep (se 1 (by rfl) ⟨4335431, by rfl⟩ : syracuseStep 5780575 = 8670863) B8670863
theorem B3609791 : Blo 1603000 3609791 := bstep (se 1 (by rfl) ⟨2707343, by rfl⟩ : syracuseStep 3609791 = 5414687) B5414687
theorem B23450867 : Blo 1603000 23450867 := bstep (se 1 (by rfl) ⟨17588150, by rfl⟩ : syracuseStep 23450867 = 35176301) B35176301
theorem B2405687 : Blo 1603000 2405687 := bstep (se 1 (by rfl) ⟨1804265, by rfl⟩ : syracuseStep 2405687 = 3608531) B3608531
theorem B5780807 : Blo 1603000 5780807 := bstep (se 1 (by rfl) ⟨4335605, by rfl⟩ : syracuseStep 5780807 = 8671211) B8671211
theorem B3044927 : Blo 1603000 3044927 := bstep (se 1 (by rfl) ⟨2283695, by rfl⟩ : syracuseStep 3044927 = 4567391) B4567391
theorem B5412473 : Blo 1603000 5412473 := bstep (se 2 (by rfl) ⟨2029677, by rfl⟩ : syracuseStep 5412473 = 4059355) B4059355
theorem B1603199 : Blo 1603000 1603199 := bstep (se 1 (by rfl) ⟨1202399, by rfl⟩ : syracuseStep 1603199 = 2404799) B2404799
theorem B1603431 : Blo 1603000 1603431 := bstep (se 1 (by rfl) ⟨1202573, by rfl⟩ : syracuseStep 1603431 = 2405147) B2405147
theorem B2406377 : Blo 1603000 2406377 := bstep (se 2 (by rfl) ⟨902391, by rfl⟩ : syracuseStep 2406377 = 1804783) B1804783
theorem B2283547 : Blo 1603000 2283547 := bstep (se 1 (by rfl) ⟨1712660, by rfl⟩ : syracuseStep 2283547 = 3425321) B3425321
theorem B3610727 : Blo 1603000 3610727 := bstep (se 1 (by rfl) ⟨2708045, by rfl⟩ : syracuseStep 3610727 = 5416091) B5416091
theorem B2406521 : Blo 1603000 2406521 := bstep (se 2 (by rfl) ⟨902445, by rfl⟩ : syracuseStep 2406521 = 1804891) B1804891
theorem B9140363 : Blo 1603000 9140363 := bstep (se 1 (by rfl) ⟨6855272, by rfl⟩ : syracuseStep 9140363 = 13710545) B13710545
theorem B2406575 : Blo 1603000 2406575 := bstep (se 1 (by rfl) ⟨1804931, by rfl⟩ : syracuseStep 2406575 = 3609863) B3609863
theorem B2406815 : Blo 1603000 2406815 := bstep (se 1 (by rfl) ⟨1805111, by rfl⟩ : syracuseStep 2406815 = 3610223) B3610223
theorem B3611051 : Blo 1603000 3611051 := bstep (se 1 (by rfl) ⟨2708288, by rfl⟩ : syracuseStep 3611051 = 5416577) B5416577
theorem B2407007 : Blo 1603000 2407007 := bstep (se 1 (by rfl) ⟨1805255, by rfl⟩ : syracuseStep 2407007 = 3610511) B3610511
theorem B4061947 : Blo 1603000 4061947 := bstep (se 1 (by rfl) ⟨3046460, by rfl⟩ : syracuseStep 4061947 = 6092921) B6092921
theorem B1604415 : Blo 1603000 1604415 := bstep (se 1 (by rfl) ⟨1203311, by rfl⟩ : syracuseStep 1604415 = 2406623) B2406623
theorem B1604455 : Blo 1603000 1604455 := bstep (se 1 (by rfl) ⟨1203341, by rfl⟩ : syracuseStep 1604455 = 2406683) B2406683
theorem B1604479 : Blo 1603000 1604479 := bstep (se 1 (by rfl) ⟨1203359, by rfl⟩ : syracuseStep 1604479 = 2406719) B2406719
theorem B52763665 : Blo 1603000 52763665 := bstep (se 2 (by rfl) ⟨19786374, by rfl⟩ : syracuseStep 52763665 = 39572749) B39572749
theorem B2407487 : Blo 1603000 2407487 := bstep (se 1 (by rfl) ⟨1805615, by rfl⟩ : syracuseStep 2407487 = 3611231) B3611231
theorem B1604735 : Blo 1603000 1604735 := bstep (se 1 (by rfl) ⟨1203551, by rfl⟩ : syracuseStep 1604735 = 2407103) B2407103
theorem B27794717 : Blo 1603000 27794717 := bstep (se 3 (by rfl) ⟨5211509, by rfl⟩ : syracuseStep 27794717 = 10423019) B10423019
theorem B1604927 : Blo 1603000 1604927 := bstep (se 1 (by rfl) ⟨1203695, by rfl⟩ : syracuseStep 1604927 = 2407391) B2407391
theorem B1604967 : Blo 1603000 1604967 := bstep (se 1 (by rfl) ⟨1203725, by rfl⟩ : syracuseStep 1604967 = 2407451) B2407451
theorem B3423647 : Blo 1603000 3423647 := bstep (se 1 (by rfl) ⟨2567735, by rfl⟩ : syracuseStep 3423647 = 5135471) B5135471
theorem B26025695 : Blo 1603000 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B8118143 : Blo 1603000 8118143 := bstep (se 1 (by rfl) ⟨6088607, by rfl⟩ : syracuseStep 8118143 = 12177215) B12177215
theorem B6848489 : Blo 1603000 6848489 := bstep (se 2 (by rfl) ⟨2568183, by rfl⟩ : syracuseStep 6848489 = 5136367) B5136367
theorem B9134279 : Blo 1603000 9134279 := bstep (se 1 (by rfl) ⟨6850709, by rfl⟩ : syracuseStep 9134279 = 13701419) B13701419
theorem B7708895 : Blo 1603000 7708895 := bstep (se 1 (by rfl) ⟨5781671, by rfl⟩ : syracuseStep 7708895 = 11563343) B11563343
theorem B4874735 : Blo 1603000 4874735 := bstep (se 1 (by rfl) ⟨3656051, by rfl⟩ : syracuseStep 4874735 = 7312103) B7312103
theorem B41124347 : Blo 1603000 41124347 := bstep (se 1 (by rfl) ⟨30843260, by rfl⟩ : syracuseStep 41124347 = 61686521) B61686521
theorem B20546135 : Blo 1603000 20546135 := bstep (se 1 (by rfl) ⟨15409601, by rfl⟩ : syracuseStep 20546135 = 30819203) B30819203
theorem B5415929 : Blo 1603000 5415929 := bstep (se 2 (by rfl) ⟨2030973, by rfl⟩ : syracuseStep 5415929 = 4061947) B4061947
theorem B28173905 : Blo 1603000 28173905 := bstep (se 2 (by rfl) ⟨10565214, by rfl⟩ : syracuseStep 28173905 = 21130429) B21130429
theorem B12175271 : Blo 1603000 12175271 := bstep (se 1 (by rfl) ⟨9131453, by rfl⟩ : syracuseStep 12175271 = 18262907) B18262907
theorem B4565659 : Blo 1603000 4565659 := bstep (se 1 (by rfl) ⟨3424244, by rfl⟩ : syracuseStep 4565659 = 6848489) B6848489
theorem B3607271 : Blo 1603000 3607271 := bstep (se 1 (by rfl) ⟨2705453, by rfl⟩ : syracuseStep 3607271 = 5410907) B5410907
theorem B9136921 : Blo 1603000 9136921 := bstep (se 2 (by rfl) ⟨3426345, by rfl⟩ : syracuseStep 9136921 = 6852691) B6852691
theorem B2706203 : Blo 1603000 2706203 := bstep (se 1 (by rfl) ⟨2029652, by rfl⟩ : syracuseStep 2706203 = 4059305) B4059305
theorem B2706223 : Blo 1603000 2706223 := bstep (se 1 (by rfl) ⟨2029667, by rfl⟩ : syracuseStep 2706223 = 4059335) B4059335
theorem B263351159 : Blo 1603000 263351159 := bstep (se 1 (by rfl) ⟨197513369, by rfl⟩ : syracuseStep 263351159 = 395026739) B395026739
theorem B85633967 : Blo 1603000 85633967 := bstep (se 1 (by rfl) ⟨64225475, by rfl⟩ : syracuseStep 85633967 = 128450951) B128450951
theorem B15633911 : Blo 1603000 15633911 := bstep (se 1 (by rfl) ⟨11725433, by rfl⟩ : syracuseStep 15633911 = 23450867) B23450867
theorem B3853871 : Blo 1603000 3853871 := bstep (se 1 (by rfl) ⟨2890403, by rfl⟩ : syracuseStep 3853871 = 5780807) B5780807
theorem B5410529 : Blo 1603000 5410529 := bstep (se 2 (by rfl) ⟨2028948, by rfl⟩ : syracuseStep 5410529 = 4057897) B4057897
theorem B3608315 : Blo 1603000 3608315 := bstep (se 1 (by rfl) ⟨2706236, by rfl⟩ : syracuseStep 3608315 = 5412473) B5412473
theorem B18518321 : Blo 1603000 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B2404895 : Blo 1603000 2404895 := bstep (se 1 (by rfl) ⟨1803671, by rfl⟩ : syracuseStep 2404895 = 3607343) B3607343
theorem B7811657 : Blo 1603000 7811657 := bstep (se 2 (by rfl) ⟨2929371, by rfl⟩ : syracuseStep 7811657 = 5858743) B5858743
theorem B31232897 : Blo 1603000 31232897 := bstep (se 2 (by rfl) ⟨11712336, by rfl⟩ : syracuseStep 31232897 = 23424673) B23424673
theorem B2282431 : Blo 1603000 2282431 := bstep (se 1 (by rfl) ⟨1711823, by rfl⟩ : syracuseStep 2282431 = 3423647) B3423647
theorem B3609593 : Blo 1603000 3609593 := bstep (se 2 (by rfl) ⟨1353597, by rfl⟩ : syracuseStep 3609593 = 2707195) B2707195
theorem B5412095 : Blo 1603000 5412095 := bstep (se 1 (by rfl) ⟨4059071, by rfl⟩ : syracuseStep 5412095 = 8118143) B8118143
theorem B3044729 : Blo 1603000 3044729 := bstep (se 2 (by rfl) ⟨1141773, by rfl⟩ : syracuseStep 3044729 = 2283547) B2283547
theorem B11130335 : Blo 1603000 11130335 := bstep (se 1 (by rfl) ⟨8347751, by rfl⟩ : syracuseStep 11130335 = 16695503) B16695503
theorem B8115713 : Blo 1603000 8115713 := bstep (se 2 (by rfl) ⟨3043392, by rfl⟩ : syracuseStep 8115713 = 6086785) B6086785
theorem B2405993 : Blo 1603000 2405993 := bstep (se 2 (by rfl) ⟨902247, by rfl⟩ : syracuseStep 2405993 = 1804495) B1804495
theorem B2406119 : Blo 1603000 2406119 := bstep (se 1 (by rfl) ⟨1804589, by rfl⟩ : syracuseStep 2406119 = 3609179) B3609179
theorem B53458721 : Blo 1603000 53458721 := bstep (se 2 (by rfl) ⟨20047020, by rfl⟩ : syracuseStep 53458721 = 40094041) B40094041
theorem B4061087 : Blo 1603000 4061087 := bstep (se 1 (by rfl) ⟨3045815, by rfl⟩ : syracuseStep 4061087 = 6091631) B6091631
theorem B1603495 : Blo 1603000 1603495 := bstep (se 1 (by rfl) ⟨1202621, by rfl⟩ : syracuseStep 1603495 = 2405243) B2405243
theorem B3045367 : Blo 1603000 3045367 := bstep (se 1 (by rfl) ⟨2284025, by rfl⟩ : syracuseStep 3045367 = 4568051) B4568051
theorem B2889769 : Blo 1603000 2889769 := bstep (se 2 (by rfl) ⟨1083663, by rfl⟩ : syracuseStep 2889769 = 2167327) B2167327
theorem B2406455 : Blo 1603000 2406455 := bstep (se 1 (by rfl) ⟨1804841, by rfl⟩ : syracuseStep 2406455 = 3609683) B3609683
theorem B1603647 : Blo 1603000 1603647 := bstep (se 1 (by rfl) ⟨1202735, by rfl⟩ : syracuseStep 1603647 = 2405471) B2405471
theorem B2406527 : Blo 1603000 2406527 := bstep (se 1 (by rfl) ⟨1804895, by rfl⟩ : syracuseStep 2406527 = 3609791) B3609791
theorem B1603791 : Blo 1603000 1603791 := bstep (se 1 (by rfl) ⟨1202843, by rfl⟩ : syracuseStep 1603791 = 2405687) B2405687
theorem B2029951 : Blo 1603000 2029951 := bstep (se 1 (by rfl) ⟨1522463, by rfl⟩ : syracuseStep 2029951 = 3044927) B3044927
theorem B1604251 : Blo 1603000 1604251 := bstep (se 1 (by rfl) ⟨1203188, by rfl⟩ : syracuseStep 1604251 = 2406377) B2406377
theorem B70351553 : Blo 1603000 70351553 := bstep (se 2 (by rfl) ⟨26381832, by rfl⟩ : syracuseStep 70351553 = 52763665) B52763665
theorem B2407151 : Blo 1603000 2407151 := bstep (se 1 (by rfl) ⟨1805363, by rfl⟩ : syracuseStep 2407151 = 3610727) B3610727
theorem B1604347 : Blo 1603000 1604347 := bstep (se 1 (by rfl) ⟨1203260, by rfl⟩ : syracuseStep 1604347 = 2406521) B2406521
theorem B6093575 : Blo 1603000 6093575 := bstep (se 1 (by rfl) ⟨4570181, by rfl⟩ : syracuseStep 6093575 = 9140363) B9140363
theorem B1604383 : Blo 1603000 1604383 := bstep (se 1 (by rfl) ⟨1203287, by rfl⟩ : syracuseStep 1604383 = 2406575) B2406575
theorem B7707433 : Blo 1603000 7707433 := bstep (se 2 (by rfl) ⟨2890287, by rfl⟩ : syracuseStep 7707433 = 5780575) B5780575
theorem B1604543 : Blo 1603000 1604543 := bstep (se 1 (by rfl) ⟨1203407, by rfl⟩ : syracuseStep 1604543 = 2406815) B2406815
theorem B2407367 : Blo 1603000 2407367 := bstep (se 1 (by rfl) ⟨1805525, by rfl⟩ : syracuseStep 2407367 = 3611051) B3611051
theorem B1604671 : Blo 1603000 1604671 := bstep (se 1 (by rfl) ⟨1203503, by rfl⟩ : syracuseStep 1604671 = 2407007) B2407007
theorem B2284681 : Blo 1603000 2284681 := bstep (se 2 (by rfl) ⟨856755, by rfl⟩ : syracuseStep 2284681 = 1713511) B1713511
theorem B1604991 : Blo 1603000 1604991 := bstep (se 1 (by rfl) ⟨1203743, by rfl⟩ : syracuseStep 1604991 = 2407487) B2407487
theorem B7814657 : Blo 1603000 7814657 := bstep (se 2 (by rfl) ⟨2930496, by rfl⟩ : syracuseStep 7814657 = 5860993) B5860993
theorem B18529811 : Blo 1603000 18529811 := bstep (se 1 (by rfl) ⟨13897358, by rfl⟩ : syracuseStep 18529811 = 27794717) B27794717
theorem B17350463 : Blo 1603000 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B12345547 : Blo 1603000 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B13697423 : Blo 1603000 13697423 := bstep (se 1 (by rfl) ⟨10273067, by rfl⟩ : syracuseStep 13697423 = 20546135) B20546135
theorem B6087545 : Blo 1603000 6087545 := bstep (se 2 (by rfl) ⟨2282829, by rfl⟩ : syracuseStep 6087545 = 4565659) B4565659
theorem B8119277 : Blo 1603000 8119277 := bstep (se 3 (by rfl) ⟨1522364, by rfl⟩ : syracuseStep 8119277 = 3044729) B3044729
theorem B12182561 : Blo 1603000 12182561 := bstep (se 2 (by rfl) ⟨4568460, by rfl⟩ : syracuseStep 12182561 = 9136921) B9136921
theorem B46901035 : Blo 1603000 46901035 := bstep (se 1 (by rfl) ⟨35175776, by rfl⟩ : syracuseStep 46901035 = 70351553) B70351553
theorem B1804135 : Blo 1603000 1804135 := bstep (se 1 (by rfl) ⟨1353101, by rfl⟩ : syracuseStep 1804135 = 2706203) B2706203
theorem B10422607 : Blo 1603000 10422607 := bstep (se 1 (by rfl) ⟨7816955, by rfl⟩ : syracuseStep 10422607 = 15633911) B15633911
theorem B3607019 : Blo 1603000 3607019 := bstep (se 1 (by rfl) ⟨2705264, by rfl⟩ : syracuseStep 3607019 = 5410529) B5410529
theorem B3853025 : Blo 1603000 3853025 := bstep (se 2 (by rfl) ⟨1444884, by rfl⟩ : syracuseStep 3853025 = 2889769) B2889769
theorem B6089519 : Blo 1603000 6089519 := bstep (se 1 (by rfl) ⟨4567139, by rfl⟩ : syracuseStep 6089519 = 9134279) B9134279
theorem B5139263 : Blo 1603000 5139263 := bstep (se 1 (by rfl) ⟨3854447, by rfl⟩ : syracuseStep 5139263 = 7708895) B7708895
theorem B2706601 : Blo 1603000 2706601 := bstep (se 2 (by rfl) ⟨1014975, by rfl⟩ : syracuseStep 2706601 = 2029951) B2029951
theorem B3608063 : Blo 1603000 3608063 := bstep (se 1 (by rfl) ⟨2706047, by rfl⟩ : syracuseStep 3608063 = 5412095) B5412095
theorem B5410475 : Blo 1603000 5410475 := bstep (se 1 (by rfl) ⟨4057856, by rfl⟩ : syracuseStep 5410475 = 8115713) B8115713
theorem B10276577 : Blo 1603000 10276577 := bstep (se 2 (by rfl) ⟨3853716, by rfl⟩ : syracuseStep 10276577 = 7707433) B7707433
theorem B3608297 : Blo 1603000 3608297 := bstep (se 2 (by rfl) ⟨1353111, by rfl⟩ : syracuseStep 3608297 = 2706223) B2706223
theorem B35639147 : Blo 1603000 35639147 := bstep (se 1 (by rfl) ⟨26729360, by rfl⟩ : syracuseStep 35639147 = 53458721) B53458721
theorem B3043241 : Blo 1603000 3043241 := bstep (se 2 (by rfl) ⟨1141215, by rfl⟩ : syracuseStep 3043241 = 2282431) B2282431
theorem B2707391 : Blo 1603000 2707391 := bstep (se 1 (by rfl) ⟨2030543, by rfl⟩ : syracuseStep 2707391 = 4061087) B4061087
theorem B2404847 : Blo 1603000 2404847 := bstep (se 1 (by rfl) ⟨1803635, by rfl⟩ : syracuseStep 2404847 = 3607271) B3607271
theorem B175567439 : Blo 1603000 175567439 := bstep (se 1 (by rfl) ⟨131675579, by rfl⟩ : syracuseStep 175567439 = 263351159) B263351159
theorem B2569247 : Blo 1603000 2569247 := bstep (se 1 (by rfl) ⟨1926935, by rfl⟩ : syracuseStep 2569247 = 3853871) B3853871
theorem B228357245 : Blo 1603000 228357245 := bstep (se 3 (by rfl) ⟨42816983, by rfl⟩ : syracuseStep 228357245 = 85633967) B85633967
theorem B2405543 : Blo 1603000 2405543 := bstep (se 1 (by rfl) ⟨1804157, by rfl⟩ : syracuseStep 2405543 = 3608315) B3608315
theorem B4060489 : Blo 1603000 4060489 := bstep (se 2 (by rfl) ⟨1522683, by rfl⟩ : syracuseStep 4060489 = 3045367) B3045367
theorem B3249823 : Blo 1603000 3249823 := bstep (se 1 (by rfl) ⟨2437367, by rfl⟩ : syracuseStep 3249823 = 4874735) B4874735
theorem B27416231 : Blo 1603000 27416231 := bstep (se 1 (by rfl) ⟨20562173, by rfl⟩ : syracuseStep 27416231 = 41124347) B41124347
theorem B1603263 : Blo 1603000 1603263 := bstep (se 1 (by rfl) ⟨1202447, by rfl⟩ : syracuseStep 1603263 = 2404895) B2404895
theorem B5207771 : Blo 1603000 5207771 := bstep (se 1 (by rfl) ⟨3905828, by rfl⟩ : syracuseStep 5207771 = 7811657) B7811657
theorem B20821931 : Blo 1603000 20821931 := bstep (se 1 (by rfl) ⟨15616448, by rfl⟩ : syracuseStep 20821931 = 31232897) B31232897
theorem B2406395 : Blo 1603000 2406395 := bstep (se 1 (by rfl) ⟨1804796, by rfl⟩ : syracuseStep 2406395 = 3609593) B3609593
theorem B3610619 : Blo 1603000 3610619 := bstep (se 1 (by rfl) ⟨2707964, by rfl⟩ : syracuseStep 3610619 = 5415929) B5415929
theorem B7420223 : Blo 1603000 7420223 := bstep (se 1 (by rfl) ⟨5565167, by rfl⟩ : syracuseStep 7420223 = 11130335) B11130335
theorem B18782603 : Blo 1603000 18782603 := bstep (se 1 (by rfl) ⟨14086952, by rfl⟩ : syracuseStep 18782603 = 28173905) B28173905
theorem B1603995 : Blo 1603000 1603995 := bstep (se 1 (by rfl) ⟨1202996, by rfl⟩ : syracuseStep 1603995 = 2405993) B2405993
theorem B1604079 : Blo 1603000 1604079 := bstep (se 1 (by rfl) ⟨1203059, by rfl⟩ : syracuseStep 1604079 = 2406119) B2406119
theorem B8116847 : Blo 1603000 8116847 := bstep (se 1 (by rfl) ⟨6087635, by rfl⟩ : syracuseStep 8116847 = 12175271) B12175271
theorem B1604303 : Blo 1603000 1604303 := bstep (se 1 (by rfl) ⟨1203227, by rfl⟩ : syracuseStep 1604303 = 2406455) B2406455
theorem B1604351 : Blo 1603000 1604351 := bstep (se 1 (by rfl) ⟨1203263, by rfl⟩ : syracuseStep 1604351 = 2406527) B2406527
theorem B3046241 : Blo 1603000 3046241 := bstep (se 2 (by rfl) ⟨1142340, by rfl⟩ : syracuseStep 3046241 = 2284681) B2284681
theorem B1604767 : Blo 1603000 1604767 := bstep (se 1 (by rfl) ⟨1203575, by rfl⟩ : syracuseStep 1604767 = 2407151) B2407151
theorem B4062383 : Blo 1603000 4062383 := bstep (se 1 (by rfl) ⟨3046787, by rfl⟩ : syracuseStep 4062383 = 6093575) B6093575
theorem B1604911 : Blo 1603000 1604911 := bstep (se 1 (by rfl) ⟨1203683, by rfl⟩ : syracuseStep 1604911 = 2407367) B2407367
theorem B5209771 : Blo 1603000 5209771 := bstep (se 1 (by rfl) ⟨3907328, by rfl⟩ : syracuseStep 5209771 = 7814657) B7814657
theorem B12353207 : Blo 1603000 12353207 := bstep (se 1 (by rfl) ⟨9264905, by rfl⟩ : syracuseStep 12353207 = 18529811) B18529811
theorem B11566975 : Blo 1603000 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B1712831 : Blo 1603000 1712831 := bstep (se 1 (by rfl) ⟨1284623, by rfl⟩ : syracuseStep 1712831 = 2569247) B2569247
theorem B18277487 : Blo 1603000 18277487 := bstep (se 1 (by rfl) ⟨13708115, by rfl⟩ : syracuseStep 18277487 = 27416231) B27416231
theorem B32941885 : Blo 1603000 32941885 := bstep (se 3 (by rfl) ⟨6176603, by rfl⟩ : syracuseStep 32941885 = 12353207) B12353207
theorem B3426175 : Blo 1603000 3426175 := bstep (se 1 (by rfl) ⟨2569631, by rfl⟩ : syracuseStep 3426175 = 5139263) B5139263
theorem B13887389 : Blo 1603000 13887389 := bstep (se 3 (by rfl) ⟨2603885, by rfl⟩ : syracuseStep 13887389 = 5207771) B5207771
theorem B95037725 : Blo 1603000 95037725 := bstep (se 3 (by rfl) ⟨17819573, by rfl⟩ : syracuseStep 95037725 = 35639147) B35639147
theorem B3606983 : Blo 1603000 3606983 := bstep (se 1 (by rfl) ⟨2705237, by rfl⟩ : syracuseStep 3606983 = 5410475) B5410475
theorem B6851051 : Blo 1603000 6851051 := bstep (se 1 (by rfl) ⟨5138288, by rfl⟩ : syracuseStep 6851051 = 10276577) B10276577
theorem B1804927 : Blo 1603000 1804927 := bstep (se 1 (by rfl) ⟨1353695, by rfl⟩ : syracuseStep 1804927 = 2707391) B2707391
theorem B16460729 : Blo 1603000 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B13896809 : Blo 1603000 13896809 := bstep (se 2 (by rfl) ⟨5211303, by rfl⟩ : syracuseStep 13896809 = 10422607) B10422607
theorem B4058363 : Blo 1603000 4058363 := bstep (se 1 (by rfl) ⟨3043772, by rfl⟩ : syracuseStep 4058363 = 6087545) B6087545
theorem B8121707 : Blo 1603000 8121707 := bstep (se 1 (by rfl) ⟨6091280, by rfl⟩ : syracuseStep 8121707 = 12182561) B12182561
theorem B13881287 : Blo 1603000 13881287 := bstep (se 1 (by rfl) ⟨10410965, by rfl⟩ : syracuseStep 13881287 = 20821931) B20821931
theorem B3608801 : Blo 1603000 3608801 := bstep (se 2 (by rfl) ⟨1353300, by rfl⟩ : syracuseStep 3608801 = 2706601) B2706601
theorem B12521735 : Blo 1603000 12521735 := bstep (se 1 (by rfl) ⟨9391301, by rfl⟩ : syracuseStep 12521735 = 18782603) B18782603
theorem B2404679 : Blo 1603000 2404679 := bstep (se 1 (by rfl) ⟨1803509, by rfl⟩ : syracuseStep 2404679 = 3607019) B3607019
theorem B5411231 : Blo 1603000 5411231 := bstep (se 1 (by rfl) ⟨4058423, by rfl⟩ : syracuseStep 5411231 = 8116847) B8116847
theorem B2568683 : Blo 1603000 2568683 := bstep (se 1 (by rfl) ⟨1926512, by rfl⟩ : syracuseStep 2568683 = 3853025) B3853025
theorem B4059679 : Blo 1603000 4059679 := bstep (se 1 (by rfl) ⟨3044759, by rfl⟩ : syracuseStep 4059679 = 6089519) B6089519
theorem B2708255 : Blo 1603000 2708255 := bstep (se 1 (by rfl) ⟨2031191, by rfl⟩ : syracuseStep 2708255 = 4062383) B4062383
theorem B2405375 : Blo 1603000 2405375 := bstep (se 1 (by rfl) ⟨1804031, by rfl⟩ : syracuseStep 2405375 = 3608063) B3608063
theorem B62534713 : Blo 1603000 62534713 := bstep (se 2 (by rfl) ⟨23450517, by rfl⟩ : syracuseStep 62534713 = 46901035) B46901035
theorem B2405513 : Blo 1603000 2405513 := bstep (se 2 (by rfl) ⟨902067, by rfl⟩ : syracuseStep 2405513 = 1804135) B1804135
theorem B2405531 : Blo 1603000 2405531 := bstep (se 1 (by rfl) ⟨1804148, by rfl⟩ : syracuseStep 2405531 = 3608297) B3608297
theorem B15422633 : Blo 1603000 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B2028827 : Blo 1603000 2028827 := bstep (se 1 (by rfl) ⟨1521620, by rfl⟩ : syracuseStep 2028827 = 3043241) B3043241
theorem B9131615 : Blo 1603000 9131615 := bstep (se 1 (by rfl) ⟨6848711, by rfl⟩ : syracuseStep 9131615 = 13697423) B13697423
theorem B1603231 : Blo 1603000 1603231 := bstep (se 1 (by rfl) ⟨1202423, by rfl⟩ : syracuseStep 1603231 = 2404847) B2404847
theorem B117044959 : Blo 1603000 117044959 := bstep (se 1 (by rfl) ⟨87783719, by rfl⟩ : syracuseStep 117044959 = 175567439) B175567439
theorem B5412851 : Blo 1603000 5412851 := bstep (se 1 (by rfl) ⟨4059638, by rfl⟩ : syracuseStep 5412851 = 8119277) B8119277
theorem B152238163 : Blo 1603000 152238163 := bstep (se 1 (by rfl) ⟨114178622, by rfl⟩ : syracuseStep 152238163 = 228357245) B228357245
theorem B1603695 : Blo 1603000 1603695 := bstep (se 1 (by rfl) ⟨1202771, by rfl⟩ : syracuseStep 1603695 = 2405543) B2405543
theorem B1604263 : Blo 1603000 1604263 := bstep (se 1 (by rfl) ⟨1203197, by rfl⟩ : syracuseStep 1604263 = 2406395) B2406395
theorem B2407079 : Blo 1603000 2407079 := bstep (se 1 (by rfl) ⟨1805309, by rfl⟩ : syracuseStep 2407079 = 3610619) B3610619
theorem B4946815 : Blo 1603000 4946815 := bstep (se 1 (by rfl) ⟨3710111, by rfl⟩ : syracuseStep 4946815 = 7420223) B7420223
theorem B5413985 : Blo 1603000 5413985 := bstep (se 2 (by rfl) ⟨2030244, by rfl⟩ : syracuseStep 5413985 = 4060489) B4060489
theorem B2030827 : Blo 1603000 2030827 := bstep (se 1 (by rfl) ⟨1523120, by rfl⟩ : syracuseStep 2030827 = 3046241) B3046241
theorem B4333097 : Blo 1603000 4333097 := bstep (se 2 (by rfl) ⟨1624911, by rfl⟩ : syracuseStep 4333097 = 3249823) B3249823
theorem B6946361 : Blo 1603000 6946361 := bstep (se 2 (by rfl) ⟨2604885, by rfl⟩ : syracuseStep 6946361 = 5209771) B5209771
theorem B8347823 : Blo 1603000 8347823 := bstep (se 1 (by rfl) ⟨6260867, by rfl⟩ : syracuseStep 8347823 = 12521735) B12521735
theorem B10281755 : Blo 1603000 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B6087743 : Blo 1603000 6087743 := bstep (se 1 (by rfl) ⟨4565807, by rfl⟩ : syracuseStep 6087743 = 9131615) B9131615
theorem B6595753 : Blo 1603000 6595753 := bstep (se 2 (by rfl) ⟨2473407, by rfl⟩ : syracuseStep 6595753 = 4946815) B4946815
theorem B9258259 : Blo 1603000 9258259 := bstep (se 1 (by rfl) ⟨6943694, by rfl⟩ : syracuseStep 9258259 = 13887389) B13887389
theorem B6849821 : Blo 1603000 6849821 := bstep (se 3 (by rfl) ⟨1284341, by rfl⟩ : syracuseStep 6849821 = 2568683) B2568683
theorem B83379617 : Blo 1603000 83379617 := bstep (se 2 (by rfl) ⟨31267356, by rfl⟩ : syracuseStep 83379617 = 62534713) B62534713
theorem B18270197 : Blo 1603000 18270197 := bstep (se 5 (by rfl) ⟨856415, by rfl⟩ : syracuseStep 18270197 = 1712831) B1712831
theorem B2705575 : Blo 1603000 2705575 := bstep (se 1 (by rfl) ⟨2029181, by rfl⟩ : syracuseStep 2705575 = 4058363) B4058363
theorem B156059945 : Blo 1603000 156059945 := bstep (se 2 (by rfl) ⟨58522479, by rfl⟩ : syracuseStep 156059945 = 117044959) B117044959
theorem B4630907 : Blo 1603000 4630907 := bstep (se 1 (by rfl) ⟨3473180, by rfl⟩ : syracuseStep 4630907 = 6946361) B6946361
theorem B202984217 : Blo 1603000 202984217 := bstep (se 2 (by rfl) ⟨76119081, by rfl⟩ : syracuseStep 202984217 = 152238163) B152238163
theorem B3607487 : Blo 1603000 3607487 := bstep (se 1 (by rfl) ⟨2705615, by rfl⟩ : syracuseStep 3607487 = 5411231) B5411231
theorem B1805503 : Blo 1603000 1805503 := bstep (se 1 (by rfl) ⟨1354127, by rfl⟩ : syracuseStep 1805503 = 2708255) B2708255
theorem B5410205 : Blo 1603000 5410205 := bstep (se 3 (by rfl) ⟨1014413, by rfl⟩ : syracuseStep 5410205 = 2028827) B2028827
theorem B12184991 : Blo 1603000 12184991 := bstep (se 1 (by rfl) ⟨9138743, by rfl⟩ : syracuseStep 12184991 = 18277487) B18277487
theorem B3608567 : Blo 1603000 3608567 := bstep (se 1 (by rfl) ⟨2706425, by rfl⟩ : syracuseStep 3608567 = 5412851) B5412851
theorem B2404655 : Blo 1603000 2404655 := bstep (se 1 (by rfl) ⟨1803491, by rfl⟩ : syracuseStep 2404655 = 3606983) B3606983
theorem B2707769 : Blo 1603000 2707769 := bstep (se 2 (by rfl) ⟨1015413, by rfl⟩ : syracuseStep 2707769 = 2030827) B2030827
theorem B4567367 : Blo 1603000 4567367 := bstep (se 1 (by rfl) ⟨3425525, by rfl⟩ : syracuseStep 4567367 = 6851051) B6851051
theorem B10973819 : Blo 1603000 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B3609323 : Blo 1603000 3609323 := bstep (se 1 (by rfl) ⟨2706992, by rfl⟩ : syracuseStep 3609323 = 5413985) B5413985
theorem B2888731 : Blo 1603000 2888731 := bstep (se 1 (by rfl) ⟨2166548, by rfl⟩ : syracuseStep 2888731 = 4333097) B4333097
theorem B43922513 : Blo 1603000 43922513 := bstep (se 2 (by rfl) ⟨16470942, by rfl⟩ : syracuseStep 43922513 = 32941885) B32941885
theorem B4568233 : Blo 1603000 4568233 := bstep (se 2 (by rfl) ⟨1713087, by rfl⟩ : syracuseStep 4568233 = 3426175) B3426175
theorem B9254191 : Blo 1603000 9254191 := bstep (se 1 (by rfl) ⟨6940643, by rfl⟩ : syracuseStep 9254191 = 13881287) B13881287
theorem B2405867 : Blo 1603000 2405867 := bstep (se 1 (by rfl) ⟨1804400, by rfl⟩ : syracuseStep 2405867 = 3608801) B3608801
theorem B1603119 : Blo 1603000 1603119 := bstep (se 1 (by rfl) ⟨1202339, by rfl⟩ : syracuseStep 1603119 = 2404679) B2404679
theorem B1603583 : Blo 1603000 1603583 := bstep (se 1 (by rfl) ⟨1202687, by rfl⟩ : syracuseStep 1603583 = 2405375) B2405375
theorem B5412905 : Blo 1603000 5412905 := bstep (se 2 (by rfl) ⟨2029839, by rfl⟩ : syracuseStep 5412905 = 4059679) B4059679
theorem B253433933 : Blo 1603000 253433933 := bstep (se 3 (by rfl) ⟨47518862, by rfl⟩ : syracuseStep 253433933 = 95037725) B95037725
theorem B1603675 : Blo 1603000 1603675 := bstep (se 1 (by rfl) ⟨1202756, by rfl⟩ : syracuseStep 1603675 = 2405513) B2405513
theorem B1603687 : Blo 1603000 1603687 := bstep (se 1 (by rfl) ⟨1202765, by rfl⟩ : syracuseStep 1603687 = 2405531) B2405531
theorem B2406569 : Blo 1603000 2406569 := bstep (se 2 (by rfl) ⟨902463, by rfl⟩ : syracuseStep 2406569 = 1804927) B1804927
theorem B1604719 : Blo 1603000 1604719 := bstep (se 1 (by rfl) ⟨1203539, by rfl⟩ : syracuseStep 1604719 = 2407079) B2407079
theorem B9264539 : Blo 1603000 9264539 := bstep (se 1 (by rfl) ⟨6948404, by rfl⟩ : syracuseStep 9264539 = 13896809) B13896809
theorem B5414471 : Blo 1603000 5414471 := bstep (se 1 (by rfl) ⟨4060853, by rfl⟩ : syracuseStep 5414471 = 8121707) B8121707
theorem B3851641 : Blo 1603000 3851641 := bstep (se 2 (by rfl) ⟨1444365, by rfl⟩ : syracuseStep 3851641 = 2888731) B2888731
theorem B104039963 : Blo 1603000 104039963 := bstep (se 1 (by rfl) ⟨78029972, by rfl⟩ : syracuseStep 104039963 = 156059945) B156059945
theorem B29263517 : Blo 1603000 29263517 := bstep (se 3 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 29263517 = 10973819) B10973819
theorem B12338921 : Blo 1603000 12338921 := bstep (se 2 (by rfl) ⟨4627095, by rfl⟩ : syracuseStep 12338921 = 9254191) B9254191
theorem B3606803 : Blo 1603000 3606803 := bstep (se 1 (by rfl) ⟨2705102, by rfl⟩ : syracuseStep 3606803 = 5410205) B5410205
theorem B5565215 : Blo 1603000 5565215 := bstep (se 1 (by rfl) ⟨4173911, by rfl⟩ : syracuseStep 5565215 = 8347823) B8347823
theorem B1805179 : Blo 1603000 1805179 := bstep (se 1 (by rfl) ⟨1353884, by rfl⟩ : syracuseStep 1805179 = 2707769) B2707769
theorem B3607433 : Blo 1603000 3607433 := bstep (se 2 (by rfl) ⟨1352787, by rfl⟩ : syracuseStep 3607433 = 2705575) B2705575
theorem B4058495 : Blo 1603000 4058495 := bstep (se 1 (by rfl) ⟨3043871, by rfl⟩ : syracuseStep 4058495 = 6087743) B6087743
theorem B29281675 : Blo 1603000 29281675 := bstep (se 1 (by rfl) ⟨21961256, by rfl⟩ : syracuseStep 29281675 = 43922513) B43922513
theorem B4566547 : Blo 1603000 4566547 := bstep (se 1 (by rfl) ⟨3424910, by rfl⟩ : syracuseStep 4566547 = 6849821) B6849821
theorem B55586411 : Blo 1603000 55586411 := bstep (se 1 (by rfl) ⟨41689808, by rfl⟩ : syracuseStep 55586411 = 83379617) B83379617
theorem B3608603 : Blo 1603000 3608603 := bstep (se 1 (by rfl) ⟨2706452, by rfl⟩ : syracuseStep 3608603 = 5412905) B5412905
theorem B168955955 : Blo 1603000 168955955 := bstep (se 1 (by rfl) ⟨126716966, by rfl⟩ : syracuseStep 168955955 = 253433933) B253433933
theorem B6090977 : Blo 1603000 6090977 := bstep (se 2 (by rfl) ⟨2284116, by rfl⟩ : syracuseStep 6090977 = 4568233) B4568233
theorem B8794337 : Blo 1603000 8794337 := bstep (se 2 (by rfl) ⟨3297876, by rfl⟩ : syracuseStep 8794337 = 6595753) B6595753
theorem B2404991 : Blo 1603000 2404991 := bstep (se 1 (by rfl) ⟨1803743, by rfl⟩ : syracuseStep 2404991 = 3607487) B3607487
theorem B8123327 : Blo 1603000 8123327 := bstep (se 1 (by rfl) ⟨6092495, by rfl⟩ : syracuseStep 8123327 = 12184991) B12184991
theorem B3609647 : Blo 1603000 3609647 := bstep (se 1 (by rfl) ⟨2707235, by rfl⟩ : syracuseStep 3609647 = 5414471) B5414471
theorem B2405711 : Blo 1603000 2405711 := bstep (se 1 (by rfl) ⟨1804283, by rfl⟩ : syracuseStep 2405711 = 3608567) B3608567
theorem B1603103 : Blo 1603000 1603103 := bstep (se 1 (by rfl) ⟨1202327, by rfl⟩ : syracuseStep 1603103 = 2404655) B2404655
theorem B2406215 : Blo 1603000 2406215 := bstep (se 1 (by rfl) ⟨1804661, by rfl⟩ : syracuseStep 2406215 = 3609323) B3609323
theorem B6854503 : Blo 1603000 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B12179645 : Blo 1603000 12179645 := bstep (se 3 (by rfl) ⟨2283683, by rfl⟩ : syracuseStep 12179645 = 4567367) B4567367
theorem B1603911 : Blo 1603000 1603911 := bstep (se 1 (by rfl) ⟨1202933, by rfl⟩ : syracuseStep 1603911 = 2405867) B2405867
theorem B12180131 : Blo 1603000 12180131 := bstep (se 1 (by rfl) ⟨9135098, by rfl⟩ : syracuseStep 12180131 = 18270197) B18270197
theorem B1604379 : Blo 1603000 1604379 := bstep (se 1 (by rfl) ⟨1203284, by rfl⟩ : syracuseStep 1604379 = 2406569) B2406569
theorem B3087271 : Blo 1603000 3087271 := bstep (se 1 (by rfl) ⟨2315453, by rfl⟩ : syracuseStep 3087271 = 4630907) B4630907
theorem B2407337 : Blo 1603000 2407337 := bstep (se 2 (by rfl) ⟨902751, by rfl⟩ : syracuseStep 2407337 = 1805503) B1805503
theorem B12344345 : Blo 1603000 12344345 := bstep (se 2 (by rfl) ⟨4629129, by rfl⟩ : syracuseStep 12344345 = 9258259) B9258259
theorem B135322811 : Blo 1603000 135322811 := bstep (se 1 (by rfl) ⟨101492108, by rfl⟩ : syracuseStep 135322811 = 202984217) B202984217
theorem B6176359 : Blo 1603000 6176359 := bstep (se 1 (by rfl) ⟨4632269, by rfl⟩ : syracuseStep 6176359 = 9264539) B9264539
theorem B5415551 : Blo 1603000 5415551 := bstep (se 1 (by rfl) ⟨4061663, by rfl⟩ : syracuseStep 5415551 = 8123327) B8123327
theorem B8225947 : Blo 1603000 8225947 := bstep (se 1 (by rfl) ⟨6169460, by rfl⟩ : syracuseStep 8225947 = 12338921) B12338921
theorem B8119763 : Blo 1603000 8119763 := bstep (se 1 (by rfl) ⟨6089822, by rfl⟩ : syracuseStep 8119763 = 12179645) B12179645
theorem B8120087 : Blo 1603000 8120087 := bstep (se 1 (by rfl) ⟨6090065, by rfl⟩ : syracuseStep 8120087 = 12180131) B12180131
theorem B6088729 : Blo 1603000 6088729 := bstep (se 2 (by rfl) ⟨2283273, by rfl⟩ : syracuseStep 6088729 = 4566547) B4566547
theorem B8235145 : Blo 1603000 8235145 := bstep (se 2 (by rfl) ⟨3088179, by rfl⟩ : syracuseStep 8235145 = 6176359) B6176359
theorem B2705663 : Blo 1603000 2705663 := bstep (se 1 (by rfl) ⟨2029247, by rfl⟩ : syracuseStep 2705663 = 4058495) B4058495
theorem B19509011 : Blo 1603000 19509011 := bstep (se 1 (by rfl) ⟨14631758, by rfl⟩ : syracuseStep 19509011 = 29263517) B29263517
theorem B2404535 : Blo 1603000 2404535 := bstep (se 1 (by rfl) ⟨1803401, by rfl⟩ : syracuseStep 2404535 = 3606803) B3606803
theorem B2404955 : Blo 1603000 2404955 := bstep (se 1 (by rfl) ⟨1803716, by rfl⟩ : syracuseStep 2404955 = 3607433) B3607433
theorem B8229563 : Blo 1603000 8229563 := bstep (se 1 (by rfl) ⟨6172172, by rfl⟩ : syracuseStep 8229563 = 12344345) B12344345
theorem B90215207 : Blo 1603000 90215207 := bstep (se 1 (by rfl) ⟨67661405, by rfl⟩ : syracuseStep 90215207 = 135322811) B135322811
theorem B37057607 : Blo 1603000 37057607 := bstep (se 1 (by rfl) ⟨27793205, by rfl⟩ : syracuseStep 37057607 = 55586411) B55586411
theorem B9139337 : Blo 1603000 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B2405735 : Blo 1603000 2405735 := bstep (se 1 (by rfl) ⟨1804301, by rfl⟩ : syracuseStep 2405735 = 3608603) B3608603
theorem B112637303 : Blo 1603000 112637303 := bstep (se 1 (by rfl) ⟨84477977, by rfl⟩ : syracuseStep 112637303 = 168955955) B168955955
theorem B4060651 : Blo 1603000 4060651 := bstep (se 1 (by rfl) ⟨3045488, by rfl⟩ : syracuseStep 4060651 = 6090977) B6090977
theorem B1603327 : Blo 1603000 1603327 := bstep (se 1 (by rfl) ⟨1202495, by rfl⟩ : syracuseStep 1603327 = 2404991) B2404991
theorem B2406431 : Blo 1603000 2406431 := bstep (se 1 (by rfl) ⟨1804823, by rfl⟩ : syracuseStep 2406431 = 3609647) B3609647
theorem B1603807 : Blo 1603000 1603807 := bstep (se 1 (by rfl) ⟨1202855, by rfl⟩ : syracuseStep 1603807 = 2405711) B2405711
theorem B69359975 : Blo 1603000 69359975 := bstep (se 1 (by rfl) ⟨52019981, by rfl⟩ : syracuseStep 69359975 = 104039963) B104039963
theorem B2406905 : Blo 1603000 2406905 := bstep (se 2 (by rfl) ⟨902589, by rfl⟩ : syracuseStep 2406905 = 1805179) B1805179
theorem B1604143 : Blo 1603000 1604143 := bstep (se 1 (by rfl) ⟨1203107, by rfl⟩ : syracuseStep 1604143 = 2406215) B2406215
theorem B5135521 : Blo 1603000 5135521 := bstep (se 2 (by rfl) ⟨1925820, by rfl⟩ : syracuseStep 5135521 = 3851641) B3851641
theorem B39042233 : Blo 1603000 39042233 := bstep (se 2 (by rfl) ⟨14640837, by rfl⟩ : syracuseStep 39042233 = 29281675) B29281675
theorem B3710143 : Blo 1603000 3710143 := bstep (se 1 (by rfl) ⟨2782607, by rfl⟩ : syracuseStep 3710143 = 5565215) B5565215
theorem B1604891 : Blo 1603000 1604891 := bstep (se 1 (by rfl) ⟨1203668, by rfl⟩ : syracuseStep 1604891 = 2407337) B2407337
theorem B16465445 : Blo 1603000 16465445 := bstep (se 4 (by rfl) ⟨1543635, by rfl⟩ : syracuseStep 16465445 = 3087271) B3087271
theorem B93806261 : Blo 1603000 93806261 := bstep (se 5 (by rfl) ⟨4397168, by rfl⟩ : syracuseStep 93806261 = 8794337) B8794337
theorem B8118305 : Blo 1603000 8118305 := bstep (se 2 (by rfl) ⟨3044364, by rfl⟩ : syracuseStep 8118305 = 6088729) B6088729
theorem B1803775 : Blo 1603000 1803775 := bstep (se 1 (by rfl) ⟨1352831, by rfl⟩ : syracuseStep 1803775 = 2705663) B2705663
theorem B26028155 : Blo 1603000 26028155 := bstep (se 1 (by rfl) ⟨19521116, by rfl⟩ : syracuseStep 26028155 = 39042233) B39042233
theorem B10980193 : Blo 1603000 10980193 := bstep (se 2 (by rfl) ⟨4117572, by rfl⟩ : syracuseStep 10980193 = 8235145) B8235145
theorem B3610367 : Blo 1603000 3610367 := bstep (se 1 (by rfl) ⟨2707775, by rfl⟩ : syracuseStep 3610367 = 5415551) B5415551
theorem B75091535 : Blo 1603000 75091535 := bstep (se 1 (by rfl) ⟨56318651, by rfl⟩ : syracuseStep 75091535 = 112637303) B112637303
theorem B19787429 : Blo 1603000 19787429 := bstep (se 4 (by rfl) ⟨1855071, by rfl⟩ : syracuseStep 19787429 = 3710143) B3710143
theorem B46239983 : Blo 1603000 46239983 := bstep (se 1 (by rfl) ⟨34679987, by rfl⟩ : syracuseStep 46239983 = 69359975) B69359975
theorem B13006007 : Blo 1603000 13006007 := bstep (se 1 (by rfl) ⟨9754505, by rfl⟩ : syracuseStep 13006007 = 19509011) B19509011
theorem B1603023 : Blo 1603000 1603023 := bstep (se 1 (by rfl) ⟨1202267, by rfl⟩ : syracuseStep 1603023 = 2404535) B2404535
theorem B1603303 : Blo 1603000 1603303 := bstep (se 1 (by rfl) ⟨1202477, by rfl⟩ : syracuseStep 1603303 = 2404955) B2404955
theorem B5486375 : Blo 1603000 5486375 := bstep (se 1 (by rfl) ⟨4114781, by rfl⟩ : syracuseStep 5486375 = 8229563) B8229563
theorem B60143471 : Blo 1603000 60143471 := bstep (se 1 (by rfl) ⟨45107603, by rfl⟩ : syracuseStep 60143471 = 90215207) B90215207
theorem B24705071 : Blo 1603000 24705071 := bstep (se 1 (by rfl) ⟨18528803, by rfl⟩ : syracuseStep 24705071 = 37057607) B37057607
theorem B6092891 : Blo 1603000 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B1603823 : Blo 1603000 1603823 := bstep (se 1 (by rfl) ⟨1202867, by rfl⟩ : syracuseStep 1603823 = 2405735) B2405735
theorem B5413175 : Blo 1603000 5413175 := bstep (se 1 (by rfl) ⟨4059881, by rfl⟩ : syracuseStep 5413175 = 8119763) B8119763
theorem B5413391 : Blo 1603000 5413391 := bstep (se 1 (by rfl) ⟨4060043, by rfl⟩ : syracuseStep 5413391 = 8120087) B8120087
theorem B1604287 : Blo 1603000 1604287 := bstep (se 1 (by rfl) ⟨1203215, by rfl⟩ : syracuseStep 1604287 = 2406431) B2406431
theorem B10967929 : Blo 1603000 10967929 := bstep (se 2 (by rfl) ⟨4112973, by rfl⟩ : syracuseStep 10967929 = 8225947) B8225947
theorem B6847361 : Blo 1603000 6847361 := bstep (se 2 (by rfl) ⟨2567760, by rfl⟩ : syracuseStep 6847361 = 5135521) B5135521
theorem B1604603 : Blo 1603000 1604603 := bstep (se 1 (by rfl) ⟨1203452, by rfl⟩ : syracuseStep 1604603 = 2406905) B2406905
theorem B5414201 : Blo 1603000 5414201 := bstep (se 2 (by rfl) ⟨2030325, by rfl⟩ : syracuseStep 5414201 = 4060651) B4060651
theorem B10976963 : Blo 1603000 10976963 := bstep (se 1 (by rfl) ⟨8232722, by rfl⟩ : syracuseStep 10976963 = 16465445) B16465445
theorem B62537507 : Blo 1603000 62537507 := bstep (se 1 (by rfl) ⟨46903130, by rfl⟩ : syracuseStep 62537507 = 93806261) B93806261
theorem B30826655 : Blo 1603000 30826655 := bstep (se 1 (by rfl) ⟨23119991, by rfl⟩ : syracuseStep 30826655 = 46239983) B46239983
theorem B14640257 : Blo 1603000 14640257 := bstep (se 2 (by rfl) ⟨5490096, by rfl⟩ : syracuseStep 14640257 = 10980193) B10980193
theorem B17352103 : Blo 1603000 17352103 := bstep (se 1 (by rfl) ⟨13014077, by rfl⟩ : syracuseStep 17352103 = 26028155) B26028155
theorem B4564907 : Blo 1603000 4564907 := bstep (se 1 (by rfl) ⟨3423680, by rfl⟩ : syracuseStep 4564907 = 6847361) B6847361
theorem B13191619 : Blo 1603000 13191619 := bstep (se 1 (by rfl) ⟨9893714, by rfl⟩ : syracuseStep 13191619 = 19787429) B19787429
theorem B41691671 : Blo 1603000 41691671 := bstep (se 1 (by rfl) ⟨31268753, by rfl⟩ : syracuseStep 41691671 = 62537507) B62537507
theorem B8670671 : Blo 1603000 8670671 := bstep (se 1 (by rfl) ⟨6503003, by rfl⟩ : syracuseStep 8670671 = 13006007) B13006007
theorem B3657583 : Blo 1603000 3657583 := bstep (se 1 (by rfl) ⟨2743187, by rfl⟩ : syracuseStep 3657583 = 5486375) B5486375
theorem B40095647 : Blo 1603000 40095647 := bstep (se 1 (by rfl) ⟨30071735, by rfl⟩ : syracuseStep 40095647 = 60143471) B60143471
theorem B16470047 : Blo 1603000 16470047 := bstep (se 1 (by rfl) ⟨12352535, by rfl⟩ : syracuseStep 16470047 = 24705071) B24705071
theorem B3608783 : Blo 1603000 3608783 := bstep (se 1 (by rfl) ⟨2706587, by rfl⟩ : syracuseStep 3608783 = 5413175) B5413175
theorem B3608927 : Blo 1603000 3608927 := bstep (se 1 (by rfl) ⟨2706695, by rfl⟩ : syracuseStep 3608927 = 5413391) B5413391
theorem B58495621 : Blo 1603000 58495621 := bstep (se 4 (by rfl) ⟨5483964, by rfl⟩ : syracuseStep 58495621 = 10967929) B10967929
theorem B2405033 : Blo 1603000 2405033 := bstep (se 2 (by rfl) ⟨901887, by rfl⟩ : syracuseStep 2405033 = 1803775) B1803775
theorem B3609467 : Blo 1603000 3609467 := bstep (se 1 (by rfl) ⟨2707100, by rfl⟩ : syracuseStep 3609467 = 5414201) B5414201
theorem B5412203 : Blo 1603000 5412203 := bstep (se 1 (by rfl) ⟨4059152, by rfl⟩ : syracuseStep 5412203 = 8118305) B8118305
theorem B2406911 : Blo 1603000 2406911 := bstep (se 1 (by rfl) ⟨1805183, by rfl⟩ : syracuseStep 2406911 = 3610367) B3610367
theorem B4061927 : Blo 1603000 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B117087605 : Blo 1603000 117087605 := bstep (se 5 (by rfl) ⟨5488481, by rfl⟩ : syracuseStep 117087605 = 10976963) B10976963
theorem B50061023 : Blo 1603000 50061023 := bstep (se 1 (by rfl) ⟨37545767, by rfl⟩ : syracuseStep 50061023 = 75091535) B75091535
theorem B17588825 : Blo 1603000 17588825 := bstep (se 2 (by rfl) ⟨6595809, by rfl⟩ : syracuseStep 17588825 = 13191619) B13191619
theorem B23136137 : Blo 1603000 23136137 := bstep (se 2 (by rfl) ⟨8676051, by rfl⟩ : syracuseStep 23136137 = 17352103) B17352103
theorem B4876777 : Blo 1603000 4876777 := bstep (se 2 (by rfl) ⟨1828791, by rfl⟩ : syracuseStep 4876777 = 3657583) B3657583
theorem B10980031 : Blo 1603000 10980031 := bstep (se 1 (by rfl) ⟨8235023, by rfl⟩ : syracuseStep 10980031 = 16470047) B16470047
theorem B9760171 : Blo 1603000 9760171 := bstep (se 1 (by rfl) ⟨7320128, by rfl⟩ : syracuseStep 9760171 = 14640257) B14640257
theorem B3608135 : Blo 1603000 3608135 := bstep (se 1 (by rfl) ⟨2706101, by rfl⟩ : syracuseStep 3608135 = 5412203) B5412203
theorem B3043271 : Blo 1603000 3043271 := bstep (se 1 (by rfl) ⟨2282453, by rfl⟩ : syracuseStep 3043271 = 4564907) B4564907
theorem B2707951 : Blo 1603000 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B78058403 : Blo 1603000 78058403 := bstep (se 1 (by rfl) ⟨58543802, by rfl⟩ : syracuseStep 78058403 = 117087605) B117087605
theorem B5780447 : Blo 1603000 5780447 := bstep (se 1 (by rfl) ⟨4335335, by rfl⟩ : syracuseStep 5780447 = 8670671) B8670671
theorem B20551103 : Blo 1603000 20551103 := bstep (se 1 (by rfl) ⟨15413327, by rfl⟩ : syracuseStep 20551103 = 30826655) B30826655
theorem B2405855 : Blo 1603000 2405855 := bstep (se 1 (by rfl) ⟨1804391, by rfl⟩ : syracuseStep 2405855 = 3608783) B3608783
theorem B2405951 : Blo 1603000 2405951 := bstep (se 1 (by rfl) ⟨1804463, by rfl⟩ : syracuseStep 2405951 = 3608927) B3608927
theorem B1603355 : Blo 1603000 1603355 := bstep (se 1 (by rfl) ⟨1202516, by rfl⟩ : syracuseStep 1603355 = 2405033) B2405033
theorem B2406311 : Blo 1603000 2406311 := bstep (se 1 (by rfl) ⟨1804733, by rfl⟩ : syracuseStep 2406311 = 3609467) B3609467
theorem B77994161 : Blo 1603000 77994161 := bstep (se 2 (by rfl) ⟨29247810, by rfl⟩ : syracuseStep 77994161 = 58495621) B58495621
theorem B1604607 : Blo 1603000 1604607 := bstep (se 1 (by rfl) ⟨1203455, by rfl⟩ : syracuseStep 1604607 = 2406911) B2406911
theorem B27794447 : Blo 1603000 27794447 := bstep (se 1 (by rfl) ⟨20845835, by rfl⟩ : syracuseStep 27794447 = 41691671) B41691671
theorem B33374015 : Blo 1603000 33374015 := bstep (se 1 (by rfl) ⟨25030511, by rfl⟩ : syracuseStep 33374015 = 50061023) B50061023
theorem B26730431 : Blo 1603000 26730431 := bstep (se 1 (by rfl) ⟨20047823, by rfl⟩ : syracuseStep 26730431 = 40095647) B40095647
theorem B14640041 : Blo 1603000 14640041 := bstep (se 2 (by rfl) ⟨5490015, by rfl⟩ : syracuseStep 14640041 = 10980031) B10980031
theorem B51996107 : Blo 1603000 51996107 := bstep (se 1 (by rfl) ⟨38997080, by rfl⟩ : syracuseStep 51996107 = 77994161) B77994161
theorem B17820287 : Blo 1603000 17820287 := bstep (se 1 (by rfl) ⟨13365215, by rfl⟩ : syracuseStep 17820287 = 26730431) B26730431
theorem B11725883 : Blo 1603000 11725883 := bstep (se 1 (by rfl) ⟨8794412, by rfl⟩ : syracuseStep 11725883 = 17588825) B17588825
theorem B52038935 : Blo 1603000 52038935 := bstep (se 1 (by rfl) ⟨39029201, by rfl⟩ : syracuseStep 52038935 = 78058403) B78058403
theorem B3853631 : Blo 1603000 3853631 := bstep (se 1 (by rfl) ⟨2890223, by rfl⟩ : syracuseStep 3853631 = 5780447) B5780447
theorem B13700735 : Blo 1603000 13700735 := bstep (se 1 (by rfl) ⟨10275551, by rfl⟩ : syracuseStep 13700735 = 20551103) B20551103
theorem B13013561 : Blo 1603000 13013561 := bstep (se 2 (by rfl) ⟨4880085, by rfl⟩ : syracuseStep 13013561 = 9760171) B9760171
theorem B2405423 : Blo 1603000 2405423 := bstep (se 1 (by rfl) ⟨1804067, by rfl⟩ : syracuseStep 2405423 = 3608135) B3608135
theorem B8115389 : Blo 1603000 8115389 := bstep (se 3 (by rfl) ⟨1521635, by rfl⟩ : syracuseStep 8115389 = 3043271) B3043271
theorem B6502369 : Blo 1603000 6502369 := bstep (se 2 (by rfl) ⟨2438388, by rfl⟩ : syracuseStep 6502369 = 4876777) B4876777
theorem B3610601 : Blo 1603000 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B1603903 : Blo 1603000 1603903 := bstep (se 1 (by rfl) ⟨1202927, by rfl⟩ : syracuseStep 1603903 = 2405855) B2405855
theorem B1603967 : Blo 1603000 1603967 := bstep (se 1 (by rfl) ⟨1202975, by rfl⟩ : syracuseStep 1603967 = 2405951) B2405951
theorem B15424091 : Blo 1603000 15424091 := bstep (se 1 (by rfl) ⟨11568068, by rfl⟩ : syracuseStep 15424091 = 23136137) B23136137
theorem B1604207 : Blo 1603000 1604207 := bstep (se 1 (by rfl) ⟨1203155, by rfl⟩ : syracuseStep 1604207 = 2406311) B2406311
theorem B18529631 : Blo 1603000 18529631 := bstep (se 1 (by rfl) ⟨13897223, by rfl⟩ : syracuseStep 18529631 = 27794447) B27794447
theorem B22249343 : Blo 1603000 22249343 := bstep (se 1 (by rfl) ⟨16687007, by rfl⟩ : syracuseStep 22249343 = 33374015) B33374015
theorem B8675707 : Blo 1603000 8675707 := bstep (se 1 (by rfl) ⟨6506780, by rfl⟩ : syracuseStep 8675707 = 13013561) B13013561
theorem B10282727 : Blo 1603000 10282727 := bstep (se 1 (by rfl) ⟨7712045, by rfl⟩ : syracuseStep 10282727 = 15424091) B15424091
theorem B11880191 : Blo 1603000 11880191 := bstep (se 1 (by rfl) ⟨8910143, by rfl⟩ : syracuseStep 11880191 = 17820287) B17820287
theorem B7817255 : Blo 1603000 7817255 := bstep (se 1 (by rfl) ⟨5862941, by rfl⟩ : syracuseStep 7817255 = 11725883) B11725883
theorem B8669825 : Blo 1603000 8669825 := bstep (se 2 (by rfl) ⟨3251184, by rfl⟩ : syracuseStep 8669825 = 6502369) B6502369
theorem B9760027 : Blo 1603000 9760027 := bstep (se 1 (by rfl) ⟨7320020, by rfl⟩ : syracuseStep 9760027 = 14640041) B14640041
theorem B5410259 : Blo 1603000 5410259 := bstep (se 1 (by rfl) ⟨4057694, by rfl⟩ : syracuseStep 5410259 = 8115389) B8115389
theorem B34664071 : Blo 1603000 34664071 := bstep (se 1 (by rfl) ⟨25998053, by rfl⟩ : syracuseStep 34664071 = 51996107) B51996107
theorem B2569087 : Blo 1603000 2569087 := bstep (se 1 (by rfl) ⟨1926815, by rfl⟩ : syracuseStep 2569087 = 3853631) B3853631
theorem B14832895 : Blo 1603000 14832895 := bstep (se 1 (by rfl) ⟨11124671, by rfl⟩ : syracuseStep 14832895 = 22249343) B22249343
theorem B1603615 : Blo 1603000 1603615 := bstep (se 1 (by rfl) ⟨1202711, by rfl⟩ : syracuseStep 1603615 = 2405423) B2405423
theorem B2407067 : Blo 1603000 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B34692623 : Blo 1603000 34692623 := bstep (se 1 (by rfl) ⟨26019467, by rfl⟩ : syracuseStep 34692623 = 52038935) B52038935
theorem B12353087 : Blo 1603000 12353087 := bstep (se 1 (by rfl) ⟨9264815, by rfl⟩ : syracuseStep 12353087 = 18529631) B18529631
theorem B9133823 : Blo 1603000 9133823 := bstep (se 1 (by rfl) ⟨6850367, by rfl⟩ : syracuseStep 9133823 = 13700735) B13700735
theorem B11567609 : Blo 1603000 11567609 := bstep (se 2 (by rfl) ⟨4337853, by rfl⟩ : syracuseStep 11567609 = 8675707) B8675707
theorem B5211503 : Blo 1603000 5211503 := bstep (se 1 (by rfl) ⟨3908627, by rfl⟩ : syracuseStep 5211503 = 7817255) B7817255
theorem B32941565 : Blo 1603000 32941565 := bstep (se 3 (by rfl) ⟨6176543, by rfl⟩ : syracuseStep 32941565 = 12353087) B12353087
theorem B19777193 : Blo 1603000 19777193 := bstep (se 2 (by rfl) ⟨7416447, by rfl⟩ : syracuseStep 19777193 = 14832895) B14832895
theorem B27420605 : Blo 1603000 27420605 := bstep (se 3 (by rfl) ⟨5141363, by rfl⟩ : syracuseStep 27420605 = 10282727) B10282727
theorem B3606839 : Blo 1603000 3606839 := bstep (se 1 (by rfl) ⟨2705129, by rfl⟩ : syracuseStep 3606839 = 5410259) B5410259
theorem B23128415 : Blo 1603000 23128415 := bstep (se 1 (by rfl) ⟨17346311, by rfl⟩ : syracuseStep 23128415 = 34692623) B34692623
theorem B6089215 : Blo 1603000 6089215 := bstep (se 1 (by rfl) ⟨4566911, by rfl⟩ : syracuseStep 6089215 = 9133823) B9133823
theorem B13013369 : Blo 1603000 13013369 := bstep (se 2 (by rfl) ⟨4880013, by rfl⟩ : syracuseStep 13013369 = 9760027) B9760027
theorem B5779883 : Blo 1603000 5779883 := bstep (se 1 (by rfl) ⟨4334912, by rfl⟩ : syracuseStep 5779883 = 8669825) B8669825
theorem B13701797 : Blo 1603000 13701797 := bstep (se 4 (by rfl) ⟨1284543, by rfl⟩ : syracuseStep 13701797 = 2569087) B2569087
theorem B7920127 : Blo 1603000 7920127 := bstep (se 1 (by rfl) ⟨5940095, by rfl⟩ : syracuseStep 7920127 = 11880191) B11880191
theorem B1604711 : Blo 1603000 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B46218761 : Blo 1603000 46218761 := bstep (se 2 (by rfl) ⟨17332035, by rfl⟩ : syracuseStep 46218761 = 34664071) B34664071
theorem B8675579 : Blo 1603000 8675579 := bstep (se 1 (by rfl) ⟨6506684, by rfl⟩ : syracuseStep 8675579 = 13013369) B13013369
theorem B9134531 : Blo 1603000 9134531 := bstep (se 1 (by rfl) ⟨6850898, by rfl⟩ : syracuseStep 9134531 = 13701797) B13701797
theorem B8118953 : Blo 1603000 8118953 := bstep (se 2 (by rfl) ⟨3044607, by rfl⟩ : syracuseStep 8118953 = 6089215) B6089215
theorem B10560169 : Blo 1603000 10560169 := bstep (se 2 (by rfl) ⟨3960063, by rfl⟩ : syracuseStep 10560169 = 7920127) B7920127
theorem B3474335 : Blo 1603000 3474335 := bstep (se 1 (by rfl) ⟨2605751, by rfl⟩ : syracuseStep 3474335 = 5211503) B5211503
theorem B15418943 : Blo 1603000 15418943 := bstep (se 1 (by rfl) ⟨11564207, by rfl⟩ : syracuseStep 15418943 = 23128415) B23128415
theorem B30812507 : Blo 1603000 30812507 := bstep (se 1 (by rfl) ⟨23109380, by rfl⟩ : syracuseStep 30812507 = 46218761) B46218761
theorem B3853255 : Blo 1603000 3853255 := bstep (se 1 (by rfl) ⟨2889941, by rfl⟩ : syracuseStep 3853255 = 5779883) B5779883
theorem B7711739 : Blo 1603000 7711739 := bstep (se 1 (by rfl) ⟨5783804, by rfl⟩ : syracuseStep 7711739 = 11567609) B11567609
theorem B13184795 : Blo 1603000 13184795 := bstep (se 1 (by rfl) ⟨9888596, by rfl⟩ : syracuseStep 13184795 = 19777193) B19777193
theorem B18280403 : Blo 1603000 18280403 := bstep (se 1 (by rfl) ⟨13710302, by rfl⟩ : syracuseStep 18280403 = 27420605) B27420605
theorem B2404559 : Blo 1603000 2404559 := bstep (se 1 (by rfl) ⟨1803419, by rfl⟩ : syracuseStep 2404559 = 3606839) B3606839
theorem B21961043 : Blo 1603000 21961043 := bstep (se 1 (by rfl) ⟨16470782, by rfl⟩ : syracuseStep 21961043 = 32941565) B32941565
theorem B5783719 : Blo 1603000 5783719 := bstep (se 1 (by rfl) ⟨4337789, by rfl⟩ : syracuseStep 5783719 = 8675579) B8675579
theorem B5137673 : Blo 1603000 5137673 := bstep (se 2 (by rfl) ⟨1926627, by rfl⟩ : syracuseStep 5137673 = 3853255) B3853255
theorem B14640695 : Blo 1603000 14640695 := bstep (se 1 (by rfl) ⟨10980521, by rfl⟩ : syracuseStep 14640695 = 21961043) B21961043
theorem B6089687 : Blo 1603000 6089687 := bstep (se 1 (by rfl) ⟨4567265, by rfl⟩ : syracuseStep 6089687 = 9134531) B9134531
theorem B20541671 : Blo 1603000 20541671 := bstep (se 1 (by rfl) ⟨15406253, by rfl⟩ : syracuseStep 20541671 = 30812507) B30812507
theorem B5141159 : Blo 1603000 5141159 := bstep (se 1 (by rfl) ⟨3855869, by rfl⟩ : syracuseStep 5141159 = 7711739) B7711739
theorem B12186935 : Blo 1603000 12186935 := bstep (se 1 (by rfl) ⟨9140201, by rfl⟩ : syracuseStep 12186935 = 18280403) B18280403
theorem B1603039 : Blo 1603000 1603039 := bstep (se 1 (by rfl) ⟨1202279, by rfl⟩ : syracuseStep 1603039 = 2404559) B2404559
theorem B5412635 : Blo 1603000 5412635 := bstep (se 1 (by rfl) ⟨4059476, by rfl⟩ : syracuseStep 5412635 = 8118953) B8118953
theorem B2316223 : Blo 1603000 2316223 := bstep (se 1 (by rfl) ⟨1737167, by rfl⟩ : syracuseStep 2316223 = 3474335) B3474335
theorem B14080225 : Blo 1603000 14080225 := bstep (se 2 (by rfl) ⟨5280084, by rfl⟩ : syracuseStep 14080225 = 10560169) B10560169
theorem B10279295 : Blo 1603000 10279295 := bstep (se 1 (by rfl) ⟨7709471, by rfl⟩ : syracuseStep 10279295 = 15418943) B15418943
theorem B35159453 : Blo 1603000 35159453 := bstep (se 3 (by rfl) ⟨6592397, by rfl⟩ : syracuseStep 35159453 = 13184795) B13184795
theorem B23439635 : Blo 1603000 23439635 := bstep (se 1 (by rfl) ⟨17579726, by rfl⟩ : syracuseStep 23439635 = 35159453) B35159453
theorem B7711625 : Blo 1603000 7711625 := bstep (se 2 (by rfl) ⟨2891859, by rfl⟩ : syracuseStep 7711625 = 5783719) B5783719
theorem B3427439 : Blo 1603000 3427439 := bstep (se 1 (by rfl) ⟨2570579, by rfl⟩ : syracuseStep 3427439 = 5141159) B5141159
theorem B13700461 : Blo 1603000 13700461 := bstep (se 3 (by rfl) ⟨2568836, by rfl⟩ : syracuseStep 13700461 = 5137673) B5137673
theorem B9760463 : Blo 1603000 9760463 := bstep (se 1 (by rfl) ⟨7320347, by rfl⟩ : syracuseStep 9760463 = 14640695) B14640695
theorem B3608423 : Blo 1603000 3608423 := bstep (se 1 (by rfl) ⟨2706317, by rfl⟩ : syracuseStep 3608423 = 5412635) B5412635
theorem B6852863 : Blo 1603000 6852863 := bstep (se 1 (by rfl) ⟨5139647, by rfl⟩ : syracuseStep 6852863 = 10279295) B10279295
theorem B4059791 : Blo 1603000 4059791 := bstep (se 1 (by rfl) ⟨3044843, by rfl⟩ : syracuseStep 4059791 = 6089687) B6089687
theorem B13694447 : Blo 1603000 13694447 := bstep (se 1 (by rfl) ⟨10270835, by rfl⟩ : syracuseStep 13694447 = 20541671) B20541671
theorem B18773633 : Blo 1603000 18773633 := bstep (se 2 (by rfl) ⟨7040112, by rfl⟩ : syracuseStep 18773633 = 14080225) B14080225
theorem B8124623 : Blo 1603000 8124623 := bstep (se 1 (by rfl) ⟨6093467, by rfl⟩ : syracuseStep 8124623 = 12186935) B12186935
theorem B3088297 : Blo 1603000 3088297 := bstep (se 2 (by rfl) ⟨1158111, by rfl⟩ : syracuseStep 3088297 = 2316223) B2316223
theorem B5416415 : Blo 1603000 5416415 := bstep (se 1 (by rfl) ⟨4062311, by rfl⟩ : syracuseStep 5416415 = 8124623) B8124623
theorem B6506975 : Blo 1603000 6506975 := bstep (se 1 (by rfl) ⟨4880231, by rfl⟩ : syracuseStep 6506975 = 9760463) B9760463
theorem B2706527 : Blo 1603000 2706527 := bstep (se 1 (by rfl) ⟨2029895, by rfl⟩ : syracuseStep 2706527 = 4059791) B4059791
theorem B9129631 : Blo 1603000 9129631 := bstep (se 1 (by rfl) ⟨6847223, by rfl⟩ : syracuseStep 9129631 = 13694447) B13694447
theorem B15626423 : Blo 1603000 15626423 := bstep (se 1 (by rfl) ⟨11719817, by rfl⟩ : syracuseStep 15626423 = 23439635) B23439635
theorem B5141083 : Blo 1603000 5141083 := bstep (se 1 (by rfl) ⟨3855812, by rfl⟩ : syracuseStep 5141083 = 7711625) B7711625
theorem B4117729 : Blo 1603000 4117729 := bstep (se 2 (by rfl) ⟨1544148, by rfl⟩ : syracuseStep 4117729 = 3088297) B3088297
theorem B2405615 : Blo 1603000 2405615 := bstep (se 1 (by rfl) ⟨1804211, by rfl⟩ : syracuseStep 2405615 = 3608423) B3608423
theorem B4568575 : Blo 1603000 4568575 := bstep (se 1 (by rfl) ⟨3426431, by rfl⟩ : syracuseStep 4568575 = 6852863) B6852863
theorem B9139837 : Blo 1603000 9139837 := bstep (se 3 (by rfl) ⟨1713719, by rfl⟩ : syracuseStep 9139837 = 3427439) B3427439
theorem B12515755 : Blo 1603000 12515755 := bstep (se 1 (by rfl) ⟨9386816, by rfl⟩ : syracuseStep 12515755 = 18773633) B18773633
theorem B18267281 : Blo 1603000 18267281 := bstep (se 2 (by rfl) ⟨6850230, by rfl⟩ : syracuseStep 18267281 = 13700461) B13700461
theorem B16687673 : Blo 1603000 16687673 := bstep (se 2 (by rfl) ⟨6257877, by rfl⟩ : syracuseStep 16687673 = 12515755) B12515755
theorem B5490305 : Blo 1603000 5490305 := bstep (se 2 (by rfl) ⟨2058864, by rfl⟩ : syracuseStep 5490305 = 4117729) B4117729
theorem B1804351 : Blo 1603000 1804351 := bstep (se 1 (by rfl) ⟨1353263, by rfl⟩ : syracuseStep 1804351 = 2706527) B2706527
theorem B4337983 : Blo 1603000 4337983 := bstep (se 1 (by rfl) ⟨3253487, by rfl⟩ : syracuseStep 4337983 = 6506975) B6506975
theorem B6091433 : Blo 1603000 6091433 := bstep (se 2 (by rfl) ⟨2284287, by rfl⟩ : syracuseStep 6091433 = 4568575) B4568575
theorem B12178187 : Blo 1603000 12178187 := bstep (se 1 (by rfl) ⟨9133640, by rfl⟩ : syracuseStep 12178187 = 18267281) B18267281
theorem B12186449 : Blo 1603000 12186449 := bstep (se 2 (by rfl) ⟨4569918, by rfl⟩ : syracuseStep 12186449 = 9139837) B9139837
theorem B10417615 : Blo 1603000 10417615 := bstep (se 1 (by rfl) ⟨7813211, by rfl⟩ : syracuseStep 10417615 = 15626423) B15626423
theorem B6854777 : Blo 1603000 6854777 := bstep (se 2 (by rfl) ⟨2570541, by rfl⟩ : syracuseStep 6854777 = 5141083) B5141083
theorem B1603743 : Blo 1603000 1603743 := bstep (se 1 (by rfl) ⟨1202807, by rfl⟩ : syracuseStep 1603743 = 2405615) B2405615
theorem B3610943 : Blo 1603000 3610943 := bstep (se 1 (by rfl) ⟨2708207, by rfl⟩ : syracuseStep 3610943 = 5416415) B5416415
theorem B12172841 : Blo 1603000 12172841 := bstep (se 2 (by rfl) ⟨4564815, by rfl⟩ : syracuseStep 12172841 = 9129631) B9129631
theorem B11125115 : Blo 1603000 11125115 := bstep (se 1 (by rfl) ⟨8343836, by rfl⟩ : syracuseStep 11125115 = 16687673) B16687673
theorem B5783977 : Blo 1603000 5783977 := bstep (se 2 (by rfl) ⟨2168991, by rfl⟩ : syracuseStep 5783977 = 4337983) B4337983
theorem B8118791 : Blo 1603000 8118791 := bstep (se 1 (by rfl) ⟨6089093, by rfl⟩ : syracuseStep 8118791 = 12178187) B12178187
theorem B55560613 : Blo 1603000 55560613 := bstep (se 4 (by rfl) ⟨5208807, by rfl⟩ : syracuseStep 55560613 = 10417615) B10417615
theorem B8115227 : Blo 1603000 8115227 := bstep (se 1 (by rfl) ⟨6086420, by rfl⟩ : syracuseStep 8115227 = 12172841) B12172841
theorem B2405801 : Blo 1603000 2405801 := bstep (se 2 (by rfl) ⟨902175, by rfl⟩ : syracuseStep 2405801 = 1804351) B1804351
theorem B4060955 : Blo 1603000 4060955 := bstep (se 1 (by rfl) ⟨3045716, by rfl⟩ : syracuseStep 4060955 = 6091433) B6091433
theorem B8124299 : Blo 1603000 8124299 := bstep (se 1 (by rfl) ⟨6093224, by rfl⟩ : syracuseStep 8124299 = 12186449) B12186449
theorem B3660203 : Blo 1603000 3660203 := bstep (se 1 (by rfl) ⟨2745152, by rfl⟩ : syracuseStep 3660203 = 5490305) B5490305
theorem B4569851 : Blo 1603000 4569851 := bstep (se 1 (by rfl) ⟨3427388, by rfl⟩ : syracuseStep 4569851 = 6854777) B6854777
theorem B2407295 : Blo 1603000 2407295 := bstep (se 1 (by rfl) ⟨1805471, by rfl⟩ : syracuseStep 2407295 = 3610943) B3610943
theorem B74080817 : Blo 1603000 74080817 := bstep (se 2 (by rfl) ⟨27780306, by rfl⟩ : syracuseStep 74080817 = 55560613) B55560613
theorem B5416199 : Blo 1603000 5416199 := bstep (se 1 (by rfl) ⟨4062149, by rfl⟩ : syracuseStep 5416199 = 8124299) B8124299
theorem B7416743 : Blo 1603000 7416743 := bstep (se 1 (by rfl) ⟨5562557, by rfl⟩ : syracuseStep 7416743 = 11125115) B11125115
theorem B5410151 : Blo 1603000 5410151 := bstep (se 1 (by rfl) ⟨4057613, by rfl⟩ : syracuseStep 5410151 = 8115227) B8115227
theorem B2707303 : Blo 1603000 2707303 := bstep (se 1 (by rfl) ⟨2030477, by rfl⟩ : syracuseStep 2707303 = 4060955) B4060955
theorem B30847877 : Blo 1603000 30847877 := bstep (se 4 (by rfl) ⟨2891988, by rfl⟩ : syracuseStep 30847877 = 5783977) B5783977
theorem B5412527 : Blo 1603000 5412527 := bstep (se 1 (by rfl) ⟨4059395, by rfl⟩ : syracuseStep 5412527 = 8118791) B8118791
theorem B1603867 : Blo 1603000 1603867 := bstep (se 1 (by rfl) ⟨1202900, by rfl⟩ : syracuseStep 1603867 = 2405801) B2405801
theorem B2440135 : Blo 1603000 2440135 := bstep (se 1 (by rfl) ⟨1830101, by rfl⟩ : syracuseStep 2440135 = 3660203) B3660203
theorem B3046567 : Blo 1603000 3046567 := bstep (se 1 (by rfl) ⟨2284925, by rfl⟩ : syracuseStep 3046567 = 4569851) B4569851
theorem B1604863 : Blo 1603000 1604863 := bstep (se 1 (by rfl) ⟨1203647, by rfl⟩ : syracuseStep 1604863 = 2407295) B2407295
theorem B3606767 : Blo 1603000 3606767 := bstep (se 1 (by rfl) ⟨2705075, by rfl⟩ : syracuseStep 3606767 = 5410151) B5410151
theorem B19777981 : Blo 1603000 19777981 := bstep (se 3 (by rfl) ⟨3708371, by rfl⟩ : syracuseStep 19777981 = 7416743) B7416743
theorem B20565251 : Blo 1603000 20565251 := bstep (se 1 (by rfl) ⟨15423938, by rfl⟩ : syracuseStep 20565251 = 30847877) B30847877
theorem B3608351 : Blo 1603000 3608351 := bstep (se 1 (by rfl) ⟨2706263, by rfl⟩ : syracuseStep 3608351 = 5412527) B5412527
theorem B13014053 : Blo 1603000 13014053 := bstep (se 4 (by rfl) ⟨1220067, by rfl⟩ : syracuseStep 13014053 = 2440135) B2440135
theorem B3609737 : Blo 1603000 3609737 := bstep (se 2 (by rfl) ⟨1353651, by rfl⟩ : syracuseStep 3609737 = 2707303) B2707303
theorem B49387211 : Blo 1603000 49387211 := bstep (se 1 (by rfl) ⟨37040408, by rfl⟩ : syracuseStep 49387211 = 74080817) B74080817
theorem B3610799 : Blo 1603000 3610799 := bstep (se 1 (by rfl) ⟨2708099, by rfl⟩ : syracuseStep 3610799 = 5416199) B5416199
theorem B4062089 : Blo 1603000 4062089 := bstep (se 2 (by rfl) ⟨1523283, by rfl⟩ : syracuseStep 4062089 = 3046567) B3046567
theorem B26370641 : Blo 1603000 26370641 := bstep (se 2 (by rfl) ⟨9888990, by rfl⟩ : syracuseStep 26370641 = 19777981) B19777981
theorem B8676035 : Blo 1603000 8676035 := bstep (se 1 (by rfl) ⟨6507026, by rfl⟩ : syracuseStep 8676035 = 13014053) B13014053
theorem B32924807 : Blo 1603000 32924807 := bstep (se 1 (by rfl) ⟨24693605, by rfl⟩ : syracuseStep 32924807 = 49387211) B49387211
theorem B2404511 : Blo 1603000 2404511 := bstep (se 1 (by rfl) ⟨1803383, by rfl⟩ : syracuseStep 2404511 = 3606767) B3606767
theorem B2708059 : Blo 1603000 2708059 := bstep (se 1 (by rfl) ⟨2031044, by rfl⟩ : syracuseStep 2708059 = 4062089) B4062089
theorem B13710167 : Blo 1603000 13710167 := bstep (se 1 (by rfl) ⟨10282625, by rfl⟩ : syracuseStep 13710167 = 20565251) B20565251
theorem B2405567 : Blo 1603000 2405567 := bstep (se 1 (by rfl) ⟨1804175, by rfl⟩ : syracuseStep 2405567 = 3608351) B3608351
theorem B2406491 : Blo 1603000 2406491 := bstep (se 1 (by rfl) ⟨1804868, by rfl⟩ : syracuseStep 2406491 = 3609737) B3609737
theorem B2407199 : Blo 1603000 2407199 := bstep (se 1 (by rfl) ⟨1805399, by rfl⟩ : syracuseStep 2407199 = 3610799) B3610799
theorem B5784023 : Blo 1603000 5784023 := bstep (se 1 (by rfl) ⟨4338017, by rfl⟩ : syracuseStep 5784023 = 8676035) B8676035
theorem B70321709 : Blo 1603000 70321709 := bstep (se 3 (by rfl) ⟨13185320, by rfl⟩ : syracuseStep 70321709 = 26370641) B26370641
theorem B21949871 : Blo 1603000 21949871 := bstep (se 1 (by rfl) ⟨16462403, by rfl⟩ : syracuseStep 21949871 = 32924807) B32924807
theorem B1603007 : Blo 1603000 1603007 := bstep (se 1 (by rfl) ⟨1202255, by rfl⟩ : syracuseStep 1603007 = 2404511) B2404511
theorem B9140111 : Blo 1603000 9140111 := bstep (se 1 (by rfl) ⟨6855083, by rfl⟩ : syracuseStep 9140111 = 13710167) B13710167
theorem B3610745 : Blo 1603000 3610745 := bstep (se 2 (by rfl) ⟨1354029, by rfl⟩ : syracuseStep 3610745 = 2708059) B2708059
theorem B1603711 : Blo 1603000 1603711 := bstep (se 1 (by rfl) ⟨1202783, by rfl⟩ : syracuseStep 1603711 = 2405567) B2405567
theorem B1604327 : Blo 1603000 1604327 := bstep (se 1 (by rfl) ⟨1203245, by rfl⟩ : syracuseStep 1604327 = 2406491) B2406491
theorem B1604799 : Blo 1603000 1604799 := bstep (se 1 (by rfl) ⟨1203599, by rfl⟩ : syracuseStep 1604799 = 2407199) B2407199
theorem B58532989 : Blo 1603000 58532989 := bstep (se 3 (by rfl) ⟨10974935, by rfl⟩ : syracuseStep 58532989 = 21949871) B21949871
theorem B187524557 : Blo 1603000 187524557 := bstep (se 3 (by rfl) ⟨35160854, by rfl⟩ : syracuseStep 187524557 = 70321709) B70321709
theorem B3856015 : Blo 1603000 3856015 := bstep (se 1 (by rfl) ⟨2892011, by rfl⟩ : syracuseStep 3856015 = 5784023) B5784023
theorem B6093407 : Blo 1603000 6093407 := bstep (se 1 (by rfl) ⟨4570055, by rfl⟩ : syracuseStep 6093407 = 9140111) B9140111
theorem B2407163 : Blo 1603000 2407163 := bstep (se 1 (by rfl) ⟨1805372, by rfl⟩ : syracuseStep 2407163 = 3610745) B3610745
theorem B5141353 : Blo 1603000 5141353 := bstep (se 2 (by rfl) ⟨1928007, by rfl⟩ : syracuseStep 5141353 = 3856015) B3856015
theorem B125016371 : Blo 1603000 125016371 := bstep (se 1 (by rfl) ⟨93762278, by rfl⟩ : syracuseStep 125016371 = 187524557) B187524557
theorem B78043985 : Blo 1603000 78043985 := bstep (se 2 (by rfl) ⟨29266494, by rfl⟩ : syracuseStep 78043985 = 58532989) B58532989
theorem B4062271 : Blo 1603000 4062271 := bstep (se 1 (by rfl) ⟨3046703, by rfl⟩ : syracuseStep 4062271 = 6093407) B6093407
theorem B1604775 : Blo 1603000 1604775 := bstep (se 1 (by rfl) ⟨1203581, by rfl⟩ : syracuseStep 1604775 = 2407163) B2407163
theorem B5416361 : Blo 1603000 5416361 := bstep (se 2 (by rfl) ⟨2031135, by rfl⟩ : syracuseStep 5416361 = 4062271) B4062271
theorem B52029323 : Blo 1603000 52029323 := bstep (se 1 (by rfl) ⟨39021992, by rfl⟩ : syracuseStep 52029323 = 78043985) B78043985
theorem B6855137 : Blo 1603000 6855137 := bstep (se 2 (by rfl) ⟨2570676, by rfl⟩ : syracuseStep 6855137 = 5141353) B5141353
theorem B83344247 : Blo 1603000 83344247 := bstep (se 1 (by rfl) ⟨62508185, by rfl⟩ : syracuseStep 83344247 = 125016371) B125016371
theorem B34686215 : Blo 1603000 34686215 := bstep (se 1 (by rfl) ⟨26014661, by rfl⟩ : syracuseStep 34686215 = 52029323) B52029323
theorem B55562831 : Blo 1603000 55562831 := bstep (se 1 (by rfl) ⟨41672123, by rfl⟩ : syracuseStep 55562831 = 83344247) B83344247
theorem B3610907 : Blo 1603000 3610907 := bstep (se 1 (by rfl) ⟨2708180, by rfl⟩ : syracuseStep 3610907 = 5416361) B5416361
theorem B4570091 : Blo 1603000 4570091 := bstep (se 1 (by rfl) ⟨3427568, by rfl⟩ : syracuseStep 4570091 = 6855137) B6855137
theorem B37041887 : Blo 1603000 37041887 := bstep (se 1 (by rfl) ⟨27781415, by rfl⟩ : syracuseStep 37041887 = 55562831) B55562831
theorem B23124143 : Blo 1603000 23124143 := bstep (se 1 (by rfl) ⟨17343107, by rfl⟩ : syracuseStep 23124143 = 34686215) B34686215
theorem B2407271 : Blo 1603000 2407271 := bstep (se 1 (by rfl) ⟨1805453, by rfl⟩ : syracuseStep 2407271 = 3610907) B3610907
theorem B3046727 : Blo 1603000 3046727 := bstep (se 1 (by rfl) ⟨2285045, by rfl⟩ : syracuseStep 3046727 = 4570091) B4570091
theorem B24694591 : Blo 1603000 24694591 := bstep (se 1 (by rfl) ⟨18520943, by rfl⟩ : syracuseStep 24694591 = 37041887) B37041887
theorem B15416095 : Blo 1603000 15416095 := bstep (se 1 (by rfl) ⟨11562071, by rfl⟩ : syracuseStep 15416095 = 23124143) B23124143
theorem B1604847 : Blo 1603000 1604847 := bstep (se 1 (by rfl) ⟨1203635, by rfl⟩ : syracuseStep 1604847 = 2407271) B2407271
theorem B2031151 : Blo 1603000 2031151 := bstep (se 1 (by rfl) ⟨1523363, by rfl⟩ : syracuseStep 2031151 = 3046727) B3046727
theorem B20554793 : Blo 1603000 20554793 := bstep (se 2 (by rfl) ⟨7708047, by rfl⟩ : syracuseStep 20554793 = 15416095) B15416095
theorem B32926121 : Blo 1603000 32926121 := bstep (se 2 (by rfl) ⟨12347295, by rfl⟩ : syracuseStep 32926121 = 24694591) B24694591
theorem B2708201 : Blo 1603000 2708201 := bstep (se 2 (by rfl) ⟨1015575, by rfl⟩ : syracuseStep 2708201 = 2031151) B2031151
theorem B1805467 : Blo 1603000 1805467 := bstep (se 1 (by rfl) ⟨1354100, by rfl⟩ : syracuseStep 1805467 = 2708201) B2708201
theorem B21950747 : Blo 1603000 21950747 := bstep (se 1 (by rfl) ⟨16463060, by rfl⟩ : syracuseStep 21950747 = 32926121) B32926121
theorem B13703195 : Blo 1603000 13703195 := bstep (se 1 (by rfl) ⟨10277396, by rfl⟩ : syracuseStep 13703195 = 20554793) B20554793
theorem B9135463 : Blo 1603000 9135463 := bstep (se 1 (by rfl) ⟨6851597, by rfl⟩ : syracuseStep 9135463 = 13703195) B13703195
theorem B14633831 : Blo 1603000 14633831 := bstep (se 1 (by rfl) ⟨10975373, by rfl⟩ : syracuseStep 14633831 = 21950747) B21950747
theorem B2407289 : Blo 1603000 2407289 := bstep (se 2 (by rfl) ⟨902733, by rfl⟩ : syracuseStep 2407289 = 1805467) B1805467
theorem B12180617 : Blo 1603000 12180617 := bstep (se 2 (by rfl) ⟨4567731, by rfl⟩ : syracuseStep 12180617 = 9135463) B9135463
theorem B9755887 : Blo 1603000 9755887 := bstep (se 1 (by rfl) ⟨7316915, by rfl⟩ : syracuseStep 9755887 = 14633831) B14633831
theorem B1604859 : Blo 1603000 1604859 := bstep (se 1 (by rfl) ⟨1203644, by rfl⟩ : syracuseStep 1604859 = 2407289) B2407289
theorem B8120411 : Blo 1603000 8120411 := bstep (se 1 (by rfl) ⟨6090308, by rfl⟩ : syracuseStep 8120411 = 12180617) B12180617
theorem B13007849 : Blo 1603000 13007849 := bstep (se 2 (by rfl) ⟨4877943, by rfl⟩ : syracuseStep 13007849 = 9755887) B9755887
theorem B34687597 : Blo 1603000 34687597 := bstep (se 3 (by rfl) ⟨6503924, by rfl⟩ : syracuseStep 34687597 = 13007849) B13007849
theorem B5413607 : Blo 1603000 5413607 := bstep (se 1 (by rfl) ⟨4060205, by rfl⟩ : syracuseStep 5413607 = 8120411) B8120411
theorem B3609071 : Blo 1603000 3609071 := bstep (se 1 (by rfl) ⟨2706803, by rfl⟩ : syracuseStep 3609071 = 5413607) B5413607
theorem B46250129 : Blo 1603000 46250129 := bstep (se 2 (by rfl) ⟨17343798, by rfl⟩ : syracuseStep 46250129 = 34687597) B34687597
theorem B2406047 : Blo 1603000 2406047 := bstep (se 1 (by rfl) ⟨1804535, by rfl⟩ : syracuseStep 2406047 = 3609071) B3609071
theorem B30833419 : Blo 1603000 30833419 := bstep (se 1 (by rfl) ⟨23125064, by rfl⟩ : syracuseStep 30833419 = 46250129) B46250129
theorem B41111225 : Blo 1603000 41111225 := bstep (se 2 (by rfl) ⟨15416709, by rfl⟩ : syracuseStep 41111225 = 30833419) B30833419
theorem B1604031 : Blo 1603000 1604031 := bstep (se 1 (by rfl) ⟨1203023, by rfl⟩ : syracuseStep 1604031 = 2406047) B2406047
theorem B27407483 : Blo 1603000 27407483 := bstep (se 1 (by rfl) ⟨20555612, by rfl⟩ : syracuseStep 27407483 = 41111225) B41111225
theorem B18271655 : Blo 1603000 18271655 := bstep (se 1 (by rfl) ⟨13703741, by rfl⟩ : syracuseStep 18271655 = 27407483) B27407483
theorem B12181103 : Blo 1603000 12181103 := bstep (se 1 (by rfl) ⟨9135827, by rfl⟩ : syracuseStep 12181103 = 18271655) B18271655
theorem B8120735 : Blo 1603000 8120735 := bstep (se 1 (by rfl) ⟨6090551, by rfl⟩ : syracuseStep 8120735 = 12181103) B12181103
theorem B5413823 : Blo 1603000 5413823 := bstep (se 1 (by rfl) ⟨4060367, by rfl⟩ : syracuseStep 5413823 = 8120735) B8120735
theorem B3609215 : Blo 1603000 3609215 := bstep (se 1 (by rfl) ⟨2706911, by rfl⟩ : syracuseStep 3609215 = 5413823) B5413823
theorem B2406143 : Blo 1603000 2406143 := bstep (se 1 (by rfl) ⟨1804607, by rfl⟩ : syracuseStep 2406143 = 3609215) B3609215
theorem B1604095 : Blo 1603000 1604095 := bstep (se 1 (by rfl) ⟨1203071, by rfl⟩ : syracuseStep 1604095 = 2406143) B2406143

theorem C0 (j : ℕ) (h1 : 400750 ≤ j) (h2 : j ≤ 401249) : Blo 1603000 (4 * j + 3) := by
  interval_cases j
  · exact B1603003
  · exact B1603007
  · exact B1603011
  · exact B1603015
  · exact B1603019
  · exact B1603023
  · exact B1603027
  · exact B1603031
  · exact B1603035
  · exact B1603039
  · exact B1603043
  · exact B1603047
  · exact B1603051
  · exact B1603055
  · exact B1603059
  · exact B1603063
  · exact B1603067
  · exact B1603071
  · exact B1603075
  · exact B1603079
  · exact B1603083
  · exact B1603087
  · exact B1603091
  · exact B1603095
  · exact B1603099
  · exact B1603103
  · exact B1603107
  · exact B1603111
  · exact B1603115
  · exact B1603119
  · exact B1603123
  · exact B1603127
  · exact B1603131
  · exact B1603135
  · exact B1603139
  · exact B1603143
  · exact B1603147
  · exact B1603151
  · exact B1603155
  · exact B1603159
  · exact B1603163
  · exact B1603167
  · exact B1603171
  · exact B1603175
  · exact B1603179
  · exact B1603183
  · exact B1603187
  · exact B1603191
  · exact B1603195
  · exact B1603199
  · exact B1603203
  · exact B1603207
  · exact B1603211
  · exact B1603215
  · exact B1603219
  · exact B1603223
  · exact B1603227
  · exact B1603231
  · exact B1603235
  · exact B1603239
  · exact B1603243
  · exact B1603247
  · exact B1603251
  · exact B1603255
  · exact B1603259
  · exact B1603263
  · exact B1603267
  · exact B1603271
  · exact B1603275
  · exact B1603279
  · exact B1603283
  · exact B1603287
  · exact B1603291
  · exact B1603295
  · exact B1603299
  · exact B1603303
  · exact B1603307
  · exact B1603311
  · exact B1603315
  · exact B1603319
  · exact B1603323
  · exact B1603327
  · exact B1603331
  · exact B1603335
  · exact B1603339
  · exact B1603343
  · exact B1603347
  · exact B1603351
  · exact B1603355
  · exact B1603359
  · exact B1603363
  · exact B1603367
  · exact B1603371
  · exact B1603375
  · exact B1603379
  · exact B1603383
  · exact B1603387
  · exact B1603391
  · exact B1603395
  · exact B1603399
  · exact B1603403
  · exact B1603407
  · exact B1603411
  · exact B1603415
  · exact B1603419
  · exact B1603423
  · exact B1603427
  · exact B1603431
  · exact B1603435
  · exact B1603439
  · exact B1603443
  · exact B1603447
  · exact B1603451
  · exact B1603455
  · exact B1603459
  · exact B1603463
  · exact B1603467
  · exact B1603471
  · exact B1603475
  · exact B1603479
  · exact B1603483
  · exact B1603487
  · exact B1603491
  · exact B1603495
  · exact B1603499
  · exact B1603503
  · exact B1603507
  · exact B1603511
  · exact B1603515
  · exact B1603519
  · exact B1603523
  · exact B1603527
  · exact B1603531
  · exact B1603535
  · exact B1603539
  · exact B1603543
  · exact B1603547
  · exact B1603551
  · exact B1603555
  · exact B1603559
  · exact B1603563
  · exact B1603567
  · exact B1603571
  · exact B1603575
  · exact B1603579
  · exact B1603583
  · exact B1603587
  · exact B1603591
  · exact B1603595
  · exact B1603599
  · exact B1603603
  · exact B1603607
  · exact B1603611
  · exact B1603615
  · exact B1603619
  · exact B1603623
  · exact B1603627
  · exact B1603631
  · exact B1603635
  · exact B1603639
  · exact B1603643
  · exact B1603647
  · exact B1603651
  · exact B1603655
  · exact B1603659
  · exact B1603663
  · exact B1603667
  · exact B1603671
  · exact B1603675
  · exact B1603679
  · exact B1603683
  · exact B1603687
  · exact B1603691
  · exact B1603695
  · exact B1603699
  · exact B1603703
  · exact B1603707
  · exact B1603711
  · exact B1603715
  · exact B1603719
  · exact B1603723
  · exact B1603727
  · exact B1603731
  · exact B1603735
  · exact B1603739
  · exact B1603743
  · exact B1603747
  · exact B1603751
  · exact B1603755
  · exact B1603759
  · exact B1603763
  · exact B1603767
  · exact B1603771
  · exact B1603775
  · exact B1603779
  · exact B1603783
  · exact B1603787
  · exact B1603791
  · exact B1603795
  · exact B1603799
  · exact B1603803
  · exact B1603807
  · exact B1603811
  · exact B1603815
  · exact B1603819
  · exact B1603823
  · exact B1603827
  · exact B1603831
  · exact B1603835
  · exact B1603839
  · exact B1603843
  · exact B1603847
  · exact B1603851
  · exact B1603855
  · exact B1603859
  · exact B1603863
  · exact B1603867
  · exact B1603871
  · exact B1603875
  · exact B1603879
  · exact B1603883
  · exact B1603887
  · exact B1603891
  · exact B1603895
  · exact B1603899
  · exact B1603903
  · exact B1603907
  · exact B1603911
  · exact B1603915
  · exact B1603919
  · exact B1603923
  · exact B1603927
  · exact B1603931
  · exact B1603935
  · exact B1603939
  · exact B1603943
  · exact B1603947
  · exact B1603951
  · exact B1603955
  · exact B1603959
  · exact B1603963
  · exact B1603967
  · exact B1603971
  · exact B1603975
  · exact B1603979
  · exact B1603983
  · exact B1603987
  · exact B1603991
  · exact B1603995
  · exact B1603999
  · exact B1604003
  · exact B1604007
  · exact B1604011
  · exact B1604015
  · exact B1604019
  · exact B1604023
  · exact B1604027
  · exact B1604031
  · exact B1604035
  · exact B1604039
  · exact B1604043
  · exact B1604047
  · exact B1604051
  · exact B1604055
  · exact B1604059
  · exact B1604063
  · exact B1604067
  · exact B1604071
  · exact B1604075
  · exact B1604079
  · exact B1604083
  · exact B1604087
  · exact B1604091
  · exact B1604095
  · exact B1604099
  · exact B1604103
  · exact B1604107
  · exact B1604111
  · exact B1604115
  · exact B1604119
  · exact B1604123
  · exact B1604127
  · exact B1604131
  · exact B1604135
  · exact B1604139
  · exact B1604143
  · exact B1604147
  · exact B1604151
  · exact B1604155
  · exact B1604159
  · exact B1604163
  · exact B1604167
  · exact B1604171
  · exact B1604175
  · exact B1604179
  · exact B1604183
  · exact B1604187
  · exact B1604191
  · exact B1604195
  · exact B1604199
  · exact B1604203
  · exact B1604207
  · exact B1604211
  · exact B1604215
  · exact B1604219
  · exact B1604223
  · exact B1604227
  · exact B1604231
  · exact B1604235
  · exact B1604239
  · exact B1604243
  · exact B1604247
  · exact B1604251
  · exact B1604255
  · exact B1604259
  · exact B1604263
  · exact B1604267
  · exact B1604271
  · exact B1604275
  · exact B1604279
  · exact B1604283
  · exact B1604287
  · exact B1604291
  · exact B1604295
  · exact B1604299
  · exact B1604303
  · exact B1604307
  · exact B1604311
  · exact B1604315
  · exact B1604319
  · exact B1604323
  · exact B1604327
  · exact B1604331
  · exact B1604335
  · exact B1604339
  · exact B1604343
  · exact B1604347
  · exact B1604351
  · exact B1604355
  · exact B1604359
  · exact B1604363
  · exact B1604367
  · exact B1604371
  · exact B1604375
  · exact B1604379
  · exact B1604383
  · exact B1604387
  · exact B1604391
  · exact B1604395
  · exact B1604399
  · exact B1604403
  · exact B1604407
  · exact B1604411
  · exact B1604415
  · exact B1604419
  · exact B1604423
  · exact B1604427
  · exact B1604431
  · exact B1604435
  · exact B1604439
  · exact B1604443
  · exact B1604447
  · exact B1604451
  · exact B1604455
  · exact B1604459
  · exact B1604463
  · exact B1604467
  · exact B1604471
  · exact B1604475
  · exact B1604479
  · exact B1604483
  · exact B1604487
  · exact B1604491
  · exact B1604495
  · exact B1604499
  · exact B1604503
  · exact B1604507
  · exact B1604511
  · exact B1604515
  · exact B1604519
  · exact B1604523
  · exact B1604527
  · exact B1604531
  · exact B1604535
  · exact B1604539
  · exact B1604543
  · exact B1604547
  · exact B1604551
  · exact B1604555
  · exact B1604559
  · exact B1604563
  · exact B1604567
  · exact B1604571
  · exact B1604575
  · exact B1604579
  · exact B1604583
  · exact B1604587
  · exact B1604591
  · exact B1604595
  · exact B1604599
  · exact B1604603
  · exact B1604607
  · exact B1604611
  · exact B1604615
  · exact B1604619
  · exact B1604623
  · exact B1604627
  · exact B1604631
  · exact B1604635
  · exact B1604639
  · exact B1604643
  · exact B1604647
  · exact B1604651
  · exact B1604655
  · exact B1604659
  · exact B1604663
  · exact B1604667
  · exact B1604671
  · exact B1604675
  · exact B1604679
  · exact B1604683
  · exact B1604687
  · exact B1604691
  · exact B1604695
  · exact B1604699
  · exact B1604703
  · exact B1604707
  · exact B1604711
  · exact B1604715
  · exact B1604719
  · exact B1604723
  · exact B1604727
  · exact B1604731
  · exact B1604735
  · exact B1604739
  · exact B1604743
  · exact B1604747
  · exact B1604751
  · exact B1604755
  · exact B1604759
  · exact B1604763
  · exact B1604767
  · exact B1604771
  · exact B1604775
  · exact B1604779
  · exact B1604783
  · exact B1604787
  · exact B1604791
  · exact B1604795
  · exact B1604799
  · exact B1604803
  · exact B1604807
  · exact B1604811
  · exact B1604815
  · exact B1604819
  · exact B1604823
  · exact B1604827
  · exact B1604831
  · exact B1604835
  · exact B1604839
  · exact B1604843
  · exact B1604847
  · exact B1604851
  · exact B1604855
  · exact B1604859
  · exact B1604863
  · exact B1604867
  · exact B1604871
  · exact B1604875
  · exact B1604879
  · exact B1604883
  · exact B1604887
  · exact B1604891
  · exact B1604895
  · exact B1604899
  · exact B1604903
  · exact B1604907
  · exact B1604911
  · exact B1604915
  · exact B1604919
  · exact B1604923
  · exact B1604927
  · exact B1604931
  · exact B1604935
  · exact B1604939
  · exact B1604943
  · exact B1604947
  · exact B1604951
  · exact B1604955
  · exact B1604959
  · exact B1604963
  · exact B1604967
  · exact B1604971
  · exact B1604975
  · exact B1604979
  · exact B1604983
  · exact B1604987
  · exact B1604991
  · exact B1604995
  · exact B1604999

theorem solution (m : ℕ) (hlo : 1603000 ≤ m) (hhi : m ≤ 1605000) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 400750 ≤ j := by omega
    have hj2 : j ≤ 401249 := by omega
    have hb : Blo 1603000 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
