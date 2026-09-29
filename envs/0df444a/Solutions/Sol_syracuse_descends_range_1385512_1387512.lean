-- Prove2me | solution 1 for syracuse_descends_range_1385512_1387512
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:27.626986+00:00
-- url     : https://prove2.me/submissions/abfe9e78-8f98-41a6-9ae5-348c91535a6a

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


theorem B1802245 : Blo 1385512 1802245 := bbase (se 4 (by rfl) ⟨168960, by rfl⟩ : syracuseStep 1802245 = 337921) (by norm_num)
theorem B2080781 : Blo 1385512 2080781 := bbase (se 3 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 2080781 = 780293) (by norm_num)
theorem B2220053 : Blo 1385512 2220053 := bbase (se 6 (by rfl) ⟨52032, by rfl⟩ : syracuseStep 2220053 = 104065) (by norm_num)
theorem B3121181 : Blo 1385512 3121181 := bbase (se 3 (by rfl) ⟨585221, by rfl⟩ : syracuseStep 3121181 = 1170443) (by norm_num)
theorem B1581089 : Blo 1385512 1581089 := bbase (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) (by norm_num)
theorem B2080805 : Blo 1385512 2080805 := bbase (se 4 (by rfl) ⟨195075, by rfl⟩ : syracuseStep 2080805 = 390151) (by norm_num)
theorem B2080829 : Blo 1385512 2080829 := bbase (se 3 (by rfl) ⟨390155, by rfl⟩ : syracuseStep 2080829 = 780311) (by norm_num)
theorem B2080853 : Blo 1385512 2080853 := bbase (se 8 (by rfl) ⟨12192, by rfl⟩ : syracuseStep 2080853 = 24385) (by norm_num)
theorem B3121253 : Blo 1385512 3121253 := bbase (se 4 (by rfl) ⟨292617, by rfl⟩ : syracuseStep 3121253 = 585235) (by norm_num)
theorem B2080877 : Blo 1385512 2080877 := bbase (se 3 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 2080877 = 780329) (by norm_num)
theorem B4677749 : Blo 1385512 4677749 := bbase (se 5 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 4677749 = 438539) (by norm_num)
theorem B2080901 : Blo 1385512 2080901 := bbase (se 4 (by rfl) ⟨195084, by rfl⟩ : syracuseStep 2080901 = 390169) (by norm_num)
theorem B2080925 : Blo 1385512 2080925 := bbase (se 3 (by rfl) ⟨390173, by rfl⟩ : syracuseStep 2080925 = 780347) (by norm_num)
theorem B4997285 : Blo 1385512 4997285 := bbase (se 4 (by rfl) ⟨468495, by rfl⟩ : syracuseStep 4997285 = 936991) (by norm_num)
theorem B3948709 : Blo 1385512 3948709 := bbase (se 4 (by rfl) ⟨370191, by rfl⟩ : syracuseStep 3948709 = 740383) (by norm_num)
theorem B3121325 : Blo 1385512 3121325 := bbase (se 3 (by rfl) ⟨585248, by rfl⟩ : syracuseStep 3121325 = 1170497) (by norm_num)
theorem B2080949 : Blo 1385512 2080949 := bbase (se 5 (by rfl) ⟨97544, by rfl⟩ : syracuseStep 2080949 = 195089) (by norm_num)
theorem B1851589 : Blo 1385512 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B2080973 : Blo 1385512 2080973 := bbase (se 3 (by rfl) ⟨390182, by rfl⟩ : syracuseStep 2080973 = 780365) (by norm_num)
theorem B2080997 : Blo 1385512 2080997 := bbase (se 4 (by rfl) ⟨195093, by rfl⟩ : syracuseStep 2080997 = 390187) (by norm_num)
theorem B3121397 : Blo 1385512 3121397 := bbase (se 5 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 3121397 = 292631) (by norm_num)
theorem B2081021 : Blo 1385512 2081021 := bbase (se 3 (by rfl) ⟨390191, by rfl⟩ : syracuseStep 2081021 = 780383) (by norm_num)
theorem B6086917 : Blo 1385512 6086917 := bbase (se 4 (by rfl) ⟨570648, by rfl⟩ : syracuseStep 6086917 = 1141297) (by norm_num)
theorem B2081045 : Blo 1385512 2081045 := bbase (se 6 (by rfl) ⟨48774, by rfl⟩ : syracuseStep 2081045 = 97549) (by norm_num)
theorem B1974565 : Blo 1385512 1974565 := bbase (se 4 (by rfl) ⟨185115, by rfl⟩ : syracuseStep 1974565 = 370231) (by norm_num)
theorem B2081069 : Blo 1385512 2081069 := bbase (se 3 (by rfl) ⟨390200, by rfl⟩ : syracuseStep 2081069 = 780401) (by norm_num)
theorem B3121469 : Blo 1385512 3121469 := bbase (se 3 (by rfl) ⟨585275, by rfl⟩ : syracuseStep 3121469 = 1170551) (by norm_num)
theorem B7119173 : Blo 1385512 7119173 := bbase (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) (by norm_num)
theorem B2081093 : Blo 1385512 2081093 := bbase (se 4 (by rfl) ⟨195102, by rfl⟩ : syracuseStep 2081093 = 390205) (by norm_num)
theorem B2081117 : Blo 1385512 2081117 := bbase (se 3 (by rfl) ⟨390209, by rfl⟩ : syracuseStep 2081117 = 780419) (by norm_num)
theorem B7020917 : Blo 1385512 7020917 := bbase (se 5 (by rfl) ⟨329105, by rfl⟩ : syracuseStep 7020917 = 658211) (by norm_num)
theorem B2081141 : Blo 1385512 2081141 := bbase (se 5 (by rfl) ⟨97553, by rfl⟩ : syracuseStep 2081141 = 195107) (by norm_num)
theorem B3121541 : Blo 1385512 3121541 := bbase (se 4 (by rfl) ⟨292644, by rfl⟩ : syracuseStep 3121541 = 585289) (by norm_num)
theorem B2081165 : Blo 1385512 2081165 := bbase (se 3 (by rfl) ⟨390218, by rfl⟩ : syracuseStep 2081165 = 780437) (by norm_num)
theorem B1778069 : Blo 1385512 1778069 := bbase (se 6 (by rfl) ⟨41673, by rfl⟩ : syracuseStep 1778069 = 83347) (by norm_num)
theorem B5267861 : Blo 1385512 5267861 := bbase (se 6 (by rfl) ⟨123465, by rfl⟩ : syracuseStep 5267861 = 246931) (by norm_num)
theorem B2081189 : Blo 1385512 2081189 := bbase (se 4 (by rfl) ⟨195111, by rfl⟩ : syracuseStep 2081189 = 390223) (by norm_num)
theorem B2081213 : Blo 1385512 2081213 := bbase (se 3 (by rfl) ⟨390227, by rfl⟩ : syracuseStep 2081213 = 780455) (by norm_num)
theorem B3121613 : Blo 1385512 3121613 := bbase (se 3 (by rfl) ⟨585302, by rfl⟩ : syracuseStep 3121613 = 1170605) (by norm_num)
theorem B2081237 : Blo 1385512 2081237 := bbase (se 7 (by rfl) ⟨24389, by rfl⟩ : syracuseStep 2081237 = 48779) (by norm_num)
theorem B2081261 : Blo 1385512 2081261 := bbase (se 3 (by rfl) ⟨390236, by rfl⟩ : syracuseStep 2081261 = 780473) (by norm_num)
theorem B1753589 : Blo 1385512 1753589 := bbase (se 5 (by rfl) ⟨82199, by rfl⟩ : syracuseStep 1753589 = 164399) (by norm_num)
theorem B7897621 : Blo 1385512 7897621 := bbase (se 6 (by rfl) ⟨185100, by rfl⟩ : syracuseStep 7897621 = 370201) (by norm_num)
theorem B3121685 : Blo 1385512 3121685 := bbase (se 6 (by rfl) ⟨73164, by rfl⟩ : syracuseStep 3121685 = 146329) (by norm_num)
theorem B4678181 : Blo 1385512 4678181 := bbase (se 4 (by rfl) ⟨438579, by rfl⟩ : syracuseStep 4678181 = 877159) (by norm_num)
theorem B1753645 : Blo 1385512 1753645 := bbase (se 3 (by rfl) ⟨328808, by rfl⟩ : syracuseStep 1753645 = 657617) (by norm_num)
theorem B2220605 : Blo 1385512 2220605 := bbase (se 3 (by rfl) ⟨416363, by rfl⟩ : syracuseStep 2220605 = 832727) (by norm_num)
theorem B1581637 : Blo 1385512 1581637 := bbase (se 4 (by rfl) ⟨148278, by rfl⟩ : syracuseStep 1581637 = 296557) (by norm_num)
theorem B2220637 : Blo 1385512 2220637 := bbase (se 3 (by rfl) ⟨416369, by rfl⟩ : syracuseStep 2220637 = 832739) (by norm_num)
theorem B3121757 : Blo 1385512 3121757 := bbase (se 3 (by rfl) ⟨585329, by rfl⟩ : syracuseStep 3121757 = 1170659) (by norm_num)
theorem B1581673 : Blo 1385512 1581673 := bbase (se 2 (by rfl) ⟨593127, by rfl⟩ : syracuseStep 1581673 = 1186255) (by norm_num)
theorem B1753741 : Blo 1385512 1753741 := bbase (se 3 (by rfl) ⟨328826, by rfl⟩ : syracuseStep 1753741 = 657653) (by norm_num)
theorem B3121829 : Blo 1385512 3121829 := bbase (se 4 (by rfl) ⟨292671, by rfl⟩ : syracuseStep 3121829 = 585343) (by norm_num)
theorem B5268149 : Blo 1385512 5268149 := bbase (se 5 (by rfl) ⟨246944, by rfl⟩ : syracuseStep 5268149 = 493889) (by norm_num)
theorem B4997861 : Blo 1385512 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B3121901 : Blo 1385512 3121901 := bbase (se 3 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 3121901 = 1170713) (by norm_num)
theorem B2499349 : Blo 1385512 2499349 := bbase (se 6 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 2499349 = 117157) (by norm_num)
theorem B1753913 : Blo 1385512 1753913 := bbase (se 2 (by rfl) ⟨657717, by rfl⟩ : syracuseStep 1753913 = 1315435) (by norm_num)
theorem B1499969 : Blo 1385512 1499969 := bbase (se 2 (by rfl) ⟨562488, by rfl⟩ : syracuseStep 1499969 = 1124977) (by norm_num)
theorem B4440901 : Blo 1385512 4440901 := bbase (se 4 (by rfl) ⟨416334, by rfl⟩ : syracuseStep 4440901 = 832669) (by norm_num)
theorem B5620549 : Blo 1385512 5620549 := bbase (se 4 (by rfl) ⟨526926, by rfl⟩ : syracuseStep 5620549 = 1053853) (by norm_num)
theorem B1753969 : Blo 1385512 1753969 := bbase (se 2 (by rfl) ⟨657738, by rfl⟩ : syracuseStep 1753969 = 1315477) (by norm_num)
theorem B1754065 : Blo 1385512 1754065 := bbase (se 2 (by rfl) ⟨657774, by rfl⟩ : syracuseStep 1754065 = 1315549) (by norm_num)
theorem B4678613 : Blo 1385512 4678613 := bbase (se 7 (by rfl) ⟨54827, by rfl⟩ : syracuseStep 4678613 = 109655) (by norm_num)
theorem B1975357 : Blo 1385512 1975357 := bbase (se 3 (by rfl) ⟨370379, by rfl⟩ : syracuseStep 1975357 = 740759) (by norm_num)
theorem B6661237 : Blo 1385512 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B1754237 : Blo 1385512 1754237 := bbase (se 3 (by rfl) ⟨328919, by rfl⟩ : syracuseStep 1754237 = 657839) (by norm_num)
theorem B2811037 : Blo 1385512 2811037 := bbase (se 3 (by rfl) ⟨527069, by rfl⟩ : syracuseStep 2811037 = 1054139) (by norm_num)
theorem B2811053 : Blo 1385512 2811053 := bbase (se 3 (by rfl) ⟨527072, by rfl⟩ : syracuseStep 2811053 = 1054145) (by norm_num)
theorem B1754293 : Blo 1385512 1754293 := bbase (se 5 (by rfl) ⟨82232, by rfl⟩ : syracuseStep 1754293 = 164465) (by norm_num)
theorem B3556541 : Blo 1385512 3556541 := bbase (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) (by norm_num)
theorem B3507421 : Blo 1385512 3507421 := bbase (se 3 (by rfl) ⟨657641, by rfl⟩ : syracuseStep 3507421 = 1315283) (by norm_num)
theorem B2630893 : Blo 1385512 2630893 := bbase (se 3 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 2630893 = 986585) (by norm_num)
theorem B3949813 : Blo 1385512 3949813 := bbase (se 5 (by rfl) ⟨185147, by rfl⟩ : syracuseStep 3949813 = 370295) (by norm_num)
theorem B1754389 : Blo 1385512 1754389 := bbase (se 6 (by rfl) ⟨41118, by rfl⟩ : syracuseStep 1754389 = 82237) (by norm_num)
theorem B3376429 : Blo 1385512 3376429 := bbase (se 3 (by rfl) ⟨633080, by rfl⟩ : syracuseStep 3376429 = 1266161) (by norm_num)
theorem B3507533 : Blo 1385512 3507533 := bbase (se 3 (by rfl) ⟨657662, by rfl⟩ : syracuseStep 3507533 = 1315325) (by norm_num)
theorem B2631037 : Blo 1385512 2631037 := bbase (se 3 (by rfl) ⟨493319, by rfl⟩ : syracuseStep 2631037 = 986639) (by norm_num)
theorem B2106757 : Blo 1385512 2106757 := bbase (se 4 (by rfl) ⟨197508, by rfl⟩ : syracuseStep 2106757 = 395017) (by norm_num)
theorem B4679045 : Blo 1385512 4679045 := bbase (se 4 (by rfl) ⟨438660, by rfl⟩ : syracuseStep 4679045 = 877321) (by norm_num)
theorem B1754561 : Blo 1385512 1754561 := bbase (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) (by norm_num)
theorem B1754617 : Blo 1385512 1754617 := bbase (se 2 (by rfl) ⟨657981, by rfl⟩ : syracuseStep 1754617 = 1315963) (by norm_num)
theorem B2221565 : Blo 1385512 2221565 := bbase (se 3 (by rfl) ⟨416543, by rfl⟩ : syracuseStep 2221565 = 833087) (by norm_num)
theorem B3507725 : Blo 1385512 3507725 := bbase (se 3 (by rfl) ⟨657698, by rfl⟩ : syracuseStep 3507725 = 1315397) (by norm_num)
theorem B2631197 : Blo 1385512 2631197 := bbase (se 3 (by rfl) ⟨493349, by rfl⟩ : syracuseStep 2631197 = 986699) (by norm_num)
theorem B11847221 : Blo 1385512 11847221 := bbase (se 5 (by rfl) ⟨555338, by rfl⟩ : syracuseStep 11847221 = 1110677) (by norm_num)
theorem B1664569 : Blo 1385512 1664569 := bbase (se 2 (by rfl) ⟨624213, by rfl⟩ : syracuseStep 1664569 = 1248427) (by norm_num)
theorem B1754713 : Blo 1385512 1754713 := bbase (se 2 (by rfl) ⟨658017, by rfl⟩ : syracuseStep 1754713 = 1316035) (by norm_num)
theorem B7022213 : Blo 1385512 7022213 := bbase (se 4 (by rfl) ⟨658332, by rfl⟩ : syracuseStep 7022213 = 1316665) (by norm_num)
theorem B2631341 : Blo 1385512 2631341 := bbase (se 3 (by rfl) ⟨493376, by rfl⟩ : syracuseStep 2631341 = 986753) (by norm_num)
theorem B3163877 : Blo 1385512 3163877 := bbase (se 4 (by rfl) ⟨296613, by rfl⟩ : syracuseStep 3163877 = 593227) (by norm_num)
theorem B1754885 : Blo 1385512 1754885 := bbase (se 4 (by rfl) ⟨164520, by rfl⟩ : syracuseStep 1754885 = 329041) (by norm_num)
theorem B1500973 : Blo 1385512 1500973 := bbase (se 3 (by rfl) ⟨281432, by rfl⟩ : syracuseStep 1500973 = 562865) (by norm_num)
theorem B4679477 : Blo 1385512 4679477 := bbase (se 5 (by rfl) ⟨219350, by rfl⟩ : syracuseStep 4679477 = 438701) (by norm_num)
theorem B1754941 : Blo 1385512 1754941 := bbase (se 3 (by rfl) ⟨329051, by rfl⟩ : syracuseStep 1754941 = 658103) (by norm_num)
theorem B3508069 : Blo 1385512 3508069 := bbase (se 4 (by rfl) ⟨328881, by rfl⟩ : syracuseStep 3508069 = 657763) (by norm_num)
theorem B1755037 : Blo 1385512 1755037 := bbase (se 3 (by rfl) ⟨329069, by rfl⟩ : syracuseStep 1755037 = 658139) (by norm_num)
theorem B5924789 : Blo 1385512 5924789 := bbase (se 5 (by rfl) ⟨277724, by rfl⟩ : syracuseStep 5924789 = 555449) (by norm_num)
theorem B1689541 : Blo 1385512 1689541 := bbase (se 4 (by rfl) ⟨158394, by rfl⟩ : syracuseStep 1689541 = 316789) (by norm_num)
theorem B2631629 : Blo 1385512 2631629 := bbase (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) (by norm_num)
theorem B3508181 : Blo 1385512 3508181 := bbase (se 7 (by rfl) ⟨41111, by rfl⟩ : syracuseStep 3508181 = 82223) (by norm_num)
theorem B7014437 : Blo 1385512 7014437 := bbase (se 4 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 7014437 = 1315207) (by norm_num)
theorem B13510709 : Blo 1385512 13510709 := bbase (se 5 (by rfl) ⟨633314, by rfl⟩ : syracuseStep 13510709 = 1266629) (by norm_num)
theorem B2959421 : Blo 1385512 2959421 := bbase (se 3 (by rfl) ⟨554891, by rfl⟩ : syracuseStep 2959421 = 1109783) (by norm_num)
theorem B1755209 : Blo 1385512 1755209 := bbase (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) (by norm_num)
theorem B2631781 : Blo 1385512 2631781 := bbase (se 4 (by rfl) ⟨246729, by rfl⟩ : syracuseStep 2631781 = 493459) (by norm_num)
theorem B12814453 : Blo 1385512 12814453 := bbase (se 5 (by rfl) ⟨600677, by rfl⟩ : syracuseStep 12814453 = 1201355) (by norm_num)
theorem B1755265 : Blo 1385512 1755265 := bbase (se 2 (by rfl) ⟨658224, by rfl⟩ : syracuseStep 1755265 = 1316449) (by norm_num)
theorem B3508373 : Blo 1385512 3508373 := bbase (se 6 (by rfl) ⟨82227, by rfl⟩ : syracuseStep 3508373 = 164455) (by norm_num)
theorem B3377309 : Blo 1385512 3377309 := bbase (se 3 (by rfl) ⟨633245, by rfl⟩ : syracuseStep 3377309 = 1266491) (by norm_num)
theorem B2222245 : Blo 1385512 2222245 := bbase (se 4 (by rfl) ⟨208335, by rfl⟩ : syracuseStep 2222245 = 416671) (by norm_num)
theorem B1558705 : Blo 1385512 1558705 := bbase (se 2 (by rfl) ⟨584514, by rfl⟩ : syracuseStep 1558705 = 1169029) (by norm_num)
theorem B3745973 : Blo 1385512 3745973 := bbase (se 5 (by rfl) ⟨175592, by rfl⟩ : syracuseStep 3745973 = 351185) (by norm_num)
theorem B1558741 : Blo 1385512 1558741 := bbase (se 7 (by rfl) ⟨18266, by rfl⟩ : syracuseStep 1558741 = 36533) (by norm_num)
theorem B1755361 : Blo 1385512 1755361 := bbase (se 2 (by rfl) ⟨658260, by rfl⟩ : syracuseStep 1755361 = 1316521) (by norm_num)
theorem B4679909 : Blo 1385512 4679909 := bbase (se 4 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 4679909 = 877483) (by norm_num)
theorem B2222309 : Blo 1385512 2222309 := bbase (se 4 (by rfl) ⟨208341, by rfl⟩ : syracuseStep 2222309 = 416683) (by norm_num)
theorem B5261557 : Blo 1385512 5261557 := bbase (se 5 (by rfl) ⟨246635, by rfl⟩ : syracuseStep 5261557 = 493271) (by norm_num)
theorem B1558777 : Blo 1385512 1558777 := bbase (se 2 (by rfl) ⟨584541, by rfl⟩ : syracuseStep 1558777 = 1169083) (by norm_num)
theorem B5335301 : Blo 1385512 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B4999445 : Blo 1385512 4999445 := bbase (se 6 (by rfl) ⟨117174, by rfl⟩ : syracuseStep 4999445 = 234349) (by norm_num)
theorem B1558813 : Blo 1385512 1558813 := bbase (se 3 (by rfl) ⟨292277, by rfl⟩ : syracuseStep 1558813 = 584555) (by norm_num)
theorem B2959661 : Blo 1385512 2959661 := bbase (se 3 (by rfl) ⟨554936, by rfl⟩ : syracuseStep 2959661 = 1109873) (by norm_num)
theorem B2812205 : Blo 1385512 2812205 := bbase (se 3 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 2812205 = 1054577) (by norm_num)
theorem B1558849 : Blo 1385512 1558849 := bbase (se 2 (by rfl) ⟨584568, by rfl⟩ : syracuseStep 1558849 = 1169137) (by norm_num)
theorem B4811093 : Blo 1385512 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B1558885 : Blo 1385512 1558885 := bbase (se 4 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 1558885 = 292291) (by norm_num)
theorem B1558921 : Blo 1385512 1558921 := bbase (se 2 (by rfl) ⟨584595, by rfl⟩ : syracuseStep 1558921 = 1169191) (by norm_num)
theorem B1755533 : Blo 1385512 1755533 := bbase (se 3 (by rfl) ⟨329162, by rfl⟩ : syracuseStep 1755533 = 658325) (by norm_num)
theorem B2632085 : Blo 1385512 2632085 := bbase (se 6 (by rfl) ⟨61689, by rfl⟩ : syracuseStep 2632085 = 123379) (by norm_num)
theorem B1558957 : Blo 1385512 1558957 := bbase (se 3 (by rfl) ⟨292304, by rfl⟩ : syracuseStep 1558957 = 584609) (by norm_num)
theorem B1755589 : Blo 1385512 1755589 := bbase (se 4 (by rfl) ⟨164586, by rfl⟩ : syracuseStep 1755589 = 329173) (by norm_num)
theorem B1558993 : Blo 1385512 1558993 := bbase (se 2 (by rfl) ⟨584622, by rfl⟩ : syracuseStep 1558993 = 1169245) (by norm_num)
theorem B7899605 : Blo 1385512 7899605 := bbase (se 7 (by rfl) ⟨92573, by rfl⟩ : syracuseStep 7899605 = 185147) (by norm_num)
theorem B3508717 : Blo 1385512 3508717 := bbase (se 3 (by rfl) ⟨657884, by rfl⟩ : syracuseStep 3508717 = 1315769) (by norm_num)
theorem B1559029 : Blo 1385512 1559029 := bbase (se 5 (by rfl) ⟨73079, by rfl⟩ : syracuseStep 1559029 = 146159) (by norm_num)
theorem B2107901 : Blo 1385512 2107901 := bbase (se 3 (by rfl) ⟨395231, by rfl⟩ : syracuseStep 2107901 = 790463) (by norm_num)
theorem B2107925 : Blo 1385512 2107925 := bbase (se 6 (by rfl) ⟨49404, by rfl⟩ : syracuseStep 2107925 = 98809) (by norm_num)
theorem B1559065 : Blo 1385512 1559065 := bbase (se 2 (by rfl) ⟨584649, by rfl⟩ : syracuseStep 1559065 = 1169299) (by norm_num)
theorem B1665569 : Blo 1385512 1665569 := bbase (se 2 (by rfl) ⟨624588, by rfl⟩ : syracuseStep 1665569 = 1249177) (by norm_num)
theorem B5261861 : Blo 1385512 5261861 := bbase (se 4 (by rfl) ⟨493299, by rfl⟩ : syracuseStep 5261861 = 986599) (by norm_num)
theorem B1755685 : Blo 1385512 1755685 := bbase (se 4 (by rfl) ⟨164595, by rfl⟩ : syracuseStep 1755685 = 329191) (by norm_num)
theorem B4999733 : Blo 1385512 4999733 := bbase (se 5 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 4999733 = 468725) (by norm_num)
theorem B1559101 : Blo 1385512 1559101 := bbase (se 3 (by rfl) ⟨292331, by rfl⟩ : syracuseStep 1559101 = 584663) (by norm_num)
theorem B3508829 : Blo 1385512 3508829 := bbase (se 3 (by rfl) ⟨657905, by rfl⟩ : syracuseStep 3508829 = 1315811) (by norm_num)
theorem B1559137 : Blo 1385512 1559137 := bbase (se 2 (by rfl) ⟨584676, by rfl⟩ : syracuseStep 1559137 = 1169353) (by norm_num)
theorem B1559173 : Blo 1385512 1559173 := bbase (se 4 (by rfl) ⟨146172, by rfl⟩ : syracuseStep 1559173 = 292345) (by norm_num)
theorem B2001541 : Blo 1385512 2001541 := bbase (se 4 (by rfl) ⟨187644, by rfl⟩ : syracuseStep 2001541 = 375289) (by norm_num)
theorem B4680341 : Blo 1385512 4680341 := bbase (se 6 (by rfl) ⟨109695, by rfl⟩ : syracuseStep 4680341 = 219391) (by norm_num)
theorem B1559209 : Blo 1385512 1559209 := bbase (se 2 (by rfl) ⟨584703, by rfl⟩ : syracuseStep 1559209 = 1169407) (by norm_num)
theorem B1559245 : Blo 1385512 1559245 := bbase (se 3 (by rfl) ⟨292358, by rfl⟩ : syracuseStep 1559245 = 584717) (by norm_num)
theorem B1755857 : Blo 1385512 1755857 := bbase (se 2 (by rfl) ⟨658446, by rfl⟩ : syracuseStep 1755857 = 1316893) (by norm_num)
theorem B3558109 : Blo 1385512 3558109 := bbase (se 3 (by rfl) ⟨667145, by rfl⟩ : syracuseStep 3558109 = 1334291) (by norm_num)
theorem B1559281 : Blo 1385512 1559281 := bbase (se 2 (by rfl) ⟨584730, by rfl⟩ : syracuseStep 1559281 = 1169461) (by norm_num)
theorem B1755913 : Blo 1385512 1755913 := bbase (se 2 (by rfl) ⟨658467, by rfl⟩ : syracuseStep 1755913 = 1316935) (by norm_num)
theorem B1559317 : Blo 1385512 1559317 := bbase (se 6 (by rfl) ⟨36546, by rfl⟩ : syracuseStep 1559317 = 73093) (by norm_num)
theorem B3509021 : Blo 1385512 3509021 := bbase (se 3 (by rfl) ⟨657941, by rfl⟩ : syracuseStep 3509021 = 1315883) (by norm_num)
theorem B2960165 : Blo 1385512 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B2960173 : Blo 1385512 2960173 := bbase (se 3 (by rfl) ⟨555032, by rfl⟩ : syracuseStep 2960173 = 1110065) (by norm_num)
theorem B4000565 : Blo 1385512 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B1559353 : Blo 1385512 1559353 := bbase (se 2 (by rfl) ⟨584757, by rfl⟩ : syracuseStep 1559353 = 1169515) (by norm_num)
theorem B1559389 : Blo 1385512 1559389 := bbase (se 3 (by rfl) ⟨292385, by rfl⟩ : syracuseStep 1559389 = 584771) (by norm_num)
theorem B1756009 : Blo 1385512 1756009 := bbase (se 2 (by rfl) ⟨658503, by rfl⟩ : syracuseStep 1756009 = 1317007) (by norm_num)
theorem B1559425 : Blo 1385512 1559425 := bbase (se 2 (by rfl) ⟨584784, by rfl⟩ : syracuseStep 1559425 = 1169569) (by norm_num)
theorem B7023509 : Blo 1385512 7023509 := bbase (se 6 (by rfl) ⟨164613, by rfl⟩ : syracuseStep 7023509 = 329227) (by norm_num)
theorem B1559461 : Blo 1385512 1559461 := bbase (se 4 (by rfl) ⟨146199, by rfl⟩ : syracuseStep 1559461 = 292399) (by norm_num)
theorem B1559497 : Blo 1385512 1559497 := bbase (se 2 (by rfl) ⟨584811, by rfl⟩ : syracuseStep 1559497 = 1169623) (by norm_num)
theorem B1444825 : Blo 1385512 1444825 := bbase (se 2 (by rfl) ⟨541809, by rfl⟩ : syracuseStep 1444825 = 1083619) (by norm_num)
theorem B1559533 : Blo 1385512 1559533 := bbase (se 3 (by rfl) ⟨292412, by rfl⟩ : syracuseStep 1559533 = 584825) (by norm_num)
theorem B1559569 : Blo 1385512 1559569 := bbase (se 2 (by rfl) ⟨584838, by rfl⟩ : syracuseStep 1559569 = 1169677) (by norm_num)
theorem B1559605 : Blo 1385512 1559605 := bbase (se 5 (by rfl) ⟨73106, by rfl⟩ : syracuseStep 1559605 = 146213) (by norm_num)
theorem B4680773 : Blo 1385512 4680773 := bbase (se 4 (by rfl) ⟨438822, by rfl⟩ : syracuseStep 4680773 = 877645) (by norm_num)
theorem B1559641 : Blo 1385512 1559641 := bbase (se 2 (by rfl) ⟨584865, by rfl⟩ : syracuseStep 1559641 = 1169731) (by norm_num)
theorem B3509365 : Blo 1385512 3509365 := bbase (se 5 (by rfl) ⟨164501, by rfl⟩ : syracuseStep 3509365 = 329003) (by norm_num)
theorem B1559677 : Blo 1385512 1559677 := bbase (se 3 (by rfl) ⟨292439, by rfl⟩ : syracuseStep 1559677 = 584879) (by norm_num)
theorem B2632837 : Blo 1385512 2632837 := bbase (se 4 (by rfl) ⟨246828, by rfl⟩ : syracuseStep 2632837 = 493657) (by norm_num)
theorem B3124373 : Blo 1385512 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B1559713 : Blo 1385512 1559713 := bbase (se 2 (by rfl) ⟨584892, by rfl⟩ : syracuseStep 1559713 = 1169785) (by norm_num)
theorem B1559749 : Blo 1385512 1559749 := bbase (se 4 (by rfl) ⟨146226, by rfl⟩ : syracuseStep 1559749 = 292453) (by norm_num)
theorem B1666261 : Blo 1385512 1666261 := bbase (se 7 (by rfl) ⟨19526, by rfl⟩ : syracuseStep 1666261 = 39053) (by norm_num)
theorem B3509477 : Blo 1385512 3509477 := bbase (se 4 (by rfl) ⟨329013, by rfl⟩ : syracuseStep 3509477 = 658027) (by norm_num)
theorem B1559785 : Blo 1385512 1559785 := bbase (se 2 (by rfl) ⟨584919, by rfl⟩ : syracuseStep 1559785 = 1169839) (by norm_num)
theorem B1559821 : Blo 1385512 1559821 := bbase (se 3 (by rfl) ⟨292466, by rfl⟩ : syracuseStep 1559821 = 584933) (by norm_num)
theorem B2632981 : Blo 1385512 2632981 := bbase (se 6 (by rfl) ⟨61710, by rfl⟩ : syracuseStep 2632981 = 123421) (by norm_num)
theorem B2338085 : Blo 1385512 2338085 := bbase (se 4 (by rfl) ⟨219195, by rfl⟩ : syracuseStep 2338085 = 438391) (by norm_num)
theorem B1559857 : Blo 1385512 1559857 := bbase (se 2 (by rfl) ⟨584946, by rfl⟩ : syracuseStep 1559857 = 1169893) (by norm_num)
theorem B7015733 : Blo 1385512 7015733 := bbase (se 5 (by rfl) ⟨328862, by rfl⟩ : syracuseStep 7015733 = 657725) (by norm_num)
theorem B1559893 : Blo 1385512 1559893 := bbase (se 11 (by rfl) ⟨1142, by rfl⟩ : syracuseStep 1559893 = 2285) (by norm_num)
theorem B1559929 : Blo 1385512 1559929 := bbase (se 2 (by rfl) ⟨584973, by rfl⟩ : syracuseStep 1559929 = 1169947) (by norm_num)
theorem B3378557 : Blo 1385512 3378557 := bbase (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) (by norm_num)
theorem B1559965 : Blo 1385512 1559965 := bbase (se 3 (by rfl) ⟨292493, by rfl⟩ : syracuseStep 1559965 = 584987) (by norm_num)
theorem B2338213 : Blo 1385512 2338213 := bbase (se 4 (by rfl) ⟨219207, by rfl⟩ : syracuseStep 2338213 = 438415) (by norm_num)
theorem B3509669 : Blo 1385512 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B1666477 : Blo 1385512 1666477 := bbase (se 3 (by rfl) ⟨312464, by rfl⟩ : syracuseStep 1666477 = 624929) (by norm_num)
theorem B2633141 : Blo 1385512 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B1560001 : Blo 1385512 1560001 := bbase (se 2 (by rfl) ⟨585000, by rfl⟩ : syracuseStep 1560001 = 1170001) (by norm_num)
theorem B5336533 : Blo 1385512 5336533 := bbase (se 7 (by rfl) ⟨62537, by rfl⟩ : syracuseStep 5336533 = 125075) (by norm_num)
theorem B1560037 : Blo 1385512 1560037 := bbase (se 4 (by rfl) ⟨146253, by rfl⟩ : syracuseStep 1560037 = 292507) (by norm_num)
theorem B4681205 : Blo 1385512 4681205 := bbase (se 5 (by rfl) ⟨219431, by rfl⟩ : syracuseStep 4681205 = 438863) (by norm_num)
theorem B2338301 : Blo 1385512 2338301 := bbase (se 3 (by rfl) ⟨438431, by rfl⟩ : syracuseStep 2338301 = 876863) (by norm_num)
theorem B1560073 : Blo 1385512 1560073 := bbase (se 2 (by rfl) ⟨585027, by rfl⟩ : syracuseStep 1560073 = 1170055) (by norm_num)
theorem B1560109 : Blo 1385512 1560109 := bbase (se 3 (by rfl) ⟨292520, by rfl⟩ : syracuseStep 1560109 = 585041) (by norm_num)
theorem B1404469 : Blo 1385512 1404469 := bbase (se 5 (by rfl) ⟨65834, by rfl⟩ : syracuseStep 1404469 = 131669) (by norm_num)
theorem B2633285 : Blo 1385512 2633285 := bbase (se 4 (by rfl) ⟨246870, by rfl⟩ : syracuseStep 2633285 = 493741) (by norm_num)
theorem B1560145 : Blo 1385512 1560145 := bbase (se 2 (by rfl) ⟨585054, by rfl⟩ : syracuseStep 1560145 = 1170109) (by norm_num)
theorem B1560181 : Blo 1385512 1560181 := bbase (se 5 (by rfl) ⟨73133, by rfl⟩ : syracuseStep 1560181 = 146267) (by norm_num)
theorem B2338429 : Blo 1385512 2338429 := bbase (se 3 (by rfl) ⟨438455, by rfl⟩ : syracuseStep 2338429 = 876911) (by norm_num)
theorem B3329677 : Blo 1385512 3329677 := bbase (se 3 (by rfl) ⟨624314, by rfl⟩ : syracuseStep 3329677 = 1248629) (by norm_num)
theorem B4443797 : Blo 1385512 4443797 := bbase (se 6 (by rfl) ⟨104151, by rfl⟩ : syracuseStep 4443797 = 208303) (by norm_num)
theorem B1560217 : Blo 1385512 1560217 := bbase (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) (by norm_num)
theorem B3747509 : Blo 1385512 3747509 := bbase (se 5 (by rfl) ⟨175664, by rfl⟩ : syracuseStep 3747509 = 351329) (by norm_num)
theorem B1560253 : Blo 1385512 1560253 := bbase (se 3 (by rfl) ⟨292547, by rfl⟩ : syracuseStep 1560253 = 585095) (by norm_num)
theorem B2338517 : Blo 1385512 2338517 := bbase (se 7 (by rfl) ⟨27404, by rfl⟩ : syracuseStep 2338517 = 54809) (by norm_num)
theorem B1560289 : Blo 1385512 1560289 := bbase (se 2 (by rfl) ⟨585108, by rfl⟩ : syracuseStep 1560289 = 1170217) (by norm_num)
theorem B3510013 : Blo 1385512 3510013 := bbase (se 3 (by rfl) ⟨658127, by rfl⟩ : syracuseStep 3510013 = 1316255) (by norm_num)
theorem B1560325 : Blo 1385512 1560325 := bbase (se 4 (by rfl) ⟨146280, by rfl⟩ : syracuseStep 1560325 = 292561) (by norm_num)
theorem B5918501 : Blo 1385512 5918501 := bbase (se 4 (by rfl) ⟨554859, by rfl⟩ : syracuseStep 5918501 = 1109719) (by norm_num)
theorem B1560361 : Blo 1385512 1560361 := bbase (se 2 (by rfl) ⟨585135, by rfl⟩ : syracuseStep 1560361 = 1170271) (by norm_num)
theorem B1560397 : Blo 1385512 1560397 := bbase (se 3 (by rfl) ⟨292574, by rfl⟩ : syracuseStep 1560397 = 585149) (by norm_num)
theorem B2338645 : Blo 1385512 2338645 := bbase (se 9 (by rfl) ⟨6851, by rfl⟩ : syracuseStep 2338645 = 13703) (by norm_num)
theorem B2633573 : Blo 1385512 2633573 := bbase (se 4 (by rfl) ⟨246897, by rfl⟩ : syracuseStep 2633573 = 493795) (by norm_num)
theorem B3510125 : Blo 1385512 3510125 := bbase (se 3 (by rfl) ⟨658148, by rfl⟩ : syracuseStep 3510125 = 1316297) (by norm_num)
theorem B1560433 : Blo 1385512 1560433 := bbase (se 2 (by rfl) ⟨585162, by rfl⟩ : syracuseStep 1560433 = 1170325) (by norm_num)
theorem B2961301 : Blo 1385512 2961301 := bbase (se 6 (by rfl) ⟨69405, by rfl⟩ : syracuseStep 2961301 = 138811) (by norm_num)
theorem B1560469 : Blo 1385512 1560469 := bbase (se 6 (by rfl) ⟨36573, by rfl⟩ : syracuseStep 1560469 = 73147) (by norm_num)
theorem B4681637 : Blo 1385512 4681637 := bbase (se 4 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 4681637 = 877807) (by norm_num)
theorem B2338733 : Blo 1385512 2338733 := bbase (se 3 (by rfl) ⟨438512, by rfl⟩ : syracuseStep 2338733 = 877025) (by norm_num)
theorem B1560505 : Blo 1385512 1560505 := bbase (se 2 (by rfl) ⟨585189, by rfl⟩ : syracuseStep 1560505 = 1170379) (by norm_num)
theorem B17756117 : Blo 1385512 17756117 := bbase (se 7 (by rfl) ⟨208079, by rfl⟩ : syracuseStep 17756117 = 416159) (by norm_num)
theorem B1560541 : Blo 1385512 1560541 := bbase (se 3 (by rfl) ⟨292601, by rfl⟩ : syracuseStep 1560541 = 585203) (by norm_num)
theorem B2633725 : Blo 1385512 2633725 := bbase (se 3 (by rfl) ⟨493823, by rfl⟩ : syracuseStep 2633725 = 987647) (by norm_num)
theorem B1560577 : Blo 1385512 1560577 := bbase (se 2 (by rfl) ⟨585216, by rfl⟩ : syracuseStep 1560577 = 1170433) (by norm_num)
theorem B2109445 : Blo 1385512 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B5918741 : Blo 1385512 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B1560613 : Blo 1385512 1560613 := bbase (se 4 (by rfl) ⟨146307, by rfl⟩ : syracuseStep 1560613 = 292615) (by norm_num)
theorem B2338861 : Blo 1385512 2338861 := bbase (se 3 (by rfl) ⟨438536, by rfl⟩ : syracuseStep 2338861 = 877073) (by norm_num)
theorem B3510317 : Blo 1385512 3510317 := bbase (se 3 (by rfl) ⟨658184, by rfl⟩ : syracuseStep 3510317 = 1316369) (by norm_num)
theorem B1560649 : Blo 1385512 1560649 := bbase (se 2 (by rfl) ⟨585243, by rfl⟩ : syracuseStep 1560649 = 1170487) (by norm_num)
theorem B33747029 : Blo 1385512 33747029 := bbase (se 8 (by rfl) ⟨197736, by rfl⟩ : syracuseStep 33747029 = 395473) (by norm_num)
theorem B7499861 : Blo 1385512 7499861 := bbase (se 8 (by rfl) ⟨43944, by rfl⟩ : syracuseStep 7499861 = 87889) (by norm_num)
theorem B3747941 : Blo 1385512 3747941 := bbase (se 4 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 3747941 = 702739) (by norm_num)
theorem B1560685 : Blo 1385512 1560685 := bbase (se 3 (by rfl) ⟨292628, by rfl⟩ : syracuseStep 1560685 = 585257) (by norm_num)
theorem B2338949 : Blo 1385512 2338949 := bbase (se 4 (by rfl) ⟨219276, by rfl⟩ : syracuseStep 2338949 = 438553) (by norm_num)
theorem B1560721 : Blo 1385512 1560721 := bbase (se 2 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 1560721 = 1170541) (by norm_num)
theorem B1560757 : Blo 1385512 1560757 := bbase (se 5 (by rfl) ⟨73160, by rfl⟩ : syracuseStep 1560757 = 146321) (by norm_num)
theorem B1560793 : Blo 1385512 1560793 := bbase (se 2 (by rfl) ⟨585297, by rfl⟩ : syracuseStep 1560793 = 1170595) (by norm_num)
theorem B1405153 : Blo 1385512 1405153 := bbase (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) (by norm_num)
theorem B1560829 : Blo 1385512 1560829 := bbase (se 3 (by rfl) ⟨292655, by rfl⟩ : syracuseStep 1560829 = 585311) (by norm_num)
theorem B2339077 : Blo 1385512 2339077 := bbase (se 4 (by rfl) ⟨219288, by rfl⟩ : syracuseStep 2339077 = 438577) (by norm_num)
theorem B2371853 : Blo 1385512 2371853 := bbase (se 3 (by rfl) ⟨444722, by rfl⟩ : syracuseStep 2371853 = 889445) (by norm_num)
theorem B2961677 : Blo 1385512 2961677 := bbase (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) (by norm_num)
theorem B1560865 : Blo 1385512 1560865 := bbase (se 2 (by rfl) ⟨585324, by rfl⟩ : syracuseStep 1560865 = 1170649) (by norm_num)
theorem B3330341 : Blo 1385512 3330341 := bbase (se 4 (by rfl) ⟨312219, by rfl⟩ : syracuseStep 3330341 = 624439) (by norm_num)
theorem B2634029 : Blo 1385512 2634029 := bbase (se 3 (by rfl) ⟨493880, by rfl⟩ : syracuseStep 2634029 = 987761) (by norm_num)
theorem B1560901 : Blo 1385512 1560901 := bbase (se 4 (by rfl) ⟨146334, by rfl⟩ : syracuseStep 1560901 = 292669) (by norm_num)
theorem B4682069 : Blo 1385512 4682069 := bbase (se 10 (by rfl) ⟨6858, by rfl⟩ : syracuseStep 4682069 = 13717) (by norm_num)
theorem B2339165 : Blo 1385512 2339165 := bbase (se 3 (by rfl) ⟨438593, by rfl⟩ : syracuseStep 2339165 = 877187) (by norm_num)
theorem B1560937 : Blo 1385512 1560937 := bbase (se 2 (by rfl) ⟨585351, by rfl⟩ : syracuseStep 1560937 = 1170703) (by norm_num)
theorem B3117437 : Blo 1385512 3117437 := bbase (se 3 (by rfl) ⟨584519, by rfl⟩ : syracuseStep 3117437 = 1169039) (by norm_num)
theorem B3510661 : Blo 1385512 3510661 := bbase (se 4 (by rfl) ⟨329124, by rfl⟩ : syracuseStep 3510661 = 658249) (by norm_num)
theorem B5624245 : Blo 1385512 5624245 := bbase (se 5 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 5624245 = 527273) (by norm_num)
theorem B3117509 : Blo 1385512 3117509 := bbase (se 4 (by rfl) ⟨292266, by rfl⟩ : syracuseStep 3117509 = 584533) (by norm_num)
theorem B2339293 : Blo 1385512 2339293 := bbase (se 3 (by rfl) ⟨438617, by rfl⟩ : syracuseStep 2339293 = 877235) (by norm_num)
theorem B3510773 : Blo 1385512 3510773 := bbase (se 5 (by rfl) ⟨164567, by rfl⟩ : syracuseStep 3510773 = 329135) (by norm_num)
theorem B3117581 : Blo 1385512 3117581 := bbase (se 3 (by rfl) ⟨584546, by rfl⟩ : syracuseStep 3117581 = 1169093) (by norm_num)
theorem B2339381 : Blo 1385512 2339381 := bbase (se 5 (by rfl) ⟨109658, by rfl⟩ : syracuseStep 2339381 = 219317) (by norm_num)
theorem B13333045 : Blo 1385512 13333045 := bbase (se 5 (by rfl) ⟨624986, by rfl⟩ : syracuseStep 13333045 = 1249973) (by norm_num)
theorem B7017029 : Blo 1385512 7017029 := bbase (se 4 (by rfl) ⟨657846, by rfl⟩ : syracuseStep 7017029 = 1315693) (by norm_num)
theorem B3117653 : Blo 1385512 3117653 := bbase (se 8 (by rfl) ⟨18267, by rfl⟩ : syracuseStep 3117653 = 36535) (by norm_num)
theorem B5263973 : Blo 1385512 5263973 := bbase (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) (by norm_num)
theorem B7901813 : Blo 1385512 7901813 := bbase (se 5 (by rfl) ⟨370397, by rfl⟩ : syracuseStep 7901813 = 740795) (by norm_num)
theorem B3117725 : Blo 1385512 3117725 := bbase (se 3 (by rfl) ⟨584573, by rfl⟩ : syracuseStep 3117725 = 1169147) (by norm_num)
theorem B2339509 : Blo 1385512 2339509 := bbase (se 5 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 2339509 = 219329) (by norm_num)
theorem B3510965 : Blo 1385512 3510965 := bbase (se 5 (by rfl) ⟨164576, by rfl⟩ : syracuseStep 3510965 = 329153) (by norm_num)
theorem B3117797 : Blo 1385512 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1405669 : Blo 1385512 1405669 := bbase (se 4 (by rfl) ⟨131781, by rfl⟩ : syracuseStep 1405669 = 263563) (by norm_num)
theorem B4682501 : Blo 1385512 4682501 := bbase (se 4 (by rfl) ⟨438984, by rfl⟩ : syracuseStep 4682501 = 877969) (by norm_num)
theorem B2339597 : Blo 1385512 2339597 := bbase (se 3 (by rfl) ⟨438674, by rfl⟩ : syracuseStep 2339597 = 877349) (by norm_num)
theorem B3117869 : Blo 1385512 3117869 := bbase (se 3 (by rfl) ⟨584600, by rfl⟩ : syracuseStep 3117869 = 1169201) (by norm_num)
theorem B2282309 : Blo 1385512 2282309 := bbase (se 4 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 2282309 = 427933) (by norm_num)
theorem B2667349 : Blo 1385512 2667349 := bbase (se 9 (by rfl) ⟨7814, by rfl⟩ : syracuseStep 2667349 = 15629) (by norm_num)
theorem B3117941 : Blo 1385512 3117941 := bbase (se 5 (by rfl) ⟨146153, by rfl⟩ : syracuseStep 3117941 = 292307) (by norm_num)
theorem B1479557 : Blo 1385512 1479557 := bbase (se 4 (by rfl) ⟨138708, by rfl⟩ : syracuseStep 1479557 = 277417) (by norm_num)
theorem B5264261 : Blo 1385512 5264261 := bbase (se 4 (by rfl) ⟨493524, by rfl⟩ : syracuseStep 5264261 = 987049) (by norm_num)
theorem B2339725 : Blo 1385512 2339725 := bbase (se 3 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 2339725 = 877397) (by norm_num)
theorem B3118013 : Blo 1385512 3118013 := bbase (se 3 (by rfl) ⟨584627, by rfl⟩ : syracuseStep 3118013 = 1169255) (by norm_num)
theorem B2339813 : Blo 1385512 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B3118085 : Blo 1385512 3118085 := bbase (se 4 (by rfl) ⟨292320, by rfl⟩ : syracuseStep 3118085 = 584641) (by norm_num)
theorem B3511309 : Blo 1385512 3511309 := bbase (se 3 (by rfl) ⟨658370, by rfl⟩ : syracuseStep 3511309 = 1316741) (by norm_num)
theorem B1479745 : Blo 1385512 1479745 := bbase (se 2 (by rfl) ⟨554904, by rfl⟩ : syracuseStep 1479745 = 1109809) (by norm_num)
theorem B3118157 : Blo 1385512 3118157 := bbase (se 3 (by rfl) ⟨584654, by rfl⟩ : syracuseStep 3118157 = 1169309) (by norm_num)
theorem B2339941 : Blo 1385512 2339941 := bbase (se 4 (by rfl) ⟨219369, by rfl⟩ : syracuseStep 2339941 = 438739) (by norm_num)
theorem B3511421 : Blo 1385512 3511421 := bbase (se 3 (by rfl) ⟨658391, by rfl⟩ : syracuseStep 3511421 = 1316783) (by norm_num)
theorem B3118229 : Blo 1385512 3118229 := bbase (se 6 (by rfl) ⟨73083, by rfl⟩ : syracuseStep 3118229 = 146167) (by norm_num)
theorem B2340029 : Blo 1385512 2340029 := bbase (se 3 (by rfl) ⟨438755, by rfl⟩ : syracuseStep 2340029 = 877511) (by norm_num)
theorem B3118301 : Blo 1385512 3118301 := bbase (se 3 (by rfl) ⟨584681, by rfl⟩ : syracuseStep 3118301 = 1169363) (by norm_num)
theorem B3118373 : Blo 1385512 3118373 := bbase (se 4 (by rfl) ⟨292347, by rfl⟩ : syracuseStep 3118373 = 584695) (by norm_num)
theorem B2340157 : Blo 1385512 2340157 := bbase (se 3 (by rfl) ⟨438779, by rfl⟩ : syracuseStep 2340157 = 877559) (by norm_num)
theorem B3511613 : Blo 1385512 3511613 := bbase (se 3 (by rfl) ⟨658427, by rfl⟩ : syracuseStep 3511613 = 1316855) (by norm_num)
theorem B3118445 : Blo 1385512 3118445 := bbase (se 3 (by rfl) ⟨584708, by rfl⟩ : syracuseStep 3118445 = 1169417) (by norm_num)
theorem B2340245 : Blo 1385512 2340245 := bbase (se 6 (by rfl) ⟨54849, by rfl⟩ : syracuseStep 2340245 = 109699) (by norm_num)
theorem B4216229 : Blo 1385512 4216229 := bbase (se 4 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 4216229 = 790543) (by norm_num)
theorem B3118517 : Blo 1385512 3118517 := bbase (se 5 (by rfl) ⟨146180, by rfl⟩ : syracuseStep 3118517 = 292361) (by norm_num)
theorem B3945941 : Blo 1385512 3945941 := bbase (se 7 (by rfl) ⟨46241, by rfl⟩ : syracuseStep 3945941 = 92483) (by norm_num)
theorem B3118589 : Blo 1385512 3118589 := bbase (se 3 (by rfl) ⟨584735, by rfl⟩ : syracuseStep 3118589 = 1169471) (by norm_num)
theorem B2340373 : Blo 1385512 2340373 := bbase (se 6 (by rfl) ⟨54852, by rfl⟩ : syracuseStep 2340373 = 109705) (by norm_num)
theorem B3118661 : Blo 1385512 3118661 := bbase (se 4 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 3118661 = 584749) (by norm_num)
theorem B2078285 : Blo 1385512 2078285 := bbase (se 3 (by rfl) ⟨389678, by rfl⟩ : syracuseStep 2078285 = 779357) (by norm_num)
theorem B2078309 : Blo 1385512 2078309 := bbase (se 4 (by rfl) ⟨194841, by rfl⟩ : syracuseStep 2078309 = 389683) (by norm_num)
theorem B2340461 : Blo 1385512 2340461 := bbase (se 3 (by rfl) ⟨438836, by rfl⟩ : syracuseStep 2340461 = 877673) (by norm_num)
theorem B2078333 : Blo 1385512 2078333 := bbase (se 3 (by rfl) ⟨389687, by rfl⟩ : syracuseStep 2078333 = 779375) (by norm_num)
theorem B3118733 : Blo 1385512 3118733 := bbase (se 3 (by rfl) ⟨584762, by rfl⟩ : syracuseStep 3118733 = 1169525) (by norm_num)
theorem B2078357 : Blo 1385512 2078357 := bbase (se 6 (by rfl) ⟨48711, by rfl⟩ : syracuseStep 2078357 = 97423) (by norm_num)
theorem B3511957 : Blo 1385512 3511957 := bbase (se 6 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 3511957 = 164623) (by norm_num)
theorem B2078381 : Blo 1385512 2078381 := bbase (se 3 (by rfl) ⟨389696, by rfl⟩ : syracuseStep 2078381 = 779393) (by norm_num)
theorem B2078405 : Blo 1385512 2078405 := bbase (se 4 (by rfl) ⟨194850, by rfl⟩ : syracuseStep 2078405 = 389701) (by norm_num)
theorem B3118805 : Blo 1385512 3118805 := bbase (se 7 (by rfl) ⟨36548, by rfl⟩ : syracuseStep 3118805 = 73097) (by norm_num)
theorem B2078429 : Blo 1385512 2078429 := bbase (se 3 (by rfl) ⟨389705, by rfl⟩ : syracuseStep 2078429 = 779411) (by norm_num)
theorem B2340589 : Blo 1385512 2340589 := bbase (se 3 (by rfl) ⟨438860, by rfl⟩ : syracuseStep 2340589 = 877721) (by norm_num)
theorem B2078453 : Blo 1385512 2078453 := bbase (se 5 (by rfl) ⟨97427, by rfl⟩ : syracuseStep 2078453 = 194855) (by norm_num)
theorem B3512069 : Blo 1385512 3512069 := bbase (se 4 (by rfl) ⟨329256, by rfl⟩ : syracuseStep 3512069 = 658513) (by norm_num)
theorem B2078477 : Blo 1385512 2078477 := bbase (se 3 (by rfl) ⟨389714, by rfl⟩ : syracuseStep 2078477 = 779429) (by norm_num)
theorem B3118877 : Blo 1385512 3118877 := bbase (se 3 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 3118877 = 1169579) (by norm_num)
theorem B2078501 : Blo 1385512 2078501 := bbase (se 4 (by rfl) ⟨194859, by rfl⟩ : syracuseStep 2078501 = 389719) (by norm_num)
theorem B2078525 : Blo 1385512 2078525 := bbase (se 3 (by rfl) ⟨389723, by rfl⟩ : syracuseStep 2078525 = 779447) (by norm_num)
theorem B2340677 : Blo 1385512 2340677 := bbase (se 4 (by rfl) ⟨219438, by rfl⟩ : syracuseStep 2340677 = 438877) (by norm_num)
theorem B2078549 : Blo 1385512 2078549 := bbase (se 9 (by rfl) ⟨6089, by rfl⟩ : syracuseStep 2078549 = 12179) (by norm_num)
theorem B7018325 : Blo 1385512 7018325 := bbase (se 9 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 7018325 = 41123) (by norm_num)
theorem B3118949 : Blo 1385512 3118949 := bbase (se 4 (by rfl) ⟨292401, by rfl⟩ : syracuseStep 3118949 = 584803) (by norm_num)
theorem B2078573 : Blo 1385512 2078573 := bbase (se 3 (by rfl) ⟨389732, by rfl⟩ : syracuseStep 2078573 = 779465) (by norm_num)
theorem B1480565 : Blo 1385512 1480565 := bbase (se 5 (by rfl) ⟨69401, by rfl⟩ : syracuseStep 1480565 = 138803) (by norm_num)
theorem B2963317 : Blo 1385512 2963317 := bbase (se 5 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 2963317 = 277811) (by norm_num)
theorem B2078597 : Blo 1385512 2078597 := bbase (se 4 (by rfl) ⟨194868, by rfl⟩ : syracuseStep 2078597 = 389737) (by norm_num)
theorem B2078621 : Blo 1385512 2078621 := bbase (se 3 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 2078621 = 779483) (by norm_num)
theorem B3119021 : Blo 1385512 3119021 := bbase (se 3 (by rfl) ⟨584816, by rfl⟩ : syracuseStep 3119021 = 1169633) (by norm_num)
theorem B2078645 : Blo 1385512 2078645 := bbase (se 5 (by rfl) ⟨97436, by rfl⟩ : syracuseStep 2078645 = 194873) (by norm_num)
theorem B2340805 : Blo 1385512 2340805 := bbase (se 4 (by rfl) ⟨219450, by rfl⟩ : syracuseStep 2340805 = 438901) (by norm_num)
theorem B2078669 : Blo 1385512 2078669 := bbase (se 3 (by rfl) ⟨389750, by rfl⟩ : syracuseStep 2078669 = 779501) (by norm_num)
theorem B2078693 : Blo 1385512 2078693 := bbase (se 4 (by rfl) ⟨194877, by rfl⟩ : syracuseStep 2078693 = 389755) (by norm_num)
theorem B3119093 : Blo 1385512 3119093 := bbase (se 5 (by rfl) ⟨146207, by rfl⟩ : syracuseStep 3119093 = 292415) (by norm_num)
theorem B2078717 : Blo 1385512 2078717 := bbase (se 3 (by rfl) ⟨389759, by rfl⟩ : syracuseStep 2078717 = 779519) (by norm_num)
theorem B2078741 : Blo 1385512 2078741 := bbase (se 6 (by rfl) ⟨48720, by rfl⟩ : syracuseStep 2078741 = 97441) (by norm_num)
theorem B3332117 : Blo 1385512 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B2340893 : Blo 1385512 2340893 := bbase (se 3 (by rfl) ⟨438917, by rfl⟩ : syracuseStep 2340893 = 877835) (by norm_num)
theorem B5265445 : Blo 1385512 5265445 := bbase (se 4 (by rfl) ⟨493635, by rfl⟩ : syracuseStep 5265445 = 987271) (by norm_num)
theorem B2078765 : Blo 1385512 2078765 := bbase (se 3 (by rfl) ⟨389768, by rfl⟩ : syracuseStep 2078765 = 779537) (by norm_num)
theorem B3119165 : Blo 1385512 3119165 := bbase (se 3 (by rfl) ⟨584843, by rfl⟩ : syracuseStep 3119165 = 1169687) (by norm_num)
theorem B2078789 : Blo 1385512 2078789 := bbase (se 4 (by rfl) ⟨194886, by rfl⟩ : syracuseStep 2078789 = 389773) (by norm_num)
theorem B2078813 : Blo 1385512 2078813 := bbase (se 3 (by rfl) ⟨389777, by rfl⟩ : syracuseStep 2078813 = 779555) (by norm_num)
theorem B2078837 : Blo 1385512 2078837 := bbase (se 5 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 2078837 = 194891) (by norm_num)
theorem B3119237 : Blo 1385512 3119237 := bbase (se 4 (by rfl) ⟨292428, by rfl⟩ : syracuseStep 3119237 = 584857) (by norm_num)
theorem B2078861 : Blo 1385512 2078861 := bbase (se 3 (by rfl) ⟨389786, by rfl⟩ : syracuseStep 2078861 = 779573) (by norm_num)
theorem B2341021 : Blo 1385512 2341021 := bbase (se 3 (by rfl) ⟨438941, by rfl⟩ : syracuseStep 2341021 = 877883) (by norm_num)
theorem B2078885 : Blo 1385512 2078885 := bbase (se 4 (by rfl) ⟨194895, by rfl⟩ : syracuseStep 2078885 = 389791) (by norm_num)
theorem B2078909 : Blo 1385512 2078909 := bbase (se 3 (by rfl) ⟨389795, by rfl⟩ : syracuseStep 2078909 = 779591) (by norm_num)
theorem B3119309 : Blo 1385512 3119309 := bbase (se 3 (by rfl) ⟨584870, by rfl⟩ : syracuseStep 3119309 = 1169741) (by norm_num)
theorem B2078933 : Blo 1385512 2078933 := bbase (se 7 (by rfl) ⟨24362, by rfl⟩ : syracuseStep 2078933 = 48725) (by norm_num)
theorem B10533077 : Blo 1385512 10533077 := bbase (se 7 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 10533077 = 246869) (by norm_num)
theorem B2078957 : Blo 1385512 2078957 := bbase (se 3 (by rfl) ⟨389804, by rfl⟩ : syracuseStep 2078957 = 779609) (by norm_num)
theorem B2341109 : Blo 1385512 2341109 := bbase (se 5 (by rfl) ⟨109739, by rfl⟩ : syracuseStep 2341109 = 219479) (by norm_num)
theorem B2078981 : Blo 1385512 2078981 := bbase (se 4 (by rfl) ⟨194904, by rfl⟩ : syracuseStep 2078981 = 389809) (by norm_num)
theorem B5921029 : Blo 1385512 5921029 := bbase (se 4 (by rfl) ⟨555096, by rfl⟩ : syracuseStep 5921029 = 1110193) (by norm_num)
theorem B3119381 : Blo 1385512 3119381 := bbase (se 6 (by rfl) ⟨73110, by rfl⟩ : syracuseStep 3119381 = 146221) (by norm_num)
theorem B2079005 : Blo 1385512 2079005 := bbase (se 3 (by rfl) ⟨389813, by rfl⟩ : syracuseStep 2079005 = 779627) (by norm_num)
theorem B1481009 : Blo 1385512 1481009 := bbase (se 2 (by rfl) ⟨555378, by rfl⟩ : syracuseStep 1481009 = 1110757) (by norm_num)
theorem B2079029 : Blo 1385512 2079029 := bbase (se 5 (by rfl) ⟨97454, by rfl⟩ : syracuseStep 2079029 = 194909) (by norm_num)
theorem B2079053 : Blo 1385512 2079053 := bbase (se 3 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 2079053 = 779645) (by norm_num)
theorem B5265749 : Blo 1385512 5265749 := bbase (se 10 (by rfl) ⟨7713, by rfl⟩ : syracuseStep 5265749 = 15427) (by norm_num)
theorem B3119453 : Blo 1385512 3119453 := bbase (se 3 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 3119453 = 1169795) (by norm_num)
theorem B3160421 : Blo 1385512 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B2079077 : Blo 1385512 2079077 := bbase (se 4 (by rfl) ⟨194913, by rfl⟩ : syracuseStep 2079077 = 389827) (by norm_num)
theorem B2341237 : Blo 1385512 2341237 := bbase (se 5 (by rfl) ⟨109745, by rfl⟩ : syracuseStep 2341237 = 219491) (by norm_num)
theorem B2079101 : Blo 1385512 2079101 := bbase (se 3 (by rfl) ⟨389831, by rfl⟩ : syracuseStep 2079101 = 779663) (by norm_num)
theorem B1898893 : Blo 1385512 1898893 := bbase (se 3 (by rfl) ⟨356042, by rfl⟩ : syracuseStep 1898893 = 712085) (by norm_num)
theorem B2079125 : Blo 1385512 2079125 := bbase (se 6 (by rfl) ⟨48729, by rfl⟩ : syracuseStep 2079125 = 97459) (by norm_num)
theorem B3119525 : Blo 1385512 3119525 := bbase (se 4 (by rfl) ⟨292455, by rfl⟩ : syracuseStep 3119525 = 584911) (by norm_num)
theorem B2079149 : Blo 1385512 2079149 := bbase (se 3 (by rfl) ⟨389840, by rfl⟩ : syracuseStep 2079149 = 779681) (by norm_num)
theorem B2079173 : Blo 1385512 2079173 := bbase (se 4 (by rfl) ⟨194922, by rfl⟩ : syracuseStep 2079173 = 389845) (by norm_num)
theorem B2341325 : Blo 1385512 2341325 := bbase (se 3 (by rfl) ⟨438998, by rfl⟩ : syracuseStep 2341325 = 877997) (by norm_num)
theorem B16857557 : Blo 1385512 16857557 := bbase (se 7 (by rfl) ⟨197549, by rfl⟩ : syracuseStep 16857557 = 395099) (by norm_num)
theorem B2079197 : Blo 1385512 2079197 := bbase (se 3 (by rfl) ⟨389849, by rfl⟩ : syracuseStep 2079197 = 779699) (by norm_num)
theorem B3119597 : Blo 1385512 3119597 := bbase (se 3 (by rfl) ⟨584924, by rfl⟩ : syracuseStep 3119597 = 1169849) (by norm_num)
theorem B2079221 : Blo 1385512 2079221 := bbase (se 5 (by rfl) ⟨97463, by rfl⟩ : syracuseStep 2079221 = 194927) (by norm_num)
theorem B8886773 : Blo 1385512 8886773 := bbase (se 5 (by rfl) ⟨416567, by rfl⟩ : syracuseStep 8886773 = 833135) (by norm_num)
theorem B2079245 : Blo 1385512 2079245 := bbase (se 3 (by rfl) ⟨389858, by rfl⟩ : syracuseStep 2079245 = 779717) (by norm_num)
theorem B1972765 : Blo 1385512 1972765 := bbase (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) (by norm_num)
theorem B2079269 : Blo 1385512 2079269 := bbase (se 4 (by rfl) ⟨194931, by rfl⟩ : syracuseStep 2079269 = 389863) (by norm_num)
theorem B1481257 : Blo 1385512 1481257 := bbase (se 2 (by rfl) ⟨555471, by rfl⟩ : syracuseStep 1481257 = 1110943) (by norm_num)
theorem B3119669 : Blo 1385512 3119669 := bbase (se 5 (by rfl) ⟨146234, by rfl⟩ : syracuseStep 3119669 = 292469) (by norm_num)
theorem B2497085 : Blo 1385512 2497085 := bbase (se 3 (by rfl) ⟨468203, by rfl⟩ : syracuseStep 2497085 = 936407) (by norm_num)
theorem B2079293 : Blo 1385512 2079293 := bbase (se 3 (by rfl) ⟨389867, by rfl⟩ : syracuseStep 2079293 = 779735) (by norm_num)
theorem B2079317 : Blo 1385512 2079317 := bbase (se 8 (by rfl) ⟨12183, by rfl⟩ : syracuseStep 2079317 = 24367) (by norm_num)
theorem B2079341 : Blo 1385512 2079341 := bbase (se 3 (by rfl) ⟨389876, by rfl⟩ : syracuseStep 2079341 = 779753) (by norm_num)
theorem B10525301 : Blo 1385512 10525301 := bbase (se 5 (by rfl) ⟨493373, by rfl⟩ : syracuseStep 10525301 = 986747) (by norm_num)
theorem B3947125 : Blo 1385512 3947125 := bbase (se 5 (by rfl) ⟨185021, by rfl⟩ : syracuseStep 3947125 = 370043) (by norm_num)
theorem B3119741 : Blo 1385512 3119741 := bbase (se 3 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 3119741 = 1169903) (by norm_num)
theorem B2079365 : Blo 1385512 2079365 := bbase (se 4 (by rfl) ⟨194940, by rfl⟩ : syracuseStep 2079365 = 389881) (by norm_num)
theorem B11844245 : Blo 1385512 11844245 := bbase (se 6 (by rfl) ⟨277599, by rfl⟩ : syracuseStep 11844245 = 555199) (by norm_num)
theorem B2079389 : Blo 1385512 2079389 := bbase (se 3 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 2079389 = 779771) (by norm_num)
theorem B2079413 : Blo 1385512 2079413 := bbase (se 5 (by rfl) ⟨97472, by rfl⟩ : syracuseStep 2079413 = 194945) (by norm_num)
theorem B3119813 : Blo 1385512 3119813 := bbase (se 4 (by rfl) ⟨292482, by rfl⟩ : syracuseStep 3119813 = 584965) (by norm_num)
theorem B2079437 : Blo 1385512 2079437 := bbase (se 3 (by rfl) ⟨389894, by rfl⟩ : syracuseStep 2079437 = 779789) (by norm_num)
theorem B2079461 : Blo 1385512 2079461 := bbase (se 4 (by rfl) ⟨194949, by rfl⟩ : syracuseStep 2079461 = 389899) (by norm_num)
theorem B2079485 : Blo 1385512 2079485 := bbase (se 3 (by rfl) ⟨389903, by rfl⟩ : syracuseStep 2079485 = 779807) (by norm_num)
theorem B3119885 : Blo 1385512 3119885 := bbase (se 3 (by rfl) ⟨584978, by rfl⟩ : syracuseStep 3119885 = 1169957) (by norm_num)
theorem B1874701 : Blo 1385512 1874701 := bbase (se 3 (by rfl) ⟨351506, by rfl⟩ : syracuseStep 1874701 = 703013) (by norm_num)
theorem B3947285 : Blo 1385512 3947285 := bbase (se 6 (by rfl) ⟨92514, by rfl⟩ : syracuseStep 3947285 = 185029) (by norm_num)
theorem B2079509 : Blo 1385512 2079509 := bbase (se 6 (by rfl) ⟨48738, by rfl⟩ : syracuseStep 2079509 = 97477) (by norm_num)
theorem B2079533 : Blo 1385512 2079533 := bbase (se 3 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 2079533 = 779825) (by norm_num)
theorem B2079557 : Blo 1385512 2079557 := bbase (se 4 (by rfl) ⟨194958, by rfl⟩ : syracuseStep 2079557 = 389917) (by norm_num)
theorem B3119957 : Blo 1385512 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B2079581 : Blo 1385512 2079581 := bbase (se 3 (by rfl) ⟨389921, by rfl⟩ : syracuseStep 2079581 = 779843) (by norm_num)
theorem B4676453 : Blo 1385512 4676453 := bbase (se 4 (by rfl) ⟨438417, by rfl⟩ : syracuseStep 4676453 = 876835) (by norm_num)
theorem B2079605 : Blo 1385512 2079605 := bbase (se 5 (by rfl) ⟨97481, by rfl⟩ : syracuseStep 2079605 = 194963) (by norm_num)
theorem B2079629 : Blo 1385512 2079629 := bbase (se 3 (by rfl) ⟨389930, by rfl⟩ : syracuseStep 2079629 = 779861) (by norm_num)
theorem B1711001 : Blo 1385512 1711001 := bbase (se 2 (by rfl) ⟨641625, by rfl⟩ : syracuseStep 1711001 = 1283251) (by norm_num)
theorem B3120029 : Blo 1385512 3120029 := bbase (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) (by norm_num)
theorem B2079653 : Blo 1385512 2079653 := bbase (se 4 (by rfl) ⟨194967, by rfl⟩ : syracuseStep 2079653 = 389935) (by norm_num)
theorem B2079677 : Blo 1385512 2079677 := bbase (se 3 (by rfl) ⟨389939, by rfl⟩ : syracuseStep 2079677 = 779879) (by norm_num)
theorem B2079701 : Blo 1385512 2079701 := bbase (se 7 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 2079701 = 48743) (by norm_num)
theorem B1580005 : Blo 1385512 1580005 := bbase (se 4 (by rfl) ⟨148125, by rfl⟩ : syracuseStep 1580005 = 296251) (by norm_num)
theorem B3120101 : Blo 1385512 3120101 := bbase (se 4 (by rfl) ⟨292509, by rfl⟩ : syracuseStep 3120101 = 585019) (by norm_num)
theorem B1874917 : Blo 1385512 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B2079725 : Blo 1385512 2079725 := bbase (se 3 (by rfl) ⟨389948, by rfl⟩ : syracuseStep 2079725 = 779897) (by norm_num)
theorem B3947525 : Blo 1385512 3947525 := bbase (se 4 (by rfl) ⟨370080, by rfl⟩ : syracuseStep 3947525 = 740161) (by norm_num)
theorem B2079749 : Blo 1385512 2079749 := bbase (se 4 (by rfl) ⟨194976, by rfl⟩ : syracuseStep 2079749 = 389953) (by norm_num)
theorem B1973261 : Blo 1385512 1973261 := bbase (se 3 (by rfl) ⟨369986, by rfl⟩ : syracuseStep 1973261 = 739973) (by norm_num)
theorem B2079773 : Blo 1385512 2079773 := bbase (se 3 (by rfl) ⟨389957, by rfl⟩ : syracuseStep 2079773 = 779915) (by norm_num)
theorem B3120173 : Blo 1385512 3120173 := bbase (se 3 (by rfl) ⟨585032, by rfl⟩ : syracuseStep 3120173 = 1170065) (by norm_num)
theorem B2079797 : Blo 1385512 2079797 := bbase (se 5 (by rfl) ⟨97490, by rfl⟩ : syracuseStep 2079797 = 194981) (by norm_num)
theorem B2079821 : Blo 1385512 2079821 := bbase (se 3 (by rfl) ⟨389966, by rfl⟩ : syracuseStep 2079821 = 779933) (by norm_num)
theorem B2079845 : Blo 1385512 2079845 := bbase (se 4 (by rfl) ⟨194985, by rfl⟩ : syracuseStep 2079845 = 389971) (by norm_num)
theorem B7019621 : Blo 1385512 7019621 := bbase (se 4 (by rfl) ⟨658089, by rfl⟩ : syracuseStep 7019621 = 1316179) (by norm_num)
theorem B3120245 : Blo 1385512 3120245 := bbase (se 5 (by rfl) ⟨146261, by rfl⟩ : syracuseStep 3120245 = 292523) (by norm_num)
theorem B2079869 : Blo 1385512 2079869 := bbase (se 3 (by rfl) ⟨389975, by rfl⟩ : syracuseStep 2079869 = 779951) (by norm_num)
theorem B2079893 : Blo 1385512 2079893 := bbase (se 6 (by rfl) ⟨48747, by rfl⟩ : syracuseStep 2079893 = 97495) (by norm_num)
theorem B2079917 : Blo 1385512 2079917 := bbase (se 3 (by rfl) ⟨389984, by rfl⟩ : syracuseStep 2079917 = 779969) (by norm_num)
theorem B3120317 : Blo 1385512 3120317 := bbase (se 3 (by rfl) ⟨585059, by rfl⟩ : syracuseStep 3120317 = 1170119) (by norm_num)
theorem B3947717 : Blo 1385512 3947717 := bbase (se 4 (by rfl) ⟨370098, by rfl⟩ : syracuseStep 3947717 = 740197) (by norm_num)
theorem B2079941 : Blo 1385512 2079941 := bbase (se 4 (by rfl) ⟨194994, by rfl⟩ : syracuseStep 2079941 = 389989) (by norm_num)
theorem B2079965 : Blo 1385512 2079965 := bbase (se 3 (by rfl) ⟨389993, by rfl⟩ : syracuseStep 2079965 = 779987) (by norm_num)
theorem B3849445 : Blo 1385512 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B1875181 : Blo 1385512 1875181 := bbase (se 3 (by rfl) ⟨351596, by rfl⟩ : syracuseStep 1875181 = 703193) (by norm_num)
theorem B2079989 : Blo 1385512 2079989 := bbase (se 5 (by rfl) ⟨97499, by rfl⟩ : syracuseStep 2079989 = 194999) (by norm_num)
theorem B3120389 : Blo 1385512 3120389 := bbase (se 4 (by rfl) ⟨292536, by rfl⟩ : syracuseStep 3120389 = 585073) (by norm_num)
theorem B2080013 : Blo 1385512 2080013 := bbase (se 3 (by rfl) ⟨390002, by rfl⟩ : syracuseStep 2080013 = 780005) (by norm_num)
theorem B4676885 : Blo 1385512 4676885 := bbase (se 6 (by rfl) ⟨109614, by rfl⟩ : syracuseStep 4676885 = 219229) (by norm_num)
theorem B6667541 : Blo 1385512 6667541 := bbase (se 6 (by rfl) ⟨156270, by rfl⟩ : syracuseStep 6667541 = 312541) (by norm_num)
theorem B2080037 : Blo 1385512 2080037 := bbase (se 4 (by rfl) ⟨195003, by rfl⟩ : syracuseStep 2080037 = 390007) (by norm_num)
theorem B2080061 : Blo 1385512 2080061 := bbase (se 3 (by rfl) ⟨390011, by rfl⟩ : syracuseStep 2080061 = 780023) (by norm_num)
theorem B3120461 : Blo 1385512 3120461 := bbase (se 3 (by rfl) ⟨585086, by rfl⟩ : syracuseStep 3120461 = 1170173) (by norm_num)
theorem B2080085 : Blo 1385512 2080085 := bbase (se 11 (by rfl) ⟨1523, by rfl⟩ : syracuseStep 2080085 = 3047) (by norm_num)
theorem B11246933 : Blo 1385512 11246933 := bbase (se 11 (by rfl) ⟨8237, by rfl⟩ : syracuseStep 11246933 = 16475) (by norm_num)
theorem B2080109 : Blo 1385512 2080109 := bbase (se 3 (by rfl) ⟨390020, by rfl⟩ : syracuseStep 2080109 = 780041) (by norm_num)
theorem B7896437 : Blo 1385512 7896437 := bbase (se 5 (by rfl) ⟨370145, by rfl⟩ : syracuseStep 7896437 = 740291) (by norm_num)
theorem B2080133 : Blo 1385512 2080133 := bbase (se 4 (by rfl) ⟨195012, by rfl⟩ : syracuseStep 2080133 = 390025) (by norm_num)
theorem B3120533 : Blo 1385512 3120533 := bbase (se 6 (by rfl) ⟨73137, by rfl⟩ : syracuseStep 3120533 = 146275) (by norm_num)
theorem B2080157 : Blo 1385512 2080157 := bbase (se 3 (by rfl) ⟨390029, by rfl⟩ : syracuseStep 2080157 = 780059) (by norm_num)
theorem B2080181 : Blo 1385512 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B2080205 : Blo 1385512 2080205 := bbase (se 3 (by rfl) ⟨390038, by rfl⟩ : syracuseStep 2080205 = 780077) (by norm_num)
theorem B3120605 : Blo 1385512 3120605 := bbase (se 3 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 3120605 = 1170227) (by norm_num)
theorem B2080229 : Blo 1385512 2080229 := bbase (se 4 (by rfl) ⟨195021, by rfl⟩ : syracuseStep 2080229 = 390043) (by norm_num)
theorem B2219509 : Blo 1385512 2219509 := bbase (se 5 (by rfl) ⟨104039, by rfl⟩ : syracuseStep 2219509 = 208079) (by norm_num)
theorem B10673653 : Blo 1385512 10673653 := bbase (se 5 (by rfl) ⟨500327, by rfl⟩ : syracuseStep 10673653 = 1000655) (by norm_num)
theorem B2080253 : Blo 1385512 2080253 := bbase (se 3 (by rfl) ⟨390047, by rfl⟩ : syracuseStep 2080253 = 780095) (by norm_num)
theorem B2080277 : Blo 1385512 2080277 := bbase (se 6 (by rfl) ⟨48756, by rfl⟩ : syracuseStep 2080277 = 97513) (by norm_num)
theorem B6659621 : Blo 1385512 6659621 := bbase (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) (by norm_num)
theorem B3120677 : Blo 1385512 3120677 := bbase (se 4 (by rfl) ⟨292563, by rfl⟩ : syracuseStep 3120677 = 585127) (by norm_num)
theorem B2080301 : Blo 1385512 2080301 := bbase (se 3 (by rfl) ⟨390056, by rfl⟩ : syracuseStep 2080301 = 780113) (by norm_num)
theorem B1973813 : Blo 1385512 1973813 := bbase (se 5 (by rfl) ⟨92522, by rfl⟩ : syracuseStep 1973813 = 185045) (by norm_num)
theorem B2080325 : Blo 1385512 2080325 := bbase (se 4 (by rfl) ⟨195030, by rfl⟩ : syracuseStep 2080325 = 390061) (by norm_num)
theorem B2080349 : Blo 1385512 2080349 := bbase (se 3 (by rfl) ⟨390065, by rfl⟩ : syracuseStep 2080349 = 780131) (by norm_num)
theorem B3120749 : Blo 1385512 3120749 := bbase (se 3 (by rfl) ⟨585140, by rfl⟩ : syracuseStep 3120749 = 1170281) (by norm_num)
theorem B2080373 : Blo 1385512 2080373 := bbase (se 5 (by rfl) ⟨97517, by rfl⟩ : syracuseStep 2080373 = 195035) (by norm_num)
theorem B2080397 : Blo 1385512 2080397 := bbase (se 3 (by rfl) ⟨390074, by rfl⟩ : syracuseStep 2080397 = 780149) (by norm_num)
theorem B2080421 : Blo 1385512 2080421 := bbase (se 4 (by rfl) ⟨195039, by rfl⟩ : syracuseStep 2080421 = 390079) (by norm_num)
theorem B3120821 : Blo 1385512 3120821 := bbase (se 5 (by rfl) ⟨146288, by rfl⟩ : syracuseStep 3120821 = 292577) (by norm_num)
theorem B2080445 : Blo 1385512 2080445 := bbase (se 3 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 2080445 = 780167) (by norm_num)
theorem B4677317 : Blo 1385512 4677317 := bbase (se 4 (by rfl) ⟨438498, by rfl⟩ : syracuseStep 4677317 = 876997) (by norm_num)
theorem B5922517 : Blo 1385512 5922517 := bbase (se 7 (by rfl) ⟨69404, by rfl⟩ : syracuseStep 5922517 = 138809) (by norm_num)
theorem B2080469 : Blo 1385512 2080469 := bbase (se 7 (by rfl) ⟨24380, by rfl⟩ : syracuseStep 2080469 = 48761) (by norm_num)
theorem B5922533 : Blo 1385512 5922533 := bbase (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) (by norm_num)
theorem B2080493 : Blo 1385512 2080493 := bbase (se 3 (by rfl) ⟨390092, by rfl⟩ : syracuseStep 2080493 = 780185) (by norm_num)
theorem B3120893 : Blo 1385512 3120893 := bbase (se 3 (by rfl) ⟨585167, by rfl⟩ : syracuseStep 3120893 = 1170335) (by norm_num)
theorem B2080517 : Blo 1385512 2080517 := bbase (se 4 (by rfl) ⟨195048, by rfl⟩ : syracuseStep 2080517 = 390097) (by norm_num)
theorem B2080541 : Blo 1385512 2080541 := bbase (se 3 (by rfl) ⟨390101, by rfl⟩ : syracuseStep 2080541 = 780203) (by norm_num)
theorem B2080565 : Blo 1385512 2080565 := bbase (se 5 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 2080565 = 195053) (by norm_num)
theorem B3120965 : Blo 1385512 3120965 := bbase (se 4 (by rfl) ⟨292590, by rfl⟩ : syracuseStep 3120965 = 585181) (by norm_num)
theorem B2080589 : Blo 1385512 2080589 := bbase (se 3 (by rfl) ⟨390110, by rfl⟩ : syracuseStep 2080589 = 780221) (by norm_num)
theorem B2080613 : Blo 1385512 2080613 := bbase (se 4 (by rfl) ⟨195057, by rfl⟩ : syracuseStep 2080613 = 390115) (by norm_num)
theorem B2080637 : Blo 1385512 2080637 := bbase (se 3 (by rfl) ⟨390119, by rfl⟩ : syracuseStep 2080637 = 780239) (by norm_num)
theorem B2809741 : Blo 1385512 2809741 := bbase (se 3 (by rfl) ⟨526826, by rfl⟩ : syracuseStep 2809741 = 1053653) (by norm_num)
theorem B3121037 : Blo 1385512 3121037 := bbase (se 3 (by rfl) ⟨585194, by rfl⟩ : syracuseStep 3121037 = 1170389) (by norm_num)
theorem B2080661 : Blo 1385512 2080661 := bbase (se 6 (by rfl) ⟨48765, by rfl⟩ : syracuseStep 2080661 = 97531) (by norm_num)
theorem B2080685 : Blo 1385512 2080685 := bbase (se 3 (by rfl) ⟨390128, by rfl⟩ : syracuseStep 2080685 = 780257) (by norm_num)
theorem B4440005 : Blo 1385512 4440005 := bbase (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) (by norm_num)
theorem B2080709 : Blo 1385512 2080709 := bbase (se 4 (by rfl) ⟨195066, by rfl⟩ : syracuseStep 2080709 = 390133) (by norm_num)
theorem B3121109 : Blo 1385512 3121109 := bbase (se 7 (by rfl) ⟨36575, by rfl⟩ : syracuseStep 3121109 = 73151) (by norm_num)
theorem B2080733 : Blo 1385512 2080733 := bbase (se 3 (by rfl) ⟨390137, by rfl⟩ : syracuseStep 2080733 = 780275) (by norm_num)
theorem B2080757 : Blo 1385512 2080757 := bbase (se 5 (by rfl) ⟨97535, by rfl⟩ : syracuseStep 2080757 = 195071) (by norm_num)
theorem B2080769 : Blo 1385512 2080769 := bstep (se 2 (by rfl) ⟨780288, by rfl⟩ : syracuseStep 2080769 = 1560577) B1560577
theorem B2080787 : Blo 1385512 2080787 := bstep (se 1 (by rfl) ⟨1560590, by rfl⟩ : syracuseStep 2080787 = 3121181) B3121181
theorem B7020593 : Blo 1385512 7020593 := bstep (se 2 (by rfl) ⟨2632722, by rfl⟩ : syracuseStep 7020593 = 5265445) B5265445
theorem B2080817 : Blo 1385512 2080817 := bstep (se 2 (by rfl) ⟨780306, by rfl⟩ : syracuseStep 2080817 = 1560613) B1560613
theorem B2498627 : Blo 1385512 2498627 := bstep (se 1 (by rfl) ⟨1873970, by rfl⟩ : syracuseStep 2498627 = 3747941) B3747941
theorem B2080835 : Blo 1385512 2080835 := bstep (se 1 (by rfl) ⟨1560626, by rfl⟩ : syracuseStep 2080835 = 3121253) B3121253
theorem B2080865 : Blo 1385512 2080865 := bstep (se 2 (by rfl) ⟨780324, by rfl⟩ : syracuseStep 2080865 = 1560649) B1560649
theorem B2080883 : Blo 1385512 2080883 := bstep (se 1 (by rfl) ⟨1560662, by rfl⟩ : syracuseStep 2080883 = 3121325) B3121325
theorem B2080913 : Blo 1385512 2080913 := bstep (se 2 (by rfl) ⟨780342, by rfl⟩ : syracuseStep 2080913 = 1560685) B1560685
theorem B2080931 : Blo 1385512 2080931 := bstep (se 1 (by rfl) ⟨1560698, by rfl⟩ : syracuseStep 2080931 = 3121397) B3121397
theorem B1974451 : Blo 1385512 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B2080961 : Blo 1385512 2080961 := bstep (se 2 (by rfl) ⟨780360, by rfl⟩ : syracuseStep 2080961 = 1560721) B1560721
theorem B2220227 : Blo 1385512 2220227 := bstep (se 1 (by rfl) ⟨1665170, by rfl⟩ : syracuseStep 2220227 = 3330341) B3330341
theorem B3121361 : Blo 1385512 3121361 := bstep (se 2 (by rfl) ⟨1170510, by rfl⟩ : syracuseStep 3121361 = 2341021) B2341021
theorem B2080979 : Blo 1385512 2080979 := bstep (se 1 (by rfl) ⟨1560734, by rfl⟩ : syracuseStep 2080979 = 3121469) B3121469
theorem B3121379 : Blo 1385512 3121379 := bstep (se 1 (by rfl) ⟨2341034, by rfl⟩ : syracuseStep 3121379 = 4682069) B4682069
theorem B2081009 : Blo 1385512 2081009 := bstep (se 2 (by rfl) ⟨780378, by rfl⟩ : syracuseStep 2081009 = 1560757) B1560757
theorem B2081027 : Blo 1385512 2081027 := bstep (se 1 (by rfl) ⟨1560770, by rfl⟩ : syracuseStep 2081027 = 3121541) B3121541
theorem B2081057 : Blo 1385512 2081057 := bstep (se 2 (by rfl) ⟨780396, by rfl⟩ : syracuseStep 2081057 = 1560793) B1560793
theorem B2081075 : Blo 1385512 2081075 := bstep (se 1 (by rfl) ⟨1560806, by rfl⟩ : syracuseStep 2081075 = 3121613) B3121613
theorem B4677965 : Blo 1385512 4677965 := bstep (se 3 (by rfl) ⟨877118, by rfl⟩ : syracuseStep 4677965 = 1754237) B1754237
theorem B2081105 : Blo 1385512 2081105 := bstep (se 2 (by rfl) ⟨780414, by rfl⟩ : syracuseStep 2081105 = 1560829) B1560829
theorem B2081123 : Blo 1385512 2081123 := bstep (se 1 (by rfl) ⟨1560842, by rfl⟩ : syracuseStep 2081123 = 3121685) B3121685
theorem B2081153 : Blo 1385512 2081153 := bstep (se 2 (by rfl) ⟨780432, by rfl⟩ : syracuseStep 2081153 = 1560865) B1560865
theorem B4678019 : Blo 1385512 4678019 := bstep (se 1 (by rfl) ⟨3508514, by rfl⟩ : syracuseStep 4678019 = 7017029) B7017029
theorem B2081171 : Blo 1385512 2081171 := bstep (se 1 (by rfl) ⟨1560878, by rfl⟩ : syracuseStep 2081171 = 3121757) B3121757
theorem B5267875 : Blo 1385512 5267875 := bstep (se 1 (by rfl) ⟨3950906, by rfl⟩ : syracuseStep 5267875 = 7901813) B7901813
theorem B2081201 : Blo 1385512 2081201 := bstep (se 2 (by rfl) ⟨780450, by rfl⟩ : syracuseStep 2081201 = 1560901) B1560901
theorem B2081219 : Blo 1385512 2081219 := bstep (se 1 (by rfl) ⟨1560914, by rfl⟩ : syracuseStep 2081219 = 3121829) B3121829
theorem B2081249 : Blo 1385512 2081249 := bstep (se 2 (by rfl) ⟨780468, by rfl⟩ : syracuseStep 2081249 = 1560937) B1560937
theorem B3121649 : Blo 1385512 3121649 := bstep (se 2 (by rfl) ⟨1170618, by rfl⟩ : syracuseStep 3121649 = 2341237) B2341237
theorem B2081267 : Blo 1385512 2081267 := bstep (se 1 (by rfl) ⟨1560950, by rfl⟩ : syracuseStep 2081267 = 3121901) B3121901
theorem B3121667 : Blo 1385512 3121667 := bstep (se 1 (by rfl) ⟨2341250, by rfl⟩ : syracuseStep 3121667 = 4682501) B4682501
theorem B10527245 : Blo 1385512 10527245 := bstep (se 3 (by rfl) ⟨1973858, by rfl⟩ : syracuseStep 10527245 = 3947717) B3947717
theorem B4678289 : Blo 1385512 4678289 := bstep (se 2 (by rfl) ⟨1754358, by rfl⟩ : syracuseStep 4678289 = 3508717) B3508717
theorem B6324941 : Blo 1385512 6324941 := bstep (se 3 (by rfl) ⟨1185926, by rfl⟩ : syracuseStep 6324941 = 2371853) B2371853
theorem B17777393 : Blo 1385512 17777393 := bstep (se 2 (by rfl) ⟨6666522, by rfl⟩ : syracuseStep 17777393 = 13333045) B13333045
theorem B2810819 : Blo 1385512 2810819 := bstep (se 1 (by rfl) ⟨2108114, by rfl⟩ : syracuseStep 2810819 = 4216229) B4216229
theorem B4744145 : Blo 1385512 4744145 := bstep (se 2 (by rfl) ⟨1779054, by rfl⟩ : syracuseStep 4744145 = 3558109) B3558109
theorem B2630627 : Blo 1385512 2630627 := bstep (se 1 (by rfl) ⟨1972970, by rfl⟩ : syracuseStep 2630627 = 3945941) B3945941
theorem B2499601 : Blo 1385512 2499601 := bstep (se 2 (by rfl) ⟨937350, by rfl⟩ : syracuseStep 2499601 = 1874701) B1874701
theorem B1754131 : Blo 1385512 1754131 := bstep (se 1 (by rfl) ⟨1315598, by rfl⟩ : syracuseStep 1754131 = 2631197) B2631197
theorem B7898147 : Blo 1385512 7898147 := bstep (se 1 (by rfl) ⟨5923610, by rfl⟩ : syracuseStep 7898147 = 11847221) B11847221
theorem B1385523 : Blo 1385512 1385523 := bstep (se 1 (by rfl) ⟨1039142, by rfl⟩ : syracuseStep 1385523 = 2078285) B2078285
theorem B1385539 : Blo 1385512 1385539 := bstep (se 1 (by rfl) ⟨1039154, by rfl⟩ : syracuseStep 1385539 = 2078309) B2078309
theorem B1385555 : Blo 1385512 1385555 := bstep (se 1 (by rfl) ⟨1039166, by rfl⟩ : syracuseStep 1385555 = 2078333) B2078333
theorem B1385571 : Blo 1385512 1385571 := bstep (se 1 (by rfl) ⟨1039178, by rfl⟩ : syracuseStep 1385571 = 2078357) B2078357
theorem B1385587 : Blo 1385512 1385587 := bstep (se 1 (by rfl) ⟨1039190, by rfl⟩ : syracuseStep 1385587 = 2078381) B2078381
theorem B1754227 : Blo 1385512 1754227 := bstep (se 1 (by rfl) ⟨1315670, by rfl⟩ : syracuseStep 1754227 = 2631341) B2631341
theorem B1385603 : Blo 1385512 1385603 := bstep (se 1 (by rfl) ⟨1039202, by rfl⟩ : syracuseStep 1385603 = 2078405) B2078405
theorem B1385619 : Blo 1385512 1385619 := bstep (se 1 (by rfl) ⟨1039214, by rfl⟩ : syracuseStep 1385619 = 2078429) B2078429
theorem B1385635 : Blo 1385512 1385635 := bstep (se 1 (by rfl) ⟨1039226, by rfl⟩ : syracuseStep 1385635 = 2078453) B2078453
theorem B4678829 : Blo 1385512 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1385651 : Blo 1385512 1385651 := bstep (se 1 (by rfl) ⟨1039238, by rfl⟩ : syracuseStep 1385651 = 2078477) B2078477
theorem B1385667 : Blo 1385512 1385667 := bstep (se 1 (by rfl) ⟨1039250, by rfl⟩ : syracuseStep 1385667 = 2078501) B2078501
theorem B1385683 : Blo 1385512 1385683 := bstep (se 1 (by rfl) ⟨1039262, by rfl⟩ : syracuseStep 1385683 = 2078525) B2078525
theorem B1385699 : Blo 1385512 1385699 := bstep (se 1 (by rfl) ⟨1039274, by rfl⟩ : syracuseStep 1385699 = 2078549) B2078549
theorem B4678883 : Blo 1385512 4678883 := bstep (se 1 (by rfl) ⟨3509162, by rfl⟩ : syracuseStep 4678883 = 7018325) B7018325
theorem B1385715 : Blo 1385512 1385715 := bstep (se 1 (by rfl) ⟨1039286, by rfl⟩ : syracuseStep 1385715 = 2078573) B2078573
theorem B1385731 : Blo 1385512 1385731 := bstep (se 1 (by rfl) ⟨1039298, by rfl⟩ : syracuseStep 1385731 = 2078597) B2078597
theorem B1385747 : Blo 1385512 1385747 := bstep (se 1 (by rfl) ⟨1039310, by rfl⟩ : syracuseStep 1385747 = 2078621) B2078621
theorem B1385763 : Blo 1385512 1385763 := bstep (se 1 (by rfl) ⟨1039322, by rfl⟩ : syracuseStep 1385763 = 2078645) B2078645
theorem B3949859 : Blo 1385512 3949859 := bstep (se 1 (by rfl) ⟨2962394, by rfl⟩ : syracuseStep 3949859 = 5924789) B5924789
theorem B1926433 : Blo 1385512 1926433 := bstep (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) B1444825
theorem B1385779 : Blo 1385512 1385779 := bstep (se 1 (by rfl) ⟨1039334, by rfl⟩ : syracuseStep 1385779 = 2078669) B2078669
theorem B1385795 : Blo 1385512 1385795 := bstep (se 1 (by rfl) ⟨1039346, by rfl⟩ : syracuseStep 1385795 = 2078693) B2078693
theorem B5621069 : Blo 1385512 5621069 := bstep (se 3 (by rfl) ⟨1053950, by rfl⟩ : syracuseStep 5621069 = 2107901) B2107901
theorem B5924173 : Blo 1385512 5924173 := bstep (se 3 (by rfl) ⟨1110782, by rfl⟩ : syracuseStep 5924173 = 2221565) B2221565
theorem B1385811 : Blo 1385512 1385811 := bstep (se 1 (by rfl) ⟨1039358, by rfl⟩ : syracuseStep 1385811 = 2078717) B2078717
theorem B1385827 : Blo 1385512 1385827 := bstep (se 1 (by rfl) ⟨1039370, by rfl⟩ : syracuseStep 1385827 = 2078741) B2078741
theorem B1385843 : Blo 1385512 1385843 := bstep (se 1 (by rfl) ⟨1039382, by rfl⟩ : syracuseStep 1385843 = 2078765) B2078765
theorem B1385859 : Blo 1385512 1385859 := bstep (se 1 (by rfl) ⟨1039394, by rfl⟩ : syracuseStep 1385859 = 2078789) B2078789
theorem B1385875 : Blo 1385512 1385875 := bstep (se 1 (by rfl) ⟨1039406, by rfl⟩ : syracuseStep 1385875 = 2078813) B2078813
theorem B1385891 : Blo 1385512 1385891 := bstep (se 1 (by rfl) ⟨1039418, by rfl⟩ : syracuseStep 1385891 = 2078837) B2078837
theorem B4441517 : Blo 1385512 4441517 := bstep (se 3 (by rfl) ⟨832784, by rfl⟩ : syracuseStep 4441517 = 1665569) B1665569
theorem B1385907 : Blo 1385512 1385907 := bstep (se 1 (by rfl) ⟨1039430, by rfl⟩ : syracuseStep 1385907 = 2078861) B2078861
theorem B1385923 : Blo 1385512 1385923 := bstep (se 1 (by rfl) ⟨1039442, by rfl⟩ : syracuseStep 1385923 = 2078885) B2078885
theorem B1385939 : Blo 1385512 1385939 := bstep (se 1 (by rfl) ⟨1039454, by rfl⟩ : syracuseStep 1385939 = 2078909) B2078909
theorem B1385955 : Blo 1385512 1385955 := bstep (se 1 (by rfl) ⟨1039466, by rfl⟩ : syracuseStep 1385955 = 2078933) B2078933
theorem B7022051 : Blo 1385512 7022051 := bstep (se 1 (by rfl) ⟨5266538, by rfl⟩ : syracuseStep 7022051 = 10533077) B10533077
theorem B8881649 : Blo 1385512 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B4679153 : Blo 1385512 4679153 := bstep (se 2 (by rfl) ⟨1754682, by rfl⟩ : syracuseStep 4679153 = 3509365) B3509365
theorem B1385971 : Blo 1385512 1385971 := bstep (se 1 (by rfl) ⟨1039478, by rfl⟩ : syracuseStep 1385971 = 2078957) B2078957
theorem B1385987 : Blo 1385512 1385987 := bstep (se 1 (by rfl) ⟨1039490, by rfl⟩ : syracuseStep 1385987 = 2078981) B2078981
theorem B3556867 : Blo 1385512 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B1386003 : Blo 1385512 1386003 := bstep (se 1 (by rfl) ⟨1039502, by rfl⟩ : syracuseStep 1386003 = 2079005) B2079005
theorem B1386019 : Blo 1385512 1386019 := bstep (se 1 (by rfl) ⟨1039514, by rfl⟩ : syracuseStep 1386019 = 2079029) B2079029
theorem B1386035 : Blo 1385512 1386035 := bstep (se 1 (by rfl) ⟨1039526, by rfl⟩ : syracuseStep 1386035 = 2079053) B2079053
theorem B33326645 : Blo 1385512 33326645 := bstep (se 5 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 33326645 = 3124373) B3124373
theorem B2106947 : Blo 1385512 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B1386051 : Blo 1385512 1386051 := bstep (se 1 (by rfl) ⟨1039538, by rfl⟩ : syracuseStep 1386051 = 2079077) B2079077
theorem B1386067 : Blo 1385512 1386067 := bstep (se 1 (by rfl) ⟨1039550, by rfl⟩ : syracuseStep 1386067 = 2079101) B2079101
theorem B1386083 : Blo 1385512 1386083 := bstep (se 1 (by rfl) ⟨1039562, by rfl⟩ : syracuseStep 1386083 = 2079125) B2079125
theorem B1754723 : Blo 1385512 1754723 := bstep (se 1 (by rfl) ⟨1316042, by rfl⟩ : syracuseStep 1754723 = 2632085) B2632085
theorem B2221681 : Blo 1385512 2221681 := bstep (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) B1666261
theorem B1386099 : Blo 1385512 1386099 := bstep (se 1 (by rfl) ⟨1039574, by rfl⟩ : syracuseStep 1386099 = 2079149) B2079149
theorem B1386115 : Blo 1385512 1386115 := bstep (se 1 (by rfl) ⟨1039586, by rfl⟩ : syracuseStep 1386115 = 2079173) B2079173
theorem B3507857 : Blo 1385512 3507857 := bstep (se 2 (by rfl) ⟨1315446, by rfl⟩ : syracuseStep 3507857 = 2630893) B2630893
theorem B1386131 : Blo 1385512 1386131 := bstep (se 1 (by rfl) ⟨1039598, by rfl⟩ : syracuseStep 1386131 = 2079197) B2079197
theorem B2500241 : Blo 1385512 2500241 := bstep (se 2 (by rfl) ⟨937590, by rfl⟩ : syracuseStep 2500241 = 1875181) B1875181
theorem B1386147 : Blo 1385512 1386147 := bstep (se 1 (by rfl) ⟨1039610, by rfl⟩ : syracuseStep 1386147 = 2079221) B2079221
theorem B5924515 : Blo 1385512 5924515 := bstep (se 1 (by rfl) ⟨4443386, by rfl⟩ : syracuseStep 5924515 = 8886773) B8886773
theorem B1386163 : Blo 1385512 1386163 := bstep (se 1 (by rfl) ⟨1039622, by rfl⟩ : syracuseStep 1386163 = 2079245) B2079245
theorem B3507907 : Blo 1385512 3507907 := bstep (se 1 (by rfl) ⟨2630930, by rfl⟩ : syracuseStep 3507907 = 5261861) B5261861
theorem B1386179 : Blo 1385512 1386179 := bstep (se 1 (by rfl) ⟨1039634, by rfl⟩ : syracuseStep 1386179 = 2079269) B2079269
theorem B1664723 : Blo 1385512 1664723 := bstep (se 1 (by rfl) ⟨1248542, by rfl⟩ : syracuseStep 1664723 = 2497085) B2497085
theorem B1386195 : Blo 1385512 1386195 := bstep (se 1 (by rfl) ⟨1039646, by rfl⟩ : syracuseStep 1386195 = 2079293) B2079293
theorem B1386211 : Blo 1385512 1386211 := bstep (se 1 (by rfl) ⟨1039658, by rfl⟩ : syracuseStep 1386211 = 2079317) B2079317
theorem B1386227 : Blo 1385512 1386227 := bstep (se 1 (by rfl) ⟨1039670, by rfl⟩ : syracuseStep 1386227 = 2079341) B2079341
theorem B1386243 : Blo 1385512 1386243 := bstep (se 1 (by rfl) ⟨1039682, by rfl⟩ : syracuseStep 1386243 = 2079365) B2079365
theorem B1386259 : Blo 1385512 1386259 := bstep (se 1 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 1386259 = 2079389) B2079389
theorem B1386275 : Blo 1385512 1386275 := bstep (se 1 (by rfl) ⟨1039706, by rfl⟩ : syracuseStep 1386275 = 2079413) B2079413
theorem B1386291 : Blo 1385512 1386291 := bstep (se 1 (by rfl) ⟨1039718, by rfl⟩ : syracuseStep 1386291 = 2079437) B2079437
theorem B1386307 : Blo 1385512 1386307 := bstep (se 1 (by rfl) ⟨1039730, by rfl⟩ : syracuseStep 1386307 = 2079461) B2079461
theorem B3508049 : Blo 1385512 3508049 := bstep (se 2 (by rfl) ⟨1315518, by rfl⟩ : syracuseStep 3508049 = 2631037) B2631037
theorem B1386323 : Blo 1385512 1386323 := bstep (se 1 (by rfl) ⟨1039742, by rfl⟩ : syracuseStep 1386323 = 2079485) B2079485
theorem B2631523 : Blo 1385512 2631523 := bstep (se 1 (by rfl) ⟨1973642, by rfl⟩ : syracuseStep 2631523 = 3947285) B3947285
theorem B1386339 : Blo 1385512 1386339 := bstep (se 1 (by rfl) ⟨1039754, by rfl⟩ : syracuseStep 1386339 = 2079509) B2079509
theorem B1386355 : Blo 1385512 1386355 := bstep (se 1 (by rfl) ⟨1039766, by rfl⟩ : syracuseStep 1386355 = 2079533) B2079533
theorem B1386371 : Blo 1385512 1386371 := bstep (se 1 (by rfl) ⟨1039778, by rfl⟩ : syracuseStep 1386371 = 2079557) B2079557
theorem B1386387 : Blo 1385512 1386387 := bstep (se 1 (by rfl) ⟨1039790, by rfl⟩ : syracuseStep 1386387 = 2079581) B2079581
theorem B1386403 : Blo 1385512 1386403 := bstep (se 1 (by rfl) ⟨1039802, by rfl⟩ : syracuseStep 1386403 = 2079605) B2079605
theorem B1386419 : Blo 1385512 1386419 := bstep (se 1 (by rfl) ⟨1039814, by rfl⟩ : syracuseStep 1386419 = 2079629) B2079629
theorem B1386435 : Blo 1385512 1386435 := bstep (se 1 (by rfl) ⟨1039826, by rfl⟩ : syracuseStep 1386435 = 2079653) B2079653
theorem B1386451 : Blo 1385512 1386451 := bstep (se 1 (by rfl) ⟨1039838, by rfl⟩ : syracuseStep 1386451 = 2079677) B2079677
theorem B1386467 : Blo 1385512 1386467 := bstep (se 1 (by rfl) ⟨1039850, by rfl⟩ : syracuseStep 1386467 = 2079701) B2079701
theorem B2959345 : Blo 1385512 2959345 := bstep (se 2 (by rfl) ⟨1109754, by rfl⟩ : syracuseStep 2959345 = 2219509) B2219509
theorem B14231537 : Blo 1385512 14231537 := bstep (se 2 (by rfl) ⟨5336826, by rfl⟩ : syracuseStep 14231537 = 10673653) B10673653
theorem B1386483 : Blo 1385512 1386483 := bstep (se 1 (by rfl) ⟨1039862, by rfl⟩ : syracuseStep 1386483 = 2079725) B2079725
theorem B2631683 : Blo 1385512 2631683 := bstep (se 1 (by rfl) ⟨1973762, by rfl⟩ : syracuseStep 2631683 = 3947525) B3947525
theorem B1386499 : Blo 1385512 1386499 := bstep (se 1 (by rfl) ⟨1039874, by rfl⟩ : syracuseStep 1386499 = 2079749) B2079749
theorem B4679693 : Blo 1385512 4679693 := bstep (se 3 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 4679693 = 1754885) B1754885
theorem B1386515 : Blo 1385512 1386515 := bstep (se 1 (by rfl) ⟨1039886, by rfl⟩ : syracuseStep 1386515 = 2079773) B2079773
theorem B1386531 : Blo 1385512 1386531 := bstep (se 1 (by rfl) ⟨1039898, by rfl⟩ : syracuseStep 1386531 = 2079797) B2079797
theorem B1386547 : Blo 1385512 1386547 := bstep (se 1 (by rfl) ⟨1039910, by rfl⟩ : syracuseStep 1386547 = 2079821) B2079821
theorem B1386563 : Blo 1385512 1386563 := bstep (se 1 (by rfl) ⟨1039922, by rfl⟩ : syracuseStep 1386563 = 2079845) B2079845
theorem B4679747 : Blo 1385512 4679747 := bstep (se 1 (by rfl) ⟨3509810, by rfl⟩ : syracuseStep 4679747 = 7019621) B7019621
theorem B10127429 : Blo 1385512 10127429 := bstep (se 4 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 10127429 = 1898893) B1898893
theorem B1386579 : Blo 1385512 1386579 := bstep (se 1 (by rfl) ⟨1039934, by rfl⟩ : syracuseStep 1386579 = 2079869) B2079869
theorem B1386595 : Blo 1385512 1386595 := bstep (se 1 (by rfl) ⟨1039946, by rfl⟩ : syracuseStep 1386595 = 2079893) B2079893
theorem B1386611 : Blo 1385512 1386611 := bstep (se 1 (by rfl) ⟨1039958, by rfl⟩ : syracuseStep 1386611 = 2079917) B2079917
theorem B1386627 : Blo 1385512 1386627 := bstep (se 1 (by rfl) ⟨1039970, by rfl⟩ : syracuseStep 1386627 = 2079941) B2079941
theorem B1386643 : Blo 1385512 1386643 := bstep (se 1 (by rfl) ⟨1039982, by rfl⟩ : syracuseStep 1386643 = 2079965) B2079965
theorem B1386659 : Blo 1385512 1386659 := bstep (se 1 (by rfl) ⟨1039994, by rfl⟩ : syracuseStep 1386659 = 2079989) B2079989
theorem B3999917 : Blo 1385512 3999917 := bstep (se 3 (by rfl) ⟨749984, by rfl⟩ : syracuseStep 3999917 = 1499969) B1499969
theorem B1386675 : Blo 1385512 1386675 := bstep (se 1 (by rfl) ⟨1040006, by rfl⟩ : syracuseStep 1386675 = 2080013) B2080013
theorem B1558723 : Blo 1385512 1558723 := bstep (se 1 (by rfl) ⟨1169042, by rfl⟩ : syracuseStep 1558723 = 2338085) B2338085
theorem B1386691 : Blo 1385512 1386691 := bstep (se 1 (by rfl) ⟨1040018, by rfl⟩ : syracuseStep 1386691 = 2080037) B2080037
theorem B1386707 : Blo 1385512 1386707 := bstep (se 1 (by rfl) ⟨1040030, by rfl⟩ : syracuseStep 1386707 = 2080061) B2080061
theorem B1386723 : Blo 1385512 1386723 := bstep (se 1 (by rfl) ⟨1040042, by rfl⟩ : syracuseStep 1386723 = 2080085) B2080085
theorem B7497955 : Blo 1385512 7497955 := bstep (se 1 (by rfl) ⟨5623466, by rfl⟩ : syracuseStep 7497955 = 11246933) B11246933
theorem B1386739 : Blo 1385512 1386739 := bstep (se 1 (by rfl) ⟨1040054, by rfl⟩ : syracuseStep 1386739 = 2080109) B2080109
theorem B1386755 : Blo 1385512 1386755 := bstep (se 1 (by rfl) ⟨1040066, by rfl⟩ : syracuseStep 1386755 = 2080133) B2080133
theorem B7022861 : Blo 1385512 7022861 := bstep (se 3 (by rfl) ⟨1316786, by rfl⟩ : syracuseStep 7022861 = 2633573) B2633573
theorem B1386771 : Blo 1385512 1386771 := bstep (se 1 (by rfl) ⟨1040078, by rfl⟩ : syracuseStep 1386771 = 2080157) B2080157
theorem B1386787 : Blo 1385512 1386787 := bstep (se 1 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 1386787 = 2080181) B2080181
theorem B1755427 : Blo 1385512 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B1386803 : Blo 1385512 1386803 := bstep (se 1 (by rfl) ⟨1040102, by rfl⟩ : syracuseStep 1386803 = 2080205) B2080205
theorem B1386819 : Blo 1385512 1386819 := bstep (se 1 (by rfl) ⟨1040114, by rfl⟩ : syracuseStep 1386819 = 2080229) B2080229
theorem B4680017 : Blo 1385512 4680017 := bstep (se 2 (by rfl) ⟨1755006, by rfl⟩ : syracuseStep 4680017 = 3510013) B3510013
theorem B1558867 : Blo 1385512 1558867 := bstep (se 1 (by rfl) ⟨1169150, by rfl⟩ : syracuseStep 1558867 = 2338301) B2338301
theorem B1386835 : Blo 1385512 1386835 := bstep (se 1 (by rfl) ⟨1040126, by rfl⟩ : syracuseStep 1386835 = 2080253) B2080253
theorem B1386851 : Blo 1385512 1386851 := bstep (se 1 (by rfl) ⟨1040138, by rfl⟩ : syracuseStep 1386851 = 2080277) B2080277
theorem B1386867 : Blo 1385512 1386867 := bstep (se 1 (by rfl) ⟨1040150, by rfl⟩ : syracuseStep 1386867 = 2080301) B2080301
theorem B1386883 : Blo 1385512 1386883 := bstep (se 1 (by rfl) ⟨1040162, by rfl⟩ : syracuseStep 1386883 = 2080325) B2080325
theorem B1755523 : Blo 1385512 1755523 := bstep (se 1 (by rfl) ⟨1316642, by rfl⟩ : syracuseStep 1755523 = 2633285) B2633285
theorem B1386899 : Blo 1385512 1386899 := bstep (se 1 (by rfl) ⟨1040174, by rfl⟩ : syracuseStep 1386899 = 2080349) B2080349
theorem B1386915 : Blo 1385512 1386915 := bstep (se 1 (by rfl) ⟨1040186, by rfl⟩ : syracuseStep 1386915 = 2080373) B2080373
theorem B1386931 : Blo 1385512 1386931 := bstep (se 1 (by rfl) ⟨1040198, by rfl⟩ : syracuseStep 1386931 = 2080397) B2080397
theorem B1386947 : Blo 1385512 1386947 := bstep (se 1 (by rfl) ⟨1040210, by rfl⟩ : syracuseStep 1386947 = 2080421) B2080421
theorem B1386963 : Blo 1385512 1386963 := bstep (se 1 (by rfl) ⟨1040222, by rfl⟩ : syracuseStep 1386963 = 2080445) B2080445
theorem B1559011 : Blo 1385512 1559011 := bstep (se 1 (by rfl) ⟨1169258, by rfl⟩ : syracuseStep 1559011 = 2338517) B2338517
theorem B1386979 : Blo 1385512 1386979 := bstep (se 1 (by rfl) ⟨1040234, by rfl⟩ : syracuseStep 1386979 = 2080469) B2080469
theorem B3951089 : Blo 1385512 3951089 := bstep (se 2 (by rfl) ⟨1481658, by rfl⟩ : syracuseStep 3951089 = 2963317) B2963317
theorem B1386995 : Blo 1385512 1386995 := bstep (se 1 (by rfl) ⟨1040246, by rfl⟩ : syracuseStep 1386995 = 2080493) B2080493
theorem B1387011 : Blo 1385512 1387011 := bstep (se 1 (by rfl) ⟨1040258, by rfl⟩ : syracuseStep 1387011 = 2080517) B2080517
theorem B3746321 : Blo 1385512 3746321 := bstep (se 2 (by rfl) ⟨1404870, by rfl⟩ : syracuseStep 3746321 = 2809741) B2809741
theorem B1387027 : Blo 1385512 1387027 := bstep (se 1 (by rfl) ⟨1040270, by rfl⟩ : syracuseStep 1387027 = 2080541) B2080541
theorem B1387043 : Blo 1385512 1387043 := bstep (se 1 (by rfl) ⟨1040282, by rfl⟩ : syracuseStep 1387043 = 2080565) B2080565
theorem B1387059 : Blo 1385512 1387059 := bstep (se 1 (by rfl) ⟨1040294, by rfl⟩ : syracuseStep 1387059 = 2080589) B2080589
theorem B1387075 : Blo 1385512 1387075 := bstep (se 1 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 1387075 = 2080613) B2080613
theorem B1387091 : Blo 1385512 1387091 := bstep (se 1 (by rfl) ⟨1040318, by rfl⟩ : syracuseStep 1387091 = 2080637) B2080637
theorem B1387107 : Blo 1385512 1387107 := bstep (se 1 (by rfl) ⟨1040330, by rfl⟩ : syracuseStep 1387107 = 2080661) B2080661
theorem B1559155 : Blo 1385512 1559155 := bstep (se 1 (by rfl) ⟨1169366, by rfl⟩ : syracuseStep 1559155 = 2338733) B2338733
theorem B1387123 : Blo 1385512 1387123 := bstep (se 1 (by rfl) ⟨1040342, by rfl⟩ : syracuseStep 1387123 = 2080685) B2080685
theorem B2960003 : Blo 1385512 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B1387139 : Blo 1385512 1387139 := bstep (se 1 (by rfl) ⟨1040354, by rfl⟩ : syracuseStep 1387139 = 2080709) B2080709
theorem B1387155 : Blo 1385512 1387155 := bstep (se 1 (by rfl) ⟨1040366, by rfl⟩ : syracuseStep 1387155 = 2080733) B2080733
theorem B1387171 : Blo 1385512 1387171 := bstep (se 1 (by rfl) ⟨1040378, by rfl⟩ : syracuseStep 1387171 = 2080757) B2080757
theorem B2402993 : Blo 1385512 2402993 := bstep (se 2 (by rfl) ⟨901122, by rfl⟩ : syracuseStep 2402993 = 1802245) B1802245
theorem B1387187 : Blo 1385512 1387187 := bstep (se 1 (by rfl) ⟨1040390, by rfl⟩ : syracuseStep 1387187 = 2080781) B2080781
theorem B1387203 : Blo 1385512 1387203 := bstep (se 1 (by rfl) ⟨1040402, by rfl⟩ : syracuseStep 1387203 = 2080805) B2080805
theorem B11250373 : Blo 1385512 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B5262029 : Blo 1385512 5262029 := bstep (se 3 (by rfl) ⟨986630, by rfl⟩ : syracuseStep 5262029 = 1973261) B1973261
theorem B1387219 : Blo 1385512 1387219 := bstep (se 1 (by rfl) ⟨1040414, by rfl⟩ : syracuseStep 1387219 = 2080829) B2080829
theorem B22498019 : Blo 1385512 22498019 := bstep (se 1 (by rfl) ⟨16873514, by rfl⟩ : syracuseStep 22498019 = 33747029) B33747029
theorem B1387235 : Blo 1385512 1387235 := bstep (se 1 (by rfl) ⟨1040426, by rfl⟩ : syracuseStep 1387235 = 2080853) B2080853
theorem B4999907 : Blo 1385512 4999907 := bstep (se 1 (by rfl) ⟨3749930, by rfl⟩ : syracuseStep 4999907 = 7499861) B7499861
theorem B1387251 : Blo 1385512 1387251 := bstep (se 1 (by rfl) ⟨1040438, by rfl⟩ : syracuseStep 1387251 = 2080877) B2080877
theorem B1559299 : Blo 1385512 1559299 := bstep (se 1 (by rfl) ⟨1169474, by rfl⟩ : syracuseStep 1559299 = 2338949) B2338949
theorem B1387267 : Blo 1385512 1387267 := bstep (se 1 (by rfl) ⟨1040450, by rfl⟩ : syracuseStep 1387267 = 2080901) B2080901
theorem B1387283 : Blo 1385512 1387283 := bstep (se 1 (by rfl) ⟨1040462, by rfl⟩ : syracuseStep 1387283 = 2080925) B2080925
theorem B1387299 : Blo 1385512 1387299 := bstep (se 1 (by rfl) ⟨1040474, by rfl⟩ : syracuseStep 1387299 = 2080949) B2080949
theorem B3509041 : Blo 1385512 3509041 := bstep (se 2 (by rfl) ⟨1315890, by rfl⟩ : syracuseStep 3509041 = 2631781) B2631781
theorem B1387315 : Blo 1385512 1387315 := bstep (se 1 (by rfl) ⟨1040486, by rfl⟩ : syracuseStep 1387315 = 2080973) B2080973
theorem B1387331 : Blo 1385512 1387331 := bstep (se 1 (by rfl) ⟨1040498, by rfl⟩ : syracuseStep 1387331 = 2080997) B2080997
theorem B10521413 : Blo 1385512 10521413 := bstep (se 4 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 10521413 = 1972765) B1972765
theorem B7891789 : Blo 1385512 7891789 := bstep (se 3 (by rfl) ⟨1479710, by rfl⟩ : syracuseStep 7891789 = 2959421) B2959421
theorem B1387347 : Blo 1385512 1387347 := bstep (se 1 (by rfl) ⟨1040510, by rfl⟩ : syracuseStep 1387347 = 2081021) B2081021
theorem B1387363 : Blo 1385512 1387363 := bstep (se 1 (by rfl) ⟨1040522, by rfl⟩ : syracuseStep 1387363 = 2081045) B2081045
theorem B4680557 : Blo 1385512 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B1387379 : Blo 1385512 1387379 := bstep (se 1 (by rfl) ⟨1040534, by rfl⟩ : syracuseStep 1387379 = 2081069) B2081069
theorem B1756019 : Blo 1385512 1756019 := bstep (se 1 (by rfl) ⟨1317014, by rfl⟩ : syracuseStep 1756019 = 2634029) B2634029
theorem B4746115 : Blo 1385512 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B1387395 : Blo 1385512 1387395 := bstep (se 1 (by rfl) ⟨1040546, by rfl⟩ : syracuseStep 1387395 = 2081093) B2081093
theorem B7900037 : Blo 1385512 7900037 := bstep (se 4 (by rfl) ⟨740628, by rfl⟩ : syracuseStep 7900037 = 1481257) B1481257
theorem B1559443 : Blo 1385512 1559443 := bstep (se 1 (by rfl) ⟨1169582, by rfl⟩ : syracuseStep 1559443 = 2339165) B2339165
theorem B1387411 : Blo 1385512 1387411 := bstep (se 1 (by rfl) ⟨1040558, by rfl⟩ : syracuseStep 1387411 = 2081117) B2081117
theorem B4680611 : Blo 1385512 4680611 := bstep (se 1 (by rfl) ⟨3510458, by rfl⟩ : syracuseStep 4680611 = 7020917) B7020917
theorem B1387427 : Blo 1385512 1387427 := bstep (se 1 (by rfl) ⟨1040570, by rfl⟩ : syracuseStep 1387427 = 2081141) B2081141
theorem B1387443 : Blo 1385512 1387443 := bstep (se 1 (by rfl) ⟨1040582, by rfl⟩ : syracuseStep 1387443 = 2081165) B2081165
theorem B1387459 : Blo 1385512 1387459 := bstep (se 1 (by rfl) ⟨1040594, by rfl⟩ : syracuseStep 1387459 = 2081189) B2081189
theorem B1387475 : Blo 1385512 1387475 := bstep (se 1 (by rfl) ⟨1040606, by rfl⟩ : syracuseStep 1387475 = 2081213) B2081213
theorem B1387491 : Blo 1385512 1387491 := bstep (se 1 (by rfl) ⟨1040618, by rfl⟩ : syracuseStep 1387491 = 2081237) B2081237
theorem B7015409 : Blo 1385512 7015409 := bstep (se 2 (by rfl) ⟨2630778, by rfl⟩ : syracuseStep 7015409 = 5261557) B5261557
theorem B1387507 : Blo 1385512 1387507 := bstep (se 1 (by rfl) ⟨1040630, by rfl⟩ : syracuseStep 1387507 = 2081261) B2081261
theorem B1559587 : Blo 1385512 1559587 := bstep (se 1 (by rfl) ⟨1169690, by rfl⟩ : syracuseStep 1559587 = 2339381) B2339381
theorem B2632753 : Blo 1385512 2632753 := bstep (se 2 (by rfl) ⟨987282, by rfl⟩ : syracuseStep 2632753 = 1974565) B1974565
theorem B3509315 : Blo 1385512 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B9006157 : Blo 1385512 9006157 := bstep (se 3 (by rfl) ⟨1688654, by rfl⟩ : syracuseStep 9006157 = 3377309) B3377309
theorem B4680881 : Blo 1385512 4680881 := bstep (se 2 (by rfl) ⟨1755330, by rfl⟩ : syracuseStep 4680881 = 3510661) B3510661
theorem B1559731 : Blo 1385512 1559731 := bstep (se 1 (by rfl) ⟨1169798, by rfl⟩ : syracuseStep 1559731 = 2339597) B2339597
theorem B15797429 : Blo 1385512 15797429 := bstep (se 5 (by rfl) ⟨740504, by rfl⟩ : syracuseStep 15797429 = 1481009) B1481009
theorem B7498993 : Blo 1385512 7498993 := bstep (se 2 (by rfl) ⟨2812122, by rfl⟩ : syracuseStep 7498993 = 5624245) B5624245
theorem B3509507 : Blo 1385512 3509507 := bstep (se 1 (by rfl) ⟨2632130, by rfl⟩ : syracuseStep 3509507 = 5264261) B5264261
theorem B1559875 : Blo 1385512 1559875 := bstep (se 1 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 1559875 = 2339813) B2339813
theorem B10530161 : Blo 1385512 10530161 := bstep (se 2 (by rfl) ⟨3948810, by rfl⟩ : syracuseStep 10530161 = 7897621) B7897621
theorem B2338193 : Blo 1385512 2338193 := bstep (se 2 (by rfl) ⟨876822, by rfl⟩ : syracuseStep 2338193 = 1753645) B1753645
theorem B2108849 : Blo 1385512 2108849 := bstep (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) B1581637
theorem B7499213 : Blo 1385512 7499213 := bstep (se 3 (by rfl) ⟨1406102, by rfl⟩ : syracuseStep 7499213 = 2812205) B2812205
theorem B2960849 : Blo 1385512 2960849 := bstep (se 2 (by rfl) ⟨1110318, by rfl⟩ : syracuseStep 2960849 = 2220637) B2220637
theorem B2371027 : Blo 1385512 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B1560019 : Blo 1385512 1560019 := bstep (se 1 (by rfl) ⟨1170014, by rfl⟩ : syracuseStep 1560019 = 2340029) B2340029
theorem B2108897 : Blo 1385512 2108897 := bstep (se 2 (by rfl) ⟨790836, by rfl⟩ : syracuseStep 2108897 = 1581673) B1581673
theorem B5262833 : Blo 1385512 5262833 := bstep (se 2 (by rfl) ⟨1973562, by rfl⟩ : syracuseStep 5262833 = 3947125) B3947125
theorem B2338321 : Blo 1385512 2338321 := bstep (se 2 (by rfl) ⟨876870, by rfl⟩ : syracuseStep 2338321 = 1753741) B1753741
theorem B2338355 : Blo 1385512 2338355 := bstep (se 1 (by rfl) ⟨1753766, by rfl⟩ : syracuseStep 2338355 = 3507533) B3507533
theorem B1560163 : Blo 1385512 1560163 := bstep (se 1 (by rfl) ⟨1170122, by rfl⟩ : syracuseStep 1560163 = 2340245) B2340245
theorem B2338483 : Blo 1385512 2338483 := bstep (se 1 (by rfl) ⟨1753862, by rfl⟩ : syracuseStep 2338483 = 3507725) B3507725
theorem B9875141 : Blo 1385512 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B4681421 : Blo 1385512 4681421 := bstep (se 3 (by rfl) ⟨877766, by rfl⟩ : syracuseStep 4681421 = 1755533) B1755533
theorem B1560307 : Blo 1385512 1560307 := bstep (se 1 (by rfl) ⟨1170230, by rfl⟩ : syracuseStep 1560307 = 2340461) B2340461
theorem B4681475 : Blo 1385512 4681475 := bstep (se 1 (by rfl) ⟨3511106, by rfl⟩ : syracuseStep 4681475 = 7022213) B7022213
theorem B2338625 : Blo 1385512 2338625 := bstep (se 2 (by rfl) ⟨876984, by rfl⟩ : syracuseStep 2338625 = 1753969) B1753969
theorem B2109251 : Blo 1385512 2109251 := bstep (se 1 (by rfl) ⟨1581938, by rfl⟩ : syracuseStep 2109251 = 3163877) B3163877
theorem B1560451 : Blo 1385512 1560451 := bstep (se 1 (by rfl) ⟨1170338, by rfl⟩ : syracuseStep 1560451 = 2340677) B2340677
theorem B2338753 : Blo 1385512 2338753 := bstep (se 2 (by rfl) ⟨877032, by rfl⟩ : syracuseStep 2338753 = 1754065) B1754065
theorem B2338787 : Blo 1385512 2338787 := bstep (se 1 (by rfl) ⟨1754090, by rfl⟩ : syracuseStep 2338787 = 3508181) B3508181
theorem B4681745 : Blo 1385512 4681745 := bstep (se 2 (by rfl) ⟨1755654, by rfl⟩ : syracuseStep 4681745 = 3511309) B3511309
theorem B1560595 : Blo 1385512 1560595 := bstep (se 1 (by rfl) ⟨1170446, by rfl⟩ : syracuseStep 1560595 = 2340893) B2340893
theorem B9007139 : Blo 1385512 9007139 := bstep (se 1 (by rfl) ⟨6755354, by rfl⟩ : syracuseStep 9007139 = 13510709) B13510709
theorem B2633809 : Blo 1385512 2633809 := bstep (se 2 (by rfl) ⟨987678, by rfl⟩ : syracuseStep 2633809 = 1975357) B1975357
theorem B2338915 : Blo 1385512 2338915 := bstep (se 1 (by rfl) ⟨1754186, by rfl⟩ : syracuseStep 2338915 = 3508373) B3508373
theorem B5263501 : Blo 1385512 5263501 := bstep (se 3 (by rfl) ⟨986906, by rfl⟩ : syracuseStep 5263501 = 1973813) B1973813
theorem B1560739 : Blo 1385512 1560739 := bstep (se 1 (by rfl) ⟨1170554, by rfl⟩ : syracuseStep 1560739 = 2341109) B2341109
theorem B3510449 : Blo 1385512 3510449 := bstep (se 2 (by rfl) ⟨1316418, by rfl⟩ : syracuseStep 3510449 = 2632837) B2632837
theorem B3748049 : Blo 1385512 3748049 := bstep (se 2 (by rfl) ⟨1405518, by rfl⟩ : syracuseStep 3748049 = 2811037) B2811037
theorem B3510499 : Blo 1385512 3510499 := bstep (se 1 (by rfl) ⟨2632874, by rfl⟩ : syracuseStep 3510499 = 5265749) B5265749
theorem B3207395 : Blo 1385512 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B2339057 : Blo 1385512 2339057 := bstep (se 2 (by rfl) ⟨877146, by rfl⟩ : syracuseStep 2339057 = 1754293) B1754293
theorem B5132593 : Blo 1385512 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B1560883 : Blo 1385512 1560883 := bstep (se 1 (by rfl) ⟨1170662, by rfl⟩ : syracuseStep 1560883 = 2341325) B2341325
theorem B1405283 : Blo 1385512 1405283 := bstep (se 1 (by rfl) ⟨1053962, by rfl⟩ : syracuseStep 1405283 = 2107925) B2107925
theorem B2339185 : Blo 1385512 2339185 := bstep (se 2 (by rfl) ⟨877194, by rfl⟩ : syracuseStep 2339185 = 1754389) B1754389
theorem B3510641 : Blo 1385512 3510641 := bstep (se 2 (by rfl) ⟨1316490, by rfl⟩ : syracuseStep 3510641 = 2632981) B2632981
theorem B2339219 : Blo 1385512 2339219 := bstep (se 1 (by rfl) ⟨1754414, by rfl⟩ : syracuseStep 2339219 = 3508829) B3508829
theorem B7016867 : Blo 1385512 7016867 := bstep (se 1 (by rfl) ⟨5262650, by rfl⟩ : syracuseStep 7016867 = 10525301) B10525301
theorem B14225861 : Blo 1385512 14225861 := bstep (se 4 (by rfl) ⟨1333674, by rfl⟩ : syracuseStep 14225861 = 2667349) B2667349
theorem B2339347 : Blo 1385512 2339347 := bstep (se 1 (by rfl) ⟨1754510, by rfl⟩ : syracuseStep 2339347 = 3509021) B3509021
theorem B2667043 : Blo 1385512 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B4682285 : Blo 1385512 4682285 := bstep (se 3 (by rfl) ⟨877928, by rfl⟩ : syracuseStep 4682285 = 1755857) B1755857
theorem B3117617 : Blo 1385512 3117617 := bstep (se 2 (by rfl) ⟨1169106, by rfl⟩ : syracuseStep 3117617 = 2338213) B2338213
theorem B3117635 : Blo 1385512 3117635 := bstep (se 1 (by rfl) ⟨2338226, by rfl⟩ : syracuseStep 3117635 = 4676453) B4676453
theorem B4682339 : Blo 1385512 4682339 := bstep (se 1 (by rfl) ⟨3511754, by rfl⟩ : syracuseStep 4682339 = 7023509) B7023509
theorem B7115377 : Blo 1385512 7115377 := bstep (se 2 (by rfl) ⟨2668266, by rfl⟩ : syracuseStep 7115377 = 5336533) B5336533
theorem B2339489 : Blo 1385512 2339489 := bstep (se 2 (by rfl) ⟨877308, by rfl⟩ : syracuseStep 2339489 = 1754617) B1754617
theorem B1872625 : Blo 1385512 1872625 := bstep (se 2 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 1872625 = 1404469) B1404469
theorem B7893773 : Blo 1385512 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B2339617 : Blo 1385512 2339617 := bstep (se 2 (by rfl) ⟨877356, by rfl⟩ : syracuseStep 2339617 = 1754713) B1754713
theorem B2339651 : Blo 1385512 2339651 := bstep (se 1 (by rfl) ⟨1754738, by rfl⟩ : syracuseStep 2339651 = 3509477) B3509477
theorem B3117905 : Blo 1385512 3117905 := bstep (se 2 (by rfl) ⟨1169214, by rfl⟩ : syracuseStep 3117905 = 2338429) B2338429
theorem B3117923 : Blo 1385512 3117923 := bstep (se 1 (by rfl) ⟨2338442, by rfl⟩ : syracuseStep 3117923 = 4676885) B4676885
theorem B4445027 : Blo 1385512 4445027 := bstep (se 1 (by rfl) ⟨3333770, by rfl⟩ : syracuseStep 4445027 = 6667541) B6667541
theorem B4682609 : Blo 1385512 4682609 := bstep (se 2 (by rfl) ⟨1755978, by rfl⟩ : syracuseStep 4682609 = 3511957) B3511957
theorem B5264291 : Blo 1385512 5264291 := bstep (se 1 (by rfl) ⟨3948218, by rfl⟩ : syracuseStep 5264291 = 7896437) B7896437
theorem B2339779 : Blo 1385512 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B3945485 : Blo 1385512 3945485 := bstep (se 3 (by rfl) ⟨739778, by rfl⟩ : syracuseStep 3945485 = 1479557) B1479557
theorem B2339921 : Blo 1385512 2339921 := bstep (se 2 (by rfl) ⟨877470, by rfl⟩ : syracuseStep 2339921 = 1754941) B1754941
theorem B2962531 : Blo 1385512 2962531 := bstep (se 1 (by rfl) ⟨2221898, by rfl⟩ : syracuseStep 2962531 = 4443797) B4443797
theorem B3118193 : Blo 1385512 3118193 := bstep (se 2 (by rfl) ⟨1169322, by rfl⟩ : syracuseStep 3118193 = 2338645) B2338645
theorem B3118211 : Blo 1385512 3118211 := bstep (se 1 (by rfl) ⟨2338658, by rfl⟩ : syracuseStep 3118211 = 4677317) B4677317
theorem B3945667 : Blo 1385512 3945667 := bstep (se 1 (by rfl) ⟨2959250, by rfl⟩ : syracuseStep 3945667 = 5918501) B5918501
theorem B8426693 : Blo 1385512 8426693 := bstep (se 4 (by rfl) ⟨790002, by rfl⟩ : syracuseStep 8426693 = 1580005) B1580005
theorem B9999557 : Blo 1385512 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B7017677 : Blo 1385512 7017677 := bstep (se 3 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 7017677 = 2631629) B2631629
theorem B2340049 : Blo 1385512 2340049 := bstep (se 2 (by rfl) ⟨877518, by rfl⟩ : syracuseStep 2340049 = 1755037) B1755037
theorem B2340083 : Blo 1385512 2340083 := bstep (se 1 (by rfl) ⟨1755062, by rfl⟩ : syracuseStep 2340083 = 3510125) B3510125
theorem B3511633 : Blo 1385512 3511633 := bstep (se 2 (by rfl) ⟨1316862, by rfl⟩ : syracuseStep 3511633 = 2633725) B2633725
theorem B3945827 : Blo 1385512 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B2340211 : Blo 1385512 2340211 := bstep (se 1 (by rfl) ⟨1755158, by rfl⟩ : syracuseStep 2340211 = 3510317) B3510317
theorem B5920141 : Blo 1385512 5920141 := bstep (se 3 (by rfl) ⟨1110026, by rfl⟩ : syracuseStep 5920141 = 2220053) B2220053
theorem B8885645 : Blo 1385512 8885645 := bstep (se 3 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 8885645 = 3332117) B3332117
theorem B3118481 : Blo 1385512 3118481 := bstep (se 2 (by rfl) ⟨1169430, by rfl⟩ : syracuseStep 3118481 = 2338861) B2338861
theorem B3118499 : Blo 1385512 3118499 := bstep (se 1 (by rfl) ⟨2338874, by rfl⟩ : syracuseStep 3118499 = 4677749) B4677749
theorem B4216237 : Blo 1385512 4216237 := bstep (se 3 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 4216237 = 1581089) B1581089
theorem B3331523 : Blo 1385512 3331523 := bstep (se 1 (by rfl) ⟨2498642, by rfl⟩ : syracuseStep 3331523 = 4997285) B4997285
theorem B17085937 : Blo 1385512 17085937 := bstep (se 2 (by rfl) ⟨6407226, by rfl⟩ : syracuseStep 17085937 = 12814453) B12814453
theorem B2340353 : Blo 1385512 2340353 := bstep (se 2 (by rfl) ⟨877632, by rfl⟩ : syracuseStep 2340353 = 1755265) B1755265
theorem B5264945 : Blo 1385512 5264945 := bstep (se 2 (by rfl) ⟨1974354, by rfl⟩ : syracuseStep 5264945 = 3948709) B3948709
theorem B2962993 : Blo 1385512 2962993 := bstep (se 2 (by rfl) ⟨1111122, by rfl⟩ : syracuseStep 2962993 = 2222245) B2222245
theorem B2078273 : Blo 1385512 2078273 := bstep (se 2 (by rfl) ⟨779352, by rfl⟩ : syracuseStep 2078273 = 1558705) B1558705
theorem B2078291 : Blo 1385512 2078291 := bstep (se 1 (by rfl) ⟨1558718, by rfl⟩ : syracuseStep 2078291 = 3117437) B3117437
theorem B3511907 : Blo 1385512 3511907 := bstep (se 1 (by rfl) ⟨2633930, by rfl⟩ : syracuseStep 3511907 = 5267861) B5267861
theorem B2078321 : Blo 1385512 2078321 := bstep (se 2 (by rfl) ⟨779370, by rfl⟩ : syracuseStep 2078321 = 1558741) B1558741
theorem B2340481 : Blo 1385512 2340481 := bstep (se 2 (by rfl) ⟨877680, by rfl⟩ : syracuseStep 2340481 = 1755361) B1755361
theorem B2078339 : Blo 1385512 2078339 := bstep (se 1 (by rfl) ⟨1558754, by rfl⟩ : syracuseStep 2078339 = 3117509) B3117509
theorem B8877701 : Blo 1385512 8877701 := bstep (se 4 (by rfl) ⟨832284, by rfl⟩ : syracuseStep 8877701 = 1664569) B1664569
theorem B2078369 : Blo 1385512 2078369 := bstep (se 2 (by rfl) ⟨779388, by rfl⟩ : syracuseStep 2078369 = 1558777) B1558777
theorem B2340515 : Blo 1385512 2340515 := bstep (se 1 (by rfl) ⟨1755386, by rfl⟩ : syracuseStep 2340515 = 3510773) B3510773
theorem B3118769 : Blo 1385512 3118769 := bstep (se 2 (by rfl) ⟨1169538, by rfl⟩ : syracuseStep 3118769 = 2339077) B2339077
theorem B7894705 : Blo 1385512 7894705 := bstep (se 2 (by rfl) ⟨2960514, by rfl⟩ : syracuseStep 7894705 = 5921029) B5921029
theorem B2078387 : Blo 1385512 2078387 := bstep (se 1 (by rfl) ⟨1558790, by rfl⟩ : syracuseStep 2078387 = 3117581) B3117581
theorem B8115889 : Blo 1385512 8115889 := bstep (se 2 (by rfl) ⟨3043458, by rfl⟩ : syracuseStep 8115889 = 6086917) B6086917
theorem B3118787 : Blo 1385512 3118787 := bstep (se 1 (by rfl) ⟨2339090, by rfl⟩ : syracuseStep 3118787 = 4678181) B4678181
theorem B2078417 : Blo 1385512 2078417 := bstep (se 2 (by rfl) ⟨779406, by rfl⟩ : syracuseStep 2078417 = 1558813) B1558813
theorem B1480403 : Blo 1385512 1480403 := bstep (se 1 (by rfl) ⟨1110302, by rfl⟩ : syracuseStep 1480403 = 2220605) B2220605
theorem B2078435 : Blo 1385512 2078435 := bstep (se 1 (by rfl) ⟨1558826, by rfl⟩ : syracuseStep 2078435 = 3117653) B3117653
theorem B2078465 : Blo 1385512 2078465 := bstep (se 2 (by rfl) ⟨779424, by rfl⟩ : syracuseStep 2078465 = 1558849) B1558849
theorem B2078483 : Blo 1385512 2078483 := bstep (se 1 (by rfl) ⟨1558862, by rfl⟩ : syracuseStep 2078483 = 3117725) B3117725
theorem B2340643 : Blo 1385512 2340643 := bstep (se 1 (by rfl) ⟨1755482, by rfl⟩ : syracuseStep 2340643 = 3510965) B3510965
theorem B3512099 : Blo 1385512 3512099 := bstep (se 1 (by rfl) ⟨2634074, by rfl⟩ : syracuseStep 3512099 = 5268149) B5268149
theorem B2078513 : Blo 1385512 2078513 := bstep (se 2 (by rfl) ⟨779442, by rfl⟩ : syracuseStep 2078513 = 1558885) B1558885
theorem B2078531 : Blo 1385512 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B3331907 : Blo 1385512 3331907 := bstep (se 1 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 3331907 = 4997861) B4997861
theorem B2078561 : Blo 1385512 2078561 := bstep (se 2 (by rfl) ⟨779460, by rfl⟩ : syracuseStep 2078561 = 1558921) B1558921
theorem B2078579 : Blo 1385512 2078579 := bstep (se 1 (by rfl) ⟨1558934, by rfl⟩ : syracuseStep 2078579 = 3117869) B3117869
theorem B1521539 : Blo 1385512 1521539 := bstep (se 1 (by rfl) ⟨1141154, by rfl⟩ : syracuseStep 1521539 = 2282309) B2282309
theorem B2078609 : Blo 1385512 2078609 := bstep (se 2 (by rfl) ⟨779478, by rfl⟩ : syracuseStep 2078609 = 1558957) B1558957
theorem B2078627 : Blo 1385512 2078627 := bstep (se 1 (by rfl) ⟨1558970, by rfl⟩ : syracuseStep 2078627 = 3117941) B3117941
theorem B2340785 : Blo 1385512 2340785 := bstep (se 2 (by rfl) ⟨877794, by rfl⟩ : syracuseStep 2340785 = 1755589) B1755589
theorem B2078657 : Blo 1385512 2078657 := bstep (se 2 (by rfl) ⟨779496, by rfl⟩ : syracuseStep 2078657 = 1558993) B1558993
theorem B3119057 : Blo 1385512 3119057 := bstep (se 2 (by rfl) ⟨1169646, by rfl⟩ : syracuseStep 3119057 = 2339293) B2339293
theorem B2078675 : Blo 1385512 2078675 := bstep (se 1 (by rfl) ⟨1559006, by rfl⟩ : syracuseStep 2078675 = 3118013) B3118013
theorem B3119075 : Blo 1385512 3119075 := bstep (se 1 (by rfl) ⟨2339306, by rfl⟩ : syracuseStep 3119075 = 4678613) B4678613
theorem B2078705 : Blo 1385512 2078705 := bstep (se 2 (by rfl) ⟨779514, by rfl⟩ : syracuseStep 2078705 = 1559029) B1559029
theorem B2078723 : Blo 1385512 2078723 := bstep (se 1 (by rfl) ⟨1559042, by rfl⟩ : syracuseStep 2078723 = 3118085) B3118085
theorem B2078753 : Blo 1385512 2078753 := bstep (se 2 (by rfl) ⟨779532, by rfl⟩ : syracuseStep 2078753 = 1559065) B1559065
theorem B2340913 : Blo 1385512 2340913 := bstep (se 2 (by rfl) ⟨877842, by rfl⟩ : syracuseStep 2340913 = 1755685) B1755685
theorem B2078771 : Blo 1385512 2078771 := bstep (se 1 (by rfl) ⟨1559078, by rfl⟩ : syracuseStep 2078771 = 3118157) B3118157
theorem B2078801 : Blo 1385512 2078801 := bstep (se 2 (by rfl) ⟨779550, by rfl⟩ : syracuseStep 2078801 = 1559101) B1559101
theorem B2340947 : Blo 1385512 2340947 := bstep (se 1 (by rfl) ⟨1755710, by rfl⟩ : syracuseStep 2340947 = 3511421) B3511421
theorem B2078819 : Blo 1385512 2078819 := bstep (se 1 (by rfl) ⟨1559114, by rfl⟩ : syracuseStep 2078819 = 3118229) B3118229
theorem B1874035 : Blo 1385512 1874035 := bstep (se 1 (by rfl) ⟨1405526, by rfl⟩ : syracuseStep 1874035 = 2811053) B2811053
theorem B2078849 : Blo 1385512 2078849 := bstep (se 2 (by rfl) ⟨779568, by rfl⟩ : syracuseStep 2078849 = 1559137) B1559137
theorem B2078867 : Blo 1385512 2078867 := bstep (se 1 (by rfl) ⟨1559150, by rfl⟩ : syracuseStep 2078867 = 3118301) B3118301
theorem B2078897 : Blo 1385512 2078897 := bstep (se 2 (by rfl) ⟨779586, by rfl⟩ : syracuseStep 2078897 = 1559173) B1559173
theorem B2668721 : Blo 1385512 2668721 := bstep (se 2 (by rfl) ⟨1000770, by rfl⟩ : syracuseStep 2668721 = 2001541) B2001541
theorem B2078915 : Blo 1385512 2078915 := bstep (se 1 (by rfl) ⟨1559186, by rfl⟩ : syracuseStep 2078915 = 3118373) B3118373
theorem B2341075 : Blo 1385512 2341075 := bstep (se 1 (by rfl) ⟨1755806, by rfl⟩ : syracuseStep 2341075 = 3511613) B3511613
theorem B2078945 : Blo 1385512 2078945 := bstep (se 2 (by rfl) ⟨779604, by rfl⟩ : syracuseStep 2078945 = 1559209) B1559209
theorem B3119345 : Blo 1385512 3119345 := bstep (se 2 (by rfl) ⟨1169754, by rfl⟩ : syracuseStep 3119345 = 2339509) B2339509
theorem B2078963 : Blo 1385512 2078963 := bstep (se 1 (by rfl) ⟨1559222, by rfl⟩ : syracuseStep 2078963 = 3118445) B3118445
theorem B3119363 : Blo 1385512 3119363 := bstep (se 1 (by rfl) ⟨2339522, by rfl⟩ : syracuseStep 3119363 = 4679045) B4679045
theorem B2078993 : Blo 1385512 2078993 := bstep (se 2 (by rfl) ⟨779622, by rfl⟩ : syracuseStep 2078993 = 1559245) B1559245
theorem B72030485 : Blo 1385512 72030485 := bstep (se 6 (by rfl) ⟨1688214, by rfl⟩ : syracuseStep 72030485 = 3376429) B3376429
theorem B32020757 : Blo 1385512 32020757 := bstep (se 6 (by rfl) ⟨750486, by rfl⟩ : syracuseStep 32020757 = 1500973) B1500973
theorem B2079011 : Blo 1385512 2079011 := bstep (se 1 (by rfl) ⟨1559258, by rfl⟩ : syracuseStep 2079011 = 3118517) B3118517
theorem B1874225 : Blo 1385512 1874225 := bstep (se 2 (by rfl) ⟨702834, by rfl⟩ : syracuseStep 1874225 = 1405669) B1405669
theorem B2079041 : Blo 1385512 2079041 := bstep (se 2 (by rfl) ⟨779640, by rfl⟩ : syracuseStep 2079041 = 1559281) B1559281
theorem B2079059 : Blo 1385512 2079059 := bstep (se 1 (by rfl) ⟨1559294, by rfl⟩ : syracuseStep 2079059 = 3118589) B3118589
theorem B2341217 : Blo 1385512 2341217 := bstep (se 2 (by rfl) ⟨877956, by rfl⟩ : syracuseStep 2341217 = 1755913) B1755913
theorem B2079089 : Blo 1385512 2079089 := bstep (se 2 (by rfl) ⟨779658, by rfl⟩ : syracuseStep 2079089 = 1559317) B1559317
theorem B3332465 : Blo 1385512 3332465 := bstep (se 2 (by rfl) ⟨1249674, by rfl⟩ : syracuseStep 3332465 = 2499349) B2499349
theorem B2079107 : Blo 1385512 2079107 := bstep (se 1 (by rfl) ⟨1559330, by rfl⟩ : syracuseStep 2079107 = 3118661) B3118661
theorem B4741517 : Blo 1385512 4741517 := bstep (se 3 (by rfl) ⟨889034, by rfl⟩ : syracuseStep 4741517 = 1778069) B1778069
theorem B3946897 : Blo 1385512 3946897 := bstep (se 2 (by rfl) ⟨1480086, by rfl⟩ : syracuseStep 3946897 = 2960173) B2960173
theorem B2079137 : Blo 1385512 2079137 := bstep (se 2 (by rfl) ⟨779676, by rfl⟩ : syracuseStep 2079137 = 1559353) B1559353
theorem B5921201 : Blo 1385512 5921201 := bstep (se 2 (by rfl) ⟨2220450, by rfl⟩ : syracuseStep 5921201 = 4440901) B4440901
theorem B7494065 : Blo 1385512 7494065 := bstep (se 2 (by rfl) ⟨2810274, by rfl⟩ : syracuseStep 7494065 = 5620549) B5620549
theorem B2079155 : Blo 1385512 2079155 := bstep (se 1 (by rfl) ⟨1559366, by rfl⟩ : syracuseStep 2079155 = 3118733) B3118733
theorem B2079185 : Blo 1385512 2079185 := bstep (se 2 (by rfl) ⟨779694, by rfl⟩ : syracuseStep 2079185 = 1559389) B1559389
theorem B2341345 : Blo 1385512 2341345 := bstep (se 2 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 2341345 = 1756009) B1756009
theorem B2079203 : Blo 1385512 2079203 := bstep (se 1 (by rfl) ⟨1559402, by rfl⟩ : syracuseStep 2079203 = 3118805) B3118805
theorem B2079233 : Blo 1385512 2079233 := bstep (se 2 (by rfl) ⟨779712, by rfl⟩ : syracuseStep 2079233 = 1559425) B1559425
theorem B2341379 : Blo 1385512 2341379 := bstep (se 1 (by rfl) ⟨1756034, by rfl⟩ : syracuseStep 2341379 = 3512069) B3512069
theorem B7494149 : Blo 1385512 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B3119633 : Blo 1385512 3119633 := bstep (se 2 (by rfl) ⟨1169862, by rfl⟩ : syracuseStep 3119633 = 2339725) B2339725
theorem B2079251 : Blo 1385512 2079251 := bstep (se 1 (by rfl) ⟨1559438, by rfl⟩ : syracuseStep 2079251 = 3118877) B3118877
theorem B3119651 : Blo 1385512 3119651 := bstep (se 1 (by rfl) ⟨2339738, by rfl⟩ : syracuseStep 3119651 = 4679477) B4679477
theorem B2079281 : Blo 1385512 2079281 := bstep (se 2 (by rfl) ⟨779730, by rfl⟩ : syracuseStep 2079281 = 1559461) B1559461
theorem B2079299 : Blo 1385512 2079299 := bstep (se 1 (by rfl) ⟨1559474, by rfl⟩ : syracuseStep 2079299 = 3118949) B3118949
theorem B2079329 : Blo 1385512 2079329 := bstep (se 2 (by rfl) ⟨779748, by rfl⟩ : syracuseStep 2079329 = 1559497) B1559497
theorem B2079347 : Blo 1385512 2079347 := bstep (se 1 (by rfl) ⟨1559510, by rfl⟩ : syracuseStep 2079347 = 3119021) B3119021
theorem B4676237 : Blo 1385512 4676237 := bstep (se 3 (by rfl) ⟨876794, by rfl⟩ : syracuseStep 4676237 = 1753589) B1753589
theorem B2079377 : Blo 1385512 2079377 := bstep (se 2 (by rfl) ⟨779766, by rfl⟩ : syracuseStep 2079377 = 1559533) B1559533
theorem B2079395 : Blo 1385512 2079395 := bstep (se 1 (by rfl) ⟨1559546, by rfl⟩ : syracuseStep 2079395 = 3119093) B3119093
theorem B2079425 : Blo 1385512 2079425 := bstep (se 2 (by rfl) ⟨779784, by rfl⟩ : syracuseStep 2079425 = 1559569) B1559569
theorem B4676291 : Blo 1385512 4676291 := bstep (se 1 (by rfl) ⟨3507218, by rfl⟩ : syracuseStep 4676291 = 7014437) B7014437
theorem B2079443 : Blo 1385512 2079443 := bstep (se 1 (by rfl) ⟨1559582, by rfl⟩ : syracuseStep 2079443 = 3119165) B3119165
theorem B2079473 : Blo 1385512 2079473 := bstep (se 2 (by rfl) ⟨779802, by rfl⟩ : syracuseStep 2079473 = 1559605) B1559605
theorem B1972993 : Blo 1385512 1972993 := bstep (se 2 (by rfl) ⟨739872, by rfl⟩ : syracuseStep 1972993 = 1479745) B1479745
theorem B2079491 : Blo 1385512 2079491 := bstep (se 1 (by rfl) ⟨1559618, by rfl⟩ : syracuseStep 2079491 = 3119237) B3119237
theorem B2079521 : Blo 1385512 2079521 := bstep (se 2 (by rfl) ⟨779820, by rfl⟩ : syracuseStep 2079521 = 1559641) B1559641
theorem B2497315 : Blo 1385512 2497315 := bstep (se 1 (by rfl) ⟨1872986, by rfl⟩ : syracuseStep 2497315 = 3745973) B3745973
theorem B3119921 : Blo 1385512 3119921 := bstep (se 2 (by rfl) ⟨1169970, by rfl⟩ : syracuseStep 3119921 = 2339941) B2339941
theorem B2079539 : Blo 1385512 2079539 := bstep (se 1 (by rfl) ⟨1559654, by rfl⟩ : syracuseStep 2079539 = 3119309) B3119309
theorem B3119939 : Blo 1385512 3119939 := bstep (se 1 (by rfl) ⟨2339954, by rfl⟩ : syracuseStep 3119939 = 4679909) B4679909
theorem B1481539 : Blo 1385512 1481539 := bstep (se 1 (by rfl) ⟨1111154, by rfl⟩ : syracuseStep 1481539 = 2222309) B2222309
theorem B2079569 : Blo 1385512 2079569 := bstep (se 2 (by rfl) ⟨779838, by rfl⟩ : syracuseStep 2079569 = 1559677) B1559677
theorem B2079587 : Blo 1385512 2079587 := bstep (se 1 (by rfl) ⟨1559690, by rfl⟩ : syracuseStep 2079587 = 3119381) B3119381
theorem B3332963 : Blo 1385512 3332963 := bstep (se 1 (by rfl) ⟨2499722, by rfl⟩ : syracuseStep 3332963 = 4999445) B4999445
theorem B1973107 : Blo 1385512 1973107 := bstep (se 1 (by rfl) ⟨1479830, by rfl⟩ : syracuseStep 1973107 = 2959661) B2959661
theorem B2079617 : Blo 1385512 2079617 := bstep (se 2 (by rfl) ⟨779856, by rfl⟩ : syracuseStep 2079617 = 1559713) B1559713
theorem B2079635 : Blo 1385512 2079635 := bstep (se 1 (by rfl) ⟨1559726, by rfl⟩ : syracuseStep 2079635 = 3119453) B3119453
theorem B2079665 : Blo 1385512 2079665 := bstep (se 2 (by rfl) ⟨779874, by rfl⟩ : syracuseStep 2079665 = 1559749) B1559749
theorem B2079683 : Blo 1385512 2079683 := bstep (se 1 (by rfl) ⟨1559762, by rfl⟩ : syracuseStep 2079683 = 3119525) B3119525
theorem B4676561 : Blo 1385512 4676561 := bstep (se 2 (by rfl) ⟨1753710, by rfl⟩ : syracuseStep 4676561 = 3507421) B3507421
theorem B2079713 : Blo 1385512 2079713 := bstep (se 2 (by rfl) ⟨779892, by rfl⟩ : syracuseStep 2079713 = 1559785) B1559785
theorem B11238371 : Blo 1385512 11238371 := bstep (se 1 (by rfl) ⟨8428778, by rfl⟩ : syracuseStep 11238371 = 16857557) B16857557
theorem B5266403 : Blo 1385512 5266403 := bstep (se 1 (by rfl) ⟨3949802, by rfl⟩ : syracuseStep 5266403 = 7899605) B7899605
theorem B5266417 : Blo 1385512 5266417 := bstep (se 2 (by rfl) ⟨1974906, by rfl⟩ : syracuseStep 5266417 = 3949813) B3949813
theorem B2079731 : Blo 1385512 2079731 := bstep (se 1 (by rfl) ⟨1559798, by rfl⟩ : syracuseStep 2079731 = 3119597) B3119597
theorem B2079761 : Blo 1385512 2079761 := bstep (se 2 (by rfl) ⟨779910, by rfl⟩ : syracuseStep 2079761 = 1559821) B1559821
theorem B2079779 : Blo 1385512 2079779 := bstep (se 1 (by rfl) ⟨1559834, by rfl⟩ : syracuseStep 2079779 = 3119669) B3119669
theorem B3333155 : Blo 1385512 3333155 := bstep (se 1 (by rfl) ⟨2499866, by rfl⟩ : syracuseStep 3333155 = 4999733) B4999733
theorem B2079809 : Blo 1385512 2079809 := bstep (se 2 (by rfl) ⟨779928, by rfl⟩ : syracuseStep 2079809 = 1559857) B1559857
theorem B3120209 : Blo 1385512 3120209 := bstep (se 2 (by rfl) ⟨1170078, by rfl⟩ : syracuseStep 3120209 = 2340157) B2340157
theorem B2079827 : Blo 1385512 2079827 := bstep (se 1 (by rfl) ⟨1559870, by rfl⟩ : syracuseStep 2079827 = 3119741) B3119741
theorem B7896163 : Blo 1385512 7896163 := bstep (se 1 (by rfl) ⟨5922122, by rfl⟩ : syracuseStep 7896163 = 11844245) B11844245
theorem B3120227 : Blo 1385512 3120227 := bstep (se 1 (by rfl) ⟨2340170, by rfl⟩ : syracuseStep 3120227 = 4680341) B4680341
theorem B2079857 : Blo 1385512 2079857 := bstep (se 2 (by rfl) ⟨779946, by rfl⟩ : syracuseStep 2079857 = 1559893) B1559893
theorem B2079875 : Blo 1385512 2079875 := bstep (se 1 (by rfl) ⟨1559906, by rfl⟩ : syracuseStep 2079875 = 3119813) B3119813
theorem B2079905 : Blo 1385512 2079905 := bstep (se 2 (by rfl) ⟨779964, by rfl⟩ : syracuseStep 2079905 = 1559929) B1559929
theorem B2809009 : Blo 1385512 2809009 := bstep (se 2 (by rfl) ⟨1053378, by rfl⟩ : syracuseStep 2809009 = 2106757) B2106757
theorem B2079923 : Blo 1385512 2079923 := bstep (se 1 (by rfl) ⟨1559942, by rfl⟩ : syracuseStep 2079923 = 3119885) B3119885
theorem B2079953 : Blo 1385512 2079953 := bstep (se 2 (by rfl) ⟨779982, by rfl⟩ : syracuseStep 2079953 = 1559965) B1559965
theorem B2079971 : Blo 1385512 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B2080001 : Blo 1385512 2080001 := bstep (se 2 (by rfl) ⟨780000, by rfl⟩ : syracuseStep 2080001 = 1560001) B1560001
theorem B2080019 : Blo 1385512 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B2080049 : Blo 1385512 2080049 := bstep (se 2 (by rfl) ⟨780018, by rfl⟩ : syracuseStep 2080049 = 1560037) B1560037
theorem B2080067 : Blo 1385512 2080067 := bstep (se 1 (by rfl) ⟨1560050, by rfl⟩ : syracuseStep 2080067 = 3120101) B3120101
theorem B2080097 : Blo 1385512 2080097 := bstep (se 2 (by rfl) ⟨780036, by rfl⟩ : syracuseStep 2080097 = 1560073) B1560073
theorem B3120497 : Blo 1385512 3120497 := bstep (se 2 (by rfl) ⟨1170186, by rfl⟩ : syracuseStep 3120497 = 2340373) B2340373
theorem B2080115 : Blo 1385512 2080115 := bstep (se 1 (by rfl) ⟨1560086, by rfl⟩ : syracuseStep 2080115 = 3120173) B3120173
theorem B3120515 : Blo 1385512 3120515 := bstep (se 1 (by rfl) ⟨2340386, by rfl⟩ : syracuseStep 3120515 = 4680773) B4680773
theorem B2080145 : Blo 1385512 2080145 := bstep (se 2 (by rfl) ⟨780054, by rfl⟩ : syracuseStep 2080145 = 1560109) B1560109
theorem B2080163 : Blo 1385512 2080163 := bstep (se 1 (by rfl) ⟨1560122, by rfl⟩ : syracuseStep 2080163 = 3120245) B3120245
theorem B2080193 : Blo 1385512 2080193 := bstep (se 2 (by rfl) ⟨780072, by rfl⟩ : syracuseStep 2080193 = 1560145) B1560145
theorem B2080211 : Blo 1385512 2080211 := bstep (se 1 (by rfl) ⟨1560158, by rfl⟩ : syracuseStep 2080211 = 3120317) B3120317
theorem B4677101 : Blo 1385512 4677101 := bstep (se 3 (by rfl) ⟨876956, by rfl⟩ : syracuseStep 4677101 = 1753913) B1753913
theorem B2080241 : Blo 1385512 2080241 := bstep (se 2 (by rfl) ⟨780090, by rfl⟩ : syracuseStep 2080241 = 1560181) B1560181
theorem B2080259 : Blo 1385512 2080259 := bstep (se 1 (by rfl) ⟨1560194, by rfl⟩ : syracuseStep 2080259 = 3120389) B3120389
theorem B4439569 : Blo 1385512 4439569 := bstep (se 2 (by rfl) ⟨1664838, by rfl⟩ : syracuseStep 4439569 = 3329677) B3329677
theorem B2080289 : Blo 1385512 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B4677155 : Blo 1385512 4677155 := bstep (se 1 (by rfl) ⟨3507866, by rfl⟩ : syracuseStep 4677155 = 7015733) B7015733
theorem B2080307 : Blo 1385512 2080307 := bstep (se 1 (by rfl) ⟨1560230, by rfl⟩ : syracuseStep 2080307 = 3120461) B3120461
theorem B8887877 : Blo 1385512 8887877 := bstep (se 4 (by rfl) ⟨833238, by rfl⟩ : syracuseStep 8887877 = 1666477) B1666477
theorem B2080337 : Blo 1385512 2080337 := bstep (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) B1560253
theorem B2252371 : Blo 1385512 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B2080355 : Blo 1385512 2080355 := bstep (se 1 (by rfl) ⟨1560266, by rfl⟩ : syracuseStep 2080355 = 3120533) B3120533
theorem B7896689 : Blo 1385512 7896689 := bstep (se 2 (by rfl) ⟨2961258, by rfl⟩ : syracuseStep 7896689 = 5922517) B5922517
theorem B2080385 : Blo 1385512 2080385 := bstep (se 2 (by rfl) ⟨780144, by rfl⟩ : syracuseStep 2080385 = 1560289) B1560289
theorem B3948173 : Blo 1385512 3948173 := bstep (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) B1480565
theorem B3120785 : Blo 1385512 3120785 := bstep (se 2 (by rfl) ⟨1170294, by rfl⟩ : syracuseStep 3120785 = 2340589) B2340589
theorem B2080403 : Blo 1385512 2080403 := bstep (se 1 (by rfl) ⟨1560302, by rfl⟩ : syracuseStep 2080403 = 3120605) B3120605
theorem B3120803 : Blo 1385512 3120803 := bstep (se 1 (by rfl) ⟨2340602, by rfl⟩ : syracuseStep 3120803 = 4681205) B4681205
theorem B2080433 : Blo 1385512 2080433 := bstep (se 2 (by rfl) ⟨780162, by rfl⟩ : syracuseStep 2080433 = 1560325) B1560325
theorem B4439747 : Blo 1385512 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B2080451 : Blo 1385512 2080451 := bstep (se 1 (by rfl) ⟨1560338, by rfl⟩ : syracuseStep 2080451 = 3120677) B3120677
theorem B9010885 : Blo 1385512 9010885 := bstep (se 4 (by rfl) ⟨844770, by rfl⟩ : syracuseStep 9010885 = 1689541) B1689541
theorem B2080481 : Blo 1385512 2080481 := bstep (se 2 (by rfl) ⟨780180, by rfl⟩ : syracuseStep 2080481 = 1560361) B1560361
theorem B4562669 : Blo 1385512 4562669 := bstep (se 3 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 4562669 = 1711001) B1711001
theorem B2080499 : Blo 1385512 2080499 := bstep (se 1 (by rfl) ⟨1560374, by rfl⟩ : syracuseStep 2080499 = 3120749) B3120749
theorem B2080529 : Blo 1385512 2080529 := bstep (se 2 (by rfl) ⟨780198, by rfl⟩ : syracuseStep 2080529 = 1560397) B1560397
theorem B2498339 : Blo 1385512 2498339 := bstep (se 1 (by rfl) ⟨1873754, by rfl⟩ : syracuseStep 2498339 = 3747509) B3747509
theorem B2080547 : Blo 1385512 2080547 := bstep (se 1 (by rfl) ⟨1560410, by rfl⟩ : syracuseStep 2080547 = 3120821) B3120821
theorem B4677425 : Blo 1385512 4677425 := bstep (se 2 (by rfl) ⟨1754034, by rfl⟩ : syracuseStep 4677425 = 3508069) B3508069
theorem B2080577 : Blo 1385512 2080577 := bstep (se 2 (by rfl) ⟨780216, by rfl⟩ : syracuseStep 2080577 = 1560433) B1560433
theorem B3948355 : Blo 1385512 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B2080595 : Blo 1385512 2080595 := bstep (se 1 (by rfl) ⟨1560446, by rfl⟩ : syracuseStep 2080595 = 3120893) B3120893
theorem B3948401 : Blo 1385512 3948401 := bstep (se 2 (by rfl) ⟨1480650, by rfl⟩ : syracuseStep 3948401 = 2961301) B2961301
theorem B2080625 : Blo 1385512 2080625 := bstep (se 2 (by rfl) ⟨780234, by rfl⟩ : syracuseStep 2080625 = 1560469) B1560469
theorem B2080643 : Blo 1385512 2080643 := bstep (se 1 (by rfl) ⟨1560482, by rfl⟩ : syracuseStep 2080643 = 3120965) B3120965
theorem B2080673 : Blo 1385512 2080673 := bstep (se 2 (by rfl) ⟨780252, by rfl⟩ : syracuseStep 2080673 = 1560505) B1560505
theorem B3121073 : Blo 1385512 3121073 := bstep (se 2 (by rfl) ⟨1170402, by rfl⟩ : syracuseStep 3121073 = 2340805) B2340805
theorem B2080691 : Blo 1385512 2080691 := bstep (se 1 (by rfl) ⟨1560518, by rfl⟩ : syracuseStep 2080691 = 3121037) B3121037
theorem B3121091 : Blo 1385512 3121091 := bstep (se 1 (by rfl) ⟨2340818, by rfl⟩ : syracuseStep 3121091 = 4681637) B4681637
theorem B2080721 : Blo 1385512 2080721 := bstep (se 2 (by rfl) ⟨780270, by rfl⟩ : syracuseStep 2080721 = 1560541) B1560541
theorem B11837411 : Blo 1385512 11837411 := bstep (se 1 (by rfl) ⟨8878058, by rfl⟩ : syracuseStep 11837411 = 17756117) B17756117
theorem B2080739 : Blo 1385512 2080739 := bstep (se 1 (by rfl) ⟨1560554, by rfl⟩ : syracuseStep 2080739 = 3121109) B3121109
theorem B3121163 : Blo 1385512 3121163 := bstep (se 1 (by rfl) ⟨2340872, by rfl⟩ : syracuseStep 3121163 = 4681745) B4681745
theorem B2080793 : Blo 1385512 2080793 := bstep (se 2 (by rfl) ⟨780297, by rfl⟩ : syracuseStep 2080793 = 1560595) B1560595
theorem B3121217 : Blo 1385512 3121217 := bstep (se 2 (by rfl) ⟨1170456, by rfl⟩ : syracuseStep 3121217 = 2340913) B2340913
theorem B24019037 : Blo 1385512 24019037 := bstep (se 3 (by rfl) ⟨4503569, by rfl⟩ : syracuseStep 24019037 = 9007139) B9007139
theorem B8888413 : Blo 1385512 8888413 := bstep (se 3 (by rfl) ⟨1666577, by rfl⟩ : syracuseStep 8888413 = 3333155) B3333155
theorem B2498699 : Blo 1385512 2498699 := bstep (se 1 (by rfl) ⟨1874024, by rfl⟩ : syracuseStep 2498699 = 3748049) B3748049
theorem B2080907 : Blo 1385512 2080907 := bstep (se 1 (by rfl) ⟨1560680, by rfl⟩ : syracuseStep 2080907 = 3121361) B3121361
theorem B2080919 : Blo 1385512 2080919 := bstep (se 1 (by rfl) ⟨1560689, by rfl⟩ : syracuseStep 2080919 = 3121379) B3121379
theorem B2080985 : Blo 1385512 2080985 := bstep (se 2 (by rfl) ⟨780369, by rfl⟩ : syracuseStep 2080985 = 1560739) B1560739
theorem B4677911 : Blo 1385512 4677911 := bstep (se 1 (by rfl) ⟨3508433, by rfl⟩ : syracuseStep 4677911 = 7016867) B7016867
theorem B3121433 : Blo 1385512 3121433 := bstep (se 2 (by rfl) ⟨1170537, by rfl⟩ : syracuseStep 3121433 = 2341075) B2341075
theorem B2081099 : Blo 1385512 2081099 := bstep (se 1 (by rfl) ⟨1560824, by rfl⟩ : syracuseStep 2081099 = 3121649) B3121649
theorem B2081111 : Blo 1385512 2081111 := bstep (se 1 (by rfl) ⟨1560833, by rfl⟩ : syracuseStep 2081111 = 3121667) B3121667
theorem B3121523 : Blo 1385512 3121523 := bstep (se 1 (by rfl) ⟨2341142, by rfl⟩ : syracuseStep 3121523 = 4682285) B4682285
theorem B3121559 : Blo 1385512 3121559 := bstep (se 1 (by rfl) ⟨2341169, by rfl⟩ : syracuseStep 3121559 = 4682339) B4682339
theorem B2081177 : Blo 1385512 2081177 := bstep (se 2 (by rfl) ⟨780441, by rfl⟩ : syracuseStep 2081177 = 1560883) B1560883
theorem B3121739 : Blo 1385512 3121739 := bstep (se 1 (by rfl) ⟨2341304, by rfl⟩ : syracuseStep 3121739 = 4682609) B4682609
theorem B8553053 : Blo 1385512 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B9994853 : Blo 1385512 9994853 := bstep (se 4 (by rfl) ⟨937017, by rfl⟩ : syracuseStep 9994853 = 1874035) B1874035
theorem B3121793 : Blo 1385512 3121793 := bstep (se 2 (by rfl) ⟨1170672, by rfl⟩ : syracuseStep 3121793 = 2341345) B2341345
theorem B3162763 : Blo 1385512 3162763 := bstep (se 1 (by rfl) ⟨2372072, by rfl⟩ : syracuseStep 3162763 = 4744145) B4744145
theorem B1753751 : Blo 1385512 1753751 := bstep (se 1 (by rfl) ⟨1315313, by rfl⟩ : syracuseStep 1753751 = 2630627) B2630627
theorem B2630323 : Blo 1385512 2630323 := bstep (se 1 (by rfl) ⟨1972742, by rfl⟩ : syracuseStep 2630323 = 3945485) B3945485
theorem B3556057 : Blo 1385512 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B4997933 : Blo 1385512 4997933 := bstep (se 3 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 4997933 = 1874225) B1874225
theorem B4678451 : Blo 1385512 4678451 := bstep (se 1 (by rfl) ⟨3508838, by rfl⟩ : syracuseStep 4678451 = 7017677) B7017677
theorem B9487169 : Blo 1385512 9487169 := bstep (se 2 (by rfl) ⟨3557688, by rfl⟩ : syracuseStep 9487169 = 7115377) B7115377
theorem B2630551 : Blo 1385512 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B15000497 : Blo 1385512 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B5923763 : Blo 1385512 5923763 := bstep (se 1 (by rfl) ⟨4442822, by rfl⟩ : syracuseStep 5923763 = 8885645) B8885645
theorem B2221015 : Blo 1385512 2221015 := bstep (se 1 (by rfl) ⟨1665761, by rfl⟩ : syracuseStep 2221015 = 3331523) B3331523
theorem B2630657 : Blo 1385512 2630657 := bstep (se 2 (by rfl) ⟨986496, by rfl⟩ : syracuseStep 2630657 = 1972993) B1972993
theorem B1385515 : Blo 1385512 1385515 := bstep (se 1 (by rfl) ⟨1039136, by rfl⟩ : syracuseStep 1385515 = 2078273) B2078273
theorem B1385527 : Blo 1385512 1385527 := bstep (se 1 (by rfl) ⟨1039145, by rfl⟩ : syracuseStep 1385527 = 2078291) B2078291
theorem B4678721 : Blo 1385512 4678721 := bstep (se 2 (by rfl) ⟨1754520, by rfl⟩ : syracuseStep 4678721 = 3509041) B3509041
theorem B1385547 : Blo 1385512 1385547 := bstep (se 1 (by rfl) ⟨1039160, by rfl⟩ : syracuseStep 1385547 = 2078321) B2078321
theorem B1385559 : Blo 1385512 1385559 := bstep (se 1 (by rfl) ⟨1039169, by rfl⟩ : syracuseStep 1385559 = 2078339) B2078339
theorem B1975385 : Blo 1385512 1975385 := bstep (se 2 (by rfl) ⟨740769, by rfl⟩ : syracuseStep 1975385 = 1481539) B1481539
theorem B1385579 : Blo 1385512 1385579 := bstep (se 1 (by rfl) ⟨1039184, by rfl⟩ : syracuseStep 1385579 = 2078369) B2078369
theorem B1385591 : Blo 1385512 1385591 := bstep (se 1 (by rfl) ⟨1039193, by rfl⟩ : syracuseStep 1385591 = 2078387) B2078387
theorem B1385611 : Blo 1385512 1385611 := bstep (se 1 (by rfl) ⟨1039208, by rfl⟩ : syracuseStep 1385611 = 2078417) B2078417
theorem B1385623 : Blo 1385512 1385623 := bstep (se 1 (by rfl) ⟨1039217, by rfl⟩ : syracuseStep 1385623 = 2078435) B2078435
theorem B2630809 : Blo 1385512 2630809 := bstep (se 2 (by rfl) ⟨986553, by rfl⟩ : syracuseStep 2630809 = 1973107) B1973107
theorem B1385643 : Blo 1385512 1385643 := bstep (se 1 (by rfl) ⟨1039232, by rfl⟩ : syracuseStep 1385643 = 2078465) B2078465
theorem B1385655 : Blo 1385512 1385655 := bstep (se 1 (by rfl) ⟨1039241, by rfl⟩ : syracuseStep 1385655 = 2078483) B2078483
theorem B1385675 : Blo 1385512 1385675 := bstep (se 1 (by rfl) ⟨1039256, by rfl⟩ : syracuseStep 1385675 = 2078513) B2078513
theorem B1385687 : Blo 1385512 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B2221271 : Blo 1385512 2221271 := bstep (se 1 (by rfl) ⟨1665953, by rfl⟩ : syracuseStep 2221271 = 3331907) B3331907
theorem B1385707 : Blo 1385512 1385707 := bstep (se 1 (by rfl) ⟨1039280, by rfl⟩ : syracuseStep 1385707 = 2078561) B2078561
theorem B1385719 : Blo 1385512 1385719 := bstep (se 1 (by rfl) ⟨1039289, by rfl⟩ : syracuseStep 1385719 = 2078579) B2078579
theorem B1385739 : Blo 1385512 1385739 := bstep (se 1 (by rfl) ⟨1039304, by rfl⟩ : syracuseStep 1385739 = 2078609) B2078609
theorem B1385751 : Blo 1385512 1385751 := bstep (se 1 (by rfl) ⟨1039313, by rfl⟩ : syracuseStep 1385751 = 2078627) B2078627
theorem B1385771 : Blo 1385512 1385771 := bstep (se 1 (by rfl) ⟨1039328, by rfl⟩ : syracuseStep 1385771 = 2078657) B2078657
theorem B1385783 : Blo 1385512 1385783 := bstep (se 1 (by rfl) ⟨1039337, by rfl⟩ : syracuseStep 1385783 = 2078675) B2078675
theorem B7021889 : Blo 1385512 7021889 := bstep (se 2 (by rfl) ⟨2633208, by rfl⟩ : syracuseStep 7021889 = 5266417) B5266417
theorem B1385803 : Blo 1385512 1385803 := bstep (se 1 (by rfl) ⟨1039352, by rfl⟩ : syracuseStep 1385803 = 2078705) B2078705
theorem B9487691 : Blo 1385512 9487691 := bstep (se 1 (by rfl) ⟨7115768, by rfl⟩ : syracuseStep 9487691 = 14231537) B14231537
theorem B1385815 : Blo 1385512 1385815 := bstep (se 1 (by rfl) ⟨1039361, by rfl⟩ : syracuseStep 1385815 = 2078723) B2078723
theorem B1754455 : Blo 1385512 1754455 := bstep (se 1 (by rfl) ⟨1315841, by rfl⟩ : syracuseStep 1754455 = 2631683) B2631683
theorem B1385835 : Blo 1385512 1385835 := bstep (se 1 (by rfl) ⟨1039376, by rfl⟩ : syracuseStep 1385835 = 2078753) B2078753
theorem B16229749 : Blo 1385512 16229749 := bstep (se 5 (by rfl) ⟨760769, by rfl⟩ : syracuseStep 16229749 = 1521539) B1521539
theorem B1385847 : Blo 1385512 1385847 := bstep (se 1 (by rfl) ⟨1039385, by rfl⟩ : syracuseStep 1385847 = 2078771) B2078771
theorem B6751619 : Blo 1385512 6751619 := bstep (se 1 (by rfl) ⟨5063714, by rfl⟩ : syracuseStep 6751619 = 10127429) B10127429
theorem B1385867 : Blo 1385512 1385867 := bstep (se 1 (by rfl) ⟨1039400, by rfl⟩ : syracuseStep 1385867 = 2078801) B2078801
theorem B1385879 : Blo 1385512 1385879 := bstep (se 1 (by rfl) ⟨1039409, by rfl⟩ : syracuseStep 1385879 = 2078819) B2078819
theorem B1385899 : Blo 1385512 1385899 := bstep (se 1 (by rfl) ⟨1039424, by rfl⟩ : syracuseStep 1385899 = 2078849) B2078849
theorem B1385911 : Blo 1385512 1385911 := bstep (se 1 (by rfl) ⟨1039433, by rfl⟩ : syracuseStep 1385911 = 2078867) B2078867
theorem B1385931 : Blo 1385512 1385931 := bstep (se 1 (by rfl) ⟨1039448, by rfl⟩ : syracuseStep 1385931 = 2078897) B2078897
theorem B1385943 : Blo 1385512 1385943 := bstep (se 1 (by rfl) ⟨1039457, by rfl⟩ : syracuseStep 1385943 = 2078915) B2078915
theorem B10528217 : Blo 1385512 10528217 := bstep (se 2 (by rfl) ⟨3948081, by rfl⟩ : syracuseStep 10528217 = 7896163) B7896163
theorem B3950041 : Blo 1385512 3950041 := bstep (se 2 (by rfl) ⟨1481265, by rfl⟩ : syracuseStep 3950041 = 2962531) B2962531
theorem B1385963 : Blo 1385512 1385963 := bstep (se 1 (by rfl) ⟨1039472, by rfl⟩ : syracuseStep 1385963 = 2078945) B2078945
theorem B1385975 : Blo 1385512 1385975 := bstep (se 1 (by rfl) ⟨1039481, by rfl⟩ : syracuseStep 1385975 = 2078963) B2078963
theorem B1385995 : Blo 1385512 1385995 := bstep (se 1 (by rfl) ⟨1039496, by rfl⟩ : syracuseStep 1385995 = 2078993) B2078993
theorem B1386007 : Blo 1385512 1386007 := bstep (se 1 (by rfl) ⟨1039505, by rfl⟩ : syracuseStep 1386007 = 2079011) B2079011
theorem B1386027 : Blo 1385512 1386027 := bstep (se 1 (by rfl) ⟨1039520, by rfl⟩ : syracuseStep 1386027 = 2079041) B2079041
theorem B1386039 : Blo 1385512 1386039 := bstep (se 1 (by rfl) ⟨1039529, by rfl⟩ : syracuseStep 1386039 = 2079059) B2079059
theorem B3745345 : Blo 1385512 3745345 := bstep (se 2 (by rfl) ⟨1404504, by rfl⟩ : syracuseStep 3745345 = 2809009) B2809009
theorem B1386059 : Blo 1385512 1386059 := bstep (se 1 (by rfl) ⟨1039544, by rfl⟩ : syracuseStep 1386059 = 2079089) B2079089
theorem B2221643 : Blo 1385512 2221643 := bstep (se 1 (by rfl) ⟨1666232, by rfl⟩ : syracuseStep 2221643 = 3332465) B3332465
theorem B1386071 : Blo 1385512 1386071 := bstep (se 1 (by rfl) ⟨1039553, by rfl⟩ : syracuseStep 1386071 = 2079107) B2079107
theorem B5260889 : Blo 1385512 5260889 := bstep (se 2 (by rfl) ⟨1972833, by rfl⟩ : syracuseStep 5260889 = 3945667) B3945667
theorem B4679261 : Blo 1385512 4679261 := bstep (se 3 (by rfl) ⟨877361, by rfl⟩ : syracuseStep 4679261 = 1754723) B1754723
theorem B1386091 : Blo 1385512 1386091 := bstep (se 1 (by rfl) ⟨1039568, by rfl⟩ : syracuseStep 1386091 = 2079137) B2079137
theorem B1386103 : Blo 1385512 1386103 := bstep (se 1 (by rfl) ⟨1039577, by rfl⟩ : syracuseStep 1386103 = 2079155) B2079155
theorem B1386123 : Blo 1385512 1386123 := bstep (se 1 (by rfl) ⟨1039592, by rfl⟩ : syracuseStep 1386123 = 2079185) B2079185
theorem B1386135 : Blo 1385512 1386135 := bstep (se 1 (by rfl) ⟨1039601, by rfl⟩ : syracuseStep 1386135 = 2079203) B2079203
theorem B1386155 : Blo 1385512 1386155 := bstep (se 1 (by rfl) ⟨1039616, by rfl⟩ : syracuseStep 1386155 = 2079233) B2079233
theorem B1386167 : Blo 1385512 1386167 := bstep (se 1 (by rfl) ⟨1039625, by rfl⟩ : syracuseStep 1386167 = 2079251) B2079251
theorem B1386187 : Blo 1385512 1386187 := bstep (se 1 (by rfl) ⟨1039640, by rfl⟩ : syracuseStep 1386187 = 2079281) B2079281
theorem B1386199 : Blo 1385512 1386199 := bstep (se 1 (by rfl) ⟨1039649, by rfl⟩ : syracuseStep 1386199 = 2079299) B2079299
theorem B1386219 : Blo 1385512 1386219 := bstep (se 1 (by rfl) ⟨1039664, by rfl⟩ : syracuseStep 1386219 = 2079329) B2079329
theorem B1386231 : Blo 1385512 1386231 := bstep (se 1 (by rfl) ⟨1039673, by rfl⟩ : syracuseStep 1386231 = 2079347) B2079347
theorem B1386251 : Blo 1385512 1386251 := bstep (se 1 (by rfl) ⟨1039688, by rfl⟩ : syracuseStep 1386251 = 2079377) B2079377
theorem B7898897 : Blo 1385512 7898897 := bstep (se 2 (by rfl) ⟨2962086, by rfl⟩ : syracuseStep 7898897 = 5924173) B5924173
theorem B1386263 : Blo 1385512 1386263 := bstep (se 1 (by rfl) ⟨1039697, by rfl⟩ : syracuseStep 1386263 = 2079395) B2079395
theorem B1386283 : Blo 1385512 1386283 := bstep (se 1 (by rfl) ⟨1039712, by rfl⟩ : syracuseStep 1386283 = 2079425) B2079425
theorem B6407981 : Blo 1385512 6407981 := bstep (se 3 (by rfl) ⟨1201496, by rfl⟩ : syracuseStep 6407981 = 2402993) B2402993
theorem B3508019 : Blo 1385512 3508019 := bstep (se 1 (by rfl) ⟨2631014, by rfl⟩ : syracuseStep 3508019 = 5262029) B5262029
theorem B1386295 : Blo 1385512 1386295 := bstep (se 1 (by rfl) ⟨1039721, by rfl⟩ : syracuseStep 1386295 = 2079443) B2079443
theorem B1386315 : Blo 1385512 1386315 := bstep (se 1 (by rfl) ⟨1039736, by rfl⟩ : syracuseStep 1386315 = 2079473) B2079473
theorem B1386327 : Blo 1385512 1386327 := bstep (se 1 (by rfl) ⟨1039745, by rfl⟩ : syracuseStep 1386327 = 2079491) B2079491
theorem B1386347 : Blo 1385512 1386347 := bstep (se 1 (by rfl) ⟨1039760, by rfl⟩ : syracuseStep 1386347 = 2079521) B2079521
theorem B1386359 : Blo 1385512 1386359 := bstep (se 1 (by rfl) ⟨1039769, by rfl⟩ : syracuseStep 1386359 = 2079539) B2079539
theorem B7014275 : Blo 1385512 7014275 := bstep (se 1 (by rfl) ⟨5260706, by rfl⟩ : syracuseStep 7014275 = 10521413) B10521413
theorem B1386379 : Blo 1385512 1386379 := bstep (se 1 (by rfl) ⟨1039784, by rfl⟩ : syracuseStep 1386379 = 2079569) B2079569
theorem B1386391 : Blo 1385512 1386391 := bstep (se 1 (by rfl) ⟨1039793, by rfl⟩ : syracuseStep 1386391 = 2079587) B2079587
theorem B2221975 : Blo 1385512 2221975 := bstep (se 1 (by rfl) ⟨1666481, by rfl⟩ : syracuseStep 2221975 = 3332963) B3332963
theorem B1386411 : Blo 1385512 1386411 := bstep (se 1 (by rfl) ⟨1039808, by rfl⟩ : syracuseStep 1386411 = 2079617) B2079617
theorem B1386423 : Blo 1385512 1386423 := bstep (se 1 (by rfl) ⟨1039817, by rfl⟩ : syracuseStep 1386423 = 2079635) B2079635
theorem B1386443 : Blo 1385512 1386443 := bstep (se 1 (by rfl) ⟨1039832, by rfl⟩ : syracuseStep 1386443 = 2079665) B2079665
theorem B12167117 : Blo 1385512 12167117 := bstep (se 3 (by rfl) ⟨2281334, by rfl⟩ : syracuseStep 12167117 = 4562669) B4562669
theorem B1386455 : Blo 1385512 1386455 := bstep (se 1 (by rfl) ⟨1039841, by rfl⟩ : syracuseStep 1386455 = 2079683) B2079683
theorem B1386475 : Blo 1385512 1386475 := bstep (se 1 (by rfl) ⟨1039856, by rfl⟩ : syracuseStep 1386475 = 2079713) B2079713
theorem B1386487 : Blo 1385512 1386487 := bstep (se 1 (by rfl) ⟨1039865, by rfl⟩ : syracuseStep 1386487 = 2079731) B2079731
theorem B1386507 : Blo 1385512 1386507 := bstep (se 1 (by rfl) ⟨1039880, by rfl⟩ : syracuseStep 1386507 = 2079761) B2079761
theorem B1386519 : Blo 1385512 1386519 := bstep (se 1 (by rfl) ⟨1039889, by rfl⟩ : syracuseStep 1386519 = 2079779) B2079779
theorem B1386539 : Blo 1385512 1386539 := bstep (se 1 (by rfl) ⟨1039904, by rfl⟩ : syracuseStep 1386539 = 2079809) B2079809
theorem B1386551 : Blo 1385512 1386551 := bstep (se 1 (by rfl) ⟨1039913, by rfl⟩ : syracuseStep 1386551 = 2079827) B2079827
theorem B3950657 : Blo 1385512 3950657 := bstep (se 2 (by rfl) ⟨1481496, by rfl⟩ : syracuseStep 3950657 = 2962993) B2962993
theorem B1386571 : Blo 1385512 1386571 := bstep (se 1 (by rfl) ⟨1039928, by rfl⟩ : syracuseStep 1386571 = 2079857) B2079857
theorem B1386583 : Blo 1385512 1386583 := bstep (se 1 (by rfl) ⟨1039937, by rfl⟩ : syracuseStep 1386583 = 2079875) B2079875
theorem B1386603 : Blo 1385512 1386603 := bstep (se 1 (by rfl) ⟨1039952, by rfl⟩ : syracuseStep 1386603 = 2079905) B2079905
theorem B1386615 : Blo 1385512 1386615 := bstep (se 1 (by rfl) ⟨1039961, by rfl⟩ : syracuseStep 1386615 = 2079923) B2079923
theorem B1386635 : Blo 1385512 1386635 := bstep (se 1 (by rfl) ⟨1039976, by rfl⟩ : syracuseStep 1386635 = 2079953) B2079953
theorem B1386647 : Blo 1385512 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B1386667 : Blo 1385512 1386667 := bstep (se 1 (by rfl) ⟨1040000, by rfl⟩ : syracuseStep 1386667 = 2080001) B2080001
theorem B1386679 : Blo 1385512 1386679 := bstep (se 1 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 1386679 = 2080019) B2080019
theorem B1386699 : Blo 1385512 1386699 := bstep (se 1 (by rfl) ⟨1040024, by rfl⟩ : syracuseStep 1386699 = 2080049) B2080049
theorem B1386711 : Blo 1385512 1386711 := bstep (se 1 (by rfl) ⟨1040033, by rfl⟩ : syracuseStep 1386711 = 2080067) B2080067
theorem B7899353 : Blo 1385512 7899353 := bstep (se 2 (by rfl) ⟨2962257, by rfl⟩ : syracuseStep 7899353 = 5924515) B5924515
theorem B1386731 : Blo 1385512 1386731 := bstep (se 1 (by rfl) ⟨1040048, by rfl⟩ : syracuseStep 1386731 = 2080097) B2080097
theorem B1386743 : Blo 1385512 1386743 := bstep (se 1 (by rfl) ⟨1040057, by rfl⟩ : syracuseStep 1386743 = 2080115) B2080115
theorem B1558795 : Blo 1385512 1558795 := bstep (se 1 (by rfl) ⟨1169096, by rfl⟩ : syracuseStep 1558795 = 2338193) B2338193
theorem B1386763 : Blo 1385512 1386763 := bstep (se 1 (by rfl) ⟨1040072, by rfl⟩ : syracuseStep 1386763 = 2080145) B2080145
theorem B1386775 : Blo 1385512 1386775 := bstep (se 1 (by rfl) ⟨1040081, by rfl⟩ : syracuseStep 1386775 = 2080163) B2080163
theorem B1386795 : Blo 1385512 1386795 := bstep (se 1 (by rfl) ⟨1040096, by rfl⟩ : syracuseStep 1386795 = 2080193) B2080193
theorem B4999475 : Blo 1385512 4999475 := bstep (se 1 (by rfl) ⟨3749606, by rfl⟩ : syracuseStep 4999475 = 7499213) B7499213
theorem B1386807 : Blo 1385512 1386807 := bstep (se 1 (by rfl) ⟨1040105, by rfl⟩ : syracuseStep 1386807 = 2080211) B2080211
theorem B3508555 : Blo 1385512 3508555 := bstep (se 1 (by rfl) ⟨2631416, by rfl⟩ : syracuseStep 3508555 = 5262833) B5262833
theorem B1386827 : Blo 1385512 1386827 := bstep (se 1 (by rfl) ⟨1040120, by rfl⟩ : syracuseStep 1386827 = 2080241) B2080241
theorem B1386839 : Blo 1385512 1386839 := bstep (se 1 (by rfl) ⟨1040129, by rfl⟩ : syracuseStep 1386839 = 2080259) B2080259
theorem B1386859 : Blo 1385512 1386859 := bstep (se 1 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 1386859 = 2080289) B2080289
theorem B1558903 : Blo 1385512 1558903 := bstep (se 1 (by rfl) ⟨1169177, by rfl⟩ : syracuseStep 1558903 = 2338355) B2338355
theorem B1386871 : Blo 1385512 1386871 := bstep (se 1 (by rfl) ⟨1040153, by rfl⟩ : syracuseStep 1386871 = 2080307) B2080307
theorem B5925251 : Blo 1385512 5925251 := bstep (se 1 (by rfl) ⟨4443938, by rfl⟩ : syracuseStep 5925251 = 8887877) B8887877
theorem B1386891 : Blo 1385512 1386891 := bstep (se 1 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 1386891 = 2080337) B2080337
theorem B1386903 : Blo 1385512 1386903 := bstep (se 1 (by rfl) ⟨1040177, by rfl⟩ : syracuseStep 1386903 = 2080355) B2080355
theorem B1386923 : Blo 1385512 1386923 := bstep (se 1 (by rfl) ⟨1040192, by rfl⟩ : syracuseStep 1386923 = 2080385) B2080385
theorem B2632115 : Blo 1385512 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B1386935 : Blo 1385512 1386935 := bstep (se 1 (by rfl) ⟨1040201, by rfl⟩ : syracuseStep 1386935 = 2080403) B2080403
theorem B1386955 : Blo 1385512 1386955 := bstep (se 1 (by rfl) ⟨1040216, by rfl⟩ : syracuseStep 1386955 = 2080433) B2080433
theorem B2959831 : Blo 1385512 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B1386967 : Blo 1385512 1386967 := bstep (se 1 (by rfl) ⟨1040225, by rfl⟩ : syracuseStep 1386967 = 2080451) B2080451
theorem B3508697 : Blo 1385512 3508697 := bstep (se 2 (by rfl) ⟨1315761, by rfl⟩ : syracuseStep 3508697 = 2631523) B2631523
theorem B1386987 : Blo 1385512 1386987 := bstep (se 1 (by rfl) ⟨1040240, by rfl⟩ : syracuseStep 1386987 = 2080481) B2080481
theorem B1386999 : Blo 1385512 1386999 := bstep (se 1 (by rfl) ⟨1040249, by rfl⟩ : syracuseStep 1386999 = 2080499) B2080499
theorem B1387019 : Blo 1385512 1387019 := bstep (se 1 (by rfl) ⟨1040264, by rfl⟩ : syracuseStep 1387019 = 2080529) B2080529
theorem B1665559 : Blo 1385512 1665559 := bstep (se 1 (by rfl) ⟨1249169, by rfl⟩ : syracuseStep 1665559 = 2498339) B2498339
theorem B1387031 : Blo 1385512 1387031 := bstep (se 1 (by rfl) ⟨1040273, by rfl⟩ : syracuseStep 1387031 = 2080547) B2080547
theorem B1559083 : Blo 1385512 1559083 := bstep (se 1 (by rfl) ⟨1169312, by rfl⟩ : syracuseStep 1559083 = 2338625) B2338625
theorem B1387051 : Blo 1385512 1387051 := bstep (se 1 (by rfl) ⟨1040288, by rfl⟩ : syracuseStep 1387051 = 2080577) B2080577
theorem B1387063 : Blo 1385512 1387063 := bstep (se 1 (by rfl) ⟨1040297, by rfl⟩ : syracuseStep 1387063 = 2080595) B2080595
theorem B2632267 : Blo 1385512 2632267 := bstep (se 1 (by rfl) ⟨1974200, by rfl⟩ : syracuseStep 2632267 = 3948401) B3948401
theorem B1387083 : Blo 1385512 1387083 := bstep (se 1 (by rfl) ⟨1040312, by rfl⟩ : syracuseStep 1387083 = 2080625) B2080625
theorem B1387095 : Blo 1385512 1387095 := bstep (se 1 (by rfl) ⟨1040321, by rfl⟩ : syracuseStep 1387095 = 2080643) B2080643
theorem B1387115 : Blo 1385512 1387115 := bstep (se 1 (by rfl) ⟨1040336, by rfl⟩ : syracuseStep 1387115 = 2080673) B2080673
theorem B1387127 : Blo 1385512 1387127 := bstep (se 1 (by rfl) ⟨1040345, by rfl⟩ : syracuseStep 1387127 = 2080691) B2080691
theorem B1387147 : Blo 1385512 1387147 := bstep (se 1 (by rfl) ⟨1040360, by rfl⟩ : syracuseStep 1387147 = 2080721) B2080721
theorem B7891607 : Blo 1385512 7891607 := bstep (se 1 (by rfl) ⟨5918705, by rfl⟩ : syracuseStep 7891607 = 11837411) B11837411
theorem B1559191 : Blo 1385512 1559191 := bstep (se 1 (by rfl) ⟨1169393, by rfl⟩ : syracuseStep 1559191 = 2338787) B2338787
theorem B1387159 : Blo 1385512 1387159 := bstep (se 1 (by rfl) ⟨1040369, by rfl⟩ : syracuseStep 1387159 = 2080739) B2080739
theorem B1387179 : Blo 1385512 1387179 := bstep (se 1 (by rfl) ⟨1040384, by rfl⟩ : syracuseStep 1387179 = 2080769) B2080769
theorem B1387191 : Blo 1385512 1387191 := bstep (se 1 (by rfl) ⟨1040393, by rfl⟩ : syracuseStep 1387191 = 2080787) B2080787
theorem B4680395 : Blo 1385512 4680395 := bstep (se 1 (by rfl) ⟨3510296, by rfl⟩ : syracuseStep 4680395 = 7020593) B7020593
theorem B1387211 : Blo 1385512 1387211 := bstep (se 1 (by rfl) ⟨1040408, by rfl⟩ : syracuseStep 1387211 = 2080817) B2080817
theorem B1387223 : Blo 1385512 1387223 := bstep (se 1 (by rfl) ⟨1040417, by rfl⟩ : syracuseStep 1387223 = 2080835) B2080835
theorem B1387243 : Blo 1385512 1387243 := bstep (se 1 (by rfl) ⟨1040432, by rfl⟩ : syracuseStep 1387243 = 2080865) B2080865
theorem B1387255 : Blo 1385512 1387255 := bstep (se 1 (by rfl) ⟨1040441, by rfl⟩ : syracuseStep 1387255 = 2080883) B2080883
theorem B1387275 : Blo 1385512 1387275 := bstep (se 1 (by rfl) ⟨1040456, by rfl⟩ : syracuseStep 1387275 = 2080913) B2080913
theorem B1387287 : Blo 1385512 1387287 := bstep (se 1 (by rfl) ⟨1040465, by rfl⟩ : syracuseStep 1387287 = 2080931) B2080931
theorem B1387307 : Blo 1385512 1387307 := bstep (se 1 (by rfl) ⟨1040480, by rfl⟩ : syracuseStep 1387307 = 2080961) B2080961
theorem B1387319 : Blo 1385512 1387319 := bstep (se 1 (by rfl) ⟨1040489, by rfl⟩ : syracuseStep 1387319 = 2080979) B2080979
theorem B1559371 : Blo 1385512 1559371 := bstep (se 1 (by rfl) ⟨1169528, by rfl⟩ : syracuseStep 1559371 = 2339057) B2339057
theorem B1387339 : Blo 1385512 1387339 := bstep (se 1 (by rfl) ⟨1040504, by rfl⟩ : syracuseStep 1387339 = 2081009) B2081009
theorem B1387351 : Blo 1385512 1387351 := bstep (se 1 (by rfl) ⟨1040513, by rfl⟩ : syracuseStep 1387351 = 2081027) B2081027
theorem B6663005 : Blo 1385512 6663005 := bstep (se 3 (by rfl) ⟨1249313, by rfl⟩ : syracuseStep 6663005 = 2498627) B2498627
theorem B1387371 : Blo 1385512 1387371 := bstep (se 1 (by rfl) ⟨1040528, by rfl⟩ : syracuseStep 1387371 = 2081057) B2081057
theorem B1387383 : Blo 1385512 1387383 := bstep (se 1 (by rfl) ⟨1040537, by rfl⟩ : syracuseStep 1387383 = 2081075) B2081075
theorem B1387403 : Blo 1385512 1387403 := bstep (se 1 (by rfl) ⟨1040552, by rfl⟩ : syracuseStep 1387403 = 2081105) B2081105
theorem B1387415 : Blo 1385512 1387415 := bstep (se 1 (by rfl) ⟨1040561, by rfl⟩ : syracuseStep 1387415 = 2081123) B2081123
theorem B2632601 : Blo 1385512 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B1387435 : Blo 1385512 1387435 := bstep (se 1 (by rfl) ⟨1040576, by rfl⟩ : syracuseStep 1387435 = 2081153) B2081153
theorem B1559479 : Blo 1385512 1559479 := bstep (se 1 (by rfl) ⟨1169609, by rfl⟩ : syracuseStep 1559479 = 2339219) B2339219
theorem B1387447 : Blo 1385512 1387447 := bstep (se 1 (by rfl) ⟨1040585, by rfl⟩ : syracuseStep 1387447 = 2081171) B2081171
theorem B1387467 : Blo 1385512 1387467 := bstep (se 1 (by rfl) ⟨1040600, by rfl⟩ : syracuseStep 1387467 = 2081201) B2081201
theorem B1387479 : Blo 1385512 1387479 := bstep (se 1 (by rfl) ⟨1040609, by rfl⟩ : syracuseStep 1387479 = 2081219) B2081219
theorem B4680665 : Blo 1385512 4680665 := bstep (se 2 (by rfl) ⟨1755249, by rfl⟩ : syracuseStep 4680665 = 3510499) B3510499
theorem B9997273 : Blo 1385512 9997273 := bstep (se 2 (by rfl) ⟨3748977, by rfl⟩ : syracuseStep 9997273 = 7497955) B7497955
theorem B1387499 : Blo 1385512 1387499 := bstep (se 1 (by rfl) ⟨1040624, by rfl⟩ : syracuseStep 1387499 = 2081249) B2081249
theorem B1387511 : Blo 1385512 1387511 := bstep (se 1 (by rfl) ⟨1040633, by rfl⟩ : syracuseStep 1387511 = 2081267) B2081267
theorem B6843457 : Blo 1385512 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B1559659 : Blo 1385512 1559659 := bstep (se 1 (by rfl) ⟨1169744, by rfl⟩ : syracuseStep 1559659 = 2339489) B2339489
theorem B5262515 : Blo 1385512 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B5262529 : Blo 1385512 5262529 := bstep (se 2 (by rfl) ⟨1973448, by rfl⟩ : syracuseStep 5262529 = 3946897) B3946897
theorem B1559767 : Blo 1385512 1559767 := bstep (se 1 (by rfl) ⟨1169825, by rfl⟩ : syracuseStep 1559767 = 2339651) B2339651
theorem B7023833 : Blo 1385512 7023833 := bstep (se 2 (by rfl) ⟨2633937, by rfl⟩ : syracuseStep 7023833 = 5267875) B5267875
theorem B3509527 : Blo 1385512 3509527 := bstep (se 1 (by rfl) ⟨2632145, by rfl⟩ : syracuseStep 3509527 = 5264291) B5264291
theorem B1559947 : Blo 1385512 1559947 := bstep (se 1 (by rfl) ⟨1169960, by rfl⟩ : syracuseStep 1559947 = 2339921) B2339921
theorem B192081293 : Blo 1385512 192081293 := bstep (se 3 (by rfl) ⟨36015242, by rfl⟩ : syracuseStep 192081293 = 72030485) B72030485
theorem B1560055 : Blo 1385512 1560055 := bstep (se 1 (by rfl) ⟨1170041, by rfl⟩ : syracuseStep 1560055 = 2340083) B2340083
theorem B2633239 : Blo 1385512 2633239 := bstep (se 1 (by rfl) ⟨1974929, by rfl⟩ : syracuseStep 2633239 = 3949859) B3949859
theorem B3747379 : Blo 1385512 3747379 := bstep (se 1 (by rfl) ⟨2810534, by rfl⟩ : syracuseStep 3747379 = 5621069) B5621069
theorem B3747421 : Blo 1385512 3747421 := bstep (se 3 (by rfl) ⟨702641, by rfl⟩ : syracuseStep 3747421 = 1405283) B1405283
theorem B2961011 : Blo 1385512 2961011 := bstep (se 1 (by rfl) ⟨2220758, by rfl⟩ : syracuseStep 2961011 = 4441517) B4441517
theorem B4681367 : Blo 1385512 4681367 := bstep (se 1 (by rfl) ⟨3511025, by rfl⟩ : syracuseStep 4681367 = 7022051) B7022051
theorem B1560235 : Blo 1385512 1560235 := bstep (se 1 (by rfl) ⟨1170176, by rfl⟩ : syracuseStep 1560235 = 2340353) B2340353
theorem B3509963 : Blo 1385512 3509963 := bstep (se 1 (by rfl) ⟨2632472, by rfl⟩ : syracuseStep 3509963 = 5264945) B5264945
theorem B1404631 : Blo 1385512 1404631 := bstep (se 1 (by rfl) ⟨1053473, by rfl⟩ : syracuseStep 1404631 = 2106947) B2106947
theorem B3329753 : Blo 1385512 3329753 := bstep (se 2 (by rfl) ⟨1248657, by rfl⟩ : syracuseStep 3329753 = 2497315) B2497315
theorem B5918467 : Blo 1385512 5918467 := bstep (se 1 (by rfl) ⟨4438850, by rfl⟩ : syracuseStep 5918467 = 8877701) B8877701
theorem B2338571 : Blo 1385512 2338571 := bstep (se 1 (by rfl) ⟨1753928, by rfl⟩ : syracuseStep 2338571 = 3507857) B3507857
theorem B10522385 : Blo 1385512 10522385 := bstep (se 2 (by rfl) ⟨3945894, by rfl⟩ : syracuseStep 10522385 = 7891789) B7891789
theorem B1560343 : Blo 1385512 1560343 := bstep (se 1 (by rfl) ⟨1170257, by rfl⟩ : syracuseStep 1560343 = 2340515) B2340515
theorem B5623597 : Blo 1385512 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B6328153 : Blo 1385512 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B2338699 : Blo 1385512 2338699 := bstep (se 1 (by rfl) ⟨1754024, by rfl⟩ : syracuseStep 2338699 = 3508049) B3508049
theorem B1560523 : Blo 1385512 1560523 := bstep (se 1 (by rfl) ⟨1170392, by rfl⟩ : syracuseStep 1560523 = 2340785) B2340785
theorem B2338841 : Blo 1385512 2338841 := bstep (se 2 (by rfl) ⟨877065, by rfl⟩ : syracuseStep 2338841 = 1754131) B1754131
theorem B1560631 : Blo 1385512 1560631 := bstep (se 1 (by rfl) ⟨1170473, by rfl⟩ : syracuseStep 1560631 = 2340947) B2340947
theorem B3510337 : Blo 1385512 3510337 := bstep (se 2 (by rfl) ⟨1316376, by rfl⟩ : syracuseStep 3510337 = 2632753) B2632753
theorem B2666611 : Blo 1385512 2666611 := bstep (se 1 (by rfl) ⟨1999958, by rfl⟩ : syracuseStep 2666611 = 3999917) B3999917
theorem B88871053 : Blo 1385512 88871053 := bstep (se 3 (by rfl) ⟨16663322, by rfl⟩ : syracuseStep 88871053 = 33326645) B33326645
theorem B2338969 : Blo 1385512 2338969 := bstep (se 2 (by rfl) ⟨877113, by rfl⟩ : syracuseStep 2338969 = 1754227) B1754227
theorem B4681907 : Blo 1385512 4681907 := bstep (se 1 (by rfl) ⟨3511430, by rfl⟩ : syracuseStep 4681907 = 7022861) B7022861
theorem B1560811 : Blo 1385512 1560811 := bstep (se 1 (by rfl) ⟨1170608, by rfl⟩ : syracuseStep 1560811 = 2341217) B2341217
theorem B9998657 : Blo 1385512 9998657 := bstep (se 2 (by rfl) ⟨3749496, by rfl⟩ : syracuseStep 9998657 = 7498993) B7498993
theorem B2634059 : Blo 1385512 2634059 := bstep (se 1 (by rfl) ⟨1975544, by rfl⟩ : syracuseStep 2634059 = 3951089) B3951089
theorem B1560919 : Blo 1385512 1560919 := bstep (se 1 (by rfl) ⟨1170689, by rfl⟩ : syracuseStep 1560919 = 2341379) B2341379
theorem B2568577 : Blo 1385512 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B3117491 : Blo 1385512 3117491 := bstep (se 1 (by rfl) ⟨2338118, by rfl⟩ : syracuseStep 3117491 = 4676237) B4676237
theorem B4682177 : Blo 1385512 4682177 := bstep (se 2 (by rfl) ⟨1755816, by rfl⟩ : syracuseStep 4682177 = 3511633) B3511633
theorem B3117527 : Blo 1385512 3117527 := bstep (se 1 (by rfl) ⟨2338145, by rfl⟩ : syracuseStep 3117527 = 4676291) B4676291
theorem B7893521 : Blo 1385512 7893521 := bstep (se 2 (by rfl) ⟨2960070, by rfl⟩ : syracuseStep 7893521 = 5920141) B5920141
theorem B3117707 : Blo 1385512 3117707 := bstep (se 1 (by rfl) ⟨2338280, by rfl⟩ : syracuseStep 3117707 = 4676561) B4676561
theorem B7492247 : Blo 1385512 7492247 := bstep (se 1 (by rfl) ⟨5619185, by rfl⟩ : syracuseStep 7492247 = 11238371) B11238371
theorem B3510935 : Blo 1385512 3510935 := bstep (se 1 (by rfl) ⟨2633201, by rfl⟩ : syracuseStep 3510935 = 5266403) B5266403
theorem B3117761 : Blo 1385512 3117761 := bstep (se 2 (by rfl) ⟨1169160, by rfl⟩ : syracuseStep 3117761 = 2338321) B2338321
theorem B5919425 : Blo 1385512 5919425 := bstep (se 2 (by rfl) ⟨2219784, by rfl⟩ : syracuseStep 5919425 = 4439569) B4439569
theorem B2339543 : Blo 1385512 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B3003161 : Blo 1385512 3003161 := bstep (se 2 (by rfl) ⟨1126185, by rfl⟩ : syracuseStep 3003161 = 2252371) B2252371
theorem B10531619 : Blo 1385512 10531619 := bstep (se 1 (by rfl) ⟨7898714, by rfl⟩ : syracuseStep 10531619 = 15797429) B15797429
theorem B2962241 : Blo 1385512 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B2339671 : Blo 1385512 2339671 := bstep (se 1 (by rfl) ⟨1754753, by rfl⟩ : syracuseStep 2339671 = 3509507) B3509507
theorem B3117977 : Blo 1385512 3117977 := bstep (se 2 (by rfl) ⟨1169241, by rfl⟩ : syracuseStep 3117977 = 2338483) B2338483
theorem B12014513 : Blo 1385512 12014513 := bstep (se 2 (by rfl) ⟨4505442, by rfl⟩ : syracuseStep 12014513 = 9010885) B9010885
theorem B4682717 : Blo 1385512 4682717 := bstep (se 3 (by rfl) ⟨878009, by rfl⟩ : syracuseStep 4682717 = 1756019) B1756019
theorem B3118067 : Blo 1385512 3118067 := bstep (se 1 (by rfl) ⟨2338550, by rfl⟩ : syracuseStep 3118067 = 4677101) B4677101
theorem B3118103 : Blo 1385512 3118103 := bstep (se 1 (by rfl) ⟨2338577, by rfl⟩ : syracuseStep 3118103 = 4677155) B4677155
theorem B5264459 : Blo 1385512 5264459 := bstep (se 1 (by rfl) ⟨3948344, by rfl⟩ : syracuseStep 5264459 = 7896689) B7896689
theorem B5264473 : Blo 1385512 5264473 := bstep (se 2 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 5264473 = 3948355) B3948355
theorem B6583427 : Blo 1385512 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B3118283 : Blo 1385512 3118283 := bstep (se 1 (by rfl) ⟨2338712, by rfl⟩ : syracuseStep 3118283 = 4677425) B4677425
theorem B1406167 : Blo 1385512 1406167 := bstep (se 1 (by rfl) ⟨1054625, by rfl⟩ : syracuseStep 1406167 = 2109251) B2109251
theorem B3118337 : Blo 1385512 3118337 := bstep (se 2 (by rfl) ⟨1169376, by rfl⟩ : syracuseStep 3118337 = 2338753) B2338753
theorem B3945793 : Blo 1385512 3945793 := bstep (se 2 (by rfl) ⟨1479672, by rfl⟩ : syracuseStep 3945793 = 2959345) B2959345
theorem B3511745 : Blo 1385512 3511745 := bstep (se 2 (by rfl) ⟨1316904, by rfl⟩ : syracuseStep 3511745 = 2633809) B2633809
theorem B2340299 : Blo 1385512 2340299 := bstep (se 1 (by rfl) ⟨1755224, by rfl⟩ : syracuseStep 2340299 = 3510449) B3510449
theorem B1480151 : Blo 1385512 1480151 := bstep (se 1 (by rfl) ⟨1110113, by rfl⟩ : syracuseStep 1480151 = 2220227) B2220227
theorem B3118553 : Blo 1385512 3118553 := bstep (se 2 (by rfl) ⟨1169457, by rfl⟩ : syracuseStep 3118553 = 2338915) B2338915
theorem B7018001 : Blo 1385512 7018001 := bstep (se 2 (by rfl) ⟨2631750, by rfl⟩ : syracuseStep 7018001 = 5263501) B5263501
theorem B3118643 : Blo 1385512 3118643 := bstep (se 1 (by rfl) ⟨2338982, by rfl⟩ : syracuseStep 3118643 = 4677965) B4677965
theorem B2340427 : Blo 1385512 2340427 := bstep (se 1 (by rfl) ⟨1755320, by rfl⟩ : syracuseStep 2340427 = 3510641) B3510641
theorem B3118679 : Blo 1385512 3118679 := bstep (se 1 (by rfl) ⟨2339009, by rfl⟩ : syracuseStep 3118679 = 4678019) B4678019
theorem B2078297 : Blo 1385512 2078297 := bstep (se 2 (by rfl) ⟨779361, by rfl⟩ : syracuseStep 2078297 = 1558723) B1558723
theorem B9483907 : Blo 1385512 9483907 := bstep (se 1 (by rfl) ⟨7112930, by rfl⟩ : syracuseStep 9483907 = 14225861) B14225861
theorem B7018163 : Blo 1385512 7018163 := bstep (se 1 (by rfl) ⟨5263622, by rfl⟩ : syracuseStep 7018163 = 10527245) B10527245
theorem B2078411 : Blo 1385512 2078411 := bstep (se 1 (by rfl) ⟨1558808, by rfl⟩ : syracuseStep 2078411 = 3117617) B3117617
theorem B2078423 : Blo 1385512 2078423 := bstep (se 1 (by rfl) ⟨1558817, by rfl⟩ : syracuseStep 2078423 = 3117635) B3117635
theorem B2340569 : Blo 1385512 2340569 := bstep (se 2 (by rfl) ⟨877713, by rfl⟩ : syracuseStep 2340569 = 1755427) B1755427
theorem B3118859 : Blo 1385512 3118859 := bstep (se 1 (by rfl) ⟨2339144, by rfl⟩ : syracuseStep 3118859 = 4678289) B4678289
theorem B2078489 : Blo 1385512 2078489 := bstep (se 2 (by rfl) ⟨779433, by rfl⟩ : syracuseStep 2078489 = 1558867) B1558867
theorem B7116589 : Blo 1385512 7116589 := bstep (se 3 (by rfl) ⟨1334360, by rfl⟩ : syracuseStep 7116589 = 2668721) B2668721
theorem B4216627 : Blo 1385512 4216627 := bstep (se 1 (by rfl) ⟨3162470, by rfl⟩ : syracuseStep 4216627 = 6324941) B6324941
theorem B3118913 : Blo 1385512 3118913 := bstep (se 2 (by rfl) ⟨1169592, by rfl⟩ : syracuseStep 3118913 = 2339185) B2339185
theorem B11851595 : Blo 1385512 11851595 := bstep (se 1 (by rfl) ⟨8888696, by rfl⟩ : syracuseStep 11851595 = 17777393) B17777393
theorem B2340697 : Blo 1385512 2340697 := bstep (se 2 (by rfl) ⟨877761, by rfl⟩ : syracuseStep 2340697 = 1755523) B1755523
theorem B2078603 : Blo 1385512 2078603 := bstep (se 1 (by rfl) ⟨1558952, by rfl⟩ : syracuseStep 2078603 = 3117905) B3117905
theorem B2078615 : Blo 1385512 2078615 := bstep (se 1 (by rfl) ⟨1558961, by rfl⟩ : syracuseStep 2078615 = 3117923) B3117923
theorem B2963351 : Blo 1385512 2963351 := bstep (se 1 (by rfl) ⟨2222513, by rfl⟩ : syracuseStep 2963351 = 4445027) B4445027
theorem B2078681 : Blo 1385512 2078681 := bstep (se 2 (by rfl) ⟨779505, by rfl⟩ : syracuseStep 2078681 = 1559011) B1559011
theorem B5265431 : Blo 1385512 5265431 := bstep (se 1 (by rfl) ⟨3949073, by rfl⟩ : syracuseStep 5265431 = 7898147) B7898147
theorem B3119129 : Blo 1385512 3119129 := bstep (se 2 (by rfl) ⟨1169673, by rfl⟩ : syracuseStep 3119129 = 2339347) B2339347
theorem B2078795 : Blo 1385512 2078795 := bstep (se 1 (by rfl) ⟨1559096, by rfl⟩ : syracuseStep 2078795 = 3118193) B3118193
theorem B2078807 : Blo 1385512 2078807 := bstep (se 1 (by rfl) ⟨1559105, by rfl⟩ : syracuseStep 2078807 = 3118211) B3118211
theorem B3119219 : Blo 1385512 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B5617795 : Blo 1385512 5617795 := bstep (se 1 (by rfl) ⟨4213346, by rfl⟩ : syracuseStep 5617795 = 8426693) B8426693
theorem B6666371 : Blo 1385512 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B3119255 : Blo 1385512 3119255 := bstep (se 1 (by rfl) ⟨2339441, by rfl⟩ : syracuseStep 3119255 = 4678883) B4678883
theorem B2078873 : Blo 1385512 2078873 := bstep (se 2 (by rfl) ⟨779577, by rfl⟩ : syracuseStep 2078873 = 1559155) B1559155
theorem B2078987 : Blo 1385512 2078987 := bstep (se 1 (by rfl) ⟨1559240, by rfl⟩ : syracuseStep 2078987 = 3118481) B3118481
theorem B2078999 : Blo 1385512 2078999 := bstep (se 1 (by rfl) ⟨1559249, by rfl⟩ : syracuseStep 2078999 = 3118499) B3118499
theorem B89946389 : Blo 1385512 89946389 := bstep (se 6 (by rfl) ⟨2108118, by rfl⟩ : syracuseStep 89946389 = 4216237) B4216237
theorem B2496833 : Blo 1385512 2496833 := bstep (se 2 (by rfl) ⟨936312, by rfl⟩ : syracuseStep 2496833 = 1872625) B1872625
theorem B5921099 : Blo 1385512 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B3119435 : Blo 1385512 3119435 := bstep (se 1 (by rfl) ⟨2339576, by rfl⟩ : syracuseStep 3119435 = 4679153) B4679153
theorem B2079065 : Blo 1385512 2079065 := bstep (se 2 (by rfl) ⟨779649, by rfl⟩ : syracuseStep 2079065 = 1559299) B1559299
theorem B3119489 : Blo 1385512 3119489 := bstep (se 2 (by rfl) ⟨1169808, by rfl⟩ : syracuseStep 3119489 = 2339617) B2339617
theorem B2341271 : Blo 1385512 2341271 := bstep (se 1 (by rfl) ⟨1755953, by rfl⟩ : syracuseStep 2341271 = 3511907) B3511907
theorem B2079179 : Blo 1385512 2079179 := bstep (se 1 (by rfl) ⟨1559384, by rfl⟩ : syracuseStep 2079179 = 3118769) B3118769
theorem B2079191 : Blo 1385512 2079191 := bstep (se 1 (by rfl) ⟨1559393, by rfl⟩ : syracuseStep 2079191 = 3118787) B3118787
theorem B2341399 : Blo 1385512 2341399 := bstep (se 1 (by rfl) ⟨1756049, by rfl⟩ : syracuseStep 2341399 = 3512099) B3512099
theorem B2079257 : Blo 1385512 2079257 := bstep (se 2 (by rfl) ⟨779721, by rfl⟩ : syracuseStep 2079257 = 1559443) B1559443
theorem B3119705 : Blo 1385512 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B2079371 : Blo 1385512 2079371 := bstep (se 1 (by rfl) ⟨1559528, by rfl⟩ : syracuseStep 2079371 = 3119057) B3119057
theorem B2079383 : Blo 1385512 2079383 := bstep (se 1 (by rfl) ⟨1559537, by rfl⟩ : syracuseStep 2079383 = 3119075) B3119075
theorem B3119795 : Blo 1385512 3119795 := bstep (se 1 (by rfl) ⟨2339846, by rfl⟩ : syracuseStep 3119795 = 4679693) B4679693
theorem B3332801 : Blo 1385512 3332801 := bstep (se 2 (by rfl) ⟨1249800, by rfl⟩ : syracuseStep 3332801 = 2499601) B2499601
theorem B89979605 : Blo 1385512 89979605 := bstep (se 7 (by rfl) ⟨1054448, by rfl⟩ : syracuseStep 89979605 = 2108897) B2108897
theorem B3119831 : Blo 1385512 3119831 := bstep (se 1 (by rfl) ⟨2339873, by rfl⟩ : syracuseStep 3119831 = 4679747) B4679747
theorem B2079449 : Blo 1385512 2079449 := bstep (se 2 (by rfl) ⟨779793, by rfl⟩ : syracuseStep 2079449 = 1559587) B1559587
theorem B12008209 : Blo 1385512 12008209 := bstep (se 2 (by rfl) ⟨4503078, by rfl⟩ : syracuseStep 12008209 = 9006157) B9006157
theorem B2079563 : Blo 1385512 2079563 := bstep (se 1 (by rfl) ⟨1559672, by rfl⟩ : syracuseStep 2079563 = 3119345) B3119345
theorem B2079575 : Blo 1385512 2079575 := bstep (se 1 (by rfl) ⟨1559681, by rfl⟩ : syracuseStep 2079575 = 3119363) B3119363
theorem B21347171 : Blo 1385512 21347171 := bstep (se 1 (by rfl) ⟨16010378, by rfl⟩ : syracuseStep 21347171 = 32020757) B32020757
theorem B3120011 : Blo 1385512 3120011 := bstep (se 1 (by rfl) ⟨2340008, by rfl⟩ : syracuseStep 3120011 = 4680017) B4680017
theorem B2079641 : Blo 1385512 2079641 := bstep (se 2 (by rfl) ⟨779865, by rfl⟩ : syracuseStep 2079641 = 1559731) B1559731
theorem B3161011 : Blo 1385512 3161011 := bstep (se 1 (by rfl) ⟨2370758, by rfl⟩ : syracuseStep 3161011 = 4741517) B4741517
theorem B3120065 : Blo 1385512 3120065 := bstep (se 2 (by rfl) ⟨1170024, by rfl⟩ : syracuseStep 3120065 = 2340049) B2340049
theorem B3947467 : Blo 1385512 3947467 := bstep (se 1 (by rfl) ⟨2960600, by rfl⟩ : syracuseStep 3947467 = 5921201) B5921201
theorem B4996043 : Blo 1385512 4996043 := bstep (se 1 (by rfl) ⟨3747032, by rfl⟩ : syracuseStep 4996043 = 7494065) B7494065
theorem B4996099 : Blo 1385512 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B2497547 : Blo 1385512 2497547 := bstep (se 1 (by rfl) ⟨1873160, by rfl⟩ : syracuseStep 2497547 = 3746321) B3746321
theorem B2079755 : Blo 1385512 2079755 := bstep (se 1 (by rfl) ⟨1559816, by rfl⟩ : syracuseStep 2079755 = 3119633) B3119633
theorem B2079767 : Blo 1385512 2079767 := bstep (se 1 (by rfl) ⟨1559825, by rfl⟩ : syracuseStep 2079767 = 3119651) B3119651
theorem B6667309 : Blo 1385512 6667309 := bstep (se 3 (by rfl) ⟨1250120, by rfl⟩ : syracuseStep 6667309 = 2500241) B2500241
theorem B1973335 : Blo 1385512 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B2079833 : Blo 1385512 2079833 := bstep (se 2 (by rfl) ⟨779937, by rfl⟩ : syracuseStep 2079833 = 1559875) B1559875
theorem B14998679 : Blo 1385512 14998679 := bstep (se 1 (by rfl) ⟨11249009, by rfl⟩ : syracuseStep 14998679 = 22498019) B22498019
theorem B3333271 : Blo 1385512 3333271 := bstep (se 1 (by rfl) ⟨2499953, by rfl⟩ : syracuseStep 3333271 = 4999907) B4999907
theorem B3120281 : Blo 1385512 3120281 := bstep (se 2 (by rfl) ⟨1170105, by rfl⟩ : syracuseStep 3120281 = 2340211) B2340211
theorem B2079947 : Blo 1385512 2079947 := bstep (se 1 (by rfl) ⟨1559960, by rfl⟩ : syracuseStep 2079947 = 3119921) B3119921
theorem B2079959 : Blo 1385512 2079959 := bstep (se 1 (by rfl) ⟨1559969, by rfl⟩ : syracuseStep 2079959 = 3119939) B3119939
theorem B4439261 : Blo 1385512 4439261 := bstep (se 3 (by rfl) ⟨832361, by rfl⟩ : syracuseStep 4439261 = 1664723) B1664723
theorem B3947741 : Blo 1385512 3947741 := bstep (se 3 (by rfl) ⟨740201, by rfl⟩ : syracuseStep 3947741 = 1480403) B1480403
theorem B3120371 : Blo 1385512 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B5266691 : Blo 1385512 5266691 := bstep (se 1 (by rfl) ⟨3950018, by rfl⟩ : syracuseStep 5266691 = 7900037) B7900037
theorem B3120407 : Blo 1385512 3120407 := bstep (se 1 (by rfl) ⟨2340305, by rfl⟩ : syracuseStep 3120407 = 4680611) B4680611
theorem B3161369 : Blo 1385512 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B2080025 : Blo 1385512 2080025 := bstep (se 2 (by rfl) ⟨780009, by rfl⟩ : syracuseStep 2080025 = 1560019) B1560019
theorem B22781249 : Blo 1385512 22781249 := bstep (se 2 (by rfl) ⟨8542968, by rfl⟩ : syracuseStep 22781249 = 17085937) B17085937
theorem B4676939 : Blo 1385512 4676939 := bstep (se 1 (by rfl) ⟨3507704, by rfl⟩ : syracuseStep 4676939 = 7015409) B7015409
theorem B4742489 : Blo 1385512 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B2080139 : Blo 1385512 2080139 := bstep (se 1 (by rfl) ⟨1560104, by rfl⟩ : syracuseStep 2080139 = 3120209) B3120209
theorem B2080151 : Blo 1385512 2080151 := bstep (se 1 (by rfl) ⟨1560113, by rfl⟩ : syracuseStep 2080151 = 3120227) B3120227
theorem B3120587 : Blo 1385512 3120587 := bstep (se 1 (by rfl) ⟨2340440, by rfl⟩ : syracuseStep 3120587 = 4680881) B4680881
theorem B2080217 : Blo 1385512 2080217 := bstep (se 2 (by rfl) ⟨780081, by rfl⟩ : syracuseStep 2080217 = 1560163) B1560163
theorem B3120641 : Blo 1385512 3120641 := bstep (se 2 (by rfl) ⟨1170240, by rfl⟩ : syracuseStep 3120641 = 2340481) B2340481
theorem B10526273 : Blo 1385512 10526273 := bstep (se 2 (by rfl) ⟨3947352, by rfl⟩ : syracuseStep 10526273 = 7894705) B7894705
theorem B10821185 : Blo 1385512 10821185 := bstep (se 2 (by rfl) ⟨4057944, by rfl⟩ : syracuseStep 10821185 = 8115889) B8115889
theorem B7020107 : Blo 1385512 7020107 := bstep (se 1 (by rfl) ⟨5265080, by rfl⟩ : syracuseStep 7020107 = 10530161) B10530161
theorem B2080331 : Blo 1385512 2080331 := bstep (se 1 (by rfl) ⟨1560248, by rfl⟩ : syracuseStep 2080331 = 3120497) B3120497
theorem B2080343 : Blo 1385512 2080343 := bstep (se 1 (by rfl) ⟨1560257, by rfl⟩ : syracuseStep 2080343 = 3120515) B3120515
theorem B4677209 : Blo 1385512 4677209 := bstep (se 2 (by rfl) ⟨1753953, by rfl⟩ : syracuseStep 4677209 = 3507907) B3507907
theorem B1973899 : Blo 1385512 1973899 := bstep (se 1 (by rfl) ⟨1480424, by rfl⟩ : syracuseStep 1973899 = 2960849) B2960849
theorem B2080409 : Blo 1385512 2080409 := bstep (se 2 (by rfl) ⟨780153, by rfl⟩ : syracuseStep 2080409 = 1560307) B1560307
theorem B3120857 : Blo 1385512 3120857 := bstep (se 2 (by rfl) ⟨1170321, by rfl⟩ : syracuseStep 3120857 = 2340643) B2340643
theorem B2080523 : Blo 1385512 2080523 := bstep (se 1 (by rfl) ⟨1560392, by rfl⟩ : syracuseStep 2080523 = 3120785) B3120785
theorem B2080535 : Blo 1385512 2080535 := bstep (se 1 (by rfl) ⟨1560401, by rfl⟩ : syracuseStep 2080535 = 3120803) B3120803
theorem B3120947 : Blo 1385512 3120947 := bstep (se 1 (by rfl) ⟨2340710, by rfl⟩ : syracuseStep 3120947 = 4681421) B4681421
theorem B3120983 : Blo 1385512 3120983 := bstep (se 1 (by rfl) ⟨2340737, by rfl⟩ : syracuseStep 3120983 = 4681475) B4681475
theorem B2080601 : Blo 1385512 2080601 := bstep (se 2 (by rfl) ⟨780225, by rfl⟩ : syracuseStep 2080601 = 1560451) B1560451
theorem B7495517 : Blo 1385512 7495517 := bstep (se 3 (by rfl) ⟨1405409, by rfl⟩ : syracuseStep 7495517 = 2810819) B2810819
theorem B2080715 : Blo 1385512 2080715 := bstep (se 1 (by rfl) ⟨1560536, by rfl⟩ : syracuseStep 2080715 = 3121073) B3121073
theorem B2080727 : Blo 1385512 2080727 := bstep (se 1 (by rfl) ⟨1560545, by rfl⟩ : syracuseStep 2080727 = 3121091) B3121091
theorem B2080775 : Blo 1385512 2080775 := bstep (se 1 (by rfl) ⟨1560581, by rfl⟩ : syracuseStep 2080775 = 3121163) B3121163
theorem B2080811 : Blo 1385512 2080811 := bstep (se 1 (by rfl) ⟨1560608, by rfl⟩ : syracuseStep 2080811 = 3121217) B3121217
theorem B2080841 : Blo 1385512 2080841 := bstep (se 2 (by rfl) ⟨780315, by rfl⟩ : syracuseStep 2080841 = 1560631) B1560631
theorem B3121271 : Blo 1385512 3121271 := bstep (se 1 (by rfl) ⟨2340953, by rfl⟩ : syracuseStep 3121271 = 4681907) B4681907
theorem B2080955 : Blo 1385512 2080955 := bstep (se 1 (by rfl) ⟨1560716, by rfl⟩ : syracuseStep 2080955 = 3121433) B3121433
theorem B5267693 : Blo 1385512 5267693 := bstep (se 3 (by rfl) ⟨987692, by rfl⟩ : syracuseStep 5267693 = 1975385) B1975385
theorem B2081015 : Blo 1385512 2081015 := bstep (se 1 (by rfl) ⟨1560761, by rfl⟩ : syracuseStep 2081015 = 3121523) B3121523
theorem B2081039 : Blo 1385512 2081039 := bstep (se 1 (by rfl) ⟨1560779, by rfl⟩ : syracuseStep 2081039 = 3121559) B3121559
theorem B3121451 : Blo 1385512 3121451 := bstep (se 1 (by rfl) ⟨2341088, by rfl⟩ : syracuseStep 3121451 = 4682177) B4682177
theorem B2081081 : Blo 1385512 2081081 := bstep (se 2 (by rfl) ⟨780405, by rfl⟩ : syracuseStep 2081081 = 1560811) B1560811
theorem B2081159 : Blo 1385512 2081159 := bstep (se 1 (by rfl) ⟨1560869, by rfl⟩ : syracuseStep 2081159 = 3121739) B3121739
theorem B2081195 : Blo 1385512 2081195 := bstep (se 1 (by rfl) ⟨1560896, by rfl⟩ : syracuseStep 2081195 = 3121793) B3121793
theorem B4678073 : Blo 1385512 4678073 := bstep (se 2 (by rfl) ⟨1754277, by rfl⟩ : syracuseStep 4678073 = 3508555) B3508555
theorem B2081225 : Blo 1385512 2081225 := bstep (se 2 (by rfl) ⟨780459, by rfl⟩ : syracuseStep 2081225 = 1560919) B1560919
theorem B3424769 : Blo 1385512 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B7021079 : Blo 1385512 7021079 := bstep (se 1 (by rfl) ⟨5265809, by rfl⟩ : syracuseStep 7021079 = 10531619) B10531619
theorem B6324779 : Blo 1385512 6324779 := bstep (se 1 (by rfl) ⟨4743584, by rfl⟩ : syracuseStep 6324779 = 9487169) B9487169
theorem B1974827 : Blo 1385512 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B14221925 : Blo 1385512 14221925 := bstep (se 4 (by rfl) ⟨1333305, by rfl⟩ : syracuseStep 14221925 = 2666611) B2666611
theorem B3949175 : Blo 1385512 3949175 := bstep (se 1 (by rfl) ⟨2961881, by rfl⟩ : syracuseStep 3949175 = 5923763) B5923763
theorem B3121811 : Blo 1385512 3121811 := bstep (se 1 (by rfl) ⟨2341358, by rfl⟩ : syracuseStep 3121811 = 4682717) B4682717
theorem B2220745 : Blo 1385512 2220745 := bstep (se 2 (by rfl) ⟨832779, by rfl⟩ : syracuseStep 2220745 = 1665559) B1665559
theorem B3121865 : Blo 1385512 3121865 := bstep (se 2 (by rfl) ⟨1170699, by rfl⟩ : syracuseStep 3121865 = 2341399) B2341399
theorem B8430317 : Blo 1385512 8430317 := bstep (se 3 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 8430317 = 3161369) B3161369
theorem B6325127 : Blo 1385512 6325127 := bstep (se 1 (by rfl) ⟨4743845, by rfl⟩ : syracuseStep 6325127 = 9487691) B9487691
theorem B3507097 : Blo 1385512 3507097 := bstep (se 2 (by rfl) ⟨1315161, by rfl⟩ : syracuseStep 3507097 = 2630323) B2630323
theorem B4678667 : Blo 1385512 4678667 := bstep (se 1 (by rfl) ⟨3509000, by rfl⟩ : syracuseStep 4678667 = 7018001) B7018001
theorem B1385531 : Blo 1385512 1385531 := bstep (se 1 (by rfl) ⟨1039148, by rfl⟩ : syracuseStep 1385531 = 2078297) B2078297
theorem B3507259 : Blo 1385512 3507259 := bstep (se 1 (by rfl) ⟨2630444, by rfl⟩ : syracuseStep 3507259 = 5260889) B5260889
theorem B4678775 : Blo 1385512 4678775 := bstep (se 1 (by rfl) ⟨3509081, by rfl⟩ : syracuseStep 4678775 = 7018163) B7018163
theorem B1385607 : Blo 1385512 1385607 := bstep (se 1 (by rfl) ⟨1039205, by rfl⟩ : syracuseStep 1385607 = 2078411) B2078411
theorem B1385615 : Blo 1385512 1385615 := bstep (se 1 (by rfl) ⟨1039211, by rfl⟩ : syracuseStep 1385615 = 2078423) B2078423
theorem B1385659 : Blo 1385512 1385659 := bstep (se 1 (by rfl) ⟨1039244, by rfl⟩ : syracuseStep 1385659 = 2078489) B2078489
theorem B3507401 : Blo 1385512 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B1385735 : Blo 1385512 1385735 := bstep (se 1 (by rfl) ⟨1039301, by rfl⟩ : syracuseStep 1385735 = 2078603) B2078603
theorem B1385743 : Blo 1385512 1385743 := bstep (se 1 (by rfl) ⟨1039307, by rfl⟩ : syracuseStep 1385743 = 2078615) B2078615
theorem B13329697 : Blo 1385512 13329697 := bstep (se 2 (by rfl) ⟨4998636, by rfl⟩ : syracuseStep 13329697 = 9997273) B9997273
theorem B8111411 : Blo 1385512 8111411 := bstep (se 1 (by rfl) ⟨6083558, by rfl⟩ : syracuseStep 8111411 = 12167117) B12167117
theorem B1385787 : Blo 1385512 1385787 := bstep (se 1 (by rfl) ⟨1039340, by rfl⟩ : syracuseStep 1385787 = 2078681) B2078681
theorem B1385863 : Blo 1385512 1385863 := bstep (se 1 (by rfl) ⟨1039397, by rfl⟩ : syracuseStep 1385863 = 2078795) B2078795
theorem B1385871 : Blo 1385512 1385871 := bstep (se 1 (by rfl) ⟨1039403, by rfl⟩ : syracuseStep 1385871 = 2078807) B2078807
theorem B8889745 : Blo 1385512 8889745 := bstep (se 2 (by rfl) ⟨3333654, by rfl⟩ : syracuseStep 8889745 = 6667309) B6667309
theorem B1385915 : Blo 1385512 1385915 := bstep (se 1 (by rfl) ⟨1039436, by rfl⟩ : syracuseStep 1385915 = 2078873) B2078873
theorem B2631113 : Blo 1385512 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B1385991 : Blo 1385512 1385991 := bstep (se 1 (by rfl) ⟨1039493, by rfl⟩ : syracuseStep 1385991 = 2078987) B2078987
theorem B1385999 : Blo 1385512 1385999 := bstep (se 1 (by rfl) ⟨1039499, by rfl⟩ : syracuseStep 1385999 = 2078999) B2078999
theorem B3507745 : Blo 1385512 3507745 := bstep (se 2 (by rfl) ⟨1315404, by rfl⟩ : syracuseStep 3507745 = 2630809) B2630809
theorem B1664555 : Blo 1385512 1664555 := bstep (se 1 (by rfl) ⟨1248416, by rfl⟩ : syracuseStep 1664555 = 2496833) B2496833
theorem B1386043 : Blo 1385512 1386043 := bstep (se 1 (by rfl) ⟨1039532, by rfl⟩ : syracuseStep 1386043 = 2079065) B2079065
theorem B29992517 : Blo 1385512 29992517 := bstep (se 4 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 29992517 = 5623597) B5623597
theorem B22808141 : Blo 1385512 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B3950167 : Blo 1385512 3950167 := bstep (se 1 (by rfl) ⟨2962625, by rfl⟩ : syracuseStep 3950167 = 5925251) B5925251
theorem B22488677 : Blo 1385512 22488677 := bstep (se 4 (by rfl) ⟨2108313, by rfl⟩ : syracuseStep 22488677 = 4216627) B4216627
theorem B1386119 : Blo 1385512 1386119 := bstep (se 1 (by rfl) ⟨1039589, by rfl⟩ : syracuseStep 1386119 = 2079179) B2079179
theorem B1386127 : Blo 1385512 1386127 := bstep (se 1 (by rfl) ⟨1039595, by rfl⟩ : syracuseStep 1386127 = 2079191) B2079191
theorem B1386171 : Blo 1385512 1386171 := bstep (se 1 (by rfl) ⟨1039628, by rfl⟩ : syracuseStep 1386171 = 2079257) B2079257
theorem B4679369 : Blo 1385512 4679369 := bstep (se 2 (by rfl) ⟨1754763, by rfl⟩ : syracuseStep 4679369 = 3509527) B3509527
theorem B5261057 : Blo 1385512 5261057 := bstep (se 2 (by rfl) ⟨1972896, by rfl⟩ : syracuseStep 5261057 = 3945793) B3945793
theorem B1386247 : Blo 1385512 1386247 := bstep (se 1 (by rfl) ⟨1039685, by rfl⟩ : syracuseStep 1386247 = 2079371) B2079371
theorem B5261071 : Blo 1385512 5261071 := bstep (se 1 (by rfl) ⟨3945803, by rfl⟩ : syracuseStep 5261071 = 7891607) B7891607
theorem B1386255 : Blo 1385512 1386255 := bstep (se 1 (by rfl) ⟨1039691, by rfl⟩ : syracuseStep 1386255 = 2079383) B2079383
theorem B2221867 : Blo 1385512 2221867 := bstep (se 1 (by rfl) ⟨1666400, by rfl⟩ : syracuseStep 2221867 = 3332801) B3332801
theorem B1386299 : Blo 1385512 1386299 := bstep (se 1 (by rfl) ⟨1039724, by rfl⟩ : syracuseStep 1386299 = 2079449) B2079449
theorem B1386375 : Blo 1385512 1386375 := bstep (se 1 (by rfl) ⟨1039781, by rfl⟩ : syracuseStep 1386375 = 2079563) B2079563
theorem B1386383 : Blo 1385512 1386383 := bstep (se 1 (by rfl) ⟨1039787, by rfl⟩ : syracuseStep 1386383 = 2079575) B2079575
theorem B4442003 : Blo 1385512 4442003 := bstep (se 1 (by rfl) ⟨3331502, by rfl⟩ : syracuseStep 4442003 = 6663005) B6663005
theorem B14231447 : Blo 1385512 14231447 := bstep (se 1 (by rfl) ⟨10673585, by rfl⟩ : syracuseStep 14231447 = 21347171) B21347171
theorem B1386427 : Blo 1385512 1386427 := bstep (se 1 (by rfl) ⟨1039820, by rfl⟩ : syracuseStep 1386427 = 2079641) B2079641
theorem B1665031 : Blo 1385512 1665031 := bstep (se 1 (by rfl) ⟨1248773, by rfl⟩ : syracuseStep 1665031 = 2497547) B2497547
theorem B1386503 : Blo 1385512 1386503 := bstep (se 1 (by rfl) ⟨1039877, by rfl⟩ : syracuseStep 1386503 = 2079755) B2079755
theorem B1386511 : Blo 1385512 1386511 := bstep (se 1 (by rfl) ⟨1039883, by rfl⟩ : syracuseStep 1386511 = 2079767) B2079767
theorem B1386555 : Blo 1385512 1386555 := bstep (se 1 (by rfl) ⟨1039916, by rfl⟩ : syracuseStep 1386555 = 2079833) B2079833
theorem B3508343 : Blo 1385512 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B1386631 : Blo 1385512 1386631 := bstep (se 1 (by rfl) ⟨1039973, by rfl⟩ : syracuseStep 1386631 = 2079947) B2079947
theorem B1386639 : Blo 1385512 1386639 := bstep (se 1 (by rfl) ⟨1039979, by rfl⟩ : syracuseStep 1386639 = 2079959) B2079959
theorem B2959507 : Blo 1385512 2959507 := bstep (se 1 (by rfl) ⟨2219630, by rfl⟩ : syracuseStep 2959507 = 4439261) B4439261
theorem B2631827 : Blo 1385512 2631827 := bstep (se 1 (by rfl) ⟨1973870, by rfl⟩ : syracuseStep 2631827 = 3947741) B3947741
theorem B2631865 : Blo 1385512 2631865 := bstep (se 2 (by rfl) ⟨986949, by rfl⟩ : syracuseStep 2631865 = 1973899) B1973899
theorem B1386683 : Blo 1385512 1386683 := bstep (se 1 (by rfl) ⟨1040012, by rfl⟩ : syracuseStep 1386683 = 2080025) B2080025
theorem B1386759 : Blo 1385512 1386759 := bstep (se 1 (by rfl) ⟨1040069, by rfl⟩ : syracuseStep 1386759 = 2080139) B2080139
theorem B1386767 : Blo 1385512 1386767 := bstep (se 1 (by rfl) ⟨1040075, by rfl⟩ : syracuseStep 1386767 = 2080151) B2080151
theorem B1386811 : Blo 1385512 1386811 := bstep (se 1 (by rfl) ⟨1040108, by rfl⟩ : syracuseStep 1386811 = 2080217) B2080217
theorem B7891289 : Blo 1385512 7891289 := bstep (se 2 (by rfl) ⟨2959233, by rfl⟩ : syracuseStep 7891289 = 5918467) B5918467
theorem B4680071 : Blo 1385512 4680071 := bstep (se 1 (by rfl) ⟨3510053, by rfl⟩ : syracuseStep 4680071 = 7020107) B7020107
theorem B1386887 : Blo 1385512 1386887 := bstep (se 1 (by rfl) ⟨1040165, by rfl⟩ : syracuseStep 1386887 = 2080331) B2080331
theorem B1386895 : Blo 1385512 1386895 := bstep (se 1 (by rfl) ⟨1040171, by rfl⟩ : syracuseStep 1386895 = 2080343) B2080343
theorem B9488785 : Blo 1385512 9488785 := bstep (se 2 (by rfl) ⟨3558294, by rfl⟩ : syracuseStep 9488785 = 7116589) B7116589
theorem B1386939 : Blo 1385512 1386939 := bstep (se 1 (by rfl) ⟨1040204, by rfl⟩ : syracuseStep 1386939 = 2080409) B2080409
theorem B1559047 : Blo 1385512 1559047 := bstep (se 1 (by rfl) ⟨1169285, by rfl⟩ : syracuseStep 1559047 = 2338571) B2338571
theorem B1387015 : Blo 1385512 1387015 := bstep (se 1 (by rfl) ⟨1040261, by rfl⟩ : syracuseStep 1387015 = 2080523) B2080523
theorem B7014923 : Blo 1385512 7014923 := bstep (se 1 (by rfl) ⟨5261192, by rfl⟩ : syracuseStep 7014923 = 10522385) B10522385
theorem B1387023 : Blo 1385512 1387023 := bstep (se 1 (by rfl) ⟨1040267, by rfl⟩ : syracuseStep 1387023 = 2080535) B2080535
theorem B1387067 : Blo 1385512 1387067 := bstep (se 1 (by rfl) ⟨1040300, by rfl⟩ : syracuseStep 1387067 = 2080601) B2080601
theorem B1387143 : Blo 1385512 1387143 := bstep (se 1 (by rfl) ⟨1040357, by rfl⟩ : syracuseStep 1387143 = 2080715) B2080715
theorem B1387151 : Blo 1385512 1387151 := bstep (se 1 (by rfl) ⟨1040363, by rfl⟩ : syracuseStep 1387151 = 2080727) B2080727
theorem B7015085 : Blo 1385512 7015085 := bstep (se 3 (by rfl) ⟨1315328, by rfl⟩ : syracuseStep 7015085 = 2630657) B2630657
theorem B1559227 : Blo 1385512 1559227 := bstep (se 1 (by rfl) ⟨1169420, by rfl⟩ : syracuseStep 1559227 = 2338841) B2338841
theorem B1387195 : Blo 1385512 1387195 := bstep (se 1 (by rfl) ⟨1040396, by rfl⟩ : syracuseStep 1387195 = 2080793) B2080793
theorem B4680449 : Blo 1385512 4680449 := bstep (se 2 (by rfl) ⟨1755168, by rfl⟩ : syracuseStep 4680449 = 3510337) B3510337
theorem B1387271 : Blo 1385512 1387271 := bstep (se 1 (by rfl) ⟨1040453, by rfl⟩ : syracuseStep 1387271 = 2080907) B2080907
theorem B1387279 : Blo 1385512 1387279 := bstep (se 1 (by rfl) ⟨1040459, by rfl⟩ : syracuseStep 1387279 = 2080919) B2080919
theorem B1387323 : Blo 1385512 1387323 := bstep (se 1 (by rfl) ⟨1040492, by rfl⟩ : syracuseStep 1387323 = 2080985) B2080985
theorem B7490393 : Blo 1385512 7490393 := bstep (se 2 (by rfl) ⟨2808897, by rfl⟩ : syracuseStep 7490393 = 5617795) B5617795
theorem B1387399 : Blo 1385512 1387399 := bstep (se 1 (by rfl) ⟨1040549, by rfl⟩ : syracuseStep 1387399 = 2081099) B2081099
theorem B1387407 : Blo 1385512 1387407 := bstep (se 1 (by rfl) ⟨1040555, by rfl⟩ : syracuseStep 1387407 = 2081111) B2081111
theorem B1387451 : Blo 1385512 1387451 := bstep (se 1 (by rfl) ⟨1040588, by rfl⟩ : syracuseStep 1387451 = 2081177) B2081177
theorem B5262347 : Blo 1385512 5262347 := bstep (se 1 (by rfl) ⟨3946760, by rfl⟩ : syracuseStep 5262347 = 7893521) B7893521
theorem B6663197 : Blo 1385512 6663197 := bstep (se 3 (by rfl) ⟨1249349, by rfl⟩ : syracuseStep 6663197 = 2498699) B2498699
theorem B6663235 : Blo 1385512 6663235 := bstep (se 1 (by rfl) ⟨4997426, by rfl⟩ : syracuseStep 6663235 = 9994853) B9994853
theorem B1559695 : Blo 1385512 1559695 := bstep (se 1 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 1559695 = 2339543) B2339543
theorem B3509639 : Blo 1385512 3509639 := bstep (se 1 (by rfl) ⟨2632229, by rfl⟩ : syracuseStep 3509639 = 5264459) B5264459
theorem B3509689 : Blo 1385512 3509689 := bstep (se 2 (by rfl) ⟨1316133, by rfl⟩ : syracuseStep 3509689 = 2632267) B2632267
theorem B7024157 : Blo 1385512 7024157 := bstep (se 3 (by rfl) ⟨1317029, by rfl⟩ : syracuseStep 7024157 = 2634059) B2634059
theorem B4681259 : Blo 1385512 4681259 := bstep (se 1 (by rfl) ⟨3510944, by rfl⟩ : syracuseStep 4681259 = 7021889) B7021889
theorem B4501079 : Blo 1385512 4501079 := bstep (se 1 (by rfl) ⟨3375809, by rfl⟩ : syracuseStep 4501079 = 6751619) B6751619
theorem B1560199 : Blo 1385512 1560199 := bstep (se 1 (by rfl) ⟨1170149, by rfl⟩ : syracuseStep 1560199 = 2340299) B2340299
theorem B16010945 : Blo 1385512 16010945 := bstep (se 2 (by rfl) ⟨6004104, by rfl⟩ : syracuseStep 16010945 = 12008209) B12008209
theorem B7491365 : Blo 1385512 7491365 := bstep (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) B1404631
theorem B7499557 : Blo 1385512 7499557 := bstep (se 4 (by rfl) ⟨703083, by rfl⟩ : syracuseStep 7499557 = 1406167) B1406167
theorem B1560379 : Blo 1385512 1560379 := bstep (se 1 (by rfl) ⟨1170284, by rfl⟩ : syracuseStep 1560379 = 2340569) B2340569
theorem B4271987 : Blo 1385512 4271987 := bstep (se 1 (by rfl) ⟨3203990, by rfl⟩ : syracuseStep 4271987 = 6407981) B6407981
theorem B2338679 : Blo 1385512 2338679 := bstep (se 1 (by rfl) ⟨1754009, by rfl⟩ : syracuseStep 2338679 = 3508019) B3508019
theorem B7901063 : Blo 1385512 7901063 := bstep (se 1 (by rfl) ⟨5925797, by rfl⟩ : syracuseStep 7901063 = 11851595) B11851595
theorem B4214681 : Blo 1385512 4214681 := bstep (se 2 (by rfl) ⟨1580505, by rfl⟩ : syracuseStep 4214681 = 3161011) B3161011
theorem B5263289 : Blo 1385512 5263289 := bstep (se 2 (by rfl) ⟨1973733, by rfl⟩ : syracuseStep 5263289 = 3947467) B3947467
theorem B2961353 : Blo 1385512 2961353 := bstep (se 2 (by rfl) ⟨1110507, by rfl⟩ : syracuseStep 2961353 = 2221015) B2221015
theorem B3510287 : Blo 1385512 3510287 := bstep (se 1 (by rfl) ⟨2632715, by rfl⟩ : syracuseStep 3510287 = 5265431) B5265431
theorem B2633771 : Blo 1385512 2633771 := bstep (se 1 (by rfl) ⟨1975328, by rfl⟩ : syracuseStep 2633771 = 3950657) B3950657
theorem B4444247 : Blo 1385512 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B4444361 : Blo 1385512 4444361 := bstep (se 2 (by rfl) ⟨1666635, by rfl⟩ : syracuseStep 4444361 = 3333271) B3333271
theorem B7016705 : Blo 1385512 7016705 := bstep (se 2 (by rfl) ⟨2631264, by rfl⟩ : syracuseStep 7016705 = 5262529) B5262529
theorem B1560847 : Blo 1385512 1560847 := bstep (se 1 (by rfl) ⟨1170635, by rfl⟩ : syracuseStep 1560847 = 2341271) B2341271
theorem B2339131 : Blo 1385512 2339131 := bstep (se 1 (by rfl) ⟨1754348, by rfl⟩ : syracuseStep 2339131 = 3508697) B3508697
theorem B2339273 : Blo 1385512 2339273 := bstep (se 2 (by rfl) ⟨877227, by rfl⟩ : syracuseStep 2339273 = 1754455) B1754455
theorem B59986403 : Blo 1385512 59986403 := bstep (se 1 (by rfl) ⟨44989802, by rfl⟩ : syracuseStep 59986403 = 89979605) B89979605
theorem B21639665 : Blo 1385512 21639665 := bstep (se 2 (by rfl) ⟨8114874, by rfl⟩ : syracuseStep 21639665 = 16229749) B16229749
theorem B3330695 : Blo 1385512 3330695 := bstep (se 1 (by rfl) ⟨2498021, by rfl⟩ : syracuseStep 3330695 = 4996043) B4996043
theorem B3510985 : Blo 1385512 3510985 := bstep (se 2 (by rfl) ⟨1316619, by rfl⟩ : syracuseStep 3510985 = 2633239) B2633239
theorem B8008429 : Blo 1385512 8008429 := bstep (se 3 (by rfl) ⟨1501580, by rfl⟩ : syracuseStep 8008429 = 3003161) B3003161
theorem B4993793 : Blo 1385512 4993793 := bstep (se 2 (by rfl) ⟨1872672, by rfl⟩ : syracuseStep 4993793 = 3745345) B3745345
theorem B9999119 : Blo 1385512 9999119 := bstep (se 1 (by rfl) ⟨7499339, by rfl⟩ : syracuseStep 9999119 = 14998679) B14998679
theorem B11850533 : Blo 1385512 11850533 := bstep (se 4 (by rfl) ⟨1110987, by rfl⟩ : syracuseStep 11850533 = 2221975) B2221975
theorem B4682555 : Blo 1385512 4682555 := bstep (se 1 (by rfl) ⟨3511916, by rfl⟩ : syracuseStep 4682555 = 7023833) B7023833
theorem B12645209 : Blo 1385512 12645209 := bstep (se 2 (by rfl) ⟨4741953, by rfl⟩ : syracuseStep 12645209 = 9483907) B9483907
theorem B3511127 : Blo 1385512 3511127 := bstep (se 1 (by rfl) ⟨2633345, by rfl⟩ : syracuseStep 3511127 = 5266691) B5266691
theorem B3117959 : Blo 1385512 3117959 := bstep (se 1 (by rfl) ⟨2338469, by rfl⟩ : syracuseStep 3117959 = 4676939) B4676939
theorem B128054195 : Blo 1385512 128054195 := bstep (se 1 (by rfl) ⟨96040646, by rfl⟩ : syracuseStep 128054195 = 192081293) B192081293
theorem B7017515 : Blo 1385512 7017515 := bstep (se 1 (by rfl) ⟨5263136, by rfl⟩ : syracuseStep 7017515 = 10526273) B10526273
theorem B7214123 : Blo 1385512 7214123 := bstep (se 1 (by rfl) ⟨5410592, by rfl⟩ : syracuseStep 7214123 = 10821185) B10821185
theorem B3118139 : Blo 1385512 3118139 := bstep (se 1 (by rfl) ⟨2338604, by rfl⟩ : syracuseStep 3118139 = 4677209) B4677209
theorem B7902269 : Blo 1385512 7902269 := bstep (se 3 (by rfl) ⟨1481675, by rfl⟩ : syracuseStep 7902269 = 2963351) B2963351
theorem B2339975 : Blo 1385512 2339975 := bstep (se 1 (by rfl) ⟨1754981, by rfl⟩ : syracuseStep 2339975 = 3509963) B3509963
theorem B3118265 : Blo 1385512 3118265 := bstep (se 2 (by rfl) ⟨1169349, by rfl⟩ : syracuseStep 3118265 = 2338699) B2338699
theorem B26645861 : Blo 1385512 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B16012691 : Blo 1385512 16012691 := bstep (se 1 (by rfl) ⟨12009518, by rfl⟩ : syracuseStep 16012691 = 24019037) B24019037
theorem B11851217 : Blo 1385512 11851217 := bstep (se 2 (by rfl) ⟨4444206, by rfl⟩ : syracuseStep 11851217 = 8888413) B8888413
theorem B3118607 : Blo 1385512 3118607 := bstep (se 1 (by rfl) ⟨2338955, by rfl⟩ : syracuseStep 3118607 = 4677911) B4677911
theorem B118494737 : Blo 1385512 118494737 := bstep (se 2 (by rfl) ⟨44435526, by rfl⟩ : syracuseStep 118494737 = 88871053) B88871053
theorem B3118625 : Blo 1385512 3118625 := bstep (se 2 (by rfl) ⟨1169484, by rfl⟩ : syracuseStep 3118625 = 2338969) B2338969
theorem B6665771 : Blo 1385512 6665771 := bstep (se 1 (by rfl) ⟨4999328, by rfl⟩ : syracuseStep 6665771 = 9998657) B9998657
theorem B2078327 : Blo 1385512 2078327 := bstep (se 1 (by rfl) ⟨1558745, by rfl⟩ : syracuseStep 2078327 = 3117491) B3117491
theorem B2078351 : Blo 1385512 2078351 := bstep (se 1 (by rfl) ⟨1558763, by rfl⟩ : syracuseStep 2078351 = 3117527) B3117527
theorem B2078393 : Blo 1385512 2078393 := bstep (se 2 (by rfl) ⟨779397, by rfl⟩ : syracuseStep 2078393 = 1558795) B1558795
theorem B2078471 : Blo 1385512 2078471 := bstep (se 1 (by rfl) ⟨1558853, by rfl⟩ : syracuseStep 2078471 = 3117707) B3117707
theorem B4994831 : Blo 1385512 4994831 := bstep (se 1 (by rfl) ⟨3746123, by rfl⟩ : syracuseStep 4994831 = 7492247) B7492247
theorem B2340623 : Blo 1385512 2340623 := bstep (se 1 (by rfl) ⟨1755467, by rfl⟩ : syracuseStep 2340623 = 3510935) B3510935
theorem B2078507 : Blo 1385512 2078507 := bstep (se 1 (by rfl) ⟨1558880, by rfl⟩ : syracuseStep 2078507 = 3117761) B3117761
theorem B3946283 : Blo 1385512 3946283 := bstep (se 1 (by rfl) ⟨2959712, by rfl⟩ : syracuseStep 3946283 = 5919425) B5919425
theorem B2078537 : Blo 1385512 2078537 := bstep (se 2 (by rfl) ⟨779451, by rfl⟩ : syracuseStep 2078537 = 1558903) B1558903
theorem B3331955 : Blo 1385512 3331955 := bstep (se 1 (by rfl) ⟨2498966, by rfl⟩ : syracuseStep 3331955 = 4997933) B4997933
theorem B3118967 : Blo 1385512 3118967 := bstep (se 1 (by rfl) ⟨2339225, by rfl⟩ : syracuseStep 3118967 = 4678451) B4678451
theorem B2078651 : Blo 1385512 2078651 := bstep (se 1 (by rfl) ⟨1558988, by rfl⟩ : syracuseStep 2078651 = 3117977) B3117977
theorem B10000331 : Blo 1385512 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B8009675 : Blo 1385512 8009675 := bstep (se 1 (by rfl) ⟨6007256, by rfl⟩ : syracuseStep 8009675 = 12014513) B12014513
theorem B2078711 : Blo 1385512 2078711 := bstep (se 1 (by rfl) ⟨1559033, by rfl⟩ : syracuseStep 2078711 = 3118067) B3118067
theorem B2078735 : Blo 1385512 2078735 := bstep (se 1 (by rfl) ⟨1559051, by rfl⟩ : syracuseStep 2078735 = 3118103) B3118103
theorem B3119147 : Blo 1385512 3119147 := bstep (se 1 (by rfl) ⟨2339360, by rfl⟩ : syracuseStep 3119147 = 4678721) B4678721
theorem B2078777 : Blo 1385512 2078777 := bstep (se 2 (by rfl) ⟨779541, by rfl⟩ : syracuseStep 2078777 = 1559083) B1559083
theorem B4388951 : Blo 1385512 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B2078855 : Blo 1385512 2078855 := bstep (se 1 (by rfl) ⟨1559141, by rfl⟩ : syracuseStep 2078855 = 3118283) B3118283
theorem B1480847 : Blo 1385512 1480847 := bstep (se 1 (by rfl) ⟨1110635, by rfl⟩ : syracuseStep 1480847 = 2221271) B2221271
theorem B2078891 : Blo 1385512 2078891 := bstep (se 1 (by rfl) ⟨1559168, by rfl⟩ : syracuseStep 2078891 = 3118337) B3118337
theorem B4217017 : Blo 1385512 4217017 := bstep (se 2 (by rfl) ⟨1581381, by rfl⟩ : syracuseStep 4217017 = 3162763) B3162763
theorem B2078921 : Blo 1385512 2078921 := bstep (se 2 (by rfl) ⟨779595, by rfl⟩ : syracuseStep 2078921 = 1559191) B1559191
theorem B4741409 : Blo 1385512 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B2341163 : Blo 1385512 2341163 := bstep (se 1 (by rfl) ⟨1755872, by rfl⟩ : syracuseStep 2341163 = 3511745) B3511745
theorem B2079035 : Blo 1385512 2079035 := bstep (se 1 (by rfl) ⟨1559276, by rfl⟩ : syracuseStep 2079035 = 3118553) B3118553
theorem B7018811 : Blo 1385512 7018811 := bstep (se 1 (by rfl) ⟨5264108, by rfl⟩ : syracuseStep 7018811 = 10528217) B10528217
theorem B2079095 : Blo 1385512 2079095 := bstep (se 1 (by rfl) ⟨1559321, by rfl⟩ : syracuseStep 2079095 = 3118643) B3118643
theorem B1481095 : Blo 1385512 1481095 := bstep (se 1 (by rfl) ⟨1110821, by rfl⟩ : syracuseStep 1481095 = 2221643) B2221643
theorem B2079119 : Blo 1385512 2079119 := bstep (se 1 (by rfl) ⟨1559339, by rfl⟩ : syracuseStep 2079119 = 3118679) B3118679
theorem B3119507 : Blo 1385512 3119507 := bstep (se 1 (by rfl) ⟨2339630, by rfl⟩ : syracuseStep 3119507 = 4679261) B4679261
theorem B2079161 : Blo 1385512 2079161 := bstep (se 2 (by rfl) ⟨779685, by rfl⟩ : syracuseStep 2079161 = 1559371) B1559371
theorem B3119561 : Blo 1385512 3119561 := bstep (se 2 (by rfl) ⟨1169835, by rfl⟩ : syracuseStep 3119561 = 2339671) B2339671
theorem B7018973 : Blo 1385512 7018973 := bstep (se 3 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 7018973 = 2632115) B2632115
theorem B2079239 : Blo 1385512 2079239 := bstep (se 1 (by rfl) ⟨1559429, by rfl⟩ : syracuseStep 2079239 = 3118859) B3118859
theorem B5265931 : Blo 1385512 5265931 := bstep (se 1 (by rfl) ⟨3949448, by rfl⟩ : syracuseStep 5265931 = 7898897) B7898897
theorem B2079275 : Blo 1385512 2079275 := bstep (se 1 (by rfl) ⟨1559456, by rfl⟩ : syracuseStep 2079275 = 3118913) B3118913
theorem B3947069 : Blo 1385512 3947069 := bstep (se 3 (by rfl) ⟨740075, by rfl⟩ : syracuseStep 3947069 = 1480151) B1480151
theorem B2079305 : Blo 1385512 2079305 := bstep (se 2 (by rfl) ⟨779739, by rfl⟩ : syracuseStep 2079305 = 1559479) B1559479
theorem B4676183 : Blo 1385512 4676183 := bstep (se 1 (by rfl) ⟨3507137, by rfl⟩ : syracuseStep 4676183 = 7014275) B7014275
theorem B2079419 : Blo 1385512 2079419 := bstep (se 1 (by rfl) ⟨1559564, by rfl⟩ : syracuseStep 2079419 = 3119129) B3119129
theorem B2079479 : Blo 1385512 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B9124609 : Blo 1385512 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B2079503 : Blo 1385512 2079503 := bstep (se 1 (by rfl) ⟨1559627, by rfl⟩ : syracuseStep 2079503 = 3119255) B3119255
theorem B7019297 : Blo 1385512 7019297 := bstep (se 2 (by rfl) ⟨2632236, by rfl⟩ : syracuseStep 7019297 = 5264473) B5264473
theorem B2079545 : Blo 1385512 2079545 := bstep (se 2 (by rfl) ⟨779829, by rfl⟩ : syracuseStep 2079545 = 1559659) B1559659
theorem B5266235 : Blo 1385512 5266235 := bstep (se 1 (by rfl) ⟨3949676, by rfl⟩ : syracuseStep 5266235 = 7899353) B7899353
theorem B59964259 : Blo 1385512 59964259 := bstep (se 1 (by rfl) ⟨44973194, by rfl⟩ : syracuseStep 59964259 = 89946389) B89946389
theorem B3332983 : Blo 1385512 3332983 := bstep (se 1 (by rfl) ⟨2499737, by rfl⟩ : syracuseStep 3332983 = 4999475) B4999475
theorem B3947399 : Blo 1385512 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B2079623 : Blo 1385512 2079623 := bstep (se 1 (by rfl) ⟨1559717, by rfl⟩ : syracuseStep 2079623 = 3119435) B3119435
theorem B2079659 : Blo 1385512 2079659 := bstep (se 1 (by rfl) ⟨1559744, by rfl⟩ : syracuseStep 2079659 = 3119489) B3119489
theorem B2079689 : Blo 1385512 2079689 := bstep (se 2 (by rfl) ⟨779883, by rfl⟩ : syracuseStep 2079689 = 1559767) B1559767
theorem B2079803 : Blo 1385512 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B4676669 : Blo 1385512 4676669 := bstep (se 3 (by rfl) ⟨876875, by rfl⟩ : syracuseStep 4676669 = 1753751) B1753751
theorem B2079863 : Blo 1385512 2079863 := bstep (se 1 (by rfl) ⟨1559897, by rfl⟩ : syracuseStep 2079863 = 3119795) B3119795
theorem B3120263 : Blo 1385512 3120263 := bstep (se 1 (by rfl) ⟨2340197, by rfl⟩ : syracuseStep 3120263 = 4680395) B4680395
theorem B2079887 : Blo 1385512 2079887 := bstep (se 1 (by rfl) ⟨1559915, by rfl⟩ : syracuseStep 2079887 = 3119831) B3119831
theorem B2079929 : Blo 1385512 2079929 := bstep (se 2 (by rfl) ⟨779973, by rfl⟩ : syracuseStep 2079929 = 1559947) B1559947
theorem B8879341 : Blo 1385512 8879341 := bstep (se 3 (by rfl) ⟨1664876, by rfl⟩ : syracuseStep 8879341 = 3329753) B3329753
theorem B2080007 : Blo 1385512 2080007 := bstep (se 1 (by rfl) ⟨1560005, by rfl⟩ : syracuseStep 2080007 = 3120011) B3120011
theorem B5266721 : Blo 1385512 5266721 := bstep (se 2 (by rfl) ⟨1975020, by rfl⟩ : syracuseStep 5266721 = 3950041) B3950041
theorem B2080043 : Blo 1385512 2080043 := bstep (se 1 (by rfl) ⟨1560032, by rfl⟩ : syracuseStep 2080043 = 3120065) B3120065
theorem B3120443 : Blo 1385512 3120443 := bstep (se 1 (by rfl) ⟨2340332, by rfl⟩ : syracuseStep 3120443 = 4680665) B4680665
theorem B2080073 : Blo 1385512 2080073 := bstep (se 2 (by rfl) ⟨780027, by rfl⟩ : syracuseStep 2080073 = 1560055) B1560055
theorem B4996505 : Blo 1385512 4996505 := bstep (se 2 (by rfl) ⟨1873689, by rfl⟩ : syracuseStep 4996505 = 3747379) B3747379
theorem B3120569 : Blo 1385512 3120569 := bstep (se 2 (by rfl) ⟨1170213, by rfl⟩ : syracuseStep 3120569 = 2340427) B2340427
theorem B2080187 : Blo 1385512 2080187 := bstep (se 1 (by rfl) ⟨1560140, by rfl⟩ : syracuseStep 2080187 = 3120281) B3120281
theorem B4996561 : Blo 1385512 4996561 := bstep (se 2 (by rfl) ⟨1873710, by rfl⟩ : syracuseStep 4996561 = 3747421) B3747421
theorem B2080247 : Blo 1385512 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B2080271 : Blo 1385512 2080271 := bstep (se 1 (by rfl) ⟨1560203, by rfl⟩ : syracuseStep 2080271 = 3120407) B3120407
theorem B15187499 : Blo 1385512 15187499 := bstep (se 1 (by rfl) ⟨11390624, by rfl⟩ : syracuseStep 15187499 = 22781249) B22781249
theorem B2080313 : Blo 1385512 2080313 := bstep (se 2 (by rfl) ⟨780117, by rfl⟩ : syracuseStep 2080313 = 1560235) B1560235
theorem B3161659 : Blo 1385512 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B2080391 : Blo 1385512 2080391 := bstep (se 1 (by rfl) ⟨1560293, by rfl⟩ : syracuseStep 2080391 = 3120587) B3120587
theorem B2080427 : Blo 1385512 2080427 := bstep (se 1 (by rfl) ⟨1560320, by rfl⟩ : syracuseStep 2080427 = 3120641) B3120641
theorem B2080457 : Blo 1385512 2080457 := bstep (se 2 (by rfl) ⟨780171, by rfl⟩ : syracuseStep 2080457 = 1560343) B1560343
theorem B7020269 : Blo 1385512 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B1974007 : Blo 1385512 1974007 := bstep (se 1 (by rfl) ⟨1480505, by rfl⟩ : syracuseStep 1974007 = 2961011) B2961011
theorem B3120911 : Blo 1385512 3120911 := bstep (se 1 (by rfl) ⟨2340683, by rfl⟩ : syracuseStep 3120911 = 4681367) B4681367
theorem B3120929 : Blo 1385512 3120929 := bstep (se 2 (by rfl) ⟨1170348, by rfl⟩ : syracuseStep 3120929 = 2340697) B2340697
theorem B8437537 : Blo 1385512 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B15785765 : Blo 1385512 15785765 := bstep (se 4 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 15785765 = 2959831) B2959831
theorem B2080571 : Blo 1385512 2080571 := bstep (se 1 (by rfl) ⟨1560428, by rfl⟩ : syracuseStep 2080571 = 3120857) B3120857
theorem B2080631 : Blo 1385512 2080631 := bstep (se 1 (by rfl) ⟨1560473, by rfl⟩ : syracuseStep 2080631 = 3120947) B3120947
theorem B2080655 : Blo 1385512 2080655 := bstep (se 1 (by rfl) ⟨1560491, by rfl⟩ : syracuseStep 2080655 = 3120983) B3120983
theorem B4997011 : Blo 1385512 4997011 := bstep (se 1 (by rfl) ⟨3747758, by rfl⟩ : syracuseStep 4997011 = 7495517) B7495517
theorem B2080697 : Blo 1385512 2080697 := bstep (se 2 (by rfl) ⟨780261, by rfl⟩ : syracuseStep 2080697 = 1560523) B1560523
theorem B2220041 : Blo 1385512 2220041 := bstep (se 2 (by rfl) ⟨832515, by rfl⟩ : syracuseStep 2220041 = 1665031) B1665031
theorem B2080847 : Blo 1385512 2080847 := bstep (se 1 (by rfl) ⟨1560635, by rfl⟩ : syracuseStep 2080847 = 3121271) B3121271
theorem B4677803 : Blo 1385512 4677803 := bstep (se 1 (by rfl) ⟨3508352, by rfl⟩ : syracuseStep 4677803 = 7016705) B7016705
theorem B2080967 : Blo 1385512 2080967 := bstep (se 1 (by rfl) ⟨1560725, by rfl⟩ : syracuseStep 2080967 = 3121451) B3121451
theorem B14426443 : Blo 1385512 14426443 := bstep (se 1 (by rfl) ⟨10819832, by rfl⟩ : syracuseStep 14426443 = 21639665) B21639665
theorem B2081129 : Blo 1385512 2081129 := bstep (se 2 (by rfl) ⟨780423, by rfl⟩ : syracuseStep 2081129 = 1560847) B1560847
theorem B3948925 : Blo 1385512 3948925 := bstep (se 3 (by rfl) ⟨740423, by rfl⟩ : syracuseStep 3948925 = 1480847) B1480847
theorem B2220463 : Blo 1385512 2220463 := bstep (se 1 (by rfl) ⟨1665347, by rfl⟩ : syracuseStep 2220463 = 3330695) B3330695
theorem B2081207 : Blo 1385512 2081207 := bstep (se 1 (by rfl) ⟨1560905, by rfl⟩ : syracuseStep 2081207 = 3121811) B3121811
theorem B2081243 : Blo 1385512 2081243 := bstep (se 1 (by rfl) ⟨1560932, by rfl⟩ : syracuseStep 2081243 = 3121865) B3121865
theorem B5620211 : Blo 1385512 5620211 := bstep (se 1 (by rfl) ⟨4215158, by rfl⟩ : syracuseStep 5620211 = 8430317) B8430317
theorem B1974793 : Blo 1385512 1974793 := bstep (se 2 (by rfl) ⟨740547, by rfl⟩ : syracuseStep 1974793 = 1481095) B1481095
theorem B3121703 : Blo 1385512 3121703 := bstep (se 1 (by rfl) ⟨2341277, by rfl⟩ : syracuseStep 3121703 = 4682555) B4682555
theorem B8430139 : Blo 1385512 8430139 := bstep (se 1 (by rfl) ⟨6322604, by rfl⟩ : syracuseStep 8430139 = 12645209) B12645209
theorem B85369463 : Blo 1385512 85369463 := bstep (se 1 (by rfl) ⟨64027097, by rfl⟩ : syracuseStep 85369463 = 128054195) B128054195
theorem B7021241 : Blo 1385512 7021241 := bstep (se 2 (by rfl) ⟨2632965, by rfl⟩ : syracuseStep 7021241 = 5265931) B5265931
theorem B4678343 : Blo 1385512 4678343 := bstep (se 1 (by rfl) ⟨3508757, by rfl⟩ : syracuseStep 4678343 = 7017515) B7017515
theorem B4809415 : Blo 1385512 4809415 := bstep (se 1 (by rfl) ⟨3607061, by rfl⟩ : syracuseStep 4809415 = 7214123) B7214123
theorem B5268179 : Blo 1385512 5268179 := bstep (se 1 (by rfl) ⟨3951134, by rfl⟩ : syracuseStep 5268179 = 7902269) B7902269
theorem B5407607 : Blo 1385512 5407607 := bstep (se 1 (by rfl) ⟨4055705, by rfl⟩ : syracuseStep 5407607 = 8111411) B8111411
theorem B10675127 : Blo 1385512 10675127 := bstep (se 1 (by rfl) ⟨8006345, by rfl⟩ : syracuseStep 10675127 = 16012691) B16012691
theorem B1754075 : Blo 1385512 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B12166145 : Blo 1385512 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B78996491 : Blo 1385512 78996491 := bstep (se 1 (by rfl) ⟨59247368, by rfl⟩ : syracuseStep 78996491 = 118494737) B118494737
theorem B15205427 : Blo 1385512 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B14992451 : Blo 1385512 14992451 := bstep (se 1 (by rfl) ⟨11244338, by rfl⟩ : syracuseStep 14992451 = 22488677) B22488677
theorem B1385551 : Blo 1385512 1385551 := bstep (se 1 (by rfl) ⟨1039163, by rfl⟩ : syracuseStep 1385551 = 2078327) B2078327
theorem B1385567 : Blo 1385512 1385567 := bstep (se 1 (by rfl) ⟨1039175, by rfl⟩ : syracuseStep 1385567 = 2078351) B2078351
theorem B1385595 : Blo 1385512 1385595 := bstep (se 1 (by rfl) ⟨1039196, by rfl⟩ : syracuseStep 1385595 = 2078393) B2078393
theorem B3507371 : Blo 1385512 3507371 := bstep (se 1 (by rfl) ⟨2630528, by rfl⟩ : syracuseStep 3507371 = 5261057) B5261057
theorem B1385647 : Blo 1385512 1385647 := bstep (se 1 (by rfl) ⟨1039235, by rfl⟩ : syracuseStep 1385647 = 2078471) B2078471
theorem B1385671 : Blo 1385512 1385671 := bstep (se 1 (by rfl) ⟨1039253, by rfl⟩ : syracuseStep 1385671 = 2078507) B2078507
theorem B2630855 : Blo 1385512 2630855 := bstep (se 1 (by rfl) ⟨1973141, by rfl⟩ : syracuseStep 2630855 = 3946283) B3946283
theorem B1385691 : Blo 1385512 1385691 := bstep (se 1 (by rfl) ⟨1039268, by rfl⟩ : syracuseStep 1385691 = 2078537) B2078537
theorem B9487631 : Blo 1385512 9487631 := bstep (se 1 (by rfl) ⟨7115723, by rfl⟩ : syracuseStep 9487631 = 14231447) B14231447
theorem B1385767 : Blo 1385512 1385767 := bstep (se 1 (by rfl) ⟨1039325, by rfl⟩ : syracuseStep 1385767 = 2078651) B2078651
theorem B1385807 : Blo 1385512 1385807 := bstep (se 1 (by rfl) ⟨1039355, by rfl⟩ : syracuseStep 1385807 = 2078711) B2078711
theorem B1385823 : Blo 1385512 1385823 := bstep (se 1 (by rfl) ⟨1039367, by rfl⟩ : syracuseStep 1385823 = 2078735) B2078735
theorem B1385851 : Blo 1385512 1385851 := bstep (se 1 (by rfl) ⟨1039388, by rfl⟩ : syracuseStep 1385851 = 2078777) B2078777
theorem B2925967 : Blo 1385512 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B1385903 : Blo 1385512 1385903 := bstep (se 1 (by rfl) ⟨1039427, by rfl⟩ : syracuseStep 1385903 = 2078855) B2078855
theorem B1754551 : Blo 1385512 1754551 := bstep (se 1 (by rfl) ⟨1315913, by rfl⟩ : syracuseStep 1754551 = 2631827) B2631827
theorem B1385927 : Blo 1385512 1385927 := bstep (se 1 (by rfl) ⟨1039445, by rfl⟩ : syracuseStep 1385927 = 2078891) B2078891
theorem B1385947 : Blo 1385512 1385947 := bstep (se 1 (by rfl) ⟨1039460, by rfl⟩ : syracuseStep 1385947 = 2078921) B2078921
theorem B1386023 : Blo 1385512 1386023 := bstep (se 1 (by rfl) ⟨1039517, by rfl⟩ : syracuseStep 1386023 = 2079035) B2079035
theorem B4679207 : Blo 1385512 4679207 := bstep (se 1 (by rfl) ⟨3509405, by rfl⟩ : syracuseStep 4679207 = 7018811) B7018811
theorem B5260859 : Blo 1385512 5260859 := bstep (se 1 (by rfl) ⟨3945644, by rfl⟩ : syracuseStep 5260859 = 7891289) B7891289
theorem B1386063 : Blo 1385512 1386063 := bstep (se 1 (by rfl) ⟨1039547, by rfl⟩ : syracuseStep 1386063 = 2079095) B2079095
theorem B1386079 : Blo 1385512 1386079 := bstep (se 1 (by rfl) ⟨1039559, by rfl⟩ : syracuseStep 1386079 = 2079119) B2079119
theorem B1386107 : Blo 1385512 1386107 := bstep (se 1 (by rfl) ⟨1039580, by rfl⟩ : syracuseStep 1386107 = 2079161) B2079161
theorem B11839121 : Blo 1385512 11839121 := bstep (se 2 (by rfl) ⟨4439670, by rfl⟩ : syracuseStep 11839121 = 8879341) B8879341
theorem B4679315 : Blo 1385512 4679315 := bstep (se 1 (by rfl) ⟨3509486, by rfl⟩ : syracuseStep 4679315 = 7018973) B7018973
theorem B1386159 : Blo 1385512 1386159 := bstep (se 1 (by rfl) ⟨1039619, by rfl⟩ : syracuseStep 1386159 = 2079239) B2079239
theorem B1386183 : Blo 1385512 1386183 := bstep (se 1 (by rfl) ⟨1039637, by rfl⟩ : syracuseStep 1386183 = 2079275) B2079275
theorem B2631379 : Blo 1385512 2631379 := bstep (se 1 (by rfl) ⟨1973534, by rfl⟩ : syracuseStep 2631379 = 3947069) B3947069
theorem B1386203 : Blo 1385512 1386203 := bstep (se 1 (by rfl) ⟨1039652, by rfl⟩ : syracuseStep 1386203 = 2079305) B2079305
theorem B1386279 : Blo 1385512 1386279 := bstep (se 1 (by rfl) ⟨1039709, by rfl⟩ : syracuseStep 1386279 = 2079419) B2079419
theorem B1386319 : Blo 1385512 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B1386335 : Blo 1385512 1386335 := bstep (se 1 (by rfl) ⟨1039751, by rfl⟩ : syracuseStep 1386335 = 2079503) B2079503
theorem B4679531 : Blo 1385512 4679531 := bstep (se 1 (by rfl) ⟨3509648, by rfl⟩ : syracuseStep 4679531 = 7019297) B7019297
theorem B1386363 : Blo 1385512 1386363 := bstep (se 1 (by rfl) ⟨1039772, by rfl⟩ : syracuseStep 1386363 = 2079545) B2079545
theorem B4679585 : Blo 1385512 4679585 := bstep (se 2 (by rfl) ⟨1754844, by rfl⟩ : syracuseStep 4679585 = 3509689) B3509689
theorem B2631599 : Blo 1385512 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B1386415 : Blo 1385512 1386415 := bstep (se 1 (by rfl) ⟨1039811, by rfl⟩ : syracuseStep 1386415 = 2079623) B2079623
theorem B6662081 : Blo 1385512 6662081 := bstep (se 2 (by rfl) ⟨2498280, by rfl⟩ : syracuseStep 6662081 = 4996561) B4996561
theorem B1386439 : Blo 1385512 1386439 := bstep (se 1 (by rfl) ⟨1039829, by rfl⟩ : syracuseStep 1386439 = 2079659) B2079659
theorem B1386459 : Blo 1385512 1386459 := bstep (se 1 (by rfl) ⟨1039844, by rfl⟩ : syracuseStep 1386459 = 2079689) B2079689
theorem B3508231 : Blo 1385512 3508231 := bstep (se 1 (by rfl) ⟨2631173, by rfl⟩ : syracuseStep 3508231 = 5262347) B5262347
theorem B4442131 : Blo 1385512 4442131 := bstep (se 1 (by rfl) ⟨3331598, by rfl⟩ : syracuseStep 4442131 = 6663197) B6663197
theorem B1386535 : Blo 1385512 1386535 := bstep (se 1 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 1386535 = 2079803) B2079803
theorem B1386575 : Blo 1385512 1386575 := bstep (se 1 (by rfl) ⟨1039931, by rfl⟩ : syracuseStep 1386575 = 2079863) B2079863
theorem B1386591 : Blo 1385512 1386591 := bstep (se 1 (by rfl) ⟨1039943, by rfl⟩ : syracuseStep 1386591 = 2079887) B2079887
theorem B1386619 : Blo 1385512 1386619 := bstep (se 1 (by rfl) ⟨1039964, by rfl⟩ : syracuseStep 1386619 = 2079929) B2079929
theorem B1386671 : Blo 1385512 1386671 := bstep (se 1 (by rfl) ⟨1040003, by rfl⟩ : syracuseStep 1386671 = 2080007) B2080007
theorem B1386695 : Blo 1385512 1386695 := bstep (se 1 (by rfl) ⟨1040021, by rfl⟩ : syracuseStep 1386695 = 2080043) B2080043
theorem B1386715 : Blo 1385512 1386715 := bstep (se 1 (by rfl) ⟨1040036, by rfl⟩ : syracuseStep 1386715 = 2080073) B2080073
theorem B1386791 : Blo 1385512 1386791 := bstep (se 1 (by rfl) ⟨1040093, by rfl⟩ : syracuseStep 1386791 = 2080187) B2080187
theorem B2632009 : Blo 1385512 2632009 := bstep (se 2 (by rfl) ⟨987003, by rfl⟩ : syracuseStep 2632009 = 1974007) B1974007
theorem B1386831 : Blo 1385512 1386831 := bstep (se 1 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 1386831 = 2080247) B2080247
theorem B1386847 : Blo 1385512 1386847 := bstep (se 1 (by rfl) ⟨1040135, by rfl⟩ : syracuseStep 1386847 = 2080271) B2080271
theorem B7014761 : Blo 1385512 7014761 := bstep (se 2 (by rfl) ⟨2630535, by rfl⟩ : syracuseStep 7014761 = 5261071) B5261071
theorem B1386875 : Blo 1385512 1386875 := bstep (se 1 (by rfl) ⟨1040156, by rfl⟩ : syracuseStep 1386875 = 2080313) B2080313
theorem B11250049 : Blo 1385512 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B3000719 : Blo 1385512 3000719 := bstep (se 1 (by rfl) ⟨2250539, by rfl⟩ : syracuseStep 3000719 = 4501079) B4501079
theorem B1386927 : Blo 1385512 1386927 := bstep (se 1 (by rfl) ⟨1040195, by rfl⟩ : syracuseStep 1386927 = 2080391) B2080391
theorem B1386951 : Blo 1385512 1386951 := bstep (se 1 (by rfl) ⟨1040213, by rfl⟩ : syracuseStep 1386951 = 2080427) B2080427
theorem B1386971 : Blo 1385512 1386971 := bstep (se 1 (by rfl) ⟨1040228, by rfl⟩ : syracuseStep 1386971 = 2080457) B2080457
theorem B4680179 : Blo 1385512 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B6662681 : Blo 1385512 6662681 := bstep (se 2 (by rfl) ⟨2498505, by rfl⟩ : syracuseStep 6662681 = 4997011) B4997011
theorem B1387047 : Blo 1385512 1387047 := bstep (se 1 (by rfl) ⟨1040285, by rfl⟩ : syracuseStep 1387047 = 2080571) B2080571
theorem B1559119 : Blo 1385512 1559119 := bstep (se 1 (by rfl) ⟨1169339, by rfl⟩ : syracuseStep 1559119 = 2338679) B2338679
theorem B1387087 : Blo 1385512 1387087 := bstep (se 1 (by rfl) ⟨1040315, by rfl⟩ : syracuseStep 1387087 = 2080631) B2080631
theorem B1387103 : Blo 1385512 1387103 := bstep (se 1 (by rfl) ⟨1040327, by rfl⟩ : syracuseStep 1387103 = 2080655) B2080655
theorem B3508859 : Blo 1385512 3508859 := bstep (se 1 (by rfl) ⟨2631644, by rfl⟩ : syracuseStep 3508859 = 5263289) B5263289
theorem B1387131 : Blo 1385512 1387131 := bstep (se 1 (by rfl) ⟨1040348, by rfl⟩ : syracuseStep 1387131 = 2080697) B2080697
theorem B1387183 : Blo 1385512 1387183 := bstep (se 1 (by rfl) ⟨1040387, by rfl⟩ : syracuseStep 1387183 = 2080775) B2080775
theorem B1387207 : Blo 1385512 1387207 := bstep (se 1 (by rfl) ⟨1040405, by rfl⟩ : syracuseStep 1387207 = 2080811) B2080811
theorem B1755847 : Blo 1385512 1755847 := bstep (se 1 (by rfl) ⟨1316885, by rfl⟩ : syracuseStep 1755847 = 2633771) B2633771
theorem B1387227 : Blo 1385512 1387227 := bstep (se 1 (by rfl) ⟨1040420, by rfl⟩ : syracuseStep 1387227 = 2080841) B2080841
theorem B1387303 : Blo 1385512 1387303 := bstep (se 1 (by rfl) ⟨1040477, by rfl⟩ : syracuseStep 1387303 = 2080955) B2080955
theorem B1387343 : Blo 1385512 1387343 := bstep (se 1 (by rfl) ⟨1040507, by rfl⟩ : syracuseStep 1387343 = 2081015) B2081015
theorem B1387359 : Blo 1385512 1387359 := bstep (se 1 (by rfl) ⟨1040519, by rfl⟩ : syracuseStep 1387359 = 2081039) B2081039
theorem B1387387 : Blo 1385512 1387387 := bstep (se 1 (by rfl) ⟨1040540, by rfl⟩ : syracuseStep 1387387 = 2081081) B2081081
theorem B3509153 : Blo 1385512 3509153 := bstep (se 2 (by rfl) ⟨1315932, by rfl⟩ : syracuseStep 3509153 = 2631865) B2631865
theorem B5622689 : Blo 1385512 5622689 := bstep (se 2 (by rfl) ⟨2108508, by rfl⟩ : syracuseStep 5622689 = 4217017) B4217017
theorem B1387439 : Blo 1385512 1387439 := bstep (se 1 (by rfl) ⟨1040579, by rfl⟩ : syracuseStep 1387439 = 2081159) B2081159
theorem B1387463 : Blo 1385512 1387463 := bstep (se 1 (by rfl) ⟨1040597, by rfl⟩ : syracuseStep 1387463 = 2081195) B2081195
theorem B1559515 : Blo 1385512 1559515 := bstep (se 1 (by rfl) ⟨1169636, by rfl⟩ : syracuseStep 1559515 = 2339273) B2339273
theorem B1387483 : Blo 1385512 1387483 := bstep (se 1 (by rfl) ⟨1040612, by rfl⟩ : syracuseStep 1387483 = 2081225) B2081225
theorem B4680719 : Blo 1385512 4680719 := bstep (se 1 (by rfl) ⟨3510539, by rfl⟩ : syracuseStep 4680719 = 7021079) B7021079
theorem B9481283 : Blo 1385512 9481283 := bstep (se 1 (by rfl) ⟨7110962, by rfl⟩ : syracuseStep 9481283 = 14221925) B14221925
theorem B3329195 : Blo 1385512 3329195 := bstep (se 1 (by rfl) ⟨2496896, by rfl⟩ : syracuseStep 3329195 = 4993793) B4993793
theorem B12651713 : Blo 1385512 12651713 := bstep (se 2 (by rfl) ⟨4744392, by rfl⟩ : syracuseStep 12651713 = 9488785) B9488785
theorem B7900355 : Blo 1385512 7900355 := bstep (se 1 (by rfl) ⟨5925266, by rfl⟩ : syracuseStep 7900355 = 11850533) B11850533
theorem B1559983 : Blo 1385512 1559983 := bstep (se 1 (by rfl) ⟨1169987, by rfl⟩ : syracuseStep 1559983 = 2339975) B2339975
theorem B2338267 : Blo 1385512 2338267 := bstep (se 1 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 2338267 = 3507401) B3507401
theorem B17763907 : Blo 1385512 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B2960993 : Blo 1385512 2960993 := bstep (se 2 (by rfl) ⟨1110372, by rfl⟩ : syracuseStep 2960993 = 2220745) B2220745
theorem B4681313 : Blo 1385512 4681313 := bstep (se 2 (by rfl) ⟨1755492, by rfl⟩ : syracuseStep 4681313 = 3510985) B3510985
theorem B7900811 : Blo 1385512 7900811 := bstep (se 1 (by rfl) ⟨5925608, by rfl⟩ : syracuseStep 7900811 = 11851217) B11851217
theorem B10677905 : Blo 1385512 10677905 := bstep (se 2 (by rfl) ⟨4004214, by rfl⟩ : syracuseStep 10677905 = 8008429) B8008429
theorem B4443977 : Blo 1385512 4443977 := bstep (se 2 (by rfl) ⟨1666491, by rfl⟩ : syracuseStep 4443977 = 3332983) B3332983
theorem B1560415 : Blo 1385512 1560415 := bstep (se 1 (by rfl) ⟨1170311, by rfl⟩ : syracuseStep 1560415 = 2340623) B2340623
theorem B2961335 : Blo 1385512 2961335 := bstep (se 1 (by rfl) ⟨2221001, by rfl⟩ : syracuseStep 2961335 = 4442003) B4442003
theorem B2338895 : Blo 1385512 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B8884313 : Blo 1385512 8884313 := bstep (se 2 (by rfl) ⟨3331617, by rfl⟩ : syracuseStep 8884313 = 6663235) B6663235
theorem B1560775 : Blo 1385512 1560775 := bstep (se 1 (by rfl) ⟨1170581, by rfl⟩ : syracuseStep 1560775 = 2341163) B2341163
theorem B10531133 : Blo 1385512 10531133 := bstep (se 3 (by rfl) ⟨1974587, by rfl⟩ : syracuseStep 10531133 = 3949175) B3949175
theorem B17772929 : Blo 1385512 17772929 := bstep (se 2 (by rfl) ⟨6664848, by rfl⟩ : syracuseStep 17772929 = 13329697) B13329697
theorem B3117455 : Blo 1385512 3117455 := bstep (se 1 (by rfl) ⟨2338091, by rfl⟩ : syracuseStep 3117455 = 4676183) B4676183
theorem B3510823 : Blo 1385512 3510823 := bstep (se 1 (by rfl) ⟨2633117, by rfl⟩ : syracuseStep 3510823 = 5266235) B5266235
theorem B4993595 : Blo 1385512 4993595 := bstep (se 1 (by rfl) ⟨3745196, by rfl⟩ : syracuseStep 4993595 = 7490393) B7490393
theorem B3117779 : Blo 1385512 3117779 := bstep (se 1 (by rfl) ⟨2338334, by rfl⟩ : syracuseStep 3117779 = 4676669) B4676669
theorem B4215545 : Blo 1385512 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B3511147 : Blo 1385512 3511147 := bstep (se 1 (by rfl) ⟨2633360, by rfl⟩ : syracuseStep 3511147 = 5266721) B5266721
theorem B2339759 : Blo 1385512 2339759 := bstep (se 1 (by rfl) ⟨1754819, by rfl⟩ : syracuseStep 2339759 = 3509639) B3509639
theorem B3331003 : Blo 1385512 3331003 := bstep (se 1 (by rfl) ⟨2498252, by rfl⟩ : syracuseStep 3331003 = 4996505) B4996505
theorem B11391965 : Blo 1385512 11391965 := bstep (se 3 (by rfl) ⟨2135993, by rfl⟩ : syracuseStep 11391965 = 4271987) B4271987
theorem B8885213 : Blo 1385512 8885213 := bstep (se 3 (by rfl) ⟨1665977, by rfl⟩ : syracuseStep 8885213 = 3331955) B3331955
theorem B4682771 : Blo 1385512 4682771 := bstep (se 1 (by rfl) ⟨3512078, by rfl⟩ : syracuseStep 4682771 = 7024157) B7024157
theorem B9999409 : Blo 1385512 9999409 := bstep (se 2 (by rfl) ⟨3749778, by rfl⟩ : syracuseStep 9999409 = 7499557) B7499557
theorem B2962489 : Blo 1385512 2962489 := bstep (se 2 (by rfl) ⟨1110933, by rfl⟩ : syracuseStep 2962489 = 2221867) B2221867
theorem B4994243 : Blo 1385512 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B10523843 : Blo 1385512 10523843 := bstep (se 1 (by rfl) ⟨7892882, by rfl⟩ : syracuseStep 10523843 = 15785765) B15785765
theorem B2340191 : Blo 1385512 2340191 := bstep (se 1 (by rfl) ⟨1755143, by rfl⟩ : syracuseStep 2340191 = 3510287) B3510287
theorem B2962831 : Blo 1385512 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B2962907 : Blo 1385512 2962907 := bstep (se 1 (by rfl) ⟨2222180, by rfl⟩ : syracuseStep 2962907 = 4444361) B4444361
theorem B3511795 : Blo 1385512 3511795 := bstep (se 1 (by rfl) ⟨2633846, by rfl⟩ : syracuseStep 3511795 = 5267693) B5267693
theorem B3946009 : Blo 1385512 3946009 := bstep (se 2 (by rfl) ⟨1479753, by rfl⟩ : syracuseStep 3946009 = 2959507) B2959507
theorem B3118715 : Blo 1385512 3118715 := bstep (se 1 (by rfl) ⟨2339036, by rfl⟩ : syracuseStep 3118715 = 4678073) B4678073
theorem B39990935 : Blo 1385512 39990935 := bstep (se 1 (by rfl) ⟨29993201, by rfl⟩ : syracuseStep 39990935 = 59986403) B59986403
theorem B2283179 : Blo 1385512 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B4216519 : Blo 1385512 4216519 := bstep (se 1 (by rfl) ⟨3162389, by rfl⟩ : syracuseStep 4216519 = 6324779) B6324779
theorem B3118841 : Blo 1385512 3118841 := bstep (se 2 (by rfl) ⟨1169565, by rfl⟩ : syracuseStep 3118841 = 2339131) B2339131
theorem B6666079 : Blo 1385512 6666079 := bstep (se 1 (by rfl) ⟨4999559, by rfl⟩ : syracuseStep 6666079 = 9999119) B9999119
theorem B2340751 : Blo 1385512 2340751 := bstep (se 1 (by rfl) ⟨1755563, by rfl⟩ : syracuseStep 2340751 = 3511127) B3511127
theorem B2078639 : Blo 1385512 2078639 := bstep (se 1 (by rfl) ⟨1558979, by rfl⟩ : syracuseStep 2078639 = 3117959) B3117959
theorem B4216751 : Blo 1385512 4216751 := bstep (se 1 (by rfl) ⟨3162563, by rfl⟩ : syracuseStep 4216751 = 6325127) B6325127
theorem B3119111 : Blo 1385512 3119111 := bstep (se 1 (by rfl) ⟨2339333, by rfl⟩ : syracuseStep 3119111 = 4678667) B4678667
theorem B2078729 : Blo 1385512 2078729 := bstep (se 2 (by rfl) ⟨779523, by rfl⟩ : syracuseStep 2078729 = 1559047) B1559047
theorem B2078759 : Blo 1385512 2078759 := bstep (se 1 (by rfl) ⟨1559069, by rfl⟩ : syracuseStep 2078759 = 3118139) B3118139
theorem B3119183 : Blo 1385512 3119183 := bstep (se 1 (by rfl) ⟨2339387, by rfl⟩ : syracuseStep 3119183 = 4678775) B4678775
theorem B2078843 : Blo 1385512 2078843 := bstep (se 1 (by rfl) ⟨1559132, by rfl⟩ : syracuseStep 2078843 = 3118265) B3118265
theorem B2078969 : Blo 1385512 2078969 := bstep (se 2 (by rfl) ⟨779613, by rfl⟩ : syracuseStep 2078969 = 1559227) B1559227
theorem B2079071 : Blo 1385512 2079071 := bstep (se 1 (by rfl) ⟨1559303, by rfl⟩ : syracuseStep 2079071 = 3118607) B3118607
theorem B2079083 : Blo 1385512 2079083 := bstep (se 1 (by rfl) ⟨1559312, by rfl⟩ : syracuseStep 2079083 = 3118625) B3118625
theorem B19995011 : Blo 1385512 19995011 := bstep (se 1 (by rfl) ⟨14996258, by rfl⟩ : syracuseStep 19995011 = 29992517) B29992517
theorem B79952345 : Blo 1385512 79952345 := bstep (se 2 (by rfl) ⟨29982129, by rfl⟩ : syracuseStep 79952345 = 59964259) B59964259
theorem B3119579 : Blo 1385512 3119579 := bstep (se 1 (by rfl) ⟨2339684, by rfl⟩ : syracuseStep 3119579 = 4679369) B4679369
theorem B4676129 : Blo 1385512 4676129 := bstep (se 2 (by rfl) ⟨1753548, by rfl⟩ : syracuseStep 4676129 = 3507097) B3507097
theorem B2079311 : Blo 1385512 2079311 := bstep (se 1 (by rfl) ⟨1559483, by rfl⟩ : syracuseStep 2079311 = 3118967) B3118967
theorem B6666887 : Blo 1385512 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B5339783 : Blo 1385512 5339783 := bstep (se 1 (by rfl) ⟨4004837, by rfl⟩ : syracuseStep 5339783 = 8009675) B8009675
theorem B2079431 : Blo 1385512 2079431 := bstep (se 1 (by rfl) ⟨1559573, by rfl⟩ : syracuseStep 2079431 = 3119147) B3119147
theorem B4676345 : Blo 1385512 4676345 := bstep (se 2 (by rfl) ⟨1753629, by rfl⟩ : syracuseStep 4676345 = 3507259) B3507259
theorem B4438813 : Blo 1385512 4438813 := bstep (se 3 (by rfl) ⟨832277, by rfl⟩ : syracuseStep 4438813 = 1664555) B1664555
theorem B5266205 : Blo 1385512 5266205 := bstep (se 3 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 5266205 = 1974827) B1974827
theorem B17775389 : Blo 1385512 17775389 := bstep (se 3 (by rfl) ⟨3332885, by rfl⟩ : syracuseStep 17775389 = 6665771) B6665771
theorem B2079593 : Blo 1385512 2079593 := bstep (se 2 (by rfl) ⟨779847, by rfl⟩ : syracuseStep 2079593 = 1559695) B1559695
theorem B3160939 : Blo 1385512 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B3120047 : Blo 1385512 3120047 := bstep (se 1 (by rfl) ⟨2340035, by rfl⟩ : syracuseStep 3120047 = 4680071) B4680071
theorem B2079671 : Blo 1385512 2079671 := bstep (se 1 (by rfl) ⟨1559753, by rfl⟩ : syracuseStep 2079671 = 3119507) B3119507
theorem B2079707 : Blo 1385512 2079707 := bstep (se 1 (by rfl) ⟨1559780, by rfl⟩ : syracuseStep 2079707 = 3119561) B3119561
theorem B4676615 : Blo 1385512 4676615 := bstep (se 1 (by rfl) ⟨3507461, by rfl⟩ : syracuseStep 4676615 = 7014923) B7014923
theorem B4676723 : Blo 1385512 4676723 := bstep (se 1 (by rfl) ⟨3507542, by rfl⟩ : syracuseStep 4676723 = 7015085) B7015085
theorem B3120299 : Blo 1385512 3120299 := bstep (se 1 (by rfl) ⟨2340224, by rfl⟩ : syracuseStep 3120299 = 4680449) B4680449
theorem B11852993 : Blo 1385512 11852993 := bstep (se 2 (by rfl) ⟨4444872, by rfl⟩ : syracuseStep 11852993 = 8889745) B8889745
theorem B13319549 : Blo 1385512 13319549 := bstep (se 3 (by rfl) ⟨2497415, by rfl⟩ : syracuseStep 13319549 = 4994831) B4994831
theorem B4676993 : Blo 1385512 4676993 := bstep (se 2 (by rfl) ⟨1753872, by rfl⟩ : syracuseStep 4676993 = 3507745) B3507745
theorem B2080175 : Blo 1385512 2080175 := bstep (se 1 (by rfl) ⟨1560131, by rfl⟩ : syracuseStep 2080175 = 3120263) B3120263
theorem B5266889 : Blo 1385512 5266889 := bstep (se 2 (by rfl) ⟨1975083, by rfl⟩ : syracuseStep 5266889 = 3950167) B3950167
theorem B2080265 : Blo 1385512 2080265 := bstep (se 2 (by rfl) ⟨780099, by rfl⟩ : syracuseStep 2080265 = 1560199) B1560199
theorem B2080295 : Blo 1385512 2080295 := bstep (se 1 (by rfl) ⟨1560221, by rfl⟩ : syracuseStep 2080295 = 3120443) B3120443
theorem B2080379 : Blo 1385512 2080379 := bstep (se 1 (by rfl) ⟨1560284, by rfl⟩ : syracuseStep 2080379 = 3120569) B3120569
theorem B10124999 : Blo 1385512 10124999 := bstep (se 1 (by rfl) ⟨7593749, by rfl⟩ : syracuseStep 10124999 = 15187499) B15187499
theorem B3120839 : Blo 1385512 3120839 := bstep (se 1 (by rfl) ⟨2340629, by rfl⟩ : syracuseStep 3120839 = 4681259) B4681259
theorem B2080505 : Blo 1385512 2080505 := bstep (se 2 (by rfl) ⟨780189, by rfl⟩ : syracuseStep 2080505 = 1560379) B1560379
theorem B10673963 : Blo 1385512 10673963 := bstep (se 1 (by rfl) ⟨8005472, by rfl⟩ : syracuseStep 10673963 = 16010945) B16010945
theorem B2080607 : Blo 1385512 2080607 := bstep (se 1 (by rfl) ⟨1560455, by rfl⟩ : syracuseStep 2080607 = 3120911) B3120911
theorem B2080619 : Blo 1385512 2080619 := bstep (se 1 (by rfl) ⟨1560464, by rfl⟩ : syracuseStep 2080619 = 3120929) B3120929
theorem B5267375 : Blo 1385512 5267375 := bstep (se 1 (by rfl) ⟨3950531, by rfl⟩ : syracuseStep 5267375 = 7901063) B7901063
theorem B2809787 : Blo 1385512 2809787 := bstep (se 1 (by rfl) ⟨2107340, by rfl⟩ : syracuseStep 2809787 = 4214681) B4214681
theorem B1974235 : Blo 1385512 1974235 := bstep (se 1 (by rfl) ⟨1480676, by rfl⟩ : syracuseStep 1974235 = 2961353) B2961353
theorem B4677641 : Blo 1385512 4677641 := bstep (se 2 (by rfl) ⟨1754115, by rfl⟩ : syracuseStep 4677641 = 3508231) B3508231
theorem B5922841 : Blo 1385512 5922841 := bstep (se 2 (by rfl) ⟨2221065, by rfl⟩ : syracuseStep 5922841 = 4442131) B4442131
theorem B5922875 : Blo 1385512 5922875 := bstep (se 1 (by rfl) ⟨4442156, by rfl⟩ : syracuseStep 5922875 = 8884313) B8884313
theorem B7020755 : Blo 1385512 7020755 := bstep (se 1 (by rfl) ⟨5265566, by rfl⟩ : syracuseStep 7020755 = 10531133) B10531133
theorem B2081033 : Blo 1385512 2081033 := bstep (se 2 (by rfl) ⟨780387, by rfl⟩ : syracuseStep 2081033 = 1560775) B1560775
theorem B2081135 : Blo 1385512 2081135 := bstep (se 1 (by rfl) ⟨1560851, by rfl⟩ : syracuseStep 2081135 = 3121703) B3121703
theorem B15000065 : Blo 1385512 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B7594643 : Blo 1385512 7594643 := bstep (se 1 (by rfl) ⟨5695982, by rfl⟩ : syracuseStep 7594643 = 11391965) B11391965
theorem B5923475 : Blo 1385512 5923475 := bstep (se 1 (by rfl) ⟨4442606, by rfl⟩ : syracuseStep 5923475 = 8885213) B8885213
theorem B8110763 : Blo 1385512 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B3121847 : Blo 1385512 3121847 := bstep (se 1 (by rfl) ⟨2341385, by rfl⟩ : syracuseStep 3121847 = 4682771) B4682771
theorem B9994967 : Blo 1385512 9994967 := bstep (se 1 (by rfl) ⟨7496225, by rfl⟩ : syracuseStep 9994967 = 14992451) B14992451
theorem B1753903 : Blo 1385512 1753903 := bstep (se 1 (by rfl) ⟨1315427, by rfl⟩ : syracuseStep 1753903 = 2630855) B2630855
theorem B6325087 : Blo 1385512 6325087 := bstep (se 1 (by rfl) ⟨4743815, by rfl⟩ : syracuseStep 6325087 = 9487631) B9487631
theorem B1975271 : Blo 1385512 1975271 := bstep (se 1 (by rfl) ⟨1481453, by rfl⟩ : syracuseStep 1975271 = 2962907) B2962907
theorem B22488101 : Blo 1385512 22488101 := bstep (se 4 (by rfl) ⟨2108259, by rfl⟩ : syracuseStep 22488101 = 4216519) B4216519
theorem B3507239 : Blo 1385512 3507239 := bstep (se 1 (by rfl) ⟨2630429, by rfl⟩ : syracuseStep 3507239 = 5260859) B5260859
theorem B4441337 : Blo 1385512 4441337 := bstep (se 2 (by rfl) ⟨1665501, by rfl⟩ : syracuseStep 4441337 = 3331003) B3331003
theorem B1385759 : Blo 1385512 1385759 := bstep (se 1 (by rfl) ⟨1039319, by rfl⟩ : syracuseStep 1385759 = 2078639) B2078639
theorem B1754399 : Blo 1385512 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B2811167 : Blo 1385512 2811167 := bstep (se 1 (by rfl) ⟨2108375, by rfl⟩ : syracuseStep 2811167 = 4216751) B4216751
theorem B4441387 : Blo 1385512 4441387 := bstep (se 1 (by rfl) ⟨3331040, by rfl⟩ : syracuseStep 4441387 = 6662081) B6662081
theorem B1385819 : Blo 1385512 1385819 := bstep (se 1 (by rfl) ⟨1039364, by rfl⟩ : syracuseStep 1385819 = 2078729) B2078729
theorem B1385839 : Blo 1385512 1385839 := bstep (se 1 (by rfl) ⟨1039379, by rfl⟩ : syracuseStep 1385839 = 2078759) B2078759
theorem B3949985 : Blo 1385512 3949985 := bstep (se 2 (by rfl) ⟨1481244, by rfl⟩ : syracuseStep 3949985 = 2962489) B2962489
theorem B1385895 : Blo 1385512 1385895 := bstep (se 1 (by rfl) ⟨1039421, by rfl⟩ : syracuseStep 1385895 = 2078843) B2078843
theorem B1385979 : Blo 1385512 1385979 := bstep (se 1 (by rfl) ⟨1039484, by rfl⟩ : syracuseStep 1385979 = 2078969) B2078969
theorem B1386047 : Blo 1385512 1386047 := bstep (se 1 (by rfl) ⟨1039535, by rfl⟩ : syracuseStep 1386047 = 2079071) B2079071
theorem B1386055 : Blo 1385512 1386055 := bstep (se 1 (by rfl) ⟨1039541, by rfl⟩ : syracuseStep 1386055 = 2079083) B2079083
theorem B13330007 : Blo 1385512 13330007 := bstep (se 1 (by rfl) ⟨9997505, by rfl⟩ : syracuseStep 13330007 = 19995011) B19995011
theorem B2000479 : Blo 1385512 2000479 := bstep (se 1 (by rfl) ⟨1500359, by rfl⟩ : syracuseStep 2000479 = 3000719) B3000719
theorem B4441787 : Blo 1385512 4441787 := bstep (se 1 (by rfl) ⟨3331340, by rfl⟩ : syracuseStep 4441787 = 6662681) B6662681
theorem B17778365 : Blo 1385512 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B14239421 : Blo 1385512 14239421 := bstep (se 3 (by rfl) ⟨2669891, by rfl⟩ : syracuseStep 14239421 = 5339783) B5339783
theorem B1386207 : Blo 1385512 1386207 := bstep (se 1 (by rfl) ⟨1039655, by rfl⟩ : syracuseStep 1386207 = 2079311) B2079311
theorem B76941029 : Blo 1385512 76941029 := bstep (se 4 (by rfl) ⟨7213221, by rfl⟩ : syracuseStep 76941029 = 14426443) B14426443
theorem B6088477 : Blo 1385512 6088477 := bstep (se 3 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 6088477 = 2283179) B2283179
theorem B1386287 : Blo 1385512 1386287 := bstep (se 1 (by rfl) ⟨1039715, by rfl⟩ : syracuseStep 1386287 = 2079431) B2079431
theorem B3901289 : Blo 1385512 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B3950441 : Blo 1385512 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B1386395 : Blo 1385512 1386395 := bstep (se 1 (by rfl) ⟨1039796, by rfl⟩ : syracuseStep 1386395 = 2079593) B2079593
theorem B1386447 : Blo 1385512 1386447 := bstep (se 1 (by rfl) ⟨1039835, by rfl⟩ : syracuseStep 1386447 = 2079671) B2079671
theorem B1386471 : Blo 1385512 1386471 := bstep (se 1 (by rfl) ⟨1039853, by rfl⟩ : syracuseStep 1386471 = 2079707) B2079707
theorem B5261345 : Blo 1385512 5261345 := bstep (se 2 (by rfl) ⟨1973004, by rfl⟩ : syracuseStep 5261345 = 3946009) B3946009
theorem B23685209 : Blo 1385512 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B3508505 : Blo 1385512 3508505 := bstep (se 2 (by rfl) ⟨1315689, by rfl⟩ : syracuseStep 3508505 = 2631379) B2631379
theorem B1386783 : Blo 1385512 1386783 := bstep (se 1 (by rfl) ⟨1040087, by rfl⟩ : syracuseStep 1386783 = 2080175) B2080175
theorem B14420285 : Blo 1385512 14420285 := bstep (se 3 (by rfl) ⟨2703803, by rfl⟩ : syracuseStep 14420285 = 5407607) B5407607
theorem B1386843 : Blo 1385512 1386843 := bstep (se 1 (by rfl) ⟨1040132, by rfl⟩ : syracuseStep 1386843 = 2080265) B2080265
theorem B1386863 : Blo 1385512 1386863 := bstep (se 1 (by rfl) ⟨1040147, by rfl⟩ : syracuseStep 1386863 = 2080295) B2080295
theorem B1386919 : Blo 1385512 1386919 := bstep (se 1 (by rfl) ⟨1040189, by rfl⟩ : syracuseStep 1386919 = 2080379) B2080379
theorem B1387003 : Blo 1385512 1387003 := bstep (se 1 (by rfl) ⟨1040252, by rfl⟩ : syracuseStep 1387003 = 2080505) B2080505
theorem B1387071 : Blo 1385512 1387071 := bstep (se 1 (by rfl) ⟨1040303, by rfl⟩ : syracuseStep 1387071 = 2080607) B2080607
theorem B1387079 : Blo 1385512 1387079 := bstep (se 1 (by rfl) ⟨1040309, by rfl⟩ : syracuseStep 1387079 = 2080619) B2080619
theorem B2632313 : Blo 1385512 2632313 := bstep (se 2 (by rfl) ⟨987117, by rfl⟩ : syracuseStep 2632313 = 1974235) B1974235
theorem B1559263 : Blo 1385512 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B1387231 : Blo 1385512 1387231 := bstep (se 1 (by rfl) ⟨1040423, by rfl⟩ : syracuseStep 1387231 = 2080847) B2080847
theorem B1387311 : Blo 1385512 1387311 := bstep (se 1 (by rfl) ⟨1040483, by rfl⟩ : syracuseStep 1387311 = 2080967) B2080967
theorem B1387419 : Blo 1385512 1387419 := bstep (se 1 (by rfl) ⟨1040564, by rfl⟩ : syracuseStep 1387419 = 2081129) B2081129
theorem B11848619 : Blo 1385512 11848619 := bstep (se 1 (by rfl) ⟨8886464, by rfl⟩ : syracuseStep 11848619 = 17772929) B17772929
theorem B1387471 : Blo 1385512 1387471 := bstep (se 1 (by rfl) ⟨1040603, by rfl⟩ : syracuseStep 1387471 = 2081207) B2081207
theorem B44960741 : Blo 1385512 44960741 := bstep (se 4 (by rfl) ⟨4215069, by rfl⟩ : syracuseStep 44960741 = 8430139) B8430139
theorem B1387495 : Blo 1385512 1387495 := bstep (se 1 (by rfl) ⟨1040621, by rfl⟩ : syracuseStep 1387495 = 2081243) B2081243
theorem B3746807 : Blo 1385512 3746807 := bstep (se 1 (by rfl) ⟨2810105, by rfl⟩ : syracuseStep 3746807 = 5620211) B5620211
theorem B3329063 : Blo 1385512 3329063 := bstep (se 1 (by rfl) ⟨2496797, by rfl⟩ : syracuseStep 3329063 = 4993595) B4993595
theorem B56912975 : Blo 1385512 56912975 := bstep (se 1 (by rfl) ⟨42684731, by rfl⟩ : syracuseStep 56912975 = 85369463) B85369463
theorem B3509345 : Blo 1385512 3509345 := bstep (se 2 (by rfl) ⟨1316004, by rfl⟩ : syracuseStep 3509345 = 2632009) B2632009
theorem B4680827 : Blo 1385512 4680827 := bstep (se 1 (by rfl) ⟨3510620, by rfl⟩ : syracuseStep 4680827 = 7021241) B7021241
theorem B1559839 : Blo 1385512 1559839 := bstep (se 1 (by rfl) ⟨1169879, by rfl⟩ : syracuseStep 1559839 = 2339759) B2339759
theorem B2633057 : Blo 1385512 2633057 := bstep (se 2 (by rfl) ⟨987396, by rfl⟩ : syracuseStep 2633057 = 1974793) B1974793
theorem B10136951 : Blo 1385512 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B4681097 : Blo 1385512 4681097 := bstep (se 2 (by rfl) ⟨1755411, by rfl⟩ : syracuseStep 4681097 = 3510823) B3510823
theorem B2338247 : Blo 1385512 2338247 := bstep (se 1 (by rfl) ⟨1753685, by rfl⟩ : syracuseStep 2338247 = 3507371) B3507371
theorem B3329495 : Blo 1385512 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B7015895 : Blo 1385512 7015895 := bstep (se 1 (by rfl) ⟨5261921, by rfl⟩ : syracuseStep 7015895 = 10523843) B10523843
theorem B1560127 : Blo 1385512 1560127 := bstep (se 1 (by rfl) ⟨1170095, by rfl⟩ : syracuseStep 1560127 = 2340191) B2340191
theorem B5918417 : Blo 1385512 5918417 := bstep (se 2 (by rfl) ⟨2219406, by rfl⟩ : syracuseStep 5918417 = 4438813) B4438813
theorem B7892747 : Blo 1385512 7892747 := bstep (se 1 (by rfl) ⟨5919560, by rfl⟩ : syracuseStep 7892747 = 11839121) B11839121
theorem B26660623 : Blo 1385512 26660623 := bstep (se 1 (by rfl) ⟨19995467, by rfl⟩ : syracuseStep 26660623 = 39990935) B39990935
theorem B4214585 : Blo 1385512 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B4681529 : Blo 1385512 4681529 := bstep (se 2 (by rfl) ⟨1755573, by rfl⟩ : syracuseStep 4681529 = 3511147) B3511147
theorem B13332545 : Blo 1385512 13332545 := bstep (se 2 (by rfl) ⟨4999704, by rfl⟩ : syracuseStep 13332545 = 9999409) B9999409
theorem B53301563 : Blo 1385512 53301563 := bstep (se 1 (by rfl) ⟨39976172, by rfl⟩ : syracuseStep 53301563 = 79952345) B79952345
theorem B3117419 : Blo 1385512 3117419 := bstep (se 1 (by rfl) ⟨2338064, by rfl⟩ : syracuseStep 3117419 = 4676129) B4676129
theorem B2339239 : Blo 1385512 2339239 := bstep (se 1 (by rfl) ⟨1754429, by rfl⟩ : syracuseStep 2339239 = 3508859) B3508859
theorem B3117563 : Blo 1385512 3117563 := bstep (se 1 (by rfl) ⟨2338172, by rfl⟩ : syracuseStep 3117563 = 4676345) B4676345
theorem B3510803 : Blo 1385512 3510803 := bstep (se 1 (by rfl) ⟨2633102, by rfl⟩ : syracuseStep 3510803 = 5266205) B5266205
theorem B11850259 : Blo 1385512 11850259 := bstep (se 1 (by rfl) ⟨8887694, by rfl⟩ : syracuseStep 11850259 = 17775389) B17775389
theorem B2339401 : Blo 1385512 2339401 := bstep (se 2 (by rfl) ⟨877275, by rfl⟩ : syracuseStep 2339401 = 1754551) B1754551
theorem B2339435 : Blo 1385512 2339435 := bstep (se 1 (by rfl) ⟨1754576, by rfl⟩ : syracuseStep 2339435 = 3509153) B3509153
theorem B3748459 : Blo 1385512 3748459 := bstep (se 1 (by rfl) ⟨2811344, by rfl⟩ : syracuseStep 3748459 = 5622689) B5622689
theorem B3117689 : Blo 1385512 3117689 := bstep (se 2 (by rfl) ⟨1169133, by rfl⟩ : syracuseStep 3117689 = 2338267) B2338267
theorem B4682393 : Blo 1385512 4682393 := bstep (se 2 (by rfl) ⟨1755897, by rfl⟩ : syracuseStep 4682393 = 3511795) B3511795
theorem B3117743 : Blo 1385512 3117743 := bstep (se 1 (by rfl) ⟨2338307, by rfl⟩ : syracuseStep 3117743 = 4676615) B4676615
theorem B6320855 : Blo 1385512 6320855 := bstep (se 1 (by rfl) ⟨4740641, by rfl⟩ : syracuseStep 6320855 = 9481283) B9481283
theorem B3117815 : Blo 1385512 3117815 := bstep (se 1 (by rfl) ⟨2338361, by rfl⟩ : syracuseStep 3117815 = 4676723) B4676723
theorem B8434475 : Blo 1385512 8434475 := bstep (se 1 (by rfl) ⟨6325856, by rfl⟩ : syracuseStep 8434475 = 12651713) B12651713
theorem B7901995 : Blo 1385512 7901995 := bstep (se 1 (by rfl) ⟨5926496, by rfl⟩ : syracuseStep 7901995 = 11852993) B11852993
theorem B11842469 : Blo 1385512 11842469 := bstep (se 4 (by rfl) ⟨1110231, by rfl⟩ : syracuseStep 11842469 = 2220463) B2220463
theorem B3117995 : Blo 1385512 3117995 := bstep (se 1 (by rfl) ⟨2338496, by rfl⟩ : syracuseStep 3117995 = 4676993) B4676993
theorem B3511259 : Blo 1385512 3511259 := bstep (se 1 (by rfl) ⟨2633444, by rfl⟩ : syracuseStep 3511259 = 5266889) B5266889
theorem B7492765 : Blo 1385512 7492765 := bstep (se 3 (by rfl) ⟨1404893, by rfl⟩ : syracuseStep 7492765 = 2809787) B2809787
theorem B7115975 : Blo 1385512 7115975 := bstep (se 1 (by rfl) ⟨5336981, by rfl⟩ : syracuseStep 7115975 = 10673963) B10673963
theorem B2962651 : Blo 1385512 2962651 := bstep (se 1 (by rfl) ⟨2221988, by rfl⟩ : syracuseStep 2962651 = 4443977) B4443977
theorem B3511583 : Blo 1385512 3511583 := bstep (se 1 (by rfl) ⟨2633687, by rfl⟩ : syracuseStep 3511583 = 5267375) B5267375
theorem B1480027 : Blo 1385512 1480027 := bstep (se 1 (by rfl) ⟨1110020, by rfl⟩ : syracuseStep 1480027 = 2220041) B2220041
theorem B3118535 : Blo 1385512 3118535 := bstep (se 1 (by rfl) ⟨2338901, by rfl⟩ : syracuseStep 3118535 = 4677803) B4677803
theorem B2078303 : Blo 1385512 2078303 := bstep (se 1 (by rfl) ⟨1558727, by rfl⟩ : syracuseStep 2078303 = 3117455) B3117455
theorem B8877853 : Blo 1385512 8877853 := bstep (se 3 (by rfl) ⟨1664597, by rfl⟩ : syracuseStep 8877853 = 3329195) B3329195
theorem B3118895 : Blo 1385512 3118895 := bstep (se 1 (by rfl) ⟨2339171, by rfl⟩ : syracuseStep 3118895 = 4678343) B4678343
theorem B2078519 : Blo 1385512 2078519 := bstep (se 1 (by rfl) ⟨1558889, by rfl⟩ : syracuseStep 2078519 = 3117779) B3117779
theorem B3512119 : Blo 1385512 3512119 := bstep (se 1 (by rfl) ⟨2634089, by rfl⟩ : syracuseStep 3512119 = 5268179) B5268179
theorem B5265233 : Blo 1385512 5265233 := bstep (se 2 (by rfl) ⟨1974462, by rfl⟩ : syracuseStep 5265233 = 3948925) B3948925
theorem B7116751 : Blo 1385512 7116751 := bstep (se 1 (by rfl) ⟨5337563, by rfl⟩ : syracuseStep 7116751 = 10675127) B10675127
theorem B52664327 : Blo 1385512 52664327 := bstep (se 1 (by rfl) ⟨39498245, by rfl⟩ : syracuseStep 52664327 = 78996491) B78996491
theorem B2078825 : Blo 1385512 2078825 := bstep (se 2 (by rfl) ⟨779559, by rfl⟩ : syracuseStep 2078825 = 1559119) B1559119
theorem B6412553 : Blo 1385512 6412553 := bstep (se 2 (by rfl) ⟨2404707, by rfl⟩ : syracuseStep 6412553 = 4809415) B4809415
theorem B2341129 : Blo 1385512 2341129 := bstep (se 2 (by rfl) ⟨877923, by rfl⟩ : syracuseStep 2341129 = 1755847) B1755847
theorem B3119471 : Blo 1385512 3119471 := bstep (se 1 (by rfl) ⟨2339603, by rfl⟩ : syracuseStep 3119471 = 4679207) B4679207
theorem B2079143 : Blo 1385512 2079143 := bstep (se 1 (by rfl) ⟨1559357, by rfl⟩ : syracuseStep 2079143 = 3118715) B3118715
theorem B3119543 : Blo 1385512 3119543 := bstep (se 1 (by rfl) ⟨2339657, by rfl⟩ : syracuseStep 3119543 = 4679315) B4679315
theorem B2079227 : Blo 1385512 2079227 := bstep (se 1 (by rfl) ⟨1559420, by rfl⟩ : syracuseStep 2079227 = 3118841) B3118841
theorem B3119687 : Blo 1385512 3119687 := bstep (se 1 (by rfl) ⟨2339765, by rfl⟩ : syracuseStep 3119687 = 4679531) B4679531
theorem B3119723 : Blo 1385512 3119723 := bstep (se 1 (by rfl) ⟨2339792, by rfl⟩ : syracuseStep 3119723 = 4679585) B4679585
theorem B2079353 : Blo 1385512 2079353 := bstep (se 2 (by rfl) ⟨779757, by rfl⟩ : syracuseStep 2079353 = 1559515) B1559515
theorem B2079407 : Blo 1385512 2079407 := bstep (se 1 (by rfl) ⟨1559555, by rfl⟩ : syracuseStep 2079407 = 3119111) B3119111
theorem B2079455 : Blo 1385512 2079455 := bstep (se 1 (by rfl) ⟨1559591, by rfl⟩ : syracuseStep 2079455 = 3119183) B3119183
theorem B4676507 : Blo 1385512 4676507 := bstep (se 1 (by rfl) ⟨3507380, by rfl⟩ : syracuseStep 4676507 = 7014761) B7014761
theorem B7895981 : Blo 1385512 7895981 := bstep (se 3 (by rfl) ⟨1480496, by rfl⟩ : syracuseStep 7895981 = 2960993) B2960993
theorem B2079719 : Blo 1385512 2079719 := bstep (se 1 (by rfl) ⟨1559789, by rfl⟩ : syracuseStep 2079719 = 3119579) B3119579
theorem B3120119 : Blo 1385512 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B2079977 : Blo 1385512 2079977 := bstep (se 2 (by rfl) ⟨779991, by rfl⟩ : syracuseStep 2079977 = 1559983) B1559983
theorem B2080031 : Blo 1385512 2080031 := bstep (se 1 (by rfl) ⟨1560023, by rfl⟩ : syracuseStep 2080031 = 3120047) B3120047
theorem B3120479 : Blo 1385512 3120479 := bstep (se 1 (by rfl) ⟨2340359, by rfl⟩ : syracuseStep 3120479 = 4680719) B4680719
theorem B2080199 : Blo 1385512 2080199 := bstep (se 1 (by rfl) ⟨1560149, by rfl⟩ : syracuseStep 2080199 = 3120299) B3120299
theorem B5266903 : Blo 1385512 5266903 := bstep (se 1 (by rfl) ⟨3950177, by rfl⟩ : syracuseStep 5266903 = 7900355) B7900355
theorem B8879699 : Blo 1385512 8879699 := bstep (se 1 (by rfl) ⟨6659774, by rfl⟩ : syracuseStep 8879699 = 13319549) B13319549
theorem B3120875 : Blo 1385512 3120875 := bstep (se 1 (by rfl) ⟨2340656, by rfl⟩ : syracuseStep 3120875 = 4681313) B4681313
theorem B5267207 : Blo 1385512 5267207 := bstep (se 1 (by rfl) ⟨3950405, by rfl⟩ : syracuseStep 5267207 = 7900811) B7900811
theorem B7118603 : Blo 1385512 7118603 := bstep (se 1 (by rfl) ⟨5338952, by rfl⟩ : syracuseStep 7118603 = 10677905) B10677905
theorem B2080553 : Blo 1385512 2080553 := bstep (se 2 (by rfl) ⟨780207, by rfl⟩ : syracuseStep 2080553 = 1560415) B1560415
theorem B8888105 : Blo 1385512 8888105 := bstep (se 2 (by rfl) ⟨3333039, by rfl⟩ : syracuseStep 8888105 = 6666079) B6666079
theorem B6749999 : Blo 1385512 6749999 := bstep (se 1 (by rfl) ⟨5062499, by rfl⟩ : syracuseStep 6749999 = 10124999) B10124999
theorem B2080559 : Blo 1385512 2080559 := bstep (se 1 (by rfl) ⟨1560419, by rfl⟩ : syracuseStep 2080559 = 3120839) B3120839
theorem B3121001 : Blo 1385512 3121001 := bstep (se 2 (by rfl) ⟨1170375, by rfl⟩ : syracuseStep 3121001 = 2340751) B2340751
theorem B4677533 : Blo 1385512 4677533 := bstep (se 3 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 4677533 = 1754075) B1754075
theorem B44965813 : Blo 1385512 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B1974223 : Blo 1385512 1974223 := bstep (se 1 (by rfl) ⟨1480667, by rfl⟩ : syracuseStep 1974223 = 2961335) B2961335
theorem B7897121 : Blo 1385512 7897121 := bstep (se 2 (by rfl) ⟨2961420, by rfl⟩ : syracuseStep 7897121 = 5922841) B5922841
theorem B3948583 : Blo 1385512 3948583 := bstep (se 1 (by rfl) ⟨2961437, by rfl⟩ : syracuseStep 3948583 = 5922875) B5922875
theorem B8888363 : Blo 1385512 8888363 := bstep (se 1 (by rfl) ⟨6666272, by rfl⟩ : syracuseStep 8888363 = 13332545) B13332545
theorem B3121505 : Blo 1385512 3121505 := bstep (se 2 (by rfl) ⟨1170564, by rfl⟩ : syracuseStep 3121505 = 2341129) B2341129
theorem B5063095 : Blo 1385512 5063095 := bstep (se 1 (by rfl) ⟨3797321, by rfl⟩ : syracuseStep 5063095 = 7594643) B7594643
theorem B3948983 : Blo 1385512 3948983 := bstep (se 1 (by rfl) ⟨2961737, by rfl⟩ : syracuseStep 3948983 = 5923475) B5923475
theorem B3121595 : Blo 1385512 3121595 := bstep (se 1 (by rfl) ⟨2341196, by rfl⟩ : syracuseStep 3121595 = 4682393) B4682393
theorem B5407175 : Blo 1385512 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B2081231 : Blo 1385512 2081231 := bstep (se 1 (by rfl) ⟨1560923, by rfl⟩ : syracuseStep 2081231 = 3121847) B3121847
theorem B14992067 : Blo 1385512 14992067 := bstep (se 1 (by rfl) ⟨11244050, by rfl⟩ : syracuseStep 14992067 = 22488101) B22488101
theorem B4678397 : Blo 1385512 4678397 := bstep (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) B1754399
theorem B4743983 : Blo 1385512 4743983 := bstep (se 1 (by rfl) ⟨3557987, by rfl⟩ : syracuseStep 4743983 = 7115975) B7115975
theorem B4997945 : Blo 1385512 4997945 := bstep (se 2 (by rfl) ⟨1874229, by rfl⟩ : syracuseStep 4997945 = 3748459) B3748459
theorem B10535993 : Blo 1385512 10535993 := bstep (se 2 (by rfl) ⟨3950997, by rfl⟩ : syracuseStep 10535993 = 7901995) B7901995
theorem B1385535 : Blo 1385512 1385535 := bstep (se 1 (by rfl) ⟨1039151, by rfl⟩ : syracuseStep 1385535 = 2078303) B2078303
theorem B1385679 : Blo 1385512 1385679 := bstep (se 1 (by rfl) ⟨1039259, by rfl⟩ : syracuseStep 1385679 = 2078519) B2078519
theorem B3507563 : Blo 1385512 3507563 := bstep (se 1 (by rfl) ⟨2630672, by rfl⟩ : syracuseStep 3507563 = 5261345) B5261345
theorem B1385883 : Blo 1385512 1385883 := bstep (se 1 (by rfl) ⟨1039412, by rfl⟩ : syracuseStep 1385883 = 2078825) B2078825
theorem B1386095 : Blo 1385512 1386095 := bstep (se 1 (by rfl) ⟨1039571, by rfl⟩ : syracuseStep 1386095 = 2079143) B2079143
theorem B3950201 : Blo 1385512 3950201 := bstep (se 2 (by rfl) ⟨1481325, by rfl⟩ : syracuseStep 3950201 = 2962651) B2962651
theorem B1386151 : Blo 1385512 1386151 := bstep (se 1 (by rfl) ⟨1039613, by rfl⟩ : syracuseStep 1386151 = 2079227) B2079227
theorem B1386235 : Blo 1385512 1386235 := bstep (se 1 (by rfl) ⟨1039676, by rfl⟩ : syracuseStep 1386235 = 2079353) B2079353
theorem B1754875 : Blo 1385512 1754875 := bstep (se 1 (by rfl) ⟨1316156, by rfl⟩ : syracuseStep 1754875 = 2632313) B2632313
theorem B1386271 : Blo 1385512 1386271 := bstep (se 1 (by rfl) ⟨1039703, by rfl⟩ : syracuseStep 1386271 = 2079407) B2079407
theorem B1386303 : Blo 1385512 1386303 := bstep (se 1 (by rfl) ⟨1039727, by rfl⟩ : syracuseStep 1386303 = 2079455) B2079455
theorem B7899079 : Blo 1385512 7899079 := bstep (se 1 (by rfl) ⟨5924309, by rfl⟩ : syracuseStep 7899079 = 11848619) B11848619
theorem B7022537 : Blo 1385512 7022537 := bstep (se 2 (by rfl) ⟨2633451, by rfl⟩ : syracuseStep 7022537 = 5266903) B5266903
theorem B1386479 : Blo 1385512 1386479 := bstep (se 1 (by rfl) ⟨1039859, by rfl⟩ : syracuseStep 1386479 = 2079719) B2079719
theorem B1386651 : Blo 1385512 1386651 := bstep (se 1 (by rfl) ⟨1039988, by rfl⟩ : syracuseStep 1386651 = 2079977) B2079977
theorem B1386687 : Blo 1385512 1386687 := bstep (se 1 (by rfl) ⟨1040015, by rfl⟩ : syracuseStep 1386687 = 2080031) B2080031
theorem B1755371 : Blo 1385512 1755371 := bstep (se 1 (by rfl) ⟨1316528, by rfl⟩ : syracuseStep 1755371 = 2633057) B2633057
theorem B1558831 : Blo 1385512 1558831 := bstep (se 1 (by rfl) ⟨1169123, by rfl⟩ : syracuseStep 1558831 = 2338247) B2338247
theorem B1386799 : Blo 1385512 1386799 := bstep (se 1 (by rfl) ⟨1040099, by rfl⟩ : syracuseStep 1386799 = 2080199) B2080199
theorem B35547497 : Blo 1385512 35547497 := bstep (se 2 (by rfl) ⟨13330311, by rfl⟩ : syracuseStep 35547497 = 26660623) B26660623
theorem B10529189 : Blo 1385512 10529189 := bstep (se 4 (by rfl) ⟨987111, by rfl⟩ : syracuseStep 10529189 = 1974223) B1974223
theorem B5261831 : Blo 1385512 5261831 := bstep (se 1 (by rfl) ⟨3946373, by rfl⟩ : syracuseStep 5261831 = 7892747) B7892747
theorem B4745735 : Blo 1385512 4745735 := bstep (se 1 (by rfl) ⟨3559301, by rfl⟩ : syracuseStep 4745735 = 7118603) B7118603
theorem B1387035 : Blo 1385512 1387035 := bstep (se 1 (by rfl) ⟨1040276, by rfl⟩ : syracuseStep 1387035 = 2080553) B2080553
theorem B5925403 : Blo 1385512 5925403 := bstep (se 1 (by rfl) ⟨4444052, by rfl⟩ : syracuseStep 5925403 = 8888105) B8888105
theorem B4499999 : Blo 1385512 4499999 := bstep (se 1 (by rfl) ⟨3374999, by rfl⟩ : syracuseStep 4499999 = 6749999) B6749999
theorem B1387039 : Blo 1385512 1387039 := bstep (se 1 (by rfl) ⟨1040279, by rfl⟩ : syracuseStep 1387039 = 2080559) B2080559
theorem B9489001 : Blo 1385512 9489001 := bstep (se 2 (by rfl) ⟨3558375, by rfl⟩ : syracuseStep 9489001 = 7116751) B7116751
theorem B4680503 : Blo 1385512 4680503 := bstep (se 1 (by rfl) ⟨3510377, by rfl⟩ : syracuseStep 4680503 = 7020755) B7020755
theorem B1387355 : Blo 1385512 1387355 := bstep (se 1 (by rfl) ⟨1040516, by rfl⟩ : syracuseStep 1387355 = 2081033) B2081033
theorem B1387423 : Blo 1385512 1387423 := bstep (se 1 (by rfl) ⟨1040567, by rfl⟩ : syracuseStep 1387423 = 2081135) B2081135
theorem B1559623 : Blo 1385512 1559623 := bstep (se 1 (by rfl) ⟨1169717, by rfl⟩ : syracuseStep 1559623 = 2339435) B2339435
theorem B4213903 : Blo 1385512 4213903 := bstep (se 1 (by rfl) ⟨3160427, by rfl⟩ : syracuseStep 4213903 = 6320855) B6320855
theorem B6663311 : Blo 1385512 6663311 := bstep (se 1 (by rfl) ⟨4997483, by rfl⟩ : syracuseStep 6663311 = 9994967) B9994967
theorem B5622983 : Blo 1385512 5622983 := bstep (se 1 (by rfl) ⟨4217237, by rfl⟩ : syracuseStep 5622983 = 8434475) B8434475
theorem B2338159 : Blo 1385512 2338159 := bstep (se 1 (by rfl) ⟨1753619, by rfl⟩ : syracuseStep 2338159 = 3507239) B3507239
theorem B2960891 : Blo 1385512 2960891 := bstep (se 1 (by rfl) ⟨2220668, by rfl⟩ : syracuseStep 2960891 = 4441337) B4441337
theorem B2633323 : Blo 1385512 2633323 := bstep (se 1 (by rfl) ⟨1974992, by rfl⟩ : syracuseStep 2633323 = 3949985) B3949985
theorem B2338537 : Blo 1385512 2338537 := bstep (se 2 (by rfl) ⟨876951, by rfl⟩ : syracuseStep 2338537 = 1753903) B1753903
theorem B2961191 : Blo 1385512 2961191 := bstep (se 1 (by rfl) ⟨2220893, by rfl⟩ : syracuseStep 2961191 = 4441787) B4441787
theorem B8433449 : Blo 1385512 8433449 := bstep (se 2 (by rfl) ⟨3162543, by rfl⟩ : syracuseStep 8433449 = 6325087) B6325087
theorem B51294019 : Blo 1385512 51294019 := bstep (se 1 (by rfl) ⟨38470514, by rfl⟩ : syracuseStep 51294019 = 76941029) B76941029
theorem B3510155 : Blo 1385512 3510155 := bstep (se 1 (by rfl) ⟨2632616, by rfl⟩ : syracuseStep 3510155 = 5265233) B5265233
theorem B2633627 : Blo 1385512 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B15790139 : Blo 1385512 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B2339003 : Blo 1385512 2339003 := bstep (se 1 (by rfl) ⟨1754252, by rfl⟩ : syracuseStep 2339003 = 3508505) B3508505
theorem B9990353 : Blo 1385512 9990353 := bstep (se 2 (by rfl) ⟨3746382, by rfl⟩ : syracuseStep 9990353 = 7492765) B7492765
theorem B9613523 : Blo 1385512 9613523 := bstep (se 1 (by rfl) ⟨7210142, by rfl⟩ : syracuseStep 9613523 = 14420285) B14420285
theorem B3117671 : Blo 1385512 3117671 := bstep (se 1 (by rfl) ⟨2338253, by rfl⟩ : syracuseStep 3117671 = 4676507) B4676507
theorem B5263987 : Blo 1385512 5263987 := bstep (se 1 (by rfl) ⟨3947990, by rfl⟩ : syracuseStep 5263987 = 7895981) B7895981
theorem B37941983 : Blo 1385512 37941983 := bstep (se 1 (by rfl) ⟨28456487, by rfl⟩ : syracuseStep 37941983 = 56912975) B56912975
theorem B2339563 : Blo 1385512 2339563 := bstep (se 1 (by rfl) ⟨1754672, by rfl⟩ : syracuseStep 2339563 = 3509345) B3509345
theorem B2667305 : Blo 1385512 2667305 := bstep (se 2 (by rfl) ⟨1000239, by rfl⟩ : syracuseStep 2667305 = 2000479) B2000479
theorem B5919799 : Blo 1385512 5919799 := bstep (se 1 (by rfl) ⟨4439849, by rfl⟩ : syracuseStep 5919799 = 8879699) B8879699
theorem B4682825 : Blo 1385512 4682825 := bstep (se 2 (by rfl) ⟨1756059, by rfl⟩ : syracuseStep 4682825 = 3512119) B3512119
theorem B3945611 : Blo 1385512 3945611 := bstep (se 1 (by rfl) ⟨2959208, by rfl⟩ : syracuseStep 3945611 = 5918417) B5918417
theorem B3511471 : Blo 1385512 3511471 := bstep (se 1 (by rfl) ⟨2633603, by rfl⟩ : syracuseStep 3511471 = 5267207) B5267207
theorem B59954417 : Blo 1385512 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B3118355 : Blo 1385512 3118355 := bstep (se 1 (by rfl) ⟨2338766, by rfl⟩ : syracuseStep 3118355 = 4677533) B4677533
theorem B3118427 : Blo 1385512 3118427 := bstep (se 1 (by rfl) ⟨2338820, by rfl⟩ : syracuseStep 3118427 = 4677641) B4677641
theorem B35534375 : Blo 1385512 35534375 := bstep (se 1 (by rfl) ⟨26650781, by rfl⟩ : syracuseStep 35534375 = 53301563) B53301563
theorem B2078279 : Blo 1385512 2078279 := bstep (se 1 (by rfl) ⟨1558709, by rfl⟩ : syracuseStep 2078279 = 3117419) B3117419
theorem B2078375 : Blo 1385512 2078375 := bstep (se 1 (by rfl) ⟨1558781, by rfl⟩ : syracuseStep 2078375 = 3117563) B3117563
theorem B10000043 : Blo 1385512 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B2340535 : Blo 1385512 2340535 := bstep (se 1 (by rfl) ⟨1755401, by rfl⟩ : syracuseStep 2340535 = 3510803) B3510803
theorem B2078459 : Blo 1385512 2078459 := bstep (se 1 (by rfl) ⟨1558844, by rfl⟩ : syracuseStep 2078459 = 3117689) B3117689
theorem B2078495 : Blo 1385512 2078495 := bstep (se 1 (by rfl) ⟨1558871, by rfl⟩ : syracuseStep 2078495 = 3117743) B3117743
theorem B2078543 : Blo 1385512 2078543 := bstep (se 1 (by rfl) ⟨1558907, by rfl⟩ : syracuseStep 2078543 = 3117815) B3117815
theorem B3118985 : Blo 1385512 3118985 := bstep (se 2 (by rfl) ⟨1169619, by rfl⟩ : syracuseStep 3118985 = 2339239) B2339239
theorem B7894979 : Blo 1385512 7894979 := bstep (se 1 (by rfl) ⟨5921234, by rfl⟩ : syracuseStep 7894979 = 11842469) B11842469
theorem B2078663 : Blo 1385512 2078663 := bstep (se 1 (by rfl) ⟨1558997, by rfl⟩ : syracuseStep 2078663 = 3117995) B3117995
theorem B2340839 : Blo 1385512 2340839 := bstep (se 1 (by rfl) ⟨1755629, by rfl⟩ : syracuseStep 2340839 = 3511259) B3511259
theorem B15800345 : Blo 1385512 15800345 := bstep (se 2 (by rfl) ⟨5925129, by rfl⟩ : syracuseStep 15800345 = 11850259) B11850259
theorem B3119201 : Blo 1385512 3119201 := bstep (se 2 (by rfl) ⟨1169700, by rfl⟩ : syracuseStep 3119201 = 2339401) B2339401
theorem B1874111 : Blo 1385512 1874111 := bstep (se 1 (by rfl) ⟨1405583, by rfl⟩ : syracuseStep 1874111 = 2811167) B2811167
theorem B2341055 : Blo 1385512 2341055 := bstep (se 1 (by rfl) ⟨1755791, by rfl⟩ : syracuseStep 2341055 = 3511583) B3511583
theorem B2079017 : Blo 1385512 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B2079023 : Blo 1385512 2079023 := bstep (se 1 (by rfl) ⟨1559267, by rfl⟩ : syracuseStep 2079023 = 3118535) B3118535
theorem B8886671 : Blo 1385512 8886671 := bstep (se 1 (by rfl) ⟨6665003, by rfl⟩ : syracuseStep 8886671 = 13330007) B13330007
theorem B41613749 : Blo 1385512 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B11852243 : Blo 1385512 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B9492947 : Blo 1385512 9492947 := bstep (se 1 (by rfl) ⟨7119710, by rfl⟩ : syracuseStep 9492947 = 14239421) B14239421
theorem B2079263 : Blo 1385512 2079263 := bstep (se 1 (by rfl) ⟨1559447, by rfl⟩ : syracuseStep 2079263 = 3118895) B3118895
theorem B35109551 : Blo 1385512 35109551 := bstep (se 1 (by rfl) ⟨26332163, by rfl⟩ : syracuseStep 35109551 = 52664327) B52664327
theorem B4275035 : Blo 1385512 4275035 := bstep (se 1 (by rfl) ⟨3206276, by rfl⟩ : syracuseStep 4275035 = 6412553) B6412553
theorem B2079647 : Blo 1385512 2079647 := bstep (se 1 (by rfl) ⟨1559735, by rfl⟩ : syracuseStep 2079647 = 3119471) B3119471
theorem B2079695 : Blo 1385512 2079695 := bstep (se 1 (by rfl) ⟨1559771, by rfl⟩ : syracuseStep 2079695 = 3119543) B3119543
theorem B2079785 : Blo 1385512 2079785 := bstep (se 2 (by rfl) ⟨779919, by rfl⟩ : syracuseStep 2079785 = 1559839) B1559839
theorem B2079791 : Blo 1385512 2079791 := bstep (se 1 (by rfl) ⟨1559843, by rfl⟩ : syracuseStep 2079791 = 3119687) B3119687
theorem B5921849 : Blo 1385512 5921849 := bstep (se 2 (by rfl) ⟨2220693, by rfl⟩ : syracuseStep 5921849 = 4441387) B4441387
theorem B2079815 : Blo 1385512 2079815 := bstep (se 1 (by rfl) ⟨1559861, by rfl⟩ : syracuseStep 2079815 = 3119723) B3119723
theorem B1973369 : Blo 1385512 1973369 := bstep (se 2 (by rfl) ⟨740013, by rfl⟩ : syracuseStep 1973369 = 1480027) B1480027
theorem B29973827 : Blo 1385512 29973827 := bstep (se 1 (by rfl) ⟨22480370, by rfl⟩ : syracuseStep 29973827 = 44960741) B44960741
theorem B2497871 : Blo 1385512 2497871 := bstep (se 1 (by rfl) ⟨1873403, by rfl⟩ : syracuseStep 2497871 = 3746807) B3746807
theorem B2080079 : Blo 1385512 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B2219375 : Blo 1385512 2219375 := bstep (se 1 (by rfl) ⟨1664531, by rfl⟩ : syracuseStep 2219375 = 3329063) B3329063
theorem B3120551 : Blo 1385512 3120551 := bstep (se 1 (by rfl) ⟨2340413, by rfl⟩ : syracuseStep 3120551 = 4680827) B4680827
theorem B2080169 : Blo 1385512 2080169 := bstep (se 2 (by rfl) ⟨780063, by rfl⟩ : syracuseStep 2080169 = 1560127) B1560127
theorem B2080319 : Blo 1385512 2080319 := bstep (se 1 (by rfl) ⟨1560239, by rfl⟩ : syracuseStep 2080319 = 3120479) B3120479
theorem B6757967 : Blo 1385512 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B3120731 : Blo 1385512 3120731 := bstep (se 1 (by rfl) ⟨2340548, by rfl⟩ : syracuseStep 3120731 = 4681097) B4681097
theorem B2219663 : Blo 1385512 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B4677263 : Blo 1385512 4677263 := bstep (se 1 (by rfl) ⟨3507947, by rfl⟩ : syracuseStep 4677263 = 7015895) B7015895
theorem B11837137 : Blo 1385512 11837137 := bstep (se 2 (by rfl) ⟨4438926, by rfl⟩ : syracuseStep 11837137 = 8877853) B8877853
theorem B8117969 : Blo 1385512 8117969 := bstep (se 2 (by rfl) ⟨3044238, by rfl⟩ : syracuseStep 8117969 = 6088477) B6088477
theorem B2080583 : Blo 1385512 2080583 := bstep (se 1 (by rfl) ⟨1560437, by rfl⟩ : syracuseStep 2080583 = 3120875) B3120875
theorem B2809723 : Blo 1385512 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B3121019 : Blo 1385512 3121019 := bstep (se 1 (by rfl) ⟨2340764, by rfl⟩ : syracuseStep 3121019 = 4681529) B4681529
theorem B2080667 : Blo 1385512 2080667 := bstep (se 1 (by rfl) ⟨1560500, by rfl⟩ : syracuseStep 2080667 = 3121001) B3121001
theorem B5267389 : Blo 1385512 5267389 := bstep (se 3 (by rfl) ⟨987635, by rfl⟩ : syracuseStep 5267389 = 1975271) B1975271
theorem B10526759 : Blo 1385512 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B6660235 : Blo 1385512 6660235 := bstep (se 1 (by rfl) ⟨4995176, by rfl⟩ : syracuseStep 6660235 = 9990353) B9990353
theorem B2081003 : Blo 1385512 2081003 := bstep (se 1 (by rfl) ⟨1560752, by rfl⟩ : syracuseStep 2081003 = 3121505) B3121505
theorem B2081063 : Blo 1385512 2081063 := bstep (se 1 (by rfl) ⟨1560797, by rfl⟩ : syracuseStep 2081063 = 3121595) B3121595
theorem B9994711 : Blo 1385512 9994711 := bstep (se 1 (by rfl) ⟨7496033, by rfl⟩ : syracuseStep 9994711 = 14992067) B14992067
theorem B4997629 : Blo 1385512 4997629 := bstep (se 3 (by rfl) ⟨937055, by rfl⟩ : syracuseStep 4997629 = 1874111) B1874111
theorem B1778203 : Blo 1385512 1778203 := bstep (se 1 (by rfl) ⟨1333652, by rfl⟩ : syracuseStep 1778203 = 2667305) B2667305
theorem B3162655 : Blo 1385512 3162655 := bstep (se 1 (by rfl) ⟨2371991, by rfl⟩ : syracuseStep 3162655 = 4743983) B4743983
theorem B6750793 : Blo 1385512 6750793 := bstep (se 2 (by rfl) ⟨2531547, by rfl⟩ : syracuseStep 6750793 = 5063095) B5063095
theorem B3121883 : Blo 1385512 3121883 := bstep (se 1 (by rfl) ⟨2341412, by rfl⟩ : syracuseStep 3121883 = 4682825) B4682825
theorem B2630407 : Blo 1385512 2630407 := bstep (se 1 (by rfl) ⟨1972805, by rfl⟩ : syracuseStep 2630407 = 3945611) B3945611
theorem B39969611 : Blo 1385512 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B1385519 : Blo 1385512 1385519 := bstep (se 1 (by rfl) ⟨1039139, by rfl⟩ : syracuseStep 1385519 = 2078279) B2078279
theorem B1385583 : Blo 1385512 1385583 := bstep (se 1 (by rfl) ⟨1039187, by rfl⟩ : syracuseStep 1385583 = 2078375) B2078375
theorem B1385639 : Blo 1385512 1385639 := bstep (se 1 (by rfl) ⟨1039229, by rfl⟩ : syracuseStep 1385639 = 2078459) B2078459
theorem B14419133 : Blo 1385512 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B1385663 : Blo 1385512 1385663 := bstep (se 1 (by rfl) ⟨1039247, by rfl⟩ : syracuseStep 1385663 = 2078495) B2078495
theorem B1385695 : Blo 1385512 1385695 := bstep (se 1 (by rfl) ⟨1039271, by rfl⟩ : syracuseStep 1385695 = 2078543) B2078543
theorem B1385775 : Blo 1385512 1385775 := bstep (se 1 (by rfl) ⟨1039331, by rfl⟩ : syracuseStep 1385775 = 2078663) B2078663
theorem B1386011 : Blo 1385512 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B1386015 : Blo 1385512 1386015 := bstep (se 1 (by rfl) ⟨1039511, by rfl⟩ : syracuseStep 1386015 = 2079023) B2079023
theorem B5924447 : Blo 1385512 5924447 := bstep (se 1 (by rfl) ⟨4443335, by rfl⟩ : syracuseStep 5924447 = 8886671) B8886671
theorem B3507887 : Blo 1385512 3507887 := bstep (se 1 (by rfl) ⟨2630915, by rfl⟩ : syracuseStep 3507887 = 5261831) B5261831
theorem B3163823 : Blo 1385512 3163823 := bstep (se 1 (by rfl) ⟨2372867, by rfl⟩ : syracuseStep 3163823 = 4745735) B4745735
theorem B1386175 : Blo 1385512 1386175 := bstep (se 1 (by rfl) ⟨1039631, by rfl⟩ : syracuseStep 1386175 = 2079263) B2079263
theorem B2999999 : Blo 1385512 2999999 := bstep (se 1 (by rfl) ⟨2249999, by rfl⟩ : syracuseStep 2999999 = 4499999) B4499999
theorem B23406367 : Blo 1385512 23406367 := bstep (se 1 (by rfl) ⟨17554775, by rfl⟩ : syracuseStep 23406367 = 35109551) B35109551
theorem B1386431 : Blo 1385512 1386431 := bstep (se 1 (by rfl) ⟨1039823, by rfl⟩ : syracuseStep 1386431 = 2079647) B2079647
theorem B1386463 : Blo 1385512 1386463 := bstep (se 1 (by rfl) ⟨1039847, by rfl⟩ : syracuseStep 1386463 = 2079695) B2079695
theorem B1386523 : Blo 1385512 1386523 := bstep (se 1 (by rfl) ⟨1039892, by rfl⟩ : syracuseStep 1386523 = 2079785) B2079785
theorem B1386527 : Blo 1385512 1386527 := bstep (se 1 (by rfl) ⟨1039895, by rfl⟩ : syracuseStep 1386527 = 2079791) B2079791
theorem B1386543 : Blo 1385512 1386543 := bstep (se 1 (by rfl) ⟨1039907, by rfl⟩ : syracuseStep 1386543 = 2079815) B2079815
theorem B4442207 : Blo 1385512 4442207 := bstep (se 1 (by rfl) ⟨3331655, by rfl⟩ : syracuseStep 4442207 = 6663311) B6663311
theorem B19982551 : Blo 1385512 19982551 := bstep (se 1 (by rfl) ⟨14986913, by rfl⟩ : syracuseStep 19982551 = 29973827) B29973827
theorem B1665247 : Blo 1385512 1665247 := bstep (se 1 (by rfl) ⟨1248935, by rfl⟩ : syracuseStep 1665247 = 2497871) B2497871
theorem B1386719 : Blo 1385512 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B1386779 : Blo 1385512 1386779 := bstep (se 1 (by rfl) ⟨1040084, by rfl⟩ : syracuseStep 1386779 = 2080169) B2080169
theorem B1386879 : Blo 1385512 1386879 := bstep (se 1 (by rfl) ⟨1040159, by rfl⟩ : syracuseStep 1386879 = 2080319) B2080319
theorem B3746297 : Blo 1385512 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B5622299 : Blo 1385512 5622299 := bstep (se 1 (by rfl) ⟨4216724, by rfl⟩ : syracuseStep 5622299 = 8433449) B8433449
theorem B1387055 : Blo 1385512 1387055 := bstep (se 1 (by rfl) ⟨1040291, by rfl⟩ : syracuseStep 1387055 = 2080583) B2080583
theorem B7023185 : Blo 1385512 7023185 := bstep (se 2 (by rfl) ⟨2633694, by rfl⟩ : syracuseStep 7023185 = 5267389) B5267389
theorem B1387111 : Blo 1385512 1387111 := bstep (se 1 (by rfl) ⟨1040333, by rfl⟩ : syracuseStep 1387111 = 2080667) B2080667
theorem B1755751 : Blo 1385512 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B5925575 : Blo 1385512 5925575 := bstep (se 1 (by rfl) ⟨4444181, by rfl⟩ : syracuseStep 5925575 = 8888363) B8888363
theorem B1559335 : Blo 1385512 1559335 := bstep (se 1 (by rfl) ⟨1169501, by rfl⟩ : syracuseStep 1559335 = 2339003) B2339003
theorem B2632655 : Blo 1385512 2632655 := bstep (se 1 (by rfl) ⟨1974491, by rfl⟩ : syracuseStep 2632655 = 3948983) B3948983
theorem B1387487 : Blo 1385512 1387487 := bstep (se 1 (by rfl) ⟨1040615, by rfl⟩ : syracuseStep 1387487 = 2081231) B2081231
theorem B5262317 : Blo 1385512 5262317 := bstep (se 3 (by rfl) ⟨986684, by rfl⟩ : syracuseStep 5262317 = 1973369) B1973369
theorem B25636061 : Blo 1385512 25636061 := bstep (se 3 (by rfl) ⟨4806761, by rfl⟩ : syracuseStep 25636061 = 9613523) B9613523
theorem B4680989 : Blo 1385512 4680989 := bstep (se 3 (by rfl) ⟨877685, by rfl⟩ : syracuseStep 4680989 = 1755371) B1755371
theorem B7900537 : Blo 1385512 7900537 := bstep (se 2 (by rfl) ⟨2962701, by rfl⟩ : syracuseStep 7900537 = 5925403) B5925403
theorem B7023995 : Blo 1385512 7023995 := bstep (se 1 (by rfl) ⟨5267996, by rfl⟩ : syracuseStep 7023995 = 10535993) B10535993
theorem B12652001 : Blo 1385512 12652001 := bstep (se 2 (by rfl) ⟨4744500, by rfl⟩ : syracuseStep 12652001 = 9489001) B9489001
theorem B2338375 : Blo 1385512 2338375 := bstep (se 1 (by rfl) ⟨1753781, by rfl⟩ : syracuseStep 2338375 = 3507563) B3507563
theorem B2633467 : Blo 1385512 2633467 := bstep (se 1 (by rfl) ⟨1975100, by rfl⟩ : syracuseStep 2633467 = 3950201) B3950201
theorem B5263319 : Blo 1385512 5263319 := bstep (se 1 (by rfl) ⟨3947489, by rfl⟩ : syracuseStep 5263319 = 7894979) B7894979
theorem B4681691 : Blo 1385512 4681691 := bstep (se 1 (by rfl) ⟨3511268, by rfl⟩ : syracuseStep 4681691 = 7022537) B7022537
theorem B1560559 : Blo 1385512 1560559 := bstep (se 1 (by rfl) ⟨1170419, by rfl⟩ : syracuseStep 1560559 = 2340839) B2340839
theorem B7893065 : Blo 1385512 7893065 := bstep (se 2 (by rfl) ⟨2959899, by rfl⟩ : syracuseStep 7893065 = 5919799) B5919799
theorem B1560703 : Blo 1385512 1560703 := bstep (se 1 (by rfl) ⟨1170527, by rfl⟩ : syracuseStep 1560703 = 2341055) B2341055
theorem B4681961 : Blo 1385512 4681961 := bstep (se 2 (by rfl) ⟨1755735, by rfl⟩ : syracuseStep 4681961 = 3511471) B3511471
theorem B27742499 : Blo 1385512 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B7901495 : Blo 1385512 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B6328631 : Blo 1385512 6328631 := bstep (se 1 (by rfl) ⟨4746473, by rfl⟩ : syracuseStep 6328631 = 9492947) B9492947
theorem B5919101 : Blo 1385512 5919101 := bstep (se 3 (by rfl) ⟨1109831, by rfl⟩ : syracuseStep 5919101 = 2219663) B2219663
theorem B3117545 : Blo 1385512 3117545 := bstep (se 2 (by rfl) ⟨1169079, by rfl⟩ : syracuseStep 3117545 = 2338159) B2338159
theorem B21647917 : Blo 1385512 21647917 := bstep (se 3 (by rfl) ⟨4058984, by rfl⟩ : syracuseStep 21647917 = 8117969) B8117969
theorem B3748655 : Blo 1385512 3748655 := bstep (se 1 (by rfl) ⟨2811491, by rfl⟩ : syracuseStep 3748655 = 5622983) B5622983
theorem B3511097 : Blo 1385512 3511097 := bstep (se 2 (by rfl) ⟨1316661, by rfl⟩ : syracuseStep 3511097 = 2633323) B2633323
theorem B1479583 : Blo 1385512 1479583 := bstep (se 1 (by rfl) ⟨1109687, by rfl⟩ : syracuseStep 1479583 = 2219375) B2219375
theorem B15782849 : Blo 1385512 15782849 := bstep (se 2 (by rfl) ⟨5918568, by rfl⟩ : syracuseStep 15782849 = 11837137) B11837137
theorem B3118049 : Blo 1385512 3118049 := bstep (se 2 (by rfl) ⟨1169268, by rfl⟩ : syracuseStep 3118049 = 2338537) B2338537
theorem B2339833 : Blo 1385512 2339833 := bstep (se 2 (by rfl) ⟨877437, by rfl⟩ : syracuseStep 2339833 = 1754875) B1754875
theorem B68392025 : Blo 1385512 68392025 := bstep (se 2 (by rfl) ⟨25647009, by rfl⟩ : syracuseStep 68392025 = 51294019) B51294019
theorem B3118175 : Blo 1385512 3118175 := bstep (se 1 (by rfl) ⟨2338631, by rfl⟩ : syracuseStep 3118175 = 4677263) B4677263
theorem B2340103 : Blo 1385512 2340103 := bstep (se 1 (by rfl) ⟨1755077, by rfl⟩ : syracuseStep 2340103 = 3510155) B3510155
theorem B10532105 : Blo 1385512 10532105 := bstep (se 2 (by rfl) ⟨3949539, by rfl⟩ : syracuseStep 10532105 = 7899079) B7899079
theorem B5264747 : Blo 1385512 5264747 := bstep (se 1 (by rfl) ⟨3948560, by rfl⟩ : syracuseStep 5264747 = 7897121) B7897121
theorem B5264777 : Blo 1385512 5264777 := bstep (se 2 (by rfl) ⟨1974291, by rfl⟩ : syracuseStep 5264777 = 3948583) B3948583
theorem B15791597 : Blo 1385512 15791597 := bstep (se 3 (by rfl) ⟨2960924, by rfl⟩ : syracuseStep 15791597 = 5921849) B5921849
theorem B2078441 : Blo 1385512 2078441 := bstep (se 2 (by rfl) ⟨779415, by rfl⟩ : syracuseStep 2078441 = 1558831) B1558831
theorem B2078447 : Blo 1385512 2078447 := bstep (se 1 (by rfl) ⟨1558835, by rfl⟩ : syracuseStep 2078447 = 3117671) B3117671
theorem B25294655 : Blo 1385512 25294655 := bstep (se 1 (by rfl) ⟨18970991, by rfl⟩ : syracuseStep 25294655 = 37941983) B37941983
theorem B3118931 : Blo 1385512 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B3331963 : Blo 1385512 3331963 := bstep (se 1 (by rfl) ⟨2498972, by rfl⟩ : syracuseStep 3331963 = 4997945) B4997945
theorem B7018649 : Blo 1385512 7018649 := bstep (se 2 (by rfl) ⟨2631993, by rfl⟩ : syracuseStep 7018649 = 5263987) B5263987
theorem B2078903 : Blo 1385512 2078903 := bstep (se 1 (by rfl) ⟨1559177, by rfl⟩ : syracuseStep 2078903 = 3118355) B3118355
theorem B2078951 : Blo 1385512 2078951 := bstep (se 1 (by rfl) ⟨1559213, by rfl⟩ : syracuseStep 2078951 = 3118427) B3118427
theorem B3119417 : Blo 1385512 3119417 := bstep (se 2 (by rfl) ⟨1169781, by rfl⟩ : syracuseStep 3119417 = 2339563) B2339563
theorem B23689583 : Blo 1385512 23689583 := bstep (se 1 (by rfl) ⟨17767187, by rfl⟩ : syracuseStep 23689583 = 35534375) B35534375
theorem B6666695 : Blo 1385512 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B2079323 : Blo 1385512 2079323 := bstep (se 1 (by rfl) ⟨1559492, by rfl⟩ : syracuseStep 2079323 = 3118985) B3118985
theorem B10533563 : Blo 1385512 10533563 := bstep (se 1 (by rfl) ⟨7900172, by rfl⟩ : syracuseStep 10533563 = 15800345) B15800345
theorem B2079467 : Blo 1385512 2079467 := bstep (se 1 (by rfl) ⟨1559600, by rfl⟩ : syracuseStep 2079467 = 3119201) B3119201
theorem B2079497 : Blo 1385512 2079497 := bstep (se 2 (by rfl) ⟨779811, by rfl⟩ : syracuseStep 2079497 = 1559623) B1559623
theorem B5618537 : Blo 1385512 5618537 := bstep (se 2 (by rfl) ⟨2106951, by rfl⟩ : syracuseStep 5618537 = 4213903) B4213903
theorem B23698331 : Blo 1385512 23698331 := bstep (se 1 (by rfl) ⟨17773748, by rfl⟩ : syracuseStep 23698331 = 35547497) B35547497
theorem B7019459 : Blo 1385512 7019459 := bstep (se 1 (by rfl) ⟨5264594, by rfl⟩ : syracuseStep 7019459 = 10529189) B10529189
theorem B3120335 : Blo 1385512 3120335 := bstep (se 1 (by rfl) ⟨2340251, by rfl⟩ : syracuseStep 3120335 = 4680503) B4680503
theorem B2850023 : Blo 1385512 2850023 := bstep (se 1 (by rfl) ⟨2137517, by rfl⟩ : syracuseStep 2850023 = 4275035) B4275035
theorem B3120713 : Blo 1385512 3120713 := bstep (se 2 (by rfl) ⟨1170267, by rfl⟩ : syracuseStep 3120713 = 2340535) B2340535
theorem B2080367 : Blo 1385512 2080367 := bstep (se 1 (by rfl) ⟨1560275, by rfl⟩ : syracuseStep 2080367 = 3120551) B3120551
theorem B1973927 : Blo 1385512 1973927 := bstep (se 1 (by rfl) ⟨1480445, by rfl⟩ : syracuseStep 1973927 = 2960891) B2960891
theorem B4505311 : Blo 1385512 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B2080487 : Blo 1385512 2080487 := bstep (se 1 (by rfl) ⟨1560365, by rfl⟩ : syracuseStep 2080487 = 3120731) B3120731
theorem B1974127 : Blo 1385512 1974127 := bstep (se 1 (by rfl) ⟨1480595, by rfl⟩ : syracuseStep 1974127 = 2961191) B2961191
theorem B2080679 : Blo 1385512 2080679 := bstep (se 1 (by rfl) ⟨1560509, by rfl⟩ : syracuseStep 2080679 = 3121019) B3121019
theorem B3121307 : Blo 1385512 3121307 := bstep (se 1 (by rfl) ⟨2340980, by rfl⟩ : syracuseStep 3121307 = 4681961) B4681961
theorem B2080937 : Blo 1385512 2080937 := bstep (se 2 (by rfl) ⟨780351, by rfl⟩ : syracuseStep 2080937 = 1560703) B1560703
theorem B5267663 : Blo 1385512 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B11845885 : Blo 1385512 11845885 := bstep (se 3 (by rfl) ⟨2221103, by rfl⟩ : syracuseStep 11845885 = 4442207) B4442207
theorem B2220329 : Blo 1385512 2220329 := bstep (se 2 (by rfl) ⟨832623, by rfl⟩ : syracuseStep 2220329 = 1665247) B1665247
theorem B2081255 : Blo 1385512 2081255 := bstep (se 1 (by rfl) ⟨1560941, by rfl⟩ : syracuseStep 2081255 = 3121883) B3121883
theorem B2499103 : Blo 1385512 2499103 := bstep (se 1 (by rfl) ⟨1874327, by rfl⟩ : syracuseStep 2499103 = 3748655) B3748655
theorem B35521253 : Blo 1385512 35521253 := bstep (se 4 (by rfl) ⟨3330117, by rfl⟩ : syracuseStep 35521253 = 6660235) B6660235
theorem B16876349 : Blo 1385512 16876349 := bstep (se 3 (by rfl) ⟨3164315, by rfl⟩ : syracuseStep 16876349 = 6328631) B6328631
theorem B7021403 : Blo 1385512 7021403 := bstep (se 1 (by rfl) ⟨5266052, by rfl⟩ : syracuseStep 7021403 = 10532105) B10532105
theorem B10527731 : Blo 1385512 10527731 := bstep (se 1 (by rfl) ⟨7895798, by rfl⟩ : syracuseStep 10527731 = 15791597) B15791597
theorem B3507209 : Blo 1385512 3507209 := bstep (se 2 (by rfl) ⟨1315203, by rfl⟩ : syracuseStep 3507209 = 2630407) B2630407
theorem B3949631 : Blo 1385512 3949631 := bstep (se 1 (by rfl) ⟨2962223, by rfl⟩ : syracuseStep 3949631 = 5924447) B5924447
theorem B1999999 : Blo 1385512 1999999 := bstep (se 1 (by rfl) ⟨1499999, by rfl⟩ : syracuseStep 1999999 = 2999999) B2999999
theorem B1385627 : Blo 1385512 1385627 := bstep (se 1 (by rfl) ⟨1039220, by rfl⟩ : syracuseStep 1385627 = 2078441) B2078441
theorem B1385631 : Blo 1385512 1385631 := bstep (se 1 (by rfl) ⟨1039223, by rfl⟩ : syracuseStep 1385631 = 2078447) B2078447
theorem B4679099 : Blo 1385512 4679099 := bstep (se 1 (by rfl) ⟨3509324, by rfl⟩ : syracuseStep 4679099 = 7018649) B7018649
theorem B1385935 : Blo 1385512 1385935 := bstep (se 1 (by rfl) ⟨1039451, by rfl⟩ : syracuseStep 1385935 = 2078903) B2078903
theorem B1385967 : Blo 1385512 1385967 := bstep (se 1 (by rfl) ⟨1039475, by rfl⟩ : syracuseStep 1385967 = 2078951) B2078951
theorem B1386215 : Blo 1385512 1386215 := bstep (se 1 (by rfl) ⟨1039661, by rfl⟩ : syracuseStep 1386215 = 2079323) B2079323
theorem B7022375 : Blo 1385512 7022375 := bstep (se 1 (by rfl) ⟨5266781, by rfl⟩ : syracuseStep 7022375 = 10533563) B10533563
theorem B3950383 : Blo 1385512 3950383 := bstep (se 1 (by rfl) ⟨2962787, by rfl⟩ : syracuseStep 3950383 = 5925575) B5925575
theorem B1386311 : Blo 1385512 1386311 := bstep (se 1 (by rfl) ⟨1039733, by rfl⟩ : syracuseStep 1386311 = 2079467) B2079467
theorem B1386331 : Blo 1385512 1386331 := bstep (se 1 (by rfl) ⟨1039748, by rfl⟩ : syracuseStep 1386331 = 2079497) B2079497
theorem B3745691 : Blo 1385512 3745691 := bstep (se 1 (by rfl) ⟨2809268, by rfl⟩ : syracuseStep 3745691 = 5618537) B5618537
theorem B4679639 : Blo 1385512 4679639 := bstep (se 1 (by rfl) ⟨3509729, by rfl⟩ : syracuseStep 4679639 = 7019459) B7019459
theorem B1755103 : Blo 1385512 1755103 := bstep (se 1 (by rfl) ⟨1316327, by rfl⟩ : syracuseStep 1755103 = 2632655) B2632655
theorem B3508211 : Blo 1385512 3508211 := bstep (se 1 (by rfl) ⟨2631158, by rfl⟩ : syracuseStep 3508211 = 5262317) B5262317
theorem B17090707 : Blo 1385512 17090707 := bstep (se 1 (by rfl) ⟨12818030, by rfl⟩ : syracuseStep 17090707 = 25636061) B25636061
theorem B6007081 : Blo 1385512 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B1386911 : Blo 1385512 1386911 := bstep (se 1 (by rfl) ⟨1040183, by rfl⟩ : syracuseStep 1386911 = 2080367) B2080367
theorem B2632169 : Blo 1385512 2632169 := bstep (se 2 (by rfl) ⟨987063, by rfl⟩ : syracuseStep 2632169 = 1974127) B1974127
theorem B1386991 : Blo 1385512 1386991 := bstep (se 1 (by rfl) ⟨1040243, by rfl⟩ : syracuseStep 1386991 = 2080487) B2080487
theorem B4442617 : Blo 1385512 4442617 := bstep (se 2 (by rfl) ⟨1665981, by rfl⟩ : syracuseStep 4442617 = 3331963) B3331963
theorem B1387119 : Blo 1385512 1387119 := bstep (se 1 (by rfl) ⟨1040339, by rfl⟩ : syracuseStep 1387119 = 2080679) B2080679
theorem B3508879 : Blo 1385512 3508879 := bstep (se 1 (by rfl) ⟨2631659, by rfl⟩ : syracuseStep 3508879 = 5263319) B5263319
theorem B5262043 : Blo 1385512 5262043 := bstep (se 1 (by rfl) ⟨3946532, by rfl⟩ : syracuseStep 5262043 = 7893065) B7893065
theorem B1387335 : Blo 1385512 1387335 := bstep (se 1 (by rfl) ⟨1040501, by rfl⟩ : syracuseStep 1387335 = 2081003) B2081003
theorem B1387375 : Blo 1385512 1387375 := bstep (se 1 (by rfl) ⟨1040531, by rfl⟩ : syracuseStep 1387375 = 2081063) B2081063
theorem B26643401 : Blo 1385512 26643401 := bstep (se 2 (by rfl) ⟨9991275, by rfl⟩ : syracuseStep 26643401 = 19982551) B19982551
theorem B10521899 : Blo 1385512 10521899 := bstep (se 1 (by rfl) ⟨7891424, by rfl⟩ : syracuseStep 10521899 = 15782849) B15782849
theorem B6663505 : Blo 1385512 6663505 := bstep (se 2 (by rfl) ⟨2498814, by rfl⟩ : syracuseStep 6663505 = 4997629) B4997629
theorem B9612755 : Blo 1385512 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B3509831 : Blo 1385512 3509831 := bstep (se 1 (by rfl) ⟨2632373, by rfl⟩ : syracuseStep 3509831 = 5264747) B5264747
theorem B3509851 : Blo 1385512 3509851 := bstep (se 1 (by rfl) ⟨2632388, by rfl⟩ : syracuseStep 3509851 = 5264777) B5264777
theorem B2338591 : Blo 1385512 2338591 := bstep (se 1 (by rfl) ⟨1753943, by rfl⟩ : syracuseStep 2338591 = 3507887) B3507887
theorem B2109215 : Blo 1385512 2109215 := bstep (se 1 (by rfl) ⟨1581911, by rfl⟩ : syracuseStep 2109215 = 3163823) B3163823
theorem B16863103 : Blo 1385512 16863103 := bstep (se 1 (by rfl) ⟨12647327, by rfl⟩ : syracuseStep 16863103 = 25294655) B25294655
theorem B9990125 : Blo 1385512 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B4444463 : Blo 1385512 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B3748199 : Blo 1385512 3748199 := bstep (se 1 (by rfl) ⟨2811149, by rfl⟩ : syracuseStep 3748199 = 5622299) B5622299
theorem B4682123 : Blo 1385512 4682123 := bstep (se 1 (by rfl) ⟨3511592, by rfl⟩ : syracuseStep 4682123 = 7023185) B7023185
theorem B5263805 : Blo 1385512 5263805 := bstep (se 3 (by rfl) ⟨986963, by rfl⟩ : syracuseStep 5263805 = 1973927) B1973927
theorem B15798887 : Blo 1385512 15798887 := bstep (se 1 (by rfl) ⟨11849165, by rfl⟩ : syracuseStep 15798887 = 23698331) B23698331
theorem B3117833 : Blo 1385512 3117833 := bstep (se 2 (by rfl) ⟨1169187, by rfl⟩ : syracuseStep 3117833 = 2338375) B2338375
theorem B4682663 : Blo 1385512 4682663 := bstep (se 1 (by rfl) ⟨3511997, by rfl⟩ : syracuseStep 4682663 = 7023995) B7023995
theorem B8434667 : Blo 1385512 8434667 := bstep (se 1 (by rfl) ⟨6326000, by rfl⟩ : syracuseStep 8434667 = 12652001) B12652001
theorem B3511289 : Blo 1385512 3511289 := bstep (se 2 (by rfl) ⟨1316733, by rfl⟩ : syracuseStep 3511289 = 2633467) B2633467
theorem B31208489 : Blo 1385512 31208489 := bstep (se 2 (by rfl) ⟨11703183, by rfl⟩ : syracuseStep 31208489 = 23406367) B23406367
theorem B7017839 : Blo 1385512 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B9483749 : Blo 1385512 9483749 := bstep (se 4 (by rfl) ⟨889101, by rfl⟩ : syracuseStep 9483749 = 1778203) B1778203
theorem B18494999 : Blo 1385512 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B115455557 : Blo 1385512 115455557 := bstep (se 4 (by rfl) ⟨10823958, by rfl⟩ : syracuseStep 115455557 = 21647917) B21647917
theorem B3946067 : Blo 1385512 3946067 := bstep (se 1 (by rfl) ⟨2959550, by rfl⟩ : syracuseStep 3946067 = 5919101) B5919101
theorem B2078363 : Blo 1385512 2078363 := bstep (se 1 (by rfl) ⟨1558772, by rfl⟩ : syracuseStep 2078363 = 3117545) B3117545
theorem B2340731 : Blo 1385512 2340731 := bstep (se 1 (by rfl) ⟨1755548, by rfl⟩ : syracuseStep 2340731 = 3511097) B3511097
theorem B26646407 : Blo 1385512 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B7600061 : Blo 1385512 7600061 := bstep (se 3 (by rfl) ⟨1425011, by rfl⟩ : syracuseStep 7600061 = 2850023) B2850023
theorem B13326281 : Blo 1385512 13326281 := bstep (se 2 (by rfl) ⟨4997355, by rfl⟩ : syracuseStep 13326281 = 9994711) B9994711
theorem B2078699 : Blo 1385512 2078699 := bstep (se 1 (by rfl) ⟨1559024, by rfl⟩ : syracuseStep 2078699 = 3118049) B3118049
theorem B4216873 : Blo 1385512 4216873 := bstep (se 2 (by rfl) ⟨1581327, by rfl⟩ : syracuseStep 4216873 = 3162655) B3162655
theorem B45594683 : Blo 1385512 45594683 := bstep (se 1 (by rfl) ⟨34196012, by rfl⟩ : syracuseStep 45594683 = 68392025) B68392025
theorem B2078783 : Blo 1385512 2078783 := bstep (se 1 (by rfl) ⟨1559087, by rfl⟩ : syracuseStep 2078783 = 3118175) B3118175
theorem B9001057 : Blo 1385512 9001057 := bstep (se 2 (by rfl) ⟨3375396, by rfl⟩ : syracuseStep 9001057 = 6750793) B6750793
theorem B2341001 : Blo 1385512 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B2079113 : Blo 1385512 2079113 := bstep (se 2 (by rfl) ⟨779667, by rfl⟩ : syracuseStep 2079113 = 1559335) B1559335
theorem B1972777 : Blo 1385512 1972777 := bstep (se 2 (by rfl) ⟨739791, by rfl⟩ : syracuseStep 1972777 = 1479583) B1479583
theorem B2079287 : Blo 1385512 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B3119777 : Blo 1385512 3119777 := bstep (se 2 (by rfl) ⟨1169916, by rfl⟩ : syracuseStep 3119777 = 2339833) B2339833
theorem B2079611 : Blo 1385512 2079611 := bstep (se 1 (by rfl) ⟨1559708, by rfl⟩ : syracuseStep 2079611 = 3119417) B3119417
theorem B15793055 : Blo 1385512 15793055 := bstep (se 1 (by rfl) ⟨11844791, by rfl⟩ : syracuseStep 15793055 = 23689583) B23689583
theorem B3120137 : Blo 1385512 3120137 := bstep (se 2 (by rfl) ⟨1170051, by rfl⟩ : syracuseStep 3120137 = 2340103) B2340103
theorem B10534049 : Blo 1385512 10534049 := bstep (se 2 (by rfl) ⟨3950268, by rfl⟩ : syracuseStep 10534049 = 7900537) B7900537
theorem B2080223 : Blo 1385512 2080223 := bstep (se 1 (by rfl) ⟨1560167, by rfl⟩ : syracuseStep 2080223 = 3120335) B3120335
theorem B3120659 : Blo 1385512 3120659 := bstep (se 1 (by rfl) ⟨2340494, by rfl⟩ : syracuseStep 3120659 = 4680989) B4680989
theorem B2080475 : Blo 1385512 2080475 := bstep (se 1 (by rfl) ⟨1560356, by rfl⟩ : syracuseStep 2080475 = 3120713) B3120713
theorem B3121127 : Blo 1385512 3121127 := bstep (se 1 (by rfl) ⟨2340845, by rfl⟩ : syracuseStep 3121127 = 4681691) B4681691
theorem B2080745 : Blo 1385512 2080745 := bstep (se 2 (by rfl) ⟨780279, by rfl⟩ : syracuseStep 2080745 = 1560559) B1560559
theorem B2080871 : Blo 1385512 2080871 := bstep (se 1 (by rfl) ⟨1560653, by rfl⟩ : syracuseStep 2080871 = 3121307) B3121307
theorem B12001409 : Blo 1385512 12001409 := bstep (se 2 (by rfl) ⟨4500528, by rfl⟩ : syracuseStep 12001409 = 9001057) B9001057
theorem B13328549 : Blo 1385512 13328549 := bstep (se 4 (by rfl) ⟨1249551, by rfl⟩ : syracuseStep 13328549 = 2499103) B2499103
theorem B3121415 : Blo 1385512 3121415 := bstep (se 1 (by rfl) ⟨2341061, by rfl⟩ : syracuseStep 3121415 = 4682123) B4682123
theorem B15794513 : Blo 1385512 15794513 := bstep (se 2 (by rfl) ⟨5922942, by rfl⟩ : syracuseStep 15794513 = 11845885) B11845885
theorem B3121775 : Blo 1385512 3121775 := bstep (se 1 (by rfl) ⟨2341331, by rfl⟩ : syracuseStep 3121775 = 4682663) B4682663
theorem B2630369 : Blo 1385512 2630369 := bstep (se 2 (by rfl) ⟨986388, by rfl⟩ : syracuseStep 2630369 = 1972777) B1972777
theorem B4678505 : Blo 1385512 4678505 := bstep (se 2 (by rfl) ⟨1754439, by rfl⟩ : syracuseStep 4678505 = 3508879) B3508879
theorem B4678559 : Blo 1385512 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B12329999 : Blo 1385512 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B2630711 : Blo 1385512 2630711 := bstep (se 1 (by rfl) ⟨1973033, by rfl⟩ : syracuseStep 2630711 = 3946067) B3946067
theorem B1385575 : Blo 1385512 1385575 := bstep (se 1 (by rfl) ⟨1039181, by rfl⟩ : syracuseStep 1385575 = 2078363) B2078363
theorem B1385799 : Blo 1385512 1385799 := bstep (se 1 (by rfl) ⟨1039349, by rfl⟩ : syracuseStep 1385799 = 2078699) B2078699
theorem B1385855 : Blo 1385512 1385855 := bstep (se 1 (by rfl) ⟨1039391, by rfl⟩ : syracuseStep 1385855 = 2078783) B2078783
theorem B307881485 : Blo 1385512 307881485 := bstep (se 3 (by rfl) ⟨57727778, by rfl⟩ : syracuseStep 307881485 = 115455557) B115455557
theorem B1386075 : Blo 1385512 1386075 := bstep (se 1 (by rfl) ⟨1039556, by rfl⟩ : syracuseStep 1386075 = 2079113) B2079113
theorem B1754779 : Blo 1385512 1754779 := bstep (se 1 (by rfl) ⟨1316084, by rfl⟩ : syracuseStep 1754779 = 2632169) B2632169
theorem B1386191 : Blo 1385512 1386191 := bstep (se 1 (by rfl) ⟨1039643, by rfl⟩ : syracuseStep 1386191 = 2079287) B2079287
theorem B1386407 : Blo 1385512 1386407 := bstep (se 1 (by rfl) ⟨1039805, by rfl⟩ : syracuseStep 1386407 = 2079611) B2079611
theorem B10528703 : Blo 1385512 10528703 := bstep (se 1 (by rfl) ⟨7896527, by rfl⟩ : syracuseStep 10528703 = 15793055) B15793055
theorem B17762267 : Blo 1385512 17762267 := bstep (se 1 (by rfl) ⟨13321700, by rfl⟩ : syracuseStep 17762267 = 26643401) B26643401
theorem B7022699 : Blo 1385512 7022699 := bstep (se 1 (by rfl) ⟨5267024, by rfl⟩ : syracuseStep 7022699 = 10534049) B10534049
theorem B4679801 : Blo 1385512 4679801 := bstep (se 2 (by rfl) ⟨1754925, by rfl⟩ : syracuseStep 4679801 = 3509851) B3509851
theorem B7014599 : Blo 1385512 7014599 := bstep (se 1 (by rfl) ⟨5260949, by rfl⟩ : syracuseStep 7014599 = 10521899) B10521899
theorem B6408503 : Blo 1385512 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B1386815 : Blo 1385512 1386815 := bstep (se 1 (by rfl) ⟨1040111, by rfl⟩ : syracuseStep 1386815 = 2080223) B2080223
theorem B1386983 : Blo 1385512 1386983 := bstep (se 1 (by rfl) ⟨1040237, by rfl⟩ : syracuseStep 1386983 = 2080475) B2080475
theorem B23693957 : Blo 1385512 23693957 := bstep (se 4 (by rfl) ⟨2221308, by rfl⟩ : syracuseStep 23693957 = 4442617) B4442617
theorem B1387163 : Blo 1385512 1387163 := bstep (se 1 (by rfl) ⟨1040372, by rfl⟩ : syracuseStep 1387163 = 2080745) B2080745
theorem B5622497 : Blo 1385512 5622497 := bstep (se 2 (by rfl) ⟨2108436, by rfl⟩ : syracuseStep 5622497 = 4216873) B4216873
theorem B1387291 : Blo 1385512 1387291 := bstep (se 1 (by rfl) ⟨1040468, by rfl⟩ : syracuseStep 1387291 = 2080937) B2080937
theorem B3509203 : Blo 1385512 3509203 := bstep (se 1 (by rfl) ⟨2631902, by rfl⟩ : syracuseStep 3509203 = 5263805) B5263805
theorem B1387503 : Blo 1385512 1387503 := bstep (se 1 (by rfl) ⟨1040627, by rfl⟩ : syracuseStep 1387503 = 2081255) B2081255
theorem B11250899 : Blo 1385512 11250899 := bstep (se 1 (by rfl) ⟨8438174, by rfl⟩ : syracuseStep 11250899 = 16876349) B16876349
theorem B4680935 : Blo 1385512 4680935 := bstep (se 1 (by rfl) ⟨3510701, by rfl⟩ : syracuseStep 4680935 = 7021403) B7021403
theorem B5623111 : Blo 1385512 5623111 := bstep (se 1 (by rfl) ⟨4217333, by rfl⟩ : syracuseStep 5623111 = 8434667) B8434667
theorem B2338139 : Blo 1385512 2338139 := bstep (se 1 (by rfl) ⟨1753604, by rfl⟩ : syracuseStep 2338139 = 3507209) B3507209
theorem B2633087 : Blo 1385512 2633087 := bstep (se 1 (by rfl) ⟨1974815, by rfl⟩ : syracuseStep 2633087 = 3949631) B3949631
theorem B7016057 : Blo 1385512 7016057 := bstep (se 2 (by rfl) ⟨2631021, by rfl⟩ : syracuseStep 7016057 = 5262043) B5262043
theorem B39980789 : Blo 1385512 39980789 := bstep (se 5 (by rfl) ⟨1874099, by rfl⟩ : syracuseStep 39980789 = 3748199) B3748199
theorem B4681583 : Blo 1385512 4681583 := bstep (se 1 (by rfl) ⟨3511187, by rfl⟩ : syracuseStep 4681583 = 7022375) B7022375
theorem B1560487 : Blo 1385512 1560487 := bstep (se 1 (by rfl) ⟨1170365, by rfl⟩ : syracuseStep 1560487 = 2340731) B2340731
theorem B17764271 : Blo 1385512 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B5066707 : Blo 1385512 5066707 := bstep (se 1 (by rfl) ⟨3800030, by rfl⟩ : syracuseStep 5066707 = 7600061) B7600061
theorem B8884187 : Blo 1385512 8884187 := bstep (se 1 (by rfl) ⟨6663140, by rfl⟩ : syracuseStep 8884187 = 13326281) B13326281
theorem B2338807 : Blo 1385512 2338807 := bstep (se 1 (by rfl) ⟨1754105, by rfl⟩ : syracuseStep 2338807 = 3508211) B3508211
theorem B30396455 : Blo 1385512 30396455 := bstep (se 1 (by rfl) ⟨22797341, by rfl⟩ : syracuseStep 30396455 = 45594683) B45594683
theorem B1560667 : Blo 1385512 1560667 := bstep (se 1 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 1560667 = 2341001) B2341001
theorem B2666665 : Blo 1385512 2666665 := bstep (se 2 (by rfl) ⟨999999, by rfl⟩ : syracuseStep 2666665 = 1999999) B1999999
theorem B8884673 : Blo 1385512 8884673 := bstep (se 2 (by rfl) ⟨3331752, by rfl⟩ : syracuseStep 8884673 = 6663505) B6663505
theorem B3118121 : Blo 1385512 3118121 := bstep (se 2 (by rfl) ⟨1169295, by rfl⟩ : syracuseStep 3118121 = 2338591) B2338591
theorem B2339887 : Blo 1385512 2339887 := bstep (se 1 (by rfl) ⟨1754915, by rfl⟩ : syracuseStep 2339887 = 3509831) B3509831
theorem B22484137 : Blo 1385512 22484137 := bstep (se 2 (by rfl) ⟨8431551, by rfl⟩ : syracuseStep 22484137 = 16863103) B16863103
theorem B1406143 : Blo 1385512 1406143 := bstep (se 1 (by rfl) ⟨1054607, by rfl⟩ : syracuseStep 1406143 = 2109215) B2109215
theorem B2340137 : Blo 1385512 2340137 := bstep (se 2 (by rfl) ⟨877551, by rfl⟩ : syracuseStep 2340137 = 1755103) B1755103
theorem B3511775 : Blo 1385512 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B22787609 : Blo 1385512 22787609 := bstep (se 2 (by rfl) ⟨8545353, by rfl⟩ : syracuseStep 22787609 = 17090707) B17090707
theorem B2962975 : Blo 1385512 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B8009441 : Blo 1385512 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B10532591 : Blo 1385512 10532591 := bstep (se 1 (by rfl) ⟨7899443, by rfl⟩ : syracuseStep 10532591 = 15798887) B15798887
theorem B23680835 : Blo 1385512 23680835 := bstep (se 1 (by rfl) ⟨17760626, by rfl⟩ : syracuseStep 23680835 = 35521253) B35521253
theorem B2078555 : Blo 1385512 2078555 := bstep (se 1 (by rfl) ⟨1558916, by rfl⟩ : syracuseStep 2078555 = 3117833) B3117833
theorem B7018487 : Blo 1385512 7018487 := bstep (se 1 (by rfl) ⟨5263865, by rfl⟩ : syracuseStep 7018487 = 10527731) B10527731
theorem B2340859 : Blo 1385512 2340859 := bstep (se 1 (by rfl) ⟨1755644, by rfl⟩ : syracuseStep 2340859 = 3511289) B3511289
theorem B20805659 : Blo 1385512 20805659 := bstep (se 1 (by rfl) ⟨15604244, by rfl⟩ : syracuseStep 20805659 = 31208489) B31208489
theorem B5920877 : Blo 1385512 5920877 := bstep (se 3 (by rfl) ⟨1110164, by rfl⟩ : syracuseStep 5920877 = 2220329) B2220329
theorem B3119399 : Blo 1385512 3119399 := bstep (se 1 (by rfl) ⟨2339549, by rfl⟩ : syracuseStep 3119399 = 4679099) B4679099
theorem B6322499 : Blo 1385512 6322499 := bstep (se 1 (by rfl) ⟨4741874, by rfl⟩ : syracuseStep 6322499 = 9483749) B9483749
theorem B2497127 : Blo 1385512 2497127 := bstep (se 1 (by rfl) ⟨1872845, by rfl⟩ : syracuseStep 2497127 = 3745691) B3745691
theorem B3119759 : Blo 1385512 3119759 := bstep (se 1 (by rfl) ⟨2339819, by rfl⟩ : syracuseStep 3119759 = 4679639) B4679639
theorem B2079851 : Blo 1385512 2079851 := bstep (se 1 (by rfl) ⟨1559888, by rfl⟩ : syracuseStep 2079851 = 3119777) B3119777
theorem B2080091 : Blo 1385512 2080091 := bstep (se 1 (by rfl) ⟨1560068, by rfl⟩ : syracuseStep 2080091 = 3120137) B3120137
theorem B2080439 : Blo 1385512 2080439 := bstep (se 1 (by rfl) ⟨1560329, by rfl⟩ : syracuseStep 2080439 = 3120659) B3120659
theorem B5267177 : Blo 1385512 5267177 := bstep (se 2 (by rfl) ⟨1975191, by rfl⟩ : syracuseStep 5267177 = 3950383) B3950383
theorem B2080751 : Blo 1385512 2080751 := bstep (se 1 (by rfl) ⟨1560563, by rfl⟩ : syracuseStep 2080751 = 3121127) B3121127
theorem B6660083 : Blo 1385512 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B2080889 : Blo 1385512 2080889 := bstep (se 2 (by rfl) ⟨780333, by rfl⟩ : syracuseStep 2080889 = 1560667) B1560667
theorem B2080943 : Blo 1385512 2080943 := bstep (se 1 (by rfl) ⟨1560707, by rfl⟩ : syracuseStep 2080943 = 3121415) B3121415
theorem B5923115 : Blo 1385512 5923115 := bstep (se 1 (by rfl) ⟨4442336, by rfl⟩ : syracuseStep 5923115 = 8884673) B8884673
theorem B2081183 : Blo 1385512 2081183 := bstep (se 1 (by rfl) ⟨1560887, by rfl⟩ : syracuseStep 2081183 = 3121775) B3121775
theorem B1753579 : Blo 1385512 1753579 := bstep (se 1 (by rfl) ⟨1315184, by rfl⟩ : syracuseStep 1753579 = 2630369) B2630369
theorem B1753807 : Blo 1385512 1753807 := bstep (se 1 (by rfl) ⟨1315355, by rfl⟩ : syracuseStep 1753807 = 2630711) B2630711
theorem B14222213 : Blo 1385512 14222213 := bstep (se 4 (by rfl) ⟨1333332, by rfl⟩ : syracuseStep 14222213 = 2666665) B2666665
theorem B7021565 : Blo 1385512 7021565 := bstep (se 3 (by rfl) ⟨1316543, by rfl⟩ : syracuseStep 7021565 = 2633087) B2633087
theorem B7021727 : Blo 1385512 7021727 := bstep (se 1 (by rfl) ⟨5266295, by rfl⟩ : syracuseStep 7021727 = 10532591) B10532591
theorem B15787223 : Blo 1385512 15787223 := bstep (se 1 (by rfl) ⟨11840417, by rfl⟩ : syracuseStep 15787223 = 23680835) B23680835
theorem B1385703 : Blo 1385512 1385703 := bstep (se 1 (by rfl) ⟨1039277, by rfl⟩ : syracuseStep 1385703 = 2078555) B2078555
theorem B4678937 : Blo 1385512 4678937 := bstep (se 2 (by rfl) ⟨1754601, by rfl⟩ : syracuseStep 4678937 = 3509203) B3509203
theorem B4678991 : Blo 1385512 4678991 := bstep (se 1 (by rfl) ⟨3509243, by rfl⟩ : syracuseStep 4678991 = 7018487) B7018487
theorem B13870439 : Blo 1385512 13870439 := bstep (se 1 (by rfl) ⟨10402829, by rfl⟩ : syracuseStep 13870439 = 20805659) B20805659
theorem B15795971 : Blo 1385512 15795971 := bstep (se 1 (by rfl) ⟨11846978, by rfl⟩ : syracuseStep 15795971 = 23693957) B23693957
theorem B7497481 : Blo 1385512 7497481 := bstep (se 2 (by rfl) ⟨2811555, by rfl⟩ : syracuseStep 7497481 = 5623111) B5623111
theorem B3950633 : Blo 1385512 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B1386567 : Blo 1385512 1386567 := bstep (se 1 (by rfl) ⟨1039925, by rfl⟩ : syracuseStep 1386567 = 2079851) B2079851
theorem B1558759 : Blo 1385512 1558759 := bstep (se 1 (by rfl) ⟨1169069, by rfl⟩ : syracuseStep 1558759 = 2338139) B2338139
theorem B1386727 : Blo 1385512 1386727 := bstep (se 1 (by rfl) ⟨1040045, by rfl⟩ : syracuseStep 1386727 = 2080091) B2080091
theorem B1386959 : Blo 1385512 1386959 := bstep (se 1 (by rfl) ⟨1040219, by rfl⟩ : syracuseStep 1386959 = 2080439) B2080439
theorem B1387167 : Blo 1385512 1387167 := bstep (se 1 (by rfl) ⟨1040375, by rfl⟩ : syracuseStep 1387167 = 2080751) B2080751
theorem B1387247 : Blo 1385512 1387247 := bstep (se 1 (by rfl) ⟨1040435, by rfl⟩ : syracuseStep 1387247 = 2080871) B2080871
theorem B10529675 : Blo 1385512 10529675 := bstep (se 1 (by rfl) ⟨7897256, by rfl⟩ : syracuseStep 10529675 = 15794513) B15794513
theorem B8219999 : Blo 1385512 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B1560091 : Blo 1385512 1560091 := bstep (se 1 (by rfl) ⟨1170068, by rfl⟩ : syracuseStep 1560091 = 2340137) B2340137
theorem B7499429 : Blo 1385512 7499429 := bstep (se 4 (by rfl) ⟨703071, by rfl⟩ : syracuseStep 7499429 = 1406143) B1406143
theorem B205254323 : Blo 1385512 205254323 := bstep (se 1 (by rfl) ⟨153940742, by rfl⟩ : syracuseStep 205254323 = 307881485) B307881485
theorem B11841511 : Blo 1385512 11841511 := bstep (se 1 (by rfl) ⟨8881133, by rfl⟩ : syracuseStep 11841511 = 17762267) B17762267
theorem B4681799 : Blo 1385512 4681799 := bstep (se 1 (by rfl) ⟨3511349, by rfl⟩ : syracuseStep 4681799 = 7022699) B7022699
theorem B4272335 : Blo 1385512 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B4214999 : Blo 1385512 4214999 := bstep (se 1 (by rfl) ⟨3161249, by rfl⟩ : syracuseStep 4214999 = 6322499) B6322499
theorem B29978849 : Blo 1385512 29978849 := bstep (se 2 (by rfl) ⟨11242068, by rfl⟩ : syracuseStep 29978849 = 22484137) B22484137
theorem B3748331 : Blo 1385512 3748331 := bstep (se 1 (by rfl) ⟨2811248, by rfl⟩ : syracuseStep 3748331 = 5622497) B5622497
theorem B7500599 : Blo 1385512 7500599 := bstep (se 1 (by rfl) ⟨5625449, by rfl⟩ : syracuseStep 7500599 = 11250899) B11250899
theorem B2339705 : Blo 1385512 2339705 := bstep (se 2 (by rfl) ⟨877389, by rfl⟩ : syracuseStep 2339705 = 1754779) B1754779
theorem B3511451 : Blo 1385512 3511451 := bstep (se 1 (by rfl) ⟨2633588, by rfl⟩ : syracuseStep 3511451 = 5267177) B5267177
theorem B26653859 : Blo 1385512 26653859 := bstep (se 1 (by rfl) ⟨19990394, by rfl⟩ : syracuseStep 26653859 = 39980789) B39980789
theorem B6755609 : Blo 1385512 6755609 := bstep (se 2 (by rfl) ⟨2533353, by rfl⟩ : syracuseStep 6755609 = 5066707) B5066707
theorem B11842847 : Blo 1385512 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B3118409 : Blo 1385512 3118409 := bstep (se 2 (by rfl) ⟨1169403, by rfl⟩ : syracuseStep 3118409 = 2338807) B2338807
theorem B20264303 : Blo 1385512 20264303 := bstep (se 1 (by rfl) ⟨15198227, by rfl⟩ : syracuseStep 20264303 = 30396455) B30396455
theorem B8000939 : Blo 1385512 8000939 := bstep (se 1 (by rfl) ⟨6000704, by rfl⟩ : syracuseStep 8000939 = 12001409) B12001409
theorem B8885699 : Blo 1385512 8885699 := bstep (se 1 (by rfl) ⟨6664274, by rfl⟩ : syracuseStep 8885699 = 13328549) B13328549
theorem B3119003 : Blo 1385512 3119003 := bstep (se 1 (by rfl) ⟨2339252, by rfl⟩ : syracuseStep 3119003 = 4678505) B4678505
theorem B3119039 : Blo 1385512 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B2078747 : Blo 1385512 2078747 := bstep (se 1 (by rfl) ⟨1559060, by rfl⟩ : syracuseStep 2078747 = 3118121) B3118121
theorem B2341183 : Blo 1385512 2341183 := bstep (se 1 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 2341183 = 3511775) B3511775
theorem B5339627 : Blo 1385512 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B7019135 : Blo 1385512 7019135 := bstep (se 1 (by rfl) ⟨5264351, by rfl⟩ : syracuseStep 7019135 = 10528703) B10528703
theorem B3119849 : Blo 1385512 3119849 := bstep (se 2 (by rfl) ⟨1169943, by rfl⟩ : syracuseStep 3119849 = 2339887) B2339887
theorem B60766957 : Blo 1385512 60766957 := bstep (se 3 (by rfl) ⟨11393804, by rfl⟩ : syracuseStep 60766957 = 22787609) B22787609
theorem B3947251 : Blo 1385512 3947251 := bstep (se 1 (by rfl) ⟨2960438, by rfl⟩ : syracuseStep 3947251 = 5920877) B5920877
theorem B3119867 : Blo 1385512 3119867 := bstep (se 1 (by rfl) ⟨2339900, by rfl⟩ : syracuseStep 3119867 = 4679801) B4679801
theorem B4676399 : Blo 1385512 4676399 := bstep (se 1 (by rfl) ⟨3507299, by rfl⟩ : syracuseStep 4676399 = 7014599) B7014599
theorem B2079599 : Blo 1385512 2079599 := bstep (se 1 (by rfl) ⟨1559699, by rfl⟩ : syracuseStep 2079599 = 3119399) B3119399
theorem B6659005 : Blo 1385512 6659005 := bstep (se 3 (by rfl) ⟨1248563, by rfl⟩ : syracuseStep 6659005 = 2497127) B2497127
theorem B2079839 : Blo 1385512 2079839 := bstep (se 1 (by rfl) ⟨1559879, by rfl⟩ : syracuseStep 2079839 = 3119759) B3119759
theorem B3120623 : Blo 1385512 3120623 := bstep (se 1 (by rfl) ⟨2340467, by rfl⟩ : syracuseStep 3120623 = 4680935) B4680935
theorem B4677371 : Blo 1385512 4677371 := bstep (se 1 (by rfl) ⟨3508028, by rfl⟩ : syracuseStep 4677371 = 7016057) B7016057
theorem B2080649 : Blo 1385512 2080649 := bstep (se 2 (by rfl) ⟨780243, by rfl⟩ : syracuseStep 2080649 = 1560487) B1560487
theorem B3121055 : Blo 1385512 3121055 := bstep (se 1 (by rfl) ⟨2340791, by rfl⟩ : syracuseStep 3121055 = 4681583) B4681583
theorem B5922791 : Blo 1385512 5922791 := bstep (se 1 (by rfl) ⟨4442093, by rfl⟩ : syracuseStep 5922791 = 8884187) B8884187
theorem B4440055 : Blo 1385512 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B3121145 : Blo 1385512 3121145 := bstep (se 2 (by rfl) ⟨1170429, by rfl⟩ : syracuseStep 3121145 = 2340859) B2340859
theorem B3121199 : Blo 1385512 3121199 := bstep (se 1 (by rfl) ⟨2340899, by rfl⟩ : syracuseStep 3121199 = 4681799) B4681799
theorem B10535021 : Blo 1385512 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B2809999 : Blo 1385512 2809999 := bstep (se 1 (by rfl) ⟨2107499, by rfl⟩ : syracuseStep 2809999 = 4214999) B4214999
theorem B3948743 : Blo 1385512 3948743 := bstep (se 1 (by rfl) ⟨2961557, by rfl⟩ : syracuseStep 3948743 = 5923115) B5923115
theorem B2498887 : Blo 1385512 2498887 := bstep (se 1 (by rfl) ⟨1874165, by rfl⟩ : syracuseStep 2498887 = 3748331) B3748331
theorem B3121577 : Blo 1385512 3121577 := bstep (se 2 (by rfl) ⟨1170591, by rfl⟩ : syracuseStep 3121577 = 2341183) B2341183
theorem B18014957 : Blo 1385512 18014957 := bstep (se 3 (by rfl) ⟨3377804, by rfl⟩ : syracuseStep 18014957 = 6755609) B6755609
theorem B17769239 : Blo 1385512 17769239 := bstep (se 1 (by rfl) ⟨13326929, by rfl⟩ : syracuseStep 17769239 = 26653859) B26653859
theorem B13509535 : Blo 1385512 13509535 := bstep (se 1 (by rfl) ⟨10132151, by rfl⟩ : syracuseStep 13509535 = 20264303) B20264303
theorem B5333959 : Blo 1385512 5333959 := bstep (se 1 (by rfl) ⟨4000469, by rfl⟩ : syracuseStep 5333959 = 8000939) B8000939
theorem B5923799 : Blo 1385512 5923799 := bstep (se 1 (by rfl) ⟨4442849, by rfl⟩ : syracuseStep 5923799 = 8885699) B8885699
theorem B1385831 : Blo 1385512 1385831 := bstep (se 1 (by rfl) ⟨1039373, by rfl⟩ : syracuseStep 1385831 = 2078747) B2078747
theorem B4679423 : Blo 1385512 4679423 := bstep (se 1 (by rfl) ⟨3509567, by rfl⟩ : syracuseStep 4679423 = 7019135) B7019135
theorem B1386399 : Blo 1385512 1386399 := bstep (se 1 (by rfl) ⟨1039799, by rfl⟩ : syracuseStep 1386399 = 2079599) B2079599
theorem B1386559 : Blo 1385512 1386559 := bstep (se 1 (by rfl) ⟨1039919, by rfl⟩ : syracuseStep 1386559 = 2079839) B2079839
theorem B9996641 : Blo 1385512 9996641 := bstep (se 2 (by rfl) ⟨3748740, by rfl⟩ : syracuseStep 9996641 = 7497481) B7497481
theorem B4999619 : Blo 1385512 4999619 := bstep (se 1 (by rfl) ⟨3749714, by rfl⟩ : syracuseStep 4999619 = 7499429) B7499429
theorem B1387099 : Blo 1385512 1387099 := bstep (se 1 (by rfl) ⟨1040324, by rfl⟩ : syracuseStep 1387099 = 2080649) B2080649
theorem B15788681 : Blo 1385512 15788681 := bstep (se 2 (by rfl) ⟨5920755, by rfl⟩ : syracuseStep 15788681 = 11841511) B11841511
theorem B1387259 : Blo 1385512 1387259 := bstep (se 1 (by rfl) ⟨1040444, by rfl⟩ : syracuseStep 1387259 = 2080889) B2080889
theorem B1387295 : Blo 1385512 1387295 := bstep (se 1 (by rfl) ⟨1040471, by rfl⟩ : syracuseStep 1387295 = 2080943) B2080943
theorem B1387455 : Blo 1385512 1387455 := bstep (se 1 (by rfl) ⟨1040591, by rfl⟩ : syracuseStep 1387455 = 2081183) B2081183
theorem B5000399 : Blo 1385512 5000399 := bstep (se 1 (by rfl) ⟨3750299, by rfl⟩ : syracuseStep 5000399 = 7500599) B7500599
theorem B1559803 : Blo 1385512 1559803 := bstep (se 1 (by rfl) ⟨1169852, by rfl⟩ : syracuseStep 1559803 = 2339705) B2339705
theorem B9481475 : Blo 1385512 9481475 := bstep (se 1 (by rfl) ⟨7111106, by rfl⟩ : syracuseStep 9481475 = 14222213) B14222213
theorem B2338105 : Blo 1385512 2338105 := bstep (se 2 (by rfl) ⟨876789, by rfl⟩ : syracuseStep 2338105 = 1753579) B1753579
theorem B4681043 : Blo 1385512 4681043 := bstep (se 1 (by rfl) ⟨3510782, by rfl⟩ : syracuseStep 4681043 = 7021565) B7021565
theorem B4681151 : Blo 1385512 4681151 := bstep (se 1 (by rfl) ⟨3510863, by rfl⟩ : syracuseStep 4681151 = 7021727) B7021727
theorem B2338409 : Blo 1385512 2338409 := bstep (se 2 (by rfl) ⟨876903, by rfl⟩ : syracuseStep 2338409 = 1753807) B1753807
theorem B81022609 : Blo 1385512 81022609 := bstep (se 2 (by rfl) ⟨30383478, by rfl⟩ : syracuseStep 81022609 = 60766957) B60766957
theorem B5263001 : Blo 1385512 5263001 := bstep (se 2 (by rfl) ⟨1973625, by rfl⟩ : syracuseStep 5263001 = 3947251) B3947251
theorem B10530647 : Blo 1385512 10530647 := bstep (se 1 (by rfl) ⟨7897985, by rfl⟩ : syracuseStep 10530647 = 15795971) B15795971
theorem B3559751 : Blo 1385512 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B3117599 : Blo 1385512 3117599 := bstep (se 1 (by rfl) ⟨2338199, by rfl⟩ : syracuseStep 3117599 = 4676399) B4676399
theorem B136836215 : Blo 1385512 136836215 := bstep (se 1 (by rfl) ⟨102627161, by rfl⟩ : syracuseStep 136836215 = 205254323) B205254323
theorem B3118247 : Blo 1385512 3118247 := bstep (se 1 (by rfl) ⟨2338685, by rfl⟩ : syracuseStep 3118247 = 4677371) B4677371
theorem B5920073 : Blo 1385512 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B2848223 : Blo 1385512 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B19985899 : Blo 1385512 19985899 := bstep (se 1 (by rfl) ⟨14989424, by rfl⟩ : syracuseStep 19985899 = 29978849) B29978849
theorem B2078345 : Blo 1385512 2078345 := bstep (se 2 (by rfl) ⟨779379, by rfl⟩ : syracuseStep 2078345 = 1558759) B1558759
theorem B2340967 : Blo 1385512 2340967 := bstep (se 1 (by rfl) ⟨1755725, by rfl⟩ : syracuseStep 2340967 = 3511451) B3511451
theorem B10524815 : Blo 1385512 10524815 := bstep (se 1 (by rfl) ⟨7893611, by rfl⟩ : syracuseStep 10524815 = 15787223) B15787223
theorem B3119291 : Blo 1385512 3119291 := bstep (se 1 (by rfl) ⟨2339468, by rfl⟩ : syracuseStep 3119291 = 4678937) B4678937
theorem B7895231 : Blo 1385512 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B2078939 : Blo 1385512 2078939 := bstep (se 1 (by rfl) ⟨1559204, by rfl⟩ : syracuseStep 2078939 = 3118409) B3118409
theorem B3119327 : Blo 1385512 3119327 := bstep (se 1 (by rfl) ⟨2339495, by rfl⟩ : syracuseStep 3119327 = 4678991) B4678991
theorem B9246959 : Blo 1385512 9246959 := bstep (se 1 (by rfl) ⟨6935219, by rfl⟩ : syracuseStep 9246959 = 13870439) B13870439
theorem B21919997 : Blo 1385512 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B8878673 : Blo 1385512 8878673 := bstep (se 2 (by rfl) ⟨3329502, by rfl⟩ : syracuseStep 8878673 = 6659005) B6659005
theorem B2079335 : Blo 1385512 2079335 := bstep (se 1 (by rfl) ⟨1559501, by rfl⟩ : syracuseStep 2079335 = 3119003) B3119003
theorem B2079359 : Blo 1385512 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B2079899 : Blo 1385512 2079899 := bstep (se 1 (by rfl) ⟨1559924, by rfl⟩ : syracuseStep 2079899 = 3119849) B3119849
theorem B2079911 : Blo 1385512 2079911 := bstep (se 1 (by rfl) ⟨1559933, by rfl⟩ : syracuseStep 2079911 = 3119867) B3119867
theorem B7019783 : Blo 1385512 7019783 := bstep (se 1 (by rfl) ⟨5264837, by rfl⟩ : syracuseStep 7019783 = 10529675) B10529675
theorem B2080121 : Blo 1385512 2080121 := bstep (se 2 (by rfl) ⟨780045, by rfl⟩ : syracuseStep 2080121 = 1560091) B1560091
theorem B2080415 : Blo 1385512 2080415 := bstep (se 1 (by rfl) ⟨1560311, by rfl⟩ : syracuseStep 2080415 = 3120623) B3120623
theorem B2080703 : Blo 1385512 2080703 := bstep (se 1 (by rfl) ⟨1560527, by rfl⟩ : syracuseStep 2080703 = 3121055) B3121055
theorem B3948527 : Blo 1385512 3948527 := bstep (se 1 (by rfl) ⟨2961395, by rfl⟩ : syracuseStep 3948527 = 5922791) B5922791
theorem B2080763 : Blo 1385512 2080763 := bstep (se 1 (by rfl) ⟨1560572, by rfl⟩ : syracuseStep 2080763 = 3121145) B3121145
theorem B2080799 : Blo 1385512 2080799 := bstep (se 1 (by rfl) ⟨1560599, by rfl⟩ : syracuseStep 2080799 = 3121199) B3121199
theorem B3121289 : Blo 1385512 3121289 := bstep (se 2 (by rfl) ⟨1170483, by rfl⟩ : syracuseStep 3121289 = 2340967) B2340967
theorem B2081051 : Blo 1385512 2081051 := bstep (se 1 (by rfl) ⟨1560788, by rfl⟩ : syracuseStep 2081051 = 3121577) B3121577
theorem B12009971 : Blo 1385512 12009971 := bstep (se 1 (by rfl) ⟨9007478, by rfl⟩ : syracuseStep 12009971 = 18014957) B18014957
theorem B11846159 : Blo 1385512 11846159 := bstep (se 1 (by rfl) ⟨8884619, by rfl⟩ : syracuseStep 11846159 = 17769239) B17769239
theorem B3949199 : Blo 1385512 3949199 := bstep (se 1 (by rfl) ⟨2961899, by rfl⟩ : syracuseStep 3949199 = 5923799) B5923799
theorem B1385563 : Blo 1385512 1385563 := bstep (se 1 (by rfl) ⟨1039172, by rfl⟩ : syracuseStep 1385563 = 2078345) B2078345
theorem B7111945 : Blo 1385512 7111945 := bstep (se 2 (by rfl) ⟨2666979, by rfl⟩ : syracuseStep 7111945 = 5333959) B5333959
theorem B1385959 : Blo 1385512 1385959 := bstep (se 1 (by rfl) ⟨1039469, by rfl⟩ : syracuseStep 1385959 = 2078939) B2078939
theorem B23676461 : Blo 1385512 23676461 := bstep (se 3 (by rfl) ⟨4439336, by rfl⟩ : syracuseStep 23676461 = 8878673) B8878673
theorem B1386223 : Blo 1385512 1386223 := bstep (se 1 (by rfl) ⟨1039667, by rfl⟩ : syracuseStep 1386223 = 2079335) B2079335
theorem B1386239 : Blo 1385512 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B1386599 : Blo 1385512 1386599 := bstep (se 1 (by rfl) ⟨1039949, by rfl⟩ : syracuseStep 1386599 = 2079899) B2079899
theorem B1386607 : Blo 1385512 1386607 := bstep (se 1 (by rfl) ⟨1039955, by rfl⟩ : syracuseStep 1386607 = 2079911) B2079911
theorem B4679855 : Blo 1385512 4679855 := bstep (se 1 (by rfl) ⟨3509891, by rfl⟩ : syracuseStep 4679855 = 7019783) B7019783
theorem B108030145 : Blo 1385512 108030145 := bstep (se 2 (by rfl) ⟨40511304, by rfl⟩ : syracuseStep 108030145 = 81022609) B81022609
theorem B1386747 : Blo 1385512 1386747 := bstep (se 1 (by rfl) ⟨1040060, by rfl⟩ : syracuseStep 1386747 = 2080121) B2080121
theorem B1558939 : Blo 1385512 1558939 := bstep (se 1 (by rfl) ⟨1169204, by rfl⟩ : syracuseStep 1558939 = 2338409) B2338409
theorem B3508667 : Blo 1385512 3508667 := bstep (se 1 (by rfl) ⟨2631500, by rfl⟩ : syracuseStep 3508667 = 5263001) B5263001
theorem B1386943 : Blo 1385512 1386943 := bstep (se 1 (by rfl) ⟨1040207, by rfl⟩ : syracuseStep 1386943 = 2080415) B2080415
theorem B1387135 : Blo 1385512 1387135 := bstep (se 1 (by rfl) ⟨1040351, by rfl⟩ : syracuseStep 1387135 = 2080703) B2080703
theorem B2632351 : Blo 1385512 2632351 := bstep (se 1 (by rfl) ⟨1974263, by rfl⟩ : syracuseStep 2632351 = 3948527) B3948527
theorem B1387175 : Blo 1385512 1387175 := bstep (se 1 (by rfl) ⟨1040381, by rfl⟩ : syracuseStep 1387175 = 2080763) B2080763
theorem B7023347 : Blo 1385512 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B2632495 : Blo 1385512 2632495 := bstep (se 1 (by rfl) ⟨1974371, by rfl⟩ : syracuseStep 2632495 = 3948743) B3948743
theorem B3746665 : Blo 1385512 3746665 := bstep (se 2 (by rfl) ⟨1404999, by rfl⟩ : syracuseStep 3746665 = 2809999) B2809999
theorem B58453325 : Blo 1385512 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B7016543 : Blo 1385512 7016543 := bstep (se 1 (by rfl) ⟨5262407, by rfl⟩ : syracuseStep 7016543 = 10524815) B10524815
theorem B5263487 : Blo 1385512 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B6164639 : Blo 1385512 6164639 := bstep (se 1 (by rfl) ⟨4623479, by rfl⟩ : syracuseStep 6164639 = 9246959) B9246959
theorem B6664427 : Blo 1385512 6664427 := bstep (se 1 (by rfl) ⟨4998320, by rfl⟩ : syracuseStep 6664427 = 9996641) B9996641
theorem B3117473 : Blo 1385512 3117473 := bstep (se 2 (by rfl) ⟨1169052, by rfl⟩ : syracuseStep 3117473 = 2338105) B2338105
theorem B6320983 : Blo 1385512 6320983 := bstep (se 1 (by rfl) ⟨4740737, by rfl⟩ : syracuseStep 6320983 = 9481475) B9481475
theorem B2373167 : Blo 1385512 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B2078399 : Blo 1385512 2078399 := bstep (se 1 (by rfl) ⟨1558799, by rfl⟩ : syracuseStep 2078399 = 3117599) B3117599
theorem B3331849 : Blo 1385512 3331849 := bstep (se 2 (by rfl) ⟨1249443, by rfl⟩ : syracuseStep 3331849 = 2498887) B2498887
theorem B91224143 : Blo 1385512 91224143 := bstep (se 1 (by rfl) ⟨68418107, by rfl⟩ : syracuseStep 91224143 = 136836215) B136836215
theorem B2078831 : Blo 1385512 2078831 := bstep (se 1 (by rfl) ⟨1559123, by rfl⟩ : syracuseStep 2078831 = 3118247) B3118247
theorem B3946715 : Blo 1385512 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B1898815 : Blo 1385512 1898815 := bstep (se 1 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 1898815 = 2848223) B2848223
theorem B3119615 : Blo 1385512 3119615 := bstep (se 1 (by rfl) ⟨2339711, by rfl⟩ : syracuseStep 3119615 = 4679423) B4679423
theorem B18012713 : Blo 1385512 18012713 := bstep (se 2 (by rfl) ⟨6754767, by rfl⟩ : syracuseStep 18012713 = 13509535) B13509535
theorem B2079527 : Blo 1385512 2079527 := bstep (se 1 (by rfl) ⟨1559645, by rfl⟩ : syracuseStep 2079527 = 3119291) B3119291
theorem B2079551 : Blo 1385512 2079551 := bstep (se 1 (by rfl) ⟨1559663, by rfl⟩ : syracuseStep 2079551 = 3119327) B3119327
theorem B3333079 : Blo 1385512 3333079 := bstep (se 1 (by rfl) ⟨2499809, by rfl⟩ : syracuseStep 3333079 = 4999619) B4999619
theorem B2079737 : Blo 1385512 2079737 := bstep (se 2 (by rfl) ⟨779901, by rfl⟩ : syracuseStep 2079737 = 1559803) B1559803
theorem B10525787 : Blo 1385512 10525787 := bstep (se 1 (by rfl) ⟨7894340, by rfl⟩ : syracuseStep 10525787 = 15788681) B15788681
theorem B26647865 : Blo 1385512 26647865 := bstep (se 2 (by rfl) ⟨9992949, by rfl⟩ : syracuseStep 26647865 = 19985899) B19985899
theorem B3333599 : Blo 1385512 3333599 := bstep (se 1 (by rfl) ⟨2500199, by rfl⟩ : syracuseStep 3333599 = 5000399) B5000399
theorem B3120695 : Blo 1385512 3120695 := bstep (se 1 (by rfl) ⟨2340521, by rfl⟩ : syracuseStep 3120695 = 4681043) B4681043
theorem B3120767 : Blo 1385512 3120767 := bstep (se 1 (by rfl) ⟨2340575, by rfl⟩ : syracuseStep 3120767 = 4681151) B4681151
theorem B7020431 : Blo 1385512 7020431 := bstep (se 1 (by rfl) ⟨5265323, by rfl⟩ : syracuseStep 7020431 = 10530647) B10530647
theorem B4677695 : Blo 1385512 4677695 := bstep (se 1 (by rfl) ⟨3508271, by rfl⟩ : syracuseStep 4677695 = 7016543) B7016543
theorem B2080859 : Blo 1385512 2080859 := bstep (se 1 (by rfl) ⟨1560644, by rfl⟩ : syracuseStep 2080859 = 3121289) B3121289
theorem B144040193 : Blo 1385512 144040193 := bstep (se 2 (by rfl) ⟨54015072, by rfl⟩ : syracuseStep 144040193 = 108030145) B108030145
theorem B7897439 : Blo 1385512 7897439 := bstep (se 1 (by rfl) ⟨5923079, by rfl⟩ : syracuseStep 7897439 = 11846159) B11846159
theorem B2531753 : Blo 1385512 2531753 := bstep (se 2 (by rfl) ⟨949407, by rfl⟩ : syracuseStep 2531753 = 1898815) B1898815
theorem B1582111 : Blo 1385512 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B1385599 : Blo 1385512 1385599 := bstep (se 1 (by rfl) ⟨1039199, by rfl⟩ : syracuseStep 1385599 = 2078399) B2078399
theorem B1385887 : Blo 1385512 1385887 := bstep (se 1 (by rfl) ⟨1039415, by rfl⟩ : syracuseStep 1385887 = 2078831) B2078831
theorem B2631143 : Blo 1385512 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B1386351 : Blo 1385512 1386351 := bstep (se 1 (by rfl) ⟨1039763, by rfl⟩ : syracuseStep 1386351 = 2079527) B2079527
theorem B1386367 : Blo 1385512 1386367 := bstep (se 1 (by rfl) ⟨1039775, by rfl⟩ : syracuseStep 1386367 = 2079551) B2079551
theorem B1386491 : Blo 1385512 1386491 := bstep (se 1 (by rfl) ⟨1039868, by rfl⟩ : syracuseStep 1386491 = 2079737) B2079737
theorem B2222399 : Blo 1385512 2222399 := bstep (se 1 (by rfl) ⟨1666799, by rfl⟩ : syracuseStep 2222399 = 3333599) B3333599
theorem B4442465 : Blo 1385512 4442465 := bstep (se 2 (by rfl) ⟨1665924, by rfl⟩ : syracuseStep 4442465 = 3331849) B3331849
theorem B4680287 : Blo 1385512 4680287 := bstep (se 1 (by rfl) ⟨3510215, by rfl⟩ : syracuseStep 4680287 = 7020431) B7020431
theorem B1387199 : Blo 1385512 1387199 := bstep (se 1 (by rfl) ⟨1040399, by rfl⟩ : syracuseStep 1387199 = 2080799) B2080799
theorem B3508991 : Blo 1385512 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B4442951 : Blo 1385512 4442951 := bstep (se 1 (by rfl) ⟨3332213, by rfl⟩ : syracuseStep 4442951 = 6664427) B6664427
theorem B1387367 : Blo 1385512 1387367 := bstep (se 1 (by rfl) ⟨1040525, by rfl⟩ : syracuseStep 1387367 = 2081051) B2081051
theorem B2632799 : Blo 1385512 2632799 := bstep (se 1 (by rfl) ⟨1974599, by rfl⟩ : syracuseStep 2632799 = 3949199) B3949199
theorem B3509801 : Blo 1385512 3509801 := bstep (se 2 (by rfl) ⟨1316175, by rfl⟩ : syracuseStep 3509801 = 2632351) B2632351
theorem B3509993 : Blo 1385512 3509993 := bstep (se 2 (by rfl) ⟨1316247, by rfl⟩ : syracuseStep 3509993 = 2632495) B2632495
theorem B4444105 : Blo 1385512 4444105 := bstep (se 2 (by rfl) ⟨1666539, by rfl⟩ : syracuseStep 4444105 = 3333079) B3333079
theorem B32026589 : Blo 1385512 32026589 := bstep (se 3 (by rfl) ⟨6004985, by rfl⟩ : syracuseStep 32026589 = 12009971) B12009971
theorem B48033901 : Blo 1385512 48033901 := bstep (se 3 (by rfl) ⟨9006356, by rfl⟩ : syracuseStep 48033901 = 18012713) B18012713
theorem B2339111 : Blo 1385512 2339111 := bstep (se 1 (by rfl) ⟨1754333, by rfl⟩ : syracuseStep 2339111 = 3508667) B3508667
theorem B9482593 : Blo 1385512 9482593 := bstep (se 2 (by rfl) ⟨3555972, by rfl⟩ : syracuseStep 9482593 = 7111945) B7111945
theorem B4682231 : Blo 1385512 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B7017191 : Blo 1385512 7017191 := bstep (se 1 (by rfl) ⟨5262893, by rfl⟩ : syracuseStep 7017191 = 10525787) B10525787
theorem B17765243 : Blo 1385512 17765243 := bstep (se 1 (by rfl) ⟨13323932, by rfl⟩ : syracuseStep 17765243 = 26647865) B26647865
theorem B4109759 : Blo 1385512 4109759 := bstep (se 1 (by rfl) ⟨3082319, by rfl⟩ : syracuseStep 4109759 = 6164639) B6164639
theorem B2078315 : Blo 1385512 2078315 := bstep (se 1 (by rfl) ⟨1558736, by rfl⟩ : syracuseStep 2078315 = 3117473) B3117473
theorem B2078585 : Blo 1385512 2078585 := bstep (se 2 (by rfl) ⟨779469, by rfl⟩ : syracuseStep 2078585 = 1558939) B1558939
theorem B15784307 : Blo 1385512 15784307 := bstep (se 1 (by rfl) ⟨11838230, by rfl⟩ : syracuseStep 15784307 = 23676461) B23676461
theorem B8427977 : Blo 1385512 8427977 := bstep (se 2 (by rfl) ⟨3160491, by rfl⟩ : syracuseStep 8427977 = 6320983) B6320983
theorem B4995553 : Blo 1385512 4995553 := bstep (se 2 (by rfl) ⟨1873332, by rfl⟩ : syracuseStep 4995553 = 3746665) B3746665
theorem B60816095 : Blo 1385512 60816095 := bstep (se 1 (by rfl) ⟨45612071, by rfl⟩ : syracuseStep 60816095 = 91224143) B91224143
theorem B3119903 : Blo 1385512 3119903 := bstep (se 1 (by rfl) ⟨2339927, by rfl⟩ : syracuseStep 3119903 = 4679855) B4679855
theorem B2079743 : Blo 1385512 2079743 := bstep (se 1 (by rfl) ⟨1559807, by rfl⟩ : syracuseStep 2079743 = 3119615) B3119615
theorem B38968883 : Blo 1385512 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B2080463 : Blo 1385512 2080463 := bstep (se 1 (by rfl) ⟨1560347, by rfl⟩ : syracuseStep 2080463 = 3120695) B3120695
theorem B2080511 : Blo 1385512 2080511 := bstep (se 1 (by rfl) ⟨1560383, by rfl⟩ : syracuseStep 2080511 = 3120767) B3120767
theorem B64045201 : Blo 1385512 64045201 := bstep (se 2 (by rfl) ⟨24016950, by rfl⟩ : syracuseStep 64045201 = 48033901) B48033901
theorem B8437925 : Blo 1385512 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B96026795 : Blo 1385512 96026795 := bstep (se 1 (by rfl) ⟨72020096, by rfl⟩ : syracuseStep 96026795 = 144040193) B144040193
theorem B1687835 : Blo 1385512 1687835 := bstep (se 1 (by rfl) ⟨1265876, by rfl⟩ : syracuseStep 1687835 = 2531753) B2531753
theorem B3121487 : Blo 1385512 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B4678127 : Blo 1385512 4678127 := bstep (se 1 (by rfl) ⟨3508595, by rfl⟩ : syracuseStep 4678127 = 7017191) B7017191
theorem B6660737 : Blo 1385512 6660737 := bstep (se 2 (by rfl) ⟨2497776, by rfl⟩ : syracuseStep 6660737 = 4995553) B4995553
theorem B1385543 : Blo 1385512 1385543 := bstep (se 1 (by rfl) ⟨1039157, by rfl⟩ : syracuseStep 1385543 = 2078315) B2078315
theorem B1385723 : Blo 1385512 1385723 := bstep (se 1 (by rfl) ⟨1039292, by rfl⟩ : syracuseStep 1385723 = 2078585) B2078585
theorem B40544063 : Blo 1385512 40544063 := bstep (se 1 (by rfl) ⟨30408047, by rfl⟩ : syracuseStep 40544063 = 60816095) B60816095
theorem B1386495 : Blo 1385512 1386495 := bstep (se 1 (by rfl) ⟨1039871, by rfl⟩ : syracuseStep 1386495 = 2079743) B2079743
theorem B1755199 : Blo 1385512 1755199 := bstep (se 1 (by rfl) ⟨1316399, by rfl⟩ : syracuseStep 1755199 = 2632799) B2632799
theorem B11847869 : Blo 1385512 11847869 := bstep (se 3 (by rfl) ⟨2221475, by rfl⟩ : syracuseStep 11847869 = 4442951) B4442951
theorem B25979255 : Blo 1385512 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B1386975 : Blo 1385512 1386975 := bstep (se 1 (by rfl) ⟨1040231, by rfl⟩ : syracuseStep 1386975 = 2080463) B2080463
theorem B1387007 : Blo 1385512 1387007 := bstep (se 1 (by rfl) ⟨1040255, by rfl⟩ : syracuseStep 1387007 = 2080511) B2080511
theorem B5925473 : Blo 1385512 5925473 := bstep (se 2 (by rfl) ⟨2222052, by rfl⟩ : syracuseStep 5925473 = 4444105) B4444105
theorem B21351059 : Blo 1385512 21351059 := bstep (se 1 (by rfl) ⟨16013294, by rfl⟩ : syracuseStep 21351059 = 32026589) B32026589
theorem B1387239 : Blo 1385512 1387239 := bstep (se 1 (by rfl) ⟨1040429, by rfl⟩ : syracuseStep 1387239 = 2080859) B2080859
theorem B1559407 : Blo 1385512 1559407 := bstep (se 1 (by rfl) ⟨1169555, by rfl⟩ : syracuseStep 1559407 = 2339111) B2339111
theorem B12643457 : Blo 1385512 12643457 := bstep (se 2 (by rfl) ⟨4741296, by rfl⟩ : syracuseStep 12643457 = 9482593) B9482593
theorem B2739839 : Blo 1385512 2739839 := bstep (se 1 (by rfl) ⟨2054879, by rfl⟩ : syracuseStep 2739839 = 4109759) B4109759
theorem B7016381 : Blo 1385512 7016381 := bstep (se 3 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 7016381 = 2631143) B2631143
theorem B2961643 : Blo 1385512 2961643 := bstep (se 1 (by rfl) ⟨2221232, by rfl⟩ : syracuseStep 2961643 = 4442465) B4442465
theorem B10522871 : Blo 1385512 10522871 := bstep (se 1 (by rfl) ⟨7892153, by rfl⟩ : syracuseStep 10522871 = 15784307) B15784307
theorem B2339327 : Blo 1385512 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B2339867 : Blo 1385512 2339867 := bstep (se 1 (by rfl) ⟨1754900, by rfl⟩ : syracuseStep 2339867 = 3509801) B3509801
theorem B2339995 : Blo 1385512 2339995 := bstep (se 1 (by rfl) ⟨1754996, by rfl⟩ : syracuseStep 2339995 = 3509993) B3509993
theorem B3118463 : Blo 1385512 3118463 := bstep (se 1 (by rfl) ⟨2338847, by rfl⟩ : syracuseStep 3118463 = 4677695) B4677695
theorem B5264959 : Blo 1385512 5264959 := bstep (se 1 (by rfl) ⟨3948719, by rfl⟩ : syracuseStep 5264959 = 7897439) B7897439
theorem B11843495 : Blo 1385512 11843495 := bstep (se 1 (by rfl) ⟨8882621, by rfl⟩ : syracuseStep 11843495 = 17765243) B17765243
theorem B1481599 : Blo 1385512 1481599 := bstep (se 1 (by rfl) ⟨1111199, by rfl⟩ : syracuseStep 1481599 = 2222399) B2222399
theorem B5618651 : Blo 1385512 5618651 := bstep (se 1 (by rfl) ⟨4213988, by rfl⟩ : syracuseStep 5618651 = 8427977) B8427977
theorem B3120191 : Blo 1385512 3120191 := bstep (se 1 (by rfl) ⟨2340143, by rfl⟩ : syracuseStep 3120191 = 4680287) B4680287
theorem B2079935 : Blo 1385512 2079935 := bstep (se 1 (by rfl) ⟨1559951, by rfl⟩ : syracuseStep 2079935 = 3119903) B3119903
theorem B85393601 : Blo 1385512 85393601 := bstep (se 2 (by rfl) ⟨32022600, by rfl⟩ : syracuseStep 85393601 = 64045201) B64045201
theorem B2080991 : Blo 1385512 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B3948857 : Blo 1385512 3948857 := bstep (se 2 (by rfl) ⟨1480821, by rfl⟩ : syracuseStep 3948857 = 2961643) B2961643
theorem B4440491 : Blo 1385512 4440491 := bstep (se 1 (by rfl) ⟨3330368, by rfl⟩ : syracuseStep 4440491 = 6660737) B6660737
theorem B1975465 : Blo 1385512 1975465 := bstep (se 2 (by rfl) ⟨740799, by rfl⟩ : syracuseStep 1975465 = 1481599) B1481599
theorem B7898579 : Blo 1385512 7898579 := bstep (se 1 (by rfl) ⟨5923934, by rfl⟩ : syracuseStep 7898579 = 11847869) B11847869
theorem B17319503 : Blo 1385512 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B3950315 : Blo 1385512 3950315 := bstep (se 1 (by rfl) ⟨2962736, by rfl⟩ : syracuseStep 3950315 = 5925473) B5925473
theorem B1386623 : Blo 1385512 1386623 := bstep (se 1 (by rfl) ⟨1039967, by rfl⟩ : syracuseStep 1386623 = 2079935) B2079935
theorem B7015247 : Blo 1385512 7015247 := bstep (se 1 (by rfl) ⟨5261435, by rfl⟩ : syracuseStep 7015247 = 10522871) B10522871
theorem B1559551 : Blo 1385512 1559551 := bstep (se 1 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 1559551 = 2339327) B2339327
theorem B1559911 : Blo 1385512 1559911 := bstep (se 1 (by rfl) ⟨1169933, by rfl⟩ : syracuseStep 1559911 = 2339867) B2339867
theorem B4500893 : Blo 1385512 4500893 := bstep (se 3 (by rfl) ⟨843917, by rfl⟩ : syracuseStep 4500893 = 1687835) B1687835
theorem B27029375 : Blo 1385512 27029375 := bstep (se 1 (by rfl) ⟨20272031, by rfl⟩ : syracuseStep 27029375 = 40544063) B40544063
theorem B14234039 : Blo 1385512 14234039 := bstep (se 1 (by rfl) ⟨10675529, by rfl⟩ : syracuseStep 14234039 = 21351059) B21351059
theorem B2340265 : Blo 1385512 2340265 := bstep (se 2 (by rfl) ⟨877599, by rfl⟩ : syracuseStep 2340265 = 1755199) B1755199
theorem B5625283 : Blo 1385512 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B64017863 : Blo 1385512 64017863 := bstep (se 1 (by rfl) ⟨48013397, by rfl⟩ : syracuseStep 64017863 = 96026795) B96026795
theorem B3118751 : Blo 1385512 3118751 := bstep (se 1 (by rfl) ⟨2339063, by rfl⟩ : syracuseStep 3118751 = 4678127) B4678127
theorem B2078975 : Blo 1385512 2078975 := bstep (se 1 (by rfl) ⟨1559231, by rfl⟩ : syracuseStep 2078975 = 3118463) B3118463
theorem B2079209 : Blo 1385512 2079209 := bstep (se 2 (by rfl) ⟨779703, by rfl⟩ : syracuseStep 2079209 = 1559407) B1559407
theorem B7895663 : Blo 1385512 7895663 := bstep (se 1 (by rfl) ⟨5921747, by rfl⟩ : syracuseStep 7895663 = 11843495) B11843495
theorem B134863541 : Blo 1385512 134863541 := bstep (se 5 (by rfl) ⟨6321728, by rfl⟩ : syracuseStep 134863541 = 12643457) B12643457
theorem B3119993 : Blo 1385512 3119993 := bstep (se 2 (by rfl) ⟨1169997, by rfl⟩ : syracuseStep 3119993 = 2339995) B2339995
theorem B7306237 : Blo 1385512 7306237 := bstep (se 3 (by rfl) ⟨1369919, by rfl⟩ : syracuseStep 7306237 = 2739839) B2739839
theorem B2080127 : Blo 1385512 2080127 := bstep (se 1 (by rfl) ⟨1560095, by rfl⟩ : syracuseStep 2080127 = 3120191) B3120191
theorem B7019945 : Blo 1385512 7019945 := bstep (se 2 (by rfl) ⟨2632479, by rfl⟩ : syracuseStep 7019945 = 5264959) B5264959
theorem B14983069 : Blo 1385512 14983069 := bstep (se 3 (by rfl) ⟨2809325, by rfl⟩ : syracuseStep 14983069 = 5618651) B5618651
theorem B4677587 : Blo 1385512 4677587 := bstep (se 1 (by rfl) ⟨3508190, by rfl⟩ : syracuseStep 4677587 = 7016381) B7016381
theorem B9741649 : Blo 1385512 9741649 := bstep (se 2 (by rfl) ⟨3653118, by rfl⟩ : syracuseStep 9741649 = 7306237) B7306237
theorem B1385983 : Blo 1385512 1385983 := bstep (se 1 (by rfl) ⟨1039487, by rfl⟩ : syracuseStep 1385983 = 2078975) B2078975
theorem B1386139 : Blo 1385512 1386139 := bstep (se 1 (by rfl) ⟨1039604, by rfl⟩ : syracuseStep 1386139 = 2079209) B2079209
theorem B89909027 : Blo 1385512 89909027 := bstep (se 1 (by rfl) ⟨67431770, by rfl⟩ : syracuseStep 89909027 = 134863541) B134863541
theorem B1386751 : Blo 1385512 1386751 := bstep (se 1 (by rfl) ⟨1040063, by rfl⟩ : syracuseStep 1386751 = 2080127) B2080127
theorem B3000595 : Blo 1385512 3000595 := bstep (se 1 (by rfl) ⟨2250446, by rfl⟩ : syracuseStep 3000595 = 4500893) B4500893
theorem B4679963 : Blo 1385512 4679963 := bstep (se 1 (by rfl) ⟨3509972, by rfl⟩ : syracuseStep 4679963 = 7019945) B7019945
theorem B56929067 : Blo 1385512 56929067 := bstep (se 1 (by rfl) ⟨42696800, by rfl⟩ : syracuseStep 56929067 = 85393601) B85393601
theorem B1387327 : Blo 1385512 1387327 := bstep (se 1 (by rfl) ⟨1040495, by rfl⟩ : syracuseStep 1387327 = 2080991) B2080991
theorem B2632571 : Blo 1385512 2632571 := bstep (se 1 (by rfl) ⟨1974428, by rfl⟩ : syracuseStep 2632571 = 3948857) B3948857
theorem B2960327 : Blo 1385512 2960327 := bstep (se 1 (by rfl) ⟨2220245, by rfl⟩ : syracuseStep 2960327 = 4440491) B4440491
theorem B9489359 : Blo 1385512 9489359 := bstep (se 1 (by rfl) ⟨7117019, by rfl⟩ : syracuseStep 9489359 = 14234039) B14234039
theorem B11546335 : Blo 1385512 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B2633543 : Blo 1385512 2633543 := bstep (se 1 (by rfl) ⟨1975157, by rfl⟩ : syracuseStep 2633543 = 3950315) B3950315
theorem B2633953 : Blo 1385512 2633953 := bstep (se 2 (by rfl) ⟨987732, by rfl⟩ : syracuseStep 2633953 = 1975465) B1975465
theorem B5263775 : Blo 1385512 5263775 := bstep (se 1 (by rfl) ⟨3947831, by rfl⟩ : syracuseStep 5263775 = 7895663) B7895663
theorem B7500377 : Blo 1385512 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B19977425 : Blo 1385512 19977425 := bstep (se 2 (by rfl) ⟨7491534, by rfl⟩ : syracuseStep 19977425 = 14983069) B14983069
theorem B18019583 : Blo 1385512 18019583 := bstep (se 1 (by rfl) ⟨13514687, by rfl⟩ : syracuseStep 18019583 = 27029375) B27029375
theorem B3118391 : Blo 1385512 3118391 := bstep (se 1 (by rfl) ⟨2338793, by rfl⟩ : syracuseStep 3118391 = 4677587) B4677587
theorem B42678575 : Blo 1385512 42678575 := bstep (se 1 (by rfl) ⟨32008931, by rfl⟩ : syracuseStep 42678575 = 64017863) B64017863
theorem B5265719 : Blo 1385512 5265719 := bstep (se 1 (by rfl) ⟨3949289, by rfl⟩ : syracuseStep 5265719 = 7898579) B7898579
theorem B2079167 : Blo 1385512 2079167 := bstep (se 1 (by rfl) ⟨1559375, by rfl⟩ : syracuseStep 2079167 = 3118751) B3118751
theorem B2079401 : Blo 1385512 2079401 := bstep (se 2 (by rfl) ⟨779775, by rfl⟩ : syracuseStep 2079401 = 1559551) B1559551
theorem B2079881 : Blo 1385512 2079881 := bstep (se 2 (by rfl) ⟨779955, by rfl⟩ : syracuseStep 2079881 = 1559911) B1559911
theorem B4676831 : Blo 1385512 4676831 := bstep (se 1 (by rfl) ⟨3507623, by rfl⟩ : syracuseStep 4676831 = 7015247) B7015247
theorem B3120353 : Blo 1385512 3120353 := bstep (se 2 (by rfl) ⟨1170132, by rfl⟩ : syracuseStep 3120353 = 2340265) B2340265
theorem B2079995 : Blo 1385512 2079995 := bstep (se 1 (by rfl) ⟨1559996, by rfl⟩ : syracuseStep 2079995 = 3119993) B3119993
theorem B64012693 : Blo 1385512 64012693 := bstep (se 6 (by rfl) ⟨1500297, by rfl⟩ : syracuseStep 64012693 = 3000595) B3000595
theorem B28452383 : Blo 1385512 28452383 := bstep (se 1 (by rfl) ⟨21339287, by rfl⟩ : syracuseStep 28452383 = 42678575) B42678575
theorem B1386111 : Blo 1385512 1386111 := bstep (se 1 (by rfl) ⟨1039583, by rfl⟩ : syracuseStep 1386111 = 2079167) B2079167
theorem B1386267 : Blo 1385512 1386267 := bstep (se 1 (by rfl) ⟨1039700, by rfl⟩ : syracuseStep 1386267 = 2079401) B2079401
theorem B1755047 : Blo 1385512 1755047 := bstep (se 1 (by rfl) ⟨1316285, by rfl⟩ : syracuseStep 1755047 = 2632571) B2632571
theorem B1386587 : Blo 1385512 1386587 := bstep (se 1 (by rfl) ⟨1039940, by rfl⟩ : syracuseStep 1386587 = 2079881) B2079881
theorem B1386663 : Blo 1385512 1386663 := bstep (se 1 (by rfl) ⟨1039997, by rfl⟩ : syracuseStep 1386663 = 2079995) B2079995
theorem B15395113 : Blo 1385512 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B1755695 : Blo 1385512 1755695 := bstep (se 1 (by rfl) ⟨1316771, by rfl⟩ : syracuseStep 1755695 = 2633543) B2633543
theorem B3509183 : Blo 1385512 3509183 := bstep (se 1 (by rfl) ⟨2631887, by rfl⟩ : syracuseStep 3509183 = 5263775) B5263775
theorem B12013055 : Blo 1385512 12013055 := bstep (se 1 (by rfl) ⟨9009791, by rfl⟩ : syracuseStep 12013055 = 18019583) B18019583
theorem B3510479 : Blo 1385512 3510479 := bstep (se 1 (by rfl) ⟨2632859, by rfl⟩ : syracuseStep 3510479 = 5265719) B5265719
theorem B20001005 : Blo 1385512 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B12988865 : Blo 1385512 12988865 := bstep (se 2 (by rfl) ⟨4870824, by rfl⟩ : syracuseStep 12988865 = 9741649) B9741649
theorem B3117887 : Blo 1385512 3117887 := bstep (se 1 (by rfl) ⟨2338415, by rfl⟩ : syracuseStep 3117887 = 4676831) B4676831
theorem B7894205 : Blo 1385512 7894205 := bstep (se 3 (by rfl) ⟨1480163, by rfl⟩ : syracuseStep 7894205 = 2960327) B2960327
theorem B3511937 : Blo 1385512 3511937 := bstep (se 2 (by rfl) ⟨1316976, by rfl⟩ : syracuseStep 3511937 = 2633953) B2633953
theorem B13318283 : Blo 1385512 13318283 := bstep (se 1 (by rfl) ⟨9988712, by rfl⟩ : syracuseStep 13318283 = 19977425) B19977425
theorem B2078927 : Blo 1385512 2078927 := bstep (se 1 (by rfl) ⟨1559195, by rfl⟩ : syracuseStep 2078927 = 3118391) B3118391
theorem B59939351 : Blo 1385512 59939351 := bstep (se 1 (by rfl) ⟨44954513, by rfl⟩ : syracuseStep 59939351 = 89909027) B89909027
theorem B3119975 : Blo 1385512 3119975 := bstep (se 1 (by rfl) ⟨2339981, by rfl⟩ : syracuseStep 3119975 = 4679963) B4679963
theorem B37952711 : Blo 1385512 37952711 := bstep (se 1 (by rfl) ⟨28464533, by rfl⟩ : syracuseStep 37952711 = 56929067) B56929067
theorem B2080235 : Blo 1385512 2080235 := bstep (se 1 (by rfl) ⟨1560176, by rfl⟩ : syracuseStep 2080235 = 3120353) B3120353
theorem B25304957 : Blo 1385512 25304957 := bstep (se 3 (by rfl) ⟨4744679, by rfl⟩ : syracuseStep 25304957 = 9489359) B9489359
theorem B8659243 : Blo 1385512 8659243 := bstep (se 1 (by rfl) ⟨6494432, by rfl⟩ : syracuseStep 8659243 = 12988865) B12988865
theorem B1385951 : Blo 1385512 1385951 := bstep (se 1 (by rfl) ⟨1039463, by rfl⟩ : syracuseStep 1385951 = 2078927) B2078927
theorem B1386823 : Blo 1385512 1386823 := bstep (se 1 (by rfl) ⟨1040117, by rfl⟩ : syracuseStep 1386823 = 2080235) B2080235
theorem B4680125 : Blo 1385512 4680125 := bstep (se 3 (by rfl) ⟨877523, by rfl⟩ : syracuseStep 4680125 = 1755047) B1755047
theorem B16869971 : Blo 1385512 16869971 := bstep (se 1 (by rfl) ⟨12652478, by rfl⟩ : syracuseStep 16869971 = 25304957) B25304957
theorem B5262803 : Blo 1385512 5262803 := bstep (se 1 (by rfl) ⟨3947102, by rfl⟩ : syracuseStep 5262803 = 7894205) B7894205
theorem B18968255 : Blo 1385512 18968255 := bstep (se 1 (by rfl) ⟨14226191, by rfl⟩ : syracuseStep 18968255 = 28452383) B28452383
theorem B4681853 : Blo 1385512 4681853 := bstep (se 3 (by rfl) ⟨877847, by rfl⟩ : syracuseStep 4681853 = 1755695) B1755695
theorem B2339455 : Blo 1385512 2339455 := bstep (se 1 (by rfl) ⟨1754591, by rfl⟩ : syracuseStep 2339455 = 3509183) B3509183
theorem B25301807 : Blo 1385512 25301807 := bstep (se 1 (by rfl) ⟨18976355, by rfl⟩ : syracuseStep 25301807 = 37952711) B37952711
theorem B8008703 : Blo 1385512 8008703 := bstep (se 1 (by rfl) ⟨6006527, by rfl⟩ : syracuseStep 8008703 = 12013055) B12013055
theorem B2340319 : Blo 1385512 2340319 := bstep (se 1 (by rfl) ⟨1755239, by rfl⟩ : syracuseStep 2340319 = 3510479) B3510479
theorem B13334003 : Blo 1385512 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B20526817 : Blo 1385512 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B85350257 : Blo 1385512 85350257 := bstep (se 2 (by rfl) ⟨32006346, by rfl⟩ : syracuseStep 85350257 = 64012693) B64012693
theorem B2078591 : Blo 1385512 2078591 := bstep (se 1 (by rfl) ⟨1558943, by rfl⟩ : syracuseStep 2078591 = 3117887) B3117887
theorem B2341291 : Blo 1385512 2341291 := bstep (se 1 (by rfl) ⟨1755968, by rfl⟩ : syracuseStep 2341291 = 3511937) B3511937
theorem B8878855 : Blo 1385512 8878855 := bstep (se 1 (by rfl) ⟨6659141, by rfl⟩ : syracuseStep 8878855 = 13318283) B13318283
theorem B39959567 : Blo 1385512 39959567 := bstep (se 1 (by rfl) ⟨29969675, by rfl⟩ : syracuseStep 39959567 = 59939351) B59939351
theorem B2079983 : Blo 1385512 2079983 := bstep (se 1 (by rfl) ⟨1559987, by rfl⟩ : syracuseStep 2079983 = 3119975) B3119975
theorem B3121235 : Blo 1385512 3121235 := bstep (se 1 (by rfl) ⟨2340926, by rfl⟩ : syracuseStep 3121235 = 4681853) B4681853
theorem B16867871 : Blo 1385512 16867871 := bstep (se 1 (by rfl) ⟨12650903, by rfl⟩ : syracuseStep 16867871 = 25301807) B25301807
theorem B3121721 : Blo 1385512 3121721 := bstep (se 2 (by rfl) ⟨1170645, by rfl⟩ : syracuseStep 3121721 = 2341291) B2341291
theorem B8889335 : Blo 1385512 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B11838473 : Blo 1385512 11838473 := bstep (se 2 (by rfl) ⟨4439427, by rfl⟩ : syracuseStep 11838473 = 8878855) B8878855
theorem B1385727 : Blo 1385512 1385727 := bstep (se 1 (by rfl) ⟨1039295, by rfl⟩ : syracuseStep 1385727 = 2078591) B2078591
theorem B1386655 : Blo 1385512 1386655 := bstep (se 1 (by rfl) ⟨1039991, by rfl⟩ : syracuseStep 1386655 = 2079983) B2079983
theorem B3508535 : Blo 1385512 3508535 := bstep (se 1 (by rfl) ⟨2631401, by rfl⟩ : syracuseStep 3508535 = 5262803) B5262803
theorem B46182629 : Blo 1385512 46182629 := bstep (se 4 (by rfl) ⟨4329621, by rfl⟩ : syracuseStep 46182629 = 8659243) B8659243
theorem B12645503 : Blo 1385512 12645503 := bstep (se 1 (by rfl) ⟨9484127, by rfl⟩ : syracuseStep 12645503 = 18968255) B18968255
theorem B5339135 : Blo 1385512 5339135 := bstep (se 1 (by rfl) ⟨4004351, by rfl⟩ : syracuseStep 5339135 = 8008703) B8008703
theorem B3119273 : Blo 1385512 3119273 := bstep (se 2 (by rfl) ⟨1169727, by rfl⟩ : syracuseStep 3119273 = 2339455) B2339455
theorem B56900171 : Blo 1385512 56900171 := bstep (se 1 (by rfl) ⟨42675128, by rfl⟩ : syracuseStep 56900171 = 85350257) B85350257
theorem B3120083 : Blo 1385512 3120083 := bstep (se 1 (by rfl) ⟨2340062, by rfl⟩ : syracuseStep 3120083 = 4680125) B4680125
theorem B11246647 : Blo 1385512 11246647 := bstep (se 1 (by rfl) ⟨8434985, by rfl⟩ : syracuseStep 11246647 = 16869971) B16869971
theorem B3120425 : Blo 1385512 3120425 := bstep (se 2 (by rfl) ⟨1170159, by rfl⟩ : syracuseStep 3120425 = 2340319) B2340319
theorem B26639711 : Blo 1385512 26639711 := bstep (se 1 (by rfl) ⟨19979783, by rfl⟩ : syracuseStep 26639711 = 39959567) B39959567
theorem B27369089 : Blo 1385512 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B2080823 : Blo 1385512 2080823 := bstep (se 1 (by rfl) ⟨1560617, by rfl⟩ : syracuseStep 2080823 = 3121235) B3121235
theorem B2081147 : Blo 1385512 2081147 := bstep (se 1 (by rfl) ⟨1560860, by rfl⟩ : syracuseStep 2081147 = 3121721) B3121721
theorem B8430335 : Blo 1385512 8430335 := bstep (se 1 (by rfl) ⟨6322751, by rfl⟩ : syracuseStep 8430335 = 12645503) B12645503
theorem B18246059 : Blo 1385512 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B30788419 : Blo 1385512 30788419 := bstep (se 1 (by rfl) ⟨23091314, by rfl⟩ : syracuseStep 30788419 = 46182629) B46182629
theorem B5926223 : Blo 1385512 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B7892315 : Blo 1385512 7892315 := bstep (se 1 (by rfl) ⟨5919236, by rfl⟩ : syracuseStep 7892315 = 11838473) B11838473
theorem B3559423 : Blo 1385512 3559423 := bstep (se 1 (by rfl) ⟨2669567, by rfl⟩ : syracuseStep 3559423 = 5339135) B5339135
theorem B14995529 : Blo 1385512 14995529 := bstep (se 2 (by rfl) ⟨5623323, by rfl⟩ : syracuseStep 14995529 = 11246647) B11246647
theorem B2339023 : Blo 1385512 2339023 := bstep (se 1 (by rfl) ⟨1754267, by rfl⟩ : syracuseStep 2339023 = 3508535) B3508535
theorem B37933447 : Blo 1385512 37933447 := bstep (se 1 (by rfl) ⟨28450085, by rfl⟩ : syracuseStep 37933447 = 56900171) B56900171
theorem B11245247 : Blo 1385512 11245247 := bstep (se 1 (by rfl) ⟨8433935, by rfl⟩ : syracuseStep 11245247 = 16867871) B16867871
theorem B2079515 : Blo 1385512 2079515 := bstep (se 1 (by rfl) ⟨1559636, by rfl⟩ : syracuseStep 2079515 = 3119273) B3119273
theorem B2080055 : Blo 1385512 2080055 := bstep (se 1 (by rfl) ⟨1560041, by rfl⟩ : syracuseStep 2080055 = 3120083) B3120083
theorem B2080283 : Blo 1385512 2080283 := bstep (se 1 (by rfl) ⟨1560212, by rfl⟩ : syracuseStep 2080283 = 3120425) B3120425
theorem B17759807 : Blo 1385512 17759807 := bstep (se 1 (by rfl) ⟨13319855, by rfl⟩ : syracuseStep 17759807 = 26639711) B26639711
theorem B5620223 : Blo 1385512 5620223 := bstep (se 1 (by rfl) ⟨4215167, by rfl⟩ : syracuseStep 5620223 = 8430335) B8430335
theorem B50577929 : Blo 1385512 50577929 := bstep (se 2 (by rfl) ⟨18966723, by rfl⟩ : syracuseStep 50577929 = 37933447) B37933447
theorem B15803261 : Blo 1385512 15803261 := bstep (se 3 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 15803261 = 5926223) B5926223
theorem B41051225 : Blo 1385512 41051225 := bstep (se 2 (by rfl) ⟨15394209, by rfl⟩ : syracuseStep 41051225 = 30788419) B30788419
theorem B7496831 : Blo 1385512 7496831 := bstep (se 1 (by rfl) ⟨5622623, by rfl⟩ : syracuseStep 7496831 = 11245247) B11245247
theorem B1386343 : Blo 1385512 1386343 := bstep (se 1 (by rfl) ⟨1039757, by rfl⟩ : syracuseStep 1386343 = 2079515) B2079515
theorem B1386703 : Blo 1385512 1386703 := bstep (se 1 (by rfl) ⟨1040027, by rfl⟩ : syracuseStep 1386703 = 2080055) B2080055
theorem B5261543 : Blo 1385512 5261543 := bstep (se 1 (by rfl) ⟨3946157, by rfl⟩ : syracuseStep 5261543 = 7892315) B7892315
theorem B1386855 : Blo 1385512 1386855 := bstep (se 1 (by rfl) ⟨1040141, by rfl⟩ : syracuseStep 1386855 = 2080283) B2080283
theorem B11839871 : Blo 1385512 11839871 := bstep (se 1 (by rfl) ⟨8879903, by rfl⟩ : syracuseStep 11839871 = 17759807) B17759807
theorem B4745897 : Blo 1385512 4745897 := bstep (se 2 (by rfl) ⟨1779711, by rfl⟩ : syracuseStep 4745897 = 3559423) B3559423
theorem B1387215 : Blo 1385512 1387215 := bstep (se 1 (by rfl) ⟨1040411, by rfl⟩ : syracuseStep 1387215 = 2080823) B2080823
theorem B9997019 : Blo 1385512 9997019 := bstep (se 1 (by rfl) ⟨7497764, by rfl⟩ : syracuseStep 9997019 = 14995529) B14995529
theorem B1387431 : Blo 1385512 1387431 := bstep (se 1 (by rfl) ⟨1040573, by rfl⟩ : syracuseStep 1387431 = 2081147) B2081147
theorem B3118697 : Blo 1385512 3118697 := bstep (se 2 (by rfl) ⟨1169511, by rfl⟩ : syracuseStep 3118697 = 2339023) B2339023
theorem B12164039 : Blo 1385512 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B33718619 : Blo 1385512 33718619 := bstep (se 1 (by rfl) ⟨25288964, by rfl⟩ : syracuseStep 33718619 = 50577929) B50577929
theorem B10535507 : Blo 1385512 10535507 := bstep (se 1 (by rfl) ⟨7901630, by rfl⟩ : syracuseStep 10535507 = 15803261) B15803261
theorem B3507695 : Blo 1385512 3507695 := bstep (se 1 (by rfl) ⟨2630771, by rfl⟩ : syracuseStep 3507695 = 5261543) B5261543
theorem B3163931 : Blo 1385512 3163931 := bstep (se 1 (by rfl) ⟨2372948, by rfl⟩ : syracuseStep 3163931 = 4745897) B4745897
theorem B19991549 : Blo 1385512 19991549 := bstep (se 3 (by rfl) ⟨3748415, by rfl⟩ : syracuseStep 19991549 = 7496831) B7496831
theorem B14987261 : Blo 1385512 14987261 := bstep (se 3 (by rfl) ⟨2810111, by rfl⟩ : syracuseStep 14987261 = 5620223) B5620223
theorem B7893247 : Blo 1385512 7893247 := bstep (se 1 (by rfl) ⟨5919935, by rfl⟩ : syracuseStep 7893247 = 11839871) B11839871
theorem B6664679 : Blo 1385512 6664679 := bstep (se 1 (by rfl) ⟨4998509, by rfl⟩ : syracuseStep 6664679 = 9997019) B9997019
theorem B27367483 : Blo 1385512 27367483 := bstep (se 1 (by rfl) ⟨20525612, by rfl⟩ : syracuseStep 27367483 = 41051225) B41051225
theorem B2079131 : Blo 1385512 2079131 := bstep (se 1 (by rfl) ⟨1559348, by rfl⟩ : syracuseStep 2079131 = 3118697) B3118697
theorem B8109359 : Blo 1385512 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B22479079 : Blo 1385512 22479079 := bstep (se 1 (by rfl) ⟨16859309, by rfl⟩ : syracuseStep 22479079 = 33718619) B33718619
theorem B1386087 : Blo 1385512 1386087 := bstep (se 1 (by rfl) ⟨1039565, by rfl⟩ : syracuseStep 1386087 = 2079131) B2079131
theorem B36489977 : Blo 1385512 36489977 := bstep (se 2 (by rfl) ⟨13683741, by rfl⟩ : syracuseStep 36489977 = 27367483) B27367483
theorem B4443119 : Blo 1385512 4443119 := bstep (se 1 (by rfl) ⟨3332339, by rfl⟩ : syracuseStep 4443119 = 6664679) B6664679
theorem B7023671 : Blo 1385512 7023671 := bstep (se 1 (by rfl) ⟨5267753, by rfl⟩ : syracuseStep 7023671 = 10535507) B10535507
theorem B2338463 : Blo 1385512 2338463 := bstep (se 1 (by rfl) ⟨1753847, by rfl⟩ : syracuseStep 2338463 = 3507695) B3507695
theorem B2109287 : Blo 1385512 2109287 := bstep (se 1 (by rfl) ⟨1581965, by rfl⟩ : syracuseStep 2109287 = 3163931) B3163931
theorem B9991507 : Blo 1385512 9991507 := bstep (se 1 (by rfl) ⟨7493630, by rfl⟩ : syracuseStep 9991507 = 14987261) B14987261
theorem B10524329 : Blo 1385512 10524329 := bstep (se 2 (by rfl) ⟨3946623, by rfl⟩ : syracuseStep 10524329 = 7893247) B7893247
theorem B13327699 : Blo 1385512 13327699 := bstep (se 1 (by rfl) ⟨9995774, by rfl⟩ : syracuseStep 13327699 = 19991549) B19991549
theorem B5406239 : Blo 1385512 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B13322009 : Blo 1385512 13322009 := bstep (se 2 (by rfl) ⟨4995753, by rfl⟩ : syracuseStep 13322009 = 9991507) B9991507
theorem B17770265 : Blo 1385512 17770265 := bstep (se 2 (by rfl) ⟨6663849, by rfl⟩ : syracuseStep 17770265 = 13327699) B13327699
theorem B1558975 : Blo 1385512 1558975 := bstep (se 1 (by rfl) ⟨1169231, by rfl⟩ : syracuseStep 1558975 = 2338463) B2338463
theorem B7016219 : Blo 1385512 7016219 := bstep (se 1 (by rfl) ⟨5262164, by rfl⟩ : syracuseStep 7016219 = 10524329) B10524329
theorem B24326651 : Blo 1385512 24326651 := bstep (se 1 (by rfl) ⟨18244988, by rfl⟩ : syracuseStep 24326651 = 36489977) B36489977
theorem B2962079 : Blo 1385512 2962079 := bstep (se 1 (by rfl) ⟨2221559, by rfl⟩ : syracuseStep 2962079 = 4443119) B4443119
theorem B4682447 : Blo 1385512 4682447 := bstep (se 1 (by rfl) ⟨3511835, by rfl⟩ : syracuseStep 4682447 = 7023671) B7023671
theorem B5624765 : Blo 1385512 5624765 := bstep (se 3 (by rfl) ⟨1054643, by rfl⟩ : syracuseStep 5624765 = 2109287) B2109287
theorem B29972105 : Blo 1385512 29972105 := bstep (se 2 (by rfl) ⟨11239539, by rfl⟩ : syracuseStep 29972105 = 22479079) B22479079
theorem B3604159 : Blo 1385512 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B1974719 : Blo 1385512 1974719 := bstep (se 1 (by rfl) ⟨1481039, by rfl⟩ : syracuseStep 1974719 = 2962079) B2962079
theorem B3121631 : Blo 1385512 3121631 := bstep (se 1 (by rfl) ⟨2341223, by rfl⟩ : syracuseStep 3121631 = 4682447) B4682447
theorem B19981403 : Blo 1385512 19981403 := bstep (se 1 (by rfl) ⟨14986052, by rfl⟩ : syracuseStep 19981403 = 29972105) B29972105
theorem B8881339 : Blo 1385512 8881339 := bstep (se 1 (by rfl) ⟨6661004, by rfl⟩ : syracuseStep 8881339 = 13322009) B13322009
theorem B11846843 : Blo 1385512 11846843 := bstep (se 1 (by rfl) ⟨8885132, by rfl⟩ : syracuseStep 11846843 = 17770265) B17770265
theorem B19222181 : Blo 1385512 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B16217767 : Blo 1385512 16217767 := bstep (se 1 (by rfl) ⟨12163325, by rfl⟩ : syracuseStep 16217767 = 24326651) B24326651
theorem B2078633 : Blo 1385512 2078633 := bstep (se 2 (by rfl) ⟨779487, by rfl⟩ : syracuseStep 2078633 = 1558975) B1558975
theorem B3749843 : Blo 1385512 3749843 := bstep (se 1 (by rfl) ⟨2812382, by rfl⟩ : syracuseStep 3749843 = 5624765) B5624765
theorem B4677479 : Blo 1385512 4677479 := bstep (se 1 (by rfl) ⟨3508109, by rfl⟩ : syracuseStep 4677479 = 7016219) B7016219
theorem B2081087 : Blo 1385512 2081087 := bstep (se 1 (by rfl) ⟨1560815, by rfl⟩ : syracuseStep 2081087 = 3121631) B3121631
theorem B13320935 : Blo 1385512 13320935 := bstep (se 1 (by rfl) ⟨9990701, by rfl⟩ : syracuseStep 13320935 = 19981403) B19981403
theorem B7897895 : Blo 1385512 7897895 := bstep (se 1 (by rfl) ⟨5923421, by rfl⟩ : syracuseStep 7897895 = 11846843) B11846843
theorem B1385755 : Blo 1385512 1385755 := bstep (se 1 (by rfl) ⟨1039316, by rfl⟩ : syracuseStep 1385755 = 2078633) B2078633
theorem B2499895 : Blo 1385512 2499895 := bstep (se 1 (by rfl) ⟨1874921, by rfl⟩ : syracuseStep 2499895 = 3749843) B3749843
theorem B12814787 : Blo 1385512 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B11841785 : Blo 1385512 11841785 := bstep (se 2 (by rfl) ⟨4440669, by rfl⟩ : syracuseStep 11841785 = 8881339) B8881339
theorem B21623689 : Blo 1385512 21623689 := bstep (se 2 (by rfl) ⟨8108883, by rfl⟩ : syracuseStep 21623689 = 16217767) B16217767
theorem B3118319 : Blo 1385512 3118319 := bstep (se 1 (by rfl) ⟨2338739, by rfl⟩ : syracuseStep 3118319 = 4677479) B4677479
theorem B5265917 : Blo 1385512 5265917 := bstep (se 3 (by rfl) ⟨987359, by rfl⟩ : syracuseStep 5265917 = 1974719) B1974719
theorem B8880623 : Blo 1385512 8880623 := bstep (se 1 (by rfl) ⟨6660467, by rfl⟩ : syracuseStep 8880623 = 13320935) B13320935
theorem B1387391 : Blo 1385512 1387391 := bstep (se 1 (by rfl) ⟨1040543, by rfl⟩ : syracuseStep 1387391 = 2081087) B2081087
theorem B34172765 : Blo 1385512 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B3510611 : Blo 1385512 3510611 := bstep (se 1 (by rfl) ⟨2632958, by rfl⟩ : syracuseStep 3510611 = 5265917) B5265917
theorem B7894523 : Blo 1385512 7894523 := bstep (se 1 (by rfl) ⟨5920892, by rfl⟩ : syracuseStep 7894523 = 11841785) B11841785
theorem B5265263 : Blo 1385512 5265263 := bstep (se 1 (by rfl) ⟨3948947, by rfl⟩ : syracuseStep 5265263 = 7897895) B7897895
theorem B2078879 : Blo 1385512 2078879 := bstep (se 1 (by rfl) ⟨1559159, by rfl⟩ : syracuseStep 2078879 = 3118319) B3118319
theorem B3333193 : Blo 1385512 3333193 := bstep (se 2 (by rfl) ⟨1249947, by rfl⟩ : syracuseStep 3333193 = 2499895) B2499895
theorem B115326341 : Blo 1385512 115326341 := bstep (se 4 (by rfl) ⟨10811844, by rfl⟩ : syracuseStep 115326341 = 21623689) B21623689
theorem B17777029 : Blo 1385512 17777029 := bstep (se 4 (by rfl) ⟨1666596, by rfl⟩ : syracuseStep 17777029 = 3333193) B3333193
theorem B1385919 : Blo 1385512 1385919 := bstep (se 1 (by rfl) ⟨1039439, by rfl⟩ : syracuseStep 1385919 = 2078879) B2078879
theorem B76884227 : Blo 1385512 76884227 := bstep (se 1 (by rfl) ⟨57663170, by rfl⟩ : syracuseStep 76884227 = 115326341) B115326341
theorem B5263015 : Blo 1385512 5263015 := bstep (se 1 (by rfl) ⟨3947261, by rfl⟩ : syracuseStep 5263015 = 7894523) B7894523
theorem B3510175 : Blo 1385512 3510175 := bstep (se 1 (by rfl) ⟨2632631, by rfl⟩ : syracuseStep 3510175 = 5265263) B5265263
theorem B2340407 : Blo 1385512 2340407 := bstep (se 1 (by rfl) ⟨1755305, by rfl⟩ : syracuseStep 2340407 = 3510611) B3510611
theorem B5920415 : Blo 1385512 5920415 := bstep (se 1 (by rfl) ⟨4440311, by rfl⟩ : syracuseStep 5920415 = 8880623) B8880623
theorem B22781843 : Blo 1385512 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B4680233 : Blo 1385512 4680233 := bstep (se 2 (by rfl) ⟨1755087, by rfl⟩ : syracuseStep 4680233 = 3510175) B3510175
theorem B23702705 : Blo 1385512 23702705 := bstep (se 2 (by rfl) ⟨8888514, by rfl⟩ : syracuseStep 23702705 = 17777029) B17777029
theorem B1560271 : Blo 1385512 1560271 := bstep (se 1 (by rfl) ⟨1170203, by rfl⟩ : syracuseStep 1560271 = 2340407) B2340407
theorem B7017353 : Blo 1385512 7017353 := bstep (se 2 (by rfl) ⟨2631507, by rfl⟩ : syracuseStep 7017353 = 5263015) B5263015
theorem B3946943 : Blo 1385512 3946943 := bstep (se 1 (by rfl) ⟨2960207, by rfl⟩ : syracuseStep 3946943 = 5920415) B5920415
theorem B51256151 : Blo 1385512 51256151 := bstep (se 1 (by rfl) ⟨38442113, by rfl⟩ : syracuseStep 51256151 = 76884227) B76884227
theorem B15187895 : Blo 1385512 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B4678235 : Blo 1385512 4678235 := bstep (se 1 (by rfl) ⟨3508676, by rfl⟩ : syracuseStep 4678235 = 7017353) B7017353
theorem B2631295 : Blo 1385512 2631295 := bstep (se 1 (by rfl) ⟨1973471, by rfl⟩ : syracuseStep 2631295 = 3946943) B3946943
theorem B34170767 : Blo 1385512 34170767 := bstep (se 1 (by rfl) ⟨25628075, by rfl⟩ : syracuseStep 34170767 = 51256151) B51256151
theorem B3120155 : Blo 1385512 3120155 := bstep (se 1 (by rfl) ⟨2340116, by rfl⟩ : syracuseStep 3120155 = 4680233) B4680233
theorem B15801803 : Blo 1385512 15801803 := bstep (se 1 (by rfl) ⟨11851352, by rfl⟩ : syracuseStep 15801803 = 23702705) B23702705
theorem B2080361 : Blo 1385512 2080361 := bstep (se 2 (by rfl) ⟨780135, by rfl⟩ : syracuseStep 2080361 = 1560271) B1560271
theorem B10125263 : Blo 1385512 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B3508393 : Blo 1385512 3508393 := bstep (se 2 (by rfl) ⟨1315647, by rfl⟩ : syracuseStep 3508393 = 2631295) B2631295
theorem B1386907 : Blo 1385512 1386907 := bstep (se 1 (by rfl) ⟨1040180, by rfl⟩ : syracuseStep 1386907 = 2080361) B2080361
theorem B3118823 : Blo 1385512 3118823 := bstep (se 1 (by rfl) ⟨2339117, by rfl⟩ : syracuseStep 3118823 = 4678235) B4678235
theorem B22780511 : Blo 1385512 22780511 := bstep (se 1 (by rfl) ⟨17085383, by rfl⟩ : syracuseStep 22780511 = 34170767) B34170767
theorem B2080103 : Blo 1385512 2080103 := bstep (se 1 (by rfl) ⟨1560077, by rfl⟩ : syracuseStep 2080103 = 3120155) B3120155
theorem B10534535 : Blo 1385512 10534535 := bstep (se 1 (by rfl) ⟨7900901, by rfl⟩ : syracuseStep 10534535 = 15801803) B15801803
theorem B27000701 : Blo 1385512 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B4677857 : Blo 1385512 4677857 := bstep (se 2 (by rfl) ⟨1754196, by rfl⟩ : syracuseStep 4677857 = 3508393) B3508393
theorem B1386735 : Blo 1385512 1386735 := bstep (se 1 (by rfl) ⟨1040051, by rfl⟩ : syracuseStep 1386735 = 2080103) B2080103
theorem B7023023 : Blo 1385512 7023023 := bstep (se 1 (by rfl) ⟨5267267, by rfl⟩ : syracuseStep 7023023 = 10534535) B10534535
theorem B18000467 : Blo 1385512 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B2079215 : Blo 1385512 2079215 := bstep (se 1 (by rfl) ⟨1559411, by rfl⟩ : syracuseStep 2079215 = 3118823) B3118823
theorem B15187007 : Blo 1385512 15187007 := bstep (se 1 (by rfl) ⟨11390255, by rfl⟩ : syracuseStep 15187007 = 22780511) B22780511
theorem B1386143 : Blo 1385512 1386143 := bstep (se 1 (by rfl) ⟨1039607, by rfl⟩ : syracuseStep 1386143 = 2079215) B2079215
theorem B4682015 : Blo 1385512 4682015 := bstep (se 1 (by rfl) ⟨3511511, by rfl⟩ : syracuseStep 4682015 = 7023023) B7023023
theorem B3118571 : Blo 1385512 3118571 := bstep (se 1 (by rfl) ⟨2338928, by rfl⟩ : syracuseStep 3118571 = 4677857) B4677857
theorem B12000311 : Blo 1385512 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B10124671 : Blo 1385512 10124671 := bstep (se 1 (by rfl) ⟨7593503, by rfl⟩ : syracuseStep 10124671 = 15187007) B15187007
theorem B3121343 : Blo 1385512 3121343 := bstep (se 1 (by rfl) ⟨2341007, by rfl⟩ : syracuseStep 3121343 = 4682015) B4682015
theorem B8000207 : Blo 1385512 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B2079047 : Blo 1385512 2079047 := bstep (se 1 (by rfl) ⟨1559285, by rfl⟩ : syracuseStep 2079047 = 3118571) B3118571
theorem B13499561 : Blo 1385512 13499561 := bstep (se 2 (by rfl) ⟨5062335, by rfl⟩ : syracuseStep 13499561 = 10124671) B10124671
theorem B2080895 : Blo 1385512 2080895 := bstep (se 1 (by rfl) ⟨1560671, by rfl⟩ : syracuseStep 2080895 = 3121343) B3121343
theorem B5333471 : Blo 1385512 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B1386031 : Blo 1385512 1386031 := bstep (se 1 (by rfl) ⟨1039523, by rfl⟩ : syracuseStep 1386031 = 2079047) B2079047
theorem B8999707 : Blo 1385512 8999707 := bstep (se 1 (by rfl) ⟨6749780, by rfl⟩ : syracuseStep 8999707 = 13499561) B13499561
theorem B3555647 : Blo 1385512 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B1387263 : Blo 1385512 1387263 := bstep (se 1 (by rfl) ⟨1040447, by rfl⟩ : syracuseStep 1387263 = 2080895) B2080895
theorem B11999609 : Blo 1385512 11999609 := bstep (se 2 (by rfl) ⟨4499853, by rfl⟩ : syracuseStep 11999609 = 8999707) B8999707
theorem B2370431 : Blo 1385512 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B7999739 : Blo 1385512 7999739 := bstep (se 1 (by rfl) ⟨5999804, by rfl⟩ : syracuseStep 7999739 = 11999609) B11999609
theorem B5333159 : Blo 1385512 5333159 := bstep (se 1 (by rfl) ⟨3999869, by rfl⟩ : syracuseStep 5333159 = 7999739) B7999739
theorem B6321149 : Blo 1385512 6321149 := bstep (se 3 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 6321149 = 2370431) B2370431
theorem B14221757 : Blo 1385512 14221757 := bstep (se 3 (by rfl) ⟨2666579, by rfl⟩ : syracuseStep 14221757 = 5333159) B5333159
theorem B4214099 : Blo 1385512 4214099 := bstep (se 1 (by rfl) ⟨3160574, by rfl⟩ : syracuseStep 4214099 = 6321149) B6321149
theorem B37924685 : Blo 1385512 37924685 := bstep (se 3 (by rfl) ⟨7110878, by rfl⟩ : syracuseStep 37924685 = 14221757) B14221757
theorem B2809399 : Blo 1385512 2809399 := bstep (se 1 (by rfl) ⟨2107049, by rfl⟩ : syracuseStep 2809399 = 4214099) B4214099
theorem B3745865 : Blo 1385512 3745865 := bstep (se 2 (by rfl) ⟨1404699, by rfl⟩ : syracuseStep 3745865 = 2809399) B2809399
theorem B25283123 : Blo 1385512 25283123 := bstep (se 1 (by rfl) ⟨18962342, by rfl⟩ : syracuseStep 25283123 = 37924685) B37924685
theorem B16855415 : Blo 1385512 16855415 := bstep (se 1 (by rfl) ⟨12641561, by rfl⟩ : syracuseStep 16855415 = 25283123) B25283123
theorem B2497243 : Blo 1385512 2497243 := bstep (se 1 (by rfl) ⟨1872932, by rfl⟩ : syracuseStep 2497243 = 3745865) B3745865
theorem B3329657 : Blo 1385512 3329657 := bstep (se 2 (by rfl) ⟨1248621, by rfl⟩ : syracuseStep 3329657 = 2497243) B2497243
theorem B11236943 : Blo 1385512 11236943 := bstep (se 1 (by rfl) ⟨8427707, by rfl⟩ : syracuseStep 11236943 = 16855415) B16855415
theorem B7491295 : Blo 1385512 7491295 := bstep (se 1 (by rfl) ⟨5618471, by rfl⟩ : syracuseStep 7491295 = 11236943) B11236943
theorem B2219771 : Blo 1385512 2219771 := bstep (se 1 (by rfl) ⟨1664828, by rfl⟩ : syracuseStep 2219771 = 3329657) B3329657
theorem B39953573 : Blo 1385512 39953573 := bstep (se 4 (by rfl) ⟨3745647, by rfl⟩ : syracuseStep 39953573 = 7491295) B7491295
theorem B5919389 : Blo 1385512 5919389 := bstep (se 3 (by rfl) ⟨1109885, by rfl⟩ : syracuseStep 5919389 = 2219771) B2219771
theorem B26635715 : Blo 1385512 26635715 := bstep (se 1 (by rfl) ⟨19976786, by rfl⟩ : syracuseStep 26635715 = 39953573) B39953573
theorem B3946259 : Blo 1385512 3946259 := bstep (se 1 (by rfl) ⟨2959694, by rfl⟩ : syracuseStep 3946259 = 5919389) B5919389
theorem B10523357 : Blo 1385512 10523357 := bstep (se 3 (by rfl) ⟨1973129, by rfl⟩ : syracuseStep 10523357 = 3946259) B3946259
theorem B17757143 : Blo 1385512 17757143 := bstep (se 1 (by rfl) ⟨13317857, by rfl⟩ : syracuseStep 17757143 = 26635715) B26635715
theorem B11838095 : Blo 1385512 11838095 := bstep (se 1 (by rfl) ⟨8878571, by rfl⟩ : syracuseStep 11838095 = 17757143) B17757143
theorem B7015571 : Blo 1385512 7015571 := bstep (se 1 (by rfl) ⟨5261678, by rfl⟩ : syracuseStep 7015571 = 10523357) B10523357
theorem B7892063 : Blo 1385512 7892063 := bstep (se 1 (by rfl) ⟨5919047, by rfl⟩ : syracuseStep 7892063 = 11838095) B11838095
theorem B4677047 : Blo 1385512 4677047 := bstep (se 1 (by rfl) ⟨3507785, by rfl⟩ : syracuseStep 4677047 = 7015571) B7015571
theorem B5261375 : Blo 1385512 5261375 := bstep (se 1 (by rfl) ⟨3946031, by rfl⟩ : syracuseStep 5261375 = 7892063) B7892063
theorem B3118031 : Blo 1385512 3118031 := bstep (se 1 (by rfl) ⟨2338523, by rfl⟩ : syracuseStep 3118031 = 4677047) B4677047
theorem B3507583 : Blo 1385512 3507583 := bstep (se 1 (by rfl) ⟨2630687, by rfl⟩ : syracuseStep 3507583 = 5261375) B5261375
theorem B2078687 : Blo 1385512 2078687 := bstep (se 1 (by rfl) ⟨1559015, by rfl⟩ : syracuseStep 2078687 = 3118031) B3118031
theorem B1385791 : Blo 1385512 1385791 := bstep (se 1 (by rfl) ⟨1039343, by rfl⟩ : syracuseStep 1385791 = 2078687) B2078687
theorem B4676777 : Blo 1385512 4676777 := bstep (se 2 (by rfl) ⟨1753791, by rfl⟩ : syracuseStep 4676777 = 3507583) B3507583
theorem B3117851 : Blo 1385512 3117851 := bstep (se 1 (by rfl) ⟨2338388, by rfl⟩ : syracuseStep 3117851 = 4676777) B4676777
theorem B2078567 : Blo 1385512 2078567 := bstep (se 1 (by rfl) ⟨1558925, by rfl⟩ : syracuseStep 2078567 = 3117851) B3117851
theorem B1385711 : Blo 1385512 1385711 := bstep (se 1 (by rfl) ⟨1039283, by rfl⟩ : syracuseStep 1385711 = 2078567) B2078567

theorem C0 (j : ℕ) (h1 : 346378 ≤ j) (h2 : j ≤ 346877) : Blo 1385512 (4 * j + 3) := by
  interval_cases j
  · exact B1385515
  · exact B1385519
  · exact B1385523
  · exact B1385527
  · exact B1385531
  · exact B1385535
  · exact B1385539
  · exact B1385543
  · exact B1385547
  · exact B1385551
  · exact B1385555
  · exact B1385559
  · exact B1385563
  · exact B1385567
  · exact B1385571
  · exact B1385575
  · exact B1385579
  · exact B1385583
  · exact B1385587
  · exact B1385591
  · exact B1385595
  · exact B1385599
  · exact B1385603
  · exact B1385607
  · exact B1385611
  · exact B1385615
  · exact B1385619
  · exact B1385623
  · exact B1385627
  · exact B1385631
  · exact B1385635
  · exact B1385639
  · exact B1385643
  · exact B1385647
  · exact B1385651
  · exact B1385655
  · exact B1385659
  · exact B1385663
  · exact B1385667
  · exact B1385671
  · exact B1385675
  · exact B1385679
  · exact B1385683
  · exact B1385687
  · exact B1385691
  · exact B1385695
  · exact B1385699
  · exact B1385703
  · exact B1385707
  · exact B1385711
  · exact B1385715
  · exact B1385719
  · exact B1385723
  · exact B1385727
  · exact B1385731
  · exact B1385735
  · exact B1385739
  · exact B1385743
  · exact B1385747
  · exact B1385751
  · exact B1385755
  · exact B1385759
  · exact B1385763
  · exact B1385767
  · exact B1385771
  · exact B1385775
  · exact B1385779
  · exact B1385783
  · exact B1385787
  · exact B1385791
  · exact B1385795
  · exact B1385799
  · exact B1385803
  · exact B1385807
  · exact B1385811
  · exact B1385815
  · exact B1385819
  · exact B1385823
  · exact B1385827
  · exact B1385831
  · exact B1385835
  · exact B1385839
  · exact B1385843
  · exact B1385847
  · exact B1385851
  · exact B1385855
  · exact B1385859
  · exact B1385863
  · exact B1385867
  · exact B1385871
  · exact B1385875
  · exact B1385879
  · exact B1385883
  · exact B1385887
  · exact B1385891
  · exact B1385895
  · exact B1385899
  · exact B1385903
  · exact B1385907
  · exact B1385911
  · exact B1385915
  · exact B1385919
  · exact B1385923
  · exact B1385927
  · exact B1385931
  · exact B1385935
  · exact B1385939
  · exact B1385943
  · exact B1385947
  · exact B1385951
  · exact B1385955
  · exact B1385959
  · exact B1385963
  · exact B1385967
  · exact B1385971
  · exact B1385975
  · exact B1385979
  · exact B1385983
  · exact B1385987
  · exact B1385991
  · exact B1385995
  · exact B1385999
  · exact B1386003
  · exact B1386007
  · exact B1386011
  · exact B1386015
  · exact B1386019
  · exact B1386023
  · exact B1386027
  · exact B1386031
  · exact B1386035
  · exact B1386039
  · exact B1386043
  · exact B1386047
  · exact B1386051
  · exact B1386055
  · exact B1386059
  · exact B1386063
  · exact B1386067
  · exact B1386071
  · exact B1386075
  · exact B1386079
  · exact B1386083
  · exact B1386087
  · exact B1386091
  · exact B1386095
  · exact B1386099
  · exact B1386103
  · exact B1386107
  · exact B1386111
  · exact B1386115
  · exact B1386119
  · exact B1386123
  · exact B1386127
  · exact B1386131
  · exact B1386135
  · exact B1386139
  · exact B1386143
  · exact B1386147
  · exact B1386151
  · exact B1386155
  · exact B1386159
  · exact B1386163
  · exact B1386167
  · exact B1386171
  · exact B1386175
  · exact B1386179
  · exact B1386183
  · exact B1386187
  · exact B1386191
  · exact B1386195
  · exact B1386199
  · exact B1386203
  · exact B1386207
  · exact B1386211
  · exact B1386215
  · exact B1386219
  · exact B1386223
  · exact B1386227
  · exact B1386231
  · exact B1386235
  · exact B1386239
  · exact B1386243
  · exact B1386247
  · exact B1386251
  · exact B1386255
  · exact B1386259
  · exact B1386263
  · exact B1386267
  · exact B1386271
  · exact B1386275
  · exact B1386279
  · exact B1386283
  · exact B1386287
  · exact B1386291
  · exact B1386295
  · exact B1386299
  · exact B1386303
  · exact B1386307
  · exact B1386311
  · exact B1386315
  · exact B1386319
  · exact B1386323
  · exact B1386327
  · exact B1386331
  · exact B1386335
  · exact B1386339
  · exact B1386343
  · exact B1386347
  · exact B1386351
  · exact B1386355
  · exact B1386359
  · exact B1386363
  · exact B1386367
  · exact B1386371
  · exact B1386375
  · exact B1386379
  · exact B1386383
  · exact B1386387
  · exact B1386391
  · exact B1386395
  · exact B1386399
  · exact B1386403
  · exact B1386407
  · exact B1386411
  · exact B1386415
  · exact B1386419
  · exact B1386423
  · exact B1386427
  · exact B1386431
  · exact B1386435
  · exact B1386439
  · exact B1386443
  · exact B1386447
  · exact B1386451
  · exact B1386455
  · exact B1386459
  · exact B1386463
  · exact B1386467
  · exact B1386471
  · exact B1386475
  · exact B1386479
  · exact B1386483
  · exact B1386487
  · exact B1386491
  · exact B1386495
  · exact B1386499
  · exact B1386503
  · exact B1386507
  · exact B1386511
  · exact B1386515
  · exact B1386519
  · exact B1386523
  · exact B1386527
  · exact B1386531
  · exact B1386535
  · exact B1386539
  · exact B1386543
  · exact B1386547
  · exact B1386551
  · exact B1386555
  · exact B1386559
  · exact B1386563
  · exact B1386567
  · exact B1386571
  · exact B1386575
  · exact B1386579
  · exact B1386583
  · exact B1386587
  · exact B1386591
  · exact B1386595
  · exact B1386599
  · exact B1386603
  · exact B1386607
  · exact B1386611
  · exact B1386615
  · exact B1386619
  · exact B1386623
  · exact B1386627
  · exact B1386631
  · exact B1386635
  · exact B1386639
  · exact B1386643
  · exact B1386647
  · exact B1386651
  · exact B1386655
  · exact B1386659
  · exact B1386663
  · exact B1386667
  · exact B1386671
  · exact B1386675
  · exact B1386679
  · exact B1386683
  · exact B1386687
  · exact B1386691
  · exact B1386695
  · exact B1386699
  · exact B1386703
  · exact B1386707
  · exact B1386711
  · exact B1386715
  · exact B1386719
  · exact B1386723
  · exact B1386727
  · exact B1386731
  · exact B1386735
  · exact B1386739
  · exact B1386743
  · exact B1386747
  · exact B1386751
  · exact B1386755
  · exact B1386759
  · exact B1386763
  · exact B1386767
  · exact B1386771
  · exact B1386775
  · exact B1386779
  · exact B1386783
  · exact B1386787
  · exact B1386791
  · exact B1386795
  · exact B1386799
  · exact B1386803
  · exact B1386807
  · exact B1386811
  · exact B1386815
  · exact B1386819
  · exact B1386823
  · exact B1386827
  · exact B1386831
  · exact B1386835
  · exact B1386839
  · exact B1386843
  · exact B1386847
  · exact B1386851
  · exact B1386855
  · exact B1386859
  · exact B1386863
  · exact B1386867
  · exact B1386871
  · exact B1386875
  · exact B1386879
  · exact B1386883
  · exact B1386887
  · exact B1386891
  · exact B1386895
  · exact B1386899
  · exact B1386903
  · exact B1386907
  · exact B1386911
  · exact B1386915
  · exact B1386919
  · exact B1386923
  · exact B1386927
  · exact B1386931
  · exact B1386935
  · exact B1386939
  · exact B1386943
  · exact B1386947
  · exact B1386951
  · exact B1386955
  · exact B1386959
  · exact B1386963
  · exact B1386967
  · exact B1386971
  · exact B1386975
  · exact B1386979
  · exact B1386983
  · exact B1386987
  · exact B1386991
  · exact B1386995
  · exact B1386999
  · exact B1387003
  · exact B1387007
  · exact B1387011
  · exact B1387015
  · exact B1387019
  · exact B1387023
  · exact B1387027
  · exact B1387031
  · exact B1387035
  · exact B1387039
  · exact B1387043
  · exact B1387047
  · exact B1387051
  · exact B1387055
  · exact B1387059
  · exact B1387063
  · exact B1387067
  · exact B1387071
  · exact B1387075
  · exact B1387079
  · exact B1387083
  · exact B1387087
  · exact B1387091
  · exact B1387095
  · exact B1387099
  · exact B1387103
  · exact B1387107
  · exact B1387111
  · exact B1387115
  · exact B1387119
  · exact B1387123
  · exact B1387127
  · exact B1387131
  · exact B1387135
  · exact B1387139
  · exact B1387143
  · exact B1387147
  · exact B1387151
  · exact B1387155
  · exact B1387159
  · exact B1387163
  · exact B1387167
  · exact B1387171
  · exact B1387175
  · exact B1387179
  · exact B1387183
  · exact B1387187
  · exact B1387191
  · exact B1387195
  · exact B1387199
  · exact B1387203
  · exact B1387207
  · exact B1387211
  · exact B1387215
  · exact B1387219
  · exact B1387223
  · exact B1387227
  · exact B1387231
  · exact B1387235
  · exact B1387239
  · exact B1387243
  · exact B1387247
  · exact B1387251
  · exact B1387255
  · exact B1387259
  · exact B1387263
  · exact B1387267
  · exact B1387271
  · exact B1387275
  · exact B1387279
  · exact B1387283
  · exact B1387287
  · exact B1387291
  · exact B1387295
  · exact B1387299
  · exact B1387303
  · exact B1387307
  · exact B1387311
  · exact B1387315
  · exact B1387319
  · exact B1387323
  · exact B1387327
  · exact B1387331
  · exact B1387335
  · exact B1387339
  · exact B1387343
  · exact B1387347
  · exact B1387351
  · exact B1387355
  · exact B1387359
  · exact B1387363
  · exact B1387367
  · exact B1387371
  · exact B1387375
  · exact B1387379
  · exact B1387383
  · exact B1387387
  · exact B1387391
  · exact B1387395
  · exact B1387399
  · exact B1387403
  · exact B1387407
  · exact B1387411
  · exact B1387415
  · exact B1387419
  · exact B1387423
  · exact B1387427
  · exact B1387431
  · exact B1387435
  · exact B1387439
  · exact B1387443
  · exact B1387447
  · exact B1387451
  · exact B1387455
  · exact B1387459
  · exact B1387463
  · exact B1387467
  · exact B1387471
  · exact B1387475
  · exact B1387479
  · exact B1387483
  · exact B1387487
  · exact B1387491
  · exact B1387495
  · exact B1387499
  · exact B1387503
  · exact B1387507
  · exact B1387511

theorem solution (m : ℕ) (hlo : 1385512 ≤ m) (hhi : m ≤ 1387512) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 346378 ≤ j := by omega
    have hj2 : j ≤ 346877 := by omega
    have hb : Blo 1385512 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
