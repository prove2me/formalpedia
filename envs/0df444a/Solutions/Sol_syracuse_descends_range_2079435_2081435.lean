-- Prove2me | solution 1 for syracuse_descends_range_2079435_2081435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:14.330743+00:00
-- url     : https://prove2.me/submissions/e3369941-ef6b-4ca7-93c7-f3be7cdb34b9

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

theorem B2339365 : Blo 2079435 2339365 := bbase (se 4 (by rfl) ⟨219315, by rfl⟩ : syracuseStep 2339365 = 438631) (by norm_num)
theorem B3119153 : Blo 2079435 3119153 := bstep (se 2 (by rfl) ⟨1169682, by rfl⟩ : syracuseStep 3119153 = 2339365) B2339365
theorem B2079435 : Blo 2079435 2079435 := bstep (se 1 (by rfl) ⟨1559576, by rfl⟩ : syracuseStep 2079435 = 3119153) B3119153
theorem B5064461 : Blo 2079435 5064461 := bbase (se 3 (by rfl) ⟨949586, by rfl⟩ : syracuseStep 5064461 = 1899173) (by norm_num)
theorem B3376307 : Blo 2079435 3376307 := bstep (se 1 (by rfl) ⟨2532230, by rfl⟩ : syracuseStep 3376307 = 5064461) B5064461
theorem B2250871 : Blo 2079435 2250871 := bstep (se 1 (by rfl) ⟨1688153, by rfl⟩ : syracuseStep 2250871 = 3376307) B3376307
theorem B12004645 : Blo 2079435 12004645 := bstep (se 4 (by rfl) ⟨1125435, by rfl⟩ : syracuseStep 12004645 = 2250871) B2250871
theorem B16006193 : Blo 2079435 16006193 := bstep (se 2 (by rfl) ⟨6002322, by rfl⟩ : syracuseStep 16006193 = 12004645) B12004645
theorem B10670795 : Blo 2079435 10670795 := bstep (se 1 (by rfl) ⟨8003096, by rfl⟩ : syracuseStep 10670795 = 16006193) B16006193
theorem B7113863 : Blo 2079435 7113863 := bstep (se 1 (by rfl) ⟨5335397, by rfl⟩ : syracuseStep 7113863 = 10670795) B10670795
theorem B18970301 : Blo 2079435 18970301 := bstep (se 3 (by rfl) ⟨3556931, by rfl⟩ : syracuseStep 18970301 = 7113863) B7113863
theorem B12646867 : Blo 2079435 12646867 := bstep (se 1 (by rfl) ⟨9485150, by rfl⟩ : syracuseStep 12646867 = 18970301) B18970301
theorem B16862489 : Blo 2079435 16862489 := bstep (se 2 (by rfl) ⟨6323433, by rfl⟩ : syracuseStep 16862489 = 12646867) B12646867
theorem B11241659 : Blo 2079435 11241659 := bstep (se 1 (by rfl) ⟨8431244, by rfl⟩ : syracuseStep 11241659 = 16862489) B16862489
theorem B7494439 : Blo 2079435 7494439 := bstep (se 1 (by rfl) ⟨5620829, by rfl⟩ : syracuseStep 7494439 = 11241659) B11241659
theorem B9992585 : Blo 2079435 9992585 := bstep (se 2 (by rfl) ⟨3747219, by rfl⟩ : syracuseStep 9992585 = 7494439) B7494439
theorem B6661723 : Blo 2079435 6661723 := bstep (se 1 (by rfl) ⟨4996292, by rfl⟩ : syracuseStep 6661723 = 9992585) B9992585
theorem B8882297 : Blo 2079435 8882297 := bstep (se 2 (by rfl) ⟨3330861, by rfl⟩ : syracuseStep 8882297 = 6661723) B6661723
theorem B5921531 : Blo 2079435 5921531 := bstep (se 1 (by rfl) ⟨4441148, by rfl⟩ : syracuseStep 5921531 = 8882297) B8882297
theorem B3947687 : Blo 2079435 3947687 := bstep (se 1 (by rfl) ⟨2960765, by rfl⟩ : syracuseStep 3947687 = 5921531) B5921531
theorem B2631791 : Blo 2079435 2631791 := bstep (se 1 (by rfl) ⟨1973843, by rfl⟩ : syracuseStep 2631791 = 3947687) B3947687
theorem B7018109 : Blo 2079435 7018109 := bstep (se 3 (by rfl) ⟨1315895, by rfl⟩ : syracuseStep 7018109 = 2631791) B2631791
theorem B4678739 : Blo 2079435 4678739 := bstep (se 1 (by rfl) ⟨3509054, by rfl⟩ : syracuseStep 4678739 = 7018109) B7018109
theorem B3119159 : Blo 2079435 3119159 := bstep (se 1 (by rfl) ⟨2339369, by rfl⟩ : syracuseStep 3119159 = 4678739) B4678739
theorem B2079439 : Blo 2079435 2079439 := bstep (se 1 (by rfl) ⟨1559579, by rfl⟩ : syracuseStep 2079439 = 3119159) B3119159
theorem B3119165 : Blo 2079435 3119165 := bbase (se 3 (by rfl) ⟨584843, by rfl⟩ : syracuseStep 3119165 = 1169687) (by norm_num)
theorem B2079443 : Blo 2079435 2079443 := bstep (se 1 (by rfl) ⟨1559582, by rfl⟩ : syracuseStep 2079443 = 3119165) B3119165
theorem B4678757 : Blo 2079435 4678757 := bbase (se 4 (by rfl) ⟨438633, by rfl⟩ : syracuseStep 4678757 = 877267) (by norm_num)
theorem B3119171 : Blo 2079435 3119171 := bstep (se 1 (by rfl) ⟨2339378, by rfl⟩ : syracuseStep 3119171 = 4678757) B4678757
theorem B2079447 : Blo 2079435 2079447 := bstep (se 1 (by rfl) ⟨1559585, by rfl⟩ : syracuseStep 2079447 = 3119171) B3119171
theorem B5263613 : Blo 2079435 5263613 := bbase (se 3 (by rfl) ⟨986927, by rfl⟩ : syracuseStep 5263613 = 1973855) (by norm_num)
theorem B3509075 : Blo 2079435 3509075 := bstep (se 1 (by rfl) ⟨2631806, by rfl⟩ : syracuseStep 3509075 = 5263613) B5263613
theorem B2339383 : Blo 2079435 2339383 := bstep (se 1 (by rfl) ⟨1754537, by rfl⟩ : syracuseStep 2339383 = 3509075) B3509075
theorem B3119177 : Blo 2079435 3119177 := bstep (se 2 (by rfl) ⟨1169691, by rfl⟩ : syracuseStep 3119177 = 2339383) B2339383
theorem B2079451 : Blo 2079435 2079451 := bstep (se 1 (by rfl) ⟨1559588, by rfl⟩ : syracuseStep 2079451 = 3119177) B3119177
theorem B3947717 : Blo 2079435 3947717 := bbase (se 4 (by rfl) ⟨370098, by rfl⟩ : syracuseStep 3947717 = 740197) (by norm_num)
theorem B10527245 : Blo 2079435 10527245 := bstep (se 3 (by rfl) ⟨1973858, by rfl⟩ : syracuseStep 10527245 = 3947717) B3947717
theorem B7018163 : Blo 2079435 7018163 := bstep (se 1 (by rfl) ⟨5263622, by rfl⟩ : syracuseStep 7018163 = 10527245) B10527245
theorem B4678775 : Blo 2079435 4678775 := bstep (se 1 (by rfl) ⟨3509081, by rfl⟩ : syracuseStep 4678775 = 7018163) B7018163
theorem B3119183 : Blo 2079435 3119183 := bstep (se 1 (by rfl) ⟨2339387, by rfl⟩ : syracuseStep 3119183 = 4678775) B4678775
theorem B2079455 : Blo 2079435 2079455 := bstep (se 1 (by rfl) ⟨1559591, by rfl⟩ : syracuseStep 2079455 = 3119183) B3119183
theorem B3119189 : Blo 2079435 3119189 := bbase (se 8 (by rfl) ⟨18276, by rfl⟩ : syracuseStep 3119189 = 36553) (by norm_num)
theorem B2079459 : Blo 2079435 2079459 := bstep (se 1 (by rfl) ⟨1559594, by rfl⟩ : syracuseStep 2079459 = 3119189) B3119189
theorem B18970517 : Blo 2079435 18970517 := bbase (se 6 (by rfl) ⟨444621, by rfl⟩ : syracuseStep 18970517 = 889243) (by norm_num)
theorem B12647011 : Blo 2079435 12647011 := bstep (se 1 (by rfl) ⟨9485258, by rfl⟩ : syracuseStep 12647011 = 18970517) B18970517
theorem B16862681 : Blo 2079435 16862681 := bstep (se 2 (by rfl) ⟨6323505, by rfl⟩ : syracuseStep 16862681 = 12647011) B12647011
theorem B44967149 : Blo 2079435 44967149 := bstep (se 3 (by rfl) ⟨8431340, by rfl⟩ : syracuseStep 44967149 = 16862681) B16862681
theorem B29978099 : Blo 2079435 29978099 := bstep (se 1 (by rfl) ⟨22483574, by rfl⟩ : syracuseStep 29978099 = 44967149) B44967149
theorem B19985399 : Blo 2079435 19985399 := bstep (se 1 (by rfl) ⟨14989049, by rfl⟩ : syracuseStep 19985399 = 29978099) B29978099
theorem B13323599 : Blo 2079435 13323599 := bstep (se 1 (by rfl) ⟨9992699, by rfl⟩ : syracuseStep 13323599 = 19985399) B19985399
theorem B8882399 : Blo 2079435 8882399 := bstep (se 1 (by rfl) ⟨6661799, by rfl⟩ : syracuseStep 8882399 = 13323599) B13323599
theorem B5921599 : Blo 2079435 5921599 := bstep (se 1 (by rfl) ⟨4441199, by rfl⟩ : syracuseStep 5921599 = 8882399) B8882399
theorem B7895465 : Blo 2079435 7895465 := bstep (se 2 (by rfl) ⟨2960799, by rfl⟩ : syracuseStep 7895465 = 5921599) B5921599
theorem B5263643 : Blo 2079435 5263643 := bstep (se 1 (by rfl) ⟨3947732, by rfl⟩ : syracuseStep 5263643 = 7895465) B7895465
theorem B3509095 : Blo 2079435 3509095 := bstep (se 1 (by rfl) ⟨2631821, by rfl⟩ : syracuseStep 3509095 = 5263643) B5263643
theorem B4678793 : Blo 2079435 4678793 := bstep (se 2 (by rfl) ⟨1754547, by rfl⟩ : syracuseStep 4678793 = 3509095) B3509095
theorem B3119195 : Blo 2079435 3119195 := bstep (se 1 (by rfl) ⟨2339396, by rfl⟩ : syracuseStep 3119195 = 4678793) B4678793
theorem B2079463 : Blo 2079435 2079463 := bstep (se 1 (by rfl) ⟨1559597, by rfl⟩ : syracuseStep 2079463 = 3119195) B3119195
theorem B2339401 : Blo 2079435 2339401 := bbase (se 2 (by rfl) ⟨877275, by rfl⟩ : syracuseStep 2339401 = 1754551) (by norm_num)
theorem B3119201 : Blo 2079435 3119201 := bstep (se 2 (by rfl) ⟨1169700, by rfl⟩ : syracuseStep 3119201 = 2339401) B2339401
theorem B2079467 : Blo 2079435 2079467 := bstep (se 1 (by rfl) ⟨1559600, by rfl⟩ : syracuseStep 2079467 = 3119201) B3119201
theorem B3161765 : Blo 2079435 3161765 := bbase (se 4 (by rfl) ⟨296415, by rfl⟩ : syracuseStep 3161765 = 592831) (by norm_num)
theorem B8431373 : Blo 2079435 8431373 := bstep (se 3 (by rfl) ⟨1580882, by rfl⟩ : syracuseStep 8431373 = 3161765) B3161765
theorem B5620915 : Blo 2079435 5620915 := bstep (se 1 (by rfl) ⟨4215686, by rfl⟩ : syracuseStep 5620915 = 8431373) B8431373
theorem B7494553 : Blo 2079435 7494553 := bstep (se 2 (by rfl) ⟨2810457, by rfl⟩ : syracuseStep 7494553 = 5620915) B5620915
theorem B9992737 : Blo 2079435 9992737 := bstep (se 2 (by rfl) ⟨3747276, by rfl⟩ : syracuseStep 9992737 = 7494553) B7494553
theorem B13323649 : Blo 2079435 13323649 := bstep (se 2 (by rfl) ⟨4996368, by rfl⟩ : syracuseStep 13323649 = 9992737) B9992737
theorem B17764865 : Blo 2079435 17764865 := bstep (se 2 (by rfl) ⟨6661824, by rfl⟩ : syracuseStep 17764865 = 13323649) B13323649
theorem B11843243 : Blo 2079435 11843243 := bstep (se 1 (by rfl) ⟨8882432, by rfl⟩ : syracuseStep 11843243 = 17764865) B17764865
theorem B7895495 : Blo 2079435 7895495 := bstep (se 1 (by rfl) ⟨5921621, by rfl⟩ : syracuseStep 7895495 = 11843243) B11843243
theorem B5263663 : Blo 2079435 5263663 := bstep (se 1 (by rfl) ⟨3947747, by rfl⟩ : syracuseStep 5263663 = 7895495) B7895495
theorem B7018217 : Blo 2079435 7018217 := bstep (se 2 (by rfl) ⟨2631831, by rfl⟩ : syracuseStep 7018217 = 5263663) B5263663
theorem B4678811 : Blo 2079435 4678811 := bstep (se 1 (by rfl) ⟨3509108, by rfl⟩ : syracuseStep 4678811 = 7018217) B7018217
theorem B3119207 : Blo 2079435 3119207 := bstep (se 1 (by rfl) ⟨2339405, by rfl⟩ : syracuseStep 3119207 = 4678811) B4678811
theorem B2079471 : Blo 2079435 2079471 := bstep (se 1 (by rfl) ⟨1559603, by rfl⟩ : syracuseStep 2079471 = 3119207) B3119207
theorem B3119213 : Blo 2079435 3119213 := bbase (se 3 (by rfl) ⟨584852, by rfl⟩ : syracuseStep 3119213 = 1169705) (by norm_num)
theorem B2079475 : Blo 2079435 2079475 := bstep (se 1 (by rfl) ⟨1559606, by rfl⟩ : syracuseStep 2079475 = 3119213) B3119213
theorem B4678829 : Blo 2079435 4678829 := bbase (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) (by norm_num)
theorem B3119219 : Blo 2079435 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B2079479 : Blo 2079435 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B27011029 : Blo 2079435 27011029 := bbase (se 7 (by rfl) ⟨316535, by rfl⟩ : syracuseStep 27011029 = 633071) (by norm_num)
theorem B36014705 : Blo 2079435 36014705 := bstep (se 2 (by rfl) ⟨13505514, by rfl⟩ : syracuseStep 36014705 = 27011029) B27011029
theorem B24009803 : Blo 2079435 24009803 := bstep (se 1 (by rfl) ⟨18007352, by rfl⟩ : syracuseStep 24009803 = 36014705) B36014705
theorem B16006535 : Blo 2079435 16006535 := bstep (se 1 (by rfl) ⟨12004901, by rfl⟩ : syracuseStep 16006535 = 24009803) B24009803
theorem B10671023 : Blo 2079435 10671023 := bstep (se 1 (by rfl) ⟨8003267, by rfl⟩ : syracuseStep 10671023 = 16006535) B16006535
theorem B7114015 : Blo 2079435 7114015 := bstep (se 1 (by rfl) ⟨5335511, by rfl⟩ : syracuseStep 7114015 = 10671023) B10671023
theorem B9485353 : Blo 2079435 9485353 := bstep (se 2 (by rfl) ⟨3557007, by rfl⟩ : syracuseStep 9485353 = 7114015) B7114015
theorem B12647137 : Blo 2079435 12647137 := bstep (se 2 (by rfl) ⟨4742676, by rfl⟩ : syracuseStep 12647137 = 9485353) B9485353
theorem B16862849 : Blo 2079435 16862849 := bstep (se 2 (by rfl) ⟨6323568, by rfl⟩ : syracuseStep 16862849 = 12647137) B12647137
theorem B11241899 : Blo 2079435 11241899 := bstep (se 1 (by rfl) ⟨8431424, by rfl⟩ : syracuseStep 11241899 = 16862849) B16862849
theorem B7494599 : Blo 2079435 7494599 := bstep (se 1 (by rfl) ⟨5620949, by rfl⟩ : syracuseStep 7494599 = 11241899) B11241899
theorem B4996399 : Blo 2079435 4996399 := bstep (se 1 (by rfl) ⟨3747299, by rfl⟩ : syracuseStep 4996399 = 7494599) B7494599
theorem B6661865 : Blo 2079435 6661865 := bstep (se 2 (by rfl) ⟨2498199, by rfl⟩ : syracuseStep 6661865 = 4996399) B4996399
theorem B4441243 : Blo 2079435 4441243 := bstep (se 1 (by rfl) ⟨3330932, by rfl⟩ : syracuseStep 4441243 = 6661865) B6661865
theorem B5921657 : Blo 2079435 5921657 := bstep (se 2 (by rfl) ⟨2220621, by rfl⟩ : syracuseStep 5921657 = 4441243) B4441243
theorem B3947771 : Blo 2079435 3947771 := bstep (se 1 (by rfl) ⟨2960828, by rfl⟩ : syracuseStep 3947771 = 5921657) B5921657
theorem B2631847 : Blo 2079435 2631847 := bstep (se 1 (by rfl) ⟨1973885, by rfl⟩ : syracuseStep 2631847 = 3947771) B3947771
theorem B3509129 : Blo 2079435 3509129 := bstep (se 2 (by rfl) ⟨1315923, by rfl⟩ : syracuseStep 3509129 = 2631847) B2631847
theorem B2339419 : Blo 2079435 2339419 := bstep (se 1 (by rfl) ⟨1754564, by rfl⟩ : syracuseStep 2339419 = 3509129) B3509129
theorem B3119225 : Blo 2079435 3119225 := bstep (se 2 (by rfl) ⟨1169709, by rfl⟩ : syracuseStep 3119225 = 2339419) B2339419
theorem B2079483 : Blo 2079435 2079483 := bstep (se 1 (by rfl) ⟨1559612, by rfl⟩ : syracuseStep 2079483 = 3119225) B3119225
theorem B2532289 : Blo 2079435 2532289 := bbase (se 2 (by rfl) ⟨949608, by rfl⟩ : syracuseStep 2532289 = 1899217) (by norm_num)
theorem B3376385 : Blo 2079435 3376385 := bstep (se 2 (by rfl) ⟨1266144, by rfl⟩ : syracuseStep 3376385 = 2532289) B2532289
theorem B2250923 : Blo 2079435 2250923 := bstep (se 1 (by rfl) ⟨1688192, by rfl⟩ : syracuseStep 2250923 = 3376385) B3376385
theorem B6002461 : Blo 2079435 6002461 := bstep (se 3 (by rfl) ⟨1125461, by rfl⟩ : syracuseStep 6002461 = 2250923) B2250923
theorem B8003281 : Blo 2079435 8003281 := bstep (se 2 (by rfl) ⟨3001230, by rfl⟩ : syracuseStep 8003281 = 6002461) B6002461
theorem B10671041 : Blo 2079435 10671041 := bstep (se 2 (by rfl) ⟨4001640, by rfl⟩ : syracuseStep 10671041 = 8003281) B8003281
theorem B7114027 : Blo 2079435 7114027 := bstep (se 1 (by rfl) ⟨5335520, by rfl⟩ : syracuseStep 7114027 = 10671041) B10671041
theorem B9485369 : Blo 2079435 9485369 := bstep (se 2 (by rfl) ⟨3557013, by rfl⟩ : syracuseStep 9485369 = 7114027) B7114027
theorem B6323579 : Blo 2079435 6323579 := bstep (se 1 (by rfl) ⟨4742684, by rfl⟩ : syracuseStep 6323579 = 9485369) B9485369
theorem B4215719 : Blo 2079435 4215719 := bstep (se 1 (by rfl) ⟨3161789, by rfl⟩ : syracuseStep 4215719 = 6323579) B6323579
theorem B2810479 : Blo 2079435 2810479 := bstep (se 1 (by rfl) ⟨2107859, by rfl⟩ : syracuseStep 2810479 = 4215719) B4215719
theorem B3747305 : Blo 2079435 3747305 := bstep (se 2 (by rfl) ⟨1405239, by rfl⟩ : syracuseStep 3747305 = 2810479) B2810479
theorem B9992813 : Blo 2079435 9992813 := bstep (se 3 (by rfl) ⟨1873652, by rfl⟩ : syracuseStep 9992813 = 3747305) B3747305
theorem B26647501 : Blo 2079435 26647501 := bstep (se 3 (by rfl) ⟨4996406, by rfl⟩ : syracuseStep 26647501 = 9992813) B9992813
theorem B35530001 : Blo 2079435 35530001 := bstep (se 2 (by rfl) ⟨13323750, by rfl⟩ : syracuseStep 35530001 = 26647501) B26647501
theorem B23686667 : Blo 2079435 23686667 := bstep (se 1 (by rfl) ⟨17765000, by rfl⟩ : syracuseStep 23686667 = 35530001) B35530001
theorem B15791111 : Blo 2079435 15791111 := bstep (se 1 (by rfl) ⟨11843333, by rfl⟩ : syracuseStep 15791111 = 23686667) B23686667
theorem B10527407 : Blo 2079435 10527407 := bstep (se 1 (by rfl) ⟨7895555, by rfl⟩ : syracuseStep 10527407 = 15791111) B15791111
theorem B7018271 : Blo 2079435 7018271 := bstep (se 1 (by rfl) ⟨5263703, by rfl⟩ : syracuseStep 7018271 = 10527407) B10527407
theorem B4678847 : Blo 2079435 4678847 := bstep (se 1 (by rfl) ⟨3509135, by rfl⟩ : syracuseStep 4678847 = 7018271) B7018271
theorem B3119231 : Blo 2079435 3119231 := bstep (se 1 (by rfl) ⟨2339423, by rfl⟩ : syracuseStep 3119231 = 4678847) B4678847
theorem B2079487 : Blo 2079435 2079487 := bstep (se 1 (by rfl) ⟨1559615, by rfl⟩ : syracuseStep 2079487 = 3119231) B3119231
theorem B3119237 : Blo 2079435 3119237 := bbase (se 4 (by rfl) ⟨292428, by rfl⟩ : syracuseStep 3119237 = 584857) (by norm_num)
theorem B2079491 : Blo 2079435 2079491 := bstep (se 1 (by rfl) ⟨1559618, by rfl⟩ : syracuseStep 2079491 = 3119237) B3119237
theorem B3509149 : Blo 2079435 3509149 := bbase (se 3 (by rfl) ⟨657965, by rfl⟩ : syracuseStep 3509149 = 1315931) (by norm_num)
theorem B4678865 : Blo 2079435 4678865 := bstep (se 2 (by rfl) ⟨1754574, by rfl⟩ : syracuseStep 4678865 = 3509149) B3509149
theorem B3119243 : Blo 2079435 3119243 := bstep (se 1 (by rfl) ⟨2339432, by rfl⟩ : syracuseStep 3119243 = 4678865) B4678865
theorem B2079495 : Blo 2079435 2079495 := bstep (se 1 (by rfl) ⟨1559621, by rfl⟩ : syracuseStep 2079495 = 3119243) B3119243
theorem B2339437 : Blo 2079435 2339437 := bbase (se 3 (by rfl) ⟨438644, by rfl⟩ : syracuseStep 2339437 = 877289) (by norm_num)
theorem B3119249 : Blo 2079435 3119249 := bstep (se 2 (by rfl) ⟨1169718, by rfl⟩ : syracuseStep 3119249 = 2339437) B2339437
theorem B2079499 : Blo 2079435 2079499 := bstep (se 1 (by rfl) ⟨1559624, by rfl⟩ : syracuseStep 2079499 = 3119249) B3119249
theorem B7018325 : Blo 2079435 7018325 := bbase (se 9 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 7018325 = 41123) (by norm_num)
theorem B4678883 : Blo 2079435 4678883 := bstep (se 1 (by rfl) ⟨3509162, by rfl⟩ : syracuseStep 4678883 = 7018325) B7018325
theorem B3119255 : Blo 2079435 3119255 := bstep (se 1 (by rfl) ⟨2339441, by rfl⟩ : syracuseStep 3119255 = 4678883) B4678883
theorem B2079503 : Blo 2079435 2079503 := bstep (se 1 (by rfl) ⟨1559627, by rfl⟩ : syracuseStep 2079503 = 3119255) B3119255
theorem B3119261 : Blo 2079435 3119261 := bbase (se 3 (by rfl) ⟨584861, by rfl⟩ : syracuseStep 3119261 = 1169723) (by norm_num)
theorem B2079507 : Blo 2079435 2079507 := bstep (se 1 (by rfl) ⟨1559630, by rfl⟩ : syracuseStep 2079507 = 3119261) B3119261
theorem B4678901 : Blo 2079435 4678901 := bbase (se 5 (by rfl) ⟨219323, by rfl⟩ : syracuseStep 4678901 = 438647) (by norm_num)
theorem B3119267 : Blo 2079435 3119267 := bstep (se 1 (by rfl) ⟨2339450, by rfl⟩ : syracuseStep 3119267 = 4678901) B4678901
theorem B2079511 : Blo 2079435 2079511 := bstep (se 1 (by rfl) ⟨1559633, by rfl⟩ : syracuseStep 2079511 = 3119267) B3119267
theorem B3376429 : Blo 2079435 3376429 := bbase (se 3 (by rfl) ⟨633080, by rfl⟩ : syracuseStep 3376429 = 1266161) (by norm_num)
theorem B72030485 : Blo 2079435 72030485 := bstep (se 6 (by rfl) ⟨1688214, by rfl⟩ : syracuseStep 72030485 = 3376429) B3376429
theorem B192081293 : Blo 2079435 192081293 := bstep (se 3 (by rfl) ⟨36015242, by rfl⟩ : syracuseStep 192081293 = 72030485) B72030485
theorem B128054195 : Blo 2079435 128054195 := bstep (se 1 (by rfl) ⟨96040646, by rfl⟩ : syracuseStep 128054195 = 192081293) B192081293
theorem B85369463 : Blo 2079435 85369463 := bstep (se 1 (by rfl) ⟨64027097, by rfl⟩ : syracuseStep 85369463 = 128054195) B128054195
theorem B56912975 : Blo 2079435 56912975 := bstep (se 1 (by rfl) ⟨42684731, by rfl⟩ : syracuseStep 56912975 = 85369463) B85369463
theorem B37941983 : Blo 2079435 37941983 := bstep (se 1 (by rfl) ⟨28456487, by rfl⟩ : syracuseStep 37941983 = 56912975) B56912975
theorem B25294655 : Blo 2079435 25294655 := bstep (se 1 (by rfl) ⟨18970991, by rfl⟩ : syracuseStep 25294655 = 37941983) B37941983
theorem B16863103 : Blo 2079435 16863103 := bstep (se 1 (by rfl) ⟨12647327, by rfl⟩ : syracuseStep 16863103 = 25294655) B25294655
theorem B22484137 : Blo 2079435 22484137 := bstep (se 2 (by rfl) ⟨8431551, by rfl⟩ : syracuseStep 22484137 = 16863103) B16863103
theorem B29978849 : Blo 2079435 29978849 := bstep (se 2 (by rfl) ⟨11242068, by rfl⟩ : syracuseStep 29978849 = 22484137) B22484137
theorem B19985899 : Blo 2079435 19985899 := bstep (se 1 (by rfl) ⟨14989424, by rfl⟩ : syracuseStep 19985899 = 29978849) B29978849
theorem B26647865 : Blo 2079435 26647865 := bstep (se 2 (by rfl) ⟨9992949, by rfl⟩ : syracuseStep 26647865 = 19985899) B19985899
theorem B17765243 : Blo 2079435 17765243 := bstep (se 1 (by rfl) ⟨13323932, by rfl⟩ : syracuseStep 17765243 = 26647865) B26647865
theorem B11843495 : Blo 2079435 11843495 := bstep (se 1 (by rfl) ⟨8882621, by rfl⟩ : syracuseStep 11843495 = 17765243) B17765243
theorem B7895663 : Blo 2079435 7895663 := bstep (se 1 (by rfl) ⟨5921747, by rfl⟩ : syracuseStep 7895663 = 11843495) B11843495
theorem B5263775 : Blo 2079435 5263775 := bstep (se 1 (by rfl) ⟨3947831, by rfl⟩ : syracuseStep 5263775 = 7895663) B7895663
theorem B3509183 : Blo 2079435 3509183 := bstep (se 1 (by rfl) ⟨2631887, by rfl⟩ : syracuseStep 3509183 = 5263775) B5263775
theorem B2339455 : Blo 2079435 2339455 := bstep (se 1 (by rfl) ⟨1754591, by rfl⟩ : syracuseStep 2339455 = 3509183) B3509183
theorem B3119273 : Blo 2079435 3119273 := bstep (se 2 (by rfl) ⟨1169727, by rfl⟩ : syracuseStep 3119273 = 2339455) B2339455
theorem B2079515 : Blo 2079435 2079515 := bstep (se 1 (by rfl) ⟨1559636, by rfl⟩ : syracuseStep 2079515 = 3119273) B3119273
theorem B10671205 : Blo 2079435 10671205 := bbase (se 4 (by rfl) ⟨1000425, by rfl⟩ : syracuseStep 10671205 = 2000851) (by norm_num)
theorem B14228273 : Blo 2079435 14228273 := bstep (se 2 (by rfl) ⟨5335602, by rfl⟩ : syracuseStep 14228273 = 10671205) B10671205
theorem B9485515 : Blo 2079435 9485515 := bstep (se 1 (by rfl) ⟨7114136, by rfl⟩ : syracuseStep 9485515 = 14228273) B14228273
theorem B12647353 : Blo 2079435 12647353 := bstep (se 2 (by rfl) ⟨4742757, by rfl⟩ : syracuseStep 12647353 = 9485515) B9485515
theorem B16863137 : Blo 2079435 16863137 := bstep (se 2 (by rfl) ⟨6323676, by rfl⟩ : syracuseStep 16863137 = 12647353) B12647353
theorem B11242091 : Blo 2079435 11242091 := bstep (se 1 (by rfl) ⟨8431568, by rfl⟩ : syracuseStep 11242091 = 16863137) B16863137
theorem B7494727 : Blo 2079435 7494727 := bstep (se 1 (by rfl) ⟨5621045, by rfl⟩ : syracuseStep 7494727 = 11242091) B11242091
theorem B9992969 : Blo 2079435 9992969 := bstep (se 2 (by rfl) ⟨3747363, by rfl⟩ : syracuseStep 9992969 = 7494727) B7494727
theorem B6661979 : Blo 2079435 6661979 := bstep (se 1 (by rfl) ⟨4996484, by rfl⟩ : syracuseStep 6661979 = 9992969) B9992969
theorem B4441319 : Blo 2079435 4441319 := bstep (se 1 (by rfl) ⟨3330989, by rfl⟩ : syracuseStep 4441319 = 6661979) B6661979
theorem B2960879 : Blo 2079435 2960879 := bstep (se 1 (by rfl) ⟨2220659, by rfl⟩ : syracuseStep 2960879 = 4441319) B4441319
theorem B7895677 : Blo 2079435 7895677 := bstep (se 3 (by rfl) ⟨1480439, by rfl⟩ : syracuseStep 7895677 = 2960879) B2960879
theorem B10527569 : Blo 2079435 10527569 := bstep (se 2 (by rfl) ⟨3947838, by rfl⟩ : syracuseStep 10527569 = 7895677) B7895677
theorem B7018379 : Blo 2079435 7018379 := bstep (se 1 (by rfl) ⟨5263784, by rfl⟩ : syracuseStep 7018379 = 10527569) B10527569
theorem B4678919 : Blo 2079435 4678919 := bstep (se 1 (by rfl) ⟨3509189, by rfl⟩ : syracuseStep 4678919 = 7018379) B7018379
theorem B3119279 : Blo 2079435 3119279 := bstep (se 1 (by rfl) ⟨2339459, by rfl⟩ : syracuseStep 3119279 = 4678919) B4678919
theorem B2079519 : Blo 2079435 2079519 := bstep (se 1 (by rfl) ⟨1559639, by rfl⟩ : syracuseStep 2079519 = 3119279) B3119279
theorem B3119285 : Blo 2079435 3119285 := bbase (se 5 (by rfl) ⟨146216, by rfl⟩ : syracuseStep 3119285 = 292433) (by norm_num)
theorem B2079523 : Blo 2079435 2079523 := bstep (se 1 (by rfl) ⟨1559642, by rfl⟩ : syracuseStep 2079523 = 3119285) B3119285
theorem B5263805 : Blo 2079435 5263805 := bbase (se 3 (by rfl) ⟨986963, by rfl⟩ : syracuseStep 5263805 = 1973927) (by norm_num)
theorem B3509203 : Blo 2079435 3509203 := bstep (se 1 (by rfl) ⟨2631902, by rfl⟩ : syracuseStep 3509203 = 5263805) B5263805
theorem B4678937 : Blo 2079435 4678937 := bstep (se 2 (by rfl) ⟨1754601, by rfl⟩ : syracuseStep 4678937 = 3509203) B3509203
theorem B3119291 : Blo 2079435 3119291 := bstep (se 1 (by rfl) ⟨2339468, by rfl⟩ : syracuseStep 3119291 = 4678937) B4678937
theorem B2079527 : Blo 2079435 2079527 := bstep (se 1 (by rfl) ⟨1559645, by rfl⟩ : syracuseStep 2079527 = 3119291) B3119291
theorem B2339473 : Blo 2079435 2339473 := bbase (se 2 (by rfl) ⟨877302, by rfl⟩ : syracuseStep 2339473 = 1754605) (by norm_num)
theorem B3119297 : Blo 2079435 3119297 := bstep (se 2 (by rfl) ⟨1169736, by rfl⟩ : syracuseStep 3119297 = 2339473) B2339473
theorem B2079531 : Blo 2079435 2079531 := bstep (se 1 (by rfl) ⟨1559648, by rfl⟩ : syracuseStep 2079531 = 3119297) B3119297
theorem B3947869 : Blo 2079435 3947869 := bbase (se 3 (by rfl) ⟨740225, by rfl⟩ : syracuseStep 3947869 = 1480451) (by norm_num)
theorem B5263825 : Blo 2079435 5263825 := bstep (se 2 (by rfl) ⟨1973934, by rfl⟩ : syracuseStep 5263825 = 3947869) B3947869
theorem B7018433 : Blo 2079435 7018433 := bstep (se 2 (by rfl) ⟨2631912, by rfl⟩ : syracuseStep 7018433 = 5263825) B5263825
theorem B4678955 : Blo 2079435 4678955 := bstep (se 1 (by rfl) ⟨3509216, by rfl⟩ : syracuseStep 4678955 = 7018433) B7018433
theorem B3119303 : Blo 2079435 3119303 := bstep (se 1 (by rfl) ⟨2339477, by rfl⟩ : syracuseStep 3119303 = 4678955) B4678955
theorem B2079535 : Blo 2079435 2079535 := bstep (se 1 (by rfl) ⟨1559651, by rfl⟩ : syracuseStep 2079535 = 3119303) B3119303
theorem B3119309 : Blo 2079435 3119309 := bbase (se 3 (by rfl) ⟨584870, by rfl⟩ : syracuseStep 3119309 = 1169741) (by norm_num)
theorem B2079539 : Blo 2079435 2079539 := bstep (se 1 (by rfl) ⟨1559654, by rfl⟩ : syracuseStep 2079539 = 3119309) B3119309
theorem B4678973 : Blo 2079435 4678973 := bbase (se 3 (by rfl) ⟨877307, by rfl⟩ : syracuseStep 4678973 = 1754615) (by norm_num)
theorem B3119315 : Blo 2079435 3119315 := bstep (se 1 (by rfl) ⟨2339486, by rfl⟩ : syracuseStep 3119315 = 4678973) B4678973
theorem B2079543 : Blo 2079435 2079543 := bstep (se 1 (by rfl) ⟨1559657, by rfl⟩ : syracuseStep 2079543 = 3119315) B3119315
theorem B3509237 : Blo 2079435 3509237 := bbase (se 5 (by rfl) ⟨164495, by rfl⟩ : syracuseStep 3509237 = 328991) (by norm_num)
theorem B2339491 : Blo 2079435 2339491 := bstep (se 1 (by rfl) ⟨1754618, by rfl⟩ : syracuseStep 2339491 = 3509237) B3509237
theorem B3119321 : Blo 2079435 3119321 := bstep (se 2 (by rfl) ⟨1169745, by rfl⟩ : syracuseStep 3119321 = 2339491) B2339491
theorem B2079547 : Blo 2079435 2079547 := bstep (se 1 (by rfl) ⟨1559660, by rfl⟩ : syracuseStep 2079547 = 3119321) B3119321
theorem B3747421 : Blo 2079435 3747421 := bbase (se 3 (by rfl) ⟨702641, by rfl⟩ : syracuseStep 3747421 = 1405283) (by norm_num)
theorem B4996561 : Blo 2079435 4996561 := bstep (se 2 (by rfl) ⟨1873710, by rfl⟩ : syracuseStep 4996561 = 3747421) B3747421
theorem B6662081 : Blo 2079435 6662081 := bstep (se 2 (by rfl) ⟨2498280, by rfl⟩ : syracuseStep 6662081 = 4996561) B4996561
theorem B4441387 : Blo 2079435 4441387 := bstep (se 1 (by rfl) ⟨3331040, by rfl⟩ : syracuseStep 4441387 = 6662081) B6662081
theorem B5921849 : Blo 2079435 5921849 := bstep (se 2 (by rfl) ⟨2220693, by rfl⟩ : syracuseStep 5921849 = 4441387) B4441387
theorem B15791597 : Blo 2079435 15791597 := bstep (se 3 (by rfl) ⟨2960924, by rfl⟩ : syracuseStep 15791597 = 5921849) B5921849
theorem B10527731 : Blo 2079435 10527731 := bstep (se 1 (by rfl) ⟨7895798, by rfl⟩ : syracuseStep 10527731 = 15791597) B15791597
theorem B7018487 : Blo 2079435 7018487 := bstep (se 1 (by rfl) ⟨5263865, by rfl⟩ : syracuseStep 7018487 = 10527731) B10527731
theorem B4678991 : Blo 2079435 4678991 := bstep (se 1 (by rfl) ⟨3509243, by rfl⟩ : syracuseStep 4678991 = 7018487) B7018487
theorem B3119327 : Blo 2079435 3119327 := bstep (se 1 (by rfl) ⟨2339495, by rfl⟩ : syracuseStep 3119327 = 4678991) B4678991
theorem B2079551 : Blo 2079435 2079551 := bstep (se 1 (by rfl) ⟨1559663, by rfl⟩ : syracuseStep 2079551 = 3119327) B3119327
theorem B3119333 : Blo 2079435 3119333 := bbase (se 4 (by rfl) ⟨292437, by rfl⟩ : syracuseStep 3119333 = 584875) (by norm_num)
theorem B2079555 : Blo 2079435 2079555 := bstep (se 1 (by rfl) ⟨1559666, by rfl⟩ : syracuseStep 2079555 = 3119333) B3119333
theorem B4441405 : Blo 2079435 4441405 := bbase (se 3 (by rfl) ⟨832763, by rfl⟩ : syracuseStep 4441405 = 1665527) (by norm_num)
theorem B5921873 : Blo 2079435 5921873 := bstep (se 2 (by rfl) ⟨2220702, by rfl⟩ : syracuseStep 5921873 = 4441405) B4441405
theorem B3947915 : Blo 2079435 3947915 := bstep (se 1 (by rfl) ⟨2960936, by rfl⟩ : syracuseStep 3947915 = 5921873) B5921873
theorem B2631943 : Blo 2079435 2631943 := bstep (se 1 (by rfl) ⟨1973957, by rfl⟩ : syracuseStep 2631943 = 3947915) B3947915
theorem B3509257 : Blo 2079435 3509257 := bstep (se 2 (by rfl) ⟨1315971, by rfl⟩ : syracuseStep 3509257 = 2631943) B2631943
theorem B4679009 : Blo 2079435 4679009 := bstep (se 2 (by rfl) ⟨1754628, by rfl⟩ : syracuseStep 4679009 = 3509257) B3509257
theorem B3119339 : Blo 2079435 3119339 := bstep (se 1 (by rfl) ⟨2339504, by rfl⟩ : syracuseStep 3119339 = 4679009) B4679009
theorem B2079559 : Blo 2079435 2079559 := bstep (se 1 (by rfl) ⟨1559669, by rfl⟩ : syracuseStep 2079559 = 3119339) B3119339
theorem B2339509 : Blo 2079435 2339509 := bbase (se 5 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 2339509 = 219329) (by norm_num)
theorem B3119345 : Blo 2079435 3119345 := bstep (se 2 (by rfl) ⟨1169754, by rfl⟩ : syracuseStep 3119345 = 2339509) B2339509
theorem B2079563 : Blo 2079435 2079563 := bstep (se 1 (by rfl) ⟨1559672, by rfl⟩ : syracuseStep 2079563 = 3119345) B3119345
theorem B2631953 : Blo 2079435 2631953 := bbase (se 2 (by rfl) ⟨986982, by rfl⟩ : syracuseStep 2631953 = 1973965) (by norm_num)
theorem B7018541 : Blo 2079435 7018541 := bstep (se 3 (by rfl) ⟨1315976, by rfl⟩ : syracuseStep 7018541 = 2631953) B2631953
theorem B4679027 : Blo 2079435 4679027 := bstep (se 1 (by rfl) ⟨3509270, by rfl⟩ : syracuseStep 4679027 = 7018541) B7018541
theorem B3119351 : Blo 2079435 3119351 := bstep (se 1 (by rfl) ⟨2339513, by rfl⟩ : syracuseStep 3119351 = 4679027) B4679027
theorem B2079567 : Blo 2079435 2079567 := bstep (se 1 (by rfl) ⟨1559675, by rfl⟩ : syracuseStep 2079567 = 3119351) B3119351
theorem B3119357 : Blo 2079435 3119357 := bbase (se 3 (by rfl) ⟨584879, by rfl⟩ : syracuseStep 3119357 = 1169759) (by norm_num)
theorem B2079571 : Blo 2079435 2079571 := bstep (se 1 (by rfl) ⟨1559678, by rfl⟩ : syracuseStep 2079571 = 3119357) B3119357
theorem B4679045 : Blo 2079435 4679045 := bbase (se 4 (by rfl) ⟨438660, by rfl⟩ : syracuseStep 4679045 = 877321) (by norm_num)
theorem B3119363 : Blo 2079435 3119363 := bstep (se 1 (by rfl) ⟨2339522, by rfl⟩ : syracuseStep 3119363 = 4679045) B4679045
theorem B2079575 : Blo 2079435 2079575 := bstep (se 1 (by rfl) ⟨1559681, by rfl⟩ : syracuseStep 2079575 = 3119363) B3119363
theorem B2960965 : Blo 2079435 2960965 := bbase (se 4 (by rfl) ⟨277590, by rfl⟩ : syracuseStep 2960965 = 555181) (by norm_num)
theorem B3947953 : Blo 2079435 3947953 := bstep (se 2 (by rfl) ⟨1480482, by rfl⟩ : syracuseStep 3947953 = 2960965) B2960965
theorem B5263937 : Blo 2079435 5263937 := bstep (se 2 (by rfl) ⟨1973976, by rfl⟩ : syracuseStep 5263937 = 3947953) B3947953
theorem B3509291 : Blo 2079435 3509291 := bstep (se 1 (by rfl) ⟨2631968, by rfl⟩ : syracuseStep 3509291 = 5263937) B5263937
theorem B2339527 : Blo 2079435 2339527 := bstep (se 1 (by rfl) ⟨1754645, by rfl⟩ : syracuseStep 2339527 = 3509291) B3509291
theorem B3119369 : Blo 2079435 3119369 := bstep (se 2 (by rfl) ⟨1169763, by rfl⟩ : syracuseStep 3119369 = 2339527) B2339527
theorem B2079579 : Blo 2079435 2079579 := bstep (se 1 (by rfl) ⟨1559684, by rfl⟩ : syracuseStep 2079579 = 3119369) B3119369
theorem B10527893 : Blo 2079435 10527893 := bbase (se 6 (by rfl) ⟨246747, by rfl⟩ : syracuseStep 10527893 = 493495) (by norm_num)
theorem B7018595 : Blo 2079435 7018595 := bstep (se 1 (by rfl) ⟨5263946, by rfl⟩ : syracuseStep 7018595 = 10527893) B10527893
theorem B4679063 : Blo 2079435 4679063 := bstep (se 1 (by rfl) ⟨3509297, by rfl⟩ : syracuseStep 4679063 = 7018595) B7018595
theorem B3119375 : Blo 2079435 3119375 := bstep (se 1 (by rfl) ⟨2339531, by rfl⟩ : syracuseStep 3119375 = 4679063) B4679063
theorem B2079583 : Blo 2079435 2079583 := bstep (se 1 (by rfl) ⟨1559687, by rfl⟩ : syracuseStep 2079583 = 3119375) B3119375
theorem B3119381 : Blo 2079435 3119381 := bbase (se 6 (by rfl) ⟨73110, by rfl⟩ : syracuseStep 3119381 = 146221) (by norm_num)
theorem B2079587 : Blo 2079435 2079587 := bstep (se 1 (by rfl) ⟨1559690, by rfl⟩ : syracuseStep 2079587 = 3119381) B3119381
theorem B3747493 : Blo 2079435 3747493 := bbase (se 4 (by rfl) ⟨351327, by rfl⟩ : syracuseStep 3747493 = 702655) (by norm_num)
theorem B4996657 : Blo 2079435 4996657 := bstep (se 2 (by rfl) ⟨1873746, by rfl⟩ : syracuseStep 4996657 = 3747493) B3747493
theorem B26648837 : Blo 2079435 26648837 := bstep (se 4 (by rfl) ⟨2498328, by rfl⟩ : syracuseStep 26648837 = 4996657) B4996657
theorem B17765891 : Blo 2079435 17765891 := bstep (se 1 (by rfl) ⟨13324418, by rfl⟩ : syracuseStep 17765891 = 26648837) B26648837
theorem B11843927 : Blo 2079435 11843927 := bstep (se 1 (by rfl) ⟨8882945, by rfl⟩ : syracuseStep 11843927 = 17765891) B17765891
theorem B7895951 : Blo 2079435 7895951 := bstep (se 1 (by rfl) ⟨5921963, by rfl⟩ : syracuseStep 7895951 = 11843927) B11843927
theorem B5263967 : Blo 2079435 5263967 := bstep (se 1 (by rfl) ⟨3947975, by rfl⟩ : syracuseStep 5263967 = 7895951) B7895951
theorem B3509311 : Blo 2079435 3509311 := bstep (se 1 (by rfl) ⟨2631983, by rfl⟩ : syracuseStep 3509311 = 5263967) B5263967
theorem B4679081 : Blo 2079435 4679081 := bstep (se 2 (by rfl) ⟨1754655, by rfl⟩ : syracuseStep 4679081 = 3509311) B3509311
theorem B3119387 : Blo 2079435 3119387 := bstep (se 1 (by rfl) ⟨2339540, by rfl⟩ : syracuseStep 3119387 = 4679081) B4679081
theorem B2079591 : Blo 2079435 2079591 := bstep (se 1 (by rfl) ⟨1559693, by rfl⟩ : syracuseStep 2079591 = 3119387) B3119387
theorem B2339545 : Blo 2079435 2339545 := bbase (se 2 (by rfl) ⟨877329, by rfl⟩ : syracuseStep 2339545 = 1754659) (by norm_num)
theorem B3119393 : Blo 2079435 3119393 := bstep (se 2 (by rfl) ⟨1169772, by rfl⟩ : syracuseStep 3119393 = 2339545) B2339545
theorem B2079595 : Blo 2079435 2079595 := bstep (se 1 (by rfl) ⟨1559696, by rfl⟩ : syracuseStep 2079595 = 3119393) B3119393
theorem B2220745 : Blo 2079435 2220745 := bbase (se 2 (by rfl) ⟨832779, by rfl⟩ : syracuseStep 2220745 = 1665559) (by norm_num)
theorem B2960993 : Blo 2079435 2960993 := bstep (se 2 (by rfl) ⟨1110372, by rfl⟩ : syracuseStep 2960993 = 2220745) B2220745
theorem B7895981 : Blo 2079435 7895981 := bstep (se 3 (by rfl) ⟨1480496, by rfl⟩ : syracuseStep 7895981 = 2960993) B2960993
theorem B5263987 : Blo 2079435 5263987 := bstep (se 1 (by rfl) ⟨3947990, by rfl⟩ : syracuseStep 5263987 = 7895981) B7895981
theorem B7018649 : Blo 2079435 7018649 := bstep (se 2 (by rfl) ⟨2631993, by rfl⟩ : syracuseStep 7018649 = 5263987) B5263987
theorem B4679099 : Blo 2079435 4679099 := bstep (se 1 (by rfl) ⟨3509324, by rfl⟩ : syracuseStep 4679099 = 7018649) B7018649
theorem B3119399 : Blo 2079435 3119399 := bstep (se 1 (by rfl) ⟨2339549, by rfl⟩ : syracuseStep 3119399 = 4679099) B4679099
theorem B2079599 : Blo 2079435 2079599 := bstep (se 1 (by rfl) ⟨1559699, by rfl⟩ : syracuseStep 2079599 = 3119399) B3119399
theorem B3119405 : Blo 2079435 3119405 := bbase (se 3 (by rfl) ⟨584888, by rfl⟩ : syracuseStep 3119405 = 1169777) (by norm_num)
theorem B2079603 : Blo 2079435 2079603 := bstep (se 1 (by rfl) ⟨1559702, by rfl⟩ : syracuseStep 2079603 = 3119405) B3119405
theorem B4679117 : Blo 2079435 4679117 := bbase (se 3 (by rfl) ⟨877334, by rfl⟩ : syracuseStep 4679117 = 1754669) (by norm_num)
theorem B3119411 : Blo 2079435 3119411 := bstep (se 1 (by rfl) ⟨2339558, by rfl⟩ : syracuseStep 3119411 = 4679117) B4679117
theorem B2079607 : Blo 2079435 2079607 := bstep (se 1 (by rfl) ⟨1559705, by rfl⟩ : syracuseStep 2079607 = 3119411) B3119411
theorem B2632009 : Blo 2079435 2632009 := bbase (se 2 (by rfl) ⟨987003, by rfl⟩ : syracuseStep 2632009 = 1974007) (by norm_num)
theorem B3509345 : Blo 2079435 3509345 := bstep (se 2 (by rfl) ⟨1316004, by rfl⟩ : syracuseStep 3509345 = 2632009) B2632009
theorem B2339563 : Blo 2079435 2339563 := bstep (se 1 (by rfl) ⟨1754672, by rfl⟩ : syracuseStep 2339563 = 3509345) B3509345
theorem B3119417 : Blo 2079435 3119417 := bstep (se 2 (by rfl) ⟨1169781, by rfl⟩ : syracuseStep 3119417 = 2339563) B2339563
theorem B2079611 : Blo 2079435 2079611 := bstep (se 1 (by rfl) ⟨1559708, by rfl⟩ : syracuseStep 2079611 = 3119417) B3119417
theorem B2136749 : Blo 2079435 2136749 := bbase (se 3 (by rfl) ⟨400640, by rfl⟩ : syracuseStep 2136749 = 801281) (by norm_num)
theorem B22791989 : Blo 2079435 22791989 := bstep (se 5 (by rfl) ⟨1068374, by rfl⟩ : syracuseStep 22791989 = 2136749) B2136749
theorem B60778637 : Blo 2079435 60778637 := bstep (se 3 (by rfl) ⟨11395994, by rfl⟩ : syracuseStep 60778637 = 22791989) B22791989
theorem B40519091 : Blo 2079435 40519091 := bstep (se 1 (by rfl) ⟨30389318, by rfl⟩ : syracuseStep 40519091 = 60778637) B60778637
theorem B27012727 : Blo 2079435 27012727 := bstep (se 1 (by rfl) ⟨20259545, by rfl⟩ : syracuseStep 27012727 = 40519091) B40519091
theorem B36016969 : Blo 2079435 36016969 := bstep (se 2 (by rfl) ⟨13506363, by rfl⟩ : syracuseStep 36016969 = 27012727) B27012727
theorem B48022625 : Blo 2079435 48022625 := bstep (se 2 (by rfl) ⟨18008484, by rfl⟩ : syracuseStep 48022625 = 36016969) B36016969
theorem B32015083 : Blo 2079435 32015083 := bstep (se 1 (by rfl) ⟨24011312, by rfl⟩ : syracuseStep 32015083 = 48022625) B48022625
theorem B42686777 : Blo 2079435 42686777 := bstep (se 2 (by rfl) ⟨16007541, by rfl⟩ : syracuseStep 42686777 = 32015083) B32015083
theorem B113831405 : Blo 2079435 113831405 := bstep (se 3 (by rfl) ⟨21343388, by rfl⟩ : syracuseStep 113831405 = 42686777) B42686777
theorem B75887603 : Blo 2079435 75887603 := bstep (se 1 (by rfl) ⟨56915702, by rfl⟩ : syracuseStep 75887603 = 113831405) B113831405
theorem B50591735 : Blo 2079435 50591735 := bstep (se 1 (by rfl) ⟨37943801, by rfl⟩ : syracuseStep 50591735 = 75887603) B75887603
theorem B33727823 : Blo 2079435 33727823 := bstep (se 1 (by rfl) ⟨25295867, by rfl⟩ : syracuseStep 33727823 = 50591735) B50591735
theorem B22485215 : Blo 2079435 22485215 := bstep (se 1 (by rfl) ⟨16863911, by rfl⟩ : syracuseStep 22485215 = 33727823) B33727823
theorem B14990143 : Blo 2079435 14990143 := bstep (se 1 (by rfl) ⟨11242607, by rfl⟩ : syracuseStep 14990143 = 22485215) B22485215
theorem B19986857 : Blo 2079435 19986857 := bstep (se 2 (by rfl) ⟨7495071, by rfl⟩ : syracuseStep 19986857 = 14990143) B14990143
theorem B13324571 : Blo 2079435 13324571 := bstep (se 1 (by rfl) ⟨9993428, by rfl⟩ : syracuseStep 13324571 = 19986857) B19986857
theorem B8883047 : Blo 2079435 8883047 := bstep (se 1 (by rfl) ⟨6662285, by rfl⟩ : syracuseStep 8883047 = 13324571) B13324571
theorem B23688125 : Blo 2079435 23688125 := bstep (se 3 (by rfl) ⟨4441523, by rfl⟩ : syracuseStep 23688125 = 8883047) B8883047
theorem B15792083 : Blo 2079435 15792083 := bstep (se 1 (by rfl) ⟨11844062, by rfl⟩ : syracuseStep 15792083 = 23688125) B23688125
theorem B10528055 : Blo 2079435 10528055 := bstep (se 1 (by rfl) ⟨7896041, by rfl⟩ : syracuseStep 10528055 = 15792083) B15792083
theorem B7018703 : Blo 2079435 7018703 := bstep (se 1 (by rfl) ⟨5264027, by rfl⟩ : syracuseStep 7018703 = 10528055) B10528055
theorem B4679135 : Blo 2079435 4679135 := bstep (se 1 (by rfl) ⟨3509351, by rfl⟩ : syracuseStep 4679135 = 7018703) B7018703
theorem B3119423 : Blo 2079435 3119423 := bstep (se 1 (by rfl) ⟨2339567, by rfl⟩ : syracuseStep 3119423 = 4679135) B4679135
theorem B2079615 : Blo 2079435 2079615 := bstep (se 1 (by rfl) ⟨1559711, by rfl⟩ : syracuseStep 2079615 = 3119423) B3119423
theorem B3119429 : Blo 2079435 3119429 := bbase (se 4 (by rfl) ⟨292446, by rfl⟩ : syracuseStep 3119429 = 584893) (by norm_num)
theorem B2079619 : Blo 2079435 2079619 := bstep (se 1 (by rfl) ⟨1559714, by rfl⟩ : syracuseStep 2079619 = 3119429) B3119429
theorem B3509365 : Blo 2079435 3509365 := bbase (se 5 (by rfl) ⟨164501, by rfl⟩ : syracuseStep 3509365 = 329003) (by norm_num)
theorem B4679153 : Blo 2079435 4679153 := bstep (se 2 (by rfl) ⟨1754682, by rfl⟩ : syracuseStep 4679153 = 3509365) B3509365
theorem B3119435 : Blo 2079435 3119435 := bstep (se 1 (by rfl) ⟨2339576, by rfl⟩ : syracuseStep 3119435 = 4679153) B4679153
theorem B2079623 : Blo 2079435 2079623 := bstep (se 1 (by rfl) ⟨1559717, by rfl⟩ : syracuseStep 2079623 = 3119435) B3119435
theorem B2339581 : Blo 2079435 2339581 := bbase (se 3 (by rfl) ⟨438671, by rfl⟩ : syracuseStep 2339581 = 877343) (by norm_num)
theorem B3119441 : Blo 2079435 3119441 := bstep (se 2 (by rfl) ⟨1169790, by rfl⟩ : syracuseStep 3119441 = 2339581) B2339581
theorem B2079627 : Blo 2079435 2079627 := bstep (se 1 (by rfl) ⟨1559720, by rfl⟩ : syracuseStep 2079627 = 3119441) B3119441
theorem B7018757 : Blo 2079435 7018757 := bbase (se 4 (by rfl) ⟨658008, by rfl⟩ : syracuseStep 7018757 = 1316017) (by norm_num)
theorem B4679171 : Blo 2079435 4679171 := bstep (se 1 (by rfl) ⟨3509378, by rfl⟩ : syracuseStep 4679171 = 7018757) B7018757
theorem B3119447 : Blo 2079435 3119447 := bstep (se 1 (by rfl) ⟨2339585, by rfl⟩ : syracuseStep 3119447 = 4679171) B4679171
theorem B2079631 : Blo 2079435 2079631 := bstep (se 1 (by rfl) ⟨1559723, by rfl⟩ : syracuseStep 2079631 = 3119447) B3119447
theorem B3119453 : Blo 2079435 3119453 := bbase (se 3 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 3119453 = 1169795) (by norm_num)
theorem B2079635 : Blo 2079435 2079635 := bstep (se 1 (by rfl) ⟨1559726, by rfl⟩ : syracuseStep 2079635 = 3119453) B3119453
theorem B4679189 : Blo 2079435 4679189 := bbase (se 6 (by rfl) ⟨109668, by rfl⟩ : syracuseStep 4679189 = 219337) (by norm_num)
theorem B3119459 : Blo 2079435 3119459 := bstep (se 1 (by rfl) ⟨2339594, by rfl⟩ : syracuseStep 3119459 = 4679189) B4679189
theorem B2079639 : Blo 2079435 2079639 := bstep (se 1 (by rfl) ⟨1559729, by rfl⟩ : syracuseStep 2079639 = 3119459) B3119459
theorem B7896149 : Blo 2079435 7896149 := bbase (se 8 (by rfl) ⟨46266, by rfl⟩ : syracuseStep 7896149 = 92533) (by norm_num)
theorem B5264099 : Blo 2079435 5264099 := bstep (se 1 (by rfl) ⟨3948074, by rfl⟩ : syracuseStep 5264099 = 7896149) B7896149
theorem B3509399 : Blo 2079435 3509399 := bstep (se 1 (by rfl) ⟨2632049, by rfl⟩ : syracuseStep 3509399 = 5264099) B5264099
theorem B2339599 : Blo 2079435 2339599 := bstep (se 1 (by rfl) ⟨1754699, by rfl⟩ : syracuseStep 2339599 = 3509399) B3509399
theorem B3119465 : Blo 2079435 3119465 := bstep (se 2 (by rfl) ⟨1169799, by rfl⟩ : syracuseStep 3119465 = 2339599) B2339599
theorem B2079643 : Blo 2079435 2079643 := bstep (se 1 (by rfl) ⟨1559732, by rfl⟩ : syracuseStep 2079643 = 3119465) B3119465
theorem B11844245 : Blo 2079435 11844245 := bbase (se 6 (by rfl) ⟨277599, by rfl⟩ : syracuseStep 11844245 = 555199) (by norm_num)
theorem B7896163 : Blo 2079435 7896163 := bstep (se 1 (by rfl) ⟨5922122, by rfl⟩ : syracuseStep 7896163 = 11844245) B11844245
theorem B10528217 : Blo 2079435 10528217 := bstep (se 2 (by rfl) ⟨3948081, by rfl⟩ : syracuseStep 10528217 = 7896163) B7896163
theorem B7018811 : Blo 2079435 7018811 := bstep (se 1 (by rfl) ⟨5264108, by rfl⟩ : syracuseStep 7018811 = 10528217) B10528217
theorem B4679207 : Blo 2079435 4679207 := bstep (se 1 (by rfl) ⟨3509405, by rfl⟩ : syracuseStep 4679207 = 7018811) B7018811
theorem B3119471 : Blo 2079435 3119471 := bstep (se 1 (by rfl) ⟨2339603, by rfl⟩ : syracuseStep 3119471 = 4679207) B4679207
theorem B2079647 : Blo 2079435 2079647 := bstep (se 1 (by rfl) ⟨1559735, by rfl⟩ : syracuseStep 2079647 = 3119471) B3119471
theorem B3119477 : Blo 2079435 3119477 := bbase (se 5 (by rfl) ⟨146225, by rfl⟩ : syracuseStep 3119477 = 292451) (by norm_num)
theorem B2079651 : Blo 2079435 2079651 := bstep (se 1 (by rfl) ⟨1559738, by rfl⟩ : syracuseStep 2079651 = 3119477) B3119477
theorem B2220805 : Blo 2079435 2220805 := bbase (se 4 (by rfl) ⟨208200, by rfl⟩ : syracuseStep 2220805 = 416401) (by norm_num)
theorem B2961073 : Blo 2079435 2961073 := bstep (se 2 (by rfl) ⟨1110402, by rfl⟩ : syracuseStep 2961073 = 2220805) B2220805
theorem B3948097 : Blo 2079435 3948097 := bstep (se 2 (by rfl) ⟨1480536, by rfl⟩ : syracuseStep 3948097 = 2961073) B2961073
theorem B5264129 : Blo 2079435 5264129 := bstep (se 2 (by rfl) ⟨1974048, by rfl⟩ : syracuseStep 5264129 = 3948097) B3948097
theorem B3509419 : Blo 2079435 3509419 := bstep (se 1 (by rfl) ⟨2632064, by rfl⟩ : syracuseStep 3509419 = 5264129) B5264129
theorem B4679225 : Blo 2079435 4679225 := bstep (se 2 (by rfl) ⟨1754709, by rfl⟩ : syracuseStep 4679225 = 3509419) B3509419
theorem B3119483 : Blo 2079435 3119483 := bstep (se 1 (by rfl) ⟨2339612, by rfl⟩ : syracuseStep 3119483 = 4679225) B4679225
theorem B2079655 : Blo 2079435 2079655 := bstep (se 1 (by rfl) ⟨1559741, by rfl⟩ : syracuseStep 2079655 = 3119483) B3119483
theorem B2339617 : Blo 2079435 2339617 := bbase (se 2 (by rfl) ⟨877356, by rfl⟩ : syracuseStep 2339617 = 1754713) (by norm_num)
theorem B3119489 : Blo 2079435 3119489 := bstep (se 2 (by rfl) ⟨1169808, by rfl⟩ : syracuseStep 3119489 = 2339617) B2339617
theorem B2079659 : Blo 2079435 2079659 := bstep (se 1 (by rfl) ⟨1559744, by rfl⟩ : syracuseStep 2079659 = 3119489) B3119489
theorem B5264149 : Blo 2079435 5264149 := bbase (se 6 (by rfl) ⟨123378, by rfl⟩ : syracuseStep 5264149 = 246757) (by norm_num)
theorem B7018865 : Blo 2079435 7018865 := bstep (se 2 (by rfl) ⟨2632074, by rfl⟩ : syracuseStep 7018865 = 5264149) B5264149
theorem B4679243 : Blo 2079435 4679243 := bstep (se 1 (by rfl) ⟨3509432, by rfl⟩ : syracuseStep 4679243 = 7018865) B7018865
theorem B3119495 : Blo 2079435 3119495 := bstep (se 1 (by rfl) ⟨2339621, by rfl⟩ : syracuseStep 3119495 = 4679243) B4679243
theorem B2079663 : Blo 2079435 2079663 := bstep (se 1 (by rfl) ⟨1559747, by rfl⟩ : syracuseStep 2079663 = 3119495) B3119495
theorem B3119501 : Blo 2079435 3119501 := bbase (se 3 (by rfl) ⟨584906, by rfl⟩ : syracuseStep 3119501 = 1169813) (by norm_num)
theorem B2079667 : Blo 2079435 2079667 := bstep (se 1 (by rfl) ⟨1559750, by rfl⟩ : syracuseStep 2079667 = 3119501) B3119501
theorem B4679261 : Blo 2079435 4679261 := bbase (se 3 (by rfl) ⟨877361, by rfl⟩ : syracuseStep 4679261 = 1754723) (by norm_num)
theorem B3119507 : Blo 2079435 3119507 := bstep (se 1 (by rfl) ⟨2339630, by rfl⟩ : syracuseStep 3119507 = 4679261) B4679261
theorem B2079671 : Blo 2079435 2079671 := bstep (se 1 (by rfl) ⟨1559753, by rfl⟩ : syracuseStep 2079671 = 3119507) B3119507
theorem B3509453 : Blo 2079435 3509453 := bbase (se 3 (by rfl) ⟨658022, by rfl⟩ : syracuseStep 3509453 = 1316045) (by norm_num)
theorem B2339635 : Blo 2079435 2339635 := bstep (se 1 (by rfl) ⟨1754726, by rfl⟩ : syracuseStep 2339635 = 3509453) B3509453
theorem B3119513 : Blo 2079435 3119513 := bstep (se 2 (by rfl) ⟨1169817, by rfl⟩ : syracuseStep 3119513 = 2339635) B2339635
theorem B2079675 : Blo 2079435 2079675 := bstep (se 1 (by rfl) ⟨1559756, by rfl⟩ : syracuseStep 2079675 = 3119513) B3119513
theorem B13324981 : Blo 2079435 13324981 := bbase (se 5 (by rfl) ⟨624608, by rfl⟩ : syracuseStep 13324981 = 1249217) (by norm_num)
theorem B17766641 : Blo 2079435 17766641 := bstep (se 2 (by rfl) ⟨6662490, by rfl⟩ : syracuseStep 17766641 = 13324981) B13324981
theorem B11844427 : Blo 2079435 11844427 := bstep (se 1 (by rfl) ⟨8883320, by rfl⟩ : syracuseStep 11844427 = 17766641) B17766641
theorem B15792569 : Blo 2079435 15792569 := bstep (se 2 (by rfl) ⟨5922213, by rfl⟩ : syracuseStep 15792569 = 11844427) B11844427
theorem B10528379 : Blo 2079435 10528379 := bstep (se 1 (by rfl) ⟨7896284, by rfl⟩ : syracuseStep 10528379 = 15792569) B15792569
theorem B7018919 : Blo 2079435 7018919 := bstep (se 1 (by rfl) ⟨5264189, by rfl⟩ : syracuseStep 7018919 = 10528379) B10528379
theorem B4679279 : Blo 2079435 4679279 := bstep (se 1 (by rfl) ⟨3509459, by rfl⟩ : syracuseStep 4679279 = 7018919) B7018919
theorem B3119519 : Blo 2079435 3119519 := bstep (se 1 (by rfl) ⟨2339639, by rfl⟩ : syracuseStep 3119519 = 4679279) B4679279
theorem B2079679 : Blo 2079435 2079679 := bstep (se 1 (by rfl) ⟨1559759, by rfl⟩ : syracuseStep 2079679 = 3119519) B3119519
theorem B3119525 : Blo 2079435 3119525 := bbase (se 4 (by rfl) ⟨292455, by rfl⟩ : syracuseStep 3119525 = 584911) (by norm_num)
theorem B2079683 : Blo 2079435 2079683 := bstep (se 1 (by rfl) ⟨1559762, by rfl⟩ : syracuseStep 2079683 = 3119525) B3119525
theorem B2632105 : Blo 2079435 2632105 := bbase (se 2 (by rfl) ⟨987039, by rfl⟩ : syracuseStep 2632105 = 1974079) (by norm_num)
theorem B3509473 : Blo 2079435 3509473 := bstep (se 2 (by rfl) ⟨1316052, by rfl⟩ : syracuseStep 3509473 = 2632105) B2632105
theorem B4679297 : Blo 2079435 4679297 := bstep (se 2 (by rfl) ⟨1754736, by rfl⟩ : syracuseStep 4679297 = 3509473) B3509473
theorem B3119531 : Blo 2079435 3119531 := bstep (se 1 (by rfl) ⟨2339648, by rfl⟩ : syracuseStep 3119531 = 4679297) B4679297
theorem B2079687 : Blo 2079435 2079687 := bstep (se 1 (by rfl) ⟨1559765, by rfl⟩ : syracuseStep 2079687 = 3119531) B3119531
theorem B2339653 : Blo 2079435 2339653 := bbase (se 4 (by rfl) ⟨219342, by rfl⟩ : syracuseStep 2339653 = 438685) (by norm_num)
theorem B3119537 : Blo 2079435 3119537 := bstep (se 2 (by rfl) ⟨1169826, by rfl⟩ : syracuseStep 3119537 = 2339653) B2339653
theorem B2079691 : Blo 2079435 2079691 := bstep (se 1 (by rfl) ⟨1559768, by rfl⟩ : syracuseStep 2079691 = 3119537) B3119537
theorem B3948173 : Blo 2079435 3948173 := bbase (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) (by norm_num)
theorem B2632115 : Blo 2079435 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B7018973 : Blo 2079435 7018973 := bstep (se 3 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 7018973 = 2632115) B2632115
theorem B4679315 : Blo 2079435 4679315 := bstep (se 1 (by rfl) ⟨3509486, by rfl⟩ : syracuseStep 4679315 = 7018973) B7018973
theorem B3119543 : Blo 2079435 3119543 := bstep (se 1 (by rfl) ⟨2339657, by rfl⟩ : syracuseStep 3119543 = 4679315) B4679315
theorem B2079695 : Blo 2079435 2079695 := bstep (se 1 (by rfl) ⟨1559771, by rfl⟩ : syracuseStep 2079695 = 3119543) B3119543
theorem B3119549 : Blo 2079435 3119549 := bbase (se 3 (by rfl) ⟨584915, by rfl⟩ : syracuseStep 3119549 = 1169831) (by norm_num)
theorem B2079699 : Blo 2079435 2079699 := bstep (se 1 (by rfl) ⟨1559774, by rfl⟩ : syracuseStep 2079699 = 3119549) B3119549
theorem B4679333 : Blo 2079435 4679333 := bbase (se 4 (by rfl) ⟨438687, by rfl⟩ : syracuseStep 4679333 = 877375) (by norm_num)
theorem B3119555 : Blo 2079435 3119555 := bstep (se 1 (by rfl) ⟨2339666, by rfl⟩ : syracuseStep 3119555 = 4679333) B4679333
theorem B2079703 : Blo 2079435 2079703 := bstep (se 1 (by rfl) ⟨1559777, by rfl⟩ : syracuseStep 2079703 = 3119555) B3119555
theorem B5264261 : Blo 2079435 5264261 := bbase (se 4 (by rfl) ⟨493524, by rfl⟩ : syracuseStep 5264261 = 987049) (by norm_num)
theorem B3509507 : Blo 2079435 3509507 := bstep (se 1 (by rfl) ⟨2632130, by rfl⟩ : syracuseStep 3509507 = 5264261) B5264261
theorem B2339671 : Blo 2079435 2339671 := bstep (se 1 (by rfl) ⟨1754753, by rfl⟩ : syracuseStep 2339671 = 3509507) B3509507
theorem B3119561 : Blo 2079435 3119561 := bstep (se 2 (by rfl) ⟨1169835, by rfl⟩ : syracuseStep 3119561 = 2339671) B2339671
theorem B2079707 : Blo 2079435 2079707 := bstep (se 1 (by rfl) ⟨1559780, by rfl⟩ : syracuseStep 2079707 = 3119561) B3119561
theorem B2498473 : Blo 2079435 2498473 := bbase (se 2 (by rfl) ⟨936927, by rfl⟩ : syracuseStep 2498473 = 1873855) (by norm_num)
theorem B3331297 : Blo 2079435 3331297 := bstep (se 2 (by rfl) ⟨1249236, by rfl⟩ : syracuseStep 3331297 = 2498473) B2498473
theorem B4441729 : Blo 2079435 4441729 := bstep (se 2 (by rfl) ⟨1665648, by rfl⟩ : syracuseStep 4441729 = 3331297) B3331297
theorem B5922305 : Blo 2079435 5922305 := bstep (se 2 (by rfl) ⟨2220864, by rfl⟩ : syracuseStep 5922305 = 4441729) B4441729
theorem B3948203 : Blo 2079435 3948203 := bstep (se 1 (by rfl) ⟨2961152, by rfl⟩ : syracuseStep 3948203 = 5922305) B5922305
theorem B10528541 : Blo 2079435 10528541 := bstep (se 3 (by rfl) ⟨1974101, by rfl⟩ : syracuseStep 10528541 = 3948203) B3948203
theorem B7019027 : Blo 2079435 7019027 := bstep (se 1 (by rfl) ⟨5264270, by rfl⟩ : syracuseStep 7019027 = 10528541) B10528541
theorem B4679351 : Blo 2079435 4679351 := bstep (se 1 (by rfl) ⟨3509513, by rfl⟩ : syracuseStep 4679351 = 7019027) B7019027
theorem B3119567 : Blo 2079435 3119567 := bstep (se 1 (by rfl) ⟨2339675, by rfl⟩ : syracuseStep 3119567 = 4679351) B4679351
theorem B2079711 : Blo 2079435 2079711 := bstep (se 1 (by rfl) ⟨1559783, by rfl⟩ : syracuseStep 2079711 = 3119567) B3119567
theorem B3119573 : Blo 2079435 3119573 := bbase (se 7 (by rfl) ⟨36557, by rfl⟩ : syracuseStep 3119573 = 73115) (by norm_num)
theorem B2079715 : Blo 2079435 2079715 := bstep (se 1 (by rfl) ⟨1559786, by rfl⟩ : syracuseStep 2079715 = 3119573) B3119573
theorem B7896437 : Blo 2079435 7896437 := bbase (se 5 (by rfl) ⟨370145, by rfl⟩ : syracuseStep 7896437 = 740291) (by norm_num)
theorem B5264291 : Blo 2079435 5264291 := bstep (se 1 (by rfl) ⟨3948218, by rfl⟩ : syracuseStep 5264291 = 7896437) B7896437
theorem B3509527 : Blo 2079435 3509527 := bstep (se 1 (by rfl) ⟨2632145, by rfl⟩ : syracuseStep 3509527 = 5264291) B5264291
theorem B4679369 : Blo 2079435 4679369 := bstep (se 2 (by rfl) ⟨1754763, by rfl⟩ : syracuseStep 4679369 = 3509527) B3509527
theorem B3119579 : Blo 2079435 3119579 := bstep (se 1 (by rfl) ⟨2339684, by rfl⟩ : syracuseStep 3119579 = 4679369) B4679369
theorem B2079719 : Blo 2079435 2079719 := bstep (se 1 (by rfl) ⟨1559789, by rfl⟩ : syracuseStep 2079719 = 3119579) B3119579
theorem B2339689 : Blo 2079435 2339689 := bbase (se 2 (by rfl) ⟨877383, by rfl⟩ : syracuseStep 2339689 = 1754767) (by norm_num)
theorem B3119585 : Blo 2079435 3119585 := bstep (se 2 (by rfl) ⟨1169844, by rfl⟩ : syracuseStep 3119585 = 2339689) B2339689
theorem B2079723 : Blo 2079435 2079723 := bstep (se 1 (by rfl) ⟨1559792, by rfl⟩ : syracuseStep 2079723 = 3119585) B3119585
theorem B6662645 : Blo 2079435 6662645 := bbase (se 5 (by rfl) ⟨312311, by rfl⟩ : syracuseStep 6662645 = 624623) (by norm_num)
theorem B4441763 : Blo 2079435 4441763 := bstep (se 1 (by rfl) ⟨3331322, by rfl⟩ : syracuseStep 4441763 = 6662645) B6662645
theorem B11844701 : Blo 2079435 11844701 := bstep (se 3 (by rfl) ⟨2220881, by rfl⟩ : syracuseStep 11844701 = 4441763) B4441763
theorem B7896467 : Blo 2079435 7896467 := bstep (se 1 (by rfl) ⟨5922350, by rfl⟩ : syracuseStep 7896467 = 11844701) B11844701
theorem B5264311 : Blo 2079435 5264311 := bstep (se 1 (by rfl) ⟨3948233, by rfl⟩ : syracuseStep 5264311 = 7896467) B7896467
theorem B7019081 : Blo 2079435 7019081 := bstep (se 2 (by rfl) ⟨2632155, by rfl⟩ : syracuseStep 7019081 = 5264311) B5264311
theorem B4679387 : Blo 2079435 4679387 := bstep (se 1 (by rfl) ⟨3509540, by rfl⟩ : syracuseStep 4679387 = 7019081) B7019081
theorem B3119591 : Blo 2079435 3119591 := bstep (se 1 (by rfl) ⟨2339693, by rfl⟩ : syracuseStep 3119591 = 4679387) B4679387
theorem B2079727 : Blo 2079435 2079727 := bstep (se 1 (by rfl) ⟨1559795, by rfl⟩ : syracuseStep 2079727 = 3119591) B3119591
theorem B3119597 : Blo 2079435 3119597 := bbase (se 3 (by rfl) ⟨584924, by rfl⟩ : syracuseStep 3119597 = 1169849) (by norm_num)
theorem B2079731 : Blo 2079435 2079731 := bstep (se 1 (by rfl) ⟨1559798, by rfl⟩ : syracuseStep 2079731 = 3119597) B3119597
theorem B4679405 : Blo 2079435 4679405 := bbase (se 3 (by rfl) ⟨877388, by rfl⟩ : syracuseStep 4679405 = 1754777) (by norm_num)
theorem B3119603 : Blo 2079435 3119603 := bstep (se 1 (by rfl) ⟨2339702, by rfl⟩ : syracuseStep 3119603 = 4679405) B4679405
theorem B2079735 : Blo 2079435 2079735 := bstep (se 1 (by rfl) ⟨1559801, by rfl⟩ : syracuseStep 2079735 = 3119603) B3119603
theorem B11243285 : Blo 2079435 11243285 := bbase (se 6 (by rfl) ⟨263514, by rfl⟩ : syracuseStep 11243285 = 527029) (by norm_num)
theorem B7495523 : Blo 2079435 7495523 := bstep (se 1 (by rfl) ⟨5621642, by rfl⟩ : syracuseStep 7495523 = 11243285) B11243285
theorem B4997015 : Blo 2079435 4997015 := bstep (se 1 (by rfl) ⟨3747761, by rfl⟩ : syracuseStep 4997015 = 7495523) B7495523
theorem B3331343 : Blo 2079435 3331343 := bstep (se 1 (by rfl) ⟨2498507, by rfl⟩ : syracuseStep 3331343 = 4997015) B4997015
theorem B2220895 : Blo 2079435 2220895 := bstep (se 1 (by rfl) ⟨1665671, by rfl⟩ : syracuseStep 2220895 = 3331343) B3331343
theorem B2961193 : Blo 2079435 2961193 := bstep (se 2 (by rfl) ⟨1110447, by rfl⟩ : syracuseStep 2961193 = 2220895) B2220895
theorem B3948257 : Blo 2079435 3948257 := bstep (se 2 (by rfl) ⟨1480596, by rfl⟩ : syracuseStep 3948257 = 2961193) B2961193
theorem B2632171 : Blo 2079435 2632171 := bstep (se 1 (by rfl) ⟨1974128, by rfl⟩ : syracuseStep 2632171 = 3948257) B3948257
theorem B3509561 : Blo 2079435 3509561 := bstep (se 2 (by rfl) ⟨1316085, by rfl⟩ : syracuseStep 3509561 = 2632171) B2632171
theorem B2339707 : Blo 2079435 2339707 := bstep (se 1 (by rfl) ⟨1754780, by rfl⟩ : syracuseStep 2339707 = 3509561) B3509561
theorem B3119609 : Blo 2079435 3119609 := bstep (se 2 (by rfl) ⟨1169853, by rfl⟩ : syracuseStep 3119609 = 2339707) B2339707
theorem B2079739 : Blo 2079435 2079739 := bstep (se 1 (by rfl) ⟨1559804, by rfl⟩ : syracuseStep 2079739 = 3119609) B3119609
theorem B4216237 : Blo 2079435 4216237 := bbase (se 3 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 4216237 = 1581089) (by norm_num)
theorem B89946389 : Blo 2079435 89946389 := bstep (se 6 (by rfl) ⟨2108118, by rfl⟩ : syracuseStep 89946389 = 4216237) B4216237
theorem B59964259 : Blo 2079435 59964259 := bstep (se 1 (by rfl) ⟨44973194, by rfl⟩ : syracuseStep 59964259 = 89946389) B89946389
theorem B79952345 : Blo 2079435 79952345 := bstep (se 2 (by rfl) ⟨29982129, by rfl⟩ : syracuseStep 79952345 = 59964259) B59964259
theorem B53301563 : Blo 2079435 53301563 := bstep (se 1 (by rfl) ⟨39976172, by rfl⟩ : syracuseStep 53301563 = 79952345) B79952345
theorem B35534375 : Blo 2079435 35534375 := bstep (se 1 (by rfl) ⟨26650781, by rfl⟩ : syracuseStep 35534375 = 53301563) B53301563
theorem B23689583 : Blo 2079435 23689583 := bstep (se 1 (by rfl) ⟨17767187, by rfl⟩ : syracuseStep 23689583 = 35534375) B35534375
theorem B15793055 : Blo 2079435 15793055 := bstep (se 1 (by rfl) ⟨11844791, by rfl⟩ : syracuseStep 15793055 = 23689583) B23689583
theorem B10528703 : Blo 2079435 10528703 := bstep (se 1 (by rfl) ⟨7896527, by rfl⟩ : syracuseStep 10528703 = 15793055) B15793055
theorem B7019135 : Blo 2079435 7019135 := bstep (se 1 (by rfl) ⟨5264351, by rfl⟩ : syracuseStep 7019135 = 10528703) B10528703
theorem B4679423 : Blo 2079435 4679423 := bstep (se 1 (by rfl) ⟨3509567, by rfl⟩ : syracuseStep 4679423 = 7019135) B7019135
theorem B3119615 : Blo 2079435 3119615 := bstep (se 1 (by rfl) ⟨2339711, by rfl⟩ : syracuseStep 3119615 = 4679423) B4679423
theorem B2079743 : Blo 2079435 2079743 := bstep (se 1 (by rfl) ⟨1559807, by rfl⟩ : syracuseStep 2079743 = 3119615) B3119615
theorem B3119621 : Blo 2079435 3119621 := bbase (se 4 (by rfl) ⟨292464, by rfl⟩ : syracuseStep 3119621 = 584929) (by norm_num)
theorem B2079747 : Blo 2079435 2079747 := bstep (se 1 (by rfl) ⟨1559810, by rfl⟩ : syracuseStep 2079747 = 3119621) B3119621
theorem B3509581 : Blo 2079435 3509581 := bbase (se 3 (by rfl) ⟨658046, by rfl⟩ : syracuseStep 3509581 = 1316093) (by norm_num)
theorem B4679441 : Blo 2079435 4679441 := bstep (se 2 (by rfl) ⟨1754790, by rfl⟩ : syracuseStep 4679441 = 3509581) B3509581
theorem B3119627 : Blo 2079435 3119627 := bstep (se 1 (by rfl) ⟨2339720, by rfl⟩ : syracuseStep 3119627 = 4679441) B4679441
theorem B2079751 : Blo 2079435 2079751 := bstep (se 1 (by rfl) ⟨1559813, by rfl⟩ : syracuseStep 2079751 = 3119627) B3119627
theorem B2339725 : Blo 2079435 2339725 := bbase (se 3 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 2339725 = 877397) (by norm_num)
theorem B3119633 : Blo 2079435 3119633 := bstep (se 2 (by rfl) ⟨1169862, by rfl⟩ : syracuseStep 3119633 = 2339725) B2339725
theorem B2079755 : Blo 2079435 2079755 := bstep (se 1 (by rfl) ⟨1559816, by rfl⟩ : syracuseStep 2079755 = 3119633) B3119633
theorem B7019189 : Blo 2079435 7019189 := bbase (se 5 (by rfl) ⟨329024, by rfl⟩ : syracuseStep 7019189 = 658049) (by norm_num)
theorem B4679459 : Blo 2079435 4679459 := bstep (se 1 (by rfl) ⟨3509594, by rfl⟩ : syracuseStep 4679459 = 7019189) B7019189
theorem B3119639 : Blo 2079435 3119639 := bstep (se 1 (by rfl) ⟨2339729, by rfl⟩ : syracuseStep 3119639 = 4679459) B4679459
theorem B2079759 : Blo 2079435 2079759 := bstep (se 1 (by rfl) ⟨1559819, by rfl⟩ : syracuseStep 2079759 = 3119639) B3119639
theorem B3119645 : Blo 2079435 3119645 := bbase (se 3 (by rfl) ⟨584933, by rfl⟩ : syracuseStep 3119645 = 1169867) (by norm_num)
theorem B2079763 : Blo 2079435 2079763 := bstep (se 1 (by rfl) ⟨1559822, by rfl⟩ : syracuseStep 2079763 = 3119645) B3119645
theorem B4679477 : Blo 2079435 4679477 := bbase (se 5 (by rfl) ⟨219350, by rfl⟩ : syracuseStep 4679477 = 438701) (by norm_num)
theorem B3119651 : Blo 2079435 3119651 := bstep (se 1 (by rfl) ⟨2339738, by rfl⟩ : syracuseStep 3119651 = 4679477) B4679477
theorem B2079767 : Blo 2079435 2079767 := bstep (se 1 (by rfl) ⟨1559825, by rfl⟩ : syracuseStep 2079767 = 3119651) B3119651
theorem B2498545 : Blo 2079435 2498545 := bbase (se 2 (by rfl) ⟨936954, by rfl⟩ : syracuseStep 2498545 = 1873909) (by norm_num)
theorem B13325573 : Blo 2079435 13325573 := bstep (se 4 (by rfl) ⟨1249272, by rfl⟩ : syracuseStep 13325573 = 2498545) B2498545
theorem B8883715 : Blo 2079435 8883715 := bstep (se 1 (by rfl) ⟨6662786, by rfl⟩ : syracuseStep 8883715 = 13325573) B13325573
theorem B11844953 : Blo 2079435 11844953 := bstep (se 2 (by rfl) ⟨4441857, by rfl⟩ : syracuseStep 11844953 = 8883715) B8883715
theorem B7896635 : Blo 2079435 7896635 := bstep (se 1 (by rfl) ⟨5922476, by rfl⟩ : syracuseStep 7896635 = 11844953) B11844953
theorem B5264423 : Blo 2079435 5264423 := bstep (se 1 (by rfl) ⟨3948317, by rfl⟩ : syracuseStep 5264423 = 7896635) B7896635
theorem B3509615 : Blo 2079435 3509615 := bstep (se 1 (by rfl) ⟨2632211, by rfl⟩ : syracuseStep 3509615 = 5264423) B5264423
theorem B2339743 : Blo 2079435 2339743 := bstep (se 1 (by rfl) ⟨1754807, by rfl⟩ : syracuseStep 2339743 = 3509615) B3509615
theorem B3119657 : Blo 2079435 3119657 := bstep (se 2 (by rfl) ⟨1169871, by rfl⟩ : syracuseStep 3119657 = 2339743) B2339743
theorem B2079771 : Blo 2079435 2079771 := bstep (se 1 (by rfl) ⟨1559828, by rfl⟩ : syracuseStep 2079771 = 3119657) B3119657
theorem B18009877 : Blo 2079435 18009877 := bbase (se 6 (by rfl) ⟨422106, by rfl⟩ : syracuseStep 18009877 = 844213) (by norm_num)
theorem B24013169 : Blo 2079435 24013169 := bstep (se 2 (by rfl) ⟨9004938, by rfl⟩ : syracuseStep 24013169 = 18009877) B18009877
theorem B16008779 : Blo 2079435 16008779 := bstep (se 1 (by rfl) ⟨12006584, by rfl⟩ : syracuseStep 16008779 = 24013169) B24013169
theorem B10672519 : Blo 2079435 10672519 := bstep (se 1 (by rfl) ⟨8004389, by rfl⟩ : syracuseStep 10672519 = 16008779) B16008779
theorem B14230025 : Blo 2079435 14230025 := bstep (se 2 (by rfl) ⟨5336259, by rfl⟩ : syracuseStep 14230025 = 10672519) B10672519
theorem B9486683 : Blo 2079435 9486683 := bstep (se 1 (by rfl) ⟨7115012, by rfl⟩ : syracuseStep 9486683 = 14230025) B14230025
theorem B6324455 : Blo 2079435 6324455 := bstep (se 1 (by rfl) ⟨4743341, by rfl⟩ : syracuseStep 6324455 = 9486683) B9486683
theorem B4216303 : Blo 2079435 4216303 := bstep (se 1 (by rfl) ⟨3162227, by rfl⟩ : syracuseStep 4216303 = 6324455) B6324455
theorem B5621737 : Blo 2079435 5621737 := bstep (se 2 (by rfl) ⟨2108151, by rfl⟩ : syracuseStep 5621737 = 4216303) B4216303
theorem B7495649 : Blo 2079435 7495649 := bstep (se 2 (by rfl) ⟨2810868, by rfl⟩ : syracuseStep 7495649 = 5621737) B5621737
theorem B4997099 : Blo 2079435 4997099 := bstep (se 1 (by rfl) ⟨3747824, by rfl⟩ : syracuseStep 4997099 = 7495649) B7495649
theorem B13325597 : Blo 2079435 13325597 := bstep (se 3 (by rfl) ⟨2498549, by rfl⟩ : syracuseStep 13325597 = 4997099) B4997099
theorem B8883731 : Blo 2079435 8883731 := bstep (se 1 (by rfl) ⟨6662798, by rfl⟩ : syracuseStep 8883731 = 13325597) B13325597
theorem B5922487 : Blo 2079435 5922487 := bstep (se 1 (by rfl) ⟨4441865, by rfl⟩ : syracuseStep 5922487 = 8883731) B8883731
theorem B7896649 : Blo 2079435 7896649 := bstep (se 2 (by rfl) ⟨2961243, by rfl⟩ : syracuseStep 7896649 = 5922487) B5922487
theorem B10528865 : Blo 2079435 10528865 := bstep (se 2 (by rfl) ⟨3948324, by rfl⟩ : syracuseStep 10528865 = 7896649) B7896649
theorem B7019243 : Blo 2079435 7019243 := bstep (se 1 (by rfl) ⟨5264432, by rfl⟩ : syracuseStep 7019243 = 10528865) B10528865
theorem B4679495 : Blo 2079435 4679495 := bstep (se 1 (by rfl) ⟨3509621, by rfl⟩ : syracuseStep 4679495 = 7019243) B7019243
theorem B3119663 : Blo 2079435 3119663 := bstep (se 1 (by rfl) ⟨2339747, by rfl⟩ : syracuseStep 3119663 = 4679495) B4679495
theorem B2079775 : Blo 2079435 2079775 := bstep (se 1 (by rfl) ⟨1559831, by rfl⟩ : syracuseStep 2079775 = 3119663) B3119663
theorem B3119669 : Blo 2079435 3119669 := bbase (se 5 (by rfl) ⟨146234, by rfl⟩ : syracuseStep 3119669 = 292469) (by norm_num)
theorem B2079779 : Blo 2079435 2079779 := bstep (se 1 (by rfl) ⟨1559834, by rfl⟩ : syracuseStep 2079779 = 3119669) B3119669
theorem B5264453 : Blo 2079435 5264453 := bbase (se 4 (by rfl) ⟨493542, by rfl⟩ : syracuseStep 5264453 = 987085) (by norm_num)
theorem B3509635 : Blo 2079435 3509635 := bstep (se 1 (by rfl) ⟨2632226, by rfl⟩ : syracuseStep 3509635 = 5264453) B5264453
theorem B4679513 : Blo 2079435 4679513 := bstep (se 2 (by rfl) ⟨1754817, by rfl⟩ : syracuseStep 4679513 = 3509635) B3509635
theorem B3119675 : Blo 2079435 3119675 := bstep (se 1 (by rfl) ⟨2339756, by rfl⟩ : syracuseStep 3119675 = 4679513) B4679513
theorem B2079783 : Blo 2079435 2079783 := bstep (se 1 (by rfl) ⟨1559837, by rfl⟩ : syracuseStep 2079783 = 3119675) B3119675
theorem B2339761 : Blo 2079435 2339761 := bbase (se 2 (by rfl) ⟨877410, by rfl⟩ : syracuseStep 2339761 = 1754821) (by norm_num)
theorem B3119681 : Blo 2079435 3119681 := bstep (se 2 (by rfl) ⟨1169880, by rfl⟩ : syracuseStep 3119681 = 2339761) B2339761
theorem B2079787 : Blo 2079435 2079787 := bstep (se 1 (by rfl) ⟨1559840, by rfl⟩ : syracuseStep 2079787 = 3119681) B3119681
theorem B5922533 : Blo 2079435 5922533 := bbase (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) (by norm_num)
theorem B3948355 : Blo 2079435 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B5264473 : Blo 2079435 5264473 := bstep (se 2 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 5264473 = 3948355) B3948355
theorem B7019297 : Blo 2079435 7019297 := bstep (se 2 (by rfl) ⟨2632236, by rfl⟩ : syracuseStep 7019297 = 5264473) B5264473
theorem B4679531 : Blo 2079435 4679531 := bstep (se 1 (by rfl) ⟨3509648, by rfl⟩ : syracuseStep 4679531 = 7019297) B7019297
theorem B3119687 : Blo 2079435 3119687 := bstep (se 1 (by rfl) ⟨2339765, by rfl⟩ : syracuseStep 3119687 = 4679531) B4679531
theorem B2079791 : Blo 2079435 2079791 := bstep (se 1 (by rfl) ⟨1559843, by rfl⟩ : syracuseStep 2079791 = 3119687) B3119687
theorem B3119693 : Blo 2079435 3119693 := bbase (se 3 (by rfl) ⟨584942, by rfl⟩ : syracuseStep 3119693 = 1169885) (by norm_num)
theorem B2079795 : Blo 2079435 2079795 := bstep (se 1 (by rfl) ⟨1559846, by rfl⟩ : syracuseStep 2079795 = 3119693) B3119693
theorem B4679549 : Blo 2079435 4679549 := bbase (se 3 (by rfl) ⟨877415, by rfl⟩ : syracuseStep 4679549 = 1754831) (by norm_num)
theorem B3119699 : Blo 2079435 3119699 := bstep (se 1 (by rfl) ⟨2339774, by rfl⟩ : syracuseStep 3119699 = 4679549) B4679549
theorem B2079799 : Blo 2079435 2079799 := bstep (se 1 (by rfl) ⟨1559849, by rfl⟩ : syracuseStep 2079799 = 3119699) B3119699
theorem B3509669 : Blo 2079435 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B2339779 : Blo 2079435 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B3119705 : Blo 2079435 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B2079803 : Blo 2079435 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B3162277 : Blo 2079435 3162277 := bbase (se 4 (by rfl) ⟨296463, by rfl⟩ : syracuseStep 3162277 = 592927) (by norm_num)
theorem B4216369 : Blo 2079435 4216369 := bstep (se 2 (by rfl) ⟨1581138, by rfl⟩ : syracuseStep 4216369 = 3162277) B3162277
theorem B5621825 : Blo 2079435 5621825 := bstep (se 2 (by rfl) ⟨2108184, by rfl⟩ : syracuseStep 5621825 = 4216369) B4216369
theorem B3747883 : Blo 2079435 3747883 := bstep (se 1 (by rfl) ⟨2810912, by rfl⟩ : syracuseStep 3747883 = 5621825) B5621825
theorem B4997177 : Blo 2079435 4997177 := bstep (se 2 (by rfl) ⟨1873941, by rfl⟩ : syracuseStep 4997177 = 3747883) B3747883
theorem B3331451 : Blo 2079435 3331451 := bstep (se 1 (by rfl) ⟨2498588, by rfl⟩ : syracuseStep 3331451 = 4997177) B4997177
theorem B2220967 : Blo 2079435 2220967 := bstep (se 1 (by rfl) ⟨1665725, by rfl⟩ : syracuseStep 2220967 = 3331451) B3331451
theorem B2961289 : Blo 2079435 2961289 := bstep (se 2 (by rfl) ⟨1110483, by rfl⟩ : syracuseStep 2961289 = 2220967) B2220967
theorem B15793541 : Blo 2079435 15793541 := bstep (se 4 (by rfl) ⟨1480644, by rfl⟩ : syracuseStep 15793541 = 2961289) B2961289
theorem B10529027 : Blo 2079435 10529027 := bstep (se 1 (by rfl) ⟨7896770, by rfl⟩ : syracuseStep 10529027 = 15793541) B15793541
theorem B7019351 : Blo 2079435 7019351 := bstep (se 1 (by rfl) ⟨5264513, by rfl⟩ : syracuseStep 7019351 = 10529027) B10529027
theorem B4679567 : Blo 2079435 4679567 := bstep (se 1 (by rfl) ⟨3509675, by rfl⟩ : syracuseStep 4679567 = 7019351) B7019351
theorem B3119711 : Blo 2079435 3119711 := bstep (se 1 (by rfl) ⟨2339783, by rfl⟩ : syracuseStep 3119711 = 4679567) B4679567
theorem B2079807 : Blo 2079435 2079807 := bstep (se 1 (by rfl) ⟨1559855, by rfl⟩ : syracuseStep 2079807 = 3119711) B3119711
theorem B3119717 : Blo 2079435 3119717 := bbase (se 4 (by rfl) ⟨292473, by rfl⟩ : syracuseStep 3119717 = 584947) (by norm_num)
theorem B2079811 : Blo 2079435 2079811 := bstep (se 1 (by rfl) ⟨1559858, by rfl⟩ : syracuseStep 2079811 = 3119717) B3119717
theorem B2961301 : Blo 2079435 2961301 := bbase (se 6 (by rfl) ⟨69405, by rfl⟩ : syracuseStep 2961301 = 138811) (by norm_num)
theorem B3948401 : Blo 2079435 3948401 := bstep (se 2 (by rfl) ⟨1480650, by rfl⟩ : syracuseStep 3948401 = 2961301) B2961301
theorem B2632267 : Blo 2079435 2632267 := bstep (se 1 (by rfl) ⟨1974200, by rfl⟩ : syracuseStep 2632267 = 3948401) B3948401
theorem B3509689 : Blo 2079435 3509689 := bstep (se 2 (by rfl) ⟨1316133, by rfl⟩ : syracuseStep 3509689 = 2632267) B2632267
theorem B4679585 : Blo 2079435 4679585 := bstep (se 2 (by rfl) ⟨1754844, by rfl⟩ : syracuseStep 4679585 = 3509689) B3509689
theorem B3119723 : Blo 2079435 3119723 := bstep (se 1 (by rfl) ⟨2339792, by rfl⟩ : syracuseStep 3119723 = 4679585) B4679585
theorem B2079815 : Blo 2079435 2079815 := bstep (se 1 (by rfl) ⟨1559861, by rfl⟩ : syracuseStep 2079815 = 3119723) B3119723
theorem B2339797 : Blo 2079435 2339797 := bbase (se 7 (by rfl) ⟨27419, by rfl⟩ : syracuseStep 2339797 = 54839) (by norm_num)
theorem B3119729 : Blo 2079435 3119729 := bstep (se 2 (by rfl) ⟨1169898, by rfl⟩ : syracuseStep 3119729 = 2339797) B2339797
theorem B2079819 : Blo 2079435 2079819 := bstep (se 1 (by rfl) ⟨1559864, by rfl⟩ : syracuseStep 2079819 = 3119729) B3119729
theorem B2632277 : Blo 2079435 2632277 := bbase (se 8 (by rfl) ⟨15423, by rfl⟩ : syracuseStep 2632277 = 30847) (by norm_num)
theorem B7019405 : Blo 2079435 7019405 := bstep (se 3 (by rfl) ⟨1316138, by rfl⟩ : syracuseStep 7019405 = 2632277) B2632277
theorem B4679603 : Blo 2079435 4679603 := bstep (se 1 (by rfl) ⟨3509702, by rfl⟩ : syracuseStep 4679603 = 7019405) B7019405
theorem B3119735 : Blo 2079435 3119735 := bstep (se 1 (by rfl) ⟨2339801, by rfl⟩ : syracuseStep 3119735 = 4679603) B4679603
theorem B2079823 : Blo 2079435 2079823 := bstep (se 1 (by rfl) ⟨1559867, by rfl⟩ : syracuseStep 2079823 = 3119735) B3119735
theorem B3119741 : Blo 2079435 3119741 := bbase (se 3 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 3119741 = 1169903) (by norm_num)
theorem B2079827 : Blo 2079435 2079827 := bstep (se 1 (by rfl) ⟨1559870, by rfl⟩ : syracuseStep 2079827 = 3119741) B3119741
theorem B4679621 : Blo 2079435 4679621 := bbase (se 4 (by rfl) ⟨438714, by rfl⟩ : syracuseStep 4679621 = 877429) (by norm_num)
theorem B3119747 : Blo 2079435 3119747 := bstep (se 1 (by rfl) ⟨2339810, by rfl⟩ : syracuseStep 3119747 = 4679621) B4679621
theorem B2079831 : Blo 2079435 2079831 := bstep (se 1 (by rfl) ⟨1559873, by rfl⟩ : syracuseStep 2079831 = 3119747) B3119747
theorem B8883989 : Blo 2079435 8883989 := bbase (se 6 (by rfl) ⟨208218, by rfl⟩ : syracuseStep 8883989 = 416437) (by norm_num)
theorem B5922659 : Blo 2079435 5922659 := bstep (se 1 (by rfl) ⟨4441994, by rfl⟩ : syracuseStep 5922659 = 8883989) B8883989
theorem B3948439 : Blo 2079435 3948439 := bstep (se 1 (by rfl) ⟨2961329, by rfl⟩ : syracuseStep 3948439 = 5922659) B5922659
theorem B5264585 : Blo 2079435 5264585 := bstep (se 2 (by rfl) ⟨1974219, by rfl⟩ : syracuseStep 5264585 = 3948439) B3948439
theorem B3509723 : Blo 2079435 3509723 := bstep (se 1 (by rfl) ⟨2632292, by rfl⟩ : syracuseStep 3509723 = 5264585) B5264585
theorem B2339815 : Blo 2079435 2339815 := bstep (se 1 (by rfl) ⟨1754861, by rfl⟩ : syracuseStep 2339815 = 3509723) B3509723
theorem B3119753 : Blo 2079435 3119753 := bstep (se 2 (by rfl) ⟨1169907, by rfl⟩ : syracuseStep 3119753 = 2339815) B2339815
theorem B2079835 : Blo 2079435 2079835 := bstep (se 1 (by rfl) ⟨1559876, by rfl⟩ : syracuseStep 2079835 = 3119753) B3119753
theorem B10529189 : Blo 2079435 10529189 := bbase (se 4 (by rfl) ⟨987111, by rfl⟩ : syracuseStep 10529189 = 1974223) (by norm_num)
theorem B7019459 : Blo 2079435 7019459 := bstep (se 1 (by rfl) ⟨5264594, by rfl⟩ : syracuseStep 7019459 = 10529189) B10529189
theorem B4679639 : Blo 2079435 4679639 := bstep (se 1 (by rfl) ⟨3509729, by rfl⟩ : syracuseStep 4679639 = 7019459) B7019459
theorem B3119759 : Blo 2079435 3119759 := bstep (se 1 (by rfl) ⟨2339819, by rfl⟩ : syracuseStep 3119759 = 4679639) B4679639
theorem B2079839 : Blo 2079435 2079839 := bstep (se 1 (by rfl) ⟨1559879, by rfl⟩ : syracuseStep 2079839 = 3119759) B3119759
theorem B3119765 : Blo 2079435 3119765 := bbase (se 6 (by rfl) ⟨73119, by rfl⟩ : syracuseStep 3119765 = 146239) (by norm_num)
theorem B2079843 : Blo 2079435 2079843 := bstep (se 1 (by rfl) ⟨1559882, by rfl⟩ : syracuseStep 2079843 = 3119765) B3119765
theorem B3557629 : Blo 2079435 3557629 := bbase (se 3 (by rfl) ⟨667055, by rfl⟩ : syracuseStep 3557629 = 1334111) (by norm_num)
theorem B4743505 : Blo 2079435 4743505 := bstep (se 2 (by rfl) ⟨1778814, by rfl⟩ : syracuseStep 4743505 = 3557629) B3557629
theorem B25298693 : Blo 2079435 25298693 := bstep (se 4 (by rfl) ⟨2371752, by rfl⟩ : syracuseStep 25298693 = 4743505) B4743505
theorem B16865795 : Blo 2079435 16865795 := bstep (se 1 (by rfl) ⟨12649346, by rfl⟩ : syracuseStep 16865795 = 25298693) B25298693
theorem B11243863 : Blo 2079435 11243863 := bstep (se 1 (by rfl) ⟨8432897, by rfl⟩ : syracuseStep 11243863 = 16865795) B16865795
theorem B14991817 : Blo 2079435 14991817 := bstep (se 2 (by rfl) ⟨5621931, by rfl⟩ : syracuseStep 14991817 = 11243863) B11243863
theorem B19989089 : Blo 2079435 19989089 := bstep (se 2 (by rfl) ⟨7495908, by rfl⟩ : syracuseStep 19989089 = 14991817) B14991817
theorem B13326059 : Blo 2079435 13326059 := bstep (se 1 (by rfl) ⟨9994544, by rfl⟩ : syracuseStep 13326059 = 19989089) B19989089
theorem B8884039 : Blo 2079435 8884039 := bstep (se 1 (by rfl) ⟨6663029, by rfl⟩ : syracuseStep 8884039 = 13326059) B13326059
theorem B11845385 : Blo 2079435 11845385 := bstep (se 2 (by rfl) ⟨4442019, by rfl⟩ : syracuseStep 11845385 = 8884039) B8884039
theorem B7896923 : Blo 2079435 7896923 := bstep (se 1 (by rfl) ⟨5922692, by rfl⟩ : syracuseStep 7896923 = 11845385) B11845385
theorem B5264615 : Blo 2079435 5264615 := bstep (se 1 (by rfl) ⟨3948461, by rfl⟩ : syracuseStep 5264615 = 7896923) B7896923
theorem B3509743 : Blo 2079435 3509743 := bstep (se 1 (by rfl) ⟨2632307, by rfl⟩ : syracuseStep 3509743 = 5264615) B5264615
theorem B4679657 : Blo 2079435 4679657 := bstep (se 2 (by rfl) ⟨1754871, by rfl⟩ : syracuseStep 4679657 = 3509743) B3509743
theorem B3119771 : Blo 2079435 3119771 := bstep (se 1 (by rfl) ⟨2339828, by rfl⟩ : syracuseStep 3119771 = 4679657) B4679657
theorem B2079847 : Blo 2079435 2079847 := bstep (se 1 (by rfl) ⟨1559885, by rfl⟩ : syracuseStep 2079847 = 3119771) B3119771
theorem B2339833 : Blo 2079435 2339833 := bbase (se 2 (by rfl) ⟨877437, by rfl⟩ : syracuseStep 2339833 = 1754875) (by norm_num)
theorem B3119777 : Blo 2079435 3119777 := bstep (se 2 (by rfl) ⟨1169916, by rfl⟩ : syracuseStep 3119777 = 2339833) B2339833
theorem B2079851 : Blo 2079435 2079851 := bstep (se 1 (by rfl) ⟨1559888, by rfl⟩ : syracuseStep 2079851 = 3119777) B3119777
theorem B3162349 : Blo 2079435 3162349 := bbase (se 3 (by rfl) ⟨592940, by rfl⟩ : syracuseStep 3162349 = 1185881) (by norm_num)
theorem B4216465 : Blo 2079435 4216465 := bstep (se 2 (by rfl) ⟨1581174, by rfl⟩ : syracuseStep 4216465 = 3162349) B3162349
theorem B22487813 : Blo 2079435 22487813 := bstep (se 4 (by rfl) ⟨2108232, by rfl⟩ : syracuseStep 22487813 = 4216465) B4216465
theorem B14991875 : Blo 2079435 14991875 := bstep (se 1 (by rfl) ⟨11243906, by rfl⟩ : syracuseStep 14991875 = 22487813) B22487813
theorem B9994583 : Blo 2079435 9994583 := bstep (se 1 (by rfl) ⟨7495937, by rfl⟩ : syracuseStep 9994583 = 14991875) B14991875
theorem B6663055 : Blo 2079435 6663055 := bstep (se 1 (by rfl) ⟨4997291, by rfl⟩ : syracuseStep 6663055 = 9994583) B9994583
theorem B8884073 : Blo 2079435 8884073 := bstep (se 2 (by rfl) ⟨3331527, by rfl⟩ : syracuseStep 8884073 = 6663055) B6663055
theorem B5922715 : Blo 2079435 5922715 := bstep (se 1 (by rfl) ⟨4442036, by rfl⟩ : syracuseStep 5922715 = 8884073) B8884073
theorem B7896953 : Blo 2079435 7896953 := bstep (se 2 (by rfl) ⟨2961357, by rfl⟩ : syracuseStep 7896953 = 5922715) B5922715
theorem B5264635 : Blo 2079435 5264635 := bstep (se 1 (by rfl) ⟨3948476, by rfl⟩ : syracuseStep 5264635 = 7896953) B7896953
theorem B7019513 : Blo 2079435 7019513 := bstep (se 2 (by rfl) ⟨2632317, by rfl⟩ : syracuseStep 7019513 = 5264635) B5264635
theorem B4679675 : Blo 2079435 4679675 := bstep (se 1 (by rfl) ⟨3509756, by rfl⟩ : syracuseStep 4679675 = 7019513) B7019513
theorem B3119783 : Blo 2079435 3119783 := bstep (se 1 (by rfl) ⟨2339837, by rfl⟩ : syracuseStep 3119783 = 4679675) B4679675
theorem B2079855 : Blo 2079435 2079855 := bstep (se 1 (by rfl) ⟨1559891, by rfl⟩ : syracuseStep 2079855 = 3119783) B3119783
theorem B3119789 : Blo 2079435 3119789 := bbase (se 3 (by rfl) ⟨584960, by rfl⟩ : syracuseStep 3119789 = 1169921) (by norm_num)
theorem B2079859 : Blo 2079435 2079859 := bstep (se 1 (by rfl) ⟨1559894, by rfl⟩ : syracuseStep 2079859 = 3119789) B3119789
theorem B4679693 : Blo 2079435 4679693 := bbase (se 3 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 4679693 = 1754885) (by norm_num)
theorem B3119795 : Blo 2079435 3119795 := bstep (se 1 (by rfl) ⟨2339846, by rfl⟩ : syracuseStep 3119795 = 4679693) B4679693
theorem B2079863 : Blo 2079435 2079863 := bstep (se 1 (by rfl) ⟨1559897, by rfl⟩ : syracuseStep 2079863 = 3119795) B3119795
theorem B2632333 : Blo 2079435 2632333 := bbase (se 3 (by rfl) ⟨493562, by rfl⟩ : syracuseStep 2632333 = 987125) (by norm_num)
theorem B3509777 : Blo 2079435 3509777 := bstep (se 2 (by rfl) ⟨1316166, by rfl⟩ : syracuseStep 3509777 = 2632333) B2632333
theorem B2339851 : Blo 2079435 2339851 := bstep (se 1 (by rfl) ⟨1754888, by rfl⟩ : syracuseStep 2339851 = 3509777) B3509777
theorem B3119801 : Blo 2079435 3119801 := bstep (se 2 (by rfl) ⟨1169925, by rfl⟩ : syracuseStep 3119801 = 2339851) B2339851
theorem B2079867 : Blo 2079435 2079867 := bstep (se 1 (by rfl) ⟨1559900, by rfl⟩ : syracuseStep 2079867 = 3119801) B3119801
theorem B3747997 : Blo 2079435 3747997 := bbase (se 3 (by rfl) ⟨702749, by rfl⟩ : syracuseStep 3747997 = 1405499) (by norm_num)
theorem B19989317 : Blo 2079435 19989317 := bstep (se 4 (by rfl) ⟨1873998, by rfl⟩ : syracuseStep 19989317 = 3747997) B3747997
theorem B13326211 : Blo 2079435 13326211 := bstep (se 1 (by rfl) ⟨9994658, by rfl⟩ : syracuseStep 13326211 = 19989317) B19989317
theorem B17768281 : Blo 2079435 17768281 := bstep (se 2 (by rfl) ⟨6663105, by rfl⟩ : syracuseStep 17768281 = 13326211) B13326211
theorem B23691041 : Blo 2079435 23691041 := bstep (se 2 (by rfl) ⟨8884140, by rfl⟩ : syracuseStep 23691041 = 17768281) B17768281
theorem B15794027 : Blo 2079435 15794027 := bstep (se 1 (by rfl) ⟨11845520, by rfl⟩ : syracuseStep 15794027 = 23691041) B23691041
theorem B10529351 : Blo 2079435 10529351 := bstep (se 1 (by rfl) ⟨7897013, by rfl⟩ : syracuseStep 10529351 = 15794027) B15794027
theorem B7019567 : Blo 2079435 7019567 := bstep (se 1 (by rfl) ⟨5264675, by rfl⟩ : syracuseStep 7019567 = 10529351) B10529351
theorem B4679711 : Blo 2079435 4679711 := bstep (se 1 (by rfl) ⟨3509783, by rfl⟩ : syracuseStep 4679711 = 7019567) B7019567
theorem B3119807 : Blo 2079435 3119807 := bstep (se 1 (by rfl) ⟨2339855, by rfl⟩ : syracuseStep 3119807 = 4679711) B4679711
theorem B2079871 : Blo 2079435 2079871 := bstep (se 1 (by rfl) ⟨1559903, by rfl⟩ : syracuseStep 2079871 = 3119807) B3119807
theorem B3119813 : Blo 2079435 3119813 := bbase (se 4 (by rfl) ⟨292482, by rfl⟩ : syracuseStep 3119813 = 584965) (by norm_num)
theorem B2079875 : Blo 2079435 2079875 := bstep (se 1 (by rfl) ⟨1559906, by rfl⟩ : syracuseStep 2079875 = 3119813) B3119813
theorem B3509797 : Blo 2079435 3509797 := bbase (se 4 (by rfl) ⟨329043, by rfl⟩ : syracuseStep 3509797 = 658087) (by norm_num)
theorem B4679729 : Blo 2079435 4679729 := bstep (se 2 (by rfl) ⟨1754898, by rfl⟩ : syracuseStep 4679729 = 3509797) B3509797
theorem B3119819 : Blo 2079435 3119819 := bstep (se 1 (by rfl) ⟨2339864, by rfl⟩ : syracuseStep 3119819 = 4679729) B4679729
theorem B2079879 : Blo 2079435 2079879 := bstep (se 1 (by rfl) ⟨1559909, by rfl⟩ : syracuseStep 2079879 = 3119819) B3119819
theorem B2339869 : Blo 2079435 2339869 := bbase (se 3 (by rfl) ⟨438725, by rfl⟩ : syracuseStep 2339869 = 877451) (by norm_num)
theorem B3119825 : Blo 2079435 3119825 := bstep (se 2 (by rfl) ⟨1169934, by rfl⟩ : syracuseStep 3119825 = 2339869) B2339869
theorem B2079883 : Blo 2079435 2079883 := bstep (se 1 (by rfl) ⟨1559912, by rfl⟩ : syracuseStep 2079883 = 3119825) B3119825
theorem B7019621 : Blo 2079435 7019621 := bbase (se 4 (by rfl) ⟨658089, by rfl⟩ : syracuseStep 7019621 = 1316179) (by norm_num)
theorem B4679747 : Blo 2079435 4679747 := bstep (se 1 (by rfl) ⟨3509810, by rfl⟩ : syracuseStep 4679747 = 7019621) B7019621
theorem B3119831 : Blo 2079435 3119831 := bstep (se 1 (by rfl) ⟨2339873, by rfl⟩ : syracuseStep 3119831 = 4679747) B4679747
theorem B2079887 : Blo 2079435 2079887 := bstep (se 1 (by rfl) ⟨1559915, by rfl⟩ : syracuseStep 2079887 = 3119831) B3119831
theorem B3119837 : Blo 2079435 3119837 := bbase (se 3 (by rfl) ⟨584969, by rfl⟩ : syracuseStep 3119837 = 1169939) (by norm_num)
theorem B2079891 : Blo 2079435 2079891 := bstep (se 1 (by rfl) ⟨1559918, by rfl⟩ : syracuseStep 2079891 = 3119837) B3119837
theorem B4679765 : Blo 2079435 4679765 := bbase (se 8 (by rfl) ⟨27420, by rfl⟩ : syracuseStep 4679765 = 54841) (by norm_num)
theorem B3119843 : Blo 2079435 3119843 := bstep (se 1 (by rfl) ⟨2339882, by rfl⟩ : syracuseStep 3119843 = 4679765) B4679765
theorem B2079895 : Blo 2079435 2079895 := bstep (se 1 (by rfl) ⟨1559921, by rfl⟩ : syracuseStep 2079895 = 3119843) B3119843
theorem B2811037 : Blo 2079435 2811037 := bbase (se 3 (by rfl) ⟨527069, by rfl⟩ : syracuseStep 2811037 = 1054139) (by norm_num)
theorem B3748049 : Blo 2079435 3748049 := bstep (se 2 (by rfl) ⟨1405518, by rfl⟩ : syracuseStep 3748049 = 2811037) B2811037
theorem B2498699 : Blo 2079435 2498699 := bstep (se 1 (by rfl) ⟨1874024, by rfl⟩ : syracuseStep 2498699 = 3748049) B3748049
theorem B6663197 : Blo 2079435 6663197 := bstep (se 3 (by rfl) ⟨1249349, by rfl⟩ : syracuseStep 6663197 = 2498699) B2498699
theorem B4442131 : Blo 2079435 4442131 := bstep (se 1 (by rfl) ⟨3331598, by rfl⟩ : syracuseStep 4442131 = 6663197) B6663197
theorem B5922841 : Blo 2079435 5922841 := bstep (se 2 (by rfl) ⟨2221065, by rfl⟩ : syracuseStep 5922841 = 4442131) B4442131
theorem B7897121 : Blo 2079435 7897121 := bstep (se 2 (by rfl) ⟨2961420, by rfl⟩ : syracuseStep 7897121 = 5922841) B5922841
theorem B5264747 : Blo 2079435 5264747 := bstep (se 1 (by rfl) ⟨3948560, by rfl⟩ : syracuseStep 5264747 = 7897121) B7897121
theorem B3509831 : Blo 2079435 3509831 := bstep (se 1 (by rfl) ⟨2632373, by rfl⟩ : syracuseStep 3509831 = 5264747) B5264747
theorem B2339887 : Blo 2079435 2339887 := bstep (se 1 (by rfl) ⟨1754915, by rfl⟩ : syracuseStep 2339887 = 3509831) B3509831
theorem B3119849 : Blo 2079435 3119849 := bstep (se 2 (by rfl) ⟨1169943, by rfl⟩ : syracuseStep 3119849 = 2339887) B2339887
theorem B2079899 : Blo 2079435 2079899 := bstep (se 1 (by rfl) ⟨1559924, by rfl⟩ : syracuseStep 2079899 = 3119849) B3119849
theorem B2137045 : Blo 2079435 2137045 := bbase (se 7 (by rfl) ⟨25043, by rfl⟩ : syracuseStep 2137045 = 50087) (by norm_num)
theorem B45590293 : Blo 2079435 45590293 := bstep (se 6 (by rfl) ⟨1068522, by rfl⟩ : syracuseStep 45590293 = 2137045) B2137045
theorem B60787057 : Blo 2079435 60787057 := bstep (se 2 (by rfl) ⟨22795146, by rfl⟩ : syracuseStep 60787057 = 45590293) B45590293
theorem B81049409 : Blo 2079435 81049409 := bstep (se 2 (by rfl) ⟨30393528, by rfl⟩ : syracuseStep 81049409 = 60787057) B60787057
theorem B54032939 : Blo 2079435 54032939 := bstep (se 1 (by rfl) ⟨40524704, by rfl⟩ : syracuseStep 54032939 = 81049409) B81049409
theorem B36021959 : Blo 2079435 36021959 := bstep (se 1 (by rfl) ⟨27016469, by rfl⟩ : syracuseStep 36021959 = 54032939) B54032939
theorem B24014639 : Blo 2079435 24014639 := bstep (se 1 (by rfl) ⟨18010979, by rfl⟩ : syracuseStep 24014639 = 36021959) B36021959
theorem B16009759 : Blo 2079435 16009759 := bstep (se 1 (by rfl) ⟨12007319, by rfl⟩ : syracuseStep 16009759 = 24014639) B24014639
theorem B21346345 : Blo 2079435 21346345 := bstep (se 2 (by rfl) ⟨8004879, by rfl⟩ : syracuseStep 21346345 = 16009759) B16009759
theorem B28461793 : Blo 2079435 28461793 := bstep (se 2 (by rfl) ⟨10673172, by rfl⟩ : syracuseStep 28461793 = 21346345) B21346345
theorem B37949057 : Blo 2079435 37949057 := bstep (se 2 (by rfl) ⟨14230896, by rfl⟩ : syracuseStep 37949057 = 28461793) B28461793
theorem B25299371 : Blo 2079435 25299371 := bstep (se 1 (by rfl) ⟨18974528, by rfl⟩ : syracuseStep 25299371 = 37949057) B37949057
theorem B16866247 : Blo 2079435 16866247 := bstep (se 1 (by rfl) ⟨12649685, by rfl⟩ : syracuseStep 16866247 = 25299371) B25299371
theorem B22488329 : Blo 2079435 22488329 := bstep (se 2 (by rfl) ⟨8433123, by rfl⟩ : syracuseStep 22488329 = 16866247) B16866247
theorem B14992219 : Blo 2079435 14992219 := bstep (se 1 (by rfl) ⟨11244164, by rfl⟩ : syracuseStep 14992219 = 22488329) B22488329
theorem B19989625 : Blo 2079435 19989625 := bstep (se 2 (by rfl) ⟨7496109, by rfl⟩ : syracuseStep 19989625 = 14992219) B14992219
theorem B26652833 : Blo 2079435 26652833 := bstep (se 2 (by rfl) ⟨9994812, by rfl⟩ : syracuseStep 26652833 = 19989625) B19989625
theorem B17768555 : Blo 2079435 17768555 := bstep (se 1 (by rfl) ⟨13326416, by rfl⟩ : syracuseStep 17768555 = 26652833) B26652833
theorem B11845703 : Blo 2079435 11845703 := bstep (se 1 (by rfl) ⟨8884277, by rfl⟩ : syracuseStep 11845703 = 17768555) B17768555
theorem B7897135 : Blo 2079435 7897135 := bstep (se 1 (by rfl) ⟨5922851, by rfl⟩ : syracuseStep 7897135 = 11845703) B11845703
theorem B10529513 : Blo 2079435 10529513 := bstep (se 2 (by rfl) ⟨3948567, by rfl⟩ : syracuseStep 10529513 = 7897135) B7897135
theorem B7019675 : Blo 2079435 7019675 := bstep (se 1 (by rfl) ⟨5264756, by rfl⟩ : syracuseStep 7019675 = 10529513) B10529513
theorem B4679783 : Blo 2079435 4679783 := bstep (se 1 (by rfl) ⟨3509837, by rfl⟩ : syracuseStep 4679783 = 7019675) B7019675
theorem B3119855 : Blo 2079435 3119855 := bstep (se 1 (by rfl) ⟨2339891, by rfl⟩ : syracuseStep 3119855 = 4679783) B4679783
theorem B2079903 : Blo 2079435 2079903 := bstep (se 1 (by rfl) ⟨1559927, by rfl⟩ : syracuseStep 2079903 = 3119855) B3119855
theorem B3119861 : Blo 2079435 3119861 := bbase (se 5 (by rfl) ⟨146243, by rfl⟩ : syracuseStep 3119861 = 292487) (by norm_num)
theorem B2079907 : Blo 2079435 2079907 := bstep (se 1 (by rfl) ⟨1559930, by rfl⟩ : syracuseStep 2079907 = 3119861) B3119861
theorem B9994853 : Blo 2079435 9994853 := bbase (se 4 (by rfl) ⟨937017, by rfl⟩ : syracuseStep 9994853 = 1874035) (by norm_num)
theorem B6663235 : Blo 2079435 6663235 := bstep (se 1 (by rfl) ⟨4997426, by rfl⟩ : syracuseStep 6663235 = 9994853) B9994853
theorem B8884313 : Blo 2079435 8884313 := bstep (se 2 (by rfl) ⟨3331617, by rfl⟩ : syracuseStep 8884313 = 6663235) B6663235
theorem B5922875 : Blo 2079435 5922875 := bstep (se 1 (by rfl) ⟨4442156, by rfl⟩ : syracuseStep 5922875 = 8884313) B8884313
theorem B3948583 : Blo 2079435 3948583 := bstep (se 1 (by rfl) ⟨2961437, by rfl⟩ : syracuseStep 3948583 = 5922875) B5922875
theorem B5264777 : Blo 2079435 5264777 := bstep (se 2 (by rfl) ⟨1974291, by rfl⟩ : syracuseStep 5264777 = 3948583) B3948583
theorem B3509851 : Blo 2079435 3509851 := bstep (se 1 (by rfl) ⟨2632388, by rfl⟩ : syracuseStep 3509851 = 5264777) B5264777
theorem B4679801 : Blo 2079435 4679801 := bstep (se 2 (by rfl) ⟨1754925, by rfl⟩ : syracuseStep 4679801 = 3509851) B3509851
theorem B3119867 : Blo 2079435 3119867 := bstep (se 1 (by rfl) ⟨2339900, by rfl⟩ : syracuseStep 3119867 = 4679801) B4679801
theorem B2079911 : Blo 2079435 2079911 := bstep (se 1 (by rfl) ⟨1559933, by rfl⟩ : syracuseStep 2079911 = 3119867) B3119867
theorem B2339905 : Blo 2079435 2339905 := bbase (se 2 (by rfl) ⟨877464, by rfl⟩ : syracuseStep 2339905 = 1754929) (by norm_num)
theorem B3119873 : Blo 2079435 3119873 := bstep (se 2 (by rfl) ⟨1169952, by rfl⟩ : syracuseStep 3119873 = 2339905) B2339905
theorem B2079915 : Blo 2079435 2079915 := bstep (se 1 (by rfl) ⟨1559936, by rfl⟩ : syracuseStep 2079915 = 3119873) B3119873
theorem B5264797 : Blo 2079435 5264797 := bbase (se 3 (by rfl) ⟨987149, by rfl⟩ : syracuseStep 5264797 = 1974299) (by norm_num)
theorem B7019729 : Blo 2079435 7019729 := bstep (se 2 (by rfl) ⟨2632398, by rfl⟩ : syracuseStep 7019729 = 5264797) B5264797
theorem B4679819 : Blo 2079435 4679819 := bstep (se 1 (by rfl) ⟨3509864, by rfl⟩ : syracuseStep 4679819 = 7019729) B7019729
theorem B3119879 : Blo 2079435 3119879 := bstep (se 1 (by rfl) ⟨2339909, by rfl⟩ : syracuseStep 3119879 = 4679819) B4679819
theorem B2079919 : Blo 2079435 2079919 := bstep (se 1 (by rfl) ⟨1559939, by rfl⟩ : syracuseStep 2079919 = 3119879) B3119879
theorem B3119885 : Blo 2079435 3119885 := bbase (se 3 (by rfl) ⟨584978, by rfl⟩ : syracuseStep 3119885 = 1169957) (by norm_num)
theorem B2079923 : Blo 2079435 2079923 := bstep (se 1 (by rfl) ⟨1559942, by rfl⟩ : syracuseStep 2079923 = 3119885) B3119885
theorem B4679837 : Blo 2079435 4679837 := bbase (se 3 (by rfl) ⟨877469, by rfl⟩ : syracuseStep 4679837 = 1754939) (by norm_num)
theorem B3119891 : Blo 2079435 3119891 := bstep (se 1 (by rfl) ⟨2339918, by rfl⟩ : syracuseStep 3119891 = 4679837) B4679837
theorem B2079927 : Blo 2079435 2079927 := bstep (se 1 (by rfl) ⟨1559945, by rfl⟩ : syracuseStep 2079927 = 3119891) B3119891
theorem B3509885 : Blo 2079435 3509885 := bbase (se 3 (by rfl) ⟨658103, by rfl⟩ : syracuseStep 3509885 = 1316207) (by norm_num)
theorem B2339923 : Blo 2079435 2339923 := bstep (se 1 (by rfl) ⟨1754942, by rfl⟩ : syracuseStep 2339923 = 3509885) B3509885
theorem B3119897 : Blo 2079435 3119897 := bstep (se 2 (by rfl) ⟨1169961, by rfl⟩ : syracuseStep 3119897 = 2339923) B2339923
theorem B2079931 : Blo 2079435 2079931 := bstep (se 1 (by rfl) ⟨1559948, by rfl⟩ : syracuseStep 2079931 = 3119897) B3119897
theorem B2371853 : Blo 2079435 2371853 := bbase (se 3 (by rfl) ⟨444722, by rfl⟩ : syracuseStep 2371853 = 889445) (by norm_num)
theorem B6324941 : Blo 2079435 6324941 := bstep (se 3 (by rfl) ⟨1185926, by rfl⟩ : syracuseStep 6324941 = 2371853) B2371853
theorem B4216627 : Blo 2079435 4216627 := bstep (se 1 (by rfl) ⟨3162470, by rfl⟩ : syracuseStep 4216627 = 6324941) B6324941
theorem B22488677 : Blo 2079435 22488677 := bstep (se 4 (by rfl) ⟨2108313, by rfl⟩ : syracuseStep 22488677 = 4216627) B4216627
theorem B14992451 : Blo 2079435 14992451 := bstep (se 1 (by rfl) ⟨11244338, by rfl⟩ : syracuseStep 14992451 = 22488677) B22488677
theorem B9994967 : Blo 2079435 9994967 := bstep (se 1 (by rfl) ⟨7496225, by rfl⟩ : syracuseStep 9994967 = 14992451) B14992451
theorem B6663311 : Blo 2079435 6663311 := bstep (se 1 (by rfl) ⟨4997483, by rfl⟩ : syracuseStep 6663311 = 9994967) B9994967
theorem B4442207 : Blo 2079435 4442207 := bstep (se 1 (by rfl) ⟨3331655, by rfl⟩ : syracuseStep 4442207 = 6663311) B6663311
theorem B11845885 : Blo 2079435 11845885 := bstep (se 3 (by rfl) ⟨2221103, by rfl⟩ : syracuseStep 11845885 = 4442207) B4442207
theorem B15794513 : Blo 2079435 15794513 := bstep (se 2 (by rfl) ⟨5922942, by rfl⟩ : syracuseStep 15794513 = 11845885) B11845885
theorem B10529675 : Blo 2079435 10529675 := bstep (se 1 (by rfl) ⟨7897256, by rfl⟩ : syracuseStep 10529675 = 15794513) B15794513
theorem B7019783 : Blo 2079435 7019783 := bstep (se 1 (by rfl) ⟨5264837, by rfl⟩ : syracuseStep 7019783 = 10529675) B10529675
theorem B4679855 : Blo 2079435 4679855 := bstep (se 1 (by rfl) ⟨3509891, by rfl⟩ : syracuseStep 4679855 = 7019783) B7019783
theorem B3119903 : Blo 2079435 3119903 := bstep (se 1 (by rfl) ⟨2339927, by rfl⟩ : syracuseStep 3119903 = 4679855) B4679855
theorem B2079935 : Blo 2079435 2079935 := bstep (se 1 (by rfl) ⟨1559951, by rfl⟩ : syracuseStep 2079935 = 3119903) B3119903
theorem B3119909 : Blo 2079435 3119909 := bbase (se 4 (by rfl) ⟨292491, by rfl⟩ : syracuseStep 3119909 = 584983) (by norm_num)
theorem B2079939 : Blo 2079435 2079939 := bstep (se 1 (by rfl) ⟨1559954, by rfl⟩ : syracuseStep 2079939 = 3119909) B3119909
theorem B2632429 : Blo 2079435 2632429 := bbase (se 3 (by rfl) ⟨493580, by rfl⟩ : syracuseStep 2632429 = 987161) (by norm_num)
theorem B3509905 : Blo 2079435 3509905 := bstep (se 2 (by rfl) ⟨1316214, by rfl⟩ : syracuseStep 3509905 = 2632429) B2632429
theorem B4679873 : Blo 2079435 4679873 := bstep (se 2 (by rfl) ⟨1754952, by rfl⟩ : syracuseStep 4679873 = 3509905) B3509905
theorem B3119915 : Blo 2079435 3119915 := bstep (se 1 (by rfl) ⟨2339936, by rfl⟩ : syracuseStep 3119915 = 4679873) B4679873
theorem B2079943 : Blo 2079435 2079943 := bstep (se 1 (by rfl) ⟨1559957, by rfl⟩ : syracuseStep 2079943 = 3119915) B3119915
theorem B2339941 : Blo 2079435 2339941 := bbase (se 4 (by rfl) ⟨219369, by rfl⟩ : syracuseStep 2339941 = 438739) (by norm_num)
theorem B3119921 : Blo 2079435 3119921 := bstep (se 2 (by rfl) ⟨1169970, by rfl⟩ : syracuseStep 3119921 = 2339941) B2339941
theorem B2079947 : Blo 2079435 2079947 := bstep (se 1 (by rfl) ⟨1559960, by rfl⟩ : syracuseStep 2079947 = 3119921) B3119921
theorem B2221121 : Blo 2079435 2221121 := bbase (se 2 (by rfl) ⟨832920, by rfl⟩ : syracuseStep 2221121 = 1665841) (by norm_num)
theorem B5922989 : Blo 2079435 5922989 := bstep (se 3 (by rfl) ⟨1110560, by rfl⟩ : syracuseStep 5922989 = 2221121) B2221121
theorem B3948659 : Blo 2079435 3948659 := bstep (se 1 (by rfl) ⟨2961494, by rfl⟩ : syracuseStep 3948659 = 5922989) B5922989
theorem B2632439 : Blo 2079435 2632439 := bstep (se 1 (by rfl) ⟨1974329, by rfl⟩ : syracuseStep 2632439 = 3948659) B3948659
theorem B7019837 : Blo 2079435 7019837 := bstep (se 3 (by rfl) ⟨1316219, by rfl⟩ : syracuseStep 7019837 = 2632439) B2632439
theorem B4679891 : Blo 2079435 4679891 := bstep (se 1 (by rfl) ⟨3509918, by rfl⟩ : syracuseStep 4679891 = 7019837) B7019837
theorem B3119927 : Blo 2079435 3119927 := bstep (se 1 (by rfl) ⟨2339945, by rfl⟩ : syracuseStep 3119927 = 4679891) B4679891
theorem B2079951 : Blo 2079435 2079951 := bstep (se 1 (by rfl) ⟨1559963, by rfl⟩ : syracuseStep 2079951 = 3119927) B3119927
theorem B3119933 : Blo 2079435 3119933 := bbase (se 3 (by rfl) ⟨584987, by rfl⟩ : syracuseStep 3119933 = 1169975) (by norm_num)
theorem B2079955 : Blo 2079435 2079955 := bstep (se 1 (by rfl) ⟨1559966, by rfl⟩ : syracuseStep 2079955 = 3119933) B3119933
theorem B4679909 : Blo 2079435 4679909 := bbase (se 4 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 4679909 = 877483) (by norm_num)
theorem B3119939 : Blo 2079435 3119939 := bstep (se 1 (by rfl) ⟨2339954, by rfl⟩ : syracuseStep 3119939 = 4679909) B4679909
theorem B2079959 : Blo 2079435 2079959 := bstep (se 1 (by rfl) ⟨1559969, by rfl⟩ : syracuseStep 2079959 = 3119939) B3119939
theorem B5264909 : Blo 2079435 5264909 := bbase (se 3 (by rfl) ⟨987170, by rfl⟩ : syracuseStep 5264909 = 1974341) (by norm_num)
theorem B3509939 : Blo 2079435 3509939 := bstep (se 1 (by rfl) ⟨2632454, by rfl⟩ : syracuseStep 3509939 = 5264909) B5264909
theorem B2339959 : Blo 2079435 2339959 := bstep (se 1 (by rfl) ⟨1754969, by rfl⟩ : syracuseStep 2339959 = 3509939) B3509939
theorem B3119945 : Blo 2079435 3119945 := bstep (se 2 (by rfl) ⟨1169979, by rfl⟩ : syracuseStep 3119945 = 2339959) B2339959
theorem B2079963 : Blo 2079435 2079963 := bstep (se 1 (by rfl) ⟨1559972, by rfl⟩ : syracuseStep 2079963 = 3119945) B3119945
theorem B2961517 : Blo 2079435 2961517 := bbase (se 3 (by rfl) ⟨555284, by rfl⟩ : syracuseStep 2961517 = 1110569) (by norm_num)
theorem B3948689 : Blo 2079435 3948689 := bstep (se 2 (by rfl) ⟨1480758, by rfl⟩ : syracuseStep 3948689 = 2961517) B2961517
theorem B10529837 : Blo 2079435 10529837 := bstep (se 3 (by rfl) ⟨1974344, by rfl⟩ : syracuseStep 10529837 = 3948689) B3948689
theorem B7019891 : Blo 2079435 7019891 := bstep (se 1 (by rfl) ⟨5264918, by rfl⟩ : syracuseStep 7019891 = 10529837) B10529837
theorem B4679927 : Blo 2079435 4679927 := bstep (se 1 (by rfl) ⟨3509945, by rfl⟩ : syracuseStep 4679927 = 7019891) B7019891
theorem B3119951 : Blo 2079435 3119951 := bstep (se 1 (by rfl) ⟨2339963, by rfl⟩ : syracuseStep 3119951 = 4679927) B4679927
theorem B2079967 : Blo 2079435 2079967 := bstep (se 1 (by rfl) ⟨1559975, by rfl⟩ : syracuseStep 2079967 = 3119951) B3119951
theorem B3119957 : Blo 2079435 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B2079971 : Blo 2079435 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B4442293 : Blo 2079435 4442293 := bbase (se 5 (by rfl) ⟨208232, by rfl⟩ : syracuseStep 4442293 = 416465) (by norm_num)
theorem B5923057 : Blo 2079435 5923057 := bstep (se 2 (by rfl) ⟨2221146, by rfl⟩ : syracuseStep 5923057 = 4442293) B4442293
theorem B7897409 : Blo 2079435 7897409 := bstep (se 2 (by rfl) ⟨2961528, by rfl⟩ : syracuseStep 7897409 = 5923057) B5923057
theorem B5264939 : Blo 2079435 5264939 := bstep (se 1 (by rfl) ⟨3948704, by rfl⟩ : syracuseStep 5264939 = 7897409) B7897409
theorem B3509959 : Blo 2079435 3509959 := bstep (se 1 (by rfl) ⟨2632469, by rfl⟩ : syracuseStep 3509959 = 5264939) B5264939
theorem B4679945 : Blo 2079435 4679945 := bstep (se 2 (by rfl) ⟨1754979, by rfl⟩ : syracuseStep 4679945 = 3509959) B3509959
theorem B3119963 : Blo 2079435 3119963 := bstep (se 1 (by rfl) ⟨2339972, by rfl⟩ : syracuseStep 3119963 = 4679945) B4679945
theorem B2079975 : Blo 2079435 2079975 := bstep (se 1 (by rfl) ⟨1559981, by rfl⟩ : syracuseStep 2079975 = 3119963) B3119963
theorem B2339977 : Blo 2079435 2339977 := bbase (se 2 (by rfl) ⟨877491, by rfl⟩ : syracuseStep 2339977 = 1754983) (by norm_num)
theorem B3119969 : Blo 2079435 3119969 := bstep (se 2 (by rfl) ⟨1169988, by rfl⟩ : syracuseStep 3119969 = 2339977) B2339977
theorem B2079979 : Blo 2079435 2079979 := bstep (se 1 (by rfl) ⟨1559984, by rfl⟩ : syracuseStep 2079979 = 3119969) B3119969
theorem B32020757 : Blo 2079435 32020757 := bbase (se 6 (by rfl) ⟨750486, by rfl⟩ : syracuseStep 32020757 = 1500973) (by norm_num)
theorem B21347171 : Blo 2079435 21347171 := bstep (se 1 (by rfl) ⟨16010378, by rfl⟩ : syracuseStep 21347171 = 32020757) B32020757
theorem B14231447 : Blo 2079435 14231447 := bstep (se 1 (by rfl) ⟨10673585, by rfl⟩ : syracuseStep 14231447 = 21347171) B21347171
theorem B9487631 : Blo 2079435 9487631 := bstep (se 1 (by rfl) ⟨7115723, by rfl⟩ : syracuseStep 9487631 = 14231447) B14231447
theorem B6325087 : Blo 2079435 6325087 := bstep (se 1 (by rfl) ⟨4743815, by rfl⟩ : syracuseStep 6325087 = 9487631) B9487631
theorem B8433449 : Blo 2079435 8433449 := bstep (se 2 (by rfl) ⟨3162543, by rfl⟩ : syracuseStep 8433449 = 6325087) B6325087
theorem B5622299 : Blo 2079435 5622299 := bstep (se 1 (by rfl) ⟨4216724, by rfl⟩ : syracuseStep 5622299 = 8433449) B8433449
theorem B3748199 : Blo 2079435 3748199 := bstep (se 1 (by rfl) ⟨2811149, by rfl⟩ : syracuseStep 3748199 = 5622299) B5622299
theorem B39980789 : Blo 2079435 39980789 := bstep (se 5 (by rfl) ⟨1874099, by rfl⟩ : syracuseStep 39980789 = 3748199) B3748199
theorem B26653859 : Blo 2079435 26653859 := bstep (se 1 (by rfl) ⟨19990394, by rfl⟩ : syracuseStep 26653859 = 39980789) B39980789
theorem B17769239 : Blo 2079435 17769239 := bstep (se 1 (by rfl) ⟨13326929, by rfl⟩ : syracuseStep 17769239 = 26653859) B26653859
theorem B11846159 : Blo 2079435 11846159 := bstep (se 1 (by rfl) ⟨8884619, by rfl⟩ : syracuseStep 11846159 = 17769239) B17769239
theorem B7897439 : Blo 2079435 7897439 := bstep (se 1 (by rfl) ⟨5923079, by rfl⟩ : syracuseStep 7897439 = 11846159) B11846159
theorem B5264959 : Blo 2079435 5264959 := bstep (se 1 (by rfl) ⟨3948719, by rfl⟩ : syracuseStep 5264959 = 7897439) B7897439
theorem B7019945 : Blo 2079435 7019945 := bstep (se 2 (by rfl) ⟨2632479, by rfl⟩ : syracuseStep 7019945 = 5264959) B5264959
theorem B4679963 : Blo 2079435 4679963 := bstep (se 1 (by rfl) ⟨3509972, by rfl⟩ : syracuseStep 4679963 = 7019945) B7019945
theorem B3119975 : Blo 2079435 3119975 := bstep (se 1 (by rfl) ⟨2339981, by rfl⟩ : syracuseStep 3119975 = 4679963) B4679963
theorem B2079983 : Blo 2079435 2079983 := bstep (se 1 (by rfl) ⟨1559987, by rfl⟩ : syracuseStep 2079983 = 3119975) B3119975
theorem B3119981 : Blo 2079435 3119981 := bbase (se 3 (by rfl) ⟨584996, by rfl⟩ : syracuseStep 3119981 = 1169993) (by norm_num)
theorem B2079987 : Blo 2079435 2079987 := bstep (se 1 (by rfl) ⟨1559990, by rfl⟩ : syracuseStep 2079987 = 3119981) B3119981
theorem B4679981 : Blo 2079435 4679981 := bbase (se 3 (by rfl) ⟨877496, by rfl⟩ : syracuseStep 4679981 = 1754993) (by norm_num)
theorem B3119987 : Blo 2079435 3119987 := bstep (se 1 (by rfl) ⟨2339990, by rfl⟩ : syracuseStep 3119987 = 4679981) B4679981
theorem B2079991 : Blo 2079435 2079991 := bstep (se 1 (by rfl) ⟨1559993, by rfl⟩ : syracuseStep 2079991 = 3119987) B3119987
theorem B4997629 : Blo 2079435 4997629 := bbase (se 3 (by rfl) ⟨937055, by rfl⟩ : syracuseStep 4997629 = 1874111) (by norm_num)
theorem B6663505 : Blo 2079435 6663505 := bstep (se 2 (by rfl) ⟨2498814, by rfl⟩ : syracuseStep 6663505 = 4997629) B4997629
theorem B8884673 : Blo 2079435 8884673 := bstep (se 2 (by rfl) ⟨3331752, by rfl⟩ : syracuseStep 8884673 = 6663505) B6663505
theorem B5923115 : Blo 2079435 5923115 := bstep (se 1 (by rfl) ⟨4442336, by rfl⟩ : syracuseStep 5923115 = 8884673) B8884673
theorem B3948743 : Blo 2079435 3948743 := bstep (se 1 (by rfl) ⟨2961557, by rfl⟩ : syracuseStep 3948743 = 5923115) B5923115
theorem B2632495 : Blo 2079435 2632495 := bstep (se 1 (by rfl) ⟨1974371, by rfl⟩ : syracuseStep 2632495 = 3948743) B3948743
theorem B3509993 : Blo 2079435 3509993 := bstep (se 2 (by rfl) ⟨1316247, by rfl⟩ : syracuseStep 3509993 = 2632495) B2632495
theorem B2339995 : Blo 2079435 2339995 := bstep (se 1 (by rfl) ⟨1754996, by rfl⟩ : syracuseStep 2339995 = 3509993) B3509993
theorem B3119993 : Blo 2079435 3119993 := bstep (se 2 (by rfl) ⟨1169997, by rfl⟩ : syracuseStep 3119993 = 2339995) B2339995
theorem B2079995 : Blo 2079435 2079995 := bstep (se 1 (by rfl) ⟨1559996, by rfl⟩ : syracuseStep 2079995 = 3119993) B3119993
theorem B2251477 : Blo 2079435 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B3001969 : Blo 2079435 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B4002625 : Blo 2079435 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B5336833 : Blo 2079435 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B7115777 : Blo 2079435 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B4743851 : Blo 2079435 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B12650269 : Blo 2079435 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B16867025 : Blo 2079435 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B11244683 : Blo 2079435 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B29985821 : Blo 2079435 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B19990547 : Blo 2079435 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B13327031 : Blo 2079435 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B35538749 : Blo 2079435 35538749 := bstep (se 3 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 35538749 = 13327031) B13327031
theorem B23692499 : Blo 2079435 23692499 := bstep (se 1 (by rfl) ⟨17769374, by rfl⟩ : syracuseStep 23692499 = 35538749) B35538749
theorem B15794999 : Blo 2079435 15794999 := bstep (se 1 (by rfl) ⟨11846249, by rfl⟩ : syracuseStep 15794999 = 23692499) B23692499
theorem B10529999 : Blo 2079435 10529999 := bstep (se 1 (by rfl) ⟨7897499, by rfl⟩ : syracuseStep 10529999 = 15794999) B15794999
theorem B7019999 : Blo 2079435 7019999 := bstep (se 1 (by rfl) ⟨5264999, by rfl⟩ : syracuseStep 7019999 = 10529999) B10529999
theorem B4679999 : Blo 2079435 4679999 := bstep (se 1 (by rfl) ⟨3509999, by rfl⟩ : syracuseStep 4679999 = 7019999) B7019999
theorem B3119999 : Blo 2079435 3119999 := bstep (se 1 (by rfl) ⟨2339999, by rfl⟩ : syracuseStep 3119999 = 4679999) B4679999
theorem B2079999 : Blo 2079435 2079999 := bstep (se 1 (by rfl) ⟨1559999, by rfl⟩ : syracuseStep 2079999 = 3119999) B3119999
theorem B3120005 : Blo 2079435 3120005 := bbase (se 4 (by rfl) ⟨292500, by rfl⟩ : syracuseStep 3120005 = 585001) (by norm_num)
theorem B2080003 : Blo 2079435 2080003 := bstep (se 1 (by rfl) ⟨1560002, by rfl⟩ : syracuseStep 2080003 = 3120005) B3120005
theorem B3510013 : Blo 2079435 3510013 := bbase (se 3 (by rfl) ⟨658127, by rfl⟩ : syracuseStep 3510013 = 1316255) (by norm_num)
theorem B4680017 : Blo 2079435 4680017 := bstep (se 2 (by rfl) ⟨1755006, by rfl⟩ : syracuseStep 4680017 = 3510013) B3510013
theorem B3120011 : Blo 2079435 3120011 := bstep (se 1 (by rfl) ⟨2340008, by rfl⟩ : syracuseStep 3120011 = 4680017) B4680017
theorem B2080007 : Blo 2079435 2080007 := bstep (se 1 (by rfl) ⟨1560005, by rfl⟩ : syracuseStep 2080007 = 3120011) B3120011
theorem B2340013 : Blo 2079435 2340013 := bbase (se 3 (by rfl) ⟨438752, by rfl⟩ : syracuseStep 2340013 = 877505) (by norm_num)
theorem B3120017 : Blo 2079435 3120017 := bstep (se 2 (by rfl) ⟨1170006, by rfl⟩ : syracuseStep 3120017 = 2340013) B2340013
theorem B2080011 : Blo 2079435 2080011 := bstep (se 1 (by rfl) ⟨1560008, by rfl⟩ : syracuseStep 2080011 = 3120017) B3120017
theorem B7020053 : Blo 2079435 7020053 := bbase (se 6 (by rfl) ⟨164532, by rfl⟩ : syracuseStep 7020053 = 329065) (by norm_num)
theorem B4680035 : Blo 2079435 4680035 := bstep (se 1 (by rfl) ⟨3510026, by rfl⟩ : syracuseStep 4680035 = 7020053) B7020053
theorem B3120023 : Blo 2079435 3120023 := bstep (se 1 (by rfl) ⟨2340017, by rfl⟩ : syracuseStep 3120023 = 4680035) B4680035
theorem B2080015 : Blo 2079435 2080015 := bstep (se 1 (by rfl) ⟨1560011, by rfl⟩ : syracuseStep 2080015 = 3120023) B3120023
theorem B3120029 : Blo 2079435 3120029 := bbase (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) (by norm_num)
theorem B2080019 : Blo 2079435 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B4680053 : Blo 2079435 4680053 := bbase (se 5 (by rfl) ⟨219377, by rfl⟩ : syracuseStep 4680053 = 438755) (by norm_num)
theorem B3120035 : Blo 2079435 3120035 := bstep (se 1 (by rfl) ⟨2340026, by rfl⟩ : syracuseStep 3120035 = 4680053) B4680053
theorem B2080023 : Blo 2079435 2080023 := bstep (se 1 (by rfl) ⟨1560017, by rfl⟩ : syracuseStep 2080023 = 3120035) B3120035
theorem B4743917 : Blo 2079435 4743917 := bbase (se 3 (by rfl) ⟨889484, by rfl⟩ : syracuseStep 4743917 = 1778969) (by norm_num)
theorem B3162611 : Blo 2079435 3162611 := bstep (se 1 (by rfl) ⟨2371958, by rfl⟩ : syracuseStep 3162611 = 4743917) B4743917
theorem B8433629 : Blo 2079435 8433629 := bstep (se 3 (by rfl) ⟨1581305, by rfl⟩ : syracuseStep 8433629 = 3162611) B3162611
theorem B5622419 : Blo 2079435 5622419 := bstep (se 1 (by rfl) ⟨4216814, by rfl⟩ : syracuseStep 5622419 = 8433629) B8433629
theorem B3748279 : Blo 2079435 3748279 := bstep (se 1 (by rfl) ⟨2811209, by rfl⟩ : syracuseStep 3748279 = 5622419) B5622419
theorem B4997705 : Blo 2079435 4997705 := bstep (se 2 (by rfl) ⟨1874139, by rfl⟩ : syracuseStep 4997705 = 3748279) B3748279
theorem B13327213 : Blo 2079435 13327213 := bstep (se 3 (by rfl) ⟨2498852, by rfl⟩ : syracuseStep 13327213 = 4997705) B4997705
theorem B17769617 : Blo 2079435 17769617 := bstep (se 2 (by rfl) ⟨6663606, by rfl⟩ : syracuseStep 17769617 = 13327213) B13327213
theorem B11846411 : Blo 2079435 11846411 := bstep (se 1 (by rfl) ⟨8884808, by rfl⟩ : syracuseStep 11846411 = 17769617) B17769617
theorem B7897607 : Blo 2079435 7897607 := bstep (se 1 (by rfl) ⟨5923205, by rfl⟩ : syracuseStep 7897607 = 11846411) B11846411
theorem B5265071 : Blo 2079435 5265071 := bstep (se 1 (by rfl) ⟨3948803, by rfl⟩ : syracuseStep 5265071 = 7897607) B7897607
theorem B3510047 : Blo 2079435 3510047 := bstep (se 1 (by rfl) ⟨2632535, by rfl⟩ : syracuseStep 3510047 = 5265071) B5265071
theorem B2340031 : Blo 2079435 2340031 := bstep (se 1 (by rfl) ⟨1755023, by rfl⟩ : syracuseStep 2340031 = 3510047) B3510047
theorem B3120041 : Blo 2079435 3120041 := bstep (se 2 (by rfl) ⟨1170015, by rfl⟩ : syracuseStep 3120041 = 2340031) B2340031
theorem B2080027 : Blo 2079435 2080027 := bstep (se 1 (by rfl) ⟨1560020, by rfl⟩ : syracuseStep 2080027 = 3120041) B3120041
theorem B7897621 : Blo 2079435 7897621 := bbase (se 6 (by rfl) ⟨185100, by rfl⟩ : syracuseStep 7897621 = 370201) (by norm_num)
theorem B10530161 : Blo 2079435 10530161 := bstep (se 2 (by rfl) ⟨3948810, by rfl⟩ : syracuseStep 10530161 = 7897621) B7897621
theorem B7020107 : Blo 2079435 7020107 := bstep (se 1 (by rfl) ⟨5265080, by rfl⟩ : syracuseStep 7020107 = 10530161) B10530161
theorem B4680071 : Blo 2079435 4680071 := bstep (se 1 (by rfl) ⟨3510053, by rfl⟩ : syracuseStep 4680071 = 7020107) B7020107
theorem B3120047 : Blo 2079435 3120047 := bstep (se 1 (by rfl) ⟨2340035, by rfl⟩ : syracuseStep 3120047 = 4680071) B4680071
theorem B2080031 : Blo 2079435 2080031 := bstep (se 1 (by rfl) ⟨1560023, by rfl⟩ : syracuseStep 2080031 = 3120047) B3120047
theorem B3120053 : Blo 2079435 3120053 := bbase (se 5 (by rfl) ⟨146252, by rfl⟩ : syracuseStep 3120053 = 292505) (by norm_num)
theorem B2080035 : Blo 2079435 2080035 := bstep (se 1 (by rfl) ⟨1560026, by rfl⟩ : syracuseStep 2080035 = 3120053) B3120053
theorem B5265101 : Blo 2079435 5265101 := bbase (se 3 (by rfl) ⟨987206, by rfl⟩ : syracuseStep 5265101 = 1974413) (by norm_num)
theorem B3510067 : Blo 2079435 3510067 := bstep (se 1 (by rfl) ⟨2632550, by rfl⟩ : syracuseStep 3510067 = 5265101) B5265101
theorem B4680089 : Blo 2079435 4680089 := bstep (se 2 (by rfl) ⟨1755033, by rfl⟩ : syracuseStep 4680089 = 3510067) B3510067
theorem B3120059 : Blo 2079435 3120059 := bstep (se 1 (by rfl) ⟨2340044, by rfl⟩ : syracuseStep 3120059 = 4680089) B4680089
theorem B2080039 : Blo 2079435 2080039 := bstep (se 1 (by rfl) ⟨1560029, by rfl⟩ : syracuseStep 2080039 = 3120059) B3120059
theorem B2340049 : Blo 2079435 2340049 := bbase (se 2 (by rfl) ⟨877518, by rfl⟩ : syracuseStep 2340049 = 1755037) (by norm_num)
theorem B3120065 : Blo 2079435 3120065 := bstep (se 2 (by rfl) ⟨1170024, by rfl⟩ : syracuseStep 3120065 = 2340049) B2340049
theorem B2080043 : Blo 2079435 2080043 := bstep (se 1 (by rfl) ⟨1560032, by rfl⟩ : syracuseStep 2080043 = 3120065) B3120065
theorem B9487925 : Blo 2079435 9487925 := bbase (se 5 (by rfl) ⟨444746, by rfl⟩ : syracuseStep 9487925 = 889493) (by norm_num)
theorem B6325283 : Blo 2079435 6325283 := bstep (se 1 (by rfl) ⟨4743962, by rfl⟩ : syracuseStep 6325283 = 9487925) B9487925
theorem B4216855 : Blo 2079435 4216855 := bstep (se 1 (by rfl) ⟨3162641, by rfl⟩ : syracuseStep 4216855 = 6325283) B6325283
theorem B5622473 : Blo 2079435 5622473 := bstep (se 2 (by rfl) ⟨2108427, by rfl⟩ : syracuseStep 5622473 = 4216855) B4216855
theorem B14993261 : Blo 2079435 14993261 := bstep (se 3 (by rfl) ⟨2811236, by rfl⟩ : syracuseStep 14993261 = 5622473) B5622473
theorem B9995507 : Blo 2079435 9995507 := bstep (se 1 (by rfl) ⟨7496630, by rfl⟩ : syracuseStep 9995507 = 14993261) B14993261
theorem B6663671 : Blo 2079435 6663671 := bstep (se 1 (by rfl) ⟨4997753, by rfl⟩ : syracuseStep 6663671 = 9995507) B9995507
theorem B4442447 : Blo 2079435 4442447 := bstep (se 1 (by rfl) ⟨3331835, by rfl⟩ : syracuseStep 4442447 = 6663671) B6663671
theorem B2961631 : Blo 2079435 2961631 := bstep (se 1 (by rfl) ⟨2221223, by rfl⟩ : syracuseStep 2961631 = 4442447) B4442447
theorem B3948841 : Blo 2079435 3948841 := bstep (se 2 (by rfl) ⟨1480815, by rfl⟩ : syracuseStep 3948841 = 2961631) B2961631
theorem B5265121 : Blo 2079435 5265121 := bstep (se 2 (by rfl) ⟨1974420, by rfl⟩ : syracuseStep 5265121 = 3948841) B3948841
theorem B7020161 : Blo 2079435 7020161 := bstep (se 2 (by rfl) ⟨2632560, by rfl⟩ : syracuseStep 7020161 = 5265121) B5265121
theorem B4680107 : Blo 2079435 4680107 := bstep (se 1 (by rfl) ⟨3510080, by rfl⟩ : syracuseStep 4680107 = 7020161) B7020161
theorem B3120071 : Blo 2079435 3120071 := bstep (se 1 (by rfl) ⟨2340053, by rfl⟩ : syracuseStep 3120071 = 4680107) B4680107
theorem B2080047 : Blo 2079435 2080047 := bstep (se 1 (by rfl) ⟨1560035, by rfl⟩ : syracuseStep 2080047 = 3120071) B3120071
theorem B3120077 : Blo 2079435 3120077 := bbase (se 3 (by rfl) ⟨585014, by rfl⟩ : syracuseStep 3120077 = 1170029) (by norm_num)
theorem B2080051 : Blo 2079435 2080051 := bstep (se 1 (by rfl) ⟨1560038, by rfl⟩ : syracuseStep 2080051 = 3120077) B3120077
theorem B4680125 : Blo 2079435 4680125 := bbase (se 3 (by rfl) ⟨877523, by rfl⟩ : syracuseStep 4680125 = 1755047) (by norm_num)
theorem B3120083 : Blo 2079435 3120083 := bstep (se 1 (by rfl) ⟨2340062, by rfl⟩ : syracuseStep 3120083 = 4680125) B4680125
theorem B2080055 : Blo 2079435 2080055 := bstep (se 1 (by rfl) ⟨1560041, by rfl⟩ : syracuseStep 2080055 = 3120083) B3120083
theorem B3510101 : Blo 2079435 3510101 := bbase (se 9 (by rfl) ⟨10283, by rfl⟩ : syracuseStep 3510101 = 20567) (by norm_num)
theorem B2340067 : Blo 2079435 2340067 := bstep (se 1 (by rfl) ⟨1755050, by rfl⟩ : syracuseStep 2340067 = 3510101) B3510101
theorem B3120089 : Blo 2079435 3120089 := bstep (se 2 (by rfl) ⟨1170033, by rfl⟩ : syracuseStep 3120089 = 2340067) B2340067
theorem B2080059 : Blo 2079435 2080059 := bstep (se 1 (by rfl) ⟨1560044, by rfl⟩ : syracuseStep 2080059 = 3120089) B3120089
theorem B12008245 : Blo 2079435 12008245 := bbase (se 5 (by rfl) ⟨562886, by rfl⟩ : syracuseStep 12008245 = 1125773) (by norm_num)
theorem B16010993 : Blo 2079435 16010993 := bstep (se 2 (by rfl) ⟨6004122, by rfl⟩ : syracuseStep 16010993 = 12008245) B12008245
theorem B42695981 : Blo 2079435 42695981 := bstep (se 3 (by rfl) ⟨8005496, by rfl⟩ : syracuseStep 42695981 = 16010993) B16010993
theorem B28463987 : Blo 2079435 28463987 := bstep (se 1 (by rfl) ⟨21347990, by rfl⟩ : syracuseStep 28463987 = 42695981) B42695981
theorem B18975991 : Blo 2079435 18975991 := bstep (se 1 (by rfl) ⟨14231993, by rfl⟩ : syracuseStep 18975991 = 28463987) B28463987
theorem B25301321 : Blo 2079435 25301321 := bstep (se 2 (by rfl) ⟨9487995, by rfl⟩ : syracuseStep 25301321 = 18975991) B18975991
theorem B16867547 : Blo 2079435 16867547 := bstep (se 1 (by rfl) ⟨12650660, by rfl⟩ : syracuseStep 16867547 = 25301321) B25301321
theorem B11245031 : Blo 2079435 11245031 := bstep (se 1 (by rfl) ⟨8433773, by rfl⟩ : syracuseStep 11245031 = 16867547) B16867547
theorem B7496687 : Blo 2079435 7496687 := bstep (se 1 (by rfl) ⟨5622515, by rfl⟩ : syracuseStep 7496687 = 11245031) B11245031
theorem B4997791 : Blo 2079435 4997791 := bstep (se 1 (by rfl) ⟨3748343, by rfl⟩ : syracuseStep 4997791 = 7496687) B7496687
theorem B6663721 : Blo 2079435 6663721 := bstep (se 2 (by rfl) ⟨2498895, by rfl⟩ : syracuseStep 6663721 = 4997791) B4997791
theorem B8884961 : Blo 2079435 8884961 := bstep (se 2 (by rfl) ⟨3331860, by rfl⟩ : syracuseStep 8884961 = 6663721) B6663721
theorem B5923307 : Blo 2079435 5923307 := bstep (se 1 (by rfl) ⟨4442480, by rfl⟩ : syracuseStep 5923307 = 8884961) B8884961
theorem B15795485 : Blo 2079435 15795485 := bstep (se 3 (by rfl) ⟨2961653, by rfl⟩ : syracuseStep 15795485 = 5923307) B5923307
theorem B10530323 : Blo 2079435 10530323 := bstep (se 1 (by rfl) ⟨7897742, by rfl⟩ : syracuseStep 10530323 = 15795485) B15795485
theorem B7020215 : Blo 2079435 7020215 := bstep (se 1 (by rfl) ⟨5265161, by rfl⟩ : syracuseStep 7020215 = 10530323) B10530323
theorem B4680143 : Blo 2079435 4680143 := bstep (se 1 (by rfl) ⟨3510107, by rfl⟩ : syracuseStep 4680143 = 7020215) B7020215
theorem B3120095 : Blo 2079435 3120095 := bstep (se 1 (by rfl) ⟨2340071, by rfl⟩ : syracuseStep 3120095 = 4680143) B4680143
theorem B2080063 : Blo 2079435 2080063 := bstep (se 1 (by rfl) ⟨1560047, by rfl⟩ : syracuseStep 2080063 = 3120095) B3120095
theorem B3120101 : Blo 2079435 3120101 := bbase (se 4 (by rfl) ⟨292509, by rfl⟩ : syracuseStep 3120101 = 585019) (by norm_num)
theorem B2080067 : Blo 2079435 2080067 := bstep (se 1 (by rfl) ⟨1560050, by rfl⟩ : syracuseStep 2080067 = 3120101) B3120101
theorem B8884997 : Blo 2079435 8884997 := bbase (se 4 (by rfl) ⟨832968, by rfl⟩ : syracuseStep 8884997 = 1665937) (by norm_num)
theorem B5923331 : Blo 2079435 5923331 := bstep (se 1 (by rfl) ⟨4442498, by rfl⟩ : syracuseStep 5923331 = 8884997) B8884997
theorem B3948887 : Blo 2079435 3948887 := bstep (se 1 (by rfl) ⟨2961665, by rfl⟩ : syracuseStep 3948887 = 5923331) B5923331
theorem B2632591 : Blo 2079435 2632591 := bstep (se 1 (by rfl) ⟨1974443, by rfl⟩ : syracuseStep 2632591 = 3948887) B3948887
theorem B3510121 : Blo 2079435 3510121 := bstep (se 2 (by rfl) ⟨1316295, by rfl⟩ : syracuseStep 3510121 = 2632591) B2632591
theorem B4680161 : Blo 2079435 4680161 := bstep (se 2 (by rfl) ⟨1755060, by rfl⟩ : syracuseStep 4680161 = 3510121) B3510121
theorem B3120107 : Blo 2079435 3120107 := bstep (se 1 (by rfl) ⟨2340080, by rfl⟩ : syracuseStep 3120107 = 4680161) B4680161
theorem B2080071 : Blo 2079435 2080071 := bstep (se 1 (by rfl) ⟨1560053, by rfl⟩ : syracuseStep 2080071 = 3120107) B3120107
theorem B2340085 : Blo 2079435 2340085 := bbase (se 5 (by rfl) ⟨109691, by rfl⟩ : syracuseStep 2340085 = 219383) (by norm_num)
theorem B3120113 : Blo 2079435 3120113 := bstep (se 2 (by rfl) ⟨1170042, by rfl⟩ : syracuseStep 3120113 = 2340085) B2340085
theorem B2080075 : Blo 2079435 2080075 := bstep (se 1 (by rfl) ⟨1560056, by rfl⟩ : syracuseStep 2080075 = 3120113) B3120113
theorem B2632601 : Blo 2079435 2632601 := bbase (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) (by norm_num)
theorem B7020269 : Blo 2079435 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B4680179 : Blo 2079435 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B3120119 : Blo 2079435 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B2080079 : Blo 2079435 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B3120125 : Blo 2079435 3120125 := bbase (se 3 (by rfl) ⟨585023, by rfl⟩ : syracuseStep 3120125 = 1170047) (by norm_num)
theorem B2080083 : Blo 2079435 2080083 := bstep (se 1 (by rfl) ⟨1560062, by rfl⟩ : syracuseStep 2080083 = 3120125) B3120125
theorem B4680197 : Blo 2079435 4680197 := bbase (se 4 (by rfl) ⟨438768, by rfl⟩ : syracuseStep 4680197 = 877537) (by norm_num)
theorem B3120131 : Blo 2079435 3120131 := bstep (se 1 (by rfl) ⟨2340098, by rfl⟩ : syracuseStep 3120131 = 4680197) B4680197
theorem B2080087 : Blo 2079435 2080087 := bstep (se 1 (by rfl) ⟨1560065, by rfl⟩ : syracuseStep 2080087 = 3120131) B3120131
theorem B3948925 : Blo 2079435 3948925 := bbase (se 3 (by rfl) ⟨740423, by rfl⟩ : syracuseStep 3948925 = 1480847) (by norm_num)
theorem B5265233 : Blo 2079435 5265233 := bstep (se 2 (by rfl) ⟨1974462, by rfl⟩ : syracuseStep 5265233 = 3948925) B3948925
theorem B3510155 : Blo 2079435 3510155 := bstep (se 1 (by rfl) ⟨2632616, by rfl⟩ : syracuseStep 3510155 = 5265233) B5265233
theorem B2340103 : Blo 2079435 2340103 := bstep (se 1 (by rfl) ⟨1755077, by rfl⟩ : syracuseStep 2340103 = 3510155) B3510155
theorem B3120137 : Blo 2079435 3120137 := bstep (se 2 (by rfl) ⟨1170051, by rfl⟩ : syracuseStep 3120137 = 2340103) B2340103
theorem B2080091 : Blo 2079435 2080091 := bstep (se 1 (by rfl) ⟨1560068, by rfl⟩ : syracuseStep 2080091 = 3120137) B3120137
theorem B10530485 : Blo 2079435 10530485 := bbase (se 5 (by rfl) ⟨493616, by rfl⟩ : syracuseStep 10530485 = 987233) (by norm_num)
theorem B7020323 : Blo 2079435 7020323 := bstep (se 1 (by rfl) ⟨5265242, by rfl⟩ : syracuseStep 7020323 = 10530485) B10530485
theorem B4680215 : Blo 2079435 4680215 := bstep (se 1 (by rfl) ⟨3510161, by rfl⟩ : syracuseStep 4680215 = 7020323) B7020323
theorem B3120143 : Blo 2079435 3120143 := bstep (se 1 (by rfl) ⟨2340107, by rfl⟩ : syracuseStep 3120143 = 4680215) B4680215
theorem B2080095 : Blo 2079435 2080095 := bstep (se 1 (by rfl) ⟨1560071, by rfl⟩ : syracuseStep 2080095 = 3120143) B3120143
theorem B3120149 : Blo 2079435 3120149 := bbase (se 6 (by rfl) ⟨73128, by rfl⟩ : syracuseStep 3120149 = 146257) (by norm_num)
theorem B2080099 : Blo 2079435 2080099 := bstep (se 1 (by rfl) ⟨1560074, by rfl⟩ : syracuseStep 2080099 = 3120149) B3120149
theorem B16229749 : Blo 2079435 16229749 := bbase (se 5 (by rfl) ⟨760769, by rfl⟩ : syracuseStep 16229749 = 1521539) (by norm_num)
theorem B21639665 : Blo 2079435 21639665 := bstep (se 2 (by rfl) ⟨8114874, by rfl⟩ : syracuseStep 21639665 = 16229749) B16229749
theorem B14426443 : Blo 2079435 14426443 := bstep (se 1 (by rfl) ⟨10819832, by rfl⟩ : syracuseStep 14426443 = 21639665) B21639665
theorem B76941029 : Blo 2079435 76941029 := bstep (se 4 (by rfl) ⟨7213221, by rfl⟩ : syracuseStep 76941029 = 14426443) B14426443
theorem B51294019 : Blo 2079435 51294019 := bstep (se 1 (by rfl) ⟨38470514, by rfl⟩ : syracuseStep 51294019 = 76941029) B76941029
theorem B68392025 : Blo 2079435 68392025 := bstep (se 2 (by rfl) ⟨25647009, by rfl⟩ : syracuseStep 68392025 = 51294019) B51294019
theorem B45594683 : Blo 2079435 45594683 := bstep (se 1 (by rfl) ⟨34196012, by rfl⟩ : syracuseStep 45594683 = 68392025) B68392025
theorem B30396455 : Blo 2079435 30396455 := bstep (se 1 (by rfl) ⟨22797341, by rfl⟩ : syracuseStep 30396455 = 45594683) B45594683
theorem B20264303 : Blo 2079435 20264303 := bstep (se 1 (by rfl) ⟨15198227, by rfl⟩ : syracuseStep 20264303 = 30396455) B30396455
theorem B13509535 : Blo 2079435 13509535 := bstep (se 1 (by rfl) ⟨10132151, by rfl⟩ : syracuseStep 13509535 = 20264303) B20264303
theorem B18012713 : Blo 2079435 18012713 := bstep (se 2 (by rfl) ⟨6754767, by rfl⟩ : syracuseStep 18012713 = 13509535) B13509535
theorem B48033901 : Blo 2079435 48033901 := bstep (se 3 (by rfl) ⟨9006356, by rfl⟩ : syracuseStep 48033901 = 18012713) B18012713
theorem B64045201 : Blo 2079435 64045201 := bstep (se 2 (by rfl) ⟨24016950, by rfl⟩ : syracuseStep 64045201 = 48033901) B48033901
theorem B85393601 : Blo 2079435 85393601 := bstep (se 2 (by rfl) ⟨32022600, by rfl⟩ : syracuseStep 85393601 = 64045201) B64045201
theorem B56929067 : Blo 2079435 56929067 := bstep (se 1 (by rfl) ⟨42696800, by rfl⟩ : syracuseStep 56929067 = 85393601) B85393601
theorem B37952711 : Blo 2079435 37952711 := bstep (se 1 (by rfl) ⟨28464533, by rfl⟩ : syracuseStep 37952711 = 56929067) B56929067
theorem B25301807 : Blo 2079435 25301807 := bstep (se 1 (by rfl) ⟨18976355, by rfl⟩ : syracuseStep 25301807 = 37952711) B37952711
theorem B16867871 : Blo 2079435 16867871 := bstep (se 1 (by rfl) ⟨12650903, by rfl⟩ : syracuseStep 16867871 = 25301807) B25301807
theorem B11245247 : Blo 2079435 11245247 := bstep (se 1 (by rfl) ⟨8433935, by rfl⟩ : syracuseStep 11245247 = 16867871) B16867871
theorem B7496831 : Blo 2079435 7496831 := bstep (se 1 (by rfl) ⟨5622623, by rfl⟩ : syracuseStep 7496831 = 11245247) B11245247
theorem B19991549 : Blo 2079435 19991549 := bstep (se 3 (by rfl) ⟨3748415, by rfl⟩ : syracuseStep 19991549 = 7496831) B7496831
theorem B13327699 : Blo 2079435 13327699 := bstep (se 1 (by rfl) ⟨9995774, by rfl⟩ : syracuseStep 13327699 = 19991549) B19991549
theorem B17770265 : Blo 2079435 17770265 := bstep (se 2 (by rfl) ⟨6663849, by rfl⟩ : syracuseStep 17770265 = 13327699) B13327699
theorem B11846843 : Blo 2079435 11846843 := bstep (se 1 (by rfl) ⟨8885132, by rfl⟩ : syracuseStep 11846843 = 17770265) B17770265
theorem B7897895 : Blo 2079435 7897895 := bstep (se 1 (by rfl) ⟨5923421, by rfl⟩ : syracuseStep 7897895 = 11846843) B11846843
theorem B5265263 : Blo 2079435 5265263 := bstep (se 1 (by rfl) ⟨3948947, by rfl⟩ : syracuseStep 5265263 = 7897895) B7897895
theorem B3510175 : Blo 2079435 3510175 := bstep (se 1 (by rfl) ⟨2632631, by rfl⟩ : syracuseStep 3510175 = 5265263) B5265263
theorem B4680233 : Blo 2079435 4680233 := bstep (se 2 (by rfl) ⟨1755087, by rfl⟩ : syracuseStep 4680233 = 3510175) B3510175
theorem B3120155 : Blo 2079435 3120155 := bstep (se 1 (by rfl) ⟨2340116, by rfl⟩ : syracuseStep 3120155 = 4680233) B4680233
theorem B2080103 : Blo 2079435 2080103 := bstep (se 1 (by rfl) ⟨1560077, by rfl⟩ : syracuseStep 2080103 = 3120155) B3120155
theorem B2340121 : Blo 2079435 2340121 := bbase (se 2 (by rfl) ⟨877545, by rfl⟩ : syracuseStep 2340121 = 1755091) (by norm_num)
theorem B3120161 : Blo 2079435 3120161 := bstep (se 2 (by rfl) ⟨1170060, by rfl⟩ : syracuseStep 3120161 = 2340121) B2340121
theorem B2080107 : Blo 2079435 2080107 := bstep (se 1 (by rfl) ⟨1560080, by rfl⟩ : syracuseStep 2080107 = 3120161) B3120161
theorem B7897925 : Blo 2079435 7897925 := bbase (se 4 (by rfl) ⟨740430, by rfl⟩ : syracuseStep 7897925 = 1480861) (by norm_num)
theorem B5265283 : Blo 2079435 5265283 := bstep (se 1 (by rfl) ⟨3948962, by rfl⟩ : syracuseStep 5265283 = 7897925) B7897925
theorem B7020377 : Blo 2079435 7020377 := bstep (se 2 (by rfl) ⟨2632641, by rfl⟩ : syracuseStep 7020377 = 5265283) B5265283
theorem B4680251 : Blo 2079435 4680251 := bstep (se 1 (by rfl) ⟨3510188, by rfl⟩ : syracuseStep 4680251 = 7020377) B7020377
theorem B3120167 : Blo 2079435 3120167 := bstep (se 1 (by rfl) ⟨2340125, by rfl⟩ : syracuseStep 3120167 = 4680251) B4680251
theorem B2080111 : Blo 2079435 2080111 := bstep (se 1 (by rfl) ⟨1560083, by rfl⟩ : syracuseStep 2080111 = 3120167) B3120167
theorem B3120173 : Blo 2079435 3120173 := bbase (se 3 (by rfl) ⟨585032, by rfl⟩ : syracuseStep 3120173 = 1170065) (by norm_num)
theorem B2080115 : Blo 2079435 2080115 := bstep (se 1 (by rfl) ⟨1560086, by rfl⟩ : syracuseStep 2080115 = 3120173) B3120173
theorem B4680269 : Blo 2079435 4680269 := bbase (se 3 (by rfl) ⟨877550, by rfl⟩ : syracuseStep 4680269 = 1755101) (by norm_num)
theorem B3120179 : Blo 2079435 3120179 := bstep (se 1 (by rfl) ⟨2340134, by rfl⟩ : syracuseStep 3120179 = 4680269) B4680269
theorem B2080119 : Blo 2079435 2080119 := bstep (se 1 (by rfl) ⟨1560089, by rfl⟩ : syracuseStep 2080119 = 3120179) B3120179
theorem B2632657 : Blo 2079435 2632657 := bbase (se 2 (by rfl) ⟨987246, by rfl⟩ : syracuseStep 2632657 = 1974493) (by norm_num)
theorem B3510209 : Blo 2079435 3510209 := bstep (se 2 (by rfl) ⟨1316328, by rfl⟩ : syracuseStep 3510209 = 2632657) B2632657
theorem B2340139 : Blo 2079435 2340139 := bstep (se 1 (by rfl) ⟨1755104, by rfl⟩ : syracuseStep 2340139 = 3510209) B3510209
theorem B3120185 : Blo 2079435 3120185 := bstep (se 2 (by rfl) ⟨1170069, by rfl⟩ : syracuseStep 3120185 = 2340139) B2340139
theorem B2080123 : Blo 2079435 2080123 := bstep (se 1 (by rfl) ⟨1560092, by rfl⟩ : syracuseStep 2080123 = 3120185) B3120185
theorem B3558109 : Blo 2079435 3558109 := bbase (se 3 (by rfl) ⟨667145, by rfl⟩ : syracuseStep 3558109 = 1334291) (by norm_num)
theorem B4744145 : Blo 2079435 4744145 := bstep (se 2 (by rfl) ⟨1779054, by rfl⟩ : syracuseStep 4744145 = 3558109) B3558109
theorem B3162763 : Blo 2079435 3162763 := bstep (se 1 (by rfl) ⟨2372072, by rfl⟩ : syracuseStep 3162763 = 4744145) B4744145
theorem B4217017 : Blo 2079435 4217017 := bstep (se 2 (by rfl) ⟨1581381, by rfl⟩ : syracuseStep 4217017 = 3162763) B3162763
theorem B5622689 : Blo 2079435 5622689 := bstep (se 2 (by rfl) ⟨2108508, by rfl⟩ : syracuseStep 5622689 = 4217017) B4217017
theorem B3748459 : Blo 2079435 3748459 := bstep (se 1 (by rfl) ⟨2811344, by rfl⟩ : syracuseStep 3748459 = 5622689) B5622689
theorem B4997945 : Blo 2079435 4997945 := bstep (se 2 (by rfl) ⟨1874229, by rfl⟩ : syracuseStep 4997945 = 3748459) B3748459
theorem B3331963 : Blo 2079435 3331963 := bstep (se 1 (by rfl) ⟨2498972, by rfl⟩ : syracuseStep 3331963 = 4997945) B4997945
theorem B4442617 : Blo 2079435 4442617 := bstep (se 2 (by rfl) ⟨1665981, by rfl⟩ : syracuseStep 4442617 = 3331963) B3331963
theorem B23693957 : Blo 2079435 23693957 := bstep (se 4 (by rfl) ⟨2221308, by rfl⟩ : syracuseStep 23693957 = 4442617) B4442617
theorem B15795971 : Blo 2079435 15795971 := bstep (se 1 (by rfl) ⟨11846978, by rfl⟩ : syracuseStep 15795971 = 23693957) B23693957
theorem B10530647 : Blo 2079435 10530647 := bstep (se 1 (by rfl) ⟨7897985, by rfl⟩ : syracuseStep 10530647 = 15795971) B15795971
theorem B7020431 : Blo 2079435 7020431 := bstep (se 1 (by rfl) ⟨5265323, by rfl⟩ : syracuseStep 7020431 = 10530647) B10530647
theorem B4680287 : Blo 2079435 4680287 := bstep (se 1 (by rfl) ⟨3510215, by rfl⟩ : syracuseStep 4680287 = 7020431) B7020431
theorem B3120191 : Blo 2079435 3120191 := bstep (se 1 (by rfl) ⟨2340143, by rfl⟩ : syracuseStep 3120191 = 4680287) B4680287
theorem B2080127 : Blo 2079435 2080127 := bstep (se 1 (by rfl) ⟨1560095, by rfl⟩ : syracuseStep 2080127 = 3120191) B3120191
theorem B3120197 : Blo 2079435 3120197 := bbase (se 4 (by rfl) ⟨292518, by rfl⟩ : syracuseStep 3120197 = 585037) (by norm_num)
theorem B2080131 : Blo 2079435 2080131 := bstep (se 1 (by rfl) ⟨1560098, by rfl⟩ : syracuseStep 2080131 = 3120197) B3120197
theorem B3510229 : Blo 2079435 3510229 := bbase (se 7 (by rfl) ⟨41135, by rfl⟩ : syracuseStep 3510229 = 82271) (by norm_num)
theorem B4680305 : Blo 2079435 4680305 := bstep (se 2 (by rfl) ⟨1755114, by rfl⟩ : syracuseStep 4680305 = 3510229) B3510229
theorem B3120203 : Blo 2079435 3120203 := bstep (se 1 (by rfl) ⟨2340152, by rfl⟩ : syracuseStep 3120203 = 4680305) B4680305
theorem B2080135 : Blo 2079435 2080135 := bstep (se 1 (by rfl) ⟨1560101, by rfl⟩ : syracuseStep 2080135 = 3120203) B3120203
theorem B2340157 : Blo 2079435 2340157 := bbase (se 3 (by rfl) ⟨438779, by rfl⟩ : syracuseStep 2340157 = 877559) (by norm_num)
theorem B3120209 : Blo 2079435 3120209 := bstep (se 2 (by rfl) ⟨1170078, by rfl⟩ : syracuseStep 3120209 = 2340157) B2340157
theorem B2080139 : Blo 2079435 2080139 := bstep (se 1 (by rfl) ⟨1560104, by rfl⟩ : syracuseStep 2080139 = 3120209) B3120209
theorem B7020485 : Blo 2079435 7020485 := bbase (se 4 (by rfl) ⟨658170, by rfl⟩ : syracuseStep 7020485 = 1316341) (by norm_num)
theorem B4680323 : Blo 2079435 4680323 := bstep (se 1 (by rfl) ⟨3510242, by rfl⟩ : syracuseStep 4680323 = 7020485) B7020485
theorem B3120215 : Blo 2079435 3120215 := bstep (se 1 (by rfl) ⟨2340161, by rfl⟩ : syracuseStep 3120215 = 4680323) B4680323
theorem B2080143 : Blo 2079435 2080143 := bstep (se 1 (by rfl) ⟨1560107, by rfl⟩ : syracuseStep 2080143 = 3120215) B3120215
theorem B3120221 : Blo 2079435 3120221 := bbase (se 3 (by rfl) ⟨585041, by rfl⟩ : syracuseStep 3120221 = 1170083) (by norm_num)
theorem B2080147 : Blo 2079435 2080147 := bstep (se 1 (by rfl) ⟨1560110, by rfl⟩ : syracuseStep 2080147 = 3120221) B3120221
theorem B4680341 : Blo 2079435 4680341 := bbase (se 6 (by rfl) ⟨109695, by rfl⟩ : syracuseStep 4680341 = 219391) (by norm_num)
theorem B3120227 : Blo 2079435 3120227 := bstep (se 1 (by rfl) ⟨2340170, by rfl⟩ : syracuseStep 3120227 = 4680341) B4680341
theorem B2080151 : Blo 2079435 2080151 := bstep (se 1 (by rfl) ⟨1560113, by rfl⟩ : syracuseStep 2080151 = 3120227) B3120227
theorem B2404469 : Blo 2079435 2404469 := bbase (se 5 (by rfl) ⟨112709, by rfl⟩ : syracuseStep 2404469 = 225419) (by norm_num)
theorem B6411917 : Blo 2079435 6411917 := bstep (se 3 (by rfl) ⟨1202234, by rfl⟩ : syracuseStep 6411917 = 2404469) B2404469
theorem B17098445 : Blo 2079435 17098445 := bstep (se 3 (by rfl) ⟨3205958, by rfl⟩ : syracuseStep 17098445 = 6411917) B6411917
theorem B11398963 : Blo 2079435 11398963 := bstep (se 1 (by rfl) ⟨8549222, by rfl⟩ : syracuseStep 11398963 = 17098445) B17098445
theorem B15198617 : Blo 2079435 15198617 := bstep (se 2 (by rfl) ⟨5699481, by rfl⟩ : syracuseStep 15198617 = 11398963) B11398963
theorem B40529645 : Blo 2079435 40529645 := bstep (se 3 (by rfl) ⟨7599308, by rfl⟩ : syracuseStep 40529645 = 15198617) B15198617
theorem B27019763 : Blo 2079435 27019763 := bstep (se 1 (by rfl) ⟨20264822, by rfl⟩ : syracuseStep 27019763 = 40529645) B40529645
theorem B18013175 : Blo 2079435 18013175 := bstep (se 1 (by rfl) ⟨13509881, by rfl⟩ : syracuseStep 18013175 = 27019763) B27019763
theorem B12008783 : Blo 2079435 12008783 := bstep (se 1 (by rfl) ⟨9006587, by rfl⟩ : syracuseStep 12008783 = 18013175) B18013175
theorem B32023421 : Blo 2079435 32023421 := bstep (se 3 (by rfl) ⟨6004391, by rfl⟩ : syracuseStep 32023421 = 12008783) B12008783
theorem B21348947 : Blo 2079435 21348947 := bstep (se 1 (by rfl) ⟨16011710, by rfl⟩ : syracuseStep 21348947 = 32023421) B32023421
theorem B14232631 : Blo 2079435 14232631 := bstep (se 1 (by rfl) ⟨10674473, by rfl⟩ : syracuseStep 14232631 = 21348947) B21348947
theorem B18976841 : Blo 2079435 18976841 := bstep (se 2 (by rfl) ⟨7116315, by rfl⟩ : syracuseStep 18976841 = 14232631) B14232631
theorem B12651227 : Blo 2079435 12651227 := bstep (se 1 (by rfl) ⟨9488420, by rfl⟩ : syracuseStep 12651227 = 18976841) B18976841
theorem B8434151 : Blo 2079435 8434151 := bstep (se 1 (by rfl) ⟨6325613, by rfl⟩ : syracuseStep 8434151 = 12651227) B12651227
theorem B5622767 : Blo 2079435 5622767 := bstep (se 1 (by rfl) ⟨4217075, by rfl⟩ : syracuseStep 5622767 = 8434151) B8434151
theorem B3748511 : Blo 2079435 3748511 := bstep (se 1 (by rfl) ⟨2811383, by rfl⟩ : syracuseStep 3748511 = 5622767) B5622767
theorem B2499007 : Blo 2079435 2499007 := bstep (se 1 (by rfl) ⟨1874255, by rfl⟩ : syracuseStep 2499007 = 3748511) B3748511
theorem B3332009 : Blo 2079435 3332009 := bstep (se 2 (by rfl) ⟨1249503, by rfl⟩ : syracuseStep 3332009 = 2499007) B2499007
theorem B2221339 : Blo 2079435 2221339 := bstep (se 1 (by rfl) ⟨1666004, by rfl⟩ : syracuseStep 2221339 = 3332009) B3332009
theorem B2961785 : Blo 2079435 2961785 := bstep (se 2 (by rfl) ⟨1110669, by rfl⟩ : syracuseStep 2961785 = 2221339) B2221339
theorem B7898093 : Blo 2079435 7898093 := bstep (se 3 (by rfl) ⟨1480892, by rfl⟩ : syracuseStep 7898093 = 2961785) B2961785
theorem B5265395 : Blo 2079435 5265395 := bstep (se 1 (by rfl) ⟨3949046, by rfl⟩ : syracuseStep 5265395 = 7898093) B7898093
theorem B3510263 : Blo 2079435 3510263 := bstep (se 1 (by rfl) ⟨2632697, by rfl⟩ : syracuseStep 3510263 = 5265395) B5265395
theorem B2340175 : Blo 2079435 2340175 := bstep (se 1 (by rfl) ⟨1755131, by rfl⟩ : syracuseStep 2340175 = 3510263) B3510263
theorem B3120233 : Blo 2079435 3120233 := bstep (se 2 (by rfl) ⟨1170087, by rfl⟩ : syracuseStep 3120233 = 2340175) B2340175
theorem B2080155 : Blo 2079435 2080155 := bstep (se 1 (by rfl) ⟨1560116, by rfl⟩ : syracuseStep 2080155 = 3120233) B3120233
theorem B5337245 : Blo 2079435 5337245 := bbase (se 3 (by rfl) ⟨1000733, by rfl⟩ : syracuseStep 5337245 = 2001467) (by norm_num)
theorem B3558163 : Blo 2079435 3558163 := bstep (se 1 (by rfl) ⟨2668622, by rfl⟩ : syracuseStep 3558163 = 5337245) B5337245
theorem B4744217 : Blo 2079435 4744217 := bstep (se 2 (by rfl) ⟨1779081, by rfl⟩ : syracuseStep 4744217 = 3558163) B3558163
theorem B3162811 : Blo 2079435 3162811 := bstep (se 1 (by rfl) ⟨2372108, by rfl⟩ : syracuseStep 3162811 = 4744217) B4744217
theorem B4217081 : Blo 2079435 4217081 := bstep (se 2 (by rfl) ⟨1581405, by rfl⟩ : syracuseStep 4217081 = 3162811) B3162811
theorem B11245549 : Blo 2079435 11245549 := bstep (se 3 (by rfl) ⟨2108540, by rfl⟩ : syracuseStep 11245549 = 4217081) B4217081
theorem B14994065 : Blo 2079435 14994065 := bstep (se 2 (by rfl) ⟨5622774, by rfl⟩ : syracuseStep 14994065 = 11245549) B11245549
theorem B9996043 : Blo 2079435 9996043 := bstep (se 1 (by rfl) ⟨7497032, by rfl⟩ : syracuseStep 9996043 = 14994065) B14994065
theorem B13328057 : Blo 2079435 13328057 := bstep (se 2 (by rfl) ⟨4998021, by rfl⟩ : syracuseStep 13328057 = 9996043) B9996043
theorem B8885371 : Blo 2079435 8885371 := bstep (se 1 (by rfl) ⟨6664028, by rfl⟩ : syracuseStep 8885371 = 13328057) B13328057
theorem B11847161 : Blo 2079435 11847161 := bstep (se 2 (by rfl) ⟨4442685, by rfl⟩ : syracuseStep 11847161 = 8885371) B8885371
theorem B7898107 : Blo 2079435 7898107 := bstep (se 1 (by rfl) ⟨5923580, by rfl⟩ : syracuseStep 7898107 = 11847161) B11847161
theorem B10530809 : Blo 2079435 10530809 := bstep (se 2 (by rfl) ⟨3949053, by rfl⟩ : syracuseStep 10530809 = 7898107) B7898107
theorem B7020539 : Blo 2079435 7020539 := bstep (se 1 (by rfl) ⟨5265404, by rfl⟩ : syracuseStep 7020539 = 10530809) B10530809
theorem B4680359 : Blo 2079435 4680359 := bstep (se 1 (by rfl) ⟨3510269, by rfl⟩ : syracuseStep 4680359 = 7020539) B7020539
theorem B3120239 : Blo 2079435 3120239 := bstep (se 1 (by rfl) ⟨2340179, by rfl⟩ : syracuseStep 3120239 = 4680359) B4680359
theorem B2080159 : Blo 2079435 2080159 := bstep (se 1 (by rfl) ⟨1560119, by rfl⟩ : syracuseStep 2080159 = 3120239) B3120239
theorem B3120245 : Blo 2079435 3120245 := bbase (se 5 (by rfl) ⟨146261, by rfl⟩ : syracuseStep 3120245 = 292523) (by norm_num)
theorem B2080163 : Blo 2079435 2080163 := bstep (se 1 (by rfl) ⟨1560122, by rfl⟩ : syracuseStep 2080163 = 3120245) B3120245
theorem B3949069 : Blo 2079435 3949069 := bbase (se 3 (by rfl) ⟨740450, by rfl⟩ : syracuseStep 3949069 = 1480901) (by norm_num)
theorem B5265425 : Blo 2079435 5265425 := bstep (se 2 (by rfl) ⟨1974534, by rfl⟩ : syracuseStep 5265425 = 3949069) B3949069
theorem B3510283 : Blo 2079435 3510283 := bstep (se 1 (by rfl) ⟨2632712, by rfl⟩ : syracuseStep 3510283 = 5265425) B5265425
theorem B4680377 : Blo 2079435 4680377 := bstep (se 2 (by rfl) ⟨1755141, by rfl⟩ : syracuseStep 4680377 = 3510283) B3510283
theorem B3120251 : Blo 2079435 3120251 := bstep (se 1 (by rfl) ⟨2340188, by rfl⟩ : syracuseStep 3120251 = 4680377) B4680377
theorem B2080167 : Blo 2079435 2080167 := bstep (se 1 (by rfl) ⟨1560125, by rfl⟩ : syracuseStep 2080167 = 3120251) B3120251
theorem B2340193 : Blo 2079435 2340193 := bbase (se 2 (by rfl) ⟨877572, by rfl⟩ : syracuseStep 2340193 = 1755145) (by norm_num)
theorem B3120257 : Blo 2079435 3120257 := bstep (se 2 (by rfl) ⟨1170096, by rfl⟩ : syracuseStep 3120257 = 2340193) B2340193
theorem B2080171 : Blo 2079435 2080171 := bstep (se 1 (by rfl) ⟨1560128, by rfl⟩ : syracuseStep 2080171 = 3120257) B3120257
theorem B5265445 : Blo 2079435 5265445 := bbase (se 4 (by rfl) ⟨493635, by rfl⟩ : syracuseStep 5265445 = 987271) (by norm_num)
theorem B7020593 : Blo 2079435 7020593 := bstep (se 2 (by rfl) ⟨2632722, by rfl⟩ : syracuseStep 7020593 = 5265445) B5265445
theorem B4680395 : Blo 2079435 4680395 := bstep (se 1 (by rfl) ⟨3510296, by rfl⟩ : syracuseStep 4680395 = 7020593) B7020593
theorem B3120263 : Blo 2079435 3120263 := bstep (se 1 (by rfl) ⟨2340197, by rfl⟩ : syracuseStep 3120263 = 4680395) B4680395
theorem B2080175 : Blo 2079435 2080175 := bstep (se 1 (by rfl) ⟨1560131, by rfl⟩ : syracuseStep 2080175 = 3120263) B3120263
theorem B3120269 : Blo 2079435 3120269 := bbase (se 3 (by rfl) ⟨585050, by rfl⟩ : syracuseStep 3120269 = 1170101) (by norm_num)
theorem B2080179 : Blo 2079435 2080179 := bstep (se 1 (by rfl) ⟨1560134, by rfl⟩ : syracuseStep 2080179 = 3120269) B3120269
theorem B4680413 : Blo 2079435 4680413 := bbase (se 3 (by rfl) ⟨877577, by rfl⟩ : syracuseStep 4680413 = 1755155) (by norm_num)
theorem B3120275 : Blo 2079435 3120275 := bstep (se 1 (by rfl) ⟨2340206, by rfl⟩ : syracuseStep 3120275 = 4680413) B4680413
theorem B2080183 : Blo 2079435 2080183 := bstep (se 1 (by rfl) ⟨1560137, by rfl⟩ : syracuseStep 2080183 = 3120275) B3120275
theorem B3510317 : Blo 2079435 3510317 := bbase (se 3 (by rfl) ⟨658184, by rfl⟩ : syracuseStep 3510317 = 1316369) (by norm_num)
theorem B2340211 : Blo 2079435 2340211 := bstep (se 1 (by rfl) ⟨1755158, by rfl⟩ : syracuseStep 2340211 = 3510317) B3510317
theorem B3120281 : Blo 2079435 3120281 := bstep (se 2 (by rfl) ⟨1170105, by rfl⟩ : syracuseStep 3120281 = 2340211) B2340211
theorem B2080187 : Blo 2079435 2080187 := bstep (se 1 (by rfl) ⟨1560140, by rfl⟩ : syracuseStep 2080187 = 3120281) B3120281
theorem B2251685 : Blo 2079435 2251685 := bbase (se 4 (by rfl) ⟨211095, by rfl⟩ : syracuseStep 2251685 = 422191) (by norm_num)
theorem B6004493 : Blo 2079435 6004493 := bstep (se 3 (by rfl) ⟨1125842, by rfl⟩ : syracuseStep 6004493 = 2251685) B2251685
theorem B4002995 : Blo 2079435 4002995 := bstep (se 1 (by rfl) ⟨3002246, by rfl⟩ : syracuseStep 4002995 = 6004493) B6004493
theorem B2668663 : Blo 2079435 2668663 := bstep (se 1 (by rfl) ⟨2001497, by rfl⟩ : syracuseStep 2668663 = 4002995) B4002995
theorem B3558217 : Blo 2079435 3558217 := bstep (se 2 (by rfl) ⟨1334331, by rfl⟩ : syracuseStep 3558217 = 2668663) B2668663
theorem B4744289 : Blo 2079435 4744289 := bstep (se 2 (by rfl) ⟨1779108, by rfl⟩ : syracuseStep 4744289 = 3558217) B3558217
theorem B12651437 : Blo 2079435 12651437 := bstep (se 3 (by rfl) ⟨2372144, by rfl⟩ : syracuseStep 12651437 = 4744289) B4744289
theorem B8434291 : Blo 2079435 8434291 := bstep (se 1 (by rfl) ⟨6325718, by rfl⟩ : syracuseStep 8434291 = 12651437) B12651437
theorem B11245721 : Blo 2079435 11245721 := bstep (se 2 (by rfl) ⟨4217145, by rfl⟩ : syracuseStep 11245721 = 8434291) B8434291
theorem B29988589 : Blo 2079435 29988589 := bstep (se 3 (by rfl) ⟨5622860, by rfl⟩ : syracuseStep 29988589 = 11245721) B11245721
theorem B39984785 : Blo 2079435 39984785 := bstep (se 2 (by rfl) ⟨14994294, by rfl⟩ : syracuseStep 39984785 = 29988589) B29988589
theorem B26656523 : Blo 2079435 26656523 := bstep (se 1 (by rfl) ⟨19992392, by rfl⟩ : syracuseStep 26656523 = 39984785) B39984785
theorem B17771015 : Blo 2079435 17771015 := bstep (se 1 (by rfl) ⟨13328261, by rfl⟩ : syracuseStep 17771015 = 26656523) B26656523
theorem B11847343 : Blo 2079435 11847343 := bstep (se 1 (by rfl) ⟨8885507, by rfl⟩ : syracuseStep 11847343 = 17771015) B17771015
theorem B15796457 : Blo 2079435 15796457 := bstep (se 2 (by rfl) ⟨5923671, by rfl⟩ : syracuseStep 15796457 = 11847343) B11847343
theorem B10530971 : Blo 2079435 10530971 := bstep (se 1 (by rfl) ⟨7898228, by rfl⟩ : syracuseStep 10530971 = 15796457) B15796457
theorem B7020647 : Blo 2079435 7020647 := bstep (se 1 (by rfl) ⟨5265485, by rfl⟩ : syracuseStep 7020647 = 10530971) B10530971
theorem B4680431 : Blo 2079435 4680431 := bstep (se 1 (by rfl) ⟨3510323, by rfl⟩ : syracuseStep 4680431 = 7020647) B7020647
theorem B3120287 : Blo 2079435 3120287 := bstep (se 1 (by rfl) ⟨2340215, by rfl⟩ : syracuseStep 3120287 = 4680431) B4680431
theorem B2080191 : Blo 2079435 2080191 := bstep (se 1 (by rfl) ⟨1560143, by rfl⟩ : syracuseStep 2080191 = 3120287) B3120287
theorem B3120293 : Blo 2079435 3120293 := bbase (se 4 (by rfl) ⟨292527, by rfl⟩ : syracuseStep 3120293 = 585055) (by norm_num)
theorem B2080195 : Blo 2079435 2080195 := bstep (se 1 (by rfl) ⟨1560146, by rfl⟩ : syracuseStep 2080195 = 3120293) B3120293
theorem B2632753 : Blo 2079435 2632753 := bbase (se 2 (by rfl) ⟨987282, by rfl⟩ : syracuseStep 2632753 = 1974565) (by norm_num)
theorem B3510337 : Blo 2079435 3510337 := bstep (se 2 (by rfl) ⟨1316376, by rfl⟩ : syracuseStep 3510337 = 2632753) B2632753
theorem B4680449 : Blo 2079435 4680449 := bstep (se 2 (by rfl) ⟨1755168, by rfl⟩ : syracuseStep 4680449 = 3510337) B3510337
theorem B3120299 : Blo 2079435 3120299 := bstep (se 1 (by rfl) ⟨2340224, by rfl⟩ : syracuseStep 3120299 = 4680449) B4680449
theorem B2080199 : Blo 2079435 2080199 := bstep (se 1 (by rfl) ⟨1560149, by rfl⟩ : syracuseStep 2080199 = 3120299) B3120299
theorem B2340229 : Blo 2079435 2340229 := bbase (se 4 (by rfl) ⟨219396, by rfl⟩ : syracuseStep 2340229 = 438793) (by norm_num)
theorem B3120305 : Blo 2079435 3120305 := bstep (se 2 (by rfl) ⟨1170114, by rfl⟩ : syracuseStep 3120305 = 2340229) B2340229
theorem B2080203 : Blo 2079435 2080203 := bstep (se 1 (by rfl) ⟨1560152, by rfl⟩ : syracuseStep 2080203 = 3120305) B3120305
theorem B4442789 : Blo 2079435 4442789 := bbase (se 4 (by rfl) ⟨416511, by rfl⟩ : syracuseStep 4442789 = 833023) (by norm_num)
theorem B2961859 : Blo 2079435 2961859 := bstep (se 1 (by rfl) ⟨2221394, by rfl⟩ : syracuseStep 2961859 = 4442789) B4442789
theorem B3949145 : Blo 2079435 3949145 := bstep (se 2 (by rfl) ⟨1480929, by rfl⟩ : syracuseStep 3949145 = 2961859) B2961859
theorem B2632763 : Blo 2079435 2632763 := bstep (se 1 (by rfl) ⟨1974572, by rfl⟩ : syracuseStep 2632763 = 3949145) B3949145
theorem B7020701 : Blo 2079435 7020701 := bstep (se 3 (by rfl) ⟨1316381, by rfl⟩ : syracuseStep 7020701 = 2632763) B2632763
theorem B4680467 : Blo 2079435 4680467 := bstep (se 1 (by rfl) ⟨3510350, by rfl⟩ : syracuseStep 4680467 = 7020701) B7020701
theorem B3120311 : Blo 2079435 3120311 := bstep (se 1 (by rfl) ⟨2340233, by rfl⟩ : syracuseStep 3120311 = 4680467) B4680467
theorem B2080207 : Blo 2079435 2080207 := bstep (se 1 (by rfl) ⟨1560155, by rfl⟩ : syracuseStep 2080207 = 3120311) B3120311
theorem B3120317 : Blo 2079435 3120317 := bbase (se 3 (by rfl) ⟨585059, by rfl⟩ : syracuseStep 3120317 = 1170119) (by norm_num)
theorem B2080211 : Blo 2079435 2080211 := bstep (se 1 (by rfl) ⟨1560158, by rfl⟩ : syracuseStep 2080211 = 3120317) B3120317
theorem B4680485 : Blo 2079435 4680485 := bbase (se 4 (by rfl) ⟨438795, by rfl⟩ : syracuseStep 4680485 = 877591) (by norm_num)
theorem B3120323 : Blo 2079435 3120323 := bstep (se 1 (by rfl) ⟨2340242, by rfl⟩ : syracuseStep 3120323 = 4680485) B4680485
theorem B2080215 : Blo 2079435 2080215 := bstep (se 1 (by rfl) ⟨1560161, by rfl⟩ : syracuseStep 2080215 = 3120323) B3120323
theorem B5265557 : Blo 2079435 5265557 := bbase (se 6 (by rfl) ⟨123411, by rfl⟩ : syracuseStep 5265557 = 246823) (by norm_num)
theorem B3510371 : Blo 2079435 3510371 := bstep (se 1 (by rfl) ⟨2632778, by rfl⟩ : syracuseStep 3510371 = 5265557) B5265557
theorem B2340247 : Blo 2079435 2340247 := bstep (se 1 (by rfl) ⟨1755185, by rfl⟩ : syracuseStep 2340247 = 3510371) B3510371
theorem B3120329 : Blo 2079435 3120329 := bstep (se 2 (by rfl) ⟨1170123, by rfl⟩ : syracuseStep 3120329 = 2340247) B2340247
theorem B2080219 : Blo 2079435 2080219 := bstep (se 1 (by rfl) ⟨1560164, by rfl⟩ : syracuseStep 2080219 = 3120329) B3120329
theorem B3332117 : Blo 2079435 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B8885645 : Blo 2079435 8885645 := bstep (se 3 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 8885645 = 3332117) B3332117
theorem B5923763 : Blo 2079435 5923763 := bstep (se 1 (by rfl) ⟨4442822, by rfl⟩ : syracuseStep 5923763 = 8885645) B8885645
theorem B3949175 : Blo 2079435 3949175 := bstep (se 1 (by rfl) ⟨2961881, by rfl⟩ : syracuseStep 3949175 = 5923763) B5923763
theorem B10531133 : Blo 2079435 10531133 := bstep (se 3 (by rfl) ⟨1974587, by rfl⟩ : syracuseStep 10531133 = 3949175) B3949175
theorem B7020755 : Blo 2079435 7020755 := bstep (se 1 (by rfl) ⟨5265566, by rfl⟩ : syracuseStep 7020755 = 10531133) B10531133
theorem B4680503 : Blo 2079435 4680503 := bstep (se 1 (by rfl) ⟨3510377, by rfl⟩ : syracuseStep 4680503 = 7020755) B7020755
theorem B3120335 : Blo 2079435 3120335 := bstep (se 1 (by rfl) ⟨2340251, by rfl⟩ : syracuseStep 3120335 = 4680503) B4680503
theorem B2080223 : Blo 2079435 2080223 := bstep (se 1 (by rfl) ⟨1560167, by rfl⟩ : syracuseStep 2080223 = 3120335) B3120335
theorem B3120341 : Blo 2079435 3120341 := bbase (se 7 (by rfl) ⟨36566, by rfl⟩ : syracuseStep 3120341 = 73133) (by norm_num)
theorem B2080227 : Blo 2079435 2080227 := bstep (se 1 (by rfl) ⟨1560170, by rfl⟩ : syracuseStep 2080227 = 3120341) B3120341
theorem B2961893 : Blo 2079435 2961893 := bbase (se 4 (by rfl) ⟨277677, by rfl⟩ : syracuseStep 2961893 = 555355) (by norm_num)
theorem B7898381 : Blo 2079435 7898381 := bstep (se 3 (by rfl) ⟨1480946, by rfl⟩ : syracuseStep 7898381 = 2961893) B2961893
theorem B5265587 : Blo 2079435 5265587 := bstep (se 1 (by rfl) ⟨3949190, by rfl⟩ : syracuseStep 5265587 = 7898381) B7898381
theorem B3510391 : Blo 2079435 3510391 := bstep (se 1 (by rfl) ⟨2632793, by rfl⟩ : syracuseStep 3510391 = 5265587) B5265587
theorem B4680521 : Blo 2079435 4680521 := bstep (se 2 (by rfl) ⟨1755195, by rfl⟩ : syracuseStep 4680521 = 3510391) B3510391
theorem B3120347 : Blo 2079435 3120347 := bstep (se 1 (by rfl) ⟨2340260, by rfl⟩ : syracuseStep 3120347 = 4680521) B4680521
theorem B2080231 : Blo 2079435 2080231 := bstep (se 1 (by rfl) ⟨1560173, by rfl⟩ : syracuseStep 2080231 = 3120347) B3120347
theorem B2340265 : Blo 2079435 2340265 := bbase (se 2 (by rfl) ⟨877599, by rfl⟩ : syracuseStep 2340265 = 1755199) (by norm_num)
theorem B3120353 : Blo 2079435 3120353 := bstep (se 2 (by rfl) ⟨1170132, by rfl⟩ : syracuseStep 3120353 = 2340265) B2340265
theorem B2080235 : Blo 2079435 2080235 := bstep (se 1 (by rfl) ⟨1560176, by rfl⟩ : syracuseStep 2080235 = 3120353) B3120353
theorem B3748661 : Blo 2079435 3748661 := bbase (se 5 (by rfl) ⟨175718, by rfl⟩ : syracuseStep 3748661 = 351437) (by norm_num)
theorem B2499107 : Blo 2079435 2499107 := bstep (se 1 (by rfl) ⟨1874330, by rfl⟩ : syracuseStep 2499107 = 3748661) B3748661
theorem B6664285 : Blo 2079435 6664285 := bstep (se 3 (by rfl) ⟨1249553, by rfl⟩ : syracuseStep 6664285 = 2499107) B2499107
theorem B8885713 : Blo 2079435 8885713 := bstep (se 2 (by rfl) ⟨3332142, by rfl⟩ : syracuseStep 8885713 = 6664285) B6664285
theorem B11847617 : Blo 2079435 11847617 := bstep (se 2 (by rfl) ⟨4442856, by rfl⟩ : syracuseStep 11847617 = 8885713) B8885713
theorem B7898411 : Blo 2079435 7898411 := bstep (se 1 (by rfl) ⟨5923808, by rfl⟩ : syracuseStep 7898411 = 11847617) B11847617
theorem B5265607 : Blo 2079435 5265607 := bstep (se 1 (by rfl) ⟨3949205, by rfl⟩ : syracuseStep 5265607 = 7898411) B7898411
theorem B7020809 : Blo 2079435 7020809 := bstep (se 2 (by rfl) ⟨2632803, by rfl⟩ : syracuseStep 7020809 = 5265607) B5265607
theorem B4680539 : Blo 2079435 4680539 := bstep (se 1 (by rfl) ⟨3510404, by rfl⟩ : syracuseStep 4680539 = 7020809) B7020809
theorem B3120359 : Blo 2079435 3120359 := bstep (se 1 (by rfl) ⟨2340269, by rfl⟩ : syracuseStep 3120359 = 4680539) B4680539
theorem B2080239 : Blo 2079435 2080239 := bstep (se 1 (by rfl) ⟨1560179, by rfl⟩ : syracuseStep 2080239 = 3120359) B3120359
theorem B3120365 : Blo 2079435 3120365 := bbase (se 3 (by rfl) ⟨585068, by rfl⟩ : syracuseStep 3120365 = 1170137) (by norm_num)
theorem B2080243 : Blo 2079435 2080243 := bstep (se 1 (by rfl) ⟨1560182, by rfl⟩ : syracuseStep 2080243 = 3120365) B3120365
theorem B4680557 : Blo 2079435 4680557 := bbase (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) (by norm_num)
theorem B3120371 : Blo 2079435 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B2080247 : Blo 2079435 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B3949229 : Blo 2079435 3949229 := bbase (se 3 (by rfl) ⟨740480, by rfl⟩ : syracuseStep 3949229 = 1480961) (by norm_num)
theorem B2632819 : Blo 2079435 2632819 := bstep (se 1 (by rfl) ⟨1974614, by rfl⟩ : syracuseStep 2632819 = 3949229) B3949229
theorem B3510425 : Blo 2079435 3510425 := bstep (se 2 (by rfl) ⟨1316409, by rfl⟩ : syracuseStep 3510425 = 2632819) B2632819
theorem B2340283 : Blo 2079435 2340283 := bstep (se 1 (by rfl) ⟨1755212, by rfl⟩ : syracuseStep 2340283 = 3510425) B3510425
theorem B3120377 : Blo 2079435 3120377 := bstep (se 2 (by rfl) ⟨1170141, by rfl⟩ : syracuseStep 3120377 = 2340283) B2340283
theorem B2080251 : Blo 2079435 2080251 := bstep (se 1 (by rfl) ⟨1560188, by rfl⟩ : syracuseStep 2080251 = 3120377) B3120377
theorem B9488869 : Blo 2079435 9488869 := bbase (se 4 (by rfl) ⟨889581, by rfl⟩ : syracuseStep 9488869 = 1779163) (by norm_num)
theorem B50607301 : Blo 2079435 50607301 := bstep (se 4 (by rfl) ⟨4744434, by rfl⟩ : syracuseStep 50607301 = 9488869) B9488869
theorem B67476401 : Blo 2079435 67476401 := bstep (se 2 (by rfl) ⟨25303650, by rfl⟩ : syracuseStep 67476401 = 50607301) B50607301
theorem B44984267 : Blo 2079435 44984267 := bstep (se 1 (by rfl) ⟨33738200, by rfl⟩ : syracuseStep 44984267 = 67476401) B67476401
theorem B29989511 : Blo 2079435 29989511 := bstep (se 1 (by rfl) ⟨22492133, by rfl⟩ : syracuseStep 29989511 = 44984267) B44984267
theorem B19993007 : Blo 2079435 19993007 := bstep (se 1 (by rfl) ⟨14994755, by rfl⟩ : syracuseStep 19993007 = 29989511) B29989511
theorem B53314685 : Blo 2079435 53314685 := bstep (se 3 (by rfl) ⟨9996503, by rfl⟩ : syracuseStep 53314685 = 19993007) B19993007
theorem B35543123 : Blo 2079435 35543123 := bstep (se 1 (by rfl) ⟨26657342, by rfl⟩ : syracuseStep 35543123 = 53314685) B53314685
theorem B23695415 : Blo 2079435 23695415 := bstep (se 1 (by rfl) ⟨17771561, by rfl⟩ : syracuseStep 23695415 = 35543123) B35543123
theorem B15796943 : Blo 2079435 15796943 := bstep (se 1 (by rfl) ⟨11847707, by rfl⟩ : syracuseStep 15796943 = 23695415) B23695415
theorem B10531295 : Blo 2079435 10531295 := bstep (se 1 (by rfl) ⟨7898471, by rfl⟩ : syracuseStep 10531295 = 15796943) B15796943
theorem B7020863 : Blo 2079435 7020863 := bstep (se 1 (by rfl) ⟨5265647, by rfl⟩ : syracuseStep 7020863 = 10531295) B10531295
theorem B4680575 : Blo 2079435 4680575 := bstep (se 1 (by rfl) ⟨3510431, by rfl⟩ : syracuseStep 4680575 = 7020863) B7020863
theorem B3120383 : Blo 2079435 3120383 := bstep (se 1 (by rfl) ⟨2340287, by rfl⟩ : syracuseStep 3120383 = 4680575) B4680575
theorem B2080255 : Blo 2079435 2080255 := bstep (se 1 (by rfl) ⟨1560191, by rfl⟩ : syracuseStep 2080255 = 3120383) B3120383
theorem B3120389 : Blo 2079435 3120389 := bbase (se 4 (by rfl) ⟨292536, by rfl⟩ : syracuseStep 3120389 = 585073) (by norm_num)
theorem B2080259 : Blo 2079435 2080259 := bstep (se 1 (by rfl) ⟨1560194, by rfl⟩ : syracuseStep 2080259 = 3120389) B3120389
theorem B3510445 : Blo 2079435 3510445 := bbase (se 3 (by rfl) ⟨658208, by rfl⟩ : syracuseStep 3510445 = 1316417) (by norm_num)
theorem B4680593 : Blo 2079435 4680593 := bstep (se 2 (by rfl) ⟨1755222, by rfl⟩ : syracuseStep 4680593 = 3510445) B3510445
theorem B3120395 : Blo 2079435 3120395 := bstep (se 1 (by rfl) ⟨2340296, by rfl⟩ : syracuseStep 3120395 = 4680593) B4680593
theorem B2080263 : Blo 2079435 2080263 := bstep (se 1 (by rfl) ⟨1560197, by rfl⟩ : syracuseStep 2080263 = 3120395) B3120395
theorem B2340301 : Blo 2079435 2340301 := bbase (se 3 (by rfl) ⟨438806, by rfl⟩ : syracuseStep 2340301 = 877613) (by norm_num)
theorem B3120401 : Blo 2079435 3120401 := bstep (se 2 (by rfl) ⟨1170150, by rfl⟩ : syracuseStep 3120401 = 2340301) B2340301
theorem B2080267 : Blo 2079435 2080267 := bstep (se 1 (by rfl) ⟨1560200, by rfl⟩ : syracuseStep 2080267 = 3120401) B3120401
theorem B7020917 : Blo 2079435 7020917 := bbase (se 5 (by rfl) ⟨329105, by rfl⟩ : syracuseStep 7020917 = 658211) (by norm_num)
theorem B4680611 : Blo 2079435 4680611 := bstep (se 1 (by rfl) ⟨3510458, by rfl⟩ : syracuseStep 4680611 = 7020917) B7020917
theorem B3120407 : Blo 2079435 3120407 := bstep (se 1 (by rfl) ⟨2340305, by rfl⟩ : syracuseStep 3120407 = 4680611) B4680611
theorem B2080271 : Blo 2079435 2080271 := bstep (se 1 (by rfl) ⟨1560203, by rfl⟩ : syracuseStep 2080271 = 3120407) B3120407
theorem B3120413 : Blo 2079435 3120413 := bbase (se 3 (by rfl) ⟨585077, by rfl⟩ : syracuseStep 3120413 = 1170155) (by norm_num)
theorem B2080275 : Blo 2079435 2080275 := bstep (se 1 (by rfl) ⟨1560206, by rfl⟩ : syracuseStep 2080275 = 3120413) B3120413
theorem B4680629 : Blo 2079435 4680629 := bbase (se 5 (by rfl) ⟨219404, by rfl⟩ : syracuseStep 4680629 = 438809) (by norm_num)
theorem B3120419 : Blo 2079435 3120419 := bstep (se 1 (by rfl) ⟨2340314, by rfl⟩ : syracuseStep 3120419 = 4680629) B4680629
theorem B2080279 : Blo 2079435 2080279 := bstep (se 1 (by rfl) ⟨1560209, by rfl⟩ : syracuseStep 2080279 = 3120419) B3120419
theorem B13510709 : Blo 2079435 13510709 := bbase (se 5 (by rfl) ⟨633314, by rfl⟩ : syracuseStep 13510709 = 1266629) (by norm_num)
theorem B9007139 : Blo 2079435 9007139 := bstep (se 1 (by rfl) ⟨6755354, by rfl⟩ : syracuseStep 9007139 = 13510709) B13510709
theorem B24019037 : Blo 2079435 24019037 := bstep (se 3 (by rfl) ⟨4503569, by rfl⟩ : syracuseStep 24019037 = 9007139) B9007139
theorem B16012691 : Blo 2079435 16012691 := bstep (se 1 (by rfl) ⟨12009518, by rfl⟩ : syracuseStep 16012691 = 24019037) B24019037
theorem B10675127 : Blo 2079435 10675127 := bstep (se 1 (by rfl) ⟨8006345, by rfl⟩ : syracuseStep 10675127 = 16012691) B16012691
theorem B7116751 : Blo 2079435 7116751 := bstep (se 1 (by rfl) ⟨5337563, by rfl⟩ : syracuseStep 7116751 = 10675127) B10675127
theorem B9489001 : Blo 2079435 9489001 := bstep (se 2 (by rfl) ⟨3558375, by rfl⟩ : syracuseStep 9489001 = 7116751) B7116751
theorem B12652001 : Blo 2079435 12652001 := bstep (se 2 (by rfl) ⟨4744500, by rfl⟩ : syracuseStep 12652001 = 9489001) B9489001
theorem B8434667 : Blo 2079435 8434667 := bstep (se 1 (by rfl) ⟨6326000, by rfl⟩ : syracuseStep 8434667 = 12652001) B12652001
theorem B5623111 : Blo 2079435 5623111 := bstep (se 1 (by rfl) ⟨4217333, by rfl⟩ : syracuseStep 5623111 = 8434667) B8434667
theorem B7497481 : Blo 2079435 7497481 := bstep (se 2 (by rfl) ⟨2811555, by rfl⟩ : syracuseStep 7497481 = 5623111) B5623111
theorem B9996641 : Blo 2079435 9996641 := bstep (se 2 (by rfl) ⟨3748740, by rfl⟩ : syracuseStep 9996641 = 7497481) B7497481
theorem B6664427 : Blo 2079435 6664427 := bstep (se 1 (by rfl) ⟨4998320, by rfl⟩ : syracuseStep 6664427 = 9996641) B9996641
theorem B4442951 : Blo 2079435 4442951 := bstep (se 1 (by rfl) ⟨3332213, by rfl⟩ : syracuseStep 4442951 = 6664427) B6664427
theorem B11847869 : Blo 2079435 11847869 := bstep (se 3 (by rfl) ⟨2221475, by rfl⟩ : syracuseStep 11847869 = 4442951) B4442951
theorem B7898579 : Blo 2079435 7898579 := bstep (se 1 (by rfl) ⟨5923934, by rfl⟩ : syracuseStep 7898579 = 11847869) B11847869
theorem B5265719 : Blo 2079435 5265719 := bstep (se 1 (by rfl) ⟨3949289, by rfl⟩ : syracuseStep 5265719 = 7898579) B7898579
theorem B3510479 : Blo 2079435 3510479 := bstep (se 1 (by rfl) ⟨2632859, by rfl⟩ : syracuseStep 3510479 = 5265719) B5265719
theorem B2340319 : Blo 2079435 2340319 := bstep (se 1 (by rfl) ⟨1755239, by rfl⟩ : syracuseStep 2340319 = 3510479) B3510479
theorem B3120425 : Blo 2079435 3120425 := bstep (se 2 (by rfl) ⟨1170159, by rfl⟩ : syracuseStep 3120425 = 2340319) B2340319
theorem B2080283 : Blo 2079435 2080283 := bstep (se 1 (by rfl) ⟨1560212, by rfl⟩ : syracuseStep 2080283 = 3120425) B3120425
theorem B4217341 : Blo 2079435 4217341 := bbase (se 3 (by rfl) ⟨790751, by rfl⟩ : syracuseStep 4217341 = 1581503) (by norm_num)
theorem B5623121 : Blo 2079435 5623121 := bstep (se 2 (by rfl) ⟨2108670, by rfl⟩ : syracuseStep 5623121 = 4217341) B4217341
theorem B14994989 : Blo 2079435 14994989 := bstep (se 3 (by rfl) ⟨2811560, by rfl⟩ : syracuseStep 14994989 = 5623121) B5623121
theorem B9996659 : Blo 2079435 9996659 := bstep (se 1 (by rfl) ⟨7497494, by rfl⟩ : syracuseStep 9996659 = 14994989) B14994989
theorem B6664439 : Blo 2079435 6664439 := bstep (se 1 (by rfl) ⟨4998329, by rfl⟩ : syracuseStep 6664439 = 9996659) B9996659
theorem B4442959 : Blo 2079435 4442959 := bstep (se 1 (by rfl) ⟨3332219, by rfl⟩ : syracuseStep 4442959 = 6664439) B6664439
theorem B5923945 : Blo 2079435 5923945 := bstep (se 2 (by rfl) ⟨2221479, by rfl⟩ : syracuseStep 5923945 = 4442959) B4442959
theorem B7898593 : Blo 2079435 7898593 := bstep (se 2 (by rfl) ⟨2961972, by rfl⟩ : syracuseStep 7898593 = 5923945) B5923945
theorem B10531457 : Blo 2079435 10531457 := bstep (se 2 (by rfl) ⟨3949296, by rfl⟩ : syracuseStep 10531457 = 7898593) B7898593
theorem B7020971 : Blo 2079435 7020971 := bstep (se 1 (by rfl) ⟨5265728, by rfl⟩ : syracuseStep 7020971 = 10531457) B10531457
theorem B4680647 : Blo 2079435 4680647 := bstep (se 1 (by rfl) ⟨3510485, by rfl⟩ : syracuseStep 4680647 = 7020971) B7020971
theorem B3120431 : Blo 2079435 3120431 := bstep (se 1 (by rfl) ⟨2340323, by rfl⟩ : syracuseStep 3120431 = 4680647) B4680647
theorem B2080287 : Blo 2079435 2080287 := bstep (se 1 (by rfl) ⟨1560215, by rfl⟩ : syracuseStep 2080287 = 3120431) B3120431
theorem B3120437 : Blo 2079435 3120437 := bbase (se 5 (by rfl) ⟨146270, by rfl⟩ : syracuseStep 3120437 = 292541) (by norm_num)
theorem B2080291 : Blo 2079435 2080291 := bstep (se 1 (by rfl) ⟨1560218, by rfl⟩ : syracuseStep 2080291 = 3120437) B3120437
theorem B5265749 : Blo 2079435 5265749 := bbase (se 10 (by rfl) ⟨7713, by rfl⟩ : syracuseStep 5265749 = 15427) (by norm_num)
theorem B3510499 : Blo 2079435 3510499 := bstep (se 1 (by rfl) ⟨2632874, by rfl⟩ : syracuseStep 3510499 = 5265749) B5265749
theorem B4680665 : Blo 2079435 4680665 := bstep (se 2 (by rfl) ⟨1755249, by rfl⟩ : syracuseStep 4680665 = 3510499) B3510499
theorem B3120443 : Blo 2079435 3120443 := bstep (se 1 (by rfl) ⟨2340332, by rfl⟩ : syracuseStep 3120443 = 4680665) B4680665
theorem B2080295 : Blo 2079435 2080295 := bstep (se 1 (by rfl) ⟨1560221, by rfl⟩ : syracuseStep 2080295 = 3120443) B3120443
theorem B2340337 : Blo 2079435 2340337 := bbase (se 2 (by rfl) ⟨877626, by rfl⟩ : syracuseStep 2340337 = 1755253) (by norm_num)
theorem B3120449 : Blo 2079435 3120449 := bstep (se 2 (by rfl) ⟨1170168, by rfl⟩ : syracuseStep 3120449 = 2340337) B2340337
theorem B2080299 : Blo 2079435 2080299 := bstep (se 1 (by rfl) ⟨1560224, by rfl⟩ : syracuseStep 2080299 = 3120449) B3120449
theorem B13328981 : Blo 2079435 13328981 := bbase (se 8 (by rfl) ⟨78099, by rfl⟩ : syracuseStep 13328981 = 156199) (by norm_num)
theorem B8885987 : Blo 2079435 8885987 := bstep (se 1 (by rfl) ⟨6664490, by rfl⟩ : syracuseStep 8885987 = 13328981) B13328981
theorem B5923991 : Blo 2079435 5923991 := bstep (se 1 (by rfl) ⟨4442993, by rfl⟩ : syracuseStep 5923991 = 8885987) B8885987
theorem B3949327 : Blo 2079435 3949327 := bstep (se 1 (by rfl) ⟨2961995, by rfl⟩ : syracuseStep 3949327 = 5923991) B5923991
theorem B5265769 : Blo 2079435 5265769 := bstep (se 2 (by rfl) ⟨1974663, by rfl⟩ : syracuseStep 5265769 = 3949327) B3949327
theorem B7021025 : Blo 2079435 7021025 := bstep (se 2 (by rfl) ⟨2632884, by rfl⟩ : syracuseStep 7021025 = 5265769) B5265769
theorem B4680683 : Blo 2079435 4680683 := bstep (se 1 (by rfl) ⟨3510512, by rfl⟩ : syracuseStep 4680683 = 7021025) B7021025
theorem B3120455 : Blo 2079435 3120455 := bstep (se 1 (by rfl) ⟨2340341, by rfl⟩ : syracuseStep 3120455 = 4680683) B4680683
theorem B2080303 : Blo 2079435 2080303 := bstep (se 1 (by rfl) ⟨1560227, by rfl⟩ : syracuseStep 2080303 = 3120455) B3120455
theorem B3120461 : Blo 2079435 3120461 := bbase (se 3 (by rfl) ⟨585086, by rfl⟩ : syracuseStep 3120461 = 1170173) (by norm_num)
theorem B2080307 : Blo 2079435 2080307 := bstep (se 1 (by rfl) ⟨1560230, by rfl⟩ : syracuseStep 2080307 = 3120461) B3120461
theorem B4680701 : Blo 2079435 4680701 := bbase (se 3 (by rfl) ⟨877631, by rfl⟩ : syracuseStep 4680701 = 1755263) (by norm_num)
theorem B3120467 : Blo 2079435 3120467 := bstep (se 1 (by rfl) ⟨2340350, by rfl⟩ : syracuseStep 3120467 = 4680701) B4680701
theorem B2080311 : Blo 2079435 2080311 := bstep (se 1 (by rfl) ⟨1560233, by rfl⟩ : syracuseStep 2080311 = 3120467) B3120467
theorem B3510533 : Blo 2079435 3510533 := bbase (se 4 (by rfl) ⟨329112, by rfl⟩ : syracuseStep 3510533 = 658225) (by norm_num)
theorem B2340355 : Blo 2079435 2340355 := bstep (se 1 (by rfl) ⟨1755266, by rfl⟩ : syracuseStep 2340355 = 3510533) B3510533
theorem B3120473 : Blo 2079435 3120473 := bstep (se 2 (by rfl) ⟨1170177, by rfl⟩ : syracuseStep 3120473 = 2340355) B2340355
theorem B2080315 : Blo 2079435 2080315 := bstep (se 1 (by rfl) ⟨1560236, by rfl⟩ : syracuseStep 2080315 = 3120473) B3120473
theorem B15797429 : Blo 2079435 15797429 := bbase (se 5 (by rfl) ⟨740504, by rfl⟩ : syracuseStep 15797429 = 1481009) (by norm_num)
theorem B10531619 : Blo 2079435 10531619 := bstep (se 1 (by rfl) ⟨7898714, by rfl⟩ : syracuseStep 10531619 = 15797429) B15797429
theorem B7021079 : Blo 2079435 7021079 := bstep (se 1 (by rfl) ⟨5265809, by rfl⟩ : syracuseStep 7021079 = 10531619) B10531619
theorem B4680719 : Blo 2079435 4680719 := bstep (se 1 (by rfl) ⟨3510539, by rfl⟩ : syracuseStep 4680719 = 7021079) B7021079
theorem B3120479 : Blo 2079435 3120479 := bstep (se 1 (by rfl) ⟨2340359, by rfl⟩ : syracuseStep 3120479 = 4680719) B4680719
theorem B2080319 : Blo 2079435 2080319 := bstep (se 1 (by rfl) ⟨1560239, by rfl⟩ : syracuseStep 2080319 = 3120479) B3120479
theorem B3120485 : Blo 2079435 3120485 := bbase (se 4 (by rfl) ⟨292545, by rfl⟩ : syracuseStep 3120485 = 585091) (by norm_num)
theorem B2080323 : Blo 2079435 2080323 := bstep (se 1 (by rfl) ⟨1560242, by rfl⟩ : syracuseStep 2080323 = 3120485) B3120485
theorem B3949373 : Blo 2079435 3949373 := bbase (se 3 (by rfl) ⟨740507, by rfl⟩ : syracuseStep 3949373 = 1481015) (by norm_num)
theorem B2632915 : Blo 2079435 2632915 := bstep (se 1 (by rfl) ⟨1974686, by rfl⟩ : syracuseStep 2632915 = 3949373) B3949373
theorem B3510553 : Blo 2079435 3510553 := bstep (se 2 (by rfl) ⟨1316457, by rfl⟩ : syracuseStep 3510553 = 2632915) B2632915
theorem B4680737 : Blo 2079435 4680737 := bstep (se 2 (by rfl) ⟨1755276, by rfl⟩ : syracuseStep 4680737 = 3510553) B3510553
theorem B3120491 : Blo 2079435 3120491 := bstep (se 1 (by rfl) ⟨2340368, by rfl⟩ : syracuseStep 3120491 = 4680737) B4680737
theorem B2080327 : Blo 2079435 2080327 := bstep (se 1 (by rfl) ⟨1560245, by rfl⟩ : syracuseStep 2080327 = 3120491) B3120491
theorem B2340373 : Blo 2079435 2340373 := bbase (se 6 (by rfl) ⟨54852, by rfl⟩ : syracuseStep 2340373 = 109705) (by norm_num)
theorem B3120497 : Blo 2079435 3120497 := bstep (se 2 (by rfl) ⟨1170186, by rfl⟩ : syracuseStep 3120497 = 2340373) B2340373
theorem B2080331 : Blo 2079435 2080331 := bstep (se 1 (by rfl) ⟨1560248, by rfl⟩ : syracuseStep 2080331 = 3120497) B3120497
theorem B2632925 : Blo 2079435 2632925 := bbase (se 3 (by rfl) ⟨493673, by rfl⟩ : syracuseStep 2632925 = 987347) (by norm_num)
theorem B7021133 : Blo 2079435 7021133 := bstep (se 3 (by rfl) ⟨1316462, by rfl⟩ : syracuseStep 7021133 = 2632925) B2632925
theorem B4680755 : Blo 2079435 4680755 := bstep (se 1 (by rfl) ⟨3510566, by rfl⟩ : syracuseStep 4680755 = 7021133) B7021133
theorem B3120503 : Blo 2079435 3120503 := bstep (se 1 (by rfl) ⟨2340377, by rfl⟩ : syracuseStep 3120503 = 4680755) B4680755
theorem B2080335 : Blo 2079435 2080335 := bstep (se 1 (by rfl) ⟨1560251, by rfl⟩ : syracuseStep 2080335 = 3120503) B3120503
theorem B3120509 : Blo 2079435 3120509 := bbase (se 3 (by rfl) ⟨585095, by rfl⟩ : syracuseStep 3120509 = 1170191) (by norm_num)
theorem B2080339 : Blo 2079435 2080339 := bstep (se 1 (by rfl) ⟨1560254, by rfl⟩ : syracuseStep 2080339 = 3120509) B3120509
theorem B4680773 : Blo 2079435 4680773 := bbase (se 4 (by rfl) ⟨438822, by rfl⟩ : syracuseStep 4680773 = 877645) (by norm_num)
theorem B3120515 : Blo 2079435 3120515 := bstep (se 1 (by rfl) ⟨2340386, by rfl⟩ : syracuseStep 3120515 = 4680773) B4680773
theorem B2080343 : Blo 2079435 2080343 := bstep (se 1 (by rfl) ⟨1560257, by rfl⟩ : syracuseStep 2080343 = 3120515) B3120515
theorem B5924117 : Blo 2079435 5924117 := bbase (se 6 (by rfl) ⟨138846, by rfl⟩ : syracuseStep 5924117 = 277693) (by norm_num)
theorem B3949411 : Blo 2079435 3949411 := bstep (se 1 (by rfl) ⟨2962058, by rfl⟩ : syracuseStep 3949411 = 5924117) B5924117
theorem B5265881 : Blo 2079435 5265881 := bstep (se 2 (by rfl) ⟨1974705, by rfl⟩ : syracuseStep 5265881 = 3949411) B3949411
theorem B3510587 : Blo 2079435 3510587 := bstep (se 1 (by rfl) ⟨2632940, by rfl⟩ : syracuseStep 3510587 = 5265881) B5265881
theorem B2340391 : Blo 2079435 2340391 := bstep (se 1 (by rfl) ⟨1755293, by rfl⟩ : syracuseStep 2340391 = 3510587) B3510587
theorem B3120521 : Blo 2079435 3120521 := bstep (se 2 (by rfl) ⟨1170195, by rfl⟩ : syracuseStep 3120521 = 2340391) B2340391
theorem B2080347 : Blo 2079435 2080347 := bstep (se 1 (by rfl) ⟨1560260, by rfl⟩ : syracuseStep 2080347 = 3120521) B3120521
theorem B10531781 : Blo 2079435 10531781 := bbase (se 4 (by rfl) ⟨987354, by rfl⟩ : syracuseStep 10531781 = 1974709) (by norm_num)
theorem B7021187 : Blo 2079435 7021187 := bstep (se 1 (by rfl) ⟨5265890, by rfl⟩ : syracuseStep 7021187 = 10531781) B10531781
theorem B4680791 : Blo 2079435 4680791 := bstep (se 1 (by rfl) ⟨3510593, by rfl⟩ : syracuseStep 4680791 = 7021187) B7021187
theorem B3120527 : Blo 2079435 3120527 := bstep (se 1 (by rfl) ⟨2340395, by rfl⟩ : syracuseStep 3120527 = 4680791) B4680791
theorem B2080351 : Blo 2079435 2080351 := bstep (se 1 (by rfl) ⟨1560263, by rfl⟩ : syracuseStep 2080351 = 3120527) B3120527
theorem B3120533 : Blo 2079435 3120533 := bbase (se 6 (by rfl) ⟨73137, by rfl⟩ : syracuseStep 3120533 = 146275) (by norm_num)
theorem B2080355 : Blo 2079435 2080355 := bstep (se 1 (by rfl) ⟨1560266, by rfl⟩ : syracuseStep 2080355 = 3120533) B3120533
theorem B9618821 : Blo 2079435 9618821 := bbase (se 4 (by rfl) ⟨901764, by rfl⟩ : syracuseStep 9618821 = 1803529) (by norm_num)
theorem B6412547 : Blo 2079435 6412547 := bstep (se 1 (by rfl) ⟨4809410, by rfl⟩ : syracuseStep 6412547 = 9618821) B9618821
theorem B4275031 : Blo 2079435 4275031 := bstep (se 1 (by rfl) ⟨3206273, by rfl⟩ : syracuseStep 4275031 = 6412547) B6412547
theorem B5700041 : Blo 2079435 5700041 := bstep (se 2 (by rfl) ⟨2137515, by rfl⟩ : syracuseStep 5700041 = 4275031) B4275031
theorem B3800027 : Blo 2079435 3800027 := bstep (se 1 (by rfl) ⟨2850020, by rfl⟩ : syracuseStep 3800027 = 5700041) B5700041
theorem B2533351 : Blo 2079435 2533351 := bstep (se 1 (by rfl) ⟨1900013, by rfl⟩ : syracuseStep 2533351 = 3800027) B3800027
theorem B3377801 : Blo 2079435 3377801 := bstep (se 2 (by rfl) ⟨1266675, by rfl⟩ : syracuseStep 3377801 = 2533351) B2533351
theorem B2251867 : Blo 2079435 2251867 := bstep (se 1 (by rfl) ⟨1688900, by rfl⟩ : syracuseStep 2251867 = 3377801) B3377801
theorem B3002489 : Blo 2079435 3002489 := bstep (se 2 (by rfl) ⟨1125933, by rfl⟩ : syracuseStep 3002489 = 2251867) B2251867
theorem B32026549 : Blo 2079435 32026549 := bstep (se 5 (by rfl) ⟨1501244, by rfl⟩ : syracuseStep 32026549 = 3002489) B3002489
theorem B42702065 : Blo 2079435 42702065 := bstep (se 2 (by rfl) ⟨16013274, by rfl⟩ : syracuseStep 42702065 = 32026549) B32026549
theorem B28468043 : Blo 2079435 28468043 := bstep (se 1 (by rfl) ⟨21351032, by rfl⟩ : syracuseStep 28468043 = 42702065) B42702065
theorem B18978695 : Blo 2079435 18978695 := bstep (se 1 (by rfl) ⟨14234021, by rfl⟩ : syracuseStep 18978695 = 28468043) B28468043
theorem B12652463 : Blo 2079435 12652463 := bstep (se 1 (by rfl) ⟨9489347, by rfl⟩ : syracuseStep 12652463 = 18978695) B18978695
theorem B8434975 : Blo 2079435 8434975 := bstep (se 1 (by rfl) ⟨6326231, by rfl⟩ : syracuseStep 8434975 = 12652463) B12652463
theorem B11246633 : Blo 2079435 11246633 := bstep (se 2 (by rfl) ⟨4217487, by rfl⟩ : syracuseStep 11246633 = 8434975) B8434975
theorem B7497755 : Blo 2079435 7497755 := bstep (se 1 (by rfl) ⟨5623316, by rfl⟩ : syracuseStep 7497755 = 11246633) B11246633
theorem B4998503 : Blo 2079435 4998503 := bstep (se 1 (by rfl) ⟨3748877, by rfl⟩ : syracuseStep 4998503 = 7497755) B7497755
theorem B3332335 : Blo 2079435 3332335 := bstep (se 1 (by rfl) ⟨2499251, by rfl⟩ : syracuseStep 3332335 = 4998503) B4998503
theorem B4443113 : Blo 2079435 4443113 := bstep (se 2 (by rfl) ⟨1666167, by rfl⟩ : syracuseStep 4443113 = 3332335) B3332335
theorem B11848301 : Blo 2079435 11848301 := bstep (se 3 (by rfl) ⟨2221556, by rfl⟩ : syracuseStep 11848301 = 4443113) B4443113
theorem B7898867 : Blo 2079435 7898867 := bstep (se 1 (by rfl) ⟨5924150, by rfl⟩ : syracuseStep 7898867 = 11848301) B11848301
theorem B5265911 : Blo 2079435 5265911 := bstep (se 1 (by rfl) ⟨3949433, by rfl⟩ : syracuseStep 5265911 = 7898867) B7898867
theorem B3510607 : Blo 2079435 3510607 := bstep (se 1 (by rfl) ⟨2632955, by rfl⟩ : syracuseStep 3510607 = 5265911) B5265911
theorem B4680809 : Blo 2079435 4680809 := bstep (se 2 (by rfl) ⟨1755303, by rfl⟩ : syracuseStep 4680809 = 3510607) B3510607
theorem B3120539 : Blo 2079435 3120539 := bstep (se 1 (by rfl) ⟨2340404, by rfl⟩ : syracuseStep 3120539 = 4680809) B4680809
theorem B2080359 : Blo 2079435 2080359 := bstep (se 1 (by rfl) ⟨1560269, by rfl⟩ : syracuseStep 2080359 = 3120539) B3120539
theorem B2340409 : Blo 2079435 2340409 := bbase (se 2 (by rfl) ⟨877653, by rfl⟩ : syracuseStep 2340409 = 1755307) (by norm_num)
theorem B3120545 : Blo 2079435 3120545 := bstep (se 2 (by rfl) ⟨1170204, by rfl⟩ : syracuseStep 3120545 = 2340409) B2340409
theorem B2080363 : Blo 2079435 2080363 := bstep (se 1 (by rfl) ⟨1560272, by rfl⟩ : syracuseStep 2080363 = 3120545) B3120545
theorem B2221565 : Blo 2079435 2221565 := bbase (se 3 (by rfl) ⟨416543, by rfl⟩ : syracuseStep 2221565 = 833087) (by norm_num)
theorem B5924173 : Blo 2079435 5924173 := bstep (se 3 (by rfl) ⟨1110782, by rfl⟩ : syracuseStep 5924173 = 2221565) B2221565
theorem B7898897 : Blo 2079435 7898897 := bstep (se 2 (by rfl) ⟨2962086, by rfl⟩ : syracuseStep 7898897 = 5924173) B5924173
theorem B5265931 : Blo 2079435 5265931 := bstep (se 1 (by rfl) ⟨3949448, by rfl⟩ : syracuseStep 5265931 = 7898897) B7898897
theorem B7021241 : Blo 2079435 7021241 := bstep (se 2 (by rfl) ⟨2632965, by rfl⟩ : syracuseStep 7021241 = 5265931) B5265931
theorem B4680827 : Blo 2079435 4680827 := bstep (se 1 (by rfl) ⟨3510620, by rfl⟩ : syracuseStep 4680827 = 7021241) B7021241
theorem B3120551 : Blo 2079435 3120551 := bstep (se 1 (by rfl) ⟨2340413, by rfl⟩ : syracuseStep 3120551 = 4680827) B4680827
theorem B2080367 : Blo 2079435 2080367 := bstep (se 1 (by rfl) ⟨1560275, by rfl⟩ : syracuseStep 2080367 = 3120551) B3120551
theorem B3120557 : Blo 2079435 3120557 := bbase (se 3 (by rfl) ⟨585104, by rfl⟩ : syracuseStep 3120557 = 1170209) (by norm_num)
theorem B2080371 : Blo 2079435 2080371 := bstep (se 1 (by rfl) ⟨1560278, by rfl⟩ : syracuseStep 2080371 = 3120557) B3120557
theorem B4680845 : Blo 2079435 4680845 := bbase (se 3 (by rfl) ⟨877658, by rfl⟩ : syracuseStep 4680845 = 1755317) (by norm_num)
theorem B3120563 : Blo 2079435 3120563 := bstep (se 1 (by rfl) ⟨2340422, by rfl⟩ : syracuseStep 3120563 = 4680845) B4680845
theorem B2080375 : Blo 2079435 2080375 := bstep (se 1 (by rfl) ⟨1560281, by rfl⟩ : syracuseStep 2080375 = 3120563) B3120563
theorem B2632981 : Blo 2079435 2632981 := bbase (se 6 (by rfl) ⟨61710, by rfl⟩ : syracuseStep 2632981 = 123421) (by norm_num)
theorem B3510641 : Blo 2079435 3510641 := bstep (se 2 (by rfl) ⟨1316490, by rfl⟩ : syracuseStep 3510641 = 2632981) B2632981
theorem B2340427 : Blo 2079435 2340427 := bstep (se 1 (by rfl) ⟨1755320, by rfl⟩ : syracuseStep 2340427 = 3510641) B3510641
theorem B3120569 : Blo 2079435 3120569 := bstep (se 2 (by rfl) ⟨1170213, by rfl⟩ : syracuseStep 3120569 = 2340427) B2340427
theorem B2080379 : Blo 2079435 2080379 := bstep (se 1 (by rfl) ⟨1560284, by rfl⟩ : syracuseStep 2080379 = 3120569) B3120569
theorem B4574773 : Blo 2079435 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B6099697 : Blo 2079435 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B32531717 : Blo 2079435 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B86751245 : Blo 2079435 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B57834163 : Blo 2079435 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B77112217 : Blo 2079435 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B102816289 : Blo 2079435 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B137088385 : Blo 2079435 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B2924552213 : Blo 2079435 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B1949701475 : Blo 2079435 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B5199203933 : Blo 2079435 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B3466135955 : Blo 2079435 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B2310757303 : Blo 2079435 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B3081009737 : Blo 2079435 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B8216025965 : Blo 2079435 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B5477350643 : Blo 2079435 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B3651567095 : Blo 2079435 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B2434378063 : Blo 2079435 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B3245837417 : Blo 2079435 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B2163891611 : Blo 2079435 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B1442594407 : Blo 2079435 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B1923459209 : Blo 2079435 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B1282306139 : Blo 2079435 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B854870759 : Blo 2079435 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B569913839 : Blo 2079435 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B379942559 : Blo 2079435 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B253295039 : Blo 2079435 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B168863359 : Blo 2079435 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B225151145 : Blo 2079435 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B2401612213 : Blo 2079435 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B3202149617 : Blo 2079435 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B2134766411 : Blo 2079435 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B1423177607 : Blo 2079435 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B948785071 : Blo 2079435 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B1265046761 : Blo 2079435 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B843364507 : Blo 2079435 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B1124486009 : Blo 2079435 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B749657339 : Blo 2079435 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B499771559 : Blo 2079435 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B333181039 : Blo 2079435 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B444241385 : Blo 2079435 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B296160923 : Blo 2079435 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B197440615 : Blo 2079435 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B263254153 : Blo 2079435 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B351005537 : Blo 2079435 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B234003691 : Blo 2079435 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B312004921 : Blo 2079435 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B416006561 : Blo 2079435 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B1109350829 : Blo 2079435 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B739567219 : Blo 2079435 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B986089625 : Blo 2079435 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B657393083 : Blo 2079435 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B438262055 : Blo 2079435 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B292174703 : Blo 2079435 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B194783135 : Blo 2079435 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B519421693 : Blo 2079435 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B692562257 : Blo 2079435 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B461708171 : Blo 2079435 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B307805447 : Blo 2079435 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B205203631 : Blo 2079435 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B273604841 : Blo 2079435 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B182403227 : Blo 2079435 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B121602151 : Blo 2079435 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B648544805 : Blo 2079435 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B432363203 : Blo 2079435 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 2079435 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B192161423 : Blo 2079435 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 2079435 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B170810153 : Blo 2079435 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 2079435 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 2079435 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 2079435 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 2079435 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 2079435 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 2079435 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 2079435 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 2079435 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B17772655 : Blo 2079435 17772655 := bstep (se 1 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 17772655 = 26658983) B26658983
theorem B23696873 : Blo 2079435 23696873 := bstep (se 2 (by rfl) ⟨8886327, by rfl⟩ : syracuseStep 23696873 = 17772655) B17772655
theorem B15797915 : Blo 2079435 15797915 := bstep (se 1 (by rfl) ⟨11848436, by rfl⟩ : syracuseStep 15797915 = 23696873) B23696873
theorem B10531943 : Blo 2079435 10531943 := bstep (se 1 (by rfl) ⟨7898957, by rfl⟩ : syracuseStep 10531943 = 15797915) B15797915
theorem B7021295 : Blo 2079435 7021295 := bstep (se 1 (by rfl) ⟨5265971, by rfl⟩ : syracuseStep 7021295 = 10531943) B10531943
theorem B4680863 : Blo 2079435 4680863 := bstep (se 1 (by rfl) ⟨3510647, by rfl⟩ : syracuseStep 4680863 = 7021295) B7021295
theorem B3120575 : Blo 2079435 3120575 := bstep (se 1 (by rfl) ⟨2340431, by rfl⟩ : syracuseStep 3120575 = 4680863) B4680863
theorem B2080383 : Blo 2079435 2080383 := bstep (se 1 (by rfl) ⟨1560287, by rfl⟩ : syracuseStep 2080383 = 3120575) B3120575
theorem B3120581 : Blo 2079435 3120581 := bbase (se 4 (by rfl) ⟨292554, by rfl⟩ : syracuseStep 3120581 = 585109) (by norm_num)
theorem B2080387 : Blo 2079435 2080387 := bstep (se 1 (by rfl) ⟨1560290, by rfl⟩ : syracuseStep 2080387 = 3120581) B3120581
theorem B3510661 : Blo 2079435 3510661 := bbase (se 4 (by rfl) ⟨329124, by rfl⟩ : syracuseStep 3510661 = 658249) (by norm_num)
theorem B4680881 : Blo 2079435 4680881 := bstep (se 2 (by rfl) ⟨1755330, by rfl⟩ : syracuseStep 4680881 = 3510661) B3510661
theorem B3120587 : Blo 2079435 3120587 := bstep (se 1 (by rfl) ⟨2340440, by rfl⟩ : syracuseStep 3120587 = 4680881) B4680881
theorem B2080391 : Blo 2079435 2080391 := bstep (se 1 (by rfl) ⟨1560293, by rfl⟩ : syracuseStep 2080391 = 3120587) B3120587
theorem B2340445 : Blo 2079435 2340445 := bbase (se 3 (by rfl) ⟨438833, by rfl⟩ : syracuseStep 2340445 = 877667) (by norm_num)
theorem B3120593 : Blo 2079435 3120593 := bstep (se 2 (by rfl) ⟨1170222, by rfl⟩ : syracuseStep 3120593 = 2340445) B2340445
theorem B2080395 : Blo 2079435 2080395 := bstep (se 1 (by rfl) ⟨1560296, by rfl⟩ : syracuseStep 2080395 = 3120593) B3120593
theorem B7021349 : Blo 2079435 7021349 := bbase (se 4 (by rfl) ⟨658251, by rfl⟩ : syracuseStep 7021349 = 1316503) (by norm_num)
theorem B4680899 : Blo 2079435 4680899 := bstep (se 1 (by rfl) ⟨3510674, by rfl⟩ : syracuseStep 4680899 = 7021349) B7021349
theorem B3120599 : Blo 2079435 3120599 := bstep (se 1 (by rfl) ⟨2340449, by rfl⟩ : syracuseStep 3120599 = 4680899) B4680899
theorem B2080399 : Blo 2079435 2080399 := bstep (se 1 (by rfl) ⟨1560299, by rfl⟩ : syracuseStep 2080399 = 3120599) B3120599
theorem B3120605 : Blo 2079435 3120605 := bbase (se 3 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 3120605 = 1170227) (by norm_num)
theorem B2080403 : Blo 2079435 2080403 := bstep (se 1 (by rfl) ⟨1560302, by rfl⟩ : syracuseStep 2080403 = 3120605) B3120605
theorem B4680917 : Blo 2079435 4680917 := bbase (se 7 (by rfl) ⟨54854, by rfl⟩ : syracuseStep 4680917 = 109709) (by norm_num)
theorem B3120611 : Blo 2079435 3120611 := bstep (se 1 (by rfl) ⟨2340458, by rfl⟩ : syracuseStep 3120611 = 4680917) B4680917
theorem B2080407 : Blo 2079435 2080407 := bstep (se 1 (by rfl) ⟨1560305, by rfl⟩ : syracuseStep 2080407 = 3120611) B3120611
theorem B6664837 : Blo 2079435 6664837 := bbase (se 4 (by rfl) ⟨624828, by rfl⟩ : syracuseStep 6664837 = 1249657) (by norm_num)
theorem B8886449 : Blo 2079435 8886449 := bstep (se 2 (by rfl) ⟨3332418, by rfl⟩ : syracuseStep 8886449 = 6664837) B6664837
theorem B5924299 : Blo 2079435 5924299 := bstep (se 1 (by rfl) ⟨4443224, by rfl⟩ : syracuseStep 5924299 = 8886449) B8886449
theorem B7899065 : Blo 2079435 7899065 := bstep (se 2 (by rfl) ⟨2962149, by rfl⟩ : syracuseStep 7899065 = 5924299) B5924299
theorem B5266043 : Blo 2079435 5266043 := bstep (se 1 (by rfl) ⟨3949532, by rfl⟩ : syracuseStep 5266043 = 7899065) B7899065
theorem B3510695 : Blo 2079435 3510695 := bstep (se 1 (by rfl) ⟨2633021, by rfl⟩ : syracuseStep 3510695 = 5266043) B5266043
theorem B2340463 : Blo 2079435 2340463 := bstep (se 1 (by rfl) ⟨1755347, by rfl⟩ : syracuseStep 2340463 = 3510695) B3510695
theorem B3120617 : Blo 2079435 3120617 := bstep (se 2 (by rfl) ⟨1170231, by rfl⟩ : syracuseStep 3120617 = 2340463) B2340463
theorem B2080411 : Blo 2079435 2080411 := bstep (se 1 (by rfl) ⟨1560308, by rfl⟩ : syracuseStep 2080411 = 3120617) B3120617
theorem B11246933 : Blo 2079435 11246933 := bbase (se 11 (by rfl) ⟨8237, by rfl⟩ : syracuseStep 11246933 = 16475) (by norm_num)
theorem B7497955 : Blo 2079435 7497955 := bstep (se 1 (by rfl) ⟨5623466, by rfl⟩ : syracuseStep 7497955 = 11246933) B11246933
theorem B9997273 : Blo 2079435 9997273 := bstep (se 2 (by rfl) ⟨3748977, by rfl⟩ : syracuseStep 9997273 = 7497955) B7497955
theorem B13329697 : Blo 2079435 13329697 := bstep (se 2 (by rfl) ⟨4998636, by rfl⟩ : syracuseStep 13329697 = 9997273) B9997273
theorem B17772929 : Blo 2079435 17772929 := bstep (se 2 (by rfl) ⟨6664848, by rfl⟩ : syracuseStep 17772929 = 13329697) B13329697
theorem B11848619 : Blo 2079435 11848619 := bstep (se 1 (by rfl) ⟨8886464, by rfl⟩ : syracuseStep 11848619 = 17772929) B17772929
theorem B7899079 : Blo 2079435 7899079 := bstep (se 1 (by rfl) ⟨5924309, by rfl⟩ : syracuseStep 7899079 = 11848619) B11848619
theorem B10532105 : Blo 2079435 10532105 := bstep (se 2 (by rfl) ⟨3949539, by rfl⟩ : syracuseStep 10532105 = 7899079) B7899079
theorem B7021403 : Blo 2079435 7021403 := bstep (se 1 (by rfl) ⟨5266052, by rfl⟩ : syracuseStep 7021403 = 10532105) B10532105
theorem B4680935 : Blo 2079435 4680935 := bstep (se 1 (by rfl) ⟨3510701, by rfl⟩ : syracuseStep 4680935 = 7021403) B7021403
theorem B3120623 : Blo 2079435 3120623 := bstep (se 1 (by rfl) ⟨2340467, by rfl⟩ : syracuseStep 3120623 = 4680935) B4680935
theorem B2080415 : Blo 2079435 2080415 := bstep (se 1 (by rfl) ⟨1560311, by rfl⟩ : syracuseStep 2080415 = 3120623) B3120623
theorem B3120629 : Blo 2079435 3120629 := bbase (se 5 (by rfl) ⟨146279, by rfl⟩ : syracuseStep 3120629 = 292559) (by norm_num)
theorem B2080419 : Blo 2079435 2080419 := bstep (se 1 (by rfl) ⟨1560314, by rfl⟩ : syracuseStep 2080419 = 3120629) B3120629
theorem B2221625 : Blo 2079435 2221625 := bbase (se 2 (by rfl) ⟨833109, by rfl⟩ : syracuseStep 2221625 = 1666219) (by norm_num)
theorem B5924333 : Blo 2079435 5924333 := bstep (se 3 (by rfl) ⟨1110812, by rfl⟩ : syracuseStep 5924333 = 2221625) B2221625
theorem B3949555 : Blo 2079435 3949555 := bstep (se 1 (by rfl) ⟨2962166, by rfl⟩ : syracuseStep 3949555 = 5924333) B5924333
theorem B5266073 : Blo 2079435 5266073 := bstep (se 2 (by rfl) ⟨1974777, by rfl⟩ : syracuseStep 5266073 = 3949555) B3949555
theorem B3510715 : Blo 2079435 3510715 := bstep (se 1 (by rfl) ⟨2633036, by rfl⟩ : syracuseStep 3510715 = 5266073) B5266073
theorem B4680953 : Blo 2079435 4680953 := bstep (se 2 (by rfl) ⟨1755357, by rfl⟩ : syracuseStep 4680953 = 3510715) B3510715
theorem B3120635 : Blo 2079435 3120635 := bstep (se 1 (by rfl) ⟨2340476, by rfl⟩ : syracuseStep 3120635 = 4680953) B4680953
theorem B2080423 : Blo 2079435 2080423 := bstep (se 1 (by rfl) ⟨1560317, by rfl⟩ : syracuseStep 2080423 = 3120635) B3120635
theorem B2340481 : Blo 2079435 2340481 := bbase (se 2 (by rfl) ⟨877680, by rfl⟩ : syracuseStep 2340481 = 1755361) (by norm_num)
theorem B3120641 : Blo 2079435 3120641 := bstep (se 2 (by rfl) ⟨1170240, by rfl⟩ : syracuseStep 3120641 = 2340481) B2340481
theorem B2080427 : Blo 2079435 2080427 := bstep (se 1 (by rfl) ⟨1560320, by rfl⟩ : syracuseStep 2080427 = 3120641) B3120641
theorem B5266093 : Blo 2079435 5266093 := bbase (se 3 (by rfl) ⟨987392, by rfl⟩ : syracuseStep 5266093 = 1974785) (by norm_num)
theorem B7021457 : Blo 2079435 7021457 := bstep (se 2 (by rfl) ⟨2633046, by rfl⟩ : syracuseStep 7021457 = 5266093) B5266093
theorem B4680971 : Blo 2079435 4680971 := bstep (se 1 (by rfl) ⟨3510728, by rfl⟩ : syracuseStep 4680971 = 7021457) B7021457
theorem B3120647 : Blo 2079435 3120647 := bstep (se 1 (by rfl) ⟨2340485, by rfl⟩ : syracuseStep 3120647 = 4680971) B4680971
theorem B2080431 : Blo 2079435 2080431 := bstep (se 1 (by rfl) ⟨1560323, by rfl⟩ : syracuseStep 2080431 = 3120647) B3120647
theorem B3120653 : Blo 2079435 3120653 := bbase (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) (by norm_num)
theorem B2080435 : Blo 2079435 2080435 := bstep (se 1 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 2080435 = 3120653) B3120653
theorem B4680989 : Blo 2079435 4680989 := bbase (se 3 (by rfl) ⟨877685, by rfl⟩ : syracuseStep 4680989 = 1755371) (by norm_num)
theorem B3120659 : Blo 2079435 3120659 := bstep (se 1 (by rfl) ⟨2340494, by rfl⟩ : syracuseStep 3120659 = 4680989) B4680989
theorem B2080439 : Blo 2079435 2080439 := bstep (se 1 (by rfl) ⟨1560329, by rfl⟩ : syracuseStep 2080439 = 3120659) B3120659
theorem B3510749 : Blo 2079435 3510749 := bbase (se 3 (by rfl) ⟨658265, by rfl⟩ : syracuseStep 3510749 = 1316531) (by norm_num)
theorem B2340499 : Blo 2079435 2340499 := bstep (se 1 (by rfl) ⟨1755374, by rfl⟩ : syracuseStep 2340499 = 3510749) B3510749
theorem B3120665 : Blo 2079435 3120665 := bstep (se 2 (by rfl) ⟨1170249, by rfl⟩ : syracuseStep 3120665 = 2340499) B2340499
theorem B2080443 : Blo 2079435 2080443 := bstep (se 1 (by rfl) ⟨1560332, by rfl⟩ : syracuseStep 2080443 = 3120665) B3120665
theorem B2372437 : Blo 2079435 2372437 := bbase (se 9 (by rfl) ⟨6950, by rfl⟩ : syracuseStep 2372437 = 13901) (by norm_num)
theorem B3163249 : Blo 2079435 3163249 := bstep (se 2 (by rfl) ⟨1186218, by rfl⟩ : syracuseStep 3163249 = 2372437) B2372437
theorem B4217665 : Blo 2079435 4217665 := bstep (se 2 (by rfl) ⟨1581624, by rfl⟩ : syracuseStep 4217665 = 3163249) B3163249
theorem B5623553 : Blo 2079435 5623553 := bstep (se 2 (by rfl) ⟨2108832, by rfl⟩ : syracuseStep 5623553 = 4217665) B4217665
theorem B14996141 : Blo 2079435 14996141 := bstep (se 3 (by rfl) ⟨2811776, by rfl⟩ : syracuseStep 14996141 = 5623553) B5623553
theorem B9997427 : Blo 2079435 9997427 := bstep (se 1 (by rfl) ⟨7498070, by rfl⟩ : syracuseStep 9997427 = 14996141) B14996141
theorem B6664951 : Blo 2079435 6664951 := bstep (se 1 (by rfl) ⟨4998713, by rfl⟩ : syracuseStep 6664951 = 9997427) B9997427
theorem B8886601 : Blo 2079435 8886601 := bstep (se 2 (by rfl) ⟨3332475, by rfl⟩ : syracuseStep 8886601 = 6664951) B6664951
theorem B11848801 : Blo 2079435 11848801 := bstep (se 2 (by rfl) ⟨4443300, by rfl⟩ : syracuseStep 11848801 = 8886601) B8886601
theorem B15798401 : Blo 2079435 15798401 := bstep (se 2 (by rfl) ⟨5924400, by rfl⟩ : syracuseStep 15798401 = 11848801) B11848801
theorem B10532267 : Blo 2079435 10532267 := bstep (se 1 (by rfl) ⟨7899200, by rfl⟩ : syracuseStep 10532267 = 15798401) B15798401
theorem B7021511 : Blo 2079435 7021511 := bstep (se 1 (by rfl) ⟨5266133, by rfl⟩ : syracuseStep 7021511 = 10532267) B10532267
theorem B4681007 : Blo 2079435 4681007 := bstep (se 1 (by rfl) ⟨3510755, by rfl⟩ : syracuseStep 4681007 = 7021511) B7021511
theorem B3120671 : Blo 2079435 3120671 := bstep (se 1 (by rfl) ⟨2340503, by rfl⟩ : syracuseStep 3120671 = 4681007) B4681007
theorem B2080447 : Blo 2079435 2080447 := bstep (se 1 (by rfl) ⟨1560335, by rfl⟩ : syracuseStep 2080447 = 3120671) B3120671
theorem B3120677 : Blo 2079435 3120677 := bbase (se 4 (by rfl) ⟨292563, by rfl⟩ : syracuseStep 3120677 = 585127) (by norm_num)
theorem B2080451 : Blo 2079435 2080451 := bstep (se 1 (by rfl) ⟨1560338, by rfl⟩ : syracuseStep 2080451 = 3120677) B3120677
theorem B2633077 : Blo 2079435 2633077 := bbase (se 5 (by rfl) ⟨123425, by rfl⟩ : syracuseStep 2633077 = 246851) (by norm_num)
theorem B3510769 : Blo 2079435 3510769 := bstep (se 2 (by rfl) ⟨1316538, by rfl⟩ : syracuseStep 3510769 = 2633077) B2633077
theorem B4681025 : Blo 2079435 4681025 := bstep (se 2 (by rfl) ⟨1755384, by rfl⟩ : syracuseStep 4681025 = 3510769) B3510769
theorem B3120683 : Blo 2079435 3120683 := bstep (se 1 (by rfl) ⟨2340512, by rfl⟩ : syracuseStep 3120683 = 4681025) B4681025
theorem B2080455 : Blo 2079435 2080455 := bstep (se 1 (by rfl) ⟨1560341, by rfl⟩ : syracuseStep 2080455 = 3120683) B3120683
theorem B2340517 : Blo 2079435 2340517 := bbase (se 4 (by rfl) ⟨219423, by rfl⟩ : syracuseStep 2340517 = 438847) (by norm_num)
theorem B3120689 : Blo 2079435 3120689 := bstep (se 2 (by rfl) ⟨1170258, by rfl⟩ : syracuseStep 3120689 = 2340517) B2340517
theorem B2080459 : Blo 2079435 2080459 := bstep (se 1 (by rfl) ⟨1560344, by rfl⟩ : syracuseStep 2080459 = 3120689) B3120689
theorem B2108849 : Blo 2079435 2108849 := bbase (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) (by norm_num)
theorem B5623597 : Blo 2079435 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B29992517 : Blo 2079435 29992517 := bstep (se 4 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 29992517 = 5623597) B5623597
theorem B19995011 : Blo 2079435 19995011 := bstep (se 1 (by rfl) ⟨14996258, by rfl⟩ : syracuseStep 19995011 = 29992517) B29992517
theorem B13330007 : Blo 2079435 13330007 := bstep (se 1 (by rfl) ⟨9997505, by rfl⟩ : syracuseStep 13330007 = 19995011) B19995011
theorem B8886671 : Blo 2079435 8886671 := bstep (se 1 (by rfl) ⟨6665003, by rfl⟩ : syracuseStep 8886671 = 13330007) B13330007
theorem B5924447 : Blo 2079435 5924447 := bstep (se 1 (by rfl) ⟨4443335, by rfl⟩ : syracuseStep 5924447 = 8886671) B8886671
theorem B3949631 : Blo 2079435 3949631 := bstep (se 1 (by rfl) ⟨2962223, by rfl⟩ : syracuseStep 3949631 = 5924447) B5924447
theorem B2633087 : Blo 2079435 2633087 := bstep (se 1 (by rfl) ⟨1974815, by rfl⟩ : syracuseStep 2633087 = 3949631) B3949631
theorem B7021565 : Blo 2079435 7021565 := bstep (se 3 (by rfl) ⟨1316543, by rfl⟩ : syracuseStep 7021565 = 2633087) B2633087
theorem B4681043 : Blo 2079435 4681043 := bstep (se 1 (by rfl) ⟨3510782, by rfl⟩ : syracuseStep 4681043 = 7021565) B7021565
theorem B3120695 : Blo 2079435 3120695 := bstep (se 1 (by rfl) ⟨2340521, by rfl⟩ : syracuseStep 3120695 = 4681043) B4681043
theorem B2080463 : Blo 2079435 2080463 := bstep (se 1 (by rfl) ⟨1560347, by rfl⟩ : syracuseStep 2080463 = 3120695) B3120695
theorem B3120701 : Blo 2079435 3120701 := bbase (se 3 (by rfl) ⟨585131, by rfl⟩ : syracuseStep 3120701 = 1170263) (by norm_num)
theorem B2080467 : Blo 2079435 2080467 := bstep (se 1 (by rfl) ⟨1560350, by rfl⟩ : syracuseStep 2080467 = 3120701) B3120701
theorem B4681061 : Blo 2079435 4681061 := bbase (se 4 (by rfl) ⟨438849, by rfl⟩ : syracuseStep 4681061 = 877699) (by norm_num)
theorem B3120707 : Blo 2079435 3120707 := bstep (se 1 (by rfl) ⟨2340530, by rfl⟩ : syracuseStep 3120707 = 4681061) B4681061
theorem B2080471 : Blo 2079435 2080471 := bstep (se 1 (by rfl) ⟨1560353, by rfl⟩ : syracuseStep 2080471 = 3120707) B3120707
theorem B5266205 : Blo 2079435 5266205 := bbase (se 3 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 5266205 = 1974827) (by norm_num)
theorem B3510803 : Blo 2079435 3510803 := bstep (se 1 (by rfl) ⟨2633102, by rfl⟩ : syracuseStep 3510803 = 5266205) B5266205
theorem B2340535 : Blo 2079435 2340535 := bstep (se 1 (by rfl) ⟨1755401, by rfl⟩ : syracuseStep 2340535 = 3510803) B3510803
theorem B3120713 : Blo 2079435 3120713 := bstep (se 2 (by rfl) ⟨1170267, by rfl⟩ : syracuseStep 3120713 = 2340535) B2340535
theorem B2080475 : Blo 2079435 2080475 := bstep (se 1 (by rfl) ⟨1560356, by rfl⟩ : syracuseStep 2080475 = 3120713) B3120713
theorem B3949661 : Blo 2079435 3949661 := bbase (se 3 (by rfl) ⟨740561, by rfl⟩ : syracuseStep 3949661 = 1481123) (by norm_num)
theorem B10532429 : Blo 2079435 10532429 := bstep (se 3 (by rfl) ⟨1974830, by rfl⟩ : syracuseStep 10532429 = 3949661) B3949661
theorem B7021619 : Blo 2079435 7021619 := bstep (se 1 (by rfl) ⟨5266214, by rfl⟩ : syracuseStep 7021619 = 10532429) B10532429
theorem B4681079 : Blo 2079435 4681079 := bstep (se 1 (by rfl) ⟨3510809, by rfl⟩ : syracuseStep 4681079 = 7021619) B7021619
theorem B3120719 : Blo 2079435 3120719 := bstep (se 1 (by rfl) ⟨2340539, by rfl⟩ : syracuseStep 3120719 = 4681079) B4681079
theorem B2080479 : Blo 2079435 2080479 := bstep (se 1 (by rfl) ⟨1560359, by rfl⟩ : syracuseStep 2080479 = 3120719) B3120719
theorem B3120725 : Blo 2079435 3120725 := bbase (se 8 (by rfl) ⟨18285, by rfl⟩ : syracuseStep 3120725 = 36571) (by norm_num)
theorem B2080483 : Blo 2079435 2080483 := bstep (se 1 (by rfl) ⟨1560362, by rfl⟩ : syracuseStep 2080483 = 3120725) B3120725
theorem B8886773 : Blo 2079435 8886773 := bbase (se 5 (by rfl) ⟨416567, by rfl⟩ : syracuseStep 8886773 = 833135) (by norm_num)
theorem B5924515 : Blo 2079435 5924515 := bstep (se 1 (by rfl) ⟨4443386, by rfl⟩ : syracuseStep 5924515 = 8886773) B8886773
theorem B7899353 : Blo 2079435 7899353 := bstep (se 2 (by rfl) ⟨2962257, by rfl⟩ : syracuseStep 7899353 = 5924515) B5924515
theorem B5266235 : Blo 2079435 5266235 := bstep (se 1 (by rfl) ⟨3949676, by rfl⟩ : syracuseStep 5266235 = 7899353) B7899353
theorem B3510823 : Blo 2079435 3510823 := bstep (se 1 (by rfl) ⟨2633117, by rfl⟩ : syracuseStep 3510823 = 5266235) B5266235
theorem B4681097 : Blo 2079435 4681097 := bstep (se 2 (by rfl) ⟨1755411, by rfl⟩ : syracuseStep 4681097 = 3510823) B3510823
theorem B3120731 : Blo 2079435 3120731 := bstep (se 1 (by rfl) ⟨2340548, by rfl⟩ : syracuseStep 3120731 = 4681097) B4681097
theorem B2080487 : Blo 2079435 2080487 := bstep (se 1 (by rfl) ⟨1560365, by rfl⟩ : syracuseStep 2080487 = 3120731) B3120731
theorem B2340553 : Blo 2079435 2340553 := bbase (se 2 (by rfl) ⟨877707, by rfl⟩ : syracuseStep 2340553 = 1755415) (by norm_num)
theorem B3120737 : Blo 2079435 3120737 := bstep (se 2 (by rfl) ⟨1170276, by rfl⟩ : syracuseStep 3120737 = 2340553) B2340553
theorem B2080491 : Blo 2079435 2080491 := bstep (se 1 (by rfl) ⟨1560368, by rfl⟩ : syracuseStep 2080491 = 3120737) B3120737
theorem B4998829 : Blo 2079435 4998829 := bbase (se 3 (by rfl) ⟨937280, by rfl⟩ : syracuseStep 4998829 = 1874561) (by norm_num)
theorem B6665105 : Blo 2079435 6665105 := bstep (se 2 (by rfl) ⟨2499414, by rfl⟩ : syracuseStep 6665105 = 4998829) B4998829
theorem B17773613 : Blo 2079435 17773613 := bstep (se 3 (by rfl) ⟨3332552, by rfl⟩ : syracuseStep 17773613 = 6665105) B6665105
theorem B11849075 : Blo 2079435 11849075 := bstep (se 1 (by rfl) ⟨8886806, by rfl⟩ : syracuseStep 11849075 = 17773613) B17773613
theorem B7899383 : Blo 2079435 7899383 := bstep (se 1 (by rfl) ⟨5924537, by rfl⟩ : syracuseStep 7899383 = 11849075) B11849075
theorem B5266255 : Blo 2079435 5266255 := bstep (se 1 (by rfl) ⟨3949691, by rfl⟩ : syracuseStep 5266255 = 7899383) B7899383
theorem B7021673 : Blo 2079435 7021673 := bstep (se 2 (by rfl) ⟨2633127, by rfl⟩ : syracuseStep 7021673 = 5266255) B5266255
theorem B4681115 : Blo 2079435 4681115 := bstep (se 1 (by rfl) ⟨3510836, by rfl⟩ : syracuseStep 4681115 = 7021673) B7021673
theorem B3120743 : Blo 2079435 3120743 := bstep (se 1 (by rfl) ⟨2340557, by rfl⟩ : syracuseStep 3120743 = 4681115) B4681115
theorem B2080495 : Blo 2079435 2080495 := bstep (se 1 (by rfl) ⟨1560371, by rfl⟩ : syracuseStep 2080495 = 3120743) B3120743
theorem B3120749 : Blo 2079435 3120749 := bbase (se 3 (by rfl) ⟨585140, by rfl⟩ : syracuseStep 3120749 = 1170281) (by norm_num)
theorem B2080499 : Blo 2079435 2080499 := bstep (se 1 (by rfl) ⟨1560374, by rfl⟩ : syracuseStep 2080499 = 3120749) B3120749
theorem B4681133 : Blo 2079435 4681133 := bbase (se 3 (by rfl) ⟨877712, by rfl⟩ : syracuseStep 4681133 = 1755425) (by norm_num)
theorem B3120755 : Blo 2079435 3120755 := bstep (se 1 (by rfl) ⟨2340566, by rfl⟩ : syracuseStep 3120755 = 4681133) B4681133
theorem B2080503 : Blo 2079435 2080503 := bstep (se 1 (by rfl) ⟨1560377, by rfl⟩ : syracuseStep 2080503 = 3120755) B3120755
theorem B3332573 : Blo 2079435 3332573 := bbase (se 3 (by rfl) ⟨624857, by rfl⟩ : syracuseStep 3332573 = 1249715) (by norm_num)
theorem B2221715 : Blo 2079435 2221715 := bstep (se 1 (by rfl) ⟨1666286, by rfl⟩ : syracuseStep 2221715 = 3332573) B3332573
theorem B5924573 : Blo 2079435 5924573 := bstep (se 3 (by rfl) ⟨1110857, by rfl⟩ : syracuseStep 5924573 = 2221715) B2221715
theorem B3949715 : Blo 2079435 3949715 := bstep (se 1 (by rfl) ⟨2962286, by rfl⟩ : syracuseStep 3949715 = 5924573) B5924573
theorem B2633143 : Blo 2079435 2633143 := bstep (se 1 (by rfl) ⟨1974857, by rfl⟩ : syracuseStep 2633143 = 3949715) B3949715
theorem B3510857 : Blo 2079435 3510857 := bstep (se 2 (by rfl) ⟨1316571, by rfl⟩ : syracuseStep 3510857 = 2633143) B2633143
theorem B2340571 : Blo 2079435 2340571 := bstep (se 1 (by rfl) ⟨1755428, by rfl⟩ : syracuseStep 2340571 = 3510857) B3510857
theorem B3120761 : Blo 2079435 3120761 := bstep (se 2 (by rfl) ⟨1170285, by rfl⟩ : syracuseStep 3120761 = 2340571) B2340571
theorem B2080507 : Blo 2079435 2080507 := bstep (se 1 (by rfl) ⟨1560380, by rfl⟩ : syracuseStep 2080507 = 3120761) B3120761
theorem B2108897 : Blo 2079435 2108897 := bbase (se 2 (by rfl) ⟨790836, by rfl⟩ : syracuseStep 2108897 = 1581673) (by norm_num)
theorem B89979605 : Blo 2079435 89979605 := bstep (se 7 (by rfl) ⟨1054448, by rfl⟩ : syracuseStep 89979605 = 2108897) B2108897
theorem B59986403 : Blo 2079435 59986403 := bstep (se 1 (by rfl) ⟨44989802, by rfl⟩ : syracuseStep 59986403 = 89979605) B89979605
theorem B39990935 : Blo 2079435 39990935 := bstep (se 1 (by rfl) ⟨29993201, by rfl⟩ : syracuseStep 39990935 = 59986403) B59986403
theorem B26660623 : Blo 2079435 26660623 := bstep (se 1 (by rfl) ⟨19995467, by rfl⟩ : syracuseStep 26660623 = 39990935) B39990935
theorem B35547497 : Blo 2079435 35547497 := bstep (se 2 (by rfl) ⟨13330311, by rfl⟩ : syracuseStep 35547497 = 26660623) B26660623
theorem B23698331 : Blo 2079435 23698331 := bstep (se 1 (by rfl) ⟨17773748, by rfl⟩ : syracuseStep 23698331 = 35547497) B35547497
theorem B15798887 : Blo 2079435 15798887 := bstep (se 1 (by rfl) ⟨11849165, by rfl⟩ : syracuseStep 15798887 = 23698331) B23698331
theorem B10532591 : Blo 2079435 10532591 := bstep (se 1 (by rfl) ⟨7899443, by rfl⟩ : syracuseStep 10532591 = 15798887) B15798887
theorem B7021727 : Blo 2079435 7021727 := bstep (se 1 (by rfl) ⟨5266295, by rfl⟩ : syracuseStep 7021727 = 10532591) B10532591
theorem B4681151 : Blo 2079435 4681151 := bstep (se 1 (by rfl) ⟨3510863, by rfl⟩ : syracuseStep 4681151 = 7021727) B7021727
theorem B3120767 : Blo 2079435 3120767 := bstep (se 1 (by rfl) ⟨2340575, by rfl⟩ : syracuseStep 3120767 = 4681151) B4681151
theorem B2080511 : Blo 2079435 2080511 := bstep (se 1 (by rfl) ⟨1560383, by rfl⟩ : syracuseStep 2080511 = 3120767) B3120767
theorem B3120773 : Blo 2079435 3120773 := bbase (se 4 (by rfl) ⟨292572, by rfl⟩ : syracuseStep 3120773 = 585145) (by norm_num)
theorem B2080515 : Blo 2079435 2080515 := bstep (se 1 (by rfl) ⟨1560386, by rfl⟩ : syracuseStep 2080515 = 3120773) B3120773
theorem B3510877 : Blo 2079435 3510877 := bbase (se 3 (by rfl) ⟨658289, by rfl⟩ : syracuseStep 3510877 = 1316579) (by norm_num)
theorem B4681169 : Blo 2079435 4681169 := bstep (se 2 (by rfl) ⟨1755438, by rfl⟩ : syracuseStep 4681169 = 3510877) B3510877
theorem B3120779 : Blo 2079435 3120779 := bstep (se 1 (by rfl) ⟨2340584, by rfl⟩ : syracuseStep 3120779 = 4681169) B4681169
theorem B2080519 : Blo 2079435 2080519 := bstep (se 1 (by rfl) ⟨1560389, by rfl⟩ : syracuseStep 2080519 = 3120779) B3120779
theorem B2340589 : Blo 2079435 2340589 := bbase (se 3 (by rfl) ⟨438860, by rfl⟩ : syracuseStep 2340589 = 877721) (by norm_num)
theorem B3120785 : Blo 2079435 3120785 := bstep (se 2 (by rfl) ⟨1170294, by rfl⟩ : syracuseStep 3120785 = 2340589) B2340589
theorem B2080523 : Blo 2079435 2080523 := bstep (se 1 (by rfl) ⟨1560392, by rfl⟩ : syracuseStep 2080523 = 3120785) B3120785
theorem B7021781 : Blo 2079435 7021781 := bbase (se 7 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 7021781 = 164573) (by norm_num)
theorem B4681187 : Blo 2079435 4681187 := bstep (se 1 (by rfl) ⟨3510890, by rfl⟩ : syracuseStep 4681187 = 7021781) B7021781
theorem B3120791 : Blo 2079435 3120791 := bstep (se 1 (by rfl) ⟨2340593, by rfl⟩ : syracuseStep 3120791 = 4681187) B4681187
theorem B2080527 : Blo 2079435 2080527 := bstep (se 1 (by rfl) ⟨1560395, by rfl⟩ : syracuseStep 2080527 = 3120791) B3120791
theorem B3120797 : Blo 2079435 3120797 := bbase (se 3 (by rfl) ⟨585149, by rfl⟩ : syracuseStep 3120797 = 1170299) (by norm_num)
theorem B2080531 : Blo 2079435 2080531 := bstep (se 1 (by rfl) ⟨1560398, by rfl⟩ : syracuseStep 2080531 = 3120797) B3120797
theorem B4681205 : Blo 2079435 4681205 := bbase (se 5 (by rfl) ⟨219431, by rfl⟩ : syracuseStep 4681205 = 438863) (by norm_num)
theorem B3120803 : Blo 2079435 3120803 := bstep (se 1 (by rfl) ⟨2340602, by rfl⟩ : syracuseStep 3120803 = 4681205) B4681205
theorem B2080535 : Blo 2079435 2080535 := bstep (se 1 (by rfl) ⟨1560401, by rfl⟩ : syracuseStep 2080535 = 3120803) B3120803
theorem B7600709 : Blo 2079435 7600709 := bbase (se 4 (by rfl) ⟨712566, by rfl⟩ : syracuseStep 7600709 = 1425133) (by norm_num)
theorem B5067139 : Blo 2079435 5067139 := bstep (se 1 (by rfl) ⟨3800354, by rfl⟩ : syracuseStep 5067139 = 7600709) B7600709
theorem B6756185 : Blo 2079435 6756185 := bstep (se 2 (by rfl) ⟨2533569, by rfl⟩ : syracuseStep 6756185 = 5067139) B5067139
theorem B4504123 : Blo 2079435 4504123 := bstep (se 1 (by rfl) ⟨3378092, by rfl⟩ : syracuseStep 4504123 = 6756185) B6756185
theorem B6005497 : Blo 2079435 6005497 := bstep (se 2 (by rfl) ⟨2252061, by rfl⟩ : syracuseStep 6005497 = 4504123) B4504123
theorem B8007329 : Blo 2079435 8007329 := bstep (se 2 (by rfl) ⟨3002748, by rfl⟩ : syracuseStep 8007329 = 6005497) B6005497
theorem B5338219 : Blo 2079435 5338219 := bstep (se 1 (by rfl) ⟨4003664, by rfl⟩ : syracuseStep 5338219 = 8007329) B8007329
theorem B7117625 : Blo 2079435 7117625 := bstep (se 2 (by rfl) ⟨2669109, by rfl⟩ : syracuseStep 7117625 = 5338219) B5338219
theorem B18980333 : Blo 2079435 18980333 := bstep (se 3 (by rfl) ⟨3558812, by rfl⟩ : syracuseStep 18980333 = 7117625) B7117625
theorem B12653555 : Blo 2079435 12653555 := bstep (se 1 (by rfl) ⟨9490166, by rfl⟩ : syracuseStep 12653555 = 18980333) B18980333
theorem B33742813 : Blo 2079435 33742813 := bstep (se 3 (by rfl) ⟨6326777, by rfl⟩ : syracuseStep 33742813 = 12653555) B12653555
theorem B44990417 : Blo 2079435 44990417 := bstep (se 2 (by rfl) ⟨16871406, by rfl⟩ : syracuseStep 44990417 = 33742813) B33742813
theorem B29993611 : Blo 2079435 29993611 := bstep (se 1 (by rfl) ⟨22495208, by rfl⟩ : syracuseStep 29993611 = 44990417) B44990417
theorem B39991481 : Blo 2079435 39991481 := bstep (se 2 (by rfl) ⟨14996805, by rfl⟩ : syracuseStep 39991481 = 29993611) B29993611
theorem B26660987 : Blo 2079435 26660987 := bstep (se 1 (by rfl) ⟨19995740, by rfl⟩ : syracuseStep 26660987 = 39991481) B39991481
theorem B17773991 : Blo 2079435 17773991 := bstep (se 1 (by rfl) ⟨13330493, by rfl⟩ : syracuseStep 17773991 = 26660987) B26660987
theorem B11849327 : Blo 2079435 11849327 := bstep (se 1 (by rfl) ⟨8886995, by rfl⟩ : syracuseStep 11849327 = 17773991) B17773991
theorem B7899551 : Blo 2079435 7899551 := bstep (se 1 (by rfl) ⟨5924663, by rfl⟩ : syracuseStep 7899551 = 11849327) B11849327
theorem B5266367 : Blo 2079435 5266367 := bstep (se 1 (by rfl) ⟨3949775, by rfl⟩ : syracuseStep 5266367 = 7899551) B7899551
theorem B3510911 : Blo 2079435 3510911 := bstep (se 1 (by rfl) ⟨2633183, by rfl⟩ : syracuseStep 3510911 = 5266367) B5266367
theorem B2340607 : Blo 2079435 2340607 := bstep (se 1 (by rfl) ⟨1755455, by rfl⟩ : syracuseStep 2340607 = 3510911) B3510911
theorem B3120809 : Blo 2079435 3120809 := bstep (se 2 (by rfl) ⟨1170303, by rfl⟩ : syracuseStep 3120809 = 2340607) B2340607
theorem B2080539 : Blo 2079435 2080539 := bstep (se 1 (by rfl) ⟨1560404, by rfl⟩ : syracuseStep 2080539 = 3120809) B3120809
theorem B2221753 : Blo 2079435 2221753 := bbase (se 2 (by rfl) ⟨833157, by rfl⟩ : syracuseStep 2221753 = 1666315) (by norm_num)
theorem B2962337 : Blo 2079435 2962337 := bstep (se 2 (by rfl) ⟨1110876, by rfl⟩ : syracuseStep 2962337 = 2221753) B2221753
theorem B7899565 : Blo 2079435 7899565 := bstep (se 3 (by rfl) ⟨1481168, by rfl⟩ : syracuseStep 7899565 = 2962337) B2962337
theorem B10532753 : Blo 2079435 10532753 := bstep (se 2 (by rfl) ⟨3949782, by rfl⟩ : syracuseStep 10532753 = 7899565) B7899565
theorem B7021835 : Blo 2079435 7021835 := bstep (se 1 (by rfl) ⟨5266376, by rfl⟩ : syracuseStep 7021835 = 10532753) B10532753
theorem B4681223 : Blo 2079435 4681223 := bstep (se 1 (by rfl) ⟨3510917, by rfl⟩ : syracuseStep 4681223 = 7021835) B7021835
theorem B3120815 : Blo 2079435 3120815 := bstep (se 1 (by rfl) ⟨2340611, by rfl⟩ : syracuseStep 3120815 = 4681223) B4681223
theorem B2080543 : Blo 2079435 2080543 := bstep (se 1 (by rfl) ⟨1560407, by rfl⟩ : syracuseStep 2080543 = 3120815) B3120815
theorem B3120821 : Blo 2079435 3120821 := bbase (se 5 (by rfl) ⟨146288, by rfl⟩ : syracuseStep 3120821 = 292577) (by norm_num)
theorem B2080547 : Blo 2079435 2080547 := bstep (se 1 (by rfl) ⟨1560410, by rfl⟩ : syracuseStep 2080547 = 3120821) B3120821
theorem B5266397 : Blo 2079435 5266397 := bbase (se 3 (by rfl) ⟨987449, by rfl⟩ : syracuseStep 5266397 = 1974899) (by norm_num)
theorem B3510931 : Blo 2079435 3510931 := bstep (se 1 (by rfl) ⟨2633198, by rfl⟩ : syracuseStep 3510931 = 5266397) B5266397
theorem B4681241 : Blo 2079435 4681241 := bstep (se 2 (by rfl) ⟨1755465, by rfl⟩ : syracuseStep 4681241 = 3510931) B3510931
theorem B3120827 : Blo 2079435 3120827 := bstep (se 1 (by rfl) ⟨2340620, by rfl⟩ : syracuseStep 3120827 = 4681241) B4681241
theorem B2080551 : Blo 2079435 2080551 := bstep (se 1 (by rfl) ⟨1560413, by rfl⟩ : syracuseStep 2080551 = 3120827) B3120827
theorem B2340625 : Blo 2079435 2340625 := bbase (se 2 (by rfl) ⟨877734, by rfl⟩ : syracuseStep 2340625 = 1755469) (by norm_num)
theorem B3120833 : Blo 2079435 3120833 := bstep (se 2 (by rfl) ⟨1170312, by rfl⟩ : syracuseStep 3120833 = 2340625) B2340625
theorem B2080555 : Blo 2079435 2080555 := bstep (se 1 (by rfl) ⟨1560416, by rfl⟩ : syracuseStep 2080555 = 3120833) B3120833
theorem B3949813 : Blo 2079435 3949813 := bbase (se 5 (by rfl) ⟨185147, by rfl⟩ : syracuseStep 3949813 = 370295) (by norm_num)
theorem B5266417 : Blo 2079435 5266417 := bstep (se 2 (by rfl) ⟨1974906, by rfl⟩ : syracuseStep 5266417 = 3949813) B3949813
theorem B7021889 : Blo 2079435 7021889 := bstep (se 2 (by rfl) ⟨2633208, by rfl⟩ : syracuseStep 7021889 = 5266417) B5266417
theorem B4681259 : Blo 2079435 4681259 := bstep (se 1 (by rfl) ⟨3510944, by rfl⟩ : syracuseStep 4681259 = 7021889) B7021889
theorem B3120839 : Blo 2079435 3120839 := bstep (se 1 (by rfl) ⟨2340629, by rfl⟩ : syracuseStep 3120839 = 4681259) B4681259
theorem B2080559 : Blo 2079435 2080559 := bstep (se 1 (by rfl) ⟨1560419, by rfl⟩ : syracuseStep 2080559 = 3120839) B3120839
theorem B3120845 : Blo 2079435 3120845 := bbase (se 3 (by rfl) ⟨585158, by rfl⟩ : syracuseStep 3120845 = 1170317) (by norm_num)
theorem B2080563 : Blo 2079435 2080563 := bstep (se 1 (by rfl) ⟨1560422, by rfl⟩ : syracuseStep 2080563 = 3120845) B3120845
theorem B4681277 : Blo 2079435 4681277 := bbase (se 3 (by rfl) ⟨877739, by rfl⟩ : syracuseStep 4681277 = 1755479) (by norm_num)
theorem B3120851 : Blo 2079435 3120851 := bstep (se 1 (by rfl) ⟨2340638, by rfl⟩ : syracuseStep 3120851 = 4681277) B4681277
theorem B2080567 : Blo 2079435 2080567 := bstep (se 1 (by rfl) ⟨1560425, by rfl⟩ : syracuseStep 2080567 = 3120851) B3120851
theorem B3510965 : Blo 2079435 3510965 := bbase (se 5 (by rfl) ⟨164576, by rfl⟩ : syracuseStep 3510965 = 329153) (by norm_num)
theorem B2340643 : Blo 2079435 2340643 := bstep (se 1 (by rfl) ⟨1755482, by rfl⟩ : syracuseStep 2340643 = 3510965) B3510965
theorem B3120857 : Blo 2079435 3120857 := bstep (se 2 (by rfl) ⟨1170321, by rfl⟩ : syracuseStep 3120857 = 2340643) B2340643
theorem B2080571 : Blo 2079435 2080571 := bstep (se 1 (by rfl) ⟨1560428, by rfl⟩ : syracuseStep 2080571 = 3120857) B3120857
theorem B3163445 : Blo 2079435 3163445 := bbase (se 5 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 3163445 = 296573) (by norm_num)
theorem B2108963 : Blo 2079435 2108963 := bstep (se 1 (by rfl) ⟨1581722, by rfl⟩ : syracuseStep 2108963 = 3163445) B3163445
theorem B5623901 : Blo 2079435 5623901 := bstep (se 3 (by rfl) ⟨1054481, by rfl⟩ : syracuseStep 5623901 = 2108963) B2108963
theorem B3749267 : Blo 2079435 3749267 := bstep (se 1 (by rfl) ⟨2811950, by rfl⟩ : syracuseStep 3749267 = 5623901) B5623901
theorem B2499511 : Blo 2079435 2499511 := bstep (se 1 (by rfl) ⟨1874633, by rfl⟩ : syracuseStep 2499511 = 3749267) B3749267
theorem B3332681 : Blo 2079435 3332681 := bstep (se 2 (by rfl) ⟨1249755, by rfl⟩ : syracuseStep 3332681 = 2499511) B2499511
theorem B2221787 : Blo 2079435 2221787 := bstep (se 1 (by rfl) ⟨1666340, by rfl⟩ : syracuseStep 2221787 = 3332681) B3332681
theorem B5924765 : Blo 2079435 5924765 := bstep (se 3 (by rfl) ⟨1110893, by rfl⟩ : syracuseStep 5924765 = 2221787) B2221787
theorem B15799373 : Blo 2079435 15799373 := bstep (se 3 (by rfl) ⟨2962382, by rfl⟩ : syracuseStep 15799373 = 5924765) B5924765
theorem B10532915 : Blo 2079435 10532915 := bstep (se 1 (by rfl) ⟨7899686, by rfl⟩ : syracuseStep 10532915 = 15799373) B15799373
theorem B7021943 : Blo 2079435 7021943 := bstep (se 1 (by rfl) ⟨5266457, by rfl⟩ : syracuseStep 7021943 = 10532915) B10532915
theorem B4681295 : Blo 2079435 4681295 := bstep (se 1 (by rfl) ⟨3510971, by rfl⟩ : syracuseStep 4681295 = 7021943) B7021943
theorem B3120863 : Blo 2079435 3120863 := bstep (se 1 (by rfl) ⟨2340647, by rfl⟩ : syracuseStep 3120863 = 4681295) B4681295
theorem B2080575 : Blo 2079435 2080575 := bstep (se 1 (by rfl) ⟨1560431, by rfl⟩ : syracuseStep 2080575 = 3120863) B3120863
theorem B3120869 : Blo 2079435 3120869 := bbase (se 4 (by rfl) ⟨292581, by rfl⟩ : syracuseStep 3120869 = 585163) (by norm_num)
theorem B2080579 : Blo 2079435 2080579 := bstep (se 1 (by rfl) ⟨1560434, by rfl⟩ : syracuseStep 2080579 = 3120869) B3120869
theorem B5924789 : Blo 2079435 5924789 := bbase (se 5 (by rfl) ⟨277724, by rfl⟩ : syracuseStep 5924789 = 555449) (by norm_num)
theorem B3949859 : Blo 2079435 3949859 := bstep (se 1 (by rfl) ⟨2962394, by rfl⟩ : syracuseStep 3949859 = 5924789) B5924789
theorem B2633239 : Blo 2079435 2633239 := bstep (se 1 (by rfl) ⟨1974929, by rfl⟩ : syracuseStep 2633239 = 3949859) B3949859
theorem B3510985 : Blo 2079435 3510985 := bstep (se 2 (by rfl) ⟨1316619, by rfl⟩ : syracuseStep 3510985 = 2633239) B2633239
theorem B4681313 : Blo 2079435 4681313 := bstep (se 2 (by rfl) ⟨1755492, by rfl⟩ : syracuseStep 4681313 = 3510985) B3510985
theorem B3120875 : Blo 2079435 3120875 := bstep (se 1 (by rfl) ⟨2340656, by rfl⟩ : syracuseStep 3120875 = 4681313) B4681313
theorem B2080583 : Blo 2079435 2080583 := bstep (se 1 (by rfl) ⟨1560437, by rfl⟩ : syracuseStep 2080583 = 3120875) B3120875
theorem B2340661 : Blo 2079435 2340661 := bbase (se 5 (by rfl) ⟨109718, by rfl⟩ : syracuseStep 2340661 = 219437) (by norm_num)
theorem B3120881 : Blo 2079435 3120881 := bstep (se 2 (by rfl) ⟨1170330, by rfl⟩ : syracuseStep 3120881 = 2340661) B2340661
theorem B2080587 : Blo 2079435 2080587 := bstep (se 1 (by rfl) ⟨1560440, by rfl⟩ : syracuseStep 2080587 = 3120881) B3120881
theorem B2633249 : Blo 2079435 2633249 := bbase (se 2 (by rfl) ⟨987468, by rfl⟩ : syracuseStep 2633249 = 1974937) (by norm_num)
theorem B7021997 : Blo 2079435 7021997 := bstep (se 3 (by rfl) ⟨1316624, by rfl⟩ : syracuseStep 7021997 = 2633249) B2633249
theorem B4681331 : Blo 2079435 4681331 := bstep (se 1 (by rfl) ⟨3510998, by rfl⟩ : syracuseStep 4681331 = 7021997) B7021997
theorem B3120887 : Blo 2079435 3120887 := bstep (se 1 (by rfl) ⟨2340665, by rfl⟩ : syracuseStep 3120887 = 4681331) B4681331
theorem B2080591 : Blo 2079435 2080591 := bstep (se 1 (by rfl) ⟨1560443, by rfl⟩ : syracuseStep 2080591 = 3120887) B3120887
theorem B3120893 : Blo 2079435 3120893 := bbase (se 3 (by rfl) ⟨585167, by rfl⟩ : syracuseStep 3120893 = 1170335) (by norm_num)
theorem B2080595 : Blo 2079435 2080595 := bstep (se 1 (by rfl) ⟨1560446, by rfl⟩ : syracuseStep 2080595 = 3120893) B3120893
theorem B4681349 : Blo 2079435 4681349 := bbase (se 4 (by rfl) ⟨438876, by rfl⟩ : syracuseStep 4681349 = 877753) (by norm_num)
theorem B3120899 : Blo 2079435 3120899 := bstep (se 1 (by rfl) ⟨2340674, by rfl⟩ : syracuseStep 3120899 = 4681349) B4681349
theorem B2080599 : Blo 2079435 2080599 := bstep (se 1 (by rfl) ⟨1560449, by rfl⟩ : syracuseStep 2080599 = 3120899) B3120899
theorem B2499545 : Blo 2079435 2499545 := bbase (se 2 (by rfl) ⟨937329, by rfl⟩ : syracuseStep 2499545 = 1874659) (by norm_num)
theorem B6665453 : Blo 2079435 6665453 := bstep (se 3 (by rfl) ⟨1249772, by rfl⟩ : syracuseStep 6665453 = 2499545) B2499545
theorem B4443635 : Blo 2079435 4443635 := bstep (se 1 (by rfl) ⟨3332726, by rfl⟩ : syracuseStep 4443635 = 6665453) B6665453
theorem B2962423 : Blo 2079435 2962423 := bstep (se 1 (by rfl) ⟨2221817, by rfl⟩ : syracuseStep 2962423 = 4443635) B4443635
theorem B3949897 : Blo 2079435 3949897 := bstep (se 2 (by rfl) ⟨1481211, by rfl⟩ : syracuseStep 3949897 = 2962423) B2962423
theorem B5266529 : Blo 2079435 5266529 := bstep (se 2 (by rfl) ⟨1974948, by rfl⟩ : syracuseStep 5266529 = 3949897) B3949897
theorem B3511019 : Blo 2079435 3511019 := bstep (se 1 (by rfl) ⟨2633264, by rfl⟩ : syracuseStep 3511019 = 5266529) B5266529
theorem B2340679 : Blo 2079435 2340679 := bstep (se 1 (by rfl) ⟨1755509, by rfl⟩ : syracuseStep 2340679 = 3511019) B3511019
theorem B3120905 : Blo 2079435 3120905 := bstep (se 2 (by rfl) ⟨1170339, by rfl⟩ : syracuseStep 3120905 = 2340679) B2340679
theorem B2080603 : Blo 2079435 2080603 := bstep (se 1 (by rfl) ⟨1560452, by rfl⟩ : syracuseStep 2080603 = 3120905) B3120905
theorem B10533077 : Blo 2079435 10533077 := bbase (se 7 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 10533077 = 246869) (by norm_num)
theorem B7022051 : Blo 2079435 7022051 := bstep (se 1 (by rfl) ⟨5266538, by rfl⟩ : syracuseStep 7022051 = 10533077) B10533077
theorem B4681367 : Blo 2079435 4681367 := bstep (se 1 (by rfl) ⟨3511025, by rfl⟩ : syracuseStep 4681367 = 7022051) B7022051
theorem B3120911 : Blo 2079435 3120911 := bstep (se 1 (by rfl) ⟨2340683, by rfl⟩ : syracuseStep 3120911 = 4681367) B4681367
theorem B2080607 : Blo 2079435 2080607 := bstep (se 1 (by rfl) ⟨1560455, by rfl⟩ : syracuseStep 2080607 = 3120911) B3120911
theorem B3120917 : Blo 2079435 3120917 := bbase (se 6 (by rfl) ⟨73146, by rfl⟩ : syracuseStep 3120917 = 146293) (by norm_num)
theorem B2080611 : Blo 2079435 2080611 := bstep (se 1 (by rfl) ⟨1560458, by rfl⟩ : syracuseStep 2080611 = 3120917) B3120917
theorem B21353653 : Blo 2079435 21353653 := bbase (se 5 (by rfl) ⟨1000952, by rfl⟩ : syracuseStep 21353653 = 2001905) (by norm_num)
theorem B28471537 : Blo 2079435 28471537 := bstep (se 2 (by rfl) ⟨10676826, by rfl⟩ : syracuseStep 28471537 = 21353653) B21353653
theorem B37962049 : Blo 2079435 37962049 := bstep (se 2 (by rfl) ⟨14235768, by rfl⟩ : syracuseStep 37962049 = 28471537) B28471537
theorem B50616065 : Blo 2079435 50616065 := bstep (se 2 (by rfl) ⟨18981024, by rfl⟩ : syracuseStep 50616065 = 37962049) B37962049
theorem B33744043 : Blo 2079435 33744043 := bstep (se 1 (by rfl) ⟨25308032, by rfl⟩ : syracuseStep 33744043 = 50616065) B50616065
theorem B44992057 : Blo 2079435 44992057 := bstep (se 2 (by rfl) ⟨16872021, by rfl⟩ : syracuseStep 44992057 = 33744043) B33744043
theorem B59989409 : Blo 2079435 59989409 := bstep (se 2 (by rfl) ⟨22496028, by rfl⟩ : syracuseStep 59989409 = 44992057) B44992057
theorem B39992939 : Blo 2079435 39992939 := bstep (se 1 (by rfl) ⟨29994704, by rfl⟩ : syracuseStep 39992939 = 59989409) B59989409
theorem B26661959 : Blo 2079435 26661959 := bstep (se 1 (by rfl) ⟨19996469, by rfl⟩ : syracuseStep 26661959 = 39992939) B39992939
theorem B17774639 : Blo 2079435 17774639 := bstep (se 1 (by rfl) ⟨13330979, by rfl⟩ : syracuseStep 17774639 = 26661959) B26661959
theorem B11849759 : Blo 2079435 11849759 := bstep (se 1 (by rfl) ⟨8887319, by rfl⟩ : syracuseStep 11849759 = 17774639) B17774639
theorem B7899839 : Blo 2079435 7899839 := bstep (se 1 (by rfl) ⟨5924879, by rfl⟩ : syracuseStep 7899839 = 11849759) B11849759
theorem B5266559 : Blo 2079435 5266559 := bstep (se 1 (by rfl) ⟨3949919, by rfl⟩ : syracuseStep 5266559 = 7899839) B7899839
theorem B3511039 : Blo 2079435 3511039 := bstep (se 1 (by rfl) ⟨2633279, by rfl⟩ : syracuseStep 3511039 = 5266559) B5266559
theorem B4681385 : Blo 2079435 4681385 := bstep (se 2 (by rfl) ⟨1755519, by rfl⟩ : syracuseStep 4681385 = 3511039) B3511039
theorem B3120923 : Blo 2079435 3120923 := bstep (se 1 (by rfl) ⟨2340692, by rfl⟩ : syracuseStep 3120923 = 4681385) B4681385
theorem B2080615 : Blo 2079435 2080615 := bstep (se 1 (by rfl) ⟨1560461, by rfl⟩ : syracuseStep 2080615 = 3120923) B3120923
theorem B2340697 : Blo 2079435 2340697 := bbase (se 2 (by rfl) ⟨877761, by rfl⟩ : syracuseStep 2340697 = 1755523) (by norm_num)
theorem B3120929 : Blo 2079435 3120929 := bstep (se 2 (by rfl) ⟨1170348, by rfl⟩ : syracuseStep 3120929 = 2340697) B2340697
theorem B2080619 : Blo 2079435 2080619 := bstep (se 1 (by rfl) ⟨1560464, by rfl⟩ : syracuseStep 2080619 = 3120929) B3120929
theorem B4443677 : Blo 2079435 4443677 := bbase (se 3 (by rfl) ⟨833189, by rfl⟩ : syracuseStep 4443677 = 1666379) (by norm_num)
theorem B2962451 : Blo 2079435 2962451 := bstep (se 1 (by rfl) ⟨2221838, by rfl⟩ : syracuseStep 2962451 = 4443677) B4443677
theorem B7899869 : Blo 2079435 7899869 := bstep (se 3 (by rfl) ⟨1481225, by rfl⟩ : syracuseStep 7899869 = 2962451) B2962451
theorem B5266579 : Blo 2079435 5266579 := bstep (se 1 (by rfl) ⟨3949934, by rfl⟩ : syracuseStep 5266579 = 7899869) B7899869
theorem B7022105 : Blo 2079435 7022105 := bstep (se 2 (by rfl) ⟨2633289, by rfl⟩ : syracuseStep 7022105 = 5266579) B5266579
theorem B4681403 : Blo 2079435 4681403 := bstep (se 1 (by rfl) ⟨3511052, by rfl⟩ : syracuseStep 4681403 = 7022105) B7022105
theorem B3120935 : Blo 2079435 3120935 := bstep (se 1 (by rfl) ⟨2340701, by rfl⟩ : syracuseStep 3120935 = 4681403) B4681403
theorem B2080623 : Blo 2079435 2080623 := bstep (se 1 (by rfl) ⟨1560467, by rfl⟩ : syracuseStep 2080623 = 3120935) B3120935
theorem B3120941 : Blo 2079435 3120941 := bbase (se 3 (by rfl) ⟨585176, by rfl⟩ : syracuseStep 3120941 = 1170353) (by norm_num)
theorem B2080627 : Blo 2079435 2080627 := bstep (se 1 (by rfl) ⟨1560470, by rfl⟩ : syracuseStep 2080627 = 3120941) B3120941
theorem B4681421 : Blo 2079435 4681421 := bbase (se 3 (by rfl) ⟨877766, by rfl⟩ : syracuseStep 4681421 = 1755533) (by norm_num)
theorem B3120947 : Blo 2079435 3120947 := bstep (se 1 (by rfl) ⟨2340710, by rfl⟩ : syracuseStep 3120947 = 4681421) B4681421
theorem B2080631 : Blo 2079435 2080631 := bstep (se 1 (by rfl) ⟨1560473, by rfl⟩ : syracuseStep 2080631 = 3120947) B3120947
theorem B2633305 : Blo 2079435 2633305 := bbase (se 2 (by rfl) ⟨987489, by rfl⟩ : syracuseStep 2633305 = 1974979) (by norm_num)
theorem B3511073 : Blo 2079435 3511073 := bstep (se 2 (by rfl) ⟨1316652, by rfl⟩ : syracuseStep 3511073 = 2633305) B2633305
theorem B2340715 : Blo 2079435 2340715 := bstep (se 1 (by rfl) ⟨1755536, by rfl⟩ : syracuseStep 2340715 = 3511073) B3511073
theorem B3120953 : Blo 2079435 3120953 := bstep (se 2 (by rfl) ⟨1170357, by rfl⟩ : syracuseStep 3120953 = 2340715) B2340715
theorem B2080635 : Blo 2079435 2080635 := bstep (se 1 (by rfl) ⟨1560476, by rfl⟩ : syracuseStep 2080635 = 3120953) B3120953
theorem B3163541 : Blo 2079435 3163541 := bbase (se 6 (by rfl) ⟨74145, by rfl⟩ : syracuseStep 3163541 = 148291) (by norm_num)
theorem B8436109 : Blo 2079435 8436109 := bstep (se 3 (by rfl) ⟨1581770, by rfl⟩ : syracuseStep 8436109 = 3163541) B3163541
theorem B11248145 : Blo 2079435 11248145 := bstep (se 2 (by rfl) ⟨4218054, by rfl⟩ : syracuseStep 11248145 = 8436109) B8436109
theorem B7498763 : Blo 2079435 7498763 := bstep (se 1 (by rfl) ⟨5624072, by rfl⟩ : syracuseStep 7498763 = 11248145) B11248145
theorem B4999175 : Blo 2079435 4999175 := bstep (se 1 (by rfl) ⟨3749381, by rfl⟩ : syracuseStep 4999175 = 7498763) B7498763
theorem B3332783 : Blo 2079435 3332783 := bstep (se 1 (by rfl) ⟨2499587, by rfl⟩ : syracuseStep 3332783 = 4999175) B4999175
theorem B8887421 : Blo 2079435 8887421 := bstep (se 3 (by rfl) ⟨1666391, by rfl⟩ : syracuseStep 8887421 = 3332783) B3332783
theorem B23699789 : Blo 2079435 23699789 := bstep (se 3 (by rfl) ⟨4443710, by rfl⟩ : syracuseStep 23699789 = 8887421) B8887421
theorem B15799859 : Blo 2079435 15799859 := bstep (se 1 (by rfl) ⟨11849894, by rfl⟩ : syracuseStep 15799859 = 23699789) B23699789
theorem B10533239 : Blo 2079435 10533239 := bstep (se 1 (by rfl) ⟨7899929, by rfl⟩ : syracuseStep 10533239 = 15799859) B15799859
theorem B7022159 : Blo 2079435 7022159 := bstep (se 1 (by rfl) ⟨5266619, by rfl⟩ : syracuseStep 7022159 = 10533239) B10533239
theorem B4681439 : Blo 2079435 4681439 := bstep (se 1 (by rfl) ⟨3511079, by rfl⟩ : syracuseStep 4681439 = 7022159) B7022159
theorem B3120959 : Blo 2079435 3120959 := bstep (se 1 (by rfl) ⟨2340719, by rfl⟩ : syracuseStep 3120959 = 4681439) B4681439
theorem B2080639 : Blo 2079435 2080639 := bstep (se 1 (by rfl) ⟨1560479, by rfl⟩ : syracuseStep 2080639 = 3120959) B3120959
theorem B3120965 : Blo 2079435 3120965 := bbase (se 4 (by rfl) ⟨292590, by rfl⟩ : syracuseStep 3120965 = 585181) (by norm_num)
theorem B2080643 : Blo 2079435 2080643 := bstep (se 1 (by rfl) ⟨1560482, by rfl⟩ : syracuseStep 2080643 = 3120965) B3120965
theorem B3511093 : Blo 2079435 3511093 := bbase (se 5 (by rfl) ⟨164582, by rfl⟩ : syracuseStep 3511093 = 329165) (by norm_num)
theorem B4681457 : Blo 2079435 4681457 := bstep (se 2 (by rfl) ⟨1755546, by rfl⟩ : syracuseStep 4681457 = 3511093) B3511093
theorem B3120971 : Blo 2079435 3120971 := bstep (se 1 (by rfl) ⟨2340728, by rfl⟩ : syracuseStep 3120971 = 4681457) B4681457
theorem B2080647 : Blo 2079435 2080647 := bstep (se 1 (by rfl) ⟨1560485, by rfl⟩ : syracuseStep 2080647 = 3120971) B3120971
theorem B2340733 : Blo 2079435 2340733 := bbase (se 3 (by rfl) ⟨438887, by rfl⟩ : syracuseStep 2340733 = 877775) (by norm_num)
theorem B3120977 : Blo 2079435 3120977 := bstep (se 2 (by rfl) ⟨1170366, by rfl⟩ : syracuseStep 3120977 = 2340733) B2340733
theorem B2080651 : Blo 2079435 2080651 := bstep (se 1 (by rfl) ⟨1560488, by rfl⟩ : syracuseStep 2080651 = 3120977) B3120977
theorem B7022213 : Blo 2079435 7022213 := bbase (se 4 (by rfl) ⟨658332, by rfl⟩ : syracuseStep 7022213 = 1316665) (by norm_num)
theorem B4681475 : Blo 2079435 4681475 := bstep (se 1 (by rfl) ⟨3511106, by rfl⟩ : syracuseStep 4681475 = 7022213) B7022213
theorem B3120983 : Blo 2079435 3120983 := bstep (se 1 (by rfl) ⟨2340737, by rfl⟩ : syracuseStep 3120983 = 4681475) B4681475
theorem B2080655 : Blo 2079435 2080655 := bstep (se 1 (by rfl) ⟨1560491, by rfl⟩ : syracuseStep 2080655 = 3120983) B3120983
theorem B3120989 : Blo 2079435 3120989 := bbase (se 3 (by rfl) ⟨585185, by rfl⟩ : syracuseStep 3120989 = 1170371) (by norm_num)
theorem B2080659 : Blo 2079435 2080659 := bstep (se 1 (by rfl) ⟨1560494, by rfl⟩ : syracuseStep 2080659 = 3120989) B3120989
theorem B4681493 : Blo 2079435 4681493 := bbase (se 6 (by rfl) ⟨109722, by rfl⟩ : syracuseStep 4681493 = 219445) (by norm_num)
theorem B3120995 : Blo 2079435 3120995 := bstep (se 1 (by rfl) ⟨2340746, by rfl⟩ : syracuseStep 3120995 = 4681493) B4681493
theorem B2080663 : Blo 2079435 2080663 := bstep (se 1 (by rfl) ⟨1560497, by rfl⟩ : syracuseStep 2080663 = 3120995) B3120995
theorem B7900037 : Blo 2079435 7900037 := bbase (se 4 (by rfl) ⟨740628, by rfl⟩ : syracuseStep 7900037 = 1481257) (by norm_num)
theorem B5266691 : Blo 2079435 5266691 := bstep (se 1 (by rfl) ⟨3950018, by rfl⟩ : syracuseStep 5266691 = 7900037) B7900037
theorem B3511127 : Blo 2079435 3511127 := bstep (se 1 (by rfl) ⟨2633345, by rfl⟩ : syracuseStep 3511127 = 5266691) B5266691
theorem B2340751 : Blo 2079435 2340751 := bstep (se 1 (by rfl) ⟨1755563, by rfl⟩ : syracuseStep 2340751 = 3511127) B3511127
theorem B3121001 : Blo 2079435 3121001 := bstep (se 2 (by rfl) ⟨1170375, by rfl⟩ : syracuseStep 3121001 = 2340751) B2340751
theorem B2080667 : Blo 2079435 2080667 := bstep (se 1 (by rfl) ⟨1560500, by rfl⟩ : syracuseStep 2080667 = 3121001) B3121001
theorem B6665669 : Blo 2079435 6665669 := bbase (se 4 (by rfl) ⟨624906, by rfl⟩ : syracuseStep 6665669 = 1249813) (by norm_num)
theorem B4443779 : Blo 2079435 4443779 := bstep (se 1 (by rfl) ⟨3332834, by rfl⟩ : syracuseStep 4443779 = 6665669) B6665669
theorem B11850077 : Blo 2079435 11850077 := bstep (se 3 (by rfl) ⟨2221889, by rfl⟩ : syracuseStep 11850077 = 4443779) B4443779
theorem B7900051 : Blo 2079435 7900051 := bstep (se 1 (by rfl) ⟨5925038, by rfl⟩ : syracuseStep 7900051 = 11850077) B11850077
theorem B10533401 : Blo 2079435 10533401 := bstep (se 2 (by rfl) ⟨3950025, by rfl⟩ : syracuseStep 10533401 = 7900051) B7900051
theorem B7022267 : Blo 2079435 7022267 := bstep (se 1 (by rfl) ⟨5266700, by rfl⟩ : syracuseStep 7022267 = 10533401) B10533401
theorem B4681511 : Blo 2079435 4681511 := bstep (se 1 (by rfl) ⟨3511133, by rfl⟩ : syracuseStep 4681511 = 7022267) B7022267
theorem B3121007 : Blo 2079435 3121007 := bstep (se 1 (by rfl) ⟨2340755, by rfl⟩ : syracuseStep 3121007 = 4681511) B4681511
theorem B2080671 : Blo 2079435 2080671 := bstep (se 1 (by rfl) ⟨1560503, by rfl⟩ : syracuseStep 2080671 = 3121007) B3121007
theorem B3121013 : Blo 2079435 3121013 := bbase (se 5 (by rfl) ⟨146297, by rfl⟩ : syracuseStep 3121013 = 292595) (by norm_num)
theorem B2080675 : Blo 2079435 2080675 := bstep (se 1 (by rfl) ⟨1560506, by rfl⟩ : syracuseStep 2080675 = 3121013) B3121013
theorem B4443797 : Blo 2079435 4443797 := bbase (se 6 (by rfl) ⟨104151, by rfl⟩ : syracuseStep 4443797 = 208303) (by norm_num)
theorem B2962531 : Blo 2079435 2962531 := bstep (se 1 (by rfl) ⟨2221898, by rfl⟩ : syracuseStep 2962531 = 4443797) B4443797
theorem B3950041 : Blo 2079435 3950041 := bstep (se 2 (by rfl) ⟨1481265, by rfl⟩ : syracuseStep 3950041 = 2962531) B2962531
theorem B5266721 : Blo 2079435 5266721 := bstep (se 2 (by rfl) ⟨1975020, by rfl⟩ : syracuseStep 5266721 = 3950041) B3950041
theorem B3511147 : Blo 2079435 3511147 := bstep (se 1 (by rfl) ⟨2633360, by rfl⟩ : syracuseStep 3511147 = 5266721) B5266721
theorem B4681529 : Blo 2079435 4681529 := bstep (se 2 (by rfl) ⟨1755573, by rfl⟩ : syracuseStep 4681529 = 3511147) B3511147
theorem B3121019 : Blo 2079435 3121019 := bstep (se 1 (by rfl) ⟨2340764, by rfl⟩ : syracuseStep 3121019 = 4681529) B4681529
theorem B2080679 : Blo 2079435 2080679 := bstep (se 1 (by rfl) ⟨1560509, by rfl⟩ : syracuseStep 2080679 = 3121019) B3121019
theorem B2340769 : Blo 2079435 2340769 := bbase (se 2 (by rfl) ⟨877788, by rfl⟩ : syracuseStep 2340769 = 1755577) (by norm_num)
theorem B3121025 : Blo 2079435 3121025 := bstep (se 2 (by rfl) ⟨1170384, by rfl⟩ : syracuseStep 3121025 = 2340769) B2340769
theorem B2080683 : Blo 2079435 2080683 := bstep (se 1 (by rfl) ⟨1560512, by rfl⟩ : syracuseStep 2080683 = 3121025) B3121025
theorem B5266741 : Blo 2079435 5266741 := bbase (se 5 (by rfl) ⟨246878, by rfl⟩ : syracuseStep 5266741 = 493757) (by norm_num)
theorem B7022321 : Blo 2079435 7022321 := bstep (se 2 (by rfl) ⟨2633370, by rfl⟩ : syracuseStep 7022321 = 5266741) B5266741
theorem B4681547 : Blo 2079435 4681547 := bstep (se 1 (by rfl) ⟨3511160, by rfl⟩ : syracuseStep 4681547 = 7022321) B7022321
theorem B3121031 : Blo 2079435 3121031 := bstep (se 1 (by rfl) ⟨2340773, by rfl⟩ : syracuseStep 3121031 = 4681547) B4681547
theorem B2080687 : Blo 2079435 2080687 := bstep (se 1 (by rfl) ⟨1560515, by rfl⟩ : syracuseStep 2080687 = 3121031) B3121031
theorem B3121037 : Blo 2079435 3121037 := bbase (se 3 (by rfl) ⟨585194, by rfl⟩ : syracuseStep 3121037 = 1170389) (by norm_num)
theorem B2080691 : Blo 2079435 2080691 := bstep (se 1 (by rfl) ⟨1560518, by rfl⟩ : syracuseStep 2080691 = 3121037) B3121037
theorem B4681565 : Blo 2079435 4681565 := bbase (se 3 (by rfl) ⟨877793, by rfl⟩ : syracuseStep 4681565 = 1755587) (by norm_num)
theorem B3121043 : Blo 2079435 3121043 := bstep (se 1 (by rfl) ⟨2340782, by rfl⟩ : syracuseStep 3121043 = 4681565) B4681565
theorem B2080695 : Blo 2079435 2080695 := bstep (se 1 (by rfl) ⟨1560521, by rfl⟩ : syracuseStep 2080695 = 3121043) B3121043
theorem B3511181 : Blo 2079435 3511181 := bbase (se 3 (by rfl) ⟨658346, by rfl⟩ : syracuseStep 3511181 = 1316693) (by norm_num)
theorem B2340787 : Blo 2079435 2340787 := bstep (se 1 (by rfl) ⟨1755590, by rfl⟩ : syracuseStep 2340787 = 3511181) B3511181
theorem B3121049 : Blo 2079435 3121049 := bstep (se 2 (by rfl) ⟨1170393, by rfl⟩ : syracuseStep 3121049 = 2340787) B2340787
theorem B2080699 : Blo 2079435 2080699 := bstep (se 1 (by rfl) ⟨1560524, by rfl⟩ : syracuseStep 2080699 = 3121049) B3121049
theorem B5624245 : Blo 2079435 5624245 := bbase (se 5 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 5624245 = 527273) (by norm_num)
theorem B7498993 : Blo 2079435 7498993 := bstep (se 2 (by rfl) ⟨2812122, by rfl⟩ : syracuseStep 7498993 = 5624245) B5624245
theorem B9998657 : Blo 2079435 9998657 := bstep (se 2 (by rfl) ⟨3749496, by rfl⟩ : syracuseStep 9998657 = 7498993) B7498993
theorem B6665771 : Blo 2079435 6665771 := bstep (se 1 (by rfl) ⟨4999328, by rfl⟩ : syracuseStep 6665771 = 9998657) B9998657
theorem B17775389 : Blo 2079435 17775389 := bstep (se 3 (by rfl) ⟨3332885, by rfl⟩ : syracuseStep 17775389 = 6665771) B6665771
theorem B11850259 : Blo 2079435 11850259 := bstep (se 1 (by rfl) ⟨8887694, by rfl⟩ : syracuseStep 11850259 = 17775389) B17775389
theorem B15800345 : Blo 2079435 15800345 := bstep (se 2 (by rfl) ⟨5925129, by rfl⟩ : syracuseStep 15800345 = 11850259) B11850259
theorem B10533563 : Blo 2079435 10533563 := bstep (se 1 (by rfl) ⟨7900172, by rfl⟩ : syracuseStep 10533563 = 15800345) B15800345
theorem B7022375 : Blo 2079435 7022375 := bstep (se 1 (by rfl) ⟨5266781, by rfl⟩ : syracuseStep 7022375 = 10533563) B10533563
theorem B4681583 : Blo 2079435 4681583 := bstep (se 1 (by rfl) ⟨3511187, by rfl⟩ : syracuseStep 4681583 = 7022375) B7022375
theorem B3121055 : Blo 2079435 3121055 := bstep (se 1 (by rfl) ⟨2340791, by rfl⟩ : syracuseStep 3121055 = 4681583) B4681583
theorem B2080703 : Blo 2079435 2080703 := bstep (se 1 (by rfl) ⟨1560527, by rfl⟩ : syracuseStep 2080703 = 3121055) B3121055
theorem B3121061 : Blo 2079435 3121061 := bbase (se 4 (by rfl) ⟨292599, by rfl⟩ : syracuseStep 3121061 = 585199) (by norm_num)
theorem B2080707 : Blo 2079435 2080707 := bstep (se 1 (by rfl) ⟨1560530, by rfl⟩ : syracuseStep 2080707 = 3121061) B3121061
theorem B2633401 : Blo 2079435 2633401 := bbase (se 2 (by rfl) ⟨987525, by rfl⟩ : syracuseStep 2633401 = 1975051) (by norm_num)
theorem B3511201 : Blo 2079435 3511201 := bstep (se 2 (by rfl) ⟨1316700, by rfl⟩ : syracuseStep 3511201 = 2633401) B2633401
theorem B4681601 : Blo 2079435 4681601 := bstep (se 2 (by rfl) ⟨1755600, by rfl⟩ : syracuseStep 4681601 = 3511201) B3511201
theorem B3121067 : Blo 2079435 3121067 := bstep (se 1 (by rfl) ⟨2340800, by rfl⟩ : syracuseStep 3121067 = 4681601) B4681601
theorem B2080711 : Blo 2079435 2080711 := bstep (se 1 (by rfl) ⟨1560533, by rfl⟩ : syracuseStep 2080711 = 3121067) B3121067
theorem B2340805 : Blo 2079435 2340805 := bbase (se 4 (by rfl) ⟨219450, by rfl⟩ : syracuseStep 2340805 = 438901) (by norm_num)
theorem B3121073 : Blo 2079435 3121073 := bstep (se 2 (by rfl) ⟨1170402, by rfl⟩ : syracuseStep 3121073 = 2340805) B2340805
theorem B2080715 : Blo 2079435 2080715 := bstep (se 1 (by rfl) ⟨1560536, by rfl⟩ : syracuseStep 2080715 = 3121073) B3121073
theorem B3950117 : Blo 2079435 3950117 := bbase (se 4 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 3950117 = 740647) (by norm_num)
theorem B2633411 : Blo 2079435 2633411 := bstep (se 1 (by rfl) ⟨1975058, by rfl⟩ : syracuseStep 2633411 = 3950117) B3950117
theorem B7022429 : Blo 2079435 7022429 := bstep (se 3 (by rfl) ⟨1316705, by rfl⟩ : syracuseStep 7022429 = 2633411) B2633411
theorem B4681619 : Blo 2079435 4681619 := bstep (se 1 (by rfl) ⟨3511214, by rfl⟩ : syracuseStep 4681619 = 7022429) B7022429
theorem B3121079 : Blo 2079435 3121079 := bstep (se 1 (by rfl) ⟨2340809, by rfl⟩ : syracuseStep 3121079 = 4681619) B4681619
theorem B2080719 : Blo 2079435 2080719 := bstep (se 1 (by rfl) ⟨1560539, by rfl⟩ : syracuseStep 2080719 = 3121079) B3121079
theorem B3121085 : Blo 2079435 3121085 := bbase (se 3 (by rfl) ⟨585203, by rfl⟩ : syracuseStep 3121085 = 1170407) (by norm_num)
theorem B2080723 : Blo 2079435 2080723 := bstep (se 1 (by rfl) ⟨1560542, by rfl⟩ : syracuseStep 2080723 = 3121085) B3121085
theorem B4681637 : Blo 2079435 4681637 := bbase (se 4 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 4681637 = 877807) (by norm_num)
theorem B3121091 : Blo 2079435 3121091 := bstep (se 1 (by rfl) ⟨2340818, by rfl⟩ : syracuseStep 3121091 = 4681637) B4681637
theorem B2080727 : Blo 2079435 2080727 := bstep (se 1 (by rfl) ⟨1560545, by rfl⟩ : syracuseStep 2080727 = 3121091) B3121091
theorem B5266853 : Blo 2079435 5266853 := bbase (se 4 (by rfl) ⟨493767, by rfl⟩ : syracuseStep 5266853 = 987535) (by norm_num)
theorem B3511235 : Blo 2079435 3511235 := bstep (se 1 (by rfl) ⟨2633426, by rfl⟩ : syracuseStep 3511235 = 5266853) B5266853
theorem B2340823 : Blo 2079435 2340823 := bstep (se 1 (by rfl) ⟨1755617, by rfl⟩ : syracuseStep 2340823 = 3511235) B3511235
theorem B3121097 : Blo 2079435 3121097 := bstep (se 2 (by rfl) ⟨1170411, by rfl⟩ : syracuseStep 3121097 = 2340823) B2340823
theorem B2080731 : Blo 2079435 2080731 := bstep (se 1 (by rfl) ⟨1560548, by rfl⟩ : syracuseStep 2080731 = 3121097) B3121097
theorem B5925221 : Blo 2079435 5925221 := bbase (se 4 (by rfl) ⟨555489, by rfl⟩ : syracuseStep 5925221 = 1110979) (by norm_num)
theorem B3950147 : Blo 2079435 3950147 := bstep (se 1 (by rfl) ⟨2962610, by rfl⟩ : syracuseStep 3950147 = 5925221) B5925221
theorem B10533725 : Blo 2079435 10533725 := bstep (se 3 (by rfl) ⟨1975073, by rfl⟩ : syracuseStep 10533725 = 3950147) B3950147
theorem B7022483 : Blo 2079435 7022483 := bstep (se 1 (by rfl) ⟨5266862, by rfl⟩ : syracuseStep 7022483 = 10533725) B10533725
theorem B4681655 : Blo 2079435 4681655 := bstep (se 1 (by rfl) ⟨3511241, by rfl⟩ : syracuseStep 4681655 = 7022483) B7022483
theorem B3121103 : Blo 2079435 3121103 := bstep (se 1 (by rfl) ⟨2340827, by rfl⟩ : syracuseStep 3121103 = 4681655) B4681655
theorem B2080735 : Blo 2079435 2080735 := bstep (se 1 (by rfl) ⟨1560551, by rfl⟩ : syracuseStep 2080735 = 3121103) B3121103
theorem B3121109 : Blo 2079435 3121109 := bbase (se 7 (by rfl) ⟨36575, by rfl⟩ : syracuseStep 3121109 = 73151) (by norm_num)
theorem B2080739 : Blo 2079435 2080739 := bstep (se 1 (by rfl) ⟨1560554, by rfl⟩ : syracuseStep 2080739 = 3121109) B3121109
theorem B7900325 : Blo 2079435 7900325 := bbase (se 4 (by rfl) ⟨740655, by rfl⟩ : syracuseStep 7900325 = 1481311) (by norm_num)
theorem B5266883 : Blo 2079435 5266883 := bstep (se 1 (by rfl) ⟨3950162, by rfl⟩ : syracuseStep 5266883 = 7900325) B7900325
theorem B3511255 : Blo 2079435 3511255 := bstep (se 1 (by rfl) ⟨2633441, by rfl⟩ : syracuseStep 3511255 = 5266883) B5266883
theorem B4681673 : Blo 2079435 4681673 := bstep (se 2 (by rfl) ⟨1755627, by rfl⟩ : syracuseStep 4681673 = 3511255) B3511255
theorem B3121115 : Blo 2079435 3121115 := bstep (se 1 (by rfl) ⟨2340836, by rfl⟩ : syracuseStep 3121115 = 4681673) B4681673
theorem B2080743 : Blo 2079435 2080743 := bstep (se 1 (by rfl) ⟨1560557, by rfl⟩ : syracuseStep 2080743 = 3121115) B3121115
theorem B2340841 : Blo 2079435 2340841 := bbase (se 2 (by rfl) ⟨877815, by rfl⟩ : syracuseStep 2340841 = 1755631) (by norm_num)
theorem B3121121 : Blo 2079435 3121121 := bstep (se 2 (by rfl) ⟨1170420, by rfl⟩ : syracuseStep 3121121 = 2340841) B2340841
theorem B2080747 : Blo 2079435 2080747 := bstep (se 1 (by rfl) ⟨1560560, by rfl⟩ : syracuseStep 2080747 = 3121121) B3121121
theorem B4999445 : Blo 2079435 4999445 := bbase (se 6 (by rfl) ⟨117174, by rfl⟩ : syracuseStep 4999445 = 234349) (by norm_num)
theorem B3332963 : Blo 2079435 3332963 := bstep (se 1 (by rfl) ⟨2499722, by rfl⟩ : syracuseStep 3332963 = 4999445) B4999445
theorem B2221975 : Blo 2079435 2221975 := bstep (se 1 (by rfl) ⟨1666481, by rfl⟩ : syracuseStep 2221975 = 3332963) B3332963
theorem B11850533 : Blo 2079435 11850533 := bstep (se 4 (by rfl) ⟨1110987, by rfl⟩ : syracuseStep 11850533 = 2221975) B2221975
theorem B7900355 : Blo 2079435 7900355 := bstep (se 1 (by rfl) ⟨5925266, by rfl⟩ : syracuseStep 7900355 = 11850533) B11850533
theorem B5266903 : Blo 2079435 5266903 := bstep (se 1 (by rfl) ⟨3950177, by rfl⟩ : syracuseStep 5266903 = 7900355) B7900355
theorem B7022537 : Blo 2079435 7022537 := bstep (se 2 (by rfl) ⟨2633451, by rfl⟩ : syracuseStep 7022537 = 5266903) B5266903
theorem B4681691 : Blo 2079435 4681691 := bstep (se 1 (by rfl) ⟨3511268, by rfl⟩ : syracuseStep 4681691 = 7022537) B7022537
theorem B3121127 : Blo 2079435 3121127 := bstep (se 1 (by rfl) ⟨2340845, by rfl⟩ : syracuseStep 3121127 = 4681691) B4681691
theorem B2080751 : Blo 2079435 2080751 := bstep (se 1 (by rfl) ⟨1560563, by rfl⟩ : syracuseStep 2080751 = 3121127) B3121127
theorem B3121133 : Blo 2079435 3121133 := bbase (se 3 (by rfl) ⟨585212, by rfl⟩ : syracuseStep 3121133 = 1170425) (by norm_num)
theorem B2080755 : Blo 2079435 2080755 := bstep (se 1 (by rfl) ⟨1560566, by rfl⟩ : syracuseStep 2080755 = 3121133) B3121133
theorem B4681709 : Blo 2079435 4681709 := bbase (se 3 (by rfl) ⟨877820, by rfl⟩ : syracuseStep 4681709 = 1755641) (by norm_num)
theorem B3121139 : Blo 2079435 3121139 := bstep (se 1 (by rfl) ⟨2340854, by rfl⟩ : syracuseStep 3121139 = 4681709) B4681709
theorem B2080759 : Blo 2079435 2080759 := bstep (se 1 (by rfl) ⟨1560569, by rfl⟩ : syracuseStep 2080759 = 3121139) B3121139
theorem B2812205 : Blo 2079435 2812205 := bbase (se 3 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 2812205 = 1054577) (by norm_num)
theorem B7499213 : Blo 2079435 7499213 := bstep (se 3 (by rfl) ⟨1406102, by rfl⟩ : syracuseStep 7499213 = 2812205) B2812205
theorem B4999475 : Blo 2079435 4999475 := bstep (se 1 (by rfl) ⟨3749606, by rfl⟩ : syracuseStep 4999475 = 7499213) B7499213
theorem B3332983 : Blo 2079435 3332983 := bstep (se 1 (by rfl) ⟨2499737, by rfl⟩ : syracuseStep 3332983 = 4999475) B4999475
theorem B4443977 : Blo 2079435 4443977 := bstep (se 2 (by rfl) ⟨1666491, by rfl⟩ : syracuseStep 4443977 = 3332983) B3332983
theorem B2962651 : Blo 2079435 2962651 := bstep (se 1 (by rfl) ⟨2221988, by rfl⟩ : syracuseStep 2962651 = 4443977) B4443977
theorem B3950201 : Blo 2079435 3950201 := bstep (se 2 (by rfl) ⟨1481325, by rfl⟩ : syracuseStep 3950201 = 2962651) B2962651
theorem B2633467 : Blo 2079435 2633467 := bstep (se 1 (by rfl) ⟨1975100, by rfl⟩ : syracuseStep 2633467 = 3950201) B3950201
theorem B3511289 : Blo 2079435 3511289 := bstep (se 2 (by rfl) ⟨1316733, by rfl⟩ : syracuseStep 3511289 = 2633467) B2633467
theorem B2340859 : Blo 2079435 2340859 := bstep (se 1 (by rfl) ⟨1755644, by rfl⟩ : syracuseStep 2340859 = 3511289) B3511289
theorem B3121145 : Blo 2079435 3121145 := bstep (se 2 (by rfl) ⟨1170429, by rfl⟩ : syracuseStep 3121145 = 2340859) B2340859
theorem B2080763 : Blo 2079435 2080763 := bstep (se 1 (by rfl) ⟨1560572, by rfl⟩ : syracuseStep 2080763 = 3121145) B3121145
theorem B3378461 : Blo 2079435 3378461 := bbase (se 3 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 3378461 = 1266923) (by norm_num)
theorem B36036917 : Blo 2079435 36036917 := bstep (se 5 (by rfl) ⟨1689230, by rfl⟩ : syracuseStep 36036917 = 3378461) B3378461
theorem B24024611 : Blo 2079435 24024611 := bstep (se 1 (by rfl) ⟨18018458, by rfl⟩ : syracuseStep 24024611 = 36036917) B36036917
theorem B16016407 : Blo 2079435 16016407 := bstep (se 1 (by rfl) ⟨12012305, by rfl⟩ : syracuseStep 16016407 = 24024611) B24024611
theorem B85420837 : Blo 2079435 85420837 := bstep (se 4 (by rfl) ⟨8008203, by rfl⟩ : syracuseStep 85420837 = 16016407) B16016407
theorem B455577797 : Blo 2079435 455577797 := bstep (se 4 (by rfl) ⟨42710418, by rfl⟩ : syracuseStep 455577797 = 85420837) B85420837
theorem B303718531 : Blo 2079435 303718531 := bstep (se 1 (by rfl) ⟨227788898, by rfl⟩ : syracuseStep 303718531 = 455577797) B455577797
theorem B404958041 : Blo 2079435 404958041 := bstep (se 2 (by rfl) ⟨151859265, by rfl⟩ : syracuseStep 404958041 = 303718531) B303718531
theorem B269972027 : Blo 2079435 269972027 := bstep (se 1 (by rfl) ⟨202479020, by rfl⟩ : syracuseStep 269972027 = 404958041) B404958041
theorem B179981351 : Blo 2079435 179981351 := bstep (se 1 (by rfl) ⟨134986013, by rfl⟩ : syracuseStep 179981351 = 269972027) B269972027
theorem B119987567 : Blo 2079435 119987567 := bstep (se 1 (by rfl) ⟨89990675, by rfl⟩ : syracuseStep 119987567 = 179981351) B179981351
theorem B79991711 : Blo 2079435 79991711 := bstep (se 1 (by rfl) ⟨59993783, by rfl⟩ : syracuseStep 79991711 = 119987567) B119987567
theorem B53327807 : Blo 2079435 53327807 := bstep (se 1 (by rfl) ⟨39995855, by rfl⟩ : syracuseStep 53327807 = 79991711) B79991711
theorem B35551871 : Blo 2079435 35551871 := bstep (se 1 (by rfl) ⟨26663903, by rfl⟩ : syracuseStep 35551871 = 53327807) B53327807
theorem B23701247 : Blo 2079435 23701247 := bstep (se 1 (by rfl) ⟨17775935, by rfl⟩ : syracuseStep 23701247 = 35551871) B35551871
theorem B15800831 : Blo 2079435 15800831 := bstep (se 1 (by rfl) ⟨11850623, by rfl⟩ : syracuseStep 15800831 = 23701247) B23701247
theorem B10533887 : Blo 2079435 10533887 := bstep (se 1 (by rfl) ⟨7900415, by rfl⟩ : syracuseStep 10533887 = 15800831) B15800831
theorem B7022591 : Blo 2079435 7022591 := bstep (se 1 (by rfl) ⟨5266943, by rfl⟩ : syracuseStep 7022591 = 10533887) B10533887
theorem B4681727 : Blo 2079435 4681727 := bstep (se 1 (by rfl) ⟨3511295, by rfl⟩ : syracuseStep 4681727 = 7022591) B7022591
theorem B3121151 : Blo 2079435 3121151 := bstep (se 1 (by rfl) ⟨2340863, by rfl⟩ : syracuseStep 3121151 = 4681727) B4681727
theorem B2080767 : Blo 2079435 2080767 := bstep (se 1 (by rfl) ⟨1560575, by rfl⟩ : syracuseStep 2080767 = 3121151) B3121151
theorem B3121157 : Blo 2079435 3121157 := bbase (se 4 (by rfl) ⟨292608, by rfl⟩ : syracuseStep 3121157 = 585217) (by norm_num)
theorem B2080771 : Blo 2079435 2080771 := bstep (se 1 (by rfl) ⟨1560578, by rfl⟩ : syracuseStep 2080771 = 3121157) B3121157
theorem B3511309 : Blo 2079435 3511309 := bbase (se 3 (by rfl) ⟨658370, by rfl⟩ : syracuseStep 3511309 = 1316741) (by norm_num)
theorem B4681745 : Blo 2079435 4681745 := bstep (se 2 (by rfl) ⟨1755654, by rfl⟩ : syracuseStep 4681745 = 3511309) B3511309
theorem B3121163 : Blo 2079435 3121163 := bstep (se 1 (by rfl) ⟨2340872, by rfl⟩ : syracuseStep 3121163 = 4681745) B4681745
theorem B2080775 : Blo 2079435 2080775 := bstep (se 1 (by rfl) ⟨1560581, by rfl⟩ : syracuseStep 2080775 = 3121163) B3121163
theorem B2340877 : Blo 2079435 2340877 := bbase (se 3 (by rfl) ⟨438914, by rfl⟩ : syracuseStep 2340877 = 877829) (by norm_num)
theorem B3121169 : Blo 2079435 3121169 := bstep (se 2 (by rfl) ⟨1170438, by rfl⟩ : syracuseStep 3121169 = 2340877) B2340877
theorem B2080779 : Blo 2079435 2080779 := bstep (se 1 (by rfl) ⟨1560584, by rfl⟩ : syracuseStep 2080779 = 3121169) B3121169
theorem B7022645 : Blo 2079435 7022645 := bbase (se 5 (by rfl) ⟨329186, by rfl⟩ : syracuseStep 7022645 = 658373) (by norm_num)
theorem B4681763 : Blo 2079435 4681763 := bstep (se 1 (by rfl) ⟨3511322, by rfl⟩ : syracuseStep 4681763 = 7022645) B7022645
theorem B3121175 : Blo 2079435 3121175 := bstep (se 1 (by rfl) ⟨2340881, by rfl⟩ : syracuseStep 3121175 = 4681763) B4681763
theorem B2080783 : Blo 2079435 2080783 := bstep (se 1 (by rfl) ⟨1560587, by rfl⟩ : syracuseStep 2080783 = 3121175) B3121175
theorem B3121181 : Blo 2079435 3121181 := bbase (se 3 (by rfl) ⟨585221, by rfl⟩ : syracuseStep 3121181 = 1170443) (by norm_num)
theorem B2080787 : Blo 2079435 2080787 := bstep (se 1 (by rfl) ⟨1560590, by rfl⟩ : syracuseStep 2080787 = 3121181) B3121181
theorem B4681781 : Blo 2079435 4681781 := bbase (se 5 (by rfl) ⟨219458, by rfl⟩ : syracuseStep 4681781 = 438917) (by norm_num)
theorem B3121187 : Blo 2079435 3121187 := bstep (se 1 (by rfl) ⟨2340890, by rfl⟩ : syracuseStep 3121187 = 4681781) B4681781
theorem B2080791 : Blo 2079435 2080791 := bstep (se 1 (by rfl) ⟨1560593, by rfl⟩ : syracuseStep 2080791 = 3121187) B3121187
theorem B5338877 : Blo 2079435 5338877 := bbase (se 3 (by rfl) ⟨1001039, by rfl⟩ : syracuseStep 5338877 = 2002079) (by norm_num)
theorem B14237005 : Blo 2079435 14237005 := bstep (se 3 (by rfl) ⟨2669438, by rfl⟩ : syracuseStep 14237005 = 5338877) B5338877
theorem B18982673 : Blo 2079435 18982673 := bstep (se 2 (by rfl) ⟨7118502, by rfl⟩ : syracuseStep 18982673 = 14237005) B14237005
theorem B12655115 : Blo 2079435 12655115 := bstep (se 1 (by rfl) ⟨9491336, by rfl⟩ : syracuseStep 12655115 = 18982673) B18982673
theorem B8436743 : Blo 2079435 8436743 := bstep (se 1 (by rfl) ⟨6327557, by rfl⟩ : syracuseStep 8436743 = 12655115) B12655115
theorem B5624495 : Blo 2079435 5624495 := bstep (se 1 (by rfl) ⟨4218371, by rfl⟩ : syracuseStep 5624495 = 8436743) B8436743
theorem B3749663 : Blo 2079435 3749663 := bstep (se 1 (by rfl) ⟨2812247, by rfl⟩ : syracuseStep 3749663 = 5624495) B5624495
theorem B9999101 : Blo 2079435 9999101 := bstep (se 3 (by rfl) ⟨1874831, by rfl⟩ : syracuseStep 9999101 = 3749663) B3749663
theorem B6666067 : Blo 2079435 6666067 := bstep (se 1 (by rfl) ⟨4999550, by rfl⟩ : syracuseStep 6666067 = 9999101) B9999101
theorem B8888089 : Blo 2079435 8888089 := bstep (se 2 (by rfl) ⟨3333033, by rfl⟩ : syracuseStep 8888089 = 6666067) B6666067
theorem B11850785 : Blo 2079435 11850785 := bstep (se 2 (by rfl) ⟨4444044, by rfl⟩ : syracuseStep 11850785 = 8888089) B8888089
theorem B7900523 : Blo 2079435 7900523 := bstep (se 1 (by rfl) ⟨5925392, by rfl⟩ : syracuseStep 7900523 = 11850785) B11850785
theorem B5267015 : Blo 2079435 5267015 := bstep (se 1 (by rfl) ⟨3950261, by rfl⟩ : syracuseStep 5267015 = 7900523) B7900523
theorem B3511343 : Blo 2079435 3511343 := bstep (se 1 (by rfl) ⟨2633507, by rfl⟩ : syracuseStep 3511343 = 5267015) B5267015
theorem B2340895 : Blo 2079435 2340895 := bstep (se 1 (by rfl) ⟨1755671, by rfl⟩ : syracuseStep 2340895 = 3511343) B3511343
theorem B3121193 : Blo 2079435 3121193 := bstep (se 2 (by rfl) ⟨1170447, by rfl⟩ : syracuseStep 3121193 = 2340895) B2340895
theorem B2080795 : Blo 2079435 2080795 := bstep (se 1 (by rfl) ⟨1560596, by rfl⟩ : syracuseStep 2080795 = 3121193) B3121193
theorem B33747029 : Blo 2079435 33747029 := bbase (se 8 (by rfl) ⟨197736, by rfl⟩ : syracuseStep 33747029 = 395473) (by norm_num)
theorem B22498019 : Blo 2079435 22498019 := bstep (se 1 (by rfl) ⟨16873514, by rfl⟩ : syracuseStep 22498019 = 33747029) B33747029
theorem B14998679 : Blo 2079435 14998679 := bstep (se 1 (by rfl) ⟨11249009, by rfl⟩ : syracuseStep 14998679 = 22498019) B22498019
theorem B9999119 : Blo 2079435 9999119 := bstep (se 1 (by rfl) ⟨7499339, by rfl⟩ : syracuseStep 9999119 = 14998679) B14998679
theorem B6666079 : Blo 2079435 6666079 := bstep (se 1 (by rfl) ⟨4999559, by rfl⟩ : syracuseStep 6666079 = 9999119) B9999119
theorem B8888105 : Blo 2079435 8888105 := bstep (se 2 (by rfl) ⟨3333039, by rfl⟩ : syracuseStep 8888105 = 6666079) B6666079
theorem B5925403 : Blo 2079435 5925403 := bstep (se 1 (by rfl) ⟨4444052, by rfl⟩ : syracuseStep 5925403 = 8888105) B8888105
theorem B7900537 : Blo 2079435 7900537 := bstep (se 2 (by rfl) ⟨2962701, by rfl⟩ : syracuseStep 7900537 = 5925403) B5925403
theorem B10534049 : Blo 2079435 10534049 := bstep (se 2 (by rfl) ⟨3950268, by rfl⟩ : syracuseStep 10534049 = 7900537) B7900537
theorem B7022699 : Blo 2079435 7022699 := bstep (se 1 (by rfl) ⟨5267024, by rfl⟩ : syracuseStep 7022699 = 10534049) B10534049
theorem B4681799 : Blo 2079435 4681799 := bstep (se 1 (by rfl) ⟨3511349, by rfl⟩ : syracuseStep 4681799 = 7022699) B7022699
theorem B3121199 : Blo 2079435 3121199 := bstep (se 1 (by rfl) ⟨2340899, by rfl⟩ : syracuseStep 3121199 = 4681799) B4681799
theorem B2080799 : Blo 2079435 2080799 := bstep (se 1 (by rfl) ⟨1560599, by rfl⟩ : syracuseStep 2080799 = 3121199) B3121199
theorem B3121205 : Blo 2079435 3121205 := bbase (se 5 (by rfl) ⟨146306, by rfl⟩ : syracuseStep 3121205 = 292613) (by norm_num)
theorem B2080803 : Blo 2079435 2080803 := bstep (se 1 (by rfl) ⟨1560602, by rfl⟩ : syracuseStep 2080803 = 3121205) B3121205
theorem B5267045 : Blo 2079435 5267045 := bbase (se 4 (by rfl) ⟨493785, by rfl⟩ : syracuseStep 5267045 = 987571) (by norm_num)
theorem B3511363 : Blo 2079435 3511363 := bstep (se 1 (by rfl) ⟨2633522, by rfl⟩ : syracuseStep 3511363 = 5267045) B5267045
theorem B4681817 : Blo 2079435 4681817 := bstep (se 2 (by rfl) ⟨1755681, by rfl⟩ : syracuseStep 4681817 = 3511363) B3511363
theorem B3121211 : Blo 2079435 3121211 := bstep (se 1 (by rfl) ⟨2340908, by rfl⟩ : syracuseStep 3121211 = 4681817) B4681817
theorem B2080807 : Blo 2079435 2080807 := bstep (se 1 (by rfl) ⟨1560605, by rfl⟩ : syracuseStep 2080807 = 3121211) B3121211
theorem B2340913 : Blo 2079435 2340913 := bbase (se 2 (by rfl) ⟨877842, by rfl⟩ : syracuseStep 2340913 = 1755685) (by norm_num)
theorem B3121217 : Blo 2079435 3121217 := bstep (se 2 (by rfl) ⟨1170456, by rfl⟩ : syracuseStep 3121217 = 2340913) B2340913
theorem B2080811 : Blo 2079435 2080811 := bstep (se 1 (by rfl) ⟨1560608, by rfl⟩ : syracuseStep 2080811 = 3121217) B3121217
theorem B5624549 : Blo 2079435 5624549 := bbase (se 4 (by rfl) ⟨527301, by rfl⟩ : syracuseStep 5624549 = 1054603) (by norm_num)
theorem B3749699 : Blo 2079435 3749699 := bstep (se 1 (by rfl) ⟨2812274, by rfl⟩ : syracuseStep 3749699 = 5624549) B5624549
theorem B9999197 : Blo 2079435 9999197 := bstep (se 3 (by rfl) ⟨1874849, by rfl⟩ : syracuseStep 9999197 = 3749699) B3749699
theorem B6666131 : Blo 2079435 6666131 := bstep (se 1 (by rfl) ⟨4999598, by rfl⟩ : syracuseStep 6666131 = 9999197) B9999197
theorem B4444087 : Blo 2079435 4444087 := bstep (se 1 (by rfl) ⟨3333065, by rfl⟩ : syracuseStep 4444087 = 6666131) B6666131
theorem B5925449 : Blo 2079435 5925449 := bstep (se 2 (by rfl) ⟨2222043, by rfl⟩ : syracuseStep 5925449 = 4444087) B4444087
theorem B3950299 : Blo 2079435 3950299 := bstep (se 1 (by rfl) ⟨2962724, by rfl⟩ : syracuseStep 3950299 = 5925449) B5925449
theorem B5267065 : Blo 2079435 5267065 := bstep (se 2 (by rfl) ⟨1975149, by rfl⟩ : syracuseStep 5267065 = 3950299) B3950299
theorem B7022753 : Blo 2079435 7022753 := bstep (se 2 (by rfl) ⟨2633532, by rfl⟩ : syracuseStep 7022753 = 5267065) B5267065
theorem B4681835 : Blo 2079435 4681835 := bstep (se 1 (by rfl) ⟨3511376, by rfl⟩ : syracuseStep 4681835 = 7022753) B7022753
theorem B3121223 : Blo 2079435 3121223 := bstep (se 1 (by rfl) ⟨2340917, by rfl⟩ : syracuseStep 3121223 = 4681835) B4681835
theorem B2080815 : Blo 2079435 2080815 := bstep (se 1 (by rfl) ⟨1560611, by rfl⟩ : syracuseStep 2080815 = 3121223) B3121223
theorem B3121229 : Blo 2079435 3121229 := bbase (se 3 (by rfl) ⟨585230, by rfl⟩ : syracuseStep 3121229 = 1170461) (by norm_num)
theorem B2080819 : Blo 2079435 2080819 := bstep (se 1 (by rfl) ⟨1560614, by rfl⟩ : syracuseStep 2080819 = 3121229) B3121229
theorem B4681853 : Blo 2079435 4681853 := bbase (se 3 (by rfl) ⟨877847, by rfl⟩ : syracuseStep 4681853 = 1755695) (by norm_num)
theorem B3121235 : Blo 2079435 3121235 := bstep (se 1 (by rfl) ⟨2340926, by rfl⟩ : syracuseStep 3121235 = 4681853) B4681853
theorem B2080823 : Blo 2079435 2080823 := bstep (se 1 (by rfl) ⟨1560617, by rfl⟩ : syracuseStep 2080823 = 3121235) B3121235
theorem B3511397 : Blo 2079435 3511397 := bbase (se 4 (by rfl) ⟨329193, by rfl⟩ : syracuseStep 3511397 = 658387) (by norm_num)
theorem B2340931 : Blo 2079435 2340931 := bstep (se 1 (by rfl) ⟨1755698, by rfl⟩ : syracuseStep 2340931 = 3511397) B3511397
theorem B3121241 : Blo 2079435 3121241 := bstep (se 2 (by rfl) ⟨1170465, by rfl⟩ : syracuseStep 3121241 = 2340931) B2340931
theorem B2080827 : Blo 2079435 2080827 := bstep (se 1 (by rfl) ⟨1560620, by rfl⟩ : syracuseStep 2080827 = 3121241) B3121241
theorem B4999637 : Blo 2079435 4999637 := bbase (se 7 (by rfl) ⟨58589, by rfl⟩ : syracuseStep 4999637 = 117179) (by norm_num)
theorem B3333091 : Blo 2079435 3333091 := bstep (se 1 (by rfl) ⟨2499818, by rfl⟩ : syracuseStep 3333091 = 4999637) B4999637
theorem B4444121 : Blo 2079435 4444121 := bstep (se 2 (by rfl) ⟨1666545, by rfl⟩ : syracuseStep 4444121 = 3333091) B3333091
theorem B2962747 : Blo 2079435 2962747 := bstep (se 1 (by rfl) ⟨2222060, by rfl⟩ : syracuseStep 2962747 = 4444121) B4444121
theorem B15801317 : Blo 2079435 15801317 := bstep (se 4 (by rfl) ⟨1481373, by rfl⟩ : syracuseStep 15801317 = 2962747) B2962747
theorem B10534211 : Blo 2079435 10534211 := bstep (se 1 (by rfl) ⟨7900658, by rfl⟩ : syracuseStep 10534211 = 15801317) B15801317
theorem B7022807 : Blo 2079435 7022807 := bstep (se 1 (by rfl) ⟨5267105, by rfl⟩ : syracuseStep 7022807 = 10534211) B10534211
theorem B4681871 : Blo 2079435 4681871 := bstep (se 1 (by rfl) ⟨3511403, by rfl⟩ : syracuseStep 4681871 = 7022807) B7022807
theorem B3121247 : Blo 2079435 3121247 := bstep (se 1 (by rfl) ⟨2340935, by rfl⟩ : syracuseStep 3121247 = 4681871) B4681871
theorem B2080831 : Blo 2079435 2080831 := bstep (se 1 (by rfl) ⟨1560623, by rfl⟩ : syracuseStep 2080831 = 3121247) B3121247
theorem B3121253 : Blo 2079435 3121253 := bbase (se 4 (by rfl) ⟨292617, by rfl⟩ : syracuseStep 3121253 = 585235) (by norm_num)
theorem B2080835 : Blo 2079435 2080835 := bstep (se 1 (by rfl) ⟨1560626, by rfl⟩ : syracuseStep 2080835 = 3121253) B3121253
theorem B10823669 : Blo 2079435 10823669 := bbase (se 5 (by rfl) ⟨507359, by rfl⟩ : syracuseStep 10823669 = 1014719) (by norm_num)
theorem B7215779 : Blo 2079435 7215779 := bstep (se 1 (by rfl) ⟨5411834, by rfl⟩ : syracuseStep 7215779 = 10823669) B10823669
theorem B4810519 : Blo 2079435 4810519 := bstep (se 1 (by rfl) ⟨3607889, by rfl⟩ : syracuseStep 4810519 = 7215779) B7215779
theorem B25656101 : Blo 2079435 25656101 := bstep (se 4 (by rfl) ⟨2405259, by rfl⟩ : syracuseStep 25656101 = 4810519) B4810519
theorem B17104067 : Blo 2079435 17104067 := bstep (se 1 (by rfl) ⟨12828050, by rfl⟩ : syracuseStep 17104067 = 25656101) B25656101
theorem B11402711 : Blo 2079435 11402711 := bstep (se 1 (by rfl) ⟨8552033, by rfl⟩ : syracuseStep 11402711 = 17104067) B17104067
theorem B7601807 : Blo 2079435 7601807 := bstep (se 1 (by rfl) ⟨5701355, by rfl⟩ : syracuseStep 7601807 = 11402711) B11402711
theorem B20271485 : Blo 2079435 20271485 := bstep (se 3 (by rfl) ⟨3800903, by rfl⟩ : syracuseStep 20271485 = 7601807) B7601807
theorem B13514323 : Blo 2079435 13514323 := bstep (se 1 (by rfl) ⟨10135742, by rfl⟩ : syracuseStep 13514323 = 20271485) B20271485
theorem B18019097 : Blo 2079435 18019097 := bstep (se 2 (by rfl) ⟨6757161, by rfl⟩ : syracuseStep 18019097 = 13514323) B13514323
theorem B12012731 : Blo 2079435 12012731 := bstep (se 1 (by rfl) ⟨9009548, by rfl⟩ : syracuseStep 12012731 = 18019097) B18019097
theorem B8008487 : Blo 2079435 8008487 := bstep (se 1 (by rfl) ⟨6006365, by rfl⟩ : syracuseStep 8008487 = 12012731) B12012731
theorem B5338991 : Blo 2079435 5338991 := bstep (se 1 (by rfl) ⟨4004243, by rfl⟩ : syracuseStep 5338991 = 8008487) B8008487
theorem B14237309 : Blo 2079435 14237309 := bstep (se 3 (by rfl) ⟨2669495, by rfl⟩ : syracuseStep 14237309 = 5338991) B5338991
theorem B9491539 : Blo 2079435 9491539 := bstep (se 1 (by rfl) ⟨7118654, by rfl⟩ : syracuseStep 9491539 = 14237309) B14237309
theorem B12655385 : Blo 2079435 12655385 := bstep (se 2 (by rfl) ⟨4745769, by rfl⟩ : syracuseStep 12655385 = 9491539) B9491539
theorem B8436923 : Blo 2079435 8436923 := bstep (se 1 (by rfl) ⟨6327692, by rfl⟩ : syracuseStep 8436923 = 12655385) B12655385
theorem B5624615 : Blo 2079435 5624615 := bstep (se 1 (by rfl) ⟨4218461, by rfl⟩ : syracuseStep 5624615 = 8436923) B8436923
theorem B3749743 : Blo 2079435 3749743 := bstep (se 1 (by rfl) ⟨2812307, by rfl⟩ : syracuseStep 3749743 = 5624615) B5624615
theorem B4999657 : Blo 2079435 4999657 := bstep (se 2 (by rfl) ⟨1874871, by rfl⟩ : syracuseStep 4999657 = 3749743) B3749743
theorem B6666209 : Blo 2079435 6666209 := bstep (se 2 (by rfl) ⟨2499828, by rfl⟩ : syracuseStep 6666209 = 4999657) B4999657
theorem B4444139 : Blo 2079435 4444139 := bstep (se 1 (by rfl) ⟨3333104, by rfl⟩ : syracuseStep 4444139 = 6666209) B6666209
theorem B2962759 : Blo 2079435 2962759 := bstep (se 1 (by rfl) ⟨2222069, by rfl⟩ : syracuseStep 2962759 = 4444139) B4444139
theorem B3950345 : Blo 2079435 3950345 := bstep (se 2 (by rfl) ⟨1481379, by rfl⟩ : syracuseStep 3950345 = 2962759) B2962759
theorem B2633563 : Blo 2079435 2633563 := bstep (se 1 (by rfl) ⟨1975172, by rfl⟩ : syracuseStep 2633563 = 3950345) B3950345
theorem B3511417 : Blo 2079435 3511417 := bstep (se 2 (by rfl) ⟨1316781, by rfl⟩ : syracuseStep 3511417 = 2633563) B2633563
theorem B4681889 : Blo 2079435 4681889 := bstep (se 2 (by rfl) ⟨1755708, by rfl⟩ : syracuseStep 4681889 = 3511417) B3511417
theorem B3121259 : Blo 2079435 3121259 := bstep (se 1 (by rfl) ⟨2340944, by rfl⟩ : syracuseStep 3121259 = 4681889) B4681889
theorem B2080839 : Blo 2079435 2080839 := bstep (se 1 (by rfl) ⟨1560629, by rfl⟩ : syracuseStep 2080839 = 3121259) B3121259
theorem B2340949 : Blo 2079435 2340949 := bbase (se 8 (by rfl) ⟨13716, by rfl⟩ : syracuseStep 2340949 = 27433) (by norm_num)
theorem B3121265 : Blo 2079435 3121265 := bstep (se 2 (by rfl) ⟨1170474, by rfl⟩ : syracuseStep 3121265 = 2340949) B2340949
theorem B2080843 : Blo 2079435 2080843 := bstep (se 1 (by rfl) ⟨1560632, by rfl⟩ : syracuseStep 2080843 = 3121265) B3121265
theorem B2633573 : Blo 2079435 2633573 := bbase (se 4 (by rfl) ⟨246897, by rfl⟩ : syracuseStep 2633573 = 493795) (by norm_num)
theorem B7022861 : Blo 2079435 7022861 := bstep (se 3 (by rfl) ⟨1316786, by rfl⟩ : syracuseStep 7022861 = 2633573) B2633573
theorem B4681907 : Blo 2079435 4681907 := bstep (se 1 (by rfl) ⟨3511430, by rfl⟩ : syracuseStep 4681907 = 7022861) B7022861
theorem B3121271 : Blo 2079435 3121271 := bstep (se 1 (by rfl) ⟨2340953, by rfl⟩ : syracuseStep 3121271 = 4681907) B4681907
theorem B2080847 : Blo 2079435 2080847 := bstep (se 1 (by rfl) ⟨1560635, by rfl⟩ : syracuseStep 2080847 = 3121271) B3121271
theorem B3121277 : Blo 2079435 3121277 := bbase (se 3 (by rfl) ⟨585239, by rfl⟩ : syracuseStep 3121277 = 1170479) (by norm_num)
theorem B2080851 : Blo 2079435 2080851 := bstep (se 1 (by rfl) ⟨1560638, by rfl⟩ : syracuseStep 2080851 = 3121277) B3121277
theorem B4681925 : Blo 2079435 4681925 := bbase (se 4 (by rfl) ⟨438930, by rfl⟩ : syracuseStep 4681925 = 877861) (by norm_num)
theorem B3121283 : Blo 2079435 3121283 := bstep (se 1 (by rfl) ⟨2340962, by rfl⟩ : syracuseStep 3121283 = 4681925) B4681925
theorem B2080855 : Blo 2079435 2080855 := bstep (se 1 (by rfl) ⟨1560641, by rfl⟩ : syracuseStep 2080855 = 3121283) B3121283
theorem B7499557 : Blo 2079435 7499557 := bbase (se 4 (by rfl) ⟨703083, by rfl⟩ : syracuseStep 7499557 = 1406167) (by norm_num)
theorem B9999409 : Blo 2079435 9999409 := bstep (se 2 (by rfl) ⟨3749778, by rfl⟩ : syracuseStep 9999409 = 7499557) B7499557
theorem B13332545 : Blo 2079435 13332545 := bstep (se 2 (by rfl) ⟨4999704, by rfl⟩ : syracuseStep 13332545 = 9999409) B9999409
theorem B8888363 : Blo 2079435 8888363 := bstep (se 1 (by rfl) ⟨6666272, by rfl⟩ : syracuseStep 8888363 = 13332545) B13332545
theorem B5925575 : Blo 2079435 5925575 := bstep (se 1 (by rfl) ⟨4444181, by rfl⟩ : syracuseStep 5925575 = 8888363) B8888363
theorem B3950383 : Blo 2079435 3950383 := bstep (se 1 (by rfl) ⟨2962787, by rfl⟩ : syracuseStep 3950383 = 5925575) B5925575
theorem B5267177 : Blo 2079435 5267177 := bstep (se 2 (by rfl) ⟨1975191, by rfl⟩ : syracuseStep 5267177 = 3950383) B3950383
theorem B3511451 : Blo 2079435 3511451 := bstep (se 1 (by rfl) ⟨2633588, by rfl⟩ : syracuseStep 3511451 = 5267177) B5267177
theorem B2340967 : Blo 2079435 2340967 := bstep (se 1 (by rfl) ⟨1755725, by rfl⟩ : syracuseStep 2340967 = 3511451) B3511451
theorem B3121289 : Blo 2079435 3121289 := bstep (se 2 (by rfl) ⟨1170483, by rfl⟩ : syracuseStep 3121289 = 2340967) B2340967
theorem B2080859 : Blo 2079435 2080859 := bstep (se 1 (by rfl) ⟨1560644, by rfl⟩ : syracuseStep 2080859 = 3121289) B3121289
theorem B10534373 : Blo 2079435 10534373 := bbase (se 4 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 10534373 = 1975195) (by norm_num)
theorem B7022915 : Blo 2079435 7022915 := bstep (se 1 (by rfl) ⟨5267186, by rfl⟩ : syracuseStep 7022915 = 10534373) B10534373
theorem B4681943 : Blo 2079435 4681943 := bstep (se 1 (by rfl) ⟨3511457, by rfl⟩ : syracuseStep 4681943 = 7022915) B7022915
theorem B3121295 : Blo 2079435 3121295 := bstep (se 1 (by rfl) ⟨2340971, by rfl⟩ : syracuseStep 3121295 = 4681943) B4681943
theorem B2080863 : Blo 2079435 2080863 := bstep (se 1 (by rfl) ⟨1560647, by rfl⟩ : syracuseStep 2080863 = 3121295) B3121295
theorem B3121301 : Blo 2079435 3121301 := bbase (se 6 (by rfl) ⟨73155, by rfl⟩ : syracuseStep 3121301 = 146311) (by norm_num)
theorem B2080867 : Blo 2079435 2080867 := bstep (se 1 (by rfl) ⟨1560650, by rfl⟩ : syracuseStep 2080867 = 3121301) B3121301
theorem B4999733 : Blo 2079435 4999733 := bbase (se 5 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 4999733 = 468725) (by norm_num)
theorem B3333155 : Blo 2079435 3333155 := bstep (se 1 (by rfl) ⟨2499866, by rfl⟩ : syracuseStep 3333155 = 4999733) B4999733
theorem B8888413 : Blo 2079435 8888413 := bstep (se 3 (by rfl) ⟨1666577, by rfl⟩ : syracuseStep 8888413 = 3333155) B3333155
theorem B11851217 : Blo 2079435 11851217 := bstep (se 2 (by rfl) ⟨4444206, by rfl⟩ : syracuseStep 11851217 = 8888413) B8888413
theorem B7900811 : Blo 2079435 7900811 := bstep (se 1 (by rfl) ⟨5925608, by rfl⟩ : syracuseStep 7900811 = 11851217) B11851217
theorem B5267207 : Blo 2079435 5267207 := bstep (se 1 (by rfl) ⟨3950405, by rfl⟩ : syracuseStep 5267207 = 7900811) B7900811
theorem B3511471 : Blo 2079435 3511471 := bstep (se 1 (by rfl) ⟨2633603, by rfl⟩ : syracuseStep 3511471 = 5267207) B5267207
theorem B4681961 : Blo 2079435 4681961 := bstep (se 2 (by rfl) ⟨1755735, by rfl⟩ : syracuseStep 4681961 = 3511471) B3511471
theorem B3121307 : Blo 2079435 3121307 := bstep (se 1 (by rfl) ⟨2340980, by rfl⟩ : syracuseStep 3121307 = 4681961) B4681961
theorem B2080871 : Blo 2079435 2080871 := bstep (se 1 (by rfl) ⟨1560653, by rfl⟩ : syracuseStep 2080871 = 3121307) B3121307
theorem B2340985 : Blo 2079435 2340985 := bbase (se 2 (by rfl) ⟨877869, by rfl⟩ : syracuseStep 2340985 = 1755739) (by norm_num)
theorem B3121313 : Blo 2079435 3121313 := bstep (se 2 (by rfl) ⟨1170492, by rfl⟩ : syracuseStep 3121313 = 2340985) B2340985
theorem B2080875 : Blo 2079435 2080875 := bstep (se 1 (by rfl) ⟨1560656, by rfl⟩ : syracuseStep 2080875 = 3121313) B3121313
theorem B2252429 : Blo 2079435 2252429 := bbase (se 3 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 2252429 = 844661) (by norm_num)
theorem B24025909 : Blo 2079435 24025909 := bstep (se 5 (by rfl) ⟨1126214, by rfl⟩ : syracuseStep 24025909 = 2252429) B2252429
theorem B32034545 : Blo 2079435 32034545 := bstep (se 2 (by rfl) ⟨12012954, by rfl⟩ : syracuseStep 32034545 = 24025909) B24025909
theorem B21356363 : Blo 2079435 21356363 := bstep (se 1 (by rfl) ⟨16017272, by rfl⟩ : syracuseStep 21356363 = 32034545) B32034545
theorem B14237575 : Blo 2079435 14237575 := bstep (se 1 (by rfl) ⟨10678181, by rfl⟩ : syracuseStep 14237575 = 21356363) B21356363
theorem B75933733 : Blo 2079435 75933733 := bstep (se 4 (by rfl) ⟨7118787, by rfl⟩ : syracuseStep 75933733 = 14237575) B14237575
theorem B101244977 : Blo 2079435 101244977 := bstep (se 2 (by rfl) ⟨37966866, by rfl⟩ : syracuseStep 101244977 = 75933733) B75933733
theorem B67496651 : Blo 2079435 67496651 := bstep (se 1 (by rfl) ⟨50622488, by rfl⟩ : syracuseStep 67496651 = 101244977) B101244977
theorem B44997767 : Blo 2079435 44997767 := bstep (se 1 (by rfl) ⟨33748325, by rfl⟩ : syracuseStep 44997767 = 67496651) B67496651
theorem B29998511 : Blo 2079435 29998511 := bstep (se 1 (by rfl) ⟨22498883, by rfl⟩ : syracuseStep 29998511 = 44997767) B44997767
theorem B19999007 : Blo 2079435 19999007 := bstep (se 1 (by rfl) ⟨14999255, by rfl⟩ : syracuseStep 19999007 = 29998511) B29998511
theorem B13332671 : Blo 2079435 13332671 := bstep (se 1 (by rfl) ⟨9999503, by rfl⟩ : syracuseStep 13332671 = 19999007) B19999007
theorem B8888447 : Blo 2079435 8888447 := bstep (se 1 (by rfl) ⟨6666335, by rfl⟩ : syracuseStep 8888447 = 13332671) B13332671
theorem B5925631 : Blo 2079435 5925631 := bstep (se 1 (by rfl) ⟨4444223, by rfl⟩ : syracuseStep 5925631 = 8888447) B8888447
theorem B7900841 : Blo 2079435 7900841 := bstep (se 2 (by rfl) ⟨2962815, by rfl⟩ : syracuseStep 7900841 = 5925631) B5925631
theorem B5267227 : Blo 2079435 5267227 := bstep (se 1 (by rfl) ⟨3950420, by rfl⟩ : syracuseStep 5267227 = 7900841) B7900841
theorem B7022969 : Blo 2079435 7022969 := bstep (se 2 (by rfl) ⟨2633613, by rfl⟩ : syracuseStep 7022969 = 5267227) B5267227
theorem B4681979 : Blo 2079435 4681979 := bstep (se 1 (by rfl) ⟨3511484, by rfl⟩ : syracuseStep 4681979 = 7022969) B7022969
theorem B3121319 : Blo 2079435 3121319 := bstep (se 1 (by rfl) ⟨2340989, by rfl⟩ : syracuseStep 3121319 = 4681979) B4681979
theorem B2080879 : Blo 2079435 2080879 := bstep (se 1 (by rfl) ⟨1560659, by rfl⟩ : syracuseStep 2080879 = 3121319) B3121319
theorem B3121325 : Blo 2079435 3121325 := bbase (se 3 (by rfl) ⟨585248, by rfl⟩ : syracuseStep 3121325 = 1170497) (by norm_num)
theorem B2080883 : Blo 2079435 2080883 := bstep (se 1 (by rfl) ⟨1560662, by rfl⟩ : syracuseStep 2080883 = 3121325) B3121325
theorem B4681997 : Blo 2079435 4681997 := bbase (se 3 (by rfl) ⟨877874, by rfl⟩ : syracuseStep 4681997 = 1755749) (by norm_num)
theorem B3121331 : Blo 2079435 3121331 := bstep (se 1 (by rfl) ⟨2340998, by rfl⟩ : syracuseStep 3121331 = 4681997) B4681997
theorem B2080887 : Blo 2079435 2080887 := bstep (se 1 (by rfl) ⟨1560665, by rfl⟩ : syracuseStep 2080887 = 3121331) B3121331
theorem B2633629 : Blo 2079435 2633629 := bbase (se 3 (by rfl) ⟨493805, by rfl⟩ : syracuseStep 2633629 = 987611) (by norm_num)
theorem B3511505 : Blo 2079435 3511505 := bstep (se 2 (by rfl) ⟨1316814, by rfl⟩ : syracuseStep 3511505 = 2633629) B2633629
theorem B2341003 : Blo 2079435 2341003 := bstep (se 1 (by rfl) ⟨1755752, by rfl⟩ : syracuseStep 2341003 = 3511505) B3511505
theorem B3121337 : Blo 2079435 3121337 := bstep (se 2 (by rfl) ⟨1170501, by rfl⟩ : syracuseStep 3121337 = 2341003) B2341003
theorem B2080891 : Blo 2079435 2080891 := bstep (se 1 (by rfl) ⟨1560668, by rfl⟩ : syracuseStep 2080891 = 3121337) B3121337
theorem B2568577 : Blo 2079435 2568577 := bbase (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) (by norm_num)
theorem B3424769 : Blo 2079435 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B2283179 : Blo 2079435 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B6088477 : Blo 2079435 6088477 := bstep (se 3 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 6088477 = 2283179) B2283179
theorem B8117969 : Blo 2079435 8117969 := bstep (se 2 (by rfl) ⟨3044238, by rfl⟩ : syracuseStep 8117969 = 6088477) B6088477
theorem B21647917 : Blo 2079435 21647917 := bstep (se 3 (by rfl) ⟨4058984, by rfl⟩ : syracuseStep 21647917 = 8117969) B8117969
theorem B115455557 : Blo 2079435 115455557 := bstep (se 4 (by rfl) ⟨10823958, by rfl⟩ : syracuseStep 115455557 = 21647917) B21647917
theorem B307881485 : Blo 2079435 307881485 := bstep (se 3 (by rfl) ⟨57727778, by rfl⟩ : syracuseStep 307881485 = 115455557) B115455557
theorem B205254323 : Blo 2079435 205254323 := bstep (se 1 (by rfl) ⟨153940742, by rfl⟩ : syracuseStep 205254323 = 307881485) B307881485
theorem B136836215 : Blo 2079435 136836215 := bstep (se 1 (by rfl) ⟨102627161, by rfl⟩ : syracuseStep 136836215 = 205254323) B205254323
theorem B91224143 : Blo 2079435 91224143 := bstep (se 1 (by rfl) ⟨68418107, by rfl⟩ : syracuseStep 91224143 = 136836215) B136836215
theorem B60816095 : Blo 2079435 60816095 := bstep (se 1 (by rfl) ⟨45612071, by rfl⟩ : syracuseStep 60816095 = 91224143) B91224143
theorem B40544063 : Blo 2079435 40544063 := bstep (se 1 (by rfl) ⟨30408047, by rfl⟩ : syracuseStep 40544063 = 60816095) B60816095
theorem B27029375 : Blo 2079435 27029375 := bstep (se 1 (by rfl) ⟨20272031, by rfl⟩ : syracuseStep 27029375 = 40544063) B40544063
theorem B18019583 : Blo 2079435 18019583 := bstep (se 1 (by rfl) ⟨13514687, by rfl⟩ : syracuseStep 18019583 = 27029375) B27029375
theorem B12013055 : Blo 2079435 12013055 := bstep (se 1 (by rfl) ⟨9009791, by rfl⟩ : syracuseStep 12013055 = 18019583) B18019583
theorem B8008703 : Blo 2079435 8008703 := bstep (se 1 (by rfl) ⟨6006527, by rfl⟩ : syracuseStep 8008703 = 12013055) B12013055
theorem B5339135 : Blo 2079435 5339135 := bstep (se 1 (by rfl) ⟨4004351, by rfl⟩ : syracuseStep 5339135 = 8008703) B8008703
theorem B3559423 : Blo 2079435 3559423 := bstep (se 1 (by rfl) ⟨2669567, by rfl⟩ : syracuseStep 3559423 = 5339135) B5339135
theorem B4745897 : Blo 2079435 4745897 := bstep (se 2 (by rfl) ⟨1779711, by rfl⟩ : syracuseStep 4745897 = 3559423) B3559423
theorem B3163931 : Blo 2079435 3163931 := bstep (se 1 (by rfl) ⟨2372948, by rfl⟩ : syracuseStep 3163931 = 4745897) B4745897
theorem B2109287 : Blo 2079435 2109287 := bstep (se 1 (by rfl) ⟨1581965, by rfl⟩ : syracuseStep 2109287 = 3163931) B3163931
theorem B5624765 : Blo 2079435 5624765 := bstep (se 3 (by rfl) ⟨1054643, by rfl⟩ : syracuseStep 5624765 = 2109287) B2109287
theorem B3749843 : Blo 2079435 3749843 := bstep (se 1 (by rfl) ⟨2812382, by rfl⟩ : syracuseStep 3749843 = 5624765) B5624765
theorem B2499895 : Blo 2079435 2499895 := bstep (se 1 (by rfl) ⟨1874921, by rfl⟩ : syracuseStep 2499895 = 3749843) B3749843
theorem B3333193 : Blo 2079435 3333193 := bstep (se 2 (by rfl) ⟨1249947, by rfl⟩ : syracuseStep 3333193 = 2499895) B2499895
theorem B17777029 : Blo 2079435 17777029 := bstep (se 4 (by rfl) ⟨1666596, by rfl⟩ : syracuseStep 17777029 = 3333193) B3333193
theorem B23702705 : Blo 2079435 23702705 := bstep (se 2 (by rfl) ⟨8888514, by rfl⟩ : syracuseStep 23702705 = 17777029) B17777029
theorem B15801803 : Blo 2079435 15801803 := bstep (se 1 (by rfl) ⟨11851352, by rfl⟩ : syracuseStep 15801803 = 23702705) B23702705
theorem B10534535 : Blo 2079435 10534535 := bstep (se 1 (by rfl) ⟨7900901, by rfl⟩ : syracuseStep 10534535 = 15801803) B15801803
theorem B7023023 : Blo 2079435 7023023 := bstep (se 1 (by rfl) ⟨5267267, by rfl⟩ : syracuseStep 7023023 = 10534535) B10534535
theorem B4682015 : Blo 2079435 4682015 := bstep (se 1 (by rfl) ⟨3511511, by rfl⟩ : syracuseStep 4682015 = 7023023) B7023023
theorem B3121343 : Blo 2079435 3121343 := bstep (se 1 (by rfl) ⟨2341007, by rfl⟩ : syracuseStep 3121343 = 4682015) B4682015
theorem B2080895 : Blo 2079435 2080895 := bstep (se 1 (by rfl) ⟨1560671, by rfl⟩ : syracuseStep 2080895 = 3121343) B3121343
theorem B3121349 : Blo 2079435 3121349 := bbase (se 4 (by rfl) ⟨292626, by rfl⟩ : syracuseStep 3121349 = 585253) (by norm_num)
theorem B2080899 : Blo 2079435 2080899 := bstep (se 1 (by rfl) ⟨1560674, by rfl⟩ : syracuseStep 2080899 = 3121349) B3121349
theorem B3511525 : Blo 2079435 3511525 := bbase (se 4 (by rfl) ⟨329205, by rfl⟩ : syracuseStep 3511525 = 658411) (by norm_num)
theorem B4682033 : Blo 2079435 4682033 := bstep (se 2 (by rfl) ⟨1755762, by rfl⟩ : syracuseStep 4682033 = 3511525) B3511525
theorem B3121355 : Blo 2079435 3121355 := bstep (se 1 (by rfl) ⟨2341016, by rfl⟩ : syracuseStep 3121355 = 4682033) B4682033
theorem B2080903 : Blo 2079435 2080903 := bstep (se 1 (by rfl) ⟨1560677, by rfl⟩ : syracuseStep 2080903 = 3121355) B3121355
theorem B2341021 : Blo 2079435 2341021 := bbase (se 3 (by rfl) ⟨438941, by rfl⟩ : syracuseStep 2341021 = 877883) (by norm_num)
theorem B3121361 : Blo 2079435 3121361 := bstep (se 2 (by rfl) ⟨1170510, by rfl⟩ : syracuseStep 3121361 = 2341021) B2341021
theorem B2080907 : Blo 2079435 2080907 := bstep (se 1 (by rfl) ⟨1560680, by rfl⟩ : syracuseStep 2080907 = 3121361) B3121361
theorem B7023077 : Blo 2079435 7023077 := bbase (se 4 (by rfl) ⟨658413, by rfl⟩ : syracuseStep 7023077 = 1316827) (by norm_num)
theorem B4682051 : Blo 2079435 4682051 := bstep (se 1 (by rfl) ⟨3511538, by rfl⟩ : syracuseStep 4682051 = 7023077) B7023077
theorem B3121367 : Blo 2079435 3121367 := bstep (se 1 (by rfl) ⟨2341025, by rfl⟩ : syracuseStep 3121367 = 4682051) B4682051
theorem B2080911 : Blo 2079435 2080911 := bstep (se 1 (by rfl) ⟨1560683, by rfl⟩ : syracuseStep 2080911 = 3121367) B3121367
theorem B3121373 : Blo 2079435 3121373 := bbase (se 3 (by rfl) ⟨585257, by rfl⟩ : syracuseStep 3121373 = 1170515) (by norm_num)
theorem B2080915 : Blo 2079435 2080915 := bstep (se 1 (by rfl) ⟨1560686, by rfl⟩ : syracuseStep 2080915 = 3121373) B3121373
theorem B4682069 : Blo 2079435 4682069 := bbase (se 10 (by rfl) ⟨6858, by rfl⟩ : syracuseStep 4682069 = 13717) (by norm_num)
theorem B3121379 : Blo 2079435 3121379 := bstep (se 1 (by rfl) ⟨2341034, by rfl⟩ : syracuseStep 3121379 = 4682069) B4682069
theorem B2080919 : Blo 2079435 2080919 := bstep (se 1 (by rfl) ⟨1560689, by rfl⟩ : syracuseStep 2080919 = 3121379) B3121379
theorem B2812421 : Blo 2079435 2812421 := bbase (se 4 (by rfl) ⟨263664, by rfl⟩ : syracuseStep 2812421 = 527329) (by norm_num)
theorem B7499789 : Blo 2079435 7499789 := bstep (se 3 (by rfl) ⟨1406210, by rfl⟩ : syracuseStep 7499789 = 2812421) B2812421
theorem B4999859 : Blo 2079435 4999859 := bstep (se 1 (by rfl) ⟨3749894, by rfl⟩ : syracuseStep 4999859 = 7499789) B7499789
theorem B3333239 : Blo 2079435 3333239 := bstep (se 1 (by rfl) ⟨2499929, by rfl⟩ : syracuseStep 3333239 = 4999859) B4999859
theorem B2222159 : Blo 2079435 2222159 := bstep (se 1 (by rfl) ⟨1666619, by rfl⟩ : syracuseStep 2222159 = 3333239) B3333239
theorem B5925757 : Blo 2079435 5925757 := bstep (se 3 (by rfl) ⟨1111079, by rfl⟩ : syracuseStep 5925757 = 2222159) B2222159
theorem B7901009 : Blo 2079435 7901009 := bstep (se 2 (by rfl) ⟨2962878, by rfl⟩ : syracuseStep 7901009 = 5925757) B5925757
theorem B5267339 : Blo 2079435 5267339 := bstep (se 1 (by rfl) ⟨3950504, by rfl⟩ : syracuseStep 5267339 = 7901009) B7901009
theorem B3511559 : Blo 2079435 3511559 := bstep (se 1 (by rfl) ⟨2633669, by rfl⟩ : syracuseStep 3511559 = 5267339) B5267339
theorem B2341039 : Blo 2079435 2341039 := bstep (se 1 (by rfl) ⟨1755779, by rfl⟩ : syracuseStep 2341039 = 3511559) B3511559
theorem B3121385 : Blo 2079435 3121385 := bstep (se 2 (by rfl) ⟨1170519, by rfl⟩ : syracuseStep 3121385 = 2341039) B2341039
theorem B2080923 : Blo 2079435 2080923 := bstep (se 1 (by rfl) ⟨1560692, by rfl⟩ : syracuseStep 2080923 = 3121385) B3121385
theorem B39998933 : Blo 2079435 39998933 := bbase (se 7 (by rfl) ⟨468737, by rfl⟩ : syracuseStep 39998933 = 937475) (by norm_num)
theorem B26665955 : Blo 2079435 26665955 := bstep (se 1 (by rfl) ⟨19999466, by rfl⟩ : syracuseStep 26665955 = 39998933) B39998933
theorem B17777303 : Blo 2079435 17777303 := bstep (se 1 (by rfl) ⟨13332977, by rfl⟩ : syracuseStep 17777303 = 26665955) B26665955
theorem B11851535 : Blo 2079435 11851535 := bstep (se 1 (by rfl) ⟨8888651, by rfl⟩ : syracuseStep 11851535 = 17777303) B17777303
theorem B7901023 : Blo 2079435 7901023 := bstep (se 1 (by rfl) ⟨5925767, by rfl⟩ : syracuseStep 7901023 = 11851535) B11851535
theorem B10534697 : Blo 2079435 10534697 := bstep (se 2 (by rfl) ⟨3950511, by rfl⟩ : syracuseStep 10534697 = 7901023) B7901023
theorem B7023131 : Blo 2079435 7023131 := bstep (se 1 (by rfl) ⟨5267348, by rfl⟩ : syracuseStep 7023131 = 10534697) B10534697
theorem B4682087 : Blo 2079435 4682087 := bstep (se 1 (by rfl) ⟨3511565, by rfl⟩ : syracuseStep 4682087 = 7023131) B7023131
theorem B3121391 : Blo 2079435 3121391 := bstep (se 1 (by rfl) ⟨2341043, by rfl⟩ : syracuseStep 3121391 = 4682087) B4682087
theorem B2080927 : Blo 2079435 2080927 := bstep (se 1 (by rfl) ⟨1560695, by rfl⟩ : syracuseStep 2080927 = 3121391) B3121391
theorem B3121397 : Blo 2079435 3121397 := bbase (se 5 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 3121397 = 292631) (by norm_num)
theorem B2080931 : Blo 2079435 2080931 := bstep (se 1 (by rfl) ⟨1560698, by rfl⟩ : syracuseStep 2080931 = 3121397) B3121397
theorem B7118981 : Blo 2079435 7118981 := bbase (se 4 (by rfl) ⟨667404, by rfl⟩ : syracuseStep 7118981 = 1334809) (by norm_num)
theorem B4745987 : Blo 2079435 4745987 := bstep (se 1 (by rfl) ⟨3559490, by rfl⟩ : syracuseStep 4745987 = 7118981) B7118981
theorem B3163991 : Blo 2079435 3163991 := bstep (se 1 (by rfl) ⟨2372993, by rfl⟩ : syracuseStep 3163991 = 4745987) B4745987
theorem B33749237 : Blo 2079435 33749237 := bstep (se 5 (by rfl) ⟨1581995, by rfl⟩ : syracuseStep 33749237 = 3163991) B3163991
theorem B22499491 : Blo 2079435 22499491 := bstep (se 1 (by rfl) ⟨16874618, by rfl⟩ : syracuseStep 22499491 = 33749237) B33749237
theorem B29999321 : Blo 2079435 29999321 := bstep (se 2 (by rfl) ⟨11249745, by rfl⟩ : syracuseStep 29999321 = 22499491) B22499491
theorem B19999547 : Blo 2079435 19999547 := bstep (se 1 (by rfl) ⟨14999660, by rfl⟩ : syracuseStep 19999547 = 29999321) B29999321
theorem B13333031 : Blo 2079435 13333031 := bstep (se 1 (by rfl) ⟨9999773, by rfl⟩ : syracuseStep 13333031 = 19999547) B19999547
theorem B8888687 : Blo 2079435 8888687 := bstep (se 1 (by rfl) ⟨6666515, by rfl⟩ : syracuseStep 8888687 = 13333031) B13333031
theorem B5925791 : Blo 2079435 5925791 := bstep (se 1 (by rfl) ⟨4444343, by rfl⟩ : syracuseStep 5925791 = 8888687) B8888687
theorem B3950527 : Blo 2079435 3950527 := bstep (se 1 (by rfl) ⟨2962895, by rfl⟩ : syracuseStep 3950527 = 5925791) B5925791
theorem B5267369 : Blo 2079435 5267369 := bstep (se 2 (by rfl) ⟨1975263, by rfl⟩ : syracuseStep 5267369 = 3950527) B3950527
theorem B3511579 : Blo 2079435 3511579 := bstep (se 1 (by rfl) ⟨2633684, by rfl⟩ : syracuseStep 3511579 = 5267369) B5267369
theorem B4682105 : Blo 2079435 4682105 := bstep (se 2 (by rfl) ⟨1755789, by rfl⟩ : syracuseStep 4682105 = 3511579) B3511579
theorem B3121403 : Blo 2079435 3121403 := bstep (se 1 (by rfl) ⟨2341052, by rfl⟩ : syracuseStep 3121403 = 4682105) B4682105
theorem B2080935 : Blo 2079435 2080935 := bstep (se 1 (by rfl) ⟨1560701, by rfl⟩ : syracuseStep 2080935 = 3121403) B3121403
theorem B2341057 : Blo 2079435 2341057 := bbase (se 2 (by rfl) ⟨877896, by rfl⟩ : syracuseStep 2341057 = 1755793) (by norm_num)
theorem B3121409 : Blo 2079435 3121409 := bstep (se 2 (by rfl) ⟨1170528, by rfl⟩ : syracuseStep 3121409 = 2341057) B2341057
theorem B2080939 : Blo 2079435 2080939 := bstep (se 1 (by rfl) ⟨1560704, by rfl⟩ : syracuseStep 2080939 = 3121409) B3121409
theorem B5267389 : Blo 2079435 5267389 := bbase (se 3 (by rfl) ⟨987635, by rfl⟩ : syracuseStep 5267389 = 1975271) (by norm_num)
theorem B7023185 : Blo 2079435 7023185 := bstep (se 2 (by rfl) ⟨2633694, by rfl⟩ : syracuseStep 7023185 = 5267389) B5267389
theorem B4682123 : Blo 2079435 4682123 := bstep (se 1 (by rfl) ⟨3511592, by rfl⟩ : syracuseStep 4682123 = 7023185) B7023185
theorem B3121415 : Blo 2079435 3121415 := bstep (se 1 (by rfl) ⟨2341061, by rfl⟩ : syracuseStep 3121415 = 4682123) B4682123
theorem B2080943 : Blo 2079435 2080943 := bstep (se 1 (by rfl) ⟨1560707, by rfl⟩ : syracuseStep 2080943 = 3121415) B3121415
theorem B3121421 : Blo 2079435 3121421 := bbase (se 3 (by rfl) ⟨585266, by rfl⟩ : syracuseStep 3121421 = 1170533) (by norm_num)
theorem B2080947 : Blo 2079435 2080947 := bstep (se 1 (by rfl) ⟨1560710, by rfl⟩ : syracuseStep 2080947 = 3121421) B3121421
theorem B4682141 : Blo 2079435 4682141 := bbase (se 3 (by rfl) ⟨877901, by rfl⟩ : syracuseStep 4682141 = 1755803) (by norm_num)
theorem B3121427 : Blo 2079435 3121427 := bstep (se 1 (by rfl) ⟨2341070, by rfl⟩ : syracuseStep 3121427 = 4682141) B4682141
theorem B2080951 : Blo 2079435 2080951 := bstep (se 1 (by rfl) ⟨1560713, by rfl⟩ : syracuseStep 2080951 = 3121427) B3121427
theorem B3511613 : Blo 2079435 3511613 := bbase (se 3 (by rfl) ⟨658427, by rfl⟩ : syracuseStep 3511613 = 1316855) (by norm_num)
theorem B2341075 : Blo 2079435 2341075 := bstep (se 1 (by rfl) ⟨1755806, by rfl⟩ : syracuseStep 2341075 = 3511613) B3511613
theorem B3121433 : Blo 2079435 3121433 := bstep (se 2 (by rfl) ⟨1170537, by rfl⟩ : syracuseStep 3121433 = 2341075) B2341075
theorem B2080955 : Blo 2079435 2080955 := bstep (se 1 (by rfl) ⟨1560716, by rfl⟩ : syracuseStep 2080955 = 3121433) B3121433
theorem B2222197 : Blo 2079435 2222197 := bbase (se 5 (by rfl) ⟨104165, by rfl⟩ : syracuseStep 2222197 = 208331) (by norm_num)
theorem B11851717 : Blo 2079435 11851717 := bstep (se 4 (by rfl) ⟨1111098, by rfl⟩ : syracuseStep 11851717 = 2222197) B2222197
theorem B15802289 : Blo 2079435 15802289 := bstep (se 2 (by rfl) ⟨5925858, by rfl⟩ : syracuseStep 15802289 = 11851717) B11851717
theorem B10534859 : Blo 2079435 10534859 := bstep (se 1 (by rfl) ⟨7901144, by rfl⟩ : syracuseStep 10534859 = 15802289) B15802289
theorem B7023239 : Blo 2079435 7023239 := bstep (se 1 (by rfl) ⟨5267429, by rfl⟩ : syracuseStep 7023239 = 10534859) B10534859
theorem B4682159 : Blo 2079435 4682159 := bstep (se 1 (by rfl) ⟨3511619, by rfl⟩ : syracuseStep 4682159 = 7023239) B7023239
theorem B3121439 : Blo 2079435 3121439 := bstep (se 1 (by rfl) ⟨2341079, by rfl⟩ : syracuseStep 3121439 = 4682159) B4682159
theorem B2080959 : Blo 2079435 2080959 := bstep (se 1 (by rfl) ⟨1560719, by rfl⟩ : syracuseStep 2080959 = 3121439) B3121439
theorem B3121445 : Blo 2079435 3121445 := bbase (se 4 (by rfl) ⟨292635, by rfl⟩ : syracuseStep 3121445 = 585271) (by norm_num)
theorem B2080963 : Blo 2079435 2080963 := bstep (se 1 (by rfl) ⟨1560722, by rfl⟩ : syracuseStep 2080963 = 3121445) B3121445
theorem B2633725 : Blo 2079435 2633725 := bbase (se 3 (by rfl) ⟨493823, by rfl⟩ : syracuseStep 2633725 = 987647) (by norm_num)
theorem B3511633 : Blo 2079435 3511633 := bstep (se 2 (by rfl) ⟨1316862, by rfl⟩ : syracuseStep 3511633 = 2633725) B2633725
theorem B4682177 : Blo 2079435 4682177 := bstep (se 2 (by rfl) ⟨1755816, by rfl⟩ : syracuseStep 4682177 = 3511633) B3511633
theorem B3121451 : Blo 2079435 3121451 := bstep (se 1 (by rfl) ⟨2341088, by rfl⟩ : syracuseStep 3121451 = 4682177) B4682177
theorem B2080967 : Blo 2079435 2080967 := bstep (se 1 (by rfl) ⟨1560725, by rfl⟩ : syracuseStep 2080967 = 3121451) B3121451
theorem B2341093 : Blo 2079435 2341093 := bbase (se 4 (by rfl) ⟨219477, by rfl⟩ : syracuseStep 2341093 = 438955) (by norm_num)
theorem B3121457 : Blo 2079435 3121457 := bstep (se 2 (by rfl) ⟨1170546, by rfl⟩ : syracuseStep 3121457 = 2341093) B2341093
theorem B2080971 : Blo 2079435 2080971 := bstep (se 1 (by rfl) ⟨1560728, by rfl⟩ : syracuseStep 2080971 = 3121457) B3121457
theorem B4444429 : Blo 2079435 4444429 := bbase (se 3 (by rfl) ⟨833330, by rfl⟩ : syracuseStep 4444429 = 1666661) (by norm_num)
theorem B5925905 : Blo 2079435 5925905 := bstep (se 2 (by rfl) ⟨2222214, by rfl⟩ : syracuseStep 5925905 = 4444429) B4444429
theorem B3950603 : Blo 2079435 3950603 := bstep (se 1 (by rfl) ⟨2962952, by rfl⟩ : syracuseStep 3950603 = 5925905) B5925905
theorem B2633735 : Blo 2079435 2633735 := bstep (se 1 (by rfl) ⟨1975301, by rfl⟩ : syracuseStep 2633735 = 3950603) B3950603
theorem B7023293 : Blo 2079435 7023293 := bstep (se 3 (by rfl) ⟨1316867, by rfl⟩ : syracuseStep 7023293 = 2633735) B2633735
theorem B4682195 : Blo 2079435 4682195 := bstep (se 1 (by rfl) ⟨3511646, by rfl⟩ : syracuseStep 4682195 = 7023293) B7023293
theorem B3121463 : Blo 2079435 3121463 := bstep (se 1 (by rfl) ⟨2341097, by rfl⟩ : syracuseStep 3121463 = 4682195) B4682195
theorem B2080975 : Blo 2079435 2080975 := bstep (se 1 (by rfl) ⟨1560731, by rfl⟩ : syracuseStep 2080975 = 3121463) B3121463
theorem B3121469 : Blo 2079435 3121469 := bbase (se 3 (by rfl) ⟨585275, by rfl⟩ : syracuseStep 3121469 = 1170551) (by norm_num)
theorem B2080979 : Blo 2079435 2080979 := bstep (se 1 (by rfl) ⟨1560734, by rfl⟩ : syracuseStep 2080979 = 3121469) B3121469
theorem B4682213 : Blo 2079435 4682213 := bbase (se 4 (by rfl) ⟨438957, by rfl⟩ : syracuseStep 4682213 = 877915) (by norm_num)
theorem B3121475 : Blo 2079435 3121475 := bstep (se 1 (by rfl) ⟨2341106, by rfl⟩ : syracuseStep 3121475 = 4682213) B4682213
theorem B2080983 : Blo 2079435 2080983 := bstep (se 1 (by rfl) ⟨1560737, by rfl⟩ : syracuseStep 2080983 = 3121475) B3121475
theorem B5267501 : Blo 2079435 5267501 := bbase (se 3 (by rfl) ⟨987656, by rfl⟩ : syracuseStep 5267501 = 1975313) (by norm_num)
theorem B3511667 : Blo 2079435 3511667 := bstep (se 1 (by rfl) ⟨2633750, by rfl⟩ : syracuseStep 3511667 = 5267501) B5267501
theorem B2341111 : Blo 2079435 2341111 := bstep (se 1 (by rfl) ⟨1755833, by rfl⟩ : syracuseStep 2341111 = 3511667) B3511667
theorem B3121481 : Blo 2079435 3121481 := bstep (se 2 (by rfl) ⟨1170555, by rfl⟩ : syracuseStep 3121481 = 2341111) B2341111
theorem B2080987 : Blo 2079435 2080987 := bstep (se 1 (by rfl) ⟨1560740, by rfl⟩ : syracuseStep 2080987 = 3121481) B3121481
theorem B7119173 : Blo 2079435 7119173 := bbase (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) (by norm_num)
theorem B4746115 : Blo 2079435 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B6328153 : Blo 2079435 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B8437537 : Blo 2079435 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B11250049 : Blo 2079435 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B15000065 : Blo 2079435 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B10000043 : Blo 2079435 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B6666695 : Blo 2079435 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B4444463 : Blo 2079435 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B2962975 : Blo 2079435 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B3950633 : Blo 2079435 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B10535021 : Blo 2079435 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B7023347 : Blo 2079435 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B4682231 : Blo 2079435 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B3121487 : Blo 2079435 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B2080991 : Blo 2079435 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B3121493 : Blo 2079435 3121493 := bbase (se 10 (by rfl) ⟨4572, by rfl⟩ : syracuseStep 3121493 = 9145) (by norm_num)
theorem B2080995 : Blo 2079435 2080995 := bstep (se 1 (by rfl) ⟨1560746, by rfl⟩ : syracuseStep 2080995 = 3121493) B3121493
theorem B5925973 : Blo 2079435 5925973 := bbase (se 8 (by rfl) ⟨34722, by rfl⟩ : syracuseStep 5925973 = 69445) (by norm_num)
theorem B7901297 : Blo 2079435 7901297 := bstep (se 2 (by rfl) ⟨2962986, by rfl⟩ : syracuseStep 7901297 = 5925973) B5925973
theorem B5267531 : Blo 2079435 5267531 := bstep (se 1 (by rfl) ⟨3950648, by rfl⟩ : syracuseStep 5267531 = 7901297) B7901297
theorem B3511687 : Blo 2079435 3511687 := bstep (se 1 (by rfl) ⟨2633765, by rfl⟩ : syracuseStep 3511687 = 5267531) B5267531
theorem B4682249 : Blo 2079435 4682249 := bstep (se 2 (by rfl) ⟨1755843, by rfl⟩ : syracuseStep 4682249 = 3511687) B3511687
theorem B3121499 : Blo 2079435 3121499 := bstep (se 1 (by rfl) ⟨2341124, by rfl⟩ : syracuseStep 3121499 = 4682249) B4682249
theorem B2080999 : Blo 2079435 2080999 := bstep (se 1 (by rfl) ⟨1560749, by rfl⟩ : syracuseStep 2080999 = 3121499) B3121499
theorem B2341129 : Blo 2079435 2341129 := bbase (se 2 (by rfl) ⟨877923, by rfl⟩ : syracuseStep 2341129 = 1755847) (by norm_num)
theorem B3121505 : Blo 2079435 3121505 := bstep (se 2 (by rfl) ⟨1170564, by rfl⟩ : syracuseStep 3121505 = 2341129) B2341129
theorem B2081003 : Blo 2079435 2081003 := bstep (se 1 (by rfl) ⟨1560752, by rfl⟩ : syracuseStep 2081003 = 3121505) B3121505
theorem B2889805 : Blo 2079435 2889805 := bbase (se 3 (by rfl) ⟨541838, by rfl⟩ : syracuseStep 2889805 = 1083677) (by norm_num)
theorem B3853073 : Blo 2079435 3853073 := bstep (se 2 (by rfl) ⟨1444902, by rfl⟩ : syracuseStep 3853073 = 2889805) B2889805
theorem B2568715 : Blo 2079435 2568715 := bstep (se 1 (by rfl) ⟨1926536, by rfl⟩ : syracuseStep 2568715 = 3853073) B3853073
theorem B13699813 : Blo 2079435 13699813 := bstep (se 4 (by rfl) ⟨1284357, by rfl⟩ : syracuseStep 13699813 = 2568715) B2568715
theorem B18266417 : Blo 2079435 18266417 := bstep (se 2 (by rfl) ⟨6849906, by rfl⟩ : syracuseStep 18266417 = 13699813) B13699813
theorem B12177611 : Blo 2079435 12177611 := bstep (se 1 (by rfl) ⟨9133208, by rfl⟩ : syracuseStep 12177611 = 18266417) B18266417
theorem B8118407 : Blo 2079435 8118407 := bstep (se 1 (by rfl) ⟨6088805, by rfl⟩ : syracuseStep 8118407 = 12177611) B12177611
theorem B5412271 : Blo 2079435 5412271 := bstep (se 1 (by rfl) ⟨4059203, by rfl⟩ : syracuseStep 5412271 = 8118407) B8118407
theorem B7216361 : Blo 2079435 7216361 := bstep (se 2 (by rfl) ⟨2706135, by rfl⟩ : syracuseStep 7216361 = 5412271) B5412271
theorem B4810907 : Blo 2079435 4810907 := bstep (se 1 (by rfl) ⟨3608180, by rfl⟩ : syracuseStep 4810907 = 7216361) B7216361
theorem B3207271 : Blo 2079435 3207271 := bstep (se 1 (by rfl) ⟨2405453, by rfl⟩ : syracuseStep 3207271 = 4810907) B4810907
theorem B4276361 : Blo 2079435 4276361 := bstep (se 2 (by rfl) ⟨1603635, by rfl⟩ : syracuseStep 4276361 = 3207271) B3207271
theorem B11403629 : Blo 2079435 11403629 := bstep (se 3 (by rfl) ⟨2138180, by rfl⟩ : syracuseStep 11403629 = 4276361) B4276361
theorem B7602419 : Blo 2079435 7602419 := bstep (se 1 (by rfl) ⟨5701814, by rfl⟩ : syracuseStep 7602419 = 11403629) B11403629
theorem B5068279 : Blo 2079435 5068279 := bstep (se 1 (by rfl) ⟨3801209, by rfl⟩ : syracuseStep 5068279 = 7602419) B7602419
theorem B6757705 : Blo 2079435 6757705 := bstep (se 2 (by rfl) ⟨2534139, by rfl⟩ : syracuseStep 6757705 = 5068279) B5068279
theorem B9010273 : Blo 2079435 9010273 := bstep (se 2 (by rfl) ⟨3378852, by rfl⟩ : syracuseStep 9010273 = 6757705) B6757705
theorem B12013697 : Blo 2079435 12013697 := bstep (se 2 (by rfl) ⟨4505136, by rfl⟩ : syracuseStep 12013697 = 9010273) B9010273
theorem B8009131 : Blo 2079435 8009131 := bstep (se 1 (by rfl) ⟨6006848, by rfl⟩ : syracuseStep 8009131 = 12013697) B12013697
theorem B10678841 : Blo 2079435 10678841 := bstep (se 2 (by rfl) ⟨4004565, by rfl⟩ : syracuseStep 10678841 = 8009131) B8009131
theorem B7119227 : Blo 2079435 7119227 := bstep (se 1 (by rfl) ⟨5339420, by rfl⟩ : syracuseStep 7119227 = 10678841) B10678841
theorem B4746151 : Blo 2079435 4746151 := bstep (se 1 (by rfl) ⟨3559613, by rfl⟩ : syracuseStep 4746151 = 7119227) B7119227
theorem B6328201 : Blo 2079435 6328201 := bstep (se 2 (by rfl) ⟨2373075, by rfl⟩ : syracuseStep 6328201 = 4746151) B4746151
theorem B8437601 : Blo 2079435 8437601 := bstep (se 2 (by rfl) ⟨3164100, by rfl⟩ : syracuseStep 8437601 = 6328201) B6328201
theorem B5625067 : Blo 2079435 5625067 := bstep (se 1 (by rfl) ⟨4218800, by rfl⟩ : syracuseStep 5625067 = 8437601) B8437601
theorem B7500089 : Blo 2079435 7500089 := bstep (se 2 (by rfl) ⟨2812533, by rfl⟩ : syracuseStep 7500089 = 5625067) B5625067
theorem B5000059 : Blo 2079435 5000059 := bstep (se 1 (by rfl) ⟨3750044, by rfl⟩ : syracuseStep 5000059 = 7500089) B7500089
theorem B26666981 : Blo 2079435 26666981 := bstep (se 4 (by rfl) ⟨2500029, by rfl⟩ : syracuseStep 26666981 = 5000059) B5000059
theorem B17777987 : Blo 2079435 17777987 := bstep (se 1 (by rfl) ⟨13333490, by rfl⟩ : syracuseStep 17777987 = 26666981) B26666981
theorem B11851991 : Blo 2079435 11851991 := bstep (se 1 (by rfl) ⟨8888993, by rfl⟩ : syracuseStep 11851991 = 17777987) B17777987
theorem B7901327 : Blo 2079435 7901327 := bstep (se 1 (by rfl) ⟨5925995, by rfl⟩ : syracuseStep 7901327 = 11851991) B11851991
theorem B5267551 : Blo 2079435 5267551 := bstep (se 1 (by rfl) ⟨3950663, by rfl⟩ : syracuseStep 5267551 = 7901327) B7901327
theorem B7023401 : Blo 2079435 7023401 := bstep (se 2 (by rfl) ⟨2633775, by rfl⟩ : syracuseStep 7023401 = 5267551) B5267551
theorem B4682267 : Blo 2079435 4682267 := bstep (se 1 (by rfl) ⟨3511700, by rfl⟩ : syracuseStep 4682267 = 7023401) B7023401
theorem B3121511 : Blo 2079435 3121511 := bstep (se 1 (by rfl) ⟨2341133, by rfl⟩ : syracuseStep 3121511 = 4682267) B4682267
theorem B2081007 : Blo 2079435 2081007 := bstep (se 1 (by rfl) ⟨1560755, by rfl⟩ : syracuseStep 2081007 = 3121511) B3121511
theorem B3121517 : Blo 2079435 3121517 := bbase (se 3 (by rfl) ⟨585284, by rfl⟩ : syracuseStep 3121517 = 1170569) (by norm_num)
theorem B2081011 : Blo 2079435 2081011 := bstep (se 1 (by rfl) ⟨1560758, by rfl⟩ : syracuseStep 2081011 = 3121517) B3121517
theorem B4682285 : Blo 2079435 4682285 := bbase (se 3 (by rfl) ⟨877928, by rfl⟩ : syracuseStep 4682285 = 1755857) (by norm_num)
theorem B3121523 : Blo 2079435 3121523 := bstep (se 1 (by rfl) ⟨2341142, by rfl⟩ : syracuseStep 3121523 = 4682285) B4682285
theorem B2081015 : Blo 2079435 2081015 := bstep (se 1 (by rfl) ⟨1560761, by rfl⟩ : syracuseStep 2081015 = 3121523) B3121523
theorem B2109413 : Blo 2079435 2109413 := bbase (se 4 (by rfl) ⟨197757, by rfl⟩ : syracuseStep 2109413 = 395515) (by norm_num)
theorem B5625101 : Blo 2079435 5625101 := bstep (se 3 (by rfl) ⟨1054706, by rfl⟩ : syracuseStep 5625101 = 2109413) B2109413
theorem B3750067 : Blo 2079435 3750067 := bstep (se 1 (by rfl) ⟨2812550, by rfl⟩ : syracuseStep 3750067 = 5625101) B5625101
theorem B20000357 : Blo 2079435 20000357 := bstep (se 4 (by rfl) ⟨1875033, by rfl⟩ : syracuseStep 20000357 = 3750067) B3750067
theorem B13333571 : Blo 2079435 13333571 := bstep (se 1 (by rfl) ⟨10000178, by rfl⟩ : syracuseStep 13333571 = 20000357) B20000357
theorem B8889047 : Blo 2079435 8889047 := bstep (se 1 (by rfl) ⟨6666785, by rfl⟩ : syracuseStep 8889047 = 13333571) B13333571
theorem B5926031 : Blo 2079435 5926031 := bstep (se 1 (by rfl) ⟨4444523, by rfl⟩ : syracuseStep 5926031 = 8889047) B8889047
theorem B3950687 : Blo 2079435 3950687 := bstep (se 1 (by rfl) ⟨2963015, by rfl⟩ : syracuseStep 3950687 = 5926031) B5926031
theorem B2633791 : Blo 2079435 2633791 := bstep (se 1 (by rfl) ⟨1975343, by rfl⟩ : syracuseStep 2633791 = 3950687) B3950687
theorem B3511721 : Blo 2079435 3511721 := bstep (se 2 (by rfl) ⟨1316895, by rfl⟩ : syracuseStep 3511721 = 2633791) B2633791
theorem B2341147 : Blo 2079435 2341147 := bstep (se 1 (by rfl) ⟨1755860, by rfl⟩ : syracuseStep 2341147 = 3511721) B3511721
theorem B3121529 : Blo 2079435 3121529 := bstep (se 2 (by rfl) ⟨1170573, by rfl⟩ : syracuseStep 3121529 = 2341147) B2341147
theorem B2081019 : Blo 2079435 2081019 := bstep (se 1 (by rfl) ⟨1560764, by rfl⟩ : syracuseStep 2081019 = 3121529) B3121529
theorem B35556245 : Blo 2079435 35556245 := bbase (se 6 (by rfl) ⟨833349, by rfl⟩ : syracuseStep 35556245 = 1666699) (by norm_num)
theorem B23704163 : Blo 2079435 23704163 := bstep (se 1 (by rfl) ⟨17778122, by rfl⟩ : syracuseStep 23704163 = 35556245) B35556245
theorem B15802775 : Blo 2079435 15802775 := bstep (se 1 (by rfl) ⟨11852081, by rfl⟩ : syracuseStep 15802775 = 23704163) B23704163
theorem B10535183 : Blo 2079435 10535183 := bstep (se 1 (by rfl) ⟨7901387, by rfl⟩ : syracuseStep 10535183 = 15802775) B15802775
theorem B7023455 : Blo 2079435 7023455 := bstep (se 1 (by rfl) ⟨5267591, by rfl⟩ : syracuseStep 7023455 = 10535183) B10535183
theorem B4682303 : Blo 2079435 4682303 := bstep (se 1 (by rfl) ⟨3511727, by rfl⟩ : syracuseStep 4682303 = 7023455) B7023455
theorem B3121535 : Blo 2079435 3121535 := bstep (se 1 (by rfl) ⟨2341151, by rfl⟩ : syracuseStep 3121535 = 4682303) B4682303
theorem B2081023 : Blo 2079435 2081023 := bstep (se 1 (by rfl) ⟨1560767, by rfl⟩ : syracuseStep 2081023 = 3121535) B3121535
theorem B3121541 : Blo 2079435 3121541 := bbase (se 4 (by rfl) ⟨292644, by rfl⟩ : syracuseStep 3121541 = 585289) (by norm_num)
theorem B2081027 : Blo 2079435 2081027 := bstep (se 1 (by rfl) ⟨1560770, by rfl⟩ : syracuseStep 2081027 = 3121541) B3121541
theorem B3511741 : Blo 2079435 3511741 := bbase (se 3 (by rfl) ⟨658451, by rfl⟩ : syracuseStep 3511741 = 1316903) (by norm_num)
theorem B4682321 : Blo 2079435 4682321 := bstep (se 2 (by rfl) ⟨1755870, by rfl⟩ : syracuseStep 4682321 = 3511741) B3511741
theorem B3121547 : Blo 2079435 3121547 := bstep (se 1 (by rfl) ⟨2341160, by rfl⟩ : syracuseStep 3121547 = 4682321) B4682321
theorem B2081031 : Blo 2079435 2081031 := bstep (se 1 (by rfl) ⟨1560773, by rfl⟩ : syracuseStep 2081031 = 3121547) B3121547
theorem B2341165 : Blo 2079435 2341165 := bbase (se 3 (by rfl) ⟨438968, by rfl⟩ : syracuseStep 2341165 = 877937) (by norm_num)
theorem B3121553 : Blo 2079435 3121553 := bstep (se 2 (by rfl) ⟨1170582, by rfl⟩ : syracuseStep 3121553 = 2341165) B2341165
theorem B2081035 : Blo 2079435 2081035 := bstep (se 1 (by rfl) ⟨1560776, by rfl⟩ : syracuseStep 2081035 = 3121553) B3121553
theorem B7023509 : Blo 2079435 7023509 := bbase (se 6 (by rfl) ⟨164613, by rfl⟩ : syracuseStep 7023509 = 329227) (by norm_num)
theorem B4682339 : Blo 2079435 4682339 := bstep (se 1 (by rfl) ⟨3511754, by rfl⟩ : syracuseStep 4682339 = 7023509) B7023509
theorem B3121559 : Blo 2079435 3121559 := bstep (se 1 (by rfl) ⟨2341169, by rfl⟩ : syracuseStep 3121559 = 4682339) B4682339
theorem B2081039 : Blo 2079435 2081039 := bstep (se 1 (by rfl) ⟨1560779, by rfl⟩ : syracuseStep 2081039 = 3121559) B3121559
theorem B3121565 : Blo 2079435 3121565 := bbase (se 3 (by rfl) ⟨585293, by rfl⟩ : syracuseStep 3121565 = 1170587) (by norm_num)
theorem B2081043 : Blo 2079435 2081043 := bstep (se 1 (by rfl) ⟨1560782, by rfl⟩ : syracuseStep 2081043 = 3121565) B3121565
theorem B4682357 : Blo 2079435 4682357 := bbase (se 5 (by rfl) ⟨219485, by rfl⟩ : syracuseStep 4682357 = 438971) (by norm_num)
theorem B3121571 : Blo 2079435 3121571 := bstep (se 1 (by rfl) ⟨2341178, by rfl⟩ : syracuseStep 3121571 = 4682357) B4682357
theorem B2081047 : Blo 2079435 2081047 := bstep (se 1 (by rfl) ⟨1560785, by rfl⟩ : syracuseStep 2081047 = 3121571) B3121571
theorem B2109445 : Blo 2079435 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B11250373 : Blo 2079435 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B15000497 : Blo 2079435 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B10000331 : Blo 2079435 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B6666887 : Blo 2079435 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B17778365 : Blo 2079435 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B11852243 : Blo 2079435 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B7901495 : Blo 2079435 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B5267663 : Blo 2079435 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B3511775 : Blo 2079435 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B2341183 : Blo 2079435 2341183 := bstep (se 1 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 2341183 = 3511775) B3511775
theorem B3121577 : Blo 2079435 3121577 := bstep (se 2 (by rfl) ⟨1170591, by rfl⟩ : syracuseStep 3121577 = 2341183) B2341183
theorem B2081051 : Blo 2079435 2081051 := bstep (se 1 (by rfl) ⟨1560788, by rfl⟩ : syracuseStep 2081051 = 3121577) B3121577
theorem B7901509 : Blo 2079435 7901509 := bbase (se 4 (by rfl) ⟨740766, by rfl⟩ : syracuseStep 7901509 = 1481533) (by norm_num)
theorem B10535345 : Blo 2079435 10535345 := bstep (se 2 (by rfl) ⟨3950754, by rfl⟩ : syracuseStep 10535345 = 7901509) B7901509
theorem B7023563 : Blo 2079435 7023563 := bstep (se 1 (by rfl) ⟨5267672, by rfl⟩ : syracuseStep 7023563 = 10535345) B10535345
theorem B4682375 : Blo 2079435 4682375 := bstep (se 1 (by rfl) ⟨3511781, by rfl⟩ : syracuseStep 4682375 = 7023563) B7023563
theorem B3121583 : Blo 2079435 3121583 := bstep (se 1 (by rfl) ⟨2341187, by rfl⟩ : syracuseStep 3121583 = 4682375) B4682375
theorem B2081055 : Blo 2079435 2081055 := bstep (se 1 (by rfl) ⟨1560791, by rfl⟩ : syracuseStep 2081055 = 3121583) B3121583
theorem B3121589 : Blo 2079435 3121589 := bbase (se 5 (by rfl) ⟨146324, by rfl⟩ : syracuseStep 3121589 = 292649) (by norm_num)
theorem B2081059 : Blo 2079435 2081059 := bstep (se 1 (by rfl) ⟨1560794, by rfl⟩ : syracuseStep 2081059 = 3121589) B3121589
theorem B5267693 : Blo 2079435 5267693 := bbase (se 3 (by rfl) ⟨987692, by rfl⟩ : syracuseStep 5267693 = 1975385) (by norm_num)
theorem B3511795 : Blo 2079435 3511795 := bstep (se 1 (by rfl) ⟨2633846, by rfl⟩ : syracuseStep 3511795 = 5267693) B5267693
theorem B4682393 : Blo 2079435 4682393 := bstep (se 2 (by rfl) ⟨1755897, by rfl⟩ : syracuseStep 4682393 = 3511795) B3511795
theorem B3121595 : Blo 2079435 3121595 := bstep (se 1 (by rfl) ⟨2341196, by rfl⟩ : syracuseStep 3121595 = 4682393) B4682393
theorem B2081063 : Blo 2079435 2081063 := bstep (se 1 (by rfl) ⟨1560797, by rfl⟩ : syracuseStep 2081063 = 3121595) B3121595
theorem B2341201 : Blo 2079435 2341201 := bbase (se 2 (by rfl) ⟨877950, by rfl⟩ : syracuseStep 2341201 = 1755901) (by norm_num)
theorem B3121601 : Blo 2079435 3121601 := bstep (se 2 (by rfl) ⟨1170600, by rfl⟩ : syracuseStep 3121601 = 2341201) B2341201
theorem B2081067 : Blo 2079435 2081067 := bstep (se 1 (by rfl) ⟨1560800, by rfl⟩ : syracuseStep 2081067 = 3121601) B3121601
theorem B2222317 : Blo 2079435 2222317 := bbase (se 3 (by rfl) ⟨416684, by rfl⟩ : syracuseStep 2222317 = 833369) (by norm_num)
theorem B2963089 : Blo 2079435 2963089 := bstep (se 2 (by rfl) ⟨1111158, by rfl⟩ : syracuseStep 2963089 = 2222317) B2222317
theorem B3950785 : Blo 2079435 3950785 := bstep (se 2 (by rfl) ⟨1481544, by rfl⟩ : syracuseStep 3950785 = 2963089) B2963089
theorem B5267713 : Blo 2079435 5267713 := bstep (se 2 (by rfl) ⟨1975392, by rfl⟩ : syracuseStep 5267713 = 3950785) B3950785
theorem B7023617 : Blo 2079435 7023617 := bstep (se 2 (by rfl) ⟨2633856, by rfl⟩ : syracuseStep 7023617 = 5267713) B5267713
theorem B4682411 : Blo 2079435 4682411 := bstep (se 1 (by rfl) ⟨3511808, by rfl⟩ : syracuseStep 4682411 = 7023617) B7023617
theorem B3121607 : Blo 2079435 3121607 := bstep (se 1 (by rfl) ⟨2341205, by rfl⟩ : syracuseStep 3121607 = 4682411) B4682411
theorem B2081071 : Blo 2079435 2081071 := bstep (se 1 (by rfl) ⟨1560803, by rfl⟩ : syracuseStep 2081071 = 3121607) B3121607
theorem B3121613 : Blo 2079435 3121613 := bbase (se 3 (by rfl) ⟨585302, by rfl⟩ : syracuseStep 3121613 = 1170605) (by norm_num)
theorem B2081075 : Blo 2079435 2081075 := bstep (se 1 (by rfl) ⟨1560806, by rfl⟩ : syracuseStep 2081075 = 3121613) B3121613
theorem B4682429 : Blo 2079435 4682429 := bbase (se 3 (by rfl) ⟨877955, by rfl⟩ : syracuseStep 4682429 = 1755911) (by norm_num)
theorem B3121619 : Blo 2079435 3121619 := bstep (se 1 (by rfl) ⟨2341214, by rfl⟩ : syracuseStep 3121619 = 4682429) B4682429
theorem B2081079 : Blo 2079435 2081079 := bstep (se 1 (by rfl) ⟨1560809, by rfl⟩ : syracuseStep 2081079 = 3121619) B3121619
theorem B3511829 : Blo 2079435 3511829 := bbase (se 6 (by rfl) ⟨82308, by rfl⟩ : syracuseStep 3511829 = 164617) (by norm_num)
theorem B2341219 : Blo 2079435 2341219 := bstep (se 1 (by rfl) ⟨1755914, by rfl⟩ : syracuseStep 2341219 = 3511829) B3511829
theorem B3121625 : Blo 2079435 3121625 := bstep (se 2 (by rfl) ⟨1170609, by rfl⟩ : syracuseStep 3121625 = 2341219) B2341219
theorem B2081083 : Blo 2079435 2081083 := bstep (se 1 (by rfl) ⟨1560812, by rfl⟩ : syracuseStep 2081083 = 3121625) B3121625
theorem B8437925 : Blo 2079435 8437925 := bbase (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) (by norm_num)
theorem B5625283 : Blo 2079435 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B7500377 : Blo 2079435 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B20001005 : Blo 2079435 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B13334003 : Blo 2079435 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B8889335 : Blo 2079435 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B5926223 : Blo 2079435 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B15803261 : Blo 2079435 15803261 := bstep (se 3 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 15803261 = 5926223) B5926223
theorem B10535507 : Blo 2079435 10535507 := bstep (se 1 (by rfl) ⟨7901630, by rfl⟩ : syracuseStep 10535507 = 15803261) B15803261
theorem B7023671 : Blo 2079435 7023671 := bstep (se 1 (by rfl) ⟨5267753, by rfl⟩ : syracuseStep 7023671 = 10535507) B10535507
theorem B4682447 : Blo 2079435 4682447 := bstep (se 1 (by rfl) ⟨3511835, by rfl⟩ : syracuseStep 4682447 = 7023671) B7023671
theorem B3121631 : Blo 2079435 3121631 := bstep (se 1 (by rfl) ⟨2341223, by rfl⟩ : syracuseStep 3121631 = 4682447) B4682447
theorem B2081087 : Blo 2079435 2081087 := bstep (se 1 (by rfl) ⟨1560815, by rfl⟩ : syracuseStep 2081087 = 3121631) B3121631
theorem B3121637 : Blo 2079435 3121637 := bbase (se 4 (by rfl) ⟨292653, by rfl⟩ : syracuseStep 3121637 = 585307) (by norm_num)
theorem B2081091 : Blo 2079435 2081091 := bstep (se 1 (by rfl) ⟨1560818, by rfl⟩ : syracuseStep 2081091 = 3121637) B3121637
theorem B12829621 : Blo 2079435 12829621 := bbase (se 5 (by rfl) ⟨601388, by rfl⟩ : syracuseStep 12829621 = 1202777) (by norm_num)
theorem B17106161 : Blo 2079435 17106161 := bstep (se 2 (by rfl) ⟨6414810, by rfl⟩ : syracuseStep 17106161 = 12829621) B12829621
theorem B45616429 : Blo 2079435 45616429 := bstep (se 3 (by rfl) ⟨8553080, by rfl⟩ : syracuseStep 45616429 = 17106161) B17106161
theorem B243287621 : Blo 2079435 243287621 := bstep (se 4 (by rfl) ⟨22808214, by rfl⟩ : syracuseStep 243287621 = 45616429) B45616429
theorem B162191747 : Blo 2079435 162191747 := bstep (se 1 (by rfl) ⟨121643810, by rfl⟩ : syracuseStep 162191747 = 243287621) B243287621
theorem B432511325 : Blo 2079435 432511325 := bstep (se 3 (by rfl) ⟨81095873, by rfl⟩ : syracuseStep 432511325 = 162191747) B162191747
theorem B288340883 : Blo 2079435 288340883 := bstep (se 1 (by rfl) ⟨216255662, by rfl⟩ : syracuseStep 288340883 = 432511325) B432511325
theorem B192227255 : Blo 2079435 192227255 := bstep (se 1 (by rfl) ⟨144170441, by rfl⟩ : syracuseStep 192227255 = 288340883) B288340883
theorem B128151503 : Blo 2079435 128151503 := bstep (se 1 (by rfl) ⟨96113627, by rfl⟩ : syracuseStep 128151503 = 192227255) B192227255
theorem B85434335 : Blo 2079435 85434335 := bstep (se 1 (by rfl) ⟨64075751, by rfl⟩ : syracuseStep 85434335 = 128151503) B128151503
theorem B56956223 : Blo 2079435 56956223 := bstep (se 1 (by rfl) ⟨42717167, by rfl⟩ : syracuseStep 56956223 = 85434335) B85434335
theorem B37970815 : Blo 2079435 37970815 := bstep (se 1 (by rfl) ⟨28478111, by rfl⟩ : syracuseStep 37970815 = 56956223) B56956223
theorem B50627753 : Blo 2079435 50627753 := bstep (se 2 (by rfl) ⟨18985407, by rfl⟩ : syracuseStep 50627753 = 37970815) B37970815
theorem B33751835 : Blo 2079435 33751835 := bstep (se 1 (by rfl) ⟨25313876, by rfl⟩ : syracuseStep 33751835 = 50627753) B50627753
theorem B22501223 : Blo 2079435 22501223 := bstep (se 1 (by rfl) ⟨16875917, by rfl⟩ : syracuseStep 22501223 = 33751835) B33751835
theorem B15000815 : Blo 2079435 15000815 := bstep (se 1 (by rfl) ⟨11250611, by rfl⟩ : syracuseStep 15000815 = 22501223) B22501223
theorem B10000543 : Blo 2079435 10000543 := bstep (se 1 (by rfl) ⟨7500407, by rfl⟩ : syracuseStep 10000543 = 15000815) B15000815
theorem B13334057 : Blo 2079435 13334057 := bstep (se 2 (by rfl) ⟨5000271, by rfl⟩ : syracuseStep 13334057 = 10000543) B10000543
theorem B8889371 : Blo 2079435 8889371 := bstep (se 1 (by rfl) ⟨6667028, by rfl⟩ : syracuseStep 8889371 = 13334057) B13334057
theorem B5926247 : Blo 2079435 5926247 := bstep (se 1 (by rfl) ⟨4444685, by rfl⟩ : syracuseStep 5926247 = 8889371) B8889371
theorem B3950831 : Blo 2079435 3950831 := bstep (se 1 (by rfl) ⟨2963123, by rfl⟩ : syracuseStep 3950831 = 5926247) B5926247
theorem B2633887 : Blo 2079435 2633887 := bstep (se 1 (by rfl) ⟨1975415, by rfl⟩ : syracuseStep 2633887 = 3950831) B3950831
theorem B3511849 : Blo 2079435 3511849 := bstep (se 2 (by rfl) ⟨1316943, by rfl⟩ : syracuseStep 3511849 = 2633887) B2633887
theorem B4682465 : Blo 2079435 4682465 := bstep (se 2 (by rfl) ⟨1755924, by rfl⟩ : syracuseStep 4682465 = 3511849) B3511849
theorem B3121643 : Blo 2079435 3121643 := bstep (se 1 (by rfl) ⟨2341232, by rfl⟩ : syracuseStep 3121643 = 4682465) B4682465
theorem B2081095 : Blo 2079435 2081095 := bstep (se 1 (by rfl) ⟨1560821, by rfl⟩ : syracuseStep 2081095 = 3121643) B3121643
theorem B2341237 : Blo 2079435 2341237 := bbase (se 5 (by rfl) ⟨109745, by rfl⟩ : syracuseStep 2341237 = 219491) (by norm_num)
theorem B3121649 : Blo 2079435 3121649 := bstep (se 2 (by rfl) ⟨1170618, by rfl⟩ : syracuseStep 3121649 = 2341237) B2341237
theorem B2081099 : Blo 2079435 2081099 := bstep (se 1 (by rfl) ⟨1560824, by rfl⟩ : syracuseStep 2081099 = 3121649) B3121649
theorem B2633897 : Blo 2079435 2633897 := bbase (se 2 (by rfl) ⟨987711, by rfl⟩ : syracuseStep 2633897 = 1975423) (by norm_num)
theorem B7023725 : Blo 2079435 7023725 := bstep (se 3 (by rfl) ⟨1316948, by rfl⟩ : syracuseStep 7023725 = 2633897) B2633897
theorem B4682483 : Blo 2079435 4682483 := bstep (se 1 (by rfl) ⟨3511862, by rfl⟩ : syracuseStep 4682483 = 7023725) B7023725
theorem B3121655 : Blo 2079435 3121655 := bstep (se 1 (by rfl) ⟨2341241, by rfl⟩ : syracuseStep 3121655 = 4682483) B4682483
theorem B2081103 : Blo 2079435 2081103 := bstep (se 1 (by rfl) ⟨1560827, by rfl⟩ : syracuseStep 2081103 = 3121655) B3121655
theorem B3121661 : Blo 2079435 3121661 := bbase (se 3 (by rfl) ⟨585311, by rfl⟩ : syracuseStep 3121661 = 1170623) (by norm_num)
theorem B2081107 : Blo 2079435 2081107 := bstep (se 1 (by rfl) ⟨1560830, by rfl⟩ : syracuseStep 2081107 = 3121661) B3121661
theorem B4682501 : Blo 2079435 4682501 := bbase (se 4 (by rfl) ⟨438984, by rfl⟩ : syracuseStep 4682501 = 877969) (by norm_num)
theorem B3121667 : Blo 2079435 3121667 := bstep (se 1 (by rfl) ⟨2341250, by rfl⟩ : syracuseStep 3121667 = 4682501) B4682501
theorem B2081111 : Blo 2079435 2081111 := bstep (se 1 (by rfl) ⟨1560833, by rfl⟩ : syracuseStep 2081111 = 3121667) B3121667
theorem B3950869 : Blo 2079435 3950869 := bbase (se 6 (by rfl) ⟨92598, by rfl⟩ : syracuseStep 3950869 = 185197) (by norm_num)
theorem B5267825 : Blo 2079435 5267825 := bstep (se 2 (by rfl) ⟨1975434, by rfl⟩ : syracuseStep 5267825 = 3950869) B3950869
theorem B3511883 : Blo 2079435 3511883 := bstep (se 1 (by rfl) ⟨2633912, by rfl⟩ : syracuseStep 3511883 = 5267825) B5267825
theorem B2341255 : Blo 2079435 2341255 := bstep (se 1 (by rfl) ⟨1755941, by rfl⟩ : syracuseStep 2341255 = 3511883) B3511883
theorem B3121673 : Blo 2079435 3121673 := bstep (se 2 (by rfl) ⟨1170627, by rfl⟩ : syracuseStep 3121673 = 2341255) B2341255
theorem B2081115 : Blo 2079435 2081115 := bstep (se 1 (by rfl) ⟨1560836, by rfl⟩ : syracuseStep 2081115 = 3121673) B3121673
theorem B10535669 : Blo 2079435 10535669 := bbase (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) (by norm_num)
theorem B7023779 : Blo 2079435 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B4682519 : Blo 2079435 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B3121679 : Blo 2079435 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B2081119 : Blo 2079435 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B3121685 : Blo 2079435 3121685 := bbase (se 6 (by rfl) ⟨73164, by rfl⟩ : syracuseStep 3121685 = 146329) (by norm_num)
theorem B2081123 : Blo 2079435 2081123 := bstep (se 1 (by rfl) ⟨1560842, by rfl⟩ : syracuseStep 2081123 = 3121685) B3121685
theorem B3333565 : Blo 2079435 3333565 := bbase (se 3 (by rfl) ⟨625043, by rfl⟩ : syracuseStep 3333565 = 1250087) (by norm_num)
theorem B17779013 : Blo 2079435 17779013 := bstep (se 4 (by rfl) ⟨1666782, by rfl⟩ : syracuseStep 17779013 = 3333565) B3333565
theorem B11852675 : Blo 2079435 11852675 := bstep (se 1 (by rfl) ⟨8889506, by rfl⟩ : syracuseStep 11852675 = 17779013) B17779013
theorem B7901783 : Blo 2079435 7901783 := bstep (se 1 (by rfl) ⟨5926337, by rfl⟩ : syracuseStep 7901783 = 11852675) B11852675
theorem B5267855 : Blo 2079435 5267855 := bstep (se 1 (by rfl) ⟨3950891, by rfl⟩ : syracuseStep 5267855 = 7901783) B7901783
theorem B3511903 : Blo 2079435 3511903 := bstep (se 1 (by rfl) ⟨2633927, by rfl⟩ : syracuseStep 3511903 = 5267855) B5267855
theorem B4682537 : Blo 2079435 4682537 := bstep (se 2 (by rfl) ⟨1755951, by rfl⟩ : syracuseStep 4682537 = 3511903) B3511903
theorem B3121691 : Blo 2079435 3121691 := bstep (se 1 (by rfl) ⟨2341268, by rfl⟩ : syracuseStep 3121691 = 4682537) B4682537
theorem B2081127 : Blo 2079435 2081127 := bstep (se 1 (by rfl) ⟨1560845, by rfl⟩ : syracuseStep 2081127 = 3121691) B3121691
theorem B2341273 : Blo 2079435 2341273 := bbase (se 2 (by rfl) ⟨877977, by rfl⟩ : syracuseStep 2341273 = 1755955) (by norm_num)
theorem B3121697 : Blo 2079435 3121697 := bstep (se 2 (by rfl) ⟨1170636, by rfl⟩ : syracuseStep 3121697 = 2341273) B2341273
theorem B2081131 : Blo 2079435 2081131 := bstep (se 1 (by rfl) ⟨1560848, by rfl⟩ : syracuseStep 2081131 = 3121697) B3121697
theorem B7901813 : Blo 2079435 7901813 := bbase (se 5 (by rfl) ⟨370397, by rfl⟩ : syracuseStep 7901813 = 740795) (by norm_num)
theorem B5267875 : Blo 2079435 5267875 := bstep (se 1 (by rfl) ⟨3950906, by rfl⟩ : syracuseStep 5267875 = 7901813) B7901813
theorem B7023833 : Blo 2079435 7023833 := bstep (se 2 (by rfl) ⟨2633937, by rfl⟩ : syracuseStep 7023833 = 5267875) B5267875
theorem B4682555 : Blo 2079435 4682555 := bstep (se 1 (by rfl) ⟨3511916, by rfl⟩ : syracuseStep 4682555 = 7023833) B7023833
theorem B3121703 : Blo 2079435 3121703 := bstep (se 1 (by rfl) ⟨2341277, by rfl⟩ : syracuseStep 3121703 = 4682555) B4682555
theorem B2081135 : Blo 2079435 2081135 := bstep (se 1 (by rfl) ⟨1560851, by rfl⟩ : syracuseStep 2081135 = 3121703) B3121703
theorem B3121709 : Blo 2079435 3121709 := bbase (se 3 (by rfl) ⟨585320, by rfl⟩ : syracuseStep 3121709 = 1170641) (by norm_num)
theorem B2081139 : Blo 2079435 2081139 := bstep (se 1 (by rfl) ⟨1560854, by rfl⟩ : syracuseStep 2081139 = 3121709) B3121709
theorem B4682573 : Blo 2079435 4682573 := bbase (se 3 (by rfl) ⟨877982, by rfl⟩ : syracuseStep 4682573 = 1755965) (by norm_num)
theorem B3121715 : Blo 2079435 3121715 := bstep (se 1 (by rfl) ⟨2341286, by rfl⟩ : syracuseStep 3121715 = 4682573) B4682573
theorem B2081143 : Blo 2079435 2081143 := bstep (se 1 (by rfl) ⟨1560857, by rfl⟩ : syracuseStep 2081143 = 3121715) B3121715
theorem B2633953 : Blo 2079435 2633953 := bbase (se 2 (by rfl) ⟨987732, by rfl⟩ : syracuseStep 2633953 = 1975465) (by norm_num)
theorem B3511937 : Blo 2079435 3511937 := bstep (se 2 (by rfl) ⟨1316976, by rfl⟩ : syracuseStep 3511937 = 2633953) B2633953
theorem B2341291 : Blo 2079435 2341291 := bstep (se 1 (by rfl) ⟨1755968, by rfl⟩ : syracuseStep 2341291 = 3511937) B3511937
theorem B3121721 : Blo 2079435 3121721 := bstep (se 2 (by rfl) ⟨1170645, by rfl⟩ : syracuseStep 3121721 = 2341291) B2341291
theorem B2081147 : Blo 2079435 2081147 := bstep (se 1 (by rfl) ⟨1560860, by rfl⟩ : syracuseStep 2081147 = 3121721) B3121721
theorem B23705621 : Blo 2079435 23705621 := bbase (se 6 (by rfl) ⟨555600, by rfl⟩ : syracuseStep 23705621 = 1111201) (by norm_num)
theorem B15803747 : Blo 2079435 15803747 := bstep (se 1 (by rfl) ⟨11852810, by rfl⟩ : syracuseStep 15803747 = 23705621) B23705621
theorem B10535831 : Blo 2079435 10535831 := bstep (se 1 (by rfl) ⟨7901873, by rfl⟩ : syracuseStep 10535831 = 15803747) B15803747
theorem B7023887 : Blo 2079435 7023887 := bstep (se 1 (by rfl) ⟨5267915, by rfl⟩ : syracuseStep 7023887 = 10535831) B10535831
theorem B4682591 : Blo 2079435 4682591 := bstep (se 1 (by rfl) ⟨3511943, by rfl⟩ : syracuseStep 4682591 = 7023887) B7023887
theorem B3121727 : Blo 2079435 3121727 := bstep (se 1 (by rfl) ⟨2341295, by rfl⟩ : syracuseStep 3121727 = 4682591) B4682591
theorem B2081151 : Blo 2079435 2081151 := bstep (se 1 (by rfl) ⟨1560863, by rfl⟩ : syracuseStep 2081151 = 3121727) B3121727
theorem B3121733 : Blo 2079435 3121733 := bbase (se 4 (by rfl) ⟨292662, by rfl⟩ : syracuseStep 3121733 = 585325) (by norm_num)
theorem B2081155 : Blo 2079435 2081155 := bstep (se 1 (by rfl) ⟨1560866, by rfl⟩ : syracuseStep 2081155 = 3121733) B3121733
theorem B3511957 : Blo 2079435 3511957 := bbase (se 6 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 3511957 = 164623) (by norm_num)
theorem B4682609 : Blo 2079435 4682609 := bstep (se 2 (by rfl) ⟨1755978, by rfl⟩ : syracuseStep 4682609 = 3511957) B3511957
theorem B3121739 : Blo 2079435 3121739 := bstep (se 1 (by rfl) ⟨2341304, by rfl⟩ : syracuseStep 3121739 = 4682609) B4682609
theorem B2081159 : Blo 2079435 2081159 := bstep (se 1 (by rfl) ⟨1560869, by rfl⟩ : syracuseStep 2081159 = 3121739) B3121739
theorem B2341309 : Blo 2079435 2341309 := bbase (se 3 (by rfl) ⟨438995, by rfl⟩ : syracuseStep 2341309 = 877991) (by norm_num)
theorem B3121745 : Blo 2079435 3121745 := bstep (se 2 (by rfl) ⟨1170654, by rfl⟩ : syracuseStep 3121745 = 2341309) B2341309
theorem B2081163 : Blo 2079435 2081163 := bstep (se 1 (by rfl) ⟨1560872, by rfl⟩ : syracuseStep 2081163 = 3121745) B3121745
theorem B7023941 : Blo 2079435 7023941 := bbase (se 4 (by rfl) ⟨658494, by rfl⟩ : syracuseStep 7023941 = 1316989) (by norm_num)
theorem B4682627 : Blo 2079435 4682627 := bstep (se 1 (by rfl) ⟨3511970, by rfl⟩ : syracuseStep 4682627 = 7023941) B7023941
theorem B3121751 : Blo 2079435 3121751 := bstep (se 1 (by rfl) ⟨2341313, by rfl⟩ : syracuseStep 3121751 = 4682627) B4682627
theorem B2081167 : Blo 2079435 2081167 := bstep (se 1 (by rfl) ⟨1560875, by rfl⟩ : syracuseStep 2081167 = 3121751) B3121751
theorem B3121757 : Blo 2079435 3121757 := bbase (se 3 (by rfl) ⟨585329, by rfl⟩ : syracuseStep 3121757 = 1170659) (by norm_num)
theorem B2081171 : Blo 2079435 2081171 := bstep (se 1 (by rfl) ⟨1560878, by rfl⟩ : syracuseStep 2081171 = 3121757) B3121757
theorem B4682645 : Blo 2079435 4682645 := bbase (se 6 (by rfl) ⟨109749, by rfl⟩ : syracuseStep 4682645 = 219499) (by norm_num)
theorem B3121763 : Blo 2079435 3121763 := bstep (se 1 (by rfl) ⟨2341322, by rfl⟩ : syracuseStep 3121763 = 4682645) B4682645
theorem B2081175 : Blo 2079435 2081175 := bstep (se 1 (by rfl) ⟨1560881, by rfl⟩ : syracuseStep 2081175 = 3121763) B3121763
theorem B2500237 : Blo 2079435 2500237 := bbase (se 3 (by rfl) ⟨468794, by rfl⟩ : syracuseStep 2500237 = 937589) (by norm_num)
theorem B3333649 : Blo 2079435 3333649 := bstep (se 2 (by rfl) ⟨1250118, by rfl⟩ : syracuseStep 3333649 = 2500237) B2500237
theorem B4444865 : Blo 2079435 4444865 := bstep (se 2 (by rfl) ⟨1666824, by rfl⟩ : syracuseStep 4444865 = 3333649) B3333649
theorem B2963243 : Blo 2079435 2963243 := bstep (se 1 (by rfl) ⟨2222432, by rfl⟩ : syracuseStep 2963243 = 4444865) B4444865
theorem B7901981 : Blo 2079435 7901981 := bstep (se 3 (by rfl) ⟨1481621, by rfl⟩ : syracuseStep 7901981 = 2963243) B2963243
theorem B5267987 : Blo 2079435 5267987 := bstep (se 1 (by rfl) ⟨3950990, by rfl⟩ : syracuseStep 5267987 = 7901981) B7901981
theorem B3511991 : Blo 2079435 3511991 := bstep (se 1 (by rfl) ⟨2633993, by rfl⟩ : syracuseStep 3511991 = 5267987) B5267987
theorem B2341327 : Blo 2079435 2341327 := bstep (se 1 (by rfl) ⟨1755995, by rfl⟩ : syracuseStep 2341327 = 3511991) B3511991
theorem B3121769 : Blo 2079435 3121769 := bstep (se 2 (by rfl) ⟨1170663, by rfl⟩ : syracuseStep 3121769 = 2341327) B2341327
theorem B2081179 : Blo 2079435 2081179 := bstep (se 1 (by rfl) ⟨1560884, by rfl⟩ : syracuseStep 2081179 = 3121769) B3121769
theorem B2500241 : Blo 2079435 2500241 := bbase (se 2 (by rfl) ⟨937590, by rfl⟩ : syracuseStep 2500241 = 1875181) (by norm_num)
theorem B6667309 : Blo 2079435 6667309 := bstep (se 3 (by rfl) ⟨1250120, by rfl⟩ : syracuseStep 6667309 = 2500241) B2500241
theorem B8889745 : Blo 2079435 8889745 := bstep (se 2 (by rfl) ⟨3333654, by rfl⟩ : syracuseStep 8889745 = 6667309) B6667309
theorem B11852993 : Blo 2079435 11852993 := bstep (se 2 (by rfl) ⟨4444872, by rfl⟩ : syracuseStep 11852993 = 8889745) B8889745
theorem B7901995 : Blo 2079435 7901995 := bstep (se 1 (by rfl) ⟨5926496, by rfl⟩ : syracuseStep 7901995 = 11852993) B11852993
theorem B10535993 : Blo 2079435 10535993 := bstep (se 2 (by rfl) ⟨3950997, by rfl⟩ : syracuseStep 10535993 = 7901995) B7901995
theorem B7023995 : Blo 2079435 7023995 := bstep (se 1 (by rfl) ⟨5267996, by rfl⟩ : syracuseStep 7023995 = 10535993) B10535993
theorem B4682663 : Blo 2079435 4682663 := bstep (se 1 (by rfl) ⟨3511997, by rfl⟩ : syracuseStep 4682663 = 7023995) B7023995
theorem B3121775 : Blo 2079435 3121775 := bstep (se 1 (by rfl) ⟨2341331, by rfl⟩ : syracuseStep 3121775 = 4682663) B4682663
theorem B2081183 : Blo 2079435 2081183 := bstep (se 1 (by rfl) ⟨1560887, by rfl⟩ : syracuseStep 2081183 = 3121775) B3121775
theorem B3121781 : Blo 2079435 3121781 := bbase (se 5 (by rfl) ⟨146333, by rfl⟩ : syracuseStep 3121781 = 292667) (by norm_num)
theorem B2081187 : Blo 2079435 2081187 := bstep (se 1 (by rfl) ⟨1560890, by rfl⟩ : syracuseStep 2081187 = 3121781) B3121781
theorem B3951013 : Blo 2079435 3951013 := bbase (se 4 (by rfl) ⟨370407, by rfl⟩ : syracuseStep 3951013 = 740815) (by norm_num)
theorem B5268017 : Blo 2079435 5268017 := bstep (se 2 (by rfl) ⟨1975506, by rfl⟩ : syracuseStep 5268017 = 3951013) B3951013
theorem B3512011 : Blo 2079435 3512011 := bstep (se 1 (by rfl) ⟨2634008, by rfl⟩ : syracuseStep 3512011 = 5268017) B5268017
theorem B4682681 : Blo 2079435 4682681 := bstep (se 2 (by rfl) ⟨1756005, by rfl⟩ : syracuseStep 4682681 = 3512011) B3512011
theorem B3121787 : Blo 2079435 3121787 := bstep (se 1 (by rfl) ⟨2341340, by rfl⟩ : syracuseStep 3121787 = 4682681) B4682681
theorem B2081191 : Blo 2079435 2081191 := bstep (se 1 (by rfl) ⟨1560893, by rfl⟩ : syracuseStep 2081191 = 3121787) B3121787
theorem B2341345 : Blo 2079435 2341345 := bbase (se 2 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 2341345 = 1756009) (by norm_num)
theorem B3121793 : Blo 2079435 3121793 := bstep (se 2 (by rfl) ⟨1170672, by rfl⟩ : syracuseStep 3121793 = 2341345) B2341345
theorem B2081195 : Blo 2079435 2081195 := bstep (se 1 (by rfl) ⟨1560896, by rfl⟩ : syracuseStep 2081195 = 3121793) B3121793
theorem B5268037 : Blo 2079435 5268037 := bbase (se 4 (by rfl) ⟨493878, by rfl⟩ : syracuseStep 5268037 = 987757) (by norm_num)
theorem B7024049 : Blo 2079435 7024049 := bstep (se 2 (by rfl) ⟨2634018, by rfl⟩ : syracuseStep 7024049 = 5268037) B5268037
theorem B4682699 : Blo 2079435 4682699 := bstep (se 1 (by rfl) ⟨3512024, by rfl⟩ : syracuseStep 4682699 = 7024049) B7024049
theorem B3121799 : Blo 2079435 3121799 := bstep (se 1 (by rfl) ⟨2341349, by rfl⟩ : syracuseStep 3121799 = 4682699) B4682699
theorem B2081199 : Blo 2079435 2081199 := bstep (se 1 (by rfl) ⟨1560899, by rfl⟩ : syracuseStep 2081199 = 3121799) B3121799
theorem B3121805 : Blo 2079435 3121805 := bbase (se 3 (by rfl) ⟨585338, by rfl⟩ : syracuseStep 3121805 = 1170677) (by norm_num)
theorem B2081203 : Blo 2079435 2081203 := bstep (se 1 (by rfl) ⟨1560902, by rfl⟩ : syracuseStep 2081203 = 3121805) B3121805
theorem B4682717 : Blo 2079435 4682717 := bbase (se 3 (by rfl) ⟨878009, by rfl⟩ : syracuseStep 4682717 = 1756019) (by norm_num)
theorem B3121811 : Blo 2079435 3121811 := bstep (se 1 (by rfl) ⟨2341358, by rfl⟩ : syracuseStep 3121811 = 4682717) B4682717
theorem B2081207 : Blo 2079435 2081207 := bstep (se 1 (by rfl) ⟨1560905, by rfl⟩ : syracuseStep 2081207 = 3121811) B3121811
theorem B3512045 : Blo 2079435 3512045 := bbase (se 3 (by rfl) ⟨658508, by rfl⟩ : syracuseStep 3512045 = 1317017) (by norm_num)
theorem B2341363 : Blo 2079435 2341363 := bstep (se 1 (by rfl) ⟨1756022, by rfl⟩ : syracuseStep 2341363 = 3512045) B3512045
theorem B3121817 : Blo 2079435 3121817 := bstep (se 2 (by rfl) ⟨1170681, by rfl⟩ : syracuseStep 3121817 = 2341363) B2341363
theorem B2081211 : Blo 2079435 2081211 := bstep (se 1 (by rfl) ⟨1560908, by rfl⟩ : syracuseStep 2081211 = 3121817) B3121817
theorem B2373313 : Blo 2079435 2373313 := bbase (se 2 (by rfl) ⟨889992, by rfl⟩ : syracuseStep 2373313 = 1779985) (by norm_num)
theorem B3164417 : Blo 2079435 3164417 := bstep (se 2 (by rfl) ⟨1186656, by rfl⟩ : syracuseStep 3164417 = 2373313) B2373313
theorem B2109611 : Blo 2079435 2109611 := bstep (se 1 (by rfl) ⟨1582208, by rfl⟩ : syracuseStep 2109611 = 3164417) B3164417
theorem B5625629 : Blo 2079435 5625629 := bstep (se 3 (by rfl) ⟨1054805, by rfl⟩ : syracuseStep 5625629 = 2109611) B2109611
theorem B3750419 : Blo 2079435 3750419 := bstep (se 1 (by rfl) ⟨2812814, by rfl⟩ : syracuseStep 3750419 = 5625629) B5625629
theorem B10001117 : Blo 2079435 10001117 := bstep (se 3 (by rfl) ⟨1875209, by rfl⟩ : syracuseStep 10001117 = 3750419) B3750419
theorem B26669645 : Blo 2079435 26669645 := bstep (se 3 (by rfl) ⟨5000558, by rfl⟩ : syracuseStep 26669645 = 10001117) B10001117
theorem B17779763 : Blo 2079435 17779763 := bstep (se 1 (by rfl) ⟨13334822, by rfl⟩ : syracuseStep 17779763 = 26669645) B26669645
theorem B11853175 : Blo 2079435 11853175 := bstep (se 1 (by rfl) ⟨8889881, by rfl⟩ : syracuseStep 11853175 = 17779763) B17779763
theorem B15804233 : Blo 2079435 15804233 := bstep (se 2 (by rfl) ⟨5926587, by rfl⟩ : syracuseStep 15804233 = 11853175) B11853175
theorem B10536155 : Blo 2079435 10536155 := bstep (se 1 (by rfl) ⟨7902116, by rfl⟩ : syracuseStep 10536155 = 15804233) B15804233
theorem B7024103 : Blo 2079435 7024103 := bstep (se 1 (by rfl) ⟨5268077, by rfl⟩ : syracuseStep 7024103 = 10536155) B10536155
theorem B4682735 : Blo 2079435 4682735 := bstep (se 1 (by rfl) ⟨3512051, by rfl⟩ : syracuseStep 4682735 = 7024103) B7024103
theorem B3121823 : Blo 2079435 3121823 := bstep (se 1 (by rfl) ⟨2341367, by rfl⟩ : syracuseStep 3121823 = 4682735) B4682735
theorem B2081215 : Blo 2079435 2081215 := bstep (se 1 (by rfl) ⟨1560911, by rfl⟩ : syracuseStep 2081215 = 3121823) B3121823
theorem B3121829 : Blo 2079435 3121829 := bbase (se 4 (by rfl) ⟨292671, by rfl⟩ : syracuseStep 3121829 = 585343) (by norm_num)
theorem B2081219 : Blo 2079435 2081219 := bstep (se 1 (by rfl) ⟨1560914, by rfl⟩ : syracuseStep 2081219 = 3121829) B3121829
theorem B2634049 : Blo 2079435 2634049 := bbase (se 2 (by rfl) ⟨987768, by rfl⟩ : syracuseStep 2634049 = 1975537) (by norm_num)
theorem B3512065 : Blo 2079435 3512065 := bstep (se 2 (by rfl) ⟨1317024, by rfl⟩ : syracuseStep 3512065 = 2634049) B2634049
theorem B4682753 : Blo 2079435 4682753 := bstep (se 2 (by rfl) ⟨1756032, by rfl⟩ : syracuseStep 4682753 = 3512065) B3512065
theorem B3121835 : Blo 2079435 3121835 := bstep (se 1 (by rfl) ⟨2341376, by rfl⟩ : syracuseStep 3121835 = 4682753) B4682753
theorem B2081223 : Blo 2079435 2081223 := bstep (se 1 (by rfl) ⟨1560917, by rfl⟩ : syracuseStep 2081223 = 3121835) B3121835
theorem B2341381 : Blo 2079435 2341381 := bbase (se 4 (by rfl) ⟨219504, by rfl⟩ : syracuseStep 2341381 = 439009) (by norm_num)
theorem B3121841 : Blo 2079435 3121841 := bstep (se 2 (by rfl) ⟨1170690, by rfl⟩ : syracuseStep 3121841 = 2341381) B2341381
theorem B2081227 : Blo 2079435 2081227 := bstep (se 1 (by rfl) ⟨1560920, by rfl⟩ : syracuseStep 2081227 = 3121841) B3121841
theorem B2963317 : Blo 2079435 2963317 := bbase (se 5 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 2963317 = 277811) (by norm_num)
theorem B3951089 : Blo 2079435 3951089 := bstep (se 2 (by rfl) ⟨1481658, by rfl⟩ : syracuseStep 3951089 = 2963317) B2963317
theorem B2634059 : Blo 2079435 2634059 := bstep (se 1 (by rfl) ⟨1975544, by rfl⟩ : syracuseStep 2634059 = 3951089) B3951089
theorem B7024157 : Blo 2079435 7024157 := bstep (se 3 (by rfl) ⟨1317029, by rfl⟩ : syracuseStep 7024157 = 2634059) B2634059
theorem B4682771 : Blo 2079435 4682771 := bstep (se 1 (by rfl) ⟨3512078, by rfl⟩ : syracuseStep 4682771 = 7024157) B7024157
theorem B3121847 : Blo 2079435 3121847 := bstep (se 1 (by rfl) ⟨2341385, by rfl⟩ : syracuseStep 3121847 = 4682771) B4682771
theorem B2081231 : Blo 2079435 2081231 := bstep (se 1 (by rfl) ⟨1560923, by rfl⟩ : syracuseStep 2081231 = 3121847) B3121847
theorem B3121853 : Blo 2079435 3121853 := bbase (se 3 (by rfl) ⟨585347, by rfl⟩ : syracuseStep 3121853 = 1170695) (by norm_num)
theorem B2081235 : Blo 2079435 2081235 := bstep (se 1 (by rfl) ⟨1560926, by rfl⟩ : syracuseStep 2081235 = 3121853) B3121853
theorem B4682789 : Blo 2079435 4682789 := bbase (se 4 (by rfl) ⟨439011, by rfl⟩ : syracuseStep 4682789 = 878023) (by norm_num)
theorem B3121859 : Blo 2079435 3121859 := bstep (se 1 (by rfl) ⟨2341394, by rfl⟩ : syracuseStep 3121859 = 4682789) B4682789
theorem B2081239 : Blo 2079435 2081239 := bstep (se 1 (by rfl) ⟨1560929, by rfl⟩ : syracuseStep 2081239 = 3121859) B3121859
theorem B5268149 : Blo 2079435 5268149 := bbase (se 5 (by rfl) ⟨246944, by rfl⟩ : syracuseStep 5268149 = 493889) (by norm_num)
theorem B3512099 : Blo 2079435 3512099 := bstep (se 1 (by rfl) ⟨2634074, by rfl⟩ : syracuseStep 3512099 = 5268149) B5268149
theorem B2341399 : Blo 2079435 2341399 := bstep (se 1 (by rfl) ⟨1756049, by rfl⟩ : syracuseStep 2341399 = 3512099) B3512099
theorem B3121865 : Blo 2079435 3121865 := bstep (se 2 (by rfl) ⟨1170699, by rfl⟩ : syracuseStep 3121865 = 2341399) B2341399
theorem B2081243 : Blo 2079435 2081243 := bstep (se 1 (by rfl) ⟨1560932, by rfl⟩ : syracuseStep 2081243 = 3121865) B3121865
theorem B13335029 : Blo 2079435 13335029 := bbase (se 5 (by rfl) ⟨625079, by rfl⟩ : syracuseStep 13335029 = 1250159) (by norm_num)
theorem B8890019 : Blo 2079435 8890019 := bstep (se 1 (by rfl) ⟨6667514, by rfl⟩ : syracuseStep 8890019 = 13335029) B13335029
theorem B5926679 : Blo 2079435 5926679 := bstep (se 1 (by rfl) ⟨4445009, by rfl⟩ : syracuseStep 5926679 = 8890019) B8890019
theorem B3951119 : Blo 2079435 3951119 := bstep (se 1 (by rfl) ⟨2963339, by rfl⟩ : syracuseStep 3951119 = 5926679) B5926679
theorem B10536317 : Blo 2079435 10536317 := bstep (se 3 (by rfl) ⟨1975559, by rfl⟩ : syracuseStep 10536317 = 3951119) B3951119
theorem B7024211 : Blo 2079435 7024211 := bstep (se 1 (by rfl) ⟨5268158, by rfl⟩ : syracuseStep 7024211 = 10536317) B10536317
theorem B4682807 : Blo 2079435 4682807 := bstep (se 1 (by rfl) ⟨3512105, by rfl⟩ : syracuseStep 4682807 = 7024211) B7024211
theorem B3121871 : Blo 2079435 3121871 := bstep (se 1 (by rfl) ⟨2341403, by rfl⟩ : syracuseStep 3121871 = 4682807) B4682807
theorem B2081247 : Blo 2079435 2081247 := bstep (se 1 (by rfl) ⟨1560935, by rfl⟩ : syracuseStep 2081247 = 3121871) B3121871
theorem B3121877 : Blo 2079435 3121877 := bbase (se 7 (by rfl) ⟨36584, by rfl⟩ : syracuseStep 3121877 = 73169) (by norm_num)
theorem B2081251 : Blo 2079435 2081251 := bstep (se 1 (by rfl) ⟨1560938, by rfl⟩ : syracuseStep 2081251 = 3121877) B3121877
theorem B6667541 : Blo 2079435 6667541 := bbase (se 6 (by rfl) ⟨156270, by rfl⟩ : syracuseStep 6667541 = 312541) (by norm_num)
theorem B4445027 : Blo 2079435 4445027 := bstep (se 1 (by rfl) ⟨3333770, by rfl⟩ : syracuseStep 4445027 = 6667541) B6667541
theorem B2963351 : Blo 2079435 2963351 := bstep (se 1 (by rfl) ⟨2222513, by rfl⟩ : syracuseStep 2963351 = 4445027) B4445027
theorem B7902269 : Blo 2079435 7902269 := bstep (se 3 (by rfl) ⟨1481675, by rfl⟩ : syracuseStep 7902269 = 2963351) B2963351
theorem B5268179 : Blo 2079435 5268179 := bstep (se 1 (by rfl) ⟨3951134, by rfl⟩ : syracuseStep 5268179 = 7902269) B7902269
theorem B3512119 : Blo 2079435 3512119 := bstep (se 1 (by rfl) ⟨2634089, by rfl⟩ : syracuseStep 3512119 = 5268179) B5268179
theorem B4682825 : Blo 2079435 4682825 := bstep (se 2 (by rfl) ⟨1756059, by rfl⟩ : syracuseStep 4682825 = 3512119) B3512119
theorem B3121883 : Blo 2079435 3121883 := bstep (se 1 (by rfl) ⟨2341412, by rfl⟩ : syracuseStep 3121883 = 4682825) B4682825
theorem B2081255 : Blo 2079435 2081255 := bstep (se 1 (by rfl) ⟨1560941, by rfl⟩ : syracuseStep 2081255 = 3121883) B3121883
theorem B2341417 : Blo 2079435 2341417 := bbase (se 2 (by rfl) ⟨878031, by rfl⟩ : syracuseStep 2341417 = 1756063) (by norm_num)
theorem B3121889 : Blo 2079435 3121889 := bstep (se 2 (by rfl) ⟨1170708, by rfl⟩ : syracuseStep 3121889 = 2341417) B2341417
theorem B2081259 : Blo 2079435 2081259 := bstep (se 1 (by rfl) ⟨1560944, by rfl⟩ : syracuseStep 2081259 = 3121889) B3121889
theorem B28480405 : Blo 2079435 28480405 := bbase (se 6 (by rfl) ⟨667509, by rfl⟩ : syracuseStep 28480405 = 1335019) (by norm_num)
theorem B37973873 : Blo 2079435 37973873 := bstep (se 2 (by rfl) ⟨14240202, by rfl⟩ : syracuseStep 37973873 = 28480405) B28480405
theorem B25315915 : Blo 2079435 25315915 := bstep (se 1 (by rfl) ⟨18986936, by rfl⟩ : syracuseStep 25315915 = 37973873) B37973873
theorem B33754553 : Blo 2079435 33754553 := bstep (se 2 (by rfl) ⟨12657957, by rfl⟩ : syracuseStep 33754553 = 25315915) B25315915
theorem B22503035 : Blo 2079435 22503035 := bstep (se 1 (by rfl) ⟨16877276, by rfl⟩ : syracuseStep 22503035 = 33754553) B33754553
theorem B15002023 : Blo 2079435 15002023 := bstep (se 1 (by rfl) ⟨11251517, by rfl⟩ : syracuseStep 15002023 = 22503035) B22503035
theorem B20002697 : Blo 2079435 20002697 := bstep (se 2 (by rfl) ⟨7501011, by rfl⟩ : syracuseStep 20002697 = 15002023) B15002023
theorem B13335131 : Blo 2079435 13335131 := bstep (se 1 (by rfl) ⟨10001348, by rfl⟩ : syracuseStep 13335131 = 20002697) B20002697
theorem B8890087 : Blo 2079435 8890087 := bstep (se 1 (by rfl) ⟨6667565, by rfl⟩ : syracuseStep 8890087 = 13335131) B13335131
theorem B11853449 : Blo 2079435 11853449 := bstep (se 2 (by rfl) ⟨4445043, by rfl⟩ : syracuseStep 11853449 = 8890087) B8890087
theorem B7902299 : Blo 2079435 7902299 := bstep (se 1 (by rfl) ⟨5926724, by rfl⟩ : syracuseStep 7902299 = 11853449) B11853449
theorem B5268199 : Blo 2079435 5268199 := bstep (se 1 (by rfl) ⟨3951149, by rfl⟩ : syracuseStep 5268199 = 7902299) B7902299
theorem B7024265 : Blo 2079435 7024265 := bstep (se 2 (by rfl) ⟨2634099, by rfl⟩ : syracuseStep 7024265 = 5268199) B5268199
theorem B4682843 : Blo 2079435 4682843 := bstep (se 1 (by rfl) ⟨3512132, by rfl⟩ : syracuseStep 4682843 = 7024265) B7024265
theorem B3121895 : Blo 2079435 3121895 := bstep (se 1 (by rfl) ⟨2341421, by rfl⟩ : syracuseStep 3121895 = 4682843) B4682843
theorem B2081263 : Blo 2079435 2081263 := bstep (se 1 (by rfl) ⟨1560947, by rfl⟩ : syracuseStep 2081263 = 3121895) B3121895
theorem B3121901 : Blo 2079435 3121901 := bbase (se 3 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 3121901 = 1170713) (by norm_num)
theorem B2081267 : Blo 2079435 2081267 := bstep (se 1 (by rfl) ⟨1560950, by rfl⟩ : syracuseStep 2081267 = 3121901) B3121901
theorem B4682861 : Blo 2079435 4682861 := bbase (se 3 (by rfl) ⟨878036, by rfl⟩ : syracuseStep 4682861 = 1756073) (by norm_num)
theorem B3121907 : Blo 2079435 3121907 := bstep (se 1 (by rfl) ⟨2341430, by rfl⟩ : syracuseStep 3121907 = 4682861) B4682861
theorem B2081271 : Blo 2079435 2081271 := bstep (se 1 (by rfl) ⟨1560953, by rfl⟩ : syracuseStep 2081271 = 3121907) B3121907
theorem B3951173 : Blo 2079435 3951173 := bbase (se 4 (by rfl) ⟨370422, by rfl⟩ : syracuseStep 3951173 = 740845) (by norm_num)
theorem B2634115 : Blo 2079435 2634115 := bstep (se 1 (by rfl) ⟨1975586, by rfl⟩ : syracuseStep 2634115 = 3951173) B3951173
theorem B3512153 : Blo 2079435 3512153 := bstep (se 2 (by rfl) ⟨1317057, by rfl⟩ : syracuseStep 3512153 = 2634115) B2634115
theorem B2341435 : Blo 2079435 2341435 := bstep (se 1 (by rfl) ⟨1756076, by rfl⟩ : syracuseStep 2341435 = 3512153) B3512153
theorem B3121913 : Blo 2079435 3121913 := bstep (se 2 (by rfl) ⟨1170717, by rfl⟩ : syracuseStep 3121913 = 2341435) B2341435
theorem B2081275 : Blo 2079435 2081275 := bstep (se 1 (by rfl) ⟨1560956, by rfl⟩ : syracuseStep 2081275 = 3121913) B3121913
theorem B9493541 : Blo 2079435 9493541 := bbase (se 4 (by rfl) ⟨890019, by rfl⟩ : syracuseStep 9493541 = 1780039) (by norm_num)
theorem B6329027 : Blo 2079435 6329027 := bstep (se 1 (by rfl) ⟨4746770, by rfl⟩ : syracuseStep 6329027 = 9493541) B9493541
theorem B4219351 : Blo 2079435 4219351 := bstep (se 1 (by rfl) ⟨3164513, by rfl⟩ : syracuseStep 4219351 = 6329027) B6329027
theorem B22503205 : Blo 2079435 22503205 := bstep (se 4 (by rfl) ⟨2109675, by rfl⟩ : syracuseStep 22503205 = 4219351) B4219351
theorem B30004273 : Blo 2079435 30004273 := bstep (se 2 (by rfl) ⟨11251602, by rfl⟩ : syracuseStep 30004273 = 22503205) B22503205
theorem B40005697 : Blo 2079435 40005697 := bstep (se 2 (by rfl) ⟨15002136, by rfl⟩ : syracuseStep 40005697 = 30004273) B30004273
theorem B53340929 : Blo 2079435 53340929 := bstep (se 2 (by rfl) ⟨20002848, by rfl⟩ : syracuseStep 53340929 = 40005697) B40005697
theorem B35560619 : Blo 2079435 35560619 := bstep (se 1 (by rfl) ⟨26670464, by rfl⟩ : syracuseStep 35560619 = 53340929) B53340929
theorem B23707079 : Blo 2079435 23707079 := bstep (se 1 (by rfl) ⟨17780309, by rfl⟩ : syracuseStep 23707079 = 35560619) B35560619
theorem B15804719 : Blo 2079435 15804719 := bstep (se 1 (by rfl) ⟨11853539, by rfl⟩ : syracuseStep 15804719 = 23707079) B23707079
theorem B10536479 : Blo 2079435 10536479 := bstep (se 1 (by rfl) ⟨7902359, by rfl⟩ : syracuseStep 10536479 = 15804719) B15804719
theorem B7024319 : Blo 2079435 7024319 := bstep (se 1 (by rfl) ⟨5268239, by rfl⟩ : syracuseStep 7024319 = 10536479) B10536479
theorem B4682879 : Blo 2079435 4682879 := bstep (se 1 (by rfl) ⟨3512159, by rfl⟩ : syracuseStep 4682879 = 7024319) B7024319
theorem B3121919 : Blo 2079435 3121919 := bstep (se 1 (by rfl) ⟨2341439, by rfl⟩ : syracuseStep 3121919 = 4682879) B4682879
theorem B2081279 : Blo 2079435 2081279 := bstep (se 1 (by rfl) ⟨1560959, by rfl⟩ : syracuseStep 2081279 = 3121919) B3121919
theorem B3121925 : Blo 2079435 3121925 := bbase (se 4 (by rfl) ⟨292680, by rfl⟩ : syracuseStep 3121925 = 585361) (by norm_num)
theorem B2081283 : Blo 2079435 2081283 := bstep (se 1 (by rfl) ⟨1560962, by rfl⟩ : syracuseStep 2081283 = 3121925) B3121925
theorem B3512173 : Blo 2079435 3512173 := bbase (se 3 (by rfl) ⟨658532, by rfl⟩ : syracuseStep 3512173 = 1317065) (by norm_num)
theorem B4682897 : Blo 2079435 4682897 := bstep (se 2 (by rfl) ⟨1756086, by rfl⟩ : syracuseStep 4682897 = 3512173) B3512173
theorem B3121931 : Blo 2079435 3121931 := bstep (se 1 (by rfl) ⟨2341448, by rfl⟩ : syracuseStep 3121931 = 4682897) B4682897
theorem B2081287 : Blo 2079435 2081287 := bstep (se 1 (by rfl) ⟨1560965, by rfl⟩ : syracuseStep 2081287 = 3121931) B3121931
theorem B2341453 : Blo 2079435 2341453 := bbase (se 3 (by rfl) ⟨439022, by rfl⟩ : syracuseStep 2341453 = 878045) (by norm_num)
theorem B3121937 : Blo 2079435 3121937 := bstep (se 2 (by rfl) ⟨1170726, by rfl⟩ : syracuseStep 3121937 = 2341453) B2341453
theorem B2081291 : Blo 2079435 2081291 := bstep (se 1 (by rfl) ⟨1560968, by rfl⟩ : syracuseStep 2081291 = 3121937) B3121937
theorem B7024373 : Blo 2079435 7024373 := bbase (se 5 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 7024373 = 658535) (by norm_num)
theorem B4682915 : Blo 2079435 4682915 := bstep (se 1 (by rfl) ⟨3512186, by rfl⟩ : syracuseStep 4682915 = 7024373) B7024373
theorem B3121943 : Blo 2079435 3121943 := bstep (se 1 (by rfl) ⟨2341457, by rfl⟩ : syracuseStep 3121943 = 4682915) B4682915
theorem B2081295 : Blo 2079435 2081295 := bstep (se 1 (by rfl) ⟨1560971, by rfl⟩ : syracuseStep 2081295 = 3121943) B3121943
theorem B3121949 : Blo 2079435 3121949 := bbase (se 3 (by rfl) ⟨585365, by rfl⟩ : syracuseStep 3121949 = 1170731) (by norm_num)
theorem B2081299 : Blo 2079435 2081299 := bstep (se 1 (by rfl) ⟨1560974, by rfl⟩ : syracuseStep 2081299 = 3121949) B3121949
theorem B4682933 : Blo 2079435 4682933 := bbase (se 5 (by rfl) ⟨219512, by rfl⟩ : syracuseStep 4682933 = 439025) (by norm_num)
theorem B3121955 : Blo 2079435 3121955 := bstep (se 1 (by rfl) ⟨2341466, by rfl⟩ : syracuseStep 3121955 = 4682933) B4682933
theorem B2081303 : Blo 2079435 2081303 := bstep (se 1 (by rfl) ⟨1560977, by rfl⟩ : syracuseStep 2081303 = 3121955) B3121955
theorem B2222569 : Blo 2079435 2222569 := bbase (se 2 (by rfl) ⟨833463, by rfl⟩ : syracuseStep 2222569 = 1666927) (by norm_num)
theorem B11853701 : Blo 2079435 11853701 := bstep (se 4 (by rfl) ⟨1111284, by rfl⟩ : syracuseStep 11853701 = 2222569) B2222569
theorem B7902467 : Blo 2079435 7902467 := bstep (se 1 (by rfl) ⟨5926850, by rfl⟩ : syracuseStep 7902467 = 11853701) B11853701
theorem B5268311 : Blo 2079435 5268311 := bstep (se 1 (by rfl) ⟨3951233, by rfl⟩ : syracuseStep 5268311 = 7902467) B7902467
theorem B3512207 : Blo 2079435 3512207 := bstep (se 1 (by rfl) ⟨2634155, by rfl⟩ : syracuseStep 3512207 = 5268311) B5268311
theorem B2341471 : Blo 2079435 2341471 := bstep (se 1 (by rfl) ⟨1756103, by rfl⟩ : syracuseStep 2341471 = 3512207) B3512207
theorem B3121961 : Blo 2079435 3121961 := bstep (se 2 (by rfl) ⟨1170735, by rfl⟩ : syracuseStep 3121961 = 2341471) B2341471
theorem B2081307 : Blo 2079435 2081307 := bstep (se 1 (by rfl) ⟨1560980, by rfl⟩ : syracuseStep 2081307 = 3121961) B3121961
theorem B2222573 : Blo 2079435 2222573 := bbase (se 3 (by rfl) ⟨416732, by rfl⟩ : syracuseStep 2222573 = 833465) (by norm_num)
theorem B5926861 : Blo 2079435 5926861 := bstep (se 3 (by rfl) ⟨1111286, by rfl⟩ : syracuseStep 5926861 = 2222573) B2222573
theorem B7902481 : Blo 2079435 7902481 := bstep (se 2 (by rfl) ⟨2963430, by rfl⟩ : syracuseStep 7902481 = 5926861) B5926861
theorem B10536641 : Blo 2079435 10536641 := bstep (se 2 (by rfl) ⟨3951240, by rfl⟩ : syracuseStep 10536641 = 7902481) B7902481
theorem B7024427 : Blo 2079435 7024427 := bstep (se 1 (by rfl) ⟨5268320, by rfl⟩ : syracuseStep 7024427 = 10536641) B10536641
theorem B4682951 : Blo 2079435 4682951 := bstep (se 1 (by rfl) ⟨3512213, by rfl⟩ : syracuseStep 4682951 = 7024427) B7024427
theorem B3121967 : Blo 2079435 3121967 := bstep (se 1 (by rfl) ⟨2341475, by rfl⟩ : syracuseStep 3121967 = 4682951) B4682951
theorem B2081311 : Blo 2079435 2081311 := bstep (se 1 (by rfl) ⟨1560983, by rfl⟩ : syracuseStep 2081311 = 3121967) B3121967
theorem B3121973 : Blo 2079435 3121973 := bbase (se 5 (by rfl) ⟨146342, by rfl⟩ : syracuseStep 3121973 = 292685) (by norm_num)
theorem B2081315 : Blo 2079435 2081315 := bstep (se 1 (by rfl) ⟨1560986, by rfl⟩ : syracuseStep 2081315 = 3121973) B3121973
theorem B5268341 : Blo 2079435 5268341 := bbase (se 5 (by rfl) ⟨246953, by rfl⟩ : syracuseStep 5268341 = 493907) (by norm_num)
theorem B3512227 : Blo 2079435 3512227 := bstep (se 1 (by rfl) ⟨2634170, by rfl⟩ : syracuseStep 3512227 = 5268341) B5268341
theorem B4682969 : Blo 2079435 4682969 := bstep (se 2 (by rfl) ⟨1756113, by rfl⟩ : syracuseStep 4682969 = 3512227) B3512227
theorem B3121979 : Blo 2079435 3121979 := bstep (se 1 (by rfl) ⟨2341484, by rfl⟩ : syracuseStep 3121979 = 4682969) B4682969
theorem B2081319 : Blo 2079435 2081319 := bstep (se 1 (by rfl) ⟨1560989, by rfl⟩ : syracuseStep 2081319 = 3121979) B3121979
theorem B2341489 : Blo 2079435 2341489 := bbase (se 2 (by rfl) ⟨878058, by rfl⟩ : syracuseStep 2341489 = 1756117) (by norm_num)
theorem B3121985 : Blo 2079435 3121985 := bstep (se 2 (by rfl) ⟨1170744, by rfl⟩ : syracuseStep 3121985 = 2341489) B2341489
theorem B2081323 : Blo 2079435 2081323 := bstep (se 1 (by rfl) ⟨1560992, by rfl⟩ : syracuseStep 2081323 = 3121985) B3121985
theorem B2670121 : Blo 2079435 2670121 := bbase (se 2 (by rfl) ⟨1001295, by rfl⟩ : syracuseStep 2670121 = 2002591) (by norm_num)
theorem B3560161 : Blo 2079435 3560161 := bstep (se 2 (by rfl) ⟨1335060, by rfl⟩ : syracuseStep 3560161 = 2670121) B2670121
theorem B4746881 : Blo 2079435 4746881 := bstep (se 2 (by rfl) ⟨1780080, by rfl⟩ : syracuseStep 4746881 = 3560161) B3560161
theorem B12658349 : Blo 2079435 12658349 := bstep (se 3 (by rfl) ⟨2373440, by rfl⟩ : syracuseStep 12658349 = 4746881) B4746881
theorem B8438899 : Blo 2079435 8438899 := bstep (se 1 (by rfl) ⟨6329174, by rfl⟩ : syracuseStep 8438899 = 12658349) B12658349
theorem B11251865 : Blo 2079435 11251865 := bstep (se 2 (by rfl) ⟨4219449, by rfl⟩ : syracuseStep 11251865 = 8438899) B8438899
theorem B7501243 : Blo 2079435 7501243 := bstep (se 1 (by rfl) ⟨5625932, by rfl⟩ : syracuseStep 7501243 = 11251865) B11251865
theorem B10001657 : Blo 2079435 10001657 := bstep (se 2 (by rfl) ⟨3750621, by rfl⟩ : syracuseStep 10001657 = 7501243) B7501243
theorem B6667771 : Blo 2079435 6667771 := bstep (se 1 (by rfl) ⟨5000828, by rfl⟩ : syracuseStep 6667771 = 10001657) B10001657
theorem B8890361 : Blo 2079435 8890361 := bstep (se 2 (by rfl) ⟨3333885, by rfl⟩ : syracuseStep 8890361 = 6667771) B6667771
theorem B5926907 : Blo 2079435 5926907 := bstep (se 1 (by rfl) ⟨4445180, by rfl⟩ : syracuseStep 5926907 = 8890361) B8890361
theorem B3951271 : Blo 2079435 3951271 := bstep (se 1 (by rfl) ⟨2963453, by rfl⟩ : syracuseStep 3951271 = 5926907) B5926907
theorem B5268361 : Blo 2079435 5268361 := bstep (se 2 (by rfl) ⟨1975635, by rfl⟩ : syracuseStep 5268361 = 3951271) B3951271
theorem B7024481 : Blo 2079435 7024481 := bstep (se 2 (by rfl) ⟨2634180, by rfl⟩ : syracuseStep 7024481 = 5268361) B5268361
theorem B4682987 : Blo 2079435 4682987 := bstep (se 1 (by rfl) ⟨3512240, by rfl⟩ : syracuseStep 4682987 = 7024481) B7024481
theorem B3121991 : Blo 2079435 3121991 := bstep (se 1 (by rfl) ⟨2341493, by rfl⟩ : syracuseStep 3121991 = 4682987) B4682987
theorem B2081327 : Blo 2079435 2081327 := bstep (se 1 (by rfl) ⟨1560995, by rfl⟩ : syracuseStep 2081327 = 3121991) B3121991
theorem B3121997 : Blo 2079435 3121997 := bbase (se 3 (by rfl) ⟨585374, by rfl⟩ : syracuseStep 3121997 = 1170749) (by norm_num)
theorem B2081331 : Blo 2079435 2081331 := bstep (se 1 (by rfl) ⟨1560998, by rfl⟩ : syracuseStep 2081331 = 3121997) B3121997
theorem B4683005 : Blo 2079435 4683005 := bbase (se 3 (by rfl) ⟨878063, by rfl⟩ : syracuseStep 4683005 = 1756127) (by norm_num)
theorem B3122003 : Blo 2079435 3122003 := bstep (se 1 (by rfl) ⟨2341502, by rfl⟩ : syracuseStep 3122003 = 4683005) B4683005
theorem B2081335 : Blo 2079435 2081335 := bstep (se 1 (by rfl) ⟨1561001, by rfl⟩ : syracuseStep 2081335 = 3122003) B3122003
theorem B3512261 : Blo 2079435 3512261 := bbase (se 4 (by rfl) ⟨329274, by rfl⟩ : syracuseStep 3512261 = 658549) (by norm_num)
theorem B2341507 : Blo 2079435 2341507 := bstep (se 1 (by rfl) ⟨1756130, by rfl⟩ : syracuseStep 2341507 = 3512261) B3512261
theorem B3122009 : Blo 2079435 3122009 := bstep (se 2 (by rfl) ⟨1170753, by rfl⟩ : syracuseStep 3122009 = 2341507) B2341507
theorem B2081339 : Blo 2079435 2081339 := bstep (se 1 (by rfl) ⟨1561004, by rfl⟩ : syracuseStep 2081339 = 3122009) B3122009
theorem B15805205 : Blo 2079435 15805205 := bbase (se 6 (by rfl) ⟨370434, by rfl⟩ : syracuseStep 15805205 = 740869) (by norm_num)
theorem B10536803 : Blo 2079435 10536803 := bstep (se 1 (by rfl) ⟨7902602, by rfl⟩ : syracuseStep 10536803 = 15805205) B15805205
theorem B7024535 : Blo 2079435 7024535 := bstep (se 1 (by rfl) ⟨5268401, by rfl⟩ : syracuseStep 7024535 = 10536803) B10536803
theorem B4683023 : Blo 2079435 4683023 := bstep (se 1 (by rfl) ⟨3512267, by rfl⟩ : syracuseStep 4683023 = 7024535) B7024535
theorem B3122015 : Blo 2079435 3122015 := bstep (se 1 (by rfl) ⟨2341511, by rfl⟩ : syracuseStep 3122015 = 4683023) B4683023
theorem B2081343 : Blo 2079435 2081343 := bstep (se 1 (by rfl) ⟨1561007, by rfl⟩ : syracuseStep 2081343 = 3122015) B3122015
theorem B3122021 : Blo 2079435 3122021 := bbase (se 4 (by rfl) ⟨292689, by rfl⟩ : syracuseStep 3122021 = 585379) (by norm_num)
theorem B2081347 : Blo 2079435 2081347 := bstep (se 1 (by rfl) ⟨1561010, by rfl⟩ : syracuseStep 2081347 = 3122021) B3122021
theorem B3951317 : Blo 2079435 3951317 := bbase (se 7 (by rfl) ⟨46304, by rfl⟩ : syracuseStep 3951317 = 92609) (by norm_num)
theorem B2634211 : Blo 2079435 2634211 := bstep (se 1 (by rfl) ⟨1975658, by rfl⟩ : syracuseStep 2634211 = 3951317) B3951317
theorem B3512281 : Blo 2079435 3512281 := bstep (se 2 (by rfl) ⟨1317105, by rfl⟩ : syracuseStep 3512281 = 2634211) B2634211
theorem B4683041 : Blo 2079435 4683041 := bstep (se 2 (by rfl) ⟨1756140, by rfl⟩ : syracuseStep 4683041 = 3512281) B3512281
theorem B3122027 : Blo 2079435 3122027 := bstep (se 1 (by rfl) ⟨2341520, by rfl⟩ : syracuseStep 3122027 = 4683041) B4683041
theorem B2081351 : Blo 2079435 2081351 := bstep (se 1 (by rfl) ⟨1561013, by rfl⟩ : syracuseStep 2081351 = 3122027) B3122027
theorem B2341525 : Blo 2079435 2341525 := bbase (se 6 (by rfl) ⟨54879, by rfl⟩ : syracuseStep 2341525 = 109759) (by norm_num)
theorem B3122033 : Blo 2079435 3122033 := bstep (se 2 (by rfl) ⟨1170762, by rfl⟩ : syracuseStep 3122033 = 2341525) B2341525
theorem B2081355 : Blo 2079435 2081355 := bstep (se 1 (by rfl) ⟨1561016, by rfl⟩ : syracuseStep 2081355 = 3122033) B3122033
theorem B2634221 : Blo 2079435 2634221 := bbase (se 3 (by rfl) ⟨493916, by rfl⟩ : syracuseStep 2634221 = 987833) (by norm_num)
theorem B7024589 : Blo 2079435 7024589 := bstep (se 3 (by rfl) ⟨1317110, by rfl⟩ : syracuseStep 7024589 = 2634221) B2634221
theorem B4683059 : Blo 2079435 4683059 := bstep (se 1 (by rfl) ⟨3512294, by rfl⟩ : syracuseStep 4683059 = 7024589) B7024589
theorem B3122039 : Blo 2079435 3122039 := bstep (se 1 (by rfl) ⟨2341529, by rfl⟩ : syracuseStep 3122039 = 4683059) B4683059
theorem B2081359 : Blo 2079435 2081359 := bstep (se 1 (by rfl) ⟨1561019, by rfl⟩ : syracuseStep 2081359 = 3122039) B3122039
theorem B3122045 : Blo 2079435 3122045 := bbase (se 3 (by rfl) ⟨585383, by rfl⟩ : syracuseStep 3122045 = 1170767) (by norm_num)
theorem B2081363 : Blo 2079435 2081363 := bstep (se 1 (by rfl) ⟨1561022, by rfl⟩ : syracuseStep 2081363 = 3122045) B3122045
theorem B4683077 : Blo 2079435 4683077 := bbase (se 4 (by rfl) ⟨439038, by rfl⟩ : syracuseStep 4683077 = 878077) (by norm_num)
theorem B3122051 : Blo 2079435 3122051 := bstep (se 1 (by rfl) ⟨2341538, by rfl⟩ : syracuseStep 3122051 = 4683077) B4683077
theorem B2081367 : Blo 2079435 2081367 := bstep (se 1 (by rfl) ⟨1561025, by rfl⟩ : syracuseStep 2081367 = 3122051) B3122051
theorem B8010533 : Blo 2079435 8010533 := bbase (se 4 (by rfl) ⟨750987, by rfl⟩ : syracuseStep 8010533 = 1501975) (by norm_num)
theorem B21361421 : Blo 2079435 21361421 := bstep (se 3 (by rfl) ⟨4005266, by rfl⟩ : syracuseStep 21361421 = 8010533) B8010533
theorem B14240947 : Blo 2079435 14240947 := bstep (se 1 (by rfl) ⟨10680710, by rfl⟩ : syracuseStep 14240947 = 21361421) B21361421
theorem B18987929 : Blo 2079435 18987929 := bstep (se 2 (by rfl) ⟨7120473, by rfl⟩ : syracuseStep 18987929 = 14240947) B14240947
theorem B12658619 : Blo 2079435 12658619 := bstep (se 1 (by rfl) ⟨9493964, by rfl⟩ : syracuseStep 12658619 = 18987929) B18987929
theorem B8439079 : Blo 2079435 8439079 := bstep (se 1 (by rfl) ⟨6329309, by rfl⟩ : syracuseStep 8439079 = 12658619) B12658619
theorem B11252105 : Blo 2079435 11252105 := bstep (se 2 (by rfl) ⟨4219539, by rfl⟩ : syracuseStep 11252105 = 8439079) B8439079
theorem B7501403 : Blo 2079435 7501403 := bstep (se 1 (by rfl) ⟨5626052, by rfl⟩ : syracuseStep 7501403 = 11252105) B11252105
theorem B5000935 : Blo 2079435 5000935 := bstep (se 1 (by rfl) ⟨3750701, by rfl⟩ : syracuseStep 5000935 = 7501403) B7501403
theorem B6667913 : Blo 2079435 6667913 := bstep (se 2 (by rfl) ⟨2500467, by rfl⟩ : syracuseStep 6667913 = 5000935) B5000935
theorem B4445275 : Blo 2079435 4445275 := bstep (se 1 (by rfl) ⟨3333956, by rfl⟩ : syracuseStep 4445275 = 6667913) B6667913
theorem B5927033 : Blo 2079435 5927033 := bstep (se 2 (by rfl) ⟨2222637, by rfl⟩ : syracuseStep 5927033 = 4445275) B4445275
theorem B3951355 : Blo 2079435 3951355 := bstep (se 1 (by rfl) ⟨2963516, by rfl⟩ : syracuseStep 3951355 = 5927033) B5927033
theorem B5268473 : Blo 2079435 5268473 := bstep (se 2 (by rfl) ⟨1975677, by rfl⟩ : syracuseStep 5268473 = 3951355) B3951355
theorem B3512315 : Blo 2079435 3512315 := bstep (se 1 (by rfl) ⟨2634236, by rfl⟩ : syracuseStep 3512315 = 5268473) B5268473
theorem B2341543 : Blo 2079435 2341543 := bstep (se 1 (by rfl) ⟨1756157, by rfl⟩ : syracuseStep 2341543 = 3512315) B3512315
theorem B3122057 : Blo 2079435 3122057 := bstep (se 2 (by rfl) ⟨1170771, by rfl⟩ : syracuseStep 3122057 = 2341543) B2341543
theorem B2081371 : Blo 2079435 2081371 := bstep (se 1 (by rfl) ⟨1561028, by rfl⟩ : syracuseStep 2081371 = 3122057) B3122057
theorem B10536965 : Blo 2079435 10536965 := bbase (se 4 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 10536965 = 1975681) (by norm_num)
theorem B7024643 : Blo 2079435 7024643 := bstep (se 1 (by rfl) ⟨5268482, by rfl⟩ : syracuseStep 7024643 = 10536965) B10536965
theorem B4683095 : Blo 2079435 4683095 := bstep (se 1 (by rfl) ⟨3512321, by rfl⟩ : syracuseStep 4683095 = 7024643) B7024643
theorem B3122063 : Blo 2079435 3122063 := bstep (se 1 (by rfl) ⟨2341547, by rfl⟩ : syracuseStep 3122063 = 4683095) B4683095
theorem B2081375 : Blo 2079435 2081375 := bstep (se 1 (by rfl) ⟨1561031, by rfl⟩ : syracuseStep 2081375 = 3122063) B3122063
theorem B3122069 : Blo 2079435 3122069 := bbase (se 6 (by rfl) ⟨73173, by rfl⟩ : syracuseStep 3122069 = 146347) (by norm_num)
theorem B2081379 : Blo 2079435 2081379 := bstep (se 1 (by rfl) ⟨1561034, by rfl⟩ : syracuseStep 2081379 = 3122069) B3122069
theorem B11854133 : Blo 2079435 11854133 := bbase (se 5 (by rfl) ⟨555662, by rfl⟩ : syracuseStep 11854133 = 1111325) (by norm_num)
theorem B7902755 : Blo 2079435 7902755 := bstep (se 1 (by rfl) ⟨5927066, by rfl⟩ : syracuseStep 7902755 = 11854133) B11854133
theorem B5268503 : Blo 2079435 5268503 := bstep (se 1 (by rfl) ⟨3951377, by rfl⟩ : syracuseStep 5268503 = 7902755) B7902755
theorem B3512335 : Blo 2079435 3512335 := bstep (se 1 (by rfl) ⟨2634251, by rfl⟩ : syracuseStep 3512335 = 5268503) B5268503
theorem B4683113 : Blo 2079435 4683113 := bstep (se 2 (by rfl) ⟨1756167, by rfl⟩ : syracuseStep 4683113 = 3512335) B3512335
theorem B3122075 : Blo 2079435 3122075 := bstep (se 1 (by rfl) ⟨2341556, by rfl⟩ : syracuseStep 3122075 = 4683113) B4683113
theorem B2081383 : Blo 2079435 2081383 := bstep (se 1 (by rfl) ⟨1561037, by rfl⟩ : syracuseStep 2081383 = 3122075) B3122075
theorem B2341561 : Blo 2079435 2341561 := bbase (se 2 (by rfl) ⟨878085, by rfl⟩ : syracuseStep 2341561 = 1756171) (by norm_num)
theorem B3122081 : Blo 2079435 3122081 := bstep (se 2 (by rfl) ⟨1170780, by rfl⟩ : syracuseStep 3122081 = 2341561) B2341561
theorem B2081387 : Blo 2079435 2081387 := bstep (se 1 (by rfl) ⟨1561040, by rfl⟩ : syracuseStep 2081387 = 3122081) B3122081
theorem B4445317 : Blo 2079435 4445317 := bbase (se 4 (by rfl) ⟨416748, by rfl⟩ : syracuseStep 4445317 = 833497) (by norm_num)
theorem B5927089 : Blo 2079435 5927089 := bstep (se 2 (by rfl) ⟨2222658, by rfl⟩ : syracuseStep 5927089 = 4445317) B4445317
theorem B7902785 : Blo 2079435 7902785 := bstep (se 2 (by rfl) ⟨2963544, by rfl⟩ : syracuseStep 7902785 = 5927089) B5927089
theorem B5268523 : Blo 2079435 5268523 := bstep (se 1 (by rfl) ⟨3951392, by rfl⟩ : syracuseStep 5268523 = 7902785) B7902785
theorem B7024697 : Blo 2079435 7024697 := bstep (se 2 (by rfl) ⟨2634261, by rfl⟩ : syracuseStep 7024697 = 5268523) B5268523
theorem B4683131 : Blo 2079435 4683131 := bstep (se 1 (by rfl) ⟨3512348, by rfl⟩ : syracuseStep 4683131 = 7024697) B7024697
theorem B3122087 : Blo 2079435 3122087 := bstep (se 1 (by rfl) ⟨2341565, by rfl⟩ : syracuseStep 3122087 = 4683131) B4683131
theorem B2081391 : Blo 2079435 2081391 := bstep (se 1 (by rfl) ⟨1561043, by rfl⟩ : syracuseStep 2081391 = 3122087) B3122087
theorem B3122093 : Blo 2079435 3122093 := bbase (se 3 (by rfl) ⟨585392, by rfl⟩ : syracuseStep 3122093 = 1170785) (by norm_num)
theorem B2081395 : Blo 2079435 2081395 := bstep (se 1 (by rfl) ⟨1561046, by rfl⟩ : syracuseStep 2081395 = 3122093) B3122093
theorem B4683149 : Blo 2079435 4683149 := bbase (se 3 (by rfl) ⟨878090, by rfl⟩ : syracuseStep 4683149 = 1756181) (by norm_num)
theorem B3122099 : Blo 2079435 3122099 := bstep (se 1 (by rfl) ⟨2341574, by rfl⟩ : syracuseStep 3122099 = 4683149) B4683149
theorem B2081399 : Blo 2079435 2081399 := bstep (se 1 (by rfl) ⟨1561049, by rfl⟩ : syracuseStep 2081399 = 3122099) B3122099
theorem B2634277 : Blo 2079435 2634277 := bbase (se 4 (by rfl) ⟨246963, by rfl⟩ : syracuseStep 2634277 = 493927) (by norm_num)
theorem B3512369 : Blo 2079435 3512369 := bstep (se 2 (by rfl) ⟨1317138, by rfl⟩ : syracuseStep 3512369 = 2634277) B2634277
theorem B2341579 : Blo 2079435 2341579 := bstep (se 1 (by rfl) ⟨1756184, by rfl⟩ : syracuseStep 2341579 = 3512369) B3512369
theorem B3122105 : Blo 2079435 3122105 := bstep (se 2 (by rfl) ⟨1170789, by rfl⟩ : syracuseStep 3122105 = 2341579) B2341579
theorem B2081403 : Blo 2079435 2081403 := bstep (se 1 (by rfl) ⟨1561052, by rfl⟩ : syracuseStep 2081403 = 3122105) B3122105
theorem B10138501 : Blo 2079435 10138501 := bbase (se 4 (by rfl) ⟨950484, by rfl⟩ : syracuseStep 10138501 = 1900969) (by norm_num)
theorem B13518001 : Blo 2079435 13518001 := bstep (se 2 (by rfl) ⟨5069250, by rfl⟩ : syracuseStep 13518001 = 10138501) B10138501
theorem B18024001 : Blo 2079435 18024001 := bstep (se 2 (by rfl) ⟨6759000, by rfl⟩ : syracuseStep 18024001 = 13518001) B13518001
theorem B384512021 : Blo 2079435 384512021 := bstep (se 6 (by rfl) ⟨9012000, by rfl⟩ : syracuseStep 384512021 = 18024001) B18024001
theorem B256341347 : Blo 2079435 256341347 := bstep (se 1 (by rfl) ⟨192256010, by rfl⟩ : syracuseStep 256341347 = 384512021) B384512021
theorem B170894231 : Blo 2079435 170894231 := bstep (se 1 (by rfl) ⟨128170673, by rfl⟩ : syracuseStep 170894231 = 256341347) B256341347
theorem B113929487 : Blo 2079435 113929487 := bstep (se 1 (by rfl) ⟨85447115, by rfl⟩ : syracuseStep 113929487 = 170894231) B170894231
theorem B75952991 : Blo 2079435 75952991 := bstep (se 1 (by rfl) ⟨56964743, by rfl⟩ : syracuseStep 75952991 = 113929487) B113929487
theorem B50635327 : Blo 2079435 50635327 := bstep (se 1 (by rfl) ⟨37976495, by rfl⟩ : syracuseStep 50635327 = 75952991) B75952991
theorem B67513769 : Blo 2079435 67513769 := bstep (se 2 (by rfl) ⟨25317663, by rfl⟩ : syracuseStep 67513769 = 50635327) B50635327
theorem B45009179 : Blo 2079435 45009179 := bstep (se 1 (by rfl) ⟨33756884, by rfl⟩ : syracuseStep 45009179 = 67513769) B67513769
theorem B30006119 : Blo 2079435 30006119 := bstep (se 1 (by rfl) ⟨22504589, by rfl⟩ : syracuseStep 30006119 = 45009179) B45009179
theorem B20004079 : Blo 2079435 20004079 := bstep (se 1 (by rfl) ⟨15003059, by rfl⟩ : syracuseStep 20004079 = 30006119) B30006119
theorem B26672105 : Blo 2079435 26672105 := bstep (se 2 (by rfl) ⟨10002039, by rfl⟩ : syracuseStep 26672105 = 20004079) B20004079
theorem B17781403 : Blo 2079435 17781403 := bstep (se 1 (by rfl) ⟨13336052, by rfl⟩ : syracuseStep 17781403 = 26672105) B26672105
theorem B23708537 : Blo 2079435 23708537 := bstep (se 2 (by rfl) ⟨8890701, by rfl⟩ : syracuseStep 23708537 = 17781403) B17781403
theorem B15805691 : Blo 2079435 15805691 := bstep (se 1 (by rfl) ⟨11854268, by rfl⟩ : syracuseStep 15805691 = 23708537) B23708537
theorem B10537127 : Blo 2079435 10537127 := bstep (se 1 (by rfl) ⟨7902845, by rfl⟩ : syracuseStep 10537127 = 15805691) B15805691
theorem B7024751 : Blo 2079435 7024751 := bstep (se 1 (by rfl) ⟨5268563, by rfl⟩ : syracuseStep 7024751 = 10537127) B10537127
theorem B4683167 : Blo 2079435 4683167 := bstep (se 1 (by rfl) ⟨3512375, by rfl⟩ : syracuseStep 4683167 = 7024751) B7024751
theorem B3122111 : Blo 2079435 3122111 := bstep (se 1 (by rfl) ⟨2341583, by rfl⟩ : syracuseStep 3122111 = 4683167) B4683167
theorem B2081407 : Blo 2079435 2081407 := bstep (se 1 (by rfl) ⟨1561055, by rfl⟩ : syracuseStep 2081407 = 3122111) B3122111
theorem B3122117 : Blo 2079435 3122117 := bbase (se 4 (by rfl) ⟨292698, by rfl⟩ : syracuseStep 3122117 = 585397) (by norm_num)
theorem B2081411 : Blo 2079435 2081411 := bstep (se 1 (by rfl) ⟨1561058, by rfl⟩ : syracuseStep 2081411 = 3122117) B3122117
theorem B3512389 : Blo 2079435 3512389 := bbase (se 4 (by rfl) ⟨329286, by rfl⟩ : syracuseStep 3512389 = 658573) (by norm_num)
theorem B4683185 : Blo 2079435 4683185 := bstep (se 2 (by rfl) ⟨1756194, by rfl⟩ : syracuseStep 4683185 = 3512389) B3512389
theorem B3122123 : Blo 2079435 3122123 := bstep (se 1 (by rfl) ⟨2341592, by rfl⟩ : syracuseStep 3122123 = 4683185) B4683185
theorem B2081415 : Blo 2079435 2081415 := bstep (se 1 (by rfl) ⟨1561061, by rfl⟩ : syracuseStep 2081415 = 3122123) B3122123
theorem B2341597 : Blo 2079435 2341597 := bbase (se 3 (by rfl) ⟨439049, by rfl⟩ : syracuseStep 2341597 = 878099) (by norm_num)
theorem B3122129 : Blo 2079435 3122129 := bstep (se 2 (by rfl) ⟨1170798, by rfl⟩ : syracuseStep 3122129 = 2341597) B2341597
theorem B2081419 : Blo 2079435 2081419 := bstep (se 1 (by rfl) ⟨1561064, by rfl⟩ : syracuseStep 2081419 = 3122129) B3122129
theorem B7024805 : Blo 2079435 7024805 := bbase (se 4 (by rfl) ⟨658575, by rfl⟩ : syracuseStep 7024805 = 1317151) (by norm_num)
theorem B4683203 : Blo 2079435 4683203 := bstep (se 1 (by rfl) ⟨3512402, by rfl⟩ : syracuseStep 4683203 = 7024805) B7024805
theorem B3122135 : Blo 2079435 3122135 := bstep (se 1 (by rfl) ⟨2341601, by rfl⟩ : syracuseStep 3122135 = 4683203) B4683203
theorem B2081423 : Blo 2079435 2081423 := bstep (se 1 (by rfl) ⟨1561067, by rfl⟩ : syracuseStep 2081423 = 3122135) B3122135
theorem B3122141 : Blo 2079435 3122141 := bbase (se 3 (by rfl) ⟨585401, by rfl⟩ : syracuseStep 3122141 = 1170803) (by norm_num)
theorem B2081427 : Blo 2079435 2081427 := bstep (se 1 (by rfl) ⟨1561070, by rfl⟩ : syracuseStep 2081427 = 3122141) B3122141
theorem B4683221 : Blo 2079435 4683221 := bbase (se 7 (by rfl) ⟨54881, by rfl⟩ : syracuseStep 4683221 = 109763) (by norm_num)
theorem B3122147 : Blo 2079435 3122147 := bstep (se 1 (by rfl) ⟨2341610, by rfl⟩ : syracuseStep 3122147 = 4683221) B4683221
theorem B2081431 : Blo 2079435 2081431 := bstep (se 1 (by rfl) ⟨1561073, by rfl⟩ : syracuseStep 2081431 = 3122147) B3122147
theorem B2851493 : Blo 2079435 2851493 := bbase (se 4 (by rfl) ⟨267327, by rfl⟩ : syracuseStep 2851493 = 534655) (by norm_num)
theorem B30415925 : Blo 2079435 30415925 := bstep (se 5 (by rfl) ⟨1425746, by rfl⟩ : syracuseStep 30415925 = 2851493) B2851493
theorem B81109133 : Blo 2079435 81109133 := bstep (se 3 (by rfl) ⟨15207962, by rfl⟩ : syracuseStep 81109133 = 30415925) B30415925
theorem B54072755 : Blo 2079435 54072755 := bstep (se 1 (by rfl) ⟨40554566, by rfl⟩ : syracuseStep 54072755 = 81109133) B81109133
theorem B36048503 : Blo 2079435 36048503 := bstep (se 1 (by rfl) ⟨27036377, by rfl⟩ : syracuseStep 36048503 = 54072755) B54072755
theorem B24032335 : Blo 2079435 24032335 := bstep (se 1 (by rfl) ⟨18024251, by rfl⟩ : syracuseStep 24032335 = 36048503) B36048503
theorem B32043113 : Blo 2079435 32043113 := bstep (se 2 (by rfl) ⟨12016167, by rfl⟩ : syracuseStep 32043113 = 24032335) B24032335
theorem B21362075 : Blo 2079435 21362075 := bstep (se 1 (by rfl) ⟨16021556, by rfl⟩ : syracuseStep 21362075 = 32043113) B32043113
theorem B14241383 : Blo 2079435 14241383 := bstep (se 1 (by rfl) ⟨10681037, by rfl⟩ : syracuseStep 14241383 = 21362075) B21362075
theorem B9494255 : Blo 2079435 9494255 := bstep (se 1 (by rfl) ⟨7120691, by rfl⟩ : syracuseStep 9494255 = 14241383) B14241383
theorem B6329503 : Blo 2079435 6329503 := bstep (se 1 (by rfl) ⟨4747127, by rfl⟩ : syracuseStep 6329503 = 9494255) B9494255
theorem B8439337 : Blo 2079435 8439337 := bstep (se 2 (by rfl) ⟨3164751, by rfl⟩ : syracuseStep 8439337 = 6329503) B6329503
theorem B11252449 : Blo 2079435 11252449 := bstep (se 2 (by rfl) ⟨4219668, by rfl⟩ : syracuseStep 11252449 = 8439337) B8439337
theorem B15003265 : Blo 2079435 15003265 := bstep (se 2 (by rfl) ⟨5626224, by rfl⟩ : syracuseStep 15003265 = 11252449) B11252449
theorem B20004353 : Blo 2079435 20004353 := bstep (se 2 (by rfl) ⟨7501632, by rfl⟩ : syracuseStep 20004353 = 15003265) B15003265
theorem B13336235 : Blo 2079435 13336235 := bstep (se 1 (by rfl) ⟨10002176, by rfl⟩ : syracuseStep 13336235 = 20004353) B20004353
theorem B8890823 : Blo 2079435 8890823 := bstep (se 1 (by rfl) ⟨6668117, by rfl⟩ : syracuseStep 8890823 = 13336235) B13336235
theorem B5927215 : Blo 2079435 5927215 := bstep (se 1 (by rfl) ⟨4445411, by rfl⟩ : syracuseStep 5927215 = 8890823) B8890823
theorem B7902953 : Blo 2079435 7902953 := bstep (se 2 (by rfl) ⟨2963607, by rfl⟩ : syracuseStep 7902953 = 5927215) B5927215
theorem B5268635 : Blo 2079435 5268635 := bstep (se 1 (by rfl) ⟨3951476, by rfl⟩ : syracuseStep 5268635 = 7902953) B7902953
theorem B3512423 : Blo 2079435 3512423 := bstep (se 1 (by rfl) ⟨2634317, by rfl⟩ : syracuseStep 3512423 = 5268635) B5268635
theorem B2341615 : Blo 2079435 2341615 := bstep (se 1 (by rfl) ⟨1756211, by rfl⟩ : syracuseStep 2341615 = 3512423) B3512423
theorem B3122153 : Blo 2079435 3122153 := bstep (se 2 (by rfl) ⟨1170807, by rfl⟩ : syracuseStep 3122153 = 2341615) B2341615
theorem B2081435 : Blo 2079435 2081435 := bstep (se 1 (by rfl) ⟨1561076, by rfl⟩ : syracuseStep 2081435 = 3122153) B3122153
theorem C0 (j : ℕ) (h1 : 519858 ≤ j) (h2 : j ≤ 520358) : Blo 2079435 (4 * j + 3) := by
  interval_cases j
  · exact B2079435
  · exact B2079439
  · exact B2079443
  · exact B2079447
  · exact B2079451
  · exact B2079455
  · exact B2079459
  · exact B2079463
  · exact B2079467
  · exact B2079471
  · exact B2079475
  · exact B2079479
  · exact B2079483
  · exact B2079487
  · exact B2079491
  · exact B2079495
  · exact B2079499
  · exact B2079503
  · exact B2079507
  · exact B2079511
  · exact B2079515
  · exact B2079519
  · exact B2079523
  · exact B2079527
  · exact B2079531
  · exact B2079535
  · exact B2079539
  · exact B2079543
  · exact B2079547
  · exact B2079551
  · exact B2079555
  · exact B2079559
  · exact B2079563
  · exact B2079567
  · exact B2079571
  · exact B2079575
  · exact B2079579
  · exact B2079583
  · exact B2079587
  · exact B2079591
  · exact B2079595
  · exact B2079599
  · exact B2079603
  · exact B2079607
  · exact B2079611
  · exact B2079615
  · exact B2079619
  · exact B2079623
  · exact B2079627
  · exact B2079631
  · exact B2079635
  · exact B2079639
  · exact B2079643
  · exact B2079647
  · exact B2079651
  · exact B2079655
  · exact B2079659
  · exact B2079663
  · exact B2079667
  · exact B2079671
  · exact B2079675
  · exact B2079679
  · exact B2079683
  · exact B2079687
  · exact B2079691
  · exact B2079695
  · exact B2079699
  · exact B2079703
  · exact B2079707
  · exact B2079711
  · exact B2079715
  · exact B2079719
  · exact B2079723
  · exact B2079727
  · exact B2079731
  · exact B2079735
  · exact B2079739
  · exact B2079743
  · exact B2079747
  · exact B2079751
  · exact B2079755
  · exact B2079759
  · exact B2079763
  · exact B2079767
  · exact B2079771
  · exact B2079775
  · exact B2079779
  · exact B2079783
  · exact B2079787
  · exact B2079791
  · exact B2079795
  · exact B2079799
  · exact B2079803
  · exact B2079807
  · exact B2079811
  · exact B2079815
  · exact B2079819
  · exact B2079823
  · exact B2079827
  · exact B2079831
  · exact B2079835
  · exact B2079839
  · exact B2079843
  · exact B2079847
  · exact B2079851
  · exact B2079855
  · exact B2079859
  · exact B2079863
  · exact B2079867
  · exact B2079871
  · exact B2079875
  · exact B2079879
  · exact B2079883
  · exact B2079887
  · exact B2079891
  · exact B2079895
  · exact B2079899
  · exact B2079903
  · exact B2079907
  · exact B2079911
  · exact B2079915
  · exact B2079919
  · exact B2079923
  · exact B2079927
  · exact B2079931
  · exact B2079935
  · exact B2079939
  · exact B2079943
  · exact B2079947
  · exact B2079951
  · exact B2079955
  · exact B2079959
  · exact B2079963
  · exact B2079967
  · exact B2079971
  · exact B2079975
  · exact B2079979
  · exact B2079983
  · exact B2079987
  · exact B2079991
  · exact B2079995
  · exact B2079999
  · exact B2080003
  · exact B2080007
  · exact B2080011
  · exact B2080015
  · exact B2080019
  · exact B2080023
  · exact B2080027
  · exact B2080031
  · exact B2080035
  · exact B2080039
  · exact B2080043
  · exact B2080047
  · exact B2080051
  · exact B2080055
  · exact B2080059
  · exact B2080063
  · exact B2080067
  · exact B2080071
  · exact B2080075
  · exact B2080079
  · exact B2080083
  · exact B2080087
  · exact B2080091
  · exact B2080095
  · exact B2080099
  · exact B2080103
  · exact B2080107
  · exact B2080111
  · exact B2080115
  · exact B2080119
  · exact B2080123
  · exact B2080127
  · exact B2080131
  · exact B2080135
  · exact B2080139
  · exact B2080143
  · exact B2080147
  · exact B2080151
  · exact B2080155
  · exact B2080159
  · exact B2080163
  · exact B2080167
  · exact B2080171
  · exact B2080175
  · exact B2080179
  · exact B2080183
  · exact B2080187
  · exact B2080191
  · exact B2080195
  · exact B2080199
  · exact B2080203
  · exact B2080207
  · exact B2080211
  · exact B2080215
  · exact B2080219
  · exact B2080223
  · exact B2080227
  · exact B2080231
  · exact B2080235
  · exact B2080239
  · exact B2080243
  · exact B2080247
  · exact B2080251
  · exact B2080255
  · exact B2080259
  · exact B2080263
  · exact B2080267
  · exact B2080271
  · exact B2080275
  · exact B2080279
  · exact B2080283
  · exact B2080287
  · exact B2080291
  · exact B2080295
  · exact B2080299
  · exact B2080303
  · exact B2080307
  · exact B2080311
  · exact B2080315
  · exact B2080319
  · exact B2080323
  · exact B2080327
  · exact B2080331
  · exact B2080335
  · exact B2080339
  · exact B2080343
  · exact B2080347
  · exact B2080351
  · exact B2080355
  · exact B2080359
  · exact B2080363
  · exact B2080367
  · exact B2080371
  · exact B2080375
  · exact B2080379
  · exact B2080383
  · exact B2080387
  · exact B2080391
  · exact B2080395
  · exact B2080399
  · exact B2080403
  · exact B2080407
  · exact B2080411
  · exact B2080415
  · exact B2080419
  · exact B2080423
  · exact B2080427
  · exact B2080431
  · exact B2080435
  · exact B2080439
  · exact B2080443
  · exact B2080447
  · exact B2080451
  · exact B2080455
  · exact B2080459
  · exact B2080463
  · exact B2080467
  · exact B2080471
  · exact B2080475
  · exact B2080479
  · exact B2080483
  · exact B2080487
  · exact B2080491
  · exact B2080495
  · exact B2080499
  · exact B2080503
  · exact B2080507
  · exact B2080511
  · exact B2080515
  · exact B2080519
  · exact B2080523
  · exact B2080527
  · exact B2080531
  · exact B2080535
  · exact B2080539
  · exact B2080543
  · exact B2080547
  · exact B2080551
  · exact B2080555
  · exact B2080559
  · exact B2080563
  · exact B2080567
  · exact B2080571
  · exact B2080575
  · exact B2080579
  · exact B2080583
  · exact B2080587
  · exact B2080591
  · exact B2080595
  · exact B2080599
  · exact B2080603
  · exact B2080607
  · exact B2080611
  · exact B2080615
  · exact B2080619
  · exact B2080623
  · exact B2080627
  · exact B2080631
  · exact B2080635
  · exact B2080639
  · exact B2080643
  · exact B2080647
  · exact B2080651
  · exact B2080655
  · exact B2080659
  · exact B2080663
  · exact B2080667
  · exact B2080671
  · exact B2080675
  · exact B2080679
  · exact B2080683
  · exact B2080687
  · exact B2080691
  · exact B2080695
  · exact B2080699
  · exact B2080703
  · exact B2080707
  · exact B2080711
  · exact B2080715
  · exact B2080719
  · exact B2080723
  · exact B2080727
  · exact B2080731
  · exact B2080735
  · exact B2080739
  · exact B2080743
  · exact B2080747
  · exact B2080751
  · exact B2080755
  · exact B2080759
  · exact B2080763
  · exact B2080767
  · exact B2080771
  · exact B2080775
  · exact B2080779
  · exact B2080783
  · exact B2080787
  · exact B2080791
  · exact B2080795
  · exact B2080799
  · exact B2080803
  · exact B2080807
  · exact B2080811
  · exact B2080815
  · exact B2080819
  · exact B2080823
  · exact B2080827
  · exact B2080831
  · exact B2080835
  · exact B2080839
  · exact B2080843
  · exact B2080847
  · exact B2080851
  · exact B2080855
  · exact B2080859
  · exact B2080863
  · exact B2080867
  · exact B2080871
  · exact B2080875
  · exact B2080879
  · exact B2080883
  · exact B2080887
  · exact B2080891
  · exact B2080895
  · exact B2080899
  · exact B2080903
  · exact B2080907
  · exact B2080911
  · exact B2080915
  · exact B2080919
  · exact B2080923
  · exact B2080927
  · exact B2080931
  · exact B2080935
  · exact B2080939
  · exact B2080943
  · exact B2080947
  · exact B2080951
  · exact B2080955
  · exact B2080959
  · exact B2080963
  · exact B2080967
  · exact B2080971
  · exact B2080975
  · exact B2080979
  · exact B2080983
  · exact B2080987
  · exact B2080991
  · exact B2080995
  · exact B2080999
  · exact B2081003
  · exact B2081007
  · exact B2081011
  · exact B2081015
  · exact B2081019
  · exact B2081023
  · exact B2081027
  · exact B2081031
  · exact B2081035
  · exact B2081039
  · exact B2081043
  · exact B2081047
  · exact B2081051
  · exact B2081055
  · exact B2081059
  · exact B2081063
  · exact B2081067
  · exact B2081071
  · exact B2081075
  · exact B2081079
  · exact B2081083
  · exact B2081087
  · exact B2081091
  · exact B2081095
  · exact B2081099
  · exact B2081103
  · exact B2081107
  · exact B2081111
  · exact B2081115
  · exact B2081119
  · exact B2081123
  · exact B2081127
  · exact B2081131
  · exact B2081135
  · exact B2081139
  · exact B2081143
  · exact B2081147
  · exact B2081151
  · exact B2081155
  · exact B2081159
  · exact B2081163
  · exact B2081167
  · exact B2081171
  · exact B2081175
  · exact B2081179
  · exact B2081183
  · exact B2081187
  · exact B2081191
  · exact B2081195
  · exact B2081199
  · exact B2081203
  · exact B2081207
  · exact B2081211
  · exact B2081215
  · exact B2081219
  · exact B2081223
  · exact B2081227
  · exact B2081231
  · exact B2081235
  · exact B2081239
  · exact B2081243
  · exact B2081247
  · exact B2081251
  · exact B2081255
  · exact B2081259
  · exact B2081263
  · exact B2081267
  · exact B2081271
  · exact B2081275
  · exact B2081279
  · exact B2081283
  · exact B2081287
  · exact B2081291
  · exact B2081295
  · exact B2081299
  · exact B2081303
  · exact B2081307
  · exact B2081311
  · exact B2081315
  · exact B2081319
  · exact B2081323
  · exact B2081327
  · exact B2081331
  · exact B2081335
  · exact B2081339
  · exact B2081343
  · exact B2081347
  · exact B2081351
  · exact B2081355
  · exact B2081359
  · exact B2081363
  · exact B2081367
  · exact B2081371
  · exact B2081375
  · exact B2081379
  · exact B2081383
  · exact B2081387
  · exact B2081391
  · exact B2081395
  · exact B2081399
  · exact B2081403
  · exact B2081407
  · exact B2081411
  · exact B2081415
  · exact B2081419
  · exact B2081423
  · exact B2081427
  · exact B2081431
  · exact B2081435
theorem solution (m : ℕ) (hlo : 2079435 ≤ m) (hhi : m ≤ 2081435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 519858 ≤ j := by omega
    have hj2 : j ≤ 520358 := by omega
    have hb : Blo 2079435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
