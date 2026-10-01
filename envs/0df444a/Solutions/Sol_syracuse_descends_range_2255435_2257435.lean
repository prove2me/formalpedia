-- Prove2me | solution 1 for syracuse_descends_range_2255435_2257435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:12.244374+00:00
-- url     : https://prove2.me/submissions/9b131268-b682-43aa-8655-58fbdaf4ef16

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

theorem B2537365 : Blo 2255435 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B3383153 : Blo 2255435 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B2255435 : Blo 2255435 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B2854541 : Blo 2255435 2854541 := bbase (se 3 (by rfl) ⟨535226, by rfl⟩ : syracuseStep 2854541 = 1070453) (by norm_num)
theorem B7612109 : Blo 2255435 7612109 := bstep (se 3 (by rfl) ⟨1427270, by rfl⟩ : syracuseStep 7612109 = 2854541) B2854541
theorem B5074739 : Blo 2255435 5074739 := bstep (se 1 (by rfl) ⟨3806054, by rfl⟩ : syracuseStep 5074739 = 7612109) B7612109
theorem B3383159 : Blo 2255435 3383159 := bstep (se 1 (by rfl) ⟨2537369, by rfl⟩ : syracuseStep 3383159 = 5074739) B5074739
theorem B2255439 : Blo 2255435 2255439 := bstep (se 1 (by rfl) ⟨1691579, by rfl⟩ : syracuseStep 2255439 = 3383159) B3383159
theorem B3383165 : Blo 2255435 3383165 := bbase (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) (by norm_num)
theorem B2255443 : Blo 2255435 2255443 := bstep (se 1 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 2255443 = 3383165) B3383165
theorem B5074757 : Blo 2255435 5074757 := bbase (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) (by norm_num)
theorem B3383171 : Blo 2255435 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B2255447 : Blo 2255435 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B2317417 : Blo 2255435 2317417 := bbase (se 2 (by rfl) ⟨869031, by rfl⟩ : syracuseStep 2317417 = 1738063) (by norm_num)
theorem B12359557 : Blo 2255435 12359557 := bstep (se 4 (by rfl) ⟨1158708, by rfl⟩ : syracuseStep 12359557 = 2317417) B2317417
theorem B65917637 : Blo 2255435 65917637 := bstep (se 4 (by rfl) ⟨6179778, by rfl⟩ : syracuseStep 65917637 = 12359557) B12359557
theorem B43945091 : Blo 2255435 43945091 := bstep (se 1 (by rfl) ⟨32958818, by rfl⟩ : syracuseStep 43945091 = 65917637) B65917637
theorem B29296727 : Blo 2255435 29296727 := bstep (se 1 (by rfl) ⟨21972545, by rfl⟩ : syracuseStep 29296727 = 43945091) B43945091
theorem B19531151 : Blo 2255435 19531151 := bstep (se 1 (by rfl) ⟨14648363, by rfl⟩ : syracuseStep 19531151 = 29296727) B29296727
theorem B13020767 : Blo 2255435 13020767 := bstep (se 1 (by rfl) ⟨9765575, by rfl⟩ : syracuseStep 13020767 = 19531151) B19531151
theorem B8680511 : Blo 2255435 8680511 := bstep (se 1 (by rfl) ⟨6510383, by rfl⟩ : syracuseStep 8680511 = 13020767) B13020767
theorem B5787007 : Blo 2255435 5787007 := bstep (se 1 (by rfl) ⟨4340255, by rfl⟩ : syracuseStep 5787007 = 8680511) B8680511
theorem B30864037 : Blo 2255435 30864037 := bstep (se 4 (by rfl) ⟨2893503, by rfl⟩ : syracuseStep 30864037 = 5787007) B5787007
theorem B41152049 : Blo 2255435 41152049 := bstep (se 2 (by rfl) ⟨15432018, by rfl⟩ : syracuseStep 41152049 = 30864037) B30864037
theorem B27434699 : Blo 2255435 27434699 := bstep (se 1 (by rfl) ⟨20576024, by rfl⟩ : syracuseStep 27434699 = 41152049) B41152049
theorem B18289799 : Blo 2255435 18289799 := bstep (se 1 (by rfl) ⟨13717349, by rfl⟩ : syracuseStep 18289799 = 27434699) B27434699
theorem B12193199 : Blo 2255435 12193199 := bstep (se 1 (by rfl) ⟨9144899, by rfl⟩ : syracuseStep 12193199 = 18289799) B18289799
theorem B8128799 : Blo 2255435 8128799 := bstep (se 1 (by rfl) ⟨6096599, by rfl⟩ : syracuseStep 8128799 = 12193199) B12193199
theorem B5419199 : Blo 2255435 5419199 := bstep (se 1 (by rfl) ⟨4064399, by rfl⟩ : syracuseStep 5419199 = 8128799) B8128799
theorem B3612799 : Blo 2255435 3612799 := bstep (se 1 (by rfl) ⟨2709599, by rfl⟩ : syracuseStep 3612799 = 5419199) B5419199
theorem B4817065 : Blo 2255435 4817065 := bstep (se 2 (by rfl) ⟨1806399, by rfl⟩ : syracuseStep 4817065 = 3612799) B3612799
theorem B6422753 : Blo 2255435 6422753 := bstep (se 2 (by rfl) ⟨2408532, by rfl⟩ : syracuseStep 6422753 = 4817065) B4817065
theorem B4281835 : Blo 2255435 4281835 := bstep (se 1 (by rfl) ⟨3211376, by rfl⟩ : syracuseStep 4281835 = 6422753) B6422753
theorem B5709113 : Blo 2255435 5709113 := bstep (se 2 (by rfl) ⟨2140917, by rfl⟩ : syracuseStep 5709113 = 4281835) B4281835
theorem B3806075 : Blo 2255435 3806075 := bstep (se 1 (by rfl) ⟨2854556, by rfl⟩ : syracuseStep 3806075 = 5709113) B5709113
theorem B2537383 : Blo 2255435 2537383 := bstep (se 1 (by rfl) ⟨1903037, by rfl⟩ : syracuseStep 2537383 = 3806075) B3806075
theorem B3383177 : Blo 2255435 3383177 := bstep (se 2 (by rfl) ⟨1268691, by rfl⟩ : syracuseStep 3383177 = 2537383) B2537383
theorem B2255451 : Blo 2255435 2255451 := bstep (se 1 (by rfl) ⟨1691588, by rfl⟩ : syracuseStep 2255451 = 3383177) B3383177
theorem B11418245 : Blo 2255435 11418245 := bbase (se 4 (by rfl) ⟨1070460, by rfl⟩ : syracuseStep 11418245 = 2140921) (by norm_num)
theorem B7612163 : Blo 2255435 7612163 := bstep (se 1 (by rfl) ⟨5709122, by rfl⟩ : syracuseStep 7612163 = 11418245) B11418245
theorem B5074775 : Blo 2255435 5074775 := bstep (se 1 (by rfl) ⟨3806081, by rfl⟩ : syracuseStep 5074775 = 7612163) B7612163
theorem B3383183 : Blo 2255435 3383183 := bstep (se 1 (by rfl) ⟨2537387, by rfl⟩ : syracuseStep 3383183 = 5074775) B5074775
theorem B2255455 : Blo 2255435 2255455 := bstep (se 1 (by rfl) ⟨1691591, by rfl⟩ : syracuseStep 2255455 = 3383183) B3383183
theorem B3383189 : Blo 2255435 3383189 := bbase (se 6 (by rfl) ⟨79293, by rfl⟩ : syracuseStep 3383189 = 158587) (by norm_num)
theorem B2255459 : Blo 2255435 2255459 := bstep (se 1 (by rfl) ⟨1691594, by rfl⟩ : syracuseStep 2255459 = 3383189) B3383189
theorem B2408545 : Blo 2255435 2408545 := bbase (se 2 (by rfl) ⟨903204, by rfl⟩ : syracuseStep 2408545 = 1806409) (by norm_num)
theorem B12845573 : Blo 2255435 12845573 := bstep (se 4 (by rfl) ⟨1204272, by rfl⟩ : syracuseStep 12845573 = 2408545) B2408545
theorem B8563715 : Blo 2255435 8563715 := bstep (se 1 (by rfl) ⟨6422786, by rfl⟩ : syracuseStep 8563715 = 12845573) B12845573
theorem B5709143 : Blo 2255435 5709143 := bstep (se 1 (by rfl) ⟨4281857, by rfl⟩ : syracuseStep 5709143 = 8563715) B8563715
theorem B3806095 : Blo 2255435 3806095 := bstep (se 1 (by rfl) ⟨2854571, by rfl⟩ : syracuseStep 3806095 = 5709143) B5709143
theorem B5074793 : Blo 2255435 5074793 := bstep (se 2 (by rfl) ⟨1903047, by rfl⟩ : syracuseStep 5074793 = 3806095) B3806095
theorem B3383195 : Blo 2255435 3383195 := bstep (se 1 (by rfl) ⟨2537396, by rfl⟩ : syracuseStep 3383195 = 5074793) B5074793
theorem B2255463 : Blo 2255435 2255463 := bstep (se 1 (by rfl) ⟨1691597, by rfl⟩ : syracuseStep 2255463 = 3383195) B3383195
theorem B2537401 : Blo 2255435 2537401 := bbase (se 2 (by rfl) ⟨951525, by rfl⟩ : syracuseStep 2537401 = 1903051) (by norm_num)
theorem B3383201 : Blo 2255435 3383201 := bstep (se 2 (by rfl) ⟨1268700, by rfl⟩ : syracuseStep 3383201 = 2537401) B2537401
theorem B2255467 : Blo 2255435 2255467 := bstep (se 1 (by rfl) ⟨1691600, by rfl⟩ : syracuseStep 2255467 = 3383201) B3383201
theorem B2286245 : Blo 2255435 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B6096653 : Blo 2255435 6096653 := bstep (se 3 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 6096653 = 2286245) B2286245
theorem B4064435 : Blo 2255435 4064435 := bstep (se 1 (by rfl) ⟨3048326, by rfl⟩ : syracuseStep 4064435 = 6096653) B6096653
theorem B2709623 : Blo 2255435 2709623 := bstep (se 1 (by rfl) ⟨2032217, by rfl⟩ : syracuseStep 2709623 = 4064435) B4064435
theorem B7225661 : Blo 2255435 7225661 := bstep (se 3 (by rfl) ⟨1354811, by rfl⟩ : syracuseStep 7225661 = 2709623) B2709623
theorem B4817107 : Blo 2255435 4817107 := bstep (se 1 (by rfl) ⟨3612830, by rfl⟩ : syracuseStep 4817107 = 7225661) B7225661
theorem B6422809 : Blo 2255435 6422809 := bstep (se 2 (by rfl) ⟨2408553, by rfl⟩ : syracuseStep 6422809 = 4817107) B4817107
theorem B8563745 : Blo 2255435 8563745 := bstep (se 2 (by rfl) ⟨3211404, by rfl⟩ : syracuseStep 8563745 = 6422809) B6422809
theorem B5709163 : Blo 2255435 5709163 := bstep (se 1 (by rfl) ⟨4281872, by rfl⟩ : syracuseStep 5709163 = 8563745) B8563745
theorem B7612217 : Blo 2255435 7612217 := bstep (se 2 (by rfl) ⟨2854581, by rfl⟩ : syracuseStep 7612217 = 5709163) B5709163
theorem B5074811 : Blo 2255435 5074811 := bstep (se 1 (by rfl) ⟨3806108, by rfl⟩ : syracuseStep 5074811 = 7612217) B7612217
theorem B3383207 : Blo 2255435 3383207 := bstep (se 1 (by rfl) ⟨2537405, by rfl⟩ : syracuseStep 3383207 = 5074811) B5074811
theorem B2255471 : Blo 2255435 2255471 := bstep (se 1 (by rfl) ⟨1691603, by rfl⟩ : syracuseStep 2255471 = 3383207) B3383207
theorem B3383213 : Blo 2255435 3383213 := bbase (se 3 (by rfl) ⟨634352, by rfl⟩ : syracuseStep 3383213 = 1268705) (by norm_num)
theorem B2255475 : Blo 2255435 2255475 := bstep (se 1 (by rfl) ⟨1691606, by rfl⟩ : syracuseStep 2255475 = 3383213) B3383213
theorem B5074829 : Blo 2255435 5074829 := bbase (se 3 (by rfl) ⟨951530, by rfl⟩ : syracuseStep 5074829 = 1903061) (by norm_num)
theorem B3383219 : Blo 2255435 3383219 := bstep (se 1 (by rfl) ⟨2537414, by rfl⟩ : syracuseStep 3383219 = 5074829) B5074829
theorem B2255479 : Blo 2255435 2255479 := bstep (se 1 (by rfl) ⟨1691609, by rfl⟩ : syracuseStep 2255479 = 3383219) B3383219
theorem B2854597 : Blo 2255435 2854597 := bbase (se 4 (by rfl) ⟨267618, by rfl⟩ : syracuseStep 2854597 = 535237) (by norm_num)
theorem B3806129 : Blo 2255435 3806129 := bstep (se 2 (by rfl) ⟨1427298, by rfl⟩ : syracuseStep 3806129 = 2854597) B2854597
theorem B2537419 : Blo 2255435 2537419 := bstep (se 1 (by rfl) ⟨1903064, by rfl⟩ : syracuseStep 2537419 = 3806129) B3806129
theorem B3383225 : Blo 2255435 3383225 := bstep (se 2 (by rfl) ⟨1268709, by rfl⟩ : syracuseStep 3383225 = 2537419) B2537419
theorem B2255483 : Blo 2255435 2255483 := bstep (se 1 (by rfl) ⟨1691612, by rfl⟩ : syracuseStep 2255483 = 3383225) B3383225
theorem B2893549 : Blo 2255435 2893549 := bbase (se 3 (by rfl) ⟨542540, by rfl⟩ : syracuseStep 2893549 = 1085081) (by norm_num)
theorem B3858065 : Blo 2255435 3858065 := bstep (se 2 (by rfl) ⟨1446774, by rfl⟩ : syracuseStep 3858065 = 2893549) B2893549
theorem B2572043 : Blo 2255435 2572043 := bstep (se 1 (by rfl) ⟨1929032, by rfl⟩ : syracuseStep 2572043 = 3858065) B3858065
theorem B27435125 : Blo 2255435 27435125 := bstep (se 5 (by rfl) ⟨1286021, by rfl⟩ : syracuseStep 27435125 = 2572043) B2572043
theorem B18290083 : Blo 2255435 18290083 := bstep (se 1 (by rfl) ⟨13717562, by rfl⟩ : syracuseStep 18290083 = 27435125) B27435125
theorem B24386777 : Blo 2255435 24386777 := bstep (se 2 (by rfl) ⟨9145041, by rfl⟩ : syracuseStep 24386777 = 18290083) B18290083
theorem B16257851 : Blo 2255435 16257851 := bstep (se 1 (by rfl) ⟨12193388, by rfl⟩ : syracuseStep 16257851 = 24386777) B24386777
theorem B10838567 : Blo 2255435 10838567 := bstep (se 1 (by rfl) ⟨8128925, by rfl⟩ : syracuseStep 10838567 = 16257851) B16257851
theorem B28902845 : Blo 2255435 28902845 := bstep (se 3 (by rfl) ⟨5419283, by rfl⟩ : syracuseStep 28902845 = 10838567) B10838567
theorem B19268563 : Blo 2255435 19268563 := bstep (se 1 (by rfl) ⟨14451422, by rfl⟩ : syracuseStep 19268563 = 28902845) B28902845
theorem B25691417 : Blo 2255435 25691417 := bstep (se 2 (by rfl) ⟨9634281, by rfl⟩ : syracuseStep 25691417 = 19268563) B19268563
theorem B17127611 : Blo 2255435 17127611 := bstep (se 1 (by rfl) ⟨12845708, by rfl⟩ : syracuseStep 17127611 = 25691417) B25691417
theorem B11418407 : Blo 2255435 11418407 := bstep (se 1 (by rfl) ⟨8563805, by rfl⟩ : syracuseStep 11418407 = 17127611) B17127611
theorem B7612271 : Blo 2255435 7612271 := bstep (se 1 (by rfl) ⟨5709203, by rfl⟩ : syracuseStep 7612271 = 11418407) B11418407
theorem B5074847 : Blo 2255435 5074847 := bstep (se 1 (by rfl) ⟨3806135, by rfl⟩ : syracuseStep 5074847 = 7612271) B7612271
theorem B3383231 : Blo 2255435 3383231 := bstep (se 1 (by rfl) ⟨2537423, by rfl⟩ : syracuseStep 3383231 = 5074847) B5074847
theorem B2255487 : Blo 2255435 2255487 := bstep (se 1 (by rfl) ⟨1691615, by rfl⟩ : syracuseStep 2255487 = 3383231) B3383231
theorem B3383237 : Blo 2255435 3383237 := bbase (se 4 (by rfl) ⟨317178, by rfl⟩ : syracuseStep 3383237 = 634357) (by norm_num)
theorem B2255491 : Blo 2255435 2255491 := bstep (se 1 (by rfl) ⟨1691618, by rfl⟩ : syracuseStep 2255491 = 3383237) B3383237
theorem B3806149 : Blo 2255435 3806149 := bbase (se 4 (by rfl) ⟨356826, by rfl⟩ : syracuseStep 3806149 = 713653) (by norm_num)
theorem B5074865 : Blo 2255435 5074865 := bstep (se 2 (by rfl) ⟨1903074, by rfl⟩ : syracuseStep 5074865 = 3806149) B3806149
theorem B3383243 : Blo 2255435 3383243 := bstep (se 1 (by rfl) ⟨2537432, by rfl⟩ : syracuseStep 3383243 = 5074865) B5074865
theorem B2255495 : Blo 2255435 2255495 := bstep (se 1 (by rfl) ⟨1691621, by rfl⟩ : syracuseStep 2255495 = 3383243) B3383243
theorem B2537437 : Blo 2255435 2537437 := bbase (se 3 (by rfl) ⟨475769, by rfl⟩ : syracuseStep 2537437 = 951539) (by norm_num)
theorem B3383249 : Blo 2255435 3383249 := bstep (se 2 (by rfl) ⟨1268718, by rfl⟩ : syracuseStep 3383249 = 2537437) B2537437
theorem B2255499 : Blo 2255435 2255499 := bstep (se 1 (by rfl) ⟨1691624, by rfl⟩ : syracuseStep 2255499 = 3383249) B3383249
theorem B7612325 : Blo 2255435 7612325 := bbase (se 4 (by rfl) ⟨713655, by rfl⟩ : syracuseStep 7612325 = 1427311) (by norm_num)
theorem B5074883 : Blo 2255435 5074883 := bstep (se 1 (by rfl) ⟨3806162, by rfl⟩ : syracuseStep 5074883 = 7612325) B7612325
theorem B3383255 : Blo 2255435 3383255 := bstep (se 1 (by rfl) ⟨2537441, by rfl⟩ : syracuseStep 3383255 = 5074883) B5074883
theorem B2255503 : Blo 2255435 2255503 := bstep (se 1 (by rfl) ⟨1691627, by rfl⟩ : syracuseStep 2255503 = 3383255) B3383255
theorem B3383261 : Blo 2255435 3383261 := bbase (se 3 (by rfl) ⟨634361, by rfl⟩ : syracuseStep 3383261 = 1268723) (by norm_num)
theorem B2255507 : Blo 2255435 2255507 := bstep (se 1 (by rfl) ⟨1691630, by rfl⟩ : syracuseStep 2255507 = 3383261) B3383261
theorem B5074901 : Blo 2255435 5074901 := bbase (se 7 (by rfl) ⟨59471, by rfl⟩ : syracuseStep 5074901 = 118943) (by norm_num)
theorem B3383267 : Blo 2255435 3383267 := bstep (se 1 (by rfl) ⟨2537450, by rfl⟩ : syracuseStep 3383267 = 5074901) B5074901
theorem B2255511 : Blo 2255435 2255511 := bstep (se 1 (by rfl) ⟨1691633, by rfl⟩ : syracuseStep 2255511 = 3383267) B3383267
theorem B14451605 : Blo 2255435 14451605 := bbase (se 6 (by rfl) ⟨338709, by rfl⟩ : syracuseStep 14451605 = 677419) (by norm_num)
theorem B9634403 : Blo 2255435 9634403 := bstep (se 1 (by rfl) ⟨7225802, by rfl⟩ : syracuseStep 9634403 = 14451605) B14451605
theorem B6422935 : Blo 2255435 6422935 := bstep (se 1 (by rfl) ⟨4817201, by rfl⟩ : syracuseStep 6422935 = 9634403) B9634403
theorem B8563913 : Blo 2255435 8563913 := bstep (se 2 (by rfl) ⟨3211467, by rfl⟩ : syracuseStep 8563913 = 6422935) B6422935
theorem B5709275 : Blo 2255435 5709275 := bstep (se 1 (by rfl) ⟨4281956, by rfl⟩ : syracuseStep 5709275 = 8563913) B8563913
theorem B3806183 : Blo 2255435 3806183 := bstep (se 1 (by rfl) ⟨2854637, by rfl⟩ : syracuseStep 3806183 = 5709275) B5709275
theorem B2537455 : Blo 2255435 2537455 := bstep (se 1 (by rfl) ⟨1903091, by rfl⟩ : syracuseStep 2537455 = 3806183) B3806183
theorem B3383273 : Blo 2255435 3383273 := bstep (se 2 (by rfl) ⟨1268727, by rfl⟩ : syracuseStep 3383273 = 2537455) B2537455
theorem B2255515 : Blo 2255435 2255515 := bstep (se 1 (by rfl) ⟨1691636, by rfl⟩ : syracuseStep 2255515 = 3383273) B3383273
theorem B6510581 : Blo 2255435 6510581 := bbase (se 5 (by rfl) ⟨305183, by rfl⟩ : syracuseStep 6510581 = 610367) (by norm_num)
theorem B4340387 : Blo 2255435 4340387 := bstep (se 1 (by rfl) ⟨3255290, by rfl⟩ : syracuseStep 4340387 = 6510581) B6510581
theorem B2893591 : Blo 2255435 2893591 := bstep (se 1 (by rfl) ⟨2170193, by rfl⟩ : syracuseStep 2893591 = 4340387) B4340387
theorem B3858121 : Blo 2255435 3858121 := bstep (se 2 (by rfl) ⟨1446795, by rfl⟩ : syracuseStep 3858121 = 2893591) B2893591
theorem B5144161 : Blo 2255435 5144161 := bstep (se 2 (by rfl) ⟨1929060, by rfl⟩ : syracuseStep 5144161 = 3858121) B3858121
theorem B6858881 : Blo 2255435 6858881 := bstep (se 2 (by rfl) ⟨2572080, by rfl⟩ : syracuseStep 6858881 = 5144161) B5144161
theorem B4572587 : Blo 2255435 4572587 := bstep (se 1 (by rfl) ⟨3429440, by rfl⟩ : syracuseStep 4572587 = 6858881) B6858881
theorem B3048391 : Blo 2255435 3048391 := bstep (se 1 (by rfl) ⟨2286293, by rfl⟩ : syracuseStep 3048391 = 4572587) B4572587
theorem B4064521 : Blo 2255435 4064521 := bstep (se 2 (by rfl) ⟨1524195, by rfl⟩ : syracuseStep 4064521 = 3048391) B3048391
theorem B5419361 : Blo 2255435 5419361 := bstep (se 2 (by rfl) ⟨2032260, by rfl⟩ : syracuseStep 5419361 = 4064521) B4064521
theorem B3612907 : Blo 2255435 3612907 := bstep (se 1 (by rfl) ⟨2709680, by rfl⟩ : syracuseStep 3612907 = 5419361) B5419361
theorem B19268837 : Blo 2255435 19268837 := bstep (se 4 (by rfl) ⟨1806453, by rfl⟩ : syracuseStep 19268837 = 3612907) B3612907
theorem B12845891 : Blo 2255435 12845891 := bstep (se 1 (by rfl) ⟨9634418, by rfl⟩ : syracuseStep 12845891 = 19268837) B19268837
theorem B8563927 : Blo 2255435 8563927 := bstep (se 1 (by rfl) ⟨6422945, by rfl⟩ : syracuseStep 8563927 = 12845891) B12845891
theorem B11418569 : Blo 2255435 11418569 := bstep (se 2 (by rfl) ⟨4281963, by rfl⟩ : syracuseStep 11418569 = 8563927) B8563927
theorem B7612379 : Blo 2255435 7612379 := bstep (se 1 (by rfl) ⟨5709284, by rfl⟩ : syracuseStep 7612379 = 11418569) B11418569
theorem B5074919 : Blo 2255435 5074919 := bstep (se 1 (by rfl) ⟨3806189, by rfl⟩ : syracuseStep 5074919 = 7612379) B7612379
theorem B3383279 : Blo 2255435 3383279 := bstep (se 1 (by rfl) ⟨2537459, by rfl⟩ : syracuseStep 3383279 = 5074919) B5074919
theorem B2255519 : Blo 2255435 2255519 := bstep (se 1 (by rfl) ⟨1691639, by rfl⟩ : syracuseStep 2255519 = 3383279) B3383279
theorem B3383285 : Blo 2255435 3383285 := bbase (se 5 (by rfl) ⟨158591, by rfl⟩ : syracuseStep 3383285 = 317183) (by norm_num)
theorem B2255523 : Blo 2255435 2255523 := bstep (se 1 (by rfl) ⟨1691642, by rfl⟩ : syracuseStep 2255523 = 3383285) B3383285
theorem B5419381 : Blo 2255435 5419381 := bbase (se 5 (by rfl) ⟨254033, by rfl⟩ : syracuseStep 5419381 = 508067) (by norm_num)
theorem B7225841 : Blo 2255435 7225841 := bstep (se 2 (by rfl) ⟨2709690, by rfl⟩ : syracuseStep 7225841 = 5419381) B5419381
theorem B4817227 : Blo 2255435 4817227 := bstep (se 1 (by rfl) ⟨3612920, by rfl⟩ : syracuseStep 4817227 = 7225841) B7225841
theorem B6422969 : Blo 2255435 6422969 := bstep (se 2 (by rfl) ⟨2408613, by rfl⟩ : syracuseStep 6422969 = 4817227) B4817227
theorem B4281979 : Blo 2255435 4281979 := bstep (se 1 (by rfl) ⟨3211484, by rfl⟩ : syracuseStep 4281979 = 6422969) B6422969
theorem B5709305 : Blo 2255435 5709305 := bstep (se 2 (by rfl) ⟨2140989, by rfl⟩ : syracuseStep 5709305 = 4281979) B4281979
theorem B3806203 : Blo 2255435 3806203 := bstep (se 1 (by rfl) ⟨2854652, by rfl⟩ : syracuseStep 3806203 = 5709305) B5709305
theorem B5074937 : Blo 2255435 5074937 := bstep (se 2 (by rfl) ⟨1903101, by rfl⟩ : syracuseStep 5074937 = 3806203) B3806203
theorem B3383291 : Blo 2255435 3383291 := bstep (se 1 (by rfl) ⟨2537468, by rfl⟩ : syracuseStep 3383291 = 5074937) B5074937
theorem B2255527 : Blo 2255435 2255527 := bstep (se 1 (by rfl) ⟨1691645, by rfl⟩ : syracuseStep 2255527 = 3383291) B3383291
theorem B2537473 : Blo 2255435 2537473 := bbase (se 2 (by rfl) ⟨951552, by rfl⟩ : syracuseStep 2537473 = 1903105) (by norm_num)
theorem B3383297 : Blo 2255435 3383297 := bstep (se 2 (by rfl) ⟨1268736, by rfl⟩ : syracuseStep 3383297 = 2537473) B2537473
theorem B2255531 : Blo 2255435 2255531 := bstep (se 1 (by rfl) ⟨1691648, by rfl⟩ : syracuseStep 2255531 = 3383297) B3383297
theorem B5709325 : Blo 2255435 5709325 := bbase (se 3 (by rfl) ⟨1070498, by rfl⟩ : syracuseStep 5709325 = 2140997) (by norm_num)
theorem B7612433 : Blo 2255435 7612433 := bstep (se 2 (by rfl) ⟨2854662, by rfl⟩ : syracuseStep 7612433 = 5709325) B5709325
theorem B5074955 : Blo 2255435 5074955 := bstep (se 1 (by rfl) ⟨3806216, by rfl⟩ : syracuseStep 5074955 = 7612433) B7612433
theorem B3383303 : Blo 2255435 3383303 := bstep (se 1 (by rfl) ⟨2537477, by rfl⟩ : syracuseStep 3383303 = 5074955) B5074955
theorem B2255535 : Blo 2255435 2255535 := bstep (se 1 (by rfl) ⟨1691651, by rfl⟩ : syracuseStep 2255535 = 3383303) B3383303
theorem B3383309 : Blo 2255435 3383309 := bbase (se 3 (by rfl) ⟨634370, by rfl⟩ : syracuseStep 3383309 = 1268741) (by norm_num)
theorem B2255539 : Blo 2255435 2255539 := bstep (se 1 (by rfl) ⟨1691654, by rfl⟩ : syracuseStep 2255539 = 3383309) B3383309
theorem B5074973 : Blo 2255435 5074973 := bbase (se 3 (by rfl) ⟨951557, by rfl⟩ : syracuseStep 5074973 = 1903115) (by norm_num)
theorem B3383315 : Blo 2255435 3383315 := bstep (se 1 (by rfl) ⟨2537486, by rfl⟩ : syracuseStep 3383315 = 5074973) B5074973
theorem B2255543 : Blo 2255435 2255543 := bstep (se 1 (by rfl) ⟨1691657, by rfl⟩ : syracuseStep 2255543 = 3383315) B3383315
theorem B3806237 : Blo 2255435 3806237 := bbase (se 3 (by rfl) ⟨713669, by rfl⟩ : syracuseStep 3806237 = 1427339) (by norm_num)
theorem B2537491 : Blo 2255435 2537491 := bstep (se 1 (by rfl) ⟨1903118, by rfl⟩ : syracuseStep 2537491 = 3806237) B3806237
theorem B3383321 : Blo 2255435 3383321 := bstep (se 2 (by rfl) ⟨1268745, by rfl⟩ : syracuseStep 3383321 = 2537491) B2537491
theorem B2255547 : Blo 2255435 2255547 := bstep (se 1 (by rfl) ⟨1691660, by rfl⟩ : syracuseStep 2255547 = 3383321) B3383321
theorem B15643253 : Blo 2255435 15643253 := bbase (se 5 (by rfl) ⟨733277, by rfl⟩ : syracuseStep 15643253 = 1466555) (by norm_num)
theorem B10428835 : Blo 2255435 10428835 := bstep (se 1 (by rfl) ⟨7821626, by rfl⟩ : syracuseStep 10428835 = 15643253) B15643253
theorem B13905113 : Blo 2255435 13905113 := bstep (se 2 (by rfl) ⟨5214417, by rfl⟩ : syracuseStep 13905113 = 10428835) B10428835
theorem B37080301 : Blo 2255435 37080301 := bstep (se 3 (by rfl) ⟨6952556, by rfl⟩ : syracuseStep 37080301 = 13905113) B13905113
theorem B49440401 : Blo 2255435 49440401 := bstep (se 2 (by rfl) ⟨18540150, by rfl⟩ : syracuseStep 49440401 = 37080301) B37080301
theorem B32960267 : Blo 2255435 32960267 := bstep (se 1 (by rfl) ⟨24720200, by rfl⟩ : syracuseStep 32960267 = 49440401) B49440401
theorem B21973511 : Blo 2255435 21973511 := bstep (se 1 (by rfl) ⟨16480133, by rfl⟩ : syracuseStep 21973511 = 32960267) B32960267
theorem B14649007 : Blo 2255435 14649007 := bstep (se 1 (by rfl) ⟨10986755, by rfl⟩ : syracuseStep 14649007 = 21973511) B21973511
theorem B19532009 : Blo 2255435 19532009 := bstep (se 2 (by rfl) ⟨7324503, by rfl⟩ : syracuseStep 19532009 = 14649007) B14649007
theorem B13021339 : Blo 2255435 13021339 := bstep (se 1 (by rfl) ⟨9766004, by rfl⟩ : syracuseStep 13021339 = 19532009) B19532009
theorem B17361785 : Blo 2255435 17361785 := bstep (se 2 (by rfl) ⟨6510669, by rfl⟩ : syracuseStep 17361785 = 13021339) B13021339
theorem B11574523 : Blo 2255435 11574523 := bstep (se 1 (by rfl) ⟨8680892, by rfl⟩ : syracuseStep 11574523 = 17361785) B17361785
theorem B15432697 : Blo 2255435 15432697 := bstep (se 2 (by rfl) ⟨5787261, by rfl⟩ : syracuseStep 15432697 = 11574523) B11574523
theorem B20576929 : Blo 2255435 20576929 := bstep (se 2 (by rfl) ⟨7716348, by rfl⟩ : syracuseStep 20576929 = 15432697) B15432697
theorem B27435905 : Blo 2255435 27435905 := bstep (se 2 (by rfl) ⟨10288464, by rfl⟩ : syracuseStep 27435905 = 20576929) B20576929
theorem B18290603 : Blo 2255435 18290603 := bstep (se 1 (by rfl) ⟨13717952, by rfl⟩ : syracuseStep 18290603 = 27435905) B27435905
theorem B12193735 : Blo 2255435 12193735 := bstep (se 1 (by rfl) ⟨9145301, by rfl⟩ : syracuseStep 12193735 = 18290603) B18290603
theorem B16258313 : Blo 2255435 16258313 := bstep (se 2 (by rfl) ⟨6096867, by rfl⟩ : syracuseStep 16258313 = 12193735) B12193735
theorem B10838875 : Blo 2255435 10838875 := bstep (se 1 (by rfl) ⟨8129156, by rfl⟩ : syracuseStep 10838875 = 16258313) B16258313
theorem B14451833 : Blo 2255435 14451833 := bstep (se 2 (by rfl) ⟨5419437, by rfl⟩ : syracuseStep 14451833 = 10838875) B10838875
theorem B9634555 : Blo 2255435 9634555 := bstep (se 1 (by rfl) ⟨7225916, by rfl⟩ : syracuseStep 9634555 = 14451833) B14451833
theorem B12846073 : Blo 2255435 12846073 := bstep (se 2 (by rfl) ⟨4817277, by rfl⟩ : syracuseStep 12846073 = 9634555) B9634555
theorem B17128097 : Blo 2255435 17128097 := bstep (se 2 (by rfl) ⟨6423036, by rfl⟩ : syracuseStep 17128097 = 12846073) B12846073
theorem B11418731 : Blo 2255435 11418731 := bstep (se 1 (by rfl) ⟨8564048, by rfl⟩ : syracuseStep 11418731 = 17128097) B17128097
theorem B7612487 : Blo 2255435 7612487 := bstep (se 1 (by rfl) ⟨5709365, by rfl⟩ : syracuseStep 7612487 = 11418731) B11418731
theorem B5074991 : Blo 2255435 5074991 := bstep (se 1 (by rfl) ⟨3806243, by rfl⟩ : syracuseStep 5074991 = 7612487) B7612487
theorem B3383327 : Blo 2255435 3383327 := bstep (se 1 (by rfl) ⟨2537495, by rfl⟩ : syracuseStep 3383327 = 5074991) B5074991
theorem B2255551 : Blo 2255435 2255551 := bstep (se 1 (by rfl) ⟨1691663, by rfl⟩ : syracuseStep 2255551 = 3383327) B3383327
theorem B3383333 : Blo 2255435 3383333 := bbase (se 4 (by rfl) ⟨317187, by rfl⟩ : syracuseStep 3383333 = 634375) (by norm_num)
theorem B2255555 : Blo 2255435 2255555 := bstep (se 1 (by rfl) ⟨1691666, by rfl⟩ : syracuseStep 2255555 = 3383333) B3383333
theorem B2854693 : Blo 2255435 2854693 := bbase (se 4 (by rfl) ⟨267627, by rfl⟩ : syracuseStep 2854693 = 535255) (by norm_num)
theorem B3806257 : Blo 2255435 3806257 := bstep (se 2 (by rfl) ⟨1427346, by rfl⟩ : syracuseStep 3806257 = 2854693) B2854693
theorem B5075009 : Blo 2255435 5075009 := bstep (se 2 (by rfl) ⟨1903128, by rfl⟩ : syracuseStep 5075009 = 3806257) B3806257
theorem B3383339 : Blo 2255435 3383339 := bstep (se 1 (by rfl) ⟨2537504, by rfl⟩ : syracuseStep 3383339 = 5075009) B5075009
theorem B2255559 : Blo 2255435 2255559 := bstep (se 1 (by rfl) ⟨1691669, by rfl⟩ : syracuseStep 2255559 = 3383339) B3383339
theorem B2537509 : Blo 2255435 2537509 := bbase (se 4 (by rfl) ⟨237891, by rfl⟩ : syracuseStep 2537509 = 475783) (by norm_num)
theorem B3383345 : Blo 2255435 3383345 := bstep (se 2 (by rfl) ⟨1268754, by rfl⟩ : syracuseStep 3383345 = 2537509) B2537509
theorem B2255563 : Blo 2255435 2255563 := bstep (se 1 (by rfl) ⟨1691672, by rfl⟩ : syracuseStep 2255563 = 3383345) B3383345
theorem B5419477 : Blo 2255435 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B7225969 : Blo 2255435 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B9634625 : Blo 2255435 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B6423083 : Blo 2255435 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B4282055 : Blo 2255435 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B2854703 : Blo 2255435 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B7612541 : Blo 2255435 7612541 := bstep (se 3 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 7612541 = 2854703) B2854703
theorem B5075027 : Blo 2255435 5075027 := bstep (se 1 (by rfl) ⟨3806270, by rfl⟩ : syracuseStep 5075027 = 7612541) B7612541
theorem B3383351 : Blo 2255435 3383351 := bstep (se 1 (by rfl) ⟨2537513, by rfl⟩ : syracuseStep 3383351 = 5075027) B5075027
theorem B2255567 : Blo 2255435 2255567 := bstep (se 1 (by rfl) ⟨1691675, by rfl⟩ : syracuseStep 2255567 = 3383351) B3383351
theorem B3383357 : Blo 2255435 3383357 := bbase (se 3 (by rfl) ⟨634379, by rfl⟩ : syracuseStep 3383357 = 1268759) (by norm_num)
theorem B2255571 : Blo 2255435 2255571 := bstep (se 1 (by rfl) ⟨1691678, by rfl⟩ : syracuseStep 2255571 = 3383357) B3383357
theorem B5075045 : Blo 2255435 5075045 := bbase (se 4 (by rfl) ⟨475785, by rfl⟩ : syracuseStep 5075045 = 951571) (by norm_num)
theorem B3383363 : Blo 2255435 3383363 := bstep (se 1 (by rfl) ⟨2537522, by rfl⟩ : syracuseStep 3383363 = 5075045) B5075045
theorem B2255575 : Blo 2255435 2255575 := bstep (se 1 (by rfl) ⟨1691681, by rfl⟩ : syracuseStep 2255575 = 3383363) B3383363
theorem B5709437 : Blo 2255435 5709437 := bbase (se 3 (by rfl) ⟨1070519, by rfl⟩ : syracuseStep 5709437 = 2141039) (by norm_num)
theorem B3806291 : Blo 2255435 3806291 := bstep (se 1 (by rfl) ⟨2854718, by rfl⟩ : syracuseStep 3806291 = 5709437) B5709437
theorem B2537527 : Blo 2255435 2537527 := bstep (se 1 (by rfl) ⟨1903145, by rfl⟩ : syracuseStep 2537527 = 3806291) B3806291
theorem B3383369 : Blo 2255435 3383369 := bstep (se 2 (by rfl) ⟨1268763, by rfl⟩ : syracuseStep 3383369 = 2537527) B2537527
theorem B2255579 : Blo 2255435 2255579 := bstep (se 1 (by rfl) ⟨1691684, by rfl⟩ : syracuseStep 2255579 = 3383369) B3383369
theorem B4282085 : Blo 2255435 4282085 := bbase (se 4 (by rfl) ⟨401445, by rfl⟩ : syracuseStep 4282085 = 802891) (by norm_num)
theorem B11418893 : Blo 2255435 11418893 := bstep (se 3 (by rfl) ⟨2141042, by rfl⟩ : syracuseStep 11418893 = 4282085) B4282085
theorem B7612595 : Blo 2255435 7612595 := bstep (se 1 (by rfl) ⟨5709446, by rfl⟩ : syracuseStep 7612595 = 11418893) B11418893
theorem B5075063 : Blo 2255435 5075063 := bstep (se 1 (by rfl) ⟨3806297, by rfl⟩ : syracuseStep 5075063 = 7612595) B7612595
theorem B3383375 : Blo 2255435 3383375 := bstep (se 1 (by rfl) ⟨2537531, by rfl⟩ : syracuseStep 3383375 = 5075063) B5075063
theorem B2255583 : Blo 2255435 2255583 := bstep (se 1 (by rfl) ⟨1691687, by rfl⟩ : syracuseStep 2255583 = 3383375) B3383375
theorem B3383381 : Blo 2255435 3383381 := bbase (se 8 (by rfl) ⟨19824, by rfl⟩ : syracuseStep 3383381 = 39649) (by norm_num)
theorem B2255587 : Blo 2255435 2255587 := bstep (se 1 (by rfl) ⟨1691690, by rfl⟩ : syracuseStep 2255587 = 3383381) B3383381
theorem B13718197 : Blo 2255435 13718197 := bbase (se 5 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 13718197 = 1286081) (by norm_num)
theorem B18290929 : Blo 2255435 18290929 := bstep (se 2 (by rfl) ⟨6859098, by rfl⟩ : syracuseStep 18290929 = 13718197) B13718197
theorem B24387905 : Blo 2255435 24387905 := bstep (se 2 (by rfl) ⟨9145464, by rfl⟩ : syracuseStep 24387905 = 18290929) B18290929
theorem B16258603 : Blo 2255435 16258603 := bstep (se 1 (by rfl) ⟨12193952, by rfl⟩ : syracuseStep 16258603 = 24387905) B24387905
theorem B21678137 : Blo 2255435 21678137 := bstep (se 2 (by rfl) ⟨8129301, by rfl⟩ : syracuseStep 21678137 = 16258603) B16258603
theorem B14452091 : Blo 2255435 14452091 := bstep (se 1 (by rfl) ⟨10839068, by rfl⟩ : syracuseStep 14452091 = 21678137) B21678137
theorem B9634727 : Blo 2255435 9634727 := bstep (se 1 (by rfl) ⟨7226045, by rfl⟩ : syracuseStep 9634727 = 14452091) B14452091
theorem B6423151 : Blo 2255435 6423151 := bstep (se 1 (by rfl) ⟨4817363, by rfl⟩ : syracuseStep 6423151 = 9634727) B9634727
theorem B8564201 : Blo 2255435 8564201 := bstep (se 2 (by rfl) ⟨3211575, by rfl⟩ : syracuseStep 8564201 = 6423151) B6423151
theorem B5709467 : Blo 2255435 5709467 := bstep (se 1 (by rfl) ⟨4282100, by rfl⟩ : syracuseStep 5709467 = 8564201) B8564201
theorem B3806311 : Blo 2255435 3806311 := bstep (se 1 (by rfl) ⟨2854733, by rfl⟩ : syracuseStep 3806311 = 5709467) B5709467
theorem B5075081 : Blo 2255435 5075081 := bstep (se 2 (by rfl) ⟨1903155, by rfl⟩ : syracuseStep 5075081 = 3806311) B3806311
theorem B3383387 : Blo 2255435 3383387 := bstep (se 1 (by rfl) ⟨2537540, by rfl⟩ : syracuseStep 3383387 = 5075081) B5075081
theorem B2255591 : Blo 2255435 2255591 := bstep (se 1 (by rfl) ⟨1691693, by rfl⟩ : syracuseStep 2255591 = 3383387) B3383387
theorem B2537545 : Blo 2255435 2537545 := bbase (se 2 (by rfl) ⟨951579, by rfl⟩ : syracuseStep 2537545 = 1903159) (by norm_num)
theorem B3383393 : Blo 2255435 3383393 := bstep (se 2 (by rfl) ⟨1268772, by rfl⟩ : syracuseStep 3383393 = 2537545) B2537545
theorem B2255595 : Blo 2255435 2255595 := bstep (se 1 (by rfl) ⟨1691696, by rfl⟩ : syracuseStep 2255595 = 3383393) B3383393
theorem B4572749 : Blo 2255435 4572749 := bbase (se 3 (by rfl) ⟨857390, by rfl⟩ : syracuseStep 4572749 = 1714781) (by norm_num)
theorem B3048499 : Blo 2255435 3048499 := bstep (se 1 (by rfl) ⟨2286374, by rfl⟩ : syracuseStep 3048499 = 4572749) B4572749
theorem B4064665 : Blo 2255435 4064665 := bstep (se 2 (by rfl) ⟨1524249, by rfl⟩ : syracuseStep 4064665 = 3048499) B3048499
theorem B5419553 : Blo 2255435 5419553 := bstep (se 2 (by rfl) ⟨2032332, by rfl⟩ : syracuseStep 5419553 = 4064665) B4064665
theorem B14452141 : Blo 2255435 14452141 := bstep (se 3 (by rfl) ⟨2709776, by rfl⟩ : syracuseStep 14452141 = 5419553) B5419553
theorem B19269521 : Blo 2255435 19269521 := bstep (se 2 (by rfl) ⟨7226070, by rfl⟩ : syracuseStep 19269521 = 14452141) B14452141
theorem B12846347 : Blo 2255435 12846347 := bstep (se 1 (by rfl) ⟨9634760, by rfl⟩ : syracuseStep 12846347 = 19269521) B19269521
theorem B8564231 : Blo 2255435 8564231 := bstep (se 1 (by rfl) ⟨6423173, by rfl⟩ : syracuseStep 8564231 = 12846347) B12846347
theorem B5709487 : Blo 2255435 5709487 := bstep (se 1 (by rfl) ⟨4282115, by rfl⟩ : syracuseStep 5709487 = 8564231) B8564231
theorem B7612649 : Blo 2255435 7612649 := bstep (se 2 (by rfl) ⟨2854743, by rfl⟩ : syracuseStep 7612649 = 5709487) B5709487
theorem B5075099 : Blo 2255435 5075099 := bstep (se 1 (by rfl) ⟨3806324, by rfl⟩ : syracuseStep 5075099 = 7612649) B7612649
theorem B3383399 : Blo 2255435 3383399 := bstep (se 1 (by rfl) ⟨2537549, by rfl⟩ : syracuseStep 3383399 = 5075099) B5075099
theorem B2255599 : Blo 2255435 2255599 := bstep (se 1 (by rfl) ⟨1691699, by rfl⟩ : syracuseStep 2255599 = 3383399) B3383399
theorem B3383405 : Blo 2255435 3383405 := bbase (se 3 (by rfl) ⟨634388, by rfl⟩ : syracuseStep 3383405 = 1268777) (by norm_num)
theorem B2255603 : Blo 2255435 2255603 := bstep (se 1 (by rfl) ⟨1691702, by rfl⟩ : syracuseStep 2255603 = 3383405) B3383405
theorem B5075117 : Blo 2255435 5075117 := bbase (se 3 (by rfl) ⟨951584, by rfl⟩ : syracuseStep 5075117 = 1903169) (by norm_num)
theorem B3383411 : Blo 2255435 3383411 := bstep (se 1 (by rfl) ⟨2537558, by rfl⟩ : syracuseStep 3383411 = 5075117) B5075117
theorem B2255607 : Blo 2255435 2255607 := bstep (se 1 (by rfl) ⟨1691705, by rfl⟩ : syracuseStep 2255607 = 3383411) B3383411
theorem B19532533 : Blo 2255435 19532533 := bbase (se 5 (by rfl) ⟨915587, by rfl⟩ : syracuseStep 19532533 = 1831175) (by norm_num)
theorem B26043377 : Blo 2255435 26043377 := bstep (se 2 (by rfl) ⟨9766266, by rfl⟩ : syracuseStep 26043377 = 19532533) B19532533
theorem B69449005 : Blo 2255435 69449005 := bstep (se 3 (by rfl) ⟨13021688, by rfl⟩ : syracuseStep 69449005 = 26043377) B26043377
theorem B92598673 : Blo 2255435 92598673 := bstep (se 2 (by rfl) ⟨34724502, by rfl⟩ : syracuseStep 92598673 = 69449005) B69449005
theorem B123464897 : Blo 2255435 123464897 := bstep (se 2 (by rfl) ⟨46299336, by rfl⟩ : syracuseStep 123464897 = 92598673) B92598673
theorem B82309931 : Blo 2255435 82309931 := bstep (se 1 (by rfl) ⟨61732448, by rfl⟩ : syracuseStep 82309931 = 123464897) B123464897
theorem B54873287 : Blo 2255435 54873287 := bstep (se 1 (by rfl) ⟨41154965, by rfl⟩ : syracuseStep 54873287 = 82309931) B82309931
theorem B36582191 : Blo 2255435 36582191 := bstep (se 1 (by rfl) ⟨27436643, by rfl⟩ : syracuseStep 36582191 = 54873287) B54873287
theorem B24388127 : Blo 2255435 24388127 := bstep (se 1 (by rfl) ⟨18291095, by rfl⟩ : syracuseStep 24388127 = 36582191) B36582191
theorem B16258751 : Blo 2255435 16258751 := bstep (se 1 (by rfl) ⟨12194063, by rfl⟩ : syracuseStep 16258751 = 24388127) B24388127
theorem B10839167 : Blo 2255435 10839167 := bstep (se 1 (by rfl) ⟨8129375, by rfl⟩ : syracuseStep 10839167 = 16258751) B16258751
theorem B7226111 : Blo 2255435 7226111 := bstep (se 1 (by rfl) ⟨5419583, by rfl⟩ : syracuseStep 7226111 = 10839167) B10839167
theorem B4817407 : Blo 2255435 4817407 := bstep (se 1 (by rfl) ⟨3613055, by rfl⟩ : syracuseStep 4817407 = 7226111) B7226111
theorem B6423209 : Blo 2255435 6423209 := bstep (se 2 (by rfl) ⟨2408703, by rfl⟩ : syracuseStep 6423209 = 4817407) B4817407
theorem B4282139 : Blo 2255435 4282139 := bstep (se 1 (by rfl) ⟨3211604, by rfl⟩ : syracuseStep 4282139 = 6423209) B6423209
theorem B2854759 : Blo 2255435 2854759 := bstep (se 1 (by rfl) ⟨2141069, by rfl⟩ : syracuseStep 2854759 = 4282139) B4282139
theorem B3806345 : Blo 2255435 3806345 := bstep (se 2 (by rfl) ⟨1427379, by rfl⟩ : syracuseStep 3806345 = 2854759) B2854759
theorem B2537563 : Blo 2255435 2537563 := bstep (se 1 (by rfl) ⟨1903172, by rfl⟩ : syracuseStep 2537563 = 3806345) B3806345
theorem B3383417 : Blo 2255435 3383417 := bstep (se 2 (by rfl) ⟨1268781, by rfl⟩ : syracuseStep 3383417 = 2537563) B2537563
theorem B2255611 : Blo 2255435 2255611 := bstep (se 1 (by rfl) ⟨1691708, by rfl⟩ : syracuseStep 2255611 = 3383417) B3383417
theorem B10288757 : Blo 2255435 10288757 := bbase (se 5 (by rfl) ⟨482285, by rfl⟩ : syracuseStep 10288757 = 964571) (by norm_num)
theorem B6859171 : Blo 2255435 6859171 := bstep (se 1 (by rfl) ⟨5144378, by rfl⟩ : syracuseStep 6859171 = 10288757) B10288757
theorem B9145561 : Blo 2255435 9145561 := bstep (se 2 (by rfl) ⟨3429585, by rfl⟩ : syracuseStep 9145561 = 6859171) B6859171
theorem B12194081 : Blo 2255435 12194081 := bstep (se 2 (by rfl) ⟨4572780, by rfl⟩ : syracuseStep 12194081 = 9145561) B9145561
theorem B8129387 : Blo 2255435 8129387 := bstep (se 1 (by rfl) ⟨6097040, by rfl⟩ : syracuseStep 8129387 = 12194081) B12194081
theorem B5419591 : Blo 2255435 5419591 := bstep (se 1 (by rfl) ⟨4064693, by rfl⟩ : syracuseStep 5419591 = 8129387) B8129387
theorem B28904485 : Blo 2255435 28904485 := bstep (se 4 (by rfl) ⟨2709795, by rfl⟩ : syracuseStep 28904485 = 5419591) B5419591
theorem B38539313 : Blo 2255435 38539313 := bstep (se 2 (by rfl) ⟨14452242, by rfl⟩ : syracuseStep 38539313 = 28904485) B28904485
theorem B25692875 : Blo 2255435 25692875 := bstep (se 1 (by rfl) ⟨19269656, by rfl⟩ : syracuseStep 25692875 = 38539313) B38539313
theorem B17128583 : Blo 2255435 17128583 := bstep (se 1 (by rfl) ⟨12846437, by rfl⟩ : syracuseStep 17128583 = 25692875) B25692875
theorem B11419055 : Blo 2255435 11419055 := bstep (se 1 (by rfl) ⟨8564291, by rfl⟩ : syracuseStep 11419055 = 17128583) B17128583
theorem B7612703 : Blo 2255435 7612703 := bstep (se 1 (by rfl) ⟨5709527, by rfl⟩ : syracuseStep 7612703 = 11419055) B11419055
theorem B5075135 : Blo 2255435 5075135 := bstep (se 1 (by rfl) ⟨3806351, by rfl⟩ : syracuseStep 5075135 = 7612703) B7612703
theorem B3383423 : Blo 2255435 3383423 := bstep (se 1 (by rfl) ⟨2537567, by rfl⟩ : syracuseStep 3383423 = 5075135) B5075135
theorem B2255615 : Blo 2255435 2255615 := bstep (se 1 (by rfl) ⟨1691711, by rfl⟩ : syracuseStep 2255615 = 3383423) B3383423
theorem B3383429 : Blo 2255435 3383429 := bbase (se 4 (by rfl) ⟨317196, by rfl⟩ : syracuseStep 3383429 = 634393) (by norm_num)
theorem B2255619 : Blo 2255435 2255619 := bstep (se 1 (by rfl) ⟨1691714, by rfl⟩ : syracuseStep 2255619 = 3383429) B3383429
theorem B3806365 : Blo 2255435 3806365 := bbase (se 3 (by rfl) ⟨713693, by rfl⟩ : syracuseStep 3806365 = 1427387) (by norm_num)
theorem B5075153 : Blo 2255435 5075153 := bstep (se 2 (by rfl) ⟨1903182, by rfl⟩ : syracuseStep 5075153 = 3806365) B3806365
theorem B3383435 : Blo 2255435 3383435 := bstep (se 1 (by rfl) ⟨2537576, by rfl⟩ : syracuseStep 3383435 = 5075153) B5075153
theorem B2255623 : Blo 2255435 2255623 := bstep (se 1 (by rfl) ⟨1691717, by rfl⟩ : syracuseStep 2255623 = 3383435) B3383435
theorem B2537581 : Blo 2255435 2537581 := bbase (se 3 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 2537581 = 951593) (by norm_num)
theorem B3383441 : Blo 2255435 3383441 := bstep (se 2 (by rfl) ⟨1268790, by rfl⟩ : syracuseStep 3383441 = 2537581) B2537581
theorem B2255627 : Blo 2255435 2255627 := bstep (se 1 (by rfl) ⟨1691720, by rfl⟩ : syracuseStep 2255627 = 3383441) B3383441
theorem B7612757 : Blo 2255435 7612757 := bbase (se 10 (by rfl) ⟨11151, by rfl⟩ : syracuseStep 7612757 = 22303) (by norm_num)
theorem B5075171 : Blo 2255435 5075171 := bstep (se 1 (by rfl) ⟨3806378, by rfl⟩ : syracuseStep 5075171 = 7612757) B7612757
theorem B3383447 : Blo 2255435 3383447 := bstep (se 1 (by rfl) ⟨2537585, by rfl⟩ : syracuseStep 3383447 = 5075171) B5075171
theorem B2255631 : Blo 2255435 2255631 := bstep (se 1 (by rfl) ⟨1691723, by rfl⟩ : syracuseStep 2255631 = 3383447) B3383447
theorem B3383453 : Blo 2255435 3383453 := bbase (se 3 (by rfl) ⟨634397, by rfl⟩ : syracuseStep 3383453 = 1268795) (by norm_num)
theorem B2255635 : Blo 2255435 2255635 := bstep (se 1 (by rfl) ⟨1691726, by rfl⟩ : syracuseStep 2255635 = 3383453) B3383453
theorem B5075189 : Blo 2255435 5075189 := bbase (se 5 (by rfl) ⟨237899, by rfl⟩ : syracuseStep 5075189 = 475799) (by norm_num)
theorem B3383459 : Blo 2255435 3383459 := bstep (se 1 (by rfl) ⟨2537594, by rfl⟩ : syracuseStep 3383459 = 5075189) B5075189
theorem B2255639 : Blo 2255435 2255639 := bstep (se 1 (by rfl) ⟨1691729, by rfl⟩ : syracuseStep 2255639 = 3383459) B3383459
theorem B3429629 : Blo 2255435 3429629 := bbase (se 3 (by rfl) ⟨643055, by rfl⟩ : syracuseStep 3429629 = 1286111) (by norm_num)
theorem B2286419 : Blo 2255435 2286419 := bstep (se 1 (by rfl) ⟨1714814, by rfl⟩ : syracuseStep 2286419 = 3429629) B3429629
theorem B6097117 : Blo 2255435 6097117 := bstep (se 3 (by rfl) ⟨1143209, by rfl⟩ : syracuseStep 6097117 = 2286419) B2286419
theorem B8129489 : Blo 2255435 8129489 := bstep (se 2 (by rfl) ⟨3048558, by rfl⟩ : syracuseStep 8129489 = 6097117) B6097117
theorem B21678637 : Blo 2255435 21678637 := bstep (se 3 (by rfl) ⟨4064744, by rfl⟩ : syracuseStep 21678637 = 8129489) B8129489
theorem B28904849 : Blo 2255435 28904849 := bstep (se 2 (by rfl) ⟨10839318, by rfl⟩ : syracuseStep 28904849 = 21678637) B21678637
theorem B19269899 : Blo 2255435 19269899 := bstep (se 1 (by rfl) ⟨14452424, by rfl⟩ : syracuseStep 19269899 = 28904849) B28904849
theorem B12846599 : Blo 2255435 12846599 := bstep (se 1 (by rfl) ⟨9634949, by rfl⟩ : syracuseStep 12846599 = 19269899) B19269899
theorem B8564399 : Blo 2255435 8564399 := bstep (se 1 (by rfl) ⟨6423299, by rfl⟩ : syracuseStep 8564399 = 12846599) B12846599
theorem B5709599 : Blo 2255435 5709599 := bstep (se 1 (by rfl) ⟨4282199, by rfl⟩ : syracuseStep 5709599 = 8564399) B8564399
theorem B3806399 : Blo 2255435 3806399 := bstep (se 1 (by rfl) ⟨2854799, by rfl⟩ : syracuseStep 3806399 = 5709599) B5709599
theorem B2537599 : Blo 2255435 2537599 := bstep (se 1 (by rfl) ⟨1903199, by rfl⟩ : syracuseStep 2537599 = 3806399) B3806399
theorem B3383465 : Blo 2255435 3383465 := bstep (se 2 (by rfl) ⟨1268799, by rfl⟩ : syracuseStep 3383465 = 2537599) B2537599
theorem B2255643 : Blo 2255435 2255643 := bstep (se 1 (by rfl) ⟨1691732, by rfl⟩ : syracuseStep 2255643 = 3383465) B3383465
theorem B5419669 : Blo 2255435 5419669 := bbase (se 6 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 5419669 = 254047) (by norm_num)
theorem B7226225 : Blo 2255435 7226225 := bstep (se 2 (by rfl) ⟨2709834, by rfl⟩ : syracuseStep 7226225 = 5419669) B5419669
theorem B4817483 : Blo 2255435 4817483 := bstep (se 1 (by rfl) ⟨3613112, by rfl⟩ : syracuseStep 4817483 = 7226225) B7226225
theorem B3211655 : Blo 2255435 3211655 := bstep (se 1 (by rfl) ⟨2408741, by rfl⟩ : syracuseStep 3211655 = 4817483) B4817483
theorem B8564413 : Blo 2255435 8564413 := bstep (se 3 (by rfl) ⟨1605827, by rfl⟩ : syracuseStep 8564413 = 3211655) B3211655
theorem B11419217 : Blo 2255435 11419217 := bstep (se 2 (by rfl) ⟨4282206, by rfl⟩ : syracuseStep 11419217 = 8564413) B8564413
theorem B7612811 : Blo 2255435 7612811 := bstep (se 1 (by rfl) ⟨5709608, by rfl⟩ : syracuseStep 7612811 = 11419217) B11419217
theorem B5075207 : Blo 2255435 5075207 := bstep (se 1 (by rfl) ⟨3806405, by rfl⟩ : syracuseStep 5075207 = 7612811) B7612811
theorem B3383471 : Blo 2255435 3383471 := bstep (se 1 (by rfl) ⟨2537603, by rfl⟩ : syracuseStep 3383471 = 5075207) B5075207
theorem B2255647 : Blo 2255435 2255647 := bstep (se 1 (by rfl) ⟨1691735, by rfl⟩ : syracuseStep 2255647 = 3383471) B3383471
theorem B3383477 : Blo 2255435 3383477 := bbase (se 5 (by rfl) ⟨158600, by rfl⟩ : syracuseStep 3383477 = 317201) (by norm_num)
theorem B2255651 : Blo 2255435 2255651 := bstep (se 1 (by rfl) ⟨1691738, by rfl⟩ : syracuseStep 2255651 = 3383477) B3383477
theorem B5709629 : Blo 2255435 5709629 := bbase (se 3 (by rfl) ⟨1070555, by rfl⟩ : syracuseStep 5709629 = 2141111) (by norm_num)
theorem B3806419 : Blo 2255435 3806419 := bstep (se 1 (by rfl) ⟨2854814, by rfl⟩ : syracuseStep 3806419 = 5709629) B5709629
theorem B5075225 : Blo 2255435 5075225 := bstep (se 2 (by rfl) ⟨1903209, by rfl⟩ : syracuseStep 5075225 = 3806419) B3806419
theorem B3383483 : Blo 2255435 3383483 := bstep (se 1 (by rfl) ⟨2537612, by rfl⟩ : syracuseStep 3383483 = 5075225) B5075225
theorem B2255655 : Blo 2255435 2255655 := bstep (se 1 (by rfl) ⟨1691741, by rfl⟩ : syracuseStep 2255655 = 3383483) B3383483
theorem B2537617 : Blo 2255435 2537617 := bbase (se 2 (by rfl) ⟨951606, by rfl⟩ : syracuseStep 2537617 = 1903213) (by norm_num)
theorem B3383489 : Blo 2255435 3383489 := bstep (se 2 (by rfl) ⟨1268808, by rfl⟩ : syracuseStep 3383489 = 2537617) B2537617
theorem B2255659 : Blo 2255435 2255659 := bstep (se 1 (by rfl) ⟨1691744, by rfl⟩ : syracuseStep 2255659 = 3383489) B3383489
theorem B4282237 : Blo 2255435 4282237 := bbase (se 3 (by rfl) ⟨802919, by rfl⟩ : syracuseStep 4282237 = 1605839) (by norm_num)
theorem B5709649 : Blo 2255435 5709649 := bstep (se 2 (by rfl) ⟨2141118, by rfl⟩ : syracuseStep 5709649 = 4282237) B4282237
theorem B7612865 : Blo 2255435 7612865 := bstep (se 2 (by rfl) ⟨2854824, by rfl⟩ : syracuseStep 7612865 = 5709649) B5709649
theorem B5075243 : Blo 2255435 5075243 := bstep (se 1 (by rfl) ⟨3806432, by rfl⟩ : syracuseStep 5075243 = 7612865) B7612865
theorem B3383495 : Blo 2255435 3383495 := bstep (se 1 (by rfl) ⟨2537621, by rfl⟩ : syracuseStep 3383495 = 5075243) B5075243
theorem B2255663 : Blo 2255435 2255663 := bstep (se 1 (by rfl) ⟨1691747, by rfl⟩ : syracuseStep 2255663 = 3383495) B3383495
theorem B3383501 : Blo 2255435 3383501 := bbase (se 3 (by rfl) ⟨634406, by rfl⟩ : syracuseStep 3383501 = 1268813) (by norm_num)
theorem B2255667 : Blo 2255435 2255667 := bstep (se 1 (by rfl) ⟨1691750, by rfl⟩ : syracuseStep 2255667 = 3383501) B3383501
theorem B5075261 : Blo 2255435 5075261 := bbase (se 3 (by rfl) ⟨951611, by rfl⟩ : syracuseStep 5075261 = 1903223) (by norm_num)
theorem B3383507 : Blo 2255435 3383507 := bstep (se 1 (by rfl) ⟨2537630, by rfl⟩ : syracuseStep 3383507 = 5075261) B5075261
theorem B2255671 : Blo 2255435 2255671 := bstep (se 1 (by rfl) ⟨1691753, by rfl⟩ : syracuseStep 2255671 = 3383507) B3383507
theorem B3806453 : Blo 2255435 3806453 := bbase (se 5 (by rfl) ⟨178427, by rfl⟩ : syracuseStep 3806453 = 356855) (by norm_num)
theorem B2537635 : Blo 2255435 2537635 := bstep (se 1 (by rfl) ⟨1903226, by rfl⟩ : syracuseStep 2537635 = 3806453) B3806453
theorem B3383513 : Blo 2255435 3383513 := bstep (se 2 (by rfl) ⟨1268817, by rfl⟩ : syracuseStep 3383513 = 2537635) B2537635
theorem B2255675 : Blo 2255435 2255675 := bstep (se 1 (by rfl) ⟨1691756, by rfl⟩ : syracuseStep 2255675 = 3383513) B3383513
theorem B3476477 : Blo 2255435 3476477 := bbase (se 3 (by rfl) ⟨651839, by rfl⟩ : syracuseStep 3476477 = 1303679) (by norm_num)
theorem B9270605 : Blo 2255435 9270605 := bstep (se 3 (by rfl) ⟨1738238, by rfl⟩ : syracuseStep 9270605 = 3476477) B3476477
theorem B6180403 : Blo 2255435 6180403 := bstep (se 1 (by rfl) ⟨4635302, by rfl⟩ : syracuseStep 6180403 = 9270605) B9270605
theorem B8240537 : Blo 2255435 8240537 := bstep (se 2 (by rfl) ⟨3090201, by rfl⟩ : syracuseStep 8240537 = 6180403) B6180403
theorem B5493691 : Blo 2255435 5493691 := bstep (se 1 (by rfl) ⟨4120268, by rfl⟩ : syracuseStep 5493691 = 8240537) B8240537
theorem B7324921 : Blo 2255435 7324921 := bstep (se 2 (by rfl) ⟨2746845, by rfl⟩ : syracuseStep 7324921 = 5493691) B5493691
theorem B39066245 : Blo 2255435 39066245 := bstep (se 4 (by rfl) ⟨3662460, by rfl⟩ : syracuseStep 39066245 = 7324921) B7324921
theorem B26044163 : Blo 2255435 26044163 := bstep (se 1 (by rfl) ⟨19533122, by rfl⟩ : syracuseStep 26044163 = 39066245) B39066245
theorem B17362775 : Blo 2255435 17362775 := bstep (se 1 (by rfl) ⟨13022081, by rfl⟩ : syracuseStep 17362775 = 26044163) B26044163
theorem B11575183 : Blo 2255435 11575183 := bstep (se 1 (by rfl) ⟨8681387, by rfl⟩ : syracuseStep 11575183 = 17362775) B17362775
theorem B15433577 : Blo 2255435 15433577 := bstep (se 2 (by rfl) ⟨5787591, by rfl⟩ : syracuseStep 15433577 = 11575183) B11575183
theorem B10289051 : Blo 2255435 10289051 := bstep (se 1 (by rfl) ⟨7716788, by rfl⟩ : syracuseStep 10289051 = 15433577) B15433577
theorem B6859367 : Blo 2255435 6859367 := bstep (se 1 (by rfl) ⟨5144525, by rfl⟩ : syracuseStep 6859367 = 10289051) B10289051
theorem B4572911 : Blo 2255435 4572911 := bstep (se 1 (by rfl) ⟨3429683, by rfl⟩ : syracuseStep 4572911 = 6859367) B6859367
theorem B3048607 : Blo 2255435 3048607 := bstep (se 1 (by rfl) ⟨2286455, by rfl⟩ : syracuseStep 3048607 = 4572911) B4572911
theorem B16259237 : Blo 2255435 16259237 := bstep (se 4 (by rfl) ⟨1524303, by rfl⟩ : syracuseStep 16259237 = 3048607) B3048607
theorem B10839491 : Blo 2255435 10839491 := bstep (se 1 (by rfl) ⟨8129618, by rfl⟩ : syracuseStep 10839491 = 16259237) B16259237
theorem B7226327 : Blo 2255435 7226327 := bstep (se 1 (by rfl) ⟨5419745, by rfl⟩ : syracuseStep 7226327 = 10839491) B10839491
theorem B4817551 : Blo 2255435 4817551 := bstep (se 1 (by rfl) ⟨3613163, by rfl⟩ : syracuseStep 4817551 = 7226327) B7226327
theorem B6423401 : Blo 2255435 6423401 := bstep (se 2 (by rfl) ⟨2408775, by rfl⟩ : syracuseStep 6423401 = 4817551) B4817551
theorem B17129069 : Blo 2255435 17129069 := bstep (se 3 (by rfl) ⟨3211700, by rfl⟩ : syracuseStep 17129069 = 6423401) B6423401
theorem B11419379 : Blo 2255435 11419379 := bstep (se 1 (by rfl) ⟨8564534, by rfl⟩ : syracuseStep 11419379 = 17129069) B17129069
theorem B7612919 : Blo 2255435 7612919 := bstep (se 1 (by rfl) ⟨5709689, by rfl⟩ : syracuseStep 7612919 = 11419379) B11419379
theorem B5075279 : Blo 2255435 5075279 := bstep (se 1 (by rfl) ⟨3806459, by rfl⟩ : syracuseStep 5075279 = 7612919) B7612919
theorem B3383519 : Blo 2255435 3383519 := bstep (se 1 (by rfl) ⟨2537639, by rfl⟩ : syracuseStep 3383519 = 5075279) B5075279
theorem B2255679 : Blo 2255435 2255679 := bstep (se 1 (by rfl) ⟨1691759, by rfl⟩ : syracuseStep 2255679 = 3383519) B3383519
theorem B3383525 : Blo 2255435 3383525 := bbase (se 4 (by rfl) ⟨317205, by rfl⟩ : syracuseStep 3383525 = 634411) (by norm_num)
theorem B2255683 : Blo 2255435 2255683 := bstep (se 1 (by rfl) ⟨1691762, by rfl⟩ : syracuseStep 2255683 = 3383525) B3383525
theorem B2572273 : Blo 2255435 2572273 := bbase (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) (by norm_num)
theorem B3429697 : Blo 2255435 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B4572929 : Blo 2255435 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B3048619 : Blo 2255435 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B4064825 : Blo 2255435 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B2709883 : Blo 2255435 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B3613177 : Blo 2255435 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B4817569 : Blo 2255435 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B6423425 : Blo 2255435 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B4282283 : Blo 2255435 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B2854855 : Blo 2255435 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B3806473 : Blo 2255435 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B5075297 : Blo 2255435 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B3383531 : Blo 2255435 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B2255687 : Blo 2255435 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B2537653 : Blo 2255435 2537653 := bbase (se 5 (by rfl) ⟨118952, by rfl⟩ : syracuseStep 2537653 = 237905) (by norm_num)
theorem B3383537 : Blo 2255435 3383537 := bstep (se 2 (by rfl) ⟨1268826, by rfl⟩ : syracuseStep 3383537 = 2537653) B2537653
theorem B2255691 : Blo 2255435 2255691 := bstep (se 1 (by rfl) ⟨1691768, by rfl⟩ : syracuseStep 2255691 = 3383537) B3383537
theorem B2854865 : Blo 2255435 2854865 := bbase (se 2 (by rfl) ⟨1070574, by rfl⟩ : syracuseStep 2854865 = 2141149) (by norm_num)
theorem B7612973 : Blo 2255435 7612973 := bstep (se 3 (by rfl) ⟨1427432, by rfl⟩ : syracuseStep 7612973 = 2854865) B2854865
theorem B5075315 : Blo 2255435 5075315 := bstep (se 1 (by rfl) ⟨3806486, by rfl⟩ : syracuseStep 5075315 = 7612973) B7612973
theorem B3383543 : Blo 2255435 3383543 := bstep (se 1 (by rfl) ⟨2537657, by rfl⟩ : syracuseStep 3383543 = 5075315) B5075315
theorem B2255695 : Blo 2255435 2255695 := bstep (se 1 (by rfl) ⟨1691771, by rfl⟩ : syracuseStep 2255695 = 3383543) B3383543
theorem B3383549 : Blo 2255435 3383549 := bbase (se 3 (by rfl) ⟨634415, by rfl⟩ : syracuseStep 3383549 = 1268831) (by norm_num)
theorem B2255699 : Blo 2255435 2255699 := bstep (se 1 (by rfl) ⟨1691774, by rfl⟩ : syracuseStep 2255699 = 3383549) B3383549
theorem B5075333 : Blo 2255435 5075333 := bbase (se 4 (by rfl) ⟨475812, by rfl⟩ : syracuseStep 5075333 = 951625) (by norm_num)
theorem B3383555 : Blo 2255435 3383555 := bstep (se 1 (by rfl) ⟨2537666, by rfl⟩ : syracuseStep 3383555 = 5075333) B5075333
theorem B2255703 : Blo 2255435 2255703 := bstep (se 1 (by rfl) ⟨1691777, by rfl⟩ : syracuseStep 2255703 = 3383555) B3383555
theorem B3211741 : Blo 2255435 3211741 := bbase (se 3 (by rfl) ⟨602201, by rfl⟩ : syracuseStep 3211741 = 1204403) (by norm_num)
theorem B4282321 : Blo 2255435 4282321 := bstep (se 2 (by rfl) ⟨1605870, by rfl⟩ : syracuseStep 4282321 = 3211741) B3211741
theorem B5709761 : Blo 2255435 5709761 := bstep (se 2 (by rfl) ⟨2141160, by rfl⟩ : syracuseStep 5709761 = 4282321) B4282321
theorem B3806507 : Blo 2255435 3806507 := bstep (se 1 (by rfl) ⟨2854880, by rfl⟩ : syracuseStep 3806507 = 5709761) B5709761
theorem B2537671 : Blo 2255435 2537671 := bstep (se 1 (by rfl) ⟨1903253, by rfl⟩ : syracuseStep 2537671 = 3806507) B3806507
theorem B3383561 : Blo 2255435 3383561 := bstep (se 2 (by rfl) ⟨1268835, by rfl⟩ : syracuseStep 3383561 = 2537671) B2537671
theorem B2255707 : Blo 2255435 2255707 := bstep (se 1 (by rfl) ⟨1691780, by rfl⟩ : syracuseStep 2255707 = 3383561) B3383561
theorem B11419541 : Blo 2255435 11419541 := bbase (se 6 (by rfl) ⟨267645, by rfl⟩ : syracuseStep 11419541 = 535291) (by norm_num)
theorem B7613027 : Blo 2255435 7613027 := bstep (se 1 (by rfl) ⟨5709770, by rfl⟩ : syracuseStep 7613027 = 11419541) B11419541
theorem B5075351 : Blo 2255435 5075351 := bstep (se 1 (by rfl) ⟨3806513, by rfl⟩ : syracuseStep 5075351 = 7613027) B7613027
theorem B3383567 : Blo 2255435 3383567 := bstep (se 1 (by rfl) ⟨2537675, by rfl⟩ : syracuseStep 3383567 = 5075351) B5075351
theorem B2255711 : Blo 2255435 2255711 := bstep (se 1 (by rfl) ⟨1691783, by rfl⟩ : syracuseStep 2255711 = 3383567) B3383567
theorem B3383573 : Blo 2255435 3383573 := bbase (se 6 (by rfl) ⟨79302, by rfl⟩ : syracuseStep 3383573 = 158605) (by norm_num)
theorem B2255715 : Blo 2255435 2255715 := bstep (se 1 (by rfl) ⟨1691786, by rfl⟩ : syracuseStep 2255715 = 3383573) B3383573
theorem B3048661 : Blo 2255435 3048661 := bbase (se 7 (by rfl) ⟨35726, by rfl⟩ : syracuseStep 3048661 = 71453) (by norm_num)
theorem B16259525 : Blo 2255435 16259525 := bstep (se 4 (by rfl) ⟨1524330, by rfl⟩ : syracuseStep 16259525 = 3048661) B3048661
theorem B10839683 : Blo 2255435 10839683 := bstep (se 1 (by rfl) ⟨8129762, by rfl⟩ : syracuseStep 10839683 = 16259525) B16259525
theorem B28905821 : Blo 2255435 28905821 := bstep (se 3 (by rfl) ⟨5419841, by rfl⟩ : syracuseStep 28905821 = 10839683) B10839683
theorem B19270547 : Blo 2255435 19270547 := bstep (se 1 (by rfl) ⟨14452910, by rfl⟩ : syracuseStep 19270547 = 28905821) B28905821
theorem B12847031 : Blo 2255435 12847031 := bstep (se 1 (by rfl) ⟨9635273, by rfl⟩ : syracuseStep 12847031 = 19270547) B19270547
theorem B8564687 : Blo 2255435 8564687 := bstep (se 1 (by rfl) ⟨6423515, by rfl⟩ : syracuseStep 8564687 = 12847031) B12847031
theorem B5709791 : Blo 2255435 5709791 := bstep (se 1 (by rfl) ⟨4282343, by rfl⟩ : syracuseStep 5709791 = 8564687) B8564687
theorem B3806527 : Blo 2255435 3806527 := bstep (se 1 (by rfl) ⟨2854895, by rfl⟩ : syracuseStep 3806527 = 5709791) B5709791
theorem B5075369 : Blo 2255435 5075369 := bstep (se 2 (by rfl) ⟨1903263, by rfl⟩ : syracuseStep 5075369 = 3806527) B3806527
theorem B3383579 : Blo 2255435 3383579 := bstep (se 1 (by rfl) ⟨2537684, by rfl⟩ : syracuseStep 3383579 = 5075369) B5075369
theorem B2255719 : Blo 2255435 2255719 := bstep (se 1 (by rfl) ⟨1691789, by rfl⟩ : syracuseStep 2255719 = 3383579) B3383579
theorem B2537689 : Blo 2255435 2537689 := bbase (se 2 (by rfl) ⟨951633, by rfl⟩ : syracuseStep 2537689 = 1903267) (by norm_num)
theorem B3383585 : Blo 2255435 3383585 := bstep (se 2 (by rfl) ⟨1268844, by rfl⟩ : syracuseStep 3383585 = 2537689) B2537689
theorem B2255723 : Blo 2255435 2255723 := bstep (se 1 (by rfl) ⟨1691792, by rfl⟩ : syracuseStep 2255723 = 3383585) B3383585
theorem B2286505 : Blo 2255435 2286505 := bbase (se 2 (by rfl) ⟨857439, by rfl⟩ : syracuseStep 2286505 = 1714879) (by norm_num)
theorem B3048673 : Blo 2255435 3048673 := bstep (se 2 (by rfl) ⟨1143252, by rfl⟩ : syracuseStep 3048673 = 2286505) B2286505
theorem B4064897 : Blo 2255435 4064897 := bstep (se 2 (by rfl) ⟨1524336, by rfl⟩ : syracuseStep 4064897 = 3048673) B3048673
theorem B2709931 : Blo 2255435 2709931 := bstep (se 1 (by rfl) ⟨2032448, by rfl⟩ : syracuseStep 2709931 = 4064897) B4064897
theorem B3613241 : Blo 2255435 3613241 := bstep (se 2 (by rfl) ⟨1354965, by rfl⟩ : syracuseStep 3613241 = 2709931) B2709931
theorem B2408827 : Blo 2255435 2408827 := bstep (se 1 (by rfl) ⟨1806620, by rfl⟩ : syracuseStep 2408827 = 3613241) B3613241
theorem B3211769 : Blo 2255435 3211769 := bstep (se 2 (by rfl) ⟨1204413, by rfl⟩ : syracuseStep 3211769 = 2408827) B2408827
theorem B8564717 : Blo 2255435 8564717 := bstep (se 3 (by rfl) ⟨1605884, by rfl⟩ : syracuseStep 8564717 = 3211769) B3211769
theorem B5709811 : Blo 2255435 5709811 := bstep (se 1 (by rfl) ⟨4282358, by rfl⟩ : syracuseStep 5709811 = 8564717) B8564717
theorem B7613081 : Blo 2255435 7613081 := bstep (se 2 (by rfl) ⟨2854905, by rfl⟩ : syracuseStep 7613081 = 5709811) B5709811
theorem B5075387 : Blo 2255435 5075387 := bstep (se 1 (by rfl) ⟨3806540, by rfl⟩ : syracuseStep 5075387 = 7613081) B7613081
theorem B3383591 : Blo 2255435 3383591 := bstep (se 1 (by rfl) ⟨2537693, by rfl⟩ : syracuseStep 3383591 = 5075387) B5075387
theorem B2255727 : Blo 2255435 2255727 := bstep (se 1 (by rfl) ⟨1691795, by rfl⟩ : syracuseStep 2255727 = 3383591) B3383591
theorem B3383597 : Blo 2255435 3383597 := bbase (se 3 (by rfl) ⟨634424, by rfl⟩ : syracuseStep 3383597 = 1268849) (by norm_num)
theorem B2255731 : Blo 2255435 2255731 := bstep (se 1 (by rfl) ⟨1691798, by rfl⟩ : syracuseStep 2255731 = 3383597) B3383597
theorem B5075405 : Blo 2255435 5075405 := bbase (se 3 (by rfl) ⟨951638, by rfl⟩ : syracuseStep 5075405 = 1903277) (by norm_num)
theorem B3383603 : Blo 2255435 3383603 := bstep (se 1 (by rfl) ⟨2537702, by rfl⟩ : syracuseStep 3383603 = 5075405) B5075405
theorem B2255735 : Blo 2255435 2255735 := bstep (se 1 (by rfl) ⟨1691801, by rfl⟩ : syracuseStep 2255735 = 3383603) B3383603
theorem B2854921 : Blo 2255435 2854921 := bbase (se 2 (by rfl) ⟨1070595, by rfl⟩ : syracuseStep 2854921 = 2141191) (by norm_num)
theorem B3806561 : Blo 2255435 3806561 := bstep (se 2 (by rfl) ⟨1427460, by rfl⟩ : syracuseStep 3806561 = 2854921) B2854921
theorem B2537707 : Blo 2255435 2537707 := bstep (se 1 (by rfl) ⟨1903280, by rfl⟩ : syracuseStep 2537707 = 3806561) B3806561
theorem B3383609 : Blo 2255435 3383609 := bstep (se 2 (by rfl) ⟨1268853, by rfl⟩ : syracuseStep 3383609 = 2537707) B2537707
theorem B2255739 : Blo 2255435 2255739 := bstep (se 1 (by rfl) ⟨1691804, by rfl⟩ : syracuseStep 2255739 = 3383609) B3383609
theorem B25801877 : Blo 2255435 25801877 := bbase (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) (by norm_num)
theorem B17201251 : Blo 2255435 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B22935001 : Blo 2255435 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B30580001 : Blo 2255435 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B20386667 : Blo 2255435 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B54364445 : Blo 2255435 54364445 := bstep (se 3 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 54364445 = 20386667) B20386667
theorem B36242963 : Blo 2255435 36242963 := bstep (se 1 (by rfl) ⟨27182222, by rfl⟩ : syracuseStep 36242963 = 54364445) B54364445
theorem B24161975 : Blo 2255435 24161975 := bstep (se 1 (by rfl) ⟨18121481, by rfl⟩ : syracuseStep 24161975 = 36242963) B36242963
theorem B16107983 : Blo 2255435 16107983 := bstep (se 1 (by rfl) ⟨12080987, by rfl⟩ : syracuseStep 16107983 = 24161975) B24161975
theorem B10738655 : Blo 2255435 10738655 := bstep (se 1 (by rfl) ⟨8053991, by rfl⟩ : syracuseStep 10738655 = 16107983) B16107983
theorem B7159103 : Blo 2255435 7159103 := bstep (se 1 (by rfl) ⟨5369327, by rfl⟩ : syracuseStep 7159103 = 10738655) B10738655
theorem B4772735 : Blo 2255435 4772735 := bstep (se 1 (by rfl) ⟨3579551, by rfl⟩ : syracuseStep 4772735 = 7159103) B7159103
theorem B203636693 : Blo 2255435 203636693 := bstep (se 7 (by rfl) ⟨2386367, by rfl⟩ : syracuseStep 203636693 = 4772735) B4772735
theorem B135757795 : Blo 2255435 135757795 := bstep (se 1 (by rfl) ⟨101818346, by rfl⟩ : syracuseStep 135757795 = 203636693) B203636693
theorem B181010393 : Blo 2255435 181010393 := bstep (se 2 (by rfl) ⟨67878897, by rfl⟩ : syracuseStep 181010393 = 135757795) B135757795
theorem B120673595 : Blo 2255435 120673595 := bstep (se 1 (by rfl) ⟨90505196, by rfl⟩ : syracuseStep 120673595 = 181010393) B181010393
theorem B321796253 : Blo 2255435 321796253 := bstep (se 3 (by rfl) ⟨60336797, by rfl⟩ : syracuseStep 321796253 = 120673595) B120673595
theorem B858123341 : Blo 2255435 858123341 := bstep (se 3 (by rfl) ⟨160898126, by rfl⟩ : syracuseStep 858123341 = 321796253) B321796253
theorem B572082227 : Blo 2255435 572082227 := bstep (se 1 (by rfl) ⟨429061670, by rfl⟩ : syracuseStep 572082227 = 858123341) B858123341
theorem B381388151 : Blo 2255435 381388151 := bstep (se 1 (by rfl) ⟨286041113, by rfl⟩ : syracuseStep 381388151 = 572082227) B572082227
theorem B254258767 : Blo 2255435 254258767 := bstep (se 1 (by rfl) ⟨190694075, by rfl⟩ : syracuseStep 254258767 = 381388151) B381388151
theorem B339011689 : Blo 2255435 339011689 := bstep (se 2 (by rfl) ⟨127129383, by rfl⟩ : syracuseStep 339011689 = 254258767) B254258767
theorem B452015585 : Blo 2255435 452015585 := bstep (se 2 (by rfl) ⟨169505844, by rfl⟩ : syracuseStep 452015585 = 339011689) B339011689
theorem B301343723 : Blo 2255435 301343723 := bstep (se 1 (by rfl) ⟨226007792, by rfl⟩ : syracuseStep 301343723 = 452015585) B452015585
theorem B200895815 : Blo 2255435 200895815 := bstep (se 1 (by rfl) ⟨150671861, by rfl⟩ : syracuseStep 200895815 = 301343723) B301343723
theorem B133930543 : Blo 2255435 133930543 := bstep (se 1 (by rfl) ⟨100447907, by rfl⟩ : syracuseStep 133930543 = 200895815) B200895815
theorem B178574057 : Blo 2255435 178574057 := bstep (se 2 (by rfl) ⟨66965271, by rfl⟩ : syracuseStep 178574057 = 133930543) B133930543
theorem B119049371 : Blo 2255435 119049371 := bstep (se 1 (by rfl) ⟨89287028, by rfl⟩ : syracuseStep 119049371 = 178574057) B178574057
theorem B79366247 : Blo 2255435 79366247 := bstep (se 1 (by rfl) ⟨59524685, by rfl⟩ : syracuseStep 79366247 = 119049371) B119049371
theorem B846573301 : Blo 2255435 846573301 := bstep (se 5 (by rfl) ⟨39683123, by rfl⟩ : syracuseStep 846573301 = 79366247) B79366247
theorem B4515057605 : Blo 2255435 4515057605 := bstep (se 4 (by rfl) ⟨423286650, by rfl⟩ : syracuseStep 4515057605 = 846573301) B846573301
theorem B3010038403 : Blo 2255435 3010038403 := bstep (se 1 (by rfl) ⟨2257528802, by rfl⟩ : syracuseStep 3010038403 = 4515057605) B4515057605
theorem B4013384537 : Blo 2255435 4013384537 := bstep (se 2 (by rfl) ⟨1505019201, by rfl⟩ : syracuseStep 4013384537 = 3010038403) B3010038403
theorem B10702358765 : Blo 2255435 10702358765 := bstep (se 3 (by rfl) ⟨2006692268, by rfl⟩ : syracuseStep 10702358765 = 4013384537) B4013384537
theorem B7134905843 : Blo 2255435 7134905843 := bstep (se 1 (by rfl) ⟨5351179382, by rfl⟩ : syracuseStep 7134905843 = 10702358765) B10702358765
theorem B4756603895 : Blo 2255435 4756603895 := bstep (se 1 (by rfl) ⟨3567452921, by rfl⟩ : syracuseStep 4756603895 = 7134905843) B7134905843
theorem B3171069263 : Blo 2255435 3171069263 := bstep (se 1 (by rfl) ⟨2378301947, by rfl⟩ : syracuseStep 3171069263 = 4756603895) B4756603895
theorem B2114046175 : Blo 2255435 2114046175 := bstep (se 1 (by rfl) ⟨1585534631, by rfl⟩ : syracuseStep 2114046175 = 3171069263) B3171069263
theorem B2818728233 : Blo 2255435 2818728233 := bstep (se 2 (by rfl) ⟨1057023087, by rfl⟩ : syracuseStep 2818728233 = 2114046175) B2114046175
theorem B1879152155 : Blo 2255435 1879152155 := bstep (se 1 (by rfl) ⟨1409364116, by rfl⟩ : syracuseStep 1879152155 = 2818728233) B2818728233
theorem B1252768103 : Blo 2255435 1252768103 := bstep (se 1 (by rfl) ⟨939576077, by rfl⟩ : syracuseStep 1252768103 = 1879152155) B1879152155
theorem B835178735 : Blo 2255435 835178735 := bstep (se 1 (by rfl) ⟨626384051, by rfl⟩ : syracuseStep 835178735 = 1252768103) B1252768103
theorem B556785823 : Blo 2255435 556785823 := bstep (se 1 (by rfl) ⟨417589367, by rfl⟩ : syracuseStep 556785823 = 835178735) B835178735
theorem B742381097 : Blo 2255435 742381097 := bstep (se 2 (by rfl) ⟨278392911, by rfl⟩ : syracuseStep 742381097 = 556785823) B556785823
theorem B1979682925 : Blo 2255435 1979682925 := bstep (se 3 (by rfl) ⟨371190548, by rfl⟩ : syracuseStep 1979682925 = 742381097) B742381097
theorem B2639577233 : Blo 2255435 2639577233 := bstep (se 2 (by rfl) ⟨989841462, by rfl⟩ : syracuseStep 2639577233 = 1979682925) B1979682925
theorem B7038872621 : Blo 2255435 7038872621 := bstep (se 3 (by rfl) ⟨1319788616, by rfl⟩ : syracuseStep 7038872621 = 2639577233) B2639577233
theorem B4692581747 : Blo 2255435 4692581747 := bstep (se 1 (by rfl) ⟨3519436310, by rfl⟩ : syracuseStep 4692581747 = 7038872621) B7038872621
theorem B3128387831 : Blo 2255435 3128387831 := bstep (se 1 (by rfl) ⟨2346290873, by rfl⟩ : syracuseStep 3128387831 = 4692581747) B4692581747
theorem B2085591887 : Blo 2255435 2085591887 := bstep (se 1 (by rfl) ⟨1564193915, by rfl⟩ : syracuseStep 2085591887 = 3128387831) B3128387831
theorem B1390394591 : Blo 2255435 1390394591 := bstep (se 1 (by rfl) ⟨1042795943, by rfl⟩ : syracuseStep 1390394591 = 2085591887) B2085591887
theorem B926929727 : Blo 2255435 926929727 := bstep (se 1 (by rfl) ⟨695197295, by rfl⟩ : syracuseStep 926929727 = 1390394591) B1390394591
theorem B617953151 : Blo 2255435 617953151 := bstep (se 1 (by rfl) ⟨463464863, by rfl⟩ : syracuseStep 617953151 = 926929727) B926929727
theorem B411968767 : Blo 2255435 411968767 := bstep (se 1 (by rfl) ⟨308976575, by rfl⟩ : syracuseStep 411968767 = 617953151) B617953151
theorem B549291689 : Blo 2255435 549291689 := bstep (se 2 (by rfl) ⟨205984383, by rfl⟩ : syracuseStep 549291689 = 411968767) B411968767
theorem B366194459 : Blo 2255435 366194459 := bstep (se 1 (by rfl) ⟨274645844, by rfl⟩ : syracuseStep 366194459 = 549291689) B549291689
theorem B244129639 : Blo 2255435 244129639 := bstep (se 1 (by rfl) ⟨183097229, by rfl⟩ : syracuseStep 244129639 = 366194459) B366194459
theorem B325506185 : Blo 2255435 325506185 := bstep (se 2 (by rfl) ⟨122064819, by rfl⟩ : syracuseStep 325506185 = 244129639) B244129639
theorem B217004123 : Blo 2255435 217004123 := bstep (se 1 (by rfl) ⟨162753092, by rfl⟩ : syracuseStep 217004123 = 325506185) B325506185
theorem B144669415 : Blo 2255435 144669415 := bstep (se 1 (by rfl) ⟨108502061, by rfl⟩ : syracuseStep 144669415 = 217004123) B217004123
theorem B192892553 : Blo 2255435 192892553 := bstep (se 2 (by rfl) ⟨72334707, by rfl⟩ : syracuseStep 192892553 = 144669415) B144669415
theorem B128595035 : Blo 2255435 128595035 := bstep (se 1 (by rfl) ⟨96446276, by rfl⟩ : syracuseStep 128595035 = 192892553) B192892553
theorem B85730023 : Blo 2255435 85730023 := bstep (se 1 (by rfl) ⟨64297517, by rfl⟩ : syracuseStep 85730023 = 128595035) B128595035
theorem B114306697 : Blo 2255435 114306697 := bstep (se 2 (by rfl) ⟨42865011, by rfl⟩ : syracuseStep 114306697 = 85730023) B85730023
theorem B609635717 : Blo 2255435 609635717 := bstep (se 4 (by rfl) ⟨57153348, by rfl⟩ : syracuseStep 609635717 = 114306697) B114306697
theorem B406423811 : Blo 2255435 406423811 := bstep (se 1 (by rfl) ⟨304817858, by rfl⟩ : syracuseStep 406423811 = 609635717) B609635717
theorem B270949207 : Blo 2255435 270949207 := bstep (se 1 (by rfl) ⟨203211905, by rfl⟩ : syracuseStep 270949207 = 406423811) B406423811
theorem B361265609 : Blo 2255435 361265609 := bstep (se 2 (by rfl) ⟨135474603, by rfl⟩ : syracuseStep 361265609 = 270949207) B270949207
theorem B963374957 : Blo 2255435 963374957 := bstep (se 3 (by rfl) ⟨180632804, by rfl⟩ : syracuseStep 963374957 = 361265609) B361265609
theorem B642249971 : Blo 2255435 642249971 := bstep (se 1 (by rfl) ⟨481687478, by rfl⟩ : syracuseStep 642249971 = 963374957) B963374957
theorem B428166647 : Blo 2255435 428166647 := bstep (se 1 (by rfl) ⟨321124985, by rfl⟩ : syracuseStep 428166647 = 642249971) B642249971
theorem B285444431 : Blo 2255435 285444431 := bstep (se 1 (by rfl) ⟨214083323, by rfl⟩ : syracuseStep 285444431 = 428166647) B428166647
theorem B190296287 : Blo 2255435 190296287 := bstep (se 1 (by rfl) ⟨142722215, by rfl⟩ : syracuseStep 190296287 = 285444431) B285444431
theorem B126864191 : Blo 2255435 126864191 := bstep (se 1 (by rfl) ⟨95148143, by rfl⟩ : syracuseStep 126864191 = 190296287) B190296287
theorem B338304509 : Blo 2255435 338304509 := bstep (se 3 (by rfl) ⟨63432095, by rfl⟩ : syracuseStep 338304509 = 126864191) B126864191
theorem B225536339 : Blo 2255435 225536339 := bstep (se 1 (by rfl) ⟨169152254, by rfl⟩ : syracuseStep 225536339 = 338304509) B338304509
theorem B150357559 : Blo 2255435 150357559 := bstep (se 1 (by rfl) ⟨112768169, by rfl⟩ : syracuseStep 150357559 = 225536339) B225536339
theorem B200476745 : Blo 2255435 200476745 := bstep (se 2 (by rfl) ⟨75178779, by rfl⟩ : syracuseStep 200476745 = 150357559) B150357559
theorem B133651163 : Blo 2255435 133651163 := bstep (se 1 (by rfl) ⟨100238372, by rfl⟩ : syracuseStep 133651163 = 200476745) B200476745
theorem B89100775 : Blo 2255435 89100775 := bstep (se 1 (by rfl) ⟨66825581, by rfl⟩ : syracuseStep 89100775 = 133651163) B133651163
theorem B475204133 : Blo 2255435 475204133 := bstep (se 4 (by rfl) ⟨44550387, by rfl⟩ : syracuseStep 475204133 = 89100775) B89100775
theorem B316802755 : Blo 2255435 316802755 := bstep (se 1 (by rfl) ⟨237602066, by rfl⟩ : syracuseStep 316802755 = 475204133) B475204133
theorem B422403673 : Blo 2255435 422403673 := bstep (se 2 (by rfl) ⟨158401377, by rfl⟩ : syracuseStep 422403673 = 316802755) B316802755
theorem B563204897 : Blo 2255435 563204897 := bstep (se 2 (by rfl) ⟨211201836, by rfl⟩ : syracuseStep 563204897 = 422403673) B422403673
theorem B375469931 : Blo 2255435 375469931 := bstep (se 1 (by rfl) ⟨281602448, by rfl⟩ : syracuseStep 375469931 = 563204897) B563204897
theorem B250313287 : Blo 2255435 250313287 := bstep (se 1 (by rfl) ⟨187734965, by rfl⟩ : syracuseStep 250313287 = 375469931) B375469931
theorem B333751049 : Blo 2255435 333751049 := bstep (se 2 (by rfl) ⟨125156643, by rfl⟩ : syracuseStep 333751049 = 250313287) B250313287
theorem B222500699 : Blo 2255435 222500699 := bstep (se 1 (by rfl) ⟨166875524, by rfl⟩ : syracuseStep 222500699 = 333751049) B333751049
theorem B148333799 : Blo 2255435 148333799 := bstep (se 1 (by rfl) ⟨111250349, by rfl⟩ : syracuseStep 148333799 = 222500699) B222500699
theorem B395556797 : Blo 2255435 395556797 := bstep (se 3 (by rfl) ⟨74166899, by rfl⟩ : syracuseStep 395556797 = 148333799) B148333799
theorem B263704531 : Blo 2255435 263704531 := bstep (se 1 (by rfl) ⟨197778398, by rfl⟩ : syracuseStep 263704531 = 395556797) B395556797
theorem B351606041 : Blo 2255435 351606041 := bstep (se 2 (by rfl) ⟨131852265, by rfl⟩ : syracuseStep 351606041 = 263704531) B263704531
theorem B234404027 : Blo 2255435 234404027 := bstep (se 1 (by rfl) ⟨175803020, by rfl⟩ : syracuseStep 234404027 = 351606041) B351606041
theorem B156269351 : Blo 2255435 156269351 := bstep (se 1 (by rfl) ⟨117202013, by rfl⟩ : syracuseStep 156269351 = 234404027) B234404027
theorem B104179567 : Blo 2255435 104179567 := bstep (se 1 (by rfl) ⟨78134675, by rfl⟩ : syracuseStep 104179567 = 156269351) B156269351
theorem B138906089 : Blo 2255435 138906089 := bstep (se 2 (by rfl) ⟨52089783, by rfl⟩ : syracuseStep 138906089 = 104179567) B104179567
theorem B92604059 : Blo 2255435 92604059 := bstep (se 1 (by rfl) ⟨69453044, by rfl⟩ : syracuseStep 92604059 = 138906089) B138906089
theorem B61736039 : Blo 2255435 61736039 := bstep (se 1 (by rfl) ⟨46302029, by rfl⟩ : syracuseStep 61736039 = 92604059) B92604059
theorem B41157359 : Blo 2255435 41157359 := bstep (se 1 (by rfl) ⟨30868019, by rfl⟩ : syracuseStep 41157359 = 61736039) B61736039
theorem B27438239 : Blo 2255435 27438239 := bstep (se 1 (by rfl) ⟨20578679, by rfl⟩ : syracuseStep 27438239 = 41157359) B41157359
theorem B18292159 : Blo 2255435 18292159 := bstep (se 1 (by rfl) ⟨13719119, by rfl⟩ : syracuseStep 18292159 = 27438239) B27438239
theorem B24389545 : Blo 2255435 24389545 := bstep (se 2 (by rfl) ⟨9146079, by rfl⟩ : syracuseStep 24389545 = 18292159) B18292159
theorem B32519393 : Blo 2255435 32519393 := bstep (se 2 (by rfl) ⟨12194772, by rfl⟩ : syracuseStep 32519393 = 24389545) B24389545
theorem B21679595 : Blo 2255435 21679595 := bstep (se 1 (by rfl) ⟨16259696, by rfl⟩ : syracuseStep 21679595 = 32519393) B32519393
theorem B14453063 : Blo 2255435 14453063 := bstep (se 1 (by rfl) ⟨10839797, by rfl⟩ : syracuseStep 14453063 = 21679595) B21679595
theorem B9635375 : Blo 2255435 9635375 := bstep (se 1 (by rfl) ⟨7226531, by rfl⟩ : syracuseStep 9635375 = 14453063) B14453063
theorem B25694333 : Blo 2255435 25694333 := bstep (se 3 (by rfl) ⟨4817687, by rfl⟩ : syracuseStep 25694333 = 9635375) B9635375
theorem B17129555 : Blo 2255435 17129555 := bstep (se 1 (by rfl) ⟨12847166, by rfl⟩ : syracuseStep 17129555 = 25694333) B25694333
theorem B11419703 : Blo 2255435 11419703 := bstep (se 1 (by rfl) ⟨8564777, by rfl⟩ : syracuseStep 11419703 = 17129555) B17129555
theorem B7613135 : Blo 2255435 7613135 := bstep (se 1 (by rfl) ⟨5709851, by rfl⟩ : syracuseStep 7613135 = 11419703) B11419703
theorem B5075423 : Blo 2255435 5075423 := bstep (se 1 (by rfl) ⟨3806567, by rfl⟩ : syracuseStep 5075423 = 7613135) B7613135
theorem B3383615 : Blo 2255435 3383615 := bstep (se 1 (by rfl) ⟨2537711, by rfl⟩ : syracuseStep 3383615 = 5075423) B5075423
theorem B2255743 : Blo 2255435 2255743 := bstep (se 1 (by rfl) ⟨1691807, by rfl⟩ : syracuseStep 2255743 = 3383615) B3383615
theorem B3383621 : Blo 2255435 3383621 := bbase (se 4 (by rfl) ⟨317214, by rfl⟩ : syracuseStep 3383621 = 634429) (by norm_num)
theorem B2255747 : Blo 2255435 2255747 := bstep (se 1 (by rfl) ⟨1691810, by rfl⟩ : syracuseStep 2255747 = 3383621) B3383621
theorem B3806581 : Blo 2255435 3806581 := bbase (se 5 (by rfl) ⟨178433, by rfl⟩ : syracuseStep 3806581 = 356867) (by norm_num)
theorem B5075441 : Blo 2255435 5075441 := bstep (se 2 (by rfl) ⟨1903290, by rfl⟩ : syracuseStep 5075441 = 3806581) B3806581
theorem B3383627 : Blo 2255435 3383627 := bstep (se 1 (by rfl) ⟨2537720, by rfl⟩ : syracuseStep 3383627 = 5075441) B5075441
theorem B2255751 : Blo 2255435 2255751 := bstep (se 1 (by rfl) ⟨1691813, by rfl⟩ : syracuseStep 2255751 = 3383627) B3383627
theorem B2537725 : Blo 2255435 2537725 := bbase (se 3 (by rfl) ⟨475823, by rfl⟩ : syracuseStep 2537725 = 951647) (by norm_num)
theorem B3383633 : Blo 2255435 3383633 := bstep (se 2 (by rfl) ⟨1268862, by rfl⟩ : syracuseStep 3383633 = 2537725) B2537725
theorem B2255755 : Blo 2255435 2255755 := bstep (se 1 (by rfl) ⟨1691816, by rfl⟩ : syracuseStep 2255755 = 3383633) B3383633
theorem B7613189 : Blo 2255435 7613189 := bbase (se 4 (by rfl) ⟨713736, by rfl⟩ : syracuseStep 7613189 = 1427473) (by norm_num)
theorem B5075459 : Blo 2255435 5075459 := bstep (se 1 (by rfl) ⟨3806594, by rfl⟩ : syracuseStep 5075459 = 7613189) B7613189
theorem B3383639 : Blo 2255435 3383639 := bstep (se 1 (by rfl) ⟨2537729, by rfl⟩ : syracuseStep 3383639 = 5075459) B5075459
theorem B2255759 : Blo 2255435 2255759 := bstep (se 1 (by rfl) ⟨1691819, by rfl⟩ : syracuseStep 2255759 = 3383639) B3383639
theorem B3383645 : Blo 2255435 3383645 := bbase (se 3 (by rfl) ⟨634433, by rfl⟩ : syracuseStep 3383645 = 1268867) (by norm_num)
theorem B2255763 : Blo 2255435 2255763 := bstep (se 1 (by rfl) ⟨1691822, by rfl⟩ : syracuseStep 2255763 = 3383645) B3383645
theorem B5075477 : Blo 2255435 5075477 := bbase (se 6 (by rfl) ⟨118956, by rfl⟩ : syracuseStep 5075477 = 237913) (by norm_num)
theorem B3383651 : Blo 2255435 3383651 := bstep (se 1 (by rfl) ⟨2537738, by rfl⟩ : syracuseStep 3383651 = 5075477) B5075477
theorem B2255767 : Blo 2255435 2255767 := bstep (se 1 (by rfl) ⟨1691825, by rfl⟩ : syracuseStep 2255767 = 3383651) B3383651
theorem B8564885 : Blo 2255435 8564885 := bbase (se 6 (by rfl) ⟨200739, by rfl⟩ : syracuseStep 8564885 = 401479) (by norm_num)
theorem B5709923 : Blo 2255435 5709923 := bstep (se 1 (by rfl) ⟨4282442, by rfl⟩ : syracuseStep 5709923 = 8564885) B8564885
theorem B3806615 : Blo 2255435 3806615 := bstep (se 1 (by rfl) ⟨2854961, by rfl⟩ : syracuseStep 3806615 = 5709923) B5709923
theorem B2537743 : Blo 2255435 2537743 := bstep (se 1 (by rfl) ⟨1903307, by rfl⟩ : syracuseStep 2537743 = 3806615) B3806615
theorem B3383657 : Blo 2255435 3383657 := bstep (se 2 (by rfl) ⟨1268871, by rfl⟩ : syracuseStep 3383657 = 2537743) B2537743
theorem B2255771 : Blo 2255435 2255771 := bstep (se 1 (by rfl) ⟨1691828, by rfl⟩ : syracuseStep 2255771 = 3383657) B3383657
theorem B12847349 : Blo 2255435 12847349 := bbase (se 5 (by rfl) ⟨602219, by rfl⟩ : syracuseStep 12847349 = 1204439) (by norm_num)
theorem B8564899 : Blo 2255435 8564899 := bstep (se 1 (by rfl) ⟨6423674, by rfl⟩ : syracuseStep 8564899 = 12847349) B12847349
theorem B11419865 : Blo 2255435 11419865 := bstep (se 2 (by rfl) ⟨4282449, by rfl⟩ : syracuseStep 11419865 = 8564899) B8564899
theorem B7613243 : Blo 2255435 7613243 := bstep (se 1 (by rfl) ⟨5709932, by rfl⟩ : syracuseStep 7613243 = 11419865) B11419865
theorem B5075495 : Blo 2255435 5075495 := bstep (se 1 (by rfl) ⟨3806621, by rfl⟩ : syracuseStep 5075495 = 7613243) B7613243
theorem B3383663 : Blo 2255435 3383663 := bstep (se 1 (by rfl) ⟨2537747, by rfl⟩ : syracuseStep 3383663 = 5075495) B5075495
theorem B2255775 : Blo 2255435 2255775 := bstep (se 1 (by rfl) ⟨1691831, by rfl⟩ : syracuseStep 2255775 = 3383663) B3383663
theorem B3383669 : Blo 2255435 3383669 := bbase (se 5 (by rfl) ⟨158609, by rfl⟩ : syracuseStep 3383669 = 317219) (by norm_num)
theorem B2255779 : Blo 2255435 2255779 := bstep (se 1 (by rfl) ⟨1691834, by rfl⟩ : syracuseStep 2255779 = 3383669) B3383669
theorem B5419997 : Blo 2255435 5419997 := bbase (se 3 (by rfl) ⟨1016249, by rfl⟩ : syracuseStep 5419997 = 2032499) (by norm_num)
theorem B3613331 : Blo 2255435 3613331 := bstep (se 1 (by rfl) ⟨2709998, by rfl⟩ : syracuseStep 3613331 = 5419997) B5419997
theorem B2408887 : Blo 2255435 2408887 := bstep (se 1 (by rfl) ⟨1806665, by rfl⟩ : syracuseStep 2408887 = 3613331) B3613331
theorem B3211849 : Blo 2255435 3211849 := bstep (se 2 (by rfl) ⟨1204443, by rfl⟩ : syracuseStep 3211849 = 2408887) B2408887
theorem B4282465 : Blo 2255435 4282465 := bstep (se 2 (by rfl) ⟨1605924, by rfl⟩ : syracuseStep 4282465 = 3211849) B3211849
theorem B5709953 : Blo 2255435 5709953 := bstep (se 2 (by rfl) ⟨2141232, by rfl⟩ : syracuseStep 5709953 = 4282465) B4282465
theorem B3806635 : Blo 2255435 3806635 := bstep (se 1 (by rfl) ⟨2854976, by rfl⟩ : syracuseStep 3806635 = 5709953) B5709953
theorem B5075513 : Blo 2255435 5075513 := bstep (se 2 (by rfl) ⟨1903317, by rfl⟩ : syracuseStep 5075513 = 3806635) B3806635
theorem B3383675 : Blo 2255435 3383675 := bstep (se 1 (by rfl) ⟨2537756, by rfl⟩ : syracuseStep 3383675 = 5075513) B5075513
theorem B2255783 : Blo 2255435 2255783 := bstep (se 1 (by rfl) ⟨1691837, by rfl⟩ : syracuseStep 2255783 = 3383675) B3383675
theorem B2537761 : Blo 2255435 2537761 := bbase (se 2 (by rfl) ⟨951660, by rfl⟩ : syracuseStep 2537761 = 1903321) (by norm_num)
theorem B3383681 : Blo 2255435 3383681 := bstep (se 2 (by rfl) ⟨1268880, by rfl⟩ : syracuseStep 3383681 = 2537761) B2537761
theorem B2255787 : Blo 2255435 2255787 := bstep (se 1 (by rfl) ⟨1691840, by rfl⟩ : syracuseStep 2255787 = 3383681) B3383681
theorem B5709973 : Blo 2255435 5709973 := bbase (se 6 (by rfl) ⟨133827, by rfl⟩ : syracuseStep 5709973 = 267655) (by norm_num)
theorem B7613297 : Blo 2255435 7613297 := bstep (se 2 (by rfl) ⟨2854986, by rfl⟩ : syracuseStep 7613297 = 5709973) B5709973
theorem B5075531 : Blo 2255435 5075531 := bstep (se 1 (by rfl) ⟨3806648, by rfl⟩ : syracuseStep 5075531 = 7613297) B7613297
theorem B3383687 : Blo 2255435 3383687 := bstep (se 1 (by rfl) ⟨2537765, by rfl⟩ : syracuseStep 3383687 = 5075531) B5075531
theorem B2255791 : Blo 2255435 2255791 := bstep (se 1 (by rfl) ⟨1691843, by rfl⟩ : syracuseStep 2255791 = 3383687) B3383687
theorem B3383693 : Blo 2255435 3383693 := bbase (se 3 (by rfl) ⟨634442, by rfl⟩ : syracuseStep 3383693 = 1268885) (by norm_num)
theorem B2255795 : Blo 2255435 2255795 := bstep (se 1 (by rfl) ⟨1691846, by rfl⟩ : syracuseStep 2255795 = 3383693) B3383693
theorem B5075549 : Blo 2255435 5075549 := bbase (se 3 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 5075549 = 1903331) (by norm_num)
theorem B3383699 : Blo 2255435 3383699 := bstep (se 1 (by rfl) ⟨2537774, by rfl⟩ : syracuseStep 3383699 = 5075549) B5075549
theorem B2255799 : Blo 2255435 2255799 := bstep (se 1 (by rfl) ⟨1691849, by rfl⟩ : syracuseStep 2255799 = 3383699) B3383699
theorem B3806669 : Blo 2255435 3806669 := bbase (se 3 (by rfl) ⟨713750, by rfl⟩ : syracuseStep 3806669 = 1427501) (by norm_num)
theorem B2537779 : Blo 2255435 2537779 := bstep (se 1 (by rfl) ⟨1903334, by rfl⟩ : syracuseStep 2537779 = 3806669) B3806669
theorem B3383705 : Blo 2255435 3383705 := bstep (se 2 (by rfl) ⟨1268889, by rfl⟩ : syracuseStep 3383705 = 2537779) B2537779
theorem B2255803 : Blo 2255435 2255803 := bstep (se 1 (by rfl) ⟨1691852, by rfl⟩ : syracuseStep 2255803 = 3383705) B3383705
theorem B4120501 : Blo 2255435 4120501 := bbase (se 5 (by rfl) ⟨193148, by rfl⟩ : syracuseStep 4120501 = 386297) (by norm_num)
theorem B5494001 : Blo 2255435 5494001 := bstep (se 2 (by rfl) ⟨2060250, by rfl⟩ : syracuseStep 5494001 = 4120501) B4120501
theorem B14650669 : Blo 2255435 14650669 := bstep (se 3 (by rfl) ⟨2747000, by rfl⟩ : syracuseStep 14650669 = 5494001) B5494001
theorem B19534225 : Blo 2255435 19534225 := bstep (se 2 (by rfl) ⟨7325334, by rfl⟩ : syracuseStep 19534225 = 14650669) B14650669
theorem B26045633 : Blo 2255435 26045633 := bstep (se 2 (by rfl) ⟨9767112, by rfl⟩ : syracuseStep 26045633 = 19534225) B19534225
theorem B17363755 : Blo 2255435 17363755 := bstep (se 1 (by rfl) ⟨13022816, by rfl⟩ : syracuseStep 17363755 = 26045633) B26045633
theorem B23151673 : Blo 2255435 23151673 := bstep (se 2 (by rfl) ⟨8681877, by rfl⟩ : syracuseStep 23151673 = 17363755) B17363755
theorem B30868897 : Blo 2255435 30868897 := bstep (se 2 (by rfl) ⟨11575836, by rfl⟩ : syracuseStep 30868897 = 23151673) B23151673
theorem B41158529 : Blo 2255435 41158529 := bstep (se 2 (by rfl) ⟨15434448, by rfl⟩ : syracuseStep 41158529 = 30868897) B30868897
theorem B27439019 : Blo 2255435 27439019 := bstep (se 1 (by rfl) ⟨20579264, by rfl⟩ : syracuseStep 27439019 = 41158529) B41158529
theorem B18292679 : Blo 2255435 18292679 := bstep (se 1 (by rfl) ⟨13719509, by rfl⟩ : syracuseStep 18292679 = 27439019) B27439019
theorem B12195119 : Blo 2255435 12195119 := bstep (se 1 (by rfl) ⟨9146339, by rfl⟩ : syracuseStep 12195119 = 18292679) B18292679
theorem B8130079 : Blo 2255435 8130079 := bstep (se 1 (by rfl) ⟨6097559, by rfl⟩ : syracuseStep 8130079 = 12195119) B12195119
theorem B10840105 : Blo 2255435 10840105 := bstep (se 2 (by rfl) ⟨4065039, by rfl⟩ : syracuseStep 10840105 = 8130079) B8130079
theorem B14453473 : Blo 2255435 14453473 := bstep (se 2 (by rfl) ⟨5420052, by rfl⟩ : syracuseStep 14453473 = 10840105) B10840105
theorem B19271297 : Blo 2255435 19271297 := bstep (se 2 (by rfl) ⟨7226736, by rfl⟩ : syracuseStep 19271297 = 14453473) B14453473
theorem B12847531 : Blo 2255435 12847531 := bstep (se 1 (by rfl) ⟨9635648, by rfl⟩ : syracuseStep 12847531 = 19271297) B19271297
theorem B17130041 : Blo 2255435 17130041 := bstep (se 2 (by rfl) ⟨6423765, by rfl⟩ : syracuseStep 17130041 = 12847531) B12847531
theorem B11420027 : Blo 2255435 11420027 := bstep (se 1 (by rfl) ⟨8565020, by rfl⟩ : syracuseStep 11420027 = 17130041) B17130041
theorem B7613351 : Blo 2255435 7613351 := bstep (se 1 (by rfl) ⟨5710013, by rfl⟩ : syracuseStep 7613351 = 11420027) B11420027
theorem B5075567 : Blo 2255435 5075567 := bstep (se 1 (by rfl) ⟨3806675, by rfl⟩ : syracuseStep 5075567 = 7613351) B7613351
theorem B3383711 : Blo 2255435 3383711 := bstep (se 1 (by rfl) ⟨2537783, by rfl⟩ : syracuseStep 3383711 = 5075567) B5075567
theorem B2255807 : Blo 2255435 2255807 := bstep (se 1 (by rfl) ⟨1691855, by rfl⟩ : syracuseStep 2255807 = 3383711) B3383711
theorem B3383717 : Blo 2255435 3383717 := bbase (se 4 (by rfl) ⟨317223, by rfl⟩ : syracuseStep 3383717 = 634447) (by norm_num)
theorem B2255811 : Blo 2255435 2255811 := bstep (se 1 (by rfl) ⟨1691858, by rfl⟩ : syracuseStep 2255811 = 3383717) B3383717
theorem B2855017 : Blo 2255435 2855017 := bbase (se 2 (by rfl) ⟨1070631, by rfl⟩ : syracuseStep 2855017 = 2141263) (by norm_num)
theorem B3806689 : Blo 2255435 3806689 := bstep (se 2 (by rfl) ⟨1427508, by rfl⟩ : syracuseStep 3806689 = 2855017) B2855017
theorem B5075585 : Blo 2255435 5075585 := bstep (se 2 (by rfl) ⟨1903344, by rfl⟩ : syracuseStep 5075585 = 3806689) B3806689
theorem B3383723 : Blo 2255435 3383723 := bstep (se 1 (by rfl) ⟨2537792, by rfl⟩ : syracuseStep 3383723 = 5075585) B5075585
theorem B2255815 : Blo 2255435 2255815 := bstep (se 1 (by rfl) ⟨1691861, by rfl⟩ : syracuseStep 2255815 = 3383723) B3383723
theorem B2537797 : Blo 2255435 2537797 := bbase (se 4 (by rfl) ⟨237918, by rfl⟩ : syracuseStep 2537797 = 475837) (by norm_num)
theorem B3383729 : Blo 2255435 3383729 := bstep (se 2 (by rfl) ⟨1268898, by rfl⟩ : syracuseStep 3383729 = 2537797) B2537797
theorem B2255819 : Blo 2255435 2255819 := bstep (se 1 (by rfl) ⟨1691864, by rfl⟩ : syracuseStep 2255819 = 3383729) B3383729
theorem B4282541 : Blo 2255435 4282541 := bbase (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) (by norm_num)
theorem B2855027 : Blo 2255435 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B7613405 : Blo 2255435 7613405 := bstep (se 3 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 7613405 = 2855027) B2855027
theorem B5075603 : Blo 2255435 5075603 := bstep (se 1 (by rfl) ⟨3806702, by rfl⟩ : syracuseStep 5075603 = 7613405) B7613405
theorem B3383735 : Blo 2255435 3383735 := bstep (se 1 (by rfl) ⟨2537801, by rfl⟩ : syracuseStep 3383735 = 5075603) B5075603
theorem B2255823 : Blo 2255435 2255823 := bstep (se 1 (by rfl) ⟨1691867, by rfl⟩ : syracuseStep 2255823 = 3383735) B3383735
theorem B3383741 : Blo 2255435 3383741 := bbase (se 3 (by rfl) ⟨634451, by rfl⟩ : syracuseStep 3383741 = 1268903) (by norm_num)
theorem B2255827 : Blo 2255435 2255827 := bstep (se 1 (by rfl) ⟨1691870, by rfl⟩ : syracuseStep 2255827 = 3383741) B3383741
theorem B5075621 : Blo 2255435 5075621 := bbase (se 4 (by rfl) ⟨475839, by rfl⟩ : syracuseStep 5075621 = 951679) (by norm_num)
theorem B3383747 : Blo 2255435 3383747 := bstep (se 1 (by rfl) ⟨2537810, by rfl⟩ : syracuseStep 3383747 = 5075621) B5075621
theorem B2255831 : Blo 2255435 2255831 := bstep (se 1 (by rfl) ⟨1691873, by rfl⟩ : syracuseStep 2255831 = 3383747) B3383747
theorem B5710085 : Blo 2255435 5710085 := bbase (se 4 (by rfl) ⟨535320, by rfl⟩ : syracuseStep 5710085 = 1070641) (by norm_num)
theorem B3806723 : Blo 2255435 3806723 := bstep (se 1 (by rfl) ⟨2855042, by rfl⟩ : syracuseStep 3806723 = 5710085) B5710085
theorem B2537815 : Blo 2255435 2537815 := bstep (se 1 (by rfl) ⟨1903361, by rfl⟩ : syracuseStep 2537815 = 3806723) B3806723
theorem B3383753 : Blo 2255435 3383753 := bstep (se 2 (by rfl) ⟨1268907, by rfl⟩ : syracuseStep 3383753 = 2537815) B2537815
theorem B2255835 : Blo 2255435 2255835 := bstep (se 1 (by rfl) ⟨1691876, by rfl⟩ : syracuseStep 2255835 = 3383753) B3383753
theorem B4817893 : Blo 2255435 4817893 := bbase (se 4 (by rfl) ⟨451677, by rfl⟩ : syracuseStep 4817893 = 903355) (by norm_num)
theorem B6423857 : Blo 2255435 6423857 := bstep (se 2 (by rfl) ⟨2408946, by rfl⟩ : syracuseStep 6423857 = 4817893) B4817893
theorem B4282571 : Blo 2255435 4282571 := bstep (se 1 (by rfl) ⟨3211928, by rfl⟩ : syracuseStep 4282571 = 6423857) B6423857
theorem B11420189 : Blo 2255435 11420189 := bstep (se 3 (by rfl) ⟨2141285, by rfl⟩ : syracuseStep 11420189 = 4282571) B4282571
theorem B7613459 : Blo 2255435 7613459 := bstep (se 1 (by rfl) ⟨5710094, by rfl⟩ : syracuseStep 7613459 = 11420189) B11420189
theorem B5075639 : Blo 2255435 5075639 := bstep (se 1 (by rfl) ⟨3806729, by rfl⟩ : syracuseStep 5075639 = 7613459) B7613459
theorem B3383759 : Blo 2255435 3383759 := bstep (se 1 (by rfl) ⟨2537819, by rfl⟩ : syracuseStep 3383759 = 5075639) B5075639
theorem B2255839 : Blo 2255435 2255839 := bstep (se 1 (by rfl) ⟨1691879, by rfl⟩ : syracuseStep 2255839 = 3383759) B3383759
theorem B3383765 : Blo 2255435 3383765 := bbase (se 7 (by rfl) ⟨39653, by rfl⟩ : syracuseStep 3383765 = 79307) (by norm_num)
theorem B2255843 : Blo 2255435 2255843 := bstep (se 1 (by rfl) ⟨1691882, by rfl⟩ : syracuseStep 2255843 = 3383765) B3383765
theorem B8565173 : Blo 2255435 8565173 := bbase (se 5 (by rfl) ⟨401492, by rfl⟩ : syracuseStep 8565173 = 802985) (by norm_num)
theorem B5710115 : Blo 2255435 5710115 := bstep (se 1 (by rfl) ⟨4282586, by rfl⟩ : syracuseStep 5710115 = 8565173) B8565173
theorem B3806743 : Blo 2255435 3806743 := bstep (se 1 (by rfl) ⟨2855057, by rfl⟩ : syracuseStep 3806743 = 5710115) B5710115
theorem B5075657 : Blo 2255435 5075657 := bstep (se 2 (by rfl) ⟨1903371, by rfl⟩ : syracuseStep 5075657 = 3806743) B3806743
theorem B3383771 : Blo 2255435 3383771 := bstep (se 1 (by rfl) ⟨2537828, by rfl⟩ : syracuseStep 3383771 = 5075657) B5075657
theorem B2255847 : Blo 2255435 2255847 := bstep (se 1 (by rfl) ⟨1691885, by rfl⟩ : syracuseStep 2255847 = 3383771) B3383771
theorem B2537833 : Blo 2255435 2537833 := bbase (se 2 (by rfl) ⟨951687, by rfl⟩ : syracuseStep 2537833 = 1903375) (by norm_num)
theorem B3383777 : Blo 2255435 3383777 := bstep (se 2 (by rfl) ⟨1268916, by rfl⟩ : syracuseStep 3383777 = 2537833) B2537833
theorem B2255851 : Blo 2255435 2255851 := bstep (se 1 (by rfl) ⟨1691888, by rfl⟩ : syracuseStep 2255851 = 3383777) B3383777
theorem B3048845 : Blo 2255435 3048845 := bbase (se 3 (by rfl) ⟨571658, by rfl⟩ : syracuseStep 3048845 = 1143317) (by norm_num)
theorem B8130253 : Blo 2255435 8130253 := bstep (se 3 (by rfl) ⟨1524422, by rfl⟩ : syracuseStep 8130253 = 3048845) B3048845
theorem B10840337 : Blo 2255435 10840337 := bstep (se 2 (by rfl) ⟨4065126, by rfl⟩ : syracuseStep 10840337 = 8130253) B8130253
theorem B7226891 : Blo 2255435 7226891 := bstep (se 1 (by rfl) ⟨5420168, by rfl⟩ : syracuseStep 7226891 = 10840337) B10840337
theorem B4817927 : Blo 2255435 4817927 := bstep (se 1 (by rfl) ⟨3613445, by rfl⟩ : syracuseStep 4817927 = 7226891) B7226891
theorem B12847805 : Blo 2255435 12847805 := bstep (se 3 (by rfl) ⟨2408963, by rfl⟩ : syracuseStep 12847805 = 4817927) B4817927
theorem B8565203 : Blo 2255435 8565203 := bstep (se 1 (by rfl) ⟨6423902, by rfl⟩ : syracuseStep 8565203 = 12847805) B12847805
theorem B5710135 : Blo 2255435 5710135 := bstep (se 1 (by rfl) ⟨4282601, by rfl⟩ : syracuseStep 5710135 = 8565203) B8565203
theorem B7613513 : Blo 2255435 7613513 := bstep (se 2 (by rfl) ⟨2855067, by rfl⟩ : syracuseStep 7613513 = 5710135) B5710135
theorem B5075675 : Blo 2255435 5075675 := bstep (se 1 (by rfl) ⟨3806756, by rfl⟩ : syracuseStep 5075675 = 7613513) B7613513
theorem B3383783 : Blo 2255435 3383783 := bstep (se 1 (by rfl) ⟨2537837, by rfl⟩ : syracuseStep 3383783 = 5075675) B5075675
theorem B2255855 : Blo 2255435 2255855 := bstep (se 1 (by rfl) ⟨1691891, by rfl⟩ : syracuseStep 2255855 = 3383783) B3383783
theorem B3383789 : Blo 2255435 3383789 := bbase (se 3 (by rfl) ⟨634460, by rfl⟩ : syracuseStep 3383789 = 1268921) (by norm_num)
theorem B2255859 : Blo 2255435 2255859 := bstep (se 1 (by rfl) ⟨1691894, by rfl⟩ : syracuseStep 2255859 = 3383789) B3383789
theorem B5075693 : Blo 2255435 5075693 := bbase (se 3 (by rfl) ⟨951692, by rfl⟩ : syracuseStep 5075693 = 1903385) (by norm_num)
theorem B3383795 : Blo 2255435 3383795 := bstep (se 1 (by rfl) ⟨2537846, by rfl⟩ : syracuseStep 3383795 = 5075693) B5075693
theorem B2255863 : Blo 2255435 2255863 := bstep (se 1 (by rfl) ⟨1691897, by rfl⟩ : syracuseStep 2255863 = 3383795) B3383795
theorem B2408977 : Blo 2255435 2408977 := bbase (se 2 (by rfl) ⟨903366, by rfl⟩ : syracuseStep 2408977 = 1806733) (by norm_num)
theorem B3211969 : Blo 2255435 3211969 := bstep (se 2 (by rfl) ⟨1204488, by rfl⟩ : syracuseStep 3211969 = 2408977) B2408977
theorem B4282625 : Blo 2255435 4282625 := bstep (se 2 (by rfl) ⟨1605984, by rfl⟩ : syracuseStep 4282625 = 3211969) B3211969
theorem B2855083 : Blo 2255435 2855083 := bstep (se 1 (by rfl) ⟨2141312, by rfl⟩ : syracuseStep 2855083 = 4282625) B4282625
theorem B3806777 : Blo 2255435 3806777 := bstep (se 2 (by rfl) ⟨1427541, by rfl⟩ : syracuseStep 3806777 = 2855083) B2855083
theorem B2537851 : Blo 2255435 2537851 := bstep (se 1 (by rfl) ⟨1903388, by rfl⟩ : syracuseStep 2537851 = 3806777) B3806777
theorem B3383801 : Blo 2255435 3383801 := bstep (se 2 (by rfl) ⟨1268925, by rfl⟩ : syracuseStep 3383801 = 2537851) B2537851
theorem B2255867 : Blo 2255435 2255867 := bstep (se 1 (by rfl) ⟨1691900, by rfl⟩ : syracuseStep 2255867 = 3383801) B3383801
theorem B56387285 : Blo 2255435 56387285 := bbase (se 7 (by rfl) ⟨660788, by rfl⟩ : syracuseStep 56387285 = 1321577) (by norm_num)
theorem B37591523 : Blo 2255435 37591523 := bstep (se 1 (by rfl) ⟨28193642, by rfl⟩ : syracuseStep 37591523 = 56387285) B56387285
theorem B25061015 : Blo 2255435 25061015 := bstep (se 1 (by rfl) ⟨18795761, by rfl⟩ : syracuseStep 25061015 = 37591523) B37591523
theorem B66829373 : Blo 2255435 66829373 := bstep (se 3 (by rfl) ⟨12530507, by rfl⟩ : syracuseStep 66829373 = 25061015) B25061015
theorem B44552915 : Blo 2255435 44552915 := bstep (se 1 (by rfl) ⟨33414686, by rfl⟩ : syracuseStep 44552915 = 66829373) B66829373
theorem B29701943 : Blo 2255435 29701943 := bstep (se 1 (by rfl) ⟨22276457, by rfl⟩ : syracuseStep 29701943 = 44552915) B44552915
theorem B19801295 : Blo 2255435 19801295 := bstep (se 1 (by rfl) ⟨14850971, by rfl⟩ : syracuseStep 19801295 = 29701943) B29701943
theorem B13200863 : Blo 2255435 13200863 := bstep (se 1 (by rfl) ⟨9900647, by rfl⟩ : syracuseStep 13200863 = 19801295) B19801295
theorem B140809205 : Blo 2255435 140809205 := bstep (se 5 (by rfl) ⟨6600431, by rfl⟩ : syracuseStep 140809205 = 13200863) B13200863
theorem B93872803 : Blo 2255435 93872803 := bstep (se 1 (by rfl) ⟨70404602, by rfl⟩ : syracuseStep 93872803 = 140809205) B140809205
theorem B125163737 : Blo 2255435 125163737 := bstep (se 2 (by rfl) ⟨46936401, by rfl⟩ : syracuseStep 125163737 = 93872803) B93872803
theorem B83442491 : Blo 2255435 83442491 := bstep (se 1 (by rfl) ⟨62581868, by rfl⟩ : syracuseStep 83442491 = 125163737) B125163737
theorem B55628327 : Blo 2255435 55628327 := bstep (se 1 (by rfl) ⟨41721245, by rfl⟩ : syracuseStep 55628327 = 83442491) B83442491
theorem B148342205 : Blo 2255435 148342205 := bstep (se 3 (by rfl) ⟨27814163, by rfl⟩ : syracuseStep 148342205 = 55628327) B55628327
theorem B98894803 : Blo 2255435 98894803 := bstep (se 1 (by rfl) ⟨74171102, by rfl⟩ : syracuseStep 98894803 = 148342205) B148342205
theorem B131859737 : Blo 2255435 131859737 := bstep (se 2 (by rfl) ⟨49447401, by rfl⟩ : syracuseStep 131859737 = 98894803) B98894803
theorem B87906491 : Blo 2255435 87906491 := bstep (se 1 (by rfl) ⟨65929868, by rfl⟩ : syracuseStep 87906491 = 131859737) B131859737
theorem B58604327 : Blo 2255435 58604327 := bstep (se 1 (by rfl) ⟨43953245, by rfl⟩ : syracuseStep 58604327 = 87906491) B87906491
theorem B39069551 : Blo 2255435 39069551 := bstep (se 1 (by rfl) ⟨29302163, by rfl⟩ : syracuseStep 39069551 = 58604327) B58604327
theorem B26046367 : Blo 2255435 26046367 := bstep (se 1 (by rfl) ⟨19534775, by rfl⟩ : syracuseStep 26046367 = 39069551) B39069551
theorem B138913957 : Blo 2255435 138913957 := bstep (se 4 (by rfl) ⟨13023183, by rfl⟩ : syracuseStep 138913957 = 26046367) B26046367
theorem B185218609 : Blo 2255435 185218609 := bstep (se 2 (by rfl) ⟨69456978, by rfl⟩ : syracuseStep 185218609 = 138913957) B138913957
theorem B246958145 : Blo 2255435 246958145 := bstep (se 2 (by rfl) ⟨92609304, by rfl⟩ : syracuseStep 246958145 = 185218609) B185218609
theorem B164638763 : Blo 2255435 164638763 := bstep (se 1 (by rfl) ⟨123479072, by rfl⟩ : syracuseStep 164638763 = 246958145) B246958145
theorem B109759175 : Blo 2255435 109759175 := bstep (se 1 (by rfl) ⟨82319381, by rfl⟩ : syracuseStep 109759175 = 164638763) B164638763
theorem B73172783 : Blo 2255435 73172783 := bstep (se 1 (by rfl) ⟨54879587, by rfl⟩ : syracuseStep 73172783 = 109759175) B109759175
theorem B48781855 : Blo 2255435 48781855 := bstep (se 1 (by rfl) ⟨36586391, by rfl⟩ : syracuseStep 48781855 = 73172783) B73172783
theorem B65042473 : Blo 2255435 65042473 := bstep (se 2 (by rfl) ⟨24390927, by rfl⟩ : syracuseStep 65042473 = 48781855) B48781855
theorem B86723297 : Blo 2255435 86723297 := bstep (se 2 (by rfl) ⟨32521236, by rfl⟩ : syracuseStep 86723297 = 65042473) B65042473
theorem B57815531 : Blo 2255435 57815531 := bstep (se 1 (by rfl) ⟨43361648, by rfl⟩ : syracuseStep 57815531 = 86723297) B86723297
theorem B38543687 : Blo 2255435 38543687 := bstep (se 1 (by rfl) ⟨28907765, by rfl⟩ : syracuseStep 38543687 = 57815531) B57815531
theorem B25695791 : Blo 2255435 25695791 := bstep (se 1 (by rfl) ⟨19271843, by rfl⟩ : syracuseStep 25695791 = 38543687) B38543687
theorem B17130527 : Blo 2255435 17130527 := bstep (se 1 (by rfl) ⟨12847895, by rfl⟩ : syracuseStep 17130527 = 25695791) B25695791
theorem B11420351 : Blo 2255435 11420351 := bstep (se 1 (by rfl) ⟨8565263, by rfl⟩ : syracuseStep 11420351 = 17130527) B17130527
theorem B7613567 : Blo 2255435 7613567 := bstep (se 1 (by rfl) ⟨5710175, by rfl⟩ : syracuseStep 7613567 = 11420351) B11420351
theorem B5075711 : Blo 2255435 5075711 := bstep (se 1 (by rfl) ⟨3806783, by rfl⟩ : syracuseStep 5075711 = 7613567) B7613567
theorem B3383807 : Blo 2255435 3383807 := bstep (se 1 (by rfl) ⟨2537855, by rfl⟩ : syracuseStep 3383807 = 5075711) B5075711
theorem B2255871 : Blo 2255435 2255871 := bstep (se 1 (by rfl) ⟨1691903, by rfl⟩ : syracuseStep 2255871 = 3383807) B3383807
theorem B3383813 : Blo 2255435 3383813 := bbase (se 4 (by rfl) ⟨317232, by rfl⟩ : syracuseStep 3383813 = 634465) (by norm_num)
theorem B2255875 : Blo 2255435 2255875 := bstep (se 1 (by rfl) ⟨1691906, by rfl⟩ : syracuseStep 2255875 = 3383813) B3383813
theorem B3806797 : Blo 2255435 3806797 := bbase (se 3 (by rfl) ⟨713774, by rfl⟩ : syracuseStep 3806797 = 1427549) (by norm_num)
theorem B5075729 : Blo 2255435 5075729 := bstep (se 2 (by rfl) ⟨1903398, by rfl⟩ : syracuseStep 5075729 = 3806797) B3806797
theorem B3383819 : Blo 2255435 3383819 := bstep (se 1 (by rfl) ⟨2537864, by rfl⟩ : syracuseStep 3383819 = 5075729) B5075729
theorem B2255879 : Blo 2255435 2255879 := bstep (se 1 (by rfl) ⟨1691909, by rfl⟩ : syracuseStep 2255879 = 3383819) B3383819
theorem B2537869 : Blo 2255435 2537869 := bbase (se 3 (by rfl) ⟨475850, by rfl⟩ : syracuseStep 2537869 = 951701) (by norm_num)
theorem B3383825 : Blo 2255435 3383825 := bstep (se 2 (by rfl) ⟨1268934, by rfl⟩ : syracuseStep 3383825 = 2537869) B2537869
theorem B2255883 : Blo 2255435 2255883 := bstep (se 1 (by rfl) ⟨1691912, by rfl⟩ : syracuseStep 2255883 = 3383825) B3383825
theorem B7613621 : Blo 2255435 7613621 := bbase (se 5 (by rfl) ⟨356888, by rfl⟩ : syracuseStep 7613621 = 713777) (by norm_num)
theorem B5075747 : Blo 2255435 5075747 := bstep (se 1 (by rfl) ⟨3806810, by rfl⟩ : syracuseStep 5075747 = 7613621) B7613621
theorem B3383831 : Blo 2255435 3383831 := bstep (se 1 (by rfl) ⟨2537873, by rfl⟩ : syracuseStep 3383831 = 5075747) B5075747
theorem B2255887 : Blo 2255435 2255887 := bstep (se 1 (by rfl) ⟨1691915, by rfl⟩ : syracuseStep 2255887 = 3383831) B3383831
theorem B3383837 : Blo 2255435 3383837 := bbase (se 3 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 3383837 = 1268939) (by norm_num)
theorem B2255891 : Blo 2255435 2255891 := bstep (se 1 (by rfl) ⟨1691918, by rfl⟩ : syracuseStep 2255891 = 3383837) B3383837
theorem B5075765 : Blo 2255435 5075765 := bbase (se 5 (by rfl) ⟨237926, by rfl⟩ : syracuseStep 5075765 = 475853) (by norm_num)
theorem B3383843 : Blo 2255435 3383843 := bstep (se 1 (by rfl) ⟨2537882, by rfl⟩ : syracuseStep 3383843 = 5075765) B5075765
theorem B2255895 : Blo 2255435 2255895 := bstep (se 1 (by rfl) ⟨1691921, by rfl⟩ : syracuseStep 2255895 = 3383843) B3383843
theorem B10840549 : Blo 2255435 10840549 := bbase (se 4 (by rfl) ⟨1016301, by rfl⟩ : syracuseStep 10840549 = 2032603) (by norm_num)
theorem B14454065 : Blo 2255435 14454065 := bstep (se 2 (by rfl) ⟨5420274, by rfl⟩ : syracuseStep 14454065 = 10840549) B10840549
theorem B9636043 : Blo 2255435 9636043 := bstep (se 1 (by rfl) ⟨7227032, by rfl⟩ : syracuseStep 9636043 = 14454065) B14454065
theorem B12848057 : Blo 2255435 12848057 := bstep (se 2 (by rfl) ⟨4818021, by rfl⟩ : syracuseStep 12848057 = 9636043) B9636043
theorem B8565371 : Blo 2255435 8565371 := bstep (se 1 (by rfl) ⟨6424028, by rfl⟩ : syracuseStep 8565371 = 12848057) B12848057
theorem B5710247 : Blo 2255435 5710247 := bstep (se 1 (by rfl) ⟨4282685, by rfl⟩ : syracuseStep 5710247 = 8565371) B8565371
theorem B3806831 : Blo 2255435 3806831 := bstep (se 1 (by rfl) ⟨2855123, by rfl⟩ : syracuseStep 3806831 = 5710247) B5710247
theorem B2537887 : Blo 2255435 2537887 := bstep (se 1 (by rfl) ⟨1903415, by rfl⟩ : syracuseStep 2537887 = 3806831) B3806831
theorem B3383849 : Blo 2255435 3383849 := bstep (se 2 (by rfl) ⟨1268943, by rfl⟩ : syracuseStep 3383849 = 2537887) B2537887
theorem B2255899 : Blo 2255435 2255899 := bstep (se 1 (by rfl) ⟨1691924, by rfl⟩ : syracuseStep 2255899 = 3383849) B3383849
theorem B23152661 : Blo 2255435 23152661 := bbase (se 6 (by rfl) ⟨542640, by rfl⟩ : syracuseStep 23152661 = 1085281) (by norm_num)
theorem B15435107 : Blo 2255435 15435107 := bstep (se 1 (by rfl) ⟨11576330, by rfl⟩ : syracuseStep 15435107 = 23152661) B23152661
theorem B10290071 : Blo 2255435 10290071 := bstep (se 1 (by rfl) ⟨7717553, by rfl⟩ : syracuseStep 10290071 = 15435107) B15435107
theorem B6860047 : Blo 2255435 6860047 := bstep (se 1 (by rfl) ⟨5145035, by rfl⟩ : syracuseStep 6860047 = 10290071) B10290071
theorem B9146729 : Blo 2255435 9146729 := bstep (se 2 (by rfl) ⟨3430023, by rfl⟩ : syracuseStep 9146729 = 6860047) B6860047
theorem B24391277 : Blo 2255435 24391277 := bstep (se 3 (by rfl) ⟨4573364, by rfl⟩ : syracuseStep 24391277 = 9146729) B9146729
theorem B16260851 : Blo 2255435 16260851 := bstep (se 1 (by rfl) ⟨12195638, by rfl⟩ : syracuseStep 16260851 = 24391277) B24391277
theorem B10840567 : Blo 2255435 10840567 := bstep (se 1 (by rfl) ⟨8130425, by rfl⟩ : syracuseStep 10840567 = 16260851) B16260851
theorem B14454089 : Blo 2255435 14454089 := bstep (se 2 (by rfl) ⟨5420283, by rfl⟩ : syracuseStep 14454089 = 10840567) B10840567
theorem B9636059 : Blo 2255435 9636059 := bstep (se 1 (by rfl) ⟨7227044, by rfl⟩ : syracuseStep 9636059 = 14454089) B14454089
theorem B6424039 : Blo 2255435 6424039 := bstep (se 1 (by rfl) ⟨4818029, by rfl⟩ : syracuseStep 6424039 = 9636059) B9636059
theorem B8565385 : Blo 2255435 8565385 := bstep (se 2 (by rfl) ⟨3212019, by rfl⟩ : syracuseStep 8565385 = 6424039) B6424039
theorem B11420513 : Blo 2255435 11420513 := bstep (se 2 (by rfl) ⟨4282692, by rfl⟩ : syracuseStep 11420513 = 8565385) B8565385
theorem B7613675 : Blo 2255435 7613675 := bstep (se 1 (by rfl) ⟨5710256, by rfl⟩ : syracuseStep 7613675 = 11420513) B11420513
theorem B5075783 : Blo 2255435 5075783 := bstep (se 1 (by rfl) ⟨3806837, by rfl⟩ : syracuseStep 5075783 = 7613675) B7613675
theorem B3383855 : Blo 2255435 3383855 := bstep (se 1 (by rfl) ⟨2537891, by rfl⟩ : syracuseStep 3383855 = 5075783) B5075783
theorem B2255903 : Blo 2255435 2255903 := bstep (se 1 (by rfl) ⟨1691927, by rfl⟩ : syracuseStep 2255903 = 3383855) B3383855
theorem B3383861 : Blo 2255435 3383861 := bbase (se 5 (by rfl) ⟨158618, by rfl⟩ : syracuseStep 3383861 = 317237) (by norm_num)
theorem B2255907 : Blo 2255435 2255907 := bstep (se 1 (by rfl) ⟨1691930, by rfl⟩ : syracuseStep 2255907 = 3383861) B3383861
theorem B5710277 : Blo 2255435 5710277 := bbase (se 4 (by rfl) ⟨535338, by rfl⟩ : syracuseStep 5710277 = 1070677) (by norm_num)
theorem B3806851 : Blo 2255435 3806851 := bstep (se 1 (by rfl) ⟨2855138, by rfl⟩ : syracuseStep 3806851 = 5710277) B5710277
theorem B5075801 : Blo 2255435 5075801 := bstep (se 2 (by rfl) ⟨1903425, by rfl⟩ : syracuseStep 5075801 = 3806851) B3806851
theorem B3383867 : Blo 2255435 3383867 := bstep (se 1 (by rfl) ⟨2537900, by rfl⟩ : syracuseStep 3383867 = 5075801) B5075801
theorem B2255911 : Blo 2255435 2255911 := bstep (se 1 (by rfl) ⟨1691933, by rfl⟩ : syracuseStep 2255911 = 3383867) B3383867
theorem B2537905 : Blo 2255435 2537905 := bbase (se 2 (by rfl) ⟨951714, by rfl⟩ : syracuseStep 2537905 = 1903429) (by norm_num)
theorem B3383873 : Blo 2255435 3383873 := bstep (se 2 (by rfl) ⟨1268952, by rfl⟩ : syracuseStep 3383873 = 2537905) B2537905
theorem B2255915 : Blo 2255435 2255915 := bstep (se 1 (by rfl) ⟨1691936, by rfl⟩ : syracuseStep 2255915 = 3383873) B3383873
theorem B6424085 : Blo 2255435 6424085 := bbase (se 6 (by rfl) ⟨150564, by rfl⟩ : syracuseStep 6424085 = 301129) (by norm_num)
theorem B4282723 : Blo 2255435 4282723 := bstep (se 1 (by rfl) ⟨3212042, by rfl⟩ : syracuseStep 4282723 = 6424085) B6424085
theorem B5710297 : Blo 2255435 5710297 := bstep (se 2 (by rfl) ⟨2141361, by rfl⟩ : syracuseStep 5710297 = 4282723) B4282723
theorem B7613729 : Blo 2255435 7613729 := bstep (se 2 (by rfl) ⟨2855148, by rfl⟩ : syracuseStep 7613729 = 5710297) B5710297
theorem B5075819 : Blo 2255435 5075819 := bstep (se 1 (by rfl) ⟨3806864, by rfl⟩ : syracuseStep 5075819 = 7613729) B7613729
theorem B3383879 : Blo 2255435 3383879 := bstep (se 1 (by rfl) ⟨2537909, by rfl⟩ : syracuseStep 3383879 = 5075819) B5075819
theorem B2255919 : Blo 2255435 2255919 := bstep (se 1 (by rfl) ⟨1691939, by rfl⟩ : syracuseStep 2255919 = 3383879) B3383879
theorem B3383885 : Blo 2255435 3383885 := bbase (se 3 (by rfl) ⟨634478, by rfl⟩ : syracuseStep 3383885 = 1268957) (by norm_num)
theorem B2255923 : Blo 2255435 2255923 := bstep (se 1 (by rfl) ⟨1691942, by rfl⟩ : syracuseStep 2255923 = 3383885) B3383885
theorem B5075837 : Blo 2255435 5075837 := bbase (se 3 (by rfl) ⟨951719, by rfl⟩ : syracuseStep 5075837 = 1903439) (by norm_num)
theorem B3383891 : Blo 2255435 3383891 := bstep (se 1 (by rfl) ⟨2537918, by rfl⟩ : syracuseStep 3383891 = 5075837) B5075837
theorem B2255927 : Blo 2255435 2255927 := bstep (se 1 (by rfl) ⟨1691945, by rfl⟩ : syracuseStep 2255927 = 3383891) B3383891
theorem B3806885 : Blo 2255435 3806885 := bbase (se 4 (by rfl) ⟨356895, by rfl⟩ : syracuseStep 3806885 = 713791) (by norm_num)
theorem B2537923 : Blo 2255435 2537923 := bstep (se 1 (by rfl) ⟨1903442, by rfl⟩ : syracuseStep 2537923 = 3806885) B3806885
theorem B3383897 : Blo 2255435 3383897 := bstep (se 2 (by rfl) ⟨1268961, by rfl⟩ : syracuseStep 3383897 = 2537923) B2537923
theorem B2255931 : Blo 2255435 2255931 := bstep (se 1 (by rfl) ⟨1691948, by rfl⟩ : syracuseStep 2255931 = 3383897) B3383897
theorem B2409049 : Blo 2255435 2409049 := bbase (se 2 (by rfl) ⟨903393, by rfl⟩ : syracuseStep 2409049 = 1806787) (by norm_num)
theorem B3212065 : Blo 2255435 3212065 := bstep (se 2 (by rfl) ⟨1204524, by rfl⟩ : syracuseStep 3212065 = 2409049) B2409049
theorem B17131013 : Blo 2255435 17131013 := bstep (se 4 (by rfl) ⟨1606032, by rfl⟩ : syracuseStep 17131013 = 3212065) B3212065
theorem B11420675 : Blo 2255435 11420675 := bstep (se 1 (by rfl) ⟨8565506, by rfl⟩ : syracuseStep 11420675 = 17131013) B17131013
theorem B7613783 : Blo 2255435 7613783 := bstep (se 1 (by rfl) ⟨5710337, by rfl⟩ : syracuseStep 7613783 = 11420675) B11420675
theorem B5075855 : Blo 2255435 5075855 := bstep (se 1 (by rfl) ⟨3806891, by rfl⟩ : syracuseStep 5075855 = 7613783) B7613783
theorem B3383903 : Blo 2255435 3383903 := bstep (se 1 (by rfl) ⟨2537927, by rfl⟩ : syracuseStep 3383903 = 5075855) B5075855
theorem B2255935 : Blo 2255435 2255935 := bstep (se 1 (by rfl) ⟨1691951, by rfl⟩ : syracuseStep 2255935 = 3383903) B3383903
theorem B3383909 : Blo 2255435 3383909 := bbase (se 4 (by rfl) ⟨317241, by rfl⟩ : syracuseStep 3383909 = 634483) (by norm_num)
theorem B2255939 : Blo 2255435 2255939 := bstep (se 1 (by rfl) ⟨1691954, by rfl⟩ : syracuseStep 2255939 = 3383909) B3383909
theorem B3212077 : Blo 2255435 3212077 := bbase (se 3 (by rfl) ⟨602264, by rfl⟩ : syracuseStep 3212077 = 1204529) (by norm_num)
theorem B4282769 : Blo 2255435 4282769 := bstep (se 2 (by rfl) ⟨1606038, by rfl⟩ : syracuseStep 4282769 = 3212077) B3212077
theorem B2855179 : Blo 2255435 2855179 := bstep (se 1 (by rfl) ⟨2141384, by rfl⟩ : syracuseStep 2855179 = 4282769) B4282769
theorem B3806905 : Blo 2255435 3806905 := bstep (se 2 (by rfl) ⟨1427589, by rfl⟩ : syracuseStep 3806905 = 2855179) B2855179
theorem B5075873 : Blo 2255435 5075873 := bstep (se 2 (by rfl) ⟨1903452, by rfl⟩ : syracuseStep 5075873 = 3806905) B3806905
theorem B3383915 : Blo 2255435 3383915 := bstep (se 1 (by rfl) ⟨2537936, by rfl⟩ : syracuseStep 3383915 = 5075873) B5075873
theorem B2255943 : Blo 2255435 2255943 := bstep (se 1 (by rfl) ⟨1691957, by rfl⟩ : syracuseStep 2255943 = 3383915) B3383915
theorem B2537941 : Blo 2255435 2537941 := bbase (se 7 (by rfl) ⟨29741, by rfl⟩ : syracuseStep 2537941 = 59483) (by norm_num)
theorem B3383921 : Blo 2255435 3383921 := bstep (se 2 (by rfl) ⟨1268970, by rfl⟩ : syracuseStep 3383921 = 2537941) B2537941
theorem B2255947 : Blo 2255435 2255947 := bstep (se 1 (by rfl) ⟨1691960, by rfl⟩ : syracuseStep 2255947 = 3383921) B3383921
theorem B2855189 : Blo 2255435 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B7613837 : Blo 2255435 7613837 := bstep (se 3 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 7613837 = 2855189) B2855189
theorem B5075891 : Blo 2255435 5075891 := bstep (se 1 (by rfl) ⟨3806918, by rfl⟩ : syracuseStep 5075891 = 7613837) B7613837
theorem B3383927 : Blo 2255435 3383927 := bstep (se 1 (by rfl) ⟨2537945, by rfl⟩ : syracuseStep 3383927 = 5075891) B5075891
theorem B2255951 : Blo 2255435 2255951 := bstep (se 1 (by rfl) ⟨1691963, by rfl⟩ : syracuseStep 2255951 = 3383927) B3383927
theorem B3383933 : Blo 2255435 3383933 := bbase (se 3 (by rfl) ⟨634487, by rfl⟩ : syracuseStep 3383933 = 1268975) (by norm_num)
theorem B2255955 : Blo 2255435 2255955 := bstep (se 1 (by rfl) ⟨1691966, by rfl⟩ : syracuseStep 2255955 = 3383933) B3383933
theorem B5075909 : Blo 2255435 5075909 := bbase (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) (by norm_num)
theorem B3383939 : Blo 2255435 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B2255959 : Blo 2255435 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B5420429 : Blo 2255435 5420429 := bbase (se 3 (by rfl) ⟨1016330, by rfl⟩ : syracuseStep 5420429 = 2032661) (by norm_num)
theorem B3613619 : Blo 2255435 3613619 := bstep (se 1 (by rfl) ⟨2710214, by rfl⟩ : syracuseStep 3613619 = 5420429) B5420429
theorem B9636317 : Blo 2255435 9636317 := bstep (se 3 (by rfl) ⟨1806809, by rfl⟩ : syracuseStep 9636317 = 3613619) B3613619
theorem B6424211 : Blo 2255435 6424211 := bstep (se 1 (by rfl) ⟨4818158, by rfl⟩ : syracuseStep 6424211 = 9636317) B9636317
theorem B4282807 : Blo 2255435 4282807 := bstep (se 1 (by rfl) ⟨3212105, by rfl⟩ : syracuseStep 4282807 = 6424211) B6424211
theorem B5710409 : Blo 2255435 5710409 := bstep (se 2 (by rfl) ⟨2141403, by rfl⟩ : syracuseStep 5710409 = 4282807) B4282807
theorem B3806939 : Blo 2255435 3806939 := bstep (se 1 (by rfl) ⟨2855204, by rfl⟩ : syracuseStep 3806939 = 5710409) B5710409
theorem B2537959 : Blo 2255435 2537959 := bstep (se 1 (by rfl) ⟨1903469, by rfl⟩ : syracuseStep 2537959 = 3806939) B3806939
theorem B3383945 : Blo 2255435 3383945 := bstep (se 2 (by rfl) ⟨1268979, by rfl⟩ : syracuseStep 3383945 = 2537959) B2537959
theorem B2255963 : Blo 2255435 2255963 := bstep (se 1 (by rfl) ⟨1691972, by rfl⟩ : syracuseStep 2255963 = 3383945) B3383945
theorem B11420837 : Blo 2255435 11420837 := bbase (se 4 (by rfl) ⟨1070703, by rfl⟩ : syracuseStep 11420837 = 2141407) (by norm_num)
theorem B7613891 : Blo 2255435 7613891 := bstep (se 1 (by rfl) ⟨5710418, by rfl⟩ : syracuseStep 7613891 = 11420837) B11420837
theorem B5075927 : Blo 2255435 5075927 := bstep (se 1 (by rfl) ⟨3806945, by rfl⟩ : syracuseStep 5075927 = 7613891) B7613891
theorem B3383951 : Blo 2255435 3383951 := bstep (se 1 (by rfl) ⟨2537963, by rfl⟩ : syracuseStep 3383951 = 5075927) B5075927
theorem B2255967 : Blo 2255435 2255967 := bstep (se 1 (by rfl) ⟨1691975, by rfl⟩ : syracuseStep 2255967 = 3383951) B3383951
theorem B3383957 : Blo 2255435 3383957 := bbase (se 6 (by rfl) ⟨79311, by rfl⟩ : syracuseStep 3383957 = 158623) (by norm_num)
theorem B2255971 : Blo 2255435 2255971 := bstep (se 1 (by rfl) ⟨1691978, by rfl⟩ : syracuseStep 2255971 = 3383957) B3383957
theorem B28194965 : Blo 2255435 28194965 := bbase (se 6 (by rfl) ⟨660819, by rfl⟩ : syracuseStep 28194965 = 1321639) (by norm_num)
theorem B18796643 : Blo 2255435 18796643 := bstep (se 1 (by rfl) ⟨14097482, by rfl⟩ : syracuseStep 18796643 = 28194965) B28194965
theorem B12531095 : Blo 2255435 12531095 := bstep (se 1 (by rfl) ⟨9398321, by rfl⟩ : syracuseStep 12531095 = 18796643) B18796643
theorem B8354063 : Blo 2255435 8354063 := bstep (se 1 (by rfl) ⟨6265547, by rfl⟩ : syracuseStep 8354063 = 12531095) B12531095
theorem B22277501 : Blo 2255435 22277501 := bstep (se 3 (by rfl) ⟨4177031, by rfl⟩ : syracuseStep 22277501 = 8354063) B8354063
theorem B14851667 : Blo 2255435 14851667 := bstep (se 1 (by rfl) ⟨11138750, by rfl⟩ : syracuseStep 14851667 = 22277501) B22277501
theorem B9901111 : Blo 2255435 9901111 := bstep (se 1 (by rfl) ⟨7425833, by rfl⟩ : syracuseStep 9901111 = 14851667) B14851667
theorem B13201481 : Blo 2255435 13201481 := bstep (se 2 (by rfl) ⟨4950555, by rfl⟩ : syracuseStep 13201481 = 9901111) B9901111
theorem B8800987 : Blo 2255435 8800987 := bstep (se 1 (by rfl) ⟨6600740, by rfl⟩ : syracuseStep 8800987 = 13201481) B13201481
theorem B11734649 : Blo 2255435 11734649 := bstep (se 2 (by rfl) ⟨4400493, by rfl⟩ : syracuseStep 11734649 = 8800987) B8800987
theorem B7823099 : Blo 2255435 7823099 := bstep (se 1 (by rfl) ⟨5867324, by rfl⟩ : syracuseStep 7823099 = 11734649) B11734649
theorem B20861597 : Blo 2255435 20861597 := bstep (se 3 (by rfl) ⟨3911549, by rfl⟩ : syracuseStep 20861597 = 7823099) B7823099
theorem B55630925 : Blo 2255435 55630925 := bstep (se 3 (by rfl) ⟨10430798, by rfl⟩ : syracuseStep 55630925 = 20861597) B20861597
theorem B37087283 : Blo 2255435 37087283 := bstep (se 1 (by rfl) ⟨27815462, by rfl⟩ : syracuseStep 37087283 = 55630925) B55630925
theorem B24724855 : Blo 2255435 24724855 := bstep (se 1 (by rfl) ⟨18543641, by rfl⟩ : syracuseStep 24724855 = 37087283) B37087283
theorem B32966473 : Blo 2255435 32966473 := bstep (se 2 (by rfl) ⟨12362427, by rfl⟩ : syracuseStep 32966473 = 24724855) B24724855
theorem B43955297 : Blo 2255435 43955297 := bstep (se 2 (by rfl) ⟨16483236, by rfl⟩ : syracuseStep 43955297 = 32966473) B32966473
theorem B29303531 : Blo 2255435 29303531 := bstep (se 1 (by rfl) ⟨21977648, by rfl⟩ : syracuseStep 29303531 = 43955297) B43955297
theorem B19535687 : Blo 2255435 19535687 := bstep (se 1 (by rfl) ⟨14651765, by rfl⟩ : syracuseStep 19535687 = 29303531) B29303531
theorem B13023791 : Blo 2255435 13023791 := bstep (se 1 (by rfl) ⟨9767843, by rfl⟩ : syracuseStep 13023791 = 19535687) B19535687
theorem B8682527 : Blo 2255435 8682527 := bstep (se 1 (by rfl) ⟨6511895, by rfl⟩ : syracuseStep 8682527 = 13023791) B13023791
theorem B5788351 : Blo 2255435 5788351 := bstep (se 1 (by rfl) ⟨4341263, by rfl⟩ : syracuseStep 5788351 = 8682527) B8682527
theorem B7717801 : Blo 2255435 7717801 := bstep (se 2 (by rfl) ⟨2894175, by rfl⟩ : syracuseStep 7717801 = 5788351) B5788351
theorem B10290401 : Blo 2255435 10290401 := bstep (se 2 (by rfl) ⟨3858900, by rfl⟩ : syracuseStep 10290401 = 7717801) B7717801
theorem B6860267 : Blo 2255435 6860267 := bstep (se 1 (by rfl) ⟨5145200, by rfl⟩ : syracuseStep 6860267 = 10290401) B10290401
theorem B4573511 : Blo 2255435 4573511 := bstep (se 1 (by rfl) ⟨3430133, by rfl⟩ : syracuseStep 4573511 = 6860267) B6860267
theorem B3049007 : Blo 2255435 3049007 := bstep (se 1 (by rfl) ⟨2286755, by rfl⟩ : syracuseStep 3049007 = 4573511) B4573511
theorem B32522741 : Blo 2255435 32522741 := bstep (se 5 (by rfl) ⟨1524503, by rfl⟩ : syracuseStep 32522741 = 3049007) B3049007
theorem B21681827 : Blo 2255435 21681827 := bstep (se 1 (by rfl) ⟨16261370, by rfl⟩ : syracuseStep 21681827 = 32522741) B32522741
theorem B14454551 : Blo 2255435 14454551 := bstep (se 1 (by rfl) ⟨10840913, by rfl⟩ : syracuseStep 14454551 = 21681827) B21681827
theorem B9636367 : Blo 2255435 9636367 := bstep (se 1 (by rfl) ⟨7227275, by rfl⟩ : syracuseStep 9636367 = 14454551) B14454551
theorem B12848489 : Blo 2255435 12848489 := bstep (se 2 (by rfl) ⟨4818183, by rfl⟩ : syracuseStep 12848489 = 9636367) B9636367
theorem B8565659 : Blo 2255435 8565659 := bstep (se 1 (by rfl) ⟨6424244, by rfl⟩ : syracuseStep 8565659 = 12848489) B12848489
theorem B5710439 : Blo 2255435 5710439 := bstep (se 1 (by rfl) ⟨4282829, by rfl⟩ : syracuseStep 5710439 = 8565659) B8565659
theorem B3806959 : Blo 2255435 3806959 := bstep (se 1 (by rfl) ⟨2855219, by rfl⟩ : syracuseStep 3806959 = 5710439) B5710439
theorem B5075945 : Blo 2255435 5075945 := bstep (se 2 (by rfl) ⟨1903479, by rfl⟩ : syracuseStep 5075945 = 3806959) B3806959
theorem B3383963 : Blo 2255435 3383963 := bstep (se 1 (by rfl) ⟨2537972, by rfl⟩ : syracuseStep 3383963 = 5075945) B5075945
theorem B2255975 : Blo 2255435 2255975 := bstep (se 1 (by rfl) ⟨1691981, by rfl⟩ : syracuseStep 2255975 = 3383963) B3383963
theorem B2537977 : Blo 2255435 2537977 := bbase (se 2 (by rfl) ⟨951741, by rfl⟩ : syracuseStep 2537977 = 1903483) (by norm_num)
theorem B3383969 : Blo 2255435 3383969 := bstep (se 2 (by rfl) ⟨1268988, by rfl⟩ : syracuseStep 3383969 = 2537977) B2537977
theorem B2255979 : Blo 2255435 2255979 := bstep (se 1 (by rfl) ⟨1691984, by rfl⟩ : syracuseStep 2255979 = 3383969) B3383969
theorem B7227301 : Blo 2255435 7227301 := bbase (se 4 (by rfl) ⟨677559, by rfl⟩ : syracuseStep 7227301 = 1355119) (by norm_num)
theorem B9636401 : Blo 2255435 9636401 := bstep (se 2 (by rfl) ⟨3613650, by rfl⟩ : syracuseStep 9636401 = 7227301) B7227301
theorem B6424267 : Blo 2255435 6424267 := bstep (se 1 (by rfl) ⟨4818200, by rfl⟩ : syracuseStep 6424267 = 9636401) B9636401
theorem B8565689 : Blo 2255435 8565689 := bstep (se 2 (by rfl) ⟨3212133, by rfl⟩ : syracuseStep 8565689 = 6424267) B6424267
theorem B5710459 : Blo 2255435 5710459 := bstep (se 1 (by rfl) ⟨4282844, by rfl⟩ : syracuseStep 5710459 = 8565689) B8565689
theorem B7613945 : Blo 2255435 7613945 := bstep (se 2 (by rfl) ⟨2855229, by rfl⟩ : syracuseStep 7613945 = 5710459) B5710459
theorem B5075963 : Blo 2255435 5075963 := bstep (se 1 (by rfl) ⟨3806972, by rfl⟩ : syracuseStep 5075963 = 7613945) B7613945
theorem B3383975 : Blo 2255435 3383975 := bstep (se 1 (by rfl) ⟨2537981, by rfl⟩ : syracuseStep 3383975 = 5075963) B5075963
theorem B2255983 : Blo 2255435 2255983 := bstep (se 1 (by rfl) ⟨1691987, by rfl⟩ : syracuseStep 2255983 = 3383975) B3383975
theorem B3383981 : Blo 2255435 3383981 := bbase (se 3 (by rfl) ⟨634496, by rfl⟩ : syracuseStep 3383981 = 1268993) (by norm_num)
theorem B2255987 : Blo 2255435 2255987 := bstep (se 1 (by rfl) ⟨1691990, by rfl⟩ : syracuseStep 2255987 = 3383981) B3383981
theorem B5075981 : Blo 2255435 5075981 := bbase (se 3 (by rfl) ⟨951746, by rfl⟩ : syracuseStep 5075981 = 1903493) (by norm_num)
theorem B3383987 : Blo 2255435 3383987 := bstep (se 1 (by rfl) ⟨2537990, by rfl⟩ : syracuseStep 3383987 = 5075981) B5075981
theorem B2255991 : Blo 2255435 2255991 := bstep (se 1 (by rfl) ⟨1691993, by rfl⟩ : syracuseStep 2255991 = 3383987) B3383987
theorem B2855245 : Blo 2255435 2855245 := bbase (se 3 (by rfl) ⟨535358, by rfl⟩ : syracuseStep 2855245 = 1070717) (by norm_num)
theorem B3806993 : Blo 2255435 3806993 := bstep (se 2 (by rfl) ⟨1427622, by rfl⟩ : syracuseStep 3806993 = 2855245) B2855245
theorem B2537995 : Blo 2255435 2537995 := bstep (se 1 (by rfl) ⟨1903496, by rfl⟩ : syracuseStep 2537995 = 3806993) B3806993
theorem B3383993 : Blo 2255435 3383993 := bstep (se 2 (by rfl) ⟨1268997, by rfl⟩ : syracuseStep 3383993 = 2537995) B2537995
theorem B2255995 : Blo 2255435 2255995 := bstep (se 1 (by rfl) ⟨1691996, by rfl⟩ : syracuseStep 2255995 = 3383993) B3383993
theorem B3858941 : Blo 2255435 3858941 := bbase (se 3 (by rfl) ⟨723551, by rfl⟩ : syracuseStep 3858941 = 1447103) (by norm_num)
theorem B2572627 : Blo 2255435 2572627 := bstep (se 1 (by rfl) ⟨1929470, by rfl⟩ : syracuseStep 2572627 = 3858941) B3858941
theorem B3430169 : Blo 2255435 3430169 := bstep (se 2 (by rfl) ⟨1286313, by rfl⟩ : syracuseStep 3430169 = 2572627) B2572627
theorem B36588469 : Blo 2255435 36588469 := bstep (se 5 (by rfl) ⟨1715084, by rfl⟩ : syracuseStep 36588469 = 3430169) B3430169
theorem B48784625 : Blo 2255435 48784625 := bstep (se 2 (by rfl) ⟨18294234, by rfl⟩ : syracuseStep 48784625 = 36588469) B36588469
theorem B32523083 : Blo 2255435 32523083 := bstep (se 1 (by rfl) ⟨24392312, by rfl⟩ : syracuseStep 32523083 = 48784625) B48784625
theorem B21682055 : Blo 2255435 21682055 := bstep (se 1 (by rfl) ⟨16261541, by rfl⟩ : syracuseStep 21682055 = 32523083) B32523083
theorem B14454703 : Blo 2255435 14454703 := bstep (se 1 (by rfl) ⟨10841027, by rfl⟩ : syracuseStep 14454703 = 21682055) B21682055
theorem B19272937 : Blo 2255435 19272937 := bstep (se 2 (by rfl) ⟨7227351, by rfl⟩ : syracuseStep 19272937 = 14454703) B14454703
theorem B25697249 : Blo 2255435 25697249 := bstep (se 2 (by rfl) ⟨9636468, by rfl⟩ : syracuseStep 25697249 = 19272937) B19272937
theorem B17131499 : Blo 2255435 17131499 := bstep (se 1 (by rfl) ⟨12848624, by rfl⟩ : syracuseStep 17131499 = 25697249) B25697249
theorem B11420999 : Blo 2255435 11420999 := bstep (se 1 (by rfl) ⟨8565749, by rfl⟩ : syracuseStep 11420999 = 17131499) B17131499
theorem B7613999 : Blo 2255435 7613999 := bstep (se 1 (by rfl) ⟨5710499, by rfl⟩ : syracuseStep 7613999 = 11420999) B11420999
theorem B5075999 : Blo 2255435 5075999 := bstep (se 1 (by rfl) ⟨3806999, by rfl⟩ : syracuseStep 5075999 = 7613999) B7613999
theorem B3383999 : Blo 2255435 3383999 := bstep (se 1 (by rfl) ⟨2537999, by rfl⟩ : syracuseStep 3383999 = 5075999) B5075999
theorem B2255999 : Blo 2255435 2255999 := bstep (se 1 (by rfl) ⟨1691999, by rfl⟩ : syracuseStep 2255999 = 3383999) B3383999
theorem B3384005 : Blo 2255435 3384005 := bbase (se 4 (by rfl) ⟨317250, by rfl⟩ : syracuseStep 3384005 = 634501) (by norm_num)
theorem B2256003 : Blo 2255435 2256003 := bstep (se 1 (by rfl) ⟨1692002, by rfl⟩ : syracuseStep 2256003 = 3384005) B3384005
theorem B3807013 : Blo 2255435 3807013 := bbase (se 4 (by rfl) ⟨356907, by rfl⟩ : syracuseStep 3807013 = 713815) (by norm_num)
theorem B5076017 : Blo 2255435 5076017 := bstep (se 2 (by rfl) ⟨1903506, by rfl⟩ : syracuseStep 5076017 = 3807013) B3807013
theorem B3384011 : Blo 2255435 3384011 := bstep (se 1 (by rfl) ⟨2538008, by rfl⟩ : syracuseStep 3384011 = 5076017) B5076017
theorem B2256007 : Blo 2255435 2256007 := bstep (se 1 (by rfl) ⟨1692005, by rfl⟩ : syracuseStep 2256007 = 3384011) B3384011
theorem B2538013 : Blo 2255435 2538013 := bbase (se 3 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 2538013 = 951755) (by norm_num)
theorem B3384017 : Blo 2255435 3384017 := bstep (se 2 (by rfl) ⟨1269006, by rfl⟩ : syracuseStep 3384017 = 2538013) B2538013
theorem B2256011 : Blo 2255435 2256011 := bstep (se 1 (by rfl) ⟨1692008, by rfl⟩ : syracuseStep 2256011 = 3384017) B3384017
theorem B7614053 : Blo 2255435 7614053 := bbase (se 4 (by rfl) ⟨713817, by rfl⟩ : syracuseStep 7614053 = 1427635) (by norm_num)
theorem B5076035 : Blo 2255435 5076035 := bstep (se 1 (by rfl) ⟨3807026, by rfl⟩ : syracuseStep 5076035 = 7614053) B7614053
theorem B3384023 : Blo 2255435 3384023 := bstep (se 1 (by rfl) ⟨2538017, by rfl⟩ : syracuseStep 3384023 = 5076035) B5076035
theorem B2256015 : Blo 2255435 2256015 := bstep (se 1 (by rfl) ⟨1692011, by rfl⟩ : syracuseStep 2256015 = 3384023) B3384023
theorem B3384029 : Blo 2255435 3384029 := bbase (se 3 (by rfl) ⟨634505, by rfl⟩ : syracuseStep 3384029 = 1269011) (by norm_num)
theorem B2256019 : Blo 2255435 2256019 := bstep (se 1 (by rfl) ⟨1692014, by rfl⟩ : syracuseStep 2256019 = 3384029) B3384029
theorem B5076053 : Blo 2255435 5076053 := bbase (se 8 (by rfl) ⟨29742, by rfl⟩ : syracuseStep 5076053 = 59485) (by norm_num)
theorem B3384035 : Blo 2255435 3384035 := bstep (se 1 (by rfl) ⟨2538026, by rfl⟩ : syracuseStep 3384035 = 5076053) B5076053
theorem B2256023 : Blo 2255435 2256023 := bstep (se 1 (by rfl) ⟨1692017, by rfl⟩ : syracuseStep 2256023 = 3384035) B3384035
theorem B4065437 : Blo 2255435 4065437 := bbase (se 3 (by rfl) ⟨762269, by rfl⟩ : syracuseStep 4065437 = 1524539) (by norm_num)
theorem B10841165 : Blo 2255435 10841165 := bstep (se 3 (by rfl) ⟨2032718, by rfl⟩ : syracuseStep 10841165 = 4065437) B4065437
theorem B7227443 : Blo 2255435 7227443 := bstep (se 1 (by rfl) ⟨5420582, by rfl⟩ : syracuseStep 7227443 = 10841165) B10841165
theorem B4818295 : Blo 2255435 4818295 := bstep (se 1 (by rfl) ⟨3613721, by rfl⟩ : syracuseStep 4818295 = 7227443) B7227443
theorem B6424393 : Blo 2255435 6424393 := bstep (se 2 (by rfl) ⟨2409147, by rfl⟩ : syracuseStep 6424393 = 4818295) B4818295
theorem B8565857 : Blo 2255435 8565857 := bstep (se 2 (by rfl) ⟨3212196, by rfl⟩ : syracuseStep 8565857 = 6424393) B6424393
theorem B5710571 : Blo 2255435 5710571 := bstep (se 1 (by rfl) ⟨4282928, by rfl⟩ : syracuseStep 5710571 = 8565857) B8565857
theorem B3807047 : Blo 2255435 3807047 := bstep (se 1 (by rfl) ⟨2855285, by rfl⟩ : syracuseStep 3807047 = 5710571) B5710571
theorem B2538031 : Blo 2255435 2538031 := bstep (se 1 (by rfl) ⟨1903523, by rfl⟩ : syracuseStep 2538031 = 3807047) B3807047
theorem B3384041 : Blo 2255435 3384041 := bstep (se 2 (by rfl) ⟨1269015, by rfl⟩ : syracuseStep 3384041 = 2538031) B2538031
theorem B2256027 : Blo 2255435 2256027 := bstep (se 1 (by rfl) ⟨1692020, by rfl⟩ : syracuseStep 2256027 = 3384041) B3384041
theorem B11139029 : Blo 2255435 11139029 := bbase (se 7 (by rfl) ⟨130535, by rfl⟩ : syracuseStep 11139029 = 261071) (by norm_num)
theorem B7426019 : Blo 2255435 7426019 := bstep (se 1 (by rfl) ⟨5569514, by rfl⟩ : syracuseStep 7426019 = 11139029) B11139029
theorem B19802717 : Blo 2255435 19802717 := bstep (se 3 (by rfl) ⟨3713009, by rfl⟩ : syracuseStep 19802717 = 7426019) B7426019
theorem B13201811 : Blo 2255435 13201811 := bstep (se 1 (by rfl) ⟨9901358, by rfl⟩ : syracuseStep 13201811 = 19802717) B19802717
theorem B8801207 : Blo 2255435 8801207 := bstep (se 1 (by rfl) ⟨6600905, by rfl⟩ : syracuseStep 8801207 = 13201811) B13201811
theorem B5867471 : Blo 2255435 5867471 := bstep (se 1 (by rfl) ⟨4400603, by rfl⟩ : syracuseStep 5867471 = 8801207) B8801207
theorem B3911647 : Blo 2255435 3911647 := bstep (se 1 (by rfl) ⟨2933735, by rfl⟩ : syracuseStep 3911647 = 5867471) B5867471
theorem B5215529 : Blo 2255435 5215529 := bstep (se 2 (by rfl) ⟨1955823, by rfl⟩ : syracuseStep 5215529 = 3911647) B3911647
theorem B3477019 : Blo 2255435 3477019 := bstep (se 1 (by rfl) ⟨2607764, by rfl⟩ : syracuseStep 3477019 = 5215529) B5215529
theorem B4636025 : Blo 2255435 4636025 := bstep (se 2 (by rfl) ⟨1738509, by rfl⟩ : syracuseStep 4636025 = 3477019) B3477019
theorem B3090683 : Blo 2255435 3090683 := bstep (se 1 (by rfl) ⟨2318012, by rfl⟩ : syracuseStep 3090683 = 4636025) B4636025
theorem B8241821 : Blo 2255435 8241821 := bstep (se 3 (by rfl) ⟨1545341, by rfl⟩ : syracuseStep 8241821 = 3090683) B3090683
theorem B5494547 : Blo 2255435 5494547 := bstep (se 1 (by rfl) ⟨4120910, by rfl⟩ : syracuseStep 5494547 = 8241821) B8241821
theorem B3663031 : Blo 2255435 3663031 := bstep (se 1 (by rfl) ⟨2747273, by rfl⟩ : syracuseStep 3663031 = 5494547) B5494547
theorem B4884041 : Blo 2255435 4884041 := bstep (se 2 (by rfl) ⟨1831515, by rfl⟩ : syracuseStep 4884041 = 3663031) B3663031
theorem B13024109 : Blo 2255435 13024109 := bstep (se 3 (by rfl) ⟨2442020, by rfl⟩ : syracuseStep 13024109 = 4884041) B4884041
theorem B34730957 : Blo 2255435 34730957 := bstep (se 3 (by rfl) ⟨6512054, by rfl⟩ : syracuseStep 34730957 = 13024109) B13024109
theorem B23153971 : Blo 2255435 23153971 := bstep (se 1 (by rfl) ⟨17365478, by rfl⟩ : syracuseStep 23153971 = 34730957) B34730957
theorem B30871961 : Blo 2255435 30871961 := bstep (se 2 (by rfl) ⟨11576985, by rfl⟩ : syracuseStep 30871961 = 23153971) B23153971
theorem B20581307 : Blo 2255435 20581307 := bstep (se 1 (by rfl) ⟨15435980, by rfl⟩ : syracuseStep 20581307 = 30871961) B30871961
theorem B13720871 : Blo 2255435 13720871 := bstep (se 1 (by rfl) ⟨10290653, by rfl⟩ : syracuseStep 13720871 = 20581307) B20581307
theorem B36588989 : Blo 2255435 36588989 := bstep (se 3 (by rfl) ⟨6860435, by rfl⟩ : syracuseStep 36588989 = 13720871) B13720871
theorem B24392659 : Blo 2255435 24392659 := bstep (se 1 (by rfl) ⟨18294494, by rfl⟩ : syracuseStep 24392659 = 36588989) B36588989
theorem B32523545 : Blo 2255435 32523545 := bstep (se 2 (by rfl) ⟨12196329, by rfl⟩ : syracuseStep 32523545 = 24392659) B24392659
theorem B21682363 : Blo 2255435 21682363 := bstep (se 1 (by rfl) ⟨16261772, by rfl⟩ : syracuseStep 21682363 = 32523545) B32523545
theorem B28909817 : Blo 2255435 28909817 := bstep (se 2 (by rfl) ⟨10841181, by rfl⟩ : syracuseStep 28909817 = 21682363) B21682363
theorem B19273211 : Blo 2255435 19273211 := bstep (se 1 (by rfl) ⟨14454908, by rfl⟩ : syracuseStep 19273211 = 28909817) B28909817
theorem B12848807 : Blo 2255435 12848807 := bstep (se 1 (by rfl) ⟨9636605, by rfl⟩ : syracuseStep 12848807 = 19273211) B19273211
theorem B8565871 : Blo 2255435 8565871 := bstep (se 1 (by rfl) ⟨6424403, by rfl⟩ : syracuseStep 8565871 = 12848807) B12848807
theorem B11421161 : Blo 2255435 11421161 := bstep (se 2 (by rfl) ⟨4282935, by rfl⟩ : syracuseStep 11421161 = 8565871) B8565871
theorem B7614107 : Blo 2255435 7614107 := bstep (se 1 (by rfl) ⟨5710580, by rfl⟩ : syracuseStep 7614107 = 11421161) B11421161
theorem B5076071 : Blo 2255435 5076071 := bstep (se 1 (by rfl) ⟨3807053, by rfl⟩ : syracuseStep 5076071 = 7614107) B7614107
theorem B3384047 : Blo 2255435 3384047 := bstep (se 1 (by rfl) ⟨2538035, by rfl⟩ : syracuseStep 3384047 = 5076071) B5076071
theorem B2256031 : Blo 2255435 2256031 := bstep (se 1 (by rfl) ⟨1692023, by rfl⟩ : syracuseStep 2256031 = 3384047) B3384047
theorem B3384053 : Blo 2255435 3384053 := bbase (se 5 (by rfl) ⟨158627, by rfl⟩ : syracuseStep 3384053 = 317255) (by norm_num)
theorem B2256035 : Blo 2255435 2256035 := bstep (se 1 (by rfl) ⟨1692026, by rfl⟩ : syracuseStep 2256035 = 3384053) B3384053
theorem B8130917 : Blo 2255435 8130917 := bbase (se 4 (by rfl) ⟨762273, by rfl⟩ : syracuseStep 8130917 = 1524547) (by norm_num)
theorem B5420611 : Blo 2255435 5420611 := bstep (se 1 (by rfl) ⟨4065458, by rfl⟩ : syracuseStep 5420611 = 8130917) B8130917
theorem B7227481 : Blo 2255435 7227481 := bstep (se 2 (by rfl) ⟨2710305, by rfl⟩ : syracuseStep 7227481 = 5420611) B5420611
theorem B9636641 : Blo 2255435 9636641 := bstep (se 2 (by rfl) ⟨3613740, by rfl⟩ : syracuseStep 9636641 = 7227481) B7227481
theorem B6424427 : Blo 2255435 6424427 := bstep (se 1 (by rfl) ⟨4818320, by rfl⟩ : syracuseStep 6424427 = 9636641) B9636641
theorem B4282951 : Blo 2255435 4282951 := bstep (se 1 (by rfl) ⟨3212213, by rfl⟩ : syracuseStep 4282951 = 6424427) B6424427
theorem B5710601 : Blo 2255435 5710601 := bstep (se 2 (by rfl) ⟨2141475, by rfl⟩ : syracuseStep 5710601 = 4282951) B4282951
theorem B3807067 : Blo 2255435 3807067 := bstep (se 1 (by rfl) ⟨2855300, by rfl⟩ : syracuseStep 3807067 = 5710601) B5710601
theorem B5076089 : Blo 2255435 5076089 := bstep (se 2 (by rfl) ⟨1903533, by rfl⟩ : syracuseStep 5076089 = 3807067) B3807067
theorem B3384059 : Blo 2255435 3384059 := bstep (se 1 (by rfl) ⟨2538044, by rfl⟩ : syracuseStep 3384059 = 5076089) B5076089
theorem B2256039 : Blo 2255435 2256039 := bstep (se 1 (by rfl) ⟨1692029, by rfl⟩ : syracuseStep 2256039 = 3384059) B3384059
theorem B2538049 : Blo 2255435 2538049 := bbase (se 2 (by rfl) ⟨951768, by rfl⟩ : syracuseStep 2538049 = 1903537) (by norm_num)
theorem B3384065 : Blo 2255435 3384065 := bstep (se 2 (by rfl) ⟨1269024, by rfl⟩ : syracuseStep 3384065 = 2538049) B2538049
theorem B2256043 : Blo 2255435 2256043 := bstep (se 1 (by rfl) ⟨1692032, by rfl⟩ : syracuseStep 2256043 = 3384065) B3384065
theorem B5710621 : Blo 2255435 5710621 := bbase (se 3 (by rfl) ⟨1070741, by rfl⟩ : syracuseStep 5710621 = 2141483) (by norm_num)
theorem B7614161 : Blo 2255435 7614161 := bstep (se 2 (by rfl) ⟨2855310, by rfl⟩ : syracuseStep 7614161 = 5710621) B5710621
theorem B5076107 : Blo 2255435 5076107 := bstep (se 1 (by rfl) ⟨3807080, by rfl⟩ : syracuseStep 5076107 = 7614161) B7614161
theorem B3384071 : Blo 2255435 3384071 := bstep (se 1 (by rfl) ⟨2538053, by rfl⟩ : syracuseStep 3384071 = 5076107) B5076107
theorem B2256047 : Blo 2255435 2256047 := bstep (se 1 (by rfl) ⟨1692035, by rfl⟩ : syracuseStep 2256047 = 3384071) B3384071
theorem B3384077 : Blo 2255435 3384077 := bbase (se 3 (by rfl) ⟨634514, by rfl⟩ : syracuseStep 3384077 = 1269029) (by norm_num)
theorem B2256051 : Blo 2255435 2256051 := bstep (se 1 (by rfl) ⟨1692038, by rfl⟩ : syracuseStep 2256051 = 3384077) B3384077
theorem B5076125 : Blo 2255435 5076125 := bbase (se 3 (by rfl) ⟨951773, by rfl⟩ : syracuseStep 5076125 = 1903547) (by norm_num)
theorem B3384083 : Blo 2255435 3384083 := bstep (se 1 (by rfl) ⟨2538062, by rfl⟩ : syracuseStep 3384083 = 5076125) B5076125
theorem B2256055 : Blo 2255435 2256055 := bstep (se 1 (by rfl) ⟨1692041, by rfl⟩ : syracuseStep 2256055 = 3384083) B3384083
theorem B3807101 : Blo 2255435 3807101 := bbase (se 3 (by rfl) ⟨713831, by rfl⟩ : syracuseStep 3807101 = 1427663) (by norm_num)
theorem B2538067 : Blo 2255435 2538067 := bstep (se 1 (by rfl) ⟨1903550, by rfl⟩ : syracuseStep 2538067 = 3807101) B3807101
theorem B3384089 : Blo 2255435 3384089 := bstep (se 2 (by rfl) ⟨1269033, by rfl⟩ : syracuseStep 3384089 = 2538067) B2538067
theorem B2256059 : Blo 2255435 2256059 := bstep (se 1 (by rfl) ⟨1692044, by rfl⟩ : syracuseStep 2256059 = 3384089) B3384089
theorem B7227557 : Blo 2255435 7227557 := bbase (se 4 (by rfl) ⟨677583, by rfl⟩ : syracuseStep 7227557 = 1355167) (by norm_num)
theorem B4818371 : Blo 2255435 4818371 := bstep (se 1 (by rfl) ⟨3613778, by rfl⟩ : syracuseStep 4818371 = 7227557) B7227557
theorem B12848989 : Blo 2255435 12848989 := bstep (se 3 (by rfl) ⟨2409185, by rfl⟩ : syracuseStep 12848989 = 4818371) B4818371
theorem B17131985 : Blo 2255435 17131985 := bstep (se 2 (by rfl) ⟨6424494, by rfl⟩ : syracuseStep 17131985 = 12848989) B12848989
theorem B11421323 : Blo 2255435 11421323 := bstep (se 1 (by rfl) ⟨8565992, by rfl⟩ : syracuseStep 11421323 = 17131985) B17131985
theorem B7614215 : Blo 2255435 7614215 := bstep (se 1 (by rfl) ⟨5710661, by rfl⟩ : syracuseStep 7614215 = 11421323) B11421323
theorem B5076143 : Blo 2255435 5076143 := bstep (se 1 (by rfl) ⟨3807107, by rfl⟩ : syracuseStep 5076143 = 7614215) B7614215
theorem B3384095 : Blo 2255435 3384095 := bstep (se 1 (by rfl) ⟨2538071, by rfl⟩ : syracuseStep 3384095 = 5076143) B5076143
theorem B2256063 : Blo 2255435 2256063 := bstep (se 1 (by rfl) ⟨1692047, by rfl⟩ : syracuseStep 2256063 = 3384095) B3384095
theorem B3384101 : Blo 2255435 3384101 := bbase (se 4 (by rfl) ⟨317259, by rfl⟩ : syracuseStep 3384101 = 634519) (by norm_num)
theorem B2256067 : Blo 2255435 2256067 := bstep (se 1 (by rfl) ⟨1692050, by rfl⟩ : syracuseStep 2256067 = 3384101) B3384101
theorem B2855341 : Blo 2255435 2855341 := bbase (se 3 (by rfl) ⟨535376, by rfl⟩ : syracuseStep 2855341 = 1070753) (by norm_num)
theorem B3807121 : Blo 2255435 3807121 := bstep (se 2 (by rfl) ⟨1427670, by rfl⟩ : syracuseStep 3807121 = 2855341) B2855341
theorem B5076161 : Blo 2255435 5076161 := bstep (se 2 (by rfl) ⟨1903560, by rfl⟩ : syracuseStep 5076161 = 3807121) B3807121
theorem B3384107 : Blo 2255435 3384107 := bstep (se 1 (by rfl) ⟨2538080, by rfl⟩ : syracuseStep 3384107 = 5076161) B5076161
theorem B2256071 : Blo 2255435 2256071 := bstep (se 1 (by rfl) ⟨1692053, by rfl⟩ : syracuseStep 2256071 = 3384107) B3384107
theorem B2538085 : Blo 2255435 2538085 := bbase (se 4 (by rfl) ⟨237945, by rfl⟩ : syracuseStep 2538085 = 475891) (by norm_num)
theorem B3384113 : Blo 2255435 3384113 := bstep (se 2 (by rfl) ⟨1269042, by rfl⟩ : syracuseStep 3384113 = 2538085) B2538085
theorem B2256075 : Blo 2255435 2256075 := bstep (se 1 (by rfl) ⟨1692056, by rfl⟩ : syracuseStep 2256075 = 3384113) B3384113
theorem B3613805 : Blo 2255435 3613805 := bbase (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) (by norm_num)
theorem B2409203 : Blo 2255435 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B6424541 : Blo 2255435 6424541 := bstep (se 3 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 6424541 = 2409203) B2409203
theorem B4283027 : Blo 2255435 4283027 := bstep (se 1 (by rfl) ⟨3212270, by rfl⟩ : syracuseStep 4283027 = 6424541) B6424541
theorem B2855351 : Blo 2255435 2855351 := bstep (se 1 (by rfl) ⟨2141513, by rfl⟩ : syracuseStep 2855351 = 4283027) B4283027
theorem B7614269 : Blo 2255435 7614269 := bstep (se 3 (by rfl) ⟨1427675, by rfl⟩ : syracuseStep 7614269 = 2855351) B2855351
theorem B5076179 : Blo 2255435 5076179 := bstep (se 1 (by rfl) ⟨3807134, by rfl⟩ : syracuseStep 5076179 = 7614269) B7614269
theorem B3384119 : Blo 2255435 3384119 := bstep (se 1 (by rfl) ⟨2538089, by rfl⟩ : syracuseStep 3384119 = 5076179) B5076179
theorem B2256079 : Blo 2255435 2256079 := bstep (se 1 (by rfl) ⟨1692059, by rfl⟩ : syracuseStep 2256079 = 3384119) B3384119
theorem B3384125 : Blo 2255435 3384125 := bbase (se 3 (by rfl) ⟨634523, by rfl⟩ : syracuseStep 3384125 = 1269047) (by norm_num)
theorem B2256083 : Blo 2255435 2256083 := bstep (se 1 (by rfl) ⟨1692062, by rfl⟩ : syracuseStep 2256083 = 3384125) B3384125
theorem B5076197 : Blo 2255435 5076197 := bbase (se 4 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 5076197 = 951787) (by norm_num)
theorem B3384131 : Blo 2255435 3384131 := bstep (se 1 (by rfl) ⟨2538098, by rfl⟩ : syracuseStep 3384131 = 5076197) B5076197
theorem B2256087 : Blo 2255435 2256087 := bstep (se 1 (by rfl) ⟨1692065, by rfl⟩ : syracuseStep 2256087 = 3384131) B3384131
theorem B5710733 : Blo 2255435 5710733 := bbase (se 3 (by rfl) ⟨1070762, by rfl⟩ : syracuseStep 5710733 = 2141525) (by norm_num)
theorem B3807155 : Blo 2255435 3807155 := bstep (se 1 (by rfl) ⟨2855366, by rfl⟩ : syracuseStep 3807155 = 5710733) B5710733
theorem B2538103 : Blo 2255435 2538103 := bstep (se 1 (by rfl) ⟨1903577, by rfl⟩ : syracuseStep 2538103 = 3807155) B3807155
theorem B3384137 : Blo 2255435 3384137 := bstep (se 2 (by rfl) ⟨1269051, by rfl⟩ : syracuseStep 3384137 = 2538103) B2538103
theorem B2256091 : Blo 2255435 2256091 := bstep (se 1 (by rfl) ⟨1692068, by rfl⟩ : syracuseStep 2256091 = 3384137) B3384137
theorem B3212293 : Blo 2255435 3212293 := bbase (se 4 (by rfl) ⟨301152, by rfl⟩ : syracuseStep 3212293 = 602305) (by norm_num)
theorem B4283057 : Blo 2255435 4283057 := bstep (se 2 (by rfl) ⟨1606146, by rfl⟩ : syracuseStep 4283057 = 3212293) B3212293
theorem B11421485 : Blo 2255435 11421485 := bstep (se 3 (by rfl) ⟨2141528, by rfl⟩ : syracuseStep 11421485 = 4283057) B4283057
theorem B7614323 : Blo 2255435 7614323 := bstep (se 1 (by rfl) ⟨5710742, by rfl⟩ : syracuseStep 7614323 = 11421485) B11421485
theorem B5076215 : Blo 2255435 5076215 := bstep (se 1 (by rfl) ⟨3807161, by rfl⟩ : syracuseStep 5076215 = 7614323) B7614323
theorem B3384143 : Blo 2255435 3384143 := bstep (se 1 (by rfl) ⟨2538107, by rfl⟩ : syracuseStep 3384143 = 5076215) B5076215
theorem B2256095 : Blo 2255435 2256095 := bstep (se 1 (by rfl) ⟨1692071, by rfl⟩ : syracuseStep 2256095 = 3384143) B3384143
theorem B3384149 : Blo 2255435 3384149 := bbase (se 9 (by rfl) ⟨9914, by rfl⟩ : syracuseStep 3384149 = 19829) (by norm_num)
theorem B2256099 : Blo 2255435 2256099 := bstep (se 1 (by rfl) ⟨1692074, by rfl⟩ : syracuseStep 2256099 = 3384149) B3384149
theorem B5420765 : Blo 2255435 5420765 := bbase (se 3 (by rfl) ⟨1016393, by rfl⟩ : syracuseStep 5420765 = 2032787) (by norm_num)
theorem B3613843 : Blo 2255435 3613843 := bstep (se 1 (by rfl) ⟨2710382, by rfl⟩ : syracuseStep 3613843 = 5420765) B5420765
theorem B4818457 : Blo 2255435 4818457 := bstep (se 2 (by rfl) ⟨1806921, by rfl⟩ : syracuseStep 4818457 = 3613843) B3613843
theorem B6424609 : Blo 2255435 6424609 := bstep (se 2 (by rfl) ⟨2409228, by rfl⟩ : syracuseStep 6424609 = 4818457) B4818457
theorem B8566145 : Blo 2255435 8566145 := bstep (se 2 (by rfl) ⟨3212304, by rfl⟩ : syracuseStep 8566145 = 6424609) B6424609
theorem B5710763 : Blo 2255435 5710763 := bstep (se 1 (by rfl) ⟨4283072, by rfl⟩ : syracuseStep 5710763 = 8566145) B8566145
theorem B3807175 : Blo 2255435 3807175 := bstep (se 1 (by rfl) ⟨2855381, by rfl⟩ : syracuseStep 3807175 = 5710763) B5710763
theorem B5076233 : Blo 2255435 5076233 := bstep (se 2 (by rfl) ⟨1903587, by rfl⟩ : syracuseStep 5076233 = 3807175) B3807175
theorem B3384155 : Blo 2255435 3384155 := bstep (se 1 (by rfl) ⟨2538116, by rfl⟩ : syracuseStep 3384155 = 5076233) B5076233
theorem B2256103 : Blo 2255435 2256103 := bstep (se 1 (by rfl) ⟨1692077, by rfl⟩ : syracuseStep 2256103 = 3384155) B3384155
theorem B2538121 : Blo 2255435 2538121 := bbase (se 2 (by rfl) ⟨951795, by rfl⟩ : syracuseStep 2538121 = 1903591) (by norm_num)
theorem B3384161 : Blo 2255435 3384161 := bstep (se 2 (by rfl) ⟨1269060, by rfl⟩ : syracuseStep 3384161 = 2538121) B2538121
theorem B2256107 : Blo 2255435 2256107 := bstep (se 1 (by rfl) ⟨1692080, by rfl⟩ : syracuseStep 2256107 = 3384161) B3384161
theorem B2349721 : Blo 2255435 2349721 := bbase (se 2 (by rfl) ⟨881145, by rfl⟩ : syracuseStep 2349721 = 1762291) (by norm_num)
theorem B3132961 : Blo 2255435 3132961 := bstep (se 2 (by rfl) ⟨1174860, by rfl⟩ : syracuseStep 3132961 = 2349721) B2349721
theorem B16709125 : Blo 2255435 16709125 := bstep (se 4 (by rfl) ⟨1566480, by rfl⟩ : syracuseStep 16709125 = 3132961) B3132961
theorem B22278833 : Blo 2255435 22278833 := bstep (se 2 (by rfl) ⟨8354562, by rfl⟩ : syracuseStep 22278833 = 16709125) B16709125
theorem B14852555 : Blo 2255435 14852555 := bstep (se 1 (by rfl) ⟨11139416, by rfl⟩ : syracuseStep 14852555 = 22278833) B22278833
theorem B9901703 : Blo 2255435 9901703 := bstep (se 1 (by rfl) ⟨7426277, by rfl⟩ : syracuseStep 9901703 = 14852555) B14852555
theorem B26404541 : Blo 2255435 26404541 := bstep (se 3 (by rfl) ⟨4950851, by rfl⟩ : syracuseStep 26404541 = 9901703) B9901703
theorem B17603027 : Blo 2255435 17603027 := bstep (se 1 (by rfl) ⟨13202270, by rfl⟩ : syracuseStep 17603027 = 26404541) B26404541
theorem B11735351 : Blo 2255435 11735351 := bstep (se 1 (by rfl) ⟨8801513, by rfl⟩ : syracuseStep 11735351 = 17603027) B17603027
theorem B7823567 : Blo 2255435 7823567 := bstep (se 1 (by rfl) ⟨5867675, by rfl⟩ : syracuseStep 7823567 = 11735351) B11735351
theorem B20862845 : Blo 2255435 20862845 := bstep (se 3 (by rfl) ⟨3911783, by rfl⟩ : syracuseStep 20862845 = 7823567) B7823567
theorem B13908563 : Blo 2255435 13908563 := bstep (se 1 (by rfl) ⟨10431422, by rfl⟩ : syracuseStep 13908563 = 20862845) B20862845
theorem B9272375 : Blo 2255435 9272375 := bstep (se 1 (by rfl) ⟨6954281, by rfl⟩ : syracuseStep 9272375 = 13908563) B13908563
theorem B98905333 : Blo 2255435 98905333 := bstep (se 5 (by rfl) ⟨4636187, by rfl⟩ : syracuseStep 98905333 = 9272375) B9272375
theorem B131873777 : Blo 2255435 131873777 := bstep (se 2 (by rfl) ⟨49452666, by rfl⟩ : syracuseStep 131873777 = 98905333) B98905333
theorem B87915851 : Blo 2255435 87915851 := bstep (se 1 (by rfl) ⟨65936888, by rfl⟩ : syracuseStep 87915851 = 131873777) B131873777
theorem B58610567 : Blo 2255435 58610567 := bstep (se 1 (by rfl) ⟨43957925, by rfl⟩ : syracuseStep 58610567 = 87915851) B87915851
theorem B156294845 : Blo 2255435 156294845 := bstep (se 3 (by rfl) ⟨29305283, by rfl⟩ : syracuseStep 156294845 = 58610567) B58610567
theorem B104196563 : Blo 2255435 104196563 := bstep (se 1 (by rfl) ⟨78147422, by rfl⟩ : syracuseStep 104196563 = 156294845) B156294845
theorem B69464375 : Blo 2255435 69464375 := bstep (se 1 (by rfl) ⟨52098281, by rfl⟩ : syracuseStep 69464375 = 104196563) B104196563
theorem B46309583 : Blo 2255435 46309583 := bstep (se 1 (by rfl) ⟨34732187, by rfl⟩ : syracuseStep 46309583 = 69464375) B69464375
theorem B123492221 : Blo 2255435 123492221 := bstep (se 3 (by rfl) ⟨23154791, by rfl⟩ : syracuseStep 123492221 = 46309583) B46309583
theorem B82328147 : Blo 2255435 82328147 := bstep (se 1 (by rfl) ⟨61746110, by rfl⟩ : syracuseStep 82328147 = 123492221) B123492221
theorem B54885431 : Blo 2255435 54885431 := bstep (se 1 (by rfl) ⟨41164073, by rfl⟩ : syracuseStep 54885431 = 82328147) B82328147
theorem B36590287 : Blo 2255435 36590287 := bstep (se 1 (by rfl) ⟨27442715, by rfl⟩ : syracuseStep 36590287 = 54885431) B54885431
theorem B48787049 : Blo 2255435 48787049 := bstep (se 2 (by rfl) ⟨18295143, by rfl⟩ : syracuseStep 48787049 = 36590287) B36590287
theorem B32524699 : Blo 2255435 32524699 := bstep (se 1 (by rfl) ⟨24393524, by rfl⟩ : syracuseStep 32524699 = 48787049) B48787049
theorem B43366265 : Blo 2255435 43366265 := bstep (se 2 (by rfl) ⟨16262349, by rfl⟩ : syracuseStep 43366265 = 32524699) B32524699
theorem B28910843 : Blo 2255435 28910843 := bstep (se 1 (by rfl) ⟨21683132, by rfl⟩ : syracuseStep 28910843 = 43366265) B43366265
theorem B19273895 : Blo 2255435 19273895 := bstep (se 1 (by rfl) ⟨14455421, by rfl⟩ : syracuseStep 19273895 = 28910843) B28910843
theorem B12849263 : Blo 2255435 12849263 := bstep (se 1 (by rfl) ⟨9636947, by rfl⟩ : syracuseStep 12849263 = 19273895) B19273895
theorem B8566175 : Blo 2255435 8566175 := bstep (se 1 (by rfl) ⟨6424631, by rfl⟩ : syracuseStep 8566175 = 12849263) B12849263
theorem B5710783 : Blo 2255435 5710783 := bstep (se 1 (by rfl) ⟨4283087, by rfl⟩ : syracuseStep 5710783 = 8566175) B8566175
theorem B7614377 : Blo 2255435 7614377 := bstep (se 2 (by rfl) ⟨2855391, by rfl⟩ : syracuseStep 7614377 = 5710783) B5710783
theorem B5076251 : Blo 2255435 5076251 := bstep (se 1 (by rfl) ⟨3807188, by rfl⟩ : syracuseStep 5076251 = 7614377) B7614377
theorem B3384167 : Blo 2255435 3384167 := bstep (se 1 (by rfl) ⟨2538125, by rfl⟩ : syracuseStep 3384167 = 5076251) B5076251
theorem B2256111 : Blo 2255435 2256111 := bstep (se 1 (by rfl) ⟨1692083, by rfl⟩ : syracuseStep 2256111 = 3384167) B3384167
theorem B3384173 : Blo 2255435 3384173 := bbase (se 3 (by rfl) ⟨634532, by rfl⟩ : syracuseStep 3384173 = 1269065) (by norm_num)
theorem B2256115 : Blo 2255435 2256115 := bstep (se 1 (by rfl) ⟨1692086, by rfl⟩ : syracuseStep 2256115 = 3384173) B3384173
theorem B5076269 : Blo 2255435 5076269 := bbase (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) (by norm_num)
theorem B3384179 : Blo 2255435 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B2256119 : Blo 2255435 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B5215741 : Blo 2255435 5215741 := bbase (se 3 (by rfl) ⟨977951, by rfl⟩ : syracuseStep 5215741 = 1955903) (by norm_num)
theorem B27817285 : Blo 2255435 27817285 := bstep (se 4 (by rfl) ⟨2607870, by rfl⟩ : syracuseStep 27817285 = 5215741) B5215741
theorem B37089713 : Blo 2255435 37089713 := bstep (se 2 (by rfl) ⟨13908642, by rfl⟩ : syracuseStep 37089713 = 27817285) B27817285
theorem B24726475 : Blo 2255435 24726475 := bstep (se 1 (by rfl) ⟨18544856, by rfl⟩ : syracuseStep 24726475 = 37089713) B37089713
theorem B32968633 : Blo 2255435 32968633 := bstep (se 2 (by rfl) ⟨12363237, by rfl⟩ : syracuseStep 32968633 = 24726475) B24726475
theorem B43958177 : Blo 2255435 43958177 := bstep (se 2 (by rfl) ⟨16484316, by rfl⟩ : syracuseStep 43958177 = 32968633) B32968633
theorem B29305451 : Blo 2255435 29305451 := bstep (se 1 (by rfl) ⟨21979088, by rfl⟩ : syracuseStep 29305451 = 43958177) B43958177
theorem B19536967 : Blo 2255435 19536967 := bstep (se 1 (by rfl) ⟨14652725, by rfl⟩ : syracuseStep 19536967 = 29305451) B29305451
theorem B26049289 : Blo 2255435 26049289 := bstep (se 2 (by rfl) ⟨9768483, by rfl⟩ : syracuseStep 26049289 = 19536967) B19536967
theorem B34732385 : Blo 2255435 34732385 := bstep (se 2 (by rfl) ⟨13024644, by rfl⟩ : syracuseStep 34732385 = 26049289) B26049289
theorem B23154923 : Blo 2255435 23154923 := bstep (se 1 (by rfl) ⟨17366192, by rfl⟩ : syracuseStep 23154923 = 34732385) B34732385
theorem B61746461 : Blo 2255435 61746461 := bstep (se 3 (by rfl) ⟨11577461, by rfl⟩ : syracuseStep 61746461 = 23154923) B23154923
theorem B41164307 : Blo 2255435 41164307 := bstep (se 1 (by rfl) ⟨30873230, by rfl⟩ : syracuseStep 41164307 = 61746461) B61746461
theorem B27442871 : Blo 2255435 27442871 := bstep (se 1 (by rfl) ⟨20582153, by rfl⟩ : syracuseStep 27442871 = 41164307) B41164307
theorem B18295247 : Blo 2255435 18295247 := bstep (se 1 (by rfl) ⟨13721435, by rfl⟩ : syracuseStep 18295247 = 27442871) B27442871
theorem B12196831 : Blo 2255435 12196831 := bstep (se 1 (by rfl) ⟨9147623, by rfl⟩ : syracuseStep 12196831 = 18295247) B18295247
theorem B16262441 : Blo 2255435 16262441 := bstep (se 2 (by rfl) ⟨6098415, by rfl⟩ : syracuseStep 16262441 = 12196831) B12196831
theorem B10841627 : Blo 2255435 10841627 := bstep (se 1 (by rfl) ⟨8131220, by rfl⟩ : syracuseStep 10841627 = 16262441) B16262441
theorem B7227751 : Blo 2255435 7227751 := bstep (se 1 (by rfl) ⟨5420813, by rfl⟩ : syracuseStep 7227751 = 10841627) B10841627
theorem B9637001 : Blo 2255435 9637001 := bstep (se 2 (by rfl) ⟨3613875, by rfl⟩ : syracuseStep 9637001 = 7227751) B7227751
theorem B6424667 : Blo 2255435 6424667 := bstep (se 1 (by rfl) ⟨4818500, by rfl⟩ : syracuseStep 6424667 = 9637001) B9637001
theorem B4283111 : Blo 2255435 4283111 := bstep (se 1 (by rfl) ⟨3212333, by rfl⟩ : syracuseStep 4283111 = 6424667) B6424667
theorem B2855407 : Blo 2255435 2855407 := bstep (se 1 (by rfl) ⟨2141555, by rfl⟩ : syracuseStep 2855407 = 4283111) B4283111
theorem B3807209 : Blo 2255435 3807209 := bstep (se 2 (by rfl) ⟨1427703, by rfl⟩ : syracuseStep 3807209 = 2855407) B2855407
theorem B2538139 : Blo 2255435 2538139 := bstep (se 1 (by rfl) ⟨1903604, by rfl⟩ : syracuseStep 2538139 = 3807209) B3807209
theorem B3384185 : Blo 2255435 3384185 := bstep (se 2 (by rfl) ⟨1269069, by rfl⟩ : syracuseStep 3384185 = 2538139) B2538139
theorem B2256123 : Blo 2255435 2256123 := bstep (se 1 (by rfl) ⟨1692092, by rfl⟩ : syracuseStep 2256123 = 3384185) B3384185
theorem B21683285 : Blo 2255435 21683285 := bbase (se 8 (by rfl) ⟨127050, by rfl⟩ : syracuseStep 21683285 = 254101) (by norm_num)
theorem B14455523 : Blo 2255435 14455523 := bstep (se 1 (by rfl) ⟨10841642, by rfl⟩ : syracuseStep 14455523 = 21683285) B21683285
theorem B38548061 : Blo 2255435 38548061 := bstep (se 3 (by rfl) ⟨7227761, by rfl⟩ : syracuseStep 38548061 = 14455523) B14455523
theorem B25698707 : Blo 2255435 25698707 := bstep (se 1 (by rfl) ⟨19274030, by rfl⟩ : syracuseStep 25698707 = 38548061) B38548061
theorem B17132471 : Blo 2255435 17132471 := bstep (se 1 (by rfl) ⟨12849353, by rfl⟩ : syracuseStep 17132471 = 25698707) B25698707
theorem B11421647 : Blo 2255435 11421647 := bstep (se 1 (by rfl) ⟨8566235, by rfl⟩ : syracuseStep 11421647 = 17132471) B17132471
theorem B7614431 : Blo 2255435 7614431 := bstep (se 1 (by rfl) ⟨5710823, by rfl⟩ : syracuseStep 7614431 = 11421647) B11421647
theorem B5076287 : Blo 2255435 5076287 := bstep (se 1 (by rfl) ⟨3807215, by rfl⟩ : syracuseStep 5076287 = 7614431) B7614431
theorem B3384191 : Blo 2255435 3384191 := bstep (se 1 (by rfl) ⟨2538143, by rfl⟩ : syracuseStep 3384191 = 5076287) B5076287
theorem B2256127 : Blo 2255435 2256127 := bstep (se 1 (by rfl) ⟨1692095, by rfl⟩ : syracuseStep 2256127 = 3384191) B3384191
theorem B3384197 : Blo 2255435 3384197 := bbase (se 4 (by rfl) ⟨317268, by rfl⟩ : syracuseStep 3384197 = 634537) (by norm_num)
theorem B2256131 : Blo 2255435 2256131 := bstep (se 1 (by rfl) ⟨1692098, by rfl⟩ : syracuseStep 2256131 = 3384197) B3384197
theorem B3807229 : Blo 2255435 3807229 := bbase (se 3 (by rfl) ⟨713855, by rfl⟩ : syracuseStep 3807229 = 1427711) (by norm_num)
theorem B5076305 : Blo 2255435 5076305 := bstep (se 2 (by rfl) ⟨1903614, by rfl⟩ : syracuseStep 5076305 = 3807229) B3807229
theorem B3384203 : Blo 2255435 3384203 := bstep (se 1 (by rfl) ⟨2538152, by rfl⟩ : syracuseStep 3384203 = 5076305) B5076305
theorem B2256135 : Blo 2255435 2256135 := bstep (se 1 (by rfl) ⟨1692101, by rfl⟩ : syracuseStep 2256135 = 3384203) B3384203
theorem B2538157 : Blo 2255435 2538157 := bbase (se 3 (by rfl) ⟨475904, by rfl⟩ : syracuseStep 2538157 = 951809) (by norm_num)
theorem B3384209 : Blo 2255435 3384209 := bstep (se 2 (by rfl) ⟨1269078, by rfl⟩ : syracuseStep 3384209 = 2538157) B2538157
theorem B2256139 : Blo 2255435 2256139 := bstep (se 1 (by rfl) ⟨1692104, by rfl⟩ : syracuseStep 2256139 = 3384209) B3384209
theorem B7614485 : Blo 2255435 7614485 := bbase (se 6 (by rfl) ⟨178464, by rfl⟩ : syracuseStep 7614485 = 356929) (by norm_num)
theorem B5076323 : Blo 2255435 5076323 := bstep (se 1 (by rfl) ⟨3807242, by rfl⟩ : syracuseStep 5076323 = 7614485) B7614485
theorem B3384215 : Blo 2255435 3384215 := bstep (se 1 (by rfl) ⟨2538161, by rfl⟩ : syracuseStep 3384215 = 5076323) B5076323
theorem B2256143 : Blo 2255435 2256143 := bstep (se 1 (by rfl) ⟨1692107, by rfl⟩ : syracuseStep 2256143 = 3384215) B3384215
theorem B3384221 : Blo 2255435 3384221 := bbase (se 3 (by rfl) ⟨634541, by rfl⟩ : syracuseStep 3384221 = 1269083) (by norm_num)
theorem B2256147 : Blo 2255435 2256147 := bstep (se 1 (by rfl) ⟨1692110, by rfl⟩ : syracuseStep 2256147 = 3384221) B3384221
theorem B5076341 : Blo 2255435 5076341 := bbase (se 5 (by rfl) ⟨237953, by rfl⟩ : syracuseStep 5076341 = 475907) (by norm_num)
theorem B3384227 : Blo 2255435 3384227 := bstep (se 1 (by rfl) ⟨2538170, by rfl⟩ : syracuseStep 3384227 = 5076341) B5076341
theorem B2256151 : Blo 2255435 2256151 := bstep (se 1 (by rfl) ⟨1692113, by rfl⟩ : syracuseStep 2256151 = 3384227) B3384227
theorem B6098501 : Blo 2255435 6098501 := bbase (se 4 (by rfl) ⟨571734, by rfl⟩ : syracuseStep 6098501 = 1143469) (by norm_num)
theorem B16262669 : Blo 2255435 16262669 := bstep (se 3 (by rfl) ⟨3049250, by rfl⟩ : syracuseStep 16262669 = 6098501) B6098501
theorem B10841779 : Blo 2255435 10841779 := bstep (se 1 (by rfl) ⟨8131334, by rfl⟩ : syracuseStep 10841779 = 16262669) B16262669
theorem B14455705 : Blo 2255435 14455705 := bstep (se 2 (by rfl) ⟨5420889, by rfl⟩ : syracuseStep 14455705 = 10841779) B10841779
theorem B19274273 : Blo 2255435 19274273 := bstep (se 2 (by rfl) ⟨7227852, by rfl⟩ : syracuseStep 19274273 = 14455705) B14455705
theorem B12849515 : Blo 2255435 12849515 := bstep (se 1 (by rfl) ⟨9637136, by rfl⟩ : syracuseStep 12849515 = 19274273) B19274273
theorem B8566343 : Blo 2255435 8566343 := bstep (se 1 (by rfl) ⟨6424757, by rfl⟩ : syracuseStep 8566343 = 12849515) B12849515
theorem B5710895 : Blo 2255435 5710895 := bstep (se 1 (by rfl) ⟨4283171, by rfl⟩ : syracuseStep 5710895 = 8566343) B8566343
theorem B3807263 : Blo 2255435 3807263 := bstep (se 1 (by rfl) ⟨2855447, by rfl⟩ : syracuseStep 3807263 = 5710895) B5710895
theorem B2538175 : Blo 2255435 2538175 := bstep (se 1 (by rfl) ⟨1903631, by rfl⟩ : syracuseStep 2538175 = 3807263) B3807263
theorem B3384233 : Blo 2255435 3384233 := bstep (se 2 (by rfl) ⟨1269087, by rfl⟩ : syracuseStep 3384233 = 2538175) B2538175
theorem B2256155 : Blo 2255435 2256155 := bstep (se 1 (by rfl) ⟨1692116, by rfl⟩ : syracuseStep 2256155 = 3384233) B3384233
theorem B8566357 : Blo 2255435 8566357 := bbase (se 8 (by rfl) ⟨50193, by rfl⟩ : syracuseStep 8566357 = 100387) (by norm_num)
theorem B11421809 : Blo 2255435 11421809 := bstep (se 2 (by rfl) ⟨4283178, by rfl⟩ : syracuseStep 11421809 = 8566357) B8566357
theorem B7614539 : Blo 2255435 7614539 := bstep (se 1 (by rfl) ⟨5710904, by rfl⟩ : syracuseStep 7614539 = 11421809) B11421809
theorem B5076359 : Blo 2255435 5076359 := bstep (se 1 (by rfl) ⟨3807269, by rfl⟩ : syracuseStep 5076359 = 7614539) B7614539
theorem B3384239 : Blo 2255435 3384239 := bstep (se 1 (by rfl) ⟨2538179, by rfl⟩ : syracuseStep 3384239 = 5076359) B5076359
theorem B2256159 : Blo 2255435 2256159 := bstep (se 1 (by rfl) ⟨1692119, by rfl⟩ : syracuseStep 2256159 = 3384239) B3384239
theorem B3384245 : Blo 2255435 3384245 := bbase (se 5 (by rfl) ⟨158636, by rfl⟩ : syracuseStep 3384245 = 317273) (by norm_num)
theorem B2256163 : Blo 2255435 2256163 := bstep (se 1 (by rfl) ⟨1692122, by rfl⟩ : syracuseStep 2256163 = 3384245) B3384245
theorem B5710925 : Blo 2255435 5710925 := bbase (se 3 (by rfl) ⟨1070798, by rfl⟩ : syracuseStep 5710925 = 2141597) (by norm_num)
theorem B3807283 : Blo 2255435 3807283 := bstep (se 1 (by rfl) ⟨2855462, by rfl⟩ : syracuseStep 3807283 = 5710925) B5710925
theorem B5076377 : Blo 2255435 5076377 := bstep (se 2 (by rfl) ⟨1903641, by rfl⟩ : syracuseStep 5076377 = 3807283) B3807283
theorem B3384251 : Blo 2255435 3384251 := bstep (se 1 (by rfl) ⟨2538188, by rfl⟩ : syracuseStep 3384251 = 5076377) B5076377
theorem B2256167 : Blo 2255435 2256167 := bstep (se 1 (by rfl) ⟨1692125, by rfl⟩ : syracuseStep 2256167 = 3384251) B3384251
theorem B2538193 : Blo 2255435 2538193 := bbase (se 2 (by rfl) ⟨951822, by rfl⟩ : syracuseStep 2538193 = 1903645) (by norm_num)
theorem B3384257 : Blo 2255435 3384257 := bstep (se 2 (by rfl) ⟨1269096, by rfl⟩ : syracuseStep 3384257 = 2538193) B2538193
theorem B2256171 : Blo 2255435 2256171 := bstep (se 1 (by rfl) ⟨1692128, by rfl⟩ : syracuseStep 2256171 = 3384257) B3384257
theorem B2710469 : Blo 2255435 2710469 := bbase (se 4 (by rfl) ⟨254106, by rfl⟩ : syracuseStep 2710469 = 508213) (by norm_num)
theorem B7227917 : Blo 2255435 7227917 := bstep (se 3 (by rfl) ⟨1355234, by rfl⟩ : syracuseStep 7227917 = 2710469) B2710469
theorem B4818611 : Blo 2255435 4818611 := bstep (se 1 (by rfl) ⟨3613958, by rfl⟩ : syracuseStep 4818611 = 7227917) B7227917
theorem B3212407 : Blo 2255435 3212407 := bstep (se 1 (by rfl) ⟨2409305, by rfl⟩ : syracuseStep 3212407 = 4818611) B4818611
theorem B4283209 : Blo 2255435 4283209 := bstep (se 2 (by rfl) ⟨1606203, by rfl⟩ : syracuseStep 4283209 = 3212407) B3212407
theorem B5710945 : Blo 2255435 5710945 := bstep (se 2 (by rfl) ⟨2141604, by rfl⟩ : syracuseStep 5710945 = 4283209) B4283209
theorem B7614593 : Blo 2255435 7614593 := bstep (se 2 (by rfl) ⟨2855472, by rfl⟩ : syracuseStep 7614593 = 5710945) B5710945
theorem B5076395 : Blo 2255435 5076395 := bstep (se 1 (by rfl) ⟨3807296, by rfl⟩ : syracuseStep 5076395 = 7614593) B7614593
theorem B3384263 : Blo 2255435 3384263 := bstep (se 1 (by rfl) ⟨2538197, by rfl⟩ : syracuseStep 3384263 = 5076395) B5076395
theorem B2256175 : Blo 2255435 2256175 := bstep (se 1 (by rfl) ⟨1692131, by rfl⟩ : syracuseStep 2256175 = 3384263) B3384263
theorem B3384269 : Blo 2255435 3384269 := bbase (se 3 (by rfl) ⟨634550, by rfl⟩ : syracuseStep 3384269 = 1269101) (by norm_num)
theorem B2256179 : Blo 2255435 2256179 := bstep (se 1 (by rfl) ⟨1692134, by rfl⟩ : syracuseStep 2256179 = 3384269) B3384269
theorem B5076413 : Blo 2255435 5076413 := bbase (se 3 (by rfl) ⟨951827, by rfl⟩ : syracuseStep 5076413 = 1903655) (by norm_num)
theorem B3384275 : Blo 2255435 3384275 := bstep (se 1 (by rfl) ⟨2538206, by rfl⟩ : syracuseStep 3384275 = 5076413) B5076413
theorem B2256183 : Blo 2255435 2256183 := bstep (se 1 (by rfl) ⟨1692137, by rfl⟩ : syracuseStep 2256183 = 3384275) B3384275
theorem B3807317 : Blo 2255435 3807317 := bbase (se 8 (by rfl) ⟨22308, by rfl⟩ : syracuseStep 3807317 = 44617) (by norm_num)
theorem B2538211 : Blo 2255435 2538211 := bstep (se 1 (by rfl) ⟨1903658, by rfl⟩ : syracuseStep 2538211 = 3807317) B3807317
theorem B3384281 : Blo 2255435 3384281 := bstep (se 2 (by rfl) ⟨1269105, by rfl⟩ : syracuseStep 3384281 = 2538211) B2538211
theorem B2256187 : Blo 2255435 2256187 := bstep (se 1 (by rfl) ⟨1692140, by rfl⟩ : syracuseStep 2256187 = 3384281) B3384281
theorem B54887381 : Blo 2255435 54887381 := bbase (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) (by norm_num)
theorem B36591587 : Blo 2255435 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B24394391 : Blo 2255435 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B16262927 : Blo 2255435 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B10841951 : Blo 2255435 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B7227967 : Blo 2255435 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B9637289 : Blo 2255435 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B6424859 : Blo 2255435 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B17132957 : Blo 2255435 17132957 := bstep (se 3 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 17132957 = 6424859) B6424859
theorem B11421971 : Blo 2255435 11421971 := bstep (se 1 (by rfl) ⟨8566478, by rfl⟩ : syracuseStep 11421971 = 17132957) B17132957
theorem B7614647 : Blo 2255435 7614647 := bstep (se 1 (by rfl) ⟨5710985, by rfl⟩ : syracuseStep 7614647 = 11421971) B11421971
theorem B5076431 : Blo 2255435 5076431 := bstep (se 1 (by rfl) ⟨3807323, by rfl⟩ : syracuseStep 5076431 = 7614647) B7614647
theorem B3384287 : Blo 2255435 3384287 := bstep (se 1 (by rfl) ⟨2538215, by rfl⟩ : syracuseStep 3384287 = 5076431) B5076431
theorem B2256191 : Blo 2255435 2256191 := bstep (se 1 (by rfl) ⟨1692143, by rfl⟩ : syracuseStep 2256191 = 3384287) B3384287
theorem B3384293 : Blo 2255435 3384293 := bbase (se 4 (by rfl) ⟨317277, by rfl⟩ : syracuseStep 3384293 = 634555) (by norm_num)
theorem B2256195 : Blo 2255435 2256195 := bstep (se 1 (by rfl) ⟨1692146, by rfl⟩ : syracuseStep 2256195 = 3384293) B3384293
theorem B3613997 : Blo 2255435 3613997 := bbase (se 3 (by rfl) ⟨677624, by rfl⟩ : syracuseStep 3613997 = 1355249) (by norm_num)
theorem B9637325 : Blo 2255435 9637325 := bstep (se 3 (by rfl) ⟨1806998, by rfl⟩ : syracuseStep 9637325 = 3613997) B3613997
theorem B6424883 : Blo 2255435 6424883 := bstep (se 1 (by rfl) ⟨4818662, by rfl⟩ : syracuseStep 6424883 = 9637325) B9637325
theorem B4283255 : Blo 2255435 4283255 := bstep (se 1 (by rfl) ⟨3212441, by rfl⟩ : syracuseStep 4283255 = 6424883) B6424883
theorem B2855503 : Blo 2255435 2855503 := bstep (se 1 (by rfl) ⟨2141627, by rfl⟩ : syracuseStep 2855503 = 4283255) B4283255
theorem B3807337 : Blo 2255435 3807337 := bstep (se 2 (by rfl) ⟨1427751, by rfl⟩ : syracuseStep 3807337 = 2855503) B2855503
theorem B5076449 : Blo 2255435 5076449 := bstep (se 2 (by rfl) ⟨1903668, by rfl⟩ : syracuseStep 5076449 = 3807337) B3807337
theorem B3384299 : Blo 2255435 3384299 := bstep (se 1 (by rfl) ⟨2538224, by rfl⟩ : syracuseStep 3384299 = 5076449) B5076449
theorem B2256199 : Blo 2255435 2256199 := bstep (se 1 (by rfl) ⟨1692149, by rfl⟩ : syracuseStep 2256199 = 3384299) B3384299
theorem B2538229 : Blo 2255435 2538229 := bbase (se 5 (by rfl) ⟨118979, by rfl⟩ : syracuseStep 2538229 = 237959) (by norm_num)
theorem B3384305 : Blo 2255435 3384305 := bstep (se 2 (by rfl) ⟨1269114, by rfl⟩ : syracuseStep 3384305 = 2538229) B2538229
theorem B2256203 : Blo 2255435 2256203 := bstep (se 1 (by rfl) ⟨1692152, by rfl⟩ : syracuseStep 2256203 = 3384305) B3384305
theorem B2855513 : Blo 2255435 2855513 := bbase (se 2 (by rfl) ⟨1070817, by rfl⟩ : syracuseStep 2855513 = 2141635) (by norm_num)
theorem B7614701 : Blo 2255435 7614701 := bstep (se 3 (by rfl) ⟨1427756, by rfl⟩ : syracuseStep 7614701 = 2855513) B2855513
theorem B5076467 : Blo 2255435 5076467 := bstep (se 1 (by rfl) ⟨3807350, by rfl⟩ : syracuseStep 5076467 = 7614701) B7614701
theorem B3384311 : Blo 2255435 3384311 := bstep (se 1 (by rfl) ⟨2538233, by rfl⟩ : syracuseStep 3384311 = 5076467) B5076467
theorem B2256207 : Blo 2255435 2256207 := bstep (se 1 (by rfl) ⟨1692155, by rfl⟩ : syracuseStep 2256207 = 3384311) B3384311
theorem B3384317 : Blo 2255435 3384317 := bbase (se 3 (by rfl) ⟨634559, by rfl⟩ : syracuseStep 3384317 = 1269119) (by norm_num)
theorem B2256211 : Blo 2255435 2256211 := bstep (se 1 (by rfl) ⟨1692158, by rfl⟩ : syracuseStep 2256211 = 3384317) B3384317
theorem B5076485 : Blo 2255435 5076485 := bbase (se 4 (by rfl) ⟨475920, by rfl⟩ : syracuseStep 5076485 = 951841) (by norm_num)
theorem B3384323 : Blo 2255435 3384323 := bstep (se 1 (by rfl) ⟨2538242, by rfl⟩ : syracuseStep 3384323 = 5076485) B5076485
theorem B2256215 : Blo 2255435 2256215 := bstep (se 1 (by rfl) ⟨1692161, by rfl⟩ : syracuseStep 2256215 = 3384323) B3384323
theorem B4283293 : Blo 2255435 4283293 := bbase (se 3 (by rfl) ⟨803117, by rfl⟩ : syracuseStep 4283293 = 1606235) (by norm_num)
theorem B5711057 : Blo 2255435 5711057 := bstep (se 2 (by rfl) ⟨2141646, by rfl⟩ : syracuseStep 5711057 = 4283293) B4283293
theorem B3807371 : Blo 2255435 3807371 := bstep (se 1 (by rfl) ⟨2855528, by rfl⟩ : syracuseStep 3807371 = 5711057) B5711057
theorem B2538247 : Blo 2255435 2538247 := bstep (se 1 (by rfl) ⟨1903685, by rfl⟩ : syracuseStep 2538247 = 3807371) B3807371
theorem B3384329 : Blo 2255435 3384329 := bstep (se 2 (by rfl) ⟨1269123, by rfl⟩ : syracuseStep 3384329 = 2538247) B2538247
theorem B2256219 : Blo 2255435 2256219 := bstep (se 1 (by rfl) ⟨1692164, by rfl⟩ : syracuseStep 2256219 = 3384329) B3384329
theorem B11422133 : Blo 2255435 11422133 := bbase (se 5 (by rfl) ⟨535412, by rfl⟩ : syracuseStep 11422133 = 1070825) (by norm_num)
theorem B7614755 : Blo 2255435 7614755 := bstep (se 1 (by rfl) ⟨5711066, by rfl⟩ : syracuseStep 7614755 = 11422133) B11422133
theorem B5076503 : Blo 2255435 5076503 := bstep (se 1 (by rfl) ⟨3807377, by rfl⟩ : syracuseStep 5076503 = 7614755) B7614755
theorem B3384335 : Blo 2255435 3384335 := bstep (se 1 (by rfl) ⟨2538251, by rfl⟩ : syracuseStep 3384335 = 5076503) B5076503
theorem B2256223 : Blo 2255435 2256223 := bstep (se 1 (by rfl) ⟨1692167, by rfl⟩ : syracuseStep 2256223 = 3384335) B3384335
theorem B3384341 : Blo 2255435 3384341 := bbase (se 6 (by rfl) ⟨79320, by rfl⟩ : syracuseStep 3384341 = 158641) (by norm_num)
theorem B2256227 : Blo 2255435 2256227 := bstep (se 1 (by rfl) ⟨1692170, by rfl⟩ : syracuseStep 2256227 = 3384341) B3384341
theorem B34734037 : Blo 2255435 34734037 := bbase (se 7 (by rfl) ⟨407039, by rfl⟩ : syracuseStep 34734037 = 814079) (by norm_num)
theorem B46312049 : Blo 2255435 46312049 := bstep (se 2 (by rfl) ⟨17367018, by rfl⟩ : syracuseStep 46312049 = 34734037) B34734037
theorem B30874699 : Blo 2255435 30874699 := bstep (se 1 (by rfl) ⟨23156024, by rfl⟩ : syracuseStep 30874699 = 46312049) B46312049
theorem B164665061 : Blo 2255435 164665061 := bstep (se 4 (by rfl) ⟨15437349, by rfl⟩ : syracuseStep 164665061 = 30874699) B30874699
theorem B109776707 : Blo 2255435 109776707 := bstep (se 1 (by rfl) ⟨82332530, by rfl⟩ : syracuseStep 109776707 = 164665061) B164665061
theorem B73184471 : Blo 2255435 73184471 := bstep (se 1 (by rfl) ⟨54888353, by rfl⟩ : syracuseStep 73184471 = 109776707) B109776707
theorem B48789647 : Blo 2255435 48789647 := bstep (se 1 (by rfl) ⟨36592235, by rfl⟩ : syracuseStep 48789647 = 73184471) B73184471
theorem B32526431 : Blo 2255435 32526431 := bstep (se 1 (by rfl) ⟨24394823, by rfl⟩ : syracuseStep 32526431 = 48789647) B48789647
theorem B21684287 : Blo 2255435 21684287 := bstep (se 1 (by rfl) ⟨16263215, by rfl⟩ : syracuseStep 21684287 = 32526431) B32526431
theorem B14456191 : Blo 2255435 14456191 := bstep (se 1 (by rfl) ⟨10842143, by rfl⟩ : syracuseStep 14456191 = 21684287) B21684287
theorem B19274921 : Blo 2255435 19274921 := bstep (se 2 (by rfl) ⟨7228095, by rfl⟩ : syracuseStep 19274921 = 14456191) B14456191
theorem B12849947 : Blo 2255435 12849947 := bstep (se 1 (by rfl) ⟨9637460, by rfl⟩ : syracuseStep 12849947 = 19274921) B19274921
theorem B8566631 : Blo 2255435 8566631 := bstep (se 1 (by rfl) ⟨6424973, by rfl⟩ : syracuseStep 8566631 = 12849947) B12849947
theorem B5711087 : Blo 2255435 5711087 := bstep (se 1 (by rfl) ⟨4283315, by rfl⟩ : syracuseStep 5711087 = 8566631) B8566631
theorem B3807391 : Blo 2255435 3807391 := bstep (se 1 (by rfl) ⟨2855543, by rfl⟩ : syracuseStep 3807391 = 5711087) B5711087
theorem B5076521 : Blo 2255435 5076521 := bstep (se 2 (by rfl) ⟨1903695, by rfl⟩ : syracuseStep 5076521 = 3807391) B3807391
theorem B3384347 : Blo 2255435 3384347 := bstep (se 1 (by rfl) ⟨2538260, by rfl⟩ : syracuseStep 3384347 = 5076521) B5076521
theorem B2256231 : Blo 2255435 2256231 := bstep (se 1 (by rfl) ⟨1692173, by rfl⟩ : syracuseStep 2256231 = 3384347) B3384347
theorem B2538265 : Blo 2255435 2538265 := bbase (se 2 (by rfl) ⟨951849, by rfl⟩ : syracuseStep 2538265 = 1903699) (by norm_num)
theorem B3384353 : Blo 2255435 3384353 := bstep (se 2 (by rfl) ⟨1269132, by rfl⟩ : syracuseStep 3384353 = 2538265) B2538265
theorem B2256235 : Blo 2255435 2256235 := bstep (se 1 (by rfl) ⟨1692176, by rfl⟩ : syracuseStep 2256235 = 3384353) B3384353
theorem B8566661 : Blo 2255435 8566661 := bbase (se 4 (by rfl) ⟨803124, by rfl⟩ : syracuseStep 8566661 = 1606249) (by norm_num)
theorem B5711107 : Blo 2255435 5711107 := bstep (se 1 (by rfl) ⟨4283330, by rfl⟩ : syracuseStep 5711107 = 8566661) B8566661
theorem B7614809 : Blo 2255435 7614809 := bstep (se 2 (by rfl) ⟨2855553, by rfl⟩ : syracuseStep 7614809 = 5711107) B5711107
theorem B5076539 : Blo 2255435 5076539 := bstep (se 1 (by rfl) ⟨3807404, by rfl⟩ : syracuseStep 5076539 = 7614809) B7614809
theorem B3384359 : Blo 2255435 3384359 := bstep (se 1 (by rfl) ⟨2538269, by rfl⟩ : syracuseStep 3384359 = 5076539) B5076539
theorem B2256239 : Blo 2255435 2256239 := bstep (se 1 (by rfl) ⟨1692179, by rfl⟩ : syracuseStep 2256239 = 3384359) B3384359
theorem B3384365 : Blo 2255435 3384365 := bbase (se 3 (by rfl) ⟨634568, by rfl⟩ : syracuseStep 3384365 = 1269137) (by norm_num)
theorem B2256243 : Blo 2255435 2256243 := bstep (se 1 (by rfl) ⟨1692182, by rfl⟩ : syracuseStep 2256243 = 3384365) B3384365
theorem B5076557 : Blo 2255435 5076557 := bbase (se 3 (by rfl) ⟨951854, by rfl⟩ : syracuseStep 5076557 = 1903709) (by norm_num)
theorem B3384371 : Blo 2255435 3384371 := bstep (se 1 (by rfl) ⟨2538278, by rfl⟩ : syracuseStep 3384371 = 5076557) B5076557
theorem B2256247 : Blo 2255435 2256247 := bstep (se 1 (by rfl) ⟨1692185, by rfl⟩ : syracuseStep 2256247 = 3384371) B3384371
theorem B2855569 : Blo 2255435 2855569 := bbase (se 2 (by rfl) ⟨1070838, by rfl⟩ : syracuseStep 2855569 = 2141677) (by norm_num)
theorem B3807425 : Blo 2255435 3807425 := bstep (se 2 (by rfl) ⟨1427784, by rfl⟩ : syracuseStep 3807425 = 2855569) B2855569
theorem B2538283 : Blo 2255435 2538283 := bstep (se 1 (by rfl) ⟨1903712, by rfl⟩ : syracuseStep 2538283 = 3807425) B3807425
theorem B3384377 : Blo 2255435 3384377 := bstep (se 2 (by rfl) ⟨1269141, by rfl⟩ : syracuseStep 3384377 = 2538283) B2538283
theorem B2256251 : Blo 2255435 2256251 := bstep (se 1 (by rfl) ⟨1692188, by rfl⟩ : syracuseStep 2256251 = 3384377) B3384377
theorem B4818781 : Blo 2255435 4818781 := bbase (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) (by norm_num)
theorem B25700165 : Blo 2255435 25700165 := bstep (se 4 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 25700165 = 4818781) B4818781
theorem B17133443 : Blo 2255435 17133443 := bstep (se 1 (by rfl) ⟨12850082, by rfl⟩ : syracuseStep 17133443 = 25700165) B25700165
theorem B11422295 : Blo 2255435 11422295 := bstep (se 1 (by rfl) ⟨8566721, by rfl⟩ : syracuseStep 11422295 = 17133443) B17133443
theorem B7614863 : Blo 2255435 7614863 := bstep (se 1 (by rfl) ⟨5711147, by rfl⟩ : syracuseStep 7614863 = 11422295) B11422295
theorem B5076575 : Blo 2255435 5076575 := bstep (se 1 (by rfl) ⟨3807431, by rfl⟩ : syracuseStep 5076575 = 7614863) B7614863
theorem B3384383 : Blo 2255435 3384383 := bstep (se 1 (by rfl) ⟨2538287, by rfl⟩ : syracuseStep 3384383 = 5076575) B5076575
theorem B2256255 : Blo 2255435 2256255 := bstep (se 1 (by rfl) ⟨1692191, by rfl⟩ : syracuseStep 2256255 = 3384383) B3384383
theorem B3384389 : Blo 2255435 3384389 := bbase (se 4 (by rfl) ⟨317286, by rfl⟩ : syracuseStep 3384389 = 634573) (by norm_num)
theorem B2256259 : Blo 2255435 2256259 := bstep (se 1 (by rfl) ⟨1692194, by rfl⟩ : syracuseStep 2256259 = 3384389) B3384389
theorem B3807445 : Blo 2255435 3807445 := bbase (se 7 (by rfl) ⟨44618, by rfl⟩ : syracuseStep 3807445 = 89237) (by norm_num)
theorem B5076593 : Blo 2255435 5076593 := bstep (se 2 (by rfl) ⟨1903722, by rfl⟩ : syracuseStep 5076593 = 3807445) B3807445
theorem B3384395 : Blo 2255435 3384395 := bstep (se 1 (by rfl) ⟨2538296, by rfl⟩ : syracuseStep 3384395 = 5076593) B5076593
theorem B2256263 : Blo 2255435 2256263 := bstep (se 1 (by rfl) ⟨1692197, by rfl⟩ : syracuseStep 2256263 = 3384395) B3384395
theorem B2538301 : Blo 2255435 2538301 := bbase (se 3 (by rfl) ⟨475931, by rfl⟩ : syracuseStep 2538301 = 951863) (by norm_num)
theorem B3384401 : Blo 2255435 3384401 := bstep (se 2 (by rfl) ⟨1269150, by rfl⟩ : syracuseStep 3384401 = 2538301) B2538301
theorem B2256267 : Blo 2255435 2256267 := bstep (se 1 (by rfl) ⟨1692200, by rfl⟩ : syracuseStep 2256267 = 3384401) B3384401
theorem B7614917 : Blo 2255435 7614917 := bbase (se 4 (by rfl) ⟨713898, by rfl⟩ : syracuseStep 7614917 = 1427797) (by norm_num)
theorem B5076611 : Blo 2255435 5076611 := bstep (se 1 (by rfl) ⟨3807458, by rfl⟩ : syracuseStep 5076611 = 7614917) B7614917
theorem B3384407 : Blo 2255435 3384407 := bstep (se 1 (by rfl) ⟨2538305, by rfl⟩ : syracuseStep 3384407 = 5076611) B5076611
theorem B2256271 : Blo 2255435 2256271 := bstep (se 1 (by rfl) ⟨1692203, by rfl⟩ : syracuseStep 2256271 = 3384407) B3384407
theorem B3384413 : Blo 2255435 3384413 := bbase (se 3 (by rfl) ⟨634577, by rfl⟩ : syracuseStep 3384413 = 1269155) (by norm_num)
theorem B2256275 : Blo 2255435 2256275 := bstep (se 1 (by rfl) ⟨1692206, by rfl⟩ : syracuseStep 2256275 = 3384413) B3384413
theorem B5076629 : Blo 2255435 5076629 := bbase (se 6 (by rfl) ⟨118983, by rfl⟩ : syracuseStep 5076629 = 237967) (by norm_num)
theorem B3384419 : Blo 2255435 3384419 := bstep (se 1 (by rfl) ⟨2538314, by rfl⟩ : syracuseStep 3384419 = 5076629) B5076629
theorem B2256279 : Blo 2255435 2256279 := bstep (se 1 (by rfl) ⟨1692209, by rfl⟩ : syracuseStep 2256279 = 3384419) B3384419
theorem B2409421 : Blo 2255435 2409421 := bbase (se 3 (by rfl) ⟨451766, by rfl⟩ : syracuseStep 2409421 = 903533) (by norm_num)
theorem B3212561 : Blo 2255435 3212561 := bstep (se 2 (by rfl) ⟨1204710, by rfl⟩ : syracuseStep 3212561 = 2409421) B2409421
theorem B8566829 : Blo 2255435 8566829 := bstep (se 3 (by rfl) ⟨1606280, by rfl⟩ : syracuseStep 8566829 = 3212561) B3212561
theorem B5711219 : Blo 2255435 5711219 := bstep (se 1 (by rfl) ⟨4283414, by rfl⟩ : syracuseStep 5711219 = 8566829) B8566829
theorem B3807479 : Blo 2255435 3807479 := bstep (se 1 (by rfl) ⟨2855609, by rfl⟩ : syracuseStep 3807479 = 5711219) B5711219
theorem B2538319 : Blo 2255435 2538319 := bstep (se 1 (by rfl) ⟨1903739, by rfl⟩ : syracuseStep 2538319 = 3807479) B3807479
theorem B3384425 : Blo 2255435 3384425 := bstep (se 2 (by rfl) ⟨1269159, by rfl⟩ : syracuseStep 3384425 = 2538319) B2538319
theorem B2256283 : Blo 2255435 2256283 := bstep (se 1 (by rfl) ⟨1692212, by rfl⟩ : syracuseStep 2256283 = 3384425) B3384425
theorem B3049429 : Blo 2255435 3049429 := bbase (se 7 (by rfl) ⟨35735, by rfl⟩ : syracuseStep 3049429 = 71471) (by norm_num)
theorem B4065905 : Blo 2255435 4065905 := bstep (se 2 (by rfl) ⟨1524714, by rfl⟩ : syracuseStep 4065905 = 3049429) B3049429
theorem B2710603 : Blo 2255435 2710603 := bstep (se 1 (by rfl) ⟨2032952, by rfl⟩ : syracuseStep 2710603 = 4065905) B4065905
theorem B14456549 : Blo 2255435 14456549 := bstep (se 4 (by rfl) ⟨1355301, by rfl⟩ : syracuseStep 14456549 = 2710603) B2710603
theorem B9637699 : Blo 2255435 9637699 := bstep (se 1 (by rfl) ⟨7228274, by rfl⟩ : syracuseStep 9637699 = 14456549) B14456549
theorem B12850265 : Blo 2255435 12850265 := bstep (se 2 (by rfl) ⟨4818849, by rfl⟩ : syracuseStep 12850265 = 9637699) B9637699
theorem B8566843 : Blo 2255435 8566843 := bstep (se 1 (by rfl) ⟨6425132, by rfl⟩ : syracuseStep 8566843 = 12850265) B12850265
theorem B11422457 : Blo 2255435 11422457 := bstep (se 2 (by rfl) ⟨4283421, by rfl⟩ : syracuseStep 11422457 = 8566843) B8566843
theorem B7614971 : Blo 2255435 7614971 := bstep (se 1 (by rfl) ⟨5711228, by rfl⟩ : syracuseStep 7614971 = 11422457) B11422457
theorem B5076647 : Blo 2255435 5076647 := bstep (se 1 (by rfl) ⟨3807485, by rfl⟩ : syracuseStep 5076647 = 7614971) B7614971
theorem B3384431 : Blo 2255435 3384431 := bstep (se 1 (by rfl) ⟨2538323, by rfl⟩ : syracuseStep 3384431 = 5076647) B5076647
theorem B2256287 : Blo 2255435 2256287 := bstep (se 1 (by rfl) ⟨1692215, by rfl⟩ : syracuseStep 2256287 = 3384431) B3384431
theorem B3384437 : Blo 2255435 3384437 := bbase (se 5 (by rfl) ⟨158645, by rfl⟩ : syracuseStep 3384437 = 317291) (by norm_num)
theorem B2256291 : Blo 2255435 2256291 := bstep (se 1 (by rfl) ⟨1692218, by rfl⟩ : syracuseStep 2256291 = 3384437) B3384437
theorem B4283437 : Blo 2255435 4283437 := bbase (se 3 (by rfl) ⟨803144, by rfl⟩ : syracuseStep 4283437 = 1606289) (by norm_num)
theorem B5711249 : Blo 2255435 5711249 := bstep (se 2 (by rfl) ⟨2141718, by rfl⟩ : syracuseStep 5711249 = 4283437) B4283437
theorem B3807499 : Blo 2255435 3807499 := bstep (se 1 (by rfl) ⟨2855624, by rfl⟩ : syracuseStep 3807499 = 5711249) B5711249
theorem B5076665 : Blo 2255435 5076665 := bstep (se 2 (by rfl) ⟨1903749, by rfl⟩ : syracuseStep 5076665 = 3807499) B3807499
theorem B3384443 : Blo 2255435 3384443 := bstep (se 1 (by rfl) ⟨2538332, by rfl⟩ : syracuseStep 3384443 = 5076665) B5076665
theorem B2256295 : Blo 2255435 2256295 := bstep (se 1 (by rfl) ⟨1692221, by rfl⟩ : syracuseStep 2256295 = 3384443) B3384443
theorem B2538337 : Blo 2255435 2538337 := bbase (se 2 (by rfl) ⟨951876, by rfl⟩ : syracuseStep 2538337 = 1903753) (by norm_num)
theorem B3384449 : Blo 2255435 3384449 := bstep (se 2 (by rfl) ⟨1269168, by rfl⟩ : syracuseStep 3384449 = 2538337) B2538337
theorem B2256299 : Blo 2255435 2256299 := bstep (se 1 (by rfl) ⟨1692224, by rfl⟩ : syracuseStep 2256299 = 3384449) B3384449
theorem B5711269 : Blo 2255435 5711269 := bbase (se 4 (by rfl) ⟨535431, by rfl⟩ : syracuseStep 5711269 = 1070863) (by norm_num)
theorem B7615025 : Blo 2255435 7615025 := bstep (se 2 (by rfl) ⟨2855634, by rfl⟩ : syracuseStep 7615025 = 5711269) B5711269
theorem B5076683 : Blo 2255435 5076683 := bstep (se 1 (by rfl) ⟨3807512, by rfl⟩ : syracuseStep 5076683 = 7615025) B7615025
theorem B3384455 : Blo 2255435 3384455 := bstep (se 1 (by rfl) ⟨2538341, by rfl⟩ : syracuseStep 3384455 = 5076683) B5076683
theorem B2256303 : Blo 2255435 2256303 := bstep (se 1 (by rfl) ⟨1692227, by rfl⟩ : syracuseStep 2256303 = 3384455) B3384455
theorem B3384461 : Blo 2255435 3384461 := bbase (se 3 (by rfl) ⟨634586, by rfl⟩ : syracuseStep 3384461 = 1269173) (by norm_num)
theorem B2256307 : Blo 2255435 2256307 := bstep (se 1 (by rfl) ⟨1692230, by rfl⟩ : syracuseStep 2256307 = 3384461) B3384461
theorem B5076701 : Blo 2255435 5076701 := bbase (se 3 (by rfl) ⟨951881, by rfl⟩ : syracuseStep 5076701 = 1903763) (by norm_num)
theorem B3384467 : Blo 2255435 3384467 := bstep (se 1 (by rfl) ⟨2538350, by rfl⟩ : syracuseStep 3384467 = 5076701) B5076701
theorem B2256311 : Blo 2255435 2256311 := bstep (se 1 (by rfl) ⟨1692233, by rfl⟩ : syracuseStep 2256311 = 3384467) B3384467
theorem B3807533 : Blo 2255435 3807533 := bbase (se 3 (by rfl) ⟨713912, by rfl⟩ : syracuseStep 3807533 = 1427825) (by norm_num)
theorem B2538355 : Blo 2255435 2538355 := bstep (se 1 (by rfl) ⟨1903766, by rfl⟩ : syracuseStep 2538355 = 3807533) B3807533
theorem B3384473 : Blo 2255435 3384473 := bstep (se 2 (by rfl) ⟨1269177, by rfl⟩ : syracuseStep 3384473 = 2538355) B2538355
theorem B2256315 : Blo 2255435 2256315 := bstep (se 1 (by rfl) ⟨1692236, by rfl⟩ : syracuseStep 2256315 = 3384473) B3384473
theorem B43370261 : Blo 2255435 43370261 := bbase (se 6 (by rfl) ⟨1016490, by rfl⟩ : syracuseStep 43370261 = 2032981) (by norm_num)
theorem B28913507 : Blo 2255435 28913507 := bstep (se 1 (by rfl) ⟨21685130, by rfl⟩ : syracuseStep 28913507 = 43370261) B43370261
theorem B19275671 : Blo 2255435 19275671 := bstep (se 1 (by rfl) ⟨14456753, by rfl⟩ : syracuseStep 19275671 = 28913507) B28913507
theorem B12850447 : Blo 2255435 12850447 := bstep (se 1 (by rfl) ⟨9637835, by rfl⟩ : syracuseStep 12850447 = 19275671) B19275671
theorem B17133929 : Blo 2255435 17133929 := bstep (se 2 (by rfl) ⟨6425223, by rfl⟩ : syracuseStep 17133929 = 12850447) B12850447
theorem B11422619 : Blo 2255435 11422619 := bstep (se 1 (by rfl) ⟨8566964, by rfl⟩ : syracuseStep 11422619 = 17133929) B17133929
theorem B7615079 : Blo 2255435 7615079 := bstep (se 1 (by rfl) ⟨5711309, by rfl⟩ : syracuseStep 7615079 = 11422619) B11422619
theorem B5076719 : Blo 2255435 5076719 := bstep (se 1 (by rfl) ⟨3807539, by rfl⟩ : syracuseStep 5076719 = 7615079) B7615079
theorem B3384479 : Blo 2255435 3384479 := bstep (se 1 (by rfl) ⟨2538359, by rfl⟩ : syracuseStep 3384479 = 5076719) B5076719
theorem B2256319 : Blo 2255435 2256319 := bstep (se 1 (by rfl) ⟨1692239, by rfl⟩ : syracuseStep 2256319 = 3384479) B3384479
theorem B3384485 : Blo 2255435 3384485 := bbase (se 4 (by rfl) ⟨317295, by rfl⟩ : syracuseStep 3384485 = 634591) (by norm_num)
theorem B2256323 : Blo 2255435 2256323 := bstep (se 1 (by rfl) ⟨1692242, by rfl⟩ : syracuseStep 2256323 = 3384485) B3384485
theorem B2855665 : Blo 2255435 2855665 := bbase (se 2 (by rfl) ⟨1070874, by rfl⟩ : syracuseStep 2855665 = 2141749) (by norm_num)
theorem B3807553 : Blo 2255435 3807553 := bstep (se 2 (by rfl) ⟨1427832, by rfl⟩ : syracuseStep 3807553 = 2855665) B2855665
theorem B5076737 : Blo 2255435 5076737 := bstep (se 2 (by rfl) ⟨1903776, by rfl⟩ : syracuseStep 5076737 = 3807553) B3807553
theorem B3384491 : Blo 2255435 3384491 := bstep (se 1 (by rfl) ⟨2538368, by rfl⟩ : syracuseStep 3384491 = 5076737) B5076737
theorem B2256327 : Blo 2255435 2256327 := bstep (se 1 (by rfl) ⟨1692245, by rfl⟩ : syracuseStep 2256327 = 3384491) B3384491
theorem B2538373 : Blo 2255435 2538373 := bbase (se 4 (by rfl) ⟨237972, by rfl⟩ : syracuseStep 2538373 = 475945) (by norm_num)
theorem B3384497 : Blo 2255435 3384497 := bstep (se 2 (by rfl) ⟨1269186, by rfl⟩ : syracuseStep 3384497 = 2538373) B2538373
theorem B2256331 : Blo 2255435 2256331 := bstep (se 1 (by rfl) ⟨1692248, by rfl⟩ : syracuseStep 2256331 = 3384497) B3384497
theorem B2287121 : Blo 2255435 2287121 := bbase (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) (by norm_num)
theorem B6098989 : Blo 2255435 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B8131985 : Blo 2255435 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B5421323 : Blo 2255435 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B3614215 : Blo 2255435 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B4818953 : Blo 2255435 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B3212635 : Blo 2255435 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B4283513 : Blo 2255435 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B2855675 : Blo 2255435 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B7615133 : Blo 2255435 7615133 := bstep (se 3 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 7615133 = 2855675) B2855675
theorem B5076755 : Blo 2255435 5076755 := bstep (se 1 (by rfl) ⟨3807566, by rfl⟩ : syracuseStep 5076755 = 7615133) B7615133
theorem B3384503 : Blo 2255435 3384503 := bstep (se 1 (by rfl) ⟨2538377, by rfl⟩ : syracuseStep 3384503 = 5076755) B5076755
theorem B2256335 : Blo 2255435 2256335 := bstep (se 1 (by rfl) ⟨1692251, by rfl⟩ : syracuseStep 2256335 = 3384503) B3384503
theorem B3384509 : Blo 2255435 3384509 := bbase (se 3 (by rfl) ⟨634595, by rfl⟩ : syracuseStep 3384509 = 1269191) (by norm_num)
theorem B2256339 : Blo 2255435 2256339 := bstep (se 1 (by rfl) ⟨1692254, by rfl⟩ : syracuseStep 2256339 = 3384509) B3384509
theorem B5076773 : Blo 2255435 5076773 := bbase (se 4 (by rfl) ⟨475947, by rfl⟩ : syracuseStep 5076773 = 951895) (by norm_num)
theorem B3384515 : Blo 2255435 3384515 := bstep (se 1 (by rfl) ⟨2538386, by rfl⟩ : syracuseStep 3384515 = 5076773) B5076773
theorem B2256343 : Blo 2255435 2256343 := bstep (se 1 (by rfl) ⟨1692257, by rfl⟩ : syracuseStep 2256343 = 3384515) B3384515
theorem B5711381 : Blo 2255435 5711381 := bbase (se 6 (by rfl) ⟨133860, by rfl⟩ : syracuseStep 5711381 = 267721) (by norm_num)
theorem B3807587 : Blo 2255435 3807587 := bstep (se 1 (by rfl) ⟨2855690, by rfl⟩ : syracuseStep 3807587 = 5711381) B5711381
theorem B2538391 : Blo 2255435 2538391 := bstep (se 1 (by rfl) ⟨1903793, by rfl⟩ : syracuseStep 2538391 = 3807587) B3807587
theorem B3384521 : Blo 2255435 3384521 := bstep (se 2 (by rfl) ⟨1269195, by rfl⟩ : syracuseStep 3384521 = 2538391) B2538391
theorem B2256347 : Blo 2255435 2256347 := bstep (se 1 (by rfl) ⟨1692260, by rfl⟩ : syracuseStep 2256347 = 3384521) B3384521
theorem B9637973 : Blo 2255435 9637973 := bbase (se 8 (by rfl) ⟨56472, by rfl⟩ : syracuseStep 9637973 = 112945) (by norm_num)
theorem B6425315 : Blo 2255435 6425315 := bstep (se 1 (by rfl) ⟨4818986, by rfl⟩ : syracuseStep 6425315 = 9637973) B9637973
theorem B4283543 : Blo 2255435 4283543 := bstep (se 1 (by rfl) ⟨3212657, by rfl⟩ : syracuseStep 4283543 = 6425315) B6425315
theorem B11422781 : Blo 2255435 11422781 := bstep (se 3 (by rfl) ⟨2141771, by rfl⟩ : syracuseStep 11422781 = 4283543) B4283543
theorem B7615187 : Blo 2255435 7615187 := bstep (se 1 (by rfl) ⟨5711390, by rfl⟩ : syracuseStep 7615187 = 11422781) B11422781
theorem B5076791 : Blo 2255435 5076791 := bstep (se 1 (by rfl) ⟨3807593, by rfl⟩ : syracuseStep 5076791 = 7615187) B7615187
theorem B3384527 : Blo 2255435 3384527 := bstep (se 1 (by rfl) ⟨2538395, by rfl⟩ : syracuseStep 3384527 = 5076791) B5076791
theorem B2256351 : Blo 2255435 2256351 := bstep (se 1 (by rfl) ⟨1692263, by rfl⟩ : syracuseStep 2256351 = 3384527) B3384527
theorem B3384533 : Blo 2255435 3384533 := bbase (se 7 (by rfl) ⟨39662, by rfl⟩ : syracuseStep 3384533 = 79325) (by norm_num)
theorem B2256355 : Blo 2255435 2256355 := bstep (se 1 (by rfl) ⟨1692266, by rfl⟩ : syracuseStep 2256355 = 3384533) B3384533
theorem B3212669 : Blo 2255435 3212669 := bbase (se 3 (by rfl) ⟨602375, by rfl⟩ : syracuseStep 3212669 = 1204751) (by norm_num)
theorem B8567117 : Blo 2255435 8567117 := bstep (se 3 (by rfl) ⟨1606334, by rfl⟩ : syracuseStep 8567117 = 3212669) B3212669
theorem B5711411 : Blo 2255435 5711411 := bstep (se 1 (by rfl) ⟨4283558, by rfl⟩ : syracuseStep 5711411 = 8567117) B8567117
theorem B3807607 : Blo 2255435 3807607 := bstep (se 1 (by rfl) ⟨2855705, by rfl⟩ : syracuseStep 3807607 = 5711411) B5711411
theorem B5076809 : Blo 2255435 5076809 := bstep (se 2 (by rfl) ⟨1903803, by rfl⟩ : syracuseStep 5076809 = 3807607) B3807607
theorem B3384539 : Blo 2255435 3384539 := bstep (se 1 (by rfl) ⟨2538404, by rfl⟩ : syracuseStep 3384539 = 5076809) B5076809
theorem B2256359 : Blo 2255435 2256359 := bstep (se 1 (by rfl) ⟨1692269, by rfl⟩ : syracuseStep 2256359 = 3384539) B3384539
theorem B2538409 : Blo 2255435 2538409 := bbase (se 2 (by rfl) ⟨951903, by rfl⟩ : syracuseStep 2538409 = 1903807) (by norm_num)
theorem B3384545 : Blo 2255435 3384545 := bstep (se 2 (by rfl) ⟨1269204, by rfl⟩ : syracuseStep 3384545 = 2538409) B2538409
theorem B2256363 : Blo 2255435 2256363 := bstep (se 1 (by rfl) ⟨1692272, by rfl⟩ : syracuseStep 2256363 = 3384545) B3384545
theorem B2287153 : Blo 2255435 2287153 := bbase (se 2 (by rfl) ⟨857682, by rfl⟩ : syracuseStep 2287153 = 1715365) (by norm_num)
theorem B3049537 : Blo 2255435 3049537 := bstep (se 2 (by rfl) ⟨1143576, by rfl⟩ : syracuseStep 3049537 = 2287153) B2287153
theorem B4066049 : Blo 2255435 4066049 := bstep (se 2 (by rfl) ⟨1524768, by rfl⟩ : syracuseStep 4066049 = 3049537) B3049537
theorem B10842797 : Blo 2255435 10842797 := bstep (se 3 (by rfl) ⟨2033024, by rfl⟩ : syracuseStep 10842797 = 4066049) B4066049
theorem B7228531 : Blo 2255435 7228531 := bstep (se 1 (by rfl) ⟨5421398, by rfl⟩ : syracuseStep 7228531 = 10842797) B10842797
theorem B9638041 : Blo 2255435 9638041 := bstep (se 2 (by rfl) ⟨3614265, by rfl⟩ : syracuseStep 9638041 = 7228531) B7228531
theorem B12850721 : Blo 2255435 12850721 := bstep (se 2 (by rfl) ⟨4819020, by rfl⟩ : syracuseStep 12850721 = 9638041) B9638041
theorem B8567147 : Blo 2255435 8567147 := bstep (se 1 (by rfl) ⟨6425360, by rfl⟩ : syracuseStep 8567147 = 12850721) B12850721
theorem B5711431 : Blo 2255435 5711431 := bstep (se 1 (by rfl) ⟨4283573, by rfl⟩ : syracuseStep 5711431 = 8567147) B8567147
theorem B7615241 : Blo 2255435 7615241 := bstep (se 2 (by rfl) ⟨2855715, by rfl⟩ : syracuseStep 7615241 = 5711431) B5711431
theorem B5076827 : Blo 2255435 5076827 := bstep (se 1 (by rfl) ⟨3807620, by rfl⟩ : syracuseStep 5076827 = 7615241) B7615241
theorem B3384551 : Blo 2255435 3384551 := bstep (se 1 (by rfl) ⟨2538413, by rfl⟩ : syracuseStep 3384551 = 5076827) B5076827
theorem B2256367 : Blo 2255435 2256367 := bstep (se 1 (by rfl) ⟨1692275, by rfl⟩ : syracuseStep 2256367 = 3384551) B3384551
theorem B3384557 : Blo 2255435 3384557 := bbase (se 3 (by rfl) ⟨634604, by rfl⟩ : syracuseStep 3384557 = 1269209) (by norm_num)
theorem B2256371 : Blo 2255435 2256371 := bstep (se 1 (by rfl) ⟨1692278, by rfl⟩ : syracuseStep 2256371 = 3384557) B3384557
theorem B5076845 : Blo 2255435 5076845 := bbase (se 3 (by rfl) ⟨951908, by rfl⟩ : syracuseStep 5076845 = 1903817) (by norm_num)
theorem B3384563 : Blo 2255435 3384563 := bstep (se 1 (by rfl) ⟨2538422, by rfl⟩ : syracuseStep 3384563 = 5076845) B5076845
theorem B2256375 : Blo 2255435 2256375 := bstep (se 1 (by rfl) ⟨1692281, by rfl⟩ : syracuseStep 2256375 = 3384563) B3384563
theorem B4283597 : Blo 2255435 4283597 := bbase (se 3 (by rfl) ⟨803174, by rfl⟩ : syracuseStep 4283597 = 1606349) (by norm_num)
theorem B2855731 : Blo 2255435 2855731 := bstep (se 1 (by rfl) ⟨2141798, by rfl⟩ : syracuseStep 2855731 = 4283597) B4283597
theorem B3807641 : Blo 2255435 3807641 := bstep (se 2 (by rfl) ⟨1427865, by rfl⟩ : syracuseStep 3807641 = 2855731) B2855731
theorem B2538427 : Blo 2255435 2538427 := bstep (se 1 (by rfl) ⟨1903820, by rfl⟩ : syracuseStep 2538427 = 3807641) B3807641
theorem B3384569 : Blo 2255435 3384569 := bstep (se 2 (by rfl) ⟨1269213, by rfl⟩ : syracuseStep 3384569 = 2538427) B2538427
theorem B2256379 : Blo 2255435 2256379 := bstep (se 1 (by rfl) ⟨1692284, by rfl⟩ : syracuseStep 2256379 = 3384569) B3384569
theorem B16264309 : Blo 2255435 16264309 := bbase (se 5 (by rfl) ⟨762389, by rfl⟩ : syracuseStep 16264309 = 1524779) (by norm_num)
theorem B21685745 : Blo 2255435 21685745 := bstep (se 2 (by rfl) ⟨8132154, by rfl⟩ : syracuseStep 21685745 = 16264309) B16264309
theorem B57828653 : Blo 2255435 57828653 := bstep (se 3 (by rfl) ⟨10842872, by rfl⟩ : syracuseStep 57828653 = 21685745) B21685745
theorem B38552435 : Blo 2255435 38552435 := bstep (se 1 (by rfl) ⟨28914326, by rfl⟩ : syracuseStep 38552435 = 57828653) B57828653
theorem B25701623 : Blo 2255435 25701623 := bstep (se 1 (by rfl) ⟨19276217, by rfl⟩ : syracuseStep 25701623 = 38552435) B38552435
theorem B17134415 : Blo 2255435 17134415 := bstep (se 1 (by rfl) ⟨12850811, by rfl⟩ : syracuseStep 17134415 = 25701623) B25701623
theorem B11422943 : Blo 2255435 11422943 := bstep (se 1 (by rfl) ⟨8567207, by rfl⟩ : syracuseStep 11422943 = 17134415) B17134415
theorem B7615295 : Blo 2255435 7615295 := bstep (se 1 (by rfl) ⟨5711471, by rfl⟩ : syracuseStep 7615295 = 11422943) B11422943
theorem B5076863 : Blo 2255435 5076863 := bstep (se 1 (by rfl) ⟨3807647, by rfl⟩ : syracuseStep 5076863 = 7615295) B7615295
theorem B3384575 : Blo 2255435 3384575 := bstep (se 1 (by rfl) ⟨2538431, by rfl⟩ : syracuseStep 3384575 = 5076863) B5076863
theorem B2256383 : Blo 2255435 2256383 := bstep (se 1 (by rfl) ⟨1692287, by rfl⟩ : syracuseStep 2256383 = 3384575) B3384575
theorem B3384581 : Blo 2255435 3384581 := bbase (se 4 (by rfl) ⟨317304, by rfl⟩ : syracuseStep 3384581 = 634609) (by norm_num)
theorem B2256387 : Blo 2255435 2256387 := bstep (se 1 (by rfl) ⟨1692290, by rfl⟩ : syracuseStep 2256387 = 3384581) B3384581
theorem B3807661 : Blo 2255435 3807661 := bbase (se 3 (by rfl) ⟨713936, by rfl⟩ : syracuseStep 3807661 = 1427873) (by norm_num)
theorem B5076881 : Blo 2255435 5076881 := bstep (se 2 (by rfl) ⟨1903830, by rfl⟩ : syracuseStep 5076881 = 3807661) B3807661
theorem B3384587 : Blo 2255435 3384587 := bstep (se 1 (by rfl) ⟨2538440, by rfl⟩ : syracuseStep 3384587 = 5076881) B5076881
theorem B2256391 : Blo 2255435 2256391 := bstep (se 1 (by rfl) ⟨1692293, by rfl⟩ : syracuseStep 2256391 = 3384587) B3384587
theorem B2538445 : Blo 2255435 2538445 := bbase (se 3 (by rfl) ⟨475958, by rfl⟩ : syracuseStep 2538445 = 951917) (by norm_num)
theorem B3384593 : Blo 2255435 3384593 := bstep (se 2 (by rfl) ⟨1269222, by rfl⟩ : syracuseStep 3384593 = 2538445) B2538445
theorem B2256395 : Blo 2255435 2256395 := bstep (se 1 (by rfl) ⟨1692296, by rfl⟩ : syracuseStep 2256395 = 3384593) B3384593
theorem B7615349 : Blo 2255435 7615349 := bbase (se 5 (by rfl) ⟨356969, by rfl⟩ : syracuseStep 7615349 = 713939) (by norm_num)
theorem B5076899 : Blo 2255435 5076899 := bstep (se 1 (by rfl) ⟨3807674, by rfl⟩ : syracuseStep 5076899 = 7615349) B7615349
theorem B3384599 : Blo 2255435 3384599 := bstep (se 1 (by rfl) ⟨2538449, by rfl⟩ : syracuseStep 3384599 = 5076899) B5076899
theorem B2256399 : Blo 2255435 2256399 := bstep (se 1 (by rfl) ⟨1692299, by rfl⟩ : syracuseStep 2256399 = 3384599) B3384599
theorem B3384605 : Blo 2255435 3384605 := bbase (se 3 (by rfl) ⟨634613, by rfl⟩ : syracuseStep 3384605 = 1269227) (by norm_num)
theorem B2256403 : Blo 2255435 2256403 := bstep (se 1 (by rfl) ⟨1692302, by rfl⟩ : syracuseStep 2256403 = 3384605) B3384605
theorem B5076917 : Blo 2255435 5076917 := bbase (se 5 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 5076917 = 475961) (by norm_num)
theorem B3384611 : Blo 2255435 3384611 := bstep (se 1 (by rfl) ⟨2538458, by rfl⟩ : syracuseStep 3384611 = 5076917) B5076917
theorem B2256407 : Blo 2255435 2256407 := bstep (se 1 (by rfl) ⟨1692305, by rfl⟩ : syracuseStep 2256407 = 3384611) B3384611
theorem B3049597 : Blo 2255435 3049597 := bbase (se 3 (by rfl) ⟨571799, by rfl⟩ : syracuseStep 3049597 = 1143599) (by norm_num)
theorem B4066129 : Blo 2255435 4066129 := bstep (se 2 (by rfl) ⟨1524798, by rfl⟩ : syracuseStep 4066129 = 3049597) B3049597
theorem B5421505 : Blo 2255435 5421505 := bstep (se 2 (by rfl) ⟨2033064, by rfl⟩ : syracuseStep 5421505 = 4066129) B4066129
theorem B7228673 : Blo 2255435 7228673 := bstep (se 2 (by rfl) ⟨2710752, by rfl⟩ : syracuseStep 7228673 = 5421505) B5421505
theorem B4819115 : Blo 2255435 4819115 := bstep (se 1 (by rfl) ⟨3614336, by rfl⟩ : syracuseStep 4819115 = 7228673) B7228673
theorem B12850973 : Blo 2255435 12850973 := bstep (se 3 (by rfl) ⟨2409557, by rfl⟩ : syracuseStep 12850973 = 4819115) B4819115
theorem B8567315 : Blo 2255435 8567315 := bstep (se 1 (by rfl) ⟨6425486, by rfl⟩ : syracuseStep 8567315 = 12850973) B12850973
theorem B5711543 : Blo 2255435 5711543 := bstep (se 1 (by rfl) ⟨4283657, by rfl⟩ : syracuseStep 5711543 = 8567315) B8567315
theorem B3807695 : Blo 2255435 3807695 := bstep (se 1 (by rfl) ⟨2855771, by rfl⟩ : syracuseStep 3807695 = 5711543) B5711543
theorem B2538463 : Blo 2255435 2538463 := bstep (se 1 (by rfl) ⟨1903847, by rfl⟩ : syracuseStep 2538463 = 3807695) B3807695
theorem B3384617 : Blo 2255435 3384617 := bstep (se 2 (by rfl) ⟨1269231, by rfl⟩ : syracuseStep 3384617 = 2538463) B2538463
theorem B2256411 : Blo 2255435 2256411 := bstep (se 1 (by rfl) ⟨1692308, by rfl⟩ : syracuseStep 2256411 = 3384617) B3384617
theorem B2710757 : Blo 2255435 2710757 := bbase (se 4 (by rfl) ⟨254133, by rfl⟩ : syracuseStep 2710757 = 508267) (by norm_num)
theorem B7228685 : Blo 2255435 7228685 := bstep (se 3 (by rfl) ⟨1355378, by rfl⟩ : syracuseStep 7228685 = 2710757) B2710757
theorem B4819123 : Blo 2255435 4819123 := bstep (se 1 (by rfl) ⟨3614342, by rfl⟩ : syracuseStep 4819123 = 7228685) B7228685
theorem B6425497 : Blo 2255435 6425497 := bstep (se 2 (by rfl) ⟨2409561, by rfl⟩ : syracuseStep 6425497 = 4819123) B4819123
theorem B8567329 : Blo 2255435 8567329 := bstep (se 2 (by rfl) ⟨3212748, by rfl⟩ : syracuseStep 8567329 = 6425497) B6425497
theorem B11423105 : Blo 2255435 11423105 := bstep (se 2 (by rfl) ⟨4283664, by rfl⟩ : syracuseStep 11423105 = 8567329) B8567329
theorem B7615403 : Blo 2255435 7615403 := bstep (se 1 (by rfl) ⟨5711552, by rfl⟩ : syracuseStep 7615403 = 11423105) B11423105
theorem B5076935 : Blo 2255435 5076935 := bstep (se 1 (by rfl) ⟨3807701, by rfl⟩ : syracuseStep 5076935 = 7615403) B7615403
theorem B3384623 : Blo 2255435 3384623 := bstep (se 1 (by rfl) ⟨2538467, by rfl⟩ : syracuseStep 3384623 = 5076935) B5076935
theorem B2256415 : Blo 2255435 2256415 := bstep (se 1 (by rfl) ⟨1692311, by rfl⟩ : syracuseStep 2256415 = 3384623) B3384623
theorem B3384629 : Blo 2255435 3384629 := bbase (se 5 (by rfl) ⟨158654, by rfl⟩ : syracuseStep 3384629 = 317309) (by norm_num)
theorem B2256419 : Blo 2255435 2256419 := bstep (se 1 (by rfl) ⟨1692314, by rfl⟩ : syracuseStep 2256419 = 3384629) B3384629
theorem B5711573 : Blo 2255435 5711573 := bbase (se 7 (by rfl) ⟨66932, by rfl⟩ : syracuseStep 5711573 = 133865) (by norm_num)
theorem B3807715 : Blo 2255435 3807715 := bstep (se 1 (by rfl) ⟨2855786, by rfl⟩ : syracuseStep 3807715 = 5711573) B5711573
theorem B5076953 : Blo 2255435 5076953 := bstep (se 2 (by rfl) ⟨1903857, by rfl⟩ : syracuseStep 5076953 = 3807715) B3807715
theorem B3384635 : Blo 2255435 3384635 := bstep (se 1 (by rfl) ⟨2538476, by rfl⟩ : syracuseStep 3384635 = 5076953) B5076953
theorem B2256423 : Blo 2255435 2256423 := bstep (se 1 (by rfl) ⟨1692317, by rfl⟩ : syracuseStep 2256423 = 3384635) B3384635
theorem B2538481 : Blo 2255435 2538481 := bbase (se 2 (by rfl) ⟨951930, by rfl⟩ : syracuseStep 2538481 = 1903861) (by norm_num)
theorem B3384641 : Blo 2255435 3384641 := bstep (se 2 (by rfl) ⟨1269240, by rfl⟩ : syracuseStep 3384641 = 2538481) B2538481
theorem B2256427 : Blo 2255435 2256427 := bstep (se 1 (by rfl) ⟨1692320, by rfl⟩ : syracuseStep 2256427 = 3384641) B3384641
theorem B10991045 : Blo 2255435 10991045 := bbase (se 4 (by rfl) ⟨1030410, by rfl⟩ : syracuseStep 10991045 = 2060821) (by norm_num)
theorem B7327363 : Blo 2255435 7327363 := bstep (se 1 (by rfl) ⟨5495522, by rfl⟩ : syracuseStep 7327363 = 10991045) B10991045
theorem B9769817 : Blo 2255435 9769817 := bstep (se 2 (by rfl) ⟨3663681, by rfl⟩ : syracuseStep 9769817 = 7327363) B7327363
theorem B6513211 : Blo 2255435 6513211 := bstep (se 1 (by rfl) ⟨4884908, by rfl⟩ : syracuseStep 6513211 = 9769817) B9769817
theorem B8684281 : Blo 2255435 8684281 := bstep (se 2 (by rfl) ⟨3256605, by rfl⟩ : syracuseStep 8684281 = 6513211) B6513211
theorem B11579041 : Blo 2255435 11579041 := bstep (se 2 (by rfl) ⟨4342140, by rfl⟩ : syracuseStep 11579041 = 8684281) B8684281
theorem B15438721 : Blo 2255435 15438721 := bstep (se 2 (by rfl) ⟨5789520, by rfl⟩ : syracuseStep 15438721 = 11579041) B11579041
theorem B20584961 : Blo 2255435 20584961 := bstep (se 2 (by rfl) ⟨7719360, by rfl⟩ : syracuseStep 20584961 = 15438721) B15438721
theorem B13723307 : Blo 2255435 13723307 := bstep (se 1 (by rfl) ⟨10292480, by rfl⟩ : syracuseStep 13723307 = 20584961) B20584961
theorem B9148871 : Blo 2255435 9148871 := bstep (se 1 (by rfl) ⟨6861653, by rfl⟩ : syracuseStep 9148871 = 13723307) B13723307
theorem B6099247 : Blo 2255435 6099247 := bstep (se 1 (by rfl) ⟨4574435, by rfl⟩ : syracuseStep 6099247 = 9148871) B9148871
theorem B8132329 : Blo 2255435 8132329 := bstep (se 2 (by rfl) ⟨3049623, by rfl⟩ : syracuseStep 8132329 = 6099247) B6099247
theorem B10843105 : Blo 2255435 10843105 := bstep (se 2 (by rfl) ⟨4066164, by rfl⟩ : syracuseStep 10843105 = 8132329) B8132329
theorem B14457473 : Blo 2255435 14457473 := bstep (se 2 (by rfl) ⟨5421552, by rfl⟩ : syracuseStep 14457473 = 10843105) B10843105
theorem B9638315 : Blo 2255435 9638315 := bstep (se 1 (by rfl) ⟨7228736, by rfl⟩ : syracuseStep 9638315 = 14457473) B14457473
theorem B6425543 : Blo 2255435 6425543 := bstep (se 1 (by rfl) ⟨4819157, by rfl⟩ : syracuseStep 6425543 = 9638315) B9638315
theorem B4283695 : Blo 2255435 4283695 := bstep (se 1 (by rfl) ⟨3212771, by rfl⟩ : syracuseStep 4283695 = 6425543) B6425543
theorem B5711593 : Blo 2255435 5711593 := bstep (se 2 (by rfl) ⟨2141847, by rfl⟩ : syracuseStep 5711593 = 4283695) B4283695
theorem B7615457 : Blo 2255435 7615457 := bstep (se 2 (by rfl) ⟨2855796, by rfl⟩ : syracuseStep 7615457 = 5711593) B5711593
theorem B5076971 : Blo 2255435 5076971 := bstep (se 1 (by rfl) ⟨3807728, by rfl⟩ : syracuseStep 5076971 = 7615457) B7615457
theorem B3384647 : Blo 2255435 3384647 := bstep (se 1 (by rfl) ⟨2538485, by rfl⟩ : syracuseStep 3384647 = 5076971) B5076971
theorem B2256431 : Blo 2255435 2256431 := bstep (se 1 (by rfl) ⟨1692323, by rfl⟩ : syracuseStep 2256431 = 3384647) B3384647
theorem B3384653 : Blo 2255435 3384653 := bbase (se 3 (by rfl) ⟨634622, by rfl⟩ : syracuseStep 3384653 = 1269245) (by norm_num)
theorem B2256435 : Blo 2255435 2256435 := bstep (se 1 (by rfl) ⟨1692326, by rfl⟩ : syracuseStep 2256435 = 3384653) B3384653
theorem B5076989 : Blo 2255435 5076989 := bbase (se 3 (by rfl) ⟨951935, by rfl⟩ : syracuseStep 5076989 = 1903871) (by norm_num)
theorem B3384659 : Blo 2255435 3384659 := bstep (se 1 (by rfl) ⟨2538494, by rfl⟩ : syracuseStep 3384659 = 5076989) B5076989
theorem B2256439 : Blo 2255435 2256439 := bstep (se 1 (by rfl) ⟨1692329, by rfl⟩ : syracuseStep 2256439 = 3384659) B3384659
theorem B3807749 : Blo 2255435 3807749 := bbase (se 4 (by rfl) ⟨356976, by rfl⟩ : syracuseStep 3807749 = 713953) (by norm_num)
theorem B2538499 : Blo 2255435 2538499 := bstep (se 1 (by rfl) ⟨1903874, by rfl⟩ : syracuseStep 2538499 = 3807749) B3807749
theorem B3384665 : Blo 2255435 3384665 := bstep (se 2 (by rfl) ⟨1269249, by rfl⟩ : syracuseStep 3384665 = 2538499) B2538499
theorem B2256443 : Blo 2255435 2256443 := bstep (se 1 (by rfl) ⟨1692332, by rfl⟩ : syracuseStep 2256443 = 3384665) B3384665
theorem B17134901 : Blo 2255435 17134901 := bbase (se 5 (by rfl) ⟨803198, by rfl⟩ : syracuseStep 17134901 = 1606397) (by norm_num)
theorem B11423267 : Blo 2255435 11423267 := bstep (se 1 (by rfl) ⟨8567450, by rfl⟩ : syracuseStep 11423267 = 17134901) B17134901
theorem B7615511 : Blo 2255435 7615511 := bstep (se 1 (by rfl) ⟨5711633, by rfl⟩ : syracuseStep 7615511 = 11423267) B11423267
theorem B5077007 : Blo 2255435 5077007 := bstep (se 1 (by rfl) ⟨3807755, by rfl⟩ : syracuseStep 5077007 = 7615511) B7615511
theorem B3384671 : Blo 2255435 3384671 := bstep (se 1 (by rfl) ⟨2538503, by rfl⟩ : syracuseStep 3384671 = 5077007) B5077007
theorem B2256447 : Blo 2255435 2256447 := bstep (se 1 (by rfl) ⟨1692335, by rfl⟩ : syracuseStep 2256447 = 3384671) B3384671
theorem B3384677 : Blo 2255435 3384677 := bbase (se 4 (by rfl) ⟨317313, by rfl⟩ : syracuseStep 3384677 = 634627) (by norm_num)
theorem B2256451 : Blo 2255435 2256451 := bstep (se 1 (by rfl) ⟨1692338, by rfl⟩ : syracuseStep 2256451 = 3384677) B3384677
theorem B4283741 : Blo 2255435 4283741 := bbase (se 3 (by rfl) ⟨803201, by rfl⟩ : syracuseStep 4283741 = 1606403) (by norm_num)
theorem B2855827 : Blo 2255435 2855827 := bstep (se 1 (by rfl) ⟨2141870, by rfl⟩ : syracuseStep 2855827 = 4283741) B4283741
theorem B3807769 : Blo 2255435 3807769 := bstep (se 2 (by rfl) ⟨1427913, by rfl⟩ : syracuseStep 3807769 = 2855827) B2855827
theorem B5077025 : Blo 2255435 5077025 := bstep (se 2 (by rfl) ⟨1903884, by rfl⟩ : syracuseStep 5077025 = 3807769) B3807769
theorem B3384683 : Blo 2255435 3384683 := bstep (se 1 (by rfl) ⟨2538512, by rfl⟩ : syracuseStep 3384683 = 5077025) B5077025
theorem B2256455 : Blo 2255435 2256455 := bstep (se 1 (by rfl) ⟨1692341, by rfl⟩ : syracuseStep 2256455 = 3384683) B3384683
theorem B2538517 : Blo 2255435 2538517 := bbase (se 6 (by rfl) ⟨59496, by rfl⟩ : syracuseStep 2538517 = 118993) (by norm_num)
theorem B3384689 : Blo 2255435 3384689 := bstep (se 2 (by rfl) ⟨1269258, by rfl⟩ : syracuseStep 3384689 = 2538517) B2538517
theorem B2256459 : Blo 2255435 2256459 := bstep (se 1 (by rfl) ⟨1692344, by rfl⟩ : syracuseStep 2256459 = 3384689) B3384689
theorem B2855837 : Blo 2255435 2855837 := bbase (se 3 (by rfl) ⟨535469, by rfl⟩ : syracuseStep 2855837 = 1070939) (by norm_num)
theorem B7615565 : Blo 2255435 7615565 := bstep (se 3 (by rfl) ⟨1427918, by rfl⟩ : syracuseStep 7615565 = 2855837) B2855837
theorem B5077043 : Blo 2255435 5077043 := bstep (se 1 (by rfl) ⟨3807782, by rfl⟩ : syracuseStep 5077043 = 7615565) B7615565
theorem B3384695 : Blo 2255435 3384695 := bstep (se 1 (by rfl) ⟨2538521, by rfl⟩ : syracuseStep 3384695 = 5077043) B5077043
theorem B2256463 : Blo 2255435 2256463 := bstep (se 1 (by rfl) ⟨1692347, by rfl⟩ : syracuseStep 2256463 = 3384695) B3384695
theorem B3384701 : Blo 2255435 3384701 := bbase (se 3 (by rfl) ⟨634631, by rfl⟩ : syracuseStep 3384701 = 1269263) (by norm_num)
theorem B2256467 : Blo 2255435 2256467 := bstep (se 1 (by rfl) ⟨1692350, by rfl⟩ : syracuseStep 2256467 = 3384701) B3384701
theorem B5077061 : Blo 2255435 5077061 := bbase (se 4 (by rfl) ⟨475974, by rfl⟩ : syracuseStep 5077061 = 951949) (by norm_num)
theorem B3384707 : Blo 2255435 3384707 := bstep (se 1 (by rfl) ⟨2538530, by rfl⟩ : syracuseStep 3384707 = 5077061) B5077061
theorem B2256471 : Blo 2255435 2256471 := bstep (se 1 (by rfl) ⟨1692353, by rfl⟩ : syracuseStep 2256471 = 3384707) B3384707
theorem B6425669 : Blo 2255435 6425669 := bbase (se 4 (by rfl) ⟨602406, by rfl⟩ : syracuseStep 6425669 = 1204813) (by norm_num)
theorem B4283779 : Blo 2255435 4283779 := bstep (se 1 (by rfl) ⟨3212834, by rfl⟩ : syracuseStep 4283779 = 6425669) B6425669
theorem B5711705 : Blo 2255435 5711705 := bstep (se 2 (by rfl) ⟨2141889, by rfl⟩ : syracuseStep 5711705 = 4283779) B4283779
theorem B3807803 : Blo 2255435 3807803 := bstep (se 1 (by rfl) ⟨2855852, by rfl⟩ : syracuseStep 3807803 = 5711705) B5711705
theorem B2538535 : Blo 2255435 2538535 := bstep (se 1 (by rfl) ⟨1903901, by rfl⟩ : syracuseStep 2538535 = 3807803) B3807803
theorem B3384713 : Blo 2255435 3384713 := bstep (se 2 (by rfl) ⟨1269267, by rfl⟩ : syracuseStep 3384713 = 2538535) B2538535
theorem B2256475 : Blo 2255435 2256475 := bstep (se 1 (by rfl) ⟨1692356, by rfl⟩ : syracuseStep 2256475 = 3384713) B3384713
theorem B11423429 : Blo 2255435 11423429 := bbase (se 4 (by rfl) ⟨1070946, by rfl⟩ : syracuseStep 11423429 = 2141893) (by norm_num)
theorem B7615619 : Blo 2255435 7615619 := bstep (se 1 (by rfl) ⟨5711714, by rfl⟩ : syracuseStep 7615619 = 11423429) B11423429
theorem B5077079 : Blo 2255435 5077079 := bstep (se 1 (by rfl) ⟨3807809, by rfl⟩ : syracuseStep 5077079 = 7615619) B7615619
theorem B3384719 : Blo 2255435 3384719 := bstep (se 1 (by rfl) ⟨2538539, by rfl⟩ : syracuseStep 3384719 = 5077079) B5077079
theorem B2256479 : Blo 2255435 2256479 := bstep (se 1 (by rfl) ⟨1692359, by rfl⟩ : syracuseStep 2256479 = 3384719) B3384719
theorem B3384725 : Blo 2255435 3384725 := bbase (se 6 (by rfl) ⟨79329, by rfl⟩ : syracuseStep 3384725 = 158659) (by norm_num)
theorem B2256483 : Blo 2255435 2256483 := bstep (se 1 (by rfl) ⟨1692362, by rfl⟩ : syracuseStep 2256483 = 3384725) B3384725
theorem B4819277 : Blo 2255435 4819277 := bbase (se 3 (by rfl) ⟨903614, by rfl⟩ : syracuseStep 4819277 = 1807229) (by norm_num)
theorem B12851405 : Blo 2255435 12851405 := bstep (se 3 (by rfl) ⟨2409638, by rfl⟩ : syracuseStep 12851405 = 4819277) B4819277
theorem B8567603 : Blo 2255435 8567603 := bstep (se 1 (by rfl) ⟨6425702, by rfl⟩ : syracuseStep 8567603 = 12851405) B12851405
theorem B5711735 : Blo 2255435 5711735 := bstep (se 1 (by rfl) ⟨4283801, by rfl⟩ : syracuseStep 5711735 = 8567603) B8567603
theorem B3807823 : Blo 2255435 3807823 := bstep (se 1 (by rfl) ⟨2855867, by rfl⟩ : syracuseStep 3807823 = 5711735) B5711735
theorem B5077097 : Blo 2255435 5077097 := bstep (se 2 (by rfl) ⟨1903911, by rfl⟩ : syracuseStep 5077097 = 3807823) B3807823
theorem B3384731 : Blo 2255435 3384731 := bstep (se 1 (by rfl) ⟨2538548, by rfl⟩ : syracuseStep 3384731 = 5077097) B5077097
theorem B2256487 : Blo 2255435 2256487 := bstep (se 1 (by rfl) ⟨1692365, by rfl⟩ : syracuseStep 2256487 = 3384731) B3384731
theorem B2538553 : Blo 2255435 2538553 := bbase (se 2 (by rfl) ⟨951957, by rfl⟩ : syracuseStep 2538553 = 1903915) (by norm_num)
theorem B3384737 : Blo 2255435 3384737 := bstep (se 2 (by rfl) ⟨1269276, by rfl⟩ : syracuseStep 3384737 = 2538553) B2538553
theorem B2256491 : Blo 2255435 2256491 := bstep (se 1 (by rfl) ⟨1692368, by rfl⟩ : syracuseStep 2256491 = 3384737) B3384737
theorem B3430925 : Blo 2255435 3430925 := bbase (se 3 (by rfl) ⟨643298, by rfl⟩ : syracuseStep 3430925 = 1286597) (by norm_num)
theorem B2287283 : Blo 2255435 2287283 := bstep (se 1 (by rfl) ⟨1715462, by rfl⟩ : syracuseStep 2287283 = 3430925) B3430925
theorem B6099421 : Blo 2255435 6099421 := bstep (se 3 (by rfl) ⟨1143641, by rfl⟩ : syracuseStep 6099421 = 2287283) B2287283
theorem B8132561 : Blo 2255435 8132561 := bstep (se 2 (by rfl) ⟨3049710, by rfl⟩ : syracuseStep 8132561 = 6099421) B6099421
theorem B5421707 : Blo 2255435 5421707 := bstep (se 1 (by rfl) ⟨4066280, by rfl⟩ : syracuseStep 5421707 = 8132561) B8132561
theorem B3614471 : Blo 2255435 3614471 := bstep (se 1 (by rfl) ⟨2710853, by rfl⟩ : syracuseStep 3614471 = 5421707) B5421707
theorem B2409647 : Blo 2255435 2409647 := bstep (se 1 (by rfl) ⟨1807235, by rfl⟩ : syracuseStep 2409647 = 3614471) B3614471
theorem B6425725 : Blo 2255435 6425725 := bstep (se 3 (by rfl) ⟨1204823, by rfl⟩ : syracuseStep 6425725 = 2409647) B2409647
theorem B8567633 : Blo 2255435 8567633 := bstep (se 2 (by rfl) ⟨3212862, by rfl⟩ : syracuseStep 8567633 = 6425725) B6425725
theorem B5711755 : Blo 2255435 5711755 := bstep (se 1 (by rfl) ⟨4283816, by rfl⟩ : syracuseStep 5711755 = 8567633) B8567633
theorem B7615673 : Blo 2255435 7615673 := bstep (se 2 (by rfl) ⟨2855877, by rfl⟩ : syracuseStep 7615673 = 5711755) B5711755
theorem B5077115 : Blo 2255435 5077115 := bstep (se 1 (by rfl) ⟨3807836, by rfl⟩ : syracuseStep 5077115 = 7615673) B7615673
theorem B3384743 : Blo 2255435 3384743 := bstep (se 1 (by rfl) ⟨2538557, by rfl⟩ : syracuseStep 3384743 = 5077115) B5077115
theorem B2256495 : Blo 2255435 2256495 := bstep (se 1 (by rfl) ⟨1692371, by rfl⟩ : syracuseStep 2256495 = 3384743) B3384743
theorem B3384749 : Blo 2255435 3384749 := bbase (se 3 (by rfl) ⟨634640, by rfl⟩ : syracuseStep 3384749 = 1269281) (by norm_num)
theorem B2256499 : Blo 2255435 2256499 := bstep (se 1 (by rfl) ⟨1692374, by rfl⟩ : syracuseStep 2256499 = 3384749) B3384749
theorem B5077133 : Blo 2255435 5077133 := bbase (se 3 (by rfl) ⟨951962, by rfl⟩ : syracuseStep 5077133 = 1903925) (by norm_num)
theorem B3384755 : Blo 2255435 3384755 := bstep (se 1 (by rfl) ⟨2538566, by rfl⟩ : syracuseStep 3384755 = 5077133) B5077133
theorem B2256503 : Blo 2255435 2256503 := bstep (se 1 (by rfl) ⟨1692377, by rfl⟩ : syracuseStep 2256503 = 3384755) B3384755
theorem B2855893 : Blo 2255435 2855893 := bbase (se 7 (by rfl) ⟨33467, by rfl⟩ : syracuseStep 2855893 = 66935) (by norm_num)
theorem B3807857 : Blo 2255435 3807857 := bstep (se 2 (by rfl) ⟨1427946, by rfl⟩ : syracuseStep 3807857 = 2855893) B2855893
theorem B2538571 : Blo 2255435 2538571 := bstep (se 1 (by rfl) ⟨1903928, by rfl⟩ : syracuseStep 2538571 = 3807857) B3807857
theorem B3384761 : Blo 2255435 3384761 := bstep (se 2 (by rfl) ⟨1269285, by rfl⟩ : syracuseStep 3384761 = 2538571) B2538571
theorem B2256507 : Blo 2255435 2256507 := bstep (se 1 (by rfl) ⟨1692380, by rfl⟩ : syracuseStep 2256507 = 3384761) B3384761
theorem B4178021 : Blo 2255435 4178021 := bbase (se 4 (by rfl) ⟨391689, by rfl⟩ : syracuseStep 4178021 = 783379) (by norm_num)
theorem B11141389 : Blo 2255435 11141389 := bstep (se 3 (by rfl) ⟨2089010, by rfl⟩ : syracuseStep 11141389 = 4178021) B4178021
theorem B14855185 : Blo 2255435 14855185 := bstep (se 2 (by rfl) ⟨5570694, by rfl⟩ : syracuseStep 14855185 = 11141389) B11141389
theorem B19806913 : Blo 2255435 19806913 := bstep (se 2 (by rfl) ⟨7427592, by rfl⟩ : syracuseStep 19806913 = 14855185) B14855185
theorem B105636869 : Blo 2255435 105636869 := bstep (se 4 (by rfl) ⟨9903456, by rfl⟩ : syracuseStep 105636869 = 19806913) B19806913
theorem B70424579 : Blo 2255435 70424579 := bstep (se 1 (by rfl) ⟨52818434, by rfl⟩ : syracuseStep 70424579 = 105636869) B105636869
theorem B46949719 : Blo 2255435 46949719 := bstep (se 1 (by rfl) ⟨35212289, by rfl⟩ : syracuseStep 46949719 = 70424579) B70424579
theorem B62599625 : Blo 2255435 62599625 := bstep (se 2 (by rfl) ⟨23474859, by rfl⟩ : syracuseStep 62599625 = 46949719) B46949719
theorem B41733083 : Blo 2255435 41733083 := bstep (se 1 (by rfl) ⟨31299812, by rfl⟩ : syracuseStep 41733083 = 62599625) B62599625
theorem B27822055 : Blo 2255435 27822055 := bstep (se 1 (by rfl) ⟨20866541, by rfl⟩ : syracuseStep 27822055 = 41733083) B41733083
theorem B37096073 : Blo 2255435 37096073 := bstep (se 2 (by rfl) ⟨13911027, by rfl⟩ : syracuseStep 37096073 = 27822055) B27822055
theorem B24730715 : Blo 2255435 24730715 := bstep (se 1 (by rfl) ⟨18548036, by rfl⟩ : syracuseStep 24730715 = 37096073) B37096073
theorem B65948573 : Blo 2255435 65948573 := bstep (se 3 (by rfl) ⟨12365357, by rfl⟩ : syracuseStep 65948573 = 24730715) B24730715
theorem B43965715 : Blo 2255435 43965715 := bstep (se 1 (by rfl) ⟨32974286, by rfl⟩ : syracuseStep 43965715 = 65948573) B65948573
theorem B58620953 : Blo 2255435 58620953 := bstep (se 2 (by rfl) ⟨21982857, by rfl⟩ : syracuseStep 58620953 = 43965715) B43965715
theorem B156322541 : Blo 2255435 156322541 := bstep (se 3 (by rfl) ⟨29310476, by rfl⟩ : syracuseStep 156322541 = 58620953) B58620953
theorem B104215027 : Blo 2255435 104215027 := bstep (se 1 (by rfl) ⟨78161270, by rfl⟩ : syracuseStep 104215027 = 156322541) B156322541
theorem B138953369 : Blo 2255435 138953369 := bstep (se 2 (by rfl) ⟨52107513, by rfl⟩ : syracuseStep 138953369 = 104215027) B104215027
theorem B92635579 : Blo 2255435 92635579 := bstep (se 1 (by rfl) ⟨69476684, by rfl⟩ : syracuseStep 92635579 = 138953369) B138953369
theorem B494056421 : Blo 2255435 494056421 := bstep (se 4 (by rfl) ⟨46317789, by rfl⟩ : syracuseStep 494056421 = 92635579) B92635579
theorem B329370947 : Blo 2255435 329370947 := bstep (se 1 (by rfl) ⟨247028210, by rfl⟩ : syracuseStep 329370947 = 494056421) B494056421
theorem B219580631 : Blo 2255435 219580631 := bstep (se 1 (by rfl) ⟨164685473, by rfl⟩ : syracuseStep 219580631 = 329370947) B329370947
theorem B146387087 : Blo 2255435 146387087 := bstep (se 1 (by rfl) ⟨109790315, by rfl⟩ : syracuseStep 146387087 = 219580631) B219580631
theorem B97591391 : Blo 2255435 97591391 := bstep (se 1 (by rfl) ⟨73193543, by rfl⟩ : syracuseStep 97591391 = 146387087) B146387087
theorem B65060927 : Blo 2255435 65060927 := bstep (se 1 (by rfl) ⟨48795695, by rfl⟩ : syracuseStep 65060927 = 97591391) B97591391
theorem B43373951 : Blo 2255435 43373951 := bstep (se 1 (by rfl) ⟨32530463, by rfl⟩ : syracuseStep 43373951 = 65060927) B65060927
theorem B28915967 : Blo 2255435 28915967 := bstep (se 1 (by rfl) ⟨21686975, by rfl⟩ : syracuseStep 28915967 = 43373951) B43373951
theorem B19277311 : Blo 2255435 19277311 := bstep (se 1 (by rfl) ⟨14457983, by rfl⟩ : syracuseStep 19277311 = 28915967) B28915967
theorem B25703081 : Blo 2255435 25703081 := bstep (se 2 (by rfl) ⟨9638655, by rfl⟩ : syracuseStep 25703081 = 19277311) B19277311
theorem B17135387 : Blo 2255435 17135387 := bstep (se 1 (by rfl) ⟨12851540, by rfl⟩ : syracuseStep 17135387 = 25703081) B25703081
theorem B11423591 : Blo 2255435 11423591 := bstep (se 1 (by rfl) ⟨8567693, by rfl⟩ : syracuseStep 11423591 = 17135387) B17135387
theorem B7615727 : Blo 2255435 7615727 := bstep (se 1 (by rfl) ⟨5711795, by rfl⟩ : syracuseStep 7615727 = 11423591) B11423591
theorem B5077151 : Blo 2255435 5077151 := bstep (se 1 (by rfl) ⟨3807863, by rfl⟩ : syracuseStep 5077151 = 7615727) B7615727
theorem B3384767 : Blo 2255435 3384767 := bstep (se 1 (by rfl) ⟨2538575, by rfl⟩ : syracuseStep 3384767 = 5077151) B5077151
theorem B2256511 : Blo 2255435 2256511 := bstep (se 1 (by rfl) ⟨1692383, by rfl⟩ : syracuseStep 2256511 = 3384767) B3384767
theorem B3384773 : Blo 2255435 3384773 := bbase (se 4 (by rfl) ⟨317322, by rfl⟩ : syracuseStep 3384773 = 634645) (by norm_num)
theorem B2256515 : Blo 2255435 2256515 := bstep (se 1 (by rfl) ⟨1692386, by rfl⟩ : syracuseStep 2256515 = 3384773) B3384773
theorem B3807877 : Blo 2255435 3807877 := bbase (se 4 (by rfl) ⟨356988, by rfl⟩ : syracuseStep 3807877 = 713977) (by norm_num)
theorem B5077169 : Blo 2255435 5077169 := bstep (se 2 (by rfl) ⟨1903938, by rfl⟩ : syracuseStep 5077169 = 3807877) B3807877
theorem B3384779 : Blo 2255435 3384779 := bstep (se 1 (by rfl) ⟨2538584, by rfl⟩ : syracuseStep 3384779 = 5077169) B5077169
theorem B2256519 : Blo 2255435 2256519 := bstep (se 1 (by rfl) ⟨1692389, by rfl⟩ : syracuseStep 2256519 = 3384779) B3384779
theorem B2538589 : Blo 2255435 2538589 := bbase (se 3 (by rfl) ⟨475985, by rfl⟩ : syracuseStep 2538589 = 951971) (by norm_num)
theorem B3384785 : Blo 2255435 3384785 := bstep (se 2 (by rfl) ⟨1269294, by rfl⟩ : syracuseStep 3384785 = 2538589) B2538589
theorem B2256523 : Blo 2255435 2256523 := bstep (se 1 (by rfl) ⟨1692392, by rfl⟩ : syracuseStep 2256523 = 3384785) B3384785
theorem B7615781 : Blo 2255435 7615781 := bbase (se 4 (by rfl) ⟨713979, by rfl⟩ : syracuseStep 7615781 = 1427959) (by norm_num)
theorem B5077187 : Blo 2255435 5077187 := bstep (se 1 (by rfl) ⟨3807890, by rfl⟩ : syracuseStep 5077187 = 7615781) B7615781
theorem B3384791 : Blo 2255435 3384791 := bstep (se 1 (by rfl) ⟨2538593, by rfl⟩ : syracuseStep 3384791 = 5077187) B5077187
theorem B2256527 : Blo 2255435 2256527 := bstep (se 1 (by rfl) ⟨1692395, by rfl⟩ : syracuseStep 2256527 = 3384791) B3384791
theorem B3384797 : Blo 2255435 3384797 := bbase (se 3 (by rfl) ⟨634649, by rfl⟩ : syracuseStep 3384797 = 1269299) (by norm_num)
theorem B2256531 : Blo 2255435 2256531 := bstep (se 1 (by rfl) ⟨1692398, by rfl⟩ : syracuseStep 2256531 = 3384797) B3384797
theorem B5077205 : Blo 2255435 5077205 := bbase (se 7 (by rfl) ⟨59498, by rfl⟩ : syracuseStep 5077205 = 118997) (by norm_num)
theorem B3384803 : Blo 2255435 3384803 := bstep (se 1 (by rfl) ⟨2538602, by rfl⟩ : syracuseStep 3384803 = 5077205) B5077205
theorem B2256535 : Blo 2255435 2256535 := bstep (se 1 (by rfl) ⟨1692401, by rfl⟩ : syracuseStep 2256535 = 3384803) B3384803
theorem B2747893 : Blo 2255435 2747893 := bbase (se 5 (by rfl) ⟨128807, by rfl⟩ : syracuseStep 2747893 = 257615) (by norm_num)
theorem B3663857 : Blo 2255435 3663857 := bstep (se 2 (by rfl) ⟨1373946, by rfl⟩ : syracuseStep 3663857 = 2747893) B2747893
theorem B2442571 : Blo 2255435 2442571 := bstep (se 1 (by rfl) ⟨1831928, by rfl⟩ : syracuseStep 2442571 = 3663857) B3663857
theorem B52108181 : Blo 2255435 52108181 := bstep (se 6 (by rfl) ⟨1221285, by rfl⟩ : syracuseStep 52108181 = 2442571) B2442571
theorem B34738787 : Blo 2255435 34738787 := bstep (se 1 (by rfl) ⟨26054090, by rfl⟩ : syracuseStep 34738787 = 52108181) B52108181
theorem B23159191 : Blo 2255435 23159191 := bstep (se 1 (by rfl) ⟨17369393, by rfl⟩ : syracuseStep 23159191 = 34738787) B34738787
theorem B30878921 : Blo 2255435 30878921 := bstep (se 2 (by rfl) ⟨11579595, by rfl⟩ : syracuseStep 30878921 = 23159191) B23159191
theorem B20585947 : Blo 2255435 20585947 := bstep (se 1 (by rfl) ⟨15439460, by rfl⟩ : syracuseStep 20585947 = 30878921) B30878921
theorem B27447929 : Blo 2255435 27447929 := bstep (se 2 (by rfl) ⟨10292973, by rfl⟩ : syracuseStep 27447929 = 20585947) B20585947
theorem B18298619 : Blo 2255435 18298619 := bstep (se 1 (by rfl) ⟨13723964, by rfl⟩ : syracuseStep 18298619 = 27447929) B27447929
theorem B12199079 : Blo 2255435 12199079 := bstep (se 1 (by rfl) ⟨9149309, by rfl⟩ : syracuseStep 12199079 = 18298619) B18298619
theorem B8132719 : Blo 2255435 8132719 := bstep (se 1 (by rfl) ⟨6099539, by rfl⟩ : syracuseStep 8132719 = 12199079) B12199079
theorem B10843625 : Blo 2255435 10843625 := bstep (se 2 (by rfl) ⟨4066359, by rfl⟩ : syracuseStep 10843625 = 8132719) B8132719
theorem B7229083 : Blo 2255435 7229083 := bstep (se 1 (by rfl) ⟨5421812, by rfl⟩ : syracuseStep 7229083 = 10843625) B10843625
theorem B9638777 : Blo 2255435 9638777 := bstep (se 2 (by rfl) ⟨3614541, by rfl⟩ : syracuseStep 9638777 = 7229083) B7229083
theorem B6425851 : Blo 2255435 6425851 := bstep (se 1 (by rfl) ⟨4819388, by rfl⟩ : syracuseStep 6425851 = 9638777) B9638777
theorem B8567801 : Blo 2255435 8567801 := bstep (se 2 (by rfl) ⟨3212925, by rfl⟩ : syracuseStep 8567801 = 6425851) B6425851
theorem B5711867 : Blo 2255435 5711867 := bstep (se 1 (by rfl) ⟨4283900, by rfl⟩ : syracuseStep 5711867 = 8567801) B8567801
theorem B3807911 : Blo 2255435 3807911 := bstep (se 1 (by rfl) ⟨2855933, by rfl⟩ : syracuseStep 3807911 = 5711867) B5711867
theorem B2538607 : Blo 2255435 2538607 := bstep (se 1 (by rfl) ⟨1903955, by rfl⟩ : syracuseStep 2538607 = 3807911) B3807911
theorem B3384809 : Blo 2255435 3384809 := bstep (se 2 (by rfl) ⟨1269303, by rfl⟩ : syracuseStep 3384809 = 2538607) B2538607
theorem B2256539 : Blo 2255435 2256539 := bstep (se 1 (by rfl) ⟨1692404, by rfl⟩ : syracuseStep 2256539 = 3384809) B3384809
theorem B5421821 : Blo 2255435 5421821 := bbase (se 3 (by rfl) ⟨1016591, by rfl⟩ : syracuseStep 5421821 = 2033183) (by norm_num)
theorem B14458189 : Blo 2255435 14458189 := bstep (se 3 (by rfl) ⟨2710910, by rfl⟩ : syracuseStep 14458189 = 5421821) B5421821
theorem B19277585 : Blo 2255435 19277585 := bstep (se 2 (by rfl) ⟨7229094, by rfl⟩ : syracuseStep 19277585 = 14458189) B14458189
theorem B12851723 : Blo 2255435 12851723 := bstep (se 1 (by rfl) ⟨9638792, by rfl⟩ : syracuseStep 12851723 = 19277585) B19277585
theorem B8567815 : Blo 2255435 8567815 := bstep (se 1 (by rfl) ⟨6425861, by rfl⟩ : syracuseStep 8567815 = 12851723) B12851723
theorem B11423753 : Blo 2255435 11423753 := bstep (se 2 (by rfl) ⟨4283907, by rfl⟩ : syracuseStep 11423753 = 8567815) B8567815
theorem B7615835 : Blo 2255435 7615835 := bstep (se 1 (by rfl) ⟨5711876, by rfl⟩ : syracuseStep 7615835 = 11423753) B11423753
theorem B5077223 : Blo 2255435 5077223 := bstep (se 1 (by rfl) ⟨3807917, by rfl⟩ : syracuseStep 5077223 = 7615835) B7615835
theorem B3384815 : Blo 2255435 3384815 := bstep (se 1 (by rfl) ⟨2538611, by rfl⟩ : syracuseStep 3384815 = 5077223) B5077223
theorem B2256543 : Blo 2255435 2256543 := bstep (se 1 (by rfl) ⟨1692407, by rfl⟩ : syracuseStep 2256543 = 3384815) B3384815
theorem B3384821 : Blo 2255435 3384821 := bbase (se 5 (by rfl) ⟨158663, by rfl⟩ : syracuseStep 3384821 = 317327) (by norm_num)
theorem B2256547 : Blo 2255435 2256547 := bstep (se 1 (by rfl) ⟨1692410, by rfl⟩ : syracuseStep 2256547 = 3384821) B3384821
theorem B2710921 : Blo 2255435 2710921 := bbase (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) (by norm_num)
theorem B3614561 : Blo 2255435 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B2409707 : Blo 2255435 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B6425885 : Blo 2255435 6425885 := bstep (se 3 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 6425885 = 2409707) B2409707
theorem B4283923 : Blo 2255435 4283923 := bstep (se 1 (by rfl) ⟨3212942, by rfl⟩ : syracuseStep 4283923 = 6425885) B6425885
theorem B5711897 : Blo 2255435 5711897 := bstep (se 2 (by rfl) ⟨2141961, by rfl⟩ : syracuseStep 5711897 = 4283923) B4283923
theorem B3807931 : Blo 2255435 3807931 := bstep (se 1 (by rfl) ⟨2855948, by rfl⟩ : syracuseStep 3807931 = 5711897) B5711897
theorem B5077241 : Blo 2255435 5077241 := bstep (se 2 (by rfl) ⟨1903965, by rfl⟩ : syracuseStep 5077241 = 3807931) B3807931
theorem B3384827 : Blo 2255435 3384827 := bstep (se 1 (by rfl) ⟨2538620, by rfl⟩ : syracuseStep 3384827 = 5077241) B5077241
theorem B2256551 : Blo 2255435 2256551 := bstep (se 1 (by rfl) ⟨1692413, by rfl⟩ : syracuseStep 2256551 = 3384827) B3384827
theorem B2538625 : Blo 2255435 2538625 := bbase (se 2 (by rfl) ⟨951984, by rfl⟩ : syracuseStep 2538625 = 1903969) (by norm_num)
theorem B3384833 : Blo 2255435 3384833 := bstep (se 2 (by rfl) ⟨1269312, by rfl⟩ : syracuseStep 3384833 = 2538625) B2538625
theorem B2256555 : Blo 2255435 2256555 := bstep (se 1 (by rfl) ⟨1692416, by rfl⟩ : syracuseStep 2256555 = 3384833) B3384833
theorem B5711917 : Blo 2255435 5711917 := bbase (se 3 (by rfl) ⟨1070984, by rfl⟩ : syracuseStep 5711917 = 2141969) (by norm_num)
theorem B7615889 : Blo 2255435 7615889 := bstep (se 2 (by rfl) ⟨2855958, by rfl⟩ : syracuseStep 7615889 = 5711917) B5711917
theorem B5077259 : Blo 2255435 5077259 := bstep (se 1 (by rfl) ⟨3807944, by rfl⟩ : syracuseStep 5077259 = 7615889) B7615889
theorem B3384839 : Blo 2255435 3384839 := bstep (se 1 (by rfl) ⟨2538629, by rfl⟩ : syracuseStep 3384839 = 5077259) B5077259
theorem B2256559 : Blo 2255435 2256559 := bstep (se 1 (by rfl) ⟨1692419, by rfl⟩ : syracuseStep 2256559 = 3384839) B3384839
theorem B3384845 : Blo 2255435 3384845 := bbase (se 3 (by rfl) ⟨634658, by rfl⟩ : syracuseStep 3384845 = 1269317) (by norm_num)
theorem B2256563 : Blo 2255435 2256563 := bstep (se 1 (by rfl) ⟨1692422, by rfl⟩ : syracuseStep 2256563 = 3384845) B3384845
theorem B5077277 : Blo 2255435 5077277 := bbase (se 3 (by rfl) ⟨951989, by rfl⟩ : syracuseStep 5077277 = 1903979) (by norm_num)
theorem B3384851 : Blo 2255435 3384851 := bstep (se 1 (by rfl) ⟨2538638, by rfl⟩ : syracuseStep 3384851 = 5077277) B5077277
theorem B2256567 : Blo 2255435 2256567 := bstep (se 1 (by rfl) ⟨1692425, by rfl⟩ : syracuseStep 2256567 = 3384851) B3384851
theorem B3807965 : Blo 2255435 3807965 := bbase (se 3 (by rfl) ⟨713993, by rfl⟩ : syracuseStep 3807965 = 1427987) (by norm_num)
theorem B2538643 : Blo 2255435 2538643 := bstep (se 1 (by rfl) ⟨1903982, by rfl⟩ : syracuseStep 2538643 = 3807965) B3807965
theorem B3384857 : Blo 2255435 3384857 := bstep (se 2 (by rfl) ⟨1269321, by rfl⟩ : syracuseStep 3384857 = 2538643) B2538643
theorem B2256571 : Blo 2255435 2256571 := bstep (se 1 (by rfl) ⟨1692428, by rfl⟩ : syracuseStep 2256571 = 3384857) B3384857
theorem B2710949 : Blo 2255435 2710949 := bbase (se 4 (by rfl) ⟨254151, by rfl⟩ : syracuseStep 2710949 = 508303) (by norm_num)
theorem B7229197 : Blo 2255435 7229197 := bstep (se 3 (by rfl) ⟨1355474, by rfl⟩ : syracuseStep 7229197 = 2710949) B2710949
theorem B9638929 : Blo 2255435 9638929 := bstep (se 2 (by rfl) ⟨3614598, by rfl⟩ : syracuseStep 9638929 = 7229197) B7229197
theorem B12851905 : Blo 2255435 12851905 := bstep (se 2 (by rfl) ⟨4819464, by rfl⟩ : syracuseStep 12851905 = 9638929) B9638929
theorem B17135873 : Blo 2255435 17135873 := bstep (se 2 (by rfl) ⟨6425952, by rfl⟩ : syracuseStep 17135873 = 12851905) B12851905
theorem B11423915 : Blo 2255435 11423915 := bstep (se 1 (by rfl) ⟨8567936, by rfl⟩ : syracuseStep 11423915 = 17135873) B17135873
theorem B7615943 : Blo 2255435 7615943 := bstep (se 1 (by rfl) ⟨5711957, by rfl⟩ : syracuseStep 7615943 = 11423915) B11423915
theorem B5077295 : Blo 2255435 5077295 := bstep (se 1 (by rfl) ⟨3807971, by rfl⟩ : syracuseStep 5077295 = 7615943) B7615943
theorem B3384863 : Blo 2255435 3384863 := bstep (se 1 (by rfl) ⟨2538647, by rfl⟩ : syracuseStep 3384863 = 5077295) B5077295
theorem B2256575 : Blo 2255435 2256575 := bstep (se 1 (by rfl) ⟨1692431, by rfl⟩ : syracuseStep 2256575 = 3384863) B3384863
theorem B3384869 : Blo 2255435 3384869 := bbase (se 4 (by rfl) ⟨317331, by rfl⟩ : syracuseStep 3384869 = 634663) (by norm_num)
theorem B2256579 : Blo 2255435 2256579 := bstep (se 1 (by rfl) ⟨1692434, by rfl⟩ : syracuseStep 2256579 = 3384869) B3384869
theorem B2855989 : Blo 2255435 2855989 := bbase (se 5 (by rfl) ⟨133874, by rfl⟩ : syracuseStep 2855989 = 267749) (by norm_num)
theorem B3807985 : Blo 2255435 3807985 := bstep (se 2 (by rfl) ⟨1427994, by rfl⟩ : syracuseStep 3807985 = 2855989) B2855989
theorem B5077313 : Blo 2255435 5077313 := bstep (se 2 (by rfl) ⟨1903992, by rfl⟩ : syracuseStep 5077313 = 3807985) B3807985
theorem B3384875 : Blo 2255435 3384875 := bstep (se 1 (by rfl) ⟨2538656, by rfl⟩ : syracuseStep 3384875 = 5077313) B5077313
theorem B2256583 : Blo 2255435 2256583 := bstep (se 1 (by rfl) ⟨1692437, by rfl⟩ : syracuseStep 2256583 = 3384875) B3384875
theorem B2538661 : Blo 2255435 2538661 := bbase (se 4 (by rfl) ⟨237999, by rfl⟩ : syracuseStep 2538661 = 475999) (by norm_num)
theorem B3384881 : Blo 2255435 3384881 := bstep (se 2 (by rfl) ⟨1269330, by rfl⟩ : syracuseStep 3384881 = 2538661) B2538661
theorem B2256587 : Blo 2255435 2256587 := bstep (se 1 (by rfl) ⟨1692440, by rfl⟩ : syracuseStep 2256587 = 3384881) B3384881
theorem B4066453 : Blo 2255435 4066453 := bbase (se 6 (by rfl) ⟨95307, by rfl⟩ : syracuseStep 4066453 = 190615) (by norm_num)
theorem B21687749 : Blo 2255435 21687749 := bstep (se 4 (by rfl) ⟨2033226, by rfl⟩ : syracuseStep 21687749 = 4066453) B4066453
theorem B14458499 : Blo 2255435 14458499 := bstep (se 1 (by rfl) ⟨10843874, by rfl⟩ : syracuseStep 14458499 = 21687749) B21687749
theorem B9638999 : Blo 2255435 9638999 := bstep (se 1 (by rfl) ⟨7229249, by rfl⟩ : syracuseStep 9638999 = 14458499) B14458499
theorem B6425999 : Blo 2255435 6425999 := bstep (se 1 (by rfl) ⟨4819499, by rfl⟩ : syracuseStep 6425999 = 9638999) B9638999
theorem B4283999 : Blo 2255435 4283999 := bstep (se 1 (by rfl) ⟨3212999, by rfl⟩ : syracuseStep 4283999 = 6425999) B6425999
theorem B2855999 : Blo 2255435 2855999 := bstep (se 1 (by rfl) ⟨2141999, by rfl⟩ : syracuseStep 2855999 = 4283999) B4283999
theorem B7615997 : Blo 2255435 7615997 := bstep (se 3 (by rfl) ⟨1427999, by rfl⟩ : syracuseStep 7615997 = 2855999) B2855999
theorem B5077331 : Blo 2255435 5077331 := bstep (se 1 (by rfl) ⟨3807998, by rfl⟩ : syracuseStep 5077331 = 7615997) B7615997
theorem B3384887 : Blo 2255435 3384887 := bstep (se 1 (by rfl) ⟨2538665, by rfl⟩ : syracuseStep 3384887 = 5077331) B5077331
theorem B2256591 : Blo 2255435 2256591 := bstep (se 1 (by rfl) ⟨1692443, by rfl⟩ : syracuseStep 2256591 = 3384887) B3384887
theorem B3384893 : Blo 2255435 3384893 := bbase (se 3 (by rfl) ⟨634667, by rfl⟩ : syracuseStep 3384893 = 1269335) (by norm_num)
theorem B2256595 : Blo 2255435 2256595 := bstep (se 1 (by rfl) ⟨1692446, by rfl⟩ : syracuseStep 2256595 = 3384893) B3384893
theorem B5077349 : Blo 2255435 5077349 := bbase (se 4 (by rfl) ⟨476001, by rfl⟩ : syracuseStep 5077349 = 952003) (by norm_num)
theorem B3384899 : Blo 2255435 3384899 := bstep (se 1 (by rfl) ⟨2538674, by rfl⟩ : syracuseStep 3384899 = 5077349) B5077349
theorem B2256599 : Blo 2255435 2256599 := bstep (se 1 (by rfl) ⟨1692449, by rfl⟩ : syracuseStep 2256599 = 3384899) B3384899
theorem B5712029 : Blo 2255435 5712029 := bbase (se 3 (by rfl) ⟨1071005, by rfl⟩ : syracuseStep 5712029 = 2142011) (by norm_num)
theorem B3808019 : Blo 2255435 3808019 := bstep (se 1 (by rfl) ⟨2856014, by rfl⟩ : syracuseStep 3808019 = 5712029) B5712029
theorem B2538679 : Blo 2255435 2538679 := bstep (se 1 (by rfl) ⟨1904009, by rfl⟩ : syracuseStep 2538679 = 3808019) B3808019
theorem B3384905 : Blo 2255435 3384905 := bstep (se 2 (by rfl) ⟨1269339, by rfl⟩ : syracuseStep 3384905 = 2538679) B2538679
theorem B2256603 : Blo 2255435 2256603 := bstep (se 1 (by rfl) ⟨1692452, by rfl⟩ : syracuseStep 2256603 = 3384905) B3384905
theorem B4284029 : Blo 2255435 4284029 := bbase (se 3 (by rfl) ⟨803255, by rfl⟩ : syracuseStep 4284029 = 1606511) (by norm_num)
theorem B11424077 : Blo 2255435 11424077 := bstep (se 3 (by rfl) ⟨2142014, by rfl⟩ : syracuseStep 11424077 = 4284029) B4284029
theorem B7616051 : Blo 2255435 7616051 := bstep (se 1 (by rfl) ⟨5712038, by rfl⟩ : syracuseStep 7616051 = 11424077) B11424077
theorem B5077367 : Blo 2255435 5077367 := bstep (se 1 (by rfl) ⟨3808025, by rfl⟩ : syracuseStep 5077367 = 7616051) B7616051
theorem B3384911 : Blo 2255435 3384911 := bstep (se 1 (by rfl) ⟨2538683, by rfl⟩ : syracuseStep 3384911 = 5077367) B5077367
theorem B2256607 : Blo 2255435 2256607 := bstep (se 1 (by rfl) ⟨1692455, by rfl⟩ : syracuseStep 2256607 = 3384911) B3384911
theorem B3384917 : Blo 2255435 3384917 := bbase (se 8 (by rfl) ⟨19833, by rfl⟩ : syracuseStep 3384917 = 39667) (by norm_num)
theorem B2256611 : Blo 2255435 2256611 := bstep (se 1 (by rfl) ⟨1692458, by rfl⟩ : syracuseStep 2256611 = 3384917) B3384917
theorem B5146661 : Blo 2255435 5146661 := bbase (se 4 (by rfl) ⟨482499, by rfl⟩ : syracuseStep 5146661 = 964999) (by norm_num)
theorem B3431107 : Blo 2255435 3431107 := bstep (se 1 (by rfl) ⟨2573330, by rfl⟩ : syracuseStep 3431107 = 5146661) B5146661
theorem B4574809 : Blo 2255435 4574809 := bstep (se 2 (by rfl) ⟨1715553, by rfl⟩ : syracuseStep 4574809 = 3431107) B3431107
theorem B6099745 : Blo 2255435 6099745 := bstep (se 2 (by rfl) ⟨2287404, by rfl⟩ : syracuseStep 6099745 = 4574809) B4574809
theorem B8132993 : Blo 2255435 8132993 := bstep (se 2 (by rfl) ⟨3049872, by rfl⟩ : syracuseStep 8132993 = 6099745) B6099745
theorem B5421995 : Blo 2255435 5421995 := bstep (se 1 (by rfl) ⟨4066496, by rfl⟩ : syracuseStep 5421995 = 8132993) B8132993
theorem B3614663 : Blo 2255435 3614663 := bstep (se 1 (by rfl) ⟨2710997, by rfl⟩ : syracuseStep 3614663 = 5421995) B5421995
theorem B9639101 : Blo 2255435 9639101 := bstep (se 3 (by rfl) ⟨1807331, by rfl⟩ : syracuseStep 9639101 = 3614663) B3614663
theorem B6426067 : Blo 2255435 6426067 := bstep (se 1 (by rfl) ⟨4819550, by rfl⟩ : syracuseStep 6426067 = 9639101) B9639101
theorem B8568089 : Blo 2255435 8568089 := bstep (se 2 (by rfl) ⟨3213033, by rfl⟩ : syracuseStep 8568089 = 6426067) B6426067
theorem B5712059 : Blo 2255435 5712059 := bstep (se 1 (by rfl) ⟨4284044, by rfl⟩ : syracuseStep 5712059 = 8568089) B8568089
theorem B3808039 : Blo 2255435 3808039 := bstep (se 1 (by rfl) ⟨2856029, by rfl⟩ : syracuseStep 3808039 = 5712059) B5712059
theorem B5077385 : Blo 2255435 5077385 := bstep (se 2 (by rfl) ⟨1904019, by rfl⟩ : syracuseStep 5077385 = 3808039) B3808039
theorem B3384923 : Blo 2255435 3384923 := bstep (se 1 (by rfl) ⟨2538692, by rfl⟩ : syracuseStep 3384923 = 5077385) B5077385
theorem B2256615 : Blo 2255435 2256615 := bstep (se 1 (by rfl) ⟨1692461, by rfl⟩ : syracuseStep 2256615 = 3384923) B3384923
theorem B2538697 : Blo 2255435 2538697 := bbase (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) (by norm_num)
theorem B3384929 : Blo 2255435 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B2256619 : Blo 2255435 2256619 := bstep (se 1 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 2256619 = 3384929) B3384929
theorem B21983957 : Blo 2255435 21983957 := bbase (se 7 (by rfl) ⟨257624, by rfl⟩ : syracuseStep 21983957 = 515249) (by norm_num)
theorem B14655971 : Blo 2255435 14655971 := bstep (se 1 (by rfl) ⟨10991978, by rfl⟩ : syracuseStep 14655971 = 21983957) B21983957
theorem B9770647 : Blo 2255435 9770647 := bstep (se 1 (by rfl) ⟨7327985, by rfl⟩ : syracuseStep 9770647 = 14655971) B14655971
theorem B13027529 : Blo 2255435 13027529 := bstep (se 2 (by rfl) ⟨4885323, by rfl⟩ : syracuseStep 13027529 = 9770647) B9770647
theorem B8685019 : Blo 2255435 8685019 := bstep (se 1 (by rfl) ⟨6513764, by rfl⟩ : syracuseStep 8685019 = 13027529) B13027529
theorem B11580025 : Blo 2255435 11580025 := bstep (se 2 (by rfl) ⟨4342509, by rfl⟩ : syracuseStep 11580025 = 8685019) B8685019
theorem B15440033 : Blo 2255435 15440033 := bstep (se 2 (by rfl) ⟨5790012, by rfl⟩ : syracuseStep 15440033 = 11580025) B11580025
theorem B10293355 : Blo 2255435 10293355 := bstep (se 1 (by rfl) ⟨7720016, by rfl⟩ : syracuseStep 10293355 = 15440033) B15440033
theorem B13724473 : Blo 2255435 13724473 := bstep (se 2 (by rfl) ⟨5146677, by rfl⟩ : syracuseStep 13724473 = 10293355) B10293355
theorem B18299297 : Blo 2255435 18299297 := bstep (se 2 (by rfl) ⟨6862236, by rfl⟩ : syracuseStep 18299297 = 13724473) B13724473
theorem B12199531 : Blo 2255435 12199531 := bstep (se 1 (by rfl) ⟨9149648, by rfl⟩ : syracuseStep 12199531 = 18299297) B18299297
theorem B16266041 : Blo 2255435 16266041 := bstep (se 2 (by rfl) ⟨6099765, by rfl⟩ : syracuseStep 16266041 = 12199531) B12199531
theorem B10844027 : Blo 2255435 10844027 := bstep (se 1 (by rfl) ⟨8133020, by rfl⟩ : syracuseStep 10844027 = 16266041) B16266041
theorem B7229351 : Blo 2255435 7229351 := bstep (se 1 (by rfl) ⟨5422013, by rfl⟩ : syracuseStep 7229351 = 10844027) B10844027
theorem B19278269 : Blo 2255435 19278269 := bstep (se 3 (by rfl) ⟨3614675, by rfl⟩ : syracuseStep 19278269 = 7229351) B7229351
theorem B12852179 : Blo 2255435 12852179 := bstep (se 1 (by rfl) ⟨9639134, by rfl⟩ : syracuseStep 12852179 = 19278269) B19278269
theorem B8568119 : Blo 2255435 8568119 := bstep (se 1 (by rfl) ⟨6426089, by rfl⟩ : syracuseStep 8568119 = 12852179) B12852179
theorem B5712079 : Blo 2255435 5712079 := bstep (se 1 (by rfl) ⟨4284059, by rfl⟩ : syracuseStep 5712079 = 8568119) B8568119
theorem B7616105 : Blo 2255435 7616105 := bstep (se 2 (by rfl) ⟨2856039, by rfl⟩ : syracuseStep 7616105 = 5712079) B5712079
theorem B5077403 : Blo 2255435 5077403 := bstep (se 1 (by rfl) ⟨3808052, by rfl⟩ : syracuseStep 5077403 = 7616105) B7616105
theorem B3384935 : Blo 2255435 3384935 := bstep (se 1 (by rfl) ⟨2538701, by rfl⟩ : syracuseStep 3384935 = 5077403) B5077403
theorem B2256623 : Blo 2255435 2256623 := bstep (se 1 (by rfl) ⟨1692467, by rfl⟩ : syracuseStep 2256623 = 3384935) B3384935
theorem B3384941 : Blo 2255435 3384941 := bbase (se 3 (by rfl) ⟨634676, by rfl⟩ : syracuseStep 3384941 = 1269353) (by norm_num)
theorem B2256627 : Blo 2255435 2256627 := bstep (se 1 (by rfl) ⟨1692470, by rfl⟩ : syracuseStep 2256627 = 3384941) B3384941
theorem B5077421 : Blo 2255435 5077421 := bbase (se 3 (by rfl) ⟨952016, by rfl⟩ : syracuseStep 5077421 = 1904033) (by norm_num)
theorem B3384947 : Blo 2255435 3384947 := bstep (se 1 (by rfl) ⟨2538710, by rfl⟩ : syracuseStep 3384947 = 5077421) B5077421
theorem B2256631 : Blo 2255435 2256631 := bstep (se 1 (by rfl) ⟨1692473, by rfl⟩ : syracuseStep 2256631 = 3384947) B3384947
theorem B2409797 : Blo 2255435 2409797 := bbase (se 4 (by rfl) ⟨225918, by rfl⟩ : syracuseStep 2409797 = 451837) (by norm_num)
theorem B6426125 : Blo 2255435 6426125 := bstep (se 3 (by rfl) ⟨1204898, by rfl⟩ : syracuseStep 6426125 = 2409797) B2409797
theorem B4284083 : Blo 2255435 4284083 := bstep (se 1 (by rfl) ⟨3213062, by rfl⟩ : syracuseStep 4284083 = 6426125) B6426125
theorem B2856055 : Blo 2255435 2856055 := bstep (se 1 (by rfl) ⟨2142041, by rfl⟩ : syracuseStep 2856055 = 4284083) B4284083
theorem B3808073 : Blo 2255435 3808073 := bstep (se 2 (by rfl) ⟨1428027, by rfl⟩ : syracuseStep 3808073 = 2856055) B2856055
theorem B2538715 : Blo 2255435 2538715 := bstep (se 1 (by rfl) ⟨1904036, by rfl⟩ : syracuseStep 2538715 = 3808073) B3808073
theorem B3384953 : Blo 2255435 3384953 := bstep (se 2 (by rfl) ⟨1269357, by rfl⟩ : syracuseStep 3384953 = 2538715) B2538715
theorem B2256635 : Blo 2255435 2256635 := bstep (se 1 (by rfl) ⟨1692476, by rfl⟩ : syracuseStep 2256635 = 3384953) B3384953
theorem B98928469 : Blo 2255435 98928469 := bbase (se 9 (by rfl) ⟨289829, by rfl⟩ : syracuseStep 98928469 = 579659) (by norm_num)
theorem B527618501 : Blo 2255435 527618501 := bstep (se 4 (by rfl) ⟨49464234, by rfl⟩ : syracuseStep 527618501 = 98928469) B98928469
theorem B351745667 : Blo 2255435 351745667 := bstep (se 1 (by rfl) ⟨263809250, by rfl⟩ : syracuseStep 351745667 = 527618501) B527618501
theorem B234497111 : Blo 2255435 234497111 := bstep (se 1 (by rfl) ⟨175872833, by rfl⟩ : syracuseStep 234497111 = 351745667) B351745667
theorem B625325629 : Blo 2255435 625325629 := bstep (se 3 (by rfl) ⟨117248555, by rfl⟩ : syracuseStep 625325629 = 234497111) B234497111
theorem B833767505 : Blo 2255435 833767505 := bstep (se 2 (by rfl) ⟨312662814, by rfl⟩ : syracuseStep 833767505 = 625325629) B625325629
theorem B555845003 : Blo 2255435 555845003 := bstep (se 1 (by rfl) ⟨416883752, by rfl⟩ : syracuseStep 555845003 = 833767505) B833767505
theorem B370563335 : Blo 2255435 370563335 := bstep (se 1 (by rfl) ⟨277922501, by rfl⟩ : syracuseStep 370563335 = 555845003) B555845003
theorem B247042223 : Blo 2255435 247042223 := bstep (se 1 (by rfl) ⟨185281667, by rfl⟩ : syracuseStep 247042223 = 370563335) B370563335
theorem B164694815 : Blo 2255435 164694815 := bstep (se 1 (by rfl) ⟨123521111, by rfl⟩ : syracuseStep 164694815 = 247042223) B247042223
theorem B109796543 : Blo 2255435 109796543 := bstep (se 1 (by rfl) ⟨82347407, by rfl⟩ : syracuseStep 109796543 = 164694815) B164694815
theorem B73197695 : Blo 2255435 73197695 := bstep (se 1 (by rfl) ⟨54898271, by rfl⟩ : syracuseStep 73197695 = 109796543) B109796543
theorem B48798463 : Blo 2255435 48798463 := bstep (se 1 (by rfl) ⟨36598847, by rfl⟩ : syracuseStep 48798463 = 73197695) B73197695
theorem B65064617 : Blo 2255435 65064617 := bstep (se 2 (by rfl) ⟨24399231, by rfl⟩ : syracuseStep 65064617 = 48798463) B48798463
theorem B43376411 : Blo 2255435 43376411 := bstep (se 1 (by rfl) ⟨32532308, by rfl⟩ : syracuseStep 43376411 = 65064617) B65064617
theorem B28917607 : Blo 2255435 28917607 := bstep (se 1 (by rfl) ⟨21688205, by rfl⟩ : syracuseStep 28917607 = 43376411) B43376411
theorem B38556809 : Blo 2255435 38556809 := bstep (se 2 (by rfl) ⟨14458803, by rfl⟩ : syracuseStep 38556809 = 28917607) B28917607
theorem B25704539 : Blo 2255435 25704539 := bstep (se 1 (by rfl) ⟨19278404, by rfl⟩ : syracuseStep 25704539 = 38556809) B38556809
theorem B17136359 : Blo 2255435 17136359 := bstep (se 1 (by rfl) ⟨12852269, by rfl⟩ : syracuseStep 17136359 = 25704539) B25704539
theorem B11424239 : Blo 2255435 11424239 := bstep (se 1 (by rfl) ⟨8568179, by rfl⟩ : syracuseStep 11424239 = 17136359) B17136359
theorem B7616159 : Blo 2255435 7616159 := bstep (se 1 (by rfl) ⟨5712119, by rfl⟩ : syracuseStep 7616159 = 11424239) B11424239
theorem B5077439 : Blo 2255435 5077439 := bstep (se 1 (by rfl) ⟨3808079, by rfl⟩ : syracuseStep 5077439 = 7616159) B7616159
theorem B3384959 : Blo 2255435 3384959 := bstep (se 1 (by rfl) ⟨2538719, by rfl⟩ : syracuseStep 3384959 = 5077439) B5077439
theorem B2256639 : Blo 2255435 2256639 := bstep (se 1 (by rfl) ⟨1692479, by rfl⟩ : syracuseStep 2256639 = 3384959) B3384959
theorem B3384965 : Blo 2255435 3384965 := bbase (se 4 (by rfl) ⟨317340, by rfl⟩ : syracuseStep 3384965 = 634681) (by norm_num)
theorem B2256643 : Blo 2255435 2256643 := bstep (se 1 (by rfl) ⟨1692482, by rfl⟩ : syracuseStep 2256643 = 3384965) B3384965
theorem B3808093 : Blo 2255435 3808093 := bbase (se 3 (by rfl) ⟨714017, by rfl⟩ : syracuseStep 3808093 = 1428035) (by norm_num)
theorem B5077457 : Blo 2255435 5077457 := bstep (se 2 (by rfl) ⟨1904046, by rfl⟩ : syracuseStep 5077457 = 3808093) B3808093
theorem B3384971 : Blo 2255435 3384971 := bstep (se 1 (by rfl) ⟨2538728, by rfl⟩ : syracuseStep 3384971 = 5077457) B5077457
theorem B2256647 : Blo 2255435 2256647 := bstep (se 1 (by rfl) ⟨1692485, by rfl⟩ : syracuseStep 2256647 = 3384971) B3384971
theorem B2538733 : Blo 2255435 2538733 := bbase (se 3 (by rfl) ⟨476012, by rfl⟩ : syracuseStep 2538733 = 952025) (by norm_num)
theorem B3384977 : Blo 2255435 3384977 := bstep (se 2 (by rfl) ⟨1269366, by rfl⟩ : syracuseStep 3384977 = 2538733) B2538733
theorem B2256651 : Blo 2255435 2256651 := bstep (se 1 (by rfl) ⟨1692488, by rfl⟩ : syracuseStep 2256651 = 3384977) B3384977
theorem B7616213 : Blo 2255435 7616213 := bbase (se 7 (by rfl) ⟨89252, by rfl⟩ : syracuseStep 7616213 = 178505) (by norm_num)
theorem B5077475 : Blo 2255435 5077475 := bstep (se 1 (by rfl) ⟨3808106, by rfl⟩ : syracuseStep 5077475 = 7616213) B7616213
theorem B3384983 : Blo 2255435 3384983 := bstep (se 1 (by rfl) ⟨2538737, by rfl⟩ : syracuseStep 3384983 = 5077475) B5077475
theorem B2256655 : Blo 2255435 2256655 := bstep (se 1 (by rfl) ⟨1692491, by rfl⟩ : syracuseStep 2256655 = 3384983) B3384983
theorem B3384989 : Blo 2255435 3384989 := bbase (se 3 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 3384989 = 1269371) (by norm_num)
theorem B2256659 : Blo 2255435 2256659 := bstep (se 1 (by rfl) ⟨1692494, by rfl⟩ : syracuseStep 2256659 = 3384989) B3384989
theorem B5077493 : Blo 2255435 5077493 := bbase (se 5 (by rfl) ⟨238007, by rfl⟩ : syracuseStep 5077493 = 476015) (by norm_num)
theorem B3384995 : Blo 2255435 3384995 := bstep (se 1 (by rfl) ⟨2538746, by rfl⟩ : syracuseStep 3384995 = 5077493) B5077493
theorem B2256663 : Blo 2255435 2256663 := bstep (se 1 (by rfl) ⟨1692497, by rfl⟩ : syracuseStep 2256663 = 3384995) B3384995
theorem B2573389 : Blo 2255435 2573389 := bbase (se 3 (by rfl) ⟨482510, by rfl⟩ : syracuseStep 2573389 = 965021) (by norm_num)
theorem B13724741 : Blo 2255435 13724741 := bstep (se 4 (by rfl) ⟨1286694, by rfl⟩ : syracuseStep 13724741 = 2573389) B2573389
theorem B36599309 : Blo 2255435 36599309 := bstep (se 3 (by rfl) ⟨6862370, by rfl⟩ : syracuseStep 36599309 = 13724741) B13724741
theorem B24399539 : Blo 2255435 24399539 := bstep (se 1 (by rfl) ⟨18299654, by rfl⟩ : syracuseStep 24399539 = 36599309) B36599309
theorem B16266359 : Blo 2255435 16266359 := bstep (se 1 (by rfl) ⟨12199769, by rfl⟩ : syracuseStep 16266359 = 24399539) B24399539
theorem B43376957 : Blo 2255435 43376957 := bstep (se 3 (by rfl) ⟨8133179, by rfl⟩ : syracuseStep 43376957 = 16266359) B16266359
theorem B28917971 : Blo 2255435 28917971 := bstep (se 1 (by rfl) ⟨21688478, by rfl⟩ : syracuseStep 28917971 = 43376957) B43376957
theorem B19278647 : Blo 2255435 19278647 := bstep (se 1 (by rfl) ⟨14458985, by rfl⟩ : syracuseStep 19278647 = 28917971) B28917971
theorem B12852431 : Blo 2255435 12852431 := bstep (se 1 (by rfl) ⟨9639323, by rfl⟩ : syracuseStep 12852431 = 19278647) B19278647
theorem B8568287 : Blo 2255435 8568287 := bstep (se 1 (by rfl) ⟨6426215, by rfl⟩ : syracuseStep 8568287 = 12852431) B12852431
theorem B5712191 : Blo 2255435 5712191 := bstep (se 1 (by rfl) ⟨4284143, by rfl⟩ : syracuseStep 5712191 = 8568287) B8568287
theorem B3808127 : Blo 2255435 3808127 := bstep (se 1 (by rfl) ⟨2856095, by rfl⟩ : syracuseStep 3808127 = 5712191) B5712191
theorem B2538751 : Blo 2255435 2538751 := bstep (se 1 (by rfl) ⟨1904063, by rfl⟩ : syracuseStep 2538751 = 3808127) B3808127
theorem B3385001 : Blo 2255435 3385001 := bstep (se 2 (by rfl) ⟨1269375, by rfl⟩ : syracuseStep 3385001 = 2538751) B2538751
theorem B2256667 : Blo 2255435 2256667 := bstep (se 1 (by rfl) ⟨1692500, by rfl⟩ : syracuseStep 2256667 = 3385001) B3385001
theorem B2711065 : Blo 2255435 2711065 := bbase (se 2 (by rfl) ⟨1016649, by rfl⟩ : syracuseStep 2711065 = 2033299) (by norm_num)
theorem B3614753 : Blo 2255435 3614753 := bstep (se 2 (by rfl) ⟨1355532, by rfl⟩ : syracuseStep 3614753 = 2711065) B2711065
theorem B2409835 : Blo 2255435 2409835 := bstep (se 1 (by rfl) ⟨1807376, by rfl⟩ : syracuseStep 2409835 = 3614753) B3614753
theorem B3213113 : Blo 2255435 3213113 := bstep (se 2 (by rfl) ⟨1204917, by rfl⟩ : syracuseStep 3213113 = 2409835) B2409835
theorem B8568301 : Blo 2255435 8568301 := bstep (se 3 (by rfl) ⟨1606556, by rfl⟩ : syracuseStep 8568301 = 3213113) B3213113
theorem B11424401 : Blo 2255435 11424401 := bstep (se 2 (by rfl) ⟨4284150, by rfl⟩ : syracuseStep 11424401 = 8568301) B8568301
theorem B7616267 : Blo 2255435 7616267 := bstep (se 1 (by rfl) ⟨5712200, by rfl⟩ : syracuseStep 7616267 = 11424401) B11424401
theorem B5077511 : Blo 2255435 5077511 := bstep (se 1 (by rfl) ⟨3808133, by rfl⟩ : syracuseStep 5077511 = 7616267) B7616267
theorem B3385007 : Blo 2255435 3385007 := bstep (se 1 (by rfl) ⟨2538755, by rfl⟩ : syracuseStep 3385007 = 5077511) B5077511
theorem B2256671 : Blo 2255435 2256671 := bstep (se 1 (by rfl) ⟨1692503, by rfl⟩ : syracuseStep 2256671 = 3385007) B3385007
theorem B3385013 : Blo 2255435 3385013 := bbase (se 5 (by rfl) ⟨158672, by rfl⟩ : syracuseStep 3385013 = 317345) (by norm_num)
theorem B2256675 : Blo 2255435 2256675 := bstep (se 1 (by rfl) ⟨1692506, by rfl⟩ : syracuseStep 2256675 = 3385013) B3385013
theorem B5712221 : Blo 2255435 5712221 := bbase (se 3 (by rfl) ⟨1071041, by rfl⟩ : syracuseStep 5712221 = 2142083) (by norm_num)
theorem B3808147 : Blo 2255435 3808147 := bstep (se 1 (by rfl) ⟨2856110, by rfl⟩ : syracuseStep 3808147 = 5712221) B5712221
theorem B5077529 : Blo 2255435 5077529 := bstep (se 2 (by rfl) ⟨1904073, by rfl⟩ : syracuseStep 5077529 = 3808147) B3808147
theorem B3385019 : Blo 2255435 3385019 := bstep (se 1 (by rfl) ⟨2538764, by rfl⟩ : syracuseStep 3385019 = 5077529) B5077529
theorem B2256679 : Blo 2255435 2256679 := bstep (se 1 (by rfl) ⟨1692509, by rfl⟩ : syracuseStep 2256679 = 3385019) B3385019
theorem B2538769 : Blo 2255435 2538769 := bbase (se 2 (by rfl) ⟨952038, by rfl⟩ : syracuseStep 2538769 = 1904077) (by norm_num)
theorem B3385025 : Blo 2255435 3385025 := bstep (se 2 (by rfl) ⟨1269384, by rfl⟩ : syracuseStep 3385025 = 2538769) B2538769
theorem B2256683 : Blo 2255435 2256683 := bstep (se 1 (by rfl) ⟨1692512, by rfl⟩ : syracuseStep 2256683 = 3385025) B3385025
theorem B4284181 : Blo 2255435 4284181 := bbase (se 6 (by rfl) ⟨100410, by rfl⟩ : syracuseStep 4284181 = 200821) (by norm_num)
theorem B5712241 : Blo 2255435 5712241 := bstep (se 2 (by rfl) ⟨2142090, by rfl⟩ : syracuseStep 5712241 = 4284181) B4284181
theorem B7616321 : Blo 2255435 7616321 := bstep (se 2 (by rfl) ⟨2856120, by rfl⟩ : syracuseStep 7616321 = 5712241) B5712241
theorem B5077547 : Blo 2255435 5077547 := bstep (se 1 (by rfl) ⟨3808160, by rfl⟩ : syracuseStep 5077547 = 7616321) B7616321
theorem B3385031 : Blo 2255435 3385031 := bstep (se 1 (by rfl) ⟨2538773, by rfl⟩ : syracuseStep 3385031 = 5077547) B5077547
theorem B2256687 : Blo 2255435 2256687 := bstep (se 1 (by rfl) ⟨1692515, by rfl⟩ : syracuseStep 2256687 = 3385031) B3385031
theorem B3385037 : Blo 2255435 3385037 := bbase (se 3 (by rfl) ⟨634694, by rfl⟩ : syracuseStep 3385037 = 1269389) (by norm_num)
theorem B2256691 : Blo 2255435 2256691 := bstep (se 1 (by rfl) ⟨1692518, by rfl⟩ : syracuseStep 2256691 = 3385037) B3385037
theorem B5077565 : Blo 2255435 5077565 := bbase (se 3 (by rfl) ⟨952043, by rfl⟩ : syracuseStep 5077565 = 1904087) (by norm_num)
theorem B3385043 : Blo 2255435 3385043 := bstep (se 1 (by rfl) ⟨2538782, by rfl⟩ : syracuseStep 3385043 = 5077565) B5077565
theorem B2256695 : Blo 2255435 2256695 := bstep (se 1 (by rfl) ⟨1692521, by rfl⟩ : syracuseStep 2256695 = 3385043) B3385043
theorem B3808181 : Blo 2255435 3808181 := bbase (se 5 (by rfl) ⟨178508, by rfl⟩ : syracuseStep 3808181 = 357017) (by norm_num)
theorem B2538787 : Blo 2255435 2538787 := bstep (se 1 (by rfl) ⟨1904090, by rfl⟩ : syracuseStep 2538787 = 3808181) B3808181
theorem B3385049 : Blo 2255435 3385049 := bstep (se 2 (by rfl) ⟨1269393, by rfl⟩ : syracuseStep 3385049 = 2538787) B2538787
theorem B2256699 : Blo 2255435 2256699 := bstep (se 1 (by rfl) ⟨1692524, by rfl⟩ : syracuseStep 2256699 = 3385049) B3385049
theorem B2409869 : Blo 2255435 2409869 := bbase (se 3 (by rfl) ⟨451850, by rfl⟩ : syracuseStep 2409869 = 903701) (by norm_num)
theorem B6426317 : Blo 2255435 6426317 := bstep (se 3 (by rfl) ⟨1204934, by rfl⟩ : syracuseStep 6426317 = 2409869) B2409869
theorem B17136845 : Blo 2255435 17136845 := bstep (se 3 (by rfl) ⟨3213158, by rfl⟩ : syracuseStep 17136845 = 6426317) B6426317
theorem B11424563 : Blo 2255435 11424563 := bstep (se 1 (by rfl) ⟨8568422, by rfl⟩ : syracuseStep 11424563 = 17136845) B17136845
theorem B7616375 : Blo 2255435 7616375 := bstep (se 1 (by rfl) ⟨5712281, by rfl⟩ : syracuseStep 7616375 = 11424563) B11424563
theorem B5077583 : Blo 2255435 5077583 := bstep (se 1 (by rfl) ⟨3808187, by rfl⟩ : syracuseStep 5077583 = 7616375) B7616375
theorem B3385055 : Blo 2255435 3385055 := bstep (se 1 (by rfl) ⟨2538791, by rfl⟩ : syracuseStep 3385055 = 5077583) B5077583
theorem B2256703 : Blo 2255435 2256703 := bstep (se 1 (by rfl) ⟨1692527, by rfl⟩ : syracuseStep 2256703 = 3385055) B3385055
theorem B3385061 : Blo 2255435 3385061 := bbase (se 4 (by rfl) ⟨317349, by rfl⟩ : syracuseStep 3385061 = 634699) (by norm_num)
theorem B2256707 : Blo 2255435 2256707 := bstep (se 1 (by rfl) ⟨1692530, by rfl⟩ : syracuseStep 2256707 = 3385061) B3385061
theorem B6426341 : Blo 2255435 6426341 := bbase (se 4 (by rfl) ⟨602469, by rfl⟩ : syracuseStep 6426341 = 1204939) (by norm_num)
theorem B4284227 : Blo 2255435 4284227 := bstep (se 1 (by rfl) ⟨3213170, by rfl⟩ : syracuseStep 4284227 = 6426341) B6426341
theorem B2856151 : Blo 2255435 2856151 := bstep (se 1 (by rfl) ⟨2142113, by rfl⟩ : syracuseStep 2856151 = 4284227) B4284227
theorem B3808201 : Blo 2255435 3808201 := bstep (se 2 (by rfl) ⟨1428075, by rfl⟩ : syracuseStep 3808201 = 2856151) B2856151
theorem B5077601 : Blo 2255435 5077601 := bstep (se 2 (by rfl) ⟨1904100, by rfl⟩ : syracuseStep 5077601 = 3808201) B3808201
theorem B3385067 : Blo 2255435 3385067 := bstep (se 1 (by rfl) ⟨2538800, by rfl⟩ : syracuseStep 3385067 = 5077601) B5077601
theorem B2256711 : Blo 2255435 2256711 := bstep (se 1 (by rfl) ⟨1692533, by rfl⟩ : syracuseStep 2256711 = 3385067) B3385067
theorem B2538805 : Blo 2255435 2538805 := bbase (se 5 (by rfl) ⟨119006, by rfl⟩ : syracuseStep 2538805 = 238013) (by norm_num)
theorem B3385073 : Blo 2255435 3385073 := bstep (se 2 (by rfl) ⟨1269402, by rfl⟩ : syracuseStep 3385073 = 2538805) B2538805
theorem B2256715 : Blo 2255435 2256715 := bstep (se 1 (by rfl) ⟨1692536, by rfl⟩ : syracuseStep 2256715 = 3385073) B3385073
theorem B2856161 : Blo 2255435 2856161 := bbase (se 2 (by rfl) ⟨1071060, by rfl⟩ : syracuseStep 2856161 = 2142121) (by norm_num)
theorem B7616429 : Blo 2255435 7616429 := bstep (se 3 (by rfl) ⟨1428080, by rfl⟩ : syracuseStep 7616429 = 2856161) B2856161
theorem B5077619 : Blo 2255435 5077619 := bstep (se 1 (by rfl) ⟨3808214, by rfl⟩ : syracuseStep 5077619 = 7616429) B7616429
theorem B3385079 : Blo 2255435 3385079 := bstep (se 1 (by rfl) ⟨2538809, by rfl⟩ : syracuseStep 3385079 = 5077619) B5077619
theorem B2256719 : Blo 2255435 2256719 := bstep (se 1 (by rfl) ⟨1692539, by rfl⟩ : syracuseStep 2256719 = 3385079) B3385079
theorem B3385085 : Blo 2255435 3385085 := bbase (se 3 (by rfl) ⟨634703, by rfl⟩ : syracuseStep 3385085 = 1269407) (by norm_num)
theorem B2256723 : Blo 2255435 2256723 := bstep (se 1 (by rfl) ⟨1692542, by rfl⟩ : syracuseStep 2256723 = 3385085) B3385085
theorem B5077637 : Blo 2255435 5077637 := bbase (se 4 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 5077637 = 952057) (by norm_num)
theorem B3385091 : Blo 2255435 3385091 := bstep (se 1 (by rfl) ⟨2538818, by rfl⟩ : syracuseStep 3385091 = 5077637) B5077637
theorem B2256727 : Blo 2255435 2256727 := bstep (se 1 (by rfl) ⟨1692545, by rfl⟩ : syracuseStep 2256727 = 3385091) B3385091
theorem B10844549 : Blo 2255435 10844549 := bbase (se 4 (by rfl) ⟨1016676, by rfl⟩ : syracuseStep 10844549 = 2033353) (by norm_num)
theorem B7229699 : Blo 2255435 7229699 := bstep (se 1 (by rfl) ⟨5422274, by rfl⟩ : syracuseStep 7229699 = 10844549) B10844549
theorem B4819799 : Blo 2255435 4819799 := bstep (se 1 (by rfl) ⟨3614849, by rfl⟩ : syracuseStep 4819799 = 7229699) B7229699
theorem B3213199 : Blo 2255435 3213199 := bstep (se 1 (by rfl) ⟨2409899, by rfl⟩ : syracuseStep 3213199 = 4819799) B4819799
theorem B4284265 : Blo 2255435 4284265 := bstep (se 2 (by rfl) ⟨1606599, by rfl⟩ : syracuseStep 4284265 = 3213199) B3213199
theorem B5712353 : Blo 2255435 5712353 := bstep (se 2 (by rfl) ⟨2142132, by rfl⟩ : syracuseStep 5712353 = 4284265) B4284265
theorem B3808235 : Blo 2255435 3808235 := bstep (se 1 (by rfl) ⟨2856176, by rfl⟩ : syracuseStep 3808235 = 5712353) B5712353
theorem B2538823 : Blo 2255435 2538823 := bstep (se 1 (by rfl) ⟨1904117, by rfl⟩ : syracuseStep 2538823 = 3808235) B3808235
theorem B3385097 : Blo 2255435 3385097 := bstep (se 2 (by rfl) ⟨1269411, by rfl⟩ : syracuseStep 3385097 = 2538823) B2538823
theorem B2256731 : Blo 2255435 2256731 := bstep (se 1 (by rfl) ⟨1692548, by rfl⟩ : syracuseStep 2256731 = 3385097) B3385097
theorem B11424725 : Blo 2255435 11424725 := bbase (se 7 (by rfl) ⟨133883, by rfl⟩ : syracuseStep 11424725 = 267767) (by norm_num)
theorem B7616483 : Blo 2255435 7616483 := bstep (se 1 (by rfl) ⟨5712362, by rfl⟩ : syracuseStep 7616483 = 11424725) B11424725
theorem B5077655 : Blo 2255435 5077655 := bstep (se 1 (by rfl) ⟨3808241, by rfl⟩ : syracuseStep 5077655 = 7616483) B7616483
theorem B3385103 : Blo 2255435 3385103 := bstep (se 1 (by rfl) ⟨2538827, by rfl⟩ : syracuseStep 3385103 = 5077655) B5077655
theorem B2256735 : Blo 2255435 2256735 := bstep (se 1 (by rfl) ⟨1692551, by rfl⟩ : syracuseStep 2256735 = 3385103) B3385103
theorem B3385109 : Blo 2255435 3385109 := bbase (se 6 (by rfl) ⟨79338, by rfl⟩ : syracuseStep 3385109 = 158677) (by norm_num)
theorem B2256739 : Blo 2255435 2256739 := bstep (se 1 (by rfl) ⟨1692554, by rfl⟩ : syracuseStep 2256739 = 3385109) B3385109
theorem B117253973 : Blo 2255435 117253973 := bbase (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) (by norm_num)
theorem B78169315 : Blo 2255435 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B104225753 : Blo 2255435 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B69483835 : Blo 2255435 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B370580453 : Blo 2255435 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B247053635 : Blo 2255435 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B164702423 : Blo 2255435 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B109801615 : Blo 2255435 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B146402153 : Blo 2255435 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B97601435 : Blo 2255435 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B65067623 : Blo 2255435 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B43378415 : Blo 2255435 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B28918943 : Blo 2255435 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B19279295 : Blo 2255435 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B12852863 : Blo 2255435 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B8568575 : Blo 2255435 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B5712383 : Blo 2255435 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B3808255 : Blo 2255435 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B5077673 : Blo 2255435 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B3385115 : Blo 2255435 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B2256743 : Blo 2255435 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B2538841 : Blo 2255435 2538841 := bbase (se 2 (by rfl) ⟨952065, by rfl⟩ : syracuseStep 2538841 = 1904131) (by norm_num)
theorem B3385121 : Blo 2255435 3385121 := bstep (se 2 (by rfl) ⟨1269420, by rfl⟩ : syracuseStep 3385121 = 2538841) B2538841
theorem B2256747 : Blo 2255435 2256747 := bstep (se 1 (by rfl) ⟨1692560, by rfl⟩ : syracuseStep 2256747 = 3385121) B3385121
theorem B2711161 : Blo 2255435 2711161 := bbase (se 2 (by rfl) ⟨1016685, by rfl⟩ : syracuseStep 2711161 = 2033371) (by norm_num)
theorem B3614881 : Blo 2255435 3614881 := bstep (se 2 (by rfl) ⟨1355580, by rfl⟩ : syracuseStep 3614881 = 2711161) B2711161
theorem B4819841 : Blo 2255435 4819841 := bstep (se 2 (by rfl) ⟨1807440, by rfl⟩ : syracuseStep 4819841 = 3614881) B3614881
theorem B3213227 : Blo 2255435 3213227 := bstep (se 1 (by rfl) ⟨2409920, by rfl⟩ : syracuseStep 3213227 = 4819841) B4819841
theorem B8568605 : Blo 2255435 8568605 := bstep (se 3 (by rfl) ⟨1606613, by rfl⟩ : syracuseStep 8568605 = 3213227) B3213227
theorem B5712403 : Blo 2255435 5712403 := bstep (se 1 (by rfl) ⟨4284302, by rfl⟩ : syracuseStep 5712403 = 8568605) B8568605
theorem B7616537 : Blo 2255435 7616537 := bstep (se 2 (by rfl) ⟨2856201, by rfl⟩ : syracuseStep 7616537 = 5712403) B5712403
theorem B5077691 : Blo 2255435 5077691 := bstep (se 1 (by rfl) ⟨3808268, by rfl⟩ : syracuseStep 5077691 = 7616537) B7616537
theorem B3385127 : Blo 2255435 3385127 := bstep (se 1 (by rfl) ⟨2538845, by rfl⟩ : syracuseStep 3385127 = 5077691) B5077691
theorem B2256751 : Blo 2255435 2256751 := bstep (se 1 (by rfl) ⟨1692563, by rfl⟩ : syracuseStep 2256751 = 3385127) B3385127
theorem B3385133 : Blo 2255435 3385133 := bbase (se 3 (by rfl) ⟨634712, by rfl⟩ : syracuseStep 3385133 = 1269425) (by norm_num)
theorem B2256755 : Blo 2255435 2256755 := bstep (se 1 (by rfl) ⟨1692566, by rfl⟩ : syracuseStep 2256755 = 3385133) B3385133
theorem B5077709 : Blo 2255435 5077709 := bbase (se 3 (by rfl) ⟨952070, by rfl⟩ : syracuseStep 5077709 = 1904141) (by norm_num)
theorem B3385139 : Blo 2255435 3385139 := bstep (se 1 (by rfl) ⟨2538854, by rfl⟩ : syracuseStep 3385139 = 5077709) B5077709
theorem B2256759 : Blo 2255435 2256759 := bstep (se 1 (by rfl) ⟨1692569, by rfl⟩ : syracuseStep 2256759 = 3385139) B3385139
theorem B2856217 : Blo 2255435 2856217 := bbase (se 2 (by rfl) ⟨1071081, by rfl⟩ : syracuseStep 2856217 = 2142163) (by norm_num)
theorem B3808289 : Blo 2255435 3808289 := bstep (se 2 (by rfl) ⟨1428108, by rfl⟩ : syracuseStep 3808289 = 2856217) B2856217
theorem B2538859 : Blo 2255435 2538859 := bstep (se 1 (by rfl) ⟨1904144, by rfl⟩ : syracuseStep 2538859 = 3808289) B3808289
theorem B3385145 : Blo 2255435 3385145 := bstep (se 2 (by rfl) ⟨1269429, by rfl⟩ : syracuseStep 3385145 = 2538859) B2538859
theorem B2256763 : Blo 2255435 2256763 := bstep (se 1 (by rfl) ⟨1692572, by rfl⟩ : syracuseStep 2256763 = 3385145) B3385145
theorem B9639749 : Blo 2255435 9639749 := bbase (se 4 (by rfl) ⟨903726, by rfl⟩ : syracuseStep 9639749 = 1807453) (by norm_num)
theorem B25705997 : Blo 2255435 25705997 := bstep (se 3 (by rfl) ⟨4819874, by rfl⟩ : syracuseStep 25705997 = 9639749) B9639749
theorem B17137331 : Blo 2255435 17137331 := bstep (se 1 (by rfl) ⟨12852998, by rfl⟩ : syracuseStep 17137331 = 25705997) B25705997
theorem B11424887 : Blo 2255435 11424887 := bstep (se 1 (by rfl) ⟨8568665, by rfl⟩ : syracuseStep 11424887 = 17137331) B17137331
theorem B7616591 : Blo 2255435 7616591 := bstep (se 1 (by rfl) ⟨5712443, by rfl⟩ : syracuseStep 7616591 = 11424887) B11424887
theorem B5077727 : Blo 2255435 5077727 := bstep (se 1 (by rfl) ⟨3808295, by rfl⟩ : syracuseStep 5077727 = 7616591) B7616591
theorem B3385151 : Blo 2255435 3385151 := bstep (se 1 (by rfl) ⟨2538863, by rfl⟩ : syracuseStep 3385151 = 5077727) B5077727
theorem B2256767 : Blo 2255435 2256767 := bstep (se 1 (by rfl) ⟨1692575, by rfl⟩ : syracuseStep 2256767 = 3385151) B3385151
theorem B3385157 : Blo 2255435 3385157 := bbase (se 4 (by rfl) ⟨317358, by rfl⟩ : syracuseStep 3385157 = 634717) (by norm_num)
theorem B2256771 : Blo 2255435 2256771 := bstep (se 1 (by rfl) ⟨1692578, by rfl⟩ : syracuseStep 2256771 = 3385157) B3385157
theorem B3808309 : Blo 2255435 3808309 := bbase (se 5 (by rfl) ⟨178514, by rfl⟩ : syracuseStep 3808309 = 357029) (by norm_num)
theorem B5077745 : Blo 2255435 5077745 := bstep (se 2 (by rfl) ⟨1904154, by rfl⟩ : syracuseStep 5077745 = 3808309) B3808309
theorem B3385163 : Blo 2255435 3385163 := bstep (se 1 (by rfl) ⟨2538872, by rfl⟩ : syracuseStep 3385163 = 5077745) B5077745
theorem B2256775 : Blo 2255435 2256775 := bstep (se 1 (by rfl) ⟨1692581, by rfl⟩ : syracuseStep 2256775 = 3385163) B3385163
theorem B2538877 : Blo 2255435 2538877 := bbase (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) (by norm_num)
theorem B3385169 : Blo 2255435 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B2256779 : Blo 2255435 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B7616645 : Blo 2255435 7616645 := bbase (se 4 (by rfl) ⟨714060, by rfl⟩ : syracuseStep 7616645 = 1428121) (by norm_num)
theorem B5077763 : Blo 2255435 5077763 := bstep (se 1 (by rfl) ⟨3808322, by rfl⟩ : syracuseStep 5077763 = 7616645) B7616645
theorem B3385175 : Blo 2255435 3385175 := bstep (se 1 (by rfl) ⟨2538881, by rfl⟩ : syracuseStep 3385175 = 5077763) B5077763
theorem B2256783 : Blo 2255435 2256783 := bstep (se 1 (by rfl) ⟨1692587, by rfl⟩ : syracuseStep 2256783 = 3385175) B3385175
theorem B3385181 : Blo 2255435 3385181 := bbase (se 3 (by rfl) ⟨634721, by rfl⟩ : syracuseStep 3385181 = 1269443) (by norm_num)
theorem B2256787 : Blo 2255435 2256787 := bstep (se 1 (by rfl) ⟨1692590, by rfl⟩ : syracuseStep 2256787 = 3385181) B3385181
theorem B5077781 : Blo 2255435 5077781 := bbase (se 6 (by rfl) ⟨119010, by rfl⟩ : syracuseStep 5077781 = 238021) (by norm_num)
theorem B3385187 : Blo 2255435 3385187 := bstep (se 1 (by rfl) ⟨2538890, by rfl⟩ : syracuseStep 3385187 = 5077781) B5077781
theorem B2256791 : Blo 2255435 2256791 := bstep (se 1 (by rfl) ⟨1692593, by rfl⟩ : syracuseStep 2256791 = 3385187) B3385187
theorem B8568773 : Blo 2255435 8568773 := bbase (se 4 (by rfl) ⟨803322, by rfl⟩ : syracuseStep 8568773 = 1606645) (by norm_num)
theorem B5712515 : Blo 2255435 5712515 := bstep (se 1 (by rfl) ⟨4284386, by rfl⟩ : syracuseStep 5712515 = 8568773) B8568773
theorem B3808343 : Blo 2255435 3808343 := bstep (se 1 (by rfl) ⟨2856257, by rfl⟩ : syracuseStep 3808343 = 5712515) B5712515
theorem B2538895 : Blo 2255435 2538895 := bstep (se 1 (by rfl) ⟨1904171, by rfl⟩ : syracuseStep 2538895 = 3808343) B3808343
theorem B3385193 : Blo 2255435 3385193 := bstep (se 2 (by rfl) ⟨1269447, by rfl⟩ : syracuseStep 3385193 = 2538895) B2538895
theorem B2256795 : Blo 2255435 2256795 := bstep (se 1 (by rfl) ⟨1692596, by rfl⟩ : syracuseStep 2256795 = 3385193) B3385193
theorem B18300725 : Blo 2255435 18300725 := bbase (se 5 (by rfl) ⟨857846, by rfl⟩ : syracuseStep 18300725 = 1715693) (by norm_num)
theorem B12200483 : Blo 2255435 12200483 := bstep (se 1 (by rfl) ⟨9150362, by rfl⟩ : syracuseStep 12200483 = 18300725) B18300725
theorem B8133655 : Blo 2255435 8133655 := bstep (se 1 (by rfl) ⟨6100241, by rfl⟩ : syracuseStep 8133655 = 12200483) B12200483
theorem B10844873 : Blo 2255435 10844873 := bstep (se 2 (by rfl) ⟨4066827, by rfl⟩ : syracuseStep 10844873 = 8133655) B8133655
theorem B7229915 : Blo 2255435 7229915 := bstep (se 1 (by rfl) ⟨5422436, by rfl⟩ : syracuseStep 7229915 = 10844873) B10844873
theorem B4819943 : Blo 2255435 4819943 := bstep (se 1 (by rfl) ⟨3614957, by rfl⟩ : syracuseStep 4819943 = 7229915) B7229915
theorem B12853181 : Blo 2255435 12853181 := bstep (se 3 (by rfl) ⟨2409971, by rfl⟩ : syracuseStep 12853181 = 4819943) B4819943
theorem B8568787 : Blo 2255435 8568787 := bstep (se 1 (by rfl) ⟨6426590, by rfl⟩ : syracuseStep 8568787 = 12853181) B12853181
theorem B11425049 : Blo 2255435 11425049 := bstep (se 2 (by rfl) ⟨4284393, by rfl⟩ : syracuseStep 11425049 = 8568787) B8568787
theorem B7616699 : Blo 2255435 7616699 := bstep (se 1 (by rfl) ⟨5712524, by rfl⟩ : syracuseStep 7616699 = 11425049) B11425049
theorem B5077799 : Blo 2255435 5077799 := bstep (se 1 (by rfl) ⟨3808349, by rfl⟩ : syracuseStep 5077799 = 7616699) B7616699
theorem B3385199 : Blo 2255435 3385199 := bstep (se 1 (by rfl) ⟨2538899, by rfl⟩ : syracuseStep 3385199 = 5077799) B5077799
theorem B2256799 : Blo 2255435 2256799 := bstep (se 1 (by rfl) ⟨1692599, by rfl⟩ : syracuseStep 2256799 = 3385199) B3385199
theorem B3385205 : Blo 2255435 3385205 := bbase (se 5 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 3385205 = 317363) (by norm_num)
theorem B2256803 : Blo 2255435 2256803 := bstep (se 1 (by rfl) ⟨1692602, by rfl⟩ : syracuseStep 2256803 = 3385205) B3385205
theorem B13028597 : Blo 2255435 13028597 := bbase (se 5 (by rfl) ⟨610715, by rfl⟩ : syracuseStep 13028597 = 1221431) (by norm_num)
theorem B8685731 : Blo 2255435 8685731 := bstep (se 1 (by rfl) ⟨6514298, by rfl⟩ : syracuseStep 8685731 = 13028597) B13028597
theorem B23161949 : Blo 2255435 23161949 := bstep (se 3 (by rfl) ⟨4342865, by rfl⟩ : syracuseStep 23161949 = 8685731) B8685731
theorem B15441299 : Blo 2255435 15441299 := bstep (se 1 (by rfl) ⟨11580974, by rfl⟩ : syracuseStep 15441299 = 23161949) B23161949
theorem B10294199 : Blo 2255435 10294199 := bstep (se 1 (by rfl) ⟨7720649, by rfl⟩ : syracuseStep 10294199 = 15441299) B15441299
theorem B6862799 : Blo 2255435 6862799 := bstep (se 1 (by rfl) ⟨5147099, by rfl⟩ : syracuseStep 6862799 = 10294199) B10294199
theorem B4575199 : Blo 2255435 4575199 := bstep (se 1 (by rfl) ⟨3431399, by rfl⟩ : syracuseStep 4575199 = 6862799) B6862799
theorem B6100265 : Blo 2255435 6100265 := bstep (se 2 (by rfl) ⟨2287599, by rfl⟩ : syracuseStep 6100265 = 4575199) B4575199
theorem B4066843 : Blo 2255435 4066843 := bstep (se 1 (by rfl) ⟨3050132, by rfl⟩ : syracuseStep 4066843 = 6100265) B6100265
theorem B5422457 : Blo 2255435 5422457 := bstep (se 2 (by rfl) ⟨2033421, by rfl⟩ : syracuseStep 5422457 = 4066843) B4066843
theorem B3614971 : Blo 2255435 3614971 := bstep (se 1 (by rfl) ⟨2711228, by rfl⟩ : syracuseStep 3614971 = 5422457) B5422457
theorem B4819961 : Blo 2255435 4819961 := bstep (se 2 (by rfl) ⟨1807485, by rfl⟩ : syracuseStep 4819961 = 3614971) B3614971
theorem B3213307 : Blo 2255435 3213307 := bstep (se 1 (by rfl) ⟨2409980, by rfl⟩ : syracuseStep 3213307 = 4819961) B4819961
theorem B4284409 : Blo 2255435 4284409 := bstep (se 2 (by rfl) ⟨1606653, by rfl⟩ : syracuseStep 4284409 = 3213307) B3213307
theorem B5712545 : Blo 2255435 5712545 := bstep (se 2 (by rfl) ⟨2142204, by rfl⟩ : syracuseStep 5712545 = 4284409) B4284409
theorem B3808363 : Blo 2255435 3808363 := bstep (se 1 (by rfl) ⟨2856272, by rfl⟩ : syracuseStep 3808363 = 5712545) B5712545
theorem B5077817 : Blo 2255435 5077817 := bstep (se 2 (by rfl) ⟨1904181, by rfl⟩ : syracuseStep 5077817 = 3808363) B3808363
theorem B3385211 : Blo 2255435 3385211 := bstep (se 1 (by rfl) ⟨2538908, by rfl⟩ : syracuseStep 3385211 = 5077817) B5077817
theorem B2256807 : Blo 2255435 2256807 := bstep (se 1 (by rfl) ⟨1692605, by rfl⟩ : syracuseStep 2256807 = 3385211) B3385211
theorem B2538913 : Blo 2255435 2538913 := bbase (se 2 (by rfl) ⟨952092, by rfl⟩ : syracuseStep 2538913 = 1904185) (by norm_num)
theorem B3385217 : Blo 2255435 3385217 := bstep (se 2 (by rfl) ⟨1269456, by rfl⟩ : syracuseStep 3385217 = 2538913) B2538913
theorem B2256811 : Blo 2255435 2256811 := bstep (se 1 (by rfl) ⟨1692608, by rfl⟩ : syracuseStep 2256811 = 3385217) B3385217
theorem B5712565 : Blo 2255435 5712565 := bbase (se 5 (by rfl) ⟨267776, by rfl⟩ : syracuseStep 5712565 = 535553) (by norm_num)
theorem B7616753 : Blo 2255435 7616753 := bstep (se 2 (by rfl) ⟨2856282, by rfl⟩ : syracuseStep 7616753 = 5712565) B5712565
theorem B5077835 : Blo 2255435 5077835 := bstep (se 1 (by rfl) ⟨3808376, by rfl⟩ : syracuseStep 5077835 = 7616753) B7616753
theorem B3385223 : Blo 2255435 3385223 := bstep (se 1 (by rfl) ⟨2538917, by rfl⟩ : syracuseStep 3385223 = 5077835) B5077835
theorem B2256815 : Blo 2255435 2256815 := bstep (se 1 (by rfl) ⟨1692611, by rfl⟩ : syracuseStep 2256815 = 3385223) B3385223
theorem B3385229 : Blo 2255435 3385229 := bbase (se 3 (by rfl) ⟨634730, by rfl⟩ : syracuseStep 3385229 = 1269461) (by norm_num)
theorem B2256819 : Blo 2255435 2256819 := bstep (se 1 (by rfl) ⟨1692614, by rfl⟩ : syracuseStep 2256819 = 3385229) B3385229
theorem B5077853 : Blo 2255435 5077853 := bbase (se 3 (by rfl) ⟨952097, by rfl⟩ : syracuseStep 5077853 = 1904195) (by norm_num)
theorem B3385235 : Blo 2255435 3385235 := bstep (se 1 (by rfl) ⟨2538926, by rfl⟩ : syracuseStep 3385235 = 5077853) B5077853
theorem B2256823 : Blo 2255435 2256823 := bstep (se 1 (by rfl) ⟨1692617, by rfl⟩ : syracuseStep 2256823 = 3385235) B3385235
theorem B3808397 : Blo 2255435 3808397 := bbase (se 3 (by rfl) ⟨714074, by rfl⟩ : syracuseStep 3808397 = 1428149) (by norm_num)
theorem B2538931 : Blo 2255435 2538931 := bstep (se 1 (by rfl) ⟨1904198, by rfl⟩ : syracuseStep 2538931 = 3808397) B3808397
theorem B3385241 : Blo 2255435 3385241 := bstep (se 2 (by rfl) ⟨1269465, by rfl⟩ : syracuseStep 3385241 = 2538931) B2538931
theorem B2256827 : Blo 2255435 2256827 := bstep (se 1 (by rfl) ⟨1692620, by rfl⟩ : syracuseStep 2256827 = 3385241) B3385241
theorem B4066885 : Blo 2255435 4066885 := bbase (se 4 (by rfl) ⟨381270, by rfl⟩ : syracuseStep 4066885 = 762541) (by norm_num)
theorem B5422513 : Blo 2255435 5422513 := bstep (se 2 (by rfl) ⟨2033442, by rfl⟩ : syracuseStep 5422513 = 4066885) B4066885
theorem B7230017 : Blo 2255435 7230017 := bstep (se 2 (by rfl) ⟨2711256, by rfl⟩ : syracuseStep 7230017 = 5422513) B5422513
theorem B19280045 : Blo 2255435 19280045 := bstep (se 3 (by rfl) ⟨3615008, by rfl⟩ : syracuseStep 19280045 = 7230017) B7230017
theorem B12853363 : Blo 2255435 12853363 := bstep (se 1 (by rfl) ⟨9640022, by rfl⟩ : syracuseStep 12853363 = 19280045) B19280045
theorem B17137817 : Blo 2255435 17137817 := bstep (se 2 (by rfl) ⟨6426681, by rfl⟩ : syracuseStep 17137817 = 12853363) B12853363
theorem B11425211 : Blo 2255435 11425211 := bstep (se 1 (by rfl) ⟨8568908, by rfl⟩ : syracuseStep 11425211 = 17137817) B17137817
theorem B7616807 : Blo 2255435 7616807 := bstep (se 1 (by rfl) ⟨5712605, by rfl⟩ : syracuseStep 7616807 = 11425211) B11425211
theorem B5077871 : Blo 2255435 5077871 := bstep (se 1 (by rfl) ⟨3808403, by rfl⟩ : syracuseStep 5077871 = 7616807) B7616807
theorem B3385247 : Blo 2255435 3385247 := bstep (se 1 (by rfl) ⟨2538935, by rfl⟩ : syracuseStep 3385247 = 5077871) B5077871
theorem B2256831 : Blo 2255435 2256831 := bstep (se 1 (by rfl) ⟨1692623, by rfl⟩ : syracuseStep 2256831 = 3385247) B3385247
theorem B3385253 : Blo 2255435 3385253 := bbase (se 4 (by rfl) ⟨317367, by rfl⟩ : syracuseStep 3385253 = 634735) (by norm_num)
theorem B2256835 : Blo 2255435 2256835 := bstep (se 1 (by rfl) ⟨1692626, by rfl⟩ : syracuseStep 2256835 = 3385253) B3385253
theorem B2856313 : Blo 2255435 2856313 := bbase (se 2 (by rfl) ⟨1071117, by rfl⟩ : syracuseStep 2856313 = 2142235) (by norm_num)
theorem B3808417 : Blo 2255435 3808417 := bstep (se 2 (by rfl) ⟨1428156, by rfl⟩ : syracuseStep 3808417 = 2856313) B2856313
theorem B5077889 : Blo 2255435 5077889 := bstep (se 2 (by rfl) ⟨1904208, by rfl⟩ : syracuseStep 5077889 = 3808417) B3808417
theorem B3385259 : Blo 2255435 3385259 := bstep (se 1 (by rfl) ⟨2538944, by rfl⟩ : syracuseStep 3385259 = 5077889) B5077889
theorem B2256839 : Blo 2255435 2256839 := bstep (se 1 (by rfl) ⟨1692629, by rfl⟩ : syracuseStep 2256839 = 3385259) B3385259
theorem B2538949 : Blo 2255435 2538949 := bbase (se 4 (by rfl) ⟨238026, by rfl⟩ : syracuseStep 2538949 = 476053) (by norm_num)
theorem B3385265 : Blo 2255435 3385265 := bstep (se 2 (by rfl) ⟨1269474, by rfl⟩ : syracuseStep 3385265 = 2538949) B2538949
theorem B2256843 : Blo 2255435 2256843 := bstep (se 1 (by rfl) ⟨1692632, by rfl⟩ : syracuseStep 2256843 = 3385265) B3385265
theorem B4284485 : Blo 2255435 4284485 := bbase (se 4 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 4284485 = 803341) (by norm_num)
theorem B2856323 : Blo 2255435 2856323 := bstep (se 1 (by rfl) ⟨2142242, by rfl⟩ : syracuseStep 2856323 = 4284485) B4284485
theorem B7616861 : Blo 2255435 7616861 := bstep (se 3 (by rfl) ⟨1428161, by rfl⟩ : syracuseStep 7616861 = 2856323) B2856323
theorem B5077907 : Blo 2255435 5077907 := bstep (se 1 (by rfl) ⟨3808430, by rfl⟩ : syracuseStep 5077907 = 7616861) B7616861
theorem B3385271 : Blo 2255435 3385271 := bstep (se 1 (by rfl) ⟨2538953, by rfl⟩ : syracuseStep 3385271 = 5077907) B5077907
theorem B2256847 : Blo 2255435 2256847 := bstep (se 1 (by rfl) ⟨1692635, by rfl⟩ : syracuseStep 2256847 = 3385271) B3385271
theorem B3385277 : Blo 2255435 3385277 := bbase (se 3 (by rfl) ⟨634739, by rfl⟩ : syracuseStep 3385277 = 1269479) (by norm_num)
theorem B2256851 : Blo 2255435 2256851 := bstep (se 1 (by rfl) ⟨1692638, by rfl⟩ : syracuseStep 2256851 = 3385277) B3385277
theorem B5077925 : Blo 2255435 5077925 := bbase (se 4 (by rfl) ⟨476055, by rfl⟩ : syracuseStep 5077925 = 952111) (by norm_num)
theorem B3385283 : Blo 2255435 3385283 := bstep (se 1 (by rfl) ⟨2538962, by rfl⟩ : syracuseStep 3385283 = 5077925) B5077925
theorem B2256855 : Blo 2255435 2256855 := bstep (se 1 (by rfl) ⟨1692641, by rfl⟩ : syracuseStep 2256855 = 3385283) B3385283
theorem B5712677 : Blo 2255435 5712677 := bbase (se 4 (by rfl) ⟨535563, by rfl⟩ : syracuseStep 5712677 = 1071127) (by norm_num)
theorem B3808451 : Blo 2255435 3808451 := bstep (se 1 (by rfl) ⟨2856338, by rfl⟩ : syracuseStep 3808451 = 5712677) B5712677
theorem B2538967 : Blo 2255435 2538967 := bstep (se 1 (by rfl) ⟨1904225, by rfl⟩ : syracuseStep 2538967 = 3808451) B3808451
theorem B3385289 : Blo 2255435 3385289 := bstep (se 2 (by rfl) ⟨1269483, by rfl⟩ : syracuseStep 3385289 = 2538967) B2538967
theorem B2256859 : Blo 2255435 2256859 := bstep (se 1 (by rfl) ⟨1692644, by rfl⟩ : syracuseStep 2256859 = 3385289) B3385289
theorem B6426773 : Blo 2255435 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B4284515 : Blo 2255435 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B11425373 : Blo 2255435 11425373 := bstep (se 3 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 11425373 = 4284515) B4284515
theorem B7616915 : Blo 2255435 7616915 := bstep (se 1 (by rfl) ⟨5712686, by rfl⟩ : syracuseStep 7616915 = 11425373) B11425373
theorem B5077943 : Blo 2255435 5077943 := bstep (se 1 (by rfl) ⟨3808457, by rfl⟩ : syracuseStep 5077943 = 7616915) B7616915
theorem B3385295 : Blo 2255435 3385295 := bstep (se 1 (by rfl) ⟨2538971, by rfl⟩ : syracuseStep 3385295 = 5077943) B5077943
theorem B2256863 : Blo 2255435 2256863 := bstep (se 1 (by rfl) ⟨1692647, by rfl⟩ : syracuseStep 2256863 = 3385295) B3385295
theorem B3385301 : Blo 2255435 3385301 := bbase (se 7 (by rfl) ⟨39671, by rfl⟩ : syracuseStep 3385301 = 79343) (by norm_num)
theorem B2256867 : Blo 2255435 2256867 := bstep (se 1 (by rfl) ⟨1692650, by rfl⟩ : syracuseStep 2256867 = 3385301) B3385301
theorem B8569061 : Blo 2255435 8569061 := bbase (se 4 (by rfl) ⟨803349, by rfl⟩ : syracuseStep 8569061 = 1606699) (by norm_num)
theorem B5712707 : Blo 2255435 5712707 := bstep (se 1 (by rfl) ⟨4284530, by rfl⟩ : syracuseStep 5712707 = 8569061) B8569061
theorem B3808471 : Blo 2255435 3808471 := bstep (se 1 (by rfl) ⟨2856353, by rfl⟩ : syracuseStep 3808471 = 5712707) B5712707
theorem B5077961 : Blo 2255435 5077961 := bstep (se 2 (by rfl) ⟨1904235, by rfl⟩ : syracuseStep 5077961 = 3808471) B3808471
theorem B3385307 : Blo 2255435 3385307 := bstep (se 1 (by rfl) ⟨2538980, by rfl⟩ : syracuseStep 3385307 = 5077961) B5077961
theorem B2256871 : Blo 2255435 2256871 := bstep (se 1 (by rfl) ⟨1692653, by rfl⟩ : syracuseStep 2256871 = 3385307) B3385307
theorem B2538985 : Blo 2255435 2538985 := bbase (se 2 (by rfl) ⟨952119, by rfl⟩ : syracuseStep 2538985 = 1904239) (by norm_num)
theorem B3385313 : Blo 2255435 3385313 := bstep (se 2 (by rfl) ⟨1269492, by rfl⟩ : syracuseStep 3385313 = 2538985) B2538985
theorem B2256875 : Blo 2255435 2256875 := bstep (se 1 (by rfl) ⟨1692656, by rfl⟩ : syracuseStep 2256875 = 3385313) B3385313
theorem B2410057 : Blo 2255435 2410057 := bbase (se 2 (by rfl) ⟨903771, by rfl⟩ : syracuseStep 2410057 = 1807543) (by norm_num)
theorem B12853637 : Blo 2255435 12853637 := bstep (se 4 (by rfl) ⟨1205028, by rfl⟩ : syracuseStep 12853637 = 2410057) B2410057
theorem B8569091 : Blo 2255435 8569091 := bstep (se 1 (by rfl) ⟨6426818, by rfl⟩ : syracuseStep 8569091 = 12853637) B12853637
theorem B5712727 : Blo 2255435 5712727 := bstep (se 1 (by rfl) ⟨4284545, by rfl⟩ : syracuseStep 5712727 = 8569091) B8569091
theorem B7616969 : Blo 2255435 7616969 := bstep (se 2 (by rfl) ⟨2856363, by rfl⟩ : syracuseStep 7616969 = 5712727) B5712727
theorem B5077979 : Blo 2255435 5077979 := bstep (se 1 (by rfl) ⟨3808484, by rfl⟩ : syracuseStep 5077979 = 7616969) B7616969
theorem B3385319 : Blo 2255435 3385319 := bstep (se 1 (by rfl) ⟨2538989, by rfl⟩ : syracuseStep 3385319 = 5077979) B5077979
theorem B2256879 : Blo 2255435 2256879 := bstep (se 1 (by rfl) ⟨1692659, by rfl⟩ : syracuseStep 2256879 = 3385319) B3385319
theorem B3385325 : Blo 2255435 3385325 := bbase (se 3 (by rfl) ⟨634748, by rfl⟩ : syracuseStep 3385325 = 1269497) (by norm_num)
theorem B2256883 : Blo 2255435 2256883 := bstep (se 1 (by rfl) ⟨1692662, by rfl⟩ : syracuseStep 2256883 = 3385325) B3385325
theorem B5077997 : Blo 2255435 5077997 := bbase (se 3 (by rfl) ⟨952124, by rfl⟩ : syracuseStep 5077997 = 1904249) (by norm_num)
theorem B3385331 : Blo 2255435 3385331 := bstep (se 1 (by rfl) ⟨2538998, by rfl⟩ : syracuseStep 3385331 = 5077997) B5077997
theorem B2256887 : Blo 2255435 2256887 := bstep (se 1 (by rfl) ⟨1692665, by rfl⟩ : syracuseStep 2256887 = 3385331) B3385331
theorem B4820141 : Blo 2255435 4820141 := bbase (se 3 (by rfl) ⟨903776, by rfl⟩ : syracuseStep 4820141 = 1807553) (by norm_num)
theorem B3213427 : Blo 2255435 3213427 := bstep (se 1 (by rfl) ⟨2410070, by rfl⟩ : syracuseStep 3213427 = 4820141) B4820141
theorem B4284569 : Blo 2255435 4284569 := bstep (se 2 (by rfl) ⟨1606713, by rfl⟩ : syracuseStep 4284569 = 3213427) B3213427
theorem B2856379 : Blo 2255435 2856379 := bstep (se 1 (by rfl) ⟨2142284, by rfl⟩ : syracuseStep 2856379 = 4284569) B4284569
theorem B3808505 : Blo 2255435 3808505 := bstep (se 2 (by rfl) ⟨1428189, by rfl⟩ : syracuseStep 3808505 = 2856379) B2856379
theorem B2539003 : Blo 2255435 2539003 := bstep (se 1 (by rfl) ⟨1904252, by rfl⟩ : syracuseStep 2539003 = 3808505) B3808505
theorem B3385337 : Blo 2255435 3385337 := bstep (se 2 (by rfl) ⟨1269501, by rfl⟩ : syracuseStep 3385337 = 2539003) B2539003
theorem B2256891 : Blo 2255435 2256891 := bstep (se 1 (by rfl) ⟨1692668, by rfl⟩ : syracuseStep 2256891 = 3385337) B3385337
theorem B2934857 : Blo 2255435 2934857 := bbase (se 2 (by rfl) ⟨1100571, by rfl⟩ : syracuseStep 2934857 = 2201143) (by norm_num)
theorem B7826285 : Blo 2255435 7826285 := bstep (se 3 (by rfl) ⟨1467428, by rfl⟩ : syracuseStep 7826285 = 2934857) B2934857
theorem B20870093 : Blo 2255435 20870093 := bstep (se 3 (by rfl) ⟨3913142, by rfl⟩ : syracuseStep 20870093 = 7826285) B7826285
theorem B55653581 : Blo 2255435 55653581 := bstep (se 3 (by rfl) ⟨10435046, by rfl⟩ : syracuseStep 55653581 = 20870093) B20870093
theorem B37102387 : Blo 2255435 37102387 := bstep (se 1 (by rfl) ⟨27826790, by rfl⟩ : syracuseStep 37102387 = 55653581) B55653581
theorem B49469849 : Blo 2255435 49469849 := bstep (se 2 (by rfl) ⟨18551193, by rfl⟩ : syracuseStep 49469849 = 37102387) B37102387
theorem B32979899 : Blo 2255435 32979899 := bstep (se 1 (by rfl) ⟨24734924, by rfl⟩ : syracuseStep 32979899 = 49469849) B49469849
theorem B21986599 : Blo 2255435 21986599 := bstep (se 1 (by rfl) ⟨16489949, by rfl⟩ : syracuseStep 21986599 = 32979899) B32979899
theorem B29315465 : Blo 2255435 29315465 := bstep (se 2 (by rfl) ⟨10993299, by rfl⟩ : syracuseStep 29315465 = 21986599) B21986599
theorem B19543643 : Blo 2255435 19543643 := bstep (se 1 (by rfl) ⟨14657732, by rfl⟩ : syracuseStep 19543643 = 29315465) B29315465
theorem B13029095 : Blo 2255435 13029095 := bstep (se 1 (by rfl) ⟨9771821, by rfl⟩ : syracuseStep 13029095 = 19543643) B19543643
theorem B34744253 : Blo 2255435 34744253 := bstep (se 3 (by rfl) ⟨6514547, by rfl⟩ : syracuseStep 34744253 = 13029095) B13029095
theorem B370605365 : Blo 2255435 370605365 := bstep (se 5 (by rfl) ⟨17372126, by rfl⟩ : syracuseStep 370605365 = 34744253) B34744253
theorem B247070243 : Blo 2255435 247070243 := bstep (se 1 (by rfl) ⟨185302682, by rfl⟩ : syracuseStep 247070243 = 370605365) B370605365
theorem B164713495 : Blo 2255435 164713495 := bstep (se 1 (by rfl) ⟨123535121, by rfl⟩ : syracuseStep 164713495 = 247070243) B247070243
theorem B219617993 : Blo 2255435 219617993 := bstep (se 2 (by rfl) ⟨82356747, by rfl⟩ : syracuseStep 219617993 = 164713495) B164713495
theorem B146411995 : Blo 2255435 146411995 := bstep (se 1 (by rfl) ⟨109808996, by rfl⟩ : syracuseStep 146411995 = 219617993) B219617993
theorem B195215993 : Blo 2255435 195215993 := bstep (se 2 (by rfl) ⟨73205997, by rfl⟩ : syracuseStep 195215993 = 146411995) B146411995
theorem B130143995 : Blo 2255435 130143995 := bstep (se 1 (by rfl) ⟨97607996, by rfl⟩ : syracuseStep 130143995 = 195215993) B195215993
theorem B86762663 : Blo 2255435 86762663 := bstep (se 1 (by rfl) ⟨65071997, by rfl⟩ : syracuseStep 86762663 = 130143995) B130143995
theorem B57841775 : Blo 2255435 57841775 := bstep (se 1 (by rfl) ⟨43381331, by rfl⟩ : syracuseStep 57841775 = 86762663) B86762663
theorem B38561183 : Blo 2255435 38561183 := bstep (se 1 (by rfl) ⟨28920887, by rfl⟩ : syracuseStep 38561183 = 57841775) B57841775
theorem B25707455 : Blo 2255435 25707455 := bstep (se 1 (by rfl) ⟨19280591, by rfl⟩ : syracuseStep 25707455 = 38561183) B38561183
theorem B17138303 : Blo 2255435 17138303 := bstep (se 1 (by rfl) ⟨12853727, by rfl⟩ : syracuseStep 17138303 = 25707455) B25707455
theorem B11425535 : Blo 2255435 11425535 := bstep (se 1 (by rfl) ⟨8569151, by rfl⟩ : syracuseStep 11425535 = 17138303) B17138303
theorem B7617023 : Blo 2255435 7617023 := bstep (se 1 (by rfl) ⟨5712767, by rfl⟩ : syracuseStep 7617023 = 11425535) B11425535
theorem B5078015 : Blo 2255435 5078015 := bstep (se 1 (by rfl) ⟨3808511, by rfl⟩ : syracuseStep 5078015 = 7617023) B7617023
theorem B3385343 : Blo 2255435 3385343 := bstep (se 1 (by rfl) ⟨2539007, by rfl⟩ : syracuseStep 3385343 = 5078015) B5078015
theorem B2256895 : Blo 2255435 2256895 := bstep (se 1 (by rfl) ⟨1692671, by rfl⟩ : syracuseStep 2256895 = 3385343) B3385343
theorem B3385349 : Blo 2255435 3385349 := bbase (se 4 (by rfl) ⟨317376, by rfl⟩ : syracuseStep 3385349 = 634753) (by norm_num)
theorem B2256899 : Blo 2255435 2256899 := bstep (se 1 (by rfl) ⟨1692674, by rfl⟩ : syracuseStep 2256899 = 3385349) B3385349
theorem B3808525 : Blo 2255435 3808525 := bbase (se 3 (by rfl) ⟨714098, by rfl⟩ : syracuseStep 3808525 = 1428197) (by norm_num)
theorem B5078033 : Blo 2255435 5078033 := bstep (se 2 (by rfl) ⟨1904262, by rfl⟩ : syracuseStep 5078033 = 3808525) B3808525
theorem B3385355 : Blo 2255435 3385355 := bstep (se 1 (by rfl) ⟨2539016, by rfl⟩ : syracuseStep 3385355 = 5078033) B5078033
theorem B2256903 : Blo 2255435 2256903 := bstep (se 1 (by rfl) ⟨1692677, by rfl⟩ : syracuseStep 2256903 = 3385355) B3385355
theorem B2539021 : Blo 2255435 2539021 := bbase (se 3 (by rfl) ⟨476066, by rfl⟩ : syracuseStep 2539021 = 952133) (by norm_num)
theorem B3385361 : Blo 2255435 3385361 := bstep (se 2 (by rfl) ⟨1269510, by rfl⟩ : syracuseStep 3385361 = 2539021) B2539021
theorem B2256907 : Blo 2255435 2256907 := bstep (se 1 (by rfl) ⟨1692680, by rfl⟩ : syracuseStep 2256907 = 3385361) B3385361
theorem B7617077 : Blo 2255435 7617077 := bbase (se 5 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 7617077 = 714101) (by norm_num)
theorem B5078051 : Blo 2255435 5078051 := bstep (se 1 (by rfl) ⟨3808538, by rfl⟩ : syracuseStep 5078051 = 7617077) B7617077
theorem B3385367 : Blo 2255435 3385367 := bstep (se 1 (by rfl) ⟨2539025, by rfl⟩ : syracuseStep 3385367 = 5078051) B5078051
theorem B2256911 : Blo 2255435 2256911 := bstep (se 1 (by rfl) ⟨1692683, by rfl⟩ : syracuseStep 2256911 = 3385367) B3385367
theorem B3385373 : Blo 2255435 3385373 := bbase (se 3 (by rfl) ⟨634757, by rfl⟩ : syracuseStep 3385373 = 1269515) (by norm_num)
theorem B2256915 : Blo 2255435 2256915 := bstep (se 1 (by rfl) ⟨1692686, by rfl⟩ : syracuseStep 2256915 = 3385373) B3385373
theorem B5078069 : Blo 2255435 5078069 := bbase (se 5 (by rfl) ⟨238034, by rfl⟩ : syracuseStep 5078069 = 476069) (by norm_num)
theorem B3385379 : Blo 2255435 3385379 := bstep (se 1 (by rfl) ⟨2539034, by rfl⟩ : syracuseStep 3385379 = 5078069) B5078069
theorem B2256919 : Blo 2255435 2256919 := bstep (se 1 (by rfl) ⟨1692689, by rfl⟩ : syracuseStep 2256919 = 3385379) B3385379
theorem B7721045 : Blo 2255435 7721045 := bbase (se 8 (by rfl) ⟨45240, by rfl⟩ : syracuseStep 7721045 = 90481) (by norm_num)
theorem B5147363 : Blo 2255435 5147363 := bstep (se 1 (by rfl) ⟨3860522, by rfl⟩ : syracuseStep 5147363 = 7721045) B7721045
theorem B3431575 : Blo 2255435 3431575 := bstep (se 1 (by rfl) ⟨2573681, by rfl⟩ : syracuseStep 3431575 = 5147363) B5147363
theorem B18301733 : Blo 2255435 18301733 := bstep (se 4 (by rfl) ⟨1715787, by rfl⟩ : syracuseStep 18301733 = 3431575) B3431575
theorem B12201155 : Blo 2255435 12201155 := bstep (se 1 (by rfl) ⟨9150866, by rfl⟩ : syracuseStep 12201155 = 18301733) B18301733
theorem B8134103 : Blo 2255435 8134103 := bstep (se 1 (by rfl) ⟨6100577, by rfl⟩ : syracuseStep 8134103 = 12201155) B12201155
theorem B5422735 : Blo 2255435 5422735 := bstep (se 1 (by rfl) ⟨4067051, by rfl⟩ : syracuseStep 5422735 = 8134103) B8134103
theorem B7230313 : Blo 2255435 7230313 := bstep (se 2 (by rfl) ⟨2711367, by rfl⟩ : syracuseStep 7230313 = 5422735) B5422735
theorem B9640417 : Blo 2255435 9640417 := bstep (se 2 (by rfl) ⟨3615156, by rfl⟩ : syracuseStep 9640417 = 7230313) B7230313
theorem B12853889 : Blo 2255435 12853889 := bstep (se 2 (by rfl) ⟨4820208, by rfl⟩ : syracuseStep 12853889 = 9640417) B9640417
theorem B8569259 : Blo 2255435 8569259 := bstep (se 1 (by rfl) ⟨6426944, by rfl⟩ : syracuseStep 8569259 = 12853889) B12853889
theorem B5712839 : Blo 2255435 5712839 := bstep (se 1 (by rfl) ⟨4284629, by rfl⟩ : syracuseStep 5712839 = 8569259) B8569259
theorem B3808559 : Blo 2255435 3808559 := bstep (se 1 (by rfl) ⟨2856419, by rfl⟩ : syracuseStep 3808559 = 5712839) B5712839
theorem B2539039 : Blo 2255435 2539039 := bstep (se 1 (by rfl) ⟨1904279, by rfl⟩ : syracuseStep 2539039 = 3808559) B3808559
theorem B3385385 : Blo 2255435 3385385 := bstep (se 2 (by rfl) ⟨1269519, by rfl⟩ : syracuseStep 3385385 = 2539039) B2539039
theorem B2256923 : Blo 2255435 2256923 := bstep (se 1 (by rfl) ⟨1692692, by rfl⟩ : syracuseStep 2256923 = 3385385) B3385385
theorem B7230325 : Blo 2255435 7230325 := bbase (se 5 (by rfl) ⟨338921, by rfl⟩ : syracuseStep 7230325 = 677843) (by norm_num)
theorem B9640433 : Blo 2255435 9640433 := bstep (se 2 (by rfl) ⟨3615162, by rfl⟩ : syracuseStep 9640433 = 7230325) B7230325
theorem B6426955 : Blo 2255435 6426955 := bstep (se 1 (by rfl) ⟨4820216, by rfl⟩ : syracuseStep 6426955 = 9640433) B9640433
theorem B8569273 : Blo 2255435 8569273 := bstep (se 2 (by rfl) ⟨3213477, by rfl⟩ : syracuseStep 8569273 = 6426955) B6426955
theorem B11425697 : Blo 2255435 11425697 := bstep (se 2 (by rfl) ⟨4284636, by rfl⟩ : syracuseStep 11425697 = 8569273) B8569273
theorem B7617131 : Blo 2255435 7617131 := bstep (se 1 (by rfl) ⟨5712848, by rfl⟩ : syracuseStep 7617131 = 11425697) B11425697
theorem B5078087 : Blo 2255435 5078087 := bstep (se 1 (by rfl) ⟨3808565, by rfl⟩ : syracuseStep 5078087 = 7617131) B7617131
theorem B3385391 : Blo 2255435 3385391 := bstep (se 1 (by rfl) ⟨2539043, by rfl⟩ : syracuseStep 3385391 = 5078087) B5078087
theorem B2256927 : Blo 2255435 2256927 := bstep (se 1 (by rfl) ⟨1692695, by rfl⟩ : syracuseStep 2256927 = 3385391) B3385391
theorem B3385397 : Blo 2255435 3385397 := bbase (se 5 (by rfl) ⟨158690, by rfl⟩ : syracuseStep 3385397 = 317381) (by norm_num)
theorem B2256931 : Blo 2255435 2256931 := bstep (se 1 (by rfl) ⟨1692698, by rfl⟩ : syracuseStep 2256931 = 3385397) B3385397
theorem B5712869 : Blo 2255435 5712869 := bbase (se 4 (by rfl) ⟨535581, by rfl⟩ : syracuseStep 5712869 = 1071163) (by norm_num)
theorem B3808579 : Blo 2255435 3808579 := bstep (se 1 (by rfl) ⟨2856434, by rfl⟩ : syracuseStep 3808579 = 5712869) B5712869
theorem B5078105 : Blo 2255435 5078105 := bstep (se 2 (by rfl) ⟨1904289, by rfl⟩ : syracuseStep 5078105 = 3808579) B3808579
theorem B3385403 : Blo 2255435 3385403 := bstep (se 1 (by rfl) ⟨2539052, by rfl⟩ : syracuseStep 3385403 = 5078105) B5078105
theorem B2256935 : Blo 2255435 2256935 := bstep (se 1 (by rfl) ⟨1692701, by rfl⟩ : syracuseStep 2256935 = 3385403) B3385403
theorem B2539057 : Blo 2255435 2539057 := bbase (se 2 (by rfl) ⟨952146, by rfl⟩ : syracuseStep 2539057 = 1904293) (by norm_num)
theorem B3385409 : Blo 2255435 3385409 := bstep (se 2 (by rfl) ⟨1269528, by rfl⟩ : syracuseStep 3385409 = 2539057) B2539057
theorem B2256939 : Blo 2255435 2256939 := bstep (se 1 (by rfl) ⟨1692704, by rfl⟩ : syracuseStep 2256939 = 3385409) B3385409
theorem B3091933 : Blo 2255435 3091933 := bbase (se 3 (by rfl) ⟨579737, by rfl⟩ : syracuseStep 3091933 = 1159475) (by norm_num)
theorem B4122577 : Blo 2255435 4122577 := bstep (se 2 (by rfl) ⟨1545966, by rfl⟩ : syracuseStep 4122577 = 3091933) B3091933
theorem B5496769 : Blo 2255435 5496769 := bstep (se 2 (by rfl) ⟨2061288, by rfl⟩ : syracuseStep 5496769 = 4122577) B4122577
theorem B7329025 : Blo 2255435 7329025 := bstep (se 2 (by rfl) ⟨2748384, by rfl⟩ : syracuseStep 7329025 = 5496769) B5496769
theorem B39088133 : Blo 2255435 39088133 := bstep (se 4 (by rfl) ⟨3664512, by rfl⟩ : syracuseStep 39088133 = 7329025) B7329025
theorem B26058755 : Blo 2255435 26058755 := bstep (se 1 (by rfl) ⟨19544066, by rfl⟩ : syracuseStep 26058755 = 39088133) B39088133
theorem B17372503 : Blo 2255435 17372503 := bstep (se 1 (by rfl) ⟨13029377, by rfl⟩ : syracuseStep 17372503 = 26058755) B26058755
theorem B23163337 : Blo 2255435 23163337 := bstep (se 2 (by rfl) ⟨8686251, by rfl⟩ : syracuseStep 23163337 = 17372503) B17372503
theorem B30884449 : Blo 2255435 30884449 := bstep (se 2 (by rfl) ⟨11581668, by rfl⟩ : syracuseStep 30884449 = 23163337) B23163337
theorem B41179265 : Blo 2255435 41179265 := bstep (se 2 (by rfl) ⟨15442224, by rfl⟩ : syracuseStep 41179265 = 30884449) B30884449
theorem B27452843 : Blo 2255435 27452843 := bstep (se 1 (by rfl) ⟨20589632, by rfl⟩ : syracuseStep 27452843 = 41179265) B41179265
theorem B18301895 : Blo 2255435 18301895 := bstep (se 1 (by rfl) ⟨13726421, by rfl⟩ : syracuseStep 18301895 = 27452843) B27452843
theorem B12201263 : Blo 2255435 12201263 := bstep (se 1 (by rfl) ⟨9150947, by rfl⟩ : syracuseStep 12201263 = 18301895) B18301895
theorem B8134175 : Blo 2255435 8134175 := bstep (se 1 (by rfl) ⟨6100631, by rfl⟩ : syracuseStep 8134175 = 12201263) B12201263
theorem B5422783 : Blo 2255435 5422783 := bstep (se 1 (by rfl) ⟨4067087, by rfl⟩ : syracuseStep 5422783 = 8134175) B8134175
theorem B7230377 : Blo 2255435 7230377 := bstep (se 2 (by rfl) ⟨2711391, by rfl⟩ : syracuseStep 7230377 = 5422783) B5422783
theorem B4820251 : Blo 2255435 4820251 := bstep (se 1 (by rfl) ⟨3615188, by rfl⟩ : syracuseStep 4820251 = 7230377) B7230377
theorem B6427001 : Blo 2255435 6427001 := bstep (se 2 (by rfl) ⟨2410125, by rfl⟩ : syracuseStep 6427001 = 4820251) B4820251
theorem B4284667 : Blo 2255435 4284667 := bstep (se 1 (by rfl) ⟨3213500, by rfl⟩ : syracuseStep 4284667 = 6427001) B6427001
theorem B5712889 : Blo 2255435 5712889 := bstep (se 2 (by rfl) ⟨2142333, by rfl⟩ : syracuseStep 5712889 = 4284667) B4284667
theorem B7617185 : Blo 2255435 7617185 := bstep (se 2 (by rfl) ⟨2856444, by rfl⟩ : syracuseStep 7617185 = 5712889) B5712889
theorem B5078123 : Blo 2255435 5078123 := bstep (se 1 (by rfl) ⟨3808592, by rfl⟩ : syracuseStep 5078123 = 7617185) B7617185
theorem B3385415 : Blo 2255435 3385415 := bstep (se 1 (by rfl) ⟨2539061, by rfl⟩ : syracuseStep 3385415 = 5078123) B5078123
theorem B2256943 : Blo 2255435 2256943 := bstep (se 1 (by rfl) ⟨1692707, by rfl⟩ : syracuseStep 2256943 = 3385415) B3385415
theorem B3385421 : Blo 2255435 3385421 := bbase (se 3 (by rfl) ⟨634766, by rfl⟩ : syracuseStep 3385421 = 1269533) (by norm_num)
theorem B2256947 : Blo 2255435 2256947 := bstep (se 1 (by rfl) ⟨1692710, by rfl⟩ : syracuseStep 2256947 = 3385421) B3385421
theorem B5078141 : Blo 2255435 5078141 := bbase (se 3 (by rfl) ⟨952151, by rfl⟩ : syracuseStep 5078141 = 1904303) (by norm_num)
theorem B3385427 : Blo 2255435 3385427 := bstep (se 1 (by rfl) ⟨2539070, by rfl⟩ : syracuseStep 3385427 = 5078141) B5078141
theorem B2256951 : Blo 2255435 2256951 := bstep (se 1 (by rfl) ⟨1692713, by rfl⟩ : syracuseStep 2256951 = 3385427) B3385427
theorem B3808613 : Blo 2255435 3808613 := bbase (se 4 (by rfl) ⟨357057, by rfl⟩ : syracuseStep 3808613 = 714115) (by norm_num)
theorem B2539075 : Blo 2255435 2539075 := bstep (se 1 (by rfl) ⟨1904306, by rfl⟩ : syracuseStep 2539075 = 3808613) B3808613
theorem B3385433 : Blo 2255435 3385433 := bstep (se 2 (by rfl) ⟨1269537, by rfl⟩ : syracuseStep 3385433 = 2539075) B2539075
theorem B2256955 : Blo 2255435 2256955 := bstep (se 1 (by rfl) ⟨1692716, by rfl⟩ : syracuseStep 2256955 = 3385433) B3385433
theorem B4820285 : Blo 2255435 4820285 := bbase (se 3 (by rfl) ⟨903803, by rfl⟩ : syracuseStep 4820285 = 1807607) (by norm_num)
theorem B3213523 : Blo 2255435 3213523 := bstep (se 1 (by rfl) ⟨2410142, by rfl⟩ : syracuseStep 3213523 = 4820285) B4820285
theorem B17138789 : Blo 2255435 17138789 := bstep (se 4 (by rfl) ⟨1606761, by rfl⟩ : syracuseStep 17138789 = 3213523) B3213523
theorem B11425859 : Blo 2255435 11425859 := bstep (se 1 (by rfl) ⟨8569394, by rfl⟩ : syracuseStep 11425859 = 17138789) B17138789
theorem B7617239 : Blo 2255435 7617239 := bstep (se 1 (by rfl) ⟨5712929, by rfl⟩ : syracuseStep 7617239 = 11425859) B11425859
theorem B5078159 : Blo 2255435 5078159 := bstep (se 1 (by rfl) ⟨3808619, by rfl⟩ : syracuseStep 5078159 = 7617239) B7617239
theorem B3385439 : Blo 2255435 3385439 := bstep (se 1 (by rfl) ⟨2539079, by rfl⟩ : syracuseStep 3385439 = 5078159) B5078159
theorem B2256959 : Blo 2255435 2256959 := bstep (se 1 (by rfl) ⟨1692719, by rfl⟩ : syracuseStep 2256959 = 3385439) B3385439
theorem B3385445 : Blo 2255435 3385445 := bbase (se 4 (by rfl) ⟨317385, by rfl⟩ : syracuseStep 3385445 = 634771) (by norm_num)
theorem B2256963 : Blo 2255435 2256963 := bstep (se 1 (by rfl) ⟨1692722, by rfl⟩ : syracuseStep 2256963 = 3385445) B3385445
theorem B6863285 : Blo 2255435 6863285 := bbase (se 5 (by rfl) ⟨321716, by rfl⟩ : syracuseStep 6863285 = 643433) (by norm_num)
theorem B4575523 : Blo 2255435 4575523 := bstep (se 1 (by rfl) ⟨3431642, by rfl⟩ : syracuseStep 4575523 = 6863285) B6863285
theorem B6100697 : Blo 2255435 6100697 := bstep (se 2 (by rfl) ⟨2287761, by rfl⟩ : syracuseStep 6100697 = 4575523) B4575523
theorem B16268525 : Blo 2255435 16268525 := bstep (se 3 (by rfl) ⟨3050348, by rfl⟩ : syracuseStep 16268525 = 6100697) B6100697
theorem B10845683 : Blo 2255435 10845683 := bstep (se 1 (by rfl) ⟨8134262, by rfl⟩ : syracuseStep 10845683 = 16268525) B16268525
theorem B7230455 : Blo 2255435 7230455 := bstep (se 1 (by rfl) ⟨5422841, by rfl⟩ : syracuseStep 7230455 = 10845683) B10845683
theorem B4820303 : Blo 2255435 4820303 := bstep (se 1 (by rfl) ⟨3615227, by rfl⟩ : syracuseStep 4820303 = 7230455) B7230455
theorem B3213535 : Blo 2255435 3213535 := bstep (se 1 (by rfl) ⟨2410151, by rfl⟩ : syracuseStep 3213535 = 4820303) B4820303
theorem B4284713 : Blo 2255435 4284713 := bstep (se 2 (by rfl) ⟨1606767, by rfl⟩ : syracuseStep 4284713 = 3213535) B3213535
theorem B2856475 : Blo 2255435 2856475 := bstep (se 1 (by rfl) ⟨2142356, by rfl⟩ : syracuseStep 2856475 = 4284713) B4284713
theorem B3808633 : Blo 2255435 3808633 := bstep (se 2 (by rfl) ⟨1428237, by rfl⟩ : syracuseStep 3808633 = 2856475) B2856475
theorem B5078177 : Blo 2255435 5078177 := bstep (se 2 (by rfl) ⟨1904316, by rfl⟩ : syracuseStep 5078177 = 3808633) B3808633
theorem B3385451 : Blo 2255435 3385451 := bstep (se 1 (by rfl) ⟨2539088, by rfl⟩ : syracuseStep 3385451 = 5078177) B5078177
theorem B2256967 : Blo 2255435 2256967 := bstep (se 1 (by rfl) ⟨1692725, by rfl⟩ : syracuseStep 2256967 = 3385451) B3385451
theorem B2539093 : Blo 2255435 2539093 := bbase (se 8 (by rfl) ⟨14877, by rfl⟩ : syracuseStep 2539093 = 29755) (by norm_num)
theorem B3385457 : Blo 2255435 3385457 := bstep (se 2 (by rfl) ⟨1269546, by rfl⟩ : syracuseStep 3385457 = 2539093) B2539093
theorem B2256971 : Blo 2255435 2256971 := bstep (se 1 (by rfl) ⟨1692728, by rfl⟩ : syracuseStep 2256971 = 3385457) B3385457
theorem B2856485 : Blo 2255435 2856485 := bbase (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) (by norm_num)
theorem B7617293 : Blo 2255435 7617293 := bstep (se 3 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 7617293 = 2856485) B2856485
theorem B5078195 : Blo 2255435 5078195 := bstep (se 1 (by rfl) ⟨3808646, by rfl⟩ : syracuseStep 5078195 = 7617293) B7617293
theorem B3385463 : Blo 2255435 3385463 := bstep (se 1 (by rfl) ⟨2539097, by rfl⟩ : syracuseStep 3385463 = 5078195) B5078195
theorem B2256975 : Blo 2255435 2256975 := bstep (se 1 (by rfl) ⟨1692731, by rfl⟩ : syracuseStep 2256975 = 3385463) B3385463
theorem B3385469 : Blo 2255435 3385469 := bbase (se 3 (by rfl) ⟨634775, by rfl⟩ : syracuseStep 3385469 = 1269551) (by norm_num)
theorem B2256979 : Blo 2255435 2256979 := bstep (se 1 (by rfl) ⟨1692734, by rfl⟩ : syracuseStep 2256979 = 3385469) B3385469
theorem B5078213 : Blo 2255435 5078213 := bbase (se 4 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 5078213 = 952165) (by norm_num)
theorem B3385475 : Blo 2255435 3385475 := bstep (se 1 (by rfl) ⟨2539106, by rfl⟩ : syracuseStep 3385475 = 5078213) B5078213
theorem B2256983 : Blo 2255435 2256983 := bstep (se 1 (by rfl) ⟨1692737, by rfl⟩ : syracuseStep 2256983 = 3385475) B3385475
theorem B20590037 : Blo 2255435 20590037 := bbase (se 7 (by rfl) ⟨241289, by rfl⟩ : syracuseStep 20590037 = 482579) (by norm_num)
theorem B13726691 : Blo 2255435 13726691 := bstep (se 1 (by rfl) ⟨10295018, by rfl⟩ : syracuseStep 13726691 = 20590037) B20590037
theorem B9151127 : Blo 2255435 9151127 := bstep (se 1 (by rfl) ⟨6863345, by rfl⟩ : syracuseStep 9151127 = 13726691) B13726691
theorem B6100751 : Blo 2255435 6100751 := bstep (se 1 (by rfl) ⟨4575563, by rfl⟩ : syracuseStep 6100751 = 9151127) B9151127
theorem B4067167 : Blo 2255435 4067167 := bstep (se 1 (by rfl) ⟨3050375, by rfl⟩ : syracuseStep 4067167 = 6100751) B6100751
theorem B5422889 : Blo 2255435 5422889 := bstep (se 2 (by rfl) ⟨2033583, by rfl⟩ : syracuseStep 5422889 = 4067167) B4067167
theorem B14461037 : Blo 2255435 14461037 := bstep (se 3 (by rfl) ⟨2711444, by rfl⟩ : syracuseStep 14461037 = 5422889) B5422889
theorem B9640691 : Blo 2255435 9640691 := bstep (se 1 (by rfl) ⟨7230518, by rfl⟩ : syracuseStep 9640691 = 14461037) B14461037
theorem B6427127 : Blo 2255435 6427127 := bstep (se 1 (by rfl) ⟨4820345, by rfl⟩ : syracuseStep 6427127 = 9640691) B9640691
theorem B4284751 : Blo 2255435 4284751 := bstep (se 1 (by rfl) ⟨3213563, by rfl⟩ : syracuseStep 4284751 = 6427127) B6427127
theorem B5713001 : Blo 2255435 5713001 := bstep (se 2 (by rfl) ⟨2142375, by rfl⟩ : syracuseStep 5713001 = 4284751) B4284751
theorem B3808667 : Blo 2255435 3808667 := bstep (se 1 (by rfl) ⟨2856500, by rfl⟩ : syracuseStep 3808667 = 5713001) B5713001
theorem B2539111 : Blo 2255435 2539111 := bstep (se 1 (by rfl) ⟨1904333, by rfl⟩ : syracuseStep 2539111 = 3808667) B3808667
theorem B3385481 : Blo 2255435 3385481 := bstep (se 2 (by rfl) ⟨1269555, by rfl⟩ : syracuseStep 3385481 = 2539111) B2539111
theorem B2256987 : Blo 2255435 2256987 := bstep (se 1 (by rfl) ⟨1692740, by rfl⟩ : syracuseStep 2256987 = 3385481) B3385481
theorem B11426021 : Blo 2255435 11426021 := bbase (se 4 (by rfl) ⟨1071189, by rfl⟩ : syracuseStep 11426021 = 2142379) (by norm_num)
theorem B7617347 : Blo 2255435 7617347 := bstep (se 1 (by rfl) ⟨5713010, by rfl⟩ : syracuseStep 7617347 = 11426021) B11426021
theorem B5078231 : Blo 2255435 5078231 := bstep (se 1 (by rfl) ⟨3808673, by rfl⟩ : syracuseStep 5078231 = 7617347) B7617347
theorem B3385487 : Blo 2255435 3385487 := bstep (se 1 (by rfl) ⟨2539115, by rfl⟩ : syracuseStep 3385487 = 5078231) B5078231
theorem B2256991 : Blo 2255435 2256991 := bstep (se 1 (by rfl) ⟨1692743, by rfl⟩ : syracuseStep 2256991 = 3385487) B3385487
theorem B3385493 : Blo 2255435 3385493 := bbase (se 6 (by rfl) ⟨79347, by rfl⟩ : syracuseStep 3385493 = 158695) (by norm_num)
theorem B2256995 : Blo 2255435 2256995 := bstep (se 1 (by rfl) ⟨1692746, by rfl⟩ : syracuseStep 2256995 = 3385493) B3385493
theorem B9640741 : Blo 2255435 9640741 := bbase (se 4 (by rfl) ⟨903819, by rfl⟩ : syracuseStep 9640741 = 1807639) (by norm_num)
theorem B12854321 : Blo 2255435 12854321 := bstep (se 2 (by rfl) ⟨4820370, by rfl⟩ : syracuseStep 12854321 = 9640741) B9640741
theorem B8569547 : Blo 2255435 8569547 := bstep (se 1 (by rfl) ⟨6427160, by rfl⟩ : syracuseStep 8569547 = 12854321) B12854321
theorem B5713031 : Blo 2255435 5713031 := bstep (se 1 (by rfl) ⟨4284773, by rfl⟩ : syracuseStep 5713031 = 8569547) B8569547
theorem B3808687 : Blo 2255435 3808687 := bstep (se 1 (by rfl) ⟨2856515, by rfl⟩ : syracuseStep 3808687 = 5713031) B5713031
theorem B5078249 : Blo 2255435 5078249 := bstep (se 2 (by rfl) ⟨1904343, by rfl⟩ : syracuseStep 5078249 = 3808687) B3808687
theorem B3385499 : Blo 2255435 3385499 := bstep (se 1 (by rfl) ⟨2539124, by rfl⟩ : syracuseStep 3385499 = 5078249) B5078249
theorem B2256999 : Blo 2255435 2256999 := bstep (se 1 (by rfl) ⟨1692749, by rfl⟩ : syracuseStep 2256999 = 3385499) B3385499
theorem B2539129 : Blo 2255435 2539129 := bbase (se 2 (by rfl) ⟨952173, by rfl⟩ : syracuseStep 2539129 = 1904347) (by norm_num)
theorem B3385505 : Blo 2255435 3385505 := bstep (se 2 (by rfl) ⟨1269564, by rfl⟩ : syracuseStep 3385505 = 2539129) B2539129
theorem B2257003 : Blo 2255435 2257003 := bstep (se 1 (by rfl) ⟨1692752, by rfl⟩ : syracuseStep 2257003 = 3385505) B3385505
theorem B3257437 : Blo 2255435 3257437 := bbase (se 3 (by rfl) ⟨610769, by rfl⟩ : syracuseStep 3257437 = 1221539) (by norm_num)
theorem B4343249 : Blo 2255435 4343249 := bstep (se 2 (by rfl) ⟨1628718, by rfl⟩ : syracuseStep 4343249 = 3257437) B3257437
theorem B2895499 : Blo 2255435 2895499 := bstep (se 1 (by rfl) ⟨2171624, by rfl⟩ : syracuseStep 2895499 = 4343249) B4343249
theorem B3860665 : Blo 2255435 3860665 := bstep (se 2 (by rfl) ⟨1447749, by rfl⟩ : syracuseStep 3860665 = 2895499) B2895499
theorem B20590213 : Blo 2255435 20590213 := bstep (se 4 (by rfl) ⟨1930332, by rfl⟩ : syracuseStep 20590213 = 3860665) B3860665
theorem B27453617 : Blo 2255435 27453617 := bstep (se 2 (by rfl) ⟨10295106, by rfl⟩ : syracuseStep 27453617 = 20590213) B20590213
theorem B18302411 : Blo 2255435 18302411 := bstep (se 1 (by rfl) ⟨13726808, by rfl⟩ : syracuseStep 18302411 = 27453617) B27453617
theorem B12201607 : Blo 2255435 12201607 := bstep (se 1 (by rfl) ⟨9151205, by rfl⟩ : syracuseStep 12201607 = 18302411) B18302411
theorem B16268809 : Blo 2255435 16268809 := bstep (se 2 (by rfl) ⟨6100803, by rfl⟩ : syracuseStep 16268809 = 12201607) B12201607
theorem B21691745 : Blo 2255435 21691745 := bstep (se 2 (by rfl) ⟨8134404, by rfl⟩ : syracuseStep 21691745 = 16268809) B16268809
theorem B14461163 : Blo 2255435 14461163 := bstep (se 1 (by rfl) ⟨10845872, by rfl⟩ : syracuseStep 14461163 = 21691745) B21691745
theorem B9640775 : Blo 2255435 9640775 := bstep (se 1 (by rfl) ⟨7230581, by rfl⟩ : syracuseStep 9640775 = 14461163) B14461163
theorem B6427183 : Blo 2255435 6427183 := bstep (se 1 (by rfl) ⟨4820387, by rfl⟩ : syracuseStep 6427183 = 9640775) B9640775
theorem B8569577 : Blo 2255435 8569577 := bstep (se 2 (by rfl) ⟨3213591, by rfl⟩ : syracuseStep 8569577 = 6427183) B6427183
theorem B5713051 : Blo 2255435 5713051 := bstep (se 1 (by rfl) ⟨4284788, by rfl⟩ : syracuseStep 5713051 = 8569577) B8569577
theorem B7617401 : Blo 2255435 7617401 := bstep (se 2 (by rfl) ⟨2856525, by rfl⟩ : syracuseStep 7617401 = 5713051) B5713051
theorem B5078267 : Blo 2255435 5078267 := bstep (se 1 (by rfl) ⟨3808700, by rfl⟩ : syracuseStep 5078267 = 7617401) B7617401
theorem B3385511 : Blo 2255435 3385511 := bstep (se 1 (by rfl) ⟨2539133, by rfl⟩ : syracuseStep 3385511 = 5078267) B5078267
theorem B2257007 : Blo 2255435 2257007 := bstep (se 1 (by rfl) ⟨1692755, by rfl⟩ : syracuseStep 2257007 = 3385511) B3385511
theorem B3385517 : Blo 2255435 3385517 := bbase (se 3 (by rfl) ⟨634784, by rfl⟩ : syracuseStep 3385517 = 1269569) (by norm_num)
theorem B2257011 : Blo 2255435 2257011 := bstep (se 1 (by rfl) ⟨1692758, by rfl⟩ : syracuseStep 2257011 = 3385517) B3385517
theorem B5078285 : Blo 2255435 5078285 := bbase (se 3 (by rfl) ⟨952178, by rfl⟩ : syracuseStep 5078285 = 1904357) (by norm_num)
theorem B3385523 : Blo 2255435 3385523 := bstep (se 1 (by rfl) ⟨2539142, by rfl⟩ : syracuseStep 3385523 = 5078285) B5078285
theorem B2257015 : Blo 2255435 2257015 := bstep (se 1 (by rfl) ⟨1692761, by rfl⟩ : syracuseStep 2257015 = 3385523) B3385523
theorem B2856541 : Blo 2255435 2856541 := bbase (se 3 (by rfl) ⟨535601, by rfl⟩ : syracuseStep 2856541 = 1071203) (by norm_num)
theorem B3808721 : Blo 2255435 3808721 := bstep (se 2 (by rfl) ⟨1428270, by rfl⟩ : syracuseStep 3808721 = 2856541) B2856541
theorem B2539147 : Blo 2255435 2539147 := bstep (se 1 (by rfl) ⟨1904360, by rfl⟩ : syracuseStep 2539147 = 3808721) B3808721
theorem B3385529 : Blo 2255435 3385529 := bstep (se 2 (by rfl) ⟨1269573, by rfl⟩ : syracuseStep 3385529 = 2539147) B2539147
theorem B2257019 : Blo 2255435 2257019 := bstep (se 1 (by rfl) ⟨1692764, by rfl⟩ : syracuseStep 2257019 = 3385529) B3385529
theorem B19281685 : Blo 2255435 19281685 := bbase (se 6 (by rfl) ⟨451914, by rfl⟩ : syracuseStep 19281685 = 903829) (by norm_num)
theorem B25708913 : Blo 2255435 25708913 := bstep (se 2 (by rfl) ⟨9640842, by rfl⟩ : syracuseStep 25708913 = 19281685) B19281685
theorem B17139275 : Blo 2255435 17139275 := bstep (se 1 (by rfl) ⟨12854456, by rfl⟩ : syracuseStep 17139275 = 25708913) B25708913
theorem B11426183 : Blo 2255435 11426183 := bstep (se 1 (by rfl) ⟨8569637, by rfl⟩ : syracuseStep 11426183 = 17139275) B17139275
theorem B7617455 : Blo 2255435 7617455 := bstep (se 1 (by rfl) ⟨5713091, by rfl⟩ : syracuseStep 7617455 = 11426183) B11426183
theorem B5078303 : Blo 2255435 5078303 := bstep (se 1 (by rfl) ⟨3808727, by rfl⟩ : syracuseStep 5078303 = 7617455) B7617455
theorem B3385535 : Blo 2255435 3385535 := bstep (se 1 (by rfl) ⟨2539151, by rfl⟩ : syracuseStep 3385535 = 5078303) B5078303
theorem B2257023 : Blo 2255435 2257023 := bstep (se 1 (by rfl) ⟨1692767, by rfl⟩ : syracuseStep 2257023 = 3385535) B3385535
theorem B3385541 : Blo 2255435 3385541 := bbase (se 4 (by rfl) ⟨317394, by rfl⟩ : syracuseStep 3385541 = 634789) (by norm_num)
theorem B2257027 : Blo 2255435 2257027 := bstep (se 1 (by rfl) ⟨1692770, by rfl⟩ : syracuseStep 2257027 = 3385541) B3385541
theorem B3808741 : Blo 2255435 3808741 := bbase (se 4 (by rfl) ⟨357069, by rfl⟩ : syracuseStep 3808741 = 714139) (by norm_num)
theorem B5078321 : Blo 2255435 5078321 := bstep (se 2 (by rfl) ⟨1904370, by rfl⟩ : syracuseStep 5078321 = 3808741) B3808741
theorem B3385547 : Blo 2255435 3385547 := bstep (se 1 (by rfl) ⟨2539160, by rfl⟩ : syracuseStep 3385547 = 5078321) B5078321
theorem B2257031 : Blo 2255435 2257031 := bstep (se 1 (by rfl) ⟨1692773, by rfl⟩ : syracuseStep 2257031 = 3385547) B3385547
theorem B2539165 : Blo 2255435 2539165 := bbase (se 3 (by rfl) ⟨476093, by rfl⟩ : syracuseStep 2539165 = 952187) (by norm_num)
theorem B3385553 : Blo 2255435 3385553 := bstep (se 2 (by rfl) ⟨1269582, by rfl⟩ : syracuseStep 3385553 = 2539165) B2539165
theorem B2257035 : Blo 2255435 2257035 := bstep (se 1 (by rfl) ⟨1692776, by rfl⟩ : syracuseStep 2257035 = 3385553) B3385553
theorem B7617509 : Blo 2255435 7617509 := bbase (se 4 (by rfl) ⟨714141, by rfl⟩ : syracuseStep 7617509 = 1428283) (by norm_num)
theorem B5078339 : Blo 2255435 5078339 := bstep (se 1 (by rfl) ⟨3808754, by rfl⟩ : syracuseStep 5078339 = 7617509) B7617509
theorem B3385559 : Blo 2255435 3385559 := bstep (se 1 (by rfl) ⟨2539169, by rfl⟩ : syracuseStep 3385559 = 5078339) B5078339
theorem B2257039 : Blo 2255435 2257039 := bstep (se 1 (by rfl) ⟨1692779, by rfl⟩ : syracuseStep 2257039 = 3385559) B3385559
theorem B3385565 : Blo 2255435 3385565 := bbase (se 3 (by rfl) ⟨634793, by rfl⟩ : syracuseStep 3385565 = 1269587) (by norm_num)
theorem B2257043 : Blo 2255435 2257043 := bstep (se 1 (by rfl) ⟨1692782, by rfl⟩ : syracuseStep 2257043 = 3385565) B3385565
theorem B5078357 : Blo 2255435 5078357 := bbase (se 11 (by rfl) ⟨3719, by rfl⟩ : syracuseStep 5078357 = 7439) (by norm_num)
theorem B3385571 : Blo 2255435 3385571 := bstep (se 1 (by rfl) ⟨2539178, by rfl⟩ : syracuseStep 3385571 = 5078357) B5078357
theorem B2257047 : Blo 2255435 2257047 := bstep (se 1 (by rfl) ⟨1692785, by rfl⟩ : syracuseStep 2257047 = 3385571) B3385571
theorem B2410241 : Blo 2255435 2410241 := bbase (se 2 (by rfl) ⟨903840, by rfl⟩ : syracuseStep 2410241 = 1807681) (by norm_num)
theorem B6427309 : Blo 2255435 6427309 := bstep (se 3 (by rfl) ⟨1205120, by rfl⟩ : syracuseStep 6427309 = 2410241) B2410241
theorem B8569745 : Blo 2255435 8569745 := bstep (se 2 (by rfl) ⟨3213654, by rfl⟩ : syracuseStep 8569745 = 6427309) B6427309
theorem B5713163 : Blo 2255435 5713163 := bstep (se 1 (by rfl) ⟨4284872, by rfl⟩ : syracuseStep 5713163 = 8569745) B8569745
theorem B3808775 : Blo 2255435 3808775 := bstep (se 1 (by rfl) ⟨2856581, by rfl⟩ : syracuseStep 3808775 = 5713163) B5713163
theorem B2539183 : Blo 2255435 2539183 := bstep (se 1 (by rfl) ⟨1904387, by rfl⟩ : syracuseStep 2539183 = 3808775) B3808775
theorem B3385577 : Blo 2255435 3385577 := bstep (se 2 (by rfl) ⟨1269591, by rfl⟩ : syracuseStep 3385577 = 2539183) B2539183
theorem B2257051 : Blo 2255435 2257051 := bstep (se 1 (by rfl) ⟨1692788, by rfl⟩ : syracuseStep 2257051 = 3385577) B3385577
theorem B2443129 : Blo 2255435 2443129 := bbase (se 2 (by rfl) ⟨916173, by rfl⟩ : syracuseStep 2443129 = 1832347) (by norm_num)
theorem B13030021 : Blo 2255435 13030021 := bstep (se 4 (by rfl) ⟨1221564, by rfl⟩ : syracuseStep 13030021 = 2443129) B2443129
theorem B17373361 : Blo 2255435 17373361 := bstep (se 2 (by rfl) ⟨6515010, by rfl⟩ : syracuseStep 17373361 = 13030021) B13030021
theorem B23164481 : Blo 2255435 23164481 := bstep (se 2 (by rfl) ⟨8686680, by rfl⟩ : syracuseStep 23164481 = 17373361) B17373361
theorem B15442987 : Blo 2255435 15442987 := bstep (se 1 (by rfl) ⟨11582240, by rfl⟩ : syracuseStep 15442987 = 23164481) B23164481
theorem B20590649 : Blo 2255435 20590649 := bstep (se 2 (by rfl) ⟨7721493, by rfl⟩ : syracuseStep 20590649 = 15442987) B15442987
theorem B13727099 : Blo 2255435 13727099 := bstep (se 1 (by rfl) ⟨10295324, by rfl⟩ : syracuseStep 13727099 = 20590649) B20590649
theorem B9151399 : Blo 2255435 9151399 := bstep (se 1 (by rfl) ⟨6863549, by rfl⟩ : syracuseStep 9151399 = 13727099) B13727099
theorem B48807461 : Blo 2255435 48807461 := bstep (se 4 (by rfl) ⟨4575699, by rfl⟩ : syracuseStep 48807461 = 9151399) B9151399
theorem B32538307 : Blo 2255435 32538307 := bstep (se 1 (by rfl) ⟨24403730, by rfl⟩ : syracuseStep 32538307 = 48807461) B48807461
theorem B43384409 : Blo 2255435 43384409 := bstep (se 2 (by rfl) ⟨16269153, by rfl⟩ : syracuseStep 43384409 = 32538307) B32538307
theorem B28922939 : Blo 2255435 28922939 := bstep (se 1 (by rfl) ⟨21692204, by rfl⟩ : syracuseStep 28922939 = 43384409) B43384409
theorem B19281959 : Blo 2255435 19281959 := bstep (se 1 (by rfl) ⟨14461469, by rfl⟩ : syracuseStep 19281959 = 28922939) B28922939
theorem B12854639 : Blo 2255435 12854639 := bstep (se 1 (by rfl) ⟨9640979, by rfl⟩ : syracuseStep 12854639 = 19281959) B19281959
theorem B8569759 : Blo 2255435 8569759 := bstep (se 1 (by rfl) ⟨6427319, by rfl⟩ : syracuseStep 8569759 = 12854639) B12854639
theorem B11426345 : Blo 2255435 11426345 := bstep (se 2 (by rfl) ⟨4284879, by rfl⟩ : syracuseStep 11426345 = 8569759) B8569759
theorem B7617563 : Blo 2255435 7617563 := bstep (se 1 (by rfl) ⟨5713172, by rfl⟩ : syracuseStep 7617563 = 11426345) B11426345
theorem B5078375 : Blo 2255435 5078375 := bstep (se 1 (by rfl) ⟨3808781, by rfl⟩ : syracuseStep 5078375 = 7617563) B7617563
theorem B3385583 : Blo 2255435 3385583 := bstep (se 1 (by rfl) ⟨2539187, by rfl⟩ : syracuseStep 3385583 = 5078375) B5078375
theorem B2257055 : Blo 2255435 2257055 := bstep (se 1 (by rfl) ⟨1692791, by rfl⟩ : syracuseStep 2257055 = 3385583) B3385583
theorem B3385589 : Blo 2255435 3385589 := bbase (se 5 (by rfl) ⟨158699, by rfl⟩ : syracuseStep 3385589 = 317399) (by norm_num)
theorem B2257059 : Blo 2255435 2257059 := bstep (se 1 (by rfl) ⟨1692794, by rfl⟩ : syracuseStep 2257059 = 3385589) B3385589
theorem B4343357 : Blo 2255435 4343357 := bbase (se 3 (by rfl) ⟨814379, by rfl⟩ : syracuseStep 4343357 = 1628759) (by norm_num)
theorem B2895571 : Blo 2255435 2895571 := bstep (se 1 (by rfl) ⟨2171678, by rfl⟩ : syracuseStep 2895571 = 4343357) B4343357
theorem B15443045 : Blo 2255435 15443045 := bstep (se 4 (by rfl) ⟨1447785, by rfl⟩ : syracuseStep 15443045 = 2895571) B2895571
theorem B10295363 : Blo 2255435 10295363 := bstep (se 1 (by rfl) ⟨7721522, by rfl⟩ : syracuseStep 10295363 = 15443045) B15443045
theorem B27454301 : Blo 2255435 27454301 := bstep (se 3 (by rfl) ⟨5147681, by rfl⟩ : syracuseStep 27454301 = 10295363) B10295363
theorem B18302867 : Blo 2255435 18302867 := bstep (se 1 (by rfl) ⟨13727150, by rfl⟩ : syracuseStep 18302867 = 27454301) B27454301
theorem B12201911 : Blo 2255435 12201911 := bstep (se 1 (by rfl) ⟨9151433, by rfl⟩ : syracuseStep 12201911 = 18302867) B18302867
theorem B8134607 : Blo 2255435 8134607 := bstep (se 1 (by rfl) ⟨6100955, by rfl⟩ : syracuseStep 8134607 = 12201911) B12201911
theorem B21692285 : Blo 2255435 21692285 := bstep (se 3 (by rfl) ⟨4067303, by rfl⟩ : syracuseStep 21692285 = 8134607) B8134607
theorem B14461523 : Blo 2255435 14461523 := bstep (se 1 (by rfl) ⟨10846142, by rfl⟩ : syracuseStep 14461523 = 21692285) B21692285
theorem B9641015 : Blo 2255435 9641015 := bstep (se 1 (by rfl) ⟨7230761, by rfl⟩ : syracuseStep 9641015 = 14461523) B14461523
theorem B6427343 : Blo 2255435 6427343 := bstep (se 1 (by rfl) ⟨4820507, by rfl⟩ : syracuseStep 6427343 = 9641015) B9641015
theorem B4284895 : Blo 2255435 4284895 := bstep (se 1 (by rfl) ⟨3213671, by rfl⟩ : syracuseStep 4284895 = 6427343) B6427343
theorem B5713193 : Blo 2255435 5713193 := bstep (se 2 (by rfl) ⟨2142447, by rfl⟩ : syracuseStep 5713193 = 4284895) B4284895
theorem B3808795 : Blo 2255435 3808795 := bstep (se 1 (by rfl) ⟨2856596, by rfl⟩ : syracuseStep 3808795 = 5713193) B5713193
theorem B5078393 : Blo 2255435 5078393 := bstep (se 2 (by rfl) ⟨1904397, by rfl⟩ : syracuseStep 5078393 = 3808795) B3808795
theorem B3385595 : Blo 2255435 3385595 := bstep (se 1 (by rfl) ⟨2539196, by rfl⟩ : syracuseStep 3385595 = 5078393) B5078393
theorem B2257063 : Blo 2255435 2257063 := bstep (se 1 (by rfl) ⟨1692797, by rfl⟩ : syracuseStep 2257063 = 3385595) B3385595
theorem B2539201 : Blo 2255435 2539201 := bbase (se 2 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 2539201 = 1904401) (by norm_num)
theorem B3385601 : Blo 2255435 3385601 := bstep (se 2 (by rfl) ⟨1269600, by rfl⟩ : syracuseStep 3385601 = 2539201) B2539201
theorem B2257067 : Blo 2255435 2257067 := bstep (se 1 (by rfl) ⟨1692800, by rfl⟩ : syracuseStep 2257067 = 3385601) B3385601
theorem B5713213 : Blo 2255435 5713213 := bbase (se 3 (by rfl) ⟨1071227, by rfl⟩ : syracuseStep 5713213 = 2142455) (by norm_num)
theorem B7617617 : Blo 2255435 7617617 := bstep (se 2 (by rfl) ⟨2856606, by rfl⟩ : syracuseStep 7617617 = 5713213) B5713213
theorem B5078411 : Blo 2255435 5078411 := bstep (se 1 (by rfl) ⟨3808808, by rfl⟩ : syracuseStep 5078411 = 7617617) B7617617
theorem B3385607 : Blo 2255435 3385607 := bstep (se 1 (by rfl) ⟨2539205, by rfl⟩ : syracuseStep 3385607 = 5078411) B5078411
theorem B2257071 : Blo 2255435 2257071 := bstep (se 1 (by rfl) ⟨1692803, by rfl⟩ : syracuseStep 2257071 = 3385607) B3385607
theorem B3385613 : Blo 2255435 3385613 := bbase (se 3 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 3385613 = 1269605) (by norm_num)
theorem B2257075 : Blo 2255435 2257075 := bstep (se 1 (by rfl) ⟨1692806, by rfl⟩ : syracuseStep 2257075 = 3385613) B3385613
theorem B5078429 : Blo 2255435 5078429 := bbase (se 3 (by rfl) ⟨952205, by rfl⟩ : syracuseStep 5078429 = 1904411) (by norm_num)
theorem B3385619 : Blo 2255435 3385619 := bstep (se 1 (by rfl) ⟨2539214, by rfl⟩ : syracuseStep 3385619 = 5078429) B5078429
theorem B2257079 : Blo 2255435 2257079 := bstep (se 1 (by rfl) ⟨1692809, by rfl⟩ : syracuseStep 2257079 = 3385619) B3385619
theorem B3808829 : Blo 2255435 3808829 := bbase (se 3 (by rfl) ⟨714155, by rfl⟩ : syracuseStep 3808829 = 1428311) (by norm_num)
theorem B2539219 : Blo 2255435 2539219 := bstep (se 1 (by rfl) ⟨1904414, by rfl⟩ : syracuseStep 2539219 = 3808829) B3808829
theorem B3385625 : Blo 2255435 3385625 := bstep (se 2 (by rfl) ⟨1269609, by rfl⟩ : syracuseStep 3385625 = 2539219) B2539219
theorem B2257083 : Blo 2255435 2257083 := bstep (se 1 (by rfl) ⟨1692812, by rfl⟩ : syracuseStep 2257083 = 3385625) B3385625
theorem B2573869 : Blo 2255435 2573869 := bbase (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) (by norm_num)
theorem B3431825 : Blo 2255435 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B2287883 : Blo 2255435 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B6101021 : Blo 2255435 6101021 := bstep (se 3 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 6101021 = 2287883) B2287883
theorem B4067347 : Blo 2255435 4067347 := bstep (se 1 (by rfl) ⟨3050510, by rfl⟩ : syracuseStep 4067347 = 6101021) B6101021
theorem B5423129 : Blo 2255435 5423129 := bstep (se 2 (by rfl) ⟨2033673, by rfl⟩ : syracuseStep 5423129 = 4067347) B4067347
theorem B3615419 : Blo 2255435 3615419 := bstep (se 1 (by rfl) ⟨2711564, by rfl⟩ : syracuseStep 3615419 = 5423129) B5423129
theorem B2410279 : Blo 2255435 2410279 := bstep (se 1 (by rfl) ⟨1807709, by rfl⟩ : syracuseStep 2410279 = 3615419) B3615419
theorem B12854821 : Blo 2255435 12854821 := bstep (se 4 (by rfl) ⟨1205139, by rfl⟩ : syracuseStep 12854821 = 2410279) B2410279
theorem B17139761 : Blo 2255435 17139761 := bstep (se 2 (by rfl) ⟨6427410, by rfl⟩ : syracuseStep 17139761 = 12854821) B12854821
theorem B11426507 : Blo 2255435 11426507 := bstep (se 1 (by rfl) ⟨8569880, by rfl⟩ : syracuseStep 11426507 = 17139761) B17139761
theorem B7617671 : Blo 2255435 7617671 := bstep (se 1 (by rfl) ⟨5713253, by rfl⟩ : syracuseStep 7617671 = 11426507) B11426507
theorem B5078447 : Blo 2255435 5078447 := bstep (se 1 (by rfl) ⟨3808835, by rfl⟩ : syracuseStep 5078447 = 7617671) B7617671
theorem B3385631 : Blo 2255435 3385631 := bstep (se 1 (by rfl) ⟨2539223, by rfl⟩ : syracuseStep 3385631 = 5078447) B5078447
theorem B2257087 : Blo 2255435 2257087 := bstep (se 1 (by rfl) ⟨1692815, by rfl⟩ : syracuseStep 2257087 = 3385631) B3385631
theorem B3385637 : Blo 2255435 3385637 := bbase (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) (by norm_num)
theorem B2257091 : Blo 2255435 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B2856637 : Blo 2255435 2856637 := bbase (se 3 (by rfl) ⟨535619, by rfl⟩ : syracuseStep 2856637 = 1071239) (by norm_num)
theorem B3808849 : Blo 2255435 3808849 := bstep (se 2 (by rfl) ⟨1428318, by rfl⟩ : syracuseStep 3808849 = 2856637) B2856637
theorem B5078465 : Blo 2255435 5078465 := bstep (se 2 (by rfl) ⟨1904424, by rfl⟩ : syracuseStep 5078465 = 3808849) B3808849
theorem B3385643 : Blo 2255435 3385643 := bstep (se 1 (by rfl) ⟨2539232, by rfl⟩ : syracuseStep 3385643 = 5078465) B5078465
theorem B2257095 : Blo 2255435 2257095 := bstep (se 1 (by rfl) ⟨1692821, by rfl⟩ : syracuseStep 2257095 = 3385643) B3385643
theorem B2539237 : Blo 2255435 2539237 := bbase (se 4 (by rfl) ⟨238053, by rfl⟩ : syracuseStep 2539237 = 476107) (by norm_num)
theorem B3385649 : Blo 2255435 3385649 := bstep (se 2 (by rfl) ⟨1269618, by rfl⟩ : syracuseStep 3385649 = 2539237) B2539237
theorem B2257099 : Blo 2255435 2257099 := bstep (se 1 (by rfl) ⟨1692824, by rfl⟩ : syracuseStep 2257099 = 3385649) B3385649
theorem B3615445 : Blo 2255435 3615445 := bbase (se 7 (by rfl) ⟨42368, by rfl⟩ : syracuseStep 3615445 = 84737) (by norm_num)
theorem B4820593 : Blo 2255435 4820593 := bstep (se 2 (by rfl) ⟨1807722, by rfl⟩ : syracuseStep 4820593 = 3615445) B3615445
theorem B6427457 : Blo 2255435 6427457 := bstep (se 2 (by rfl) ⟨2410296, by rfl⟩ : syracuseStep 6427457 = 4820593) B4820593
theorem B4284971 : Blo 2255435 4284971 := bstep (se 1 (by rfl) ⟨3213728, by rfl⟩ : syracuseStep 4284971 = 6427457) B6427457
theorem B2856647 : Blo 2255435 2856647 := bstep (se 1 (by rfl) ⟨2142485, by rfl⟩ : syracuseStep 2856647 = 4284971) B4284971
theorem B7617725 : Blo 2255435 7617725 := bstep (se 3 (by rfl) ⟨1428323, by rfl⟩ : syracuseStep 7617725 = 2856647) B2856647
theorem B5078483 : Blo 2255435 5078483 := bstep (se 1 (by rfl) ⟨3808862, by rfl⟩ : syracuseStep 5078483 = 7617725) B7617725
theorem B3385655 : Blo 2255435 3385655 := bstep (se 1 (by rfl) ⟨2539241, by rfl⟩ : syracuseStep 3385655 = 5078483) B5078483
theorem B2257103 : Blo 2255435 2257103 := bstep (se 1 (by rfl) ⟨1692827, by rfl⟩ : syracuseStep 2257103 = 3385655) B3385655
theorem B3385661 : Blo 2255435 3385661 := bbase (se 3 (by rfl) ⟨634811, by rfl⟩ : syracuseStep 3385661 = 1269623) (by norm_num)
theorem B2257107 : Blo 2255435 2257107 := bstep (se 1 (by rfl) ⟨1692830, by rfl⟩ : syracuseStep 2257107 = 3385661) B3385661
theorem B5078501 : Blo 2255435 5078501 := bbase (se 4 (by rfl) ⟨476109, by rfl⟩ : syracuseStep 5078501 = 952219) (by norm_num)
theorem B3385667 : Blo 2255435 3385667 := bstep (se 1 (by rfl) ⟨2539250, by rfl⟩ : syracuseStep 3385667 = 5078501) B5078501
theorem B2257111 : Blo 2255435 2257111 := bstep (se 1 (by rfl) ⟨1692833, by rfl⟩ : syracuseStep 2257111 = 3385667) B3385667
theorem B5713325 : Blo 2255435 5713325 := bbase (se 3 (by rfl) ⟨1071248, by rfl⟩ : syracuseStep 5713325 = 2142497) (by norm_num)
theorem B3808883 : Blo 2255435 3808883 := bstep (se 1 (by rfl) ⟨2856662, by rfl⟩ : syracuseStep 3808883 = 5713325) B5713325
theorem B2539255 : Blo 2255435 2539255 := bstep (se 1 (by rfl) ⟨1904441, by rfl⟩ : syracuseStep 2539255 = 3808883) B3808883
theorem B3385673 : Blo 2255435 3385673 := bstep (se 2 (by rfl) ⟨1269627, by rfl⟩ : syracuseStep 3385673 = 2539255) B2539255
theorem B2257115 : Blo 2255435 2257115 := bstep (se 1 (by rfl) ⟨1692836, by rfl⟩ : syracuseStep 2257115 = 3385673) B3385673
theorem B4067405 : Blo 2255435 4067405 := bbase (se 3 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 4067405 = 1525277) (by norm_num)
theorem B2711603 : Blo 2255435 2711603 := bstep (se 1 (by rfl) ⟨2033702, by rfl⟩ : syracuseStep 2711603 = 4067405) B4067405
theorem B7230941 : Blo 2255435 7230941 := bstep (se 3 (by rfl) ⟨1355801, by rfl⟩ : syracuseStep 7230941 = 2711603) B2711603
theorem B4820627 : Blo 2255435 4820627 := bstep (se 1 (by rfl) ⟨3615470, by rfl⟩ : syracuseStep 4820627 = 7230941) B7230941
theorem B3213751 : Blo 2255435 3213751 := bstep (se 1 (by rfl) ⟨2410313, by rfl⟩ : syracuseStep 3213751 = 4820627) B4820627
theorem B4285001 : Blo 2255435 4285001 := bstep (se 2 (by rfl) ⟨1606875, by rfl⟩ : syracuseStep 4285001 = 3213751) B3213751
theorem B11426669 : Blo 2255435 11426669 := bstep (se 3 (by rfl) ⟨2142500, by rfl⟩ : syracuseStep 11426669 = 4285001) B4285001
theorem B7617779 : Blo 2255435 7617779 := bstep (se 1 (by rfl) ⟨5713334, by rfl⟩ : syracuseStep 7617779 = 11426669) B11426669
theorem B5078519 : Blo 2255435 5078519 := bstep (se 1 (by rfl) ⟨3808889, by rfl⟩ : syracuseStep 5078519 = 7617779) B7617779
theorem B3385679 : Blo 2255435 3385679 := bstep (se 1 (by rfl) ⟨2539259, by rfl⟩ : syracuseStep 3385679 = 5078519) B5078519
theorem B2257119 : Blo 2255435 2257119 := bstep (se 1 (by rfl) ⟨1692839, by rfl⟩ : syracuseStep 2257119 = 3385679) B3385679
theorem B3385685 : Blo 2255435 3385685 := bbase (se 10 (by rfl) ⟨4959, by rfl⟩ : syracuseStep 3385685 = 9919) (by norm_num)
theorem B2257123 : Blo 2255435 2257123 := bstep (se 1 (by rfl) ⟨1692842, by rfl⟩ : syracuseStep 2257123 = 3385685) B3385685
theorem B6427525 : Blo 2255435 6427525 := bbase (se 4 (by rfl) ⟨602580, by rfl⟩ : syracuseStep 6427525 = 1205161) (by norm_num)
theorem B8570033 : Blo 2255435 8570033 := bstep (se 2 (by rfl) ⟨3213762, by rfl⟩ : syracuseStep 8570033 = 6427525) B6427525
theorem B5713355 : Blo 2255435 5713355 := bstep (se 1 (by rfl) ⟨4285016, by rfl⟩ : syracuseStep 5713355 = 8570033) B8570033
theorem B3808903 : Blo 2255435 3808903 := bstep (se 1 (by rfl) ⟨2856677, by rfl⟩ : syracuseStep 3808903 = 5713355) B5713355
theorem B5078537 : Blo 2255435 5078537 := bstep (se 2 (by rfl) ⟨1904451, by rfl⟩ : syracuseStep 5078537 = 3808903) B3808903
theorem B3385691 : Blo 2255435 3385691 := bstep (se 1 (by rfl) ⟨2539268, by rfl⟩ : syracuseStep 3385691 = 5078537) B5078537
theorem B2257127 : Blo 2255435 2257127 := bstep (se 1 (by rfl) ⟨1692845, by rfl⟩ : syracuseStep 2257127 = 3385691) B3385691
theorem B2539273 : Blo 2255435 2539273 := bbase (se 2 (by rfl) ⟨952227, by rfl⟩ : syracuseStep 2539273 = 1904455) (by norm_num)
theorem B3385697 : Blo 2255435 3385697 := bstep (se 2 (by rfl) ⟨1269636, by rfl⟩ : syracuseStep 3385697 = 2539273) B2539273
theorem B2257131 : Blo 2255435 2257131 := bstep (se 1 (by rfl) ⟨1692848, by rfl⟩ : syracuseStep 2257131 = 3385697) B3385697
theorem B3860885 : Blo 2255435 3860885 := bbase (se 6 (by rfl) ⟨90489, by rfl⟩ : syracuseStep 3860885 = 180979) (by norm_num)
theorem B2573923 : Blo 2255435 2573923 := bstep (se 1 (by rfl) ⟨1930442, by rfl⟩ : syracuseStep 2573923 = 3860885) B3860885
theorem B3431897 : Blo 2255435 3431897 := bstep (se 2 (by rfl) ⟨1286961, by rfl⟩ : syracuseStep 3431897 = 2573923) B2573923
theorem B2287931 : Blo 2255435 2287931 := bstep (se 1 (by rfl) ⟨1715948, by rfl⟩ : syracuseStep 2287931 = 3431897) B3431897
theorem B24404597 : Blo 2255435 24404597 := bstep (se 5 (by rfl) ⟨1143965, by rfl⟩ : syracuseStep 24404597 = 2287931) B2287931
theorem B16269731 : Blo 2255435 16269731 := bstep (se 1 (by rfl) ⟨12202298, by rfl⟩ : syracuseStep 16269731 = 24404597) B24404597
theorem B10846487 : Blo 2255435 10846487 := bstep (se 1 (by rfl) ⟨8134865, by rfl⟩ : syracuseStep 10846487 = 16269731) B16269731
theorem B28923965 : Blo 2255435 28923965 := bstep (se 3 (by rfl) ⟨5423243, by rfl⟩ : syracuseStep 28923965 = 10846487) B10846487
theorem B19282643 : Blo 2255435 19282643 := bstep (se 1 (by rfl) ⟨14461982, by rfl⟩ : syracuseStep 19282643 = 28923965) B28923965
theorem B12855095 : Blo 2255435 12855095 := bstep (se 1 (by rfl) ⟨9641321, by rfl⟩ : syracuseStep 12855095 = 19282643) B19282643
theorem B8570063 : Blo 2255435 8570063 := bstep (se 1 (by rfl) ⟨6427547, by rfl⟩ : syracuseStep 8570063 = 12855095) B12855095
theorem B5713375 : Blo 2255435 5713375 := bstep (se 1 (by rfl) ⟨4285031, by rfl⟩ : syracuseStep 5713375 = 8570063) B8570063
theorem B7617833 : Blo 2255435 7617833 := bstep (se 2 (by rfl) ⟨2856687, by rfl⟩ : syracuseStep 7617833 = 5713375) B5713375
theorem B5078555 : Blo 2255435 5078555 := bstep (se 1 (by rfl) ⟨3808916, by rfl⟩ : syracuseStep 5078555 = 7617833) B7617833
theorem B3385703 : Blo 2255435 3385703 := bstep (se 1 (by rfl) ⟨2539277, by rfl⟩ : syracuseStep 3385703 = 5078555) B5078555
theorem B2257135 : Blo 2255435 2257135 := bstep (se 1 (by rfl) ⟨1692851, by rfl⟩ : syracuseStep 2257135 = 3385703) B3385703
theorem B3385709 : Blo 2255435 3385709 := bbase (se 3 (by rfl) ⟨634820, by rfl⟩ : syracuseStep 3385709 = 1269641) (by norm_num)
theorem B2257139 : Blo 2255435 2257139 := bstep (se 1 (by rfl) ⟨1692854, by rfl⟩ : syracuseStep 2257139 = 3385709) B3385709
theorem B5078573 : Blo 2255435 5078573 := bbase (se 3 (by rfl) ⟨952232, by rfl⟩ : syracuseStep 5078573 = 1904465) (by norm_num)
theorem B3385715 : Blo 2255435 3385715 := bstep (se 1 (by rfl) ⟨2539286, by rfl⟩ : syracuseStep 3385715 = 5078573) B5078573
theorem B2257143 : Blo 2255435 2257143 := bstep (se 1 (by rfl) ⟨1692857, by rfl⟩ : syracuseStep 2257143 = 3385715) B3385715
theorem B27829909 : Blo 2255435 27829909 := bbase (se 6 (by rfl) ⟨652263, by rfl⟩ : syracuseStep 27829909 = 1304527) (by norm_num)
theorem B37106545 : Blo 2255435 37106545 := bstep (se 2 (by rfl) ⟨13914954, by rfl⟩ : syracuseStep 37106545 = 27829909) B27829909
theorem B49475393 : Blo 2255435 49475393 := bstep (se 2 (by rfl) ⟨18553272, by rfl⟩ : syracuseStep 49475393 = 37106545) B37106545
theorem B32983595 : Blo 2255435 32983595 := bstep (se 1 (by rfl) ⟨24737696, by rfl⟩ : syracuseStep 32983595 = 49475393) B49475393
theorem B21989063 : Blo 2255435 21989063 := bstep (se 1 (by rfl) ⟨16491797, by rfl⟩ : syracuseStep 21989063 = 32983595) B32983595
theorem B14659375 : Blo 2255435 14659375 := bstep (se 1 (by rfl) ⟨10994531, by rfl⟩ : syracuseStep 14659375 = 21989063) B21989063
theorem B19545833 : Blo 2255435 19545833 := bstep (se 2 (by rfl) ⟨7329687, by rfl⟩ : syracuseStep 19545833 = 14659375) B14659375
theorem B13030555 : Blo 2255435 13030555 := bstep (se 1 (by rfl) ⟨9772916, by rfl⟩ : syracuseStep 13030555 = 19545833) B19545833
theorem B17374073 : Blo 2255435 17374073 := bstep (se 2 (by rfl) ⟨6515277, by rfl⟩ : syracuseStep 17374073 = 13030555) B13030555
theorem B46330861 : Blo 2255435 46330861 := bstep (se 3 (by rfl) ⟨8687036, by rfl⟩ : syracuseStep 46330861 = 17374073) B17374073
theorem B61774481 : Blo 2255435 61774481 := bstep (se 2 (by rfl) ⟨23165430, by rfl⟩ : syracuseStep 61774481 = 46330861) B46330861
theorem B41182987 : Blo 2255435 41182987 := bstep (se 1 (by rfl) ⟨30887240, by rfl⟩ : syracuseStep 41182987 = 61774481) B61774481
theorem B54910649 : Blo 2255435 54910649 := bstep (se 2 (by rfl) ⟨20591493, by rfl⟩ : syracuseStep 54910649 = 41182987) B41182987
theorem B36607099 : Blo 2255435 36607099 := bstep (se 1 (by rfl) ⟨27455324, by rfl⟩ : syracuseStep 36607099 = 54910649) B54910649
theorem B48809465 : Blo 2255435 48809465 := bstep (se 2 (by rfl) ⟨18303549, by rfl⟩ : syracuseStep 48809465 = 36607099) B36607099
theorem B32539643 : Blo 2255435 32539643 := bstep (se 1 (by rfl) ⟨24404732, by rfl⟩ : syracuseStep 32539643 = 48809465) B48809465
theorem B21693095 : Blo 2255435 21693095 := bstep (se 1 (by rfl) ⟨16269821, by rfl⟩ : syracuseStep 21693095 = 32539643) B32539643
theorem B14462063 : Blo 2255435 14462063 := bstep (se 1 (by rfl) ⟨10846547, by rfl⟩ : syracuseStep 14462063 = 21693095) B21693095
theorem B9641375 : Blo 2255435 9641375 := bstep (se 1 (by rfl) ⟨7231031, by rfl⟩ : syracuseStep 9641375 = 14462063) B14462063
theorem B6427583 : Blo 2255435 6427583 := bstep (se 1 (by rfl) ⟨4820687, by rfl⟩ : syracuseStep 6427583 = 9641375) B9641375
theorem B4285055 : Blo 2255435 4285055 := bstep (se 1 (by rfl) ⟨3213791, by rfl⟩ : syracuseStep 4285055 = 6427583) B6427583
theorem B2856703 : Blo 2255435 2856703 := bstep (se 1 (by rfl) ⟨2142527, by rfl⟩ : syracuseStep 2856703 = 4285055) B4285055
theorem B3808937 : Blo 2255435 3808937 := bstep (se 2 (by rfl) ⟨1428351, by rfl⟩ : syracuseStep 3808937 = 2856703) B2856703
theorem B2539291 : Blo 2255435 2539291 := bstep (se 1 (by rfl) ⟨1904468, by rfl⟩ : syracuseStep 2539291 = 3808937) B3808937
theorem B3385721 : Blo 2255435 3385721 := bstep (se 2 (by rfl) ⟨1269645, by rfl⟩ : syracuseStep 3385721 = 2539291) B2539291
theorem B2257147 : Blo 2255435 2257147 := bstep (se 1 (by rfl) ⟨1692860, by rfl⟩ : syracuseStep 2257147 = 3385721) B3385721
theorem B2711641 : Blo 2255435 2711641 := bbase (se 2 (by rfl) ⟨1016865, by rfl⟩ : syracuseStep 2711641 = 2033731) (by norm_num)
theorem B3615521 : Blo 2255435 3615521 := bstep (se 2 (by rfl) ⟨1355820, by rfl⟩ : syracuseStep 3615521 = 2711641) B2711641
theorem B38565557 : Blo 2255435 38565557 := bstep (se 5 (by rfl) ⟨1807760, by rfl⟩ : syracuseStep 38565557 = 3615521) B3615521
theorem B25710371 : Blo 2255435 25710371 := bstep (se 1 (by rfl) ⟨19282778, by rfl⟩ : syracuseStep 25710371 = 38565557) B38565557
theorem B17140247 : Blo 2255435 17140247 := bstep (se 1 (by rfl) ⟨12855185, by rfl⟩ : syracuseStep 17140247 = 25710371) B25710371
theorem B11426831 : Blo 2255435 11426831 := bstep (se 1 (by rfl) ⟨8570123, by rfl⟩ : syracuseStep 11426831 = 17140247) B17140247
theorem B7617887 : Blo 2255435 7617887 := bstep (se 1 (by rfl) ⟨5713415, by rfl⟩ : syracuseStep 7617887 = 11426831) B11426831
theorem B5078591 : Blo 2255435 5078591 := bstep (se 1 (by rfl) ⟨3808943, by rfl⟩ : syracuseStep 5078591 = 7617887) B7617887
theorem B3385727 : Blo 2255435 3385727 := bstep (se 1 (by rfl) ⟨2539295, by rfl⟩ : syracuseStep 3385727 = 5078591) B5078591
theorem B2257151 : Blo 2255435 2257151 := bstep (se 1 (by rfl) ⟨1692863, by rfl⟩ : syracuseStep 2257151 = 3385727) B3385727
theorem B3385733 : Blo 2255435 3385733 := bbase (se 4 (by rfl) ⟨317412, by rfl⟩ : syracuseStep 3385733 = 634825) (by norm_num)
theorem B2257155 : Blo 2255435 2257155 := bstep (se 1 (by rfl) ⟨1692866, by rfl⟩ : syracuseStep 2257155 = 3385733) B3385733
theorem B3808957 : Blo 2255435 3808957 := bbase (se 3 (by rfl) ⟨714179, by rfl⟩ : syracuseStep 3808957 = 1428359) (by norm_num)
theorem B5078609 : Blo 2255435 5078609 := bstep (se 2 (by rfl) ⟨1904478, by rfl⟩ : syracuseStep 5078609 = 3808957) B3808957
theorem B3385739 : Blo 2255435 3385739 := bstep (se 1 (by rfl) ⟨2539304, by rfl⟩ : syracuseStep 3385739 = 5078609) B5078609
theorem B2257159 : Blo 2255435 2257159 := bstep (se 1 (by rfl) ⟨1692869, by rfl⟩ : syracuseStep 2257159 = 3385739) B3385739
theorem B2539309 : Blo 2255435 2539309 := bbase (se 3 (by rfl) ⟨476120, by rfl⟩ : syracuseStep 2539309 = 952241) (by norm_num)
theorem B3385745 : Blo 2255435 3385745 := bstep (se 2 (by rfl) ⟨1269654, by rfl⟩ : syracuseStep 3385745 = 2539309) B2539309
theorem B2257163 : Blo 2255435 2257163 := bstep (se 1 (by rfl) ⟨1692872, by rfl⟩ : syracuseStep 2257163 = 3385745) B3385745
theorem B7617941 : Blo 2255435 7617941 := bbase (se 6 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 7617941 = 357091) (by norm_num)
theorem B5078627 : Blo 2255435 5078627 := bstep (se 1 (by rfl) ⟨3808970, by rfl⟩ : syracuseStep 5078627 = 7617941) B7617941
theorem B3385751 : Blo 2255435 3385751 := bstep (se 1 (by rfl) ⟨2539313, by rfl⟩ : syracuseStep 3385751 = 5078627) B5078627
theorem B2257167 : Blo 2255435 2257167 := bstep (se 1 (by rfl) ⟨1692875, by rfl⟩ : syracuseStep 2257167 = 3385751) B3385751
theorem B3385757 : Blo 2255435 3385757 := bbase (se 3 (by rfl) ⟨634829, by rfl⟩ : syracuseStep 3385757 = 1269659) (by norm_num)
theorem B2257171 : Blo 2255435 2257171 := bstep (se 1 (by rfl) ⟨1692878, by rfl⟩ : syracuseStep 2257171 = 3385757) B3385757
theorem B5078645 : Blo 2255435 5078645 := bbase (se 5 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 5078645 = 476123) (by norm_num)
theorem B3385763 : Blo 2255435 3385763 := bstep (se 1 (by rfl) ⟨2539322, by rfl⟩ : syracuseStep 3385763 = 5078645) B5078645
theorem B2257175 : Blo 2255435 2257175 := bstep (se 1 (by rfl) ⟨1692881, by rfl⟩ : syracuseStep 2257175 = 3385763) B3385763
theorem B3431965 : Blo 2255435 3431965 := bbase (se 3 (by rfl) ⟨643493, by rfl⟩ : syracuseStep 3431965 = 1286987) (by norm_num)
theorem B4575953 : Blo 2255435 4575953 := bstep (se 2 (by rfl) ⟨1715982, by rfl⟩ : syracuseStep 4575953 = 3431965) B3431965
theorem B3050635 : Blo 2255435 3050635 := bstep (se 1 (by rfl) ⟨2287976, by rfl⟩ : syracuseStep 3050635 = 4575953) B4575953
theorem B4067513 : Blo 2255435 4067513 := bstep (se 2 (by rfl) ⟨1525317, by rfl⟩ : syracuseStep 4067513 = 3050635) B3050635
theorem B2711675 : Blo 2255435 2711675 := bstep (se 1 (by rfl) ⟨2033756, by rfl⟩ : syracuseStep 2711675 = 4067513) B4067513
theorem B7231133 : Blo 2255435 7231133 := bstep (se 3 (by rfl) ⟨1355837, by rfl⟩ : syracuseStep 7231133 = 2711675) B2711675
theorem B19283021 : Blo 2255435 19283021 := bstep (se 3 (by rfl) ⟨3615566, by rfl⟩ : syracuseStep 19283021 = 7231133) B7231133
theorem B12855347 : Blo 2255435 12855347 := bstep (se 1 (by rfl) ⟨9641510, by rfl⟩ : syracuseStep 12855347 = 19283021) B19283021
theorem B8570231 : Blo 2255435 8570231 := bstep (se 1 (by rfl) ⟨6427673, by rfl⟩ : syracuseStep 8570231 = 12855347) B12855347
theorem B5713487 : Blo 2255435 5713487 := bstep (se 1 (by rfl) ⟨4285115, by rfl⟩ : syracuseStep 5713487 = 8570231) B8570231
theorem B3808991 : Blo 2255435 3808991 := bstep (se 1 (by rfl) ⟨2856743, by rfl⟩ : syracuseStep 3808991 = 5713487) B5713487
theorem B2539327 : Blo 2255435 2539327 := bstep (se 1 (by rfl) ⟨1904495, by rfl⟩ : syracuseStep 2539327 = 3808991) B3808991
theorem B3385769 : Blo 2255435 3385769 := bstep (se 2 (by rfl) ⟨1269663, by rfl⟩ : syracuseStep 3385769 = 2539327) B2539327
theorem B2257179 : Blo 2255435 2257179 := bstep (se 1 (by rfl) ⟨1692884, by rfl⟩ : syracuseStep 2257179 = 3385769) B3385769
theorem B8570245 : Blo 2255435 8570245 := bbase (se 4 (by rfl) ⟨803460, by rfl⟩ : syracuseStep 8570245 = 1606921) (by norm_num)
theorem B11426993 : Blo 2255435 11426993 := bstep (se 2 (by rfl) ⟨4285122, by rfl⟩ : syracuseStep 11426993 = 8570245) B8570245
theorem B7617995 : Blo 2255435 7617995 := bstep (se 1 (by rfl) ⟨5713496, by rfl⟩ : syracuseStep 7617995 = 11426993) B11426993
theorem B5078663 : Blo 2255435 5078663 := bstep (se 1 (by rfl) ⟨3808997, by rfl⟩ : syracuseStep 5078663 = 7617995) B7617995
theorem B3385775 : Blo 2255435 3385775 := bstep (se 1 (by rfl) ⟨2539331, by rfl⟩ : syracuseStep 3385775 = 5078663) B5078663
theorem B2257183 : Blo 2255435 2257183 := bstep (se 1 (by rfl) ⟨1692887, by rfl⟩ : syracuseStep 2257183 = 3385775) B3385775
theorem B3385781 : Blo 2255435 3385781 := bbase (se 5 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 3385781 = 317417) (by norm_num)
theorem B2257187 : Blo 2255435 2257187 := bstep (se 1 (by rfl) ⟨1692890, by rfl⟩ : syracuseStep 2257187 = 3385781) B3385781
theorem B5713517 : Blo 2255435 5713517 := bbase (se 3 (by rfl) ⟨1071284, by rfl⟩ : syracuseStep 5713517 = 2142569) (by norm_num)
theorem B3809011 : Blo 2255435 3809011 := bstep (se 1 (by rfl) ⟨2856758, by rfl⟩ : syracuseStep 3809011 = 5713517) B5713517
theorem B5078681 : Blo 2255435 5078681 := bstep (se 2 (by rfl) ⟨1904505, by rfl⟩ : syracuseStep 5078681 = 3809011) B3809011
theorem B3385787 : Blo 2255435 3385787 := bstep (se 1 (by rfl) ⟨2539340, by rfl⟩ : syracuseStep 3385787 = 5078681) B5078681
theorem B2257191 : Blo 2255435 2257191 := bstep (se 1 (by rfl) ⟨1692893, by rfl⟩ : syracuseStep 2257191 = 3385787) B3385787
theorem B2539345 : Blo 2255435 2539345 := bbase (se 2 (by rfl) ⟨952254, by rfl⟩ : syracuseStep 2539345 = 1904509) (by norm_num)
theorem B3385793 : Blo 2255435 3385793 := bstep (se 2 (by rfl) ⟨1269672, by rfl⟩ : syracuseStep 3385793 = 2539345) B2539345
theorem B2257195 : Blo 2255435 2257195 := bstep (se 1 (by rfl) ⟨1692896, by rfl⟩ : syracuseStep 2257195 = 3385793) B3385793
theorem B5791493 : Blo 2255435 5791493 := bbase (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) (by norm_num)
theorem B3860995 : Blo 2255435 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B5147993 : Blo 2255435 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B13727981 : Blo 2255435 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B9151987 : Blo 2255435 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B12202649 : Blo 2255435 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B8135099 : Blo 2255435 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B5423399 : Blo 2255435 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B3615599 : Blo 2255435 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B2410399 : Blo 2255435 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B3213865 : Blo 2255435 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B4285153 : Blo 2255435 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B5713537 : Blo 2255435 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B7618049 : Blo 2255435 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B5078699 : Blo 2255435 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B3385799 : Blo 2255435 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B2257199 : Blo 2255435 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B3385805 : Blo 2255435 3385805 := bbase (se 3 (by rfl) ⟨634838, by rfl⟩ : syracuseStep 3385805 = 1269677) (by norm_num)
theorem B2257203 : Blo 2255435 2257203 := bstep (se 1 (by rfl) ⟨1692902, by rfl⟩ : syracuseStep 2257203 = 3385805) B3385805
theorem B5078717 : Blo 2255435 5078717 := bbase (se 3 (by rfl) ⟨952259, by rfl⟩ : syracuseStep 5078717 = 1904519) (by norm_num)
theorem B3385811 : Blo 2255435 3385811 := bstep (se 1 (by rfl) ⟨2539358, by rfl⟩ : syracuseStep 3385811 = 5078717) B5078717
theorem B2257207 : Blo 2255435 2257207 := bstep (se 1 (by rfl) ⟨1692905, by rfl⟩ : syracuseStep 2257207 = 3385811) B3385811
theorem B3809045 : Blo 2255435 3809045 := bbase (se 6 (by rfl) ⟨89274, by rfl⟩ : syracuseStep 3809045 = 178549) (by norm_num)
theorem B2539363 : Blo 2255435 2539363 := bstep (se 1 (by rfl) ⟨1904522, by rfl⟩ : syracuseStep 2539363 = 3809045) B3809045
theorem B3385817 : Blo 2255435 3385817 := bstep (se 2 (by rfl) ⟨1269681, by rfl⟩ : syracuseStep 3385817 = 2539363) B2539363
theorem B2257211 : Blo 2255435 2257211 := bstep (se 1 (by rfl) ⟨1692908, by rfl⟩ : syracuseStep 2257211 = 3385817) B3385817
theorem B46332245 : Blo 2255435 46332245 := bbase (se 10 (by rfl) ⟨67869, by rfl⟩ : syracuseStep 46332245 = 135739) (by norm_num)
theorem B30888163 : Blo 2255435 30888163 := bstep (se 1 (by rfl) ⟨23166122, by rfl⟩ : syracuseStep 30888163 = 46332245) B46332245
theorem B41184217 : Blo 2255435 41184217 := bstep (se 2 (by rfl) ⟨15444081, by rfl⟩ : syracuseStep 41184217 = 30888163) B30888163
theorem B54912289 : Blo 2255435 54912289 := bstep (se 2 (by rfl) ⟨20592108, by rfl⟩ : syracuseStep 54912289 = 41184217) B41184217
theorem B73216385 : Blo 2255435 73216385 := bstep (se 2 (by rfl) ⟨27456144, by rfl⟩ : syracuseStep 73216385 = 54912289) B54912289
theorem B48810923 : Blo 2255435 48810923 := bstep (se 1 (by rfl) ⟨36608192, by rfl⟩ : syracuseStep 48810923 = 73216385) B73216385
theorem B32540615 : Blo 2255435 32540615 := bstep (se 1 (by rfl) ⟨24405461, by rfl⟩ : syracuseStep 32540615 = 48810923) B48810923
theorem B21693743 : Blo 2255435 21693743 := bstep (se 1 (by rfl) ⟨16270307, by rfl⟩ : syracuseStep 21693743 = 32540615) B32540615
theorem B14462495 : Blo 2255435 14462495 := bstep (se 1 (by rfl) ⟨10846871, by rfl⟩ : syracuseStep 14462495 = 21693743) B21693743
theorem B9641663 : Blo 2255435 9641663 := bstep (se 1 (by rfl) ⟨7231247, by rfl⟩ : syracuseStep 9641663 = 14462495) B14462495
theorem B6427775 : Blo 2255435 6427775 := bstep (se 1 (by rfl) ⟨4820831, by rfl⟩ : syracuseStep 6427775 = 9641663) B9641663
theorem B17140733 : Blo 2255435 17140733 := bstep (se 3 (by rfl) ⟨3213887, by rfl⟩ : syracuseStep 17140733 = 6427775) B6427775
theorem B11427155 : Blo 2255435 11427155 := bstep (se 1 (by rfl) ⟨8570366, by rfl⟩ : syracuseStep 11427155 = 17140733) B17140733
theorem B7618103 : Blo 2255435 7618103 := bstep (se 1 (by rfl) ⟨5713577, by rfl⟩ : syracuseStep 7618103 = 11427155) B11427155
theorem B5078735 : Blo 2255435 5078735 := bstep (se 1 (by rfl) ⟨3809051, by rfl⟩ : syracuseStep 5078735 = 7618103) B7618103
theorem B3385823 : Blo 2255435 3385823 := bstep (se 1 (by rfl) ⟨2539367, by rfl⟩ : syracuseStep 3385823 = 5078735) B5078735
theorem B2257215 : Blo 2255435 2257215 := bstep (se 1 (by rfl) ⟨1692911, by rfl⟩ : syracuseStep 2257215 = 3385823) B3385823
theorem B3385829 : Blo 2255435 3385829 := bbase (se 4 (by rfl) ⟨317421, by rfl⟩ : syracuseStep 3385829 = 634843) (by norm_num)
theorem B2257219 : Blo 2255435 2257219 := bstep (se 1 (by rfl) ⟨1692914, by rfl⟩ : syracuseStep 2257219 = 3385829) B3385829
theorem B14462549 : Blo 2255435 14462549 := bbase (se 8 (by rfl) ⟨84741, by rfl⟩ : syracuseStep 14462549 = 169483) (by norm_num)
theorem B9641699 : Blo 2255435 9641699 := bstep (se 1 (by rfl) ⟨7231274, by rfl⟩ : syracuseStep 9641699 = 14462549) B14462549
theorem B6427799 : Blo 2255435 6427799 := bstep (se 1 (by rfl) ⟨4820849, by rfl⟩ : syracuseStep 6427799 = 9641699) B9641699
theorem B4285199 : Blo 2255435 4285199 := bstep (se 1 (by rfl) ⟨3213899, by rfl⟩ : syracuseStep 4285199 = 6427799) B6427799
theorem B2856799 : Blo 2255435 2856799 := bstep (se 1 (by rfl) ⟨2142599, by rfl⟩ : syracuseStep 2856799 = 4285199) B4285199
theorem B3809065 : Blo 2255435 3809065 := bstep (se 2 (by rfl) ⟨1428399, by rfl⟩ : syracuseStep 3809065 = 2856799) B2856799
theorem B5078753 : Blo 2255435 5078753 := bstep (se 2 (by rfl) ⟨1904532, by rfl⟩ : syracuseStep 5078753 = 3809065) B3809065
theorem B3385835 : Blo 2255435 3385835 := bstep (se 1 (by rfl) ⟨2539376, by rfl⟩ : syracuseStep 3385835 = 5078753) B5078753
theorem B2257223 : Blo 2255435 2257223 := bstep (se 1 (by rfl) ⟨1692917, by rfl⟩ : syracuseStep 2257223 = 3385835) B3385835
theorem B2539381 : Blo 2255435 2539381 := bbase (se 5 (by rfl) ⟨119033, by rfl⟩ : syracuseStep 2539381 = 238067) (by norm_num)
theorem B3385841 : Blo 2255435 3385841 := bstep (se 2 (by rfl) ⟨1269690, by rfl⟩ : syracuseStep 3385841 = 2539381) B2539381
theorem B2257227 : Blo 2255435 2257227 := bstep (se 1 (by rfl) ⟨1692920, by rfl⟩ : syracuseStep 2257227 = 3385841) B3385841
theorem B2856809 : Blo 2255435 2856809 := bbase (se 2 (by rfl) ⟨1071303, by rfl⟩ : syracuseStep 2856809 = 2142607) (by norm_num)
theorem B7618157 : Blo 2255435 7618157 := bstep (se 3 (by rfl) ⟨1428404, by rfl⟩ : syracuseStep 7618157 = 2856809) B2856809
theorem B5078771 : Blo 2255435 5078771 := bstep (se 1 (by rfl) ⟨3809078, by rfl⟩ : syracuseStep 5078771 = 7618157) B7618157
theorem B3385847 : Blo 2255435 3385847 := bstep (se 1 (by rfl) ⟨2539385, by rfl⟩ : syracuseStep 3385847 = 5078771) B5078771
theorem B2257231 : Blo 2255435 2257231 := bstep (se 1 (by rfl) ⟨1692923, by rfl⟩ : syracuseStep 2257231 = 3385847) B3385847
theorem B3385853 : Blo 2255435 3385853 := bbase (se 3 (by rfl) ⟨634847, by rfl⟩ : syracuseStep 3385853 = 1269695) (by norm_num)
theorem B2257235 : Blo 2255435 2257235 := bstep (se 1 (by rfl) ⟨1692926, by rfl⟩ : syracuseStep 2257235 = 3385853) B3385853
theorem B5078789 : Blo 2255435 5078789 := bbase (se 4 (by rfl) ⟨476136, by rfl⟩ : syracuseStep 5078789 = 952273) (by norm_num)
theorem B3385859 : Blo 2255435 3385859 := bstep (se 1 (by rfl) ⟨2539394, by rfl⟩ : syracuseStep 3385859 = 5078789) B5078789
theorem B2257239 : Blo 2255435 2257239 := bstep (se 1 (by rfl) ⟨1692929, by rfl⟩ : syracuseStep 2257239 = 3385859) B3385859
theorem B4285237 : Blo 2255435 4285237 := bbase (se 5 (by rfl) ⟨200870, by rfl⟩ : syracuseStep 4285237 = 401741) (by norm_num)
theorem B5713649 : Blo 2255435 5713649 := bstep (se 2 (by rfl) ⟨2142618, by rfl⟩ : syracuseStep 5713649 = 4285237) B4285237
theorem B3809099 : Blo 2255435 3809099 := bstep (se 1 (by rfl) ⟨2856824, by rfl⟩ : syracuseStep 3809099 = 5713649) B5713649
theorem B2539399 : Blo 2255435 2539399 := bstep (se 1 (by rfl) ⟨1904549, by rfl⟩ : syracuseStep 2539399 = 3809099) B3809099
theorem B3385865 : Blo 2255435 3385865 := bstep (se 2 (by rfl) ⟨1269699, by rfl⟩ : syracuseStep 3385865 = 2539399) B2539399
theorem B2257243 : Blo 2255435 2257243 := bstep (se 1 (by rfl) ⟨1692932, by rfl⟩ : syracuseStep 2257243 = 3385865) B3385865
theorem B11427317 : Blo 2255435 11427317 := bbase (se 5 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 11427317 = 1071311) (by norm_num)
theorem B7618211 : Blo 2255435 7618211 := bstep (se 1 (by rfl) ⟨5713658, by rfl⟩ : syracuseStep 7618211 = 11427317) B11427317
theorem B5078807 : Blo 2255435 5078807 := bstep (se 1 (by rfl) ⟨3809105, by rfl⟩ : syracuseStep 5078807 = 7618211) B7618211
theorem B3385871 : Blo 2255435 3385871 := bstep (se 1 (by rfl) ⟨2539403, by rfl⟩ : syracuseStep 3385871 = 5078807) B5078807
theorem B2257247 : Blo 2255435 2257247 := bstep (se 1 (by rfl) ⟨1692935, by rfl⟩ : syracuseStep 2257247 = 3385871) B3385871
theorem B3385877 : Blo 2255435 3385877 := bbase (se 6 (by rfl) ⟨79356, by rfl⟩ : syracuseStep 3385877 = 158713) (by norm_num)
theorem B2257251 : Blo 2255435 2257251 := bstep (se 1 (by rfl) ⟨1692938, by rfl⟩ : syracuseStep 2257251 = 3385877) B3385877
theorem B19283669 : Blo 2255435 19283669 := bbase (se 7 (by rfl) ⟨225980, by rfl⟩ : syracuseStep 19283669 = 451961) (by norm_num)
theorem B12855779 : Blo 2255435 12855779 := bstep (se 1 (by rfl) ⟨9641834, by rfl⟩ : syracuseStep 12855779 = 19283669) B19283669
theorem B8570519 : Blo 2255435 8570519 := bstep (se 1 (by rfl) ⟨6427889, by rfl⟩ : syracuseStep 8570519 = 12855779) B12855779
theorem B5713679 : Blo 2255435 5713679 := bstep (se 1 (by rfl) ⟨4285259, by rfl⟩ : syracuseStep 5713679 = 8570519) B8570519
theorem B3809119 : Blo 2255435 3809119 := bstep (se 1 (by rfl) ⟨2856839, by rfl⟩ : syracuseStep 3809119 = 5713679) B5713679
theorem B5078825 : Blo 2255435 5078825 := bstep (se 2 (by rfl) ⟨1904559, by rfl⟩ : syracuseStep 5078825 = 3809119) B3809119
theorem B3385883 : Blo 2255435 3385883 := bstep (se 1 (by rfl) ⟨2539412, by rfl⟩ : syracuseStep 3385883 = 5078825) B5078825
theorem B2257255 : Blo 2255435 2257255 := bstep (se 1 (by rfl) ⟨1692941, by rfl⟩ : syracuseStep 2257255 = 3385883) B3385883
theorem B2539417 : Blo 2255435 2539417 := bbase (se 2 (by rfl) ⟨952281, by rfl⟩ : syracuseStep 2539417 = 1904563) (by norm_num)
theorem B3385889 : Blo 2255435 3385889 := bstep (se 2 (by rfl) ⟨1269708, by rfl⟩ : syracuseStep 3385889 = 2539417) B2539417
theorem B2257259 : Blo 2255435 2257259 := bstep (se 1 (by rfl) ⟨1692944, by rfl⟩ : syracuseStep 2257259 = 3385889) B3385889
theorem B8570549 : Blo 2255435 8570549 := bbase (se 5 (by rfl) ⟨401744, by rfl⟩ : syracuseStep 8570549 = 803489) (by norm_num)
theorem B5713699 : Blo 2255435 5713699 := bstep (se 1 (by rfl) ⟨4285274, by rfl⟩ : syracuseStep 5713699 = 8570549) B8570549
theorem B7618265 : Blo 2255435 7618265 := bstep (se 2 (by rfl) ⟨2856849, by rfl⟩ : syracuseStep 7618265 = 5713699) B5713699
theorem B5078843 : Blo 2255435 5078843 := bstep (se 1 (by rfl) ⟨3809132, by rfl⟩ : syracuseStep 5078843 = 7618265) B7618265
theorem B3385895 : Blo 2255435 3385895 := bstep (se 1 (by rfl) ⟨2539421, by rfl⟩ : syracuseStep 3385895 = 5078843) B5078843
theorem B2257263 : Blo 2255435 2257263 := bstep (se 1 (by rfl) ⟨1692947, by rfl⟩ : syracuseStep 2257263 = 3385895) B3385895
theorem B3385901 : Blo 2255435 3385901 := bbase (se 3 (by rfl) ⟨634856, by rfl⟩ : syracuseStep 3385901 = 1269713) (by norm_num)
theorem B2257267 : Blo 2255435 2257267 := bstep (se 1 (by rfl) ⟨1692950, by rfl⟩ : syracuseStep 2257267 = 3385901) B3385901
theorem B5078861 : Blo 2255435 5078861 := bbase (se 3 (by rfl) ⟨952286, by rfl⟩ : syracuseStep 5078861 = 1904573) (by norm_num)
theorem B3385907 : Blo 2255435 3385907 := bstep (se 1 (by rfl) ⟨2539430, by rfl⟩ : syracuseStep 3385907 = 5078861) B5078861
theorem B2257271 : Blo 2255435 2257271 := bstep (se 1 (by rfl) ⟨1692953, by rfl⟩ : syracuseStep 2257271 = 3385907) B3385907
theorem B2856865 : Blo 2255435 2856865 := bbase (se 2 (by rfl) ⟨1071324, by rfl⟩ : syracuseStep 2856865 = 2142649) (by norm_num)
theorem B3809153 : Blo 2255435 3809153 := bstep (se 2 (by rfl) ⟨1428432, by rfl⟩ : syracuseStep 3809153 = 2856865) B2856865
theorem B2539435 : Blo 2255435 2539435 := bstep (se 1 (by rfl) ⟨1904576, by rfl⟩ : syracuseStep 2539435 = 3809153) B3809153
theorem B3385913 : Blo 2255435 3385913 := bstep (se 2 (by rfl) ⟨1269717, by rfl⟩ : syracuseStep 3385913 = 2539435) B2539435
theorem B2257275 : Blo 2255435 2257275 := bstep (se 1 (by rfl) ⟨1692956, by rfl⟩ : syracuseStep 2257275 = 3385913) B3385913
theorem B25711829 : Blo 2255435 25711829 := bbase (se 7 (by rfl) ⟨301310, by rfl⟩ : syracuseStep 25711829 = 602621) (by norm_num)
theorem B17141219 : Blo 2255435 17141219 := bstep (se 1 (by rfl) ⟨12855914, by rfl⟩ : syracuseStep 17141219 = 25711829) B25711829
theorem B11427479 : Blo 2255435 11427479 := bstep (se 1 (by rfl) ⟨8570609, by rfl⟩ : syracuseStep 11427479 = 17141219) B17141219
theorem B7618319 : Blo 2255435 7618319 := bstep (se 1 (by rfl) ⟨5713739, by rfl⟩ : syracuseStep 7618319 = 11427479) B11427479
theorem B5078879 : Blo 2255435 5078879 := bstep (se 1 (by rfl) ⟨3809159, by rfl⟩ : syracuseStep 5078879 = 7618319) B7618319
theorem B3385919 : Blo 2255435 3385919 := bstep (se 1 (by rfl) ⟨2539439, by rfl⟩ : syracuseStep 3385919 = 5078879) B5078879
theorem B2257279 : Blo 2255435 2257279 := bstep (se 1 (by rfl) ⟨1692959, by rfl⟩ : syracuseStep 2257279 = 3385919) B3385919
theorem B3385925 : Blo 2255435 3385925 := bbase (se 4 (by rfl) ⟨317430, by rfl⟩ : syracuseStep 3385925 = 634861) (by norm_num)
theorem B2257283 : Blo 2255435 2257283 := bstep (se 1 (by rfl) ⟨1692962, by rfl⟩ : syracuseStep 2257283 = 3385925) B3385925
theorem B3809173 : Blo 2255435 3809173 := bbase (se 6 (by rfl) ⟨89277, by rfl⟩ : syracuseStep 3809173 = 178555) (by norm_num)
theorem B5078897 : Blo 2255435 5078897 := bstep (se 2 (by rfl) ⟨1904586, by rfl⟩ : syracuseStep 5078897 = 3809173) B3809173
theorem B3385931 : Blo 2255435 3385931 := bstep (se 1 (by rfl) ⟨2539448, by rfl⟩ : syracuseStep 3385931 = 5078897) B5078897
theorem B2257287 : Blo 2255435 2257287 := bstep (se 1 (by rfl) ⟨1692965, by rfl⟩ : syracuseStep 2257287 = 3385931) B3385931
theorem B2539453 : Blo 2255435 2539453 := bbase (se 3 (by rfl) ⟨476147, by rfl⟩ : syracuseStep 2539453 = 952295) (by norm_num)
theorem B3385937 : Blo 2255435 3385937 := bstep (se 2 (by rfl) ⟨1269726, by rfl⟩ : syracuseStep 3385937 = 2539453) B2539453
theorem B2257291 : Blo 2255435 2257291 := bstep (se 1 (by rfl) ⟨1692968, by rfl⟩ : syracuseStep 2257291 = 3385937) B3385937
theorem B7618373 : Blo 2255435 7618373 := bbase (se 4 (by rfl) ⟨714222, by rfl⟩ : syracuseStep 7618373 = 1428445) (by norm_num)
theorem B5078915 : Blo 2255435 5078915 := bstep (se 1 (by rfl) ⟨3809186, by rfl⟩ : syracuseStep 5078915 = 7618373) B7618373
theorem B3385943 : Blo 2255435 3385943 := bstep (se 1 (by rfl) ⟨2539457, by rfl⟩ : syracuseStep 3385943 = 5078915) B5078915
theorem B2257295 : Blo 2255435 2257295 := bstep (se 1 (by rfl) ⟨1692971, by rfl⟩ : syracuseStep 2257295 = 3385943) B3385943
theorem B3385949 : Blo 2255435 3385949 := bbase (se 3 (by rfl) ⟨634865, by rfl⟩ : syracuseStep 3385949 = 1269731) (by norm_num)
theorem B2257299 : Blo 2255435 2257299 := bstep (se 1 (by rfl) ⟨1692974, by rfl⟩ : syracuseStep 2257299 = 3385949) B3385949
theorem B5078933 : Blo 2255435 5078933 := bbase (se 6 (by rfl) ⟨119037, by rfl⟩ : syracuseStep 5078933 = 238075) (by norm_num)
theorem B3385955 : Blo 2255435 3385955 := bstep (se 1 (by rfl) ⟨2539466, by rfl⟩ : syracuseStep 3385955 = 5078933) B5078933
theorem B2257303 : Blo 2255435 2257303 := bstep (se 1 (by rfl) ⟨1692977, by rfl⟩ : syracuseStep 2257303 = 3385955) B3385955
theorem B4821029 : Blo 2255435 4821029 := bbase (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) (by norm_num)
theorem B3214019 : Blo 2255435 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B8570717 : Blo 2255435 8570717 := bstep (se 3 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 8570717 = 3214019) B3214019
theorem B5713811 : Blo 2255435 5713811 := bstep (se 1 (by rfl) ⟨4285358, by rfl⟩ : syracuseStep 5713811 = 8570717) B8570717
theorem B3809207 : Blo 2255435 3809207 := bstep (se 1 (by rfl) ⟨2856905, by rfl⟩ : syracuseStep 3809207 = 5713811) B5713811
theorem B2539471 : Blo 2255435 2539471 := bstep (se 1 (by rfl) ⟨1904603, by rfl⟩ : syracuseStep 2539471 = 3809207) B3809207
theorem B3385961 : Blo 2255435 3385961 := bstep (se 2 (by rfl) ⟨1269735, by rfl⟩ : syracuseStep 3385961 = 2539471) B2539471
theorem B2257307 : Blo 2255435 2257307 := bstep (se 1 (by rfl) ⟨1692980, by rfl⟩ : syracuseStep 2257307 = 3385961) B3385961
theorem B10847333 : Blo 2255435 10847333 := bbase (se 4 (by rfl) ⟨1016937, by rfl⟩ : syracuseStep 10847333 = 2033875) (by norm_num)
theorem B7231555 : Blo 2255435 7231555 := bstep (se 1 (by rfl) ⟨5423666, by rfl⟩ : syracuseStep 7231555 = 10847333) B10847333
theorem B9642073 : Blo 2255435 9642073 := bstep (se 2 (by rfl) ⟨3615777, by rfl⟩ : syracuseStep 9642073 = 7231555) B7231555
theorem B12856097 : Blo 2255435 12856097 := bstep (se 2 (by rfl) ⟨4821036, by rfl⟩ : syracuseStep 12856097 = 9642073) B9642073
theorem B8570731 : Blo 2255435 8570731 := bstep (se 1 (by rfl) ⟨6428048, by rfl⟩ : syracuseStep 8570731 = 12856097) B12856097
theorem B11427641 : Blo 2255435 11427641 := bstep (se 2 (by rfl) ⟨4285365, by rfl⟩ : syracuseStep 11427641 = 8570731) B8570731
theorem B7618427 : Blo 2255435 7618427 := bstep (se 1 (by rfl) ⟨5713820, by rfl⟩ : syracuseStep 7618427 = 11427641) B11427641
theorem B5078951 : Blo 2255435 5078951 := bstep (se 1 (by rfl) ⟨3809213, by rfl⟩ : syracuseStep 5078951 = 7618427) B7618427
theorem B3385967 : Blo 2255435 3385967 := bstep (se 1 (by rfl) ⟨2539475, by rfl⟩ : syracuseStep 3385967 = 5078951) B5078951
theorem B2257311 : Blo 2255435 2257311 := bstep (se 1 (by rfl) ⟨1692983, by rfl⟩ : syracuseStep 2257311 = 3385967) B3385967
theorem B3385973 : Blo 2255435 3385973 := bbase (se 5 (by rfl) ⟨158717, by rfl⟩ : syracuseStep 3385973 = 317435) (by norm_num)
theorem B2257315 : Blo 2255435 2257315 := bstep (se 1 (by rfl) ⟨1692986, by rfl⟩ : syracuseStep 2257315 = 3385973) B3385973
theorem B4285381 : Blo 2255435 4285381 := bbase (se 4 (by rfl) ⟨401754, by rfl⟩ : syracuseStep 4285381 = 803509) (by norm_num)
theorem B5713841 : Blo 2255435 5713841 := bstep (se 2 (by rfl) ⟨2142690, by rfl⟩ : syracuseStep 5713841 = 4285381) B4285381
theorem B3809227 : Blo 2255435 3809227 := bstep (se 1 (by rfl) ⟨2856920, by rfl⟩ : syracuseStep 3809227 = 5713841) B5713841
theorem B5078969 : Blo 2255435 5078969 := bstep (se 2 (by rfl) ⟨1904613, by rfl⟩ : syracuseStep 5078969 = 3809227) B3809227
theorem B3385979 : Blo 2255435 3385979 := bstep (se 1 (by rfl) ⟨2539484, by rfl⟩ : syracuseStep 3385979 = 5078969) B5078969
theorem B2257319 : Blo 2255435 2257319 := bstep (se 1 (by rfl) ⟨1692989, by rfl⟩ : syracuseStep 2257319 = 3385979) B3385979
theorem B2539489 : Blo 2255435 2539489 := bbase (se 2 (by rfl) ⟨952308, by rfl⟩ : syracuseStep 2539489 = 1904617) (by norm_num)
theorem B3385985 : Blo 2255435 3385985 := bstep (se 2 (by rfl) ⟨1269744, by rfl⟩ : syracuseStep 3385985 = 2539489) B2539489
theorem B2257323 : Blo 2255435 2257323 := bstep (se 1 (by rfl) ⟨1692992, by rfl⟩ : syracuseStep 2257323 = 3385985) B3385985
theorem B5713861 : Blo 2255435 5713861 := bbase (se 4 (by rfl) ⟨535674, by rfl⟩ : syracuseStep 5713861 = 1071349) (by norm_num)
theorem B7618481 : Blo 2255435 7618481 := bstep (se 2 (by rfl) ⟨2856930, by rfl⟩ : syracuseStep 7618481 = 5713861) B5713861
theorem B5078987 : Blo 2255435 5078987 := bstep (se 1 (by rfl) ⟨3809240, by rfl⟩ : syracuseStep 5078987 = 7618481) B7618481
theorem B3385991 : Blo 2255435 3385991 := bstep (se 1 (by rfl) ⟨2539493, by rfl⟩ : syracuseStep 3385991 = 5078987) B5078987
theorem B2257327 : Blo 2255435 2257327 := bstep (se 1 (by rfl) ⟨1692995, by rfl⟩ : syracuseStep 2257327 = 3385991) B3385991
theorem B3385997 : Blo 2255435 3385997 := bbase (se 3 (by rfl) ⟨634874, by rfl⟩ : syracuseStep 3385997 = 1269749) (by norm_num)
theorem B2257331 : Blo 2255435 2257331 := bstep (se 1 (by rfl) ⟨1692998, by rfl⟩ : syracuseStep 2257331 = 3385997) B3385997
theorem B5079005 : Blo 2255435 5079005 := bbase (se 3 (by rfl) ⟨952313, by rfl⟩ : syracuseStep 5079005 = 1904627) (by norm_num)
theorem B3386003 : Blo 2255435 3386003 := bstep (se 1 (by rfl) ⟨2539502, by rfl⟩ : syracuseStep 3386003 = 5079005) B5079005
theorem B2257335 : Blo 2255435 2257335 := bstep (se 1 (by rfl) ⟨1693001, by rfl⟩ : syracuseStep 2257335 = 3386003) B3386003
theorem B3809261 : Blo 2255435 3809261 := bbase (se 3 (by rfl) ⟨714236, by rfl⟩ : syracuseStep 3809261 = 1428473) (by norm_num)
theorem B2539507 : Blo 2255435 2539507 := bstep (se 1 (by rfl) ⟨1904630, by rfl⟩ : syracuseStep 2539507 = 3809261) B3809261
theorem B3386009 : Blo 2255435 3386009 := bstep (se 2 (by rfl) ⟨1269753, by rfl⟩ : syracuseStep 3386009 = 2539507) B2539507
theorem B2257339 : Blo 2255435 2257339 := bstep (se 1 (by rfl) ⟨1693004, by rfl⟩ : syracuseStep 2257339 = 3386009) B3386009
theorem B2981713 : Blo 2255435 2981713 := bbase (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) (by norm_num)
theorem B3975617 : Blo 2255435 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B2650411 : Blo 2255435 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B3533881 : Blo 2255435 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B4711841 : Blo 2255435 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B3141227 : Blo 2255435 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B8376605 : Blo 2255435 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B5584403 : Blo 2255435 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B3722935 : Blo 2255435 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B4963913 : Blo 2255435 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B3309275 : Blo 2255435 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B8824733 : Blo 2255435 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B5883155 : Blo 2255435 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B3922103 : Blo 2255435 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B2614735 : Blo 2255435 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B3486313 : Blo 2255435 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B4648417 : Blo 2255435 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B24791557 : Blo 2255435 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B33055409 : Blo 2255435 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B88147757 : Blo 2255435 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B58765171 : Blo 2255435 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B78353561 : Blo 2255435 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B52235707 : Blo 2255435 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B69647609 : Blo 2255435 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B46431739 : Blo 2255435 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B61908985 : Blo 2255435 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B82545313 : Blo 2255435 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B110060417 : Blo 2255435 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B73373611 : Blo 2255435 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B97831481 : Blo 2255435 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B1043535797 : Blo 2255435 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B695690531 : Blo 2255435 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B463793687 : Blo 2255435 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B309195791 : Blo 2255435 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B206130527 : Blo 2255435 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B137420351 : Blo 2255435 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B91613567 : Blo 2255435 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B61075711 : Blo 2255435 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B81434281 : Blo 2255435 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B108579041 : Blo 2255435 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B72386027 : Blo 2255435 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B48257351 : Blo 2255435 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B32171567 : Blo 2255435 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B85790845 : Blo 2255435 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B457551173 : Blo 2255435 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B305034115 : Blo 2255435 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B406712153 : Blo 2255435 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B271141435 : Blo 2255435 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B1446087653 : Blo 2255435 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B964058435 : Blo 2255435 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B642705623 : Blo 2255435 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B428470415 : Blo 2255435 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B285646943 : Blo 2255435 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B761725181 : Blo 2255435 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B507816787 : Blo 2255435 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B677089049 : Blo 2255435 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1805570797 : Blo 2255435 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 2255435 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 2255435 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1069967879 : Blo 2255435 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B713311919 : Blo 2255435 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 2255435 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B317027519 : Blo 2255435 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B211351679 : Blo 2255435 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B140901119 : Blo 2255435 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 2255435 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B62622719 : Blo 2255435 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B41748479 : Blo 2255435 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B27832319 : Blo 2255435 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 2255435 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 2255435 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 2255435 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 2255435 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 2255435 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 2255435 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 2255435 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 2255435 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 2255435 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 2255435 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 2255435 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 2255435 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 2255435 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 2255435 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 2255435 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 2255435 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 2255435 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 2255435 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B12856279 : Blo 2255435 12856279 := bstep (se 1 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 12856279 = 19284419) B19284419
theorem B17141705 : Blo 2255435 17141705 := bstep (se 2 (by rfl) ⟨6428139, by rfl⟩ : syracuseStep 17141705 = 12856279) B12856279
theorem B11427803 : Blo 2255435 11427803 := bstep (se 1 (by rfl) ⟨8570852, by rfl⟩ : syracuseStep 11427803 = 17141705) B17141705
theorem B7618535 : Blo 2255435 7618535 := bstep (se 1 (by rfl) ⟨5713901, by rfl⟩ : syracuseStep 7618535 = 11427803) B11427803
theorem B5079023 : Blo 2255435 5079023 := bstep (se 1 (by rfl) ⟨3809267, by rfl⟩ : syracuseStep 5079023 = 7618535) B7618535
theorem B3386015 : Blo 2255435 3386015 := bstep (se 1 (by rfl) ⟨2539511, by rfl⟩ : syracuseStep 3386015 = 5079023) B5079023
theorem B2257343 : Blo 2255435 2257343 := bstep (se 1 (by rfl) ⟨1693007, by rfl⟩ : syracuseStep 2257343 = 3386015) B3386015
theorem B3386021 : Blo 2255435 3386021 := bbase (se 4 (by rfl) ⟨317439, by rfl⟩ : syracuseStep 3386021 = 634879) (by norm_num)
theorem B2257347 : Blo 2255435 2257347 := bstep (se 1 (by rfl) ⟨1693010, by rfl⟩ : syracuseStep 2257347 = 3386021) B3386021
theorem B2856961 : Blo 2255435 2856961 := bbase (se 2 (by rfl) ⟨1071360, by rfl⟩ : syracuseStep 2856961 = 2142721) (by norm_num)
theorem B3809281 : Blo 2255435 3809281 := bstep (se 2 (by rfl) ⟨1428480, by rfl⟩ : syracuseStep 3809281 = 2856961) B2856961
theorem B5079041 : Blo 2255435 5079041 := bstep (se 2 (by rfl) ⟨1904640, by rfl⟩ : syracuseStep 5079041 = 3809281) B3809281
theorem B3386027 : Blo 2255435 3386027 := bstep (se 1 (by rfl) ⟨2539520, by rfl⟩ : syracuseStep 3386027 = 5079041) B5079041
theorem B2257351 : Blo 2255435 2257351 := bstep (se 1 (by rfl) ⟨1693013, by rfl⟩ : syracuseStep 2257351 = 3386027) B3386027
theorem B2539525 : Blo 2255435 2539525 := bbase (se 4 (by rfl) ⟨238080, by rfl⟩ : syracuseStep 2539525 = 476161) (by norm_num)
theorem B3386033 : Blo 2255435 3386033 := bstep (se 2 (by rfl) ⟨1269762, by rfl⟩ : syracuseStep 3386033 = 2539525) B2539525
theorem B2257355 : Blo 2255435 2257355 := bstep (se 1 (by rfl) ⟨1693016, by rfl⟩ : syracuseStep 2257355 = 3386033) B3386033
theorem B3214093 : Blo 2255435 3214093 := bbase (se 3 (by rfl) ⟨602642, by rfl⟩ : syracuseStep 3214093 = 1205285) (by norm_num)
theorem B4285457 : Blo 2255435 4285457 := bstep (se 2 (by rfl) ⟨1607046, by rfl⟩ : syracuseStep 4285457 = 3214093) B3214093
theorem B2856971 : Blo 2255435 2856971 := bstep (se 1 (by rfl) ⟨2142728, by rfl⟩ : syracuseStep 2856971 = 4285457) B4285457
theorem B7618589 : Blo 2255435 7618589 := bstep (se 3 (by rfl) ⟨1428485, by rfl⟩ : syracuseStep 7618589 = 2856971) B2856971
theorem B5079059 : Blo 2255435 5079059 := bstep (se 1 (by rfl) ⟨3809294, by rfl⟩ : syracuseStep 5079059 = 7618589) B7618589
theorem B3386039 : Blo 2255435 3386039 := bstep (se 1 (by rfl) ⟨2539529, by rfl⟩ : syracuseStep 3386039 = 5079059) B5079059
theorem B2257359 : Blo 2255435 2257359 := bstep (se 1 (by rfl) ⟨1693019, by rfl⟩ : syracuseStep 2257359 = 3386039) B3386039
theorem B3386045 : Blo 2255435 3386045 := bbase (se 3 (by rfl) ⟨634883, by rfl⟩ : syracuseStep 3386045 = 1269767) (by norm_num)
theorem B2257363 : Blo 2255435 2257363 := bstep (se 1 (by rfl) ⟨1693022, by rfl⟩ : syracuseStep 2257363 = 3386045) B3386045
theorem B5079077 : Blo 2255435 5079077 := bbase (se 4 (by rfl) ⟨476163, by rfl⟩ : syracuseStep 5079077 = 952327) (by norm_num)
theorem B3386051 : Blo 2255435 3386051 := bstep (se 1 (by rfl) ⟨2539538, by rfl⟩ : syracuseStep 3386051 = 5079077) B5079077
theorem B2257367 : Blo 2255435 2257367 := bstep (se 1 (by rfl) ⟨1693025, by rfl⟩ : syracuseStep 2257367 = 3386051) B3386051
theorem B5713973 : Blo 2255435 5713973 := bbase (se 5 (by rfl) ⟨267842, by rfl⟩ : syracuseStep 5713973 = 535685) (by norm_num)
theorem B3809315 : Blo 2255435 3809315 := bstep (se 1 (by rfl) ⟨2856986, by rfl⟩ : syracuseStep 3809315 = 5713973) B5713973
theorem B2539543 : Blo 2255435 2539543 := bstep (se 1 (by rfl) ⟨1904657, by rfl⟩ : syracuseStep 2539543 = 3809315) B3809315
theorem B3386057 : Blo 2255435 3386057 := bstep (se 2 (by rfl) ⟨1269771, by rfl⟩ : syracuseStep 3386057 = 2539543) B2539543
theorem B2257371 : Blo 2255435 2257371 := bstep (se 1 (by rfl) ⟨1693028, by rfl⟩ : syracuseStep 2257371 = 3386057) B3386057
theorem B4576349 : Blo 2255435 4576349 := bbase (se 3 (by rfl) ⟨858065, by rfl⟩ : syracuseStep 4576349 = 1716131) (by norm_num)
theorem B12203597 : Blo 2255435 12203597 := bstep (se 3 (by rfl) ⟨2288174, by rfl⟩ : syracuseStep 12203597 = 4576349) B4576349
theorem B8135731 : Blo 2255435 8135731 := bstep (se 1 (by rfl) ⟨6101798, by rfl⟩ : syracuseStep 8135731 = 12203597) B12203597
theorem B10847641 : Blo 2255435 10847641 := bstep (se 2 (by rfl) ⟨4067865, by rfl⟩ : syracuseStep 10847641 = 8135731) B8135731
theorem B14463521 : Blo 2255435 14463521 := bstep (se 2 (by rfl) ⟨5423820, by rfl⟩ : syracuseStep 14463521 = 10847641) B10847641
theorem B9642347 : Blo 2255435 9642347 := bstep (se 1 (by rfl) ⟨7231760, by rfl⟩ : syracuseStep 9642347 = 14463521) B14463521
theorem B6428231 : Blo 2255435 6428231 := bstep (se 1 (by rfl) ⟨4821173, by rfl⟩ : syracuseStep 6428231 = 9642347) B9642347
theorem B4285487 : Blo 2255435 4285487 := bstep (se 1 (by rfl) ⟨3214115, by rfl⟩ : syracuseStep 4285487 = 6428231) B6428231
theorem B11427965 : Blo 2255435 11427965 := bstep (se 3 (by rfl) ⟨2142743, by rfl⟩ : syracuseStep 11427965 = 4285487) B4285487
theorem B7618643 : Blo 2255435 7618643 := bstep (se 1 (by rfl) ⟨5713982, by rfl⟩ : syracuseStep 7618643 = 11427965) B11427965
theorem B5079095 : Blo 2255435 5079095 := bstep (se 1 (by rfl) ⟨3809321, by rfl⟩ : syracuseStep 5079095 = 7618643) B7618643
theorem B3386063 : Blo 2255435 3386063 := bstep (se 1 (by rfl) ⟨2539547, by rfl⟩ : syracuseStep 3386063 = 5079095) B5079095
theorem B2257375 : Blo 2255435 2257375 := bstep (se 1 (by rfl) ⟨1693031, by rfl⟩ : syracuseStep 2257375 = 3386063) B3386063
theorem B3386069 : Blo 2255435 3386069 := bbase (se 7 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 3386069 = 79361) (by norm_num)
theorem B2257379 : Blo 2255435 2257379 := bstep (se 1 (by rfl) ⟨1693034, by rfl⟩ : syracuseStep 2257379 = 3386069) B3386069
theorem B5148413 : Blo 2255435 5148413 := bbase (se 3 (by rfl) ⟨965327, by rfl⟩ : syracuseStep 5148413 = 1930655) (by norm_num)
theorem B3432275 : Blo 2255435 3432275 := bstep (se 1 (by rfl) ⟨2574206, by rfl⟩ : syracuseStep 3432275 = 5148413) B5148413
theorem B2288183 : Blo 2255435 2288183 := bstep (se 1 (by rfl) ⟨1716137, by rfl⟩ : syracuseStep 2288183 = 3432275) B3432275
theorem B6101821 : Blo 2255435 6101821 := bstep (se 3 (by rfl) ⟨1144091, by rfl⟩ : syracuseStep 6101821 = 2288183) B2288183
theorem B8135761 : Blo 2255435 8135761 := bstep (se 2 (by rfl) ⟨3050910, by rfl⟩ : syracuseStep 8135761 = 6101821) B6101821
theorem B10847681 : Blo 2255435 10847681 := bstep (se 2 (by rfl) ⟨4067880, by rfl⟩ : syracuseStep 10847681 = 8135761) B8135761
theorem B7231787 : Blo 2255435 7231787 := bstep (se 1 (by rfl) ⟨5423840, by rfl⟩ : syracuseStep 7231787 = 10847681) B10847681
theorem B4821191 : Blo 2255435 4821191 := bstep (se 1 (by rfl) ⟨3615893, by rfl⟩ : syracuseStep 4821191 = 7231787) B7231787
theorem B3214127 : Blo 2255435 3214127 := bstep (se 1 (by rfl) ⟨2410595, by rfl⟩ : syracuseStep 3214127 = 4821191) B4821191
theorem B8571005 : Blo 2255435 8571005 := bstep (se 3 (by rfl) ⟨1607063, by rfl⟩ : syracuseStep 8571005 = 3214127) B3214127
theorem B5714003 : Blo 2255435 5714003 := bstep (se 1 (by rfl) ⟨4285502, by rfl⟩ : syracuseStep 5714003 = 8571005) B8571005
theorem B3809335 : Blo 2255435 3809335 := bstep (se 1 (by rfl) ⟨2857001, by rfl⟩ : syracuseStep 3809335 = 5714003) B5714003
theorem B5079113 : Blo 2255435 5079113 := bstep (se 2 (by rfl) ⟨1904667, by rfl⟩ : syracuseStep 5079113 = 3809335) B3809335
theorem B3386075 : Blo 2255435 3386075 := bstep (se 1 (by rfl) ⟨2539556, by rfl⟩ : syracuseStep 3386075 = 5079113) B5079113
theorem B2257383 : Blo 2255435 2257383 := bstep (se 1 (by rfl) ⟨1693037, by rfl⟩ : syracuseStep 2257383 = 3386075) B3386075
theorem B2539561 : Blo 2255435 2539561 := bbase (se 2 (by rfl) ⟨952335, by rfl⟩ : syracuseStep 2539561 = 1904671) (by norm_num)
theorem B3386081 : Blo 2255435 3386081 := bstep (se 2 (by rfl) ⟨1269780, by rfl⟩ : syracuseStep 3386081 = 2539561) B2539561
theorem B2257387 : Blo 2255435 2257387 := bstep (se 1 (by rfl) ⟨1693040, by rfl⟩ : syracuseStep 2257387 = 3386081) B3386081
theorem B4576381 : Blo 2255435 4576381 := bbase (se 3 (by rfl) ⟨858071, by rfl⟩ : syracuseStep 4576381 = 1716143) (by norm_num)
theorem B24407365 : Blo 2255435 24407365 := bstep (se 4 (by rfl) ⟨2288190, by rfl⟩ : syracuseStep 24407365 = 4576381) B4576381
theorem B32543153 : Blo 2255435 32543153 := bstep (se 2 (by rfl) ⟨12203682, by rfl⟩ : syracuseStep 32543153 = 24407365) B24407365
theorem B21695435 : Blo 2255435 21695435 := bstep (se 1 (by rfl) ⟨16271576, by rfl⟩ : syracuseStep 21695435 = 32543153) B32543153
theorem B14463623 : Blo 2255435 14463623 := bstep (se 1 (by rfl) ⟨10847717, by rfl⟩ : syracuseStep 14463623 = 21695435) B21695435
theorem B9642415 : Blo 2255435 9642415 := bstep (se 1 (by rfl) ⟨7231811, by rfl⟩ : syracuseStep 9642415 = 14463623) B14463623
theorem B12856553 : Blo 2255435 12856553 := bstep (se 2 (by rfl) ⟨4821207, by rfl⟩ : syracuseStep 12856553 = 9642415) B9642415
theorem B8571035 : Blo 2255435 8571035 := bstep (se 1 (by rfl) ⟨6428276, by rfl⟩ : syracuseStep 8571035 = 12856553) B12856553
theorem B5714023 : Blo 2255435 5714023 := bstep (se 1 (by rfl) ⟨4285517, by rfl⟩ : syracuseStep 5714023 = 8571035) B8571035
theorem B7618697 : Blo 2255435 7618697 := bstep (se 2 (by rfl) ⟨2857011, by rfl⟩ : syracuseStep 7618697 = 5714023) B5714023
theorem B5079131 : Blo 2255435 5079131 := bstep (se 1 (by rfl) ⟨3809348, by rfl⟩ : syracuseStep 5079131 = 7618697) B7618697
theorem B3386087 : Blo 2255435 3386087 := bstep (se 1 (by rfl) ⟨2539565, by rfl⟩ : syracuseStep 3386087 = 5079131) B5079131
theorem B2257391 : Blo 2255435 2257391 := bstep (se 1 (by rfl) ⟨1693043, by rfl⟩ : syracuseStep 2257391 = 3386087) B3386087
theorem B3386093 : Blo 2255435 3386093 := bbase (se 3 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 3386093 = 1269785) (by norm_num)
theorem B2257395 : Blo 2255435 2257395 := bstep (se 1 (by rfl) ⟨1693046, by rfl⟩ : syracuseStep 2257395 = 3386093) B3386093
theorem B5079149 : Blo 2255435 5079149 := bbase (se 3 (by rfl) ⟨952340, by rfl⟩ : syracuseStep 5079149 = 1904681) (by norm_num)
theorem B3386099 : Blo 2255435 3386099 := bstep (se 1 (by rfl) ⟨2539574, by rfl⟩ : syracuseStep 3386099 = 5079149) B5079149
theorem B2257399 : Blo 2255435 2257399 := bstep (se 1 (by rfl) ⟨1693049, by rfl⟩ : syracuseStep 2257399 = 3386099) B3386099
theorem B4285541 : Blo 2255435 4285541 := bbase (se 4 (by rfl) ⟨401769, by rfl⟩ : syracuseStep 4285541 = 803539) (by norm_num)
theorem B2857027 : Blo 2255435 2857027 := bstep (se 1 (by rfl) ⟨2142770, by rfl⟩ : syracuseStep 2857027 = 4285541) B4285541
theorem B3809369 : Blo 2255435 3809369 := bstep (se 2 (by rfl) ⟨1428513, by rfl⟩ : syracuseStep 3809369 = 2857027) B2857027
theorem B2539579 : Blo 2255435 2539579 := bstep (se 1 (by rfl) ⟨1904684, by rfl⟩ : syracuseStep 2539579 = 3809369) B3809369
theorem B3386105 : Blo 2255435 3386105 := bstep (se 2 (by rfl) ⟨1269789, by rfl⟩ : syracuseStep 3386105 = 2539579) B2539579
theorem B2257403 : Blo 2255435 2257403 := bstep (se 1 (by rfl) ⟨1693052, by rfl⟩ : syracuseStep 2257403 = 3386105) B3386105
theorem B8135845 : Blo 2255435 8135845 := bbase (se 4 (by rfl) ⟨762735, by rfl⟩ : syracuseStep 8135845 = 1525471) (by norm_num)
theorem B43391173 : Blo 2255435 43391173 := bstep (se 4 (by rfl) ⟨4067922, by rfl⟩ : syracuseStep 43391173 = 8135845) B8135845
theorem B57854897 : Blo 2255435 57854897 := bstep (se 2 (by rfl) ⟨21695586, by rfl⟩ : syracuseStep 57854897 = 43391173) B43391173
theorem B38569931 : Blo 2255435 38569931 := bstep (se 1 (by rfl) ⟨28927448, by rfl⟩ : syracuseStep 38569931 = 57854897) B57854897
theorem B25713287 : Blo 2255435 25713287 := bstep (se 1 (by rfl) ⟨19284965, by rfl⟩ : syracuseStep 25713287 = 38569931) B38569931
theorem B17142191 : Blo 2255435 17142191 := bstep (se 1 (by rfl) ⟨12856643, by rfl⟩ : syracuseStep 17142191 = 25713287) B25713287
theorem B11428127 : Blo 2255435 11428127 := bstep (se 1 (by rfl) ⟨8571095, by rfl⟩ : syracuseStep 11428127 = 17142191) B17142191
theorem B7618751 : Blo 2255435 7618751 := bstep (se 1 (by rfl) ⟨5714063, by rfl⟩ : syracuseStep 7618751 = 11428127) B11428127
theorem B5079167 : Blo 2255435 5079167 := bstep (se 1 (by rfl) ⟨3809375, by rfl⟩ : syracuseStep 5079167 = 7618751) B7618751
theorem B3386111 : Blo 2255435 3386111 := bstep (se 1 (by rfl) ⟨2539583, by rfl⟩ : syracuseStep 3386111 = 5079167) B5079167
theorem B2257407 : Blo 2255435 2257407 := bstep (se 1 (by rfl) ⟨1693055, by rfl⟩ : syracuseStep 2257407 = 3386111) B3386111
theorem B3386117 : Blo 2255435 3386117 := bbase (se 4 (by rfl) ⟨317448, by rfl⟩ : syracuseStep 3386117 = 634897) (by norm_num)
theorem B2257411 : Blo 2255435 2257411 := bstep (se 1 (by rfl) ⟨1693058, by rfl⟩ : syracuseStep 2257411 = 3386117) B3386117
theorem B3809389 : Blo 2255435 3809389 := bbase (se 3 (by rfl) ⟨714260, by rfl⟩ : syracuseStep 3809389 = 1428521) (by norm_num)
theorem B5079185 : Blo 2255435 5079185 := bstep (se 2 (by rfl) ⟨1904694, by rfl⟩ : syracuseStep 5079185 = 3809389) B3809389
theorem B3386123 : Blo 2255435 3386123 := bstep (se 1 (by rfl) ⟨2539592, by rfl⟩ : syracuseStep 3386123 = 5079185) B5079185
theorem B2257415 : Blo 2255435 2257415 := bstep (se 1 (by rfl) ⟨1693061, by rfl⟩ : syracuseStep 2257415 = 3386123) B3386123
theorem B2539597 : Blo 2255435 2539597 := bbase (se 3 (by rfl) ⟨476174, by rfl⟩ : syracuseStep 2539597 = 952349) (by norm_num)
theorem B3386129 : Blo 2255435 3386129 := bstep (se 2 (by rfl) ⟨1269798, by rfl⟩ : syracuseStep 3386129 = 2539597) B2539597
theorem B2257419 : Blo 2255435 2257419 := bstep (se 1 (by rfl) ⟨1693064, by rfl⟩ : syracuseStep 2257419 = 3386129) B3386129
theorem B7618805 : Blo 2255435 7618805 := bbase (se 5 (by rfl) ⟨357131, by rfl⟩ : syracuseStep 7618805 = 714263) (by norm_num)
theorem B5079203 : Blo 2255435 5079203 := bstep (se 1 (by rfl) ⟨3809402, by rfl⟩ : syracuseStep 5079203 = 7618805) B7618805
theorem B3386135 : Blo 2255435 3386135 := bstep (se 1 (by rfl) ⟨2539601, by rfl⟩ : syracuseStep 3386135 = 5079203) B5079203
theorem B2257423 : Blo 2255435 2257423 := bstep (se 1 (by rfl) ⟨1693067, by rfl⟩ : syracuseStep 2257423 = 3386135) B3386135
theorem B3386141 : Blo 2255435 3386141 := bbase (se 3 (by rfl) ⟨634901, by rfl⟩ : syracuseStep 3386141 = 1269803) (by norm_num)
theorem B2257427 : Blo 2255435 2257427 := bstep (se 1 (by rfl) ⟨1693070, by rfl⟩ : syracuseStep 2257427 = 3386141) B3386141
theorem B5079221 : Blo 2255435 5079221 := bbase (se 5 (by rfl) ⟨238088, by rfl⟩ : syracuseStep 5079221 = 476177) (by norm_num)
theorem B3386147 : Blo 2255435 3386147 := bstep (se 1 (by rfl) ⟨2539610, by rfl⟩ : syracuseStep 3386147 = 5079221) B5079221
theorem B2257431 : Blo 2255435 2257431 := bstep (se 1 (by rfl) ⟨1693073, by rfl⟩ : syracuseStep 2257431 = 3386147) B3386147
theorem B6864709 : Blo 2255435 6864709 := bbase (se 4 (by rfl) ⟨643566, by rfl⟩ : syracuseStep 6864709 = 1287133) (by norm_num)
theorem B9152945 : Blo 2255435 9152945 := bstep (se 2 (by rfl) ⟨3432354, by rfl⟩ : syracuseStep 9152945 = 6864709) B6864709
theorem B6101963 : Blo 2255435 6101963 := bstep (se 1 (by rfl) ⟨4576472, by rfl⟩ : syracuseStep 6101963 = 9152945) B9152945
theorem B4067975 : Blo 2255435 4067975 := bstep (se 1 (by rfl) ⟨3050981, by rfl⟩ : syracuseStep 4067975 = 6101963) B6101963
theorem B2711983 : Blo 2255435 2711983 := bstep (se 1 (by rfl) ⟨2033987, by rfl⟩ : syracuseStep 2711983 = 4067975) B4067975
theorem B3615977 : Blo 2255435 3615977 := bstep (se 2 (by rfl) ⟨1355991, by rfl⟩ : syracuseStep 3615977 = 2711983) B2711983
theorem B2410651 : Blo 2255435 2410651 := bstep (se 1 (by rfl) ⟨1807988, by rfl⟩ : syracuseStep 2410651 = 3615977) B3615977
theorem B12856805 : Blo 2255435 12856805 := bstep (se 4 (by rfl) ⟨1205325, by rfl⟩ : syracuseStep 12856805 = 2410651) B2410651
theorem B8571203 : Blo 2255435 8571203 := bstep (se 1 (by rfl) ⟨6428402, by rfl⟩ : syracuseStep 8571203 = 12856805) B12856805
theorem B5714135 : Blo 2255435 5714135 := bstep (se 1 (by rfl) ⟨4285601, by rfl⟩ : syracuseStep 5714135 = 8571203) B8571203
theorem B3809423 : Blo 2255435 3809423 := bstep (se 1 (by rfl) ⟨2857067, by rfl⟩ : syracuseStep 3809423 = 5714135) B5714135
theorem B2539615 : Blo 2255435 2539615 := bstep (se 1 (by rfl) ⟨1904711, by rfl⟩ : syracuseStep 2539615 = 3809423) B3809423
theorem B3386153 : Blo 2255435 3386153 := bstep (se 2 (by rfl) ⟨1269807, by rfl⟩ : syracuseStep 3386153 = 2539615) B2539615
theorem B2257435 : Blo 2255435 2257435 := bstep (se 1 (by rfl) ⟨1693076, by rfl⟩ : syracuseStep 2257435 = 3386153) B3386153
theorem C0 (j : ℕ) (h1 : 563858 ≤ j) (h2 : j ≤ 564358) : Blo 2255435 (4 * j + 3) := by
  interval_cases j
  · exact B2255435
  · exact B2255439
  · exact B2255443
  · exact B2255447
  · exact B2255451
  · exact B2255455
  · exact B2255459
  · exact B2255463
  · exact B2255467
  · exact B2255471
  · exact B2255475
  · exact B2255479
  · exact B2255483
  · exact B2255487
  · exact B2255491
  · exact B2255495
  · exact B2255499
  · exact B2255503
  · exact B2255507
  · exact B2255511
  · exact B2255515
  · exact B2255519
  · exact B2255523
  · exact B2255527
  · exact B2255531
  · exact B2255535
  · exact B2255539
  · exact B2255543
  · exact B2255547
  · exact B2255551
  · exact B2255555
  · exact B2255559
  · exact B2255563
  · exact B2255567
  · exact B2255571
  · exact B2255575
  · exact B2255579
  · exact B2255583
  · exact B2255587
  · exact B2255591
  · exact B2255595
  · exact B2255599
  · exact B2255603
  · exact B2255607
  · exact B2255611
  · exact B2255615
  · exact B2255619
  · exact B2255623
  · exact B2255627
  · exact B2255631
  · exact B2255635
  · exact B2255639
  · exact B2255643
  · exact B2255647
  · exact B2255651
  · exact B2255655
  · exact B2255659
  · exact B2255663
  · exact B2255667
  · exact B2255671
  · exact B2255675
  · exact B2255679
  · exact B2255683
  · exact B2255687
  · exact B2255691
  · exact B2255695
  · exact B2255699
  · exact B2255703
  · exact B2255707
  · exact B2255711
  · exact B2255715
  · exact B2255719
  · exact B2255723
  · exact B2255727
  · exact B2255731
  · exact B2255735
  · exact B2255739
  · exact B2255743
  · exact B2255747
  · exact B2255751
  · exact B2255755
  · exact B2255759
  · exact B2255763
  · exact B2255767
  · exact B2255771
  · exact B2255775
  · exact B2255779
  · exact B2255783
  · exact B2255787
  · exact B2255791
  · exact B2255795
  · exact B2255799
  · exact B2255803
  · exact B2255807
  · exact B2255811
  · exact B2255815
  · exact B2255819
  · exact B2255823
  · exact B2255827
  · exact B2255831
  · exact B2255835
  · exact B2255839
  · exact B2255843
  · exact B2255847
  · exact B2255851
  · exact B2255855
  · exact B2255859
  · exact B2255863
  · exact B2255867
  · exact B2255871
  · exact B2255875
  · exact B2255879
  · exact B2255883
  · exact B2255887
  · exact B2255891
  · exact B2255895
  · exact B2255899
  · exact B2255903
  · exact B2255907
  · exact B2255911
  · exact B2255915
  · exact B2255919
  · exact B2255923
  · exact B2255927
  · exact B2255931
  · exact B2255935
  · exact B2255939
  · exact B2255943
  · exact B2255947
  · exact B2255951
  · exact B2255955
  · exact B2255959
  · exact B2255963
  · exact B2255967
  · exact B2255971
  · exact B2255975
  · exact B2255979
  · exact B2255983
  · exact B2255987
  · exact B2255991
  · exact B2255995
  · exact B2255999
  · exact B2256003
  · exact B2256007
  · exact B2256011
  · exact B2256015
  · exact B2256019
  · exact B2256023
  · exact B2256027
  · exact B2256031
  · exact B2256035
  · exact B2256039
  · exact B2256043
  · exact B2256047
  · exact B2256051
  · exact B2256055
  · exact B2256059
  · exact B2256063
  · exact B2256067
  · exact B2256071
  · exact B2256075
  · exact B2256079
  · exact B2256083
  · exact B2256087
  · exact B2256091
  · exact B2256095
  · exact B2256099
  · exact B2256103
  · exact B2256107
  · exact B2256111
  · exact B2256115
  · exact B2256119
  · exact B2256123
  · exact B2256127
  · exact B2256131
  · exact B2256135
  · exact B2256139
  · exact B2256143
  · exact B2256147
  · exact B2256151
  · exact B2256155
  · exact B2256159
  · exact B2256163
  · exact B2256167
  · exact B2256171
  · exact B2256175
  · exact B2256179
  · exact B2256183
  · exact B2256187
  · exact B2256191
  · exact B2256195
  · exact B2256199
  · exact B2256203
  · exact B2256207
  · exact B2256211
  · exact B2256215
  · exact B2256219
  · exact B2256223
  · exact B2256227
  · exact B2256231
  · exact B2256235
  · exact B2256239
  · exact B2256243
  · exact B2256247
  · exact B2256251
  · exact B2256255
  · exact B2256259
  · exact B2256263
  · exact B2256267
  · exact B2256271
  · exact B2256275
  · exact B2256279
  · exact B2256283
  · exact B2256287
  · exact B2256291
  · exact B2256295
  · exact B2256299
  · exact B2256303
  · exact B2256307
  · exact B2256311
  · exact B2256315
  · exact B2256319
  · exact B2256323
  · exact B2256327
  · exact B2256331
  · exact B2256335
  · exact B2256339
  · exact B2256343
  · exact B2256347
  · exact B2256351
  · exact B2256355
  · exact B2256359
  · exact B2256363
  · exact B2256367
  · exact B2256371
  · exact B2256375
  · exact B2256379
  · exact B2256383
  · exact B2256387
  · exact B2256391
  · exact B2256395
  · exact B2256399
  · exact B2256403
  · exact B2256407
  · exact B2256411
  · exact B2256415
  · exact B2256419
  · exact B2256423
  · exact B2256427
  · exact B2256431
  · exact B2256435
  · exact B2256439
  · exact B2256443
  · exact B2256447
  · exact B2256451
  · exact B2256455
  · exact B2256459
  · exact B2256463
  · exact B2256467
  · exact B2256471
  · exact B2256475
  · exact B2256479
  · exact B2256483
  · exact B2256487
  · exact B2256491
  · exact B2256495
  · exact B2256499
  · exact B2256503
  · exact B2256507
  · exact B2256511
  · exact B2256515
  · exact B2256519
  · exact B2256523
  · exact B2256527
  · exact B2256531
  · exact B2256535
  · exact B2256539
  · exact B2256543
  · exact B2256547
  · exact B2256551
  · exact B2256555
  · exact B2256559
  · exact B2256563
  · exact B2256567
  · exact B2256571
  · exact B2256575
  · exact B2256579
  · exact B2256583
  · exact B2256587
  · exact B2256591
  · exact B2256595
  · exact B2256599
  · exact B2256603
  · exact B2256607
  · exact B2256611
  · exact B2256615
  · exact B2256619
  · exact B2256623
  · exact B2256627
  · exact B2256631
  · exact B2256635
  · exact B2256639
  · exact B2256643
  · exact B2256647
  · exact B2256651
  · exact B2256655
  · exact B2256659
  · exact B2256663
  · exact B2256667
  · exact B2256671
  · exact B2256675
  · exact B2256679
  · exact B2256683
  · exact B2256687
  · exact B2256691
  · exact B2256695
  · exact B2256699
  · exact B2256703
  · exact B2256707
  · exact B2256711
  · exact B2256715
  · exact B2256719
  · exact B2256723
  · exact B2256727
  · exact B2256731
  · exact B2256735
  · exact B2256739
  · exact B2256743
  · exact B2256747
  · exact B2256751
  · exact B2256755
  · exact B2256759
  · exact B2256763
  · exact B2256767
  · exact B2256771
  · exact B2256775
  · exact B2256779
  · exact B2256783
  · exact B2256787
  · exact B2256791
  · exact B2256795
  · exact B2256799
  · exact B2256803
  · exact B2256807
  · exact B2256811
  · exact B2256815
  · exact B2256819
  · exact B2256823
  · exact B2256827
  · exact B2256831
  · exact B2256835
  · exact B2256839
  · exact B2256843
  · exact B2256847
  · exact B2256851
  · exact B2256855
  · exact B2256859
  · exact B2256863
  · exact B2256867
  · exact B2256871
  · exact B2256875
  · exact B2256879
  · exact B2256883
  · exact B2256887
  · exact B2256891
  · exact B2256895
  · exact B2256899
  · exact B2256903
  · exact B2256907
  · exact B2256911
  · exact B2256915
  · exact B2256919
  · exact B2256923
  · exact B2256927
  · exact B2256931
  · exact B2256935
  · exact B2256939
  · exact B2256943
  · exact B2256947
  · exact B2256951
  · exact B2256955
  · exact B2256959
  · exact B2256963
  · exact B2256967
  · exact B2256971
  · exact B2256975
  · exact B2256979
  · exact B2256983
  · exact B2256987
  · exact B2256991
  · exact B2256995
  · exact B2256999
  · exact B2257003
  · exact B2257007
  · exact B2257011
  · exact B2257015
  · exact B2257019
  · exact B2257023
  · exact B2257027
  · exact B2257031
  · exact B2257035
  · exact B2257039
  · exact B2257043
  · exact B2257047
  · exact B2257051
  · exact B2257055
  · exact B2257059
  · exact B2257063
  · exact B2257067
  · exact B2257071
  · exact B2257075
  · exact B2257079
  · exact B2257083
  · exact B2257087
  · exact B2257091
  · exact B2257095
  · exact B2257099
  · exact B2257103
  · exact B2257107
  · exact B2257111
  · exact B2257115
  · exact B2257119
  · exact B2257123
  · exact B2257127
  · exact B2257131
  · exact B2257135
  · exact B2257139
  · exact B2257143
  · exact B2257147
  · exact B2257151
  · exact B2257155
  · exact B2257159
  · exact B2257163
  · exact B2257167
  · exact B2257171
  · exact B2257175
  · exact B2257179
  · exact B2257183
  · exact B2257187
  · exact B2257191
  · exact B2257195
  · exact B2257199
  · exact B2257203
  · exact B2257207
  · exact B2257211
  · exact B2257215
  · exact B2257219
  · exact B2257223
  · exact B2257227
  · exact B2257231
  · exact B2257235
  · exact B2257239
  · exact B2257243
  · exact B2257247
  · exact B2257251
  · exact B2257255
  · exact B2257259
  · exact B2257263
  · exact B2257267
  · exact B2257271
  · exact B2257275
  · exact B2257279
  · exact B2257283
  · exact B2257287
  · exact B2257291
  · exact B2257295
  · exact B2257299
  · exact B2257303
  · exact B2257307
  · exact B2257311
  · exact B2257315
  · exact B2257319
  · exact B2257323
  · exact B2257327
  · exact B2257331
  · exact B2257335
  · exact B2257339
  · exact B2257343
  · exact B2257347
  · exact B2257351
  · exact B2257355
  · exact B2257359
  · exact B2257363
  · exact B2257367
  · exact B2257371
  · exact B2257375
  · exact B2257379
  · exact B2257383
  · exact B2257387
  · exact B2257391
  · exact B2257395
  · exact B2257399
  · exact B2257403
  · exact B2257407
  · exact B2257411
  · exact B2257415
  · exact B2257419
  · exact B2257423
  · exact B2257427
  · exact B2257431
  · exact B2257435
theorem solution (m : ℕ) (hlo : 2255435 ≤ m) (hhi : m ≤ 2257435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 563858 ≤ j := by omega
    have hj2 : j ≤ 564358 := by omega
    have hb : Blo 2255435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
